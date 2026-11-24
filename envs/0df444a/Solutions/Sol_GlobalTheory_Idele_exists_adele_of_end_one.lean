-- Prove2me | solution 1 for GlobalTheory.Idele.exists_adele_of_end_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:37:19.189385+00:00
-- url     : https://prove2.me/submissions/884fd952-4663-44c8-b194-1441b6bbf6fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_exists_exp_neg_lt
import Theorems.Thm_GlobalTheory_Idele_exists_limit
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_mem_adelicIdeal_one_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk

set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing
noncomputable section
open GlobalTheory GlobalTheory.Idele
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace GlobalTheory.Idele
theorem _root_.solution
    (ψ : (𝔸ᶠ[R, K] ⧸ adelicIdeal (1 : FractionalIdeal R⁰ K)) →ₗ[R]
      (𝔸ᶠ[R, K] ⧸ adelicIdeal (1 : FractionalIdeal R⁰ K))) :
    ∃ t : 𝔸ᶠ[R, K], ∀ a, ψ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (t * a) := by
  choose y hy using fun b : R => Submodule.Quotient.mk_surjective _
    (ψ (Submodule.Quotient.mk (algebraMap K 𝔸ᶠ[R, K] (algebraMap R K b)⁻¹)))
  let ι : ∀ v : HeightOneSpectrum R, R → v.adicCompletion K :=
    fun v b => algebraMap K (v.adicCompletion K) (algebraMap R K b)
  have hsm : ∀ (r : R) (x : K), r • algebraMap K 𝔸ᶠ[R, K] x =
      algebraMap K 𝔸ᶠ[R, K] (algebraMap R K r * x) := fun r x => by
    rw [Algebra.smul_def, map_mul]; rfl

  have hint : ∀ b v, Valued.v (ι v b * y b v) ≤ 1 := by
    intro b v
    have : b • y b ∈ adelicIdeal (1 : FractionalIdeal R⁰ K) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, hy, ← map_smul,
        ← Submodule.Quotient.mk_smul, hsm, (Submodule.Quotient.mk_eq_zero _).2, map_zero]
      rw [algebraMap_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal R⁰ K))]
      rcases eq_or_ne (algebraMap R K b) 0 with h | h
      · simp [h, FractionalIdeal.zero_mem]
      · rw [mul_inv_cancel₀ h]; exact FractionalIdeal.one_mem_one _
    have := mem_adelicIdeal_one_iff.1 this v
    rwa [adele_smul_apply] at this

  have hcomp : ∀ b c, c ≠ 0 → ∀ v,
      Valued.v (ι v (b * c) * y (b * c) v - ι v b * y b v) ≤ Valued.v (ι v b) := by
    intro b c hc v
    have hc1 : algebraMap R K c ≠ 0 := by simpa using hc
    have : c • y (b * c) - y b ∈ adelicIdeal (1 : FractionalIdeal R⁰ K) := by
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_smul, hy, hy, ← map_smul,
        ← Submodule.Quotient.mk_smul, hsm, map_mul (algebraMap R K), mul_inv, mul_comm,
        mul_assoc, inv_mul_cancel₀ hc1, mul_one]
    have := mem_adelicIdeal_one_iff.1 this v
    rw [adele_sub_apply, adele_smul_apply] at this
    have h2 : ι v (b * c) * y (b * c) v - ι v b * y b v = ι v b * (ι v c * y (b * c) v - y b v) := by
      simp only [ι, map_mul]; ring
    rw [h2, map_mul]
    exact mul_le_of_le_one_right' this
  choose π hπ using fun v : HeightOneSpectrum R => v.valuation_exists_uniformizer' K
  have hπn : ∀ v (n : ℕ), Valued.v (ι v (π v ^ n)) = exp (-(n : ℤ)) := by
    intro v n
    have : v.valuation K (algebraMap R K (π v)) = exp (-1) := hπ v
    simp only [ι]
    rw [valued_algebraMap, map_pow, map_pow, this, ← exp_nsmul]
    simp
  have hπ0 : ∀ v (n : ℕ), π v ^ n ≠ 0 := by
    intro v n h
    have := hπn v n
    rw [h] at this
    simp only [ι, map_zero] at this
    exact exp_ne_zero this.symm
  have hlim : ∀ v, ∃ t : v.adicCompletion K, ∀ n : ℕ,
      Valued.v (t - ι v (π v ^ n) * y (π v ^ n) v) ≤ exp (-(n : ℤ)) := by
    intro v
    refine exists_limit v _ fun m n hnm => ?_
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add, ← hπn v n]
    exact hcomp _ _ (hπ0 v k) v
  choose t ht using hlim
  have htb : ∀ b, b ≠ 0 → ∀ v, Valued.v (t v - ι v b * y b v) ≤ Valued.v (ι v b) := by
    intro b hb v
    have hb0 : Valued.v (ι v b) ≠ 0 := by simpa [ι] using hb
    obtain ⟨n, hn⟩ := exists_exp_neg_lt hb0
    have h1 := (ht v n).trans hn.le
    have h2 := hcomp b (π v ^ n) (hπ0 v n) v
    have h3 := hcomp (π v ^ n) b hb v
    rw [hπn, mul_comm (π v ^ n) b, Valuation.map_sub_swap] at h3
    rw [← sub_add_sub_cancel (t v) (ι v (π v ^ n) * y (π v ^ n) v),
      ← sub_add_sub_cancel (ι v (π v ^ n) * y (π v ^ n) v)
        (ι v (b * π v ^ n) * y (b * π v ^ n) v)]
    exact (Valuation.map_add _ _ _).trans (max_le h1
      ((Valuation.map_add _ _ _).trans (max_le (h3.trans hn.le) h2)))
  have ht1 : ∀ v, Valued.v (t v) ≤ 1 := by
    intro v
    have h1 := ht v 0
    rw [← sub_add_cancel (t v) (ι v (π v ^ 0) * y (π v ^ 0) v)]
    exact (Valuation.map_add _ _ _).trans (max_le (by simpa using h1) (hint _ v))
  let T : 𝔸ᶠ[R, K] := ⟨t, Filter.Eventually.of_forall fun v => ht1 v⟩
  have hT : ∀ v, T v = t v := fun _ => rfl
  refine ⟨T, fun a => ?_⟩
  obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal R⁰ K)) a
  obtain ⟨r, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rw [(Submodule.Quotient.eq _).2 hx, div_eq_mul_inv, ← hsm, Submodule.Quotient.mk_smul, map_smul,
    ← hy, ← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq, mem_adelicIdeal_one_iff]
  intro v
  have hx' := mem_adelicIdeal_one_iff.1 hx v
  rw [adele_sub_apply, adele_algebraMap_apply, map_div₀] at hx'
  have hb1 : ι v b ≠ 0 := by simpa [ι] using hb0
  have hb2 : Valued.v (ι v b) ≠ 0 := by simpa using hb1
  have h2 : (T * a - r • y b) v =
      t v * (a v - ι v r / ι v b) + ι v r * ((t v - ι v b * y b v) / ι v b) := by
    rw [adele_sub_apply, adele_mul_apply, adele_smul_apply, hT]
    change t v * a v - ι v r * y b v = _
    field_simp
    ring
  rw [h2]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact mul_le_one' (ht1 v) hx'
  · rw [map_mul, map_div₀]
    refine mul_le_one' ?_ ((div_le_one₀ (zero_lt_iff.2 hb2)).2 (htb b hb0 v))
    simp only [ι]
    rw [valued_algebraMap]; exact v.valuation_le_one r
end GlobalTheory.Idele
