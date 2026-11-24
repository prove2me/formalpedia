-- Prove2me | solution 1 for GlobalTheory.NoCommonZeroSpread.no_common_zero_spreads
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:27.003271+00:00
-- url     : https://prove2.me/submissions/88fcabc5-e845-4b45-9437-a1b9b65cf6d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhd
import Theorems.Thm_GlobalTheory_NoCommonZeroSpread_exists_common_denominator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.NoCommonZeroSpread
namespace GlobalTheory.NoCommonZeroSpread
theorem _root_.solution : ∀ (A : Type) [CommRing A] (τ J : Type) [Finite τ] (F : J → MvPolynomial τ A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), (¬ ∃ z : τ → Ω, ∀ j, MvPolynomial.eval₂ φ z (F j) = 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ ∃ z : τ → k, ∀ j, MvPolynomial.eval₂ ψ z (F j) = 0 := by
  intro A _ τ J _ F Ω _ _ φ hno
  classical
  let G : J → MvPolynomial τ Ω := fun j => MvPolynomial.map φ (F j)

  have h1 : (1 : MvPolynomial τ Ω) ∈ Ideal.span (Set.range G) := by
    have hz : MvPolynomial.zeroLocus Ω (Ideal.span (Set.range G)) = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      apply hno
      refine ⟨x, fun j => ?_⟩
      have := hx (G j) (Ideal.subset_span ⟨j, rfl⟩)
      simpa [G, MvPolynomial.coe_aeval_eq_eval, MvPolynomial.eval_map] using this
    have := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω) (Ideal.span (Set.range G))
    rw [hz, MvPolynomial.vanishingIdeal_empty, eq_comm, Ideal.radical_eq_top] at this
    rw [this]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1

  let K : Subfield Ω := Subfield.closure (φ.range : Set Ω)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K Ω)
    (LinearMap.ker_eq_bot.2 (algebraMap K Ω).injective)
  have hg1 : ∀ y : K, g (y : Ω) = y := fun y => by
    exact LinearMap.congr_fun hg y
  have hgK : ∀ (x : Ω) (y : K), ((g (x * y) : K) : Ω) = (g x : Ω) * y := by
    intro x y
    have : x * (y : Ω) = y • x := by rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, Subfield.coe_mul, mul_comm]
  have hφK : ∀ a : A, φ a ∈ K := fun a => Subfield.subset_closure (RingHom.mem_range_self φ a)
  let P : MvPolynomial τ Ω → MvPolynomial τ Ω := fun h =>
    ∑ m ∈ h.support, MvPolynomial.monomial m ((g (h.coeff m) : K) : Ω)
  have hPc : ∀ h n, (P h).coeff n = ((g (h.coeff n) : K) : Ω) := by
    intro h n
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hn
    · rfl
    · rw [MvPolynomial.notMem_support_iff.1 hn]; simp
  have hPadd : ∀ h₁ h₂, P (h₁ + h₂) = P h₁ + P h₂ := by
    intro h₁ h₂; ext n; simp [hPc, MvPolynomial.coeff_add]
  have hP1 : P 1 = 1 := by
    ext n
    rw [hPc, MvPolynomial.coeff_one]
    split_ifs
    · have := hg1 1; simpa using this
    · simp
  have hPmul : ∀ h j, P (h * G j) = P h * G j := by
    intro h j; ext n
    rw [hPc, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul, map_sum]
    refine (map_sum K.subtype _ _).trans (Finset.sum_congr rfl fun x _ => ?_)
    show ((g _ : K) : Ω) = _
    have e : (G j).coeff x.2 = ((⟨φ ((F j).coeff x.2), hφK _⟩ : K) : Ω) := by
      simp [G, MvPolynomial.coeff_map]
    rw [e, hgK, hPc]
  let PA : MvPolynomial τ Ω →+ MvPolynomial τ Ω := AddMonoidHom.mk' P hPadd
  have hsum : ∑ j ∈ c.support, P (c j) * G j = 1 := by
    simp only [Finsupp.sum, smul_eq_mul] at hc
    have := congrArg PA hc
    rw [map_sum] at this
    simp only [PA, AddMonoidHom.mk'_apply] at this
    rw [← hP1]
    convert this using 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (hPmul _ _).symm

  let S : Finset Ω := c.support.biUnion (fun j => (P (c j)).coeffs)
  obtain ⟨b, hb, hbS⟩ := exists_common_denominator φ S (by
    intro x hx
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hj
    rw [hPc]; exact (g _).2)
  have hQ : ∀ j, ∃ q : MvPolynomial τ A,
      MvPolynomial.map φ q = MvPolynomial.C (φ b) * P (c j) := by
    intro j
    have : MvPolynomial.C (φ b) * P (c j) ∈ Set.range (MvPolynomial.map (σ := τ) φ) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro y hy
      obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 (Finset.mem_coe.1 hy)
      rw [MvPolynomial.coeff_C_mul]
      by_cases hn : (P (c j)).coeff n = 0
      · rw [hn, mul_zero]; exact ⟨0, map_zero φ⟩
      · have hj : j ∈ c.support := by
          rw [Finsupp.mem_support_iff]
          intro h0; apply hn; rw [hPc, h0]; simp
        exact hbS _ (Finset.mem_biUnion.2 ⟨j, hj,
          MvPolynomial.mem_coeffs_iff.2 ⟨n, MvPolynomial.mem_support_iff.2 hn, rfl⟩⟩)
    exact this
  choose q hq using hQ
  let E : MvPolynomial τ A := MvPolynomial.C b - ∑ j ∈ c.support, q j * F j
  have hE : MvPolynomial.map φ E = 0 := by
    have hG : ∀ j, MvPolynomial.map φ (F j) = G j := fun j => rfl
    simp only [E, map_sub, map_sum, map_mul, MvPolynomial.map_C, hq, hG, _root_.mul_assoc]
    rw [← Finset.mul_sum, hsum, _root_.mul_one, sub_self]
  refine ⟨b, E.coeffs, hb, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hy
    have := congrArg (MvPolynomial.coeff n) hE
    rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
  · intro k _ ψ hψb hψI ⟨z, hz⟩
    have h0 : MvPolynomial.map ψ E = 0 := by
      ext n
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
      by_cases hn : n ∈ E.support
      · exact hψI _ (MvPolynomial.mem_coeffs_iff.2 ⟨n, hn, rfl⟩)
      · rw [MvPolynomial.notMem_support_iff.1 hn, map_zero]
    have h2 : MvPolynomial.eval₂ ψ z E = 0 := by
      rw [MvPolynomial.eval₂_eq_eval_map, h0, map_zero]
    have h3 : MvPolynomial.eval₂ ψ z E = ψ b := by
      simp [E, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum,
        MvPolynomial.eval₂_mul, hz]
    exact hψb (h3 ▸ h2)
end GlobalTheory.NoCommonZeroSpread
