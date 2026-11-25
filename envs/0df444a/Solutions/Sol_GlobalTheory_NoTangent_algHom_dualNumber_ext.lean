-- Prove2me | solution 1 for GlobalTheory.NoTangent.algHom_dualNumber_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:55.434554+00:00
-- url     : https://prove2.me/submissions/d56699f2-b861-4132-bbe1-47586d253f53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsAdicCompleteOfFgOfNatCastMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesExistsPolynomialTotalDegreeLeSubMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AlgHomDualNumberExt
import Theorems.Thm_GlobalTheory_NoTangent_leibniz_eq_zero
import Theorems.Thm_GlobalTheory_NoTangent_finite_quotient
import Theorems.Thm_GlobalTheory_T_isAdicComplete_of_fg_of_natCast_mem_of_integers
import Theorems.Thm_GlobalTheory_T_mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.NoTangent
open MvPowerSeries
namespace GlobalTheory.NoTangent
theorem _root_.solution : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (p : ℕ), p ≠ 0 → IsAdicComplete (Ideal.span {(p : O)}) O → ∀ J : Ideal O, J.FG → J ≠ ⊤ → (p : O) ∈ J → ∀ (σ : Type) [Finite σ] (n : ℕ) (e : Fin n ≃ σ) (f : Fin n → MvPowerSeries σ O) (M N : ℕ) (U : (MvPowerSeries σ O)ˣ), N ≠ 0 → Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : O →+* MvPowerSeries σ O) J → Matrix.det (Matrix.of fun i j : Fin n => MvPowerSeries.pderiv O (e j) (f i)) = (N : MvPowerSeries σ O) * U → ∀ φ φ' : (MvPowerSeries σ O ⧸ Ideal.span (Set.range f)) →ₐ[O] DualNumber C, (∀ a, (φ a).fst = (φ' a).fst) → φ = φ' := by
  intro C _ _ _ v O _ _ hv p hp hc J hJ hJt hpJ σ _ n e f M N U hN hM hdet φ φ' hfst
  classical
  have hJc := GlobalTheory.T.isAdicComplete_of_fg_of_natCast_mem_of_integers C v O hv p hp hc J hJ hJt hpJ
  have hfin := finite_quotient _ M (GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem O J hJ hJc σ (Fin n) f M hM)
  let I := Ideal.span (Set.range f)
  let ψ : MvPowerSeries σ O →ₐ[O] DualNumber C := φ.comp (Ideal.Quotient.mkₐ O I)
  let ψ' : MvPowerSeries σ O →ₐ[O] DualNumber C := φ'.comp (Ideal.Quotient.mkₐ O I)
  let φ₀ : MvPowerSeries σ O →ₐ[O] C := (TrivSqZeroExt.fstHom O C C).comp ψ
  have h0 : ∀ g, (ψ g).fst = φ₀ g := fun g => rfl
  have h0' : ∀ g, (ψ' g).fst = φ₀ g := fun g => (hfst _).symm
  have hψI : ∀ g ∈ I, ψ g = 0 := fun g hg => by
    simp [ψ, Ideal.Quotient.eq_zero_iff_mem.2 hg]
  have hψI' : ∀ g ∈ I, ψ' g = 0 := fun g hg => by
    simp [ψ', Ideal.Quotient.eq_zero_iff_mem.2 hg]
  have hCa : ∀ c : O, (MvPowerSeries.C c : MvPowerSeries σ O) = algebraMap O _ c := fun c => rfl
  have hle : ∀ g, v (φ₀ g) ≤ 1 := by
    intro g
    have h1 : IsIntegral O (Ideal.Quotient.mkₐ O I g) := Algebra.IsIntegral.isIntegral _
    have h2 := h1.map ((TrivSqZeroExt.fstHom O C C).comp φ)
    exact hv.mem_of_integral h2
  choose a ha using fun j => hv.exists_of_le_one (hle (X j))
  let K : Ideal (MvPowerSeries σ O) :=
    { carrier := {g | v (φ₀ g) < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
        exact v.map_add_lt hx hy
      zero_mem' := by simp
      smul_mem' := fun s x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hx ⊢
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle s) zero_le hx }
  have hK : ∀ g, g ∈ K ↔ v (φ₀ g) < 1 := fun g => Iff.rfl
  have hJK : J ≤ K.comap (MvPowerSeries.C : O →+* MvPowerSeries σ O) := by
    intro c hc
    rw [Ideal.mem_comap, hK, hCa, AlgHom.commutes]
    refine lt_of_le_of_ne (hv.map_le_one c) fun h => hJt ?_
    exact J.eq_top_of_isUnit_mem hc (hv.isUnit_of_one' h)
  have hIK : I ≤ K := by
    intro g hg
    rw [hK, ← h0, hψI g hg]; simp
  have hXK : ∀ j, X j ∈ K := by
    intro j
    have h1 : (X j : MvPowerSeries σ O) ^ M ∈ K :=
      (hM.trans (sup_le hIK (Ideal.map_le_iff_le_comap.2 hJK)))
        (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) M)
    rw [hK, map_pow, map_pow] at h1
    refine lt_of_le_of_ne (hle _) fun h => ?_
    simp [h] at h1
  let J' : Ideal O := J ⊔ Ideal.span (Set.range a)
  have hJ' : J'.FG := Submodule.FG.sup hJ (Submodule.fg_span (Set.finite_range a))
  have hJ'K : J' ≤ K.comap (MvPowerSeries.C : O →+* MvPowerSeries σ O) := by
    refine sup_le hJK (Ideal.span_le.2 ?_)
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, hK, hCa, AlgHom.commutes, ha]
    exact hXK j
  have hJ't : J' ≠ ⊤ := by
    intro h
    have : (1 : O) ∈ J' := h ▸ Submodule.mem_top
    have h2 := hJ'K this
    rw [Ideal.mem_comap, hK] at h2
    simp at h2
  have hJ'c := GlobalTheory.T.isAdicComplete_of_fg_of_natCast_mem_of_integers C v O hv p hp hc J' hJ' hJ't (Ideal.mem_sup_left hpJ)
  have hP := GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem O J' hJ' hJ'c σ σ
    (fun j => (X j - MvPowerSeries.C (a j) : MvPowerSeries σ O)) 1 (by
      rw [pow_one, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : (X j : MvPowerSeries σ O) =
          (X j - MvPowerSeries.C (a j)) + MvPowerSeries.C (a j) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.subset_span ⟨j, rfl⟩)
        (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩))))
  let d : Fin n → C := fun j => (ψ' (X (e j))).snd - (ψ (X (e j))).snd
  let E : MvPowerSeries σ O →+ C :=
    { toFun := fun g => (ψ' g).snd - (ψ g).snd - ∑ j, φ₀ (pderiv O (e j) g) * d j
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [map_add, TrivSqZeroExt.snd_add, add_mul, Finset.sum_add_distrib]; ring }
  have hE : ∀ g, E g = (ψ' g).snd - (ψ g).snd - ∑ j, φ₀ (pderiv O (e j) g) * d j :=
    fun g => rfl
  have hE0 : ∀ g, E g = 0 := by
    refine leibniz_eq_zero (φ₀ : MvPowerSeries σ O →+* C) E a ?_ ?_ ?_ ?_
      (fun g => (hP g).imp fun P h => h.2)
    · intro g h
      simp only [hE, map_mul, DualNumber.snd_mul, h0, h0', Derivation.leibniz, smul_eq_mul,
        map_add, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
        RingHom.coe_coe]
      ring
    · intro c
      rw [hE]
      simp only [pderiv_C, map_zero, zero_mul, Finset.sum_const_zero, sub_zero]
      rw [hCa, AlgHom.commutes, AlgHom.commutes, sub_self]
    · intro s
      obtain ⟨k, rfl⟩ := e.surjective s
      rw [hE, Finset.sum_eq_single k]
      · simp [d, pderiv_X]
      · intro j _ hj
        simp [pderiv_X, hj, hj.symm]
      · simp
    · intro j
      rw [RingHom.coe_coe, map_sub, hCa, AlgHom.commutes, ha, sub_self]
  have hd : d = 0 := by
    let A : Matrix (Fin n) (Fin n) (MvPowerSeries σ O) :=
      Matrix.of fun i j : Fin n => MvPowerSeries.pderiv O (e j) (f i)
    refine Matrix.eq_zero_of_mulVec_eq_zero
      (M := (φ₀ : MvPowerSeries σ O →+* C).mapMatrix A) ?_ ?_
    · rw [← RingHom.map_det, hdet, map_mul, map_natCast]
      exact mul_ne_zero (Nat.cast_ne_zero.2 hN) (U.isUnit.map _).ne_zero
    · funext i
      have h1 := hE0 (f i)
      have hi : f i ∈ I := Ideal.subset_span ⟨i, rfl⟩
      rw [hE, hψI _ hi, hψI' _ hi, sub_self, zero_sub, neg_eq_zero] at h1
      simpa [Matrix.mulVec, dotProduct, A] using h1
  refine AlgHom.ext fun q => ?_
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine TrivSqZeroExt.ext (hfst _) ?_
  have h1 := hE0 g
  rw [hE, hd] at h1
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero] at h1
  exact (sub_eq_zero.1 h1).symm
end GlobalTheory.NoTangent
