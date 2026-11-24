-- Prove2me | solution 1 for GlobalTheory.ThetaFn.exists_isPullConst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:44:59.234706+00:00
-- url     : https://prove2.me/submissions/8f9a3827-2208-41f6-804f-f618ca4e4ce2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Theorems.Thm_GlobalTheory_ThetaFn_hermForm_pull
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_mem_pairChart_iff
import Theorems.Thm_GlobalTheory_ThetaFn_exists_fn_of_isGen
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_exists_chart
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules
import Theorems.Thm_GlobalTheory_ThetaFn_IsFnAt_differentiable
import Theorems.Thm_GlobalTheory_ThetaFn_IsFnT_differentiable
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_add_period
import Theorems.Thm_GlobalTheory_appellHumbert_trivial_of_nowhere_vanishing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
namespace GlobalTheory.ThetaFn
theorem _root_.solution (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (hAH : u.IsAH Hm χ) {m : T ⊗ A ⟶ A} {Φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hΦ : ∀ z, exAt u p z ≫ m.left = (u.ex (Φ z)).left) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen) :
    (∀ z w, (b : ℂ) * hermForm Hm (Φ z) (Φ w) = a * hermForm Hm z w) ∧
      (∀ l : u.Λ, χ ⟨Φ l, map_mem_period hΦ l.2⟩ ^ b = χ l ^ a) ∧
      ∃ c : ℂ, c ≠ 0 ∧ IsPullConst u p Φ a b α c := by
  obtain ⟨r, hr, hne, hrj⟩ := exists_fn_of_isGen hL Φ.toContinuousLinearMap.differentiable hΦ hα
  have hχ : ∀ l, χ l ≠ 0 := fun l h0 => by simpa [h0] using hAH.2.2.1 l
  set B : Matrix (Fin g) (Fin g) ℂ := (a : ℂ) • Hm - (b : ℂ) • ((LinearMap.toMatrix' Φ).transpose *
    Hm * (LinearMap.toMatrix' Φ).transpose.conjTranspose) with hB
  have hBf : ∀ z w, hermForm B z w = a * hermForm Hm z w - b * hermForm Hm (Φ z) (Φ w) := by
    intro z w
    rw [← hermForm_pull]
    simp only [hB, hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
  have hBh : B.IsHermitian := by
    have h2 := Matrix.isHermitian_mul_mul_conjTranspose (LinearMap.toMatrix' Φ).transpose hAH.1
    rw [hB, Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_smul, h2.eq, hAH.1.eq, star_intCast, star_intCast]
  haveI := u.discrete
  obtain ⟨k1, k2, k3⟩ := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full B
    (fun l => χ l ^ a / χ ⟨Φ l, map_mem_period hΦ l.2⟩ ^ b) r hBh
    (fun l => by rw [norm_div, norm_zpow, norm_zpow, hAH.2.2.1, hAH.2.2.1]; simp) hr hne
    (fun l z => by
      obtain ⟨i, hi⟩ := exists_chart u valueRules hL z
      obtain ⟨i', hi'⟩ := exists_chart u valueRules hL (Φ z)
      have hj := (exAt_mem_pairChart_iff (hΦ z) ![i, i']).2 ⟨hi, hi'⟩
      have hj' := hj
      rw [← exAt_add_period u p z l l.2] at hj'
      rw [hrj _ _ hj', hrj _ _ hj, exAt_add_period u p z l l.2]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.coe_coe,
        LinearMap.coe_toContinuousLinearMap']
      rw [hAH.2.2.2 l i z hi, hAH.2.2.2 ⟨Φ l, map_mem_period hΦ l.2⟩ i' (Φ z) hi', map_add,
        hBf, hBf]
      have n1 := zpow_ne_zero a (hχ l)
      have n2 := zpow_ne_zero b (hχ ⟨Φ l, map_mem_period hΦ l.2⟩)
      simp only [mul_zpow, zpow_neg, ← Complex.exp_int_mul, hermForm]
      set E0 := (Real.pi : ℂ) * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) with hE0
      set E1 := (Real.pi : ℂ) * (Φ z ⬝ᵥ Hm.mulVec (star (Φ l))) +
        Real.pi / 2 * (Φ l ⬝ᵥ Hm.mulVec (star (Φ l))) with hE1
      have he : ∀ x : ℂ, x = a * E0 - b * E1 →
          Complex.exp x = Complex.exp (a * E0) / Complex.exp (b * E1) := fun x hx => by
        rw [hx, Complex.exp_sub]
      rw [he _ (by rw [hE0, hE1]; ring)]
      have n3 := Complex.exp_ne_zero (a * E0)
      have n4 := Complex.exp_ne_zero (b * E1)
      field_simp)
  refine ⟨fun z w => ?_, fun l => ?_, r 0, hne 0, fun j z hj => ?_⟩
  · have h := hBf z w
    rw [k1] at h
    simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero] at h ⊢
    exact (sub_eq_zero.1 h.symm).symm
  · exact ((div_eq_one_iff_eq (zpow_ne_zero b (hχ _))).1 (k2 l)).symm
  · have n := zpow_ne_zero a (u.fr_ne _ _ ((exAt_mem_pairChart_iff (hΦ z) j).1 hj).1)
    rw [← k3 z, hrj j z hj, zpow_neg, inv_mul_cancel_right₀ n]
    rfl
end GlobalTheory.ThetaFn
