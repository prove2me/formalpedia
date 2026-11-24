-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadricUnit.gauss_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:26:30.037673+00:00
-- url     : https://prove2.me/submissions/6fb85375-d953-4146-8a84-33da9a1e8961

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardQuadricUnit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricUnit_char_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricUnit_sum_sq_scale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricCount_quadForm_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricUnit
open GlobalTheory.CompanionTheory.SW.QuadricCount
variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.QuadricUnit
theorem _root_.solution (hchar : ringChar k ≠ 2) (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    {B : Matrix ι ι k} (hB : B.IsSymm) (hdet : B.det ≠ 0) {M : ℕ}
    (hM : Fintype.card ι = 2 * M) {t : k} (ht : t ≠ 0) :
    ∑ x, ψ (t * quadForm B x) = ∑ x, ψ (quadForm B x) := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  haveI : Invertible (2 : k) := invertibleOfNonzero h2
  let Q : QuadraticForm k (ι → k) := (2 : k)⁻¹ • Matrix.toQuadraticForm' B
  have hQ : ∀ x, Q x = quadForm B x := by
    intro x
    simp [Q, quadForm, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']
  have hsep : (QuadraticMap.associated (R := k) Q).SeparatingLeft := by
    intro x hx
    have hass : ∀ y, x ⬝ᵥ (B *ᵥ y) = 0 := by
      intro y
      have hxy : QuadraticMap.associatedHom k Q x y = 0 := hx y
      have hyx : QuadraticMap.associatedHom k Q y x = 0 := by
        rw [← QuadraticMap.associated_isSymm k Q x y]
        exact hxy
      have e1 := QuadraticMap.associated_eq_self_apply k Q (x + y)
      have e2 := QuadraticMap.associated_eq_self_apply k Q x
      have e3 := QuadraticMap.associated_eq_self_apply k Q y
      simp only [map_add, LinearMap.add_apply] at e1
      rw [hQ, quadForm_add h2 hB] at e1
      rw [hQ] at e2 e3
      linear_combination e2 + e3 - e1 + hxy + hyx
    have hz : B *ᵥ x = 0 := by
      funext i
      have h3 := hass (Pi.single i 1)
      have hs : x ⬝ᵥ (B *ᵥ (Pi.single i 1)) = (Pi.single i 1 : ι → k) ⬝ᵥ (B *ᵥ x) := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hB.eq, dotProduct_comm]
      rw [hs, single_dotProduct, one_mul] at h3
      exact h3
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet hz
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hsep
  have hsum : ∀ u : k, ∑ x, ψ (u * quadForm B x) = ∏ i, ∑ y : k, ψ ((u * (w i : k)) * (y * y)) := by
    intro u
    calc ∑ x, ψ (u * quadForm B x)
        = ∑ y : Fin (Module.finrank k (ι → k)) → k, ψ (u * ∑ i, (w i : k) * (y i * y i)) := by
          refine Fintype.sum_equiv e.toLinearEquiv.toEquiv _ _ fun x => ?_
          have h3 := e.map_app x
          rw [hQ, QuadraticMap.weightedSumSquares_apply] at h3
          simp only [Units.smul_def, smul_eq_mul] at h3
          rw [← h3]
          rfl
      _ = ∑ y : Fin (Module.finrank k (ι → k)) → k,
            ∏ i, ψ ((u * (w i : k)) * (y i * y i)) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum, char_sum]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [mul_assoc]
      _ = ∏ i, ∑ y : k, ψ ((u * (w i : k)) * (y * y)) := by
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have h1 := hsum 1
  simp only [one_mul] at h1
  rw [hsum t, h1]
  have hsc : ∀ i, ∑ y : k, ψ ((t * (w i : k)) * (y * y)) =
      (quadraticChar k t : ℂ) * ∑ y : k, ψ ((w i : k) * (y * y)) :=
    fun i => sum_sq_scale hchar ψ hψ (w i).ne_zero ht
  simp_rw [hsc]
  have hfr : Fintype.card (Fin (Module.finrank k (ι → k))) = 2 * M := by
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, hM]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hfr, pow_mul]
  have h3 : (quadraticChar k t : ℂ) ^ 2 = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℂ) (quadraticChar_sq_one ht)
  rw [h3, one_pow, one_mul]
end GlobalTheory.CompanionTheory.SW.QuadricUnit
