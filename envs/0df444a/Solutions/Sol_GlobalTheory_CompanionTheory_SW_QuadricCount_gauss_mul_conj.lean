-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadricCount.gauss_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:50:35.722166+00:00
-- url     : https://prove2.me/submissions/4ebe4ac7-ab22-47ec-9d3d-a70e254a4966

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricCount_quadForm_add
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricCount_sum_char_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricCount
open ComplexConjugate
variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.QuadricCount
theorem _root_.solution (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k}
    (hB : B.IsSymm) (hdet : B.det ≠ 0) {t : k} (ht : t ≠ 0) :
    (∑ x, ψ (t * quadForm B x)) * conj (∑ x, ψ (t * quadForm B x)) =
      (Fintype.card k : ℂ) ^ Fintype.card ι := by
  classical
  have inner : ∀ z : ι → k, ∑ y : ι → k, ψ (t * (y ⬝ᵥ (B *ᵥ z))) =
      if z = 0 then (Fintype.card k : ℂ) ^ Fintype.card ι else 0 := by
    intro z
    split_ifs with hz
    · subst hz
      simp
    · have hw : t • (B *ᵥ z) ≠ 0 := by
        intro h
        have h' : B *ᵥ z = 0 := (smul_eq_zero.mp h).resolve_left ht
        exact hz (Matrix.eq_zero_of_mulVec_eq_zero hdet h')
      have := sum_char_dot ψ hψ hw
      simpa [dotProduct_smul, smul_eq_mul] using this
  have step : ∀ y : ι → k, ∑ x, ψ (t * quadForm B x) * conj (ψ (t * quadForm B y)) =
      ∑ z, ψ (t * quadForm B z) * ψ (t * (y ⬝ᵥ (B *ᵥ z))) := by
    intro y
    refine (Fintype.sum_equiv (Equiv.addLeft y) _ _ ?_).symm
    intro z
    rw [Equiv.coe_addLeft, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, quadForm_add h2 hB]
    congr 1
    ring
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm]
  simp_rw [step]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, inner]
  simp [quadForm]
end GlobalTheory.CompanionTheory.SW.QuadricCount
