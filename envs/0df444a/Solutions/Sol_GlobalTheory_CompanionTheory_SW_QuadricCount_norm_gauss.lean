-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadricCount.norm_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:08:12.694506+00:00
-- url     : https://prove2.me/submissions/259ce992-34b1-415b-9606-5a9f5748baaf

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricCount_gauss_mul_conj

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
    (hB : B.IsSymm) (hdet : B.det ≠ 0) {M : ℕ} (hM : Fintype.card ι = 2 * M) {t : k}
    (ht : t ≠ 0) : ‖∑ x, ψ (t * quadForm B x)‖ = (Fintype.card k : ℝ) ^ M := by
  have h := gauss_mul_conj ψ hψ h2 hB hdet ht
  rw [Complex.mul_conj', hM] at h
  have h' : ‖∑ x, ψ (t * quadForm B x)‖ ^ 2 = ((Fintype.card k : ℝ) ^ M) ^ 2 := by
    rw [← pow_mul, mul_comm M 2]
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h'
end GlobalTheory.CompanionTheory.SW.QuadricCount
