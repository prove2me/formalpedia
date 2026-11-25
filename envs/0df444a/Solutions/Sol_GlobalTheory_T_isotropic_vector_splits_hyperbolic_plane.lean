-- Prove2me | solution 1 for GlobalTheory.T.isotropic_vector_splits_hyperbolic_plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:20:37.104598+00:00
-- url     : https://prove2.me/submissions/48b33f18-72d1-49c2-aaf8-482b75c97b05

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IsotropicVectorSplitsHyperbolicPlane
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IsotropicVectorSplitsHyperbolicPlaneStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_splitHyp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin M → E, x ≠ 0 → hE σ J x x = 0 → ∃ (M₁ : ℕ) (hM : M = M₁ + 2) (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧ hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * (hM ▸ J) * (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  first | exact @GlobalTheory.CompanionTheory.SW.HypSplit.splitHyp | exact GlobalTheory.CompanionTheory.SW.HypSplit.splitHyp | (intros; apply GlobalTheory.CompanionTheory.SW.HypSplit.splitHyp <;> assumption)
end _root_.GlobalTheory.T
