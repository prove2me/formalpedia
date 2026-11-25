-- Prove2me | solution 1 for GlobalTheory.T.haar_measure_nonunits_null
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:11:42.752817+00:00
-- url     : https://prove2.me/submissions/4a2b1de6-e8d3-4af4-8212-33bc9735d05d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HaarMeasureNonunitsNull
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureNonunitsNull
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_NullV_null_nonunits


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 ∧ μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) X)} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.NullV.null_nonunits | exact GlobalTheory.CompanionTheory.SW.NullV.null_nonunits | (intros; apply GlobalTheory.CompanionTheory.SW.NullV.null_nonunits <;> assumption)
end _root_.GlobalTheory.T
