-- Prove2me | solution 1 for GlobalTheory.T.local_primitive_vector_compact_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:00:50.748695+00:00
-- url     : https://prove2.me/submissions/bf4a8702-e91b-49d4-8ed3-44abf2ceb900

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescaleStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_exists_compact_unimodular_vectors_mod_units


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (v : HeightOneSpectrum (𝓞 F)), ∃ Ω : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact Ω ∧ ∀ y : Fin 1 → Fin M → Fv F v ⊗[F] E, (∃ z : Fin M → Fv F v ⊗[F] E, z ⬝ᵥ y 0 = 1) → ∃ (a : (Fv F v ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Fv F v ⊗[F] E), (a : Fv F v ⊗[F] E) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : Fv F v ⊗[F] E) • y) 0 = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.PrimV.exists_compact_unimodular_vectors_mod_units | exact GlobalTheory.CompanionTheory.SW.PrimV.exists_compact_unimodular_vectors_mod_units | (intros; apply GlobalTheory.CompanionTheory.SW.PrimV.exists_compact_unimodular_vectors_mod_units <;> assumption)
end _root_.GlobalTheory.T
