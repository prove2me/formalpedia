-- Prove2me | solution 1 for GlobalTheory.T.archimedean_primitive_vector_compact_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:02:48.580678+00:00
-- url     : https://prove2.me/submissions/15bacf62-bfc6-417a-a498-e4ca7500d03e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanPrimitiveVectorCompactRescale
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanPrimitiveVectorCompactRescaleStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimInf_unimodular_mod_units_inf


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), ∃ Ω : Set (Fin 1 → Fin M → Ainf F ⊗[F] E), IsCompact Ω ∧ ∀ y : Fin 1 → Fin M → Ainf F ⊗[F] E, (∃ z : Fin M → Ainf F ⊗[F] E, z ⬝ᵥ y 0 = 1) → ∃ (a : (Ainf F ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Ainf F ⊗[F] E), (a : Ainf F ⊗[F] E) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : Ainf F ⊗[F] E) • y) 0 = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.PrimInf.unimodular_mod_units_inf | exact GlobalTheory.CompanionTheory.SW.PrimInf.unimodular_mod_units_inf | (intros; apply GlobalTheory.CompanionTheory.SW.PrimInf.unimodular_mod_units_inf <;> assumption)
end _root_.GlobalTheory.T
