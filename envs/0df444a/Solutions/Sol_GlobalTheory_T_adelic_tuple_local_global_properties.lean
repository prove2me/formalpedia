-- Prove2me | solution 1 for GlobalTheory.T.adelic_tuple_local_global_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:02:50.045948+00:00
-- url     : https://prove2.me/submissions/ee7b51c1-435b-4fba-b012-7d524ecab5f5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalPropertiesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_glue_main


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ X Y : Fin n → Fin M → AF F ⊗[F] E, projInf X = projInf Y → (∀ v, projV v (projFin X) = projV v (projFin Y)) → X = Y) ∧ (∀ X : Fin n → Fin M → AF F ⊗[F] E, ∀ᶠ v in Filter.cofinite, projV v (projFin X) ∈ latV b v) ∧ (∀ (Xinf : Fin n → Fin M → Ainf F ⊗[F] E) (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E), (∀ᶠ v in Filter.cofinite, Xv v ∈ latV b v) → ∃ X : Fin n → Fin M → AF F ⊗[F] E, projInf X = Xinf ∧ ∀ v, projV v (projFin X) = Xv v) ∧ ∀ (Cinf : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), IsCompact Cinf → (∀ v, IsCompact (Cv v)) → (∀ᶠ v in Filter.cofinite, Cv v ⊆ latV b v) → IsCompact {X : Fin n → Fin M → AF F ⊗[F] E | projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} := by
  first | exact @GlobalTheory.CompanionTheory.SW.Glue.glue_main | exact GlobalTheory.CompanionTheory.SW.Glue.glue_main | (intros; apply GlobalTheory.CompanionTheory.SW.Glue.glue_main <;> assumption)
end _root_.GlobalTheory.T
