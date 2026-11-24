-- Prove2me | solution 1 for GlobalTheory.T.adelic_tuple_projections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:30:25.754683+00:00
-- url     : https://prove2.me/submissions/1d16006d-236c-4f7d-ab69-e441e1747cf8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_proj_props


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), Continuous (projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) ∧ Continuous (projFin : (Fin n → Fin M → AF F ⊗[F] E) → _) ∧ (∀ v, Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _)) ∧ (∀ v, IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) ∧ (∀ S, IsOpen (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))) ∧ (∀ X : (Fin n → Fin M → Af F ⊗[F] E), ∀ᶠ v in Filter.cofinite, projV v X ∈ latV b v) ∧ (∀ X Y : (Fin n → Fin M → AF F ⊗[F] E), projInf X = projInf Y → (∀ v, projV v (projFin X) = projV v (projFin Y)) → X = Y) ∧ (∀ (Y : (Fin n → Fin M → Ainf F ⊗[F] E)) (Z : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ᶠ v in Filter.cofinite, Z v ∈ latV b v) → ∃ X : (Fin n → Fin M → AF F ⊗[F] E), projInf X = Y ∧ ∀ v, projV v (projFin X) = Z v) ∧ Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.MeasProj.proj_props | exact GlobalTheory.CompanionTheory.SW.MeasProj.proj_props | (intros; apply GlobalTheory.CompanionTheory.SW.MeasProj.proj_props <;> assumption)
end _root_.GlobalTheory.T
