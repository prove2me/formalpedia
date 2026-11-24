-- Prove2me | solution 1 for GlobalTheory.T.adelic_unitary_group_locally_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:32:30.120231+00:00
-- url     : https://prove2.me/submissions/dc5c22dd-2fc6-48b6-b3bd-eebf2ef48226

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompact
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TopH_topH_props


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalGroup (HA R σ J) ∧ LocallyCompactSpace (HA R σ J) ∧ SecondCountableTopology (HA R σ J) ∧ T2Space (HA R σ J) ∧ BorelSpace (HA R σ J) ∧ ∀ n : ℕ, (Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) => actW R σ J p.1 p.2) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, actW R σ J 1 X = X) ∧ (∀ (g h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), actW R σ J (g * h) X = actW R σ J g (actW R σ J h X)) ∧ ∀ (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), gramR R σ J (actW R σ J h X) = gramR R σ J X := by
  first | exact @GlobalTheory.CompanionTheory.SW.TopH.topH_props | exact GlobalTheory.CompanionTheory.SW.TopH.topH_props | (intros; apply GlobalTheory.CompanionTheory.SW.TopH.topH_props <;> assumption)
end _root_.GlobalTheory.T
