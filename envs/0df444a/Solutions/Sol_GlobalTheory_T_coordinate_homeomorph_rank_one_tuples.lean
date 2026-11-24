-- Prove2me | solution 1 for GlobalTheory.T.coordinate_homeomorph_rank_one_tuples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:00:39.708835+00:00
-- url     : https://prove2.me/submissions/277cc2ce-20b1-468a-8f1b-f9a0461eb629

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHomeomorphRankOneTuples
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHomeomorphRankOneTuplesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_coordMap_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ M : ℕ, IsHomeomorph (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) ∧ MeasurableEmbedding (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) ∧ (coordW R b lam 1 M).map (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) = Measure.pi fun _ : Fin M × Fin d => lam := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.coordMap_one | exact GlobalTheory.CompanionTheory.SW.BB.coordMap_one | (intros; apply GlobalTheory.CompanionTheory.SW.BB.coordMap_one <;> assumption)
end _root_.GlobalTheory.T
