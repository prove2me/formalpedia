-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Pack.norm_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:30.831348+00:00
-- url     : https://prove2.me/submissions/73ba3b58-59c9-4a33-9098-5d0290c3781c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBoundStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicBoxLatticeCountRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Pack
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.Pack
theorem _root_.solution (hF : IsTotallyReal F) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ‖coord hF b X‖ = sizeTup b (projInf X) := by
  rw [PiLp.norm_eq_of_L1]
  simp only [sizeTup, sizeInf, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun v _ => ?_
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal v)).norm_map_of_map_zero
    (map_zero _) _
end GlobalTheory.CompanionTheory.SW.Pack
