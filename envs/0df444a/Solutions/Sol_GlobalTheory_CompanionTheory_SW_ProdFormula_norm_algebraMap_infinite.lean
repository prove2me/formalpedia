-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ProdFormula.norm_algebraMap_infinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:41:17.638802+00:00
-- url     : https://prove2.me/submissions/e63f1401-4a99-4421-9cfd-64fc162a38db

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GlobalUnitScalingHaarProductFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ProdFormula
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.ProdFormula
theorem _root_.solution (a : F) :
    ‖algebraMap F (InfiniteAdeleRing F) a‖ = ∏ w : InfinitePlace F, w a ^ w.mult := by
  rw [InfiniteAdeleRing.norm_def]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  exact InfinitePlace.Completion.norm_coe w _
end GlobalTheory.CompanionTheory.SW.ProdFormula
