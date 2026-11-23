-- Prove2me | solution 1 for GlobalTheory.LGrp.modulus_measure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:03.464838+00:00
-- url     : https://prove2.me/submissions/b6cb5258-4723-4ed5-a01a-85d22ca50ea2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
variable [IsTopologicalGroup G]
variable [LocallyCompactSpace G]
namespace GlobalTheory.LGrp
theorem _root_.solution (U : Subgroup G) (hU : IsClosed (U : Set G)) [MeasurableSpace U] [BorelSpace U]
    (μ : Measure U) [μ.IsHaarMeasure] [μ.Regular] (g : Subgroup.normalizer (U : Set G)) (X : Set U) :
    μ (conjAut U g '' X) = modulus U hU g * μ X := by
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  have h := mulEquivHaarChar_smul_preimage μ (X := conjAut U g '' X) (conjAut U g)
  rw [Set.preimage_image_eq _ (conjAut U g).injective] at h
  have e : modulus U hU g = mulEquivHaarChar (conjAut U g) := by
    borelize ↥U
    rfl
  rw [← h, e]; rfl
end GlobalTheory.LGrp
