-- Prove2me | solution 1 for GlobalTheory.KuennethOne.isAffineOpen_inf_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:33:49.114876+00:00
-- url     : https://prove2.me/submissions/0df87093-039a-476e-a3bf-0b3c362f6111

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KuennethOne
namespace GlobalTheory.KuennethOne
theorem _root_.solution {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S)
    [IsSeparated f] (U U' : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen U') :
    IsAffineOpen (U ⊓ U') := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  exact hU.inf hU'
end GlobalTheory.KuennethOne
