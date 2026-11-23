-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.algebraMap_germ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:52.438126+00:00
-- url     : https://prove2.me/submissions/f29d696d-276b-4a80-aafa-cc7788c4506f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution {U : X.Opens} {x : X} (hx : x ∈ U) (h : genericPoint X ∈ U)
    (s : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) =
      X.presheaf.germ U _ h s :=
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  Scheme.algebraMap_germ_eq_germToFunctionField X hx s
end GlobalTheory.ExtendLineBundle
