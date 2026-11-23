-- Prove2me | solution 1 for GlobalTheory.GenTorsor.pb_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:20.760156+00:00
-- url     : https://prove2.me/submissions/5c3ae2ca-07da-4324-b91b-78ac94a4dc56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover
import Theorems.Thm_GlobalTheory_GenTorsor_pb_pb
import Theorems.Thm_GlobalTheory_GenTorsor_pb_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenTorsor
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.GenTorsor
theorem _root_.solution (a : Y ⟶ X) {U V : X.Opens} {W : Y.Opens}
    (h : V ≤ U) (h' : W ≤ a ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    pb a V W h' (res h x) = pb a U W (h'.trans (a.preimage_mono h)) x :=
  (pb_pb a (𝟙 X) h h' x).trans (pb_congr (Category.comp_id a) _ _ _)
end GlobalTheory.GenTorsor
