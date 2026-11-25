-- Prove2me | solution 1 for GlobalTheory.GenTorsor.res_pb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:49:28.525523+00:00
-- url     : https://prove2.me/submissions/4249e77e-3a1d-4bfc-86c1-5f9553db4b74

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
theorem _root_.solution (a : Y ⟶ X) {U : X.Opens} {V W : Y.Opens}
    (h : V ≤ a ⁻¹ᵁ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (pb a U V h x) = pb a U W (le_trans h' h) x :=
  (pb_pb (𝟙 Y) a h h' x).trans (pb_congr (Category.id_comp a) _ _ _)
end GlobalTheory.GenTorsor
