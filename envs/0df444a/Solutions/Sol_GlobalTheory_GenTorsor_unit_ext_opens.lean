-- Prove2me | solution 1 for GlobalTheory.GenTorsor.unit_ext_opens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:11.283668+00:00
-- url     : https://prove2.me/submissions/c24ea918-ed9b-4d4f-8321-fc2fd43ce4f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover

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
theorem _root_.solution {J : Type*} {V : X.Opens} (W : J → X.Opens) (hW : ∀ i, W i ≤ V)
    (hc : V ≤ iSup W) {u v : Γ(X, V)ˣ}
    (h : ∀ i, res (hW i) u = res (hW i) v) : u = v := by
  ext
  exact X.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc _ _
    fun i => congrArg Units.val (h i)
end GlobalTheory.GenTorsor
