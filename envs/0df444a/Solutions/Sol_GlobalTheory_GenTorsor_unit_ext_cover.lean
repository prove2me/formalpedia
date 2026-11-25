-- Prove2me | solution 1 for GlobalTheory.GenTorsor.unit_ext_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:50:15.534294+00:00
-- url     : https://prove2.me/submissions/17c5f788-7f72-476d-9536-d56d4d9ba3af

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover
import Theorems.Thm_GlobalTheory_GenTorsor_pb_res
import Theorems.Thm_GlobalTheory_GenTorsor_pb_bijective
import Theorems.Thm_GlobalTheory_GenTorsor_unit_ext_opens
import Theorems.Thm_GlobalTheory_GenTorsor_le_iSup_range
import Theorems.Thm_GlobalTheory_GenTorsor_preimage_inf_range

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
variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]
namespace GlobalTheory.GenTorsor
theorem _root_.solution (hc : ∀ x : X, ∃ i y, a i y = x) {V : X.Opens} {u v : Γ(X, V)ˣ}
    (h : ∀ i, pb (a i) V _ le_rfl u = pb (a i) V _ le_rfl v) : u = v := by
  refine unit_ext_opens _ (fun i => inf_le_left) (le_iSup_range a hc V) fun i => ?_
  apply (pb_bijective (a i) inf_le_right (preimage_inf_range a i V)).1
  rw [pb_res, pb_res]
  exact h i
end GlobalTheory.GenTorsor
