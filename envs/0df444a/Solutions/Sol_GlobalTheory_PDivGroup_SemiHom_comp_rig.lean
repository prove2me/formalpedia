-- Prove2me | solution 1 for GlobalTheory.PDivGroup.SemiHom.comp_rig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:46:11.039197+00:00
-- url     : https://prove2.me/submissions/60c497e6-32d9-4b15-bafb-c430a1a0eaa7

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
import Theorems.Thm_GlobalTheory_PDivGroup_SemiHom_rig_rig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
open GlobalTheory.PDivGroup.SemiHom
variable {σ : O →+* O'} {τ : O' →+* O''} {G H : PDivGroup p O} {G' H' : PDivGroup p O'}
  {G'' : PDivGroup p O''}
variable (s : SemiHom σ G' G)
namespace GlobalTheory.PDivGroup.SemiHom
theorem _root_.solution (t : SemiHom τ G'' G') (x : G.RigExt) : (t.comp s).rig x = t.rig (s.rig x) :=
  (s.rig_rig t _ (fun _ _ => rfl) x).symm
end GlobalTheory.PDivGroup.SemiHom
