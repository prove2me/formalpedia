-- Prove2me | solution 1 for GlobalTheory.PDivGroup.SemiHom.rig_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:10:45.062862+00:00
-- url     : https://prove2.me/submissions/fd8a39e6-49e0-479b-afff-081ac8954340

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
import Theorems.Thm_GlobalTheory_PDivGroup_SemiHom_rig_rig
import Theorems.Thm_GlobalTheory_PDivGroup_SemiHom_comp_rig

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
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup.SemiHom
theorem _root_.solution (s' : SemiHom σ H' H) (f : G ⟶ H) (f' : G' ⟶ H')
    (h : ∀ n a, s.app n (f.app n a) = f'.app n (s'.app n a)) (x : H.RigExt) :
    s.rig (rigExtMap f x) = rigExtMap f' (s'.rig x) := by
  rw [← ofHom_rig, ← ofHom_rig, ← comp_rig]
  exact (s'.rig_rig (ofHom f') _ h x).symm
end GlobalTheory.PDivGroup.SemiHom
