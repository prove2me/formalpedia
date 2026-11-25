-- Prove2me | solution 1 for GlobalTheory.PDivGroup.SemiHom.rig_rig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:11:32.682377+00:00
-- url     : https://prove2.me/submissions/b8b7d22d-16cf-42b6-95e8-f7dc555f1fe0

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
import Theorems.Thm_GlobalTheory_PDivGroup_SemiHom_cocycles_cocycles
import Theorems.Thm_GlobalTheory_PDivGroup_SemiHom_omega_omega

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
variable (t : SemiHom τ G'' G') {ρ : O →+* O''} (u : SemiHom ρ G'' G)
  (h : ∀ n a, u.app n a = t.app n (s.app n a))
include h
namespace GlobalTheory.PDivGroup.SemiHom
theorem _root_.solution (x : G.RigExt) : t.rig (s.rig x) = u.rig x := by
  obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  exact congrArg G''.rigMk (Prod.ext (s.cocycles_cocycles t u h c) (s.omega_omega t u h w))
end GlobalTheory.PDivGroup.SemiHom
