-- Prove2me | solution 1 for GlobalTheory.PDivGroup.SemiHom.rig_rigOfOmega
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:14.046733+00:00
-- url     : https://prove2.me/submissions/7d0d83d8-1166-44b2-8669-03e28d246696

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective

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
theorem _root_.solution (w : G.omega) : s.rig (G.rigOfOmega w) = G'.rigOfOmega (s.omega w) :=
  congrArg G'.rigMk (Prod.ext (map_zero s.cocycles) rfl)
end GlobalTheory.PDivGroup.SemiHom
