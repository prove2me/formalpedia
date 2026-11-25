-- Prove2me | solution 1 for GlobalTheory.PDivGroup.SemiHom.cocycles_cocycles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:54:36.451147+00:00
-- url     : https://prove2.me/submissions/f4fa32fb-7d8d-4092-a6c3-5681125759cb

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
variable (t : SemiHom τ G'' G') {ρ : O →+* O''} (u : SemiHom ρ G'' G)
  (h : ∀ n a, u.app n a = t.app n (s.app n a))
include h
namespace GlobalTheory.PDivGroup.SemiHom
theorem _root_.solution (c : G.cocycles) : t.cocycles (s.cocycles c) = u.cocycles c :=
  Subtype.ext (funext fun n => (s.app n).two_two _ _ (h n) _)
end GlobalTheory.PDivGroup.SemiHom
