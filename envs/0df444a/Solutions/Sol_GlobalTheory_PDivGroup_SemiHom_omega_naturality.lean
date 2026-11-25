-- Prove2me | solution 1 for GlobalTheory.PDivGroup.SemiHom.omega_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:15:19.516808+00:00
-- url     : https://prove2.me/submissions/a843820e-a976-4d6e-bce0-c552b14a7228

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
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
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup.SemiHom
theorem _root_.solution (s' : SemiHom σ H' H) (f : G ⟶ H) (f' : G' ⟶ H')
    (h : ∀ n a, s.app n (f.app n a) = f'.app n (s'.app n a)) (w : H.omega) :
    s.omega (omegaMap G H f w) = omegaMap G' H' f' (s'.omega w) := by
  rw [← ofHom_omega, ← ofHom_omega]
  exact ((ofHom f).omega_omega s (s.comp (ofHom f)) (fun _ _ => rfl) w).trans
    (s'.omega_omega (ofHom f') _ h w).symm
end GlobalTheory.PDivGroup.SemiHom
