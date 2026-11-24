-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.hom_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:07:50.079672+00:00
-- url     : https://prove2.me/submissions/6dd9286c-c166-4b2f-8c1a-3ca62f40c15a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_rel_existsUnique
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_Rel_mul
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_rel_io
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_wp_eq
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_txT_eq
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_evT_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.NumD
theorem _root_.solution : ∀ (O O' : Type) [CommRing O] [CommRing O'] (f : O →+* O') (N : NumD O) (N' : NumD O') (I : NumD.Hom f N N'), (∀ g, ∃! g', I.Rel g g') ∧ (∀ g h g' h', I.Rel g g' → I.Rel h h' → I.Rel (g * h) (g' * h')) ∧ (∀ y, I.Rel (N.io y) (N'.io (I.e y))) ∧ (∀ k (p q : N.QT k) (p' q' : N'.QT k), p'.1.1.toAdd = I.e p.1.1.toAdd → I.Rel p.1.2 p'.1.2 → q'.1.1.toAdd = I.e q.1.1.toAdd → I.Rel q.1.2 q'.1.2 → N'.wp p' q' = Units.map f.toMonoidHom (N.wp p q)) ∧ ∀ m, Odd m → ∀ (p : N.QT (m ^ 2)) (p' : N'.QT (m ^ 2)), p'.1.1.toAdd = I.e p.1.1.toAdd → I.Rel p.1.2 p'.1.2 → ∀ χ, N'.txT m p' (I.e χ) = I.lam * f (N.txT m p χ) ∧ ∀ h h', I.Rel h h' → N'.evT m p' h' (I.e χ) = (I.lam * I.h h.b ^ (m ^ 2) : O'ˣ) * f (N.evT m p h χ) :=
  fun _ _ _ _ _ _ _ I => ⟨I.rel_existsUnique, fun _ _ _ _ hg hh => hg.mul hh, I.rel_io,
    fun _ p q p' q' => I.wp_eq p q p' q',
    fun _ hm p p' ep hp χ => ⟨I.txT_eq hm p p' ep hp χ, I.evT_eq hm p p' ep hp χ⟩⟩
end GlobalTheory.Ex.NumD
