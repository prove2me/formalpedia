-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.cone_ex_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:09.206241+00:00
-- url     : https://prove2.me/submissions/2c646b5f-1a5e-4c38-ac43-06da1f63b88a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_Cx_ex_succ_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.NerveCoh
theorem _root_.solution {A B : Cx R} (f : Hm A B) (k : ℕ) :
    (cone f).Ex (k + 2) ↔ ∀ (a : A.X (k + 2)) (b : B.X (k + 1)), A.d (k + 2) a = 0 →
      f.f (k + 2) a = B.d (k + 1) b →
      ∃ (y : A.X (k + 1)) (z : B.X k), A.d (k + 1) y = a ∧ f.f (k + 1) y - B.d k z = b := by
  rw [Cx.ex_succ_iff]
  refine ⟨fun h a b h1 h2 ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨y, hy⟩ := h (a, b) (Prod.ext h1 (sub_eq_zero.2 h2))
    exact ⟨y.1, y.2, congrArg Prod.fst hy, congrArg Prod.snd hy⟩
  · obtain ⟨y, z, h1, h2⟩ := h x.1 x.2 (congrArg Prod.fst hx) (sub_eq_zero.1 (congrArg Prod.snd hx))
    exact ⟨(y, z), Prod.ext h1 h2⟩
end GlobalTheory.CompanionTheory.NerveCoh
