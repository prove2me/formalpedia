-- Prove2me | solution 1 for GlobalTheory.GalOfCusp.IsAttached.tempered
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:09:45.867803+00:00
-- url     : https://prove2.me/submissions/87ba226b-a3fa-440d-861e-2400a05e55a3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__TrivialOnInertiaOfUnr_d5f82434e8467b70

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GalOfCusp
open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open scoped Matrix
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)
variable {A}
variable {i : N.Loc} {a : ℕ} {π : A.CG a} {s : ℝ} {r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))}
namespace GlobalTheory.GalOfCusp
namespace IsAttached
theorem _root_.solution (h : IsAttached A i π s r) {w : PlE H} (hw : w ∉ placesOver H.E (N.l i)) :
    A.tempered (A.locG π w) := by
  have := h.pure w hw
  rwa [h.away w hw, A.lpTw_add, show s + (1 - (a : ℝ)) / 2 + (((a : ℝ) - 1) / 2 - s) = 0 by ring,
    A.lpTw_zero] at this
end IsAttached
end GlobalTheory.GalOfCusp
