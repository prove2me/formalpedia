-- Prove2me | solution 1 for GlobalTheory.CechDR.SemiHom.mDR_dDR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:24:38.544826+00:00
-- url     : https://prove2.me/submissions/30b67af6-b410-409e-82fe-45ef89afb041

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mDR_sgn

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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
variable {R R' R'' B B' B'' : Type} [CommRing R] [CommRing B] [Algebra R B]
  [CommRing R'] [CommRing B'] [Algebra R' B'] [CommRing R''] [CommRing B''] [Algebra R'' B'']
variable {σ : R →+* R'} {α : B →+* B'}
namespace GlobalTheory.CechDR
namespace SemiHom
theorem _root_.solution (h : SemiHom σ α) (x : DR R B) : h.mDR (dDR R B x) = dDR R' B' (h.mDR x) := by
  induction x using indDR with
  | h b => simp
  | hd b => simp
  | hm x y hx hy => simp [dDR_mul, h.mDR_sgn, hx, hy]
  | ha x y hx hy => simp [hx, hy]
end SemiHom
end GlobalTheory.CechDR
