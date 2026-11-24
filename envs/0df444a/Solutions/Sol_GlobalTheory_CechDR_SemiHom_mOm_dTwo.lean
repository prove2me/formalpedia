-- Prove2me | solution 1 for GlobalTheory.CechDR.SemiHom.mOm_dTwo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:40:47.541747+00:00
-- url     : https://prove2.me/submissions/97234aa1-cdbf-4bf3-a3c9-cee03fa3e133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mDR_dDR
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm

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
theorem _root_.solution (h : SemiHom σ α) (x : Om R B 2) : h.mOm 3 (dTwo R B x) = dTwo R' B' (h.mOm 2 x) :=
  Subtype.ext (h.mDR_dDR x)
end SemiHom
end GlobalTheory.CechDR
