-- Prove2me | solution 1 for GlobalTheory.CechDR.SemiHom.mOm_dOm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:43:50.797806+00:00
-- url     : https://prove2.me/submissions/377a0e41-7210-410c-80d6-d29f8f2e709d

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
theorem _root_.solution (h : SemiHom σ α) {j : ℕ} (x : Om R B j) :
    h.mOm (j + 1) (dOm R B j x) = dOm R' B' j (h.mOm j x) := Subtype.ext (h.mDR_dDR x)
end SemiHom
end GlobalTheory.CechDR
