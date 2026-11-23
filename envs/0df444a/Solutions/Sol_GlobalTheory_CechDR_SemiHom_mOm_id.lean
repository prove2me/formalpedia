-- Prove2me | solution 1 for GlobalTheory.CechDR.SemiHom.mOm_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:36.598954+00:00
-- url     : https://prove2.me/submissions/cf8e6a8f-a4e0-41c6-80c3-10f8efaaf000

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
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
theorem _root_.solution {τ : R →+* R} {β : B →+* B} (h : SemiHom τ β) (e : ∀ b, β b = b) {j : ℕ}
    (x : Om R B j) : h.mOm j x = x := by
  refine Subtype.ext ?_
  rw [coe_mOm]
  induction (x : DR R B) using indDR with
  | h b => simp [e]
  | hd b => simp [e]
  | hm x y hx hy => rw [map_mul, hx, hy]
  | ha x y hx hy => rw [map_add, hx, hy]
end SemiHom
end GlobalTheory.CechDR
