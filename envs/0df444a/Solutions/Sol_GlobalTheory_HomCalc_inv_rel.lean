-- Prove2me | solution 1 for GlobalTheory.HomCalc.inv_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:49:41.667286+00:00
-- url     : https://prove2.me/submissions/ad40cbff-bb85-49f8-b1fc-10a2602c90c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CompRel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Ex
noncomputable section
open GlobalTheory GlobalTheory.HomCalc
variable {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O''] {f : O →+* O'} {g : O' →+* O''}
  {N : NumD O} {N' : NumD O'} {N'' : NumD O''}
namespace GlobalTheory.HomCalc
theorem _root_.solution {M M' : NumD O} {I : NumD.Iso M' M} {a : M'.Gt} {b : M.Gt} (h : I.Rel a b) : (inv I).Rel b a := by
  refine ⟨(I.φ.symm_apply_eq.2 h.1).symm, fun χ => ?_⟩
  obtain ⟨χ, rfl⟩ := I.e.surjective χ
  have u := congrArg Additive.ofMul (h.2 χ)
  show a.s (I.e.symm _) * (I.h (I.φ.symm _))⁻¹ = b.s _ * (I.h (I.φ.symm _))⁻¹ * (I.h (I.φ.symm _))⁻¹
  rw [AddEquiv.symm_apply_apply, I.c_eq, h.1, ← map_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, MulEquiv.symm_apply_apply] at u ⊢
  linear_combination (norm := abel) -u
end GlobalTheory.HomCalc
