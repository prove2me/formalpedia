-- Prove2me | solution 1 for GlobalTheory.HomCalc.comp_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:52:39.311021+00:00
-- url     : https://prove2.me/submissions/8ee5e42b-b64c-47e8-a2f7-2d9dce4e7bac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CompRel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
theorem _root_.solution {I : NumD.Hom f N N'} {I' : NumD.Hom g N' N''} {a : N.Gt} {b : N'.Gt} {c : N''.Gt} (h : I.Rel a b)
    (h' : I'.Rel b c) : (comp I I').Rel a c := by
  refine ⟨h'.1.trans (congrArg I'.φ h.1), fun χ => ?_⟩
  have u := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (h.2 χ)
  have v := congrArg Additive.ofMul (h'.2 (I.e χ))
  have w : Units.map (g.comp f).toMonoidHom (a.s χ) = Units.map g.toMonoidHom (Units.map f.toMonoidHom (a.s χ)) := rfl
  rw [I.c_eq, h.1] at v
  show c.s (I'.e (I.e χ)) * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _)) =
    _ * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _)) * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _))
  apply Additive.ofMul.injective
  simp only [w, map_mul, ofMul_mul] at u v ⊢
  linear_combination (norm := abel) u + v
end GlobalTheory.HomCalc
