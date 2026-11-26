-- Prove2me | solution 1 for KrohnRhodes.eq_constEnd_of_R_constEnd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:56:59.765974+00:00
-- url     : https://prove2.me/submissions/de2ce053-3910-4b0b-aac7-e4bf642baf49

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Theorems.Thm_KrohnRhodes_constEnd_mul
public import Theorems.Thm_KrohnRhodes_krasnerKaloujnine_hom_left
attribute [local simp] KrohnRhodes.krasnerKaloujnine_hom_left


attribute [local simp] KrohnRhodes.constEnd_mul

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.show false
open KrohnRhodes
universe u
variable {Q : Type u}
namespace KrohnRhodes
theorem _root_.solution {p : Q} {b : Function.End Q}
    (h : Green.R (constEnd p) b) : b = constEnd p := by
  obtain ⟨s, _t, hs, _ht⟩ := h
  rw [← hs, constEnd_mul]
end KrohnRhodes
