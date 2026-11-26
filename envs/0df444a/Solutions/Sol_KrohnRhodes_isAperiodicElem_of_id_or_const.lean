-- Prove2me | solution 1 for KrohnRhodes.isAperiodicElem_of_id_or_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:49.304959+00:00
-- url     : https://prove2.me/submissions/a1fe10ab-a38c-4208-9899-34f2b7bd931d

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Theorems.Thm_KrohnRhodes_constEnd_mul
public import Theorems.Thm_KrohnRhodes_eq_constEnd_of_R_constEnd
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
theorem _root_.solution
    (S : Submonoid (Function.End Q))
    (hS : ∀ t ∈ S, t = 1 ∨ IsConstEnd t) :
    ∀ a b : S,
      ((∃ s t : S, s * a = b ∧ t * b = a) ∧
       (∃ s t : S, a * s = b ∧ b * t = a)) → a = b := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨_hLpair, hRpair⟩
  obtain ⟨⟨sR, _⟩, ⟨tR, _⟩, hsaR, htbR⟩ := hRpair
  apply Subtype.ext
  show a = b
  -- The underlying R-relation in `Function.End Q`.
  have hR : Green.R a b :=
    ⟨sR, tR, congrArg Subtype.val hsaR, congrArg Subtype.val htbR⟩
  rcases hS a ha with haId | haC
  · -- `a = 1`.  Use `R 1 b`: `b * tR = 1` (with `tR ∈ Function.End Q`).
    rcases hS b hb with hbId | hbC
    · rw [haId, hbId]
    · -- `b = constEnd q`; then `b * tR = constEnd q` but also `= 1`.
      obtain ⟨q, hbq⟩ := hbC
      obtain ⟨_s, t, _hs, ht⟩ := hR
      -- `ht : b * t = a = 1`; with `b = constEnd q`, `constEnd q * t = constEnd q`.
      rw [hbq, constEnd_mul, haId] at ht
      -- `constEnd q = 1` ⟹ `Q` subsingleton.
      have : Subsingleton Q := by
        refine ⟨fun x y => ?_⟩
        -- `congrFun ht x : constEnd q x = (1 : Function.End Q) x`, i.e. `q = x`.
        have hx : q = x := congrFun ht x
        have hy : q = y := congrFun ht y
        rw [← hx, ← hy]
      -- `Q` subsingleton ⟹ all transformations of `Q` are equal.
      funext x
      exact Subsingleton.elim _ _
  · -- `a` is a constant: `R a b` forces `b = a`.
    obtain ⟨p, hap⟩ := haC
    rw [hap]
    rw [hap] at hR
    exact (eq_constEnd_of_R_constEnd hR).symm
end KrohnRhodes
