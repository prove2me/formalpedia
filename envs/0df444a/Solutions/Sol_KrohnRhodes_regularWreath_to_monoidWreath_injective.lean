-- Prove2me | solution 1 for KrohnRhodes.regularWreath_to_monoidWreath_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:59.411171+00:00
-- url     : https://prove2.me/submissions/c2c32840-f1c9-4064-a8ce-7f093d49f332

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib.GroupTheory.RegularWreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge

set_option autoImplicit true
@[expose] public section
public section
open KrohnRhodes
universe u
variable (D Q : Type u) [Group D] [Group Q]
namespace KrohnRhodes
theorem _root_.solution :
    Function.Injective (regularWreath_to_monoidWreath D Q) := by
  intro a b hab
  -- From `φ a = φ b` we read off `a.right = b.right` and
  -- `∀ x, a.left (a.right * x) = b.left (b.right * x)`.
  have hbase : a.right = b.right :=
    congrArg WreathProduct.base hab
  have hfunc : ∀ x, a.left (a.right * x) = b.left (b.right * x) := by
    intro x
    have := congrArg (fun w : WreathProduct D Q Q => w.func x) hab
    simpa [regularWreath_to_monoidWreath, regularWreathToMonoidWreathFun] using this
  -- Recover equality of `a.left` and `b.left` by substituting `x = a.right⁻¹ * y`.
  have hleft : a.left = b.left := by
    funext y
    have h := hfunc (a.right⁻¹ * y)
    have hcancel : a.right * (a.right⁻¹ * y) = y := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    rw [hcancel] at h
    have hb : b.right * (a.right⁻¹ * y) = y := by
      rw [hbase, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hb] at h
    exact h
  -- Conclude with the structure extensionality lemma.
  exact RegularWreathProduct.ext hleft hbase
end KrohnRhodes
