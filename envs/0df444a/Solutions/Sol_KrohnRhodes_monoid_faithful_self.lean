-- Prove2me | solution 1 for KrohnRhodes.monoid_faithful_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:56:42.904631+00:00
-- url     : https://prove2.me/submissions/560f1173-56f4-4a23-866f-5cf338b0dacc

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_Foundations_Cayley

set_option autoImplicit true
@[expose] public section
public section
set_option linter.style.show false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
open KrohnRhodes
universe u
variable {M : Type u} [Monoid M] [Finite M]
namespace KrohnRhodes
theorem _root_.solution (N : Type u) [Monoid N] :
    Function.Injective (MulAction.toEndHom (M := N) (α := N)) := by
  intro a b h
  -- `MulAction.toEndHom x` is `(x • ·) = (x * ·)`; evaluate both sides at `1`.
  have h1 : (MulAction.toEndHom (M := N) (α := N) a) (1 : N)
      = (MulAction.toEndHom (M := N) (α := N) b) (1 : N) := by rw [h]
  -- `MulAction.toEndHom x y = x • y = x * y`, so this is `a * 1 = b * 1`.
  show a = b
  have ha : (MulAction.toEndHom (M := N) (α := N) a) (1 : N) = a := by
    show a • (1 : N) = a; rw [smul_eq_mul, mul_one]
  have hb : (MulAction.toEndHom (M := N) (α := N) b) (1 : N) = b := by
    show b • (1 : N) = b; rw [smul_eq_mul, mul_one]
  rw [← ha, ← hb, h1]
end KrohnRhodes
