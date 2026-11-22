-- Prove2me | solution 1 for IsVecLatHom.of_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:26:01.944344+00:00
-- url     : https://prove2.me/submissions/1997bd4e-73dc-49ac-93b2-78f5cb9306fe

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Hom
public import Theorems.Thm_VecLatHom_isVecLatHom

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} {Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]
open IsVecLatHom
namespace IsVecLatHom
theorem _root_.solution {f : X → Y} (lin : IsLinearMap ℝ f) (abs : ∀ x : X, f |x|
  = |f x|) : IsVecLatHom f :=
  VecLatHom.isVecLatHom (VecLatHom.ofAbs (IsLinearMap.mk' f lin) abs)
end IsVecLatHom
