-- Prove2me | solution 1 for IsVecLatHom.of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:25:01.628656+00:00
-- url     : https://prove2.me/submissions/f945e631-e167-42e5-b875-daa47e28a4d9

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Hom
public import Theorems.Thm_uniqueness_posPart


set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} {Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]
open IsVecLatHom
namespace IsVecLatHom
theorem _root_.solution {f : X → Y} (lin : IsLinearMap ℝ f)
    (disj : ∀ x y : X, x ⊓ y = 0 → f x ⊓ f y = 0) : IsVecLatHom f := by
  have fNeg : ∀ x : X, f (-x) = -f x := fun x => by
    have h := lin.map_smul (-1 : ℝ) x; rwa [neg_one_smul, neg_one_smul] at h
  have fSub : ∀ x y : X, f (x - y) = f x - f y := fun x y => by
    rw [sub_eq_add_neg, lin.map_add, fNeg, ← sub_eq_add_neg]
  have fPosPart : ∀ c : X, f c⁺ = (f c)⁺ := fun c =>
    uniqueness_posPart (f c) (by rw [← fSub, posPart_sub_negPart])
      (disj c⁺ c⁻ (posPart_inf_negPart_eq_zero c))
  have fSup : ∀ a b : X, f (a ⊔ b) = f a ⊔ f b := fun a b => by
    rw [sup_eq_add_posPart_sub, lin.map_add, fPosPart, fSub, ← sup_eq_add_posPart_sub]
  exact { lin with
    map_sup' := fSup
    map_inf' := fun a b => by
      have h := fSup (-a) (-b)
      rw [← neg_inf] at h
      rw [fNeg, fNeg a, fNeg b, ← neg_inf] at h
      exact neg_inj.mp h }
end IsVecLatHom
