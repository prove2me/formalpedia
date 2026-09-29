-- Prove2me | solution 1 for MilnorConjecture.milnor_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-25T12:06:00.898435+00:00
-- url     : https://prove2.me/submissions/3fe0f58e-67e6-477d-beb3-d4417d5998ad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol
import Theorems.Thm_MilnorConjecture_galoisSymbol_update_mul
import Theorems.Thm_MilnorConjecture_galoisSymbol_steinberg
import Theorems.Thm_MilnorConjecture_galoisSymbol_generate
import Theorems.Thm_MilnorConjecture_norm_residue_ker_le

open MilnorConjecture
open scoped TensorProduct

theorem solution (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ) :
    ∃ φ : MilnorK F n →+ H F n,
      (∀ a : Fin n → Fˣ, φ (symbol a) = galoisSymbol a) ∧
      Function.Surjective φ ∧
      ∀ x : MilnorK F n, φ x = 0 ↔ ∃ y : MilnorK F n, x = 2 • y := by
  -- the Galois symbol, viewed on `Additive Fˣ`
  let g : (Fin n → Additive Fˣ) → H F n := fun a ↦ galoisSymbol (fun l ↦ Additive.toMul (a l))
  have hadd : ∀ (a : Fin n → Additive Fˣ) (i : Fin n) (x y : Additive Fˣ),
      g (Function.update a i (x + y)) = g (Function.update a i x) + g (Function.update a i y) := by
    intro a i x y
    have key := galoisSymbol_update_mul F n (fun l ↦ Additive.toMul (a l)) i
      (Additive.toMul x) (Additive.toMul y)
    have e : ∀ z : Additive Fˣ, (fun l ↦ Additive.toMul (Function.update a i z l)) =
        Function.update (fun l ↦ Additive.toMul (a l)) i (Additive.toMul z) := by
      intro z; funext l
      by_cases hl : l = i
      · subst hl; simp
      · simp [Function.update_of_ne hl]
    simp only [g, e]
    exact key
  -- in each slot, `g` is an additive homomorphism
  let slot : (Fin n → Additive Fˣ) → Fin n → Additive Fˣ →+ H F n := fun a i ↦
    AddMonoidHom.mk' (fun z ↦ g (Function.update a i z)) (hadd a i)
  let M : MultilinearMap ℤ (fun _ : Fin n ↦ Additive Fˣ) (H F n) :=
    { toFun := g
      map_update_add' := fun a i x y ↦ by
        obtain rfl : ‹DecidableEq (Fin n)› = instDecidableEqFin n := Subsingleton.elim _ _
        exact hadd a i x y
      map_update_smul' := fun a i c x ↦ by
        obtain rfl : ‹DecidableEq (Fin n)› = instDecidableEqFin n := Subsingleton.elim _ _
        exact (slot a i).map_zsmul c x }
  let L : (⨂[ℤ]^n (Additive Fˣ)) →ₗ[ℤ] H F n := PiTensorProduct.lift M
  have hL : steinberg F n ≤ LinearMap.ker L := by
    rw [steinberg, Submodule.span_le]
    rintro x ⟨a, i, j, hij, h, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, L, PiTensorProduct.lift.tprod]
    exact galoisSymbol_steinberg F n a i j hij h
  let φ : MilnorK F n →+ H F n := ((steinberg F n).liftQ L hL).toAddMonoidHom
  have hφ : ∀ a : Fin n → Fˣ, φ (symbol a) = galoisSymbol a := by
    intro a
    simp [φ, symbol, L, M, g]
  refine ⟨φ, hφ, ?_, ?_⟩
  · -- surjectivity: the image contains all Galois symbols, which generate
    intro h
    have hmem : h ∈ AddSubgroup.closure (Set.range (galoisSymbol (F := F) (n := n))) := by
      rw [galoisSymbol_generate F n]; trivial
    have hle : AddSubgroup.closure (Set.range (galoisSymbol (F := F) (n := n))) ≤ φ.range := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      exact ⟨symbol a, hφ a⟩
    exact hle hmem
  · intro x
    constructor
    · exact norm_residue_ker_le F n φ hφ x
    · rintro ⟨y, rfl⟩
      rw [map_nsmul]
      have : (2 : ℕ) • φ y = ((2 : ℕ) : ZMod 2) • φ y := by rw [Nat.cast_smul_eq_nsmul]
      rw [this, show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_smul]
