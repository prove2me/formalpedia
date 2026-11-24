-- Prove2me | solution 1 for GlobalTheory.Serre.exists_elem_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:45:37.352317+00:00
-- url     : https://prove2.me/submissions/37507947-aa1f-4885-94cb-2c780386e801

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers
import Theorems.Thm_GlobalTheory_Serre_mulChar_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Serre.mulChar_tmul

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.Serre
variable {R O O' : Type*} [CommRing R] [CommRing O] [CommRing O'] [Algebra O O'] [Algebra O R]
  [Algebra O' R] [IsScalarTower O O' R]
namespace GlobalTheory.Serre
theorem _root_.solution {A : Type*} [CommRing A] [Algebra R A]
    [Algebra.FormallyUnramified R A] [Algebra.EssFiniteType R A] (χ : A →ₐ[R] R) :
    ∃ e : A, χ e = 1 ∧ ∀ x, x * e = χ x • e := by
  let f : A ⊗[R] A →ₐ[R] A :=
    Algebra.TensorProduct.lift ((Algebra.ofId R A).comp χ) (AlgHom.id R A) fun _ _ ↦ .all _ _
  refine ⟨f (Algebra.FormallyUnramified.elem R A), ?_, fun x ↦ ?_⟩
  · have : ∀ z, χ (f z) = χ (Algebra.TensorProduct.lmul' R z) := fun z ↦ by
      induction z with
      | zero => simp
      | tmul x y => simp [f]
      | add z w hz hw => simp only [map_add, hz, hw]
    rw [this, Algebra.FormallyUnramified.lmul_elem, map_one]
  · simpa [f, Algebra.smul_def] using
      congrArg f (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) x)
end GlobalTheory.Serre
