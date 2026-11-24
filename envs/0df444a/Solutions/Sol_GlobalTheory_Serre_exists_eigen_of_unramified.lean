-- Prove2me | solution 1 for GlobalTheory.Serre.exists_eigen_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:59:58.67964+00:00
-- url     : https://prove2.me/submissions/bd8a4a85-478e-469d-8855-2cb7866bd219

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers
import Theorems.Thm_GlobalTheory_Serre_mulChar_tmul
import Theorems.Thm_GlobalTheory_Serre_exists_elem_of_unramified
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
variable {M : Type*} [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M]
namespace GlobalTheory.Serre
theorem _root_.solution (N : Type*) [AddCommGroup N] [Module R N] [Module O N]
    [Module O' N] [IsScalarTower O R N] [IsScalarTower O' R N] [IsScalarTower O O' N]
    [Algebra.FormallyUnramified R (R ⊗[O] O')] [Algebra.EssFiniteType R (R ⊗[O] O')] :
    ∃ s : N ⊗[O'] M →ₗ[R] N ⊗[O] M, Function.Injective s ∧ ∀ z, z ∈ LinearMap.range s ↔
      ∀ x : O', (Algebra.lsmul O O M x).lTensor N z = algebraMap O' R x • z := by
  obtain ⟨e, he₁, he₂⟩ := exists_elem_of_unramified (mulChar R O O')
  let g : O' →ₐ[O] Module.End R (N ⊗[O] M) :=
    { toFun x := AlgebraTensorModule.lTensor R N (Algebra.lsmul O O M x)
      map_one' := by ext; simp
      map_mul' x y := by ext; simp
      map_zero' := by ext; simp
      map_add' x y := by ext; simp
      commutes' x := by ext; simp }
  let ρ : R ⊗[O] O' →ₐ[R] Module.End R (N ⊗[O] M) :=
    Algebra.TensorProduct.lift (Algebra.ofId R _) g fun r x ↦ Algebra.commute_algebraMap_left _ _
  have hρ : ∀ (r : R) (x : O') z, ρ (r ⊗ₜ x) z = r • (Algebra.lsmul O O M x).lTensor N z :=
    fun r x z ↦ rfl
  have hρe : ∀ (x : O') z, (Algebra.lsmul O O M x).lTensor N (ρ e z) = algebraMap O' R x • ρ e z :=
    fun x z ↦ by
      have := congrArg (fun y ↦ ρ y z) (he₂ (1 ⊗ₜ x))
      simpa only [map_mul, map_smul, Module.End.mul_apply, hρ, one_smul, mulChar_tmul, one_mul,
        LinearMap.smul_apply] using this
  have hρe' : ∀ (x : O') z, ρ e ((Algebra.lsmul O O M x).lTensor N z) = algebraMap O' R x • ρ e z :=
    fun x z ↦ by
      have := congrArg (fun y ↦ ρ y z) ((mul_comm _ _).trans (he₂ (1 ⊗ₜ x)))
      simpa only [map_mul, map_smul, Module.End.mul_apply, hρ, one_smul, mulChar_tmul, one_mul,
        LinearMap.smul_apply] using this
  let s : N ⊗[O'] M →ₗ[R] N ⊗[O] M := AlgebraTensorModule.lift
    { toFun n :=
        { toFun m := ρ e (n ⊗ₜ m)
          map_add' m m' := by rw [tmul_add, map_add]
          map_smul' x m := (hρe' x (n ⊗ₜ m)).trans (algebraMap_smul R x _) }
      map_add' n n' := LinearMap.ext fun m ↦ (congrArg (ρ e) (add_tmul n n' m)).trans (map_add _ _ _)
      map_smul' r n := LinearMap.ext fun m ↦ map_smul (ρ e) r (n ⊗ₜ m) }
  let q : N ⊗[O] M →ₗ[R] N ⊗[O'] M := mapOfCompatibleSMul O' O R N M
  have hq : ∀ y z, q (ρ y z) = mulChar R O O' y • q z := fun y z ↦ by
    induction y with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy', add_smul]
    | tmul r x =>
      induction z with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, hz, hz', smul_add]
      | tmul n m => simp [hρ, q, mul_smul]
  have hqs : ∀ z, q (s z) = z := fun z ↦ by
    induction z with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul n m => exact (hq e (n ⊗ₜ m)).trans (by rw [he₁, one_smul]; rfl)
  have hsq : ∀ z, s (q z) = ρ e z := fun z ↦ by
    induction z with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul n m => rfl
  refine ⟨s, Function.LeftInverse.injective hqs, fun z ↦ ⟨?_, fun hz ↦ ⟨q z, ?_⟩⟩⟩
  · rintro ⟨z, rfl⟩ x
    rw [← hqs z, hsq, hρe]
  · have : ∀ y, ρ y z = mulChar R O O' y • z := fun y ↦ by
      induction y with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy', add_smul]
      | tmul r x => rw [hρ, hz, mulChar_tmul, mul_smul]
    rw [hsq, this, he₁, one_smul]
end GlobalTheory.Serre
