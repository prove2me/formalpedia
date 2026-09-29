-- Prove2me | solution 1 for LinearIndependent.linearMap_baseChange_of_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/91d0657f-3179-5261-9233-6733e6943366

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearIndependent_linearMap_baseChange_of_int

open scoped TensorProduct

namespace FixlFacesA

theorem matrixEquivTensor_symm_smul (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    (n : Type) [Fintype n] [DecidableEq n] (a : A) (x : A ⊗[R] Matrix n n R) :
    (matrixEquivTensor n R A).symm (a • x) = a • (matrixEquivTensor n R A).symm x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b M =>
    rw [TensorProduct.smul_tmul', matrixEquivTensor_apply_symm, matrixEquivTensor_apply_symm,
      smul_eq_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem linearIndependent_matrix_map (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (n : Type) [Fintype n] [DecidableEq n] {ι : Type} (M : ι → Matrix n n R)
    (hM : LinearIndependent R M) :
    LinearIndependent A (fun i => (M i).map (algebraMap R A)) := by
  have h1 : LinearIndependent A (fun i => (1 : A) ⊗ₜ[R] M i) :=
    Module.Flat.linearIndependent_one_tmul hM
  have h2 := h1.map_of_injective_injective id (matrixEquivTensor n R A).symm.toAddEquiv.toAddMonoidHom
    (fun _ h => h) (fun x hx => by simpa using hx)
    (fun a x => by simpa using matrixEquivTensor_symm_smul R A n a x)
  convert h2 using 1
  · funext i
    simp [matrixEquivTensor_apply_symm]
  all_goals first | rfl | exact Subsingleton.elim _ _

end FixlFacesA

open FixlFacesA in

theorem solution (K : Type) [Field K] [CharZero K]
    (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ] {ι : Type}
    (f : ι → Module.End ℤ Λ) (hf : LinearIndependent ℤ f) :
    LinearIndependent K (fun i => ((f i).baseChange K : Module.End K (K ⊗[ℤ] Λ))) := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let bK := Algebra.TensorProduct.basis K b
  refine LinearIndependent.of_comp (LinearMap.toMatrix bK bK).toLinearMap ?_
  have key : ((LinearMap.toMatrix bK bK).toLinearMap ∘ fun i => ((f i).baseChange K : Module.End K (K ⊗[ℤ] Λ)))
      = fun i => (LinearMap.toMatrix b b (f i)).map (algebraMap ℤ K) := by
    funext i
    exact LinearMap.toMatrix_baseChange K (f i) b b
  rw [key]
  have hM : LinearIndependent ℤ (fun i => LinearMap.toMatrix b b (f i)) :=
    hf.map' (LinearMap.toMatrix b b).toLinearMap (LinearEquiv.ker _)
  exact linearIndependent_matrix_map ℤ K _ (fun i => LinearMap.toMatrix b b (f i)) hM

end S_LinearIndependent_linearMap_baseChange_of_int
end P2MW
export P2MW.S_LinearIndependent_linearMap_baseChange_of_int (solution)
