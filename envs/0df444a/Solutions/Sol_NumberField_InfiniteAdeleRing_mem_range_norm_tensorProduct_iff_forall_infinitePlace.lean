-- Prove2me | solution 1 for NumberField.InfiniteAdeleRing.mem_range_norm_tensorProduct_iff_forall_infinitePlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8b628a08-ad30-5906-8dc2-6da5649557e1

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfiniteAdeleRing_mem_range_norm_tensorProduct_iff_forall_infinitePlace

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace K55

open scoped TensorProduct.RightActions

section general

variable {K L A A' : Type*} [Field K] [CommRing L] [Algebra K L]
  [CommRing A] [Algebra K A] [CommRing A'] [Algebra K A']

theorem rightBasis_apply {ι : Type*} (b : Module.Basis ι K L) (i : ι) :
    TensorProduct.RightActions.Algebra.TensorProduct.basis A b i = b i ⊗ₜ[K] (1 : A) := by
  simp [TensorProduct.RightActions.Algebra.TensorProduct.basis, Module.Basis.map_apply,
    Algebra.TensorProduct.basis_apply]

theorem rightBasis_repr_tmul {ι : Type*} (b : Module.Basis ι K L) (l : L) (a : A) (i : ι) :
    (TensorProduct.RightActions.Algebra.TensorProduct.basis A b).repr (l ⊗ₜ[K] a) i
      = a * algebraMap K A (b.repr l i) := by
  simp [TensorProduct.RightActions.Algebra.TensorProduct.basis,
    Algebra.TensorProduct.basis_repr_tmul]

variable [Module.Finite K L]

theorem norm_map_eq_norm_map (φ : A →ₐ[K] A') (ψ : L ⊗[K] A →ₐ[K] L ⊗[K] A')
    (h : ∀ (l : L) (a : A), ψ (l ⊗ₜ[K] a) = l ⊗ₜ[K] φ a) (t : L ⊗[K] A) :
    φ (Algebra.norm A t) = Algebra.norm A' (ψ t) := by
  classical
  let b := Module.finBasis K L
  let bA := TensorProduct.RightActions.Algebra.TensorProduct.basis A b
  let bA' := TensorProduct.RightActions.Algebra.TensorProduct.basis A' b
  have hrepr : ∀ (y : L ⊗[K] A) (i : Fin (Module.finrank K L)),
      φ (bA.repr y i) = bA'.repr (ψ y) i := by
    intro y i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      simp only [bA, bA']
      rw [h, rightBasis_repr_tmul, rightBasis_repr_tmul, map_mul, AlgHom.commutes]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have hb : ∀ j, ψ (bA j) = bA' j := by
    intro j
    simp only [bA, bA']
    rw [rightBasis_apply, rightBasis_apply, h, map_one]
  rw [Algebra.norm_eq_matrix_det bA, Algebra.norm_eq_matrix_det bA', AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hrepr, map_mul, hb]

end general

section arch

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable def toPlace (v : InfinitePlace K) :
    L ⊗[K] InfiniteAdeleRing K →ₐ[K] L ⊗[K] v.Completion :=
  Algebra.TensorProduct.map (AlgHom.id K L) (FLT.InfiniteAdeleBaseChange.evalAlgHom K v)

omit [NumberField K] [NumberField L] in
theorem toPlace_tmul (v : InfinitePlace K) (l : L) (x : InfiniteAdeleRing K) :
    toPlace K L v (l ⊗ₜ[K] x) = l ⊗ₜ[K] x v := rfl

theorem norm_apply_eq_norm_toPlace (v : InfinitePlace K) (t : L ⊗[K] InfiniteAdeleRing K) :
    (Algebra.norm (InfiniteAdeleRing K) t) v = Algebra.norm v.Completion (toPlace K L v t) := by
  show FLT.InfiniteAdeleBaseChange.evalAlgHom K v (Algebra.norm (InfiniteAdeleRing K) t) = _
  exact norm_map_eq_norm_map (FLT.InfiniteAdeleBaseChange.evalAlgHom K v) (toPlace K L v)
    (fun _ _ => rfl) t

noncomputable def toPi :
    L ⊗[K] InfiniteAdeleRing K →ₐ[K] ((v : InfinitePlace K) → L ⊗[K] v.Completion) :=
  Pi.algHom K (fun v : InfinitePlace K => L ⊗[K] v.Completion) (toPlace K L)

omit [NumberField K] [NumberField L] in
theorem toPi_apply (t : L ⊗[K] InfiniteAdeleRing K) (v : InfinitePlace K) :
    toPi K L t v = toPlace K L v t := rfl

omit [NumberField L] in

theorem toPi_bijective : Function.Bijective (toPi K L) := by
  have key : ⇑(toPi K L) =
      ⇑(AlgEquiv.piCongrRight
          fun v : InfinitePlace K => (Algebra.TensorProduct.comm K v.Completion L)) ∘
        ⇑(FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv K L) ∘
          ⇑(Algebra.TensorProduct.comm K L (InfiniteAdeleRing K)) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp only [Function.comp_apply, map_zero]
    | tmul l x =>
      funext v
      simp only [Function.comp_apply, toPi_apply, toPlace_tmul, Algebra.TensorProduct.comm_tmul,
        FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply, AlgEquiv.piCongrRight_apply]
    | add z₁ z₂ h₁ h₂ =>
      simp only [Function.comp_apply, map_add] at h₁ h₂ ⊢
      rw [h₁, h₂]
  rw [key]
  exact (AlgEquiv.piCongrRight
      fun v : InfinitePlace K => (Algebra.TensorProduct.comm K v.Completion L)).bijective.comp
    ((FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv K L).bijective.comp
      (Algebra.TensorProduct.comm K L (InfiniteAdeleRing K)).bijective)

omit [NumberField L] in

noncomputable def piEquiv :
    L ⊗[K] InfiniteAdeleRing K ≃ₐ[K] ((v : InfinitePlace K) → L ⊗[K] v.Completion) :=
  AlgEquiv.ofBijective (toPi K L) (toPi_bijective K L)

omit [NumberField L] in
theorem piEquiv_apply (t : L ⊗[K] InfiniteAdeleRing K) (v : InfinitePlace K) :
    piEquiv K L t v = toPlace K L v t := rfl

end arch

end K55

open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (a : (InfiniteAdeleRing K)ˣ) :
    ((a : InfiniteAdeleRing K) ∈ Set.range
        (fun t : (L ⊗[K] InfiniteAdeleRing K)ˣ => Algebra.norm (InfiniteAdeleRing K) (t : L ⊗[K] InfiniteAdeleRing K))) ↔
      ∀ w : InfinitePlace K,
        (a : InfiniteAdeleRing K) w ∈ Set.range
          (fun t : (L ⊗[K] w.Completion)ˣ => Algebra.norm w.Completion (t : L ⊗[K] w.Completion)) := by
  constructor
  · rintro ⟨t, ht⟩ w
    refine ⟨Units.map (K55.toPlace K L w : L ⊗[K] InfiniteAdeleRing K →* L ⊗[K] w.Completion) t, ?_⟩
    have ht' : Algebra.norm (InfiniteAdeleRing K) (t : L ⊗[K] InfiniteAdeleRing K)
        = (a : InfiniteAdeleRing K) := ht
    show Algebra.norm w.Completion (K55.toPlace K L w (t : L ⊗[K] InfiniteAdeleRing K))
        = (a : InfiniteAdeleRing K) w
    rw [← ht', K55.norm_apply_eq_norm_toPlace]
  · intro h
    choose tf htf using h
    let e := K55.piEquiv K L
    let x : (v : InfinitePlace K) → L ⊗[K] v.Completion := fun v => (tf v : L ⊗[K] v.Completion)
    let y : (v : InfinitePlace K) → L ⊗[K] v.Completion :=
      fun v => ((tf v)⁻¹ : (L ⊗[K] v.Completion)ˣ)
    have hxy : x * y = 1 := funext fun v => (tf v).mul_inv
    have hyx : y * x = 1 := funext fun v => (tf v).inv_mul
    let t : (L ⊗[K] InfiniteAdeleRing K)ˣ :=
      ⟨e.symm x, e.symm y, by rw [← map_mul, hxy, map_one], by rw [← map_mul, hyx, map_one]⟩
    refine ⟨t, ?_⟩
    show Algebra.norm (InfiniteAdeleRing K) (e.symm x) = (a : InfiniteAdeleRing K)
    funext w
    have htf' : Algebra.norm w.Completion (tf w : L ⊗[K] w.Completion)
        = (a : InfiniteAdeleRing K) w := htf w
    rw [K55.norm_apply_eq_norm_toPlace, ← htf']
    congr 1
    show e (e.symm x) w = x w
    rw [AlgEquiv.apply_symm_apply]

end S_NumberField_InfiniteAdeleRing_mem_range_norm_tensorProduct_iff_forall_infinitePlace
end P2MW
export P2MW.S_NumberField_InfiniteAdeleRing_mem_range_norm_tensorProduct_iff_forall_infinitePlace (solution)
