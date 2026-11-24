-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Dens.exists_tmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:07:29.322803+00:00
-- url     : https://prove2.me/submissions/240471e8-5837-4b27-813d-23c1e9b37d6f

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_PairsD
import Theorems.Thm_GlobalTheory_ThK_Dbl_Dens_exists_mem_adjoin_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Dens
open Polynomial Cardinal
namespace GlobalTheory.ThK.Dbl.Dens
theorem _root_.solution {α : Type} [Finite α] [DecidableEq α] {A : Type} [AddCommGroup A]
    [Module ℂ A] {X : α → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (O : ∀ i, Set (Module.End ℂ (X i))) (hrank : ∀ i, Module.rank ℂ (X i) ≤ Cardinal.aleph0)
    (hnt : ∀ i, Nontrivial (X i))
    (hirr : ∀ i (N : Submodule ℂ (X i)), (∀ T ∈ O i, ∀ x ∈ N, T x ∈ N) → N = ⊥ ∨ N = ⊤)
    (N : Submodule ℂ (A ⊗[ℂ] PiTensorProduct ℂ X))
    (hN : ∀ i, ∀ T ∈ O i, ∀ x ∈ N, LinearMap.lTensor A (PiTensorProduct.map
      (Function.update (fun j => (LinearMap.id : X j →ₗ[ℂ] X j)) i T)) x ∈ N)
    (x : A ⊗[ℂ] PiTensorProduct ℂ X) (hxN : x ∈ N) (hx0 : x ≠ 0) :
    ∃ a₀ : A, a₀ ≠ 0 ∧ ∀ y, a₀ ⊗ₜ[ℂ] y ∈ N := by
  classical
  cases nonempty_fintype α
  have hcomp : ∀ (f g : ∀ a, X a →ₗ[ℂ] X a) (y : A ⊗[ℂ] PiTensorProduct ℂ X),
      LinearMap.lTensor A (PiTensorProduct.map fun a => f a ∘ₗ g a) y =
        LinearMap.lTensor A (PiTensorProduct.map f) (LinearMap.lTensor A (PiTensorProduct.map g) y) := by
    intro f g y
    rw [PiTensorProduct.map_comp, LinearMap.lTensor_comp_apply]
  let Asub : ∀ a, Subalgebra ℂ (Module.End ℂ (X a)) := fun i =>
    { carrier := {T | ∀ y ∈ N, LinearMap.lTensor A (PiTensorProduct.map
        (Function.update (fun b => (LinearMap.id : X b →ₗ[ℂ] X b)) i T)) y ∈ N}
      mul_mem' := fun {a b} ha hb y hy => by
        have := ha _ (hb y hy)
        rw [← hcomp] at this
        convert this using 4
        funext ρ
        by_cases hρ : ρ = i
        · subst hρ; simp [Module.End.mul_eq_comp]
        · simp [Function.update_of_ne hρ]
      add_mem' := fun {a b} ha hb y hy => by
        rw [PiTensorProduct.map_update_add, LinearMap.lTensor_add]
        exact N.add_mem (ha y hy) (hb y hy)
      algebraMap_mem' := fun c y hy => by
        rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul, LinearMap.lTensor_smul]
        have : Function.update (fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ)) i (1 : Module.End ℂ (X i)) =
            fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ) := Function.update_eq_self i _
        rw [this, PiTensorProduct.map_id, LinearMap.lTensor_id]
        exact N.smul_mem c hy }
  have hA : ∀ a, Algebra.adjoin ℂ (O a) ≤ Asub a := fun a =>
    Algebra.adjoin_le fun T hT y hy => hN a T hT y hy
  have h3 : ∀ T : ∀ a, Module.End ℂ (X a), (∀ a, T a ∈ Asub a) →
      ∀ y ∈ N, LinearMap.lTensor A (PiTensorProduct.map T) y ∈ N := by
    intro T hT
    have h2 : ∀ s : Finset α, ∀ y ∈ N, LinearMap.lTensor A
        (PiTensorProduct.map (fun a => if a ∈ s then T a else LinearMap.id)) y ∈ N := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro y hy
        simpa using hy
      | insert j s hj ih =>
        intro y hy
        have := hT j _ (ih y hy)
        rw [← hcomp] at this
        convert this using 4
        funext b
        by_cases hb : b = j
        · subst hb; simp [hj]
        · simp [hb]
    intro y hy
    simpa using h2 Finset.univ y hy
  let b := fun a => Module.Free.chooseBasis ℂ (X a)
  let B := Basis.piTensorProduct b
  let e := TensorProduct.equivFinsuppOfBasisRight (M := A) B
  obtain ⟨p, hp⟩ : ∃ p, e x p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx0 (e.map_eq_zero_iff.1 (Finsupp.ext hcon))
  refine ⟨e x p, hp, ?_⟩
  have hsum : x = (e x).sum fun q a => a ⊗ₜ[ℂ] B q := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  have hcoef : ∀ (t : PiTensorProduct ℂ X) (y : A ⊗[ℂ] PiTensorProduct ℂ X),
      LinearMap.lTensor A ((B.coord p).smulRight t) y = e y p ⊗ₜ[ℂ] t := by
    intro t y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a n =>
      simp [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, TensorProduct.smul_tmul']
    | add y z hy hz => simp [hy, hz, TensorProduct.add_tmul]
  have hpure : ∀ v : ∀ i, X i, e x p ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v ∈ N := by
    intro v
    let f : ∀ a, Module.End ℂ (X a) := fun a => ((b a).coord (p a)).smulRight (v a)
    have hT : ∀ a, ∃ T ∈ Asub a, ∀ y ∈ (e x).support.image (fun q => b a (q a)), T y = f a y :=
      fun a => by
        haveI := hnt a
        obtain ⟨T, hT1, hT2⟩ := exists_mem_adjoin_eq (O a) (hrank a) (hirr a) (f a)
          ((e x).support.image (fun q => b a (q a)))
        exact ⟨T, hA a hT1, hT2⟩
    choose T hTA hTf using hT
    have hf : PiTensorProduct.map f = (B.coord p).smulRight (PiTensorProduct.tprod ℂ v) := by
      ext w
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
        LinearMap.smulRight_apply, Module.Basis.coord_apply, B, f,
        Basis.piTensorProduct_repr_tprod_apply]
      exact (PiTensorProduct.tprod ℂ).map_smul_univ _ v
    have hmap : LinearMap.lTensor A (PiTensorProduct.map T) x =
        LinearMap.lTensor A (PiTensorProduct.map f) x := by
      rw [hsum, map_finsuppSum, map_finsuppSum]
      refine Finsupp.sum_congr fun q hq => ?_
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, Basis.piTensorProduct_apply,
        PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
      congr 2
      funext a
      exact hTf a _ (Finset.mem_image_of_mem _ hq)
    have h4 := h3 T hTA x hxN
    rwa [hmap, hf, hcoef] at h4
  have hall : (⊤ : Submodule ℂ (PiTensorProduct ℂ X)) ≤
      N.comap (TensorProduct.mk ℂ A (PiTensorProduct ℂ X) (e x p)) := by
    rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact hpure v
  exact fun y => hall (Submodule.mem_top (x := y))
end GlobalTheory.ThK.Dbl.Dens
