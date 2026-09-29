-- Prove2me | solution 1 for HopfAlgebra.exists_hopfAlgebra_algEquiv_of_natural_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d7ae8dd5-2936-5945-8cf4-cb61b856d5a3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_hopfAlgebra_algEquiv_of_natural_mul

set_option autoImplicit false

open scoped TensorProduct

universe u

open Algebra.TensorProduct in
theorem solution
    (A : Type u) [CommRing A] (W : Type u) [CommRing W] [Algebra A W]
    (mul : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) → (W →ₐ[A] T) → (W →ₐ[A] T))
    (one : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T))
    (inv : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) → (W →ₐ[A] T))
    (h_assoc : ∀ (T : Type u) [CommRing T] [Algebra A T] (f g h : W →ₐ[A] T),
      mul T (mul T f g) h = mul T f (mul T g h))
    (h_comm : ∀ (T : Type u) [CommRing T] [Algebra A T] (f g : W →ₐ[A] T), mul T f g = mul T g f)
    (h_one : ∀ (T : Type u) [CommRing T] [Algebra A T] (f : W →ₐ[A] T), mul T (one T) f = f)
    (h_inv : ∀ (T : Type u) [CommRing T] [Algebra A T] (f : W →ₐ[A] T), mul T (inv T f) f = one T)
    (h_nat_mul : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
      (f g : W →ₐ[A] T), u.comp (mul T f g) = mul T' (u.comp f) (u.comp g))
    (h_nat_one : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T'),
      u.comp (one T) = one T') :
    ∃ (W' : Type u) (_ : CommRing W') (_ : HopfAlgebra A W') (ψ : W' ≃ₐ[A] W),
      Coalgebra.IsCocomm A W' ∧
      ∀ (T : Type u) [CommRing T] [Algebra A T] (f g : W →ₐ[A] T),
        WithConv.toConv ((mul T f g).comp (ψ : W' →ₐ[A] W)) =
          WithConv.toConv (f.comp (ψ : W' →ₐ[A] W)) * WithConv.toConv (g.comp (ψ : W' →ₐ[A] W)) := by
  classical

  set iL : W →ₐ[A] W ⊗[A] W := includeLeft with hiL
  set iR : W →ₐ[A] W ⊗[A] W := includeRight with hiR
  set δ : W →ₐ[A] W ⊗[A] W := mul (W ⊗[A] W) iL iR with hδ
  set ε : W →ₐ[A] A := one A with hε
  set S : W →ₐ[A] W := inv W (AlgHom.id A W) with hS

  have key : ∀ (T : Type u) [CommRing T] [Algebra A T] (f g : W →ₐ[A] T),
      mul T f g = (lift f g (fun _ _ => Commute.all _ _)).comp δ := by
    intro T _ _ f g
    have h := h_nat_mul (W ⊗[A] W) T (lift f g (fun _ _ => Commute.all _ _)) iL iR
    have hL : (lift f g (fun _ _ => Commute.all _ _)).comp iL = f := by
      ext w; simp [hiL]
    have hR : (lift f g (fun _ _ => Commute.all _ _)).comp iR = g := by
      ext w; simp [hiR]
    rw [hL, hR] at h
    exact h.symm
  have key_one : ∀ (T : Type u) [CommRing T] [Algebra A T], one T = (Algebra.ofId A T).comp ε := by
    intro T _ _
    exact (h_nat_one A T (Algebra.ofId A T)).symm

  have h_one' : ∀ (T : Type u) [CommRing T] [Algebra A T] (f : W →ₐ[A] T), mul T f (one T) = f := by
    intro T _ _ f; rw [h_comm]; exact h_one T f
  have h_inv' : ∀ (T : Type u) [CommRing T] [Algebra A T] (f : W →ₐ[A] T), mul T f (inv T f) = one T := by
    intro T _ _ f; rw [h_comm]; exact h_inv T f

  have hco : (Algebra.TensorProduct.assoc A A A W W W).toAlgHom.comp
      ((map δ (AlgHom.id A W)).comp δ) = (map (AlgHom.id A W) δ).comp δ := by

    set T3 : Type u := W ⊗[A] (W ⊗[A] W) with hT3
    set j₁ : W →ₐ[A] W ⊗[A] (W ⊗[A] W) := includeLeft with hj₁
    set j₂ : W →ₐ[A] W ⊗[A] (W ⊗[A] W) :=
      (includeRight : W ⊗[A] W →ₐ[A] W ⊗[A] (W ⊗[A] W)).comp iL with hj₂
    set j₃ : W →ₐ[A] W ⊗[A] (W ⊗[A] W) :=
      (includeRight : W ⊗[A] W →ₐ[A] W ⊗[A] (W ⊗[A] W)).comp iR with hj₃
    set k₁ : W →ₐ[A] (W ⊗[A] W) ⊗[A] W :=
      (includeLeft : W ⊗[A] W →ₐ[A] (W ⊗[A] W) ⊗[A] W).comp iL with hk₁
    set k₂ : W →ₐ[A] (W ⊗[A] W) ⊗[A] W :=
      (includeLeft : W ⊗[A] W →ₐ[A] (W ⊗[A] W) ⊗[A] W).comp iR with hk₂
    set k₃ : W →ₐ[A] (W ⊗[A] W) ⊗[A] W := includeRight with hk₃

    have eR : (map (AlgHom.id A W) δ).comp δ =
        mul (W ⊗[A] (W ⊗[A] W)) j₁ (mul (W ⊗[A] (W ⊗[A] W)) j₂ j₃) := by
      have n1 := h_nat_mul (W ⊗[A] W) (W ⊗[A] (W ⊗[A] W)) (map (AlgHom.id A W) δ) iL iR
      have e1 : (map (AlgHom.id A W) δ).comp iL = j₁ := by ext w; simp [hiL, hj₁]
      have e2 : (map (AlgHom.id A W) δ).comp iR =
          (includeRight : W ⊗[A] W →ₐ[A] W ⊗[A] (W ⊗[A] W)).comp δ := by ext w; simp [hiR]
      have n2 := h_nat_mul (W ⊗[A] W) (W ⊗[A] (W ⊗[A] W))
        (includeRight : W ⊗[A] W →ₐ[A] W ⊗[A] (W ⊗[A] W)) iL iR
      have e3 : (includeRight : W ⊗[A] W →ₐ[A] W ⊗[A] (W ⊗[A] W)).comp δ =
          mul (W ⊗[A] (W ⊗[A] W)) j₂ j₃ := by
        rw [hδ, n2]
      rw [← hδ] at n1
      rw [n1, e1, e2, e3]

    have eL : (map δ (AlgHom.id A W)).comp δ =
        mul ((W ⊗[A] W) ⊗[A] W) (mul ((W ⊗[A] W) ⊗[A] W) k₁ k₂) k₃ := by
      have n1 := h_nat_mul (W ⊗[A] W) ((W ⊗[A] W) ⊗[A] W) (map δ (AlgHom.id A W)) iL iR
      have e1 : (map δ (AlgHom.id A W)).comp iL =
          (includeLeft : W ⊗[A] W →ₐ[A] (W ⊗[A] W) ⊗[A] W).comp δ := by ext w; simp [hiL]
      have e2 : (map δ (AlgHom.id A W)).comp iR = k₃ := by ext w; simp [hiR, hk₃]
      have n2 := h_nat_mul (W ⊗[A] W) ((W ⊗[A] W) ⊗[A] W)
        (includeLeft : W ⊗[A] W →ₐ[A] (W ⊗[A] W) ⊗[A] W) iL iR
      have e3 : (includeLeft : W ⊗[A] W →ₐ[A] (W ⊗[A] W) ⊗[A] W).comp δ =
          mul ((W ⊗[A] W) ⊗[A] W) k₁ k₂ := by
        rw [hδ, n2]
      rw [← hδ] at n1
      rw [n1, e1, e2, e3]
    have a1 : (Algebra.TensorProduct.assoc A A A W W W).toAlgHom.comp k₁ = j₁ := by
      ext w; simp [hiL, hj₁, hk₁, Algebra.TensorProduct.one_def]
    have a2 : (Algebra.TensorProduct.assoc A A A W W W).toAlgHom.comp k₂ = j₂ := by
      ext w; simp [hiR, hiL, hj₂, hk₂]
    have a3 : (Algebra.TensorProduct.assoc A A A W W W).toAlgHom.comp k₃ = j₃ := by
      ext w; simp [hiR, hj₃, hk₃, Algebra.TensorProduct.one_def]
    have n3 := h_nat_mul ((W ⊗[A] W) ⊗[A] W) (W ⊗[A] (W ⊗[A] W))
      (Algebra.TensorProduct.assoc A A A W W W).toAlgHom (mul ((W ⊗[A] W) ⊗[A] W) k₁ k₂) k₃
    have n4 := h_nat_mul ((W ⊗[A] W) ⊗[A] W) (W ⊗[A] (W ⊗[A] W))
      (Algebra.TensorProduct.assoc A A A W W W).toAlgHom k₁ k₂
    rw [eL, eR, n3, n4, a1, a2, a3, h_assoc]

  have hr : (map ε (AlgHom.id A W)).comp δ = (Algebra.TensorProduct.lid A W).symm := by
    have n1 := h_nat_mul (W ⊗[A] W) (A ⊗[A] W) (map ε (AlgHom.id A W)) iL iR
    have e1 : (map ε (AlgHom.id A W)).comp iL = (includeLeft : A →ₐ[A] A ⊗[A] W).comp ε := by
      ext w; simp [hiL]
    have e2 : (map ε (AlgHom.id A W)).comp iR = (includeRight : W →ₐ[A] A ⊗[A] W) := by
      ext w; simp [hiR]
    have n2 := h_nat_one A (A ⊗[A] W) (includeLeft : A →ₐ[A] A ⊗[A] W)
    rw [hδ, n1, e1, e2, hε, n2, h_one]
    ext w; simp
  have hl : (map (AlgHom.id A W) ε).comp δ = (Algebra.TensorProduct.rid A A W).symm := by
    have n1 := h_nat_mul (W ⊗[A] W) (W ⊗[A] A) (map (AlgHom.id A W) ε) iL iR
    have e1 : (map (AlgHom.id A W) ε).comp iL = (includeLeft : W →ₐ[A] W ⊗[A] A) := by
      ext w; simp [hiL]
    have e2 : (map (AlgHom.id A W) ε).comp iR = (includeRight : A →ₐ[A] W ⊗[A] A).comp ε := by
      ext w; simp [hiR]
    have n2 := h_nat_one A (W ⊗[A] A) (includeRight : A →ₐ[A] W ⊗[A] A)
    rw [hδ, n1, e1, e2, hε, n2, h_one']
    ext w; simp
  letI hB : Bialgebra A W := Bialgebra.ofAlgHom δ ε hco hr hl
  have hcomul : (Bialgebra.comulAlgHom A W : W →ₐ[A] W ⊗[A] W) = δ := AlgHom.ext fun _ => rfl
  have hcounit : (Bialgebra.counitAlgHom A W : W →ₐ[A] A) = ε := AlgHom.ext fun _ => rfl

  have lmul_map : ∀ (T : Type u) [CommRing T] [Algebra A T] (f g : W →ₐ[A] T),
      (lmul' A (S := T)).comp (map f g) = lift f g (fun _ _ => Commute.all _ _) := by
    intro T _ _ f g
    exact lmul'_comp_map f g

  have hSr : (lmul' A (S := W)).comp ((map S (AlgHom.id A W)).comp δ) = (Algebra.ofId A W).comp ε := by
    rw [← AlgHom.comp_assoc, lmul_map, ← key, hS, h_inv, key_one]
  have hSl : (lmul' A (S := W)).comp ((map (AlgHom.id A W) S).comp δ) = (Algebra.ofId A W).comp ε := by
    rw [← AlgHom.comp_assoc, lmul_map, ← key, hS, h_inv', key_one]
  have hmapS_r : ∀ x : W ⊗[A] W, (map S (AlgHom.id A W)) x = S.toLinearMap.rTensor W x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [LinearMap.rTensor_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmapS_l : ∀ x : W ⊗[A] W, (map (AlgHom.id A W) S) x = S.toLinearMap.lTensor W x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [LinearMap.lTensor_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hlmul : ∀ x : W ⊗[A] W, (lmul' A (S := W)) x = LinearMap.mul' A W x := fun x =>
    congrArg (fun (φ : W ⊗[A] W →ₗ[A] W) => φ x) (lmul'_toLinearMap (R := A) (S := W))
  letI hH : HopfAlgebra A W :=
    { antipode := S.toLinearMap
      mul_antipode_rTensor_comul := by
        apply LinearMap.ext
        intro w
        have h := AlgHom.congr_fun hSr w
        simp only [AlgHom.comp_apply] at h
        rw [hlmul, hmapS_r] at h
        exact h
      mul_antipode_lTensor_comul := by
        apply LinearMap.ext
        intro w
        have h := AlgHom.congr_fun hSl w
        simp only [AlgHom.comp_apply] at h
        rw [hlmul, hmapS_l] at h
        exact h }

  have hcomm : (Algebra.TensorProduct.comm A W W).toAlgHom.comp δ = δ := by
    have n1 := h_nat_mul (W ⊗[A] W) (W ⊗[A] W) (Algebra.TensorProduct.comm A W W).toAlgHom iL iR
    have c1 : (Algebra.TensorProduct.comm A W W).toAlgHom.comp iL = iR := by ext w; simp [hiL, hiR]
    have c2 : (Algebra.TensorProduct.comm A W W).toAlgHom.comp iR = iL := by ext w; simp [hiL, hiR]
    conv_lhs => rw [hδ]
    rw [n1, c1, c2, h_comm, ← hδ]
  haveI hcc : Coalgebra.IsCocomm A W :=
    ⟨by
      apply LinearMap.ext
      intro w
      have h := AlgHom.congr_fun hcomm w
      exact h⟩
  refine ⟨W, inferInstance, hH, AlgEquiv.refl, hcc, ?_⟩
  intro T _ _ f g
  have hrefl : ((AlgEquiv.refl : W ≃ₐ[A] W) : W →ₐ[A] W) = AlgHom.id A W := rfl
  rw [hrefl, AlgHom.comp_id, AlgHom.comp_id, AlgHom.comp_id]
  apply congrArg WithConv.toConv
  rw [key T f g, WithConv.ofConv_toConv, WithConv.ofConv_toConv, hcomul, ← AlgHom.comp_assoc, lmul'_comp_map]

end S_HopfAlgebra_exists_hopfAlgebra_algEquiv_of_natural_mul
end P2MW
export P2MW.S_HopfAlgebra_exists_hopfAlgebra_algEquiv_of_natural_mul (solution)
