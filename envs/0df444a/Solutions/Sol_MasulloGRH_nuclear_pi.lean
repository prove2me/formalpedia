-- Prove2me | solution 1 for MasulloGRH.nuclear_pi
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T22:48:54.504149+00:00
-- url     : https://prove2.me/submissions/5895a3b3-80fd-44e5-b5ad-f2b1b7a42142

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_nuclear_of_continuousLinearEquiv
import Theorems.Thm_MasulloGRH_nuclear_prod
import Theorems.Thm_MasulloGRH_nuclear_pi_of_finite_subproducts

set_option autoImplicit false

open MasulloGRH
open TensorProduct Topology

universe u

/-- Any two topologies on a subsingleton type coincide. -/
private lemma top_eq_of_subsingleton {X : Type*} [Subsingleton X] (t₁ t₂ : TopologicalSpace X) :
    t₁ = t₂ := by
  ext s
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp only [@isOpen_empty]
  · have : s = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    subst this
    simp only [@isOpen_univ]

/-- The zero space is nuclear. -/
private lemma nuclear_of_subsingleton (Z : Type u) [AddCommGroup Z] [Module ℂ Z]
    [TopologicalSpace Z] [Subsingleton Z] : IsNuclear Z := by
  refine ⟨⟨⟨PUnit.{u+1}, inferInstance, fun _ => 0, ⟨top_eq_of_subsingleton _ _⟩⟩, ?_⟩, ?_⟩
  · infer_instance
  · intro F _ _ _ _
    have : Subsingleton (Z ⊗[ℂ] F) := by
      constructor
      intro a b
      have h : ∀ x : Z ⊗[ℂ] F, x = 0 := by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => rfl
        | tmul z y => rw [Subsingleton.elim z 0, TensorProduct.zero_tmul]
        | add x y hx hy => rw [hx, hy, add_zero]
      rw [h a, h b]
    exact top_eq_of_subsingleton _ _

/-- `Π o : Option α, E o ≃L E none × Π a, E (some a)`. -/
private def piOptionCLE {α : Type u} (E : Option α → Type u) [∀ i, AddCommGroup (E i)]
    [∀ i, Module ℂ (E i)] [∀ i, TopologicalSpace (E i)] :
    (∀ o, E o) ≃L[ℂ] (E none × ∀ a, E (some a)) where
  toFun f := (f none, fun a => f (some a))
  invFun p o := Option.rec p.1 p.2 o
  left_inv f := by funext o; cases o <;> rfl
  right_inv p := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := (continuous_apply _).prodMk (continuous_pi fun a => continuous_apply _)
  continuous_invFun := by
    refine continuous_pi fun o => ?_
    cases o with
    | none => exact continuous_fst
    | some a => exact (continuous_apply a).comp continuous_snd

private lemma nuclear_pi_finite (κ : Type u) [Finite κ] :
    ∀ (E : κ → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
      [∀ i, TopologicalSpace (E i)], (∀ i, IsNuclear (E i)) → IsNuclear (∀ i, E i) := by
  refine Finite.induction_empty_option
    (P := fun κ => ∀ (E : κ → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
      [∀ i, TopologicalSpace (E i)], (∀ i, IsNuclear (E i)) → IsNuclear (∀ i, E i))
    ?_ ?_ ?_ κ
  · intro α β e hα E _ _ _ hE
    exact nuclear_of_continuousLinearEquiv _ _
      (ContinuousLinearEquiv.piCongrLeft ℂ E e).symm (hα (fun a => E (e a)) fun a => hE (e a))
  · intro E _ _ _ _
    exact nuclear_of_subsingleton _
  · intro α _ hα E _ _ _ hE
    exact nuclear_of_continuousLinearEquiv _ _ (piOptionCLE E)
      (nuclear_prod _ _ (hE none) (hα (fun a => E (some a)) fun a => hE (some a)))

theorem solution (ι : Type u) (E : ι → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    [∀ i, TopologicalSpace (E i)] (hE : ∀ i, IsNuclear (E i)) : IsNuclear (∀ i, E i) :=
  nuclear_pi_of_finite_subproducts ι E (fun i => (hE i).1)
    (fun J => nuclear_pi_finite J (fun j : J => E j) fun j => hE j)
