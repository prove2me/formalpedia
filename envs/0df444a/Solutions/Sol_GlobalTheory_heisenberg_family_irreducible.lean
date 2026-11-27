-- Prove2me | solution 1 for GlobalTheory.heisenberg_family_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:39:05.455249+00:00
-- url     : https://prove2.me/submissions/321f6d4b-e768-4dee-8356-36b8ed670ade

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LinearIndependentOfCommSmul
import Theorems.Thm_GlobalTheory_linearIndependent_of_comm_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (K G V : Type) [Field K] [CommGroup G] [Finite G] [AddCommGroup V] [Module K V] [Module.Finite K V] (U : G → V ≃ₗ[K] V) (e : G → G →* Kˣ), (∀ x y v, U x (U y v) = (e x y : K) • U y (U x v)) → Function.Injective e → Module.finrank K V ^ 2 ≤ Nat.card G → ∀ W : Submodule K V, (∀ x v, v ∈ W → U x v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro K G V _ _ _ _ _ _ U e hU he hcard W hW
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Or.inl (Submodule.eq_bot_of_subsingleton)
  haveI : Fintype G := Fintype.ofFinite G
  have hind : LinearIndependent K (fun x => (U x : V →ₗ[K] V)) := by
    refine _root_.GlobalTheory.linearIndependent_of_comm_smul (fun x => (U x : V →ₗ[K] V))
      (fun x y => (e x y : K)) (fun x => (U x).injective) (fun x y v => hU x y v) ?_
    intro x x' hxx'
    apply he
    ext y
    exact congr_fun hxx' y
  have hdim : Module.finrank K (V →ₗ[K] V) = Module.finrank K V ^ 2 := by
    rw [Module.finrank_linearMap, sq]
  have hle := hind.fintype_card_le_finrank
  rw [hdim] at hle
  rw [Nat.card_eq_fintype_card] at hcard
  have hspan := hind.span_eq_top_of_card_eq_finrank (le_antisymm hle hcard |>.trans hdim.symm)

  let S : Submodule K (V →ₗ[K] V) :=
    { carrier := {f | ∀ w ∈ W, f w ∈ W}
      add_mem' := fun hf hg w hw => W.add_mem (hf w hw) (hg w hw)
      zero_mem' := fun w _ => by simp
      smul_mem' := fun a f hf w hw => W.smul_mem a (hf w hw) }
  have hS : ∀ f : V →ₗ[K] V, ∀ w ∈ W, f w ∈ W := by
    intro f
    have : f ∈ Submodule.span K (Set.range fun x => (U x : V →ₗ[K] V)) := by
      rw [hspan]; exact Submodule.mem_top
    have hsub : Submodule.span K (Set.range fun x => (U x : V →ₗ[K] V)) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩ w hw
      exact hW x w hw
    exact hsub this
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 hcon)
  rw [eq_top_iff]
  intro v _
  have := hS ((φ w)⁻¹ • φ.smulRight v) w hwW
  simpa [LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ] using this
end _root_.GlobalTheory
end GlobalTheory
