-- Prove2me | solution 1 for GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:08.408346+00:00
-- url     : https://prove2.me/submissions/68cb5e16-1e42-417e-81ee-a0d8fb601a32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosOfPosMulInnerOnJointEigenvectors
import Theorems.Thm_GlobalTheory_pos_of_pos_mul_inner_on_joint_eigenvectors_finiteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module.End
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (W : Submodule ℂ V), FiniteDimensional ℂ W → ∀ (I : Type) (T : I → Module.End ℂ V), (∀ i, ∀ w ∈ W, T i w ∈ W) → (∀ i x y, inner ℂ (ι (T i x)) (ι y) = inner ℂ (ι x) (ι (T i y))) → (∀ i j, T i * T j = T j * T i) → ∀ (u : V →ₗ[ℂ] H), (∀ (m : I → ℝ), ∀ y ∈ W, (∀ i, T i y = (m i : ℂ) • y) → ∃ c : ℝ, 0 < c ∧ ∀ x ∈ W, inner ℂ (ι x) (u y) = (c : ℂ) * inner ℂ (ι x) (ι y)) → ∀ x ∈ W, x ≠ 0 → (inner ℂ (ι x) (u x)).im = 0 ∧ 0 < (inner ℂ (ι x) (u x)).re := by
  intro V _ _ H _ _ ι hι W hW I T hTW hsym hcomm u hu x hxW hx0
  let e : W ≃ₗ[ℂ] W.map ι := Submodule.equivMapOfInjective ι hι W
  have : FiniteDimensional ℂ (W.map ι) := e.finiteDimensional
  let T' : I → (W.map ι) →ₗ[ℂ] (W.map ι) := fun i =>
    e.toLinearMap ∘ₗ (T i).restrict (hTW i) ∘ₗ e.symm.toLinearMap
  have hesymm : ∀ z : W.map ι, ι (e.symm z : V) = (z : H) := fun z =>
    congrArg Subtype.val (e.apply_symm_apply z)
  have hTe : ∀ i (z : W.map ι), (e.symm (T' i z) : V) = T i (e.symm z) := by
    intro i z
    simp [T']
  have hT'coe : ∀ i (z : W.map ι), (T' i z : H) = ι (T i (e.symm z)) := by
    intro i z
    rw [← hesymm (T' i z), hTe]
  have hsym' : ∀ i, (T' i).IsSymmetric := by
    intro i a b
    change inner ℂ (T' i a : H) (b : H) = inner ℂ (a : H) (T' i b : H)
    rw [hT'coe, hT'coe, ← hesymm a, ← hesymm b]
    exact hsym i _ _
  have hc' : ∀ i k, Commute (T' i) (T' k) := by
    intro i k
    refine LinearMap.ext fun z => e.symm.injective (Subtype.ext ?_)
    rw [Module.End.mul_apply, Module.End.mul_apply]
    simp only [hTe]
    exact LinearMap.congr_fun (hcomm i k) _
  let u' : (W.map ι) →ₗ[ℂ] H := u ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap
  have hu' : ∀ (m : I → ℝ) (y : W.map ι), (∀ i, T' i y = (m i : ℂ) • y) →
      ∃ c : ℝ, 0 < c ∧ ∀ z, inner ℂ ((W.map ι).subtype z) (u' y) = (c : ℂ) * inner ℂ z y := by
    intro m y hy
    have hy' : ∀ i, T i (e.symm y) = (m i : ℂ) • (e.symm y : V) := by
      intro i
      rw [← hTe, hy i, map_smul, Submodule.coe_smul]
    obtain ⟨c, hc, hcx⟩ := hu m (e.symm y) (e.symm y).2 hy'
    refine ⟨c, hc, fun z => ?_⟩
    have h := hcx (e.symm z) (e.symm z).2
    rw [hesymm z, hesymm y] at h
    exact h
  have hne : e ⟨x, hxW⟩ ≠ 0 := by
    intro h
    apply hx0
    have h2 : ((e ⟨x, hxW⟩ : W.map ι) : H) = 0 := by rw [h]; rfl
    exact hι ((show ι x = 0 from h2).trans (map_zero ι).symm)
  have hmain := pos_of_pos_mul_inner_on_joint_eigenvectors_finiteDimensional T' hsym' hc' (W.map ι).subtype u' hu'
    (e ⟨x, hxW⟩) hne
  have h1 : (W.map ι).subtype (e ⟨x, hxW⟩) = ι x := rfl
  have h2 : u' (e ⟨x, hxW⟩) = u x := by simp [u']
  rw [h1, h2] at hmain
  exact hmain
end GlobalTheory
