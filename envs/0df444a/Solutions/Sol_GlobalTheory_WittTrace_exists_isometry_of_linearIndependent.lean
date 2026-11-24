-- Prove2me | solution 1 for GlobalTheory.WittTrace.exists_isometry_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:37:05.347013+00:00
-- url     : https://prove2.me/submissions/44bffa1d-7d74-4095-bb1e-e66859b35bdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfLinearIndependent
import Theorems.Thm_GlobalTheory_WittTrace_exists_isometry_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittTrace
open Module Matrix GlobalTheory.HermDiag GlobalTheory.HermWitt
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
namespace GlobalTheory.WittTrace
theorem _root_.solution
    (hs : ∀ b : E, c b = b → ∃ s : E, s ≠ 0 ∧ s + c s = b)
    (hc : ∀ t, c (c t) = t) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hrep : ∀ ψ : V →ₗ[E] E, ∃ w, ∀ z, B z w = ψ z) {ι : Type*} [Finite ι] {x y : ι → V}
    (hx : LinearIndependent E x) (hy : LinearIndependent E y)
    (hxy : ∀ i j, B (x i) (x j) = B (y i) (y j)) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ i, γ (x i) = y i := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧
      ∀ i ∈ s, γ (x i) = y i by
    obtain ⟨γ, hγ, hγs⟩ := H Finset.univ
    exact ⟨γ, hγ, fun i => hγs i (Finset.mem_univ i)⟩
  intro s
  refine Finset.induction_on s ⟨LinearEquiv.refl E V, fun _ _ => rfl, by simp⟩ ?_
  intro j s hj ih
  obtain ⟨γ, hγ, hγs⟩ := ih
  have hjs : j ∉ (s : Set ι) := by simpa using hj
  have hyj : y j ∉ Submodule.span E (y '' ↑s) := hy.notMem_span_image hjs
  have himg : y '' ↑s = γ '' (x '' ↑s) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨x i, ⟨i, hi, rfl⟩, hγs i hi⟩
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩; exact ⟨i, hi, (hγs i hi).symm⟩
  have hxj : γ (x j) ∉ Submodule.span E (y '' ↑s) := by
    rw [himg]
    intro hm
    exact hx.notMem_span_image hjs
      ((Submodule.apply_mem_span_image_iff_mem_span (f := (γ : V →ₗ[E] V)) γ.injective).1 hm)
  obtain ⟨γ₁, hγ₁, hγ₁x, hγ₁S⟩ := exists_isometry_step hs hc hB hrep (y '' ↑s) hxj hyj
    (by rw [hγ]; exact hxy j j) (by
      rintro _ ⟨i, hi, rfl⟩
      calc B (y i) (γ (x j)) = B (γ (x i)) (γ (x j)) := by rw [hγs i hi]
        _ = B (x i) (x j) := hγ _ _
        _ = B (y i) (y j) := hxy i j)
  refine ⟨γ.trans γ₁, fun z w => by simp only [LinearEquiv.trans_apply, hγ₁, hγ], ?_⟩
  intro i hi
  rcases Finset.mem_insert.1 hi with rfl | hi
  · simp only [LinearEquiv.trans_apply]; exact hγ₁x
  · simp only [LinearEquiv.trans_apply, hγs i hi]
    exact hγ₁S _ ⟨i, hi, rfl⟩
end GlobalTheory.WittTrace
