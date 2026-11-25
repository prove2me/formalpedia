-- Prove2me | solution 1 for GlobalTheory.finite_classes_selfDual_of_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:39:29.152879+00:00
-- url     : https://prove2.me/submissions/cf7e7358-24a1-4c16-ae38-2cf0144c7cf8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual
import Theorems.Thm_GlobalTheory_SelfDualClasses_exists_isometry
import Theorems.Thm_GlobalTheory_SelfDualClasses_finite_integral_of_basis
import Theorems.Thm_GlobalTheory_SelfDualClasses_norm_herm_le
import Theorems.Thm_GlobalTheory_exists_short_vectors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open SelfDualClasses
namespace GlobalTheory
theorem _root_.solution (n : ℕ) :
    ∃ S : Finset (Submodule (𝓞 E) (Fin n → E)),
    (∀ Λ ∈ S, Λ.FG ∧ (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) ∧
    ∀ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG →
    (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) →
    (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) →
    ∃ Λ₀ ∈ S, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
      (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧ ∀ x, x ∈ Λ₀ ↔ γ x ∈ Λ := by
  classical
  set C : ℝ := (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) ^ 2 with hC
  let ι := Fin (2 * fdeg E * n)
  let A : Set E := {x | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C}
  have hA : A.Finite := Embeddings.finite_of_norm_le E ℂ C
  let gram : Basis ι ℚ (Fin n → E) → ι → ι → E := fun b i j => herm 1 (b i) (b j)
  let B : Set (Basis ι ℚ (Fin n → E)) := {b | ∀ i j, gram b i j ∈ A}
  have hG : (gram '' B).Finite := by
    refine (Set.Finite.pi' fun _ : ι => Set.Finite.pi' fun _ : ι => hA).subset ?_
    rintro _ ⟨b, hb, rfl⟩
    exact hb
  obtain ⟨B₀, -, hB₀fin, hB₀⟩ := Set.exists_subset_image_finite_and.mp
    (⟨gram '' B, subset_rfl, hG, rfl⟩ : ∃ t ⊆ gram '' B, t.Finite ∧ t = gram '' B)
  have hS : {Λ : Submodule (𝓞 E) (Fin n → E) | (∃ b ∈ B₀, ∀ i, b i ∈ Λ) ∧ Λ.FG ∧
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ}.Finite := by
    refine (hB₀fin.biUnion fun b _ => finite_integral_of_basis b).subset ?_
    rintro Λ ⟨⟨b, hb, hbΛ⟩, -, hi, -⟩
    exact Set.mem_biUnion hb ⟨hbΛ, hi⟩
  refine ⟨hS.toFinset, fun Λ hΛ => (hS.mem_toFinset.mp hΛ).2, fun Λ hfg hint hdual => ?_⟩
  obtain ⟨v, hv, hli, hsp, hle⟩ := exists_short_vectors Λ hfg hint hdual
  let b : Basis ι ℚ (Fin n → E) := Basis.mk hli hsp.ge
  have hb : ∀ i, b i = v i := fun i => Basis.mk_apply _ _ i
  have hbB : gram b ∈ gram '' B₀ := by
    rw [hB₀]
    refine ⟨b, fun i j => ?_, rfl⟩
    simp only [gram, hb]
    exact ⟨hint _ (hv i) _ (hv j), fun φ => norm_herm_le φ _ _ C (hle i φ) (hle j φ)⟩
  obtain ⟨b₀, hb₀, hgram⟩ := hbB
  obtain ⟨γ, hγ, hγb⟩ := exists_isometry b₀ b fun i j => (congrFun₂ hgram i j).symm
  let γ' : (Fin n → E) ≃ₗ[𝓞 E] (Fin n → E) := γ.restrictScalars (𝓞 E)
  refine ⟨Λ.comap γ'.toLinearMap, hS.mem_toFinset.mpr ⟨⟨b₀, hb₀, fun i => ?_⟩, ?_, ?_, ?_⟩,
    γ, hγ, fun x => Iff.rfl⟩
  · change γ (b₀ i) ∈ Λ
    rw [hγb, hb]
    exact hv i
  · rw [Submodule.comap_equiv_eq_map_symm]
    exact hfg.map _
  · intro x hx y hy
    rw [← hγ]
    exact hint _ hx _ hy
  · intro x hx
    refine hdual (γ x) fun y hy => ?_
    obtain ⟨z, rfl⟩ := γ.surjective y
    rw [hγ]
    exact hx z hy
end GlobalTheory
