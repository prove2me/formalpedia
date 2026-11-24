-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.exists_finset_row_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:52:04.329801+00:00
-- url     : https://prove2.me/submissions/3b5cfcdb-b8e2-4aa4-bbe1-f382708ac04c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CuspRepresentativesFinite
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_RowCompletion_exists_adapted
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_RowCompletion_integral_inv_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_RowCompletion_exists_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open nonZeroDivisors GlobalTheory.CompanionTheory.SW.Core.RowCompletion
namespace GlobalTheory.CompanionTheory.SW.Core
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F], ∃ (s : Finset SL(2, F)) (C : ℝ), ∀ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) → ∃ l : F, l ≠ 0 ∧ |((Algebra.norm ℚ l : ℚ) : ℝ)| ≤ C ∧ ∀ u : (𝓞 F)ˣ, ∃ r ∈ s, ∃ k : SL(2, F), (∀ i j, ∃ z : 𝓞 F, (z : F) = k i j) ∧ (r * k) 1 0 = ((u : 𝓞 F) : F) * l * (c : F) ∧ (r * k) 1 1 = ((u : 𝓞 F) : F) * l * (d : F) := by
  intro F _ _
  classical
  let J : ClassGroup (𝓞 F) → (Ideal (𝓞 F))⁰ := fun g => (ClassGroup.mk0_surjective g).choose
  have hJ : ∀ g, ClassGroup.mk0 (J g) = g := fun g => (ClassGroup.mk0_surjective g).choose_spec
  let A : ClassGroup (𝓞 F) → FractionalIdeal (𝓞 F)⁰ F :=
    fun g => ((J g : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have hA : ∀ g, A g ≠ 0 := by
    intro g
    simpa [A] using nonZeroDivisors.ne_zero (J g).2
  let r : ClassGroup (𝓞 F) → SL(2, F) := fun g =>
    if h : ∃ r, Adapted (A g) r then h.choose else 1
  have hr : ∀ g, (∃ r, Adapted (A g) r) → Adapted (A g) (r g) := by
    intro g h
    simp only [r, dif_pos h]
    exact h.choose_spec
  refine ⟨Finset.univ.image r, ∑ g, (Ideal.absNorm (J g : Ideal (𝓞 F)) : ℝ), ?_⟩
  intro c d hcd
  have hI : Ideal.span {c, d} ∈ (Ideal (𝓞 F))⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    have h1 : c ∈ Ideal.span {c, d} := Ideal.subset_span (by simp)
    have h2 : d ∈ Ideal.span {c, d} := Ideal.subset_span (by simp)
    rw [h0] at h1 h2
    rcases hcd with h | h
    · exact h (by simpa using h1)
    · exact h (by simpa using h2)
  let g := ClassGroup.mk0 ⟨Ideal.span {c, d}, hI⟩
  obtain ⟨l, hl0, hln, hlA⟩ := exists_scale (F := F) (J g) ⟨Ideal.span {c, d}, hI⟩ (hJ g).symm rfl
  refine ⟨l, hl0, hln.trans ?_, ?_⟩
  · exact Finset.single_le_sum (f := fun g => (Ideal.absNorm (J g : Ideal (𝓞 F)) : ℝ))
      (fun _ _ => by positivity) (Finset.mem_univ g)
  intro u
  have hu : FractionalIdeal.spanSingleton (𝓞 F)⁰ ((u : 𝓞 F) : F) = 1 := by
    have := FractionalIdeal.coeIdeal_span_singleton (S := (𝓞 F)⁰) (P := F) (u : 𝓞 F)
    rw [Ideal.span_singleton_eq_top.2 u.isUnit] at this
    simpa using this.symm
  have hAu : A g = FractionalIdeal.spanSingleton _ (((u : 𝓞 F) : F) * l * (c : F)) +
      FractionalIdeal.spanSingleton _ (((u : 𝓞 F) : F) * l * (d : F)) := by
    have : A g = FractionalIdeal.spanSingleton (𝓞 F)⁰ ((u : 𝓞 F) : F) * A g := by rw [hu, one_mul]
    rw [this]
    change _ * ((J g : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = _
    rw [hlA, mul_add, FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_assoc, mul_assoc]
  obtain ⟨γ, hγ, h10, h11⟩ := exists_adapted (hA g) hAu
  have hrg := hr g ⟨γ, hγ⟩
  refine ⟨r g, Finset.mem_image_of_mem _ (Finset.mem_univ g), (r g)⁻¹ * γ,
    integral_inv_mul (hA g) hrg hγ, ?_, ?_⟩
  · rw [mul_inv_cancel_left]; exact h10
  · rw [mul_inv_cancel_left]; exact h11
end GlobalTheory.CompanionTheory.SW.Core
