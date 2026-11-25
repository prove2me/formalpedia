-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.summable_norm_iff_and_tsum_eq_cosetPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:39.180889+00:00
-- url     : https://prove2.me/submissions/406335d0-0e73-4c19-b14e-aa89be3293fe

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]
variable {K}
omit [Fintype ι]
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : ι → K) (g : (ι → mixedSpace K) → ℂ) :
    (Summable (fun ξ ↦ ‖(cosetPi K I c).indicator (fun ξ ↦ g (embPi K ξ)) ξ‖) ↔
      Summable (fun α : idealLatticePi I ↦ ‖g (α + embPi K c)‖)) ∧
      ∑' ξ, (cosetPi K I c).indicator (fun ξ ↦ g (embPi K ξ)) ξ =
        ∑' α : idealLatticePi I, g (α + embPi K c) := by
  have hpre : ∀ α : idealLatticePi I, ∀ i, ∃ y ∈ ((I i : FractionalIdeal (𝓞 K)⁰ K) : Set K),
      mixedEmbedding K y = (α : ι → mixedSpace K) i := fun α i ↦
    (mem_idealLattice K (I i)).mp (mem_idealLatticePi.mp α.2 i)
  choose y hyI hy using hpre
  set h : idealLatticePi I → ι → K := fun α i ↦ c i + y α i with hh
  have hinj : Function.Injective h := by
    intro α β hαβ
    apply Subtype.ext
    funext i
    have h1 : y α i = y β i := add_left_cancel (congrFun hαβ i)
    rw [← hy α i, ← hy β i, h1]
  have hmem : ∀ α, h α ∈ cosetPi K I c := fun α i ↦ by
    simp only [hh, add_sub_cancel_left]
    exact hyI α i
  have hemb : ∀ α, embPi K (h α) = (α : ι → mixedSpace K) + embPi K c := by
    intro α
    funext i
    simp only [embPi, hh, Pi.add_apply, map_add, hy α i, add_comm]
  set G : (ι → K) → ℂ := (cosetPi K I c).indicator (fun ξ ↦ g (embPi K ξ))
  have hsupp : ∀ ξ ∉ Set.range h, G ξ = 0 := by
    intro ξ hξ
    refine Set.indicator_of_notMem (fun hm ↦ hξ ?_) _
    have hα : embPi K (fun i ↦ ξ i - c i) ∈ idealLatticePi I := by
      rw [mem_idealLatticePi]
      intro i
      exact (mem_idealLattice K (I i)).mpr ⟨ξ i - c i, hm i, rfl⟩
    refine ⟨⟨_, hα⟩, funext fun i ↦ ?_⟩
    have h2 : mixedEmbedding K (y ⟨_, hα⟩ i) = mixedEmbedding K (ξ i - c i) := hy _ i
    have h3 := mixedEmbedding_injective K h2
    simp only [hh, h3]
    ring
  have hGh : ∀ α, G (h α) = g (α + embPi K c) := by
    intro α
    simp only [G]
    rw [Set.indicator_of_mem (hmem α), hemb]
  refine ⟨?_, ?_⟩
  · rw [← hinj.summable_iff (f := fun ξ ↦ ‖G ξ‖) (fun ξ hξ ↦ by simp [hsupp ξ hξ])]
    simp only [Function.comp_def, hGh]
  · rw [← hinj.tsum_eq (fun ξ hξ ↦ by_contra fun hn ↦ hξ (hsupp ξ hn))]
    simp only [hGh]
end GroundTheory.Automorphic.GJMatrix
