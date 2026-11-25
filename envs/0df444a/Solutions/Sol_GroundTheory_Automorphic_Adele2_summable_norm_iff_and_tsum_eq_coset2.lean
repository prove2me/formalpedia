-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.summable_norm_iff_and_tsum_eq_coset2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:06:10.18447+00:00
-- url     : https://prove2.me/submissions/5cff6c4e-3cd8-483e-9f98-438983f08606

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Automorphic.Adele2
theorem _root_.solution (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : Fin 2 → K) (g : (Fin 2 → mixedSpace K) → ℂ) :
    (Summable (fun ξ => ‖(coset2 K I c).indicator (fun ξ => g (emb2 K ξ)) ξ‖) ↔
      Summable (fun α : idealLattice2 I => ‖g (α + emb2 K c)‖)) ∧
      ∑' ξ, (coset2 K I c).indicator (fun ξ => g (emb2 K ξ)) ξ =
        ∑' α : idealLattice2 I, g (α + emb2 K c) := by
  have hpre : ∀ α : idealLattice2 I, ∀ i, ∃ y ∈ ((I i : FractionalIdeal (𝓞 K)⁰ K) : Set K),
      mixedEmbedding K y = (α : Fin 2 → mixedSpace K) i := fun α i =>
    (mem_idealLattice K (I i)).mp (mem_idealLattice2.mp α.2 i)
  choose y hyI hy using hpre
  set h : idealLattice2 I → Fin 2 → K := fun α i => c i + y α i with hh
  have hinj : Function.Injective h := by
    intro α β hαβ
    apply Subtype.ext
    funext i
    have h1 : y α i = y β i := add_left_cancel (congrFun hαβ i)
    rw [← hy α i, ← hy β i, h1]
  have hmem : ∀ α, h α ∈ coset2 K I c := fun α i => by
    simp only [hh, add_sub_cancel_left]
    exact hyI α i
  have hemb : ∀ α, emb2 K (h α) = (α : Fin 2 → mixedSpace K) + emb2 K c := by
    intro α
    funext i
    simp only [emb2, hh, Pi.add_apply, map_add, hy α i, add_comm]
  set G : (Fin 2 → K) → ℂ := (coset2 K I c).indicator (fun ξ => g (emb2 K ξ))
  have hsupp : ∀ ξ ∉ Set.range h, G ξ = 0 := by
    intro ξ hξ
    refine Set.indicator_of_notMem (fun hm => hξ ?_) _
    have hα : emb2 K (fun i => ξ i - c i) ∈ idealLattice2 I := by
      rw [mem_idealLattice2]
      intro i
      exact (mem_idealLattice K (I i)).mpr ⟨ξ i - c i, hm i, rfl⟩
    refine ⟨⟨_, hα⟩, funext fun i => ?_⟩
    have h2 : mixedEmbedding K (y ⟨_, hα⟩ i) = mixedEmbedding K (ξ i - c i) := hy _ i
    have h3 := mixedEmbedding_injective K h2
    simp only [hh, h3]
    ring
  have hGh : ∀ α, G (h α) = g (α + emb2 K c) := by
    intro α
    simp only [G]
    rw [Set.indicator_of_mem (hmem α), hemb]
  refine ⟨?_, ?_⟩
  · rw [← hinj.summable_iff (f := fun ξ => ‖G ξ‖) (fun ξ hξ => by simp [hsupp ξ hξ])]
    simp only [Function.comp_def, hGh]
  · rw [← hinj.tsum_eq (fun ξ hξ => by_contra fun hn => hξ (hsupp ξ hn))]
    simp only [hGh]
end GroundTheory.Automorphic.Adele2
