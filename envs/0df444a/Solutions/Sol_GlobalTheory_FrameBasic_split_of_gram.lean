-- Prove2me | solution 1 for GlobalTheory.FrameBasic.split_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:28:15.081945+00:00
-- url     : https://prove2.me/submissions/db9a3a23-5c8c-497a-9ba7-6164a49daecd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Theorems.Thm_GlobalTheory_FrameBasic_mem_perp_span
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameBasic
theorem _root_.solution (L : LocE F E) [IsArtinianRing E] {n : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (h : IsHerm L H) {ι : Type} [Fintype ι] (g : ι → Fin n → E)
    (hg : ∀ α : ι → E, (∀ j, ∑ i, α i * hf L H (g i) (g j) = 0) → α = 0) :
    LinearIndependent E g ∧
      IsCompl (Submodule.span E (Set.range g)) (perp L H (Submodule.span E (Set.range g))) := by
  have key : ∀ (α : ι → E) (y : Fin n → E),
      hf L H (∑ i, α i • g i) y = ∑ i, α i * hf L H (g i) y := fun α y => by
    change hfL L H y _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
  let φ : (ι → E) →ₗ[E] (ι → E) :=
    LinearMap.pi fun j => (hfL L H (g j)).comp (Fintype.linearCombination E g)
  have hφ : ∀ α j, φ α j = hf L H (∑ i, α i • g i) (g j) := fun α j => by
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Fintype.linearCombination_apply]; rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro α hα
    refine hg α fun j => ?_
    rw [← key, ← hφ, hα]; rfl
  have hsurj := (IsArtinian.bijective_of_injective_endomorphism φ hinj).2
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro α hα
    have : α = 0 := hg α fun j => by rw [← key, hα]; simp [hf]
    simp [this]
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [mem_perp_span L h] at hx'
    obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    have : α = 0 := hg α fun j => by rw [← key, hx']
    simp [this]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨α, hα⟩ := hsurj fun j => hf L H v (g j)
    refine Submodule.mem_sup.2 ⟨∑ i, α i • g i,
      (Submodule.mem_span_range_iff_exists_fun E).2 ⟨α, rfl⟩, v - ∑ i, α i • g i, ?_, by simp⟩
    rw [mem_perp_span L h]
    intro j
    change hfL L H (g j) _ = 0
    rw [map_sub]
    have := congrFun hα j
    rw [hφ] at this
    exact sub_eq_zero.2 this.symm
end GlobalTheory.FrameBasic
