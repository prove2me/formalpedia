-- Prove2me | solution 1 for OAI.ForestSpace.averageModulus_lower_of_subspaces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:56:11.602825+00:00
-- url     : https://prove2.me/submissions/a6a6bffb-2b07-4539-978d-550ce4d79d9a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/ModulusProofs.lean:L68-L91
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.averageModulus_lower_of_subspaces. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections

-- ---- from OAI.Analysis.ForestSpace.ModulusProofs ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section ModulusDefinitions

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E}

 theorem cofinite_nontrivial (hI : ¬FiniteDimensional ℝ E) (F : Cofinite E) :
    Nontrivial F.val := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hss
  let := hss
  let : FiniteDimensional ℝ F.val := Module.Finite.of_injective
    (0 : F.val →ₗ[ℝ] ℝ) (fun _ _ _ => Subsingleton.elim _ _)
  let : FiniteDimensional ℝ (E ⧸ F.val) := F.property.2
  exact hI (Module.Finite.of_submodule_quotient F.val)

 theorem cofinite_exists_unit (hI : ¬FiniteDimensional ℝ E) (F : Cofinite E) :
    ∃ y : E, y ∈ F.val ∧ ‖y‖ = 1 := by
  let := cofinite_nontrivial hI F
  obtain ⟨y,hy⟩ := exists_norm_eq F.val zero_le_one
  exact ⟨y,y.property,hy⟩

 theorem averageValues_nonempty (hI : ¬FiniteDimensional ℝ E)
    (t : ℝ) (x : E) (F : Cofinite E) : (averageValues E norm t x F).Nonempty := by
  obtain ⟨y,hy,hyn⟩ := cofinite_exists_unit hI F
  exact ⟨_,y,hy,hyn,rfl⟩

 theorem averageValues_bddBelow (t : ℝ) (x : E) (F : Cofinite E) :
    BddBelow (averageValues E norm t x F) := by
  refine ⟨-1, ?_⟩
  rintro a ⟨y,hy,hyn,rfl⟩
  linarith [norm_nonneg (x+t•y),norm_nonneg (x-t•y)]

 theorem averageInner_le (hI : ¬FiniteDimensional ℝ E)
    {t : ℝ} (ht : 0 ≤ t) {x : E} (hx : ‖x‖ = 1) (F : Cofinite E) :
    averageInner E norm t x F ≤ t := by
  obtain ⟨y,hy,hyn⟩ := cofinite_exists_unit hI F
  have hp := norm_add_le x (t•y)
  have hm := norm_sub_le x (t•y)
  rw [hx,norm_smul,Real.norm_of_nonneg ht,hyn,mul_one] at hp hm
  have hh : averageInner E norm t x F ≤ (‖x+t•y‖+‖x-t•y‖)/2-1 :=
    csInf_le (averageValues_bddBelow t x F) ⟨y,hy,hyn,rfl⟩
  linarith

 theorem averageCenter_bddAbove (hI : ¬FiniteDimensional ℝ E)
    {t : ℝ} (ht : 0 ≤ t) {x : E} (hx : ‖x‖ = 1) :
    BddAbove (Set.range (averageInner E norm t x)) := by
  exact ⟨t, fun a ⟨F,hF⟩ => hF ▸ averageInner_le hI ht hx F⟩

/-- A quantitative subspace formulation implies the literal inf-sup-inf bound.
The nonempty-inner-sphere and bounded-supremum details are explicit. -/
 theorem averageModulus_lower_of_subspaces (hI : ¬FiniteDimensional ℝ E)
    {t L : ℝ} (ht : 0 ≤ t)
    (h : ∀ x : E, ‖x‖ = 1 → ∀ ε : ℝ, 0 < ε → ∃ F : Cofinite E,
      ∀ y : E, y ∈ F.val → ‖y‖ = 1 → L-ε ≤ (‖x+t•y‖+‖x-t•y‖)/2-1) :
    L ≤ averageModulus E norm t := by
  have hunit : ∃ x : E, ‖x‖ = 1 := by
    obtain ⟨x,hx,hxn⟩ := cofinite_exists_unit hI (cofiniteTop E)
    exact ⟨x,hxn⟩
  apply le_csInf
  · obtain ⟨x,hx⟩ := hunit
    exact ⟨_,x,hx,rfl⟩
  · rintro a ⟨x,hx,rfl⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨F,hF⟩ := h x hx ε hε
    have hb : L-ε ≤ averageInner E norm t x F := by
      apply le_csInf (averageValues_nonempty hI t x F)
      rintro b ⟨y,hy,hyn,rfl⟩
      exact hF y hy hyn
    have hs : averageInner E norm t x F ≤ averageCenter E norm t x :=
      le_csSup (averageCenter_bddAbove hI ht hx) ⟨F,rfl⟩
    linarith

end ModulusDefinitions

section ForestModulus
variable {V : Type} [PartialOrder V]

end ForestModulus

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.averageModulus_lower_of_subspaces := @_root_.OAI.ForestSpace.averageModulus_lower_of_subspaces
