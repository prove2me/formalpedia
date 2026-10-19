-- Prove2me | solution 1 for OAI.Problem313.incident_mass_le_erase_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:09:06.10081+00:00
-- url     : https://prove2.me/submissions/b9802feb-bf62-44de-a627-71665701effd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/LowDegreeBounds.lean:L77-L115
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.incident_mass_le_erase_mass. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype

-- ---- from OAI.Combinatorics.SharpThreshold.LowDegreeBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u

noncomputable section

namespace Problem313

open Finset

/-- Erasing a fixed coordinate injects supports containing it into supports
of no larger degree.  This transports a derivative coefficient identity to
a low-degree mass bound, without changing the ambient coordinate type. -/
theorem incident_mass_le_erase_mass
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a b : Finset ι → ℝ) (hb : ∀ T, 0 ≤ b T) (i : ι) (k C : ℝ)
    (hC : 0 ≤ C)
    (hderiv : ∀ S, i ∈ S → a S = C * b (S.erase i)) :
    (∑ S : Finset ι, if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
      C * ∑ T : Finset ι, if (T.card : ℝ) ≤ k then b T else 0 := by
  let s : Finset (Finset ι) := univ.filter (fun S => i ∈ S ∧ (S.card : ℝ) ≤ k)
  let t : Finset (Finset ι) := univ.filter (fun T => (T.card : ℝ) ≤ k)
  have hinj : Set.InjOn (fun S : Finset ι => S.erase i) (s : Set (Finset ι)) := by
    intro S hS T hT hST
    have hiS : i ∈ S := (Finset.mem_filter.mp hS).2.1
    have hiT : i ∈ T := (Finset.mem_filter.mp hT).2.1
    simpa only [Finset.insert_erase hiS, Finset.insert_erase hiT] using
      congrArg (fun U : Finset ι => insert i U) hST
  have hsub : s.image (fun S => S.erase i) ⊆ t := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcard : ((S.erase i).card : ℝ) ≤ S.card := by
      exact_mod_cast Finset.card_erase_le (s := S) (a := i)
    exact hcard.trans (Finset.mem_filter.mp hS).2.2
  calc
    _ = ∑ S ∈ s, a S := (Finset.sum_filter _ _).symm
    _ = ∑ S ∈ s, C * b (S.erase i) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact hderiv S (Finset.mem_filter.mp hS).2.1
    _ = C * ∑ S ∈ s, b (S.erase i) := (Finset.mul_sum _ _ _).symm
    _ = C * ∑ T ∈ s.image (fun S => S.erase i), b T := by
      rw [Finset.sum_image hinj]
    _ ≤ C * ∑ T ∈ t, b T := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ => hb T)
    _ = _ := by rw [Finset.sum_filter]

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open Finset


theorem solution.{u} : type_of% @_root_.OAI.Problem313.incident_mass_le_erase_mass.{u} := @_root_.OAI.Problem313.incident_mass_le_erase_mass.{u}
