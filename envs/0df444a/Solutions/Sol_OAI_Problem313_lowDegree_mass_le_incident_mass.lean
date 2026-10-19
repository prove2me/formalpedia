-- Prove2me | solution 1 for OAI.Problem313.lowDegree_mass_le_incident_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:07:30.709485+00:00
-- url     : https://prove2.me/submissions/ba4f0299-86f7-4b49-8982-16f8bc1b2478

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/LowDegreeBounds.lean:L18-L46
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.lowDegree_mass_le_incident_mass. The node keeps its source
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
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u

noncomputable section

namespace Problem313

open Finset

/-- Every nonempty low-degree Fourier support is counted by at least one of
its incident coordinate sums.  This is purely finite, nonnegative double counting. -/
theorem lowDegree_mass_le_incident_mass
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) (ha : ∀ S, 0 ≤ a S) (k : ℝ) :
    (∑ S : Finset ι, if S.Nonempty ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
      ∑ i : ι, ∑ S : Finset ι, if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro S hS
  by_cases h : S.Nonempty ∧ (S.card : ℝ) ≤ k
  · rw [ite_eq_left h]
    obtain ⟨i, hi⟩ := h.1
    calc
      a S = (if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) := by simp [hi, h.2]
      _ ≤ ∑ j : ι, if j ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0 := by
        apply Finset.single_le_sum (f := fun j : ι =>
          if j ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) (s := Finset.univ)
        · intro j hj
          split_ifs
          · exact ha S
          · exact le_refl 0
        · exact Finset.mem_univ i
  · rw [ite_eq_right h]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact ha S
    · exact le_refl 0

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open Finset


theorem solution.{u} : type_of% @_root_.OAI.Problem313.lowDegree_mass_le_incident_mass.{u} := @_root_.OAI.Problem313.lowDegree_mass_le_incident_mass.{u}
