-- Prove2me | solution 1 for OAI.Problem313.lowDegree_bound_of_projection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:10:38.776905+00:00
-- url     : https://prove2.me/submissions/6426bc41-1375-4840-ae49-2aa3ab955851

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/LowDegreeBounds.lean:L117-L161
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.lowDegree_bound_of_projection. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_incident_mass_le_erase_mass
import Theorems.Thm_OAI_Problem313_lowDegree_mass_le_incident_mass
import Theorems.Thm_OAI_Problem313_low_degree_influence_bound
import Theorems.Thm_OAI_Problem313_noise_loss_le_rpow

-- ---- from OAI.Combinatorics.SharpThreshold.LowDegreeInfluence ----
namespace OAI

universe u

noncomputable section

namespace Problem313

/-- Version accepting the hypercontractive factor before its power bound is substituted. -/
theorem low_degree_influence_bound_of_factor {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (m I A R L : ℝ)
    (hm : 1 ≤ m) (ha : ∀ i, 0 ≤ a i)
    (hsum : ∑ i, a i = I) (hindividual : ∀ i, a i ≤ I/m)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hR : R ≤ m ^ (1/16 : ℝ)) (hL1 : L ≤ 1)
    (hprojection : L ≤ A * R * ∑ i, (a i) ^ (3/2 : ℝ)) :
    L ≤ m ^ (-1/4 : ℝ) * I := by
  apply low_degree_influence_bound a m I A L hm ha hsum hindividual hA0 hA1 hL1
  exact hprojection.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hR hA0)
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (ha i) _))

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.LowDegreeBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u

noncomputable section

namespace Problem313

open Finset

/-- Assemble coordinatewise low-degree estimates without any choice of a
single coordinate common to all supports. -/
theorem lowDegree_mass_le_of_coordinate_bound
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) (ha : ∀ S, 0 ≤ a S) (k C : ℝ)
    (J : ι → ℝ)
    (hcoord : ∀ i, (∑ S : Finset ι,
      if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) ≤ C * J i) :
    (∑ S : Finset ι, if S.Nonempty ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
      C * ∑ i : ι, J i := by
  calc
    _ ≤ ∑ i : ι, ∑ S : Finset ι,
        if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0 :=
      lowDegree_mass_le_incident_mass a ha k
    _ ≤ ∑ i : ι, C * J i := Finset.sum_le_sum (fun i _ => hcoord i)
    _ = C * ∑ i : ι, J i := (Finset.mul_sum _ _ _).symm

/-- The complete low-degree estimate once the analytic Fourier ingredients
are supplied: the derivative coefficient identity and the low-degree
projection bound.  All incidence counting, bias constants, and the
small/large total-influence split are discharged here. -/
theorem lowDegree_bound_of_projection
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) (b : ι → Finset ι → ℝ) (J : ι → ℝ)
    (σ m : ℝ) (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2) (hm : 1 ≤ m)
    (ha : ∀ S, 0 ≤ a S) (hb : ∀ i S, 0 ≤ b i S)
    (hJ : ∀ i, 0 ≤ J i) (horbit : ∀ i, J i ≤ (∑ j, J j) / m)
    (henergy : (∑ S : Finset ι, a S) ≤ 1)
    (hderiv : ∀ i S, i ∈ S → a S = σ ^ 2 * b i (S.erase i))
    (hprojection : ∀ i,
      (∑ S : Finset ι, if (S.card : ℝ) ≤ σ * Real.log m / 64 then b i S else 0) ≤
        (σ / 4) ^ (-(2 : ℝ) * (σ * Real.log m / 64)) * (J i) ^ (3 / 2 : ℝ)) :
    (∑ S : Finset ι,
      if S.Nonempty ∧ (S.card : ℝ) ≤ σ * Real.log m / 64 then a S else 0) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, J i := by
  let k : ℝ := σ * Real.log m / 64
  let R : ℝ := (σ / 4) ^ (-(2 : ℝ) * k)
  let L : ℝ := ∑ S : Finset ι, if S.Nonempty ∧ (S.card : ℝ) ≤ k then a S else 0
  have hL1 : L ≤ 1 := by
    apply le_trans _ henergy
    apply Finset.sum_le_sum
    intro S hS
    split_ifs
    · exact le_refl _
    · exact ha S
  have hcoord : ∀ i,
      (∑ S : Finset ι, if i ∈ S ∧ (S.card : ℝ) ≤ k then a S else 0) ≤
        (σ ^ 2 * R) * (J i) ^ (3 / 2 : ℝ) := by
    intro i
    calc
      _ ≤ σ ^ 2 * ∑ S : Finset ι, if (S.card : ℝ) ≤ k then b i S else 0 :=
        incident_mass_le_erase_mass a (b i) (hb i) i k (σ ^ 2)
          (sq_nonneg σ) (hderiv i)
      _ ≤ σ ^ 2 * (R * (J i) ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hprojection i) (sq_nonneg σ)
      _ = _ := by ring
  have hproj : L ≤ σ ^ 2 * R * ∑ i, (J i) ^ (3 / 2 : ℝ) :=
    lowDegree_mass_le_of_coordinate_bound a ha k (σ ^ 2 * R)
      (fun i => (J i) ^ (3 / 2 : ℝ)) hcoord
  have hσsq : σ ^ 2 ≤ 1 := by nlinarith
  exact low_degree_influence_bound_of_factor J m (∑ i, J i) (σ ^ 2) R L
    hm hJ rfl horbit (sq_nonneg σ) hσsq (noise_loss_le_rpow hσ hσhalf hm) hL1 hproj

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open Finset


theorem solution.{u} : type_of% @_root_.OAI.Problem313.lowDegree_bound_of_projection.{u} := @_root_.OAI.Problem313.lowDegree_bound_of_projection.{u}
