-- Prove2me | solution 1 for OAI.Problem313.BiasedFourier.project_fourth_moment_of_noise
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:25:42.211646+00:00
-- url     : https://prove2.me/submissions/17f1a105-1d0d-4899-8600-c34eaa1688ca

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierProjection.lean:L61-L92
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BiasedFourier.project_fourth_moment_of_noise. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection
import Theorems.Thm_OAI_Problem313_lowDegree_fourth_of_noise

-- ---- from OAI.Combinatorics.SharpThreshold.FourierProjection ----
namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- Specialization of inverse-noise hypercontractivity to the canonical Fourier
projection.  The hypothesis is precisely the coefficient-form noise estimate. -/
theorem project_fourth_moment_of_noise (p rho k : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k) :
    (∑ x, weight p x * (project p L g x) ^ 4) ≤
      rho ^ (-4 * k) * (∑ S ∈ L, (coeff p g S) ^ 2) ^ 2 := by
  classical
  let c : Finset ι → ℝ := fun S => if S ∈ L then coeff p g S else 0
  have hdegree' : ∀ S, c S ≠ 0 → (S.card : ℝ) ≤ k := by
    intro S hc
    by_cases hS : S ∈ L
    · exact hdegree S hS
    · simp [c, hS] at hc
  have hnoise' : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ (S.card : ℝ) * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2 := by
    intro a
    simpa only [Real.rpow_natCast] using hnoise a
  have hbound := Problem313.lowDegree_fourth_of_noise Finset.card (char p)
    (weight p) rho k hrho hrho1 hnoise' c hdegree'
  have hsynth (x : ι → Bool) : (∑ S, c S * char p S x) = project p L g x := by
    simp [c, project, ite_mul, Finset.sum_ite_mem]
  have henergy : (∑ S, (c S) ^ 2) = ∑ S ∈ L, (coeff p g S) ^ 2 := by
    simp [c, ite_pow, Finset.sum_ite_mem]
  simpa only [hsynth, henergy] using hbound

end Problem313.BiasedFourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
open scoped BigOperators Classical


theorem solution.{u} : type_of% @_root_.OAI.Problem313.BiasedFourier.project_fourth_moment_of_noise.{u} := @_root_.OAI.Problem313.BiasedFourier.project_fourth_moment_of_noise.{u}
