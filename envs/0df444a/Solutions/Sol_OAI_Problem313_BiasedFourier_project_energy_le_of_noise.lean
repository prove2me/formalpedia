-- Prove2me | solution 1 for OAI.Problem313.BiasedFourier.project_energy_le_of_noise
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:27:36.10084+00:00
-- url     : https://prove2.me/submissions/b2456cfc-f370-4356-b04c-5ca568876423

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierProjection.lean:L94-L118
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BiasedFourier.project_energy_le_of_noise. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_BiasedFourier_char_inner_product
import Theorems.Thm_OAI_Problem313_BiasedFourier_project_fourth_moment_of_noise
import Theorems.Thm_OAI_Problem313_BiasedFourier_project_inner
import Theorems.Thm_OAI_Problem313_WeightedProjection_second_moment_synthesis
import Theorems.Thm_OAI_Problem313_weighted_projection_noise_bound

-- ---- from OAI.Combinatorics.SharpThreshold.FourierProjection ----
namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- The squared norm of a Fourier projection is its selected Fourier energy. -/
theorem project_second_moment {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * (project p L g x) ^ 2) =
      ∑ S ∈ L, (coeff p g S) ^ 2 := by
  classical
  simpa only [project, WeightedProjection.synthesis] using
    WeightedProjection.second_moment_synthesis (weight p) (char p)
      (char_inner_product hp hp1) L (coeff p g)

/-- The defining orthogonality identity needed by the projection/Hölder estimate. -/
theorem project_inner_eq_second_moment {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * g x * project p L g x) =
      ∑ x, weight p x * (project p L g x) ^ 2 := by
  rw [project_inner, project_second_moment hp hp1]

/-- The concrete Fourier projection estimate for ternary-valued functions,
including Boolean coordinate differences. -/
theorem project_energy_le_of_noise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ)
    (hg : ∀ x, g x = -1 ∨ g x = 0 ∨ g x = 1)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k) :
    (∑ S ∈ L, (coeff p g S) ^ 2) ≤
      rho ^ (-2 * k) *
        (∑ x, if g x ≠ 0 then weight p x else 0) ^ (3 / 2 : ℝ) := by
  have hw (x : ι → Bool) : 0 ≤ weight p x := by
    unfold weight
    apply Finset.prod_nonneg
    intro i hi
    unfold scalarWeight
    split_ifs <;> linarith
  have hfour := project_fourth_moment_of_noise p rho k hrho hrho1 hnoise L g hdegree
  have hbound := Problem313.weighted_projection_noise_bound (weight p) g (project p L g)
    hw hg rho k hrho.le (project_inner_eq_second_moment hp hp1 L g)
    (by simpa only [project_second_moment hp hp1] using hfour)
  simpa only [project_second_moment hp hp1] using hbound

end Problem313.BiasedFourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
open scoped BigOperators Classical


theorem solution.{u} : type_of% @_root_.OAI.Problem313.BiasedFourier.project_energy_le_of_noise.{u} := @_root_.OAI.Problem313.BiasedFourier.project_energy_le_of_noise.{u}
