-- Prove2me | solution 1 for OAI.Problem313.BiasedFourier.booleanDifference_project_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:29:22.534084+00:00
-- url     : https://prove2.me/submissions/edc80a94-595b-4886-b216-666150c966d2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BooleanProjection.lean:L17-L46
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BiasedFourier.booleanDifference_project_energy_le. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_BiasedFourier_project_energy_le_of_noise

-- ---- from OAI.Combinatorics.SharpThreshold.BooleanProjection ----
namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- Low-degree projection bound for a Boolean coordinate difference, with the
pivotal probability expressed by the shared generic influence definition. -/
theorem booleanDifference_project_energy_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (L : Finset (Finset ι)) (f : (ι → Bool) → Bool) (i : ι)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k) :
    (∑ S ∈ L, (coeff p
      (fun x => boolReal (f (Function.update x i true)) -
        boolReal (f (Function.update x i false))) S) ^ 2) ≤
      rho ^ (-2 * k) * (Reindex.influence p f i) ^ (3 / 2 : ℝ) := by
  let g : (ι → Bool) → ℝ := fun x =>
    boolReal (f (Function.update x i true)) -
      boolReal (f (Function.update x i false))
  have hg (x : ι → Bool) : g x = -1 ∨ g x = 0 ∨ g x = 1 := by
    cases ht : f (Function.update x i true) <;>
      cases hf : f (Function.update x i false) <;> simp [g, ht, hf, boolReal]
  have hpiv : (∑ x, if g x ≠ 0 then weight p x else 0) =
      Reindex.influence p f i := by
    unfold Reindex.influence
    apply Finset.sum_congr rfl
    intro x hx
    cases ht : f (Function.update x i true) <;>
      cases hf : f (Function.update x i false) <;>
        simp [g, ht, hf, boolReal, weight, scalarWeight, Reindex.weight]
  simpa only [hpiv] using
    project_energy_le_of_noise hp hp1 rho k hrho hrho1 hnoise L g hg hdegree

end Problem313.BiasedFourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
open scoped BigOperators Classical


theorem solution.{u} : type_of% @_root_.OAI.Problem313.BiasedFourier.booleanDifference_project_energy_le.{u} := @_root_.OAI.Problem313.BiasedFourier.booleanDifference_project_energy_le.{u}
