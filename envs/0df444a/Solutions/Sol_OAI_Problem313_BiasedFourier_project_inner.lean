-- Prove2me | solution 1 for OAI.Problem313.BiasedFourier.project_inner
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:24:14.591346+00:00
-- url     : https://prove2.me/submissions/8558a4d0-320c-47a9-86b7-578024131f41

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierProjection.lean:L23-L42
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BiasedFourier.project_inner. The node keeps its source
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

-- ---- from OAI.Combinatorics.SharpThreshold.FourierProjection ----
namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- Pairing a function with its projection gives its selected Fourier energy. -/
theorem project_inner (p : ℝ) (L : Finset (Finset ι)) (g : (ι → Bool) → ℝ) :
    (∑ x, weight p x * g x * project p L g x) =
      ∑ S ∈ L, (coeff p g S) ^ 2 := by
  classical
  unfold project
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  calc
    (∑ x, weight p x * g x * (coeff p g S * char p S x)) =
        coeff p g S * (∑ x, weight p x * g x * char p S x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (coeff p g S) ^ 2 := by
      change coeff p g S * coeff p g S = (coeff p g S) ^ 2
      ring

end Problem313.BiasedFourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
open scoped BigOperators Classical


theorem solution.{u} : type_of% @_root_.OAI.Problem313.BiasedFourier.project_inner.{u} := @_root_.OAI.Problem313.BiasedFourier.project_inner.{u}
