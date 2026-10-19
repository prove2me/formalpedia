-- Prove2me | solution 1 for OAI.Problem313.RestrictionInfluence.join_update
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:48:36.608288+00:00
-- url     : https://prove2.me/submissions/12e60e12-212a-413b-85c3-50d89dca96a1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/RestrictionInfluence.lean:L69-L84
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.RestrictionInfluence.join_update. The node keeps its source
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

-- ---- from OAI.Combinatorics.SharpThreshold.RestrictionInfluence ----
namespace OAI

universe u

/-! Finite-product averaging for pivotal influences under restrictions. -/
noncomputable section
open scoped BigOperators

namespace Problem313.RestrictionInfluence

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

variable (P : ι → Prop) [DecidablePred P]

omit [Fintype ι] in
/-- Updating a free coordinate commutes with gluing an exterior configuration. -/
theorem join_update (x : {i // P i} → Bool) (y : {i // ¬ P i} → Bool)
    (i : {i // P i}) (b : Bool) :
    join P (Function.update x i b) y = Function.update (join P x y) i.val b := by
  classical
  funext j
  by_cases hji : j = i.val
  · subst j
    simp [join, i.property]
  · by_cases hj : P j
    · have hsub : (⟨j, hj⟩ : {i // P i}) ≠ i := by
        intro h
        exact hji (congrArg Subtype.val h)
      simp [join, hj, hji, hsub]
    · simp [join, hj, hji]

end Problem313.RestrictionInfluence

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.RestrictionInfluence
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.Problem313.RestrictionInfluence.join_update.{u} := @_root_.OAI.Problem313.RestrictionInfluence.join_update.{u}
