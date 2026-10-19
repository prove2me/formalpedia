-- Prove2me | solution 1 for OAI.Problem313.RestrictionInfluence.sum_weight_join
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:45:59.427219+00:00
-- url     : https://prove2.me/submissions/aa7973a3-b965-4584-9ab4-94a2492af343

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/RestrictionInfluence.lean:L50-L67
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.RestrictionInfluence.sum_weight_join. The node keeps its source
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

omit [DecidableEq ι] in
/-- Product weights factor across any coordinate partition. -/
theorem weight_join (p : ℝ) (x : {i // P i} → Bool)
    (y : {i // ¬ P i} → Bool) :
    weight p (join P x y) = weight p x * weight p y := by
  unfold weight
  rw [← Fintype.prod_subtype_mul_prod_subtype P]
  simp only [join_pos, join_neg]

/-- Fubini for a coordinate restriction, with the exterior sum outermost. -/
theorem sum_weight_join (p : ℝ) (g : (ι → Bool) → ℝ) :
    (∑ z, weight p z * g z) =
      ∑ y : {i // ¬ P i} → Bool, weight p y *
        ∑ x : {i // P i} → Bool, weight p x * g (join P x y) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => Bool)
  rw [← e.symm.sum_comp (fun z => weight p z * g z)]
  change (∑ z : ({i // P i} → Bool) × ({i // ¬ P i} → Bool),
    weight p (join P z.1 z.2) * g (join P z.1 z.2)) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [weight_join]
  ring

end Problem313.RestrictionInfluence

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.RestrictionInfluence
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.Problem313.RestrictionInfluence.sum_weight_join.{u} := @_root_.OAI.Problem313.RestrictionInfluence.sum_weight_join.{u}
