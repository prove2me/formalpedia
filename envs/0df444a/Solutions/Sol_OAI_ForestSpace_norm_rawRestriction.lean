-- Prove2me | solution 1 for OAI.ForestSpace.norm_rawRestriction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:46:28.384661+00:00
-- url     : https://prove2.me/submissions/d49f0c62-5706-44ef-bd66-c4a848a3b98d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Polar.lean:L22-L34
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.norm_rawRestriction. The node keeps its source
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

-- ---- from OAI.Analysis.ForestSpace.Polar ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section PolarTests
variable {V : Type} [PartialOrder V]

 theorem norm_rawRestriction (x : FullDual V) : ‖rawRestriction x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (rawRestriction x).opNorm_le_bound (norm_nonneg x)
    intro u
    simpa only [rawRestriction_apply, UniformSpace.Completion.norm_coe]
      using x.le_opNorm (u : J V)
  · apply x.opNorm_le_bound (norm_nonneg _)
    intro u
    refine UniformSpace.Completion.induction_on u
      (isClosed_le x.continuous.norm (continuous_const.mul continuous_norm)) ?_
    intro v
    simpa only [← rawRestriction_apply, UniformSpace.Completion.norm_coe]
      using (rawRestriction x).le_opNorm v

end PolarTests

section CoordinateCompletion
variable {W : Type} [PartialOrder W]
variable {V : Type} [PartialOrder V]

end CoordinateCompletion

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.norm_rawRestriction := @_root_.OAI.ForestSpace.norm_rawRestriction
