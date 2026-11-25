-- Prove2me | solution 1 for GroundTheory.Automorphic.isCompact_maxCompact_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:32:46.506142+00:00
-- url     : https://prove2.me/submissions/e2e2b8d2-99db-48f4-96e0-c6cac92c08c5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isClosed
import Theorems.Thm_GroundTheory_Automorphic_isCompact_unitaryGroup_entries
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a


attribute [local simp] GroundTheory.Automorphic.conjCME_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
open Matrix
open scoped Matrix.Norms.L2Operator
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic
theorem _root_.solution {G : Subgroup (Matrix ι ι 𝕜)ˣ}
    (hG : IsClosed (G : Set (Matrix ι ι 𝕜)ˣ)) :
    IsCompact ((maxCompact G : Subgroup G) : Set G) := by
  set e : G → Matrix ι ι 𝕜 := fun x => ((x : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) with he
  have hemb : Topology.IsEmbedding e :=
    Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  rw [hemb.isCompact_iff]
  set S := (Matrix.unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜))
  have himg : e '' (maxCompact G : Set G) = S ∩ range e := by
    ext a
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hg, g, rfl⟩
    · rintro ⟨ha, g, rfl⟩
      exact ⟨g, ha, rfl⟩
  rw [himg]
  refine isCompact_unitaryGroup_entries.of_isClosed_subset ?_ inter_subset_left
  refine isClosed_of_closure_subset fun a ha => ?_
  have haS : a ∈ S :=
    (closure_mono inter_subset_left |>.trans isCompact_unitaryGroup_entries.isClosed.closure_subset) ha
  set u : (Matrix ι ι 𝕜)ˣ :=
    ⟨a, star a, Matrix.mem_unitaryGroup_iff.1 haS, Matrix.mem_unitaryGroup_iff'.1 haS⟩
  have hu : u ∈ closure (G : Set (Matrix ι ι 𝕜)ˣ) := by
    rw [Units.isOpenEmbedding_val.isInducing.closure_eq_preimage_closure_image]
    refine closure_mono ?_ ha
    rintro _ ⟨-, g, rfl⟩
    exact ⟨g, g.2, rfl⟩
  have huG : u ∈ G := hG.closure_subset hu
  exact ⟨haS, ⟨u, huG⟩, rfl⟩
end GroundTheory.Automorphic
