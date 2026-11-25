-- Prove2me | solution 1 for GlobalTheory.T.exists_section_extending_of_dense_openImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:21:56.444049+00:00
-- url     : https://prove2.me/submissions/eba93a32-406d-46a9-b8d7-b1204342cb60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueOfDenseOpenImmersion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueOfDenseOpenImmersionStatement
import Theorems.Thm_GlobalTheory_glue_of_dense_openImmersion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j], Dense (Set.range j) →
    ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) →
    ∃ h : Γ(Z, U), j.app U h = s := by
  first | exact @GlobalTheory.glue_of_dense_openImmersion | exact GlobalTheory.glue_of_dense_openImmersion | (intros; apply GlobalTheory.glue_of_dense_openImmersion <;> assumption)
end _root_.GlobalTheory.T
