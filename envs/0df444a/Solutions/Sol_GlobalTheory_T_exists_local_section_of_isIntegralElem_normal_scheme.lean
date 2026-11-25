-- Prove2me | solution 1 for GlobalTheory.T.exists_local_section_of_isIntegralElem_normal_scheme
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:17:10.52256+00:00
-- url     : https://prove2.me/submissions/d1652edb-d6c1-4817-9672-ec81ac172b57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLocalSectionOfIsIntegralElemNormalScheme
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLocalSectionOfIsIntegralElemNormalSchemeStatement
import Theorems.Thm_GlobalTheory_exists_section_of_isIntegralElem_of_isOpenImmersion


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
theorem _root_.solution : ∀ {T Z : Scheme.{0}} [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z] (j : T ⟶ Z) [IsOpenImmersion j],
    Dense (Set.range j) → ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (j.app U).hom.IsIntegralElem s →
    ∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s := by
  first | exact @GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion | exact GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion | (intros; apply GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion <;> assumption)
end _root_.GlobalTheory.T
