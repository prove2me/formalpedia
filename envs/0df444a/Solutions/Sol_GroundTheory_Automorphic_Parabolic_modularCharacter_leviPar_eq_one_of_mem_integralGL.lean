-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.modularCharacter_leviPar_eq_one_of_mem_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:49:23.234811+00:00
-- url     : https://prove2.me/submissions/e015f313-4d76-43e7-981e-cd3c31eb8602

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Measures_LinearChart_modularCharacter_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa MeasureTheory Measure Topology Set ValuativeRel Measures
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α α' : Type*} [LinearOrder α] [LinearOrder α'] (γ : Fin n → α) (δ : Fin n → α')
variable {F n γ δ}
variable (F n γ δ)
variable {F n γ δ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (l : leviPar F n γ δ)
    (hl : (l : GL (Fin n) F) ∈ GLnLocal.integralGL F n) : modularCharacter l = 1 := by
  borelize F ↥(leviPar F n γ δ)
  let V : OpenSubgroup (leviPar F n γ δ) :=
    ⟨(GLnLocal.integralGL F n).subgroupOf (leviPar F n γ δ),
      (GLnLocal.isOpen_integralGL F n).preimage continuous_subtype_val⟩
  have hV : IsCompact (V : Set (leviPar F n γ δ)) :=
    (isClosed_leviPar F n γ δ).isClosedEmbedding_subtypeVal.isCompact_preimage
      (GLnLocal.isCompact_integralGL F n)
  obtain ⟨h1, h2⟩ := (leviParChart F n γ δ).modulus_eq_one_of_mem hV (v := l) hl
  rw [(leviParChart F n γ δ).modularCharacter_eq, h1, h2, div_one]
end GroundTheory.Automorphic.Parabolic
