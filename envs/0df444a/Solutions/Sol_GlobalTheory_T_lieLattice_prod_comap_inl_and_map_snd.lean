-- Prove2me | solution 1 for GlobalTheory.T.lieLattice_prod_comap_inl_and_map_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:20:11.730264+00:00
-- url     : https://prove2.me/submissions/5c67a50b-6988-42c7-94c3-b3fa5bedfa74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LieLatticeProdComapInlAndMapSnd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LieLatticeProdComapInlAndMapSndStatement
import Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_lin_fst_snd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)), M ∈ (B₁.prod B₂).Lin → M.comap (LinearMap.inl K.O B₁.A B₂.A) ∈ B₁.Lin ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) ∈ B₂.Lin := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.lin_fst_snd | exact GlobalTheory.UnitLemma.InvAlg.lin_fst_snd | (intros; apply GlobalTheory.UnitLemma.InvAlg.lin_fst_snd <;> assumption)
end _root_.GlobalTheory.T
