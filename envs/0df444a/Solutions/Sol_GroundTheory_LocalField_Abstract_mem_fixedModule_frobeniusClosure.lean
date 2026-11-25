-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.mem_fixedModule_frobeniusClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:22:33.618201+00:00
-- url     : https://prove2.me/submissions/3f1d93ec-3dd2-4b40-b128-e4719092f328

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Theorems.Thm_GroundTheory_LocalField_Abstract_le_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_mem_frobeniusClosure_self
import Theorems.Thm_GroundTheory_LocalField_Abstract_frobeniusClosure_le
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {A : Type*} [CommGroup A] [MulDistribMulAction G A]
    [IsDiscreteModule G A] {a : A} :
    a ∈ fixedModule A (frobeniusClosure d L σ) ↔ a ∈ fixedModule A (L ⊓ d.ker) ∧ σ • a = a := by
  constructor
  · intro ha
    exact ⟨fixedModule_anti le_frobeniusClosure ha, ha σ mem_frobeniusClosure_self⟩
  · rintro ⟨ha, hσa⟩
    have hS : IsClosed (MulAction.stabilizer G a : Set G) :=
      Subgroup.isClosed_of_isOpen _ (IsDiscreteModule.isOpen_stabilizer a)
    have hle : frobeniusClosure d L σ ≤ MulAction.stabilizer G a :=
      frobeniusClosure_le hS (MulAction.mem_stabilizer_iff.2 hσa) fun g hg => ha g hg
    exact fun g hg => MulAction.mem_stabilizer_iff.1 (hle hg)
end GroundTheory.LocalField.Abstract
