-- Prove2me | solution 1 for GlobalTheory.CommTriang.exists_common_eigenvector_commuting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:30:03.81138+00:00
-- url     : https://prove2.me/submissions/5a7dfa03-ec7c-434a-a8b6-5c0905159a30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBisFurther
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonEigenvectorCommuting
import Theorems.Thm_GlobalTheory_CommonEigenvectorExistenceInertiaEigenvalues_target


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory GlobalTheory.CommTriang
namespace GlobalTheory.CommTriang
theorem _root_.solution {k ι V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (f : ι → Module.End k V) (hc : ∀ i j, f i * f j = f j * f i) :
    ∀ (d : ℕ) (W : Submodule k V), Module.finrank k W = d → W ≠ ⊥ → (∀ i, ∀ w ∈ W, f i w ∈ W) →
      ∃ x ∈ W, x ≠ 0 ∧ ∀ i, ∃ c : k, f i x = c • x := by
  first
  | exact @_root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target
  | exact _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target
  | (apply _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target ..)
end GlobalTheory.CommTriang
