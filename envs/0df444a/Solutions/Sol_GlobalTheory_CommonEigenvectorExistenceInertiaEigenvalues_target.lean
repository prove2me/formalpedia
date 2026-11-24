-- Prove2me | solution 1 for GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:15:59.028982+00:00
-- url     : https://prove2.me/submissions/a29b39fa-76b0-4dd2-852c-df2a405566ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBisFurther
import Theorems.Thm_GlobalTheory_CommonEigenvectorExistenceInertiaEigenvalues_exists_common_eigenvector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues
open Module
namespace GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues
theorem _root_.solution : ∀ {k ι V : Type} [inst : Field k] [IsAlgClosed k] [inst_2 : AddCommGroup V] [inst_3 : Module k V] [FiniteDimensional k V] (f : ι → Module.End k V), (∀ (i j : ι), f i * f j = f j * f i) → ∀ (d : ℕ) (W : Submodule k V), Module.finrank k ↥W = d → W ≠ ⊥ → (∀ (i : ι), ∀ w ∈ W, (f i : V → V) w ∈ W) → ∃ x ∈ W, x ≠ (0 : V) ∧ ∀ (i : ι), ∃ (c : k), (f i : V → V) x = c • x :=
  fun f hc => exists_common_eigenvector f hc
end GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues
