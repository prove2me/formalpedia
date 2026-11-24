-- Prove2me | solution 1 for GlobalTheory.isDiscrete_ker_mkQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:49.177264+00:00
-- url     : https://prove2.me/submissions/237ea838-b490-4e45-b144-34e183fbdb5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk

set_option autoImplicit false
open Filter Topology Set
open GlobalTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
namespace GlobalTheory
theorem _root_.solution {M : Type*} [AddCommGroup M] [TopologicalSpace M] (Λ : Submodule ℤ M)
    [DiscreteTopology Λ] : IsDiscrete (Λ.mkQ.toAddMonoidHom.ker : Set M) := by
  have : (Λ.mkQ.toAddMonoidHom.ker : Set M) = Λ := by
    ext x
    exact Submodule.Quotient.mk_eq_zero Λ
  rw [this]
  exact DiscreteTopology.isDiscrete
end GlobalTheory
