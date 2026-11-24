-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrincipalCongruence.isOpen_congSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:55:26.478799+00:00
-- url     : https://prove2.me/submissions/4644535c-0633-4ec6-b71c-4b163b0eca26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenIsCompactPrincipal
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrincipalCongruence
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.PrincipalCongruence
theorem _root_.solution (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsOpen (congSet n t) := by
  have h : congSet n t = ⋂ i, ⋂ j, (fun A : Matrix n n k => A i j - (1 : Matrix n n k) i j) ⁻¹'
      GlobalTheory.SplitWeil.cball (Units.mk0 t ht) := by
    ext A
    simp [congSet, GlobalTheory.SplitWeil.cball]
  rw [h]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (GlobalTheory.SplitWeil.isOpen_cball _).preimage
    ((continuous_id.matrix_elem i j).sub continuous_const)
end GlobalTheory.CompanionTheory.PrincipalCongruence
