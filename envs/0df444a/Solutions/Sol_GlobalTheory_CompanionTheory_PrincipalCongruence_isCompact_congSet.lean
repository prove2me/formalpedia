-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrincipalCongruence.isCompact_congSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:55:24.155612+00:00
-- url     : https://prove2.me/submissions/542517bf-bc6d-449d-bd15-5c25204f3a12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenIsCompactPrincipal
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_cball


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
    IsCompact (congSet n t) := by
  have h : congSet n t = Set.pi Set.univ fun i => Set.pi Set.univ fun j =>
      (fun x : k => x + (1 : Matrix n n k) i j) '' GlobalTheory.SplitWeil.cball (Units.mk0 t ht) := by
    ext A
    constructor
    · intro hA i _ j _
      exact ⟨A i j - (1 : Matrix n n k) i j, hA i j, by simp⟩
    · intro hA i j
      obtain ⟨x, hx, hxA⟩ := hA i (Set.mem_univ _) j (Set.mem_univ _)
      have hx' : A i j - (1 : Matrix n n k) i j = x := by
        rw [← hxA]
        simp
      rw [hx']
      exact hx
  rw [h]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    (GlobalTheory.SplitWeil.isCompact_cball _).image (continuous_id.add continuous_const)
end GlobalTheory.CompanionTheory.PrincipalCongruence
