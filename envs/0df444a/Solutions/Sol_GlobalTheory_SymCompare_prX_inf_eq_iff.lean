-- Prove2me | solution 1 for GlobalTheory.SymCompare.prX_inf_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:13:23.157771+00:00
-- url     : https://prove2.me/submissions/a3856ba1-e8c5-402c-aacc-f0d565873ee1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_SymCompare_mul_embX_mem_R

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}
namespace GlobalTheory.SymCompare
theorem _root_.solution (J : Subgroup (GL (n ⊕ Fin c) k)) : prX (R k n c 1 ⊓ J) = J.comap (embX c) ↔
    ∀ u ∈ N k n c 1, ∀ g, u * embX c g ∈ J → embX c g ∈ J := by
  constructor
  · intro h u hu g hg
    have : g ∈ prX (R k n c 1 ⊓ J) := ⟨u, hu, mul_embX_mem_R hu g, hg⟩
    rwa [h] at this
  · intro h
    ext g
    exact ⟨fun ⟨u, hu, H⟩ => h u hu g H.2, fun H => ⟨1, one_mem _, mul_embX_mem_R (one_mem _) g, by
      rw [one_mul]; exact H⟩⟩
end GlobalTheory.SymCompare
