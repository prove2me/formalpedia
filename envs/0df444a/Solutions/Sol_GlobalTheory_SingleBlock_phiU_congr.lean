-- Prove2me | solution 1 for GlobalTheory.SingleBlock.phiU_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:03:00.312273+00:00
-- url     : https://prove2.me/submissions/ba741f78-dbdc-4175-93fc-dd24a9322081

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_GlobalTheory_SingleBlock_phiU_of_notMem
import Theorems.Thm_GlobalTheory_SingleBlock_add_mem_supp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] {r t : ℕ} {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ)
    (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) (ρ : P →* ℂˣ)
    (hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub O ϖ r), ρ ⟨k, hKP hk⟩ = 1)
    {x y : Matrix (Fin r ⊕ Fin t) (Fin r) F} (hy : ∀ i j, ϖ⁻¹ * (y i j - x i j) ∈ O) :
    phiU O ϖ P ρ y = phiU O ϖ P ρ x := by
  by_cases hx : x ∈ suppSet t O ϖ P
  · exact (add_mem_supp hϖ hϖ0 hloc hKP hP ρ hρ hy hx).2
  · rw [phiU_of_notMem ρ hx, phiU_of_notMem]
    intro h
    refine hx (add_mem_supp hϖ hϖ0 hloc hKP hP ρ hρ (fun i j => ?_) h).1
    have := O.neg_mem (hy i j)
    rwa [← mul_neg, neg_sub] at this
end GlobalTheory.SingleBlock
