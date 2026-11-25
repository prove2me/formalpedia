-- Prove2me | solution 1 for GlobalTheory.SingleBlock.exists_of_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:51:33.000166+00:00
-- url     : https://prove2.me/submissions/12124909-9424-44ea-b971-d7b6092fad6b

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_mem_piece
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_piece_sub_mul_cong


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
    (hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub O ϖ r), ρ ⟨k, hKP hk⟩ = 1) (k : P)
    {m : Matrix (Fin r) (Fin r) F}
    (hm : m - ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈ IIset O ϖ) :
    ∃ k' : P, ((k' : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = m ∧ ρ k' = ρ k := by
  obtain ⟨κ, hκ, e⟩ := Vol.piece_sub_mul_cong O ϖ hϖ hϖ0 hloc (hP k.2) (Vol.mem_piece.2 hm)
  exact ⟨k * ⟨κ, hKP hκ⟩, e, by rw [map_mul, hρ κ hκ, mul_one]⟩
end GlobalTheory.SingleBlock
