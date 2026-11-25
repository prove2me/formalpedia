-- Prove2me | solution 1 for GlobalTheory.SingleBlock.measurableSet_Jset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:37.370649+00:00
-- url     : https://prove2.me/submissions/02aa9c85-41d1-471b-8caf-65a5f091ec14

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_intMat_eq_iUnion
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_meas_piece
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
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {r t : ℕ}
  {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}
variable [MeasurableSpace F] [BorelSpace F]
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hO : IsOpen (O : Set F)) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) [Finite (kF O ϖ hϖ)] (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) :
    MeasurableSet (Jset P) := by
  have e : Jset P = ⋃ c : {c : Fin r → Fin r → kF O ϖ hϖ //
      Vol.piece O ϖ (Vol.repM O ϖ hϖ c) ⊆ Jset P}, Vol.piece O ϖ (Vol.repM O ϖ hϖ c.1) := by
    refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun c => c.2)
    rintro _ ⟨p, hp, rfl⟩
    have h1 : (p : Matrix (Fin r) (Fin r) F) ∈ intMat O r r := (hP hp).1
    rw [Vol.intMat_eq_iUnion O ϖ hϖ] at h1
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 h1
    refine Set.mem_iUnion.2 ⟨⟨c, fun z hz => ?_⟩, hc⟩
    have hz' : z ∈ Vol.piece O ϖ (p : Matrix (Fin r) (Fin r) F) := by
      rw [Vol.mem_piece] at hz hc ⊢
      intro i j
      obtain ⟨o1, ho1, e1⟩ := hz i j
      obtain ⟨o2, ho2, e2⟩ := hc i j
      exact ⟨o1 - o2, O.sub_mem ho1 ho2, by rw [mul_sub, ← e1, ← e2]; ring⟩
    obtain ⟨κ, hκ, e⟩ := Vol.piece_sub_mul_cong O ϖ hϖ hϖ0 hloc (hP hp) hz'
    exact ⟨_, P.mul_mem hp (hKP hκ), e⟩
  rw [e]
  exact MeasurableSet.iUnion fun c => Vol.meas_piece O hO ϖ hϖ0 _
end GlobalTheory.SingleBlock
