-- Prove2me | solution 1 for GlobalTheory.SingleBlock.hasCompactSupport_phiU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:32.586186+00:00
-- url     : https://prove2.me/submissions/bfecadec-ccf5-423c-a8ea-7fbfbeac4573

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Theorems.Thm_GlobalTheory_SingleBlock_phiU_of_notMem
import Theorems.Thm_GlobalTheory_SingleBlock_suppSet_subset

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
namespace GlobalTheory.SingleBlock
theorem _root_.solution [T2Space F] (hO : IsCompact (O : Set F)) (hϖ : ϖ ∈ O)
    (hP : P ≤ GLint O r) (ρ : P →* ℂˣ) : HasCompactSupport (phiU (t := t) O ϖ P ρ) := by
  have hS : IsCompact (Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => (O : Set F))) :
      Set (Matrix (Fin r ⊕ Fin t) (Fin r) F)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => hO))
  refine HasCompactSupport.intro hS fun x hx => phiU_of_notMem ρ fun h => hx ?_
  exact fun i _ j _ => suppSet_subset hϖ hP h i j
end GlobalTheory.SingleBlock
