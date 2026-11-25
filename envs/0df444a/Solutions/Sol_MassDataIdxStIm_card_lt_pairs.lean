-- Prove2me | solution 1 for MassDataIdxStIm.card_lt_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:30:48.757015+00:00
-- url     : https://prove2.me/submissions/642826b6-2f12-4a8f-b0e6-1c8ae1032b0a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_LeviEmbeddingBlock32
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_Block31OfBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open MassDataIdxStIm
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
namespace MassDataIdxStIm
theorem _root_.solution (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hoff : ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2)).card = n * (n - 1) := by
    have h1 : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) =
        (Finset.univ : Finset (Fin n)).offDiag := by
      ext p
      simp [Finset.mem_offDiag]
    rw [h1, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.mul_sub_one]
  have hsplit : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) =
      (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)) ∪
        (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      exact lt_or_gt_of_ne h
    · rintro (h | h)
      · exact h.ne
      · exact h.ne'
  have hdisj : Disjoint (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
      (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_filter] at hp hq
    exact lt_asymm hp.2 hq.2
  have hswap : (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)).card =
      (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card := by
    apply Finset.card_bij (fun p _ => p.swap)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact hp
    · intro p _ q _ h
      exact Prod.swap_injective h
    · intro q hq
      refine ⟨q.swap, ?_, Prod.swap_swap q⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hq ⊢
      exact hq
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hswap] at hoff
  generalize n * (n - 1) = X at hoff ⊢
  omega
end MassDataIdxStIm
