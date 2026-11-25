-- Prove2me | solution 1 for MassDataIdxStIm.card_par
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:50:12.756815+00:00
-- url     : https://prove2.me/submissions/8f0cb254-9eb3-4af9-82f9-2bc3aa214d7f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_LeviEmbeddingBlock32
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_Block31OfBlocks
import Theorems.Thm_MassDataIdxStIm_card_matrix
import Theorems.Thm_MassDataIdxStIm_card_uni
import Theorems.Thm_MassDataIdxStIm_parMap_bij

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
variable {A : Type} [CommRing A]
variable {r k : ℕ}
namespace MassDataIdxStIm
theorem _root_.solution (K : Type) [Field K] [Fintype K] (r k : ℕ) (P : Matrix (Fin k) (Fin k) K → Prop) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // Par P x} =
      Nat.card {h : Matrix (Fin k) (Fin k) K // P h} *
        Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
  have hM : Nat.card (Mid k) = k + 1 := by
    unfold Mid
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  rw [← Nat.card_congr (Equiv.ofBijective _ (parMap_bij (r := r) P))]
  simp only [Nat.card_prod, card_uni, card_matrix, hM, Nat.card_fin]
  rw [Nat.card_eq_fintype_card (α := K)]
  obtain ⟨t, ht⟩ := Nat.even_mul_pred_self r
  rw [ht, show (t + t) / 2 = t by omega]
  ring
end MassDataIdxStIm
