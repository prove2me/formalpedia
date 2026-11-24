-- Prove2me | solution 1 for GlobalTheory.MinorFrame.rsub_frame_detG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:40:11.883678+00:00
-- url     : https://prove2.me/submissions/4cc39686-9102-4834-89ca-31a75666e24d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumNormRowSubProdMinors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CauchyBinetColumnFrameProdDetPowEqSum
import Theorems.Thm_GlobalTheory_MinorFrame_rsub_frame_det
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Classical MvPolynomial
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open scoped Matrix
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame
theorem _root_.solution {a d : ℕ} (n : ι → ℕ) (x₀ : Var ι d a → ℂ) :
    rsub (frameMat x₀).conjTranspose (detG a n) =
      ∑ T : Tup ι a d n, star (eval x₀ (prodMinors T)) • prodMinors T := by
  unfold detG
  simp only [map_prod, map_pow, rsub_frame_det]
  rw [Finset.prod_congr rfl fun τ _ => (Fin.prod_const (n τ) _).symm]
  rw [Finset.prod_congr rfl fun τ _ => Fintype.prod_sum _, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold prodMinors
  simp only [map_prod, star_prod, smul_eq_C_mul, Finset.prod_mul_distrib]
end GlobalTheory.MinorFrame
