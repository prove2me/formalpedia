-- Prove2me | solution 1 for GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:51:26.438395+00:00
-- url     : https://prove2.me/submissions/083d4eae-9ac1-4080-bc7d-61dcdfff6c55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtCoeffFockColumnSubstitutionExp
import Theorems.Thm_GlobalTheory_ColLie_hasDerivAt_exp_ofReal_smul_entry
import Theorems.Thm_GlobalTheory_ColLie_hasDerivAt_coeff_colSub_of_curve
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
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ColLie
open GlobalTheory.MinorFrame
variable {ι : Type} [DecidableEq ι]
namespace GlobalTheory.ColLie
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι)
    (S : Matrix (Fin a) (Fin a) ℂ) (R : Pol ι d a) (m : Var ι d a →₀ ℕ) :
    HasDerivAt (fun h : ℝ => coeff m (colSub (atPl τ (NormedSpace.exp ((h : ℂ) • S))) R))
      (coeff m (colDer τ S R)) 0 := by
  refine hasDerivAt_coeff_colSub_of_curve τ S (fun h => atPl τ (NormedSpace.exp ((h : ℂ) • S))) ?_ ?_ R m
  · simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, atPl]
    exact Function.update_eq_self τ 1
  · intro σ i j
    by_cases h : σ = τ
    · subst h
      simp only [atPl, Function.update_self, if_true]
      exact hasDerivAt_exp_ofReal_smul_entry S i j
    · simp only [atPl, Function.update_of_ne h, if_neg h]
      exact hasDerivAt_const _ _
end GlobalTheory.ColLie
