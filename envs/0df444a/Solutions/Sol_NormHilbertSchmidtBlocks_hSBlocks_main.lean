-- Prove2me | solution 1 for NormHilbertSchmidtBlocks.hSBlocks_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:57.929848+00:00
-- url     : https://prove2.me/submissions/bf133ae4-3eb7-4c67-992e-d32f246e611d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HilbertSchmidtBlocks_Change
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HilbertSchmidtBlocks_HSBlocksMain
import Theorems.Thm_NormHilbertSchmidtBlocks_parseval_single
import Theorems.Thm_NormHilbertSchmidtBlocks_sum_inner_change


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open NormHilbertSchmidtBlocks
open Formalism.L2.SG.NormCut
namespace NormHilbertSchmidtBlocks
theorem _root_.solution : HSBlocks := by
  intro C C' V V' _ _ _ _ _ _ _ A B
  have hS : ∀ {W U : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      [NormedAddCommGroup U] [InnerProductSpace ℂ U] (S T : W →L[ℂ] U),
      inner ℂ (hsV S) (hsV T) =
        ∑ i, inner ℂ (S (stdOrthonormalBasis ℂ W i)) (T (stdOrthonormalBasis ℂ W i)) := by
    intro W U _ _ _ _ _ S T
    simp [hsV, PiLp.inner_apply]
  have hblk : ∀ (T : PiLp 2 (fun _ : C' => V') →L[ℂ] PiLp 2 (fun _ : C => V)) (ρ : C) (ρ' : C') (v : V'),
      blockOf T ρ ρ' v = T (WithLp.toLp 2 (Pi.single ρ' v : C' → V')) ρ := by
    intro T ρ ρ' v
    rfl
  have hch := sum_inner_change (stdOrthonormalBasis ℂ (PiLp 2 (fun _ : C' => V')))
    (fun p : (Σ _ : C', Fin (Module.finrank ℂ V')) =>
      WithLp.toLp 2 (Pi.single p.1 (stdOrthonormalBasis ℂ V' p.2) : C' → V'))
    (parseval_single) A.toLinearMap B.toLinearMap
  simp only [ContinuousLinearMap.coe_coe] at hch
  rw [hS, ← hch, Fintype.sum_sigma]
  simp only [hS]
  simp only [hblk, PiLp.inner_apply]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ' _ => ?_
  rw [Finset.sum_comm]
end NormHilbertSchmidtBlocks
