-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.stdH_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:41:12.343343+00:00
-- url     : https://prove2.me/submissions/83fb6ea0-8e76-42d4-abe3-d6b8571869b7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_area_eq
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_periodLatticeSesquilinearForm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.ThetaVec
open Formalism.L2.Th1 Formalism.L2.Th1.H Complex GlobalTheory.ThetaInter
open scoped BigOperators ComplexConjugate Real
variable (L : PeriodPair)
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution (z w : n → ℂ) : stdH L n z w = ∑ i, form1 L (z i) (w i) := by
  change ∑ i, ∑ j, z i * _ * conj (w j) = _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.one_apply_ne hj.symm]) (by simp), periodLatticeSesquilinearForm_apply,
    latticeForm, area_eq]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
  ring
end GlobalTheory.Mem.Col2.ThetaVec
