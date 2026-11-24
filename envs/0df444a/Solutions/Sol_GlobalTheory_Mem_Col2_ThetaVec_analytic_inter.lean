-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.analytic_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:35:07.568676+00:00
-- url     : https://prove2.me/submissions/cbd40e51-1e28-4745-a21c-4e0832191e8c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_ThetaInter_inter_eq


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
variable {n : Type} [Fintype n]
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution (H : Sesq (n → ℂ)) (α : (n → ℂ) → ℂ) (A₁ A₂ : AddSubgroup (n → ℂ))
    [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)] {G : (n → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) :
    AnalyticOnNhd ℂ (inter H α A₁ A₂ G) Set.univ := by
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  rw [inter_eq]
  intro z _
  refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun c _ => analyticAt_const.mul ?_)
  generalize ((Quotient.out c : A₂) : n → ℂ) = x
  have h : AnalyticAt ℂ (fun z => H z x) z := (LinearMap.toContinuousLinearMap (H.flip x)).analyticAt z
  exact ((hG _ trivial).comp (f := fun z => z + x) (analyticAt_id.add analyticAt_const)).mul
    (((analyticAt_const.mul h).sub analyticAt_const).cexp)
end GlobalTheory.Mem.Col2.ThetaVec
