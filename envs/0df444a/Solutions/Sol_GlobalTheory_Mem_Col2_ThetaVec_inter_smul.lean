-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.inter_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:46.292806+00:00
-- url     : https://prove2.me/submissions/ce25e874-d365-4694-bf61-8aebda41b558

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A₁ A₂ : AddSubgroup V)
    [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)] (c : ℂ) (G : V → ℂ) :
    inter H α A₁ A₂ (c • G) = c • inter H α A₁ A₂ G := by
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  rw [inter_eq, inter_eq]
  funext z
  simp only [opU, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
end GlobalTheory.Mem.Col2.ThetaVec
