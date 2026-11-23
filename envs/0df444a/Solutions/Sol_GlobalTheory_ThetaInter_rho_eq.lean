-- Prove2me | solution 1 for GlobalTheory.ThetaInter.rho_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:31.200041+00:00
-- url     : https://prove2.me/submissions/bd937f71-bf22-44f7-ad93-360b1d06a4ff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
variable {α : V → ℂ}
namespace GlobalTheory.ThetaInter
theorem _root_.solution (hH : IsHerm H) (F : V → ℂ) (z : V) : (rho H F z : ℂ) = dens H F F z := by
  have : ((H z z).re : ℂ) = H z z := Complex.conj_eq_iff_re.1 (hH z z).symm
  rw [rho, dens, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [this]
end GlobalTheory.ThetaInter
