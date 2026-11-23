-- Prove2me | solution 1 for GlobalTheory.ThetaInter.rho_opU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:59.524549+00:00
-- url     : https://prove2.me/submissions/4a3a2159-7b85-4774-80f7-d6cfe0c95964

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_rho_eq
import Theorems.Thm_GlobalTheory_ThetaInter_dens_opU

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
theorem _root_.solution (hH : IsHerm H) (x : V) (F : V → ℂ) (z : V) : rho H (opU H x F) z = rho H F (z + x) := by
  apply Complex.ofReal_injective
  rw [rho_eq hH, rho_eq hH, dens_opU hH]
end GlobalTheory.ThetaInter
