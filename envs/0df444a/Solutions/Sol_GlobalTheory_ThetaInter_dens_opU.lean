-- Prove2me | solution 1 for GlobalTheory.ThetaInter.dens_opU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:31.873255+00:00
-- url     : https://prove2.me/submissions/a45fd4fd-48b7-47d9-bed1-20b08d68701c

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
theorem _root_.solution (hH : IsHerm H) (x : V) (F G : V → ℂ) (z : V) :
    dens H (opU H x F) (opU H x G) z = dens H F G (z + x) := by
  simp only [dens, opU, map_mul, ← Complex.exp_conj, map_sub, map_neg, map_div₀, Complex.conj_ofReal,
    ← hH _ _, map_ofNat, map_add, LinearMap.add_apply]
  have key : cexp (-(Real.pi : ℂ) * H z x - Real.pi * H x x / 2) *
      cexp (-(Real.pi : ℂ) * H x z - Real.pi * H x x / 2) * cexp (-(Real.pi : ℂ) * H z z) =
      cexp (-(Real.pi : ℂ) * (H z z + H x z + (H z x + H x x))) := by
    simp only [← Complex.exp_add]; congr 1; ring
  rw [← key]; ring
end GlobalTheory.ThetaInter
