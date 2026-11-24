-- Prove2me | solution 1 for GlobalTheory.ThetaInter.dens_add_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:09:32.933687+00:00
-- url     : https://prove2.me/submissions/9a410f12-a2b2-46d3-b603-e43bcf63a1a6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_chi_mul_conj
import Theorems.Thm_GlobalTheory_ThetaInter_opU_comm
import Theorems.Thm_GlobalTheory_ThetaInter_opU_mul
import Theorems.Thm_GlobalTheory_ThetaInter_alpha_sq
import Theorems.Thm_GlobalTheory_ThetaInter_alpha_conj
import Theorems.Thm_GlobalTheory_ThetaInter_opU_of_fixed
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
theorem _root_.solution (hH : IsHerm H) {A : AddSubgroup V} (hs : IsSemiChar H A α) {F : V → ℂ}
    (hF : F ∈ fixedBy H α A) (y y' : V) {x : V} (hx : x ∈ A) (z : V) :
    dens H (opU H y F) (opU H y' F) (z + x) = chi H x (y - y') * dens H (opU H y F) (opU H y' F) z := by
  rw [← dens_opU hH, ← chi_mul_conj]
  simp only [dens, opU_comm hH x, opU_of_fixed hs hF hx, opU_mul, map_mul, alpha_conj hs hx]
  linear_combination (chi H x y * conj (chi H x y') * opU H y F z * conj (opU H y' F z) *
    cexp (-(Real.pi : ℂ) * H z z)) * alpha_sq hs hx
end GlobalTheory.ThetaInter
