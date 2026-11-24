-- Prove2me | solution 1 for GlobalTheory.ThetaInter.alpha_opU_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:57:44.488348+00:00
-- url     : https://prove2.me/submissions/9bea3db1-a00f-45cf-aef7-448018d8ff4a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_chi_eq_one_iff
import Theorems.Thm_GlobalTheory_ThetaInter_opU_opU

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
theorem _root_.solution (hH : IsHerm H) {A : AddSubgroup V} (hd : IsSelfDual H A) (hs : IsSemiChar H A α)
    {x y : V} (hx : x ∈ A) (hy : y ∈ A) (F : V → ℂ) (z : V) :
    α (x + y) * opU H (x + y) F z = α x * (α y * opU H x (opU H y F) z) := by
  have hx' : x ∈ dualLat H A := by rw [hd]; exact hx
  have h1 : chi H x y = 1 := (chi_eq_one_iff x y).2 (hx' y hy)
  rw [opU_opU hH, hs.2 x hx y hy]
  have : cexp (-(Real.pi * I * (altE H x y : ℂ))) = cexp (Real.pi * I * (altE H x y : ℂ)) * chi H x y := by
    rw [chi, ← Complex.exp_add]; congr 1; ring
  rw [this, h1]; ring
end GlobalTheory.ThetaInter
