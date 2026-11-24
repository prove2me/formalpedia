-- Prove2me | solution 1 for GlobalTheory.ThetaInter.rho_add_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:20:11.014255+00:00
-- url     : https://prove2.me/submissions/d8954262-1e41-4dce-890a-c231379fc186

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Theorems.Thm_GlobalTheory_ThetaInter_rho_eq
import Theorems.Thm_GlobalTheory_ThetaInter_dens_add_of_fixed

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
    (hF : F ∈ fixedBy H α A) {x : V} (hx : x ∈ A) (z : V) : rho H F (z + x) = rho H F z := by
  apply Complex.ofReal_injective
  have h0 : opU H 0 F = F := by funext w; simp [opU]
  have := dens_add_of_fixed hH hs hF 0 0 hx z
  rw [h0] at this
  rw [rho_eq hH, rho_eq hH, this]
  simp [chi, altE]
end GlobalTheory.ThetaInter
