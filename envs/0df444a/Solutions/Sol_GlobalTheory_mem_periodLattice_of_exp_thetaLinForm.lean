-- Prove2me | solution 1 for GlobalTheory.mem_periodLattice_of_exp_thetaLinForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:28.22481+00:00
-- url     : https://prove2.me/submissions/0dd5be3f-193b-45ed-be53-97c47e2d50a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfExpThetaLinForm
import Theorems.Thm_GlobalTheory_thetaLinForm_apply
import Theorems.Thm_P2M_GlobalTheory_ofIntVec_single__0c7ebe1c80f5
import Theorems.Thm_GlobalTheory_linForm_eq_dotProduct
import Theorems.Thm_P2M_GlobalTheory_two_pi_I_ne_zero__c58fadd1bf16

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (w : Fin g → ℂ) (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ n n' : Fin g → ℤ, cexp (thetaLinForm n w) = cexp (lam (τ *ᵥ ofIntVec n + ofIntVec n'))) :
    w ∈ periodLattice τ := by

  have hk : ∀ j, ∃ k : ℤ, lam (Pi.single j 1) = k * (2 * Real.pi * Complex.I) := by
    intro j
    have hj := h 0 (Pi.single j 1)
    rw [thetaLinForm_apply, ofIntVec_zero, zero_dotProduct, mul_zero, Complex.exp_zero, mulVec_zero,
      zero_add, ofIntVec_single'] at hj
    exact Complex.exp_eq_one_iff.mp hj.symm
  choose k hk using hk

  have hm : ∀ i, ∃ m : ℤ, -(2 * Real.pi * Complex.I) * w i =
      (2 * Real.pi * Complex.I) * (τ *ᵥ ofIntVec k) i + m * (2 * Real.pi * Complex.I) := by
    intro i
    have hi := h (Pi.single i 1) 0
    rw [thetaLinForm_apply, ofIntVec_single', single_dotProduct, _root_.one_mul, ofIntVec_zero, add_zero,
      linForm_eq_dotProduct lam] at hi
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hi
    refine ⟨m, ?_⟩
    rw [hm]
    congr 1
    simp only [dotProduct, mulVec, hk, ofIntVec, Pi.single_apply, mul_ite, _root_.mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hτ.apply i j]
    ring
  choose m hm using hm
  refine ⟨-k, -m, funext fun i => ?_⟩
  rw [ofIntVec_neg, ofIntVec_neg, mulVec_neg]
  show w i = -(τ *ᵥ ofIntVec k) i + -((m i : ℤ) : ℂ)
  apply mul_left_cancel₀ two_pi_I_ne_zero'
  linear_combination (-1 : ℂ) * hm i
end GlobalTheory
