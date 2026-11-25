-- Prove2me | solution 1 for GlobalTheory.PeriodSymm.period_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:57.849098+00:00
-- url     : https://prove2.me/submissions/a893df3f-41ed-499b-95cc-fbfbd5a1a673

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSections
import Theorems.Thm_GlobalTheory_PeriodSymm_symm_of_cocycle
import Theorems.Thm_GlobalTheory_PeriodSymm_antiRow_apply
import Theorems.Thm_GlobalTheory_PeriodSymm_antiRow_I
import Theorems.Thm_GlobalTheory_PeriodSymm_clm_eq_sum
import Theorems.Thm_GlobalTheory_PeriodSymm_logDeriv_translate
import Theorems.Thm_GlobalTheory_cauchyRiemann_iff_differentiableOn_complex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology
open GlobalTheory GlobalTheory.PeriodSymm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.PeriodSymm
theorem _root_.solution : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm Θ : Matrix (Fin g) (Fin g) ℂ) (ι : Type) (U : ι → Set (Fin g → ℂ)) (a : ι → (Fin g → ℂ) → ℂ) (k : ι → ι → (Fin g → ℂ) → ℂ) (e : Λ → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i, DifferentiableOn ℂ (a i) (U i) ∧ ∀ z ∈ U i, a i z ≠ 0) → (∀ i (l : Λ), ∀ z ∈ U i, a i z = e l * cexp (π * (z ⬝ᵥ Hm.mulVec (star (l : (Fin g → ℂ))))) * a i (z + l)) → (∀ i j, DifferentiableOn ℂ (k i j) (U i ∩ U j)) → (∀ i j m, ∀ z ∈ U i ∩ U j ∩ U m, k i j z + k j m z = k i m z) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, k i j (z + l) = k i j z + (fderiv ℂ (a i) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a i z - fderiv ℂ (a j) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a j z)) → ∀ z w, Θ.mulVec (star z) ⬝ᵥ Hm.mulVec (star w) = Θ.mulVec (star w) ⬝ᵥ Hm.mulVec (star z) := by
  intro g Λ hd hsp Hm Θ ι U a k e hU hinv hcov ha hf hk hkc hkp z w
  have key : ∑ m, antiRow Θ m z * ((Real.pi) • antiRow Hm m) w
      = ∑ m, antiRow Θ m w * ((Real.pi) • antiRow Hm m) z := by
    refine symm_of_cocycle g Λ hd hsp ι U (fun i m x => fderiv ℂ (a i) x (Pi.single m 1) / a i x)
      k (fun m => antiRow Θ m) (fun m => (Real.pi) • antiRow Hm m) (fun m u => antiRow_I Θ m u)
      ?_ hU hinv hcov ?_ ?_ hk hkc ?_ z w
    · intro m u
      simp only [ContinuousLinearMap.smul_apply, antiRow_I, Complex.real_smul]
      ring
    · intro i m
      have h1 : DifferentiableOn ℂ (fun x => fderiv ℂ (a i) x (Pi.single m 1)) (U i) :=
        ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g (U i) (a i) (hU i)).2 (ha i).1).2 _
      have h2 : DifferentiableOn ℂ (fun x => (a i x)⁻¹) (U i) := (ha i).1.inv (ha i).2
      exact (h1.mul h2).congr fun x _ => div_eq_mul_inv _ _
    · intro i m l x hx
      simp only [ContinuousLinearMap.smul_apply, antiRow_apply, Complex.real_smul]
      exact logDeriv_translate (hU i) (ha i).1 (ha i).2 (l : Fin g → ℂ) _ (e l)
        (fun y hy => hinv i l y hy) (fun y hy => hf i l y hy) m hx
    · intro i j l x hx
      rw [hkp i j l x hx, clm_eq_sum (fderiv ℂ (a i) x), clm_eq_sum (fderiv ℂ (a j) x),
        Finset.sum_div, Finset.sum_div]
      simp only [antiRow_apply, mul_div_assoc]
  have e1 : ∀ x y : Fin g → ℂ, ∑ m, antiRow Θ m x * ((Real.pi) • antiRow Hm m) y
      = Real.pi * (Θ.mulVec (star x) ⬝ᵥ Hm.mulVec (star y)) := by
    intro x y
    simp only [ContinuousLinearMap.smul_apply, antiRow_apply, Complex.real_smul, dotProduct,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [e1, e1] at key
  exact mul_left_cancel₀ hπ key
end GlobalTheory.PeriodSymm
