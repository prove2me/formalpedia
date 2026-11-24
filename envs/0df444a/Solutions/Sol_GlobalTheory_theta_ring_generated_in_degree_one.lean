-- Prove2me | solution 1 for GlobalTheory.theta_ring_generated_in_degree_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:09:24.868848+00:00
-- url     : https://prove2.me/submissions/35715038-a571-4fb7-ba54-3517727a972d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow
import Theorems.Thm_GlobalTheory_ThetaGen_le_pow_of_succ_le_mul
import Theorems.Thm_GlobalTheory_ThetaGen_const_of_isIntegral
import Theorems.Thm_GlobalTheory_ThetaGen_exists_succ_le_mul_of_integral
import Theorems.Thm_GlobalTheory_ThetaGen_exists_isHomogeneous_of_mem_span_pow
import Theorems.Thm_GlobalTheory_ThetaGen_level_mul
import Theorems.Thm_GlobalTheory_ThetaGen_one_mem_level

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open ThetaGen
namespace GlobalTheory
theorem _root_.solution :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → IsIntegral (Algebra.adjoin ℂ (Set.range fun (c : Fin g → Fin N) (p : ℂ × (Fin g → ℂ)) => p.1 * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • p.2) ((N : ℂ) • τ))) (fun p : ℂ × (Fin g → ℂ) => p.1 ^ d * f p.2) ∧ ∃ a ∈ (Algebra.adjoin ℂ (Set.range fun (c : Fin g → Fin N) (p : ℂ × (Fin g → ℂ)) => p.1 * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • p.2) ((N : ℂ) • τ))), ∃ b ∈ (Algebra.adjoin ℂ (Set.range fun (c : Fin g → Fin N) (p : ℂ × (Fin g → ℂ)) => p.1 * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • p.2) ((N : ℂ) • τ))), b ≠ 0 ∧ b * (fun p : ℂ × (Fin g → ℂ) => p.1 ^ d * f p.2) = a) → (∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B], (∀ b : B, ∃ a a' : A, a' ≠ 0 ∧ algebraMap A B a' * b = algebraMap A B a) → Module.Finite A B) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∃ N : ℕ, 3 ≤ N ∧ ∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F) := by
  intro hbasis hspan hint hfin g τ hτ
  let R : ℕ → Submodule ℂ ((Fin g → ℂ) → ℂ) := fun d => level τ (3 * d)
  have hmul : ∀ a b, R a * R b ≤ R (a + b) := fun a b => by
    simp only [R, mul_add]; exact level_mul τ _ _
  let θ : (Fin g → Fin 3) → (Fin g → ℂ) → ℂ := fun c z =>
    theta (fun i => ((c i : ℕ) : ℝ) / (3 : ℕ)) 0 (((3 : ℕ) : ℂ) • z) (((3 : ℕ) : ℂ) • τ)
  obtain ⟨e, he⟩ := exists_succ_le_mul_of_integral R (one_mem_level τ) hmul
    (fun d f hf => hf.1) θ (fun c => (hbasis g τ hτ 3 (by norm_num)).1 c)
    (fun d f hf => hint g τ hτ 3 le_rfl d f hf) hfin
  have hpow := le_pow_of_succ_le_mul R hmul (e := e + 1) (by omega)
    (fun d hd => he d (by omega))
  refine ⟨3 * (e + 1), by omega, fun d f hf => ?_⟩
  rcases d with _ | j
  · have hc := const_of_isIntegral θ hf.1 (hint g τ hτ 3 le_rfl 0 f hf).1
    exact ⟨MvPolynomial.C (f 0), MvPolynomial.isHomogeneous_C _ _, fun z => by simp [hc z]⟩
  · have h1 : f ∈ R ((e + 1) * (j + 1)) := by
      simp only [R, ← mul_assoc]; exact hf
    refine exists_isHomogeneous_of_mem_span_pow (fun (c : Fin g → Fin (3 * (e + 1))) z =>
      theta (fun i => ((c i : ℕ) : ℝ) / (3 * (e + 1) : ℕ)) 0 (((3 * (e + 1) : ℕ) : ℂ) • z)
        (((3 * (e + 1) : ℕ) : ℂ) • τ)) (j + 1) ?_
    refine SetLike.le_def.1 (pow_le_pow_left' ?_ (j + 1)) (hpow j h1)
    exact fun u hu => hspan g τ hτ (3 * (e + 1)) (by omega) u hu
end GlobalTheory
