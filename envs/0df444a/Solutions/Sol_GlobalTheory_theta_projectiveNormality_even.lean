-- Prove2me | solution 1 for GlobalTheory.theta_projectiveNormality_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:20.484816+00:00
-- url     : https://prove2.me/submissions/da805d98-d1c5-41b9-b731-eebbefc85590

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousEvalOfMulMemSpan
import Theorems.Thm_GlobalTheory_exists_isHomogeneous_eval_of_mul_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∃ N : ℕ, 3 ≤ N ∧ ∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∃ N : ℕ, 3 ≤ N ∧ Even N ∧ (∀ (d : ℕ) (f : (Fin g → ℂ) → ℂ), (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → ∃ F : MvPolynomial (Fin g → Fin N) ℂ, F.IsHomogeneous d ∧ ∀ z, f z = MvPolynomial.eval (fun c => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F)) := by
  intro hA hB hC g τ hτ
  obtain ⟨N, hN3, hNC⟩ := hC g τ hτ
  refine ⟨2 * N, by omega, even_two_mul N, fun d f hf => ?_⟩
  obtain ⟨F, hF, hFz⟩ := hNC (2 * d) f
    ⟨hf.1, fun n n' z => by rw [show N * (2 * d) = 2 * N * d by ring]; exact hf.2 n n' z⟩
  have hA' := (hA g τ hτ N (by omega)).1
  have hab : ∀ i j : Fin g → Fin N,
      (fun z : Fin g → ℂ => theta (fun k => ((i k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) *
        (fun z : Fin g → ℂ => theta (fun k => ((j k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∈
      Submodule.span ℂ (Set.range (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) =>
        theta (fun k => ((c k : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)) 0
          (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ))) := by
    intro i j
    refine hB g τ hτ (2 * N) (by omega) _ ⟨(hA' i).1.mul (hA' j).1, fun n n' z => ?_⟩
    have h1 := (hA' i).2 n n' z
    have h2 := (hA' j).2 n n' z
    beta_reduce at h1 h2 ⊢
    rw [Pi.mul_apply, Pi.mul_apply, h1, h2,
      show ∀ x : ℂ, eC (-((2 * N : ℕ) : ℂ) * x) = eC (-(N : ℂ) * x) * eC (-(N : ℂ) * x) from
        fun x => by unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  obtain ⟨G, hG, hGz⟩ := exists_isHomogeneous_eval_of_mul_mem_span
    (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
      theta (fun k => ((c k : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))
    (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) =>
      theta (fun k => ((c k : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)) 0
        (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ))
    hab d F hF
  exact ⟨G, hG, fun z => (hFz z).trans (hGz z)⟩
end GlobalTheory
