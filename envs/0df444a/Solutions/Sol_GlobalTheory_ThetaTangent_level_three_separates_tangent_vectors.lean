-- Prove2me | solution 1 for GlobalTheory.ThetaTangent.level_three_separates_tangent_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:01:54.772942+00:00
-- url     : https://prove2.me/submissions/37e9f76b-7cb7-411a-ae10-1d0aa3cb8fe9

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors
import Theorems.Thm_GlobalTheory_ThetaTangent_exists_unit_of_three_term

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
open GlobalTheory GlobalTheory.ThetaTangent
namespace GlobalTheory.ThetaTangent
theorem _root_.solution :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧ (fun z => theta 0 0 z τ) ≠ 0) →
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ (w : Fin g → ℂ) (h : (Fin g → ℂ) → ℂ), Differentiable ℂ h → (∀ z, h z ≠ 0) → (∀ z, theta 0 0 (z + w) τ = h z * theta 0 0 z τ) → w ∈ periodLattice τ) →
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) →
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z ξ : Fin g → ℂ) (γ : ℂ), (∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → fderiv ℂ f z ξ = γ * f z) → ξ = 0) := by
  intro H1 H2 H3 g τ hτ N hN z ξ γ hf
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 3 := ⟨N - 3, by omega⟩
  obtain ⟨⟨hθ, hlaw⟩, h0⟩ := H1 g τ hτ
  have hper := H2 g τ hτ
  have hdisc := (H3 g τ hτ).1
  set θ : (Fin g → ℂ) → ℂ := fun z => theta 0 0 z τ with hθdef
  have hmem : ∀ t : ℂ, t • ξ ∈ periodLattice τ := by
    intro t
    obtain ⟨h, h1, h2, h3⟩ := exists_unit_of_three_term hθ h0 ξ (((m : ℂ) + 3) • z) γ m (by
      intro a b
      set c := ((m : ℂ) + 3) • z - a - ((m : ℂ) + 1) • b with hc
      have hd : ∀ p : Fin g → ℂ, HasFDerivAt (fun x => θ (x + (p - z))) (fderiv ℂ θ p) z := by
        intro p
        have := (hθ p).hasFDerivAt
        rw [show p = z + (p - z) by abel] at this
        rw [← hasFDerivAt_comp_add_right] at this
        simpa using this
      have hdd : ∀ p : Fin g → ℂ, Differentiable ℂ (fun x => θ (x + (p - z))) := fun p =>
        hθ.comp (by fun_prop)
      have key := hf (fun x => θ (x + (a - z)) * θ (x + (b - z)) ^ (m + 1) * θ (x + (c - z)))
        ⟨((hdd a).mul ((hdd b).pow _)).mul (hdd c), ?_⟩
      · have hD := (((hd a).mul ((hd b).pow (m + 1))).mul (hd c)).fderiv
        have e : (fun x => θ (x + (a - z)) * θ (x + (b - z)) ^ (m + 1) * θ (x + (c - z)))
          = ((fun x => θ (x + (a - z))) * (fun x => θ (x + (b - z)) ^ (m + 1)))
            * fun x => θ (x + (c - z)) := rfl
        rw [e, hD] at key
        simp at key
        linear_combination key
      · intro n n' x
        have e : ∀ p : Fin g → ℂ, x + τ *ᵥ ofIntVec n + ofIntVec n' + p
            = x + p + τ *ᵥ ofIntVec n + ofIntVec n' := fun p => by abel
        simp only [e]
        rw [hlaw n n', hlaw n n', hlaw n n', mul_pow]
        have e2 : eC (-((m + 3 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ x))
            = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ (x + (a - z))))
              * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2
                  + ofIntVec n ⬝ᵥ (x + (b - z)))) ^ (m + 1)
              * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2
                  + ofIntVec n ⬝ᵥ (x + (c - z)))) := by
          unfold eC
          rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, hc]
          congr 1
          simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
          push_cast
          ring
        rw [e2]
        ring) t
    exact hper _ h h1 h2 h3
  have hcont : Continuous (fun t : ℂ => (⟨t • ξ, hmem t⟩ : periodLattice τ)) :=
    Continuous.subtype_mk (by fun_prop) _
  have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hcont (x := 1) (y := 0)
  simpa using congrArg Subtype.val this
end GlobalTheory.ThetaTangent
