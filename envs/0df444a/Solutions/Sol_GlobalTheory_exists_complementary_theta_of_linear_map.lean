-- Prove2me | solution 1 for GlobalTheory.exists_complementary_theta_of_linear_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:47.363906+00:00
-- url     : https://prove2.me/submissions/69d21a39-ba4e-4451-909a-ead432c8772a

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsComplementaryThetaOfLinearMap
import Theorems.Thm_GlobalTheory_ThetaComplement_exists_le_mul_of_homogeneous
import Theorems.Thm_GlobalTheory_ThetaComplement_exists_normal_form
import Theorems.Thm_GlobalTheory_ThetaComplement_form_conj

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
open ThetaComplement
namespace GlobalTheory
theorem _root_.solution :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧ (fun z => theta 0 0 z τ) ≠ 0) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∀ l, a l ≠ 0) → (∀ l m : Λ, a (l + m) = a l * a m * cexp (B l m)) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Q : (Fin g → ℂ) → ℂ), Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ ∀ (l : Λ) z, a l * cexp (B l z) * cexp (Q z - Q (z + l)) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))))) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (θ : (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Injective Ef → Differentiable ℂ θ → θ ≠ 0 → (∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) → ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ H₀ : Matrix (Fin g) (Fin g) ℂ, (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) → ∃ ρ : ℝ, ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, ρ * (z ⬝ᵥ H₀.mulVec (star z)).re ≤ (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, χ (l + m) = χ l * χ m * cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)) → ∀ z₀, ∃ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ θ z₀ ≠ 0 ∧ ∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ (N : ℕ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ l ∈ periodLattice τ, F l ∈ periodLattice τ) → ∃ d : ℕ, ∀ z₀, ∃ G : (Fin g → ℂ) → ℂ, G z₀ ≠ 0 ∧ ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → (Differentiable ℂ (fun z => f (F z) * G z) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => f (F z) * G z) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => f (F z) * G z) z)) := by
  intro h1 _ _ _ h5 g τ hτ N F hF
  obtain ⟨hd, hsp, huniq⟩ := h1 g τ hτ
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨0, fun z₀ => ⟨fun _ => 1, one_ne_zero, fun f hf => ⟨?_, fun n n' z => ?_⟩⟩⟩
    · exact (hf.1.comp F.toContinuousLinearMap.differentiable).mul (differentiable_const _)
    · obtain ⟨p, p', hp⟩ := hF _ ⟨n, n', rfl⟩
      have := hf.2 p p' (F z)
      simp only [add_assoc, map_add F z, hp] at this ⊢
      simpa [eC] using this
  obtain ⟨H, s, Q, hH, hpos, hQ, hs, hnf⟩ := exists_normal_form τ hτ huniq
  let Λ : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule (periodLattice τ)
  obtain ⟨ρ, hρ⟩ := h5 g Λ hd hsp H hpos
  have hFc : Continuous F := F.continuous_of_finiteDimensional
  have hcont : Continuous (fun z : Fin g → ℂ => (z ⬝ᵥ H.mulVec (star z)).re) := by
    simp only [dotProduct, mulVec, Pi.star_apply]
    fun_prop
  have hhom : ∀ (r : ℝ) (z : Fin g → ℂ), (((r : ℂ) • z) ⬝ᵥ H.mulVec (star ((r : ℂ) • z))).re
      = r ^ 2 * (z ⬝ᵥ H.mulVec (star z)).re := by
    intro r z
    simp only [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    simp
    ring
  obtain ⟨C, hC⟩ := exists_le_mul_of_homogeneous (fun z => (z ⬝ᵥ H.mulVec (star z)).re)
    (fun z => (F z ⬝ᵥ H.mulVec (star (F z))).re) hcont (hcont.comp hFc) hhom
    (fun r z => by rw [map_smul]; exact hhom r (F z)) hpos
  obtain ⟨d, hdC⟩ := exists_nat_ge (C + |ρ|)
  refine ⟨d, fun z₀ => ?_⟩
  set M := LinearMap.toMatrix' F with hM
  have hMF : ∀ z, M *ᵥ z = F z := fun z => by simp [hM]
  set H' : Matrix (Fin g) (Fin g) ℂ := ((N * d : ℕ) : ℂ) • H - (N : ℂ) • (Mᵀ * H * Mᵀᴴ) with hH'
  have hform : ∀ u v : Fin g → ℂ, u ⬝ᵥ H'.mulVec (star v) = (N : ℂ) * d * (u ⬝ᵥ H.mulVec (star v))
      - N * (F u ⬝ᵥ H.mulVec (star (F v))) := by
    intro u v
    rw [hH', sub_mulVec, dotProduct_sub, smul_mulVec, smul_mulVec, dotProduct_smul,
      dotProduct_smul, form_conj, hMF, hMF]
    simp
  obtain ⟨θ, hθd, hθ0, hθ⟩ := hρ H'
    (fun l => cexp (π * I * ((N : ℂ) * d * s l - N * s (F l)))) (by
      have := Matrix.isHermitian_mul_mul_conjTranspose Mᵀ hH
      rw [Matrix.IsHermitian, hH', conjTranspose_sub, conjTranspose_smul, conjTranspose_smul,
        this.eq, hH.eq]
      simp) (by
      intro z
      rw [hform]
      have h0 : 0 ≤ (z ⬝ᵥ H.mulVec (star z)).re := by
        by_cases hz : z = 0
        · simp [hz]
        · exact (hpos z hz).le
      have h1 := hC z
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have h2 : ((N : ℂ) * d * (z ⬝ᵥ H.mulVec (star z)) - N * (F z ⬝ᵥ H.mulVec (star (F z)))).re
          = N * (d * (z ⬝ᵥ H.mulVec (star z)).re - (F z ⬝ᵥ H.mulVec (star (F z))).re) := by
        simp; ring
      rw [h2]
      generalize (z ⬝ᵥ H.mulVec (star z)).re = a at *
      generalize (F z ⬝ᵥ H.mulVec (star (F z))).re = b at *
      have h3 : |ρ| * a ≤ d * a - b := by nlinarith
      have h4 : 0 ≤ |ρ| * a := mul_nonneg (abs_nonneg _) h0
      have h5 : ρ * a ≤ |ρ| * a := mul_le_mul_of_nonneg_right (le_abs_self _) h0
      nlinarith) (by
      intro l
      rw [Complex.norm_exp]
      simp) (by
      intro l m
      obtain ⟨k, hk⟩ := hs l l.2 m m.2
      obtain ⟨k', hk'⟩ := hs _ (hF _ l.2) _ (hF _ m.2)
      rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
      refine ⟨N * d * k - N * k', ?_⟩
      have h2 : (((l : Fin g → ℂ) ⬝ᵥ H'.mulVec (star (m : Fin g → ℂ))).im : ℂ)
          = N * d * (((l : Fin g → ℂ) ⬝ᵥ H.mulVec (star (m : Fin g → ℂ))).im : ℂ)
            - N * ((F l ⬝ᵥ H.mulVec (star (F m))).im : ℂ) := by
        rw [hform]; simp
      rw [h2, Submodule.coe_add, map_add, hk, hk']
      push_cast
      ring) z₀
  refine ⟨fun z => θ z * cexp ((N : ℂ) * d * Q z - N * Q (F z)),
    mul_ne_zero hθ0 (Complex.exp_ne_zero _), fun f hf => ⟨?_, fun n n' z => ?_⟩⟩
  · have hFd : Differentiable ℂ F := F.toContinuousLinearMap.differentiable
    exact (hf.1.comp hFd).mul (hθd.mul ((hQ.const_mul _).sub
      ((hQ.comp hFd).const_mul _)).cexp)
  · obtain ⟨p, p', hp⟩ := hF _ ⟨n, n', rfl⟩
    have e1 := hf.2 p p' (F z)
    have e2 := hθ ⟨_, n, n', rfl⟩ z
    have e3 := hnf n n' _ z rfl
    have e4 := hnf p p' _ (F z) hp
    simp only [add_assoc] at e1 ⊢
    simp only [hform] at e2
    rw [← hp] at e1
    generalize τ *ᵥ ofIntVec n + ofIntVec n' = l at *
    rw [map_add, e1, e2]
    unfold eC
    have key : ∀ a b c e a' e' x y : ℂ, a + b + c + e = a' + e' →
        cexp a * x * (cexp b * cexp c * y * cexp e) = cexp a' * (x * (y * cexp e')) := by
      intro a b c e a' e' x y h
      have := congrArg cexp h
      simp only [Complex.exp_add] at this
      linear_combination x * y * this
    apply key
    push_cast
    linear_combination (-(N : ℂ)) * e4 + N * d * e3
end GlobalTheory
