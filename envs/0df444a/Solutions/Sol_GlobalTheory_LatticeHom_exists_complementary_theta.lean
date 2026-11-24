-- Prove2me | solution 1 for GlobalTheory.LatticeHom.exists_complementary_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:45.927885+00:00
-- url     : https://prove2.me/submissions/fbe2516c-4d75-443b-9374-e36cd4434e3a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HermFormSwapOfIsHermitian
import Theorems.Thm_GlobalTheory_LatticeHom_exists_le_mul_of_homogeneous
import Theorems.Thm_GlobalTheory_LatticeHom_re_hermForm_real_smul
import Theorems.Thm_GlobalTheory_LatticeHom_continuous_re_hermForm
import Theorems.Thm_GlobalTheory_LatticeHom_exists_hermForm_pull
import Theorems.Thm_GlobalTheory_LatticeHom_semicharacter_add
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_Cartier_SecMaps_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.LatticeHom
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
private theorem conj_cexp_pi_mul_I_mul_real (t : ℝ) :
    (starRingEnd ℂ) (cexp (Real.pi * I * t)) = cexp (-(Real.pi * I * t)) := by
  rw [← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  ring
end GlobalTheory.LatticeHom
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LatticeHom
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
namespace GlobalTheory.LatticeHom
theorem _root_.solution
    (hth : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ H₀ : Matrix (Fin g) (Fin g) ℂ, (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) → ∃ ρ : ℝ, ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, ρ * (z ⬝ᵥ H₀.mulVec (star z)).re ≤ (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, χ (l + m) = χ l * χ m * cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)) → ∀ z₀, ∃ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ θ z₀ ≠ 0 ∧ ∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z)
    (u : HolUnif A L g) (u' : HolUnif A' L' g') (hL : L.IsLB) (hL' : L'.IsLB)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ' : u'.Λ → ℂ}
    (h : u.IsAH Hm χ) (h' : u'.IsAH Hm' χ') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u'.Λ) (N : ℕ) :
    ∃ d : ℕ, ∀ z₀, ∃ G : (Fin g → ℂ) → ℂ, G z₀ ≠ 0 ∧
      ∀ θ, u'.IsThetaFn Hm' χ' N θ → u.IsThetaFn Hm χ d (fun z => θ (F z) * G z) := by
  obtain ⟨K, hK, hKF⟩ := exists_hermForm_pull h'.1 F
  obtain ⟨Fl, hFl⟩ : ∃ Fl : u.Λ → u'.Λ, ∀ l, ((Fl l : u'.Λ) : Fin g' → ℂ) = F l :=
    ⟨fun l => ⟨F l, hF l l.2⟩, fun _ => rfl⟩
  have hFl_add : ∀ l m, Fl (l + m) = Fl l + Fl m := fun l m => by
    apply Subtype.ext
    rw [Submodule.coe_add, hFl, hFl, hFl, Submodule.coe_add, map_add]
  obtain ⟨ρ, hρ⟩ := hth g u.Λ u.discrete u.full Hm h.2.1
  obtain ⟨C, hC⟩ := exists_le_mul_of_homogeneous (fun z => (hermForm Hm z z).re) (fun z => (hermForm K z z).re)
    (continuous_re_hermForm Hm) (continuous_re_hermForm K) h.2.1 (re_hermForm_real_smul Hm)
    (re_hermForm_real_smul K)
  obtain ⟨d, hd⟩ := exists_nat_ge (ρ + N * C)
  refine ⟨d, fun z₀ => ?_⟩
  obtain ⟨Hg, hHg⟩ : ∃ Hg : Matrix (Fin g) (Fin g) ℂ, Hg = (d : ℂ) • Hm - (N : ℂ) • K := ⟨_, rfl⟩
  obtain ⟨χg, hχg⟩ : ∃ f : u.Λ → ℂ, ∀ l, f l = χ l ^ d * (starRingEnd ℂ) (χ' (Fl l)) ^ N := ⟨_, fun _ => rfl⟩
  have hHg_form : ∀ z w, hermForm Hg z w = d * hermForm Hm z w - N * hermForm K z w := by
    intro z w
    simp [hHg, hermForm, sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul]
  have hHgH : Hg.IsHermitian := by
    rw [hHg, IsHermitian, conjTranspose_sub, conjTranspose_smul, conjTranspose_smul, h.1.eq, hK.eq]
    simp
  have hbound : ∀ z : Fin g → ℂ, ρ * (hermForm Hm z z).re ≤ (hermForm Hg z z).re := by
    intro z
    have hre : (hermForm Hg z z).re = d * (hermForm Hm z z).re - N * (hermForm K z z).re := by
      rw [hHg_form]; simp
    rw [hre]
    have h1 := hC z
    have h2 : 0 ≤ (hermForm Hm z z).re := by
      by_cases hz : z = 0
      · simp [hz, hermForm]
      · exact (h.2.1 z hz).le
    nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hd) h2]
  have hnorm : ∀ l, ‖χg l‖ = 1 := by
    intro l
    rw [hχg, norm_mul, norm_pow, norm_pow, h.2.2.1, Complex.norm_conj, h'.2.2.1, one_pow, one_pow, _root_.one_mul]
  have hsemi : ∀ l m : u.Λ, χg (l + m) = χg l * χg m *
      cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hg.mulVec (star (m : Fin g → ℂ))).im) := by
    intro l m
    change χg (l + m) = χg l * χg m * cexp (Real.pi * I * (hermForm Hg l m).im)
    have s1 := semicharacter_add u hL h l m
    have s2 := semicharacter_add u' hL' h' (Fl l) (Fl m)
    rw [hFl, hFl, ← hKF] at s2
    rw [hχg, hχg, hχg, hFl_add, s1, s2, hHg_form, map_mul, map_mul, conj_cexp_pi_mul_I_mul_real]
    have him : ((d : ℂ) * hermForm Hm l m - N * hermForm K l m).im =
        d * (hermForm Hm l m).im - N * (hermForm K l m).im := by simp
    rw [him]
    have he : cexp (Real.pi * I * (hermForm Hm l m).im) ^ d * cexp (-(Real.pi * I * (hermForm K l m).im)) ^ N =
        cexp (Real.pi * I * ((d * (hermForm Hm l m).im - N * (hermForm K l m).im : ℝ) : ℂ)) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    linear_combination (χ l ^ d * χ m ^ d * (starRingEnd ℂ) (χ' (Fl l)) ^ N * (starRingEnd ℂ) (χ' (Fl m)) ^ N) * he
  obtain ⟨G, hGd, hG0, hGt⟩ := hρ Hg χg hHgH hbound hnorm hsemi z₀
  refine ⟨G, hG0, fun θ hθ => ⟨?_, fun l z => ?_⟩⟩
  · exact (hθ.1.comp (LinearMap.toContinuousLinearMap F).differentiable).mul hGd
  · have t1 := hθ.2 (Fl l) (F z)
    rw [hFl, ← hKF, ← hKF] at t1
    have t2 : G (z + l) = χg l * cexp (Real.pi * hermForm Hg z l + Real.pi / 2 * hermForm Hg l l) * G z := hGt l z
    have hψ : χ' (Fl l) * (starRingEnd ℂ) (χ' (Fl l)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h'.2.2.1]; simp
    have hψN : (χ' (Fl l) * (starRingEnd ℂ) (χ' (Fl l))) ^ N = 1 := by rw [hψ, one_pow]
    have hexp : cexp (Real.pi * (d * hermForm Hm z l - N * hermForm K z l) +
        Real.pi / 2 * (d * hermForm Hm l l - N * hermForm K l l)) *
        cexp (Real.pi * hermForm K z l + Real.pi / 2 * hermForm K l l) ^ N =
        cexp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) ^ d := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      ring
    show θ (F (z + l)) * G (z + l) = _ * (θ (F z) * G z)
    rw [map_add, t1, t2, hHg_form, hHg_form, hχg]
    linear_combination (χ l ^ d * θ (F z) * G z * (cexp (Real.pi * (d * hermForm Hm z l - N * hermForm K z l) +
        Real.pi / 2 * (d * hermForm Hm l l - N * hermForm K l l)) *
        cexp (Real.pi * hermForm K z l + Real.pi / 2 * hermForm K l l) ^ N)) * hψN +
      (χ l ^ d * θ (F z) * G z) * hexp
end GlobalTheory.LatticeHom
