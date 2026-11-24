-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.RT.Siegel.triv_of_cell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:51:00.187815+00:00
-- url     : https://prove2.me/submissions/fecadd69-976b-4724-b6a3-7d635d4aebd8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_Siegel_finite_nonunit_matrix
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_finite_nonunit_matrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.WeilM GlobalTheory.CompanionTheory.SiegelChar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.Siegel
namespace GlobalTheory.CompanionTheory.Ar.RT.Siegel
theorem _root_.solution {F : Type} [Field F] [Infinite F] {E : Type} [CommRing E] [Algebra F E] [IsArtinianRing E]
    {β : Type} [Fintype β] [DecidableEq β] {c : E →ₐ[F] E} {ξ : E} (hξ : IsUnit ξ) (h2 : IsUnit (2 : E))
    (hc : c ξ = -ξ) {σ : Matrix β β E →+ Matrix β β E} {G : Type} [Group G] {φ : G →* Matrix β β E}
    {e f : Matrix β β E} (hsm : ∀ (a : E) x, σ (a • x) = c a • σ x) (hmul : ∀ x y, σ (x * y) = σ y * σ x) (h1 : σ 1 = 1)
    (hu : ∀ g, σ (φ g) * φ g = 1) (hsurj : ∀ x, σ x * x = 1 → ∃ g, φ g = x)
    (hef : e + f = 1) (hee : e * e = e) (hff : f * f = f) (hef0 : e * f = 0) (hfe0 : f * e = 0) (lam : G →* ℂˣ)
    (hcell : ∀ g, IsUnit (φ g * e + f) → lam g = 1) (g : G) : lam g = 1 := by
  have hk1 : φ g⁻¹ * φ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hk2 : φ g * φ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hσh : σ (φ g) = φ g⁻¹ := by
    calc σ (φ g) = σ (φ g) * φ g * φ g⁻¹ := by rw [mul_assoc, hk2, mul_one]
      _ = _ := by rw [hu, one_mul]
  have hσk : σ (φ g⁻¹) = φ g := by
    calc σ (φ g⁻¹) = σ (φ g⁻¹) * φ g⁻¹ * φ g := by rw [mul_assoc, hk1, mul_one]
      _ = _ := by rw [hu, one_mul]
  generalize hkd : φ g⁻¹ = k at hk1 hk2 hσh hσk
  generalize hhd : φ g = h at hk1 hk2 hσh hσk
  have hunit : ∀ a b : E, IsUnit a → IsUnit b → IsUnit (a • e + b • f) := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine IsUnit.of_mul_eq_one (((a⁻¹ : Eˣ) : E) • e + ((b⁻¹ : Eˣ) : E) • f) ?_
    simp only [add_mul, mul_add, smul_mul_smul_comm, hee, hff, hef0, hfe0, smul_zero, Units.mul_inv, one_smul,
      zero_add, add_zero, hef]
  let y : E → Matrix β β E := fun t => (t * t + t * ξ) • h + (t - ξ) • 1
  let y' : E → Matrix β β E := fun t => (t * t - t * ξ) • k + (t + ξ) • 1
  have e1 : ∀ t, y' t = ξ • 1 + t • (1 - ξ • k) + (t * t) • k := by
    intro t; simp only [y']; module
  have e2 : ∀ (t : E) (z : Matrix β β E), y t * e + y' t * z = ((-ξ) • e + ξ • z) + t • (ξ • (h * e) + e - ξ • (k * z) + z) +
      (t * t) • (h * e + k * z) := by
    intro t z; simp only [y, y', add_mul, smul_mul_assoc, one_mul]; module
  have f1 : {t : F | ¬ IsUnit (y' (algebraMap F E t))}.Finite := by
    simp only [e1]
    refine finite_nonunit_matrix _ _ _ 0 ?_
    rw [← e1]
    simp only [y', mul_zero, zero_mul, sub_zero, zero_smul, zero_add]
    rw [← hef, smul_add]
    exact hunit _ _ hξ hξ
  have f2 : {t : F | ¬ IsUnit (y (algebraMap F E t) * e + y' (algebraMap F E t) * f)}.Finite := by
    simp only [e2]
    refine finite_nonunit_matrix _ _ _ 0 ?_
    simp only [mul_zero, zero_smul, add_zero]
    exact hunit _ _ hξ.neg hξ
  have f3 : {t : F | ¬ IsUnit (y (algebraMap F E t) * e + y' (algebraMap F E t) * (h * f))}.Finite := by
    simp only [e2]
    refine finite_nonunit_matrix _ _ _ ξ ?_
    rw [← e2]
    have : y ξ * e + y' ξ * (h * f) = h * ((2 * ξ * ξ) • e + (2 * ξ) • f) := by
      simp only [y, y', add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, sub_self, zero_smul, zero_mul]; module
    rw [this]
    exact (IsUnit.of_mul_eq_one _ hk2).mul (hunit _ _ ((h2.mul hξ).mul hξ) (h2.mul hξ))
  obtain ⟨t, ht⟩ := ((f1.union f2).union f3).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at ht
  obtain ⟨⟨⟨W, hW⟩, u2⟩, u3⟩ := ht
  have s1 : σ (y (algebraMap F E t)) = y' (algebraMap F E t) := by
    simp only [y, y', map_add, hsm, hσh, h1, map_mul, map_sub, c.commutes, hc]; module
  have s2 : σ (y' (algebraMap F E t)) = y (algebraMap F E t) := by
    simp only [y, y', map_add, hsm, hσk, h1, map_mul, map_sub, c.commutes, hc]; module
  have cm : y (algebraMap F E t) * y' (algebraMap F E t) = y' (algebraMap F E t) * y (algebraMap F E t) := by
    simp only [y, y', add_mul, mul_add, smul_mul_smul_comm, hk1, hk2, one_mul, mul_one]; module
  have w1 : y' (algebraMap F E t) * (↑W⁻¹ : Matrix β β E) = 1 := by rw [← hW, Units.mul_inv]
  have w2 : (↑W⁻¹ : Matrix β β E) * y' (algebraMap F E t) = 1 := by rw [← hW, Units.inv_mul]
  have wu : IsUnit (↑W⁻¹ : Matrix β β E) := Units.isUnit _
  generalize (↑W⁻¹ : Matrix β β E) = w at w1 w2 wu
  generalize y (algebraMap F E t) = Y at s1 s2 cm u2 u3
  generalize y' (algebraMap F E t) = Y' at s1 s2 cm u2 u3 w1 w2
  have cw : w * Y = Y * w := by
    calc w * Y = w * (Y * Y') * w := by rw [mul_assoc w, mul_assoc Y, w1, mul_one]
      _ = Y * w := by rw [cm, ← mul_assoc, w2, one_mul]
  obtain ⟨x, hx⟩ := hsurj (w * Y) (by
    have : σ w * Y = 1 := by rw [← s2, ← hmul, w1, h1]
    rw [hmul, s1, cw, mul_assoc, ← mul_assoc (σ w), this, one_mul, w1])
  have l1 : lam x = 1 := hcell x (by
    have : φ x * e + f = w * (Y * e + Y' * f) := by rw [hx, mul_add, ← mul_assoc w Y', w2, one_mul, mul_assoc]
    rw [this]; exact wu.mul u2)
  have l2 : lam (g⁻¹ * x) = 1 := hcell _ (by
    have : φ (g⁻¹ * x) * e + f = k * (w * (Y * e + Y' * (h * f))) := by
      rw [map_mul, hkd, hx, mul_add, ← mul_assoc w Y', w2, one_mul, mul_add, ← mul_assoc k h, hk1, one_mul]
      simp only [mul_assoc]
    rw [this]; exact (IsUnit.of_mul_eq_one _ hk1).mul (wu.mul u3))
  rwa [map_mul, l1, mul_one, map_inv, inv_eq_one] at l2
end GlobalTheory.CompanionTheory.Ar.RT.Siegel
