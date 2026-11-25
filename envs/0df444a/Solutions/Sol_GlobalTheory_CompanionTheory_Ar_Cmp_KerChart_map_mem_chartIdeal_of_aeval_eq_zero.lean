-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.KerChart.map_mem_chartIdeal_of_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:50:20.694601+00:00
-- url     : https://prove2.me/submissions/db5f538e-ccbb-4705-abea-8cb31f67ace6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MapMemChartIdealOfAevalEqZero
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_KerChart_exists_int_clear
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_KerChart_exists_homog
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
open MvPolynomial ReciprocityTheory.AnForm.R
variable {σ : Type}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
theorem _root_.solution :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (p : (k : K) → ι k), (∀ k, y ⟨k, p k⟩ ≠ 0) →
      ∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G = 0 →
        map (algebraMap ℚ ℂ) G ∈
          chartIdeal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p := by
  intro K _ ι _ Ω _ _ y p hy G hG
  classical
  obtain ⟨n, G₀, hn, hG₀⟩ := exists_int_clear G
  obtain ⟨H, m, hHm⟩ := exists_homog (fun q : Σ k, ι k => (⟨q.1, p q.1⟩ : Σ k, ι k)) G₀
  have hz : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G₀ = (0 : Ω) := by
    have h1 : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩)
        (map (algebraMap ℤ ℚ) G₀) = (0 : Ω) := by
      have : (algebraMap ℤ ℚ) = Int.castRingHom ℚ := rfl
      rw [this, hG₀, map_mul, hG, mul_zero]
    rwa [aeval_map_algebraMap] at h1

  have hH : H ∈ ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y := by
    let F := FractionRing (MvPolynomial K Ω)
    let f : MvPolynomial (Σ k, ι k) ℤ →+* F :=
      (algebraMap (MvPolynomial K Ω) F).comp (ReciprocityTheory.ChartRestriction.G.Geo.mConeMap y).toRingHom
    let w : (Σ k, ι k) → F := fun q => algebraMap (MvPolynomial K Ω) F (C (y q / y ⟨q.1, p q.1⟩))
    have hfX : ∀ q, f (X q) = algebraMap (MvPolynomial K Ω) F (C (y q) * X q.1) := by
      intro q
      simp [f, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap]
    have hinj : Function.Injective (algebraMap (MvPolynomial K Ω) F) :=
      IsFractionRing.injective _ _
    have hu : ∀ q : Σ k, ι k, IsUnit (f (X ⟨q.1, p q.1⟩)) := by
      intro q
      rw [hfX, isUnit_iff_ne_zero]
      intro h0
      have := hinj (h0.trans (map_zero _).symm)
      exact mul_ne_zero (C_ne_zero.mpr (hy q.1)) (X_ne_zero _) this
    have hw : ∀ q, f (X q) = f (X ⟨q.1, p q.1⟩) * w q := by
      intro q
      rw [hfX, hfX, ← map_mul]
      congr 1
      have : y q = y ⟨q.1, p q.1⟩ * (y q / y ⟨q.1, p q.1⟩) := by
        field_simp [hy q.1]
      show C (y q) * X q.1 = C (y ⟨q.1, p q.1⟩) * X q.1 * C (y q / y ⟨q.1, p q.1⟩)
      rw [mul_right_comm, ← C_mul, ← this]
    obtain ⟨-, h⟩ := hHm F f w hu hw
    have hev : eval₂Hom (Int.castRingHom F) w G₀ = 0 := by
      have : eval₂Hom (Int.castRingHom F) w =
          ((algebraMap (MvPolynomial K Ω) F).comp C).comp
            (aeval (R := ℤ) (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩)).toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp
        · intro q
          simp [w]
      rw [this]
      simp [hz]
    rw [hev, zero_mul] at h
    exact hinj (h.symm.trans (map_zero _).symm)

  set P := ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y) with hP
  let A := MvPolynomial (Σ k, ι k) ℂ ⧸ chartIdeal P p
  let f : MvPolynomial (Σ k, ι k) ℤ →+* A :=
    (Ideal.Quotient.mk (chartIdeal P p)).comp (map (Int.castRingHom ℂ))
  let w : (Σ k, ι k) → A := fun q => Ideal.Quotient.mk _ (X q)
  have hone : ∀ k, f (X ⟨k, p k⟩) = 1 := by
    intro k
    have : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal P p :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
    simpa [f, sub_eq_zero] using Ideal.Quotient.eq_zero_iff_mem.mpr this
  obtain ⟨hm, h⟩ := hHm A f w (fun q => by rw [hone]; exact isUnit_one)
    (fun q => by rw [hone, one_mul]; simp [f, w])
  have hfH : f H = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.subset_span ⟨H, hH, rfl⟩))
  have hev : eval₂Hom (Int.castRingHom A) w = f := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f]
    · intro q
      simp [f, w]
  rw [hev, hfH] at h
  have hG₀0 : f G₀ = 0 := hm.mul_left_eq_zero.mp h
  have hmem : map (Int.castRingHom ℂ) G₀ ∈ chartIdeal P p :=
    Ideal.Quotient.eq_zero_iff_mem.mp hG₀0
  have hmap : map (Int.castRingHom ℂ) G₀ = C (n : ℂ) * map (algebraMap ℚ ℂ) G := by
    have h1 : map (Int.castRingHom ℂ) G₀ = map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) G₀) := by
      rw [map_map]
      congr 1
    rw [h1, hG₀, map_mul, map_C]
    simp
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [hmap] at hmem
  have := (chartIdeal P p).mul_mem_left (C (n : ℂ)⁻¹) hmem
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hn', C_1, one_mul] at this
end GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
