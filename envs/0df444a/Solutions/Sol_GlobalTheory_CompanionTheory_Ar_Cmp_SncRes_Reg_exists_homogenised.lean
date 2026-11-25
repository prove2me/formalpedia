-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_homogenised
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:34:02.101611+00:00
-- url     : https://prove2.me/submissions/a5a979a5-80f3-4dfb-a2bf-759925a36156

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
theorem _root_.solution (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (I : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    (hI : ∀ k, (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ I) (g : MvPolynomial (Σ k, ι k) ℚ) :
    ∃ (d : ℤ) (H E : MRing ι), d ≠ 0 ∧
      mConeMap y H =
        MvPolynomial.C ((d : Ω) * aeval (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) g) * mConeMap y E ∧
      map (Int.castRingHom ℂ) H - MvPolynomial.C (d : ℂ) * map (algebraMap ℚ ℂ) g ∈ I ∧
      map (Int.castRingHom ℂ) E - 1 ∈ I := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, MvPolynomial.C a.num, 1, by exact_mod_cast a.den_ne_zero, ?_, ?_, by simp⟩
    · have h1 : ((a.den : ℤ) : Ω) * algebraMap ℚ Ω a = (a.num : Ω) := by
        calc ((a.den : ℤ) : Ω) * algebraMap ℚ Ω a = algebraMap ℚ Ω ((a.den : ℚ) * a) := by
              rw [map_mul]; simp
          _ = _ := by rw [Rat.den_mul_eq_num]; simp
      simp only [aeval_C, map_one, mul_one, h1]
      simp [mConeMap]
    · have h1 : ((a.den : ℤ) : ℂ) * algebraMap ℚ ℂ a = (a.num : ℂ) := by
        calc ((a.den : ℤ) : ℂ) * algebraMap ℚ ℂ a = algebraMap ℚ ℂ ((a.den : ℚ) * a) := by
              rw [map_mul]; simp
          _ = _ := by rw [Rat.den_mul_eq_num]; simp
      have : map (Int.castRingHom ℂ) (MvPolynomial.C a.num : MRing ι) -
          MvPolynomial.C ((a.den : ℤ) : ℂ) * map (algebraMap ℚ ℂ) (MvPolynomial.C a) = 0 := by
        rw [map_C, map_C, ← map_mul, h1]
        simp
      rw [this]; exact I.zero_mem
  | add p q hp hq =>
    obtain ⟨d₁, H₁, E₁, hd₁, ha₁, hb₁, he₁⟩ := hp
    obtain ⟨d₂, H₂, E₂, hd₂, ha₂, hb₂, he₂⟩ := hq
    have hC : ∀ d : ℤ, mConeMap y (MvPolynomial.C d) = MvPolynomial.C (d : Ω) := fun d => by
      rw [mConeMap, aeval_C]; simp
    have hZ : ∀ d : ℤ, map (Int.castRingHom ℂ) (MvPolynomial.C d : MRing ι) = MvPolynomial.C (d : ℂ) :=
      fun d => by rw [map_C]; simp
    refine ⟨d₁ * d₂, MvPolynomial.C d₂ * H₁ * E₂ + MvPolynomial.C d₁ * H₂ * E₁, E₁ * E₂,
      mul_ne_zero hd₁ hd₂, ?_, ?_, ?_⟩
    · simp only [map_add, map_mul, ha₁, ha₂, hC, Int.cast_mul, mul_add]
      ring
    · have e : map (Int.castRingHom ℂ) (MvPolynomial.C d₂ * H₁ * E₂ + MvPolynomial.C d₁ * H₂ * E₁ : MRing ι) -
          MvPolynomial.C ((d₁ * d₂ : ℤ) : ℂ) * map (algebraMap ℚ ℂ) (p + q) =
          (MvPolynomial.C (d₂ : ℂ) * map (Int.castRingHom ℂ) E₂) *
              (map (Int.castRingHom ℂ) H₁ - MvPolynomial.C (d₁ : ℂ) * map (algebraMap ℚ ℂ) p) +
            (MvPolynomial.C (d₁ : ℂ) * map (Int.castRingHom ℂ) E₁) *
              (map (Int.castRingHom ℂ) H₂ - MvPolynomial.C (d₂ : ℂ) * map (algebraMap ℚ ℂ) q) +
            (MvPolynomial.C (d₁ : ℂ) * MvPolynomial.C (d₂ : ℂ) * map (algebraMap ℚ ℂ) p) *
              (map (Int.castRingHom ℂ) E₂ - 1) +
            (MvPolynomial.C (d₁ : ℂ) * MvPolynomial.C (d₂ : ℂ) * map (algebraMap ℚ ℂ) q) *
              (map (Int.castRingHom ℂ) E₁ - 1) := by
        simp only [map_add, map_mul, hZ, Int.cast_mul]
        ring
      rw [e]
      exact I.add_mem (I.add_mem (I.add_mem (I.mul_mem_left _ hb₁) (I.mul_mem_left _ hb₂))
        (I.mul_mem_left _ he₂)) (I.mul_mem_left _ he₁)
    · have e : map (Int.castRingHom ℂ) (E₁ * E₂ : MRing ι) - 1 =
          map (Int.castRingHom ℂ) E₂ * (map (Int.castRingHom ℂ) E₁ - 1) +
            (map (Int.castRingHom ℂ) E₂ - 1) := by
        rw [map_mul]; ring
      rw [e]
      exact I.add_mem (I.mul_mem_left _ he₁) he₂
  | mul_X p s hp =>
    obtain ⟨d, H, E, hd, ha, hb, he⟩ := hp
    have hX : mConeMap y (X s) = MvPolynomial.C (y s / y ⟨s.1, c s.1⟩) * mConeMap y (X ⟨s.1, c s.1⟩) := by
      simp only [mConeMap, aeval_X, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (hc s.1)]
    refine ⟨d, H * X s, E * X ⟨s.1, c s.1⟩, hd, ?_, ?_, ?_⟩
    · simp only [map_mul, ha, hX, aeval_X]
      ring
    · have e : map (Int.castRingHom ℂ) (H * X s : MRing ι) -
          MvPolynomial.C (d : ℂ) * map (algebraMap ℚ ℂ) (p * X s) =
          X s * (map (Int.castRingHom ℂ) H - MvPolynomial.C (d : ℂ) * map (algebraMap ℚ ℂ) p) := by
        simp only [map_mul, map_X]
        ring
      rw [e]
      exact I.mul_mem_left _ hb
    · have e : map (Int.castRingHom ℂ) (E * X ⟨s.1, c s.1⟩ : MRing ι) - 1 =
          X ⟨s.1, c s.1⟩ * (map (Int.castRingHom ℂ) E - 1) + (X ⟨s.1, c s.1⟩ - 1) := by
        simp only [map_mul, map_X]
        ring
      rw [e]
      exact I.add_mem (I.mul_mem_left _ he) (hI s.1)
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
