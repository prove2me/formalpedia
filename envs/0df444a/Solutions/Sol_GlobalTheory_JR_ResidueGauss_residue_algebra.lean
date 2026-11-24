-- Prove2me | solution 1 for GlobalTheory.JR.ResidueGauss.residue_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:09:43.436994+00:00
-- url     : https://prove2.me/submissions/8622a000-1f62-4554-b7e2-1671bca0668d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGaussIntegralNormForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ResidueGauss
namespace GlobalTheory.JR.ResidueGauss
theorem _root_.solution {K L : Type} [CommRing K] [CommRing L] [StarRing L] [Algebra K L]
    (hK : IsField K) (hinj : Function.Injective (algebraMap K L)) (N : L → K)
    (hN : ∀ y, algebraMap K L (N y) = y * star y) (O : Subring L) (ϖ : Kˣ)
    (hOs : ∀ y ∈ O, star y ∈ O) (hϖO : algebraMap K L (ϖ : K) ∈ O)
    (hϖnu : ¬ ∃ z ∈ O, algebraMap K L (ϖ : K) * z = 1)
    (hdich : ∀ y ∈ O, (∃ z ∈ O, y = algebraMap K L (ϖ : K) * z) ∨ ∃ z ∈ O, y * z = 1)
    (hnorm : ∀ s : K, algebraMap K L s ∈ O → (∃ r ∈ O, algebraMap K L s * r = 1) → ∃ w ∈ O, N w = s) :
    (∀ y ∈ O, (¬ ∃ z ∈ O, y = algebraMap K L (ϖ : K) * z) →
      algebraMap K L (N y) ∈ O ∧ (¬ ∃ t, algebraMap K L t ∈ O ∧ N y = ϖ * t) ∧
        ∃ r, algebraMap K L r ∈ O ∧ N y * r = 1) ∧
    (∀ s, algebraMap K L s ∈ O → (¬ ∃ t, algebraMap K L t ∈ O ∧ s = ϖ * t) →
      (∃ r, algebraMap K L r ∈ O ∧ s * r = 1) ∧ ∃ w ∈ O, ∃ v ∈ O, w * v = 1 ∧ N w = s) := by
  set ι := algebraMap K L with hι
  have hNmul1 : ∀ y z, y * z = 1 → N y * N z = 1 := by
    intro y z h
    apply hinj
    rw [map_mul, hN, hN, map_one]
    calc y * star y * (z * star z) = (y * z) * star (y * z) := by rw [star_mul']; ring
      _ = 1 := by rw [h, star_one, one_mul]
  refine ⟨fun y hy hny => ?_, fun s hs hns => ?_⟩
  · have hNO : ι (N y) ∈ O := by rw [hN]; exact O.mul_mem hy (hOs y hy)
    obtain ⟨z, hz, hyz⟩ := (hdich y hy).resolve_left hny
    have h1 := hNmul1 y z hyz
    have hNz : ι (N z) ∈ O := by rw [hN]; exact O.mul_mem hz (hOs z hz)
    refine ⟨hNO, ?_, N z, hNz, h1⟩
    rintro ⟨t, ht, e⟩
    apply hϖnu
    refine ⟨ι t * ι (N z), O.mul_mem ht hNz, ?_⟩
    rw [← map_mul, ← map_mul, ← mul_assoc, ← e, h1, map_one]
  · have hsu : ∃ z ∈ O, ι s * z = 1 := by
      refine (hdich _ hs).resolve_left ?_
      rintro ⟨z, hz, e⟩
      apply hns
      refine ⟨((ϖ⁻¹ : Kˣ) : K) * s, ?_, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
      have : ι (((ϖ⁻¹ : Kˣ) : K) * s) = z := by
        rw [map_mul, e, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      rw [this]; exact hz
    obtain ⟨z, hz, hsz⟩ := hsu
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hsz
      have h10 : (1 : K) = 0 := hinj (by rw [map_one, map_zero]; exact hsz.symm)
      obtain ⟨x, y, hxy⟩ := hK.exists_pair_ne
      exact hxy (by rw [← one_mul x, ← one_mul y, h10, zero_mul, zero_mul])
    obtain ⟨r, hr⟩ := hK.mul_inv_cancel hs0
    have hzr : z = ι r := by
      calc z = ι (s * r) * z := by rw [hr, map_one, one_mul]
        _ = ι r := by rw [map_mul, mul_comm (ι s), mul_assoc, hsz, mul_one]
    have hrO : ι r ∈ O := hzr ▸ hz
    refine ⟨⟨r, hrO, hr⟩, ?_⟩
    obtain ⟨w, hw, hNw⟩ := hnorm s hs ⟨ι r, hrO, by rw [← map_mul, hr, map_one]⟩
    refine ⟨w, hw, star w * ι r, O.mul_mem (hOs w hw) hrO, ?_, hNw⟩
    rw [← mul_assoc, ← hN, hNw, ← map_mul, hr, map_one]
end GlobalTheory.JR.ResidueGauss
