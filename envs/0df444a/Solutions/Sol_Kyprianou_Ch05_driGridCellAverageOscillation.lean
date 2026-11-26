-- Prove2me | solution 1 for Kyprianou.Ch05.driGridCellAverageOscillation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:47:58.761371+00:00
-- url     : https://prove2.me/submissions/714e5916-1eae-4f45-a44c-ee2033c87549

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- The Lebesgue cell average lies between the extrema of the closed cell. -/
theorem solution
    (h : Real → Real) (hi : Integrable h)
    (hloc : ∀ a b : Real, a < b →
      BddAbove (h '' Set.Icc a b) ∧ BddBelow (h '' Set.Icc a b))
    (d : Real) (hd : 0 < d) (k : Nat) (y : Real)
    (hy : y ∈ Set.Ico ((k : Real)*d) (((k : Real)+1)*d)) :
    |h y - (∫ z in Set.Ico ((k : Real)*d) (((k : Real)+1)*d), h z ∂volume)/d| ≤
      riCellOscillation h d (k : Int) := by
  let a : Real := (k : Real)*d
  let b : Real := ((k : Real)+1)*d
  let S := h '' Icc a b
  let lo := sInf S
  let up := sSup S
  have hab : a < b := by dsimp [a,b]; nlinarith
  obtain ⟨hu,hl⟩ := hloc a b hab
  have hb (z : Real) (hz : z ∈ Ico a b) : lo ≤ h z ∧ h z ≤ up := by
    have hz' : h z ∈ S := ⟨z, ⟨hz.1,hz.2.le⟩,rfl⟩
    exact ⟨csInf_le hl hz',le_csSup hu hz'⟩
  have hv : volume (Ico a b) = ENNReal.ofReal d := by
    rw [Real.volume_Ico]
    congr 1
    dsimp [a,b]
    ring
  have hf : volume (Ico a b) ≠ ⊤ := by rw [hv]; exact ENNReal.ofReal_ne_top
  have hconst (c : Real) : (∫ z in Ico a b, c ∂volume) = d*c := by
    rw [setIntegral_const, Measure.real, hv, ENNReal.toReal_ofReal hd.le, smul_eq_mul]
  have hlow : lo ≤ (∫ z in Ico a b, h z ∂volume)/d := by
    apply (le_div_iff₀ hd).2
    have hle := setIntegral_mono_on (integrableOn_const (C := lo) hf) hi.integrableOn
      measurableSet_Ico (fun z hz => (hb z hz).1)
    rw [hconst] at hle
    linarith
  have hupp : (∫ z in Ico a b, h z ∂volume)/d ≤ up := by
    apply (div_le_iff₀ hd).2
    have hle := setIntegral_mono_on hi.integrableOn (integrableOn_const (C := up) hf)
      measurableSet_Ico (fun z hz => (hb z hz).2)
    rw [hconst] at hle
    linarith
  have hyb := hb y hy
  simp only [riCellOscillation, Int.cast_natCast]
  change |h y-(∫ z in Ico a b, h z ∂volume)/d| ≤ up-lo
  exact abs_le.mpr ⟨by linarith [hyb.1,hyb.2],by linarith [hyb.1,hyb.2]⟩
