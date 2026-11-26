-- Prove2me | solution 1 for Kyprianou.Ch04.measurableNegativeInfimumLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:46:25.987101+00:00
-- url     : https://prove2.me/submissions/3fa1c12a-1ab8-46b0-9b48-4d008e8d9c67

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_pathRunningInfimumLimit
import Theorems.Thm_Kyprianou_Ch04_fixedHorizonSignedExtremaMeasurable
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The finite-horizon negative infima converge almost surely to a measurable variable. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hb : ∀ᵐ z ∂P, BddBelow (range (fun t : NNReal => L.X t z))) :
    ∃ Z : Ω → ℝ, Measurable Z ∧ (∀ᵐ z ∂P, 0 ≤ Z z) ∧
      (∀ᵐ z ∂P, Tendsto
        (fun t : NNReal => -sInf ((fun s : NNReal => L.X s z) '' Iic t))
        atTop (nhds (Z z))) := by
  let Z (z : Ω) := -(⨅ n : ℕ, sInf ((fun s : NNReal => L.X s z) '' Iic (n : NNReal)))
  have hZm : Measurable Z := by
    apply Measurable.neg
    exact Measurable.iInf (fun n : ℕ =>
      (Kyprianou.Ch04.fixedHorizonSignedExtremaMeasurable P F L (n : NNReal)).2)
  have hZ (z : Ω) (h : BddBelow (range (fun t : NNReal => L.X t z))) :
      Z z = -sInf (range (fun t : NNReal => L.X t z)) := by
    let R := range (fun t : NNReal => L.X t z)
    let g (n : ℕ) := sInf ((fun s : NNReal => L.X s z) '' Iic (n : NNReal))
    have hl (n : ℕ) : sInf R ≤ g n := by
      apply le_csInf (show ((fun s : NNReal => L.X s z) '' Iic (n : NNReal)).Nonempty from ⟨L.X 0 z,0,by simp,rfl⟩)
      rintro y ⟨t,ht,rfl⟩
      exact csInf_le h ⟨t,rfl⟩
    have hg : BddBelow (range g) := ⟨sInf R,by rintro y ⟨n,rfl⟩; exact hl n⟩
    have he : (⨅ n, g n) = sInf R := by
      apply le_antisymm
      · apply le_csInf (range_nonempty _)
        rintro y ⟨t,rfl⟩
        obtain ⟨n,hn⟩ := exists_nat_ge t
        have hs : BddBelow ((fun s : NNReal => L.X s z) '' Iic (n : NNReal)) :=
          h.mono (by rintro y ⟨s,hs,rfl⟩; exact ⟨s,rfl⟩)
        exact (ciInf_le hg n).trans (csInf_le hs ⟨t,hn,rfl⟩)
      · exact le_ciInf hl
    exact congrArg Neg.neg he
  refine ⟨Z,hZm,?_,?_⟩
  · filter_upwards [hb] with z hz
    rw [hZ z hz]
    exact neg_nonneg.mpr (by simpa [L.X_zero] using
      (csInf_le hz (show L.X 0 z ∈ range (fun t : NNReal => L.X t z) from ⟨0,rfl⟩)))
  · filter_upwards [hb] with z hz
    rw [hZ z hz]
    exact (Kyprianou.Ch04.pathRunningInfimumLimit (fun t => L.X t z) hz).neg
