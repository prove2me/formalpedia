-- Prove2me | solution 1 for Kyprianou.Ch01.independentHeadAtomOnMarkSlice
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:44:38.131635+00:00
-- url     : https://prove2.me/submissions/01addde2-d786-42f4-82ec-849b24fd5eb6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch01_independentHeadAtomOnArrivalHalfLine

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hHeadLaw : HasLaw (fun w => (arrival 0 w, marks 0 w))
      ((expMeasure rate).prod jumpLaw) Q)
    (hHeadTailIndependent : IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w => ((fun n : ℕ => arrival (n + 1) w),
                 (fun n : ℕ => marks (n + 1) w))) Q)
    (K : PopulationLaws)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k j : ℕ)
    (hPop : ∀ s : ℝ≥0,
      Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w)) s ω).toNat = k} =
        K ((y - 1) + j) s k) :
    (Q {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        ¬ ((y : ℝ) * (t : ℝ) < arrival 0 ω)}).toReal =
      ∫ z in Ioc (0 : ℝ) ((y : ℝ) * (t : ℝ)) ×ˢ {((j : ℝ) - 1)},
        (K ((y - 1) + j)
          (Real.toNNReal ((t : ℝ) - z.1 / (y : ℝ))) k).toReal
        ∂(expMeasure (rate : ℝ)).prod jumpLaw := by
  let b : ℝ := (y : ℝ) * (t : ℝ)
  let u : Set ℝ := {((j : ℝ) - 1)}
  have hhalf :=
    independentHeadAtomOnArrivalHalfLine Q rate hrate offspring hNoZeroJumps arrival marks jumpLaw
      hSupport hHeadLaw hHeadTailIndependent K y hy t ht k j hPop
  rw [hhalf]
  have : IsProbabilityMeasure (expMeasure (rate : ℝ)) :=
    isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hrate)
  have hcdf : cdf (expMeasure (rate : ℝ)) 0 = 0 := by
    rw [cdf_expMeasure_eq (NNReal.coe_pos.mpr hrate) 0, if_pos le_rfl]
    simp
  have hnull : expMeasure (rate : ℝ) (Iic (0 : ℝ)) = 0 := by
    rw [← ofReal_cdf (expMeasure (rate : ℝ)) 0, hcdf, ENNReal.ofReal_zero]
  have hb : (0 : ℝ) ≤ b := by positivity
  have hdiff : (Iic b ×ˢ u) \ (Ioc (0 : ℝ) b ×ˢ u) = Iic (0 : ℝ) ×ˢ u := by
    ext z
    constructor
    · intro hz
      have hzb : z.1 ≤ b := hz.1.1
      have hzu : z.2 ∈ u := hz.1.2
      have hle : z.1 ≤ 0 := by
        by_contra hgt
        exact hz.2 ⟨⟨lt_of_not_ge hgt, hzb⟩, hzu⟩
      exact ⟨hle, hzu⟩
    · intro hz
      refine ⟨⟨hz.1.trans hb, hz.2⟩, ?_⟩
      intro hmem
      exact (lt_irrefl (0 : ℝ) (hmem.1.1.trans_le hz.1))
  have hempty : (Ioc (0 : ℝ) b ×ˢ u) \ (Iic b ×ˢ u) = ∅ := by
    ext z
    constructor
    · intro hz
      exact hz.2 ⟨hz.1.1.2, hz.1.2⟩
    · intro hz
      simp at hz
  refine setIntegral_congr_set ?_
  rw [ae_eq_set]
  constructor
  · rw [hdiff, Measure.prod_prod, hnull, zero_mul]
  · rw [hempty, measure_empty]
