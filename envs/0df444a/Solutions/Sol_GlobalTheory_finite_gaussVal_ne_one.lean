-- Prove2me | solution 1 for GlobalTheory.finite_gaussVal_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:11:12.706493+00:00
-- url     : https://prove2.me/submissions/a216bdc9-7845-4e58-859e-1d5c7dec1363

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial Module IsDedekindDomain

theorem solution {O K σ : Type*} [CommRing O] [IsDedekindDomain O] [Field K]
    [Algebra O K] [IsFractionRing O K] {f : MvPolynomial σ K} (hf : f ≠ 0) :
    {p : HeightOneSpectrum O | gaussVal (p.valuation K) f ≠ 1}.Finite := by
  have finite_val_ne_one {x : K} (hx : x ≠ 0) :
      {p : HeightOneSpectrum O | p.valuation K x ≠ 1}.Finite := by
    have hsub : {p : HeightOneSpectrum O | p.valuation K x ≠ 1} ⊆
        HeightOneSpectrum.Support O x ∪ HeightOneSpectrum.Support O x⁻¹ := by
      intro p hp
      have hx0 : p.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      rcases lt_or_gt_of_ne hp with hlt | hgt
      · refine Or.inr ?_
        change 1 < p.valuation K x⁻¹
        rw [map_inv₀]
        exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hx0, hlt⟩
      · exact Or.inl hgt
    exact ((HeightOneSpectrum.Support.finite (R := O) x).union
      (HeightOneSpectrum.Support.finite (R := O) x⁻¹)).subset hsub
  have hsub : {p : HeightOneSpectrum O | gaussVal (p.valuation K) f ≠ 1} ⊆
      ⋃ m ∈ f.support, {p : HeightOneSpectrum O | p.valuation K (coeff m f) ≠ 1} := by
    intro p hp
    by_contra hnone
    simp only [Set.mem_iUnion, exists_prop, not_exists, not_and, Set.mem_ofPred_eq,
      not_not] at hnone
    have heq : gaussVal (p.valuation K) f = 1 := by
      refine le_antisymm ?_ ?_
      · rw [gaussVal_le_iff]
        intro m
        by_cases hm : coeff m f = 0
        · simp [hm]
        · exact (hnone m (mem_support_iff.mpr hm)).le
      · obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hf
        have : p.valuation K (coeff m f) = 1 := hnone m (mem_support_iff.mpr hm)
        rw [← this]
        exact le_gaussVal _ f m
    exact hp heq
  refine Set.Finite.subset ?_ hsub
  refine (f.support.finite_toSet).biUnion fun m hm => ?_
  exact finite_val_ne_one (mem_support_iff.mp hm)
