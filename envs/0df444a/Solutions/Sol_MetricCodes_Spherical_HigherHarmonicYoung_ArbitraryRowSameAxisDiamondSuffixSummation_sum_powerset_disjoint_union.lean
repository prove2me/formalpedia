-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation.sum_powerset_disjoint_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/cfbc265d-6f0e-406e-8a21-a589ba831a9e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
theorem _root_.solution
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (lower upper : Finset α) (hdisjoint : Disjoint lower upper)
    (f : Finset α → M) :
    (∑ S ∈ (lower ∪ upper).powerset, f S) =
      ∑ U ∈ upper.powerset,
        ∑ L ∈ lower.powerset, f (L ∪ U) := by
  classical
  rw [← Finset.sum_product upper.powerset lower.powerset
    (fun z => f (z.2 ∪ z.1))]
  apply Finset.sum_bij
    (fun S _ => (S ∩ upper, S ∩ lower))
  · intro S _
    simp only [Finset.mem_product, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro S hS T hT heq
    have hu : S ∩ upper = T ∩ upper := congrArg Prod.fst heq
    have hl : S ∩ lower = T ∩ lower := congrArg Prod.snd heq
    have hsubS : S ⊆ lower ∪ upper := Finset.mem_powerset.mp hS
    have hsubT : T ⊆ lower ∪ upper := Finset.mem_powerset.mp hT
    ext a
    constructor
    · intro ha
      rcases Finset.mem_union.mp (hsubS ha) with halow | haup
      · have ha' : a ∈ S ∩ lower := Finset.mem_inter.mpr ⟨ha, halow⟩
        rw [hl] at ha'
        exact (Finset.mem_inter.mp ha').1
      · have ha' : a ∈ S ∩ upper := Finset.mem_inter.mpr ⟨ha, haup⟩
        rw [hu] at ha'
        exact (Finset.mem_inter.mp ha').1
    · intro ha
      rcases Finset.mem_union.mp (hsubT ha) with halow | haup
      · have ha' : a ∈ T ∩ lower := Finset.mem_inter.mpr ⟨ha, halow⟩
        rw [← hl] at ha'
        exact (Finset.mem_inter.mp ha').1
      · have ha' : a ∈ T ∩ upper := Finset.mem_inter.mpr ⟨ha, haup⟩
        rw [← hu] at ha'
        exact (Finset.mem_inter.mp ha').1
  · rintro ⟨U, L⟩ hUL
    have hU : U ⊆ upper :=
      Finset.mem_powerset.mp (Finset.mem_product.mp hUL).1
    have hL : L ⊆ lower :=
      Finset.mem_powerset.mp (Finset.mem_product.mp hUL).2
    refine ⟨L ∪ U, Finset.mem_powerset.mpr ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact Finset.mem_union_left _ (hL ha)
      · exact Finset.mem_union_right _ (hU ha)
    · apply Prod.ext
      · change (L ∪ U) ∩ upper = U
        ext a
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨ha, haup⟩
          rcases Finset.mem_union.mp ha with halow | haU
          · exact False.elim
              ((Finset.disjoint_left.mp hdisjoint (hL halow)) haup)
          · exact haU
        · intro ha
          exact ⟨Finset.mem_union_right _ ha, hU ha⟩
      · change (L ∪ U) ∩ lower = L
        ext a
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨ha, halow⟩
          rcases Finset.mem_union.mp ha with haL | haup
          · exact haL
          · exact False.elim
              ((Finset.disjoint_left.mp hdisjoint halow) (hU haup))
        · intro ha
          exact ⟨Finset.mem_union_left _ ha, hL ha⟩
  · intro S hS
    congr 1
    ext a
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro ha
      rcases Finset.mem_union.mp ((Finset.mem_powerset.mp hS) ha) with
        halow | haup
      · exact Or.inl ⟨ha, halow⟩
      · exact Or.inr ⟨ha, haup⟩
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩)
      · exact ha
      · exact ha
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
