-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.inner_partitionElementaryIntegralValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:32:48.408941+00:00
-- url     : https://prove2.me/submissions/3123ad8d-5f08-4f4d-abbc-9d2401c3e38b

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_ElementaryIto
import Theorems.Thm_Malliavin_ClarkOconeFamily_inner_elementaryIntegralValue_eq_inner_elementaryPredictable_of_le
import Theorems.Thm_Malliavin_ClarkOconeFamily_inner_elementaryIntegralValue_eq_inner_elementaryPredictable_same
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_partition_succ_le_castSucc
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
namespace ClarkOconeFamily
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {n : ℕ} (Q : Partition n)
    (Z Y : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    inner ℝ (C.partitionElementaryIntegralValue Q Z)
        (C.partitionElementaryIntegralValue Q Y) =
      inner ℝ (partitionElementaryPredictable Q Z)
        (partitionElementaryPredictable Q Y) := by
  simp only [partitionElementaryIntegralValue, partitionElementaryPredictable,
    sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hiord : Q.t i.castSucc ≤ Q.t i.succ :=
    Q.mono.monotone (Fin.castSucc_le_succ i)
  have hjord : Q.t j.castSucc ≤ Q.t j.succ :=
    Q.mono.monotone (Fin.castSucc_le_succ j)
  by_cases hij : i = j
  · subst j
    exact C.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_same
      hiord (Z i) (Y i)
  · rcases Fin.lt_or_lt_of_ne hij with hij | hji
    · calc
        inner ℝ (C.elementaryIntegralValue hjord (Z j))
            (C.elementaryIntegralValue hiord (Y i)) =
            inner ℝ (C.elementaryIntegralValue hiord (Y i))
              (C.elementaryIntegralValue hjord (Z j)) := real_inner_comm _ _
        _ = inner ℝ
              (elementaryPredictable 𝓕 (Q.t i.castSucc) (Q.t i.succ) (Y i))
              (elementaryPredictable 𝓕 (Q.t j.castSucc) (Q.t j.succ) (Z j)) :=
          C.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_of_le
            hiord (partition_succ_le_castSucc Q hij) hjord (Y i) (Z j)
        _ = inner ℝ
              (elementaryPredictable 𝓕 (Q.t j.castSucc) (Q.t j.succ) (Z j))
              (elementaryPredictable 𝓕 (Q.t i.castSucc) (Q.t i.succ) (Y i)) :=
          real_inner_comm _ _
    · exact C.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_of_le
        hjord (partition_succ_le_castSucc Q hji) hiord (Z j) (Y i)
end ClarkOconeFamily
end Malliavin
