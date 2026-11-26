-- Prove2me | solution 1 for Malliavin.inner_partitionElementaryBrownianValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:35:45.352586+00:00
-- url     : https://prove2.me/submissions/e1d9e0bd-cbf1-409c-9220-ea2623555437

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_ElementaryIto
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_inner_elementaryBrownianValue_eq_inner_elementaryPredictable_of_le
import Theorems.Thm_Malliavin_inner_elementaryBrownianValue_eq_inner_elementaryPredictable_same
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


attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply

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
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) {n : ℕ} (Q : Partition n)
    (Z Y : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    inner ℝ (partitionElementaryBrownianValue hB hsm hnat Q Z)
        (partitionElementaryBrownianValue hB hsm hnat Q Y) =
      inner ℝ (partitionElementaryPredictable Q Z)
        (partitionElementaryPredictable Q Y) := by
  simp only [partitionElementaryBrownianValue, partitionElementaryPredictable,
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
    exact inner_elementaryBrownianValue_eq_inner_elementaryPredictable_same
      hB hsm hnat hiord (Z i) (Y i)
  · rcases Fin.lt_or_lt_of_ne hij with hij | hji
    · calc
        inner ℝ (elementaryBrownianValue hB hsm hnat hjord (Z j))
            (elementaryBrownianValue hB hsm hnat hiord (Y i)) =
            inner ℝ (elementaryBrownianValue hB hsm hnat hiord (Y i))
              (elementaryBrownianValue hB hsm hnat hjord (Z j)) := real_inner_comm _ _
        _ = inner ℝ
              (elementaryPredictable 𝓕 (Q.t i.castSucc) (Q.t i.succ) (Y i))
              (elementaryPredictable 𝓕 (Q.t j.castSucc) (Q.t j.succ) (Z j)) :=
          inner_elementaryBrownianValue_eq_inner_elementaryPredictable_of_le
            hB hsm hnat hiord (partition_succ_le_castSucc Q hij) hjord (Y i) (Z j)
        _ = inner ℝ
              (elementaryPredictable 𝓕 (Q.t j.castSucc) (Q.t j.succ) (Z j))
              (elementaryPredictable 𝓕 (Q.t i.castSucc) (Q.t i.succ) (Y i)) :=
          real_inner_comm _ _
    · exact inner_elementaryBrownianValue_eq_inner_elementaryPredictable_of_le
        hB hsm hnat hjord (partition_succ_le_castSucc Q hji) hiord (Z j) (Y i)
end Malliavin
