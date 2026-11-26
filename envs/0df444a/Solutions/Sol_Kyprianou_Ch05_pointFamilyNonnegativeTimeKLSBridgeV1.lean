-- Prove2me | solution 1 for Kyprianou.Ch05.pointFamilyNonnegativeTimeKLSBridgeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:48:12.553851+00:00
-- url     : https://prove2.me/submissions/50debb09-b108-4a87-9925-7e7a86e609a4

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_pointFamilyFinitePRMCoreCh02V1
import Theorems.Thm_Kyprianou_Ch02_pointFamilyPRMResidualV3
import Theorems.Thm_ProbabilityTheory_indep_prmEvalSigma
import Theorems.Thm_Kyprianou_Ch05_pointFamilyAllRegionEvalMeasurableV1
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) P) :
    ∃ N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P Pi,
      ∀ w, N.N w = (poissonRandomMeasure K Z w).restrict (Ici (0 : ℝ) ×ˢ univ) := by
  let S : Set (ℝ × ℝ) := Ici (0 : ℝ) ×ˢ univ
  let m := (volume : Measure ℝ).prod Pi
  let M := fun w => (poissonRandomMeasure K Z w).restrict S
  have hS : MeasurableSet S := measurableSet_Ici.prod MeasurableSet.univ
  have hI : LevyStochCalc.Poisson.referenceIntensity Pi = m.restrict S :=
    Measure.restrict_prod_eq_prod_univ _
  have hM (w : Ω) (B : Set (ℝ × ℝ)) (hB : MeasurableSet B) :
      M w B = poissonRandomMeasure K Z w (B ∩ S) := Measure.restrict_apply hB
  have hCore := Kyprianou.Ch02.pointFamilyFinitePRMCoreCh02V1 P m K Z hd
  have hRes := Kyprianou.Ch02.pointFamilyPRMResidualV3 P m K Z hd
  have hmass (B : Set (ℝ × ℝ)) (hB : MeasurableSet B) :
      LevyStochCalc.Poisson.referenceIntensity Pi B = m (B ∩ S) := by
    rw [hI,Measure.restrict_apply hB]
  refine ⟨⟨M,?_,?_,?_,?_,?_,?_⟩,fun _ => rfl⟩
  · intro B hB
    simp_rw [hM _ B hB]
    exact hCore.1 _ (hB.inter hS)
  · intro B hB hfin
    simp_rw [hM _ B hB]
    exact hRes.1 _ (hB.inter hS) (lt_top_iff_ne_top.mpr ((hmass B hB) ▸ hfin))
  · intro B hB hinf
    simp_rw [hM _ B hB]
    exact hRes.2.1 _ (hB.inter hS) ((hmass B hB) ▸ hinf)
  · intro B hB hfin
    simp_rw [hM _ B hB,hmass B hB]
    exact hCore.2.1 _ (hB.inter hS) (lt_top_iff_ne_top.mpr ((hmass B hB) ▸ hfin))
  · intro ι _ B hB hDis
    have hEq : (fun i w => M w (B i)) =
        fun i w => poissonRandomMeasure K Z w (B i ∩ S) := by
      funext i w
      exact hM w (B i) (hB i)
    rw [hEq]
    exact hRes.2.2 (fun i => B i ∩ S) (fun i => (hB i).inter hS)
      (fun i j hij => (hDis hij).mono inter_subset_left inter_subset_left)
  · intro s t hs hst A hA hfin
    let R : Set (ℝ × ℝ) := Iic s ×ˢ univ
    let T : Set (ℝ × ℝ) := Ioc s t ×ˢ A
    have hRT : Disjoint R T := by
      refine disjoint_left.2 fun z hz hzt => ?_
      exact (not_lt_of_ge hz.1) hzt.1.1
    apply indep_of_indep_of_le (indep_prmEvalSigma hd hRT)
    · refine iSup_le fun B => iSup_le fun hB => ?_
      have he : (fun w => M w B) = fun w => poissonRandomMeasure K Z w (B ∩ S) :=
        funext fun w => hM w B hB.2
      rw [he]
      exact (Kyprianou.Ch05.pointFamilyAllRegionEvalMeasurableV1 m K Z R
        (B ∩ S) (hB.2.inter hS) (inter_subset_left.trans hB.1)).comap_le
    · have he : (fun w => M w T) = fun w => poissonRandomMeasure K Z w (T ∩ S) :=
        funext fun w => hM w T (measurableSet_Ioc.prod hA)
      rw [he]
      exact (Kyprianou.Ch05.pointFamilyAllRegionEvalMeasurableV1 m K Z T
        (T ∩ S) ((measurableSet_Ioc.prod hA).inter hS) inter_subset_left).comap_le
