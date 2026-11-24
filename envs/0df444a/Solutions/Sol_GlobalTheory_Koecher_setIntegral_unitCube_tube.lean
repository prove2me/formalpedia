-- Prove2me | solution 1 for GlobalTheory.Koecher.setIntegral_unitCube_tube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:24:54.94293+00:00
-- url     : https://prove2.me/submissions/f9cf0ad3-365b-4f58-bf9a-54acfd9c084c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
import Theorems.Thm_GlobalTheory_SCV_eq_of_invariant_real
import Theorems.Thm_GlobalTheory_differentiableOn_setIntegral_of_holomorphic_of_continuousOn
import Theorems.Thm_GlobalTheory_setIntegral_unitCube_add_right_of_periodic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.Koecher
namespace GlobalTheory.Koecher
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℂ) → ℂ} {U : Set (ι → ℂ)} (hU : IsOpen U) (hU' : IsPreconnected U)
    (htube : ∀ z ∈ U, ∀ t : ι → ℝ, (fun i => (t i : ℂ)) + z ∈ U) (hf : DifferentiableOn ℂ f U)
    (hper : ∀ z ∈ U, ∀ i, f (z + Pi.single i 1) = f z) {w w' : ι → ℂ} (hw : w ∈ U)
    (hw' : w' ∈ U) :
    ∫ x in Set.Icc (0 : ι → ℝ) 1, f ((fun i => (x i : ℂ)) + w)
      = ∫ x in Set.Icc (0 : ι → ℝ) 1, f ((fun i => (x i : ℂ)) + w') := by
  have hd : DifferentiableOn ℂ
      (fun w => ∫ x in Set.Icc (0 : ι → ℝ) 1, f ((fun i => (x i : ℂ)) + w)) U := by
    refine (differentiableOn_setIntegral_of_holomorphic_of_continuousOn
      (F := fun (x : ι → ℝ) w => f ((fun i => (x i : ℂ)) + w)) hU
      isCompact_Icc subset_rfl measurableSet_Icc isCompact_Icc.measure_lt_top.ne ?_ ?_).1
    · refine hf.continuousOn.comp
        (f := fun q : (ι → ℝ) × (ι → ℂ) => (fun i => (q.1 i : ℂ)) + q.2) (by fun_prop) ?_
      exact fun q hq => htube _ hq.2 _
    · intro x _
      exact hf.comp ((differentiable_const _).add differentiable_id).differentiableOn
        fun z hz => htube _ hz _
  exact SCV.eq_of_invariant_real hU hU' hd
    (fun z hz t _ => by
      have := setIntegral_unitCube_add_right_of_periodic
        (F := fun x : ι → ℝ => f ((fun i => (x i : ℂ)) + z)) (fun i x => by
          rw [← hper _ (htube z hz x) i]
          congr 1
          funext j
          by_cases hij : j = i
          · subst hij; simp; ring
          · simp [hij]) t
      rw [← this]
      congr 1
      funext x
      congr 1
      funext j
      simp
      ring) hw hw'
end GlobalTheory.Koecher
