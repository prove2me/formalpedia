-- Prove2me | solution 1 for GlobalTheory.setIntegral_unitCube_add_right_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:42:44.444025+00:00
-- url     : https://prove2.me/submissions/27575273-7150-4d80-8c91-28ac9dda0fc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ShiftSingleInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Theorems.Thm_GlobalTheory_apply_add_intCast_vec_of_unit_periods

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
namespace GlobalTheory
theorem _root_.solution {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : (ι → ℝ) → E}
    (hF : ∀ (i : ι) x, F (x + Pi.single i 1) = F x) (t : ι → ℝ) :
    ∫ x in Set.Icc (0 : ι → ℝ) 1, F (x + t) = ∫ x in Set.Icc (0 : ι → ℝ) 1, F x := by
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  haveI : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
  let G : UnitAddTorus ι → E := fun y => F fun i => (AddCircle.equivIoc 1 0 (y i) : ℝ)
  have hG : ∀ x : ι → ℝ, G (fun i => (x i : UnitAddCircle)) = F x := by
    intro x
    have h : ∀ i, ∃ n : ℤ, (AddCircle.equivIoc 1 0 (x i : UnitAddCircle) : ℝ) = x i + n := by
      intro i
      have h1 : ((AddCircle.equivIoc 1 0 (x i : UnitAddCircle) : ℝ) : UnitAddCircle) = x i :=
        (AddCircle.equivIoc 1 0).symm_apply_apply _
      rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff] at h1
      obtain ⟨k, hk⟩ := h1
      refine ⟨k, ?_⟩
      rw [zsmul_eq_mul, mul_one] at hk
      linarith
    choose n hn using h
    have := apply_add_intCast_vec_of_unit_periods hF n x
    rw [← this]
    simp only [G, hn]
    rfl
  have hae : Set.Icc (0 : ι → ℝ) 1 =ᵐ[volume]
      {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} := by
    have h := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : ι => (volume : Measure ℝ))
      (f := (0 : ι → ℝ)) (g := 1)
    have e : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)}
        = Set.univ.pi fun i => Set.Ioc ((0 : ι → ℝ) i) ((1 : ι → ℝ) i) := by
      ext x
      simp [Set.mem_pi]
    rw [e]
    exact h.symm
  rw [setIntegral_congr_set hae, setIntegral_congr_set hae]
  have h1 := UnitAddTorus.integral_preimage G 0
  have h2 := UnitAddTorus.integral_preimage (fun y => G (y + fun i => (t i : UnitAddCircle))) 0
  have h3 : ∫ y : UnitAddTorus ι, G (y + fun i => (t i : UnitAddCircle)) = ∫ y, G y :=
    integral_add_right_eq_self G _
  have h4 : ∀ x : ι → ℝ, G ((fun i => (x i : UnitAddCircle)) + fun i => (t i : UnitAddCircle))
      = F (x + t) := fun x => hG (x + t)
  simp only [hG] at h1
  simp only [h4] at h2
  rw [← h1, ← h2]
  exact h3
end GlobalTheory
