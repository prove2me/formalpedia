-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_cube_fourierCoeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:59.633249+00:00
-- url     : https://prove2.me/submissions/61792941-a6fd-41fc-8ddb-4aa82fb45599

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Theorems.Thm_GlobalTheory_apply_add_intCast_of_periodic_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {g : ℕ} {A : (Fin g → ℝ) → ℂ} (hc : Continuous A)
    (hA : ∀ (i : Fin g) x, A (x + Pi.single i 1) = A x)
    (h : ∀ m : Fin g → ℤ, (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      A x * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = 0) (y : Fin g → ℝ) :
    A y = 0 := by
  set p : (Fin g → ℝ) → UnitAddTorus (Fin g) := fun x i ↦ (x i : UnitAddCircle) with hp
  have hq : IsOpenQuotientMap p :=
    IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk
  set f₀ : UnitAddTorus (Fin g) → ℂ := fun z ↦ A (Function.surjInv hq.surjective z) with hf₀
  have hfp : ∀ x, f₀ (p x) = A x := fun x ↦ by
    set x' := Function.surjInv hq.surjective (p x)
    have h1 : p x' = p x := Function.surjInv_eq _ _
    have h2 : ∀ i, ∃ n : ℤ, (n : ℝ) = x' i - x i := fun i ↦ by
      have h3 : ((x' i - x i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]; exact congrFun h1 i
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h3
      exact ⟨n, by simpa using hn⟩
    choose n hn using h2
    rw [← apply_add_intCast_of_periodic_single hA n x]
    change A x' = _
    congr 1
    funext i
    simp [hn]
  let f : C(UnitAddTorus (Fin g), ℂ) := ⟨f₀,
    hq.isQuotientMap.continuous_iff.2 <| by
      rw [show f₀ ∘ p = A from funext hfp]; exact hc⟩
  have hchar : ∀ n x, UnitAddTorus.mFourier (-n) (p x) =
      cexp (-(2 * Real.pi * I) * ∑ i, (n i : ℂ) * (x i : ℂ)) := fun n x ↦ by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hp, fourier_coe_apply,
      ← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Pi.neg_apply]
    push_cast
    ring
  have hcoeff : ∀ n, UnitAddTorus.mFourierCoeff f n = 0 := fun n ↦ by
    rw [UnitAddTorus.mFourierCoeff_eq_integral f n 0, ← h n]
    simp only [Pi.zero_apply, zero_add]
    have h2 : {x : Fin g → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
        Set.pi Set.univ fun i ↦ Set.Ioc ((0 : Fin g → ℝ) i) ((1 : Fin g → ℝ) i) := by
      ext x; simp
    rw [h2, MeasureTheory.setIntegral_congr_set
      (μ := MeasureTheory.volume) MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc]
    refine MeasureTheory.integral_congr_ae (.of_forall fun x ↦ ?_)
    change UnitAddTorus.mFourier (-n) (p x) • f₀ (p x) = _
    simp only [hchar, hfp, smul_eq_mul, mul_comm]
  have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f)
    (by rw [funext hcoeff]; exact summable_zero) (p y)
  change HasSum _ (f₀ (p _)) at hsum
  simp only [hcoeff, zero_smul, hfp] at hsum
  exact hsum.unique hasSum_zero
end GlobalTheory
