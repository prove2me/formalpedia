-- Prove2me | solution 1 for GlobalTheory.KSp.Homog.measure_mul_measure_units_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:04:02.937333+00:00
-- url     : https://prove2.me/submissions/506bd9ec-0a43-460f-b3d4-94dacb51c901

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField
import Theorems.Thm_GlobalTheory_KSp_Homog_nhdsNE_neBot
import Theorems.Thm_GlobalTheory_KSp_Homog_absE_ne_zero
import Theorems.Thm_GlobalTheory_KSp_Homog_absE_ne_top
import Theorems.Thm_GlobalTheory_KSp_Homog_absE_inv
import Theorems.Thm_GlobalTheory_KSp_Homog_absE_eq_one
import Theorems.Thm_GlobalTheory_KSp_Homog_absE_eq_of_val_eq
import Theorems.Thm_GlobalTheory_KSp_Homog_measurable_absE
import Theorems.Thm_GlobalTheory_KSp_Homog_lintegral_comp_mul_left
import Theorems.Thm_GlobalTheory_KSp_Homog_map_mul_haar
import Theorems.Thm_GlobalTheory_KSp_Homog_measurableSet_U
import Theorems.Thm_GlobalTheory_KSp_Homog_inv_mem_U_iff
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.Homog
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
namespace GlobalTheory.KSp.Homog
theorem _root_.solution (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F) [SFinite n]
    (hn0 : n {0} = 0) (hn : ∀ x : F, x ≠ 0 → n.map (fun y ↦ x * y) = (absE x)⁻¹ • n)
    {A : Set F} (hA : MeasurableSet A) :
    n A * lam U = n U * lam A := by
  haveI := GlobalTheory.SplitWeil.secondCountable F
  haveI := GlobalTheory.SplitWeil.t2Space F
  haveI := nhdsNE_neBot (F := F)
  have hU := measurableSet_U (F := F)
  have hl := fun x (hx : x ≠ 0) ↦ map_mul_haar lam (x := x) hx
  have hlam0 : lam {0} = 0 := measure_singleton 0
  let K : F → F → ℝ≥0∞ := fun x y ↦ A.indicator 1 x * (absE x)⁻¹ * U.indicator 1 (x⁻¹ * y)
  let G : F → F → ℝ≥0∞ := fun y t ↦ U.indicator 1 t * A.indicator 1 (y * t)
  have hIA : Measurable (A.indicator (1 : F → ℝ≥0∞)) := measurable_one.indicator hA
  have hIU : Measurable (U.indicator (1 : F → ℝ≥0∞)) := measurable_one.indicator hU
  have hK : Measurable (Function.uncurry K) := by
    refine ((hIA.comp measurable_fst).mul (measurable_absE.comp measurable_fst).inv).mul
      (hIU.comp (measurable_fst.inv.mul measurable_snd))
  have hG : Measurable (Function.uncurry G) :=
    (hIU.comp measurable_snd).mul (hIA.comp (measurable_fst.mul measurable_snd))

  have h1 : ∫⁻ x, ∫⁻ y, K x y ∂lam ∂n = n A * lam U := by
    have h0 : ∀ᵐ x ∂n, x ≠ 0 := by
      rw [ae_iff]; simpa using hn0
    have : ∀ᵐ x ∂n, ∫⁻ y, K x y ∂lam = A.indicator 1 x * lam U := by
      filter_upwards [h0] with x hx
      simp only [K]
      rw [lintegral_const_mul, lintegral_comp_mul_left lam hl hIU (inv_ne_zero hx), absE_inv hx,
        inv_inv, lintegral_indicator_one hU, mul_assoc, ← mul_assoc (absE x)⁻¹,
        ENNReal.inv_mul_cancel (absE_ne_zero hx) (absE_ne_top x), one_mul]
      exact hIU.comp (measurable_const_mul _)
    rw [lintegral_congr_ae this, lintegral_mul_const _ hIA, lintegral_indicator_one hA]

  have h2 : ∫⁻ y, ∫⁻ x, K x y ∂n ∂lam = ∫⁻ y, ∫⁻ t, G y t ∂n ∂lam := by
    have h0 : ∀ᵐ y ∂lam, y ≠ 0 := by
      rw [ae_iff]; simpa using hlam0
    apply lintegral_congr_ae
    filter_upwards [h0] with y hy
    have hf : Measurable fun x ↦ K x y := hK.comp (measurable_id.prodMk measurable_const)
    have hsub := lintegral_comp_mul_left n hn hf hy
    have hpt : ∀ t, K (y * t) y = (absE y)⁻¹ * G y t := by
      intro t
      simp only [K, G]
      have e : (y * t)⁻¹ * y = t⁻¹ := by rw [_root_.mul_inv_rev, inv_mul_cancel_right₀ hy]
      rw [e]
      by_cases ht : t ∈ (U : Set F)
      · have hv : valuation F (y * t) = valuation F y := by
          rw [map_mul, show valuation F t = 1 from ht, mul_one]
        rw [absE_eq_of_val_eq hv, Set.indicator_of_mem ((inv_mem_U_iff t).mpr ht),
          Set.indicator_of_mem ht]
        simp only [Pi.one_apply]; ring
      · rw [Set.indicator_of_notMem (fun h ↦ ht ((inv_mem_U_iff t).mp h)),
          Set.indicator_of_notMem ht]
        simp
    simp only [hpt] at hsub
    rw [lintegral_const_mul _ (show Measurable fun t ↦ G y t from
      hG.comp (measurable_const.prodMk measurable_id))] at hsub
    have hne := absE_ne_zero hy
    have hnt := absE_ne_top y

    have := congrArg (fun z ↦ absE y * z) hsub
    simp only [← mul_assoc, ENNReal.mul_inv_cancel hne hnt, one_mul] at this
    exact this.symm

  have h3 : ∫⁻ t, ∫⁻ y, G y t ∂lam ∂n = n U * lam A := by
    have : ∀ t, ∫⁻ y, G y t ∂lam = U.indicator 1 t * lam A := by
      intro t
      simp only [G]
      rw [lintegral_const_mul]
      swap; · exact hIA.comp (measurable_mul_const t)
      by_cases ht : t ∈ (U : Set F)
      · have ht0 : t ≠ 0 := by rintro rfl; simp [U] at ht
        simp_rw [mul_comm _ t]
        rw [lintegral_comp_mul_left lam hl hIA ht0, absE_eq_one ht, inv_one, one_mul,
          lintegral_indicator_one hA]
      · simp [Set.indicator_of_notMem ht]
    simp_rw [this]
    rw [lintegral_mul_const _ hIU, lintegral_indicator_one hU]
  rw [← h1, lintegral_lintegral_swap hK.aemeasurable, h2,
    lintegral_lintegral_swap hG.aemeasurable, h3]
end GlobalTheory.KSp.Homog
