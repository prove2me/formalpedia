-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Euler.factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:41:19.421064+00:00
-- url     : https://prove2.me/submissions/3e7dbf34-5267-4f48-960c-ecb97e5604bf

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_EulerA
import Theorems.Thm_GlobalTheory_ThK_Dbl_Euler_pres_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Euler
open MeasureTheory Set
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  [LocallyCompactSpace H] [SecondCountableTopology H] {ν : Measure H} [ν.IsHaarMeasure] {K : Subgroup H}
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [SecondCountableTopology G] {μ : Measure G} [μ.IsHaarMeasure]
namespace GlobalTheory.ThK.Dbl.Euler
theorem _root_.solution (hK : MeasurableSet (K : Set H)) (h1 : ν K = 1) (i : H →* G) (hi : Continuous i) (π : G → H) (hπ : Continuous π)
    (e : ∀ u g, π (i u * g) = u * π g) {f : G → ℂ} {l : H → ℂ} (hf : Integrable f μ)
    (hl : ∀ u g, π g = 1 → f (i u * g) = l u * f g) (hl1 : ∀ u ∈ K, l u = 1) {A : Set G} (hA : MeasurableSet A)
    (hAi : ∀ u g, i u * g ∈ A ↔ g ∈ A) : ∫ g in A, f g ∂μ = (∫ u, l u ∂ν) * ∫ g in A ∩ π ⁻¹' K, f g ∂μ := by
  let S : Set (H × G) := {p | p.1⁻¹ * π p.2 ∈ K}
  have hS : MeasurableSet S := (continuous_fst.inv.mul (hπ.comp continuous_snd)).measurable hK
  let Φ : H × G → ℂ := S.indicator fun p => A.indicator f p.2
  have vol : ∀ g, ν {u | u⁻¹ * π g ∈ K} = 1 := fun g => by
    rw [← h1, ← measure_preimage_mul ν (π g)⁻¹ K]
    congr 1
    ext u
    exact (K.inv_mem_iff.symm.trans (by simp))
  have mS : ∀ g, MeasurableSet {u | u⁻¹ * π g ∈ K} := fun g => (continuous_inv.mul continuous_const).measurable hK
  have sl : ∀ g, (fun u => Φ (u, g)) = {u | u⁻¹ * π g ∈ K}.indicator fun _ => A.indicator f g := fun g => rfl
  have hfA := hf.indicator hA
  have iΦ : Integrable Φ (ν.prod μ) := by
    refine (integrable_prod_iff' (hfA.1.comp_snd.indicator hS)).2 ⟨Filter.Eventually.of_forall fun g => ?_, ?_⟩
    · rw [sl, integrable_indicator_iff (mS g)]
      exact integrableOn_const (by simp [vol])
    · refine hfA.norm.congr (Filter.Eventually.of_forall fun g => ?_)
      have : (fun u => ‖Φ (u, g)‖) = {u | u⁻¹ * π g ∈ K}.indicator fun _ => ‖A.indicator f g‖ :=
        funext fun u => by rw [congrFun (sl g) u, norm_indicator_eq_indicator_norm]
      show _ = ∫ u, ‖Φ (u, g)‖ ∂ν
      rw [this, integral_indicator_const _ (mS g), Measure.real, vol]
      simp
  have sh : MeasurePreserving (fun p : H × G => (p.1, i p.1 * p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (g := fun u g => i u * g) ((hi.comp continuous_fst).mul continuous_snd).measurable
      (Filter.Eventually.of_forall fun u => map_mul_left_eq_self μ (i u))
  have i2 := sh.integrable_comp_of_integrable iΦ
  have mB : MeasurableSet (A ∩ π ⁻¹' K) := hA.inter (hπ.measurable hK)
  calc ∫ g in A, f g ∂μ = ∫ g, ∫ u, Φ (u, g) ∂ν ∂μ := by
        rw [← integral_indicator hA]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [sl]
        rw [integral_indicator_const _ (mS g), Measure.real, vol]
        simp
    _ = ∫ u, ∫ g, Φ (u, i u * g) ∂μ ∂ν := by
        rw [← integral_integral_swap (f := fun u g => Φ (u, g)) iΦ]
        exact integral_congr_ae (Filter.Eventually.of_forall fun u =>
          (integral_mul_left_eq_self (fun g => Φ (u, g)) (i u)).symm)
    _ = ∫ g, ∫ u, Φ (u, i u * g) ∂ν ∂μ := integral_integral_swap (f := fun u g => Φ (u, i u * g)) i2
    _ = _ := by
        rw [← integral_const_mul, ← integral_indicator mB]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        by_cases hg : g ∈ A ∩ π ⁻¹' K
        · have z : π (i (π g)⁻¹ * g) = 1 := by rw [e, inv_mul_cancel]
          have w : ∀ u, f (i u * g) = l (u * π g) * f (i (π g)⁻¹ * g) := fun u => by
            rw [← hl _ _ z, ← mul_assoc, ← map_mul, mul_inv_cancel_right]
          have w1 := w 1
          rw [map_one, one_mul, one_mul, hl1 _ hg.2, one_mul] at w1
          have : ∀ u, Φ (u, i u * g) = l (u * π g) * f g := fun u => by
            simp only [Φ]
            rw [indicator_of_mem (show (u, i u * g) ∈ S by simpa [S, e] using hg.2), indicator_of_mem ((hAi u g).2 hg.1), w, w1]
          simp only [this]
          rw [indicator_of_mem hg, integral_mul_const,
            (pres_right hK h1 hg.2).integral_comp (Homeomorph.mulRight (π g)).measurableEmbedding l]
        · have : ∀ u, Φ (u, i u * g) = 0 := fun u => by
            simp only [Φ]
            by_cases h2 : π g ∈ K
            · exact indicator_apply_eq_zero.2 fun _ => indicator_of_notMem (fun h => hg ⟨(hAi u g).1 h, h2⟩) _
            · exact indicator_of_notMem (by simpa [S, e] using h2) _
          simp only [this]
          rw [indicator_of_notMem hg, integral_zero]
end GlobalTheory.ThK.Dbl.Euler
