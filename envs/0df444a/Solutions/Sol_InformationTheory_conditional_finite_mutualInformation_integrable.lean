-- Prove2me | solution 1 for InformationTheory.conditional_finite_mutualInformation_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T03:16:04.45796+00:00
-- url     : https://prove2.me/submissions/18f0f821-0ad7-4e2b-8dad-0b9ece9cec73

import Definitions.Def_BayesianTSRoundConditionalGains
import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral_of_ae
import Theorems.Thm_InformationTheory_categorical_toReal_klDiv_eq_sum
import Theorems.Thm_InformationTheory_kernel_average_categorical_kl_le_marginal_entropy_general
import Theorems.Thm_InformationTheory_klDiv_map_measurableEmbedding
import Theorems.Thm_InformationTheory_finite_range_mutualInformation_le_marginal_entropy
import Mathlib.Probability.Kernel.CompProdEqIff

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal BigOperators

namespace InformationTheory

private theorem categorical_kernel_ac_marginal
    {Alpha : Type*} {mAlpha : MeasurableSpace Alpha}
    {k : ℕ} (mu : Measure Alpha) [IsProbabilityMeasure mu]
    (kappa : Kernel Alpha (Fin k)) [IsMarkovKernel kappa] :
    ∀ᵐ x ∂mu, kappa x ≪ (kappa ∘ₘ mu) := by
  let p : Measure (Fin k) := kappa ∘ₘ mu
  have hsingle (a : Fin k) (ha : p {a} = 0) :
      ∀ᵐ x ∂mu, kappa x {a} = 0 := by
    dsimp [p] at ha
    rw [Measure.bind_apply (MeasurableSet.singleton a) kappa.aemeasurable] at ha
    rw [lintegral_eq_zero_iff
      (Kernel.measurable_coe kappa (MeasurableSet.singleton a))] at ha
    exact ha
  have hall : ∀ᵐ x ∂mu, ∀ a : Fin k, p {a} = 0 → kappa x {a} = 0 := by
    rw [ae_all_iff]
    intro a
    by_cases ha : p {a} = 0
    · filter_upwards [hsingle a ha] with x hx
      exact fun _ ↦ hx
    · exact Filter.Eventually.of_forall fun _ h ↦ (ha h).elim
  filter_upwards [hall] with x hx
  apply Measure.AbsolutelyContinuous.mk
  intro s _ hs
  have hs' : p (↑s.toFinite.toFinset : Set (Fin k)) = 0 := by simpa using hs
  have hzero : ∀ a ∈ s.toFinite.toFinset, kappa x {a} = 0 := by
    intro a ha
    apply hx a
    exact measure_mono_null (Set.singleton_subset_iff.mpr ha) hs'
  rw [← Set.Finite.coe_toFinset s.toFinite, ← sum_measure_singleton]
  exact Finset.sum_eq_zero hzero

private theorem mutualInformation_eq_categorical_kernel_average
    {Y : Type} {mY : MeasurableSpace Y} [StandardBorelSpace Y] [Nonempty Y]
    {k : ℕ} [NeZero k]
    (rho : Measure (Fin k × Y)) [IsProbabilityMeasure rho]
    (p : Measure (Fin k)) [IsProbabilityMeasure p]
    (kappa : Kernel Y (Fin k)) [IsMarkovKernel kappa]
    (hp : rho.map Prod.fst = p)
    (hdecomp : rho.map Prod.swap = (rho.map Prod.snd) ⊗ₘ kappa) :
    (klDiv rho (p.prod (rho.map Prod.snd))).toReal =
      ∫ y, ∑ a, (kappa y).real {a} *
        Real.log ((kappa y).real {a} / p.real {a}) ∂rho.map Prod.snd := by
  let muY : Measure Y := rho.map Prod.snd
  letI : IsProbabilityMeasure muY := by
    dsimp [muY]
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hmarg : kappa ∘ₘ muY = p := by
    have h := congrArg (Measure.map Prod.snd) hdecomp
    change (rho.map Prod.swap).snd = (muY ⊗ₘ kappa).snd at h
    rw [Measure.snd_compProd] at h
    rw [Measure.snd_map_swap] at h
    change rho.fst = p at hp
    exact h.symm.trans hp
  have hac : ∀ᵐ y ∂muY, kappa y ≪ p := by
    simpa [hmarg] using categorical_kernel_ac_marginal muY kappa
  have hlt : ∀ᵐ y ∂muY, klDiv (kappa y) p < ∞ := by
    filter_upwards [hac] with y hy
    exact lt_top_iff_ne_top.mpr (klDiv_ne_top hy Integrable.of_finite)
  let F : Y → ℝ := fun y ↦ ∑ a, (kappa y).real {a} *
    Real.log ((kappa y).real {a} / p.real {a})
  have hF : Measurable F := by
    apply Finset.measurable_sum
    intro a _
    have hqa : Measurable (fun y ↦ (kappa y).real {a}) :=
      (Kernel.measurable_coe kappa (MeasurableSet.singleton a)).ennreal_toReal
    exact hqa.mul (Real.measurable_log.comp (hqa.div_const _))
  have hKL : (fun y ↦ (klDiv (kappa y) p).toReal) =ᵐ[muY] F := by
    filter_upwards [hac] with y hy
    exact categorical_toReal_klDiv_eq_sum (kappa y) p hy
  have hmeasKL : AEMeasurable (fun y ↦ klDiv (kappa y) p) muY := by
    have hreal : AEMeasurable (fun y ↦ (klDiv (kappa y) p).toReal) muY :=
      hF.aemeasurable.congr hKL.symm
    apply AEMeasurable.congr hreal.ennreal_ofReal
    filter_upwards [hlt] with y hy
    exact ENNReal.ofReal_toReal hy.ne
  have hswap := klDiv_map_measurableEmbedding
    (MeasurableEquiv.prodComm.measurableEmbedding :
      MeasurableEmbedding (Prod.swap : Fin k × Y → Y × Fin k))
    rho (p.prod muY)
  have hden : Measure.map Prod.swap (p.prod muY) = muY.prod p := by
    exact Measure.prod_swap
  have hKLcomp : klDiv rho (p.prod muY) =
      klDiv (muY ⊗ₘ kappa) (muY ⊗ₘ Kernel.const Y p) := by
    have h := hswap.symm
    change klDiv rho (p.prod muY) =
      klDiv (rho.map Prod.swap) ((p.prod muY).map Prod.swap) at h
    rw [hdecomp, hden, ← Measure.compProd_const] at h
    simpa [muY] using h
  have hlin : klDiv (muY ⊗ₘ kappa) (muY ⊗ₘ Kernel.const Y p) =
      ∫⁻ y, klDiv (kappa y) p ∂muY := by
    simpa only [Kernel.const_apply] using
      (klDiv_compProd_self_eq_lintegral_of_ae
        muY kappa (Kernel.const Y p) (by simpa using hac))
  rw [hKLcomp, hlin, ← integral_toReal hmeasKL hlt]
  exact integral_congr_ae hKL

theorem _root_.solution
    {Omega H Y : Type} {mOmega : MeasurableSpace Omega}
    {mH : MeasurableSpace H} {mY : MeasurableSpace Y}
    [StandardBorelSpace H] [StandardBorelSpace Y] [Nonempty Y]
    {k : ℕ} [NeZero k]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (hist : Omega → H) (obs : Omega → Y) (act : Omega → Fin k)
    (hhist : Measurable hist) (hobs : Measurable obs) (hact : Measurable act) :
    Integrable
      (fun h ↦ (klDiv (condDistrib (fun w ↦ (act w, obs w)) hist mu h)
        ((condDistrib act hist mu h).prod (condDistrib obs hist mu h))).toReal)
      (mu.map hist) := by
  let nu : Measure H := mu.map hist
  let kAY : Kernel H (Fin k × Y) := condDistrib (fun w ↦ (act w, obs w)) hist mu
  let kA : Kernel H (Fin k) := condDistrib act hist mu
  let kY : Kernel H Y := condDistrib obs hist mu
  let post : Kernel (H × Y) (Fin k) :=
    condDistrib act (fun w ↦ (hist w, obs w)) mu
  have hAY : nu ⊗ₘ kAY = mu.map (fun w ↦ (hist w, (act w, obs w))) := by
    exact compProd_map_condDistrib (hact.prodMk hobs).aemeasurable
  have hY : nu ⊗ₘ kY = mu.map (fun w ↦ (hist w, obs w)) := by
    exact compProd_map_condDistrib hobs.aemeasurable
  have hpost : (mu.map (fun w ↦ (hist w, obs w))) ⊗ₘ post =
      mu.map (fun w ↦ ((hist w, obs w), act w)) := by
    exact compProd_map_condDistrib hact.aemeasurable
  have hleft : nu ⊗ₘ (kAY.map Prod.swap) =
      mu.map (fun w ↦ (hist w, (obs w, act w))) := by
    rw [Measure.compProd_map measurable_swap, hAY,
      Measure.map_map]
    · rfl
    · exact measurable_id.prodMap measurable_swap
    · exact hhist.prodMk (hact.prodMk hobs)
  have hright : nu ⊗ₘ (kY ⊗ₖ post) =
      mu.map (fun w ↦ (hist w, (obs w, act w))) := by
    rw [← Measure.compProd_assoc', hY, hpost, Measure.map_map]
    · rfl
    · exact MeasurableEquiv.prodAssoc.measurable
    · exact (hhist.prodMk hobs).prodMk hact
  have hlocal : kAY.map Prod.swap =ᵐ[nu] kY ⊗ₖ post := by
    apply Kernel.ae_eq_of_compProd_eq
    exact hleft.trans hright.symm
  have hAmap : kA =ᵐ[nu] kAY.map Prod.fst := by
    dsimp [kA, kAY, nu]
    simpa [Function.comp_def] using
      (condDistrib_comp hist (hact.prodMk hobs).aemeasurable measurable_fst)
  have hYmap : kY =ᵐ[nu] kAY.map Prod.snd := by
    dsimp [kY, kAY, nu]
    simpa [Function.comp_def] using
      (condDistrib_comp hist (hact.prodMk hobs).aemeasurable measurable_snd)
  let F : H × Y → ℝ := fun z ↦ ∑ a,
    (post z).real {a} * Real.log ((post z).real {a} / (kA z.1).real {a})
  let G : H → ℝ := fun h ↦ ∫ y, F (h, y) ∂kY h
  have hF : Measurable F := by
    apply Finset.measurable_sum
    intro a _
    have hq : Measurable (fun z : H × Y ↦ (post z).real {a}) :=
      (Kernel.measurable_coe post (MeasurableSet.singleton a)).ennreal_toReal
    have hp : Measurable (fun z : H × Y ↦ (kA z.1).real {a}) :=
      (Kernel.measurable_coe kA (MeasurableSet.singleton a)).ennreal_toReal.comp measurable_fst
    exact hq.mul (Real.measurable_log.comp (hq.div hp))
  have hG : StronglyMeasurable G := by
    exact hF.stronglyMeasurable.integral_kernel_prod_right'
  have hgainG :
      (fun h ↦ (klDiv (kAY h) ((kA h).prod (kY h))).toReal) =ᵐ[nu] G := by
    filter_upwards [hlocal, hAmap, hYmap] with h hloc hha hhy
    let postAt : Kernel Y (Fin k) := post.comap (fun y ↦ (h, y))
      (measurable_const.prodMk measurable_id)
    have hrhs : (kY ⊗ₖ post) h = (kY h) ⊗ₘ postAt := by
      ext s hs
      rw [Kernel.compProd_apply hs, Measure.compProd_apply hs]
      rfl
    rw [Kernel.map_apply kAY measurable_swap h] at hloc
    rw [Kernel.map_apply kAY measurable_fst h] at hha
    rw [Kernel.map_apply kAY measurable_snd h] at hhy
    have hdecomp : (kAY h).map Prod.swap = (kY h) ⊗ₘ postAt := by
      exact hloc.trans hrhs
    have hp : (kAY h).map Prod.fst = kA h := hha.symm
    have hdecomp' : (kAY h).map Prod.swap =
        ((kAY h).map Prod.snd) ⊗ₘ postAt := by
      rw [← hhy]
      exact hdecomp
    have heq := mutualInformation_eq_categorical_kernel_average
      (kAY h) (kA h) postAt hp hdecomp'
    simpa [G, F, postAt, hhy] using heq
  have hgain_meas : AEMeasurable
      (fun h ↦ (klDiv (kAY h) ((kA h).prod (kY h))).toReal) nu :=
    hG.aemeasurable.congr hgainG.symm
  have hgain_bound : ∀ᵐ h ∂nu,
      ‖(klDiv (kAY h) ((kA h).prod (kY h))).toReal‖ ≤ k := by
    filter_upwards [hAmap, hYmap] with h hha hhy
    rw [Kernel.map_apply kAY measurable_fst h] at hha
    rw [Kernel.map_apply kAY measurable_snd h] at hhy
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have hmi := finite_range_mutualInformation_le_marginal_entropy
      (Omega := Fin k × Y) (Alpha := Y) (k := k)
      (mu := kAY h) (f := fun z : Fin k × Y ↦ z.2)
      (g := fun z : Fin k × Y ↦ z.1)
      (hf := (measurable_snd : Measurable (fun z : Fin k × Y ↦ z.2)))
      (hg := (measurable_fst : Measurable (fun z : Fin k × Y ↦ z.1)))
    have hswap := klDiv_map_measurableEmbedding
      (MeasurableEquiv.prodComm.measurableEmbedding :
        MeasurableEmbedding (Prod.swap : Fin k × Y → Y × Fin k))
      (kAY h) ((kA h).prod (kY h))
    change klDiv ((kAY h).map Prod.swap)
      (((kA h).prod (kY h)).map Prod.swap) =
        klDiv (kAY h) ((kA h).prod (kY h)) at hswap
    rw [Measure.prod_swap] at hswap
    rw [← hswap, hha, hhy]
    refine hmi.trans ?_
    calc
      ∑ a, Real.negMulLog (((kAY h).map Prod.fst).real {a}) ≤ ∑ _a : Fin k, 1 := by
        apply Finset.sum_le_sum
        intro a _
        have h0 : 0 ≤ ((kAY h).map Prod.fst).real {a} := measureReal_nonneg
        exact (Real.negMulLog_le_one_sub_self h0).trans (by linarith)
      _ = k := by simp
  have hint : Integrable
      (fun h ↦ (klDiv (kAY h) ((kA h).prod (kY h))).toReal) nu :=
    Integrable.of_bound hgain_meas.aestronglyMeasurable k hgain_bound
  simpa [nu, kAY, kA, kY] using hint

end InformationTheory
