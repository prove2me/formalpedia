-- Prove2me | solution 1 for InfoRelax.RelaxOrder.proposition_2_3_i
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T05:58:35.306026+00:00
-- url     : https://prove2.me/submissions/c9208c22-8e9a-470d-82bc-6cc3d963ade0

import Mathlib
import Definitions.Def_InfoRelax_RelaxOrder_Framework
import Definitions.Def_InfoRelax_RelaxOrder_RecursiveModel
import Definitions.Def_InfoRelax_RelaxOrder_Penalty

set_option autoImplicit false

open MeasureTheory

/-- Integrability of `ω ↦ F (β ω) ω` for a countable-valued measurable `β` and uniformly
a.e.-bounded, a.e.-strongly measurable `F y`. -/
lemma p7_integrable_comp {Ω Y : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Y] [Countable Y]
    [MeasurableSingletonClass Y] (μ : Measure Ω) [IsFiniteMeasure μ] (β : Ω → Y)
    (hβ : Measurable β) (F : Y → Ω → ℝ) (hF : ∀ y, AEStronglyMeasurable (F y) μ) (C : ℝ)
    (hC : ∀ y, ∀ᵐ ω ∂μ, |F y ω| ≤ C) : Integrable (fun ω => F (β ω) ω) μ := by
  let g : Y → Ω → ℝ := fun y => (hF y).mk (F y)
  have hg : ∀ y, StronglyMeasurable (g y) := fun y => (hF y).stronglyMeasurable_mk
  have hfg : ∀ᵐ ω ∂μ, ∀ y, F y ω = g y ω := ae_all_iff.2 fun y => (hF y).ae_eq_mk
  have hmeas : Measurable (fun p : Y × Ω => g p.1 p.2) :=
    measurable_from_prod_countable_right (fun y => (hg y).measurable)
  have hcomp : Measurable (fun ω => g (β ω) ω) :=
    hmeas.comp (hβ.prodMk measurable_id)
  have hae : (fun ω => F (β ω) ω) =ᵐ[μ] (fun ω => g (β ω) ω) := hfg.mono fun ω h => h _
  refine Integrable.of_bound ((hcomp.aestronglyMeasurable).congr hae.symm) C ?_
  filter_upwards [ae_all_iff.2 hC] with ω h
  simpa [Real.norm_eq_abs] using h (β ω)

/-- The key identity: for an `m`-measurable countable-valued `β`,
`∫ μ[f (β ω) | m](ω) = ∫ f (β ω)(ω)`. -/
lemma p7_integral_condExp_comp {Ω Y : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace Y] [Countable Y] [MeasurableSingletonClass Y] (μ : Measure Ω)
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) (β : Ω → Y) (hβ : Measurable[m] β)
    (f : Y → Ω → ℝ) (hf : ∀ y, AEStronglyMeasurable (f y) μ) (C : ℝ)
    (hC : ∀ y, ∀ᵐ ω ∂μ, |f y ω| ≤ C) :
    ∫ ω, μ[f (β ω) | m] ω ∂μ = ∫ ω, f (β ω) ω ∂μ := by
  have hβ' : Measurable β := hβ.mono hm le_rfl
  have hfi : ∀ y, Integrable (f y) μ := fun y =>
    Integrable.of_bound (hf y) C ((hC y).mono fun ω h => by simpa [Real.norm_eq_abs] using h)
  have hG : Integrable (fun ω => μ[f (β ω) | m] ω) μ :=
    p7_integrable_comp μ β hβ' (fun y => μ[f y | m])
      (fun y => (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable) C
      (fun y => ae_bdd_abs_condExp_of_ae_bdd_abs (hC y))
  have hH : Integrable (fun ω => f (β ω) ω) μ := p7_integrable_comp μ β hβ' f hf C hC
  let s : Y → Set Ω := fun y => β ⁻¹' {y}
  have hsm : ∀ y, MeasurableSet[m] (s y) := fun y => hβ (measurableSet_singleton y)
  have hs : ∀ y, MeasurableSet (s y) := fun y => hm _ (hsm y)
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro y y' hyy'
    exact Set.disjoint_left.2 fun ω h1 h2 => hyy' (h1.symm.trans h2)
  have hU : (⋃ y, s y) = Set.univ := by
    ext ω; simp [s]
  have e1 : ∫ ω, μ[f (β ω) | m] ω ∂μ = ∑' y, ∫ ω in s y, μ[f (β ω) | m] ω ∂μ := by
    rw [← integral_iUnion hs hd (by rw [hU]; exact hG.integrableOn), hU, setIntegral_univ]
  have e2 : ∫ ω, f (β ω) ω ∂μ = ∑' y, ∫ ω in s y, f (β ω) ω ∂μ := by
    rw [← integral_iUnion hs hd (by rw [hU]; exact hH.integrableOn), hU, setIntegral_univ]
  rw [e1, e2]
  congr 1
  funext y
  have h1 : ∫ ω in s y, μ[f (β ω) | m] ω ∂μ = ∫ ω in s y, μ[f y | m] ω ∂μ := by
    refine setIntegral_congr_fun (hs y) fun ω hω => ?_
    simp only [s, Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp only [hω]
  have h2 : ∫ ω in s y, f (β ω) ω ∂μ = ∫ ω in s y, f y ω ∂μ := by
    refine setIntegral_congr_fun (hs y) fun ω hω => ?_
    simp only [s, Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp only [hω]
  rw [h1, h2]
  exact setIntegral_condExp hm (hfi y) (hsm y)

open MeasureTheory InfoRelax.RelaxOrder in
theorem solution {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Countable X] {T : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T) (hM : M.Valid)
    (𝔾₁ 𝔾₂ : Filtration (Fin (T + 1)) mΩ) (h₁ : InfoRelax.IdealPenalty.IsRelaxation M.𝔽 𝔾₁)
    (h₁₂ : InfoRelax.IdealPenalty.IsRelaxation 𝔾₁ 𝔾₂)
    (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (hw : GeneratingFns μ w) :
    InfoRelax.IdealPenalty.dualBound μ M.A 𝔾₁ M.r (penalty μ M.𝔽 𝔾₁ w) ≤
      InfoRelax.IdealPenalty.dualBound μ M.A 𝔾₂ M.r (penalty μ M.𝔽 𝔾₂ w) := by
  obtain ⟨-, -, -, hrm, -, ⟨Cr, hCr⟩⟩ := hM
  obtain ⟨hwdep, hwm, ⟨Cw, hCw⟩⟩ := hw
  -- the integral formula for a `𝔾`-adapted policy
  have key : ∀ (𝔾 : Filtration (Fin (T + 1)) mΩ) (α : Ω → Fin (T + 1) → X),
      (∀ t, Measurable[𝔾 t] (fun ω => α ω t)) →
      ∫ ω, (M.r (α ω) ω - penalty μ M.𝔽 𝔾 w (α ω) ω) ∂μ =
        ∫ ω, M.r (α ω) ω ∂μ -
          ∑ t, (∫ ω, w t (α ω) ω ∂μ - ∫ ω, μ[w t (α ω) | M.𝔽 t] ω ∂μ) := by
    intro 𝔾 α hα
    have hαm : Measurable α :=
      measurable_pi_lambda _ fun t => (hα t).mono (𝔾.le t) le_rfl
    have hr : Integrable (fun ω => M.r (α ω) ω) μ := by
      refine p7_integrable_comp μ α hαm (fun a ω => M.r a ω) (fun a => ?_) (∑ _t : Fin (T + 1), Cr)
        (fun a => Filter.Eventually.of_forall fun ω => ?_)
      · exact (Finset.measurable_sum _ fun t _ =>
          (hrm t a).mono (M.𝔽.le t) le_rfl).aestronglyMeasurable
      · simp only [InfoRelax.RelaxOrder.RecursiveDP.r]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => hCr t a ω)
    have hceG : ∀ t, Integrable (fun ω => μ[w t (α ω) | 𝔾 t] ω) μ := fun t =>
      p7_integrable_comp μ α hαm (fun a => μ[w t a | 𝔾 t])
        (fun a => (stronglyMeasurable_condExp.mono (𝔾.le t)).aestronglyMeasurable) Cw
        (fun a => ae_bdd_abs_condExp_of_ae_bdd_abs (hCw t a))
    have hceF : ∀ t, Integrable (fun ω => μ[w t (α ω) | M.𝔽 t] ω) μ := fun t =>
      p7_integrable_comp μ α hαm (fun a => μ[w t a | M.𝔽 t])
        (fun a => (stronglyMeasurable_condExp.mono (M.𝔽.le t)).aestronglyMeasurable) Cw
        (fun a => ae_bdd_abs_condExp_of_ae_bdd_abs (hCw t a))
    have hdiff : ∀ t, Integrable
        (fun ω => μ[w t (α ω) | 𝔾 t] ω - μ[w t (α ω) | M.𝔽 t] ω) μ := fun t =>
      (hceG t).sub (hceF t)
    have hsum : Integrable
        (fun ω => ∑ t, (μ[w t (α ω) | 𝔾 t] ω - μ[w t (α ω) | M.𝔽 t] ω)) μ :=
      integrable_finsetSum _ fun t _ => hdiff t
    have hwi : ∀ t, Integrable (fun ω => w t (α ω) ω) μ := fun t =>
      p7_integrable_comp μ α hαm (w t) (hwm t) Cw (hCw t)
    have hpen : ∀ ω, penalty μ M.𝔽 𝔾 w (α ω) ω =
        ∑ t, (μ[w t (α ω) | 𝔾 t] ω - μ[w t (α ω) | M.𝔽 t] ω) := fun ω => by
      simp [penalty, penaltyComp]
    simp_rw [hpen]
    rw [integral_sub hr hsum, integral_finsetSum _ fun t _ => hdiff t]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [integral_sub (hceG t) (hceF t)]
    congr 1
    -- truncate the policy at time `t`
    let β : Ω → Fin (T + 1) → X := fun ω s => α ω (min s t)
    have hβ : Measurable[𝔾 t] β :=
      @measurable_pi_lambda Ω (Fin (T + 1)) (fun _ => X) (𝔾 t) _ β
        fun s => (hα (min s t)).mono (𝔾.mono (min_le_right s t)) le_rfl
    have hwβ : ∀ ω, w t (α ω) = w t (β ω) := fun ω =>
      hwdep t _ _ fun s hs => by simp [β, min_eq_left hs]
    have e1 : (fun ω => μ[w t (α ω) | 𝔾 t] ω) = fun ω => μ[w t (β ω) | 𝔾 t] ω := by
      funext ω; rw [hwβ ω]
    have e2 : (fun ω => w t (α ω) ω) = fun ω => w t (β ω) ω := by
      funext ω; rw [hwβ ω]
    rw [e1, e2]
    exact p7_integral_condExp_comp (m := 𝔾 t) μ (𝔾.le t) β hβ (w t) (hwm t) Cw (hCw t)
  unfold InfoRelax.IdealPenalty.dualBound InfoRelax.IdealPenalty.supValue
  refine iSup₂_le fun α hα => ?_
  have hα2 : α ∈ InfoRelax.IdealPenalty.adaptedPolicies M.A 𝔾₂ :=
    ⟨hα.1, fun t => (hα.2 t).mono (h₁₂ t) le_rfl⟩
  refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun α (_ : α ∈
    InfoRelax.IdealPenalty.adaptedPolicies M.A 𝔾₂) =>
      ((∫ ω, (M.r (α ω) ω - penalty μ M.𝔽 𝔾₂ w (α ω) ω) ∂μ : ℝ) : EReal)) α hα2)
  congr 1
  rw [key 𝔾₁ α hα.2, key 𝔾₂ α hα2.2]
