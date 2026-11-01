-- Prove2me | solution 1 for GittinsUCB.Patient.standardization
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:04:29.191946+00:00
-- url     : https://prove2.me/submissions/4a8c6ecd-bccd-4eb8-af62-c4b4cd29c974

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
import Theorems.Thm_GittinsUCB_Patient_equation_5
import Theorems.Thm_GittinsUCB_Patient_lemma_4
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal
open GittinsUCB.Patient

namespace GittinsStdAux

/-- The affine change of location and scale on the sample space. -/
def Tf (a c : ℝ) (ω : Ω) : Ω := (a + c * ω.1, fun t => c * ω.2 t)

lemma measurable_Tf (a c : ℝ) : Measurable (Tf a c) :=
  (measurable_const.add (measurable_const.mul measurable_fst)).prodMk
    (measurable_pi_lambda _ fun t => measurable_const.mul ((measurable_pi_apply t).comp
      measurable_snd))

lemma Tf_Tf (a c : ℝ) (hc : c ≠ 0) (ω : Ω) : Tf (-a / c) (1 / c) (Tf a c ω) = ω := by
  unfold Tf
  ext
  · simp only; field_simp; ring
  · simp only; field_simp

lemma Tf_Tf' (a c : ℝ) (hc : c ≠ 0) (ω : Ω) : Tf a c (Tf (-a / c) (1 / c) ω) = ω := by
  unfold Tf
  ext
  · simp only; field_simp; ring
  · simp only; field_simp

noncomputable def TE (a c : ℝ) (hc : c ≠ 0) : Ω ≃ᵐ Ω where
  toFun := Tf a c
  invFun := Tf (-a / c) (1 / c)
  left_inv := Tf_Tf a c hc
  right_inv := Tf_Tf' a c hc
  measurable_toFun := measurable_Tf a c
  measurable_invFun := measurable_Tf _ _

lemma R_Tf (a c : ℝ) (s : ℕ) (ω : Ω) : R s (Tf a c ω) = a + c * R s ω := by
  simp [R, Tf]; ring

lemma measurable_Tf_reward (a c : ℝ) (t : ℕ) :
    Measurable[rewardSigma t, rewardSigma t] (Tf a c) := by
  unfold rewardSigma
  rw [measurable_iff_comap_le, MeasurableSpace.comap_comp]
  have e : (fun ω (s : Fin (t + 1)) => R s ω) ∘ Tf a c =
      (fun v : Fin (t + 1) → ℝ => fun s => a + c * v s) ∘ (fun ω (s : Fin (t + 1)) => R s ω) := by
    funext ω s; simp [R_Tf]
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (Measurable.comap_le (measurable_pi_lambda _
    (fun s => measurable_const.add (measurable_const.mul (measurable_pi_apply s)))))

lemma isRT_comp {τ : Ω → ℕ∞} (hτ : IsRetirementTime τ) (a c : ℝ) :
    IsRetirementTime (τ ∘ Tf a c) :=
  ⟨fun t => measurable_Tf_reward a c t (hτ.1 t), fun ω => hτ.2 _⟩

/-- Reindexing retirement times along the change of variables. -/
noncomputable def RTequiv (a c : ℝ) (hc : c ≠ 0) :
    {τ : Ω → ℕ∞ // IsRetirementTime τ} ≃ {τ : Ω → ℕ∞ // IsRetirementTime τ} where
  toFun τ := ⟨τ.1 ∘ Tf a c, isRT_comp τ.2 a c⟩
  invFun τ := ⟨τ.1 ∘ Tf (-a / c) (1 / c), isRT_comp τ.2 _ _⟩
  left_inv τ := by
    apply Subtype.ext; funext ω
    show τ.1 (Tf a c (Tf (-a / c) (1 / c) ω)) = τ.1 ω
    rw [Tf_Tf' a c hc]
  right_inv τ := by
    apply Subtype.ext; funext ω
    show τ.1 (Tf (-a / c) (1 / c) (Tf a c ω)) = τ.1 ω
    rw [Tf_Tf a c hc]

lemma model_map (μ : ℝ) (σ2 σW2 : ℝ≥0) (hσ : 0 < σ2) :
    (model 0 1 (σW2 / σ2)).map (Tf μ (Real.sqrt σ2)) = model μ σ2 σW2 := by
  set c := Real.sqrt (σ2 : ℝ) with hc
  have hc2 : c ^ 2 = σ2 := Real.sq_sqrt σ2.2
  have hσ' : (σ2 : ℝ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hT : Tf μ c = Prod.map (fun x => μ + c * x) (fun (w : ℕ → ℝ) (t : ℕ) => c * w t) := rfl
  unfold model
  rw [hT, ← Measure.map_prod_map (f := fun x => μ + c * x)
    (g := fun (w : ℕ → ℝ) (t : ℕ) => c * w t) _ _ (measurable_const.add (measurable_const_mul c))
    (measurable_pi_lambda _ fun t => (measurable_const_mul c).comp (measurable_pi_apply t))]
  congr 1
  · have e : (fun x => μ + c * x) = (fun x => μ + x) ∘ (fun x => c * x) := rfl
    rw [e, ← Measure.map_map (measurable_const_add μ) (measurable_const_mul c),
      gaussianReal_map_const_mul, gaussianReal_map_const_add]
    congr 1
    · simp
    · apply NNReal.eq; simp [hc2]
  · rw [Measure.infinitePi_map_pi _ (f := fun _ (x : ℝ) => c * x) (fun _ => measurable_const_mul c)]
    congr 1
    funext t
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply NNReal.eq
      simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_div, hc2]
      field_simp

lemma stoppedReward_Tf (γ lam μ c : ℝ) (hc : c ≠ 0) (τ : Ω → ℕ∞) (ω : Ω) :
    stoppedReward γ lam (fun _ => θ) τ (Tf μ c ω) =
      c * stoppedReward γ ((lam - μ) / c) (fun _ => θ) (τ ∘ Tf μ c) ω := by
  unfold stoppedReward
  rw [← _root_.tsum_mul_left]
  congr 1
  funext t
  by_cases h : (t : ℕ∞) ≤ τ (Tf μ c ω)
  · have h' : (t : ℕ∞) ≤ (τ ∘ Tf μ c) ω := h
    rw [if_pos h, if_pos h']
    simp only [θ, Tf]
    field_simp
    ring
  · have h' : ¬ (t : ℕ∞) ≤ (τ ∘ Tf μ c) ω := h
    rw [if_neg h, if_neg h', mul_zero]

end GittinsStdAux

open GittinsStdAux in
theorem solution (σW2 : ℝ≥0) (hW : 0 < σW2)
    (γ μ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (σ2 : ℝ≥0) (hσ : 0 < σ2) :
    gittinsIndex σW2 γ μ σ2 = μ + Real.sqrt (σ2 : ℝ) *
      gittinsIndex (σW2 / σ2) γ 0 1 := by
  set c := Real.sqrt (σ2 : ℝ) with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr (by exact_mod_cast hσ)
  set ρ : ℝ≥0 := σW2 / σ2 with hρ
  have hρ0 : 0 < ρ := div_pos hW hσ
  -- value scaling
  have hval : ∀ lam, value σW2 γ lam μ σ2 = c * value ρ γ ((lam - μ) / c) 0 1 := by
    intro lam
    unfold value
    rw [← model_map μ σ2 σW2 hσ, Real.mul_iSup_of_nonneg hc0.le]
    have h1 : ∀ τ : {τ : Ω → ℕ∞ // IsRetirementTime τ},
        ∫ ω, stoppedReward γ lam (fun _ => θ) τ.1 ω ∂((model 0 1 ρ).map (Tf μ c)) =
          c * ∫ ω, stoppedReward γ ((lam - μ) / c) (fun _ => θ) (RTequiv μ c hc0.ne' τ).1 ω
            ∂(model 0 1 ρ) := by
      intro τ
      rw [show Tf μ c = TE μ c hc0.ne' from rfl, (TE μ c hc0.ne').measurableEmbedding.integral_map,
        ← integral_const_mul]
      congr 1
      funext ω
      exact stoppedReward_Tf γ lam μ c hc0.ne' τ.1 ω
    rw [iSup_congr h1]
    exact (RTequiv μ c hc0.ne').iSup_comp
      (g := fun τ' => c * ∫ ω, stoppedReward γ ((lam - μ) / c) (fun _ => θ) τ'.1 ω
        ∂(model 0 1 ρ))
  -- the standardized admissible set
  set S' := {x : ℝ | 0 ≤ value ρ γ x 0 1} with hS'
  have hset : {lam : ℝ | 0 ≤ value σW2 γ lam μ σ2} = (fun x => μ + c * x) '' S' := by
    ext lam
    simp only [Set.mem_setOf_eq, Set.mem_image, hS']
    rw [hval]
    constructor
    · intro h
      refine ⟨(lam - μ) / c, ?_, ?_⟩
      · exact (mul_nonneg_iff_of_pos_left hc0).mp h
      · field_simp; ring
    · rintro ⟨x, hx, rfl⟩
      have : (μ + c * x - μ) / c = x := by field_simp; ring
      rw [this]
      exact mul_nonneg hc0.le hx
  -- `S'` is nonempty: the tax `0` is admissible (never retire)
  have hne : S'.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [hS', Set.mem_setOf_eq]
    unfold value
    set f := fun τ : {τ : Ω → ℕ∞ // IsRetirementTime τ} =>
      ∫ ω, stoppedReward γ 0 (fun _ => θ) τ.1 ω ∂(model 0 1 ρ) with hf
    by_cases hb : BddAbove (Set.range f)
    · let τtop : {τ : Ω → ℕ∞ // IsRetirementTime τ} :=
        ⟨fun _ => ⊤, fun t => by simp, fun ω => le_top⟩
      refine le_ciSup_of_le hb τtop (le_of_eq ?_)
      have hpt : ∀ ω, stoppedReward γ 0 (fun _ => θ) τtop.1 ω = θ ω * (1 - γ)⁻¹ := by
        intro ω
        unfold stoppedReward
        simp only [τtop, le_top, if_true, sub_zero]
        rw [_root_.tsum_mul_right, tsum_geometric_of_lt_one hγ0.le hγ1, mul_comm]
      have hθ0 : ∫ ω, θ ω ∂(model 0 1 ρ) = 0 := by
        unfold model θ
        exact (integral_fun_fst (μ := gaussianReal 0 1) (fun x : ℝ => x)).trans
          (by simp [integral_id_gaussianReal])
      simp only [hf]
      simp_rw [hpt]
      rw [integral_mul_const, hθ0, zero_mul]
    · rw [Real.iSup_of_not_bddAbove hb]
  -- `S'` is bounded above
  have hbdd : BddAbove S' := by
    refine ⟨max 2 (γ / (1 - γ)), fun x hx => ?_⟩
    simp only [hS', Set.mem_setOf_eq] at hx
    by_contra hlt
    rw [not_le, max_lt_iff] at hlt
    obtain ⟨h2, hg⟩ := hlt
    have h5 := equation_5 ρ hρ0 γ x hγ0 hγ1
    have hint : (∫ ω, max (θ ω - x) 0 ∂(model 0 1 ρ)) =
        ∫ y : ℝ, max (y - x) 0 ∂(gaussianReal 0 1) := by
      unfold model θ
      exact (integral_fun_fst (μ := gaussianReal 0 1) (fun y : ℝ => max (y - x) 0)).trans
        (by simp)
    have h4 := (lemma_4 1 x one_pos (by linarith)).2
    have e : (gaussianReal 0 ⟨(1:ℝ) ^ 2, sq_nonneg 1⟩ : Measure ℝ) = gaussianReal 0 1 := by
      congr 1; exact NNReal.eq (show ((1:ℝ)^2) = 1 by norm_num)
    rw [e, ← hint, div_one, one_mul] at h4
    have hφ : stdPdf x ≤ 1 := by
      unfold stdPdf
      have h1 : Real.exp (-x ^ 2 / 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      have h2 : 1 ≤ Real.sqrt (2 * Real.pi) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        have := Real.pi_gt_three; linarith
      rw [div_le_one (by linarith)]; linarith
    have hc' : 0 ≤ γ / (1 - γ) := div_nonneg hγ0.le (by linarith)
    have := mul_le_mul_of_nonneg_left (h4.trans hφ) hc'
    linarith
  -- conclude
  unfold gittinsIndex
  rw [hset, ← Monotone.map_csSup_of_continuousAt (by fun_prop)
    (fun x y hxy => by nlinarith) hne hbdd]
