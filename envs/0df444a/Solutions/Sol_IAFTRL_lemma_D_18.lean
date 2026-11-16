-- Prove2me | solution 1 for IAFTRL.lemma_D_18
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T07:06:48.765053+00:00
-- url     : https://prove2.me/submissions/ef0a39f3-9cae-42dd-9f54-6a7009632e30

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_Run_mixGap
import Definitions.Def_IAFTRL_proxyC
import Definitions.Def_IAFTRL_regretDist
import Theorems.Thm_IAFTRL_lemma_D_4
import Theorems.Thm_IAFTRL_lemma_D_15

open Matrix Finset MeasureTheory IAFTRL
set_option maxHeartbeats 2000000
set_option autoImplicit false
namespace D18Entropy

private noncomputable def Z {K : ℕ} (b : ℝ) (S : Fin K → ℝ) : ℝ :=
  ∑ a, Real.exp (-S a / b)
private noncomputable def Q {K : ℕ} (b : ℝ) (S : Fin K → ℝ) (a : Fin K) : ℝ :=
  Real.exp (-S a / b) / Z b S
private noncomputable def F {K : ℕ} (b : ℝ) (S : Fin K → ℝ) : ℝ :=
  -b * Real.log (Z b S)
private noncomputable def H {K : ℕ} (p : Fin K → ℝ) : ℝ :=
  -∑ a, p a * Real.log (p a)

private lemma Z_pos {K : ℕ} [Nonempty (Fin K)] (b : ℝ) (S : Fin K → ℝ) : 0 < Z b S :=
  sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty

private lemma Q_pos {K : ℕ} [Nonempty (Fin K)] (b : ℝ) (S : Fin K → ℝ) (a : Fin K) :
    0 < Q b S a := div_pos (Real.exp_pos _) (Z_pos b S)

private lemma Q_sum {K : ℕ} [Nonempty (Fin K)] (b : ℝ) (S : Fin K → ℝ) :
    ∑ a, Q b S a = 1 := by
  simp only [Q, ← sum_div]
  exact div_self (Z_pos b S).ne'

private lemma log_Q {K : ℕ} [Nonempty (Fin K)] (b : ℝ) (S : Fin K → ℝ) (a : Fin K) :
    Real.log (Q b S a) = -S a / b - Real.log (Z b S) := by
  rw [Q, Real.log_div (Real.exp_pos _).ne' (Z_pos b S).ne', Real.log_exp]

private lemma F_identity {K : ℕ} [Nonempty (Fin K)] (b : ℝ) (hb : 0 < b)
    (S : Fin K → ℝ) : F b S = ∑ a, Q b S a * S a - b * H (Q b S) := by
  have he (a : Fin K) : b * (Q b S a * Real.log (Q b S a)) =
      -Q b S a * S a - b * Q b S a * Real.log (Z b S) := by
    rw [log_Q]; field_simp
  have hs := congrArg (fun f : Fin K → ℝ => ∑ a, f a) (funext he)
  simp only [neg_mul, sum_sub_distrib, sum_neg_distrib, ← mul_sum, ← sum_mul, Q_sum] at hs
  unfold F H
  linarith

private lemma F_le_entropy {K : ℕ} [Nonempty (Fin K)] (b : ℝ) (hb : 0 < b)
    (S p : Fin K → ℝ) (hp : ∀ a, 0 < p a) (hp1 : ∑ a, p a = 1) :
    F b S ≤ ∑ a, p a * S a - b * H p := by
  have hpoint (a : Fin K) : p a * (Real.log (Q b S a) - Real.log (p a)) ≤ Q b S a - p a := by
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (Q_pos b S a) (hp a))) (hp a).le
    rw [Real.log_div (Q_pos b S a).ne' (hp a).ne'] at h
    calc
      _ ≤ p a * (Q b S a / p a - 1) := h
      _ = _ := by field_simp [(hp a).ne']
  have hs := sum_le_sum (s := univ) (fun a _ => hpoint a)
  have he (a : Fin K) : b * (p a * (Real.log (Q b S a) - Real.log (p a))) =
      -p a * S a - p a * (b * Real.log (Z b S)) - b * (p a * Real.log (p a)) := by
    rw [log_Q]; field_simp
  have he' := congrArg (fun f : Fin K → ℝ => ∑ a, f a) (funext he)
  simp only [neg_mul, sum_sub_distrib, sum_neg_distrib, ← sum_mul, ← mul_sum, hp1] at he'
  simp only [sum_sub_distrib, Q_sum, hp1, sub_self] at hs
  have hmul := mul_nonpos_of_nonneg_of_nonpos hb.le hs
  unfold F H
  linarith

private lemma F_change {K : ℕ} [Nonempty (Fin K)] (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (S : Fin K → ℝ) : F b S - F c S ≤ (c-b) * H (Q c S) := by
  have h := F_le_entropy b hb S (Q c S) (Q_pos c S) (Q_sum c S)
  rw [F_identity c hc S]
  linarith

private lemma F_terminal {K : ℕ} [Nonempty (Fin K)] (b : ℝ) (hb : 0 < b)
    (S u : Fin K → ℝ) (hu0 : ∀ a, 0 ≤ u a) (hu1 : ∑ a, u a = 1) :
    F b S ≤ ∑ a, u a * S a := by
  have h (a : Fin K) : F b S ≤ S a := by
    have hz : Real.exp (-S a/b) ≤ Z b S := by
      unfold Z
      exact single_le_sum (fun j _ => (Real.exp_pos (-S j/b)).le) (mem_univ a)
    have hl := Real.log_le_log (Real.exp_pos _) hz
    rw [Real.log_exp] at hl
    have hm := mul_le_mul_of_nonneg_left hl hb.le
    have he : b * (-S a / b) = -S a := by field_simp
    rw [he] at hm
    unfold F; linarith
  have hs := sum_le_sum (s := univ) (fun a _ => mul_le_mul_of_nonneg_left (h a) (hu0 a))
  simpa only [← sum_mul, hu1, one_mul] using hs

private lemma F_zero {K : ℕ} (b : ℝ) : F b (fun _ : Fin K => 0) = -b * Real.log K := by
  simp [F, Z]

private lemma step {K : ℕ} [Nonempty (Fin K)] (b : ℝ) (hb : 0 < b)
    (S V u : Fin K → ℝ) (hu1 : ∑ a, u a = 1) (c : ℝ) :
    let g := fun a => V a - S a - c
    let D := ∑ a, Q b S a * g a + b * Real.log (∑ a, Q b S a * Real.exp (-g a/b))
    ∑ a, (Q b S a-u a) * g a - D =
      (F b V - ∑ a, u a * V a) - (F b S - ∑ a, u a * S a) := by
  dsimp only
  have he (a : Fin K) : Q b S a * Real.exp (-(V a-S a-c)/b) =
      Real.exp (c/b) * Real.exp (-V a/b) / Z b S := by
    unfold Q
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    congr 1
    rw [← Real.exp_add]
    congr 1; ring
  have hsum : (∑ a, Q b S a * Real.exp (-(V a-S a-c)/b)) =
      Real.exp (c/b) * Z b V / Z b S := by
    simp_rw [he]; rw [← sum_div, ← mul_sum]; rfl
  rw [hsum, Real.log_div (mul_pos (Real.exp_pos _) (Z_pos b V)).ne' (Z_pos b S).ne',
    Real.log_mul (Real.exp_pos _).ne' (Z_pos b V).ne', Real.log_exp]
  simp only [sub_mul, mul_sub, sum_sub_distrib, ← sum_mul, hu1, one_mul]
  unfold F
  field_simp
  ring

lemma telescoping {K : ℕ} [Nonempty (Fin K)]
    (b : ℕ → ℝ) (hb : ∀ t, 0 < b t) (S : ℕ → Fin K → ℝ) (hS : S 0 = 0)
    (u : Fin K → ℝ) (hu0 : ∀ a, 0 ≤ u a) (hu1 : ∑ a, u a = 1)
    (c : ℕ → ℝ) (T : ℕ) :
    let g := fun t a => S (t+1) a - S t a - c t
    let D := fun t => ∑ a, Q (b t) (S t) a * g t a + b t *
      Real.log (∑ a, Q (b t) (S t) a * Real.exp (-g t a/b t))
    (∑ t ∈ range T, ∑ a, (Q (b t) (S t) a-u a) * g t a) ≤
      b 0 * Real.log K + (∑ t ∈ Ico 1 T, (b t-b (t-1)) * H (Q (b t) (S t))) +
        ∑ t ∈ range T, D t := by
  dsimp only
  let A (t : ℕ) := F (b t) (S (t+1)) - ∑ a, u a * S (t+1) a
  let B (t : ℕ) := F (b t) (S t) - ∑ a, u a * S t a
  let C (t : ℕ) := (b t-b (t-1)) * H (Q (b t) (S t))
  have hsum : ∀ n, 1 ≤ n → (∑ t ∈ range n, (A t - B t)) ≤
      A (n-1) - B 0 + ∑ t ∈ Ico 1 n, C t := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hn0 : n = 0
      · subst n; simp
      · have hn1 : 1 ≤ n := by omega
        have hi := ih hn1
        have hc : A (n-1) - B n ≤ C n := by
          dsimp [A,B,C]
          rw [Nat.sub_add_cancel hn1]
          linarith [F_change (b (n-1)) (b n) (hb _) (hb _) (S n)]
        rw [sum_range_succ, sum_Ico_succ_top hn1]
        simp only [Nat.add_sub_cancel]
        linarith
  have hB : B 0 = -b 0 * Real.log K := by
    dsimp [B]; rw [hS]; simp [F,Z]
  by_cases hT : T = 0
  · subst T
    simp only [range_zero, sum_empty, Ico_eq_empty_of_le (by omega : 0 ≤ 1), add_zero]
    exact mul_nonneg (hb 0).le (Real.log_nonneg (by
      have : 0 < K := by simpa using Fintype.card_pos (α := Fin K)
      exact_mod_cast this))
  · have ht : 1 ≤ T := by omega
    have hs := hsum T ht
    have ha : A (T-1) ≤ 0 := sub_nonpos.mpr (F_terminal _ (hb _) _ u hu0 hu1)
    rw [hB] at hs
    have he : (∑ t ∈ range T, ∑ a, (Q (b t) (S t) a-u a) * (S (t+1) a-S t a-c t)) -
        (∑ t ∈ range T, (∑ a, Q (b t) (S t) a * (S (t+1) a-S t a-c t) + b t *
          Real.log (∑ a, Q (b t) (S t) a * Real.exp (-(S (t+1) a-S t a-c t)/b t)))) =
        ∑ t ∈ range T, (A t-B t) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun t _ => step (b t) (hb t) (S t) (S (t+1)) u hu1 (c t)
    dsimp only [C] at hs
    linarith

end D18Entropy

namespace D18Proof
local instance {d : ℕ} : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

local instance {d : ℕ} : BorelSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))

private lemma q_prob {d K : ℕ} [Nonempty (Fin K)] (β : ℝ)
    (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) :
    (∀ a, 0 ≤ qSoft β arms S a) ∧ ∑ a, qSoft β arms S a = 1 := by
  have hp : 0 < ∑ a, Real.exp (-(arms a ⬝ᵥ S) / β) :=
    sum_pos (fun a _ => Real.exp_pos _) univ_nonempty
  constructor
  · intro a; exact div_nonneg (Real.exp_pos _).le hp.le
  · simp only [qSoft]
    rw [← sum_div, div_self (ne_of_gt hp)]


private lemma matrix_inv_measurable {d : ℕ} :
    Measurable (fun M : Matrix (Fin d) (Fin d) ℝ => M⁻¹) := by
  change Measurable (fun M : Matrix (Fin d) (Fin d) ℝ => Ring.inverse M.det • M.adjugate)
  simp only [Ring.inverse_eq_inv']
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable


private lemma v_measurable {d K : ℕ} (arms : Fin K → Fin d → ℝ) (b : Fin K) :
    Measurable (fun p : Fin K → ℝ => vCoef arms p b) := by
  have hcov : Measurable (fun p : Fin K → ℝ => BanditAlgorithm.linearAllocationMatrix arms p) := by
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    simp only [BanditAlgorithm.linearAllocationMatrix, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
    exact Finset.measurable_sum _ fun a _ => (measurable_pi_apply a).mul_const _
  have hi := matrix_inv_measurable.comp hcov
  unfold vCoef
  refine measurable_pi_iff.mpr fun i => ?_
  change Measurable (fun p : Fin K → ℝ =>
    ∑ j, (BanditAlgorithm.linearAllocationMatrix arms p)⁻¹ i j * arms b j)
  exact Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).comp
    ((measurable_pi_apply i).comp hi)).mul_const _


private lemma q_measurable {d K : ℕ} (arms : Fin K → Fin d → ℝ) (β : ℝ) (a : Fin K) :
    Measurable (fun S : Fin d → ℝ => qSoft β arms S a) := by
  have h (b : Fin K) : Measurable (fun S : Fin d → ℝ => Real.exp (-(arms b ⬝ᵥ S)/β)) :=
    ((Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _).neg.div_const β).exp
  exact (h a).div (Finset.measurable_sum _ fun b _ => h b)


private lemma selected_measurable {K : ℕ} {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (f : Fin K → Ω → E) (hf : ∀ b, Measurable (f b))
    (A : Ω → Fin K) (hA : Measurable A) : Measurable (fun ω => f (A ω) ω) :=
  (measurable_from_prod_countable_left (f := fun x : Ω × Fin K => f x.2 x.1) hf).comp
    (measurable_id.prodMk hA)


private lemma hist_mono {d K : ℕ} {Ω : Type*} (R : Run d K Ω)
    {s t : ℕ} (hst : s ≤ t) : R.hist s ≤ R.hist t := by
  unfold Run.hist
  exact iSup_le fun n => iSup_le fun hn =>
    le_iSup_of_le n (le_iSup_of_le (lt_of_lt_of_le hn hst) le_rfl)


private lemma cum_measurable {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (arms : Fin K → Fin d → ℝ) (T : ℕ)
    (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R)
    (t : ℕ) (ht : t ≤ T) : Measurable[R.hist t] (R.cumEst arms t) := by
  apply Finset.measurable_sum
  intro s hs
  have hs' : s < t := mem_range.mp hs
  have hpair : Measurable[R.hist t] (fun ω => (R.A s ω, R.Y s ω)) := by
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le s (le_iSup_of_le hs' le_rfl)
  have hp : Measurable[R.hist t] (R.p s) :=
    (hR s (lt_of_lt_of_le hs' ht)).2.1.1.mono (hist_mono R hs'.le) le_rfl
  have hv := @selected_measurable K Ω (Fin d → ℝ) (R.hist t) inferInstance
    (fun b ω => vCoef arms (R.p s ω) b)
    (fun b => (v_measurable arms b).comp hp) (R.A s) (measurable_fst.comp hpair)
  exact (measurable_snd.comp hpair).smul hv


private lemma beta_pos {d K t : ℕ} (hd : 1 ≤ d) : 0 < beta d K t := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
  unfold beta
  positivity


private lemma finite_condExp {K : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (A : Ω → Fin K) (hA : Measurable[mΩ] A) (p : Ω → Fin K → ℝ)
    (hlaw : ∀ b, P[(A ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) | m] =ᵐ[P] fun ω => p ω b)
    (f : Fin K → Ω → ℝ) (hf : ∀ b, Measurable[m] (f b))
    (C : ℝ) (hbound : ∀ b ω, |f b ω| ≤ C) :
    Integrable (fun ω => f (A ω) ω) P ∧
      P[fun ω => f (A ω) ω | m] =ᵐ[P] fun ω => ∑ b, p ω b * f b ω := by
  classical
  have hfi (b : Fin K) : Integrable (f b) P :=
    Integrable.of_bound ((hf b).mono hm le_rfl).aestronglyMeasurable C
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hbound b ω)
  let I (b : Fin K) : Ω → ℝ := (A ⁻¹' {b}).indicator (fun _ => (1 : ℝ))
  have hIi (b : Fin K) : Integrable (I b) P :=
    (integrable_const (1 : ℝ)).indicator (hA (measurableSet_singleton b))
  have hprod (b : Fin K) : Integrable (f b * I b) P := by
    have he : f b * I b = (A ⁻¹' {b}).indicator (f b) := by
      funext ω
      by_cases hw : A ω = b <;> simp [I, hw]
    rw [he]
    exact (hfi b).indicator (hA (measurableSet_singleton b))
  have he : (fun ω => f (A ω) ω) = ∑ b, f b * I b := by
    funext ω
    simp [I, Set.indicator, Pi.mul_apply, eq_comm]
  have hce (b : Fin K) : P[f b * I b | m] =ᵐ[P] fun ω => p ω b * f b ω := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (hf b).stronglyMeasurable
      (hprod b) (hIi b), hlaw b] with ω hω hl
    change P[I b | m] ω = p ω b at hl
    simpa only [Pi.mul_apply, hl, mul_comm] using hω
  constructor
  · rw [he]
    have hs : (∑ b, f b * I b) = fun ω => ∑ b, (f b * I b) ω := by
      funext ω
      simp only [Finset.sum_apply]
    rw [hs]
    exact integrable_finsetSum univ (fun b _ => hprod b)
  · rw [he]
    apply (condExp_finsetSum (fun b _ => hprod b) m).trans
    filter_upwards [ae_all_iff.mpr hce] with ω hω
    simp only [Finset.sum_apply]
    exact sum_congr rfl fun b _ => hω b


private lemma norm_bound {d K : ℕ} (arms : Fin K → Fin d → ℝ)
    (z : Fin d → ℝ) (a : Fin K) : |arms a ⬝ᵥ z| ≤ actionNorm arms z := by
  unfold actionNorm
  exact le_ciSup (f := fun j : Fin K => |arms j ⬝ᵥ z|) (Set.finite_range _).bddAbove a


private lemma prob_le_one {K : ℕ} (p : Fin K → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (a : Fin K) : p a ≤ 1 := by
  simpa only [hp1] using single_le_sum (fun b _ => hp0 b) (mem_univ a)

private lemma bounded_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) (C : ℝ)
    (hb : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb ω)

private lemma mul_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Integrable g P) (C : ℝ)
    (hb : ∀ ω, |f ω| ≤ C) : Integrable (fun ω => f ω*g ω) P :=
  hg.bdd_mul hf.aestronglyMeasurable (ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs] using hb ω)

private lemma round_identity {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hA : IsActionSet arms) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ) (R : Run d K Ω)
    (hR : IsIAFTRLRun P arms T R) (θ : Fin d → ℝ) (j : Fin K)
    (u : Fin K → ℝ) (hu1 : ∑ a, u a = 1) (t : ℕ) (ht : t < T) :
    let q := fun ω => qSoft (beta d K (t+1)) arms (R.cumEst arms t ω)
    let r := fun ω => (arms (R.A t ω)-∑ a, u a • arms a) ⬝ᵥ R.θs t ω
    let f := fun ω => ∑ a, (q ω a-u a)*R.gEst arms t a ω
    let e := fun ω => ∑ a, (R.p t ω a-q ω a)*((arms a-arms j) ⬝ᵥ θ)
    let c := fun ω => ∑ a, (R.p t ω a-q ω a)*(arms a ⬝ᵥ (R.θs t ω-θ))
    Integrable r P ∧ Integrable f P ∧ Integrable e P ∧ Integrable c P ∧
      (∫ ω, r ω ∂P) = (∫ ω, f ω ∂P)+(∫ ω, e ω ∂P)+(∫ ω, c ω ∂P) := by
  classical
  let : Nonempty (Fin K) := ⟨j⟩
  dsimp only
  let q := fun ω => qSoft (beta d K (t+1)) arms (R.cumEst arms t ω)
  let μ := fun a ω => arms a ⬝ᵥ R.θs t ω
  let w := fun a ω => q ω a-u a
  let v := fun a ω => R.p t ω a-q ω a
  have hr := hR t ht
  have hm : R.G t ≤ mΩ := hr.1.2.2.2.1
  have hp : Measurable[R.G t] (R.p t) := hr.2.1.1.mono hr.1.2.2.2.2.1 le_rfl
  have hc := (cum_measurable P arms T R hR t ht.le).mono hr.1.2.2.2.2.1 le_rfl
  have hq (a) : Measurable[R.G t] (fun ω => q ω a) := (q_measurable arms _ a).comp hc
  have hw (a) : Measurable[R.G t] (w a) := (hq a).sub_const _
  have hv (a) : Measurable[mΩ] (v a) :=
    (((measurable_pi_apply a).comp hp).sub (hq a)).mono hm le_rfl
  have hμ (a) : Measurable[R.G t] (μ a) := Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hr.1.2.2.2.2.2.1).const_mul _
  have hμb (a) (ω) : |μ a ω| ≤ 1 := (norm_bound arms _ a).trans (hr.2.2.2.2 ω)
  have hμi (a) : Integrable (μ a) P := bounded_integrable P ((hμ a).mono hm le_rfl) 1 (hμb a)
  have hq0 (ω) : ∀ a, 0 ≤ q ω a := (q_prob _ arms _).1
  have hq1 (ω) : ∑ a, q ω a = 1 := (q_prob _ arms _).2
  have hp0 (ω) : ∀ a, 0 ≤ R.p t ω a := (hr.2.1.2 ω).1.1
  have hp1 (ω) : ∑ a, R.p t ω a = 1 := (hr.2.1.2 ω).1.2.1
  have hqb (a) (ω) : |q ω a| ≤ 1 := by
    rw [abs_of_nonneg (hq0 ω a)]; exact prob_le_one _ (hq0 ω) (hq1 ω) a
  have hpb (a) (ω) : |R.p t ω a| ≤ 1 := by
    rw [abs_of_nonneg (hp0 ω a)]; exact prob_le_one _ (hp0 ω) (hp1 ω) a
  have hwb (a) (ω) : |w a ω| ≤ 1+|u a| :=
    (abs_sub _ _).trans (by linarith [hqb a ω])
  have hvb (a) (ω) : |v a ω| ≤ 2 := (abs_sub _ _).trans (by linarith [hpb a ω,hqb a ω])
  have hgi (a) := (IAFTRL.lemma_D_15 hd arms hA P T R hR t ht a j).1
  have hwgi (a) : Integrable (fun ω => w a ω*R.gEst arms t a ω) P :=
    mul_integrable P ((hw a).mono hm le_rfl) (hgi a) _ (hwb a)
  have hwi (a) : Integrable (fun ω => w a ω*(R.gEst arms t a ω-R.gEst arms t j ω)) P :=
    mul_integrable P ((hw a).mono hm le_rfl) ((hgi a).sub (hgi j)) _ (hwb a)
  have hwμi (a) : Integrable (fun ω => w a ω*(μ a ω-μ j ω)) P :=
    mul_integrable P ((hw a).mono hm le_rfl) ((hμi a).sub (hμi j)) _ (hwb a)
  have heq (a) : (∫ ω, w a ω*(R.gEst arms t a ω-R.gEst arms t j ω) ∂P) =
      ∫ ω, w a ω*(μ a ω-μ j ω) ∂P := by
    have hce := condExp_mul_of_stronglyMeasurable_left (hw a).stronglyMeasurable (hwi a)
      ((hgi a).sub (hgi j))
    have hdiff := (IAFTRL.lemma_D_15 hd arms hA P T R hR t ht a j).2.2.2.1
    rw [← integral_condExp hm]
    apply integral_congr_ae
    filter_upwards [hce,hdiff] with ω hω hδ
    change P[fun ω => w a ω*(R.gEst arms t a ω-R.gEst arms t j ω) | R.G t] ω =
      w a ω*P[fun ω => R.gEst arms t a ω-R.gEst arms t j ω | R.G t] ω at hω
    rw [hδ] at hω
    simpa only [μ,sub_dotProduct] using hω
  have hsweight (ω) : ∑ a, w a ω = 0 := by simp [w,sum_sub_distrib,hq1 ω,hu1]
  have hcore (ω) : (∑ a, w a ω*R.gEst arms t a ω) =
      ∑ a, w a ω*(R.gEst arms t a ω-R.gEst arms t j ω) := by
    simp only [mul_sub,sum_sub_distrib,← sum_mul,hsweight,zero_mul,sub_zero]
  have hmean (ω) : (∑ a, w a ω*μ a ω) = ∑ a, w a ω*(μ a ω-μ j ω) := by
    simp only [mul_sub,sum_sub_distrib,← sum_mul,hsweight,zero_mul,sub_zero]
  have hcoreeq : (∫ ω, ∑ a, w a ω*R.gEst arms t a ω ∂P) =
      ∫ ω, ∑ a, w a ω*μ a ω ∂P := by
    simp_rw [hcore,hmean]
    rw [integral_finsetSum _ (fun a _ => hwi a),integral_finsetSum _ (fun a _ => hwμi a)]
    exact sum_congr rfl fun a _ => heq a
  obtain ⟨hseli,hsel⟩ := @finite_condExp K Ω mΩ P inferInstance (R.G t) hm (R.A t) hr.1.1
    (R.p t) hr.2.2.1 μ hμ 1 hμb
  have hseleq : (∫ ω, μ (R.A t ω) ω ∂P) = ∫ ω, ∑ a, R.p t ω a*μ a ω ∂P := by
    rw [← integral_condExp hm]; exact integral_congr_ae hsel
  have hpi (a) : Integrable (fun ω => R.p t ω a*μ a ω) P :=
    mul_integrable P (((measurable_pi_apply a).comp hp).mono hm le_rfl) (hμi a) 1 (hpb a)
  have hqi (a) := mul_integrable P ((hw a).mono hm le_rfl) (hμi a) _ (hwb a)
  have hei (a) : Integrable (fun ω => v a ω*((arms a-arms j) ⬝ᵥ θ)) P :=
    (bounded_integrable P (hv a) 2 (hvb a)).mul_const _
  have hci (a) : Integrable (fun ω => v a ω*(arms a ⬝ᵥ (R.θs t ω-θ))) P := by
    simp_rw [dotProduct_sub]
    exact mul_integrable P (hv a) ((hμi a).sub (integrable_const _)) 2 (hvb a)
  have hreg (ω) : (arms (R.A t ω)-∑ a, u a • arms a) ⬝ᵥ R.θs t ω =
      μ (R.A t ω) ω-∑ a, u a*μ a ω := by
    simp only [sub_dotProduct,sum_dotProduct,smul_dotProduct,smul_eq_mul,μ]
  have hri : Integrable (fun ω => (arms (R.A t ω)-∑ a,u a • arms a) ⬝ᵥ R.θs t ω) P := by
    simp_rw [hreg]; exact hseli.sub (integrable_finsetSum _ fun a _ => (hμi a).const_mul _)
  refine ⟨hri,integrable_finsetSum _ (fun a _ => hwgi a),
    integrable_finsetSum _ (fun a _ => hei a),integrable_finsetSum _ (fun a _ => hci a),?_⟩
  change (∫ ω, _ ∂P) = (∫ ω, ∑ a,w a ω*R.gEst arms t a ω ∂P)+_+_
  rw [hcoreeq]
  simp_rw [hreg]
  rw [integral_sub hseli (integrable_finsetSum _ fun a _ => (hμi a).const_mul _),hseleq]
  rw [← integral_sub (integrable_finsetSum _ fun a _ => hpi a)
    (integrable_finsetSum _ fun a _ => (hμi a).const_mul _)]
  rw [← integral_add (integrable_finsetSum _ fun a _ => hqi a)
    (integrable_finsetSum _ fun a _ => hei a)]
  have hsumqi : Integrable (fun ω => (∑ a,w a ω*μ a ω)+
      (∑ a,v a ω*((arms a-arms j) ⬝ᵥ θ))) P :=
    (integrable_finsetSum univ fun a _ => hqi a).add
      (integrable_finsetSum univ fun a _ => hei a)
  rw [← integral_add hsumqi (integrable_finsetSum univ fun a _ => hci a)]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  have hsv : ∑ a, v a ω = 0 := by simp [v,sum_sub_distrib,hp1 ω,hq1 ω]
  have hz : (∑ a, v a ω*((arms j) ⬝ᵥ θ)) = 0 := by rw [← sum_mul,hsv,zero_mul]
  simp only [dotProduct_sub,sub_dotProduct]
  dsimp only [w,v,μ] at *
  rw [← sum_sub_distrib,← sum_add_distrib,← sum_add_distrib]
  calc
    _ = ∑ a, ((q ω a-u a)*(arms a ⬝ᵥ R.θs t ω) +
        (R.p t ω a-q ω a)*((arms a ⬝ᵥ θ)-(arms j ⬝ᵥ θ)) +
        (R.p t ω a-q ω a)*((arms a ⬝ᵥ R.θs t ω)-(arms a ⬝ᵥ θ)) +
        (R.p t ω a-q ω a)*(arms j ⬝ᵥ θ)) := sum_congr rfl fun a _ => by ring
    _ = _ := by rw [sum_add_distrib,hz,add_zero]

private lemma entropy_integrable {d K : ℕ} [Nonempty (Fin K)] {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (arms : Fin K → Fin d → ℝ) (T : ℕ)
    (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) (t : ℕ) (ht : t < T) :
    Integrable (fun ω => -∑ a, qSoft (beta d K (t+1)) arms (R.cumEst arms t ω) a *
      Real.log (qSoft (beta d K (t+1)) arms (R.cumEst arms t ω) a)) P := by
  have hr := hR t ht
  have hc := (cum_measurable P arms T R hR t ht.le).mono
    (hr.1.2.2.2.2.1.trans hr.1.2.2.2.1) le_rfl
  apply Integrable.neg
  apply integrable_finsetSum
  intro a _
  have hq : Measurable[mΩ] (fun ω => qSoft (beta d K (t+1)) arms (R.cumEst arms t ω) a) :=
    (q_measurable arms (beta d K (t+1)) a).comp hc
  apply bounded_integrable P (hq.mul hq.log) 1
  intro ω
  change |qSoft (beta d K (t+1)) arms (R.cumEst arms t ω) a *
    Real.log (qSoft (beta d K (t+1)) arms (R.cumEst arms t ω) a)| ≤ 1
  have hp := q_prob (beta d K (t+1)) arms (R.cumEst arms t ω)
  have hlo := Real.self_sub_one_le_mul_log (hp.1 a)
  have hhi := mul_nonpos_of_nonneg_of_nonpos (hp.1 a)
    (Real.log_nonpos (hp.1 a) (prob_le_one _ hp.1 hp.2 a))
  exact abs_le.mpr ⟨by linarith [hp.1 a],by linarith⟩

private lemma proxy_integrable {d K : ℕ} (hd : 1 ≤ d) [Nonempty (Fin K)]
    (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) (t : ℕ) (ht : t < T) :
    Integrable (fun ω => proxyC arms (t+1) (R.cumEst arms t ω) (R.p t ω)) P := by
  have hr := hR t ht
  have hh := hr.1.2.2.2.2.1.trans hr.1.2.2.2.1
  have hc := (cum_measurable P arms T R hR t ht.le).mono hh le_rfl
  have hp := hr.2.1.1.mono hh le_rfl
  let q := fun ω => qSoft (beta d K (t+1)) arms (R.cumEst arms t ω)
  have hq (a) : Measurable[mΩ] (fun ω => q ω a) := (q_measurable arms _ a).comp hc
  have hbar (i : Fin d) : Measurable[mΩ] (fun ω => abar arms (q ω) i) := by
    simp only [abar,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact Finset.measurable_sum _ fun a _ => (hq a).mul_const _
  have hv (b) := (v_measurable arms b).comp hp
  have hrow (a b) : Measurable[mΩ] (fun ω =>
      (arms a-abar arms (q ω)) ⬝ᵥ vCoef arms (R.p t ω) b) :=
    Finset.measurable_sum _ fun i _ => (measurable_const.sub (hbar i)).mul
      ((measurable_pi_apply i).comp (hv b))
  have hχ : Measurable chi := by unfold chi; fun_prop
  have hf : Measurable[mΩ] (fun ω => proxyC arms (t+1) (R.cumEst arms t ω) (R.p t ω)) := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro b _
    apply ((measurable_pi_apply b).comp hp).mul
    exact Finset.measurable_sum _ fun a _ => (hq a).mul (hχ.comp ((hrow a b).div_const _))
  apply bounded_integrable P hf (2*(d : ℝ)/beta d K (t+1))
  intro ω
  have h0 : 0 ≤ proxyC arms (t+1) (R.cumEst arms t ω) (R.p t ω) := by
    unfold proxyC
    apply mul_nonneg (beta_pos hd).le
    apply sum_nonneg; intro b _
    apply mul_nonneg ((hr.2.1.2 ω).1.1 b)
    apply sum_nonneg; intro a _
    apply mul_nonneg ((q_prob _ arms _).1 a)
    have hnonneg (x : ℝ) : 0 ≤ chi x := by
      unfold chi
      linarith [Real.add_one_le_exp x,Real.add_one_le_exp (-x)]
    exact hnonneg _
  rw [abs_of_nonneg h0]
  exact (IAFTRL.lemma_D_4 hd arms hA P T R hR t ht).2.2 ω

private lemma pathwise {d K : ℕ} (hd : 1 ≤ d) [Nonempty (Fin K)]
    (arms : Fin K → Fin d → ℝ) {Ω : Type*} (R : Run d K Ω) (ω : Ω)
    (u : Fin K → ℝ) (hu0 : ∀ a, 0 ≤ u a) (hu1 : ∑ a, u a = 1) (T : ℕ) :
    (∑ t ∈ range T, ∑ a, (qSoft (beta d K (t+1)) arms (R.cumEst arms t ω) a-u a)*
      R.gEst arms t a ω) ≤ beta d K 1 * Real.log K +
      (∑ t ∈ Ico 1 T, (beta d K (t+1)-beta d K t) *
        (-∑ a, qSoft (beta d K (t+1)) arms (R.cumEst arms t ω) a *
          Real.log (qSoft (beta d K (t+1)) arms (R.cumEst arms t ω) a))) +
      ∑ t ∈ range T, R.mixGap arms t ω := by
  classical
  let S := fun t a => arms a ⬝ᵥ R.cumEst arms t ω
  let b := fun t => beta d K (t+1)
  let c := fun t => refArm arms (R.cumEst arms t ω) ⬝ᵥ R.thetaHat arms t ω
  have hS : S 0 = 0 := by ext a; simp [S,Run.cumEst]
  have hg (t a) : S (t+1) a-S t a-c t = R.gEst arms t a ω := by
    have he : R.cumEst arms (t+1) ω = R.cumEst arms t ω+R.thetaHat arms t ω :=
      sum_range_succ _ _
    dsimp [S,c]
    rw [he,dotProduct_add]
    simp only [Run.gEst,Run.thetaHat,dotProduct_smul,smul_eq_mul,sub_dotProduct]
    ring
  have hq (t a) : D18Entropy.Q (b t) (S t) a =
      qSoft (beta d K (t+1)) arms (R.cumEst arms t ω) a := rfl
  have hs := D18Entropy.telescoping b (fun _ => beta_pos hd) S hS u hu0 hu1 c T
  dsimp only at hs
  simp_rw [hg,hq] at hs
  have hpen : (∑ t ∈ Ico 1 T, (b t-b (t-1))*D18Entropy.H (D18Entropy.Q (b t) (S t))) =
      ∑ t ∈ Ico 1 T, (beta d K (t+1)-beta d K t)*
        (-∑ a, qSoft (beta d K (t+1)) arms (R.cumEst arms t ω) a *
          Real.log (qSoft (beta d K (t+1)) arms (R.cumEst arms t ω) a)) := by
    apply sum_congr rfl; intro t ht
    have ht1 := (mem_Ico.mp ht).1
    simp only [b,Nat.sub_add_cancel ht1,D18Entropy.H]
    rfl
  rw [hpen] at hs
  exact hs

end D18Proof

theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
    (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) (θ : Fin d → ℝ) (jstar : Fin K)
    (u : Fin K → ℝ) (hu0 : ∀ a, 0 ≤ u a) (hu1 : ∑ a, u a = 1) :
    let q : ℕ → Ω → Fin K → ℝ := fun t ω => qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω)
    let H : (Fin K → ℝ) → ℝ := fun p => -∑ a, p a * Real.log (p a)
    let explo : ℝ := ∑ t ∈ Finset.range T,
      ∫ ω, ∑ a, (R.p t ω a - q t ω a) * ((arms a - arms jstar) ⬝ᵥ θ) ∂P
    let corr : ℝ := ∑ t ∈ Finset.range T,
      ∫ ω, ∑ a, (R.p t ω a - q t ω a) * (arms a ⬝ᵥ (R.θs t ω - θ)) ∂P
    let pen : ℝ := beta d K 1 * Real.log K +
      ∑ t ∈ Finset.Ico 1 T, (beta d K (t + 1) - beta d K t) * ∫ ω, H (q t ω) ∂P
    regretDist P arms T R u =
        (∫ ω, ∑ t ∈ Finset.range T, ∑ a, (q t ω a - u a) * R.gEst arms t a ω ∂P) + explo + corr ∧
      regretDist P arms T R u ≤
        pen + ∑ t ∈ Finset.range T, ∫ ω, R.mixGap arms t ω ∂P + explo + corr ∧
      regretDist P arms T R u ≤
        pen + ∑ t ∈ Finset.range T, ∫ ω, proxyC arms (t + 1) (R.cumEst arms t ω) (R.p t ω) ∂P +
          explo + corr := by
  classical
  let : Nonempty (Fin K) := ⟨jstar⟩
  let q := fun t ω => qSoft (beta d K (t+1)) arms (R.cumEst arms t ω)
  let H := fun p : Fin K → ℝ => -∑ a, p a*Real.log (p a)
  let f := fun t ω => ∑ a, (q t ω a-u a)*R.gEst arms t a ω
  let e := fun t ω => ∑ a, (R.p t ω a-q t ω a)*((arms a-arms jstar) ⬝ᵥ θ)
  let c := fun t ω => ∑ a, (R.p t ω a-q t ω a)*(arms a ⬝ᵥ (R.θs t ω-θ))
  let r := fun t ω => (arms (R.A t ω)-∑ a,u a • arms a) ⬝ᵥ R.θs t ω
  let pen := beta d K 1*Real.log K +
    ∑ t ∈ Ico 1 T, (beta d K (t+1)-beta d K t)*(∫ ω,H (q t ω) ∂P)
  change regretDist P arms T R u = (∫ ω,∑ t ∈ range T,f t ω ∂P) +
      (∑ t ∈ range T,∫ ω,e t ω ∂P)+(∑ t ∈ range T,∫ ω,c t ω ∂P) ∧
    regretDist P arms T R u ≤ pen + (∑ t ∈ range T,∫ ω,R.mixGap arms t ω ∂P) +
      (∑ t ∈ range T,∫ ω,e t ω ∂P)+(∑ t ∈ range T,∫ ω,c t ω ∂P) ∧
    regretDist P arms T R u ≤ pen +
      (∑ t ∈ range T,∫ ω,proxyC arms (t+1) (R.cumEst arms t ω) (R.p t ω) ∂P) +
      (∑ t ∈ range T,∫ ω,e t ω ∂P)+(∑ t ∈ range T,∫ ω,c t ω ∂P)
  have hr (t : ℕ) (ht : t < T) : Integrable (r t) P ∧ Integrable (f t) P ∧
      Integrable (e t) P ∧ Integrable (c t) P ∧
        (∫ ω,r t ω ∂P)=(∫ ω,f t ω ∂P)+(∫ ω,e t ω ∂P)+(∫ ω,c t ω ∂P) :=
    D18Proof.round_identity hd arms hA P T R hR θ jstar u hu1 t ht
  have hfi : Integrable (fun ω => ∑ t ∈ range T,f t ω) P :=
    integrable_finsetSum _ fun t ht => (hr t (mem_range.mp ht)).2.1
  have heq : regretDist P arms T R u = (∫ ω,∑ t ∈ range T,f t ω ∂P) +
      (∑ t ∈ range T,∫ ω,e t ω ∂P)+(∑ t ∈ range T,∫ ω,c t ω ∂P) := by
    change (∫ ω,∑ t ∈ range T,r t ω ∂P)=_
    rw [integral_finsetSum _ (fun t ht => (hr t (mem_range.mp ht)).1)]
    calc
      _ = ∑ t ∈ range T, ((∫ ω,f t ω ∂P)+(∫ ω,e t ω ∂P)+(∫ ω,c t ω ∂P)) :=
        sum_congr rfl fun t ht => (hr t (mem_range.mp ht)).2.2.2.2
      _ = _ := by
        rw [sum_add_distrib,sum_add_distrib,
          integral_finsetSum _ (fun t ht => (hr t (mem_range.mp ht)).2.1)]
  have hHi (t : ℕ) (ht : t < T) : Integrable (fun ω => H (q t ω)) P :=
    D18Proof.entropy_integrable P arms T R hR t ht
  have hDi (t : ℕ) (ht : t < T) : Integrable (R.mixGap arms t) P :=
    (IAFTRL.lemma_D_4 hd arms hA P T R hR t ht).1
  let penfun := fun ω => ∑ t ∈ Ico 1 T, (beta d K (t+1)-beta d K t)*H (q t ω)
  have hpi : Integrable penfun P := integrable_finsetSum _ fun t ht =>
    (hHi t (mem_Ico.mp ht).2).const_mul _
  have hdi : Integrable (fun ω => ∑ t ∈ range T,R.mixGap arms t ω) P :=
    integrable_finsetSum _ fun t ht => hDi t (mem_range.mp ht)
  have hconst : Integrable (fun _ : Ω => beta d K 1*Real.log K) P := integrable_const _
  have hadd : Integrable (fun ω => beta d K 1*Real.log K+penfun ω) P := hconst.add hpi
  have hpen : (∫ ω, beta d K 1*Real.log K+penfun ω+
      (∑ t ∈ range T,R.mixGap arms t ω) ∂P) =
      pen + ∑ t ∈ range T,∫ ω,R.mixGap arms t ω ∂P := by
    rw [integral_add hadd hdi,
      integral_add hconst hpi,
      integral_finsetSum _ (fun t ht => hDi t (mem_range.mp ht))]
    change (∫ ω,beta d K 1*Real.log K ∂P)+
      (∫ ω,∑ t ∈ Ico 1 T,(beta d K (t+1)-beta d K t)*H (q t ω) ∂P)+_=_
    rw [integral_finsetSum _ (fun t ht => (hHi t (mem_Ico.mp ht).2).const_mul _)]
    simp only [integral_const,probReal_univ,one_smul,integral_const_mul]
    rfl
  have hcore : (∫ ω,∑ t ∈ range T,f t ω ∂P) ≤
      pen + ∑ t ∈ range T,∫ ω,R.mixGap arms t ω ∂P := by
    rw [← hpen]
    apply integral_mono hfi (hadd.add hdi)
    intro ω
    exact D18Proof.pathwise hd arms R ω u hu0 hu1 T
  have hstab : (∑ t ∈ range T,∫ ω,R.mixGap arms t ω ∂P) ≤
      ∑ t ∈ range T,∫ ω,proxyC arms (t+1) (R.cumEst arms t ω) (R.p t ω) ∂P := by
    apply sum_le_sum
    intro t ht
    have ht' := mem_range.mp ht
    have hm := (hR t ht').1.2.2.2.1
    calc
      _ = ∫ ω,P[R.mixGap arms t | R.G t] ω ∂P := (integral_condExp hm).symm
      _ ≤ _ := integral_mono_ae integrable_condExp
        (D18Proof.proxy_integrable hd arms hA P T R hR t ht')
        (IAFTRL.lemma_D_4 hd arms hA P T R hR t ht').2.1
  exact ⟨heq,by linarith,by linarith⟩
