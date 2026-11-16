-- Prove2me | solution 1 for IAFTRL.lemma_D_4
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T06:18:59.767456+00:00
-- url     : https://prove2.me/submissions/3c6cb049-5e7b-4440-b9d9-cdbee77b2f47

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_Run_mixGap
import Theorems.Thm_IAFTRL_lemma_J_4

open Matrix Finset MeasureTheory IAFTRL
set_option maxHeartbeats 1000000

namespace D4Proof

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

private lemma ref_spec {d K : ℕ} [Nonempty (Fin K)]
    (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) :
    ∃ j, refArm arms S = arms j ∧ ∀ a, 0 ≤ Zd arms S a := by
  classical
  let s := univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S
  have hs : s.Nonempty := by
    obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image univ (fun j : Fin K => arms j ⬝ᵥ S) univ_nonempty
    exact ⟨j, mem_filter.mpr ⟨hj, fun i => hmin i (mem_univ i)⟩⟩
  have href : refArm arms S = arms (s.min' hs) := by
    unfold refArm
    rw [dif_pos hs]
  refine ⟨s.min' hs, href, ?_⟩
  intro a
  unfold Zd
  rw [href]
  exact sub_nonneg.mpr ((mem_filter.mp (s.min'_mem hs)).2 a)

private lemma gap_center {K : ℕ} (q g u : Fin K → ℝ) (β y : ℝ)
    (hβ : 0 < β) (hpos : 0 < ∑ a, q a * Real.exp (-g a / β))
    (hrel : ∀ a, g a - ∑ c, q c * g c = y * u a) :
    (∑ a, q a * g a) + β * Real.log (∑ a, q a * Real.exp (-g a / β)) =
      β * Real.log (∑ a, q a * Real.exp (-y * u a / β)) := by
  let m := ∑ c, q c * g c
  have he (a : Fin K) : Real.exp (-y * u a / β) =
      Real.exp (m/β) * Real.exp (-g a / β) := by
    rw [← Real.exp_add]
    congr 1
    calc
      _ = (m-g a)/β := congrArg (fun z : ℝ => z/β) (by dsimp [m]; linarith [hrel a])
      _ = _ := by ring
  simp_rw [he]
  have hsum : (∑ a, q a * (Real.exp (m/β) * Real.exp (-g a / β))) =
      Real.exp (m/β) * ∑ a, q a * Real.exp (-g a / β) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    ring
  rw [hsum, Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hpos), Real.log_exp]
  change m + _ = _
  field_simp [ne_of_gt hβ]

private lemma centered_bounds {K : ℕ} (q u : Fin K → ℝ) (β y : ℝ)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) (hβ : 0 < β)
    (hmean : ∑ a, q a * u a = 0) (hy : |y| ≤ 1) :
    0 ≤ β * Real.log (∑ a, q a * Real.exp (-y * u a / β)) ∧
    β * Real.log (∑ a, q a * Real.exp (-y * u a / β)) ≤
      β * ∑ a, q a * chi (u a / β) := by
  let z (a : Fin K) := -y * u a / β
  have hz : ∑ a, q a * z a = 0 := by
    calc
      _ = (-y/β) * ∑ a, q a * u a := by
        rw [mul_sum]; apply sum_congr rfl; intro a _; dsimp [z]; ring
      _ = 0 := by rw [hmean, mul_zero]
  have hone : 1 ≤ ∑ a, q a * Real.exp (z a) := by
    calc
      1 = ∑ a, q a * (z a + 1) := by
        simp_rw [mul_add, mul_one]
        rw [sum_add_distrib, hz, hq1, zero_add]
      _ ≤ _ := sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (hq0 a)
  constructor
  · exact mul_nonneg hβ.le (Real.log_nonneg hone)
  · apply mul_le_mul_of_nonneg_left _ hβ.le
    calc
      _ ≤ (∑ a, q a * Real.exp (z a)) - 1 := Real.log_le_sub_one_of_pos (by linarith)
      _ = ∑ a, q a * (Real.exp (z a) - z a - 1) := by
        simp_rw [mul_sub, mul_one]
        rw [sum_sub_distrib, sum_sub_distrib, hz, hq1, sub_zero]
      _ ≤ ∑ a, q a * chi (z a) := sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (IAFTRL.lemma_J_4.{0}.2.2.2.2.1 _) (hq0 a)
      _ ≤ _ := by
        apply sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (hq0 a)
        apply IAFTRL.lemma_J_4.{0}.2.2.2.1
        dsimp [z]
        rw [abs_div, abs_div, abs_mul, abs_neg]
        exact div_le_div_of_nonneg_right (by nlinarith [abs_nonneg (u a)]) (abs_nonneg β)

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

private lemma B_pos {K : ℕ} (hK : 1 ≤ K) : 0 < Bc K := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hc : (256 : ℝ) ≤ (⌈256 + Real.log (2 * (K : ℝ))⌉ : ℝ) := by
    have hlog : 0 ≤ Real.log (2 * (K : ℝ)) := Real.log_nonneg (by linarith)
    exact (by linarith : (256 : ℝ) ≤ 256 + Real.log (2 * (K : ℝ))).trans (Int.le_ceil _)
  unfold Bc
  exact mul_pos (by norm_num) (by linarith)

private lemma row_bounded {d K : ℕ} [Nonempty (Fin K)]
    (arms : Fin K → Fin d → ℝ) (t : ℕ) (S : Fin d → ℝ) (p : Fin K → ℝ)
    (hp : IsFeasible2_3 arms t S p) (L : ℝ) (hB : 0 < Bc K)
    (hL : ∀ a b, |(arms a-arms b) ⬝ᵥ S| ≤ L) :
    ∀ a b, |(arms a-refArm arms S) ⬝ᵥ vCoef arms p b| ≤ beta d K t + L / Bc K := by
  obtain ⟨j, hj, _⟩ := ref_spec arms S
  intro a b
  apply (hp.2.2.2.1 a b).trans
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ hB.le
  change arms a ⬝ᵥ S - refArm arms S ⬝ᵥ S ≤ L
  rw [hj, ← sub_dotProduct]
  exact (le_abs_self _).trans (hL a j)

private lemma cumulative_bound {d K : ℕ} [Nonempty (Fin K)] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (arms : Fin K → Fin d → ℝ) (T : ℕ)
    (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) (hd : 1 ≤ d) (hB : 0 < Bc K) :
    ∀ t ≤ T, ∃ L : ℝ, 0 ≤ L ∧ ∀ ω a b,
      |(arms a-arms b) ⬝ᵥ R.cumEst arms t ω| ≤ L := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨0, le_rfl, by intros; simp [Run.cumEst]⟩
  | succ t ih =>
    intro ht
    obtain ⟨L, hL0, hL⟩ := ih (by omega)
    let C := beta d K (t+1) + L / Bc K
    have hC : 0 ≤ C := add_nonneg (beta_pos hd).le (div_nonneg hL0 hB.le)
    refine ⟨L+2*C, by positivity, ?_⟩
    intro ω a b
    have hf := (hR t (by omega)).2.1.2 ω |>.1
    have hr := row_bounded arms (t+1) (R.cumEst arms t ω) (R.p t ω) hf L hB (hL ω)
    have hy := (hR t (by omega)).2.2.2.1.1 ω
    have hg (c : Fin K) :
        |((arms c-refArm arms (R.cumEst arms t ω)) ⬝ᵥ
          vCoef arms (R.p t ω) (R.A t ω)) * R.Y t ω| ≤ C := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hy (abs_nonneg _)).trans (by simpa using hr c (R.A t ω))
    have he : (arms a-arms b) ⬝ᵥ R.thetaHat arms t ω =
        ((arms a-refArm arms (R.cumEst arms t ω)) ⬝ᵥ vCoef arms (R.p t ω) (R.A t ω)) * R.Y t ω -
        ((arms b-refArm arms (R.cumEst arms t ω)) ⬝ᵥ vCoef arms (R.p t ω) (R.A t ω)) * R.Y t ω := by
      simp only [Run.thetaHat, dotProduct_smul, sub_dotProduct, smul_eq_mul]
      ring
    have htBound : |(arms a-arms b) ⬝ᵥ R.thetaHat arms t ω| ≤ 2*C := by
      rw [he]
      exact (abs_sub _ _).trans (by linarith [hg a, hg b])
    have hsucc : R.cumEst arms (t+1) ω = R.cumEst arms t ω + R.thetaHat arms t ω :=
      sum_range_succ _ _
    rw [hsucc, dotProduct_add]
    exact (abs_add_le _ _).trans (add_le_add (hL ω a b) htBound)

private lemma row_center {d K : ℕ} (arms : Fin K → Fin d → ℝ) (q : Fin K → ℝ)
    (hq1 : ∑ a, q a = 1) (v r : Fin d → ℝ) (y : ℝ) :
    (∑ a, q a * ((arms a-abar arms q) ⬝ᵥ v) = 0) ∧
    (∀ a, ((arms a-r) ⬝ᵥ v)*y - ∑ c, q c * (((arms c-r) ⬝ᵥ v)*y) =
      y * ((arms a-abar arms q) ⬝ᵥ v)) := by
  have hm : (abar arms q) ⬝ᵥ v = ∑ a, q a * (arms a ⬝ᵥ v) := by
    simp [abar, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  have hg : ∑ c, q c * (((arms c-r) ⬝ᵥ v)*y) =
      ((abar arms q) ⬝ᵥ v-r ⬝ᵥ v)*y := by
    simp only [sub_dotProduct]
    simp_rw [← mul_assoc]
    rw [← sum_mul]
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ← sum_mul, hq1, one_mul, hm]
  constructor
  · simp only [sub_dotProduct, mul_sub, sum_sub_distrib, ← sum_mul, hq1, one_mul, hm, sub_self]
  · intro a
    rw [hg]
    simp only [sub_dotProduct]
    ring

private lemma centered_row_bound {d K : ℕ} (arms : Fin K → Fin d → ℝ) (q : Fin K → ℝ)
    (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) (v r : Fin d → ℝ) (C : ℝ)
    (hrow : ∀ a, |(arms a-r) ⬝ᵥ v| ≤ C) :
    ∀ a, |(arms a-abar arms q) ⬝ᵥ v| ≤ 2*C := by
  have havg : |∑ c, q c * ((arms c-r) ⬝ᵥ v)| ≤ C := by
    calc
      _ ≤ ∑ c, |q c * ((arms c-r) ⬝ᵥ v)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, q c * C := by
        apply sum_le_sum
        intro c _
        rw [abs_mul, abs_of_nonneg (hq0 c)]
        exact mul_le_mul_of_nonneg_left (hrow c) (hq0 c)
      _ = C := by rw [← sum_mul, hq1, one_mul]
  intro a
  have hr := (row_center arms q hq1 v r 1).2 a
  simp only [mul_one, one_mul] at hr
  rw [← hr]
  exact (abs_sub _ _).trans (by linarith [hrow a])

private lemma q_pos {d K : ℕ} [Nonempty (Fin K)] (β : ℝ)
    (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (a : Fin K) :
    0 < qSoft β arms S a :=
  div_pos (Real.exp_pos _) (sum_pos (fun b _ => Real.exp_pos _) univ_nonempty)

private lemma mix_center {d K : ℕ} [Nonempty (Fin K)] {Ω : Type*}
    (R : Run d K Ω) (arms : Fin K → Fin d → ℝ) (t : ℕ) (ω : Ω) (hd : 1 ≤ d) :
    R.mixGap arms t ω =
      beta d K (t+1) * Real.log (∑ a,
        qSoft (beta d K (t+1)) arms (R.cumEst arms t ω) a *
          Real.exp (-R.Y t ω * ((arms a-abar arms
            (qSoft (beta d K (t+1)) arms (R.cumEst arms t ω))) ⬝ᵥ
              vCoef arms (R.p t ω) (R.A t ω)) / beta d K (t+1))) := by
  let q := qSoft (beta d K (t+1)) arms (R.cumEst arms t ω)
  have hq := (q_prob (beta d K (t+1)) arms (R.cumEst arms t ω)).2
  apply gap_center q (fun a => R.gEst arms t a ω) _ _ _ (beta_pos hd)
  · exact sum_pos (fun a _ => mul_pos (q_pos _ _ _ a) (Real.exp_pos _)) univ_nonempty
  · exact (row_center arms q hq (vCoef arms (R.p t ω) (R.A t ω))
      (refArm arms (R.cumEst arms t ω)) (R.Y t ω)).2

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

end D4Proof

theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
    (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) (t : ℕ) (ht : t < T) :
    Integrable (R.mixGap arms t) P ∧
    P[R.mixGap arms t | R.G t] ≤ᵐ[P]
      (fun ω => proxyC arms (t + 1) (R.cumEst arms t ω) (R.p t ω)) ∧
    ∀ ω, proxyC arms (t + 1) (R.cumEst arms t ω) (R.p t ω) ≤ 2 * (d : ℝ) / beta d K (t + 1) := by
  classical
  let ω0 : Ω := Classical.choice (nonempty_of_isProbabilityMeasure P)
  let b0 : Fin K := R.A t ω0
  let : Nonempty (Fin K) := ⟨b0⟩
  have hK : 1 ≤ K := by have h := b0.isLt; omega
  have hr := hR t ht
  have hm : R.G t ≤ ‹MeasurableSpace Ω› := hr.1.2.2.2.1
  have hβ : 0 < beta d K (t+1) := D4Proof.beta_pos hd
  have hB : 0 < Bc K := D4Proof.B_pos hK
  let β := beta d K (t+1)
  let q (ω : Ω) := qSoft β arms (R.cumEst arms t ω)
  let v (b : Fin K) (ω : Ω) := vCoef arms (R.p t ω) b
  let u (a b : Fin K) (ω : Ω) := (arms a-abar arms (q ω)) ⬝ᵥ v b ω
  let H (b : Fin K) (ω : Ω) := β * ∑ a, q ω a * chi (u a b ω / β)
  let F (ω : Ω) := H (R.A t ω) ω
  have hq0 (ω : Ω) : ∀ a, 0 ≤ q ω a := (D4Proof.q_prob β arms _).1
  have hq1 (ω : Ω) : ∑ a, q ω a = 1 := (D4Proof.q_prob β arms _).2
  have hmean (ω : Ω) (b : Fin K) : ∑ a, q ω a * u a b ω = 0 :=
    (D4Proof.row_center arms (q ω) (hq1 ω) (v b ω) 0 1).1
  have hpoint (ω : Ω) : 0 ≤ R.mixGap arms t ω ∧ R.mixGap arms t ω ≤ F ω := by
    rw [D4Proof.mix_center R arms t ω hd]
    exact D4Proof.centered_bounds (q ω) (fun a => u a (R.A t ω) ω) β (R.Y t ω)
      (hq0 ω) (hq1 ω) hβ (hmean ω (R.A t ω)) (hr.2.2.2.1.1 ω)
  have hc : Measurable[R.G t] (R.cumEst arms t) :=
    (D4Proof.cum_measurable P arms T R hR t ht.le).mono hr.1.2.2.2.2.1 le_rfl
  have hp : Measurable[R.G t] (R.p t) :=
    hr.2.1.1.mono hr.1.2.2.2.2.1 le_rfl
  have hq (a : Fin K) : Measurable[R.G t] (fun ω => q ω a) :=
    (D4Proof.q_measurable arms β a).comp hc
  have hv (b : Fin K) : Measurable[R.G t] (v b) :=
    (D4Proof.v_measurable arms b).comp hp
  have hbar (i : Fin d) : Measurable[R.G t] (fun ω => abar arms (q ω) i) := by
    simp only [abar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ fun a _ => (hq a).mul_const _
  have hu (a b : Fin K) : Measurable[R.G t] (u a b) :=
    Finset.measurable_sum _ fun i _ =>
      (measurable_const.sub (hbar i)).mul ((measurable_pi_apply i).comp (hv b))
  have hχ : Measurable chi := by unfold chi; fun_prop
  have hH (b : Fin K) : Measurable[R.G t] (H b) :=
    (Finset.measurable_sum _ fun a _ => (hq a).mul (hχ.comp ((hu a b).div_const β))).const_mul β
  have hD : Measurable (R.mixGap arms t) := by
    have he : R.mixGap arms t = fun ω => β * Real.log
        (∑ a, q ω a * Real.exp (-R.Y t ω * u a (R.A t ω) ω / β)) := by
      funext ω
      exact D4Proof.mix_center R arms t ω hd
    rw [he]
    apply Measurable.const_mul
    apply Measurable.log
    apply Finset.measurable_sum
    intro a _
    apply (hq a |>.mono hm le_rfl).mul
    apply Measurable.exp
    apply Measurable.div_const
    apply hr.1.2.1.neg.mul
    exact D4Proof.selected_measurable (u a) (fun b => (hu a b).mono hm le_rfl) (R.A t) hr.1.1
  obtain ⟨L, hL0, hL⟩ := D4Proof.cumulative_bound P arms T R hR hd hB t ht.le
  let C := β + L / Bc K
  have hC0 : 0 ≤ C := add_nonneg hβ.le (div_nonneg hL0 hB.le)
  have hrbound (ω : Ω) (a b : Fin K) :
      |(arms a-refArm arms (R.cumEst arms t ω)) ⬝ᵥ v b ω| ≤ C :=
    D4Proof.row_bounded arms (t+1) (R.cumEst arms t ω) (R.p t ω)
      (hr.2.1.2 ω).1 L hB (hL ω) a b
  have hubound (ω : Ω) (a b : Fin K) : |u a b ω| ≤ 2*C :=
    D4Proof.centered_row_bound arms (q ω) (hq0 ω) (hq1 ω) (v b ω)
      (refArm arms (R.cumEst arms t ω)) C (fun a => hrbound ω a b) a
  have hH0 (b : Fin K) (ω : Ω) : 0 ≤ H b ω :=
    mul_nonneg hβ.le (sum_nonneg fun a _ => mul_nonneg (hq0 ω a)
      (IAFTRL.lemma_J_4.{0}.2.2.1 _))
  have hHbound (b : Fin K) (ω : Ω) : |H b ω| ≤ β * chi (2*C/β) := by
    rw [abs_of_nonneg (hH0 b ω)]
    apply mul_le_mul_of_nonneg_left _ hβ.le
    calc
      _ ≤ ∑ a, q ω a * chi (2*C/β) := by
        apply sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (hq0 ω a)
        apply IAFTRL.lemma_J_4.{0}.2.2.2.1
        rw [abs_div, abs_of_pos hβ, abs_of_nonneg (div_nonneg (by positivity) hβ.le)]
        exact div_le_div_of_nonneg_right (hubound ω a b) hβ.le
      _ = _ := by rw [← sum_mul, hq1 ω, one_mul]
  obtain ⟨hFi, hFce⟩ := D4Proof.finite_condExp P (R.G t) hm (R.A t) hr.1.1 (R.p t)
    hr.2.2.1 H hH (β*chi (2*C/β)) hHbound
  have hDi : Integrable (R.mixGap arms t) P := hFi.mono_nonneg hD.aestronglyMeasurable
    (ae_of_all _ fun ω => (hpoint ω).1) (ae_of_all _ fun ω => (hpoint ω).2)
  have hsum (ω : Ω) : ∑ b, R.p t ω b * H b ω =
      proxyC arms (t+1) (R.cumEst arms t ω) (R.p t ω) := by
    change (∑ b, R.p t ω b * (β * ∑ a, q ω a * chi (u a b ω/β))) =
      β * ∑ b, R.p t ω b * ∑ a, q ω a * chi (u a b ω/β)
    rw [mul_sum]
    apply sum_congr rfl
    intro b _
    ring
  refine ⟨hDi, ?_, fun ω => (hr.2.1.2 ω).1.2.2.2.2.2⟩
  have hle := condExp_mono (m := R.G t) hDi hFi (ae_of_all _ fun ω => (hpoint ω).2)
  filter_upwards [hle, hFce] with ω hleω hceω
  exact hleω.trans_eq (hceω.trans (hsum ω))
