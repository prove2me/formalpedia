-- Prove2me | solution 1 for IAFTRL.lemma_D_15
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T06:38:11.631897+00:00
-- url     : https://prove2.me/submissions/56b35eaf-cc8f-4b08-8675-c0315cdac7d3

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_Run_gEst

open Matrix Finset MeasureTheory IAFTRL
set_option maxHeartbeats 1000000

namespace D15Proof

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


private lemma q_pos {d K : ℕ} [Nonempty (Fin K)] (β : ℝ)
    (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (a : Fin K) :
    0 < qSoft β arms S a :=
  div_pos (Real.exp_pos _) (sum_pos (fun b _ => Real.exp_pos _) univ_nonempty)


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


private lemma sym_bilin {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.IsHermitian) (x y : Fin d → ℝ) :
    x ⬝ᵥ H *ᵥ y = y ⬝ᵥ H *ᵥ x := by
  have hs : Hᵀ = H := by simpa only [conjTranspose_eq_transpose_of_trivial] using hH.eq
  rw [dotProduct_mulVec, ← mulVec_transpose, hs, dotProduct_comm]


private lemma cov_bilin {d K : ℕ} (arms : Fin K → Fin d → ℝ) (p : Fin K → ℝ)
    (x y : Fin d → ℝ) :
    x ⬝ᵥ (∑ b, p b • vecMulVec (arms b) (arms b)) *ᵥ y =
      ∑ b, p b * (x ⬝ᵥ arms b) * (arms b ⬝ᵥ y) := by
  rw [sum_mulVec, dotProduct_sum]
  apply sum_congr rfl
  intro b _
  simp [smul_mulVec, vecMulVec_mulVec, dotProduct_smul, mul_comm, mul_left_comm]


private lemma cov_psd {d K : ℕ} (arms : Fin K → Fin d → ℝ)
    (p : Fin K → ℝ) (hp : ∀ b, 0 ≤ p b) :
    (∑ b, p b • vecMulVec (arms b) (arms b)).PosSemidef := by
  apply posSemidef_sum
  intro b _
  have h : (vecMulVec (arms b) (arms b)).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (arms b)
  exact h.smul (hp b)


private lemma reconstruct {d K : ℕ} (arms : Fin K → Fin d → ℝ) (p : Fin K → ℝ)
    (hM : (∑ b, p b • vecMulVec (arms b) (arms b)).PosDef) :
    let M := ∑ b, p b • vecMulVec (arms b) (arms b)
    ∑ b, p b • vecMulVec (M⁻¹ *ᵥ arms b) (arms b) = 1 := by
  intro M
  simp_rw [← mul_vecMulVec, ← Matrix.mul_smul]
  rw [← Matrix.mul_sum]
  exact nonsing_inv_mul M ((isUnit_iff_isUnit_det M).mp hM.isUnit)


private lemma variance {d K : ℕ} (arms : Fin K → Fin d → ℝ) (p : Fin K → ℝ)
    (hM : (∑ b, p b • vecMulVec (arms b) (arms b)).PosDef) (x : Fin d → ℝ) :
    let M := ∑ b, p b • vecMulVec (arms b) (arms b)
    ∑ b, p b * (x ⬝ᵥ M⁻¹ *ᵥ arms b) ^ 2 = x ⬝ᵥ M⁻¹ *ᵥ x := by
  intro M
  have hMx : M *ᵥ (M⁻¹ *ᵥ x) = x := by
    rw [mulVec_mulVec, mul_nonsing_inv M ((isUnit_iff_isUnit_det M).mp hM.isUnit), one_mulVec]
  calc
    _ = (M⁻¹ *ᵥ x) ⬝ᵥ M *ᵥ (M⁻¹ *ᵥ x) := by
      rw [cov_bilin]
      apply sum_congr rfl
      intro b _
      rw [dotProduct_comm (M⁻¹ *ᵥ x) (arms b), sym_bilin M⁻¹ hM.inv.1 (arms b) x]
      ring
    _ = _ := by rw [hMx, dotProduct_comm]


private lemma schedules {d K t : ℕ} (hd : 1 ≤ d) (hK : 1 ≤ K) (ht : 1 ≤ t) :
    0 < beta d K t ∧ 0 < Gam d K t ∧ Gam d K t < 1/4 ∧
      Gam d K t * beta d K t = 4 * d ∧ 0 < Bc K := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast ht
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlog := Real.log_nonneg hK1
  have hl : 0 < 1 + Real.log K := by linarith
  have hroot : 0 < Real.sqrt ((d : ℝ) * t / (1 + Real.log K)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < beta d K t := by unfold beta; positivity
  have hg : 0 < Gam d K t := by unfold Gam; positivity
  have hless : Gam d K t < 1/4 := by
    rw [Gam, div_lt_iff₀ hb]
    unfold beta
    linarith
  have hident : Gam d K t * beta d K t = 4 * d := by
    rw [Gam, div_mul_cancel₀ _ (ne_of_gt hb)]
  have hc : (256 : ℝ) ≤ (⌈256 + Real.log (2 * (K : ℝ))⌉ : ℝ) := by
    have hlog2 : 0 ≤ Real.log (2 * (K : ℝ)) := Real.log_nonneg (by linarith)
    exact (by linarith : (256 : ℝ) ≤ 256 + Real.log (2 * (K : ℝ))).trans (Int.le_ceil _)
  refine ⟨hb, hg, hless, hident, ?_⟩
  unfold Bc
  exact mul_pos (by norm_num) (by linarith)




private lemma ref_measurable {d K : ℕ} [Nonempty (Fin K)]
    (arms : Fin K → Fin d → ℝ) : Measurable (refArm arms) := by
  classical
  let s (S : Fin d → ℝ) := univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S
  have hs (S : Fin d → ℝ) : (s S).Nonempty := by
    obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image univ (fun j : Fin K => arms j ⬝ᵥ S) univ_nonempty
    exact ⟨j, mem_filter.mpr ⟨hj, fun i => hmin i (mem_univ i)⟩⟩
  let idx (S : Fin d → ℝ) := (s S).min' (hs S)
  have hval (a : Fin K) : Measurable (fun S : Fin d → ℝ => arms a ⬝ᵥ S) :=
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _
  have hmin (a : Fin K) : MeasurableSet {S : Fin d → ℝ | ∀ i, arms a ⬝ᵥ S ≤ arms i ⬝ᵥ S} := by
    simpa only [Set.ofPred_forall] using
      (MeasurableSet.iInter fun i => measurableSet_le (hval a) (hval i))
  have hi : Measurable idx := by
    apply measurable_to_countable'
    intro j
    have he : idx ⁻¹' {j} = {S : Fin d → ℝ |
        (∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S) ∧
          ∀ b, (∀ i, arms b ⬝ᵥ S ≤ arms i ⬝ᵥ S) → j ≤ b} := by
      ext S
      simp only [Set.mem_preimage, Set.mem_singleton_iff, idx, Finset.min'_eq_iff,
        s, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    rw [he]
    have hleast : MeasurableSet {S : Fin d → ℝ |
        ∀ b, (∀ i, arms b ⬝ᵥ S ≤ arms i ⬝ᵥ S) → j ≤ b} := by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun b => (hmin b).imp (MeasurableSet.const (j ≤ b))
    exact (hmin j).inter hleast
  have he : refArm arms = arms ∘ idx := by
    funext S
    unfold refArm
    rw [dif_pos (hs S)]
    rfl
  rw [he]
  exact (measurable_of_countable arms).comp hi

private lemma cov_posDef {d K : ℕ} (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    (p : Fin K → ℝ) (hp : ∀ b, 0 < p b) :
    (BanditAlgorithm.linearAllocationMatrix arms p).PosDef := by
  apply posDef_iff_dotProduct_mulVec.mpr
  refine ⟨(cov_psd arms p (fun b => (hp b).le)).1, ?_⟩
  intro x hx
  have hex : ∃ b, arms b ⬝ᵥ x ≠ 0 := by
    by_contra hn
    push Not at hn
    have hall : ∀ y ∈ Submodule.span ℝ (Set.range arms), y ⬝ᵥ x = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨b, rfl⟩ := hy; exact hn b
      | zero => simp
      | add y z hy hz ihy ihz => simp only [add_dotProduct, ihy, ihz, add_zero]
      | smul r y hy ih => simp only [smul_dotProduct, ih, smul_zero]
    have hxx : x ⬝ᵥ x = 0 := hall x (by rw [hA.2.2]; trivial)
    exact hx (dotProduct_self_eq_zero.mp hxx)
  obtain ⟨b, hb⟩ := hex
  simp only [star_trivial]
  rw [BanditAlgorithm.linearAllocationMatrix, cov_bilin]
  have he (a : Fin K) : p a * (x ⬝ᵥ arms a) * (arms a ⬝ᵥ x) = p a * (arms a ⬝ᵥ x)^2 := by
    rw [dotProduct_comm x (arms a)]; ring
  simp_rw [he]
  exact sum_pos' (fun a _ => mul_nonneg (hp a).le (sq_nonneg _))
    ⟨b, mem_univ b, mul_pos (hp b) (sq_pos_of_ne_zero hb)⟩

private lemma feasible_posDef {d K : ℕ} [Nonempty (Fin K)] (hd : 1 ≤ d) (hK : 1 ≤ K)
    (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    (t : ℕ) (ht : 1 ≤ t) (S : Fin d → ℝ) (p : Fin K → ℝ)
    (hp : IsFeasible2_3 arms t S p) :
    (BanditAlgorithm.linearAllocationMatrix arms p).PosDef := by
  obtain ⟨w, hw, hcap, he⟩ := hp.2.2.1
  have hg := (schedules hd hK ht).2.2.1
  have hm : 0 < 1 - ∑ b, w b := by linarith
  apply cov_posDef arms hA p
  intro b
  rw [he]
  exact add_pos_of_pos_of_nonneg (mul_pos hm (q_pos _ _ _ b)) (hw b)

private lemma reconstruction_mean {d K : ℕ} (arms : Fin K → Fin d → ℝ)
    (p : Fin K → ℝ) (hM : (BanditAlgorithm.linearAllocationMatrix arms p).PosDef)
    (x θ : Fin d → ℝ) :
    ∑ b, p b * ((x ⬝ᵥ vCoef arms p b) * (arms b ⬝ᵥ θ)) = x ⬝ᵥ θ := by
  have hr := reconstruct arms p hM
  have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => x ⬝ᵥ M *ᵥ θ) hr
  simp only [sum_mulVec, dotProduct_sum, smul_mulVec, vecMulVec_mulVec,
    dotProduct_smul, smul_eq_mul, one_mulVec] at h
  convert h using 1
  apply sum_congr rfl
  intro b _
  simp only [vCoef, BanditAlgorithm.linearAllocationMatrix, op_smul_eq_mul]

private lemma norm_bound {d K : ℕ} (arms : Fin K → Fin d → ℝ)
    (z : Fin d → ℝ) (a : Fin K) : |arms a ⬝ᵥ z| ≤ actionNorm arms z := by
  unfold actionNorm
  exact le_ciSup (f := fun j : Fin K => |arms j ⬝ᵥ z|) (Set.finite_range _).bddAbove a

end D15Proof

theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
    (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) (t : ℕ) (ht : t < T) (a c : Fin K) :
    Integrable (R.gEst arms t a) P ∧ Integrable (fun ω => R.gEst arms t a ω ^ 2) P ∧
    P[R.gEst arms t a | R.G t] =ᵐ[P]
      (fun ω => (arms a - refArm arms (R.cumEst arms t ω)) ⬝ᵥ R.θs t ω) ∧
    P[fun ω => R.gEst arms t a ω - R.gEst arms t c ω | R.G t] =ᵐ[P]
      (fun ω => (arms a - arms c) ⬝ᵥ R.θs t ω) ∧
    P[fun ω => R.gEst arms t a ω ^ 2 | R.G t] ≤ᵐ[P]
      (fun ω => beta d K (t + 1) + Zd arms (R.cumEst arms t ω) a ^ 2 / (Bc K * (t + 1))) ∧
    ∀ ω, |R.gEst arms t a ω| ≤ beta d K (t + 1) + Zd arms (R.cumEst arms t ω) a / Bc K := by
  classical
  let : Nonempty (Fin K) := ⟨a⟩
  have hK : 1 ≤ K := by have h := a.isLt; omega
  have hr := hR t ht
  have hm : R.G t ≤ mΩ := hr.1.2.2.2.1
  have hβ : 0 < beta d K (t+1) := D15Proof.beta_pos hd
  have hB : 0 < Bc K := D15Proof.B_pos hK
  let r (ω : Ω) := refArm arms (R.cumEst arms t ω)
  let v (b : Fin K) (ω : Ω) := vCoef arms (R.p t ω) b
  let f (j b : Fin K) (ω : Ω) := (arms j-r ω) ⬝ᵥ v b ω
  let μ (b : Fin K) (ω : Ω) := arms b ⬝ᵥ R.θs t ω
  have hfeas (ω : Ω) : IsFeasible2_3 arms (t+1) (R.cumEst arms t ω) (R.p t ω) :=
    (hr.2.1.2 ω).1
  have hM (ω : Ω) : (BanditAlgorithm.linearAllocationMatrix arms (R.p t ω)).PosDef :=
    D15Proof.feasible_posDef hd hK arms hA (t+1) (by omega) _ _ (hfeas ω)
  have hc : Measurable[R.G t] (R.cumEst arms t) :=
    (D15Proof.cum_measurable P arms T R hR t ht.le).mono hr.1.2.2.2.2.1 le_rfl
  have hp : Measurable[R.G t] (R.p t) := hr.2.1.1.mono hr.1.2.2.2.2.1 le_rfl
  have href : Measurable[R.G t] r := (D15Proof.ref_measurable arms).comp hc
  have hv (b : Fin K) : Measurable[R.G t] (v b) := (D15Proof.v_measurable arms b).comp hp
  have hf (j b : Fin K) : Measurable[R.G t] (f j b) :=
    Finset.measurable_sum _ fun i _ =>
      (measurable_const.sub ((measurable_pi_apply i).comp href)).mul
        ((measurable_pi_apply i).comp (hv b))
  have hμ (b : Fin K) : Measurable[R.G t] (μ b) :=
    Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp hr.1.2.2.2.2.2.1).const_mul _
  have hμbound (b : Fin K) (ω : Ω) : |μ b ω| ≤ 1 :=
    (D15Proof.norm_bound arms (R.θs t ω) b).trans (hr.2.2.2.2 ω)
  have hy (ω : Ω) : |R.Y t ω| ≤ 1 := hr.2.2.2.1.1 ω
  have hYi : Integrable (R.Y t) P := Integrable.of_bound hr.1.2.1.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hy ω)
  obtain ⟨L, hL0, hL⟩ := D15Proof.cumulative_bound P arms T R hR hd hB t ht.le
  let C := beta d K (t+1) + L / Bc K
  have hC0 : 0 ≤ C := add_nonneg hβ.le (div_nonneg hL0 hB.le)
  have hbound (j b : Fin K) (ω : Ω) : |f j b ω| ≤ C :=
    D15Proof.row_bounded arms (t+1) (R.cumEst arms t ω) (R.p t ω)
      (hfeas ω) L hB (hL ω) j b
  have hgbound (j : Fin K) (ω : Ω) : |R.gEst arms t j ω| ≤ C := by
    change |f j (R.A t ω) ω * R.Y t ω| ≤ C
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hy ω) (abs_nonneg _)).trans
      (by simpa using hbound j (R.A t ω) ω)
  have hgm (j : Fin K) : Measurable[mΩ] (R.gEst arms t j) :=
    (D15Proof.selected_measurable (f j) (fun b => (hf j b).mono hm le_rfl)
      (R.A t) hr.1.1).mul hr.1.2.1
  have hgi (j : Fin K) : Integrable (R.gEst arms t j) P :=
    Integrable.of_bound (hgm j).aestronglyMeasurable C
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hgbound j ω)
  have hsq (x : ℝ) (hx : |x| ≤ C) : |x^2| ≤ C^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_abs x).symm.trans_le ((sq_le_sq₀ (abs_nonneg x) hC0).mpr hx)
  have hgi2 (j : Fin K) : Integrable (fun ω => R.gEst arms t j ω ^ 2) P :=
    Integrable.of_bound (hgm j |>.pow_const 2).aestronglyMeasurable (C^2)
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hsq _ (hgbound j ω))
  have hmeanSum (j : Fin K) (ω : Ω) :
      ∑ b, R.p t ω b * (f j b ω * μ b ω) = (arms j-r ω) ⬝ᵥ R.θs t ω :=
    D15Proof.reconstruction_mean arms (R.p t ω) (hM ω) (arms j-r ω) (R.θs t ω)
  have hμprod (j b : Fin K) (ω : Ω) : |f j b ω * μ b ω| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hμbound b ω) (abs_nonneg _)).trans
      (by simpa using hbound j b ω)
  have hfinite (j : Fin K) :
      Integrable (fun ω => f j (R.A t ω) ω * μ (R.A t ω) ω) P ∧
      P[fun ω => f j (R.A t ω) ω * μ (R.A t ω) ω | R.G t] =ᵐ[P]
        fun ω => ∑ b, R.p t ω b * (f j b ω * μ b ω) :=
    D15Proof.finite_condExp P (R.G t) hm (R.A t) hr.1.1 (R.p t) hr.2.2.1
      (fun b ω => f j b ω * μ b ω) (fun b => (hf j b).mul (hμ b)) C (hμprod j)
  let n : MeasurableSpace Ω := R.G t ⊔ MeasurableSpace.comap (R.A t) inferInstance
  have hmn : R.G t ≤ n := le_sup_left
  have hn : n ≤ mΩ := sup_le hm (measurable_iff_comap_le.mp hr.1.1)
  have hAn : Measurable[n] (R.A t) := measurable_iff_comap_le.mpr le_sup_right
  have hUn (j : Fin K) : Measurable[n] (fun ω => f j (R.A t ω) ω) :=
    @D15Proof.selected_measurable K Ω ℝ n inferInstance (f j)
      (fun b => (hf j b).mono hmn le_rfl) (R.A t) hAn
  have hinner (j : Fin K) : P[R.gEst arms t j | n] =ᵐ[P]
      fun ω => f j (R.A t ω) ω * μ (R.A t ω) ω := by
    have hmul := condExp_mul_of_stronglyMeasurable_left (hUn j).stronglyMeasurable (hgi j) hYi
    filter_upwards [hmul, hr.2.2.2.1.2] with ω hω hyω
    change P[fun ω => f j (R.A t ω) ω * R.Y t ω | n] ω =
      f j (R.A t ω) ω * P[R.Y t | n] ω at hω
    change P[R.Y t | n] ω = μ (R.A t ω) ω at hyω
    exact hω.trans (congrArg (fun y : ℝ => f j (R.A t ω) ω * y) hyω)
  have hmean (j : Fin K) : P[R.gEst arms t j | R.G t] =ᵐ[P]
      fun ω => (arms j-r ω) ⬝ᵥ R.θs t ω := by
    have hce := (condExp_condExp_of_le (f := R.gEst arms t j) hmn hn).symm.trans
      (condExp_congr_ae (hinner j))
    filter_upwards [hce, (hfinite j).2] with ω hω hfω
    exact hω.trans (hfω.trans (hmeanSum j ω))
  have hsecond : P[fun ω => R.gEst arms t a ω ^ 2 | R.G t] ≤ᵐ[P]
      fun ω => beta d K (t+1) + Zd arms (R.cumEst arms t ω) a ^ 2 / (Bc K * (t+1)) := by
    obtain ⟨hSi, hSce⟩ := @D15Proof.finite_condExp K Ω mΩ P _ (R.G t) hm (R.A t) hr.1.1 (R.p t)
      hr.2.2.1 (fun b ω => f a b ω ^ 2) (fun b => (hf a b).pow_const 2) (C^2)
      (fun b ω => hsq _ (hbound a b ω))
    have hdom (ω : Ω) : R.gEst arms t a ω ^ 2 ≤ f a (R.A t ω) ω ^ 2 := by
      change (f a (R.A t ω) ω * R.Y t ω)^2 ≤ _
      rw [mul_pow]
      exact (mul_le_mul_of_nonneg_left ((sq_le_one_iff_abs_le_one _).mpr (hy ω))
        (sq_nonneg _)).trans_eq (mul_one _)
    have hle := condExp_mono (m := R.G t) (hgi2 a) hSi (ae_of_all _ hdom)
    filter_upwards [hle, hSce] with ω hω hsω
    apply hω.trans
    rw [hsω]
    have hv := D15Proof.variance arms (R.p t ω) (hM ω) (arms a-r ω)
    change (∑ b, R.p t ω b * (f a b ω)^2) = _ at hv
    exact hv.trans_le (by
      simpa only [r, BanditAlgorithm.linearAllocationMatrix, Nat.cast_add, Nat.cast_one]
        using (hfeas ω).2.2.2.2.1 a)
  refine ⟨hgi a, hgi2 a, hmean a, ?_, hsecond, ?_⟩
  · have hsub := condExp_sub (hgi a) (hgi c) (R.G t)
    filter_upwards [hsub, hmean a, hmean c] with ω hω haω hcω
    change P[fun ω => R.gEst arms t a ω - R.gEst arms t c ω | R.G t] ω =
      P[R.gEst arms t a | R.G t] ω - P[R.gEst arms t c | R.G t] ω at hω
    rw [haω, hcω] at hω
    exact hω.trans (by simp only [sub_dotProduct]; ring)
  · intro ω
    change |f a (R.A t ω) ω * R.Y t ω| ≤ _
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hy ω) (abs_nonneg _)).trans
      (by simpa only [mul_one] using (hfeas ω).2.2.2.1 a (R.A t ω))
