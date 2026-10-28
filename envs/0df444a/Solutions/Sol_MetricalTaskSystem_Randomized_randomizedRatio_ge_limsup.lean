-- Prove2me | solution 1 for MetricalTaskSystem.Randomized.randomizedRatio_ge_limsup
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T10:13:01.278039+00:00
-- url     : https://prove2.me/submissions/0390f0e1-ae3e-4531-a16b-a8d408560bce

import Definitions.Def_MetricalTaskSystem_Randomized_Model
import Definitions.Def_MetricalTaskSystem_Randomized_RandomizedAlgorithm
import Definitions.Def_MetricalTaskSystem_Randomized_TaskDistribution

open MetricalTaskSystem.Randomized
open MeasureTheory Filter
open scoped ENNReal

private lemma pmf_sum_toReal {S : Type} [Fintype S] (P : PMF S) :
    ∑ s : S, (P s).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun s _ => P.apply_ne_top s)]
  have h1 : ∑ s : S, P s = ∑' s : S, P s := (tsum_fintype (fun s => P s)).symm
  rw [h1, P.tsum_coe, ENNReal.toReal_one]

open Classical in
private noncomputable def updateR {S : Type} (R' : RandomizedOnlineAlgorithm S)
    (q : List (S → ℝ) × List S) (sStar : S) : RandomizedOnlineAlgorithm S :=
  fun s L_T L_S => if (L_T, L_S) = q then PMF.pure sStar else R' s L_T L_S

open Classical in
private lemma schedProb_updateR_sum {S : Type} [Fintype S] [DecidableEq S]
    (R' : RandomizedOnlineAlgorithm S) (s₀ : S) (q : List (S → ℝ) × List S)
    {j : ℕ} (T : Fin j → S → ℝ) (σ : Fin (j + 1) → S) :
    ∑ sStar : S, (R' s₀ q.1 q.2 sStar).toReal * schedProb (updateR R' q sStar) s₀ T σ =
      schedProb R' s₀ T σ := by
  unfold schedProb
  by_cases hσ0 : σ 0 = s₀
  · simp only [if_pos hσ0]
    let qAt (i : Fin j) : List (S → ℝ) × List S :=
      ((List.ofFn T).take (i.val + 1), (List.ofFn σ).take (i.val + 1))
    have hqAt_inj : ∀ i₁ i₂ : Fin j, qAt i₁ = qAt i₂ → i₁ = i₂ := by
      intro i₁ i₂ hq
      have hlen : (qAt i₁).1.length = (qAt i₂).1.length := congrArg (fun p => p.1.length) hq
      dsimp [qAt] at hlen
      rw [List.length_take, List.length_ofFn, Nat.min_eq_left i₁.isLt,
          List.length_take, List.length_ofFn, Nat.min_eq_left i₂.isLt] at hlen
      exact Fin.ext (by omega)
    change (∑ sStar : S, (R' s₀ q.1 q.2 sStar).toReal *
        ∏ i : Fin j, (updateR R' q sStar s₀ (qAt i).1 (qAt i).2 (σ i.succ)).toReal) =
      ∏ i : Fin j, (R' s₀ (qAt i).1 (qAt i).2 (σ i.succ)).toReal
    by_cases hex : ∃ i₀ : Fin j, qAt i₀ = q
    · obtain ⟨i₀, hi₀⟩ := hex
      let rest : ℝ := ∏ i ∈ Finset.univ.erase i₀,
        (R' s₀ (qAt i).1 (qAt i).2 (σ i.succ)).toReal
      have hprod_sStar : ∀ sStar : S,
          (∏ i : Fin j,
            (updateR R' q sStar s₀ (qAt i).1 (qAt i).2 (σ i.succ)).toReal) =
            (if sStar = σ i₀.succ then 1 else 0) * rest := by
        intro sStar
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
        have h_i₀ : (updateR R' q sStar s₀ (qAt i₀).1 (qAt i₀).2 (σ i₀.succ)).toReal =
            if sStar = σ i₀.succ then 1 else 0 := by
          simp only [updateR, if_pos hi₀, PMF.pure_apply]
          by_cases hs : σ i₀.succ = sStar
          · subst hs
            simp
          · have hs' : sStar ≠ σ i₀.succ := Ne.symm hs
            simp [hs, hs']
        have h_rest : (∏ i ∈ Finset.univ.erase i₀,
            (updateR R' q sStar s₀ (qAt i).1 (qAt i).2 (σ i.succ)).toReal) = rest := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have hne_i : i ≠ i₀ := (Finset.mem_erase.mp hi).1
          have hne_q : qAt i ≠ q := by
            intro heq
            exact hne_i (hqAt_inj i i₀ (heq.trans hi₀.symm))
          have h_upd : updateR R' q sStar s₀ (qAt i).1 (qAt i).2 = R' s₀ (qAt i).1 (qAt i).2 := by
            unfold updateR
            exact if_neg hne_q
          rw [h_upd]
        rw [h_i₀, h_rest]
      simp_rw [hprod_sStar]
      have hsum_ite : (∑ sStar : S,
          (R' s₀ q.1 q.2 sStar).toReal * ((if sStar = σ i₀.succ then 1 else 0) * rest)) =
          (R' s₀ q.1 q.2 (σ i₀.succ)).toReal * rest := by
        have h1 : ∀ sStar : S,
            (R' s₀ q.1 q.2 sStar).toReal * ((if sStar = σ i₀.succ then 1 else 0) * rest) =
              if sStar = σ i₀.succ then (R' s₀ q.1 q.2 (σ i₀.succ)).toReal * rest else 0 := by
          intro sStar
          split_ifs with h
          · subst h; ring
          · ring
        simp_rw [h1]
        simp
      rw [hsum_ite, ← hi₀]
      exact Finset.mul_prod_erase Finset.univ
        (fun i : Fin j => (R' s₀ (qAt i).1 (qAt i).2 (σ i.succ)).toReal) (Finset.mem_univ i₀)
    · have hprod_const : ∀ sStar : S,
          (∏ i : Fin j,
            (updateR R' q sStar s₀ (qAt i).1 (qAt i).2 (σ i.succ)).toReal) =
            ∏ i : Fin j, (R' s₀ (qAt i).1 (qAt i).2 (σ i.succ)).toReal := by
        intro sStar
        refine Finset.prod_congr rfl fun i _ => ?_
        have hne_q : qAt i ≠ q := fun heq => hex ⟨i, heq⟩
        have h_upd : updateR R' q sStar s₀ (qAt i).1 (qAt i).2 = R' s₀ (qAt i).1 (qAt i).2 := by
          unfold updateR
          exact if_neg hne_q
        rw [h_upd]
      simp_rw [hprod_const, ← Finset.sum_mul, pmf_sum_toReal, one_mul]
  · simp [hσ0]

private noncomputable def avgCost {S α : Type} [Fintype S] [DecidableEq S] [Fintype α]
    (d : S → S → ℝ) (s₀ : S) (U : α → S → ℝ) {j : ℕ} (p : (Fin j → α) → ℝ)
    (R' : RandomizedOnlineAlgorithm S) : ℝ :=
  ∑ v : (Fin j → α), p v * expCost d R' s₀ (fun i : Fin j => U (v i))

open Classical in
private lemma avgCost_updateR_sum {S α : Type} [Fintype S] [DecidableEq S] [Fintype α]
    (d : S → S → ℝ) (s₀ : S) (U : α → S → ℝ) {j : ℕ} (p : (Fin j → α) → ℝ)
    (R' : RandomizedOnlineAlgorithm S) (q : List (S → ℝ) × List S) :
    ∑ sStar : S, (R' s₀ q.1 q.2 sStar).toReal * avgCost d s₀ U p (updateR R' q sStar) =
      avgCost d s₀ U p R' := by
  unfold avgCost expCost
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h1 : ∀ sStar : S,
      (R' s₀ q.1 q.2 sStar).toReal *
        (p v * (schedProb (updateR R' q sStar) s₀ (fun i => U (v i)) σ *
          schedCost d (fun i => U (v i)) σ)) =
        p v * (((R' s₀ q.1 q.2 sStar).toReal *
          schedProb (updateR R' q sStar) s₀ (fun i => U (v i)) σ) *
          schedCost d (fun i => U (v i)) σ) := by
    intro sStar; ring
  simp_rw [h1, ← Finset.mul_sum, ← Finset.sum_mul, schedProb_updateR_sum]

open Classical in
private lemma exists_updateR_le {S α : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype α]
    (d : S → S → ℝ) (s₀ : S) (U : α → S → ℝ) {j : ℕ} (p : (Fin j → α) → ℝ)
    (R' : RandomizedOnlineAlgorithm S) (q : List (S → ℝ) × List S) :
    ∃ sStar : S, avgCost d s₀ U p (updateR R' q sStar) ≤ avgCost d s₀ U p R' := by
  obtain ⟨sStar, _, hsStar⟩ :=
    Finset.exists_min_image Finset.univ (fun s => avgCost d s₀ U p (updateR R' q s))
      Finset.univ_nonempty
  refine ⟨sStar, ?_⟩
  calc avgCost d s₀ U p (updateR R' q sStar)
      = (∑ s : S, (R' s₀ q.1 q.2 s).toReal) * avgCost d s₀ U p (updateR R' q sStar) := by
        rw [pmf_sum_toReal, one_mul]
    _ = ∑ s : S, (R' s₀ q.1 q.2 s).toReal * avgCost d s₀ U p (updateR R' q sStar) := by
        rw [Finset.sum_mul]
    _ ≤ ∑ s : S, (R' s₀ q.1 q.2 s).toReal * avgCost d s₀ U p (updateR R' q s) := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact mul_le_mul_of_nonneg_left (hsStar s (Finset.mem_univ s)) ENNReal.toReal_nonneg
    _ = avgCost d s₀ U p R' := avgCost_updateR_sum d s₀ U p R' q

open Classical in
private lemma exists_deterministic_on_finset {S α : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype α] (d : S → S → ℝ) (s₀ : S) (U : α → S → ℝ) {j : ℕ} (p : (Fin j → α) → ℝ)
    (R : RandomizedOnlineAlgorithm S) (Q : Finset (List (S → ℝ) × List S)) :
    ∃ (R' : RandomizedOnlineAlgorithm S) (f : List (S → ℝ) → List S → S),
      avgCost d s₀ U p R' ≤ avgCost d s₀ U p R ∧
      ∀ q ∈ Q, R' s₀ q.1 q.2 = PMF.pure (f q.1 q.2) := by
  induction Q using Finset.induction_on with
  | empty =>
    refine ⟨R, fun _ _ => s₀, le_refl _, ?_⟩
    intro q hq
    exact False.elim (Finset.notMem_empty q hq)
  | @insert q Q hq ih =>
    obtain ⟨R₁, f₁, hle₁, hdet₁⟩ := ih
    obtain ⟨sStar, hle₂⟩ := exists_updateR_le d s₀ U p R₁ q
    refine ⟨updateR R₁ q sStar,
      fun L_T L_S => if (L_T, L_S) = q then sStar else f₁ L_T L_S,
      le_trans hle₂ hle₁, ?_⟩
    intro q' hq'
    rcases Finset.mem_insert.mp hq' with rfl | hq'_in
    · simp only [updateR, Prod.mk.eta, ↓reduceIte]
    · have hne : (q'.1, q'.2) ≠ q := by
        rw [Prod.mk.eta]
        exact fun h => hq (h ▸ hq'_in)
      simp only [updateR, if_neg hne, hdet₁ q' hq'_in]

private def stateAt {S : Type} (f : List (S → ℝ) → List S → S) (s₀ : S)
    (L_T : List (S → ℝ)) : ℕ → S
  | 0 => s₀
  | k + 1 => f (L_T.take (k + 1)) (List.ofFn (fun m : Fin (k + 1) => stateAt f s₀ L_T m.val))

private def algOf {S : Type} (f : List (S → ℝ) → List S → S) : OnlineAlgorithm S :=
  fun s₀ L_T => stateAt f s₀ L_T L_T.length

private lemma stateAt_take {S : Type} (f : List (S → ℝ) → List S → S) (s₀ : S)
    (L_T : List (S → ℝ)) (k n : ℕ) (hk : k ≤ n) :
    stateAt f s₀ (L_T.take n) k = stateAt f s₀ L_T k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [stateAt]
    | succ k =>
      rw [stateAt, stateAt, List.take_take, Nat.min_eq_left hk]
      have hfn : (fun m : Fin (k + 1) => stateAt f s₀ (L_T.take n) m.val) =
          (fun m : Fin (k + 1) => stateAt f s₀ L_T m.val) :=
        funext fun m => ih m.val m.isLt (by omega)
      rw [hfn]

private lemma onlineSchedule_algOf {S : Type} (f : List (S → ℝ) → List S → S) (s₀ : S)
    {j : ℕ} (T : Fin j → S → ℝ) (i : Fin (j + 1)) :
    onlineSchedule (algOf f) s₀ T i = stateAt f s₀ (List.ofFn T) i.val := by
  unfold onlineSchedule algOf
  split_ifs with hi
  · rw [hi, stateAt]
  · have hlen : ((List.ofFn T).take i.val).length = i.val := by
      rw [List.length_take, List.length_ofFn, Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)]
    rw [hlen]
    exact stateAt_take f s₀ (List.ofFn T) i.val i.val (le_refl _)

private lemma take_ofFn_eq {S : Type} {j : ℕ} (σ : Fin (j + 1) → S) (k : ℕ) (hk : k ≤ j + 1) :
    (List.ofFn σ).take k = List.ofFn (fun m : Fin k => σ ⟨m.val, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn, Nat.min_eq_left hk]
  · intro m hm₁ hm₂
    simp only [List.getElem_take, List.getElem_ofFn]

private lemma onlineSchedule_algOf_succ {S : Type} (f : List (S → ℝ) → List S → S) (s₀ : S)
    {j : ℕ} (T : Fin j → S → ℝ) (i : Fin j) :
    onlineSchedule (algOf f) s₀ T i.succ =
      f ((List.ofFn T).take (i.val + 1))
        ((List.ofFn (onlineSchedule (algOf f) s₀ T)).take (i.val + 1)) := by
  rw [onlineSchedule_algOf f s₀ T i.succ, Fin.val_succ, stateAt,
      take_ofFn_eq (onlineSchedule (algOf f) s₀ T) (i.val + 1) (by omega)]
  have hfn : (fun m : Fin (i.val + 1) =>
      onlineSchedule (algOf f) s₀ T ⟨m.val, by omega⟩) =
      (fun m : Fin (i.val + 1) => stateAt f s₀ (List.ofFn T) m.val) :=
    funext fun m => onlineSchedule_algOf f s₀ T ⟨m.val, by omega⟩
  rw [hfn]

private lemma eq_stateAt_of_step {S : Type} (f : List (S → ℝ) → List S → S) (s₀ : S)
    {j : ℕ} (T : Fin j → S → ℝ) (σ : Fin (j + 1) → S)
    (h0 : σ 0 = s₀)
    (hstep : ∀ i : Fin j, σ i.succ =
      f ((List.ofFn T).take (i.val + 1)) ((List.ofFn σ).take (i.val + 1))) :
    ∀ k (hk : k ≤ j), σ ⟨k, by omega⟩ = stateAt f s₀ (List.ofFn T) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    cases k with
    | zero =>
      rw [stateAt]
      exact h0
    | succ k =>
      let i : Fin j := ⟨k, hk⟩
      have hi : (⟨k + 1, by omega⟩ : Fin (j + 1)) = i.succ := rfl
      rw [hi, hstep i, take_ofFn_eq σ (i.val + 1) (by omega), stateAt]
      dsimp [i]
      have hfn : (fun m : Fin (k + 1) => σ ⟨m.val, by omega⟩) =
          (fun m : Fin (k + 1) => stateAt f s₀ (List.ofFn T) m.val) :=
        funext fun m => ih m.val m.isLt (by omega)
      rw [hfn]

private lemma expCost_eq_onlineCost_of_det {S : Type} [Fintype S] [DecidableEq S]
    (d : S → S → ℝ) (s₀ : S) {j : ℕ} (T : Fin j → S → ℝ)
    (R' : RandomizedOnlineAlgorithm S) (f : List (S → ℝ) → List S → S)
    (hdet : ∀ (σ : Fin (j + 1) → S) (i : Fin j),
      R' s₀ ((List.ofFn T).take (i.val + 1)) ((List.ofFn σ).take (i.val + 1)) =
        PMF.pure (f ((List.ofFn T).take (i.val + 1)) ((List.ofFn σ).take (i.val + 1)))) :
    expCost d R' s₀ T = onlineCost d (algOf f) s₀ T := by
  unfold expCost onlineCost
  let σStar : Fin (j + 1) → S := onlineSchedule (algOf f) s₀ T
  have hprob : ∀ σ : Fin (j + 1) → S,
      schedProb R' s₀ T σ = if σ = σStar then 1 else 0 := by
    intro σ
    by_cases hσ : σ = σStar
    · subst hσ
      rw [if_pos rfl]
      unfold schedProb
      have h0 : σStar 0 = s₀ := by
        dsimp [σStar, onlineSchedule]
      rw [if_pos h0]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hdet σStar i, PMF.pure_apply, if_pos (onlineSchedule_algOf_succ f s₀ T i),
          ENNReal.toReal_one]
    · rw [if_neg hσ]
      unfold schedProb
      split_ifs with h0
      · have hex_ne : ∃ i : Fin j, σ i.succ ≠
            f ((List.ofFn T).take (i.val + 1)) ((List.ofFn σ).take (i.val + 1)) := by
          by_contra hall
          push Not at hall
          apply hσ
          ext k
          change σ k = onlineSchedule (algOf f) s₀ T k
          rw [onlineSchedule_algOf f s₀ T k]
          exact eq_stateAt_of_step f s₀ T σ h0 hall k.val (Nat.le_of_lt_succ k.isLt)
        obtain ⟨i₀, hi₀⟩ := hex_ne
        refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
        rw [hdet σ i₀, PMF.pure_apply, if_neg hi₀, ENNReal.toReal_zero]
      · rfl
  simp_rw [hprob]
  simp [σStar]

private lemma integral_fin_prefix {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (D : Measure (ℕ → α)) [IsProbabilityMeasure D]
    (j : ℕ) (g : (Fin j → α) → ℝ) :
    ∫ ω, g (fun i : Fin j => ω i) ∂D =
      ∑ v : (Fin j → α), (D.map (fun ω (i : Fin j) => ω i)).real {v} * g v := by
  let proj : (ℕ → α) → (Fin j → α) := fun ω i => ω i
  have hmeas_proj : Measurable proj :=
    measurable_pi_lambda _ (fun i : Fin j => measurable_pi_apply i.val)
  have hmeas_g : AEStronglyMeasurable g (D.map proj) :=
    (Measurable.of_discrete (f := g)).aestronglyMeasurable
  change (∫ ω, g (proj ω) ∂D) = ∑ v : (Fin j → α), (D.map proj).real {v} * g v
  rw [← integral_map hmeas_proj.aemeasurable hmeas_g, integral_fintype (Integrable.of_finite)]
  simp_rw [smul_eq_mul]

private lemma sum_proj_prob {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (D : Measure (ℕ → α)) [IsProbabilityMeasure D] (j : ℕ) :
    ∑ v : (Fin j → α), (D.map (fun ω (i : Fin j) => ω i)).real {v} = 1 := by
  have h := integral_fin_prefix D j (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [← h, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

private lemma schedCost_nonneg {S α : Type} [Fintype S] (d : S → S → ℝ) (hd : IsTaskSystem d)
    (U : α → S → ℝ) (hU : ∀ a s, 0 ≤ U a s) {j : ℕ} (v : Fin j → α) (σ : Fin (j + 1) → S) :
    0 ≤ schedCost d (fun i : Fin j => U (v i)) σ := by
  unfold schedCost
  refine Finset.sum_nonneg fun i _ => ?_
  have hd_nonneg : 0 ≤ d (σ i.castSucc) (σ i.succ) := by
    by_cases h : σ i.castSucc = σ i.succ
    · rw [h, hd.diag]
    · exact le_of_lt (hd.pos _ _ h)
  exact add_nonneg hd_nonneg (hU (v i) (σ i.succ))

open Classical in
private lemma minDetExpCost_le_avgCost {S α : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (U : α → S → ℝ) (hU : ∀ a s, 0 ≤ U a s)
    (D : Measure (ℕ → α)) [IsProbabilityMeasure D] (s₀ : S)
    (R : RandomizedOnlineAlgorithm S) (j : ℕ) :
    minDetExpCost d s₀ U D j ≤
      avgCost d s₀ U (fun v : Fin j → α => (D.map (fun ω (i : Fin j) => ω i)).real {v}) R := by
  let p : (Fin j → α) → ℝ := fun v => (D.map (fun ω (i : Fin j) => ω i)).real {v}
  let Q : Finset (List (S → ℝ) × List S) :=
    (Finset.univ (α := (Fin j → α) × (Fin (j + 1) → S) × Fin j)).image
      (fun ⟨v, σ, i⟩ =>
        ((List.ofFn (fun k : Fin j => U (v k))).take (i.val + 1),
         (List.ofFn σ).take (i.val + 1)))
  obtain ⟨R', f, hle, hdet⟩ := exists_deterministic_on_finset d s₀ U p R Q
  have havg_eq : avgCost d s₀ U p R' = expOnlineCost d (algOf f) s₀ U D j := by
    unfold avgCost expOnlineCost
    have hprefix : ∀ ω : ℕ → α,
        onlineCost d (algOf f) s₀ (prefixTasks U ω j) =
          onlineCost d (algOf f) s₀ (fun i : Fin j => U (ω i)) := fun _ => rfl
    simp_rw [hprefix]
    rw [integral_fin_prefix D j (fun v => onlineCost d (algOf f) s₀ (fun i => U (v i)))]
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    refine expCost_eq_onlineCost_of_det d s₀ (fun i => U (v i)) R' f ?_
    intro σ i
    have hmem : (((List.ofFn (fun k : Fin j => U (v k))).take (i.val + 1),
        (List.ofFn σ).take (i.val + 1))) ∈ Q := by
      refine Finset.mem_image.mpr ⟨⟨v, σ, i⟩, Finset.mem_univ _, rfl⟩
    exact hdet _ hmem
  have hbdd : BddBelow (Set.range (fun A : OnlineAlgorithm S => expOnlineCost d A s₀ U D j)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨A, rfl⟩
    unfold expOnlineCost
    have hprefix : ∀ ω : ℕ → α,
        onlineCost d A s₀ (prefixTasks U ω j) =
          onlineCost d A s₀ (fun i : Fin j => U (ω i)) := fun _ => rfl
    simp_rw [hprefix]
    rw [integral_fin_prefix D j (fun v => onlineCost d A s₀ (fun i => U (v i)))]
    refine Finset.sum_nonneg fun v _ => ?_
    exact mul_nonneg measureReal_nonneg
      (schedCost_nonneg d hd U hU v (onlineSchedule A s₀ (fun i => U (v i))))
  have hmin_le : minDetExpCost d s₀ U D j ≤ expOnlineCost d (algOf f) s₀ U D j :=
    ciInf_le hbdd (algOf f)
  linarith

theorem solution {S α : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (d : S → S → ℝ) (hd : IsTaskSystem d)
    (U : α → S → ℝ) (hU : ∀ a s, 0 ≤ U a s)
    (D : Measure (ℕ → α)) [IsProbabilityMeasure D] (s₀ : S)
    (hE : Tendsto (fun j => expOfflineCost d s₀ U D j) atTop atTop)
    (R : RandomizedOnlineAlgorithm S) (w : ℝ) (hR : IsExpCompetitive d R w) :
    limsup (fun j : ℕ =>
        ((minDetExpCost d s₀ U D j / expOfflineCost d s₀ U D j : ℝ) : EReal)) atTop
      ≤ (w : EReal) := by
  obtain ⟨_, K, hK⟩ := hR
  have hbound : ∀ j : ℕ, minDetExpCost d s₀ U D j ≤ w * expOfflineCost d s₀ U D j + K := by
    intro j
    let p : (Fin j → α) → ℝ := fun v => (D.map (fun ω (i : Fin j) => ω i)).real {v}
    have hmin_le := minDetExpCost_le_avgCost d hd U hU D s₀ R j
    have havg_le : avgCost d s₀ U p R ≤ w * expOfflineCost d s₀ U D j + K := by
      unfold avgCost expOfflineCost
      have hprefix : ∀ ω : ℕ → α,
          offlineOpt d s₀ (prefixTasks U ω j) =
            offlineOpt d s₀ (fun i : Fin j => U (ω i)) := fun _ => rfl
      simp_rw [hprefix]
      rw [integral_fin_prefix D j (fun v => offlineOpt d s₀ (fun i => U (v i)))]
      calc ∑ v : (Fin j → α), p v * expCost d R s₀ (fun i : Fin j => U (v i))
          ≤ ∑ v : (Fin j → α), p v * (w * offlineOpt d s₀ (fun i : Fin j => U (v i)) + K) := by
            refine Finset.sum_le_sum fun v _ => ?_
            exact mul_le_mul_of_nonneg_left
              (hK s₀ j (fun i => U (v i)) (fun i s => hU (v i) s)) measureReal_nonneg
        _ = w * (∑ v : (Fin j → α), p v * offlineOpt d s₀ (fun i : Fin j => U (v i))) +
              (∑ v : (Fin j → α), p v) * K := by
            simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun v _ => by ring
        _ = w * (∑ v : (Fin j → α), p v * offlineOpt d s₀ (fun i : Fin j => U (v i))) + K := by
            rw [sum_proj_prob D j, one_mul]
    exact le_trans hmin_le havg_le
  have h_eps : ∀ ε : ℝ, 0 < ε →
      limsup (fun j : ℕ =>
          ((minDetExpCost d s₀ U D j / expOfflineCost d s₀ U D j : ℝ) : EReal)) atTop
        ≤ ((w + ε : ℝ) : EReal) := by
    intro ε hε
    refine limsup_le_of_le (by isBoundedDefault) ?_
    have hev : ∀ᶠ j : ℕ in atTop,
        max 1 (max K 0 / ε) ≤ expOfflineCost d s₀ U D j :=
      hE.eventually_ge_atTop (max 1 (max K 0 / ε))
    filter_upwards [hev] with j hj
    rw [EReal.coe_le_coe_iff]
    have hEj_ge_one : 1 ≤ expOfflineCost d s₀ U D j := le_trans (le_max_left _ _) hj
    have hEj_pos : 0 < expOfflineCost d s₀ U D j := lt_of_lt_of_le zero_lt_one hEj_ge_one
    have hEj_ge_K : max K 0 / ε ≤ expOfflineCost d s₀ U D j := le_trans (le_max_right _ _) hj
    have hK_le : K ≤ ε * expOfflineCost d s₀ U D j := by
      have h1 : max K 0 ≤ expOfflineCost d s₀ U D j * ε := (div_le_iff₀ hε).mp hEj_ge_K
      have h2 : K ≤ max K 0 := le_max_left K 0
      linarith
    rw [div_le_iff₀ hEj_pos]
    have hbj := hbound j
    linarith
  generalize hL : limsup (fun j : ℕ =>
      ((minDetExpCost d s₀ U D j / expOfflineCost d s₀ U D j : ℝ) : EReal)) atTop = L
  rw [hL] at h_eps
  induction L using EReal.rec with
  | bot => exact bot_le
  | top =>
    have h1 := h_eps 1 zero_lt_one
    exact False.elim (EReal.coe_ne_top (w + 1) (top_le_iff.mp h1))
  | coe r =>
    rw [EReal.coe_le_coe_iff]
    by_contra hlt
    have hr : w < r := not_le.mp hlt
    have h2 := EReal.coe_le_coe_iff.mp (h_eps ((r - w) / 2) (by linarith))
    linarith
