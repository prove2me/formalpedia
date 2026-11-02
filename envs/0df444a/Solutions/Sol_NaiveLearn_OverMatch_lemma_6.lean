-- Prove2me | solution 1 for NaiveLearn.OverMatch.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T13:09:06.037254+00:00
-- url     : https://prove2.me/submissions/e5638a80-cf7b-401d-84b0-7988b1211856

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model
import Theorems.Thm_NaiveLearn_OverMatch_proposition_2
import Theorems.Thm_NaiveLearn_OverMatch_lemma_4
import Theorems.Thm_NaiveLearn_OverMatch_lemma_5

open MeasureTheory ProbabilityTheory Filter Topology
open NaiveLearn.OverMatch

namespace NLode

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma local_exists (g : E → E) (Kg : NNReal) (hg : LipschitzWith Kg g) (B : NNReal)
    (hB : ∀ z, ‖g z‖ ≤ B) (x : E) (n : ℕ) :
    ∃ α : ℝ → E, α 0 = x ∧ ∀ t ∈ Set.Icc (0 : ℝ) n,
      HasDerivWithinAt α (g (α t) - α t) (Set.Icc 0 n) t := by
  set F : ℝ → E → E := fun t w => Real.exp t • g (Real.exp (-t) • w) with hF
  set L : NNReal := ⟨Real.exp n * B, by positivity⟩ with hL
  have ht0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) n := ⟨le_rfl, Nat.cast_nonneg n⟩
  have hlip : ∀ t, LipschitzWith Kg (F t) := by
    intro t
    apply LipschitzWith.of_dist_le_mul
    intro w w'
    simp only [hF]
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
    have := hg.dist_le_mul (Real.exp (-t) • w) (Real.exp (-t) • w')
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-t))] at this
    calc Real.exp t * dist (g (Real.exp (-t) • w)) (g (Real.exp (-t) • w'))
        ≤ Real.exp t * (Kg * (Real.exp (-t) * dist w w')) :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos t).le
      _ = Kg * dist w w' := by
          rw [show Real.exp t * (Kg * (Real.exp (-t) * dist w w')) =
            (Real.exp t * Real.exp (-t)) * (Kg * dist w w') by ring, ← Real.exp_add]
          simp
  have hPL : IsPicardLindelof F (tmin := 0) (tmax := n) ⟨0, ht0⟩ x (L * n) 0 L Kg :=
    { lipschitzOnWith := fun t _ => (hlip t).lipschitzOnWith
      continuousOn := fun w _ => by
        have hc := hg.continuous
        exact (Continuous.smul Real.continuous_exp
          (hc.comp (Continuous.smul (Real.continuous_exp.comp continuous_neg)
            continuous_const))).continuousOn
      norm_le := fun t ht w _ => by
        simp only [hF, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t), hL]
        calc Real.exp t * ‖g (Real.exp (-t) • w)‖ ≤ Real.exp t * B :=
              mul_le_mul_of_nonneg_left (hB _) (Real.exp_pos t).le
          _ ≤ Real.exp n * B := mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.2 ht.2) B.2
      mul_max_le := by
        simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_zero, sub_zero]
        apply le_of_eq
        congr 1
        simp }
  obtain ⟨w, hw0, hw⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨fun t => Real.exp (-t) • w t, by simp [hw0], fun t ht => ?_⟩
  have h1 := ((hasDerivAt_neg t).exp).hasDerivWithinAt (s := Set.Icc (0 : ℝ) n)
  have h2 := h1.fun_smul (hw t ht)
  convert h2 using 1
  show g (Real.exp (-t) • w t) - Real.exp (-t) • w t =
    Real.exp (-t) • (Real.exp t • g (Real.exp (-t) • w t)) + (Real.exp (-t) * -1) • w t
  rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul, mul_neg_one, neg_smul]
  abel

lemma glue (f : E → E) (Kf : NNReal) (hf : LipschitzWith Kf f) (x : E)
    (hloc : ∀ n : ℕ, ∃ α : ℝ → E, α 0 = x ∧ ∀ t ∈ Set.Icc (0 : ℝ) n,
      HasDerivWithinAt α (f (α t)) (Set.Icc 0 n) t) :
    ∃ z : ℝ → E, IsODESolution f z ∧ z 0 = x := by
  choose α hα0 hα using hloc
  -- each α n solves on [0, n] in the sense of right derivatives
  have hright : ∀ n : ℕ, ∀ t ∈ Set.Ico (0 : ℝ) n,
      HasDerivWithinAt (α n) (f (α n t)) (Set.Ici t) t := by
    intro n t ht
    have h := (hα n t ⟨ht.1, ht.2.le⟩).mono (Set.Icc_subset_Icc ht.1 le_rfl)
    exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE ht.2)
  have hcont : ∀ n : ℕ, ContinuousOn (α n) (Set.Icc 0 n) := fun n t ht =>
    (hα n t ht).continuousWithinAt
  -- agreement
  have hagree : ∀ n k : ℕ, n ≤ k → Set.EqOn (α n) (α k) (Set.Icc 0 n) := by
    intro n k hnk
    have hk : Set.Icc (0 : ℝ) n ⊆ Set.Icc 0 k :=
      Set.Icc_subset_Icc le_rfl (Nat.cast_le.2 hnk)
    exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => f) (s := fun _ => Set.univ)
      (K := Kf) (fun _ _ => hf.lipschitzOnWith) (hcont n) (fun t ht => hright n t ht)
      (fun _ _ => trivial) ((hcont k).mono hk)
      (fun t ht => hright k t ⟨ht.1, lt_of_lt_of_le ht.2 (Nat.cast_le.2 hnk)⟩)
      (fun _ _ => trivial) (by rw [hα0, hα0])
  set z : ℝ → E := fun t => α (⌈t⌉₊ + 1) t with hz
  have hzeq : ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) n, z t = α n t := by
    intro n t ht
    simp only [hz]
    rcases le_total (⌈t⌉₊ + 1) n with h | h
    · exact hagree _ _ h ⟨ht.1, by
        have := Nat.le_ceil t
        push_cast; linarith⟩
    · exact (hagree _ _ h ht).symm
  have hlt : ∀ t : ℝ, t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by
    intro t; push_cast; linarith [Nat.le_ceil t]
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    set n := ⌈t⌉₊ + 1
    have h1 : ContinuousWithinAt (α n) (Set.Icc 0 n) t := hcont n t ⟨ht, (hlt t).le⟩
    have h2 : ContinuousWithinAt z (Set.Icc 0 n) t :=
      h1.congr (fun s hs => hzeq n s hs) (hzeq n t ⟨ht, (hlt t).le⟩)
    have hmem : Set.Icc (0 : ℝ) n ∈ 𝓝[Set.Ici 0] t := by
      rw [Set.mem_Ici] at ht
      have : Set.Icc (0 : ℝ) n = Set.Ici 0 ∩ Set.Iic (n : ℝ) := by
        ext s; simp [Set.mem_Icc]
      rw [this]
      exact inter_mem_nhdsWithin _ (Iic_mem_nhds (hlt t))
    exact h2.mono_of_mem_nhdsWithin hmem
  · intro t ht
    set n := ⌈t⌉₊ + 1
    have h1 := hright n t ⟨ht, hlt t⟩
    have hmem : Set.Icc t (n : ℝ) ∈ 𝓝[Set.Ici t] t := Icc_mem_nhdsGE (hlt t)
    have h2 := (h1.mono (Set.Icc_subset_Ici_self)).congr_of_mem
      (fun s hs => hzeq n s ⟨ht.trans hs.1, hs.2⟩) ⟨le_rfl, (hlt t).le⟩
    rw [hzeq n t ⟨ht, (hlt t).le⟩]
    exact h2.mono_of_mem_nhdsWithin hmem
  · simp [hz, hα0]

end NLode

namespace NL6

lemma actOf_cases (σ : ℝ → ℝ) (u : unitInterval) (y : ℝ) :
    actOf σ u y = 0 ∨ actOf σ u y = 1 := by
  unfold actOf; split_ifs <;> simp

lemma actOf_mem (σ : ℝ → ℝ) (u : unitInterval) (y : ℝ) :
    actOf σ u y ∈ Set.Icc (0 : ℝ) 1 := by
  rcases actOf_cases σ u y with h | h <;> rw [h] <;> simp

lemma bel_succ {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (U : Coins m) (t : ℕ) (i : Fin m) :
    beliefAct σ ε W x1 U (t + 1) i =
      (1 - ε) * beliefAct σ ε W x1 U t i +
        ε * ∑ j, W i j * actOf σ (U t j) (beliefAct σ ε W x1 U t j) := by
  simp [beliefAct, Matrix.mulVec, dotProduct]

lemma wsum_mem {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (a : Fin m → ℝ) (ha : ∀ j, a j ∈ Set.Icc (0 : ℝ) 1) (i : Fin m) :
    ∑ j, W i j * a j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (Matrix.nonneg_of_mem_rowStochastic hW) (ha j).1
  · calc ∑ j, W i j * a j ≤ ∑ j, W i j * 1 := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (ha j).2 (Matrix.nonneg_of_mem_rowStochastic hW)
      _ = 1 := by simp [Matrix.sum_row_of_mem_rowStochastic hW]

lemma bel_mem {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (x1 : Fin m → ℝ) (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (U : Coins m) :
    ∀ t i, beliefAct σ ε W x1 U t i ∈ Set.Icc (0 : ℝ) 1 := by
  intro t
  induction t with
  | zero => exact hx1
  | succ t ih =>
    intro i
    rw [bel_succ]
    have h1 := ih i
    have h2 := wsum_mem W hW (fun j => actOf σ (U t j) (beliefAct σ ε W x1 U t j))
      (fun j => actOf_mem σ (U t j) _) i
    obtain ⟨hε0, hε1⟩ := hε
    constructor
    · nlinarith [h1.1, h2.1]
    · nlinarith [h1.2, h2.2]

lemma bel_congr_sigma {m : ℕ} (σ σ' : ℝ → ℝ) (hσ : ∀ y ∈ Set.Icc (0 : ℝ) 1, σ y = σ' y)
    (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (x1 : Fin m → ℝ) (hx1 : ∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) (U : Coins m) :
    ∀ t, beliefAct σ ε W x1 U t = beliefAct σ' ε W x1 U t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm := bel_mem σ ε hε W hW x1 hx1 U t
    have hact : (fun j => actOf σ (U t j) (beliefAct σ ε W x1 U t j)) =
        (fun j => actOf σ' (U t j) (beliefAct σ' ε W x1 U t j)) := by
      funext j
      rw [← ih]
      unfold actOf
      rw [hσ _ (hm j)]
    simp only [beliefAct]
    rw [hact, ih]

lemma bel_restart {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (U : Coins m) (N : ℕ) :
    ∀ k, beliefAct σ ε W x1 U (N + k) =
      beliefAct σ ε W (beliefAct σ ε W x1 U N) (fun t => U (N + t)) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc]
    simp only [beliefAct]
    rw [ih]

lemma bel_prefix {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (U U' : Coins m) (N : ℕ) (h : ∀ t < N, U t = U' t) :
    ∀ k ≤ N, beliefAct σ ε W x1 U k = beliefAct σ ε W x1 U' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    simp only [beliefAct]
    rw [ih (by omega), h k (by omega)]

lemma actOf_meas (σ : ℝ → ℝ) (hσ : Measurable σ) :
    Measurable (fun q : unitInterval × ℝ => actOf σ q.1 q.2) := by
  unfold actOf
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt (measurable_subtype_coe.comp measurable_fst) (hσ.comp measurable_snd)

lemma bel_meas {m : ℕ} (σ : ℝ → ℝ) (hσ : Measurable σ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (t : ℕ) : Measurable (fun q : (Fin m → ℝ) × Coins m => beliefAct σ ε W q.1 q.2 t) := by
  induction t with
  | zero => exact measurable_fst
  | succ t ih =>
    simp only [beliefAct]
    have ha : Measurable (fun q : (Fin m → ℝ) × Coins m =>
        fun j => actOf σ (q.2 t j) (beliefAct σ ε W q.1 q.2 t j)) := by
      refine measurable_pi_lambda _ fun j => ?_
      exact (actOf_meas σ hσ).comp (Measurable.prodMk
        ((measurable_pi_apply j).comp ((measurable_pi_apply t).comp measurable_snd))
        ((measurable_pi_apply j).comp ih))
    exact (ih.const_smul (1 - ε)).add ((Continuous.measurable (by fun_prop :
      Continuous (fun v : Fin m → ℝ => ε • W.mulVec v))).comp ha)


lemma coupling_up {m : ℕ} (p : ℝ) (σ : ℝ → ℝ) (hσup : ∀ x ∈ Set.Ioc p 1, x ≤ σ x)
    (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (x0 y0 : Fin m → ℝ) (hx0 : ∀ i, x0 i ∈ Set.Icc (0 : ℝ) 1) (hxy : ∀ i, y0 i ≤ x0 i)
    (V : Coins m) (hy : ∀ t i, p < beliefAct id ε W y0 V t i) :
    ∀ t i, beliefAct id ε W y0 V t i ≤ beliefAct σ ε W x0 V t i := by
  intro t
  induction t with
  | zero => exact hxy
  | succ t ih =>
    intro i
    rw [bel_succ, bel_succ]
    have hxm := bel_mem σ ε hε W hW x0 hx0 V t
    have hact : ∀ j, actOf id (V t j) (beliefAct id ε W y0 V t j) ≤
        actOf σ (V t j) (beliefAct σ ε W x0 V t j) := by
      intro j
      have h1 := hy t j
      have h2 := ih j
      have h3 : beliefAct σ ε W x0 V t j ≤ σ (beliefAct σ ε W x0 V t j) :=
        hσup _ ⟨lt_of_lt_of_le h1 h2, (hxm j).2⟩
      unfold actOf
      split_ifs with ha hb hb
      · exact le_rfl
      · exfalso; apply hb; simp only [id] at ha; linarith
      · norm_num
      · exact le_rfl
    have hsum : ∑ j, W i j * actOf id (V t j) (beliefAct id ε W y0 V t j) ≤
        ∑ j, W i j * actOf σ (V t j) (beliefAct σ ε W x0 V t j) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hact j) (Matrix.nonneg_of_mem_rowStochastic hW)
    obtain ⟨hε0, hε1⟩ := hε
    have := ih i
    nlinarith

lemma coupling_down {m : ℕ} (p : ℝ) (σ : ℝ → ℝ) (hσdn : ∀ x ∈ Set.Ico 0 p, σ x ≤ x)
    (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (x0 y0 : Fin m → ℝ) (hx0 : ∀ i, x0 i ∈ Set.Icc (0 : ℝ) 1) (hxy : ∀ i, x0 i ≤ y0 i)
    (V : Coins m) (hy : ∀ t i, beliefAct id ε W y0 V t i < p) :
    ∀ t i, beliefAct σ ε W x0 V t i ≤ beliefAct id ε W y0 V t i := by
  intro t
  induction t with
  | zero => exact hxy
  | succ t ih =>
    intro i
    rw [bel_succ, bel_succ]
    have hxm := bel_mem σ ε hε W hW x0 hx0 V t
    have hact : ∀ j, actOf σ (V t j) (beliefAct σ ε W x0 V t j) ≤
        actOf id (V t j) (beliefAct id ε W y0 V t j) := by
      intro j
      have h1 := hy t j
      have h2 := ih j
      have h3 : σ (beliefAct σ ε W x0 V t j) ≤ beliefAct σ ε W x0 V t j :=
        hσdn _ ⟨(hxm j).1, lt_of_le_of_lt h2 h1⟩
      unfold actOf
      split_ifs with ha hb hb
      · exact le_rfl
      · exfalso; apply hb; simp only [id]; linarith
      · norm_num
      · exact le_rfl
    have hsum : ∑ j, W i j * actOf σ (V t j) (beliefAct σ ε W x0 V t j) ≤
        ∑ j, W i j * actOf id (V t j) (beliefAct id ε W y0 V t j) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hact j) (Matrix.nonneg_of_mem_rowStochastic hW)
    obtain ⟨hε0, hε1⟩ := hε
    have := ih i
    nlinarith

lemma sigma_up (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : ℝ → ℝ)
    (hcont : ContinuousOn σ (Set.Icc 0 1)) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (hgt : ∀ x ∈ Set.Ioo p 1, x < σ x) : ∀ x ∈ Set.Ioc p 1, x ≤ σ x := by
  rintro x ⟨hx1, hx2⟩
  rcases lt_or_eq_of_le hx2 with h | h
  · exact (hgt x ⟨hx1, h⟩).le
  · subst h
    have hc : ContinuousWithinAt σ (Set.Ioo p 1) 1 :=
      (hcont.continuousWithinAt ⟨zero_le_one, le_rfl⟩).mono
        (Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc hp0.le le_rfl))
    have ht : Tendsto σ (𝓝[<] (1 : ℝ)) (𝓝 (σ 1)) := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hx1]; exact hc.tendsto
    have hev : ∀ᶠ y in 𝓝[<] (1 : ℝ), y ≤ σ y := by
      filter_upwards [Ioo_mem_nhdsLT hx1] with y hy using (hgt y hy).le
    exact le_of_tendsto_of_tendsto (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) ht hev

lemma sigma_dn (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : ℝ → ℝ)
    (hcont : ContinuousOn σ (Set.Icc 0 1)) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (hlt : ∀ x ∈ Set.Ioo 0 p, σ x < x) : ∀ x ∈ Set.Ico 0 p, σ x ≤ x := by
  rintro x ⟨hx1, hx2⟩
  rcases lt_or_eq_of_le hx1 with h | h
  · exact (hlt x ⟨h, hx2⟩).le
  · subst h
    have hc : ContinuousWithinAt σ (Set.Ioo 0 p) 0 :=
      (hcont.continuousWithinAt ⟨le_rfl, zero_le_one⟩).mono
        (Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hp1.le))
    have ht : Tendsto σ (𝓝[>] (0 : ℝ)) (𝓝 (σ 0)) := by
      rw [← nhdsWithin_Ioo_eq_nhdsGT hx2]; exact hc.tendsto
    have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), σ y ≤ y := by
      filter_upwards [Ioo_mem_nhdsGT hx2] with y hy using (hlt y hy).le
    exact le_of_tendsto_of_tendsto ht (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) hev


/-- Concatenate a block of `N` coin vectors with a coin sequence. -/
def join {m : ℕ} (N : ℕ) (q : (Fin N → Fin m → unitInterval) × Coins m) : Coins m :=
  fun t => if h : t < N then q.1 ⟨t, h⟩ else q.2 (t - N)

/-- Split a coin sequence into its first `N` coin vectors and the shifted remainder. -/
def split {m : ℕ} (N : ℕ) (U : Coins m) : (Fin N → Fin m → unitInterval) × Coins m :=
  (fun k => U k, fun t => U (N + t))

lemma join_split {m : ℕ} (N : ℕ) (U : Coins m) : join N (split N U) = U := by
  funext t
  unfold join split
  split_ifs with h
  · rfl
  · simp only; congr 1; omega

lemma measurable_join {m : ℕ} (N : ℕ) : Measurable (join (m := m) N) := by
  refine measurable_pi_lambda _ fun t => ?_
  unfold join
  by_cases h : t < N
  · simp only [h, dif_pos]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [h, dif_neg, not_false_eq_true]
    exact (measurable_pi_apply _).comp measurable_snd

lemma measurable_split {m : ℕ} (N : ℕ) : Measurable (split (m := m) N) := by
  unfold split
  exact Measurable.prodMk (measurable_pi_lambda _ fun k => measurable_pi_apply _)
    (measurable_pi_lambda _ fun t => measurable_pi_apply _)

/-- The law of the coin vector of one period. -/
noncomputable abbrev cv (m : ℕ) : Measure (Fin m → unitInterval) :=
  Measure.pi (fun _ : Fin m => (volume : Measure unitInterval))

lemma map_join {m : ℕ} (N : ℕ) :
    ((Measure.pi fun _ : Fin N => cv m).prod (coinLaw m)).map (join N) = coinLaw m := by
  classical
  unfold coinLaw
  apply Measure.eq_infinitePi
  intro s t ht
  have hinj : Set.InjOn (fun j : ℕ => N + j) ((fun j : ℕ => N + j) ⁻¹' ↑s) :=
    fun a _ b _ hab => by simpa using hab
  set box1 : Set (Fin N → Fin m → unitInterval) :=
    Set.univ.pi (fun k : Fin N => if (k : ℕ) ∈ s then t k else Set.univ)
  set box2 : Set (Coins m) := Set.pi ↑(s.preimage (fun j : ℕ => N + j) hinj)
    (fun j => t (N + j))
  have hpre : join N ⁻¹' (Set.pi ↑s t) = box1 ×ˢ box2 := by
    ext ⟨a, V⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, box1, box2,
      Set.mem_univ, true_implies, Finset.mem_preimage]
    constructor
    · intro h
      refine ⟨fun k => ?_, fun j hj => ?_⟩
      · split_ifs with hk
        · have := h k hk
          unfold join at this
          simpa [k.2] using this
        · trivial
      · have := h (N + j) hj
        unfold join at this
        simpa using this
    · rintro ⟨h1, h2⟩ i hi
      unfold join
      split_ifs with hiN
      · have := h1 ⟨i, hiN⟩
        simpa [hi] using this
      · have := h2 (i - N) (by rw [show N + (i - N) = i by omega]; exact hi)
        rw [show N + (i - N) = i by omega] at this
        exact this
  rw [Measure.map_apply (measurable_join N) (MeasurableSet.pi s.countable_toSet
    (fun i _ => ht i)), hpre, Measure.prod_prod, Measure.pi_pi,
    Measure.infinitePi_pi _ (fun i _ => ht _)]
  have e1 : ∏ k : Fin N, (cv m) (if (k : ℕ) ∈ s then t k else Set.univ) =
      ∏ i ∈ s with i < N, (cv m) (t i) := by
    have : ∀ k : Fin N, (cv m) (if (k : ℕ) ∈ s then t k else Set.univ) =
        (fun i : ℕ => if i ∈ s then (cv m) (t i) else 1) k := by
      intro k; by_cases hk : (k : ℕ) ∈ s <;> simp [hk]
    rw [Finset.prod_congr rfl (fun k _ => this k), Fin.prod_univ_eq_prod_range
      (fun i : ℕ => if i ∈ s then (cv m) (t i) else 1) N, ← Finset.prod_filter]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext i; simp [and_comm]
  have e2 : ∏ j ∈ s.preimage (fun j : ℕ => N + j) hinj, (cv m) (t (N + j)) =
      ∏ i ∈ s with ¬ i < N, (cv m) (t i) := by
    rw [Finset.prod_preimage' (fun j : ℕ => N + j) s hinj (fun i => (cv m) (t i))]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, Set.mem_range, not_lt]
    constructor
    · rintro ⟨h1, j, rfl⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, i - N, by omega⟩
  rw [e1, e2, Finset.prod_filter_mul_prod_filter_not]

/-- Markov splitting of the coin law at time `N`. -/
lemma coinLaw_split {m : ℕ} (N : ℕ) (S : Set ((Fin N → Fin m → unitInterval) × Coins m))
    (hS : MeasurableSet S) :
    coinLaw m (split N ⁻¹' S) = ((Measure.pi fun _ : Fin N => cv m).prod (coinLaw m)) S := by
  conv_lhs => rw [← map_join N]
  rw [Measure.map_apply (measurable_join N) ((measurable_split N) hS)]
  congr 1
  ext ⟨a, V⟩
  simp only [Set.mem_preimage]
  have : split N (join N (a, V)) = (a, V) := by
    unfold split join
    ext k
    · simp [k.2]
    · simp
  rw [this]


instance coinLaw_prob (m : ℕ) : IsProbabilityMeasure (coinLaw m) := by
  unfold coinLaw; infer_instance

lemma bel_join_indep {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (N : ℕ) (a : Fin N → Fin m → unitInterval) (V V' : Coins m) :
    beliefAct σ ε W x1 (join N (a, V)) N = beliefAct σ ε W x1 (join N (a, V')) N := by
  apply bel_prefix σ ε W x1 _ _ N _ N le_rfl
  intro t ht
  unfold join
  simp [ht]

/-- Markov lower bound: if from every good state the event `A` has probability at least `c`,
then the probability of being in a good state at time `N` and then seeing `A` (with the shifted
coins) is at least `c` times the probability of being good at time `N`. -/
lemma markov_bound {m : ℕ} (σ : ℝ → ℝ) (hσ : Measurable σ) (ε : ℝ)
    (W : Matrix (Fin m) (Fin m) ℝ) (x1 : Fin m → ℝ) (N : ℕ)
    (Good : Set (Fin m → ℝ)) (hGood : MeasurableSet Good)
    (A : Set ((Fin m → ℝ) × Coins m)) (hA : MeasurableSet A) (c : ENNReal)
    (hc : ∀ y ∈ Good, c ≤ coinLaw m {V | (y, V) ∈ A}) :
    c * coinLaw m {U | beliefAct σ ε W x1 U N ∈ Good} ≤
      coinLaw m {U | beliefAct σ ε W x1 U N ∈ Good ∧
        (beliefAct σ ε W x1 U N, fun t => U (N + t)) ∈ A} := by
  set g : Coins m → (Fin m → ℝ) := fun U => beliefAct σ ε W x1 U N with hg
  have hgm : Measurable g :=
    (bel_meas σ hσ ε W N).comp (Measurable.prodMk measurable_const measurable_id)
  set μN : Measure (Fin N → Fin m → unitInterval) := Measure.pi fun _ : Fin N => cv m
  set S : Set ((Fin N → Fin m → unitInterval) × Coins m) :=
    {q | g (join N q) ∈ Good ∧ (g (join N q), q.2) ∈ A}
  have hgj : Measurable (fun q : (Fin N → Fin m → unitInterval) × Coins m => g (join N q)) :=
    hgm.comp (measurable_join N)
  have hSm : MeasurableSet S :=
    (hgj hGood).inter (hA.preimage (Measurable.prodMk hgj measurable_snd))
  set S' : Set ((Fin N → Fin m → unitInterval) × Coins m) := {q | g (join N q) ∈ Good}
  have hS'm : MeasurableSet S' := hgj hGood
  have e1 : split N ⁻¹' S = {U | beliefAct σ ε W x1 U N ∈ Good ∧
        (beliefAct σ ε W x1 U N, fun t => U (N + t)) ∈ A} := by
    ext U; simp only [S, Set.mem_preimage, Set.mem_setOf_eq, join_split]; rfl
  have e2 : split N ⁻¹' S' = {U | beliefAct σ ε W x1 U N ∈ Good} := by
    ext U; simp only [S', Set.mem_preimage, Set.mem_setOf_eq, join_split]; rfl
  let V0 : Coins m := fun _ _ => 0
  set h : (Fin N → Fin m → unitInterval) → (Fin m → ℝ) := fun a => g (join N (a, V0))
  have hhm : Measurable h := hgj.comp (Measurable.prodMk measurable_id measurable_const)
  have hgh : ∀ a V, g (join N (a, V)) = h a := fun a V => bel_join_indep σ ε W x1 N a V V0
  rw [← e1, ← e2, coinLaw_split N S hSm, coinLaw_split N S' hS'm,
    Measure.prod_apply hSm, Measure.prod_apply hS'm]
  have hsec' : ∀ a, coinLaw m (Prod.mk a ⁻¹' S') = (h ⁻¹' Good).indicator (fun _ => 1) a := by
    intro a
    by_cases ha : h a ∈ Good
    · rw [Set.indicator_of_mem (show a ∈ h ⁻¹' Good from ha)]
      have : Prod.mk a ⁻¹' S' = Set.univ := by
        ext V; simp [S', hgh, ha]
      rw [this, measure_univ]
    · rw [Set.indicator_of_notMem (show a ∉ h ⁻¹' Good from ha)]
      have : Prod.mk a ⁻¹' S' = ∅ := by
        ext V; simp [S', hgh, ha]
      rw [this, measure_empty]
  simp_rw [hsec']
  rw [lintegral_indicator_const (hhm hGood), one_mul, ← lintegral_indicator_const (hhm hGood)]
  refine lintegral_mono fun a => ?_
  by_cases ha : h a ∈ Good
  · rw [Set.indicator_of_mem (show a ∈ h ⁻¹' Good from ha)]
    refine (hc _ ha).trans (measure_mono fun V hV => ?_)
    simp only [Set.mem_setOf_eq] at hV
    simp only [S, Set.mem_preimage, Set.mem_setOf_eq, hgh]
    exact ⟨ha, hV⟩
  · rw [Set.indicator_of_notMem (show a ∉ h ⁻¹' Good from ha)]; exact bot_le


lemma meanField_lip {m : ℕ} (σ : ℝ → ℝ) (K : NNReal) (hσlip : LipschitzOnWith K σ (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) :
    LipschitzWith (K + 1) (meanField σ W) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  have hd0 : 0 ≤ dist z z' := dist_nonneg
  have hc : ∀ j, |σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)) -
      σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j))| ≤ K * dist z z' := by
    intro j
    have h1 := hσlip.dist_le_mul _ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)).2 _
      (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j)).2
    rw [Real.dist_eq, Real.dist_eq] at h1
    have h2 := Set.abs_projIcc_sub_projIcc (a := (0 : ℝ)) (b := 1) zero_le_one
      (c := z j) (d := z' j)
    have h3 : |z j - z' j| ≤ dist z z' := by
      rw [← Real.dist_eq]; exact dist_le_pi_dist z z' j
    calc _ ≤ (K : ℝ) * |(Set.projIcc (0 : ℝ) 1 zero_le_one (z j) : ℝ) -
          (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j) : ℝ)| := h1
      _ ≤ K * dist z z' := by
          apply mul_le_mul_of_nonneg_left (h2.trans h3) K.2
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  simp only [meanField, Pi.sub_apply, Matrix.mulVec, dotProduct, Real.dist_eq]
  have hsum : |∑ j, W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)) -
      ∑ j, W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j))| ≤ K * dist z z' := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ j, |W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)) -
          W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, W i j * (K * dist z z') := by
          apply Finset.sum_le_sum; intro j _
          rw [← mul_sub, abs_mul, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hW)]
          exact mul_le_mul_of_nonneg_left (hc j) (Matrix.nonneg_of_mem_rowStochastic hW)
      _ = K * dist z z' := by
          rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hW, one_mul]
  have hzi : |z i - z' i| ≤ dist z z' := by
    rw [← Real.dist_eq]; exact dist_le_pi_dist z z' i
  calc _ = |(∑ j, W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)) -
        ∑ j, W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j))) - (z i - z' i)| := by
        congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ K * dist z z' + dist z z' := add_le_add hsum hzi
    _ = ((K + 1 : NNReal) : ℝ) * dist z z' := by push_cast; ring

lemma uniform_time {m : ℕ} (f : (Fin m → ℝ) → (Fin m → ℝ)) (L : NNReal) (hf : LipschitzWith L f)
    (Kset : Set (Fin m → ℝ)) (hK : IsCompact Kset) (c : Fin m → ℝ)
    (hex : ∀ x ∈ Kset, ∃ z, IsODESolution f z ∧ z 0 = x)
    (hconv : ∀ x ∈ Kset, ∀ z, IsODESolution f z → z 0 = x → Tendsto z atTop (𝓝 c))
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ T, 0 ≤ T ∧ ∀ y ∈ Kset, ∀ z, IsODESolution f z → z 0 = y →
      ∃ s ∈ Set.Icc 0 T, dist (z s) c < ρ := by
  have key : ∀ x ∈ Kset, ∃ T r : ℝ, 0 ≤ T ∧ 0 < r ∧ ∀ y ∈ Kset, dist y x < r →
      ∀ z, IsODESolution f z → z 0 = y → dist (z T) c < ρ := by
    intro x hx
    obtain ⟨zx, hzx, hzx0⟩ := hex x hx
    have hev := (hconv x hx zx hzx hzx0).eventually (Metric.ball_mem_nhds c (half_pos hρ))
    obtain ⟨T0, hT0⟩ := eventually_atTop.1 hev
    set T := max T0 0
    refine ⟨T, ρ / 2 * Real.exp (-(L * T)), le_max_right _ _, by positivity, ?_⟩
    intro y hy hdy z hz hz0
    have hG := dist_le_of_trajectories_ODE (v := fun _ => f) (K := L) (a := 0) (b := T)
      (δ := dist y x) (fun _ => hf)
      (hz.1.mono (Set.Icc_subset_Ici_self)) (fun t ht => hz.2 t ht.1)
      (hzx.1.mono (Set.Icc_subset_Ici_self)) (fun t ht => hzx.2 t ht.1)
      (by rw [hz0, hzx0]) T ⟨le_max_right _ _, le_rfl⟩
    have h1 : dist (z T) (zx T) < ρ / 2 := by
      calc dist (z T) (zx T) ≤ dist y x * Real.exp (L * (T - 0)) := hG
        _ < ρ / 2 * Real.exp (-(L * T)) * Real.exp (L * (T - 0)) := by
            apply mul_lt_mul_of_pos_right hdy (Real.exp_pos _)
        _ = ρ / 2 := by rw [sub_zero, mul_assoc, ← Real.exp_add]; simp
    have h2 : dist (zx T) c < ρ / 2 := hT0 T (le_max_left _ _)
    calc dist (z T) c ≤ dist (z T) (zx T) + dist (zx T) c := dist_triangle _ _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add h1 h2
      _ = ρ := by ring
  choose! T r hT hr H using key
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (r x))
    (fun x hx => Metric.ball_mem_nhds x (hr x hx))
  refine ⟨∑ x ∈ t, T x, Finset.sum_nonneg fun x hx => hT x (htK x hx), ?_⟩
  intro y hy z hz hz0
  have := hcover hy
  simp only [Set.mem_iUnion, Metric.mem_ball] at this
  obtain ⟨x, hxt, hyx⟩ := this
  refine ⟨T x, ⟨hT x (htK x hxt), ?_⟩, H x (htK x hxt) y hy hyx z hz hz0⟩
  exact Finset.single_le_sum (fun x hx => hT x (htK x hx)) hxt


lemma measurableSet_A1 {m : ℕ} (p ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) :
    MeasurableSet {q : (Fin m → ℝ) × Coins m |
      Tendsto (fun t => beliefAct id ε W q.1 q.2 t) atTop (𝓝 1) ∧
        ∀ t i, p < beliefAct id ε W q.1 q.2 t i} := by
  have h1 : MeasurableSet {q : (Fin m → ℝ) × Coins m |
      Tendsto (fun t => beliefAct id ε W q.1 q.2 t) atTop (𝓝 1)} :=
    measurableSet_tendsto (𝓝 1) (fun t => bel_meas id measurable_id ε W t)
  have h2 : MeasurableSet (⋂ t, ⋂ i, {q : (Fin m → ℝ) × Coins m |
      p < beliefAct id ε W q.1 q.2 t i}) :=
    MeasurableSet.iInter fun t => MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const ((measurable_pi_apply i).comp (bel_meas id measurable_id ε W t))
  have e : {q : (Fin m → ℝ) × Coins m |
      Tendsto (fun t => beliefAct id ε W q.1 q.2 t) atTop (𝓝 1) ∧
        ∀ t i, p < beliefAct id ε W q.1 q.2 t i} =
      {q : (Fin m → ℝ) × Coins m | Tendsto (fun t => beliefAct id ε W q.1 q.2 t) atTop (𝓝 1)} ∩
      (⋂ t, ⋂ i, {q : (Fin m → ℝ) × Coins m | p < beliefAct id ε W q.1 q.2 t i}) := by
    ext q; simp
  rw [e]; exact h1.inter h2

lemma measurableSet_A0 {m : ℕ} (p ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) :
    MeasurableSet {q : (Fin m → ℝ) × Coins m |
      Tendsto (fun t => beliefAct id ε W q.1 q.2 t) atTop (𝓝 0) ∧
        ∀ t i, beliefAct id ε W q.1 q.2 t i < p} := by
  have h1 : MeasurableSet {q : (Fin m → ℝ) × Coins m |
      Tendsto (fun t => beliefAct id ε W q.1 q.2 t) atTop (𝓝 0)} :=
    measurableSet_tendsto (𝓝 0) (fun t => bel_meas id measurable_id ε W t)
  have h2 : MeasurableSet (⋂ t, ⋂ i, {q : (Fin m → ℝ) × Coins m |
      beliefAct id ε W q.1 q.2 t i < p}) :=
    MeasurableSet.iInter fun t => MeasurableSet.iInter fun i =>
      measurableSet_lt ((measurable_pi_apply i).comp (bel_meas id measurable_id ε W t)) measurable_const
  have e : {q : (Fin m → ℝ) × Coins m |
      Tendsto (fun t => beliefAct id ε W q.1 q.2 t) atTop (𝓝 0) ∧
        ∀ t i, beliefAct id ε W q.1 q.2 t i < p} =
      {q : (Fin m → ℝ) × Coins m | Tendsto (fun t => beliefAct id ε W q.1 q.2 t) atTop (𝓝 0)} ∩
      (⋂ t, ⋂ i, {q : (Fin m → ℝ) × Coins m | beliefAct id ε W q.1 q.2 t i < p}) := by
    ext q; simp
  rw [e]; exact h1.inter h2

lemma isCompact_K {m : ℕ} (μ : Fin m → ℝ) (P : ℝ → Prop) (hP : IsClosed {v : ℝ | P v}) :
    IsCompact {x : Fin m → ℝ | (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧ P (∑ i, μ i * x i)} := by
  have h1 : IsClosed (⋂ i, (fun x : Fin m → ℝ => x i) ⁻¹' Set.Icc (0 : ℝ) 1) :=
    isClosed_iInter fun i => isClosed_Icc.preimage (continuous_apply i)
  have h2 : IsClosed ((fun x : Fin m → ℝ => ∑ i, μ i * x i) ⁻¹' {v : ℝ | P v}) :=
    hP.preimage (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))
  have e : {x : Fin m → ℝ | (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧ P (∑ i, μ i * x i)} =
      (⋂ i, (fun x : Fin m → ℝ => x i) ⁻¹' Set.Icc (0 : ℝ) 1) ∩
        ((fun x : Fin m → ℝ => ∑ i, μ i * x i) ⁻¹' {v : ℝ | P v}) := by
    ext x; simp
  rw [e]
  apply IsCompact.of_isClosed_subset (isCompact_univ_pi
    (fun _ : Fin m => (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)))) (h1.inter h2)
  intro x hx
  exact Set.mem_univ_pi.2 (by simpa using hx.1)

lemma sigc_meas (σ : ℝ → ℝ) (hc : ContinuousOn σ (Set.Icc 0 1)) :
    Measurable (fun y => σ (Set.projIcc (0 : ℝ) 1 zero_le_one y)) := by
  apply Continuous.measurable
  exact hc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun y => (Set.projIcc (0 : ℝ) 1 zero_le_one y).2)

lemma sigc_eq (σ : ℝ → ℝ) : ∀ y ∈ Set.Icc (0 : ℝ) 1,
    σ y = (fun y => σ (Set.projIcc (0 : ℝ) 1 zero_le_one y)) y := by
  intro y hy
  simp [Set.projIcc_of_mem zero_le_one hy]


lemma g_lip {m : ℕ} (σ : ℝ → ℝ) (K : NNReal) (hσlip : LipschitzOnWith K σ (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) :
    LipschitzWith K (fun z : Fin m → ℝ =>
      W.mulVec (fun j => σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)))) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  have hd0 : 0 ≤ dist z z' := dist_nonneg
  have hc : ∀ j, |σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)) -
      σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j))| ≤ K * dist z z' := by
    intro j
    have h1 := hσlip.dist_le_mul _ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)).2 _
      (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j)).2
    rw [Real.dist_eq, Real.dist_eq] at h1
    have h2 := Set.abs_projIcc_sub_projIcc (a := (0 : ℝ)) (b := 1) zero_le_one
      (c := z j) (d := z' j)
    have h3 : |z j - z' j| ≤ dist z z' := by
      rw [← Real.dist_eq]; exact dist_le_pi_dist z z' j
    calc _ ≤ (K : ℝ) * |(Set.projIcc (0 : ℝ) 1 zero_le_one (z j) : ℝ) -
          (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j) : ℝ)| := h1
      _ ≤ K * dist z z' := by
          apply mul_le_mul_of_nonneg_left (h2.trans h3) K.2
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Real.dist_eq]
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ j, |W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)) -
        W i j * σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z' j))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, W i j * (K * dist z z') := by
        apply Finset.sum_le_sum; intro j _
        rw [← mul_sub, abs_mul, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hW)]
        exact mul_le_mul_of_nonneg_left (hc j) (Matrix.nonneg_of_mem_rowStochastic hW)
    _ = K * dist z z' := by
        rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hW, one_mul]

lemma g_bound {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m)) (z : Fin m → ℝ) :
    ‖W.mulVec (fun j => σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)))‖ ≤ ((1 : NNReal) : ℝ) := by
  rw [NNReal.coe_one, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have := wsum_mem W hW (fun j => σ (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)))
    (fun j => hmaps (Set.projIcc (0 : ℝ) 1 zero_le_one (z j)).2) i
  rw [Real.norm_eq_abs, abs_le]
  simp only [Matrix.mulVec, dotProduct]
  exact ⟨by linarith [this.1], this.2⟩

lemma ode_exists {m : ℕ} (σ : ℝ → ℝ) (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1))
    (K : NNReal) (hσlip : LipschitzOnWith K σ (Set.Icc 0 1))
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ Matrix.rowStochastic ℝ (Fin m))
    (x1 : Fin m → ℝ) :
    ∃ z : ℝ → (Fin m → ℝ), IsODESolution (meanField σ W) z ∧ z 0 = x1 :=
  NLode.glue (meanField σ W) (K + 1) (meanField_lip σ K hσlip W hW) x1 fun n =>
    NLode.local_exists _ K (g_lip σ K hσlip W hW) 1 (g_bound σ hmaps W hW) x1 n

lemma half_up {m : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : ℝ → ℝ)
    (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1)) (K : NNReal)
    (hlip : LipschitzOnWith K σ (Set.Icc 0 1)) (hgt : ∀ x ∈ Set.Ioo p 1, x < σ x)
    (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ) (hW : IsWeightMatrix W) (θ : ℝ)
    (hconv : ∀ x1 : Fin m → ℝ, (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) → p + θ ≤ ∑ i, μ i * x1 i →
      ∀ z, IsODESolution (meanField σ W) z → z 0 = x1 → Tendsto z atTop (𝓝 1))
    (ρ : ℝ) (hρ : 0 < ρ) (γ : ℝ) (hγ : 0 < γ)
    (hA : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ y : Fin m → ℝ, (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, 1 - ρ < y i) → ENNReal.ofReal (1 - γ) ≤ coinLaw m {V |
        Tendsto (beliefAct id ε W y V) atTop (𝓝 1) ∧ ∀ t i, p < beliefAct id ε W y V t i}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) ε0, ∀ x1 : Fin m → ℝ,
      (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) → p + θ ≤ ∑ i, μ i * x1 i →
      ENNReal.ofReal (1 - γ) * ENNReal.ofReal (1 - γ) ≤
        coinLaw m {U | Tendsto (beliefAct σ ε W x1 U) atTop (𝓝 1)} := by
  set Kset : Set (Fin m → ℝ) :=
    {x | (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧ (fun v => p + θ ≤ v) (∑ i, μ i * x i)}
  have hK : IsCompact Kset :=
    isCompact_K μ (fun v => p + θ ≤ v) (isClosed_le continuous_const continuous_id)
  obtain ⟨T, hT0, hT⟩ := uniform_time (meanField σ W) (K + 1) (meanField_lip σ K hlip W hW.1)
    Kset hK 1 (fun x _ => ode_exists σ hmaps K hlip W hW.1 x)
    (fun x hx => hconv x hx.1 hx.2) (ρ / 2) (half_pos hρ)
  obtain ⟨ε1, hε1, hP⟩ := proposition_2 σ hmaps K hlip W hW (T + 1) (by linarith) (ρ / 2)
    (half_pos hρ) γ hγ
  refine ⟨min ε1 1, lt_min hε1 one_pos, ?_⟩
  intro ε hε x1 hx1 hθ
  have hεI : ε ∈ Set.Ioc (0 : ℝ) 1 := ⟨hε.1, (hε.2.trans_le (min_le_right _ _)).le⟩
  have hεP : ε ∈ Set.Ioo (0 : ℝ) ε1 := ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  obtain ⟨z, hz, hz0⟩ := ode_exists σ hmaps K hlip W hW.1 x1
  obtain ⟨s, hs, hsd⟩ := hT x1 ⟨hx1, hθ⟩ z hz hz0
  set N := ⌊s / ε⌋₊ with hN
  have hbad := hP ε hεP x1 hx1 z hz hz0
  set σc : ℝ → ℝ := fun y => σ (Set.projIcc (0 : ℝ) 1 zero_le_one y) with hσc
  have hcont : ContinuousOn σ (Set.Icc 0 1) := hlip.continuousOn
  have heq : ∀ U, beliefAct σ ε W x1 U = beliefAct σc ε W x1 U := fun U =>
    funext (bel_congr_sigma σ σc (sigc_eq σ) ε hεI W hW.1 x1 hx1 U)
  set Good : Set (Fin m → ℝ) := {y | ∀ i, y i ∈ Set.Icc (0 : ℝ) 1 ∧ 1 - ρ < y i}
  have hGood : MeasurableSet Good := by
    have e : Good = ⋂ i, (fun y : Fin m → ℝ => y i) ⁻¹' (Set.Icc (0 : ℝ) 1 ∩ Set.Ioi (1 - ρ)) := by
      ext y; simp [Good]
    rw [e]
    exact MeasurableSet.iInter fun i =>
      (measurable_pi_apply i) (measurableSet_Icc.inter measurableSet_Ioi)
  set A : Set ((Fin m → ℝ) × Coins m) := {q : (Fin m → ℝ) × Coins m |
      Tendsto (fun t => beliefAct id ε W q.1 q.2 t) atTop (𝓝 1) ∧
        ∀ t i, p < beliefAct id ε W q.1 q.2 t i}
  have hmk := markov_bound σc (sigc_meas σ hcont) ε W x1 N Good hGood A
    (measurableSet_A1 p ε W) (ENNReal.ofReal (1 - γ))
    (fun y hy => hA ε hεI y (fun i => (hy i).1) (fun i => (hy i).2))
  -- probability of being good at time N
  have hG : ENNReal.ofReal (1 - γ) ≤ coinLaw m {U | beliefAct σc ε W x1 U N ∈ Good} := by
    set G := {U | beliefAct σc ε W x1 U N ∈ Good}
    have hsub : Gᶜ ⊆ {U | ∃ t ∈ Set.Icc (0 : ℝ) (T + 1),
        ρ / 2 < ‖z t - beliefAct σ ε W x1 U ⌊t / ε⌋₊‖} := by
      intro U hU
      simp only [G, Good, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hU
      obtain ⟨i, hi⟩ := hU
      have hm := bel_mem σ ε hεI W hW.1 x1 hx1 U N i
      rw [heq] at hm
      have hle : beliefAct σc ε W x1 U N i ≤ 1 - ρ := by
        by_contra hc; exact hi ⟨hm, lt_of_not_ge hc⟩
      refine ⟨s, ⟨hs.1, by linarith [hs.2]⟩, ?_⟩
      rw [heq]
      have h1 : |z s i - 1| ≤ dist (z s) 1 := by
        rw [← Real.dist_eq]; exact dist_le_pi_dist (z s) 1 i
      have h2 : |z s i - beliefAct σc ε W x1 U N i| ≤
          ‖z s - beliefAct σc ε W x1 U N‖ := by
        have := norm_le_pi_norm (z s - beliefAct σc ε W x1 U N) i
        simpa [Real.norm_eq_abs] using this
      have h3 : ρ ≤ |1 - beliefAct σc ε W x1 U N i| := by
        rw [abs_of_nonneg (by linarith)]; linarith
      have h4 : |1 - beliefAct σc ε W x1 U N i| ≤
          |z s i - 1| + |z s i - beliefAct σc ε W x1 U N i| := by
        calc |1 - beliefAct σc ε W x1 U N i| =
            |(z s i - beliefAct σc ε W x1 U N i) - (z s i - 1)| := by ring_nf
          _ ≤ |z s i - beliefAct σc ε W x1 U N i| + |z s i - 1| := abs_sub _ _
          _ = _ := add_comm _ _
      linarith
    have hu : (1 : ENNReal) ≤ coinLaw m G + coinLaw m Gᶜ := by
      rw [← measure_univ (μ := coinLaw m), ← Set.union_compl_self G]
      exact measure_union_le _ _
    have hc := (measure_mono hsub).trans hbad
    rw [ENNReal.ofReal_sub 1 hγ.le, ENNReal.ofReal_one]
    exact tsub_le_iff_right.2 (hu.trans (add_le_add le_rfl hc))
  -- inclusion into the convergence event
  have hinc : {U | beliefAct σc ε W x1 U N ∈ Good ∧
      (beliefAct σc ε W x1 U N, fun t => U (N + t)) ∈ A} ⊆
      {U | Tendsto (beliefAct σ ε W x1 U) atTop (𝓝 1)} := by
    rintro U ⟨hg, hA'⟩
    simp only [Set.mem_setOf_eq]
    rw [← heq] at hg hA'
    set y := beliefAct σ ε W x1 U N
    set V : Coins m := fun t => U (N + t)
    have hcube : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1 := fun i => (hg i).1
    have hcp := coupling_up p σ (sigma_up p hp0 hp1 σ hcont hmaps hgt) ε hεI W hW.1 y y hcube
      (fun i => le_rfl) V hA'.2
    have hup := bel_mem σ ε hεI W hW.1 y hcube V
    have hlim : Tendsto (beliefAct σ ε W y V) atTop (𝓝 1) := by
      rw [tendsto_pi_nhds]
      intro i
      have hyi : Tendsto (fun k => beliefAct id ε W y V k i) atTop (𝓝 ((1 : Fin m → ℝ) i)) :=
        (tendsto_pi_nhds.1 hA'.1) i
      simp only [Pi.one_apply] at hyi ⊢
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hyi tendsto_const_nhds
        (fun k => hcp k i) (fun k => (hup k i).2)
    rw [← tendsto_add_atTop_iff_nat N]
    have : (fun k => beliefAct σ ε W x1 U (k + N)) = beliefAct σ ε W y V := by
      funext k; rw [Nat.add_comm]; exact bel_restart σ ε W x1 U N k
    rw [this]; exact hlim
  calc ENNReal.ofReal (1 - γ) * ENNReal.ofReal (1 - γ) ≤
      ENNReal.ofReal (1 - γ) * coinLaw m {U | beliefAct σc ε W x1 U N ∈ Good} := by gcongr
    _ ≤ _ := hmk
    _ ≤ _ := measure_mono hinc

lemma half_dn {m : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : ℝ → ℝ)
    (hmaps : Set.MapsTo σ (Set.Icc 0 1) (Set.Icc 0 1)) (K : NNReal)
    (hlip : LipschitzOnWith K σ (Set.Icc 0 1)) (hlt : ∀ x ∈ Set.Ioo 0 p, σ x < x)
    (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ) (hW : IsWeightMatrix W) (θ : ℝ)
    (hconv : ∀ x1 : Fin m → ℝ, (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) → ∑ i, μ i * x1 i ≤ p - θ →
      ∀ z, IsODESolution (meanField σ W) z → z 0 = x1 → Tendsto z atTop (𝓝 0))
    (ρ : ℝ) (hρ : 0 < ρ) (γ : ℝ) (hγ : 0 < γ)
    (hA : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ y : Fin m → ℝ, (∀ i, y i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, y i < ρ) → ENNReal.ofReal (1 - γ) ≤ coinLaw m {V |
        Tendsto (beliefAct id ε W y V) atTop (𝓝 0) ∧ ∀ t i, beliefAct id ε W y V t i < p}) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) ε0, ∀ x1 : Fin m → ℝ,
      (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) → ∑ i, μ i * x1 i ≤ p - θ →
      ENNReal.ofReal (1 - γ) * ENNReal.ofReal (1 - γ) ≤
        coinLaw m {U | Tendsto (beliefAct σ ε W x1 U) atTop (𝓝 0)} := by
  set Kset : Set (Fin m → ℝ) :=
    {x | (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧ (fun v => v ≤ p - θ) (∑ i, μ i * x i)}
  have hK : IsCompact Kset :=
    isCompact_K μ (fun v => v ≤ p - θ) (isClosed_le continuous_id continuous_const)
  obtain ⟨T, hT0, hT⟩ := uniform_time (meanField σ W) (K + 1) (meanField_lip σ K hlip W hW.1)
    Kset hK 0 (fun x _ => ode_exists σ hmaps K hlip W hW.1 x)
    (fun x hx => hconv x hx.1 hx.2) (ρ / 2) (half_pos hρ)
  obtain ⟨ε1, hε1, hP⟩ := proposition_2 σ hmaps K hlip W hW (T + 1) (by linarith) (ρ / 2)
    (half_pos hρ) γ hγ
  refine ⟨min ε1 1, lt_min hε1 one_pos, ?_⟩
  intro ε hε x1 hx1 hθ
  have hεI : ε ∈ Set.Ioc (0 : ℝ) 1 := ⟨hε.1, (hε.2.trans_le (min_le_right _ _)).le⟩
  have hεP : ε ∈ Set.Ioo (0 : ℝ) ε1 := ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  obtain ⟨z, hz, hz0⟩ := ode_exists σ hmaps K hlip W hW.1 x1
  obtain ⟨s, hs, hsd⟩ := hT x1 ⟨hx1, hθ⟩ z hz hz0
  set N := ⌊s / ε⌋₊ with hN
  have hbad := hP ε hεP x1 hx1 z hz hz0
  set σc : ℝ → ℝ := fun y => σ (Set.projIcc (0 : ℝ) 1 zero_le_one y) with hσc
  have hcont : ContinuousOn σ (Set.Icc 0 1) := hlip.continuousOn
  have heq : ∀ U, beliefAct σ ε W x1 U = beliefAct σc ε W x1 U := fun U =>
    funext (bel_congr_sigma σ σc (sigc_eq σ) ε hεI W hW.1 x1 hx1 U)
  set Good : Set (Fin m → ℝ) := {y | ∀ i, y i ∈ Set.Icc (0 : ℝ) 1 ∧ y i < ρ}
  have hGood : MeasurableSet Good := by
    have e : Good = ⋂ i, (fun y : Fin m → ℝ => y i) ⁻¹' (Set.Icc (0 : ℝ) 1 ∩ Set.Iio ρ) := by
      ext y; simp [Good]
    rw [e]
    exact MeasurableSet.iInter fun i =>
      (measurable_pi_apply i) (measurableSet_Icc.inter measurableSet_Iio)
  set A : Set ((Fin m → ℝ) × Coins m) := {q : (Fin m → ℝ) × Coins m |
      Tendsto (fun t => beliefAct id ε W q.1 q.2 t) atTop (𝓝 0) ∧
        ∀ t i, beliefAct id ε W q.1 q.2 t i < p}
  have hmk := markov_bound σc (sigc_meas σ hcont) ε W x1 N Good hGood A
    (measurableSet_A0 p ε W) (ENNReal.ofReal (1 - γ))
    (fun y hy => hA ε hεI y (fun i => (hy i).1) (fun i => (hy i).2))
  -- probability of being good at time N
  have hG : ENNReal.ofReal (1 - γ) ≤ coinLaw m {U | beliefAct σc ε W x1 U N ∈ Good} := by
    set G := {U | beliefAct σc ε W x1 U N ∈ Good}
    have hsub : Gᶜ ⊆ {U | ∃ t ∈ Set.Icc (0 : ℝ) (T + 1),
        ρ / 2 < ‖z t - beliefAct σ ε W x1 U ⌊t / ε⌋₊‖} := by
      intro U hU
      simp only [G, Good, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hU
      obtain ⟨i, hi⟩ := hU
      have hm := bel_mem σ ε hεI W hW.1 x1 hx1 U N i
      rw [heq] at hm
      have hle : ρ ≤ beliefAct σc ε W x1 U N i := by
        by_contra hc; exact hi ⟨hm, lt_of_not_ge hc⟩
      refine ⟨s, ⟨hs.1, by linarith [hs.2]⟩, ?_⟩
      rw [heq]
      have h1 : |z s i - 0| ≤ dist (z s) 0 := by
        rw [← Real.dist_eq]; exact dist_le_pi_dist (z s) 0 i
      have h2 : |z s i - beliefAct σc ε W x1 U N i| ≤
          ‖z s - beliefAct σc ε W x1 U N‖ := by
        have := norm_le_pi_norm (z s - beliefAct σc ε W x1 U N) i
        simpa [Real.norm_eq_abs] using this
      have h3 : ρ ≤ |0 - beliefAct σc ε W x1 U N i| := by
        rw [abs_of_nonpos (by linarith)]; linarith
      have h4 : |0 - beliefAct σc ε W x1 U N i| ≤
          |z s i - 0| + |z s i - beliefAct σc ε W x1 U N i| := by
        calc |0 - beliefAct σc ε W x1 U N i| =
            |(z s i - beliefAct σc ε W x1 U N i) - (z s i - 0)| := by ring_nf
          _ ≤ |z s i - beliefAct σc ε W x1 U N i| + |z s i - 0| := abs_sub _ _
          _ = _ := add_comm _ _
      linarith
    have hu : (1 : ENNReal) ≤ coinLaw m G + coinLaw m Gᶜ := by
      rw [← measure_univ (μ := coinLaw m), ← Set.union_compl_self G]
      exact measure_union_le _ _
    have hc := (measure_mono hsub).trans hbad
    rw [ENNReal.ofReal_sub 1 hγ.le, ENNReal.ofReal_one]
    exact tsub_le_iff_right.2 (hu.trans (add_le_add le_rfl hc))
  -- inclusion into the convergence event
  have hinc : {U | beliefAct σc ε W x1 U N ∈ Good ∧
      (beliefAct σc ε W x1 U N, fun t => U (N + t)) ∈ A} ⊆
      {U | Tendsto (beliefAct σ ε W x1 U) atTop (𝓝 0)} := by
    rintro U ⟨hg, hA'⟩
    simp only [Set.mem_setOf_eq]
    rw [← heq] at hg hA'
    set y := beliefAct σ ε W x1 U N
    set V : Coins m := fun t => U (N + t)
    have hcube : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1 := fun i => (hg i).1
    have hcp := coupling_down p σ (sigma_dn p hp0 hp1 σ hcont hmaps hlt) ε hεI W hW.1 y y hcube
      (fun i => le_rfl) V hA'.2
    have hup := bel_mem σ ε hεI W hW.1 y hcube V
    have hlim : Tendsto (beliefAct σ ε W y V) atTop (𝓝 0) := by
      rw [tendsto_pi_nhds]
      intro i
      have hyi : Tendsto (fun k => beliefAct id ε W y V k i) atTop (𝓝 ((0 : Fin m → ℝ) i)) :=
        (tendsto_pi_nhds.1 hA'.1) i
      simp only [Pi.zero_apply] at hyi ⊢
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hyi
        (fun k => (hup k i).1) (fun k => hcp k i)
    rw [← tendsto_add_atTop_iff_nat N]
    have : (fun k => beliefAct σ ε W x1 U (k + N)) = beliefAct σ ε W y V := by
      funext k; rw [Nat.add_comm]; exact bel_restart σ ε W x1 U N k
    rw [this]; exact hlim
  calc ENNReal.ofReal (1 - γ) * ENNReal.ofReal (1 - γ) ≤
      ENNReal.ofReal (1 - γ) * coinLaw m {U | beliefAct σc ε W x1 U N ∈ Good} := by gcongr
    _ ≤ _ := hmk
    _ ≤ _ := measure_mono hinc

end NL6

open NL6 in
theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : ℝ → ℝ → ℝ)
    (hσ : IsExtremizationFamily p σ) {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) :
    ∀ η : ℝ, 0 < η → ∃ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ ε0 : ℝ, 0 < ε0 ∧
      ∀ ε ∈ Set.Ioo (0 : ℝ) ε0, ∀ x1 : Fin m → ℝ, (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) →
        (p + η < ∑ i, μ i * x1 i →
          ENNReal.ofReal (1 - η) ≤
            coinLaw m {U | Tendsto (beliefAct (σ δ) ε W x1 U) atTop (𝓝 1)}) ∧
        (∑ i, μ i * x1 i < p - η →
          ENNReal.ofReal (1 - η) ≤
            coinLaw m {U | Tendsto (beliefAct (σ δ) ε W x1 U) atTop (𝓝 0)}) := by
  intro η hη
  by_cases hη1 : 1 ≤ η
  · refine ⟨1, ⟨one_pos, le_rfl⟩, 1, one_pos, fun ε _ x1 _ => ⟨fun _ => ?_, fun _ => ?_⟩⟩ <;>
    · rw [ENNReal.ofReal_of_nonpos (by linarith)]; exact bot_le
  push Not at hη1
  set γ := η / 2 with hγ
  have hγ0 : 0 < γ := by positivity
  have hfin : ENNReal.ofReal (1 - η) ≤ ENNReal.ofReal (1 - γ) * ENNReal.ofReal (1 - γ) := by
    rw [← ENNReal.ofReal_mul (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  obtain ⟨η0, hη0, H5⟩ := lemma_5 p hp0 hp1 W μ hW hμ γ hγ0
  set ρ := η0 / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρI : ρ ∈ Set.Ioo (0 : ℝ) η0 := ⟨hρ0, by linarith⟩
  obtain ⟨δ0, hδ0, H4⟩ := lemma_4 p hp0 hp1 σ hσ W μ hW hμ (η / 2) (by positivity)
  obtain ⟨hmaps, ⟨K, hlip⟩, hgt, hlt⟩ := hσ.1 δ0 hδ0
  have H4' := fun x1 hx1 z hz hz0 => H4 δ0 ⟨hδ0.1, le_rfl⟩ x1 hx1 z hz hz0
  obtain ⟨εu, hεu, Hu⟩ := half_up p hp0 hp1 (σ δ0) hmaps K hlip hgt W μ hW η
    (fun x1 hx1 hθ z hz hz0 => (H4' x1 hx1 z hz hz0).1 (by linarith)) ρ hρ0 γ hγ0
    (fun ε hε y hy hy1 => (H5 ρ hρI ε hε y hy).1 hy1)
  obtain ⟨εd, hεd, Hd⟩ := half_dn p hp0 hp1 (σ δ0) hmaps K hlip hlt W μ hW η
    (fun x1 hx1 hθ z hz hz0 => (H4' x1 hx1 z hz hz0).2 (by linarith)) ρ hρ0 γ hγ0
    (fun ε hε y hy hy1 => (H5 ρ hρI ε hε y hy).2 hy1)
  refine ⟨δ0, hδ0, min εu εd, lt_min hεu hεd, ?_⟩
  intro ε hε x1 hx1
  refine ⟨fun h => hfin.trans (Hu ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩ x1 hx1 h.le),
    fun h => hfin.trans (Hd ε ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩ x1 hx1 h.le)⟩
