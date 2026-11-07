-- Prove2me | solution 1 for HordijkKallenbergLP.ExtremePoint.system7_solution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:32:31.474825+00:00
-- url     : https://prove2.me/submissions/664f3fb2-93a7-473f-b4d9-4a8d45cc28a1

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_ExtremePoint_Model
open Matrix MarkovDecisionProcesses BlackwellDiscreteDP.NearOne

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Filter Topology

namespace HordijkKallenbergLP.ExtremePoint.Aux

section MarkovTheory
variable {n : Type*} [Fintype n] [DecidableEq n]

instance bmk_fc : FirstCountableTopology (Matrix n n ℝ) :=
  inferInstanceAs (FirstCountableTopology (n → n → ℝ))

lemma bmk_mul {A B : Matrix n n ℝ} (hA : IsMarkovMatrix A) (hB : IsMarkovMatrix B) :
    IsMarkovMatrix (A * B) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hA.1 i k) (hB.1 k j)
  · simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hB.2, mul_one]
    exact hA.2 i

lemma bmk_one : IsMarkovMatrix (1 : Matrix n n ℝ) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · rw [Matrix.one_apply]; split_ifs <;> norm_num
  · simp [Matrix.one_apply]

lemma bmk_pow {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (k : ℕ) : IsMarkovMatrix (P ^ k) := by
  induction k with
  | zero => simpa using (bmk_one (n := n))
  | succ k ih => rw [pow_succ]; exact bmk_mul ih hP

lemma bmk_le_one {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (i j : n) : P i j ≤ 1 := by
  rw [← hP.2 i]
  exact Finset.single_le_sum (f := fun j => P i j) (fun j _ => hP.1 i j) (Finset.mem_univ j)

lemma bmk_cesaro {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (N : ℕ) :
    IsMarkovMatrix (cesaroMean P N) := by
  unfold cesaroMean
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => (bmk_pow hP k).1 i j)
  · simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [(bmk_pow hP _).2 i]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp

lemma bmk_P_mul_sum (P : Matrix n n ℝ) (N : ℕ) :
    P * ∑ k ∈ Finset.range (N + 1), P ^ k = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, ← pow_succ']
    abel

lemma bmk_sum_mul_P (P : Matrix n n ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), P ^ k) * P = ∑ k ∈ Finset.range (N + 1), P ^ k + (P ^ (N + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_mul, ih, ← pow_succ]
    abel

lemma bmk_P_cesaro (P : Matrix n n ℝ) (N : ℕ) :
    P * cesaroMean P N - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.mul_smul, bmk_P_mul_sum, smul_add]
  abel

lemma bmk_cesaro_P (P : Matrix n n ℝ) (N : ℕ) :
    cesaroMean P N * P - cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1) := by
  unfold cesaroMean
  rw [Matrix.smul_mul, bmk_sum_mul_P, smul_add]
  abel

lemma bmk_D_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hb : ∀ N : ℕ, ‖(((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) i j‖ ≤ 1 / ((N : ℝ) + 1) := by
    intro N
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Real.norm_eq_abs]
    have h1 := (bmk_pow hP (N + 1)).1 i j
    have h2 := bmk_le_one (bmk_pow hP (N + 1)) i j
    have h3 : (0 : ℝ) ≤ (1 : Matrix n n ℝ) i j := bmk_one.1 i j
    have h4 : (1 : Matrix n n ℝ) i j ≤ 1 := bmk_le_one bmk_one i j
    rw [abs_mul, abs_of_pos (by positivity), one_div]
    have : |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc ((N : ℝ) + 1)⁻¹ * |(P ^ (N + 1)) i j - (1 : Matrix n n ℝ) i j| ≤ ((N : ℝ) + 1)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  exact squeeze_zero_norm hb tendsto_one_div_add_atTop_nhds_zero_nat

lemma bmk_clus {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) {L : Matrix n n ℝ}
    (hL : Tendsto (fun j => cesaroMean P (ns j)) atTop (𝓝 L)) : P * L = L ∧ L * P = L := by
  have hD := (bmk_D_tendsto hP).comp hns
  constructor
  · have h1 : Tendsto (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) atTop
        (𝓝 (P * L - L)) := (hL.const_mul P).sub hL
    have h2 : (fun j => P * cesaroMean P (ns j) - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact bmk_P_cesaro P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)
  · have h1 : Tendsto (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) atTop
        (𝓝 (L * P - L)) := (hL.mul_const P).sub hL
    have h2 : (fun j => cesaroMean P (ns j) * P - cesaroMean P (ns j)) =
        (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • (P ^ (N + 1) - 1)) ∘ ns := by
      funext j; exact bmk_cesaro_P P (ns j)
    rw [h2] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 hD)

lemma bmk_avg_const (L : Matrix n n ℝ) (N : ℕ) :
    ((N : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (N + 1), L = L := by
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (by positivity), one_smul]

lemma bmk_cesaro_mul_fix {P L : Matrix n n ℝ} (h : P * L = L) (N : ℕ) :
    cesaroMean P N * L = L := by
  have hk : ∀ k : ℕ, P ^ k * L = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp_rw [hk]
  exact bmk_avg_const L N

lemma bmk_fix_mul_cesaro {P L : Matrix n n ℝ} (h : L * P = L) (N : ℕ) :
    L * cesaroMean P N = L := by
  have hk : ∀ k : ℕ, L * P ^ k = L := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mul_assoc, ih, h]
  unfold cesaroMean
  rw [Matrix.mul_smul, Finset.mul_sum]
  simp_rw [hk]
  exact bmk_avg_const L N

lemma bmk_compact : IsCompact {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} := by
  have e : {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} =
      Set.pi Set.univ (fun (_ : n) => Set.pi Set.univ (fun (_ : n) => Set.Icc (0 : ℝ) 1)) := by
    ext M; exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [e]
  exact isCompact_univ_pi (fun (_ : n) => isCompact_univ_pi (fun (_ : n) => isCompact_Icc))

theorem bmk_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    Tendsto (cesaroMean P) atTop (𝓝 (limitMatrix P)) := by
  have hmem : ∀ N, cesaroMean P N ∈ {M : Matrix n n ℝ | ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1} :=
    fun N i j => ⟨(bmk_cesaro hP N).1 i j, bmk_le_one (bmk_cesaro hP N) i j⟩
  obtain ⟨L, -, φ, hφ, hL⟩ := bmk_compact.tendsto_subseq hmem
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨hPL, hLP⟩ := bmk_clus hP hφt hL
  have main : Tendsto (cesaroMean P) atTop (𝓝 L) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨L', -, ψ, hψ, hL'⟩ := bmk_compact.tendsto_subseq (fun j => hmem (ns j))
    refine ⟨ψ, ?_⟩
    have hnsψ : Tendsto (ns ∘ ψ) atTop atTop := hns.comp hψ.tendsto_atTop
    obtain ⟨hPL', hL'P⟩ := bmk_clus hP hnsψ hL'
    have e1 : L * L' = L' := by
      have t : Tendsto (fun j => cesaroMean P (φ j) * L') atTop (𝓝 (L * L')) := hL.mul_const L'
      simp_rw [bmk_cesaro_mul_fix hPL'] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have e2 : L * L' = L := by
      have t : Tendsto (fun j => L * cesaroMean P ((ns ∘ ψ) j)) atTop (𝓝 (L * L')) :=
        hL'.const_mul L
      simp_rw [bmk_fix_mul_cesaro hLP] at t
      exact (tendsto_nhds_unique tendsto_const_nhds t).symm
    have : L' = L := e1.symm.trans e2
    rw [this] at hL'
    exact hL'
  rw [limitMatrix, main.limUnder_eq]
  exact main

variable {P : Matrix n n ℝ}

lemma bmk_PL (hP : IsMarkovMatrix P) : P * limitMatrix P = limitMatrix P :=
  (bmk_clus hP tendsto_id (bmk_tendsto hP)).1

lemma bmk_LP (hP : IsMarkovMatrix P) : limitMatrix P * P = limitMatrix P :=
  (bmk_clus hP tendsto_id (bmk_tendsto hP)).2

lemma bmk_LL (hP : IsMarkovMatrix P) : limitMatrix P * limitMatrix P = limitMatrix P := by
  have t : Tendsto (fun N => cesaroMean P N * limitMatrix P) atTop
      (𝓝 (limitMatrix P * limitMatrix P)) := (bmk_tendsto hP).mul_const _
  simp_rw [bmk_cesaro_mul_fix (bmk_PL hP)] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

lemma bmk_fixvec (hP : IsMarkovMatrix P) {v : n → ℝ} (hv : P *ᵥ v = v) :
    limitMatrix P *ᵥ v = v := by
  have hk : ∀ k : ℕ, (P ^ k) *ᵥ v = v := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  have hA : ∀ N, cesaroMean P N *ᵥ v = v := by
    intro N
    rw [cesaroMean, Matrix.smul_mulVec, Matrix.sum_mulVec]
    simp_rw [hk]
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (by positivity), one_smul]
  have t : Tendsto (fun N => cesaroMean P N *ᵥ v) atTop (𝓝 (limitMatrix P *ᵥ v)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto _).comp (bmk_tendsto hP)
  simp_rw [hA] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

lemma bmk_L_markov (hP : IsMarkovMatrix P) : IsMarkovMatrix (limitMatrix P) := by
  have hc : IsClosed {M : Matrix n n ℝ | IsMarkovMatrix M} := by
    have : {M : Matrix n n ℝ | IsMarkovMatrix M} =
        (⋂ i, ⋂ j, {M : Matrix n n ℝ | 0 ≤ M i j}) ∩ ⋂ i, {M : Matrix n n ℝ | ∑ j, M i j = 1} := by
      ext M; simp [IsMarkovMatrix]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
      (isClosed_iInter fun i => ?_)
    · exact isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
    · exact isClosed_eq (continuous_finsetSum _ fun j _ =>
        (continuous_apply j).comp (continuous_apply i)) continuous_const
  exact hc.mem_of_tendsto (bmk_tendsto hP) (Eventually.of_forall fun N => bmk_cesaro hP N)

lemma bmk_ZL_inj (hP : IsMarkovMatrix P) :
    Function.Injective (1 - P + limitMatrix P).mulVec := by
  set L := limitMatrix P
  have hLA : L * (1 - P + L) = L := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
  intro v w hvw
  set d := v - w
  have hd : (1 - P + L) *ᵥ d = 0 := by
    simp only [d, Matrix.mulVec_sub, hvw, sub_self]
  have hLd : L *ᵥ d = 0 := by
    have := congrArg (fun z => L *ᵥ z) hd
    simp only [Matrix.mulVec_mulVec, hLA, Matrix.mulVec_zero] at this
    exact this
  have hPd : P *ᵥ d = d := by
    have := hd
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, hLd, Matrix.one_mulVec, add_zero, sub_eq_zero] at this
    exact this.symm
  have : d = 0 := by rw [← bmk_fixvec hP hPd, hLd]
  exact sub_eq_zero.1 this

lemma bmk_Z_unit (hP : IsMarkovMatrix P) : IsUnit (1 - P + limitMatrix P).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_injective_iff_isUnit.1 (bmk_ZL_inj hP))

lemma bmk_PH (hP : IsMarkovMatrix P) :
    P * deviationMatrix P = deviationMatrix P + limitMatrix P - 1 := by
  set L := limitMatrix P
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + L) * (1 - P + L)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hLZ : L * (1 - P + L)⁻¹ = L := by
    have hLA : L * (1 - P + L) = L := by
      rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
    calc L * (1 - P + L)⁻¹ = (L * (1 - P + L)) * (1 - P + L)⁻¹ := by rw [hLA]
      _ = L * ((1 - P + L) * (1 - P + L)⁻¹) := Matrix.mul_assoc _ _ _
      _ = L := by rw [h1, Matrix.mul_one]
  have h2 : (1 - P + L) * (1 - P + L)⁻¹ = (1 - P + L)⁻¹ - P * (1 - P + L)⁻¹ + L * (1 - P + L)⁻¹ := by
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul]
  rw [h1, hLZ] at h2
  unfold deviationMatrix
  rw [Matrix.mul_sub, bmk_PL hP]
  change P * (1 - P + L)⁻¹ - L = (1 - P + L)⁻¹ - L + L - 1
  generalize (1 - P + L)⁻¹ = Z at h2 ⊢
  have : P * Z = Z + L - 1 := by rw [h2]; abel
  rw [this]; abel

lemma bmk_LH (hP : IsMarkovMatrix P) : limitMatrix P * deviationMatrix P = 0 := by
  set L := limitMatrix P
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + L) * (1 - P + L)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hLA : L * (1 - P + L) = L := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
  have hLZ : L * (1 - P + L)⁻¹ = L := by
    calc L * (1 - P + L)⁻¹ = (L * (1 - P + L)) * (1 - P + L)⁻¹ := by rw [hLA]
      _ = L * ((1 - P + L) * (1 - P + L)⁻¹) := Matrix.mul_assoc _ _ _
      _ = L := by rw [h1, Matrix.mul_one]
  unfold deviationMatrix
  rw [Matrix.mul_sub, hLZ, bmk_LL hP, sub_self]

end MarkovTheory

section Chain
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma acc_of_pow_pos {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    ∀ (k : ℕ) (l i : n), 0 < (P ^ k) l i → Accessible P l i := by
  intro k
  induction k with
  | zero =>
    intro l i h
    by_cases hli : l = i
    · subst hli; exact Relation.ReflTransGen.refl
    · simp [Matrix.one_apply, hli] at h
  | succ k ih =>
    intro l i h
    rw [pow_succ, Matrix.mul_apply] at h
    have : ∃ j, 0 < (P ^ k) l j * P j i := by
      by_contra hc
      push_neg at hc
      have := Finset.sum_nonpos (fun j (_ : j ∈ Finset.univ) => hc j)
      linarith
    obtain ⟨j, hj⟩ := this
    have h1 : 0 < (P ^ k) l j := by
      by_contra h0
      have : (P ^ k) l j = 0 := le_antisymm (not_lt.mp h0) ((bmk_pow hP k).1 l j)
      rw [this, zero_mul] at hj
      exact lt_irrefl _ hj
    have h2 : 0 < P j i := by
      by_contra h0
      have : P j i = 0 := le_antisymm (not_lt.mp h0) (hP.1 j i)
      rw [this, mul_zero] at hj
      exact lt_irrefl _ hj
    exact (ih l j h1).tail h2

lemma L_entry_tendsto {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (l i : n) :
    Tendsto (fun N => cesaroMean P N l i) atTop (𝓝 (limitMatrix P l i)) := by
  have hc : Continuous (fun Mx : Matrix n n ℝ => Mx l i) :=
    (continuous_apply i).comp (continuous_apply l)
  exact (hc.tendsto _).comp (bmk_tendsto hP)

lemma acc_of_L_pos {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {l i : n}
    (h : 0 < limitMatrix P l i) : Accessible P l i := by
  by_contra hacc
  have hz : ∀ k, (P ^ k) l i = 0 := fun k =>
    le_antisymm (not_lt.mp (fun h' => hacc (acc_of_pow_pos hP k l i h'))) ((bmk_pow hP k).1 l i)
  have hc : ∀ N, cesaroMean P N l i = 0 := by
    intro N
    simp [cesaroMean, Matrix.smul_apply, Matrix.sum_apply, hz]
  have ht := L_entry_tendsto hP l i
  simp_rw [hc] at ht
  have := tendsto_nhds_unique tendsto_const_nhds ht
  linarith

lemma L_nonneg {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (l i : n) : 0 ≤ limitMatrix P l i :=
  (bmk_L_markov hP).1 l i

/-- Columns of the limit matrix vanish at non-recurrent states. -/
lemma L_col_zero {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {i : n}
    (hi : ¬ IsRecurrent P i) (l : n) : limitMatrix P l i = 0 := by
  classical
  set μ : n → ℝ := fun s => limitMatrix P l s with hμdef
  have hμ0 : ∀ s, 0 ≤ μ s := fun s => L_nonneg hP l s
  have hμP : ∀ t, μ t = ∑ s, μ s * P s t := by
    intro t
    have := congrFun (congrFun (bmk_LP hP) l) t
    rw [Matrix.mul_apply] at this
    exact this.symm
  let U : Set n := {s | Accessible P s i}
  have hUi : i ∈ U := Relation.ReflTransGen.refl
  have hout : ∀ s t, s ∉ U → t ∈ U → P s t = 0 := by
    intro s t hs ht
    by_contra hne
    have hpos : 0 < P s t := lt_of_le_of_ne (hP.1 s t) (Ne.symm hne)
    exact hs (Relation.ReflTransGen.head hpos ht)
  let ind : n → ℝ := fun t => if t ∈ U then 1 else 0
  have hind0 : ∀ t, 0 ≤ ind t := fun t => by simp only [ind]; split_ifs <;> norm_num
  have hind1 : ∀ t, ind t ≤ 1 := fun t => by simp only [ind]; split_ifs <;> norm_num
  let q : n → ℝ := fun s => ∑ t, P s t * ind t
  have hq1 : ∀ s, q s ≤ 1 := by
    intro s
    calc q s ≤ ∑ t, P s t * 1 :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hind1 t) (hP.1 s t)
      _ = 1 := by simp [hP.2 s]
  have hq0 : ∀ s, s ∉ U → q s = 0 := by
    intro s hs
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : t ∈ U
    · rw [hout s t hs ht, zero_mul]
    · simp [ind, ht]
  have hsum : ∑ s, μ s * (ind s - q s) = 0 := by
    have e1 : ∑ s, μ s * ind s = ∑ s, μ s * q s := by
      calc ∑ s, μ s * ind s = ∑ t, ind t * ∑ s, μ s * P s t :=
            Finset.sum_congr rfl fun t _ => by rw [← hμP t, mul_comm]
        _ = ∑ s, μ s * q s := by
            simp only [q, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    simp_rw [mul_sub, Finset.sum_sub_distrib, e1, sub_self]
  have hterm0 : ∀ s, 0 ≤ μ s * (ind s - q s) := by
    intro s
    by_cases hs : s ∈ U
    · have : ind s = 1 := by simp [ind, hs]
      rw [this]; exact mul_nonneg (hμ0 s) (by linarith [hq1 s])
    · have : ind s = 0 := by simp [ind, hs]
      rw [this, hq0 s hs]; simp
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun s (_ : s ∈ Finset.univ) => hterm0 s)).mp hsum
  obtain ⟨j, hij, hji⟩ : ∃ j, Accessible P i j ∧ ¬ Accessible P j i := by
    simpa [IsRecurrent] using hi
  have hexit : ∃ a b, Accessible P i a ∧ a ∈ U ∧ b ∉ U ∧ 0 < P a b := by
    have hjU : j ∉ U := hji
    clear hji
    revert hjU
    induction hij with
    | refl => intro h; exact absurd hUi h
    | @tail k j' hik hkj ih =>
      intro hj'
      by_cases hk : k ∈ U
      · exact ⟨k, j', hik, hk, hj', hkj⟩
      · exact ih hk
  obtain ⟨a, b, hia, haU, hbU, hab⟩ := hexit
  have hμa : μ a = 0 := by
    by_contra hne
    have hpos : 0 < μ a := lt_of_le_of_ne (hμ0 a) (Ne.symm hne)
    have h1 := hzero a (Finset.mem_univ a)
    have hind : ind a = 1 := by simp [ind, haU]
    rw [hind] at h1
    have hqa : q a = 1 := by
      have := (mul_eq_zero.mp h1).resolve_left hpos.ne'
      linarith
    have hcomp : ∑ t, P a t * (1 - ind t) = 0 := by
      simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, hP.2 a]
      change 1 - q a = 0
      rw [hqa, sub_self]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun t (_ : t ∈ Finset.univ) =>
      mul_nonneg (hP.1 a t) (by linarith [hind1 t]))).mp hcomp
    have := hterm b (Finset.mem_univ b)
    have hindb : ind b = 0 := by simp [ind, hbU]
    rw [hindb, sub_zero, mul_one] at this
    linarith
  have hback : ∀ s, Accessible P s a → μ s = 0 := by
    intro s hs
    induction hs using Relation.ReflTransGen.head_induction_on with
    | refl => exact hμa
    | @head s' c hsc hca ih =>
      have hc := hμP c
      have hle : μ s' * P s' c ≤ ∑ t, μ t * P t c :=
        Finset.single_le_sum (f := fun t => μ t * P t c)
          (fun t _ => mul_nonneg (hμ0 t) (hP.1 t c)) (Finset.mem_univ s')
      rw [← hc, ih] at hle
      by_contra hne
      have := mul_pos (lt_of_le_of_ne (hμ0 s') (Ne.symm hne)) hsc
      linarith
  exact hback i hia

lemma pow_mul_L {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (k : ℕ) :
    P ^ k * limitMatrix P = limitMatrix P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Matrix.mul_assoc, ih, bmk_PL hP]

lemma S_mul_Z {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (m : ℕ) :
    (∑ k ∈ Finset.range m, (P ^ k - limitMatrix P)) * (1 - P + limitMatrix P) = 1 - P ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Matrix.add_mul, ih]
    have : (P ^ m - limitMatrix P) * (1 - P + limitMatrix P) = P ^ m - P ^ (m + 1) := by
      rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, pow_mul_L hP,
        Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP, pow_succ]
      abel
    rw [this]; abel

lemma L_mul_Zi {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    limitMatrix P * (1 - P + limitMatrix P)⁻¹ = limitMatrix P := by
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + limitMatrix P) * (1 - P + limitMatrix P)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hu
  have hLA : limitMatrix P * (1 - P + limitMatrix P) = limitMatrix P := by
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, bmk_LP hP, bmk_LL hP]; abel
  calc limitMatrix P * (1 - P + limitMatrix P)⁻¹
      = (limitMatrix P * (1 - P + limitMatrix P)) * (1 - P + limitMatrix P)⁻¹ := by rw [hLA]
    _ = limitMatrix P * ((1 - P + limitMatrix P) * (1 - P + limitMatrix P)⁻¹) :=
        Matrix.mul_assoc _ _ _
    _ = limitMatrix P := by rw [h1, Matrix.mul_one]

lemma Zi_mul_L {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    (1 - P + limitMatrix P)⁻¹ * limitMatrix P = limitMatrix P := by
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + limitMatrix P)⁻¹ * (1 - P + limitMatrix P) = 1 :=
    Matrix.nonsing_inv_mul _ hu
  have hAL : (1 - P + limitMatrix P) * limitMatrix P = limitMatrix P := by
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, bmk_PL hP, bmk_LL hP]; abel
  calc (1 - P + limitMatrix P)⁻¹ * limitMatrix P
      = (1 - P + limitMatrix P)⁻¹ * ((1 - P + limitMatrix P) * limitMatrix P) := by rw [hAL]
    _ = ((1 - P + limitMatrix P)⁻¹ * (1 - P + limitMatrix P)) * limitMatrix P :=
        (Matrix.mul_assoc _ _ _).symm
    _ = limitMatrix P := by rw [h1, Matrix.one_mul]

lemma DP_eq {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) :
    deviationMatrix P * P = deviationMatrix P + limitMatrix P - 1 := by
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + limitMatrix P)⁻¹ * (1 - P + limitMatrix P) = 1 :=
    Matrix.nonsing_inv_mul _ hu
  rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Zi_mul_L hP] at h1
  unfold deviationMatrix
  rw [Matrix.sub_mul, bmk_LP hP]
  generalize (1 - P + limitMatrix P)⁻¹ = Z at h1 ⊢
  have : Z * P = Z + limitMatrix P - 1 := by rw [← h1]; abel
  rw [this]; abel

lemma S_eq {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (m : ℕ) :
    ∑ k ∈ Finset.range m, (P ^ k - limitMatrix P) = (1 - P ^ m) * (1 - P + limitMatrix P)⁻¹ := by
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + limitMatrix P) * (1 - P + limitMatrix P)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hu
  rw [← S_mul_Z hP m, Matrix.mul_assoc, h1, Matrix.mul_one]

lemma avg_eq {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (N : ℕ) :
    ((N : ℝ) + 1)⁻¹ • ∑ m ∈ Finset.range (N + 1), ∑ k ∈ Finset.range m, (P ^ k - limitMatrix P) =
      (1 - cesaroMean P N) * (1 - P + limitMatrix P)⁻¹ := by
  simp_rw [S_eq hP]
  rw [← Finset.sum_mul, ← Matrix.smul_mul, Finset.sum_sub_distrib, smul_sub, bmk_avg_const]
  rfl

lemma D_col_nonneg {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (i : n)
    (hcol : ∀ k, limitMatrix P k i = 0) (k : n) : 0 ≤ deviationMatrix P k i := by
  have hD : deviationMatrix P = (1 - limitMatrix P) * (1 - P + limitMatrix P)⁻¹ := by
    unfold deviationMatrix
    rw [Matrix.sub_mul, Matrix.one_mul, L_mul_Zi hP]
  have ht0 : Tendsto (fun N => (1 - cesaroMean P N) * (1 - P + limitMatrix P)⁻¹) atTop
      (𝓝 ((1 - limitMatrix P) * (1 - P + limitMatrix P)⁻¹)) :=
    (tendsto_const_nhds.sub (bmk_tendsto hP)).mul_const _
  have ht : Tendsto (fun N => ((1 - cesaroMean P N) * (1 - P + limitMatrix P)⁻¹) k i) atTop
      (𝓝 (deviationMatrix P k i)) := by
    rw [hD]
    exact (((continuous_apply i).comp (continuous_apply k)).tendsto _).comp ht0
  apply ge_of_tendsto ht
  apply Eventually.of_forall
  intro N
  rw [← avg_eq hP N]
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.sub_apply, hcol, sub_zero, smul_eq_mul]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j _ => (bmk_pow hP j).1 k i)

end Chain

section Sys7
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma vec_fix_L {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {x : n → ℝ} (hx : x ᵥ* P = x) :
    x ᵥ* limitMatrix P = x := by
  have hk : ∀ k : ℕ, x ᵥ* (P ^ k) = x := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hx]
  have hA : ∀ N, x ᵥ* cesaroMean P N = x := by
    intro N
    rw [cesaroMean, Matrix.vecMul_smul, Matrix.vecMul_sum]
    simp_rw [hk]
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (by positivity), one_smul]
  have t : Tendsto (fun N => x ᵥ* cesaroMean P N) atTop (𝓝 (x ᵥ* limitMatrix P)) :=
    ((continuous_const.matrix_vecMul continuous_id).tendsto _).comp (bmk_tendsto hP)
  simp_rw [hA] at t
  exact (tendsto_nhds_unique tendsto_const_nhds t).symm

theorem sys7 (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (β x y : n → ℝ)
    (h3 : x ᵥ* (1 - P) = 0) (h4 : x + y ᵥ* (1 - P) = β) :
    x = β ᵥ* limitMatrix P ∧ y = β ᵥ* deviationMatrix P + y ᵥ* limitMatrix P := by
  have hxP : x ᵥ* P = x := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at h3; exact h3.symm
  have hxL : x ᵥ* limitMatrix P = x := vec_fix_L hP hxP
  have hIPL : (1 - P) * limitMatrix P = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, bmk_PL hP, sub_self]
  have hx : x = β ᵥ* limitMatrix P := by
    have := congrArg (fun v => v ᵥ* limitMatrix P) h4
    simp only [Matrix.add_vecMul, Matrix.vecMul_vecMul, hIPL, Matrix.vecMul_zero, add_zero,
      hxL] at this
    exact this
  refine ⟨hx, ?_⟩
  have hu := bmk_Z_unit hP
  have h1 : (1 - P + limitMatrix P) * (1 - P + limitMatrix P)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hu
  have e1 : y ᵥ* (1 - P) = β ᵥ* (1 - limitMatrix P) := by
    rw [Matrix.vecMul_sub (1 : Matrix n n ℝ) (limitMatrix P) β, Matrix.vecMul_one β, ← hx, ← h4]
    abel
  have e2 : y ᵥ* (1 - P + limitMatrix P) = β ᵥ* (1 - limitMatrix P) + y ᵥ* limitMatrix P := by
    rw [Matrix.vecMul_add, e1]
  calc y = y ᵥ* ((1 - P + limitMatrix P) * (1 - P + limitMatrix P)⁻¹) := by
          rw [h1, Matrix.vecMul_one]
    _ = (β ᵥ* (1 - limitMatrix P) + y ᵥ* limitMatrix P) ᵥ* (1 - P + limitMatrix P)⁻¹ := by
          rw [← Matrix.vecMul_vecMul, e2]
    _ = β ᵥ* ((1 - limitMatrix P) * (1 - P + limitMatrix P)⁻¹) +
          y ᵥ* (limitMatrix P * (1 - P + limitMatrix P)⁻¹) := by
          rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul]
    _ = β ᵥ* deviationMatrix P + y ᵥ* limitMatrix P := by
          rw [Matrix.sub_mul, Matrix.one_mul, L_mul_Zi hP]; rfl

theorem sys7_transient (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (β x y : n → ℝ)
    (h3 : x ᵥ* (1 - P) = 0) (h4 : x + y ᵥ* (1 - P) = β) (i : n) (hi : ¬ IsRecurrent P i) :
    y i = (β ᵥ* deviationMatrix P) i := by
  have h := congrFun (sys7 P hP β x y h3 h4).2 i
  have hc : (y ᵥ* limitMatrix P) i = 0 := by
    simp only [Matrix.vecMul, dotProduct]
    exact Finset.sum_eq_zero fun k _ => by rw [L_col_zero hP hi k, mul_zero]
  rw [Pi.add_apply, hc, add_zero] at h
  exact h

lemma mem_ergodicSet_iff (P : Matrix n n ℝ) (l i : n) :
    i ∈ ergodicSet P l ↔ Accessible P l i := by
  classical
  simp [ergodicSet]

theorem inv_vanish (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (l : n) (hl : IsRecurrent P l)
    (z : n → ℝ) (hz : ∀ i ∈ ergodicSet P l, z i = ∑ k ∈ ergodicSet P l, z k * P k i)
    (i₀ : n) (hi₀ : i₀ ∈ ergodicSet P l) (hz₀ : z i₀ = 0) :
    ∀ i ∈ ergodicSet P l, z i = 0 := by
  classical
  have memC := mem_ergodicSet_iff P l
  have closed : ∀ k i, k ∈ ergodicSet P l → 0 < P k i → i ∈ ergodicSet P l :=
    fun k i hk hp => (memC i).2 (((memC k).1 hk).tail hp)
  have rowC : ∀ k ∈ ergodicSet P l, ∑ i ∈ ergodicSet P l, P k i = 1 := by
    intro k hk
    rw [← hP.2 k]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    by_contra hne
    exact hi (closed k i hk (lt_of_le_of_ne (hP.1 k i) (Ne.symm hne)))
  have sub : ∀ i ∈ ergodicSet P l, |z i| ≤ ∑ k ∈ ergodicSet P l, |z k| * P k i := by
    intro i hi
    rw [hz i hi]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun k _ => by rw [abs_mul, abs_of_nonneg (hP.1 k i)]
  have tot : ∑ i ∈ ergodicSet P l, ∑ k ∈ ergodicSet P l, |z k| * P k i =
      ∑ i ∈ ergodicSet P l, |z i| := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k hk => by rw [← Finset.mul_sum, rowC k hk, mul_one]
  have heq : ∀ i ∈ ergodicSet P l, |z i| = ∑ k ∈ ergodicSet P l, |z k| * P k i := by
    have hsum : ∑ i ∈ ergodicSet P l, (∑ k ∈ ergodicSet P l, |z k| * P k i - |z i|) = 0 := by
      rw [Finset.sum_sub_distrib, tot, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => sub_nonneg.2 (sub i hi))).1 hsum
    intro i hi; linarith [this i hi]
  have pred : ∀ k j, k ∈ ergodicSet P l → j ∈ ergodicSet P l → 0 < P k j → z j = 0 →
      z k = 0 := by
    intro k j hk hj hp hzj
    have e := heq j hj
    rw [hzj, abs_zero] at e
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k' _ => mul_nonneg (abs_nonneg (z k')) (hP.1 k' j))).1 e.symm k hk
    rcases mul_eq_zero.1 this with h | h
    · exact abs_eq_zero.1 h
    · exact absurd h (ne_of_gt hp)
  have key : ∀ s, Accessible P s i₀ → s ∈ ergodicSet P l → z s = 0 := by
    intro s hs
    induction hs using Relation.ReflTransGen.head_induction_on with
    | refl => intro _; exact hz₀
    | @head s' c hsc hca ih =>
      intro hs'
      exact pred s' c hs' (closed s' c hs' hsc) hsc (ih (closed s' c hs' hsc))
  intro i hi
  have hil : Accessible P i l := hl i ((memC i).1 hi)
  exact key i (hil.trans ((memC i₀).1 hi₀)) hi

end Sys7

section Gamma
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma rec_of_mem {P : Matrix n n ℝ} {l k : n} (hl : IsRecurrent P l)
    (hk : k ∈ ergodicSet P l) : IsRecurrent P k := by
  have hlk := (mem_ergodicSet_iff P l k).1 hk
  intro m hkm
  exact (hl m (hlk.trans hkm)).trans hlk

lemma ergodicSet_eq_of_mem {P : Matrix n n ℝ} {l k : n} (hl : IsRecurrent P l)
    (hk : k ∈ ergodicSet P l) : ergodicSet P k = ergodicSet P l := by
  have hlk := (mem_ergodicSet_iff P l k).1 hk
  have hkl := hl k hlk
  ext m
  rw [mem_ergodicSet_iff, mem_ergodicSet_iff]
  exact ⟨fun h => hlk.trans h, fun h => hkl.trans h⟩

lemma gamma_rec (P : Matrix n n ℝ) (β : n → ℝ) {l : n} (hl : IsRecurrent P l) :
    gamma P β l = (ergodicSet P l).sup' ⟨l, mem_ergodicSet_self P l⟩
      (fun i => (-(∑ k, β k * deviationMatrix P k i)) /
        (∑ k ∈ ergodicSet P l, limitMatrix P k i)) := by
  unfold gamma
  rw [if_pos hl]

lemma gamma_not_rec (P : Matrix n n ℝ) (β : n → ℝ) {l : n} (hl : ¬ IsRecurrent P l) :
    gamma P β l = 0 := by
  unfold gamma
  rw [if_neg hl]

lemma sup'_congr_all {ι : Type*} (s t : Finset ι) (hs : s.Nonempty) (ht : t.Nonempty)
    (g h : ι → ℝ) (hst : s = t) (hgh : g = h) : s.sup' hs g = t.sup' ht h := by
  subst hst; subst hgh; rfl

lemma gamma_eq_of_mem (P : Matrix n n ℝ) (β : n → ℝ) {l k : n} (hl : IsRecurrent P l)
    (hk : k ∈ ergodicSet P l) : gamma P β k = gamma P β l := by
  rw [gamma_rec P β hl, gamma_rec P β (rec_of_mem hl hk)]
  have he := ergodicSet_eq_of_mem hl hk
  apply sup'_congr_all _ _ _ _ _ _ he
  funext i; rw [he]

lemma le_gamma (P : Matrix n n ℝ) (β : n → ℝ) {l i : n} (hl : IsRecurrent P l)
    (hi : i ∈ ergodicSet P l) :
    (-(∑ k, β k * deviationMatrix P k i)) / (∑ k ∈ ergodicSet P l, limitMatrix P k i) ≤
      gamma P β l := by
  rw [gamma_rec P β hl]
  exact Finset.le_sup' (fun i => (-(∑ k, β k * deviationMatrix P k i)) /
    (∑ k ∈ ergodicSet P l, limitMatrix P k i)) hi

lemma L_diag_pos {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {i : n} (hi : IsRecurrent P i) :
    0 < limitMatrix P i i := by
  by_contra hneg
  have h0 : limitMatrix P i i = 0 := le_antisymm (not_lt.1 hneg) (L_nonneg hP i i)
  have hμP : ∀ t, limitMatrix P i t = ∑ s, limitMatrix P i s * P s t := by
    intro t
    have := congrFun (congrFun (bmk_LP hP) i) t
    rw [Matrix.mul_apply] at this
    exact this.symm
  have hback : ∀ s, Accessible P s i → limitMatrix P i s = 0 := by
    intro s hs
    induction hs using Relation.ReflTransGen.head_induction_on with
    | refl => exact h0
    | @head s' c hsc hca ih =>
      have hle : limitMatrix P i s' * P s' c ≤ ∑ t, limitMatrix P i t * P t c :=
        Finset.single_le_sum (f := fun t => limitMatrix P i t * P t c)
          (fun t _ => mul_nonneg (L_nonneg hP i t) (hP.1 t c)) (Finset.mem_univ s')
      rw [← hμP c, ih] at hle
      by_contra hne
      have := mul_pos (lt_of_le_of_ne (L_nonneg hP i s') (Ne.symm hne)) hsc
      linarith
  have hall : ∀ s, limitMatrix P i s = 0 := by
    intro s
    by_contra hne
    have hpos := lt_of_le_of_ne (L_nonneg hP i s) (Ne.symm hne)
    exact hne (hback s (hi s (acc_of_L_pos hP hpos)))
  have := (bmk_L_markov hP).2 i
  simp [hall] at this

/-- On the ergodic set of a recurrent `l`, `(γ^T P*)_i = γ_l ∑_{k ∈ E} p*_ki`. -/
lemma gammaL_on_class {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (β : n → ℝ) {l i : n}
    (hl : IsRecurrent P l) (hi : i ∈ ergodicSet P l) :
    (gamma P β ᵥ* limitMatrix P) i = gamma P β l * ∑ k ∈ ergodicSet P l, limitMatrix P k i := by
  have hli := (mem_ergodicSet_iff P l i).1 hi
  simp only [Matrix.vecMul, dotProduct]
  calc ∑ k, gamma P β k * limitMatrix P k i
      = ∑ k ∈ ergodicSet P l, gamma P β k * limitMatrix P k i := by
        refine (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => ?_)).symm
        by_cases hL : limitMatrix P k i = 0
        · rw [hL, mul_zero]
        · have hpos := lt_of_le_of_ne (L_nonneg hP k i) (Ne.symm hL)
          have hki := acc_of_L_pos hP hpos
          by_cases hkr : IsRecurrent P k
          · exact absurd ((mem_ergodicSet_iff P l k).2 (hli.trans (hkr i hki))) hk
          · rw [gamma_not_rec P β hkr, zero_mul]
    _ = ∑ k ∈ ergodicSet P l, gamma P β l * limitMatrix P k i :=
        Finset.sum_congr rfl fun k hk => by rw [gamma_eq_of_mem P β hl hk]
    _ = _ := by rw [Finset.mul_sum]

lemma den_pos {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) {l i : n}
    (hl : IsRecurrent P l) (hi : i ∈ ergodicSet P l) :
    0 < ∑ k ∈ ergodicSet P l, limitMatrix P k i :=
  lt_of_lt_of_le (L_diag_pos hP (rec_of_mem hl hi))
    (Finset.single_le_sum (f := fun k => limitMatrix P k i) (fun k _ => L_nonneg hP k i) hi)

/-- The `y`-coefficient `[β^T D + γ^T P*]_i` vanishes at some state of every ergodic set. -/
theorem ycoef_zero {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (β : n → ℝ) {l : n}
    (hl : IsRecurrent P l) :
    ∃ i ∈ ergodicSet P l,
      (β ᵥ* deviationMatrix P + gamma P β ᵥ* limitMatrix P) i = 0 := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' ⟨l, mem_ergodicSet_self P l⟩
    (fun i => (-(∑ k, β k * deviationMatrix P k i)) /
      (∑ k ∈ ergodicSet P l, limitMatrix P k i))
  refine ⟨i, hi, ?_⟩
  have hg : gamma P β l = (-(∑ k, β k * deviationMatrix P k i)) /
      (∑ k ∈ ergodicSet P l, limitMatrix P k i) := by
    rw [gamma_rec P β hl]; exact hmax
  have hd := den_pos hP hl hi
  rw [Pi.add_apply, gammaL_on_class hP β hl hi, hg, div_mul_cancel₀ _ hd.ne']
  simp only [Matrix.vecMul, dotProduct]
  ring

/-- Nonnegativity of the `y`-coefficient `[β^T D + γ^T P*]_i` (p. 360). -/
theorem ycoef_nonneg {P : Matrix n n ℝ} (hP : IsMarkovMatrix P) (β : n → ℝ)
    (hβ : ∀ i, 0 < β i) (i : n) :
    0 ≤ (β ᵥ* deviationMatrix P + gamma P β ᵥ* limitMatrix P) i := by
  rw [Pi.add_apply]
  by_cases hrec : IsRecurrent P i
  · rw [gammaL_on_class hP β hrec (mem_ergodicSet_self P i)]
    have hd := den_pos hP hrec (mem_ergodicSet_self P i)
    have hg := le_gamma P β hrec (mem_ergodicSet_self P i)
    rw [div_le_iff₀ hd] at hg
    simp only [Matrix.vecMul, dotProduct] at hg ⊢
    linarith
  · have hc : (gamma P β ᵥ* limitMatrix P) i = 0 := by
      simp only [Matrix.vecMul, dotProduct]
      exact Finset.sum_eq_zero fun k _ => by rw [L_col_zero hP hrec k, mul_zero]
    rw [hc, add_zero]
    simp only [Matrix.vecMul, dotProduct]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hβ k).le
      (D_col_nonneg hP i (fun k => L_col_zero hP hrec k) k)

end Gamma

section MDP
variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

lemma policyMatrix_markov (M : StationaryMDP S A) (π : S → A → ℝ) (hπ : IsStationaryRule M π) :
    IsMarkovMatrix (policyMatrix M π) := by
  refine ⟨fun i j => Finset.sum_nonneg fun a ha => mul_nonneg (M.trans_nonneg i a j)
    (hπ.1 i a ha), fun i => ?_⟩
  unfold policyMatrix
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, M.trans_sum, one_mul]
  exact hπ.2 i

def pairEquiv (M : StationaryMDP S A) : Pair M ≃ Σ i : S, {a // a ∈ M.admissible i} where
  toFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv p := rfl
  right_inv q := rfl

lemma pair_sum (M : StationaryMDP S A) (g : S → A → ℝ) :
    ∑ p : Pair M, g p.1.1 p.1.2 = ∑ i, ∑ a ∈ M.admissible i, g i a := by
  rw [Fintype.sum_equiv (pairEquiv M) (fun p : Pair M => g p.1.1 p.1.2)
    (fun q => g q.1 q.2.1) (fun p => rfl)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_coe_sort (M.admissible i) (g i)

lemma mass_form (M : StationaryMDP S A) (π : S → A → ℝ) (hπ : IsStationaryRule M π)
    (F : S → ℝ) (j : S) :
    (∑ p : Pair M, if p.1.1 = j then F p.1.1 * π p.1.1 p.1.2 else 0) = F j := by
  rw [pair_sum M (fun i a => if i = j then F i * π i a else 0)]
  rw [Finset.sum_eq_single j]
  · simp only [if_true]
    rw [← Finset.mul_sum, hπ.2 j, mul_one]
  · intro i _ hij
    exact Finset.sum_eq_zero fun a _ => if_neg hij
  · intro h; exact absurd (Finset.mem_univ j) h

lemma flow_form (M : StationaryMDP S A) (π : S → A → ℝ) (hπ : IsStationaryRule M π)
    (F : S → ℝ) (j : S) :
    ∑ p : Pair M, ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) *
      (F p.1.1 * π p.1.1 p.1.2) = F j - (F ᵥ* policyMatrix M π) j := by
  have e1 : ∀ p : Pair M, ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) *
      (F p.1.1 * π p.1.1 p.1.2) = (if p.1.1 = j then F p.1.1 * π p.1.1 p.1.2 else 0) -
        M.trans p.1.1 p.1.2 j * (F p.1.1 * π p.1.1 p.1.2) := by
    intro p; split_ifs <;> ring
  simp_rw [e1]
  rw [Finset.sum_sub_distrib, mass_form M π hπ F j]
  congr 1
  rw [pair_sum M (fun i a => M.trans i a j * (F i * π i a))]
  simp only [Matrix.vecMul, dotProduct, policyMatrix]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem rep_feasible (M : StationaryMDP S A) (β : S → ℝ) (hβpos : ∀ j, 0 < β j)
    (π : S → A → ℝ) (hπ : IsStationaryRule M π) :
    (repX M β π, repY M β π) ∈ dualFeasible M β := by
  have hP := policyMatrix_markov M π hπ
  refine ⟨fun j => ?_, fun j => ?_, fun p => ?_, fun p => ?_⟩
  · change ∑ p : Pair M, ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) *
      ((β ᵥ* limitMatrix (policyMatrix M π)) p.1.1 * π p.1.1 p.1.2) = 0
    rw [flow_form M π hπ, Matrix.vecMul_vecMul, bmk_LP hP, sub_self]
  · change (∑ p : Pair M, if p.1.1 = j then
        (β ᵥ* limitMatrix (policyMatrix M π)) p.1.1 * π p.1.1 p.1.2 else 0) +
      ∑ p : Pair M, ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) *
      ((β ᵥ* deviationMatrix (policyMatrix M π) +
        gamma (policyMatrix M π) β ᵥ* limitMatrix (policyMatrix M π)) p.1.1 * π p.1.1 p.1.2)
      = β j
    rw [mass_form M π hπ, flow_form M π hπ, Matrix.add_vecMul, Matrix.vecMul_vecMul,
      Matrix.vecMul_vecMul, bmk_LP hP, DP_eq hP]
    simp only [Pi.add_apply, Matrix.vecMul_sub, Matrix.vecMul_add, Matrix.vecMul_one,
      Pi.sub_apply]
    ring
  · exact mul_nonneg (by
      simp only [Matrix.vecMul, dotProduct]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hβpos k).le (L_nonneg hP k _))
      (hπ.1 _ _ p.2)
  · exact mul_nonneg (ycoef_nonneg hP β hβpos _) (hπ.1 _ _ p.2)

lemma pure_isRule (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) :
    IsStationaryRule M (pureRule f) := by
  refine ⟨fun i a _ => ?_, fun i => ?_⟩
  · unfold pureRule; split_ifs <;> norm_num
  · simp [pureRule, hf i]

lemma policy_pure (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i)
    (i j : S) : policyMatrix M (pureRule f) i j = M.trans i (f i) j := by
  simp [policyMatrix, pureRule, hf i]

theorem repY_zero (M : StationaryMDP S A) (β : S → ℝ) (f : S → A)
    (hf : ∀ i, f i ∈ M.admissible i) (l : S)
    (hl : IsRecurrent (policyMatrix M (pureRule f)) l) :
    ∃ i ∈ ergodicSet (policyMatrix M (pureRule f)) l,
      repY M β (pureRule f) ⟨(i, f i), hf i⟩ = 0 := by
  obtain ⟨i, hi, h0⟩ := ycoef_zero (policyMatrix_markov M _ (pure_isRule M f hf)) β hl
  refine ⟨i, hi, ?_⟩
  change (β ᵥ* deviationMatrix (policyMatrix M (pureRule f)) +
      gamma (policyMatrix M (pureRule f)) β ᵥ* limitMatrix (policyMatrix M (pureRule f))) i *
      pureRule f i (f i) = 0
  rw [h0, zero_mul]

end MDP

end HordijkKallenbergLP.ExtremePoint.Aux


open HordijkKallenbergLP.ExtremePoint in
theorem solution {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : IsMarkovMatrix P) (β x y : n → ℝ) (h3 : x ᵥ* (1 - P) = 0)
    (h4 : x + y ᵥ* (1 - P) = β) :
    x = β ᵥ* limitMatrix P ∧ y = β ᵥ* deviationMatrix P + y ᵥ* limitMatrix P :=
  Aux.sys7 P hP β x y h3 h4
