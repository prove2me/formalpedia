-- Prove2me | solution 1 for MDPFinance.InfiniteHorizonApplications.theorem_7_6_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:25:23.389257+00:00
-- url     : https://prove2.me/submissions/2c29cf19-9a98-46ce-b59d-f9df6895acb0

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Bandit

open MeasureTheory ProbabilityTheory


namespace MDPFinance.InfiniteHorizonApplications

section Gen
variable {β : ℝ} {q : ℕ × ℕ → ℝ}

lemma gk_PQ_le_add (hq : ∀ mn, 0 ≤ q mn ∧ q mn ≤ 1) (v w : ℕ × ℕ → ℝ) (c : ℝ)
    (h : ∀ mn, v mn ≤ w mn + c) (mn : ℕ × ℕ) : PQ q v mn ≤ PQ q w mn + c := by
  unfold PQ
  have h1 := h (mn.1+1, mn.2)
  have h2 := h (mn.1, mn.2+1)
  obtain ⟨a, b⟩ := hq mn
  nlinarith [mul_le_mul_of_nonneg_left h1 a, mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ 1 - q mn)]

lemma gk_PQ_const (c : ℝ) (mn : ℕ × ℕ) : PQ q (fun _ => c) mn = c := by
  unfold PQ; ring

lemma gk_PQ_add (v : ℕ × ℕ → ℝ) (c : ℝ) (mn : ℕ × ℕ) :
    PQ q (fun x => v x + c) mn = PQ q v mn + c := by
  unfold PQ; ring

lemma gk_PQ_lin (v w : ℕ × ℕ → ℝ) (a b : ℝ) (mn : ℕ × ℕ) :
    PQ q (fun x => a * v x + b * w x) mn = a * PQ q v mn + b * PQ q w mn := by
  unfold PQ; ring

lemma gk_comp (hβ0 : 0 < β) (hβ1 : β < 1) (hq : ∀ mn, 0 ≤ q mn ∧ q mn ≤ 1) (K K' : ℝ)
    (hK : K ≤ K') (v w : ℕ × ℕ → ℝ)
    (hv : ∀ mn, v mn ≤ max K (q mn + β * PQ q v mn))
    (hw : ∀ mn, max K' (q mn + β * PQ q w mn) ≤ w mn)
    (hb : ∃ C, ∀ mn, v mn - w mn ≤ C) : ∀ mn, v mn ≤ w mn := by
  obtain ⟨C, hC⟩ := hb
  have key : ∀ n : ℕ, ∀ mn, v mn ≤ w mn + β ^ n * max C 0 := by
    intro n
    induction n with
    | zero => intro mn; simp; linarith [hC mn, le_max_left C 0]
    | succ n ih =>
      intro mn
      have hP := gk_PQ_le_add hq v w _ ih mn
      have hP' := mul_le_mul_of_nonneg_left hP hβ0.le
      have e : β ^ (n+1) * max C 0 = β * (β ^ n * max C 0) := by ring
      calc v mn ≤ max K (q mn + β * PQ q v mn) := hv mn
        _ ≤ max K' (q mn + β * PQ q w mn) + β^(n+1) * max C 0 := by
          have hc : 0 ≤ β ^ (n+1) * max C 0 :=
            mul_nonneg (pow_nonneg hβ0.le _) (le_max_right _ _)
          apply max_le
          · have := le_max_left K' (q mn + β * PQ q w mn); linarith
          · have := le_max_right K' (q mn + β * PQ q w mn); rw [e]; linarith
        _ ≤ w mn + β ^ (n+1) * max C 0 := by linarith [hw mn]
  intro mn
  have ht : Filter.Tendsto (fun n : ℕ => w mn + β ^ n * max C 0) Filter.atTop
      (nhds (w mn + 0 * max C 0)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul
      tendsto_const_nhds)
  simp only [zero_mul, add_zero] at ht
  exact ge_of_tendsto' ht (fun n => key n mn)

variable (KS : KStoppingValue β q)

lemma gk_bdd (K K' : ℝ) (c : ℝ) : ∃ C, ∀ mn, KS.J K mn - (KS.J K' mn + c) ≤ C := by
  obtain ⟨C1, h1⟩ := KS.hJ_bdd K
  obtain ⟨C2, h2⟩ := KS.hJ_bdd K'
  refine ⟨C1 + C2 + |c|, fun mn => ?_⟩
  have := h1 mn; have := h2 mn
  have := abs_le.1 (h1 mn); have := abs_le.1 (h2 mn); have := neg_abs_le c
  linarith

lemma gk_ge (K : ℝ) (mn : ℕ × ℕ) : K ≤ KS.J K mn := by
  rw [KS.hJ_fix]; exact le_max_left _ _

lemma gk_ge_A (K : ℝ) (mn : ℕ × ℕ) : q mn + β * PQ q (KS.J K) mn ≤ KS.J K mn := by
  rw [KS.hJ_fix K mn]; exact le_max_right _ _

lemma gk_mono {K K' : ℝ} (h : K ≤ K') (mn : ℕ × ℕ) : KS.J K mn ≤ KS.J K' mn := by
  refine gk_comp KS.hβ0 KS.hβ1 KS.hq K K' h (KS.J K) (KS.J K') (fun x => (KS.hJ_fix K x).le)
    (fun x => (KS.hJ_fix K' x).ge) ?_ mn
  obtain ⟨C, hC⟩ := gk_bdd KS K K' 0
  exact ⟨C, fun x => by have := hC x; linarith⟩

lemma gk_sub {K K' : ℝ} (h : K ≤ K') (mn : ℕ × ℕ) : KS.J K' mn ≤ KS.J K mn + (K' - K) := by
  refine gk_comp KS.hβ0 KS.hβ1 KS.hq K' K' le_rfl (KS.J K') (fun x => KS.J K x + (K' - K))
    (fun x => (KS.hJ_fix K' x).le) ?_ ?_ mn
  · intro x
    rw [gk_PQ_add]
    have h1 := gk_ge KS K x
    have h2 := gk_ge_A KS K x
    have hb := KS.hβ0; have hb1 := KS.hβ1
    apply max_le
    · linarith
    · nlinarith
  · obtain ⟨C, hC⟩ := gk_bdd KS K' K (K' - K)
    exact ⟨C, hC⟩

lemma gk_lip (K K' : ℝ) (mn : ℕ × ℕ) : |KS.J K mn - KS.J K' mn| ≤ |K - K'| := by
  rcases le_total K K' with h | h
  · have := gk_mono KS h mn; have := gk_sub KS h mn
    rw [abs_le, abs_of_nonpos (by linarith : K - K' ≤ 0)]; constructor <;> linarith
  · have := gk_mono KS h mn; have := gk_sub KS h mn
    rw [abs_le, abs_of_nonneg (by linarith : 0 ≤ K - K')]; constructor <;> linarith

lemma gk_cont (mn : ℕ × ℕ) : Continuous (KS.J · mn) := by
  have : LipschitzWith 1 (KS.J · mn) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    exact gk_lip KS x y mn
  exact this.continuous

lemma gk_convex (mn : ℕ × ℕ) : ConvexOn ℝ Set.univ (KS.J · mn) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  refine gk_comp KS.hβ0 KS.hβ1 KS.hq (a * x + b * y) (a * x + b * y) le_rfl
    (KS.J (a * x + b * y)) (fun z => a * KS.J x z + b * KS.J y z)
    (fun z => (KS.hJ_fix _ z).le) ?_ ?_ mn
  · intro z
    rw [gk_PQ_lin]
    have h1 := gk_ge KS x z
    have h2 := gk_ge_A KS x z
    have h3 := gk_ge KS y z
    have h4 := gk_ge_A KS y z
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h3 hb]
    · have e : q z + β * (a * PQ q (KS.J x) z + b * PQ q (KS.J y) z) =
          a * (q z + β * PQ q (KS.J x) z) + b * (q z + β * PQ q (KS.J y) z) := by
        have : q z = (a + b) * q z := by rw [hab, one_mul]
        linear_combination this
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h4 hb]
  · obtain ⟨C1, h1⟩ := KS.hJ_bdd (a * x + b * y)
    obtain ⟨C2, h2⟩ := KS.hJ_bdd x
    obtain ⟨C3, h3⟩ := KS.hJ_bdd y
    refine ⟨C1 + a * C2 + b * C3, fun z => ?_⟩
    have := abs_le.1 (h1 z); have := abs_le.1 (h2 z); have := abs_le.1 (h3 z)
    nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 (h2 z)).1 ha,
      mul_le_mul_of_nonneg_left (abs_le.1 (h3 z)).1 hb]

lemma gk_le_const (K : ℝ) (mn : ℕ × ℕ) : KS.J K mn ≤ max K (1 / (1 - β)) := by
  have hb := KS.hβ0; have hb1 := KS.hβ1
  refine gk_comp KS.hβ0 KS.hβ1 KS.hq K K le_rfl (KS.J K) (fun _ => max K (1 / (1 - β)))
    (fun x => (KS.hJ_fix K x).le) ?_ ?_ mn
  · intro z
    rw [gk_PQ_const]
    apply max_le (le_max_left _ _)
    have hq := (KS.hq z).2
    have h1 : 1 / (1 - β) ≤ max K (1 / (1 - β)) := le_max_right _ _
    have h2 : 1 ≤ (1 - β) * max K (1 / (1 - β)) := by
      rw [div_le_iff₀ (by linarith)] at h1; linarith
    nlinarith
  · obtain ⟨C, hC⟩ := KS.hJ_bdd K
    exact ⟨C - max K (1 / (1 - β)), fun z => by have := (abs_le.1 (hC z)).2; linarith⟩

lemma gk_sinf_mem (mn : ℕ × ℕ) : KS.J (GittinsIndex KS mn) mn = GittinsIndex KS mn := by
  have hb := KS.hβ0; have hb1 := KS.hβ1
  have hclosed : IsClosed {K : ℝ | KS.J K mn = K} := isClosed_eq (gk_cont KS mn) continuous_id
  have hne : ({K : ℝ | KS.J K mn = K}).Nonempty := by
    refine ⟨1 / (1 - β), le_antisymm ?_ (gk_ge KS _ _)⟩
    have := gk_le_const KS (1 / (1 - β)) mn
    rwa [max_self] at this
  have hbdd : BddBelow {K : ℝ | KS.J K mn = K} := by
    refine ⟨q mn / (1 - β), fun K hK => ?_⟩
    simp only [Set.mem_setOf_eq] at hK
    have h1 := gk_ge_A KS K mn
    have h2 := gk_PQ_le_add KS.hq (fun _ => K) (KS.J K) 0 (fun x => by simp [gk_ge KS K x]) mn
    rw [gk_PQ_const] at h2
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  exact hclosed.csInf_mem hne hbdd

lemma gk_iff (K : ℝ) (mn : ℕ × ℕ) : KS.J K mn = K ↔ GittinsIndex KS mn ≤ K := by
  constructor
  · intro h
    show sInf {K : ℝ | KS.J K mn = K} ≤ K
    refine csInf_le ?_ (show K ∈ {K : ℝ | KS.J K mn = K} from h)
    refine ⟨q mn / (1 - β), fun K hK => ?_⟩
    have hb := KS.hβ0; have hb1 := KS.hβ1
    simp only [Set.mem_setOf_eq] at hK
    have h1 := gk_ge_A KS K mn
    have h2 := gk_PQ_le_add KS.hq (fun _ => K) (KS.J K) 0 (fun x => by simp [gk_ge KS K x]) mn
    rw [gk_PQ_const] at h2
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · intro h
    have h1 := gk_sub KS h mn
    rw [gk_sinf_mem] at h1
    exact le_antisymm (by linarith) (gk_ge KS K mn)

lemma gk_lower (mn : ℕ × ℕ) : q mn / (1 - β) ≤ GittinsIndex KS mn := by
  have hb := KS.hβ0; have hb1 := KS.hβ1
  set K := GittinsIndex KS mn
  have hK := gk_sinf_mem KS mn
  have h1 := gk_ge_A KS K mn
  have h2 := gk_PQ_le_add KS.hq (fun _ => K) (KS.J K) 0 (fun x => by simp [gk_ge KS K x]) mn
  rw [gk_PQ_const] at h2
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma gk_upper (mn : ℕ × ℕ) : GittinsIndex KS mn ≤ 1 / (1 - β) := by
  rw [← gk_iff]
  refine le_antisymm ?_ (gk_ge KS _ _)
  have := gk_le_const KS (1 / (1 - β)) mn
  rwa [max_self] at this

lemma gk_below (K : ℝ) (mn : ℕ × ℕ) (hK : K < GittinsIndex KS mn) :
    KS.J K mn = q mn + β * PQ q (KS.J K) mn := by
  have hne : KS.J K mn ≠ K := fun h => absurd ((gk_iff KS K mn).1 h) (not_le.2 hK)
  have := KS.hJ_fix K mn
  rcases le_total K (q mn + β * PQ q (KS.J K) mn) with h | h
  · rw [max_eq_right h] at this; exact this
  · rw [max_eq_left h] at this; exact absurd this hne

lemma gk_indiff (mn : ℕ × ℕ) :
    GittinsIndex KS mn = q mn + β * PQ q (KS.J (GittinsIndex KS mn)) mn := by
  set I := GittinsIndex KS mn with hI
  have hb := KS.hβ0
  have hmem := gk_sinf_mem KS mn
  rw [← hI] at hmem
  have hA := gk_ge_A KS I mn
  rw [hmem] at hA
  refine le_antisymm ?_ hA
  by_contra hlt
  push Not at hlt
  set D := I - (q mn + β * PQ q (KS.J I) mn)
  have hD : 0 < D := by simp only [D]; linarith
  have hK : I - D < I := by linarith
  have h1 := gk_below KS (I - D) mn hK
  have h2 : ∀ x, KS.J I x ≤ KS.J (I - D) x + D := by
    intro x; have := gk_sub KS hK.le x; linarith
  have h3 := gk_PQ_le_add KS.hq _ _ D h2 mn
  have h4 := gk_mono KS hK.le
  have h5 : PQ q (KS.J (I - D)) mn ≤ PQ q (KS.J I) mn := by
    have := gk_PQ_le_add KS.hq (KS.J (I - D)) (KS.J I) 0 (fun x => by simp [h4 x]) mn
    linarith
  have h6 := gk_sub KS hK.le mn
  rw [hmem] at h6
  -- J (I-D) mn ≥ I - D, and = q + β PQ(J(I-D)) ≤ q + β PQ(J I) = I - D
  have h7 : KS.J (I - D) mn ≤ q mn + β * PQ q (KS.J I) mn := by
    rw [h1]; nlinarith
  have h8 := gk_ge KS (I - D) mn
  -- so J(I-D) mn = I - D, contradiction with below
  have h9 : KS.J (I - D) mn = I - D := by
    apply le_antisymm _ h8; simp only [D] at h7 ⊢; linarith
  exact absurd ((gk_iff KS _ mn).1 h9) (not_le.2 hK)

end Gen


lemma g6_states_congr (i0 : ℕ × ℕ) (w w' : ℕ → Bool) (j : ℕ) (h : ∀ i < j, w i = w' i) :
    statesOf i0 w j = statesOf i0 w' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [statesOf]
    rw [ih (fun i hi => h i (by omega)), h j (by omega)]

lemma g6_ext_snoc_lt {k : ℕ} (w : Fin k → Bool) (b : Bool) (i : ℕ) (hi : i < k) :
    extendPrefix (Fin.snoc w b : Fin (k + 1) → Bool) i = extendPrefix w i := by
  unfold extendPrefix
  rw [dif_pos (by omega), dif_pos hi]
  have : (⟨i, by omega⟩ : Fin (k + 1)) = Fin.castSucc ⟨i, hi⟩ := rfl
  rw [this, Fin.snoc_castSucc]

lemma g6_ext_snoc_k {k : ℕ} (w : Fin k → Bool) (b : Bool) :
    extendPrefix (Fin.snoc w b : Fin (k + 1) → Bool) k = b := by
  unfold extendPrefix
  rw [dif_pos (by omega)]
  have : (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k := rfl
  rw [this, Fin.snoc_last]

lemma g6_states_snoc_le (i0 : ℕ × ℕ) {k : ℕ} (w : Fin k → Bool) (b : Bool) (j : ℕ) (hj : j ≤ k) :
    statesOf i0 (extendPrefix (Fin.snoc w b : Fin (k + 1) → Bool)) j =
      statesOf i0 (extendPrefix w) j :=
  g6_states_congr i0 _ _ j (fun i hi => g6_ext_snoc_lt w b i (by omega))

lemma g6_states_snoc_succ (i0 : ℕ × ℕ) {k : ℕ} (w : Fin k → Bool) (b : Bool) :
    statesOf i0 (extendPrefix (Fin.snoc w b : Fin (k + 1) → Bool)) (k + 1) =
      (if b then ((statesOf i0 (extendPrefix w) k).1 + 1, (statesOf i0 (extendPrefix w) k).2)
       else ((statesOf i0 (extendPrefix w) k).1, (statesOf i0 (extendPrefix w) k).2 + 1)) := by
  rw [statesOf]
  rw [g6_states_snoc_le i0 w b k le_rfl, g6_ext_snoc_k]

lemma g6_prob_snoc (i0 : ℕ × ℕ) {k : ℕ} (w : Fin k → Bool) (b : Bool) :
    prefixProb i0 (extendPrefix (Fin.snoc w b : Fin (k + 1) → Bool)) (k + 1) =
      prefixProb i0 (extendPrefix w) k *
        (if b then pMN (statesOf i0 (extendPrefix w) k)
         else 1 - pMN (statesOf i0 (extendPrefix w) k)) := by
  unfold prefixProb
  rw [Finset.prod_range_succ, g6_ext_snoc_k, g6_states_snoc_le i0 w b k le_rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [g6_ext_snoc_lt w b j hj, g6_states_snoc_le i0 w b j hj.le]

lemma g6_pMN_bounds (mn : ℕ × ℕ) : 0 ≤ pMN mn ∧ pMN mn ≤ 1 := by
  unfold pMN
  constructor
  · positivity
  · rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg mn.2 : (0:ℝ) ≤ mn.2)]

lemma g6_prob_nonneg (i0 : ℕ × ℕ) (w : ℕ → Bool) (k : ℕ) : 0 ≤ prefixProb i0 w k := by
  unfold prefixProb
  apply Finset.prod_nonneg
  intro j _
  have := g6_pMN_bounds (statesOf i0 w j)
  split_ifs <;> linarith

lemma g6_tau_snoc {τ : (ℕ → ℕ × ℕ) → ℕ∞} (hτ : IsStoppingTime τ) (i0 : ℕ × ℕ) {k : ℕ}
    (w : Fin k → Bool) (b : Bool) :
    ((k : ℕ∞) < τ (statesOf i0 (extendPrefix (Fin.snoc w b : Fin (k + 1) → Bool)))) ↔
      ((k : ℕ∞) < τ (statesOf i0 (extendPrefix w))) := by
  have := hτ k (statesOf i0 (extendPrefix (Fin.snoc w b : Fin (k + 1) → Bool)))
    (statesOf i0 (extendPrefix w)) (fun j hj => g6_states_snoc_le i0 w b j hj)
  rw [← not_le, ← not_le, this]

lemma g6_sum_snoc {k : ℕ} (F : (Fin (k + 1) → Bool) → ℝ) :
    ∑ w : Fin (k + 1) → Bool, F w = ∑ w : Fin k → Bool, (F (Fin.snoc w true) + F (Fin.snoc w false)) := by
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => Bool)) (fun p => F (Fin.snocEquiv (fun _ => Bool) p)) F
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  rfl

/-- `E[h(X_k) 1_{τ>k}]` -/
noncomputable def g6E (τ : (ℕ → ℕ × ℕ) → ℕ∞) (i0 : ℕ × ℕ) (h : ℕ × ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ w : Fin k → Bool,
    (if (k : ℕ∞) < τ (statesOf i0 (extendPrefix w)) then
      prefixProb i0 (extendPrefix w) k * h (statesOf i0 (extendPrefix w) k) else 0)

/-- `E[h(X_k) 1_{τ=k}]` -/
noncomputable def g6C (τ : (ℕ → ℕ × ℕ) → ℕ∞) (i0 : ℕ × ℕ) (h : ℕ × ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ w : Fin k → Bool,
    (if τ (statesOf i0 (extendPrefix w)) = k then
      prefixProb i0 (extendPrefix w) k * h (statesOf i0 (extendPrefix w) k) else 0)

lemma g6_E1 {τ : (ℕ → ℕ × ℕ) → ℕ∞} (hτ : IsStoppingTime τ) (i0 : ℕ × ℕ) (h : ℕ × ℕ → ℝ)
    (k : ℕ) :
    ∑ w : Fin (k + 1) → Bool,
      (if (k : ℕ∞) < τ (statesOf i0 (extendPrefix w)) then
        prefixProb i0 (extendPrefix w) (k + 1) * h (statesOf i0 (extendPrefix w) (k + 1)) else 0) =
    ∑ w : Fin k → Bool,
      (if (k : ℕ∞) < τ (statesOf i0 (extendPrefix w)) then
        prefixProb i0 (extendPrefix w) k * PMN h (statesOf i0 (extendPrefix w) k) else 0) := by
  rw [g6_sum_snoc]
  apply Finset.sum_congr rfl
  intro w _
  simp only [g6_tau_snoc hτ, g6_prob_snoc, g6_states_snoc_succ, if_true, Bool.false_eq_true,
    if_false]
  split_ifs
  · unfold PMN PQ; ring
  · ring

lemma g6_split (τ : (ℕ → ℕ × ℕ) → ℕ∞) (i0 : ℕ × ℕ) (h : ℕ × ℕ → ℝ) (k : ℕ) :
    ∑ w : Fin (k + 1) → Bool,
      (if (k : ℕ∞) < τ (statesOf i0 (extendPrefix w)) then
        prefixProb i0 (extendPrefix w) (k + 1) * h (statesOf i0 (extendPrefix w) (k + 1)) else 0) =
    g6E τ i0 h (k + 1) + g6C τ i0 h (k + 1) := by
  unfold g6E g6C
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  have key : ∀ t : ℕ∞, (k : ℕ∞) < t ↔ ((k + 1 : ℕ) : ℕ∞) < t ∨ t = ((k + 1 : ℕ) : ℕ∞) := by
    intro t
    rw [← ENat.add_one_le_iff (ENat.natCast_ne_top k), le_iff_lt_or_eq]
    push_cast
    constructor
    · rintro (h | h); exact Or.inl h; exact Or.inr h.symm
    · rintro (h | h); exact Or.inl h; exact Or.inr h.symm
  have := key (τ (statesOf i0 (extendPrefix w)))
  by_cases h1 : ((k + 1 : ℕ) : ℕ∞) < τ (statesOf i0 (extendPrefix w))
  · rw [if_pos (this.2 (Or.inl h1)), if_pos h1, if_neg (ne_of_gt h1)]; ring
  · by_cases h2 : τ (statesOf i0 (extendPrefix w)) = ((k + 1 : ℕ) : ℕ∞)
    · rw [if_pos (this.2 (Or.inr h2)), if_neg h1, if_pos h2]; ring
    · rw [if_neg (fun h' => (this.1 h').elim h1 h2), if_neg h1, if_neg h2]; ring

lemma g6_top_stop : IsStoppingTime (fun _ : ℕ → ℕ × ℕ => (⊤ : ℕ∞)) := fun _ _ _ _ => Iff.rfl

lemma g6_E0 (τ : (ℕ → ℕ × ℕ) → ℕ∞) (hpos : IsPositiveStoppingTime τ) (i0 : ℕ × ℕ)
    (h : ℕ × ℕ → ℝ) : g6E τ i0 h 0 = h i0 := by
  unfold g6E
  rw [Fintype.sum_unique]
  rw [if_pos (lt_of_lt_of_le (by norm_num) (hpos _))]
  simp [prefixProb, statesOf]

lemma g6_probsum (i0 : ℕ × ℕ) (k : ℕ) :
    ∑ w : Fin k → Bool, prefixProb i0 (extendPrefix w) k = 1 := by
  have e : ∀ k, ∑ w : Fin k → Bool, prefixProb i0 (extendPrefix w) k =
      g6E (fun _ => ⊤) i0 (fun _ => 1) k := by
    intro k; unfold g6E; apply Finset.sum_congr rfl; intro w _
    rw [if_pos (ENat.natCast_lt_top k), mul_one]
  rw [e]
  induction k with
  | zero => rw [g6_E0 _ (fun _ => le_top)]
  | succ k ih =>
    have h1 := (g6_split (fun _ => ⊤) i0 (fun _ => 1) k).symm.trans (g6_E1 g6_top_stop i0 (fun _ => 1) k)
    have hC : g6C (fun _ => ⊤) i0 (fun _ => 1) (k + 1) = 0 := by
      unfold g6C; apply Finset.sum_eq_zero; intro w _
      rw [if_neg (ENat.top_ne_natCast _)]
    rw [hC, add_zero] at h1
    rw [h1]
    refine Eq.trans ?_ ih
    unfold g6E; apply Finset.sum_congr rfl; intro w _
    have : PMN (fun _ => (1:ℝ)) (statesOf i0 (extendPrefix w) k) = 1 := by unfold PMN PQ; ring
    rw [this]

lemma g6_E_bound (τ : (ℕ → ℕ × ℕ) → ℕ∞) (i0 : ℕ × ℕ) (h : ℕ × ℕ → ℝ) (C : ℝ)
    (hC : ∀ y, |h y| ≤ C) (k : ℕ) : |g6E τ i0 h k| ≤ C := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC (0, 0))
  unfold g6E
  calc |∑ w : Fin k → Bool, _| ≤ ∑ w : Fin k → Bool,
        prefixProb i0 (extendPrefix w) k * C := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
        intro w _
        have hp := g6_prob_nonneg i0 (extendPrefix w) k
        split_ifs
        · rw [abs_mul, abs_of_nonneg hp]
          exact mul_le_mul_of_nonneg_left (hC _) hp
        · simp only [abs_zero]; exact mul_nonneg hp hC0
    _ = C := by rw [← Finset.sum_mul, g6_probsum, one_mul]

lemma g6_step {β : ℝ} (hβ0 : 0 < β) {τ : (ℕ → ℕ × ℕ) → ℕ∞} (hτ : IsStoppingTime τ)
    (i0 : ℕ × ℕ) (J g : ℕ × ℕ → ℝ) (K : ℝ) (k : ℕ)
    (H1 : ∀ w : Fin k → Bool, (k : ℕ∞) < τ (statesOf i0 (extendPrefix w)) →
      g (statesOf i0 (extendPrefix w) k) + β * PMN J (statesOf i0 (extendPrefix w) k) ≤
        J (statesOf i0 (extendPrefix w) k))
    (H2 : ∀ w : Fin (k + 1) → Bool, τ (statesOf i0 (extendPrefix w)) = ((k + 1 : ℕ) : ℕ∞) →
      K ≤ J (statesOf i0 (extendPrefix w) (k + 1))) :
    g6E τ i0 g k + β * (g6E τ i0 J (k + 1) + K * g6C τ i0 (fun _ => 1) (k + 1)) ≤
      g6E τ i0 J k := by
  have hE1 := g6_E1 hτ i0 J k
  rw [g6_split] at hE1
  have hA : g6E τ i0 g k + β * (∑ w : Fin k → Bool,
      (if (k : ℕ∞) < τ (statesOf i0 (extendPrefix w)) then
        prefixProb i0 (extendPrefix w) k * PMN J (statesOf i0 (extendPrefix w) k) else 0)) ≤
      g6E τ i0 J k := by
    unfold g6E
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro w _
    have hp := g6_prob_nonneg i0 (extendPrefix w) k
    split_ifs with hk
    · have := mul_le_mul_of_nonneg_left (H1 w hk) hp
      linarith
    · simp
  have hB : K * g6C τ i0 (fun _ => 1) (k + 1) ≤ g6C τ i0 J (k + 1) := by
    unfold g6C
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _
    have hp := g6_prob_nonneg i0 (extendPrefix w) (k + 1)
    split_ifs with hk
    · have := mul_le_mul_of_nonneg_left (H2 w hk) hp
      linarith
    · simp
  rw [← hE1] at hA
  nlinarith

lemma g6_qrel {τ : (ℕ → ℕ × ℕ) → ℕ∞} (hτ : IsStoppingTime τ) (i0 : ℕ × ℕ) (k : ℕ) :
    g6E τ i0 (fun _ => 1) k = g6E τ i0 (fun _ => 1) (k + 1) + g6C τ i0 (fun _ => 1) (k + 1) := by
  have hE1 := (g6_split τ i0 (fun _ => 1) k).symm.trans (g6_E1 hτ i0 (fun _ => 1) k)
  rw [hE1]
  unfold g6E; apply Finset.sum_congr rfl; intro w _
  have : PMN (fun _ => (1:ℝ)) (statesOf i0 (extendPrefix w) k) = 1 := by unfold PMN PQ; ring
  rw [this]

lemma g6_tele {β : ℝ} (hβ0 : 0 < β) {τ : (ℕ → ℕ × ℕ) → ℕ∞} (hτ : IsStoppingTime τ)
    (hpos : IsPositiveStoppingTime τ) (i0 : ℕ × ℕ) (J g : ℕ × ℕ → ℝ) (K : ℝ)
    (H1 : ∀ k, ∀ w : Fin k → Bool, (k : ℕ∞) < τ (statesOf i0 (extendPrefix w)) →
      g (statesOf i0 (extendPrefix w) k) + β * PMN J (statesOf i0 (extendPrefix w) k) ≤
        J (statesOf i0 (extendPrefix w) k))
    (H2 : ∀ k, ∀ w : Fin k → Bool, τ (statesOf i0 (extendPrefix w)) = (k : ℕ∞) →
      K ≤ J (statesOf i0 (extendPrefix w) k)) (N : ℕ) :
    ∑ k ∈ Finset.range N, β ^ k * g6E τ i0 g k +
      K * (1 - (1 - β) * ∑ k ∈ Finset.range N, β ^ k * g6E τ i0 (fun _ => 1) k -
        β ^ N * g6E τ i0 (fun _ => 1) N) + β ^ N * g6E τ i0 J N ≤ J i0 := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, mul_zero, sub_zero]
    rw [g6_E0 τ hpos, g6_E0 τ hpos]; simp
  | succ N ih =>
    have hs := g6_step hβ0 hτ i0 J g K N (H1 N) (fun w hw => H2 (N + 1) w (by exact_mod_cast hw))
    have hq := g6_qrel hτ i0 N
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hb : 0 ≤ β ^ N := pow_nonneg hβ0.le N
    have := mul_le_mul_of_nonneg_left hs hb
    have hq1 : K * β ^ N * g6E τ i0 (fun _ => 1) N = K * β ^ N * g6E τ i0 (fun _ => 1) (N + 1) +
        K * β ^ N * g6C τ i0 (fun _ => 1) (N + 1) := by rw [hq]; ring
    have hq2 : K * β ^ N * β * g6E τ i0 (fun _ => 1) N =
        K * β ^ N * β * g6E τ i0 (fun _ => 1) (N + 1) +
        K * β ^ N * β * g6C τ i0 (fun _ => 1) (N + 1) := by rw [hq]; ring
    rw [pow_succ]
    linarith

lemma g6_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (τ : (ℕ → ℕ × ℕ) → ℕ∞) (i0 : ℕ × ℕ)
    (h : ℕ × ℕ → ℝ) (C : ℝ) (hC : ∀ y, |h y| ≤ C) :
    Summable (fun k => β ^ k * g6E τ i0 h k) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left C) ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le k)]
  have := g6_E_bound τ i0 h C hC k
  have hb := pow_nonneg hβ0.le k
  nlinarith

lemma g6_EStop_eq (β : ℝ) (τ : (ℕ → ℕ × ℕ) → ℕ∞) (i0 : ℕ × ℕ) (h : ℕ × ℕ → ℝ) :
    EStop β h τ i0 = ∑' k, β ^ k * g6E τ i0 h k := rfl

lemma g6_pow_bdd_tendsto {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (x : ℕ → ℝ) (C : ℝ)
    (hx : ∀ N, |x N| ≤ C) : Filter.Tendsto (fun N => β ^ N * x N) Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun N : ℕ => C * β ^ N) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul C
  refine squeeze_zero_norm (fun N => ?_) ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le N)]
  have := hx N
  have hb := pow_nonneg hβ0.le N
  nlinarith

theorem g6_gen {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {τ : (ℕ → ℕ × ℕ) → ℕ∞}
    (hτ : IsStoppingTime τ) (hpos : IsPositiveStoppingTime τ) (i0 : ℕ × ℕ) (J g : ℕ × ℕ → ℝ)
    (CJ Cg : ℝ) (hJ : ∀ y, |J y| ≤ CJ) (hg : ∀ y, |g y| ≤ Cg) (K : ℝ)
    (H1 : ∀ k, ∀ w : Fin k → Bool, (k : ℕ∞) < τ (statesOf i0 (extendPrefix w)) →
      g (statesOf i0 (extendPrefix w) k) + β * PMN J (statesOf i0 (extendPrefix w) k) ≤
        J (statesOf i0 (extendPrefix w) k))
    (H2 : ∀ k, ∀ w : Fin k → Bool, τ (statesOf i0 (extendPrefix w)) = (k : ℕ∞) →
      K ≤ J (statesOf i0 (extendPrefix w) k)) :
    EStop β g τ i0 + K * (1 - (1 - β) * EStop β (fun _ => 1) τ i0) ≤ J i0 := by
  have h1 : ∀ y : ℕ × ℕ, |(fun _ => (1:ℝ)) y| ≤ 1 := fun y => by simp
  have hSg := (g6_summable hβ0 hβ1 τ i0 g Cg hg).hasSum.tendsto_sum_nat
  have hS1 := (g6_summable hβ0 hβ1 τ i0 _ 1 h1).hasSum.tendsto_sum_nat
  have hq := g6_pow_bdd_tendsto hβ0 hβ1 _ 1 (g6_E_bound τ i0 _ 1 h1)
  have ha := g6_pow_bdd_tendsto hβ0 hβ1 _ CJ (g6_E_bound τ i0 J CJ hJ)
  have hlim := (hSg.add ((((tendsto_const_nhds (x := (1:ℝ))).sub (hS1.const_mul (1 - β))).sub hq).const_mul K)).add ha
  rw [g6_EStop_eq, g6_EStop_eq]
  simp only [sub_zero, add_zero] at hlim
  exact le_of_tendsto' hlim (fun N => g6_tele hβ0 hτ hpos i0 J g K H1 H2 N)

lemma g6_EStop_neg (β : ℝ) (τ : (ℕ → ℕ × ℕ) → ℕ∞) (i0 : ℕ × ℕ) (g : ℕ × ℕ → ℝ) :
    EStop β (fun y => -g y) τ i0 = -EStop β g τ i0 := by
  rw [g6_EStop_eq, g6_EStop_eq, ← tsum_neg]
  congr 1; funext k
  unfold g6E
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro w _
  split_ifs <;> ring

theorem g6_gen_eq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {τ : (ℕ → ℕ × ℕ) → ℕ∞}
    (hτ : IsStoppingTime τ) (hpos : IsPositiveStoppingTime τ) (i0 : ℕ × ℕ) (J g : ℕ × ℕ → ℝ)
    (CJ Cg : ℝ) (hJ : ∀ y, |J y| ≤ CJ) (hg : ∀ y, |g y| ≤ Cg) (K : ℝ)
    (H1 : ∀ k, ∀ w : Fin k → Bool, (k : ℕ∞) < τ (statesOf i0 (extendPrefix w)) →
      J (statesOf i0 (extendPrefix w) k) =
        g (statesOf i0 (extendPrefix w) k) + β * PMN J (statesOf i0 (extendPrefix w) k))
    (H2 : ∀ k, ∀ w : Fin k → Bool, τ (statesOf i0 (extendPrefix w)) = (k : ℕ∞) →
      J (statesOf i0 (extendPrefix w) k) = K) :
    EStop β g τ i0 + K * (1 - (1 - β) * EStop β (fun _ => 1) τ i0) = J i0 := by
  apply le_antisymm
  · exact g6_gen hβ0 hβ1 hτ hpos i0 J g CJ Cg hJ hg K (fun k w hk => (H1 k w hk).ge)
      (fun k w hk => (H2 k w hk).ge)
  · have := g6_gen hβ0 hβ1 hτ hpos i0 (fun y => -J y) (fun y => -g y) CJ Cg
      (fun y => by rw [abs_neg]; exact hJ y) (fun y => by rw [abs_neg]; exact hg y) (-K)
      (fun k w hk => by
        have := H1 k w hk
        have e : PMN (fun y => -J y) (statesOf i0 (extendPrefix w) k) =
            -PMN J (statesOf i0 (extendPrefix w) k) := by unfold PMN PQ; ring
        rw [e]; linarith)
      (fun k w hk => by have := H2 k w hk; linarith)
    rw [g6_EStop_neg] at this
    linarith

section T766
variable {β : ℝ} (KS : KStoppingValue β pMN)

lemma g6_tau_le_iff (i0 : ℕ × ℕ) (x : ℕ → ℕ × ℕ) (n : ℕ) :
    tauStar KS i0 x ≤ n ↔ ∃ k, 1 ≤ k ∧ k ≤ n ∧ GittinsIndex KS (x k) ≤ GittinsIndex KS i0 := by
  unfold tauStar
  constructor
  · intro h
    set S := {n : ℕ∞ | ∃ k : ℕ, 1 ≤ k ∧ n = (k : ℕ∞) ∧
      GittinsIndex KS (x k) ≤ GittinsIndex KS i0} with hS
    rcases S.eq_empty_or_nonempty with he | hne
    · rw [he, sInf_empty] at h; exact absurd h (by simp)
    · obtain ⟨k, hk1, hk2, hk3⟩ := csInf_mem hne
      rw [hk2] at h
      exact ⟨k, hk1, by exact_mod_cast h, hk3⟩
  · rintro ⟨k, hk1, hk2, hk3⟩
    exact le_trans (sInf_le ⟨k, hk1, rfl, hk3⟩) (by exact_mod_cast hk2)

lemma g6_tau_stop (i0 : ℕ × ℕ) : IsStoppingTime (tauStar KS i0) := by
  intro n x y hxy
  rw [g6_tau_le_iff, g6_tau_le_iff]
  constructor
  · rintro ⟨k, h1, h2, h3⟩; exact ⟨k, h1, h2, by rw [← hxy k h2]; exact h3⟩
  · rintro ⟨k, h1, h2, h3⟩; exact ⟨k, h1, h2, by rw [hxy k h2]; exact h3⟩

lemma g6_tau_pos (i0 : ℕ × ℕ) : IsPositiveStoppingTime (tauStar KS i0) := by
  intro x
  unfold tauStar
  apply le_sInf
  rintro _ ⟨k, hk1, rfl, _⟩
  exact_mod_cast hk1

lemma g6_tau_eq (i0 : ℕ × ℕ) (x : ℕ → ℕ × ℕ) (k : ℕ) (h : tauStar KS i0 x = k) :
    GittinsIndex KS (x k) ≤ GittinsIndex KS i0 := by
  unfold tauStar at h
  set S := {n : ℕ∞ | ∃ k : ℕ, 1 ≤ k ∧ n = (k : ℕ∞) ∧
      GittinsIndex KS (x k) ≤ GittinsIndex KS i0} with hS
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he, sInf_empty] at h; exact absurd h (by simp)
  · obtain ⟨k', _, hk2, hk3⟩ := csInf_mem hne
    rw [h] at hk2
    have : k = k' := by exact_mod_cast hk2
    rw [this]; exact hk3

lemma g6_tau_lt (i0 : ℕ × ℕ) (x : ℕ → ℕ × ℕ) (k : ℕ) (hk1 : 1 ≤ k)
    (h : (k : ℕ∞) < tauStar KS i0 x) : GittinsIndex KS i0 < GittinsIndex KS (x k) := by
  by_contra hc
  push Not at hc
  have := (g6_tau_le_iff KS i0 x k).2 ⟨k, hk1, le_rfl, hc⟩
  exact absurd h (not_lt.2 this)

lemma g6_pMN_abs (y : ℕ × ℕ) : |pMN y| ≤ 1 := by
  have := g6_pMN_bounds y
  rw [abs_le]; constructor <;> linarith

lemma g6_EStop1_ge (hβ0 : 0 < β) (hβ1 : β < 1) (τ : (ℕ → ℕ × ℕ) → ℕ∞)
    (hpos : IsPositiveStoppingTime τ) (i0 : ℕ × ℕ) : 1 ≤ EStop β (fun _ => 1) τ i0 := by
  have h1 : ∀ y : ℕ × ℕ, |(fun _ => (1:ℝ)) y| ≤ 1 := fun y => by simp
  have hS := g6_summable hβ0 hβ1 τ i0 _ 1 h1
  rw [g6_EStop_eq]
  have := hS.sum_le_tsum (Finset.range 1) (fun k _ => by
    apply mul_nonneg (pow_nonneg hβ0.le k)
    unfold g6E
    apply Finset.sum_nonneg
    intro w _
    split_ifs
    · rw [mul_one]; exact g6_prob_nonneg _ _ _
    · exact le_rfl)
  rw [Finset.sum_range_one, pow_zero, one_mul, g6_E0 τ hpos] at this
  exact this

theorem t766_core (m0 n0 : ℕ) :
    IsStoppingTime (tauStar KS (m0, n0)) ∧ IsPositiveStoppingTime (tauStar KS (m0, n0)) ∧
      GittinsIndex KS (m0, n0) =
        EStop β pMN (tauStar KS (m0, n0)) (m0, n0) /
          ((1 - β) * EStop β (fun _ => 1) (tauStar KS (m0, n0)) (m0, n0)) ∧
      GittinsIndex KS (m0, n0) =
        ⨆ τ ∈ {τ : (ℕ → ℕ × ℕ) → ℕ∞ | IsStoppingTime τ ∧ IsPositiveStoppingTime τ},
          EStop β pMN τ (m0, n0) / ((1 - β) * EStop β (fun _ => 1) τ (m0, n0)) := by
  have hβ0 := KS.hβ0
  have hβ1 := KS.hβ1
  set i0 : ℕ × ℕ := (m0, n0) with hi0
  set I := GittinsIndex KS i0 with hI
  obtain ⟨CJ, hCJ⟩ := KS.hJ_bdd I
  have hIpos : 0 ≤ I := by
    have := gk_lower KS i0
    have := (g6_pMN_bounds i0).1
    have : 0 ≤ pMN i0 / (1 - β) := div_nonneg this (by linarith)
    linarith
  have hden : ∀ τ, IsPositiveStoppingTime τ → 0 < (1 - β) * EStop β (fun _ => 1) τ i0 := by
    intro τ hτ
    have := g6_EStop1_ge hβ0 hβ1 τ hτ i0
    exact mul_pos (by linarith) (by linarith)
  -- upper bound for any stopping time
  have hub : ∀ τ, IsStoppingTime τ → IsPositiveStoppingTime τ →
      EStop β pMN τ i0 / ((1 - β) * EStop β (fun _ => 1) τ i0) ≤ I := by
    intro τ hτ hpos
    have := g6_gen hβ0 hβ1 hτ hpos i0 (KS.J I) pMN CJ 1 hCJ g6_pMN_abs I
      (fun k w _ => gk_ge_A KS I _) (fun k w _ => gk_ge KS I _)
    rw [gk_sinf_mem KS i0] at this
    rw [div_le_iff₀ (hden τ hpos)]
    linarith
  have hst := g6_tau_stop KS i0
  have hps := g6_tau_pos KS i0
  have heq : EStop β pMN (tauStar KS i0) i0 / ((1 - β) * EStop β (fun _ => 1) (tauStar KS i0) i0)
      = I := by
    have := g6_gen_eq hβ0 hβ1 hst hps i0 (KS.J I) pMN CJ 1 hCJ g6_pMN_abs I
      (fun k w hk => by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          have e : statesOf i0 (extendPrefix w) 0 = i0 := rfl
          rw [e, gk_sinf_mem KS i0]
          exact gk_indiff KS i0
        · exact gk_below KS I _ (g6_tau_lt KS i0 _ k h0 hk))
      (fun k w hk => (gk_iff KS I _).2 (g6_tau_eq KS i0 _ k hk))
    rw [gk_sinf_mem KS i0] at this
    rw [div_eq_iff (hden _ hps).ne']
    linarith
  refine ⟨hst, hps, heq.symm, ?_⟩
  apply le_antisymm
  · have hbdd : BddAbove (Set.range fun τ : (ℕ → ℕ × ℕ) → ℕ∞ =>
        ⨆ (_ : τ ∈ {τ : (ℕ → ℕ × ℕ) → ℕ∞ | IsStoppingTime τ ∧ IsPositiveStoppingTime τ}),
          EStop β pMN τ i0 / ((1 - β) * EStop β (fun _ => 1) τ i0)) := by
      refine ⟨I, ?_⟩
      rintro _ ⟨τ, rfl⟩
      exact Real.iSup_le (fun h => hub τ h.1 h.2) hIpos
    refine le_trans ?_ (le_ciSup hbdd (tauStar KS i0))
    rw [ciSup_pos (show tauStar KS i0 ∈ {τ : (ℕ → ℕ × ℕ) → ℕ∞ |
      IsStoppingTime τ ∧ IsPositiveStoppingTime τ} from ⟨hst, hps⟩)]
    exact heq.ge
  · exact Real.iSup_le (fun τ => Real.iSup_le (fun h => hub τ h.1 h.2) hIpos) hIpos

end T766

end MDPFinance.InfiniteHorizonApplications

open MDPFinance.InfiniteHorizonApplications


theorem solution {β : ℝ} (KS : KStoppingValue β pMN) (m0 n0 : ℕ) :
    IsStoppingTime (tauStar KS (m0, n0)) ∧ IsPositiveStoppingTime (tauStar KS (m0, n0)) ∧
      GittinsIndex KS (m0, n0) =
        EStop β pMN (tauStar KS (m0, n0)) (m0, n0) /
          ((1 - β) * EStop β (fun _ => 1) (tauStar KS (m0, n0)) (m0, n0)) ∧
      GittinsIndex KS (m0, n0) =
        ⨆ τ ∈ {τ : (ℕ → ℕ × ℕ) → ℕ∞ | IsStoppingTime τ ∧ IsPositiveStoppingTime τ},
          EStop β pMN τ (m0, n0) / ((1 - β) * EStop β (fun _ => 1) τ (m0, n0)) := by
  exact t766_core KS m0 n0
