-- Prove2me | solution 1 for MomentSearch.Supplement.theorem_28
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T01:08:47.957623+00:00
-- url     : https://prove2.me/submissions/92daf60c-a29b-425a-9933-23ef835e51cf

import Mathlib
import Definitions.Def_MomentSearch_OPT
import Theorems.Thm_MomentSearch_kraft_average_depth

import Theorems.Thm_MomentSearch_Supplement_sparse_support_opt_upper_bound

open Finset MomentSearch MomentSearch.Supplement MeasureTheory

private noncomputable def empirical {n q : ℕ} (u : Fin q → Fin n) (j : Fin n) : ℝ :=
  (∑ i, if u i = j then (1 : ℝ) else 0) / q

private theorem empirical_eval {n q : ℕ} (u : Fin q → Fin n) (f : Fin n → ℝ) :
    ∑ j, empirical u j * f j = (∑ i, f (u i)) / q := by
  classical
  simp only [empirical, div_mul_eq_mul_div, ← sum_div, sum_mul, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  simp

private theorem empirical_mem {n q : ℕ} (hq : 0 < q) (u : Fin q → Fin n) :
    empirical u ∈ stdSimplex ℝ (Fin n) := by
  refine ⟨fun j => ?_, ?_⟩
  · unfold empirical
    positivity
  · simpa [Nat.ne_of_gt hq] using empirical_eval u (fun _ => 1)

private theorem empirical_sparse {n q : ℕ} (u : Fin q → Fin n) :
    (Function.support (empirical u)).ncard ≤ q := by
  classical
  have sub : Function.support (empirical u) ⊆ Set.range u := by
    intro j hj
    by_contra h
    have hh : ∀ i, u i ≠ j := fun i e => h ⟨i,e⟩
    exact hj (by simp [empirical,hh])
  apply (Set.ncard_le_ncard sub).trans
  simpa using (Set.ncard_image_le (f := u) (Set.finite_univ : (Set.univ : Set (Fin q)).Finite))

private theorem kraft_four {n : ℕ} (hn : 2 ≤ n) (T : Strategy n) :
    ∑ j : Fin n, Real.exp (-((queries T j : ℝ) * Real.log 4)) ≤ 1 := by
  cases n with
  | zero => omega
  | succ m =>
    have K := (kraft_average_depth hn T m id Function.injective_id).1
    apply le_trans (sum_le_sum fun j _ => ?_) K
    rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num)]
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

private theorem depth_bound {a b : ℕ} (T : SearchTree a b) (t : ℕ) :
    queries T t ≤ b+1-a := by
  induction T with
  | leaf a => simp [queries]
  | node v hav hvb hab l r il ir =>
    simp only [queries]
    split
    · omega
    · split
      · split
        · rename_i h
          have := il h
          omega
        · omega
      · split
        · rename_i h
          have := ir h
          omega
        · omega

private theorem tuple_average {n q k : ℕ} (hn : 2 ≤ n) (hq : 0 < q)
    (budget : (k:ℝ) ≤ (q:ℝ)/2 * Real.logb 2 n)
    (g : (Fin q → Fin n) → (Fin k → Bool)) (S : (Fin k → Bool) → Strategy n) :
    (∑ _ : Fin q → Fin n, Real.logb 2 n / 4) ≤
      ∑ u, cost (empirical u) (S (g u)) := by
  classical
  let B := Real.logb 2 n / 4
  let D := (q:ℝ) * Real.log 4
  let c (u : Fin q → Fin n) := cost (empirical u) (S (g u))
  let W (T : Strategy n) (u : Fin q → Fin n) :=
    ∏ i, Real.exp (-((queries T (u i):ℝ)*Real.log 4))
  have total (T : Strategy n) : ∑ u, W T u ≤ 1 := by
    have e := sum_pow' (univ : Finset (Fin n)) (fun j => Real.exp (-((queries T j:ℝ)*Real.log 4))) q
    simp only [Fintype.piFinset_univ] at e
    exact e.ge.trans (pow_le_one₀ (sum_nonneg fun _ _ => (Real.exp_pos _).le) (kraft_four hn T))
  have weights : ∑ u, W (S (g u)) u ≤ (2:ℝ)^k := by
    rw [← sum_fiberwise univ g]
    calc
      _ ≤ ∑ _ : Fin k → Bool, (1:ℝ) := by
        apply sum_le_sum
        intro x _
        calc
          _ = ∑ u ∈ univ.filter (fun u => g u = x), W (S x) u :=
            sum_congr rfl fun u hu => by rw [(mem_filter.mp hu).2]
          _ ≤ 1 := (sum_le_sum_of_subset_of_nonneg (filter_subset ..)
            (fun u _ _ => prod_nonneg fun _ _ => (Real.exp_pos _).le)).trans (total _)
      _ = _ := by simp
  have qp : 0 < (q:ℝ) := by exact_mod_cast hq
  have np : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have l2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have l4 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have DB : D*B = (q:ℝ)*Real.log n/2 := by
    dsimp [D,B,Real.logb]; rw [l4]; field_simp; ring
  have expbudget : Real.exp (D*B)*(2:ℝ)^k ≤ (n:ℝ)^q := by
    have h := mul_le_mul_of_nonneg_right budget l2.le
    rw [Real.logb] at h
    have e : (q:ℝ)/2*(Real.log n/Real.log 2)*Real.log 2 = (q:ℝ)*Real.log n/2 := by field_simp
    rw [e] at h
    calc
      _ = Real.exp (D*B+(k:ℝ)*Real.log 2) := by
        rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log (by norm_num)]
      _ ≤ Real.exp ((q:ℝ)*Real.log n) := Real.exp_le_exp.mpr (by rw [DB]; linarith)
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log np]
  have linear (u : Fin q → Fin n) : 1 + D*(B-c u) ≤ Real.exp (D*B)*W (S (g u)) u := by
    have ew : W (S (g u)) u = Real.exp (-(D*c u)) := by
      unfold c cost
      rw [empirical_eval]
      have e (z : ℝ) : D*(z/q) = z*Real.log 4 := by dsimp [D]; field_simp
      rw [e,sum_mul,← sum_neg_distrib,Real.exp_sum]
    rw [ew,← Real.exp_add,← mul_neg,← mul_add]
    simpa [sub_eq_add_neg,add_comm] using Real.add_one_le_exp (D*(B-c u))
  have summed := (sum_le_sum (fun u (_ : u ∈ univ) => linear u))
  simp only [sum_add_distrib,← mul_sum,sum_sub_distrib,sum_const,card_univ,
    Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,mul_one] at summed
  have top := (mul_le_mul_of_nonneg_left weights (Real.exp_pos (D*B)).le).trans expbudget
  have dp : 0 < D := mul_pos qp (Real.log_pos (by norm_num))
  change (∑ _ : Fin q → Fin n, B) ≤ ∑ u, c u
  simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right (by linarith only [summed,top]) dp)

theorem solution :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∀ (k : ℕ), (k : ℝ) ≤ 1 / 2 * (n : ℝ) ^ ε * Real.logb 2 n →
          ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (σ : Ω → (Fin n → ℝ) → (Fin k → Bool)) (S : Ω → (Fin k → Bool) → Strategy n),
            (∀ p ∈ stdSimplex ℝ (Fin n), Measurable (fun r => cost p (S r (σ r p)))) →
            ∃ p ∈ stdSimplex ℝ (Fin n),
              γ / ε * OPT p ≤ ∫ r, cost p (S r (σ r p)) ∂μ := by
  classical
  refine ⟨1/12, by norm_num, ?_⟩
  intro ε hε _hε
  obtain ⟨N,hN⟩ := exists_nat_gt ((2:ℝ)^(1/ε))
  refine ⟨max 2 N, ?_⟩
  intro n hn k hk Ω _ μ _ σ S hmeas
  have hn2 : 2 ≤ n := le_trans (le_max_left ..) hn
  have hNr : (N:ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right 2 N) hn)
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have logN := Real.logb_le_logb_of_le (b := (2:ℝ)) (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _) (hN.le.trans hNr)
  rw [Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0:ℝ)<2),Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] at logN
  have scale : 1 ≤ ε * Real.logb 2 n := by
    have e := (div_le_iff₀ hε).mp logN
    linarith
  let q := ⌈(n:ℝ)^ε⌉₊
  have lo : (n:ℝ)^ε ≤ q := Nat.le_ceil _
  have pos : 0 < q := by
    exact_mod_cast (lt_of_lt_of_le (Real.rpow_pos_of_pos hn' ε) lo)
  have logpos : 0 < Real.logb 2 n := by
    apply Real.logb_pos (by norm_num)
    exact_mod_cast (by omega : 1 < n)
  have one : 1 ≤ (n:ℝ)^ε := Real.one_le_rpow (by exact_mod_cast (by omega : 1≤n)) hε.le
  have qbound : (q:ℝ) ≤ 2*(n:ℝ)^ε := by
    have e := Nat.ceil_lt_add_one (show 0 ≤ (n:ℝ)^ε from zero_le_one.trans one)
    change (q:ℝ) < _ at e
    linarith
  have logq := Real.logb_le_logb_of_le (b := (2:ℝ)) (by norm_num)
    (by exact_mod_cast pos : 0 < (q:ℝ)) qbound
  rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos hn' ε).ne',
    Real.logb_self_eq_one (by norm_num : (1:ℝ)<2), Real.logb_rpow_eq_mul_logb_of_pos hn'] at logq
  have budget : (k:ℝ) ≤ (q:ℝ)/2*Real.logb 2 n :=
    hk.trans (by nlinarith [mul_le_mul_of_nonneg_right lo logpos.le])
  let c (u : Fin q → Fin n) (r : Ω) := cost (empirical u) (S r (σ r (empirical u)))
  have integr (u : Fin q → Fin n) : Integrable (c u) μ := by
    have hp := empirical_mem pos u
    refine (integrable_const (n:ℝ)).mono' (hmeas _ hp).aestronglyMeasurable
      (ae_of_all _ fun r => ?_)
    let T := S r (σ r (empirical u))
    change ‖cost (empirical u) T‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ cost (empirical u) T from
      sum_nonneg fun j _ => mul_nonneg (hp.1 j) (by positivity))]
    calc
      _ ≤ ∑ j, empirical u j * (n:ℝ) := by
        apply sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (hp.1 j)
        exact_mod_cast (depth_bound T j).trans (by omega : n-1+1-0 ≤ n)
      _ = _ := by rw [← sum_mul,hp.2,one_mul]
  have av (r : Ω) := tuple_average hn2 pos budget (fun u => σ r (empirical u)) (S r)
  have h := integral_mono (μ := μ) (integrable_const (∑ _ : Fin q → Fin n, Real.logb 2 n / 4))
    (integrable_finsetSum univ (fun u _ => integr u)) (fun r => av r)
  rw [integral_finsetSum univ (fun u _ => integr u)] at h
  simp only [integral_const,probReal_univ,one_smul] at h
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨u,_,hard⟩ := exists_le_of_sum_le univ_nonempty h
  have hp := empirical_mem pos u
  refine ⟨empirical u,hp,?_⟩
  have opt := (sparse_support_opt_upper_bound hn2 pos _ hp (empirical_sparse u)).2
  apply le_trans _ hard
  rw [div_mul_eq_mul_div,div_le_iff₀ hε]
  linarith
