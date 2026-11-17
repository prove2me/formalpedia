-- Prove2me | solution 1 for MNLBandit.UCB.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-16T12:52:20.486375+00:00
-- url     : https://prove2.me/submissions/19170bd6-44b3-46b5-9e98-fef6777f3f23

import Definitions.Def_MNLBandit_UCB_Algorithm1
import Theorems.Thm_MNLBandit_UCB_corollary_D_1
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

noncomputable section

private def flag (P : Prop) : ℝ≥0∞ := by
  classical
  exact if P then 1 else 0

/-- Expected payoff after collecting the remaining geometric counts. The list
stores completed counts in reverse order. The current count already includes
the purchases made in the current epoch. -/
private def geomValue (p q : ℝ≥0∞) (E : List ℕ → Prop) :
    ℕ → List ℕ → ℕ → ℝ≥0∞
  | 0, xs, _ => flag (E xs.reverse)
  | n + 1, xs, k => ∑' j : ℕ, (q ^ j * p) * geomValue p q E n ((k+j)::xs) 0

private theorem geomValue_shift (p q : ℝ≥0∞) (E : List ℕ → Prop)
    (n : ℕ) (xs : List ℕ) (k : ℕ) :
    geomValue p q E (n+1) xs k =
      p * geomValue p q E n (k::xs) 0 + q * geomValue p q E (n+1) xs (k+1) := by
  conv_lhs => rw [geomValue, tsum_eq_zero_add' ENNReal.summable]
  conv_rhs => rw [geomValue, ← ENNReal.tsum_mul_left]
  simp only [pow_zero, one_mul, Nat.add_zero]
  congr 1
  apply tsum_congr
  intro j
  rw [pow_succ']
  simp only [mul_assoc, Nat.add_assoc, Nat.add_comm j 1]

private def continuation (p q : ℝ≥0∞) (E : List ℕ → Prop) (m : ℕ)
    (xs : List ℕ) (k : ℕ) : ℝ≥0∞ :=
  if m ≤ xs.length then flag (E (xs.take m))
  else geomValue p q E (m-xs.length) xs.reverse k

private theorem continuation_shift (p q : ℝ≥0∞) (hpq : p+q=1)
    (E : List ℕ → Prop) (m : ℕ) (xs : List ℕ) (k : ℕ) :
    continuation p q E m xs k =
      p * continuation p q E m (xs ++ [k]) 0 + q * continuation p q E m xs (k+1) := by
  by_cases h : m ≤ xs.length
  · have h' : m ≤ (xs++[k]).length := by simp; omega
    simp only [continuation, if_pos h, if_pos h', List.take_append_of_le_length h,
      ← add_mul, hpq, one_mul]
  · have hd : m - xs.length = (m - (xs++[k]).length) + 1 := by simp; omega
    have hb : continuation p q E m (xs++[k]) 0 =
        geomValue p q E (m - (xs++[k]).length) (k::xs.reverse) 0 := by
      by_cases ht : m ≤ (xs++[k]).length
      · have hm : m = (xs++[k]).length := by simp at ht ⊢; omega
        rw [continuation, if_pos ht, hm, Nat.sub_self, geomValue]
        rw [List.take_length]
        simp
      · rw [continuation, if_neg ht]
        simp
    rw [hb]
    simp only [continuation, if_neg h]
    rw [hd, geomValue_shift]

private def countsFor {N : ℕ} (i : Fin N) (xs : List (EpochRecord N)) : List ℕ :=
  (xs.filter (fun e => decide (i ∈ e.1))).map (fun e => e.2 i)

private theorem countsFor_append {N : ℕ} (i : Fin N) (xs ys : List (EpochRecord N)) :
    countsFor i (xs ++ ys) = countsFor i xs ++ countsFor i ys := by
  simp [countsFor]

private def weight {N : ℕ} (v : Fin N → ℝ) (S : Finset (Fin N)) (o : Option (Fin N)) :=
  ENNReal.ofReal (choiceProb v S o)

private theorem denom_pos {N : ℕ} {v : Fin N → ℝ} (hv : ∀ i, 0 ≤ v i)
    (S : Finset (Fin N)) : 0 < 1 + ∑ j ∈ S, v j :=
  add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun j _ => hv j))

private theorem choice_nonneg {N : ℕ} {v : Fin N → ℝ} (hv : ∀ i, 0 ≤ v i)
    (S : Finset (Fin N)) (o : Option (Fin N)) : 0 ≤ choiceProb v S o := by
  cases o with
  | none => exact div_nonneg zero_le_one (denom_pos hv S).le
  | some j =>
    simp only [choiceProb]
    split
    · exact div_nonneg (hv j) (denom_pos hv S).le
    · exact le_rfl

private theorem weight_total {N : ℕ} {v : Fin N → ℝ} (hv : ∀ i, 0 ≤ v i)
    (S : Finset (Fin N)) : ∑ o, weight v S o = 1 := by
  classical
  unfold weight
  rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => choice_nonneg hv S o),
    Fintype.sum_option]
  change ENNReal.ofReal (1 / (1+∑ j ∈ S, v j) +
    ∑ j : Fin N, (if j ∈ S then v j / (1+∑ k ∈ S, v k) else 0)) = 1
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    ← Finset.sum_div, ← add_div, div_self (denom_pos hv S).ne', ENNReal.ofReal_one]

private def acceptParam (x : ℝ) (hx : 0 ≤ x) : unitInterval :=
  ⟨1/(1+x), div_nonneg zero_le_one (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩

private theorem acceptParam_ne_zero (x : ℝ) (hx : 0 ≤ x) : acceptParam x hx ≠ 0 := by
  intro h
  have hh := congrArg Subtype.val h
  change 1/(1+x) = 0 at hh
  exact (div_pos zero_lt_one (by linarith)).ne' hh

private theorem acceptParam_mean (x : ℝ) (hx : 0 ≤ x) :
    (1 - (acceptParam x hx : ℝ)) / (acceptParam x hx : ℝ) = x := by
  change (1 - 1/(1+x)) / (1/(1+x)) = x
  have h : 1+x ≠ 0 := by linarith
  field_simp
  ring

private def stateValue {N : ℕ} (i : Fin N) (p q : ℝ≥0∞) (E : List ℕ → Prop)
    (m : ℕ) (s : AlgState N) : ℝ≥0∞ :=
  continuation p q E m (countsFor i s.past) (if i ∈ s.cur then s.counts i else 0)

private theorem stateValue_step {N : ℕ} (v r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hv : ∀ j, 0 ≤ v j) (i : Fin N) (E : List ℕ → Prop)
    (m : ℕ) (s : AlgState N) :
    let p := ENNReal.ofReal (acceptParam (v i) (hv i) : ℝ)
    let q := ENNReal.ofReal (1 - (acceptParam (v i) (hv i) : ℝ))
    ∑ o, weight v s.cur o * stateValue i p q E m (step r sel s o) =
      stateValue i p q E m s := by
  classical
  dsimp only
  let pR : ℝ := acceptParam (v i) (hv i)
  let p := ENNReal.ofReal pR
  let q := ENNReal.ofReal (1-pR)
  let V := stateValue i p q E m
  change (∑ o, weight v s.cur o * V (step r sel s o)) = V s
  have hp0 : 0 ≤ pR := (acceptParam (v i) (hv i)).2.1
  have hq0 : 0 ≤ 1-pR := sub_nonneg.mpr (acceptParam (v i) (hv i)).2.2
  have hpq : p+q=1 := by
    change ENNReal.ofReal pR + ENNReal.ofReal (1-pR) = 1
    rw [← ENNReal.ofReal_add hp0 hq0, show pR + (1-pR) = 1 by ring, ENNReal.ofReal_one]
  have hOther (j : Fin N) (hj : j ≠ i) : V (step r sel s (some j)) = V s := by
    simp [V, stateValue, step, Function.update_of_ne (Ne.symm hj)]
  by_cases hi : i ∈ s.cur
  · let xs := countsFor i s.past
    let k := s.counts i
    have hnil : V (step r sel s none) = continuation p q E m (xs++[k]) 0 := by
      simp [V, stateValue, step, xs, k, countsFor, hi]
    have hsome : V (step r sel s (some i)) = continuation p q E m xs (k+1) := by
      simp [V, stateValue, step, xs, k, hi]
    have hbase : V s = continuation p q E m xs k := by simp [V, stateValue, hi, xs, k]
    let a := weight v s.cur none
    let b := weight v s.cur (some i)
    have hab : a+b = ENNReal.ofReal ((1+v i) / (1+∑ j ∈ s.cur, v j)) := by
      dsimp [a,b,weight,choiceProb]
      rw [if_pos hi, ← ENNReal.ofReal_add (div_nonneg zero_le_one (denom_pos hv _).le)
        (div_nonneg (hv i) (denom_pos hv _).le), ← add_div]
    have ha : a = (a+b)*p := by
      dsimp only [p]
      rw [hab, ← ENNReal.ofReal_mul (div_nonneg (by linarith [hv i]) (denom_pos hv _).le)]
      change ENNReal.ofReal (1 / (1+∑ j ∈ s.cur, v j)) =
        ENNReal.ofReal ((1+v i) / (1+∑ j ∈ s.cur, v j) * (1/(1+v i)))
      congr 1
      have hh : 1+v i ≠ 0 := by linarith [hv i]
      field_simp
    have hb : b = (a+b)*q := by
      dsimp only [q]
      rw [hab, ← ENNReal.ofReal_mul (div_nonneg (by linarith [hv i]) (denom_pos hv _).le)]
      change ENNReal.ofReal (if i ∈ s.cur then v i/(1+∑ j ∈ s.cur, v j) else 0) =
        ENNReal.ofReal ((1+v i)/(1+∑ j ∈ s.cur, v j) * (1-1/(1+v i)))
      congr 1
      rw [if_pos hi]
      have hh : 1+v i ≠ 0 := by linarith [hv i]
      field_simp
      ring
    let z := ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, weight v s.cur (some j)
    have ht : a+b+z=1 := by
      have hh := weight_total hv s.cur
      rw [Fintype.sum_option, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hh
      simpa [a,b,z,add_left_comm,add_comm,add_assoc] using hh
    rw [Fintype.sum_option, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    have hz : (∑ j ∈ (Finset.univ : Finset (Fin N)).erase i,
        weight v s.cur (some j) * V (step r sel s (some j))) = z * V s := by
      dsimp only [z]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j hj => by rw [hOther j (Finset.ne_of_mem_erase hj)])
    rw [hz, hnil, hsome]
    change a * _ + (z * V s + b * _) = V s
    calc
      _ = ((a+b)*p) * continuation p q E m (xs++[k]) 0 +
          ((a+b)*q) * continuation p q E m xs (k+1) + z * V s := by
        rw [← ha, ← hb]
        ac_rfl
      _ = (a+b) * (p * continuation p q E m (xs++[k]) 0 +
          q * continuation p q E m xs (k+1)) + z * V s := by simp only [mul_assoc, mul_add]
      _ = ((a+b)+z) * V s := by
        rw [← continuation_shift p q hpq, ← hbase]
        simp only [add_mul]
      _ = V s := by rw [ht, one_mul]
  · have he (o : Option (Fin N)) : V (step r sel s o) = V s := by
      cases o with
      | none => simp [V, stateValue, step, countsFor, hi]
      | some j => simp [V, stateValue, step, hi]
    simp_rw [he, ← Finset.sum_mul, weight_total hv, one_mul]

private theorem ofFn_snoc_local {α : Type*} (t : ℕ) (h : Fin t → α) (o : α) :
    List.ofFn (Fin.snoc h o) = List.ofFn h ++ [o] := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    rw [List.getElem_ofFn, List.getElem_append]
    split
    · rw [List.getElem_ofFn]
      exact Fin.snoc_castSucc (α := fun _ : Fin (t+1) => α) o h
        ⟨j, by simpa using ‹j < (List.ofFn h).length›⟩
    · have hjt : j = t := by
        have hlt : j < t+1 := by simpa only [List.length_ofFn] using hj
        have hnlt : ¬ j < t := by
          simpa only [List.length_ofFn] using ‹¬j < (List.ofFn h).length›
        omega
      subst j
      have hlast : Fin.last t = (⟨t, Nat.lt_succ_self t⟩ : Fin (t+1)) := Fin.ext (by simp)
      simpa only [List.length_ofFn, Nat.sub_self, List.getElem_cons_zero, hlast] using
        (Fin.snoc_last (α := fun _ : Fin (t+1) => α) o h)

private theorem finalState_snoc {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (o : Option (Fin N)) :
    finalState r sel (Fin.snoc h o) = step r sel (finalState r sel h) o := by
  rw [finalState, ofFn_snoc_local, runAlg, List.foldl_append]
  rfl

private theorem histWeight_snoc {N T : ℕ} (v r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (hv : ∀ i, 0 ≤ v i)
    (h : History N T) (o : Option (Fin N)) :
    ENNReal.ofReal (histProb v (alg1 r sel) (Fin.snoc h o)) =
      ENNReal.ofReal (histProb v (alg1 r sel) h) *
        weight v (finalState r sel h).cur o := by
  have hc (t : Fin T) : histPrefix (Fin.snoc h o) t.castSucc = histPrefix h t := by
    funext j
    exact Fin.snoc_castSucc (α := fun _ : Fin (T+1) => Option (Fin N)) o h
      (Fin.castLE t.isLt.le j)
  have hl : histPrefix (Fin.snoc h o) (Fin.last T) = h := by
    funext j
    exact Fin.snoc_castSucc (α := fun _ : Fin (T+1) => Option (Fin N)) o h j
  simp only [histProb, Fin.prod_univ_castSucc, offered, hc, hl,
    Fin.snoc_castSucc, Fin.snoc_last]
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg (fun _ _ => choice_nonneg hv _ _))]
  rfl

private theorem expected_stateValue {N : ℕ} (v r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hv : ∀ j, 0 ≤ v j) (i : Fin N) (E : List ℕ → Prop) (m T : ℕ) :
    let p := ENNReal.ofReal (acceptParam (v i) (hv i) : ℝ)
    let q := ENNReal.ofReal (1 - (acceptParam (v i) (hv i) : ℝ))
    ∑ h : History N T, ENNReal.ofReal (histProb v (alg1 r sel) h) *
        stateValue i p q E m (finalState r sel h) =
      geomValue p q E m [] 0 := by
  classical
  dsimp only
  induction T with
  | zero =>
      simp [histProb, finalState, runAlg, initState, stateValue, countsFor, continuation]
      rintro rfl
      rfl
  | succ T ih =>
      let e := Fin.snocEquiv (fun _ : Fin (T+1) => Option (Fin N))
      rw [← e.sum_comp]
      simp only [e, Fin.snocEquiv, Equiv.coe_fn_mk, histWeight_snoc v r sel hv, finalState_snoc]
      simp only [Fintype.sum_prod_type_right, mul_assoc, ← Finset.mul_sum, stateValue_step]
      exact ih


private theorem geomValue_product (p q : ℝ≥0∞) (E : List ℕ → Prop)
    (n : ℕ) (xs : List ℕ) :
    geomValue p q E n xs 0 = ∑' x : Fin n → ℕ,
      (∏ j, q ^ (x j) * p) * flag (E (xs.reverse ++ List.ofFn x)) := by
  induction n generalizing xs with
  | zero => simp [geomValue, tsum_fintype]
  | succ n ih =>
      let e := Fin.consEquiv (fun _ : Fin (n+1) => ℕ)
      rw [← e.tsum_eq, ENNReal.tsum_prod']
      simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ, List.ofFn_succ, geomValue, Nat.zero_add]
      congr 1
      funext k
      rw [ih, ← ENNReal.tsum_mul_left]
      congr 1
      funext y
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append, mul_assoc]

private theorem geomValue_measure (p : unitInterval) (hp : p ≠ 0)
    (E : List ℕ → Prop) (n : ℕ) :
    geomValue (ENNReal.ofReal (p : ℝ)) (ENNReal.ofReal (1-(p : ℝ))) E n [] 0 =
      (Measure.pi (fun _ : Fin n => geometricMeasure p)) {x | E (List.ofFn x)} := by
  classical
  rw [geomValue_product, ← lintegral_indicator_one MeasurableSet.of_discrete,
    lintegral_countable']
  congr 1
  funext x
  rw [Measure.pi_singleton]
  simp only [geometricMeasure_singleton hp, ENNReal.ofReal_mul
    (pow_nonneg (sub_nonneg.mpr p.2.2) _), ENNReal.ofReal_pow (sub_nonneg.mpr p.2.2)]
  by_cases hx : E (List.ofFn x) <;> simp [flag, Set.indicator, hx]

private theorem length_countsFor {N : ℕ} (i : Fin N) (xs : List (EpochRecord N)) :
    (countsFor i xs).length = TcountL xs i := by simp [countsFor, TcountL]

private theorem count_le_epoch {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (i : Fin N) (ℓ : ℕ) :
    (countsFor i (pastUpTo r sel h ℓ)).length ≤ ℓ := by
  simpa [countsFor, pastUpTo] using
    (List.length_filter_le (p := fun e : EpochRecord N => decide (i ∈ e.1))
      ((finalState r sel h).past.take ℓ)).trans (by simp)

private theorem stateValue_ge_sample {N : ℕ} (i : Fin N) (p q : ℝ≥0∞)
    (E : List ℕ → Prop) (m ℓ : ℕ) (s : AlgState N) :
    flag ((countsFor i (s.past.take ℓ)).length = m ∧ E (countsFor i (s.past.take ℓ))) ≤
      stateValue i p q E m s := by
  classical
  by_cases hh : (countsFor i (s.past.take ℓ)).length = m ∧ E (countsFor i (s.past.take ℓ))
  · have he : countsFor i s.past =
      countsFor i (s.past.take ℓ) ++ countsFor i (s.past.drop ℓ) := by
      rw [← countsFor_append, List.take_append_drop]
    have hle : m ≤ (countsFor i s.past).length := by rw [he]; simp [hh.1]
    have ht : (countsFor i s.past).take m = countsFor i (s.past.take ℓ) := by
      rw [he, List.take_append_of_le_length hh.1.ge, ← hh.1, List.take_length]
    simp [flag, hh, stateValue, continuation, hle, ht]
  · simp [flag, hh]

private theorem adaptive_tail {N : ℕ} (v r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hv : ∀ j, 0 ≤ v j) (i : Fin N) (E : ℕ → List ℕ → Prop)
    (T ℓ : ℕ) (G : History N T → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (bound : ∀ m : Fin ℓ,
      (Measure.pi (fun _ : Fin (m.val+1) => geometricMeasure (acceptParam (v i) (hv i))))
        {x | E (m.val+1) (List.ofFn x)} ≤ ENNReal.ofReal δ) :
    probT v (alg1 r sel) T (fun h =>
      let xs := countsFor i (pastUpTo r sel h ℓ)
      G h ∧ 1 ≤ xs.length ∧ E xs.length xs) ≤ (ℓ : ℝ) * δ := by
  classical
  let xs := fun h : History N T => countsFor i (pastUpTo r sel h ℓ)
  let H := fun h : History N T => ENNReal.ofReal (histProb v (alg1 r sel) h)
  let pR := acceptParam (v i) (hv i)
  let p := ENNReal.ofReal (pR : ℝ)
  let q := ENNReal.ofReal (1-(pR : ℝ))
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg ℓ) hδ)).mp
  have hProb : ∀ h : History N T, 0 ≤ histProb v (alg1 r sel) h :=
    fun h => Finset.prod_nonneg (fun _ _ => choice_nonneg hv _ _)
  rw [probT, ENNReal.ofReal_sum_of_nonneg (fun h _ => by split <;> simp [hProb])]
  simp only [ENNReal.ofReal_mul (Nat.cast_nonneg ℓ), ENNReal.ofReal_natCast]
  calc
    _ = ∑ h : History N T, H h * flag (G h ∧ 1 ≤ (xs h).length ∧ E (xs h).length (xs h)) := by
      refine Finset.sum_congr rfl (fun h _ => ?_)
      by_cases he : G h ∧ 1 ≤ (xs h).length ∧ E (xs h).length (xs h) <;> simp [xs, H, flag, he]
    _ ≤ ∑ h : History N T, ∑ j : Fin ℓ, H h *
        flag ((xs h).length = j.val+1 ∧ E (j.val+1) (xs h)) := by
      apply Finset.sum_le_sum
      intro h _
      by_cases he : G h ∧ 1 ≤ (xs h).length ∧ E (xs h).length (xs h)
      · let j : Fin ℓ := ⟨(xs h).length-1, by
          have := count_le_epoch r sel h i ℓ
          change (xs h).length ≤ ℓ at this
          omega⟩
        have hj : j.val+1 = (xs h).length := Nat.sub_add_cancel he.2.1
        rw [show H h * flag (G h ∧ 1 ≤ (xs h).length ∧ E (xs h).length (xs h)) =
          H h * flag ((xs h).length = j.val+1 ∧ E (j.val+1) (xs h)) by simp [hj, flag, he]]
        exact Finset.single_le_sum
          (f := fun k : Fin ℓ => H h * flag ((xs h).length = k.val+1 ∧ E (k.val+1) (xs h)))
          (fun _ _ => zero_le) (Finset.mem_univ j)
      · simp [flag, he]
    _ = ∑ j : Fin ℓ, ∑ h : History N T, H h *
        flag ((xs h).length = j.val+1 ∧ E (j.val+1) (xs h)) := Finset.sum_comm
    _ ≤ ∑ j : Fin ℓ, ∑ h : History N T, H h *
        stateValue i p q (E (j.val+1)) (j.val+1) (finalState r sel h) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro h _
      gcongr
      exact stateValue_ge_sample i p q (E (j.val+1)) (j.val+1) ℓ _
    _ = ∑ j : Fin ℓ, geomValue p q (E (j.val+1)) (j.val+1) [] 0 := by
      exact Finset.sum_congr rfl (fun j _ => expected_stateValue v r sel hv i _ _ T)
    _ ≤ ∑ _j : Fin ℓ, ENNReal.ofReal δ := by
      exact Finset.sum_le_sum (fun j _ => (geomValue_measure pR
        (acceptParam_ne_zero (v i) (hv i)) _ _).trans_le (bound j))
    _ = ℓ * ENNReal.ofReal δ := by simp [nsmul_eq_mul]


private def sampleMean (m : ℕ) (xs : List ℕ) : ℝ :=
  (xs.map (fun k : ℕ => (k : ℝ))).sum / (m : ℝ)

private theorem sampleMean_ofFn (m : ℕ) (x : Fin m → ℕ) :
    sampleMean m (List.ofFn x) = (∑ j, (x j : ℝ)) / (m : ℝ) := by
  simp only [sampleMean, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

private theorem vbar_sampleMean {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (i : Fin N) (ℓ : ℕ) :
    sampleMean (countsFor i (pastUpTo r sel h ℓ)).length
      (countsFor i (pastUpTo r sel h ℓ)) = vbar r sel h i ℓ := by
  simp only [sampleMean, countsFor, vbar, vbarL, TcountL, List.length_map, List.map_map,
    Function.comp_def]

private theorem vbar_sampleMean_count {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (i : Fin N) (ℓ : ℕ) :
    sampleMean (TcountL (pastUpTo r sel h ℓ) i)
      (countsFor i (pastUpTo r sel h ℓ)) = vbar r sel h i ℓ := by
  rw [← length_countsFor]
  exact vbar_sampleMean r sel h i ℓ

private theorem rescale {N ℓ : ℕ} (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ) (C : ℝ) :
    (ℓ : ℝ) * (C / ((N : ℝ) * (ℓ : ℝ)^2)) = C / ((N : ℝ) * (ℓ : ℝ)) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hℓr : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  field_simp

end
end MNLBandit.UCB

open MNLBandit.UCB ChoiceCDLP.MNL

theorem solution {N : ℕ} (v r : Fin N → ℝ)
    (𝒮 : Finset (Finset (Fin N))) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (_hTU : IsTU 𝒮) (_hdc : DownClosed 𝒮) (_hne : 𝒮.Nonempty) (_hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (_hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) (i : Fin N) :
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h i ℓ ∧
        |vbar r sel h i ℓ - v i| >
          Real.sqrt (48 * vbar r sel h i ℓ * Real.log (Real.sqrt N * ℓ + 1)
              / Tcount r sel h i ℓ)
            + 48 * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
        ≤ 6 / (N * ℓ) ∧
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h i ℓ ∧
        |vbar r sel h i ℓ - v i| >
          Real.sqrt (24 * v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
            + 48 * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
        ≤ 4 / (N * ℓ) ∧
    probT v (alg1 r sel) T (fun h =>
        ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h i ℓ ∧
        vbar r sel h i ℓ >
          3 * v i / 2 + 48 * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
        ≤ 3 / (N * ℓ) := by 
  have hN : 1 ≤ N := Nat.succ_le_of_lt ((Nat.zero_le i.val).trans_lt i.isLt)
  let p := acceptParam (v i) (hv0 i)
  let G := fun h : History N T => ℓ ≤ epochsDone r sel h
  let L := Real.log (Real.sqrt N * ℓ + 1)
  let E₁ := fun (m : ℕ) (xs : List ℕ) =>
    |sampleMean m xs - v i| > Real.sqrt (48 * sampleMean m xs * L / m) + 48 * L / m
  let E₂ := fun (m : ℕ) (xs : List ℕ) =>
    |sampleMean m xs - v i| > Real.sqrt (24 * v i * L / m) + 48 * L / m
  let E₃ := fun (m : ℕ) (xs : List ℕ) => sampleMean m xs > 3 * v i / 2 + 48 * L / m
  have bounds (m : Fin ℓ) :=
    corollary_D_1 (m.val+1) (by omega) N ℓ hN hℓ p (acceptParam_ne_zero (v i) (hv0 i))
  have mean_p : (1 - (p : ℝ)) / (p : ℝ) = v i := acceptParam_mean (v i) (hv0 i)
  have hb (m : Fin ℓ) := bounds m (by simpa only [mean_p] using hv1 i)
  have h1 (m : Fin ℓ) :
      (Measure.pi (fun _ : Fin (m.val+1) => geometricMeasure p))
        {x | E₁ (m.val+1) (List.ofFn x)} ≤ ENNReal.ofReal (6 / (N * (ℓ:ℝ)^2)) := by
    simpa only [E₁, sampleMean_ofFn, L, mean_p] using (hb m).1
  have h2 (m : Fin ℓ) :
      (Measure.pi (fun _ : Fin (m.val+1) => geometricMeasure p))
        {x | E₂ (m.val+1) (List.ofFn x)} ≤ ENNReal.ofReal (4 / (N * (ℓ:ℝ)^2)) := by
    apply le_trans (measure_mono ?_) (hb m).2.1
    intro x hx
    simp only [Set.mem_ofPred_eq, E₂, sampleMean_ofFn, L] at hx
    simpa only [Set.mem_ofPred_eq, mean_p] using hx.le
  have h3 (m : Fin ℓ) :
      (Measure.pi (fun _ : Fin (m.val+1) => geometricMeasure p))
        {x | E₃ (m.val+1) (List.ofFn x)} ≤ ENNReal.ofReal (3 / (N * (ℓ:ℝ)^2)) := by
    apply le_trans (measure_mono ?_) (hb m).2.2
    intro x hx
    simp only [Set.mem_ofPred_eq, E₃, sampleMean_ofFn, L] at hx
    simpa only [Set.mem_ofPred_eq, mean_p] using hx.le
  constructor
  · simpa only [length_countsFor, vbar_sampleMean_count, Tcount, G, E₁, L, rescale hN hℓ] using
      adaptive_tail v r sel hv0 i E₁ T ℓ G _ (by positivity) h1
  · constructor
    · simpa only [length_countsFor, vbar_sampleMean_count, Tcount, G, E₂, L, rescale hN hℓ] using
        adaptive_tail v r sel hv0 i E₂ T ℓ G _ (by positivity) h2
    · simpa only [length_countsFor, vbar_sampleMean_count, Tcount, G, E₃, L, rescale hN hℓ] using
        adaptive_tail v r sel hv0 i E₃ T ℓ G _ (by positivity) h3

