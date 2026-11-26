-- Prove2me | solution 1 for MasulloRH.central_interval_arithmetic_sound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T14:06:07.68715+00:00
-- url     : https://prove2.me/submissions/8cd62ba3-b9e7-420e-a705-23ef7d971397

import Definitions.Def_MasulloRH_CentralInterval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MasulloRH.CentralInterval

private theorem pt (q : ℚ) : Covers (point q) (q:ℝ) := ⟨le_rfl,le_rfl⟩
private theorem add {a b : Box} {x y : ℝ} (h : Covers a x) (k : Covers b y) : Covers (a+b) (x+y) := by
  rcases h with ⟨hl,hu⟩; rcases k with ⟨kl,ku⟩
  simpa [Covers] using And.intro (add_le_add hl kl) (add_le_add hu ku)
private theorem neg {a : Box} {x : ℝ} (h : Covers a x) : Covers (negB a) (-x) := by
  simpa [Covers,negB] using And.intro (neg_le_neg h.2) (neg_le_neg h.1)

private theorem mult {a b : Box} {x y : ℝ} (h : Covers a x) (k : Covers b y) : Covers (mulB a b) (x*y) := by
  rcases h with ⟨hl,hu⟩; rcases k with ⟨kl,ku⟩
  have between {l z u d A B : ℝ} (h1 : l ≤ z) (h2 : z ≤ u)
      (p : A ≤ l*d) (q : A ≤ u*d) (v : l*d ≤ B) (w : u*d ≤ B) : A ≤ z*d ∧ z*d ≤ B := by
    by_cases hd : 0 ≤ d
    · exact ⟨p.trans (mul_le_mul_of_nonneg_right h1 hd),(mul_le_mul_of_nonneg_right h2 hd).trans w⟩
    · exact ⟨q.trans (mul_le_mul_of_nonpos_right h2 (le_of_not_ge hd)),
        (mul_le_mul_of_nonpos_right h1 (le_of_not_ge hd)).trans v⟩
  dsimp [Covers,mulB]
  push_cast
  let L := min (min ((a.1:ℝ)*b.1) ((a.1:ℝ)*b.2)) (min ((a.2:ℝ)*b.1) ((a.2:ℝ)*b.2))
  let U := max (max ((a.1:ℝ)*b.1) ((a.1:ℝ)*b.2)) (max ((a.2:ℝ)*b.1) ((a.2:ℝ)*b.2))
  have hL : L ≤ x*(b.1:ℝ) ∧ x*(b.1:ℝ) ≤ U :=
    between hl hu ((min_le_left ..).trans (min_le_left ..)) ((min_le_right ..).trans (min_le_left ..))
       ((le_max_left ..).trans (le_max_left ..)) ((le_max_left ..).trans (le_max_right ..))
  have hU : L ≤ x*(b.2:ℝ) ∧ x*(b.2:ℝ) ≤ U :=
    between hl hu ((min_le_left ..).trans (min_le_right ..)) ((min_le_right ..).trans (min_le_right ..))
       ((le_max_right ..).trans (le_max_left ..)) ((le_max_right ..).trans (le_max_right ..))
  simp only [mul_comm x] at hL hU ⊢
  exact between kl ku hL.1 hU.1 hL.2 hU.2

private theorem ab {a : Box} {x : ℝ} (h : Covers a x) : Covers (absB a) |x| := by
  dsimp [Covers,absB,mag]; push_cast
  refine ⟨max_le (abs_nonneg _) (max_le (h.1.trans (le_abs_self _)) ((neg_le_neg h.2).trans (neg_le_abs _))),?_⟩
  exact abs_le.mpr ⟨(neg_le_neg (le_max_left _ _)).trans (by simpa using h.1),h.2.trans (le_max_right ..)⟩
private theorem square {a : Box} {x : ℝ} (h : Covers a x) : Covers (sqB a) (x^2) := by
  have ha := ab h
  have hn : 0 ≤ ((absB a).1:ℝ) := by dsimp [absB]; positivity
  dsimp only [Covers,sqB]; push_cast
  simpa only [sq_abs] using And.intro (pow_le_pow_left₀ hn ha.1 2) (pow_le_pow_left₀ (abs_nonneg _) ha.2 2)
private theorem hS : 0 < S := by decide
private theorem hR : (0:ℝ) < S := by exact_mod_cast hS
private noncomputable def v (n : ℕ) : ℝ := n/(S:ℝ)
private theorem v_nonneg (n : ℕ) : 0 ≤ v n := by unfold v; positivity
private theorem vS : v S = 1 := by simp [v,hR.ne']
private theorem vmul (a b : ℕ) :
    v (times false a b) ≤ v a * v b ∧ v a * v b ≤ v (times true a b) := by
  have hl := Nat.div_mul_le_self (a*b) S
  have hu : a*b ≤ ((a*b)/S +1)*S := by
    have h := Nat.mod_add_div (a*b) S
    have hh := Nat.mod_lt (a*b) hS
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm ((a*b)/S) S]
    omega
  have hl' : (((a*b)/S:ℕ):ℝ)*(S:ℝ) ≤ (a:ℝ)*b := by exact_mod_cast hl
  have hu' : (a:ℝ)*b ≤ ((((a*b)/S:ℕ):ℝ)+1)*(S:ℝ) := by exact_mod_cast hu
  simp only [v,times,Bool.false_eq_true,↓reduceIte,Nat.add_zero,Nat.cast_add,Nat.cast_one]
  norm_num [S] at hl' hu' ⊢
  constructor <;> linarith
private theorem bbound (n k l u : ℕ) (hk : n < 2^k) (x : ℝ)
    (hl : v l ≤ x) (hu : x ≤ v u) :
    v (bin false l k n) ≤ x^n ∧ x^n ≤ v (bin true u k n) := by
  have hx : 0 ≤ x := (v_nonneg _).trans hl
  induction k generalizing n with
  | zero =>
    have hn : n=0 := by simpa using hk
    subst n; simp [bin,vS]
  | succ k ih =>
    by_cases hn : n=0
    · subst n; simp [bin,vS]
    have hk' : n/2 < 2^k := by rw [pow_succ] at hk; omega
    obtain ⟨a,b⟩ := ih (n/2) hk'
    have ha := (vmul (bin false l k (n/2)) (bin false l k (n/2))).1.trans
      (mul_le_mul a a (v_nonneg _) (pow_nonneg hx _))
    have hb := (mul_le_mul b b (pow_nonneg hx _) (v_nonneg _)).trans
      (vmul (bin true u k (n/2)) (bin true u k (n/2))).2
    by_cases he : n%2=0
    · simp only [bin,if_neg hn,if_pos he]
      rw [←pow_add] at ha hb
      convert And.intro ha hb using 2 <;> congr 1 <;> omega
    · simp only [bin,if_neg hn,if_neg he]
      have hla := (vmul (times false (bin false l k (n/2)) (bin false l k (n/2))) l).1.trans
        (mul_le_mul ha hl (v_nonneg _) (mul_nonneg (pow_nonneg hx _) (pow_nonneg hx _)))
      have hua := (mul_le_mul hb hu hx (v_nonneg _)).trans
        (vmul (times true (bin true u k (n/2)) (bin true u k (n/2))) u).2
      rw [←pow_add,←pow_succ] at hla hua
      convert And.intro hla hua using 2 <;> congr 1 <;> omega

private theorem pw {a : Box} {x : ℝ} (ha : Covers a x) (n : ℕ) : Covers (powB a n) (x^n) := by
  have hab := ab ha
  let l := ⌊(absB a).1*(S:ℚ)⌋₊
  let u := ⌈(absB a).2*(S:ℚ)⌉₊
  have hn : 0 ≤ (absB a).1 := le_max_left .. 
  have hl : v l ≤ |x| := by
    have hh : (l:ℚ) ≤ (absB a).1*(S:ℚ) := Nat.floor_le (mul_nonneg hn (Nat.cast_nonneg _))
    apply le_trans _ hab.1
    exact (div_le_iff₀ hR).mpr (by exact_mod_cast hh)
  have hu : |x| ≤ v u := by
    have hh : (absB a).2*(S:ℚ) ≤ (u:ℚ) := Nat.le_ceil _
    apply hab.2.trans
    exact (le_div_iff₀ hR).mpr (by exact_mod_cast hh)
  have hlog : n < 2^(n.log2+1) := Nat.lt_log2_self
  obtain ⟨L,U⟩ := bbound n (n.log2+1) l u hlog |x| hl hu
  rw [←abs_pow] at L U
  have castV (m : ℕ) : (valQ m:ℝ) = v m := by simp [valQ,v]
  unfold powB
  split_ifs with h h'
  · have hp : 0 ≤ x^n := by
      rcases h with e|e
      · exact (Nat.even_iff.mpr e).pow_nonneg _
      · exact pow_nonneg ((Rat.cast_nonneg.mpr e).trans ha.1) _
    rw [abs_of_nonneg hp] at L U
    simpa only [Covers,castV] using And.intro L U
  · have hodd : Odd n := Nat.odd_iff.mpr (by omega)
    have hx := ha.2.trans (Rat.cast_nonpos.mpr h')
    have hn' := hodd.pow_nonpos hx
    rw [abs_of_nonpos hn'] at L U
    dsimp only [Covers]; push_cast; rw [castV,castV]; constructor <;> linarith
  · dsimp only [Covers]; push_cast; rw [castV]; exact abs_le.mp U

private theorem expP (t : ℚ) : Covers (expPoint t) (Real.exp (t:ℝ)) := by
  unfold expPoint
  split_ifs with low hn
  · have h : (t:ℝ) ≤ -64 := by exact_mod_cast low
    refine ⟨by simpa using (Real.exp_pos (t:ℝ)).le,?_⟩
    apply (Real.exp_le_exp.mpr h).trans
    rw [Real.exp_neg,←one_div]
    push_cast
    apply one_div_le_one_div_of_le (by norm_num)
    simpa using (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le 64).trans_eq (Real.exp_nat_mul 1 64).symm
  all_goals
    let d : ℝ := (step:ℝ)
    have hd : 0 < d := by norm_num [d,step,ticks]
    have hd1 : d < 1 := by norm_num [d,step,ticks]
    let n := ⌊|t| * ticks⌋₊
    have hq : 0 ≤ |t| * ticks := mul_nonneg (abs_nonneg _) (by norm_num [ticks])
    have hl : (n:ℝ)*d ≤ |(t:ℝ)| := by
      have hlq : (n:ℚ) ≤ |t| * ticks := Nat.floor_le hq
      have H : (n:ℝ) ≤ |(t:ℝ)| * (ticks:ℝ) := by exact_mod_cast hlq
      norm_num [ticks,step,d] at H ⊢
      linarith
    have hu : |(t:ℝ)| ≤ ((n:ℝ)+1)*d := by
      have huq : |t| * ticks < (n:ℚ)+1 := Nat.lt_floor_add_one _
      have H : |(t:ℝ)| * (ticks:ℝ) < (n:ℝ)+1 := by exact_mod_cast huq
      norm_num [ticks,step,d] at H ⊢
      linarith
    have mulinv : Real.exp d*Real.exp (-d) = 1 := by rw [← Real.exp_add]; simp
  · have hb : Covers nbase (Real.exp (-d)) := by
      dsimp only [Covers,nbase]; push_cast
      constructor
      · linarith [Real.add_one_le_exp (-d)]
      · apply (le_div_iff₀ (by linarith : 0 < 1+d)).2
        have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp d) (Real.exp_pos (-d)).le
        linarith
    have h0 := pw hb n
    have h1 := mult h0 hb
    have hh : (t:ℝ)<0 := by exact_mod_cast hn
    rw [abs_of_neg hh] at hl hu
    rw [←Real.exp_nat_mul] at h0 h1
    rw [←Real.exp_add] at h1
    exact ⟨h1.1.trans (Real.exp_le_exp.mpr (by linarith)),(Real.exp_le_exp.mpr (by linarith)).trans h0.2⟩
  · have hb : Covers pbase (Real.exp d) := by
      dsimp only [Covers,pbase]; push_cast
      constructor
      · linarith [Real.add_one_le_exp d]
      · apply (le_div_iff₀ (by linarith : 0 < 1-d)).2
        have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-d)) (Real.exp_pos d).le
        linarith
    have h0 := pw hb n
    have h1 := mult h0 hb
    have hh : 0 ≤ (t:ℝ) := by exact_mod_cast le_of_not_gt hn
    rw [abs_of_nonneg hh] at hl hu
    rw [←Real.exp_nat_mul] at h0 h1
    rw [←Real.exp_add] at h1
    exact ⟨h0.1.trans (Real.exp_le_exp.mpr hl),(Real.exp_le_exp.mpr (by linarith)).trans h1.2⟩

theorem solution : Sound := by
  refine ⟨pt, fun h k => add h k, fun h k => ?_,fun h => neg h,fun h k => mult h k,
    fun h => ab h,fun h => square h,?_,fun h n => pw h n,?_,?_⟩
  · simpa [subB,sub_eq_add_neg] using add h (neg k)
  · intro a x ha h
    have hl : (0:ℝ)<a.1 := by exact_mod_cast ha
    dsimp [Covers,invB]; push_cast
    exact ⟨one_div_le_one_div_of_le (hl.trans_le h.1) h.2,one_div_le_one_div_of_le hl h.1⟩
  · intro a x h
    exact ⟨(expP a.1).1.trans (Real.exp_le_exp.mpr h.1),(Real.exp_le_exp.mpr h.2).trans (expP a.2).2⟩
  · intro ι _ a f h
    dsimp [Covers]
    simp only [Prod.fst_sum,Prod.snd_sum,Rat.cast_sum]
    exact ⟨Finset.sum_le_sum fun i _ => (h i).1, Finset.sum_le_sum fun i _ => (h i).2⟩
