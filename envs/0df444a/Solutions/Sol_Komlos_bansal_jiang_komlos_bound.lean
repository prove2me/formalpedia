-- Prove2me | solution 1 for Komlos.bansal_jiang_komlos_bound
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-30T10:54:34.245211+00:00
-- url     : https://prove2.me/submissions/9cf64878-b080-4524-ad40-e4b4953e7c1f

import Mathlib
import Definitions.Def_Komlos_model

-- BEGIN KMProof/SharedBasics.lean

-- END KMProof/SharedBasics.lean

-- BEGIN KMProof/FiniteLaw.lean

noncomputable section
open scoped BigOperators
namespace Komlos.KMFresh

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

structure FiniteLaw (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  total : ∑ i, weight i = 1

namespace FiniteLaw

def mean (P : FiniteLaw ι) (f : ι → ℝ) : ℝ := ∑ i, P.weight i * f i

theorem mean_const (P : FiniteLaw ι) (c : ℝ) : P.mean (fun _ => c) = c := by
  rw [mean, ← Finset.sum_mul, P.total, one_mul]

theorem mean_add (P : FiniteLaw ι) (f g : ι → ℝ) :
    P.mean (fun i => f i + g i) = P.mean f + P.mean g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]

theorem mean_sub (P : FiniteLaw ι) (f g : ι → ℝ) :
    P.mean (fun i => f i - g i) = P.mean f - P.mean g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_mul (P : FiniteLaw ι) (c : ℝ) (f : ι → ℝ) :
    P.mean (fun i => c * f i) = c * P.mean f := by
  simp only [mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mean_mono (P : FiniteLaw ι) {f g : ι → ℝ} (h : ∀ i, f i ≤ g i) :
    P.mean f ≤ P.mean g :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (P.nonneg i)

theorem mean_nonneg (P : FiniteLaw ι) {f : ι → ℝ} (h : ∀ i, 0 ≤ f i) :
    0 ≤ P.mean f := by
  simpa only [P.mean_const] using P.mean_mono h

def prod (P : FiniteLaw ι) (Q : FiniteLaw κ) : FiniteLaw (ι × κ) where
  weight z := P.weight z.1 * Q.weight z.2
  nonneg z := mul_nonneg (P.nonneg z.1) (Q.nonneg z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, Q.total, mul_one, P.total]

theorem mean_prod (P : FiniteLaw ι) (Q : FiniteLaw κ) (f : ι × κ → ℝ) :
    (P.prod Q).mean f = P.mean (fun i => Q.mean (fun j => f (i,j))) := by
  simp only [mean, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end FiniteLaw
end Komlos.KMFresh

-- END KMProof/FiniteLaw.lean

-- BEGIN KMProof/FiniteProbability.lean
noncomputable section
open Finset
namespace Komlos.KMFresh
namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

def prob (P : FiniteLaw Ω) (A : Ω → Prop) : ℝ := by
  classical
  exact P.mean (fun x => if A x then 1 else 0)

theorem prob_nonneg (P : FiniteLaw Ω) (A : Ω → Prop) : 0 ≤ P.prob A := by
  classical
  apply P.mean_nonneg
  intro x
  split_ifs <;> norm_num

theorem prob_mono (P : FiniteLaw Ω) {A B : Ω → Prop} (h : ∀x, A x → B x) :
    P.prob A ≤ P.prob B := by
  classical
  apply P.mean_mono
  intro x
  by_cases ha : A x
  · simp [ha,h x ha]
  · simp [ha]
    split_ifs <;> norm_num

theorem prob_true (P : FiniteLaw Ω) : P.prob (fun _ => True) = 1 := by
  classical
  simp [prob,P.mean_const]

theorem prob_false (P : FiniteLaw Ω) : P.prob (fun _ => False) = 0 := by
  classical
  simp [prob,P.mean_const]

theorem prob_le_one (P : FiniteLaw Ω) (A : Ω → Prop) : P.prob A ≤ 1 := by
  simpa only [P.prob_true] using P.prob_mono (A := A) (B := fun _ => True) (by simp)

theorem prob_split (P : FiniteLaw Ω) (A B : Ω → Prop) :
    P.prob A = P.prob (fun x => A x ∧ B x) + P.prob (fun x => A x ∧ ¬B x) := by
  classical
  rw [prob,prob,prob,←P.mean_add]
  congr 1
  funext x
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha,hb]

theorem exists_of_prob_pos (P : FiniteLaw Ω) {A : Ω → Prop} (h : 0 < P.prob A) : ∃x,A x := by
  classical
  by_contra hn
  have he : A = fun _ => False := by
    funext x
    exact propext ⟨fun hx => hn ⟨x,hx⟩,False.elim⟩
  rw [he,P.prob_false] at h
  exact lt_irrefl 0 h

end FiniteLaw
end Komlos.KMFresh

-- END KMProof/FiniteProbability.lean

-- BEGIN KMProof/FiniteMoments.lean
noncomputable section
open Finset
namespace Komlos.KMFresh.FiniteLaw
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]
lemma mean_sum (P : FiniteLaw Ω) (f : ι → Ω → ℝ) :
    P.mean (fun ω => ∑i,f i ω)=∑i,P.mean (f i) := by
  simp only [mean,Finset.mul_sum]
  exact Finset.sum_comm

lemma mean_linear_square [DecidableEq ι] (P : FiniteLaw Ω) (r : ι → Ω → ℝ) (a : ι → ℝ)
    (hr : ∀i j,P.mean (fun ω => r i ω*r j ω)=if i=j then 1 else 0) :
    P.mean (fun ω => (∑i,a i*r i ω)^2)=∑i,(a i)^2 := by
  classical
  have he (ω : Ω) : (∑i,a i*r i ω)^2 =
      ∑i,∑j,(a i*a j)*(r i ω*r j ω) := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he,mean_sum,mean_mul,hr]
  simp [pow_two]
end Komlos.KMFresh.FiniteLaw

-- END KMProof/FiniteMoments.lean

-- BEGIN KMProof/FiniteUnion.lean
noncomputable section
open Finset
namespace Komlos.KMFresh.FiniteLaw
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

lemma prob_exists_le_sum (P : FiniteLaw Ω) (A : I → Ω → Prop) :
    P.prob (fun ω => ∃i,A i ω)≤∑i,P.prob (A i) := by
  classical
  unfold prob
  rw [←P.mean_sum]
  apply P.mean_mono
  intro ω
  dsimp only
  by_cases h:∃i,A i ω
  · rw [if_pos h]
    obtain ⟨i,hi⟩ := h
    have hh := Finset.single_le_sum (fun j _ => (show (0:ℝ) ≤ if A j ω then 1 else 0 by split_ifs <;> norm_num))
      (Finset.mem_univ i)
    simpa only [if_pos hi] using hh
  · simp only [if_neg h]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

lemma exists_avoiding (P : FiniteLaw Ω) (A : I → Ω → Prop) (p : I → ℝ)
    (hA : ∀i,P.prob (A i)≤p i) (hp : (∑i,p i)<1) :
    ∃ω,∀i,¬A i ω := by
  classical
  by_contra hn
  have hall : ∀ω,∃i,A i ω := by simpa only [not_exists,not_forall,not_not] using hn
  have he : P.prob (fun ω => ∃i,A i ω)=1 := by
    have hf : (fun ω => ∃i,A i ω)=(fun _ => True) := by funext ω; simp [hall ω]
    rw [hf,P.prob_true]
  have hh := (P.prob_exists_le_sum A).trans (Finset.sum_le_sum (fun i _ => hA i))
  rw [he] at hh
  exact (not_lt_of_ge hh) hp
end Komlos.KMFresh.FiniteLaw

-- END KMProof/FiniteUnion.lean

-- BEGIN KMProof/Confidence.lean
noncomputable section
namespace Komlos.KMFresh

def confidence (n : ℕ) : ℝ := 1/((n:ℝ)+2)^10

lemma confidence_pos (n : ℕ) : 0 < confidence n := by
  unfold confidence
  positivity

lemma confidence_log (n : ℕ) : 1-Real.log (confidence n)=1+10*Real.log ((n:ℝ)+2) := by
  rw [confidence,one_div,Real.log_inv,Real.log_pow]
  push_cast
  ring

lemma confidence_log_bound (n : ℕ) (h : 1 ≤ Real.log ((n:ℝ)+2)) :
    1-Real.log (confidence n) ≤ 11*Real.log ((n:ℝ)+2) := by
  rw [confidence_log]
  linarith

lemma confidence_union_bound (n R P : ℕ) (hR : R ≤ 2*n^3) (hP : P ≤ n+2) :
    ((P:ℝ)*((n:ℝ)+R))*confidence n < 1 := by
  let x : ℝ := (n:ℝ)+2
  have hx : 2 ≤ x := by dsimp [x]; have hn := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx0 : 0 < x := by linarith
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hnle : (n:ℝ) ≤ x := by dsimp [x]; linarith
  have hRR : (R:ℝ) ≤ 2*(n:ℝ)^3 := by exact_mod_cast hR
  have hPP : (P:ℝ) ≤ x := by dsimp [x]; exact_mod_cast hP
  have hn3 : (n:ℝ)^3 ≤ x^3 := pow_le_pow_left₀ hn hnle 3
  have hx3 : x ≤ x^3 := by nlinarith [sq_nonneg (x-1)]
  have hc : (P:ℝ)*((n:ℝ)+R) ≤ 3*x^4 := by
    calc
      _ ≤ x*((n:ℝ)+R) := mul_le_mul_of_nonneg_right hPP (by positivity)
      _ ≤ x*(3*x^3) := mul_le_mul_of_nonneg_left (by linarith) hx0.le
      _ = _ := by ring
  have hx6 : (2:ℝ)^6 ≤ x^6 := pow_le_pow_left₀ (by norm_num) hx 6
  have hlast : 3*x^4 < x^10 := by
    have hp := mul_pos (pow_pos hx0 4) (show 0 < x^6-3 by norm_num at hx6; linarith)
    nlinarith
  change ((P:ℝ)*((n:ℝ)+R))*(1/x^10) < 1
  rw [one_div,←div_eq_mul_inv,div_lt_one (pow_pos hx0 10)]
  exact hc.trans_lt hlast

lemma exists_good_confidence {Ω I : Type*} [Fintype Ω] [Fintype I]
    (law : FiniteLaw Ω) (bad : I → Ω → Prop) (n R P : ℕ)
    (hR : R ≤ 2*n^3) (hP : P ≤ n+2) (hcard : Fintype.card I ≤ P*(n+R))
    (hbad : ∀i,law.prob (bad i) ≤ confidence n) : ∃ω,∀i,¬bad i ω := by
  apply law.exists_avoiding bad (fun _ => confidence n) hbad
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc : (Fintype.card I:ℝ) ≤ (P:ℝ)*((n:ℝ)+R) := by exact_mod_cast hcard
  exact (mul_le_mul_of_nonneg_right hc (confidence_pos n).le).trans_lt (confidence_union_bound n R P hR hP)
end Komlos.KMFresh

-- END KMProof/Confidence.lean

-- BEGIN KMProof/ProductLaw.lean
noncomputable section
open Finset
namespace Komlos.KMFresh
namespace FiniteLaw

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have h : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
    simp [h]

def pi {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*} [∀j,Fintype (α j)]
    (P : ∀j,FiniteLaw (α j)) : FiniteLaw (∀j,α j) where
  weight s := ∏j,(P j).weight (s j)
  nonneg s := Finset.prod_nonneg fun j _ => (P j).nonneg (s j)
  total := by
    classical
    rw [←Fintype.prod_sum]
    simp only [FiniteLaw.total,Finset.prod_const_one]

theorem mean_pi_prod {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*} [∀j,Fintype (α j)]
    (P : ∀j,FiniteLaw (α j)) (f : ∀j,α j → ℝ) :
    (pi P).mean (fun s => ∏j,f j (s j)) = ∏j,(P j).mean (f j) := by
  classical
  simp only [mean,pi,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j a => (P j).weight a*f j a)).symm

theorem mean_pi_eval {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*} [∀j,Fintype (α j)]
    (P : ∀j,FiniteLaw (α j)) (i : J) (f : α i → ℝ) :
    (pi P).mean (fun s => f (s i)) = (P i).mean f := by
  classical
  let g : ∀j,α j → ℝ := fun j a => if h : j=i then f (h ▸ a) else 1
  have h := mean_pi_prod P g
  have he (s : ∀j,α j) : (∏j,g j (s j)) = f (s i) := by
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro b _ hbi
      simp [g,hbi]
    · simp
  have hf : (∏j,(P j).mean (g j)) = (P i).mean f := by
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro b _ hbi
      simp [g,hbi,mean_const]
    · simp
  simpa only [he,hf] using h

end FiniteLaw
end Komlos.KMFresh

-- END KMProof/ProductLaw.lean

-- BEGIN KMProof/HistoryMean.lean
noncomputable section
open Finset
namespace Komlos.KMFresh

abbrev History (Ω : Type*) (n : ℕ) := Fin n → Ω

namespace FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Ξ] [Nonempty Ξ]
lemma uniform_mean_equiv (e : Ω ≃ Ξ) (f : Ξ → ℝ) :
    (uniform Ω).mean (fun x => f (e x))=(uniform Ξ).mean f := by
  unfold mean uniform
  simp only [←Finset.mul_sum,Fintype.card_congr e]
  rw [e.sum_comp]

lemma uniform_mean_prod (f : Ω × Ξ → ℝ) :
    (uniform (Ω × Ξ)).mean f =
      (uniform Ω).mean (fun x => (uniform Ξ).mean (fun y => f (x,y))) := by
  unfold mean uniform
  simp only [Fintype.card_prod,Nat.cast_mul,mul_inv_rev,Fintype.sum_prod_type,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring
end FiniteLaw

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
def historyMean (n : ℕ) (f : History Ω n → ℝ) : ℝ :=
  (FiniteLaw.uniform (History Ω n)).mean f

lemma historyMean_zero (f : History Ω 0 → ℝ) : historyMean 0 f=f Fin.elim0 := by
  unfold historyMean FiniteLaw.mean FiniteLaw.uniform
  simp
  congr 1

lemma historyMean_succ (n : ℕ) (f : History Ω (n+1) → ℝ) :
    historyMean (n+1) f = historyMean n (fun h =>
      (FiniteLaw.uniform Ω).mean (fun x => f (Fin.snoc h x))) := by
  let e : (History Ω n × Ω) ≃ History Ω (n+1) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Ω))
  have he := FiniteLaw.uniform_mean_equiv e f
  rw [FiniteLaw.uniform_mean_prod] at he
  exact he.symm

lemma historyMean_mono {n : ℕ} {f g : History Ω n → ℝ} (h : ∀x,f x≤g x) :
    historyMean n f≤historyMean n g := (FiniteLaw.uniform _).mean_mono h

lemma historyMean_const (n : ℕ) (c : ℝ) :
    historyMean n (fun _ : History Ω n => c)=c :=
  (FiniteLaw.uniform _).mean_const c

lemma historyMean_step_le (M : (n : ℕ) → History Ω n → ℝ) (q : ℝ)
    (hstep : ∀n h,(FiniteLaw.uniform Ω).mean (fun x => M (n+1) (Fin.snoc h x))≤q*M n h)
    (n : ℕ) : historyMean (n+1) (M (n+1)) ≤ q*historyMean n (M n) := by
  rw [historyMean_succ]
  calc
    historyMean n (fun h => (FiniteLaw.uniform Ω).mean
      (fun x => M (n+1) (Fin.snoc h x))) ≤ historyMean n (fun h => q*M n h) :=
      historyMean_mono (hstep n)
    _ = q*historyMean n (M n) := (FiniteLaw.uniform _).mean_mul q _

end Komlos.KMFresh

-- END KMProof/HistoryMean.lean

-- BEGIN KMProof/HistoryMaximal.lean
noncomputable section
open Finset
namespace Komlos.KMFresh
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def historyPrefix {n : ℕ} (h : History Ω n) (k : ℕ) (hk : k≤n) : History Ω k :=
  fun i => h (Fin.castLE hk i)

def historyHit (M : (n : ℕ) → History Ω n → ℝ) (a : ℝ) :
    (n : ℕ) → History Ω n → Prop
  | 0,h => a≤M 0 h
  | n+1,h => historyHit M a n (Fin.init h) ∨ a≤M (n+1) h

def stoppedValue (M : (n : ℕ) → History Ω n → ℝ) (a : ℝ)
    (n : ℕ) (h : History Ω n) : ℝ := by
  classical
  exact if historyHit M a n h then a else M n h

omit [Fintype Ω] [Nonempty Ω] in
lemma historyHit_of_current (M : (n : ℕ) → History Ω n → ℝ) (a : ℝ)
    (n : ℕ) (h : History Ω n) (hh : a≤M n h) : historyHit M a n h := by
  cases n with
  | zero => exact hh
  | succ n => exact Or.inr hh

omit [Fintype Ω] [Nonempty Ω] in
lemma historyHit_of_prefix (M : (n : ℕ) → History Ω n → ℝ) (a : ℝ)
    {n k : ℕ} (hk : k≤n) (h : History Ω n)
    (hh : historyHit M a k (historyPrefix h k hk)) : historyHit M a n h := by
  induction n with
  | zero =>
    have : k=0 := by omega
    subst k
    exact hh
  | succ n ih =>
    by_cases he : k=n+1
    · subst k
      exact hh
    · have hkn : k≤n := by omega
      apply Or.inl
      apply ih hkn (Fin.init h)
      have heq : historyPrefix (Fin.init h) k hkn = historyPrefix h k hk := by
        funext i
        apply congrArg h
        apply Fin.ext
        rfl
      rw [heq]
      exact hh

lemma stoppedValue_step (M : (n : ℕ) → History Ω n → ℝ) (a : ℝ)
    (hstep : ∀n h,(FiniteLaw.uniform Ω).mean (fun x => M (n+1) (Fin.snoc h x))≤M n h)
    (n : ℕ) (h : History Ω n) :
    (FiniteLaw.uniform Ω).mean (fun x => stoppedValue M a (n+1) (Fin.snoc h x))≤
      stoppedValue M a n h := by
  classical
  by_cases hh : historyHit M a n h
  · simp [stoppedValue,historyHit,hh,FiniteLaw.mean_const]
  · have hb (x : Ω) : stoppedValue M a (n+1) (Fin.snoc h x)≤M (n+1) (Fin.snoc h x) := by
      simp only [stoppedValue,historyHit,Fin.init_snoc,hh,false_or]
      split_ifs with hx
      · exact hx
      · exact le_refl _
    simpa only [stoppedValue,if_neg hh] using
      ((FiniteLaw.uniform Ω).mean_mono hb).trans (hstep n h)

lemma stoppedValue_mean_le (M : (n : ℕ) → History Ω n → ℝ) (a : ℝ)
    (hstep : ∀n h,(FiniteLaw.uniform Ω).mean (fun x => M (n+1) (Fin.snoc h x))≤M n h)
    (n : ℕ) : historyMean n (stoppedValue M a n)≤M 0 Fin.elim0 := by
  induction n with
  | zero =>
    rw [historyMean_zero]
    unfold stoppedValue historyHit
    split_ifs with h
    · exact h
    · exact le_refl _
  | succ n ih =>
    have hs := historyMean_step_le (stoppedValue M a) 1
      (fun t h => by simpa only [one_mul] using stoppedValue_step M a hstep t h) n
    simpa only [one_mul] using hs.trans (by simpa only [one_mul] using ih)

lemma history_maximal_bound (M : (n : ℕ) → History Ω n → ℝ) {a : ℝ} (ha : 0<a)
    (hM : ∀n h,0≤M n h)
    (hstep : ∀n h,(FiniteLaw.uniform Ω).mean (fun x => M (n+1) (Fin.snoc h x))≤M n h)
    (n : ℕ) : (FiniteLaw.uniform (History Ω n)).prob (historyHit M a n)≤M 0 Fin.elim0/a := by
  classical
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm]
  have hp : a*(FiniteLaw.uniform (History Ω n)).prob (historyHit M a n)≤
      historyMean n (stoppedValue M a n) := by
    unfold FiniteLaw.prob
    rw [←FiniteLaw.mean_mul]
    apply (FiniteLaw.uniform _).mean_mono
    intro h
    unfold stoppedValue
    split_ifs
    · simp
    · simpa using hM n h
  exact hp.trans (stoppedValue_mean_le M a hstep n)

end Komlos.KMFresh

-- END KMProof/HistoryMaximal.lean

-- BEGIN KMProof/GoodHistoryEvents.lean

noncomputable section
namespace Komlos.KMFresh

lemma exists_good_history_events {R Ω : Type*} [Fintype R] [Fintype Ω] [Nonempty Ω]
    (n q N : ℕ) (hR : Fintype.card R ≤ 2*n^3) (hP : q+1 ≤ n+2)
    (column : Fin (q+1) → Fin n → (k:ℕ) → History Ω k → ℝ)
    (row : Fin (q+1) → R → (k:ℕ) → History Ω k → ℝ)
    (active : Fin (q+1) → R → (k:ℕ) → History Ω k → Prop)
    (eligible : Fin (q+1) → Prop) (columnBound rowBound : Fin (q+1) → ℝ)
    (hcolumn : ∀p j,(FiniteLaw.uniform (History Ω N)).prob
      (fun h => ∃k:ℕ,∃hk:k ≤ N,columnBound p < column p j k (historyPrefix h k hk)) ≤ confidence n)
    (hrow : ∀p r,eligible p → (FiniteLaw.uniform (History Ω N)).prob
      (fun h => ∃k:ℕ,∃hk:k ≤ N,active p r k (historyPrefix h k hk) ∧
        rowBound p ≤ row p r k (historyPrefix h k hk)) ≤ confidence n) :
    ∃h : History Ω N,
      (∀p j k (hk:k ≤ N),column p j k (historyPrefix h k hk) ≤ columnBound p) ∧
      (∀p r,eligible p → ∀k (hk:k ≤ N),active p r k (historyPrefix h k hk) →
        row p r k (historyPrefix h k hk) < rowBound p) := by
  classical
  let bad : (Fin (q+1) × (Fin n ⊕ R)) → History Ω N → Prop := fun i h =>
    match i.2 with
    | Sum.inl j => ∃k:ℕ,∃hk:k ≤ N,columnBound i.1 < column i.1 j k (historyPrefix h k hk)
    | Sum.inr r => eligible i.1 ∧ ∃k:ℕ,∃hk:k ≤ N,active i.1 r k (historyPrefix h k hk) ∧
        rowBound i.1 ≤ row i.1 r k (historyPrefix h k hk)
  have hb i : (FiniteLaw.uniform (History Ω N)).prob (bad i) ≤ confidence n := by
    rcases i with ⟨p,j|r⟩
    · exact hcolumn p j
    · by_cases he : eligible p
      · simpa only [bad,he,true_and] using hrow p r he
      · simp only [bad,he,false_and,FiniteLaw.prob_false]
        exact (confidence_pos n).le
  obtain ⟨h,hh⟩ := exists_good_confidence (FiniteLaw.uniform (History Ω N)) bad n
    (Fintype.card R) (q+1) hR hP (by simp) hb
  refine ⟨h,?_,?_⟩
  · intro p j k hk
    exact le_of_not_gt (fun ht => hh (p,Sum.inl j) ⟨k,hk,ht⟩)
  · intro p r he k hk ha
    exact lt_of_not_ge (fun ht => hh (p,Sum.inr r) ⟨he,k,hk,ha,ht⟩)

end Komlos.KMFresh

-- END KMProof/GoodHistoryEvents.lean

-- BEGIN KMProof/AdaptiveState.lean

namespace Komlos.KMFresh

structure AdaptiveState (R : Type*) (n : ℕ) where
  x : Fin n → ℝ
  hit : Finset R

noncomputable def aliveSet {n : ℕ} (ρ : ℝ) (x : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => |x i| < 1 - ρ)

noncomputable def rowEnergy {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (x : Fin n → ℝ) (r : R) : ℝ :=
  ∑ i ∈ aliveSet ρ x, A r i ^ 2

def rowDiscrepancy {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (x : Fin n → ℝ) (r : R) : ℝ := ∑ i, A r i * x i

noncomputable def adaptiveStep {R Ω : Type*} [Fintype R] {n : ℕ}
    (running : AdaptiveState R n → Prop)
    (direction : AdaptiveState R n → Ω → Fin n → ℝ)
    (newHit : (Fin n → ℝ) → R → Prop) (t : ℝ)
    (s : AdaptiveState R n) (ω : Ω) : AdaptiveState R n := by
  classical
  exact if running s then
    let y := fun i => s.x i + t * direction s ω i
    ⟨y, s.hit ∪ Finset.univ.filter (newHit y)⟩
  else s

noncomputable def adaptiveHistory {S Ω : Type*} (initial : S)
    (step : ℕ → S → Ω → S) : (k : ℕ) → (Fin k → Ω) → S
  | 0, _ => initial
  | k + 1, ω => step k (adaptiveHistory initial step k (Fin.init ω)) (ω (Fin.last k))

lemma adaptiveStep_x {R Ω : Type*} [Fintype R] {n : ℕ}
    (running : AdaptiveState R n → Prop)
    (direction : AdaptiveState R n → Ω → Fin n → ℝ)
    (newHit : (Fin n → ℝ) → R → Prop) (t : ℝ)
    (s : AdaptiveState R n) (ω : Ω) (h : running s) :
    (adaptiveStep running direction newHit t s ω).x =
      fun i => s.x i + t * direction s ω i := by
  classical
  simp only [adaptiveStep, if_pos h]

lemma adaptiveStep_hit_mono {R Ω : Type*} [Fintype R] {n : ℕ}
    (running : AdaptiveState R n → Prop)
    (direction : AdaptiveState R n → Ω → Fin n → ℝ)
    (newHit : (Fin n → ℝ) → R → Prop) (t : ℝ)
    (s : AdaptiveState R n) (ω : Ω) :
    s.hit ⊆ (adaptiveStep running direction newHit t s ω).hit := by
  classical
  unfold adaptiveStep
  split_ifs
  · exact Finset.subset_union_left
  · exact Finset.Subset.refl _

lemma rowEnergy_nonneg {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (x : Fin n → ℝ) (r : R) : 0 ≤ rowEnergy A ρ x r := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

end Komlos.KMFresh

-- END KMProof/AdaptiveState.lean

-- BEGIN KMProof/WalkAlgebra.lean

namespace Komlos.KMFresh

lemma square_step (x v t : ℝ) :
    (x + t * v) ^ 2 = x ^ 2 + 2 * t * (x * v) + t ^ 2 * v ^ 2 := by
  ring

lemma square_mass_step {I : Type*} [Fintype I] (x v : I → ℝ) (t : ℝ)
    (hortho : ∑ i, x i * v i = 0) (hunit : ∑ i, v i ^ 2 = 1) :
    ∑ i, (x i + t * v i) ^ 2 = (∑ i, x i ^ 2) + t ^ 2 := by
  simp only [square_step, Finset.sum_add_distrib, ← Finset.mul_sum, hortho, hunit,
    mul_zero, mul_one, add_zero]

lemma step_box (x v t ρ : ℝ) (ht : 0 ≤ t) (htρ : t ≤ ρ)
    (hx : |x| ≤ 1 - ρ) (hv : |v| ≤ 1) : |x + t * v| ≤ 1 := by
  calc
    |x + t * v| ≤ |x| + |t * v| := abs_add_le _ _
    _ = |x| + t * |v| := by rw [abs_mul, abs_of_nonneg ht]
    _ ≤ (1 - ρ) + t * 1 := add_le_add hx (mul_le_mul_of_nonneg_left hv ht)
    _ ≤ 1 := by linarith

lemma square_mass_le_card {I : Type*} [Fintype I] (x : I → ℝ)
    (hx : ∀ i, |x i| ≤ 1) : ∑ i, x i ^ 2 ≤ (Fintype.card I : ℝ) := by
  calc
    ∑ i, x i ^ 2 ≤ ∑ _i : I, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hx i
      have hab := abs_nonneg (x i)
      have hs := sq_abs (x i)
      nlinarith
    _ = _ := by simp

lemma growth_forces_stop (E : ℕ → ℝ) (ε M : ℝ) (N : ℕ)
    (_hε : 0 < ε) (hE0 : 0 ≤ E 0) (hbound : E N ≤ M)
    (hstep : ∀ k < N, E (k + 1) = E k + ε) (hN : M < N * ε) : False := by
  have hg : ∀ k ≤ N, E k = E 0 + k * ε := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hstep k (by omega), ih (by omega)]
      push_cast
      ring
  have hlast := hg N le_rfl
  nlinarith

end Komlos.KMFresh

-- END KMProof/WalkAlgebra.lean

-- BEGIN KMProof/AliveDynamics.lean

namespace Komlos.KMFresh

lemma mem_aliveSet {n : ℕ} (ρ : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    i ∈ aliveSet ρ x ↔ |x i| < 1 - ρ := by
  classical
  simp [aliveSet]

lemma aliveSet_shrinks {n : ℕ} (ρ : ℝ) (x y : Fin n → ℝ)
    (hfix : ∀ i, i ∉ aliveSet ρ x → y i = x i) :
    aliveSet ρ y ⊆ aliveSet ρ x := by
  intro i hi
  by_contra hx
  have hy := (mem_aliveSet ρ y i).mp hi
  rw [hfix i hx] at hy
  exact hx ((mem_aliveSet ρ x i).mpr hy)

lemma rowEnergy_decreases {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (x y : Fin n → ℝ) (r : R)
    (hfix : ∀ i, i ∉ aliveSet ρ x → y i = x i) :
    rowEnergy A ρ y r ≤ rowEnergy A ρ x r := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (aliveSet_shrinks ρ x y hfix)
  intro i _ _
  exact sq_nonneg _

lemma unit_coordinate_bound {n : ℕ} (v : Fin n → ℝ) (hv : ∑ i, v i ^ 2 = 1)
    (i : Fin n) : |v i| ≤ 1 := by
  have hs : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  rw [hv] at hs
  have ha := abs_nonneg (v i)
  have he := sq_abs (v i)
  nlinarith

lemma supported_step_box {n : ℕ} (ρ t : ℝ) (x v : Fin n → ℝ)
    (ht : 0 ≤ t) (htρ : t ≤ ρ) (hx : ∀ i, |x i| ≤ 1)
    (hv : ∑ i, v i ^ 2 = 1) (hsupport : ∀ i, i ∉ aliveSet ρ x → v i = 0) :
    ∀ i, |x i + t * v i| ≤ 1 := by
  intro i
  by_cases hi : i ∈ aliveSet ρ x
  · exact step_box _ _ _ _ ht htρ ((mem_aliveSet ρ x i).mp hi).le
      (unit_coordinate_bound v hv i)
  · rw [hsupport i hi, mul_zero, add_zero]
    exact hx i

lemma supported_step_alive {n : ℕ} (ρ t : ℝ) (x v : Fin n → ℝ)
    (hsupport : ∀ i, i ∉ aliveSet ρ x → v i = 0) :
    aliveSet ρ (fun i => x i + t * v i) ⊆ aliveSet ρ x := by
  apply aliveSet_shrinks
  intro i hi
  simp only [hsupport i hi, mul_zero, add_zero]

end Komlos.KMFresh

-- END KMProof/AliveDynamics.lean

-- BEGIN KMProof/RowPhases.lean

namespace Komlos.KMFresh

noncomputable def rowLarge {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k : R → ℝ) (x : Fin n → ℝ) (r : R) : Prop :=
  64 * k r < rowEnergy A ρ x r
noncomputable def rowTiny {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (μ : R → ℝ) (x : Fin n → ℝ) (r : R) : Prop :=
  rowEnergy A ρ x r ≤ μ r
noncomputable def rowMedium {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ : R → ℝ) (x : Fin n → ℝ) (r : R) : Prop :=
  μ r < rowEnergy A ρ x r ∧ rowEnergy A ρ x r ≤ 64 * k r
noncomputable def newlyDangerous {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ b : R → ℝ) (x : Fin n → ℝ) (r : R) : Prop :=
  rowMedium A ρ k μ x r ∧ 2 * b r ≤ rowDiscrepancy A x r

lemma row_phase_exhaustive {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ : R → ℝ) (x : Fin n → ℝ) (r : R) :
    rowLarge A ρ k x r ∨ rowMedium A ρ k μ x r ∨ rowTiny A ρ μ x r := by
  unfold rowLarge rowMedium rowTiny
  by_cases h : 64 * k r < rowEnergy A ρ x r
  · exact Or.inl h
  · by_cases ht : rowEnergy A ρ x r ≤ μ r
    · exact Or.inr (Or.inr ht)
    · exact Or.inr (Or.inl ⟨lt_of_not_ge ht, le_of_not_gt h⟩)

lemma rowTiny_persistent {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (μ : R → ℝ) (x y : Fin n → ℝ) (r : R)
    (hfix : ∀ i, i ∉ aliveSet ρ x → y i = x i)
    (ht : rowTiny A ρ μ x r) : rowTiny A ρ μ y r :=
  (rowEnergy_decreases A ρ x y r hfix).trans ht

lemma rowLarge_no_reentry {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k : R → ℝ) (x y : Fin n → ℝ) (r : R)
    (hfix : ∀ i, i ∉ aliveSet ρ x → y i = x i)
    (ht : ¬rowLarge A ρ k x r) : ¬rowLarge A ρ k y r := by
  unfold rowLarge at *
  have he := rowEnergy_decreases A ρ x y r hfix
  linarith

end Komlos.KMFresh

-- END KMProof/RowPhases.lean

-- BEGIN KMProof/RowAlgebra.lean

namespace Komlos.KMFresh

lemma regularized_coordinate_step (a x v t β : ℝ) :
    a * (x + t * v) + β * a ^ 2 * (1 - (x + t * v) ^ 2) -
      (a * x + β * a ^ 2 * (1 - x ^ 2)) =
    t * ((a - 2 * β * a ^ 2 * x) * v) - t ^ 2 * (β * a ^ 2 * v ^ 2) := by
  ring

lemma regularized_row_step {I : Type*} [Fintype I]
    (a x v : I → ℝ) (t β : ℝ) :
    (∑ i, (a i * (x i + t * v i) + β * a i ^ 2 * (1 - (x i + t * v i) ^ 2))) -
      (∑ i, (a i * x i + β * a i ^ 2 * (1 - x i ^ 2))) =
    t * (∑ i, (a i - 2 * β * a i ^ 2 * x i) * v i) -
      t ^ 2 * (∑ i, β * a i ^ 2 * v i ^ 2) := by
  rw [← Finset.sum_sub_distrib]
  simp only [regularized_coordinate_step, Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma remaining_energy_nonneg (a x : ℝ) (hx : |x| ≤ 1) :
    0 ≤ a ^ 2 * (1 - x ^ 2) := by
  have hs : x ^ 2 ≤ 1 := by
    have ha := abs_nonneg x
    have he := sq_abs x
    nlinarith
  exact mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hs)

lemma freeze_energy_decreases {I : Type*} [DecidableEq I]
    (A B : Finset I) (a x : I → ℝ) (β : ℝ) (hBA : B ⊆ A)
    (hβ : 0 ≤ β) (hx : ∀ i ∈ A, |x i| ≤ 1) :
    β * (∑ i ∈ B, a i ^ 2 * (1 - x i ^ 2)) ≤
      β * (∑ i ∈ A, a i ^ 2 * (1 - x i ^ 2)) := by
  apply mul_le_mul_of_nonneg_left _ hβ
  apply Finset.sum_le_sum_of_subset_of_nonneg hBA
  intro i hi _
  exact remaining_energy_nonneg (a i) (x i) (hx i hi)

end Komlos.KMFresh

-- END KMProof/RowAlgebra.lean

-- BEGIN KMProof/ActiveRegularizer.lean

namespace Komlos.KMFresh

noncomputable def activeRegularizer {I : Type*} [Fintype I]
    (A : Finset I) (a x : I → ℝ) (β : ℝ) : ℝ :=
  (∑ i, a i * x i) + β * ∑ i ∈ A, a i ^ 2 * (1 - x i ^ 2)

lemma activeRegularizer_freeze {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Finset I) (a x : I → ℝ) (β : ℝ) (hBA : B ⊆ A)
    (hβ : 0 ≤ β) (hx : ∀ i ∈ A, |x i| ≤ 1) :
    activeRegularizer B a x β ≤ activeRegularizer A a x β := by
  exact add_le_add le_rfl (freeze_energy_decreases A B a x β hBA hβ hx)

lemma activeRegularizer_step {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (a x v : I → ℝ) (t β : ℝ)
    (hsupport : ∀ i, i ∉ A → v i = 0) :
    activeRegularizer A a (fun i => x i + t * v i) β - activeRegularizer A a x β =
      t * (∑ i ∈ A, (a i - 2 * β * a i ^ 2 * x i) * v i) -
        t ^ 2 * (∑ i ∈ A, β * a i ^ 2 * v i ^ 2) := by
  have hl : (∑ i, (a i * (x i + t * v i) - a i * x i)) =
      ∑ i ∈ A, (a i * (x i + t * v i) - a i * x i) := by
    apply (Finset.sum_subset (Finset.subset_univ A) ?_).symm
    intro i _ hi
    simp only [hsupport i hi, mul_zero, add_zero, sub_self]
  unfold activeRegularizer
  have he : (∑ i, a i * (x i + t * v i)) - (∑ i, a i * x i) =
      ∑ i ∈ A, (a i * (x i + t * v i) - a i * x i) := by
    rw [← Finset.sum_sub_distrib]
    exact hl
  calc
    _ = (∑ i ∈ A, (a i * (x i + t * v i) - a i * x i)) +
        β * ((∑ i ∈ A, a i ^ 2 * (1 - (x i + t * v i) ^ 2)) -
          ∑ i ∈ A, a i ^ 2 * (1 - x i ^ 2)) := by linarith
    _ = ∑ i ∈ A, ((a i * (x i + t * v i) + β * a i ^ 2 * (1 - (x i + t * v i) ^ 2)) -
          (a i * x i + β * a i ^ 2 * (1 - x i ^ 2))) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [regularized_coordinate_step, Finset.sum_sub_distrib, ← Finset.mul_sum]

end Komlos.KMFresh

-- END KMProof/ActiveRegularizer.lean

-- BEGIN KMProof/ProxyExponential.lean
noncomputable section
namespace Komlos.KMFresh

lemma exp_quadratic_absolute {x : ℝ} (hx : |x|≤1) :
    Real.exp x≤1+x+x^2 := by
  have hh := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
  linarith

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
lemma mean_exp_quadratic (P : FiniteLaw Ω) (Y : Ω → ℝ) (δ : ℝ)
    (hb : ∀ω,|δ*Y ω|≤1) :
    P.mean (fun ω => Real.exp (δ*Y ω))≤
      1+δ*P.mean Y+δ^2*P.mean (fun ω => (Y ω)^2) := by
  have hh := P.mean_mono (fun ω => exp_quadratic_absolute (hb ω))
  have he : (fun ω => 1+δ*Y ω+(δ*Y ω)^2) =
      (fun ω => (1+δ*Y ω)+δ^2*(Y ω)^2) := by funext ω; ring
  rw [he,P.mean_add,P.mean_add,P.mean_const,P.mean_mul,P.mean_mul] at hh
  exact hh

lemma proxy_exp_bound (P : FiniteLaw Ω) (Y : Ω → ℝ)
    {δ a b s e₁ e₂ : ℝ} (hδ : 0≤δ)
    (hmean : P.mean Y≤-a*s+e₁)
    (hsquare : P.mean (fun ω => (Y ω)^2)≤b*s+e₂)
    (hcancel : δ^2*b≤δ*a) (hs : 0 ≤ s)
    (hb : ∀ω,|δ*Y ω|≤1) :
    P.mean (fun ω => Real.exp (δ*Y ω))≤1+δ*e₁+δ^2*e₂ := by
  have hm := mul_le_mul_of_nonneg_left hmean hδ
  have hq := mul_le_mul_of_nonneg_left hsquare (sq_nonneg δ)
  have hc := mul_le_mul_of_nonneg_right hcancel hs
  have he := P.mean_exp_quadratic Y δ hb
  nlinarith
end FiniteLaw
end Komlos.KMFresh

-- END KMProof/ProxyExponential.lean

-- BEGIN KMProof/CappedExponential.lean
noncomputable section
namespace Komlos.KMFresh

def cappedExponential (lam B z : ℝ) : ℝ := Real.exp (lam*min z B)

lemma capped_exponential_increment {lam B z z' Δ : ℝ}
    (hlam : 0≤lam) (hz : z≤B) (hz' : z'≤z+Δ) (hΔ : |lam*Δ|≤1) :
    cappedExponential lam B z'-cappedExponential lam B z≤
      (lam*Real.exp (lam*z))*(Δ+lam*Δ^2) := by
  have h1 : Real.exp (lam*min z' B)≤Real.exp (lam*(z+Δ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hz') hlam)
  have h2 := mul_le_mul_of_nonneg_left (exp_quadratic_absolute hΔ) (Real.exp_pos (lam*z)).le
  have he : Real.exp (lam*(z+Δ))=Real.exp (lam*z)*Real.exp (lam*Δ) := by
    rw [mul_add,Real.exp_add]
  rw [he] at h1
  simp only [cappedExponential,min_eq_left hz]
  nlinarith

lemma capped_exponential_bound {lam B z : ℝ} (hlam : 0≤lam) :
    cappedExponential lam B z≤Real.exp (lam*B) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (min_le_right _ _) hlam)

lemma capped_exponential_monotone {lam B x y : ℝ} (hlam : 0≤lam) (hxy : x≤y) :
    cappedExponential lam B x≤cappedExponential lam B y :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (min_le_min_right B hxy) hlam)

lemma exponential_weight_bound {lam B z : ℝ} (hlam : 0≤lam) (hz : z≤B) :
    0≤lam*Real.exp (lam*z) ∧ lam*Real.exp (lam*z)≤lam*Real.exp (lam*B) :=
  ⟨mul_nonneg hlam (Real.exp_pos _).le,
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz hlam)) hlam⟩
end Komlos.KMFresh

-- END KMProof/CappedExponential.lean

-- BEGIN KMProof/RegularizedPhases.lean

namespace Komlos.KMFresh

noncomputable def rowRegularizer {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (β : R → ℝ) (x : Fin n → ℝ) (r : R) : ℝ :=
  activeRegularizer (aliveSet ρ x) (A r) x (β r)

noncomputable def regularizedHit {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b : R → ℝ) (x : Fin n → ℝ) (r : R) : Prop :=
  rowMedium A ρ k μ x r ∧ 2 * b r ≤ rowRegularizer A ρ β x r

noncomputable def phasePotential {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b lam : R → ℝ) (s : AdaptiveState R n) (r : R) : ℝ := by
  classical
  exact if r ∈ s.hit then Real.exp (lam r * (2 * b r))
    else if rowLarge A ρ k s.x r then Real.exp (lam r * b r)
    else if rowTiny A ρ μ s.x r then 0
    else cappedExponential (lam r) (2 * b r) (rowRegularizer A ρ β s.x r)

lemma rowRegularizer_ge_discrepancy {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (β : R → ℝ) (x : Fin n → ℝ) (r : R)
    (hβ : 0 ≤ β r) (hx : ∀ i, |x i| ≤ 1) :
    rowDiscrepancy A x r ≤ rowRegularizer A ρ β x r := by
  have he : 0 ≤ ∑ i ∈ aliveSet ρ x, A r i ^ 2 * (1 - x i ^ 2) := by
    apply Finset.sum_nonneg
    intro i _
    have hi := (abs_le.mp (hx i))
    exact mul_nonneg (sq_nonneg _) (by nlinarith)
  exact le_add_of_nonneg_right (mul_nonneg hβ he)

lemma phasePotential_nonneg {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b lam : R → ℝ) (s : AdaptiveState R n) (r : R) :
    0 ≤ phasePotential A ρ k μ β b lam s r := by
  classical
  unfold phasePotential
  split_ifs <;> first | exact (Real.exp_pos _).le | exact le_rfl

lemma phasePotential_hit {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b lam : R → ℝ) (s : AdaptiveState R n) (r : R)
    (hr : r ∈ s.hit) :
    phasePotential A ρ k μ β b lam s r = Real.exp (lam r * (2 * b r)) := by
  classical
  simp only [phasePotential, if_pos hr]

lemma phasePotential_medium {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b lam : R → ℝ) (s : AdaptiveState R n) (r : R)
    (hr : r ∉ s.hit) (hm : rowMedium A ρ k μ s.x r) :
    phasePotential A ρ k μ β b lam s r =
      cappedExponential (lam r) (2 * b r) (rowRegularizer A ρ β s.x r) := by
  classical
  have hl : ¬rowLarge A ρ k s.x r := not_lt_of_ge hm.2
  have ht : ¬rowTiny A ρ μ s.x r := not_le_of_gt hm.1
  simp only [phasePotential, if_neg hr, if_neg hl, if_neg ht]

lemma regularizedHit_of_discrepancy {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b : R → ℝ) (x : Fin n → ℝ) (r : R)
    (hm : rowMedium A ρ k μ x r) (hβ : 0 ≤ β r) (hx : ∀ i, |x i| ≤ 1)
    (hd : 2 * b r ≤ rowDiscrepancy A x r) : regularizedHit A ρ k μ β b x r :=
  ⟨hm, hd.trans (rowRegularizer_ge_discrepancy A ρ β x r hβ hx)⟩

end Komlos.KMFresh

-- END KMProof/RegularizedPhases.lean

-- BEGIN KMProof/EnergyCounting.lean

namespace Komlos.KMFresh

lemma weighted_row_count {R C : Type*}
    (rows : Finset R) (alive : Finset C) (w : R → C → ℝ) (μ K : ℝ)
    (hrow : ∀ i ∈ rows, μ ≤ ∑ j ∈ alive, w i j)
    (hcol : ∀ j ∈ alive, ∑ i ∈ rows, w i j ≤ K) :
    (rows.card : ℝ) * μ ≤ (alive.card : ℝ) * K := by
  calc
    (rows.card : ℝ) * μ = ∑ _i ∈ rows, μ := by simp
    _ ≤ ∑ i ∈ rows, ∑ j ∈ alive, w i j := Finset.sum_le_sum hrow
    _ = ∑ j ∈ alive, ∑ i ∈ rows, w i j := Finset.sum_comm
    _ ≤ ∑ _j ∈ alive, K := Finset.sum_le_sum hcol
    _ = (alive.card : ℝ) * K := by simp

lemma square_column_subset {R C : Type*} [Fintype R]
    (rows : Finset R) (A : R → C → ℝ) (j : C) :
    ∑ i ∈ rows, A i j ^ 2 ≤ ∑ i, A i j ^ 2 := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ rows)
  intro i _ _
  exact sq_nonneg _

end Komlos.KMFresh

-- END KMProof/EnergyCounting.lean

-- BEGIN KMProof/DangerousCount.lean

namespace Komlos.KMFresh

lemma dangerous_rows_count {R C : Type*} (dangerous : Finset R) (alive : Finset C)
    (A : R → C → ℝ) (μ P : ℝ) (hμ : 0 < μ)
    (hr : ∀ i ∈ dangerous, μ ≤ ∑ j ∈ alive, A i j ^ 2)
    (hc : ∀ j ∈ alive, ∑ i ∈ dangerous, A i j ^ 2 ≤ μ / (64 * P)) :
    (dangerous.card : ℝ) ≤ (alive.card : ℝ) / (64 * P) := by
  have h := weighted_row_count dangerous alive (fun i j => A i j ^ 2) μ (μ / (64 * P)) hr hc
  suffices he : (dangerous.card : ℝ) * μ ≤ ((alive.card : ℝ) / (64 * P)) * μ by
    nlinarith
  calc
    (dangerous.card : ℝ) * μ ≤ (alive.card : ℝ) * (μ / (64 * P)) := h
    _ = ((alive.card : ℝ) / (64 * P)) * μ := by ring

lemma sum_dangerous_count {P : ℕ} (hP : 0 < P) (d : Fin P → ℕ) (h : ℕ)
    (hd : ∀ p, (d p : ℝ) ≤ (h : ℝ) / (64 * (P : ℝ))) :
    (∑ p, (d p : ℝ)) ≤ (h : ℝ) / 64 := by
  have hp : (P : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hP)
  calc
    (∑ p, (d p : ℝ)) ≤ ∑ _p : Fin P, (h : ℝ) / (64 * (P : ℝ)) :=
      Finset.sum_le_sum (fun p _ => hd p)
    _ = (h : ℝ) / 64 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

end Komlos.KMFresh

-- END KMProof/DangerousCount.lean

-- BEGIN KMProof/StateRowCounts.lean

namespace Komlos.KMFresh

noncomputable def mediumRows {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (ρ k μ : ℝ) (x : Fin n → ℝ) : Finset R := by
  classical
  exact Finset.univ.filter (fun r => μ < rowEnergy A ρ x r ∧ rowEnergy A ρ x r ≤ 64 * k)

noncomputable def dangerousRows {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (ρ k μ : ℝ) (s : AdaptiveState R n) : Finset R := by
  classical
  exact (mediumRows A ρ k μ s.x).filter (fun r => r ∈ s.hit)

lemma mediumRows_count {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (ρ k μ : ℝ) (x : Fin n → ℝ)
    (hc : ∀ i, ∑ r, A r i ^ 2 ≤ 2 * k) :
    ((mediumRows A ρ k μ x).card : ℝ) * μ ≤ 2 * k * (aliveSet ρ x).card := by
  classical
  have hr : ∀ r ∈ mediumRows A ρ k μ x, μ ≤ ∑ i ∈ aliveSet ρ x, A r i ^ 2 := by
    intro r hr
    exact ((Finset.mem_filter.mp hr).2.1).le
  have hcol : ∀ i ∈ aliveSet ρ x, ∑ r ∈ mediumRows A ρ k μ x, A r i ^ 2 ≤ 2 * k := by
    intro i _
    exact (square_column_subset (mediumRows A ρ k μ x) A i).trans (hc i)
  have he := weighted_row_count (mediumRows A ρ k μ x) (aliveSet ρ x)
    (fun r i => A r i ^ 2) μ (2 * k) hr hcol
  nlinarith

lemma dangerousRows_count {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (ρ k μ P : ℝ) (s : AdaptiveState R n) (hμ : 0 < μ)
    (hc : ∀ i ∈ aliveSet ρ s.x, ∑ r ∈ s.hit, A r i ^ 2 ≤ μ / (64 * P)) :
    ((dangerousRows A ρ k μ s).card : ℝ) ≤ (aliveSet ρ s.x).card / (64 * P) := by
  classical
  apply dangerous_rows_count (dangerousRows A ρ k μ s) (aliveSet ρ s.x) A μ P hμ
  · intro r hr
    exact ((Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.1).le
  · intro i hi
    apply le_trans _ (hc i hi)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro r hr
      exact (Finset.mem_filter.mp hr).2
    · intro r _ _
      exact sq_nonneg _

end Komlos.KMFresh

-- END KMProof/StateRowCounts.lean

-- BEGIN KMProof/RawScales.lean

namespace Komlos.KMFresh

noncomputable def scaleCut (p : ℕ) : ℝ := (1 / 2 : ℝ) ^ p
noncomputable def lightEntry (p : ℕ) (a : ℝ) : ℝ := if |a| ≤ scaleCut p then a else 0
noncomputable def heavyEntry (p : ℕ) (a : ℝ) : ℝ :=
  if scaleCut (p + 1) < |a| ∧ |a| ≤ scaleCut p then a else 0

lemma scaleCut_pos (p : ℕ) : 0 < scaleCut p := by unfold scaleCut; positivity

lemma scaleCut_succ (p : ℕ) : scaleCut (p + 1) = scaleCut p / 2 := by
  unfold scaleCut
  rw [pow_succ]
  ring

lemma scaleCut_decreases (p : ℕ) : scaleCut (p + 1) ≤ scaleCut p := by
  rw [scaleCut_succ]
  have := scaleCut_pos p
  linarith

lemma lightEntry_split (p : ℕ) (a : ℝ) :
    lightEntry p a = heavyEntry p a + lightEntry (p + 1) a := by
  unfold lightEntry heavyEntry
  by_cases hp : |a| ≤ scaleCut p
  · by_cases hn : |a| ≤ scaleCut (p + 1)
    · simp [hp, hn, not_lt.mpr hn]
    · simp [hp, hn, lt_of_not_ge hn]
  · have hn : ¬ |a| ≤ scaleCut (p + 1) := fun h => hp (h.trans (scaleCut_decreases p))
    simp [hp, hn]

lemma lightEntry_square_split (p : ℕ) (a : ℝ) :
    (lightEntry p a) ^ 2 = (heavyEntry p a) ^ 2 + (lightEntry (p + 1) a) ^ 2 := by
  unfold lightEntry heavyEntry
  by_cases hp : |a| ≤ scaleCut p
  · by_cases hn : |a| ≤ scaleCut (p + 1)
    · simp [hp, hn, not_lt.mpr hn]
    · simp [hp, hn, lt_of_not_ge hn]
  · have hn : ¬ |a| ≤ scaleCut (p + 1) := fun h => hp (h.trans (scaleCut_decreases p))
    simp [hp, hn]

lemma scale_reconstruction (q : ℕ) (a : ℝ) (ha : |a| ≤ 1) :
    a = (∑ p ∈ Finset.range q, heavyEntry p a) + lightEntry q a := by
  have h : ∀ q, lightEntry 0 a = (∑ p ∈ Finset.range q, heavyEntry p a) + lightEntry q a := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Finset.sum_range_succ]
      have hs := lightEntry_split q a
      linarith
  simpa [lightEntry, scaleCut, ha] using h q

lemma scale_square_reconstruction (q : ℕ) (a : ℝ) (ha : |a| ≤ 1) :
    a ^ 2 = (∑ p ∈ Finset.range q, (heavyEntry p a) ^ 2) + (lightEntry q a) ^ 2 := by
  have h : ∀ q, (lightEntry 0 a) ^ 2 =
      (∑ p ∈ Finset.range q, (heavyEntry p a) ^ 2) + (lightEntry q a) ^ 2 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Finset.sum_range_succ]
      have hs := lightEntry_square_split q a
      linarith
  simpa [lightEntry, scaleCut, ha] using h q

end Komlos.KMFresh

-- END KMProof/RawScales.lean

-- BEGIN KMProof/NormalizedScales.lean

namespace Komlos.KMFresh

noncomputable def normalizedHeavy (p : ℕ) (a : ℝ) : ℝ := (2 : ℝ) ^ p * heavyEntry p a
noncomputable def normalizedLight (p : ℕ) (a : ℝ) : ℝ := (2 : ℝ) ^ p * lightEntry p a

lemma scale_inverse (p : ℕ) : (2 : ℝ) ^ p * scaleCut p = 1 := by
  unfold scaleCut
  rw [← mul_pow]
  norm_num

lemma heavyEntry_abs_le (p : ℕ) (a : ℝ) : |heavyEntry p a| ≤ scaleCut p := by
  unfold heavyEntry
  split_ifs with h
  · exact h.2
  · simpa using (scaleCut_pos p).le

lemma lightEntry_abs_le (p : ℕ) (a : ℝ) : |lightEntry p a| ≤ scaleCut p := by
  unfold lightEntry
  split_ifs with h
  · exact h
  · simpa using (scaleCut_pos p).le

lemma normalizedHeavy_abs_le (p : ℕ) (a : ℝ) : |normalizedHeavy p a| ≤ 1 := by
  unfold normalizedHeavy
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ p)]
  calc
    _ ≤ (2 : ℝ) ^ p * scaleCut p := mul_le_mul_of_nonneg_left (heavyEntry_abs_le p a) (by positivity)
    _ = 1 := scale_inverse p

lemma normalizedLight_abs_le (p : ℕ) (a : ℝ) : |normalizedLight p a| ≤ 1 := by
  unfold normalizedLight
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ p)]
  calc
    _ ≤ (2 : ℝ) ^ p * scaleCut p := mul_le_mul_of_nonneg_left (lightEntry_abs_le p a) (by positivity)
    _ = 1 := scale_inverse p

lemma normalizedHeavy_lower (p : ℕ) (a : ℝ) :
    normalizedHeavy p a = 0 ∨ (1 : ℝ) / 2 < |normalizedHeavy p a| := by
  unfold normalizedHeavy heavyEntry
  split_ifs with h
  · right
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ p)]
    have he : (2 : ℝ) ^ p * scaleCut (p + 1) = 1 / 2 := by
      rw [scaleCut_succ, ← mul_div_assoc, scale_inverse]
    rw [← he]
    exact mul_lt_mul_of_pos_left h.1 (by positivity)
  · left
    simp

lemma normalized_square_mass (p : ℕ) (a : ℝ) :
    ((2 : ℝ) ^ p * a) ^ 2 / (4 : ℝ) ^ p = a ^ 2 := by
  have hp : ((2 : ℝ) ^ p) ^ 2 = (4 : ℝ) ^ p := by
    calc
      _ = (2 : ℝ) ^ p * 2 ^ p := by ring
      _ = ((2 : ℝ) * 2) ^ p := (mul_pow _ _ _).symm
      _ = _ := by norm_num
  rw [mul_pow, hp]
  exact mul_div_cancel_left₀ _ (by positivity)

end Komlos.KMFresh

-- END KMProof/NormalizedScales.lean

-- BEGIN KMProof/ScaleFamily.lean

namespace Komlos.KMFresh

noncomputable def rawScale (q : ℕ) (p : Fin (q + 1)) (a : ℝ) : ℝ :=
  if p.val < q then heavyEntry p.val a else lightEntry q a
noncomputable def scaleEntry (q : ℕ) (p : Fin (q + 1)) (a : ℝ) : ℝ :=
  (2 : ℝ) ^ p.val * rawScale q p a

lemma sum_rawScale_apply (q : ℕ) (a : ℝ) (F : ℝ → ℝ) :
    (∑ p : Fin (q + 1), F (rawScale q p a)) =
      (∑ p ∈ Finset.range q, F (heavyEntry p a)) + F (lightEntry q a) := by
  rw [Fin.sum_univ_castSucc]
  simp only [rawScale, Fin.val_castSucc, Fin.val_last, Fin.is_lt, if_true,
    lt_self_iff_false, if_false]
  rw [Fin.sum_univ_eq_sum_range (fun p => F (heavyEntry p a))]

lemma scaleFamily_reconstruct (q : ℕ) (a : ℝ) (ha : |a| ≤ 1) :
    ∑ p : Fin (q + 1), scaleCut p.val * scaleEntry q p a = a := by
  have he : ∀ p : Fin (q + 1), scaleCut p.val * scaleEntry q p a = rawScale q p a := by
    intro p
    unfold scaleEntry
    rw [← mul_assoc, mul_comm (scaleCut p.val), scale_inverse, one_mul]
  simp only [he]
  rw [sum_rawScale_apply q a (fun x => x)]
  exact (scale_reconstruction q a ha).symm

lemma scaleFamily_square_reconstruct (q : ℕ) (a : ℝ) (ha : |a| ≤ 1) :
    ∑ p : Fin (q + 1), (scaleEntry q p a) ^ 2 / (4 : ℝ) ^ p.val = a ^ 2 := by
  simp only [scaleEntry, normalized_square_mass]
  rw [sum_rawScale_apply q a (fun x => x ^ 2)]
  exact (scale_square_reconstruction q a ha).symm

lemma scaleEntry_abs_le (q : ℕ) (p : Fin (q + 1)) (a : ℝ) :
    |scaleEntry q p a| ≤ 1 := by
  unfold scaleEntry rawScale
  split_ifs with h
  · exact normalizedHeavy_abs_le p.val a
  · have he : p.val = q := by omega
    rw [he]
    exact normalizedLight_abs_le q a

end Komlos.KMFresh

-- END KMProof/ScaleFamily.lean

-- BEGIN KMProof/ScaleEnergy.lean

namespace Komlos.KMFresh

lemma scale_column_energy {R C : Type*} [Fintype R] (A : R → C → ℝ)
    (q : ℕ) (j : C) (ha : ∀ i, |A i j| ≤ 1) :
    (∑ p : Fin (q + 1), ∑ i : R,
      (scaleEntry q p (A i j)) ^ 2 / (4 : ℝ) ^ p.val) = ∑ i : R, A i j ^ 2 := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => scaleFamily_square_reconstruct q (A i j) (ha i))

lemma scale_column_bound {R C : Type*} [Fintype R] (A : R → C → ℝ)
    (q : ℕ) (j : C) (ha : ∀ i, |A i j| ≤ 1) (hA : ∑ i, A i j ^ 2 ≤ 2) :
    (∑ p : Fin (q + 1), ∑ i : R,
      (scaleEntry q p (A i j)) ^ 2 / (4 : ℝ) ^ p.val) ≤ 2 := by
  rw [scale_column_energy A q j ha]
  exact hA

lemma all_scale_column_bound {R C : Type*} [Fintype R] (A : R → C → ℝ)
    (q : ℕ) (j : C) (ha : ∀ i, |A i j| ≤ 1) (hA : ∑ i, A i j ^ 2 ≤ 2) :
    (∑ z : Fin (q + 1) × R,
      (scaleEntry q z.1 (A z.2 j)) ^ 2 / (4 : ℝ) ^ z.1.val) ≤ 2 := by
  rw [Fintype.sum_prod_type]
  exact scale_column_bound A q j ha hA

lemma large_rows_count {R C : Type*} [Fintype R] [Fintype C]
    (A : R → C → ℝ) (q : ℕ) (alive : Finset C)
    (large : Finset (Fin (q + 1) × R))
    (ha : ∀ i j, |A i j| ≤ 1) (hA : ∀ j, ∑ i, A i j ^ 2 ≤ 2)
    (hl : ∀ z ∈ large, 64 * (4 : ℝ) ^ z.1.val ≤
      ∑ j ∈ alive, (scaleEntry q z.1 (A z.2 j)) ^ 2) :
    (large.card : ℝ) ≤ (alive.card : ℝ) / 32 := by
  classical
  have hc := weighted_row_count large alive
    (fun z j => (scaleEntry q z.1 (A z.2 j)) ^ 2 / (4 : ℝ) ^ z.1.val) 64 2
  have hr : ∀ z ∈ large, (64 : ℝ) ≤
      ∑ j ∈ alive, (scaleEntry q z.1 (A z.2 j)) ^ 2 / (4 : ℝ) ^ z.1.val := by
    intro z hz
    rw [← Finset.sum_div]
    exact (le_div_iff₀ (by positivity)).mpr (hl z hz)
  have hcol : ∀ j ∈ alive, (∑ z ∈ large,
      (scaleEntry q z.1 (A z.2 j)) ^ 2 / (4 : ℝ) ^ z.1.val) ≤ 2 := by
    intro j _
    apply le_trans _ (all_scale_column_bound A q j (fun i => ha i j) (hA j))
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ large)
    intro z _ _
    positivity
  have he := hc hr hcol
  linarith

end Komlos.KMFresh

-- END KMProof/ScaleEnergy.lean

-- BEGIN KMProof/ScaleColumnBounds.lean

namespace Komlos.KMFresh

lemma single_scale_column_bound {R C : Type*} [Fintype R] (A : R → C → ℝ)
    (q : ℕ) (p : Fin (q + 1)) (j : C)
    (ha : ∀ r, |A r j| ≤ 1) (hA : ∑ r, A r j ^ 2 ≤ 2) :
    (∑ r, (scaleEntry q p (A r j)) ^ 2) ≤ 2 * (4 : ℝ) ^ p.val := by
  have hsum := scale_column_bound A q j ha hA
  have hterm : (∑ r, (scaleEntry q p (A r j)) ^ 2 / (4 : ℝ) ^ p.val) ≤
      ∑ t : Fin (q + 1), ∑ r, (scaleEntry q t (A r j)) ^ 2 / (4 : ℝ) ^ t.val := by
    apply Finset.single_le_sum (f := fun t : Fin (q + 1) => ∑ r, (scaleEntry q t (A r j)) ^ 2 / (4 : ℝ) ^ t.val) (a := p)
    · intro t _
      apply Finset.sum_nonneg
      intro r _
      positivity
    · exact Finset.mem_univ p
  have he := hterm.trans hsum
  rw [← Finset.sum_div] at he
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ)^p.val)).mp he

end Komlos.KMFresh

-- END KMProof/ScaleColumnBounds.lean

-- BEGIN KMProof/ScaleStateCounts.lean

namespace Komlos.KMFresh

noncomputable def scaleRows {R : Type*} {n : ℕ} (A : R → Fin n → ℝ) (q : ℕ) :
    (Fin (q + 1) × R) → Fin n → ℝ := fun z i => scaleEntry q z.1 (A z.2 i)

noncomputable def scaleLocalState {R : Type*} [Fintype R] {n P : ℕ}
    (s : AdaptiveState (Fin P × R) n) (p : Fin P) : AdaptiveState R n := by
  classical
  exact ⟨s.x, Finset.univ.filter (fun r => (p,r) ∈ s.hit)⟩

noncomputable def scaleDangerous {R : Type*} [Fintype R] {n P : ℕ}
    (A : Fin P → R → Fin n → ℝ) (ρ : ℝ) (k μ : Fin P → ℝ)
    (s : AdaptiveState (Fin P × R) n) : Finset (Fin P × R) := by
  classical
  exact Finset.univ.filter (fun z => z.2 ∈ dangerousRows (A z.1) ρ (k z.1) (μ z.1) (scaleLocalState s z.1))

lemma scaleDangerous_card {R : Type*} [Fintype R] {n P : ℕ}
    (A : Fin P → R → Fin n → ℝ) (ρ : ℝ) (k μ : Fin P → ℝ)
    (s : AdaptiveState (Fin P × R) n) :
    (scaleDangerous A ρ k μ s).card =
      ∑ p, (dangerousRows (A p) ρ (k p) (μ p) (scaleLocalState s p)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, scaleDangerous, Finset.sum_filter,
    Fintype.sum_prod_type, Finset.sum_ite_mem_eq]

lemma scaleDangerous_count {R : Type*} [Fintype R] {n P : ℕ}
    (A : Fin P → R → Fin n → ℝ) (ρ : ℝ) (k μ : Fin P → ℝ)
    (s : AdaptiveState (Fin P × R) n) (hP : 0 < P) (hμ : ∀ p, 0 < μ p)
    (hc : ∀ p i, i ∈ aliveSet ρ s.x →
      ∑ r ∈ (scaleLocalState s p).hit, A p r i ^ 2 ≤ μ p / (64 * (P : ℝ))) :
    ((scaleDangerous A ρ k μ s).card : ℝ) ≤ (aliveSet ρ s.x).card / 64 := by
  rw [scaleDangerous_card, Nat.cast_sum]
  apply sum_dangerous_count hP _ (aliveSet ρ s.x).card
  intro p
  exact dangerousRows_count (A p) ρ (k p) (μ p) P (scaleLocalState s p) (hμ p) (hc p)

noncomputable def scaleLarge {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (x : Fin n → ℝ) : Finset (Fin (q + 1) × R) := by
  classical
  exact Finset.univ.filter (fun z => 64 * (4 : ℝ)^z.1.val < rowEnergy (scaleRows A q) ρ x z)

lemma scaleLarge_count {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (x : Fin n → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) :
    ((scaleLarge A q ρ x).card : ℝ) ≤ (aliveSet ρ x).card / 32 := by
  classical
  apply large_rows_count A q (aliveSet ρ x) (scaleLarge A q ρ x) ha hA
  intro z hz
  exact ((Finset.mem_filter.mp hz).2).le

end Komlos.KMFresh

-- END KMProof/ScaleStateCounts.lean

-- BEGIN KMProof/MatrixBasics.lean
noncomputable section
open Finset Matrix
namespace Komlos.KMFresh

lemma quadratic_nonneg_discriminant {a b c : ℝ} (ha : 0 ≤ a) (_hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ a * t^2 + 2*b*t + c) : b^2 ≤ a*c := by
  by_cases hz : a=0
  · subst a
    have hb : b=0 := by
      by_contra hn
      have ht := h (-(c+1)/(2*b))
      have he : 2*b*(-(c+1)/(2*b)) = -(c+1) := by field_simp
      simp only [zero_mul,zero_add] at ht
      rw [he] at ht
      linarith
    simp [hb]
  · have hp : 0<a := lt_of_le_of_ne ha (Ne.symm hz)
    have ht := h (-b/a)
    have he : a * (-b/a)^2 + 2*b*(-b/a)+c = (a*c-b^2)/a := by
      field_simp
      ring
    rw [he] at ht
    have hh := mul_nonneg ht ha
    rw [div_mul_cancel₀ _ hz] at hh
    linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def quadratic (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ x)

omit [DecidableEq ι] in
lemma psd_quadratic_nonneg {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (x : ι → ℝ) :
    0 ≤ quadratic A x := by
  simpa [quadratic] using hA.dotProduct_mulVec_nonneg x

omit [Fintype ι] [DecidableEq ι] in
lemma real_hermitian_apply {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (i j : ι) :
    A j i = A i j := by simpa using hA.apply i j

lemma quadratic_two_single (A : Matrix ι ι ℝ) (i j : ι) (t : ℝ) :
    quadratic A (t • Pi.single i 1 + Pi.single j 1) =
      A i i*t^2 + (A i j+A j i)*t + A j j := by
  simp [quadratic,Matrix.mulVec_add,Matrix.mulVec_smul,dotProduct_add,
    add_dotProduct,smul_dotProduct,dotProduct_smul]
  ring

lemma psd_entry_square {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) :
    (A i j)^2 ≤ A i i*A j j := by
  apply quadratic_nonneg_discriminant hA.diag_nonneg hA.diag_nonneg
  intro t
  have h := psd_quadratic_nonneg hA (t • Pi.single i 1 + Pi.single j 1)
  rw [quadratic_two_single,real_hermitian_apply hA.isHermitian i j] at h
  nlinarith

lemma psd_zero_diagonal_row {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {i : ι}
    (hi : A i i=0) (j : ι) : A i j=0 := by
  have h := psd_entry_square hA i j
  rw [hi,zero_mul] at h
  nlinarith [sq_nonneg (A i j)]

omit [DecidableEq ι] in
lemma psd_diagonal_le_trace {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i : ι) :
    A i i ≤ A.trace := by
  change A i i ≤ ∑ j, A j j
  exact Finset.single_le_sum (fun j _ => hA.diag_nonneg (i := j)) (Finset.mem_univ i)

end Komlos.KMFresh

-- END KMProof/MatrixBasics.lean

-- BEGIN KMProof/PsdNormalization.lean
noncomputable section
open Finset Matrix
namespace Komlos.KMFresh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagonalRoot (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => Real.sqrt (A i i))
def diagonalInvRoot (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => (Real.sqrt (A i i))⁻¹)
def normalizedPsd (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  diagonalInvRoot A * A * diagonalInvRoot A

lemma normalizedPsd_pos {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (normalizedPsd A).PosSemidef := by
  have h := hA.conjTranspose_mul_mul_same (diagonalInvRoot A)
  simpa [normalizedPsd,diagonalInvRoot] using h

lemma normalizedPsd_apply (A : Matrix ι ι ℝ) (i j : ι) :
    normalizedPsd A i j = (Real.sqrt (A i i))⁻¹*A i j*(Real.sqrt (A j j))⁻¹ := by
  simp [normalizedPsd,diagonalInvRoot,Matrix.diagonal_mul,Matrix.mul_diagonal]

lemma normalizedPsd_diagonal {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i : ι) :
    normalizedPsd A i i = if A i i=0 then 0 else 1 := by
  rw [normalizedPsd_apply]
  by_cases h : A i i=0
  · simp [h]
  · have hp : 0<A i i := lt_of_le_of_ne hA.diag_nonneg (Ne.symm h)
    have hs : Real.sqrt (A i i)≠0 := ne_of_gt (Real.sqrt_pos.mpr hp)
    rw [if_neg h]
    have he : (Real.sqrt (A i i))^2=A i i := Real.sq_sqrt hA.diag_nonneg
    field_simp
    nlinarith

lemma normalizedPsd_trace_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (normalizedPsd A).trace ≤ Fintype.card ι := by
  unfold Matrix.trace
  calc
    (∑i,normalizedPsd A i i) ≤ ∑_i : ι,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [normalizedPsd_diagonal hA]
      split_ifs <;> norm_num
    _ = Fintype.card ι := by simp

lemma normalizedPsd_reconstruct {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    diagonalRoot A * normalizedPsd A * diagonalRoot A = A := by
  ext i j
  simp only [diagonalRoot,Matrix.diagonal_mul,Matrix.mul_diagonal,normalizedPsd_apply]
  by_cases hi : A i i=0
  · rw [psd_zero_diagonal_row hA hi j]
    simp
  by_cases hj : A j j=0
  · have hz := psd_zero_diagonal_row hA hj i
    rw [real_hermitian_apply hA.isHermitian i j] at hz
    rw [hz]
    simp
  have hsi : Real.sqrt (A i i)≠0 :=
    ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne hA.diag_nonneg (Ne.symm hi)))
  have hsj : Real.sqrt (A j j)≠0 :=
    ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne hA.diag_nonneg (Ne.symm hj)))
  field_simp

end Komlos.KMFresh

-- END KMProof/PsdNormalization.lean

-- BEGIN KMProof/SpectralCut.lean
noncomputable section
open Finset
open scoped RealInnerProductSpace
namespace Komlos.KMFresh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma positive_spectral_quadratic {T : E →ₗ[ℝ] E} (hT : T.IsPositive) (x : E) :
    ⟪x,T x⟫ = ∑ i : Fin (Module.finrank ℝ E),
      hT.isSymmetric.eigenvalues rfl i *
        ⟪hT.isSymmetric.eigenvectorBasis rfl i,x⟫^2 := by
  let b := hT.isSymmetric.eigenvectorBasis rfl
  rw [←b.sum_inner_mul_inner x (T x)]
  apply Finset.sum_congr rfl
  intro i _
  have he : ⟪b i,T x⟫ = hT.isSymmetric.eigenvalues rfl i * ⟪b i,x⟫ := by
    rw [←hT.isSymmetric, hT.isSymmetric.apply_eigenvectorBasis]
    simp [b, real_inner_smul_left]
  rw [he,real_inner_comm x (b i)]
  ring

lemma positive_spectral_cut {T : E →ₗ[ℝ] E} (hT : T.IsPositive) (t : ℝ) :
    ∃ Z : Submodule ℝ E, ∃ b : ℕ,
      Module.finrank ℝ E ≤ Module.finrank ℝ Z+b ∧
      (b:ℝ)*t ≤ T.trace ℝ E ∧
      ∀x∈Z, ⟪x,T x⟫ ≤ t*‖x‖^2 := by
  let e := hT.isSymmetric.eigenvectorBasis rfl
  let lam := hT.isSymmetric.eigenvalues rfl
  let B : Finset (Fin (Module.finrank ℝ E)) := univ.filter (fun i => t<lam i)
  let F : E →ₗ[ℝ] ({i // i∈B} → ℝ) :=
    LinearMap.pi (fun i => (innerSL ℝ (e i.1)).toLinearMap)
  refine ⟨F.ker,B.card,?_,?_,?_⟩
  · have he := F.finrank_range_add_finrank_ker
    have hr : Module.finrank ℝ F.range≤B.card := by
      calc
        Module.finrank ℝ F.range ≤ Module.finrank ℝ ({i // i∈B} → ℝ) :=
          Submodule.finrank_le _
        _ = B.card := by simp
    omega
  · rw [hT.isSymmetric.trace_eq_sum_eigenvalues rfl]
    calc
      (B.card:ℝ)*t = ∑i∈B,t := by simp
      _ ≤ ∑i∈B,lam i := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Finset.mem_filter.mp hi).2.le
      _ ≤ ∑i,lam i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hT.nonneg_eigenvalues rfl i)
  · intro x hx
    have hx0 : ∀i∈B,⟪e i,x⟫=0 := by
      intro i hi
      have he := congrFun (LinearMap.mem_ker.mp hx) ⟨i,hi⟩
      exact he
    rw [positive_spectral_quadratic hT,←e.sum_sq_inner_right x,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i∈B
    · change lam i*⟪e i,x⟫^2≤t*⟪e i,x⟫^2
      rw [hx0 i hi]
      simp
    · have hl : lam i≤t := by simpa [B] using hi
      exact mul_le_mul_of_nonneg_right hl (sq_nonneg _)

end Komlos.KMFresh

-- END KMProof/SpectralCut.lean

-- BEGIN KMProof/SpectralPullback.lean
noncomputable section
open Finset
open scoped RealInnerProductSpace
namespace Komlos.KMFresh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma positive_spectral_pullback_cut
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V →ₗ[ℝ] E) {T : E →ₗ[ℝ] E} (hT : T.IsPositive) (t : ℝ) :
    ∃ Z : Submodule ℝ V, ∃ b : ℕ,
      Module.finrank ℝ V ≤ Module.finrank ℝ Z+b ∧
      (b:ℝ)*t ≤ T.trace ℝ E ∧
      ∀x∈Z, ⟪A x,T (A x)⟫ ≤ t*‖A x‖^2 := by
  let e := hT.isSymmetric.eigenvectorBasis rfl
  let lam := hT.isSymmetric.eigenvalues rfl
  let B : Finset (Fin (Module.finrank ℝ E)) := univ.filter (fun i => t<lam i)
  let F : V →ₗ[ℝ] ({i // i∈B} → ℝ) :=
    LinearMap.pi (fun i => ((innerSL ℝ (e i.1)).toLinearMap.comp A))
  refine ⟨F.ker,B.card,?_,?_,?_⟩
  · have he := F.finrank_range_add_finrank_ker
    have hr : Module.finrank ℝ F.range≤B.card := by
      calc
        Module.finrank ℝ F.range ≤ Module.finrank ℝ ({i // i∈B} → ℝ) :=
          Submodule.finrank_le _
        _ = B.card := by simp
    omega
  · rw [hT.isSymmetric.trace_eq_sum_eigenvalues rfl]
    calc
      (B.card:ℝ)*t = ∑i∈B,t := by simp
      _ ≤ ∑i∈B,lam i := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Finset.mem_filter.mp hi).2.le
      _ ≤ ∑i,lam i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hT.nonneg_eigenvalues rfl i)
  · intro x hx
    have hx0 : ∀i∈B,⟪e i,A x⟫=0 := by
      intro i hi
      have he := congrFun (LinearMap.mem_ker.mp hx) ⟨i,hi⟩
      exact he
    rw [positive_spectral_quadratic hT,←e.sum_sq_inner_right (A x),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i∈B
    · change lam i*⟪e i,A x⟫^2≤t*⟪e i,A x⟫^2
      rw [hx0 i hi]
      simp
    · have hl : lam i≤t := by simpa [B] using hi
      exact mul_le_mul_of_nonneg_right hl (sq_nonneg _)

end Komlos.KMFresh

-- END KMProof/SpectralPullback.lean

-- BEGIN KMProof/NormalizedCut.lean
noncomputable section
open Finset Matrix
open scoped RealInnerProductSpace
namespace Komlos.KMFresh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma euclidean_quadratic (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    ⟪x,A.toEuclideanLin x⟫=quadratic A (fun i => x i) := by
  simp only [quadratic,Matrix.toEuclideanLin,Matrix.toLpLin_apply,PiLp.inner_apply,
    RCLike.inner_apply,starRingEnd_apply,star_trivial,Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma euclidean_trace (A : Matrix ι ι ℝ) :
    A.toEuclideanLin.trace ℝ (EuclideanSpace ℝ ι)=A.trace := by
  simp only [Matrix.toEuclideanLin,Matrix.toLpLin_eq_toLin,Matrix.trace_toLin_eq]

lemma diagonalRoot_norm {G : Matrix ι ι ℝ} (hG : G.PosSemidef)
    (x : EuclideanSpace ℝ ι) :
    ‖(diagonalRoot G).toEuclideanLin x‖^2=∑i,G i i*(x i)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  change ((diagonalRoot G *ᵥ (fun j => x j)) i)^2=G i i*(x i)^2
  simp only [diagonalRoot,Matrix.mulVec_diagonal,mul_pow,Real.sq_sqrt hG.diag_nonneg]

lemma diagonalRoot_quadratic {G : Matrix ι ι ℝ} (hG : G.PosSemidef)
    (x : EuclideanSpace ℝ ι) :
    ⟪(diagonalRoot G).toEuclideanLin x,
      (normalizedPsd G).toEuclideanLin ((diagonalRoot G).toEuclideanLin x)⟫ =
      quadratic G (fun i => x i) := by
  rw [euclidean_quadratic]
  have he (i j : ι) : G i j = Real.sqrt (G i i)*normalizedPsd G i j*Real.sqrt (G j j) := by
    have hh := congrArg (fun A : Matrix ι ι ℝ => A i j) (normalizedPsd_reconstruct hG)
    simpa only [diagonalRoot,Matrix.diagonal_mul,Matrix.mul_diagonal] using hh.symm
  change quadratic (normalizedPsd G) ((diagonalRoot G) *ᵥ (fun i => x i))=_
  have hr : (diagonalRoot G) *ᵥ (fun i => x i) = (fun i => Real.sqrt (G i i)*x i) := by
    funext i
    simp [diagonalRoot,Matrix.mulVec_diagonal]
  rw [hr]
  unfold quadratic Matrix.mulVec dotProduct
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [he i j]
  ring

lemma normalized_multiplier_cut {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) (A : E →ₗ[ℝ] EuclideanSpace ℝ ι) (t : ℝ) :
    ∃Z:Submodule ℝ E,∃b:ℕ,
      Module.finrank ℝ E≤Module.finrank ℝ Z+b ∧
      (b:ℝ)*t≤Fintype.card ι ∧
      ∀x∈Z,quadratic G (fun i => A x i)≤t*(∑i,G i i*(A x i)^2) := by
  have hp : (normalizedPsd G).toEuclideanLin.IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr (normalizedPsd_pos hG)
  obtain ⟨Z,b,hb,ht,hq⟩ := positive_spectral_pullback_cut
    ((diagonalRoot G).toEuclideanLin.comp A) hp t
  refine ⟨Z,b,hb,?_,?_⟩
  · rw [euclidean_trace] at ht
    exact ht.trans (normalizedPsd_trace_le hG)
  · intro x hx
    have hh := hq x hx
    change ⟪(diagonalRoot G).toEuclideanLin (A x),
      (normalizedPsd G).toEuclideanLin ((diagonalRoot G).toEuclideanLin (A x))⟫ ≤
      t*‖(diagonalRoot G).toEuclideanLin (A x)‖^2 at hh
    simpa only [diagonalRoot_quadratic hG,diagonalRoot_norm hG] using hh
end Komlos.KMFresh

-- END KMProof/NormalizedCut.lean

-- BEGIN KMProof/SubspaceBudget.lean
noncomputable section
open Finset
namespace Komlos.KMFresh
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

lemma intersection_codimension (U V : Submodule ℝ E) {a b : ℕ}
    (hU : Module.finrank ℝ E ≤ Module.finrank ℝ U+a)
    (hV : Module.finrank ℝ E ≤ Module.finrank ℝ V+b) :
    Module.finrank ℝ E ≤ Module.finrank ℝ ↥(U⊓V)+(a+b) := by
  have he := Submodule.finrank_sup_add_finrank_inf_eq U V
  have hs := Submodule.finrank_le (U⊔V)
  omega

lemma finite_intersection_codimension {ι : Type*} (s : Finset ι)
    (Z : ι → Submodule ℝ E) (b : ι → ℕ)
    (hZ : ∀i∈s,Module.finrank ℝ E ≤ Module.finrank ℝ (Z i)+b i) :
    Module.finrank ℝ E ≤ Module.finrank ℝ ↥(s.inf Z)+∑i∈s,b i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change Module.finrank ℝ E ≤ Module.finrank ℝ ↥(⊤ : Submodule ℝ E)+0
    simp
  | @insert i s hi ih =>
    rw [Finset.inf_insert,Finset.sum_insert hi]
    exact intersection_codimension (Z i) (s.inf Z) (hZ i (by simp))
      (ih (fun j hj => hZ j (by simp [hj])))

end Komlos.KMFresh

-- END KMProof/SubspaceBudget.lean

-- BEGIN KMProof/GoodSubspace.lean
noncomputable section
open Finset
namespace Komlos.KMFresh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {J : Type*} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
lemma simultaneous_good_subspace (d : J → ℕ)
    (G : (j:J) → Matrix (Fin (d j)) (Fin (d j)) ℝ)
    (hG : ∀j,(G j).PosSemidef)
    (A : (j:J) → E →ₗ[ℝ] EuclideanSpace ℝ (Fin (d j)))
    (t : J → ℝ) (ht : ∀j,0<t j) (Z₀ : Submodule ℝ E) (τ : ℝ)
    (hbudget : τ+(∑j,(d j:ℝ)/t j)≤Module.finrank ℝ Z₀) :
    ∃Z:Submodule ℝ E,Z≤Z₀ ∧ τ≤Module.finrank ℝ Z ∧
      ∀j,∀x∈Z,quadratic (G j) (fun i => A j x i)≤
        t j*(∑i,G j i i*(A j x i)^2) := by
  classical
  choose V b hdim hcost hquad using
    (fun j => normalized_multiplier_cut (hG j) (A j) (t j))
  let V₀ : Submodule ℝ E := Finset.univ.inf V
  let Z := Z₀⊓V₀
  have hdV : Module.finrank ℝ E≤Module.finrank ℝ V₀+∑j,b j :=
    finite_intersection_codimension Finset.univ V b (fun j _ => hdim j)
  have hd : Module.finrank ℝ Z₀≤Module.finrank ℝ Z+∑j,b j := by
    have hi := Submodule.finrank_sup_add_finrank_inf_eq Z₀ V₀
    have hs := Submodule.finrank_le (Z₀⊔V₀)
    dsimp [Z]
    omega
  have hb : ∑j,(b j:ℝ)≤∑j,(d j:ℝ)/t j := by
    apply Finset.sum_le_sum
    intro j _
    apply (le_div_iff₀ (ht j)).mpr
    simpa using hcost j
  have hdR : (Module.finrank ℝ Z₀:ℝ)≤Module.finrank ℝ Z+∑j,(b j:ℝ) := by
    exact_mod_cast hd
  refine ⟨Z,inf_le_left,by linarith,?_⟩
  intro j x hx
  apply hquad j x
  have hv : x∈V₀ := hx.2
  exact (Finset.inf_le (Finset.mem_univ j) : V₀≤V j) hv
end Komlos.KMFresh

-- END KMProof/GoodSubspace.lean

-- BEGIN KMProof/MatrixDual.lean
noncomputable section
open Finset Matrix
namespace Komlos.KMFresh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixPair (A B : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

def symmetricDual (f : Matrix ι ι ℝ →ₗ[ℝ] ℝ) : Matrix ι ι ℝ :=
  fun i j => (f (Matrix.single i j 1)+f (Matrix.single j i 1))/2

omit [Fintype ι] in
lemma symmetricDual_hermitian (f : Matrix ι ι ℝ →ₗ[ℝ] ℝ) :
    (symmetricDual f).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial,symmetricDual]
  ring

lemma matrix_functional_expansion (f : Matrix ι ι ℝ →ₗ[ℝ] ℝ) (A : Matrix ι ι ℝ) :
    f A = ∑ i, ∑ j, A i j * f (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : Matrix.single i j (A i j) = (A i j) • Matrix.single i j (1:ℝ) := by
    ext a b
    simp [Matrix.single_apply]
  rw [he,map_smul]
  rfl

lemma symmetricDual_represents (f : Matrix ι ι ℝ →ₗ[ℝ] ℝ)
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : matrixPair (symmetricDual f) A=f A := by
  have hx : (∑ i, ∑ j, f (Matrix.single j i 1)*A i j) =
      ∑ i, ∑ j, f (Matrix.single i j 1)*A i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_hermitian_apply hA i j]
  unfold matrixPair symmetricDual
  simp only [add_div,add_mul,Finset.sum_add_distrib,div_mul_eq_mul_div,
    ←Finset.sum_div]
  rw [hx,matrix_functional_expansion f A]
  have he : (∑ i, ∑ j, f (Matrix.single i j 1)*A i j) =
      ∑ i, ∑ j, A i j*f (Matrix.single i j 1) := by
    simp only [mul_comm]
  rw [he]
  ring

omit [DecidableEq ι] in
lemma matrixPair_rankOne (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    matrixPair A (Matrix.vecMulVec x x)=quadratic A x := by
  unfold matrixPair quadratic Matrix.vecMulVec Matrix.mulVec dotProduct
  simp only [Finset.mul_sum,Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma positive_functional_psd (f : Matrix ι ι ℝ →ₗ[ℝ] ℝ)
    (hf : ∀ A, A.PosSemidef → 0≤f A) : (symmetricDual f).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (symmetricDual_hermitian f)
  intro x
  have hp : (Matrix.vecMulVec x x).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star x
  have h := hf _ hp
  rw [←symmetricDual_represents f hp.isHermitian,matrixPair_rankOne] at h
  simpa [quadratic] using h

end Komlos.KMFresh

-- END KMProof/MatrixDual.lean

-- BEGIN KMProof/FrameMatrix.lean
noncomputable section
open Finset Matrix
open scoped RealInnerProductSpace
namespace Komlos.KMFresh
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def frameMatrix (v : κ → EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  fun i j => ∑a,v a i*v a j

lemma frameMatrix_psd (v : κ → EuclideanSpace ℝ ι) : (frameMatrix v).PosSemidef := by
  have he : frameMatrix v = ∑a,vecMulVec (fun i => v a i) (fun i => v a i) := by
    ext i j
    simp [frameMatrix,vecMulVec,Matrix.sum_apply,Matrix.of_apply]
  rw [he]
  exact Matrix.posSemidef_sum Finset.univ (fun a _ => by
    simpa using Matrix.posSemidef_vecMulVec_self_star (fun i => v a i))

lemma frameMatrix_trace (v : κ → EuclideanSpace ℝ ι) (hv : ∀a,‖v a‖=1) :
    (frameMatrix v).trace = Fintype.card κ := by
  change (∑i,∑a,v a i*v a i) = (Fintype.card κ:ℝ)
  rw [Finset.sum_comm]
  have hh (a : κ) : ∑i,v a i*v a i=1 := by
    simpa [pow_two,hv a] using (EuclideanSpace.real_norm_sq_eq (v a)).symm
  simp_rw [hh]
  simp

lemma frameMatrix_diag_le (v : κ → EuclideanSpace ℝ ι) (hv : Orthonormal ℝ v) (i : ι) :
    frameMatrix v i i≤1 := by
  classical
  have hh := hv.sum_inner_products_le (s:=Finset.univ) (EuclideanSpace.single i (1:ℝ))
  simpa [frameMatrix,EuclideanSpace.inner_single_right,Real.norm_eq_abs,sq_abs,pow_two]
    using hh

lemma matrixPair_frame (A : Matrix ι ι ℝ) (v : κ → EuclideanSpace ℝ ι) :
    matrixPair A (frameMatrix v) = ∑a,quadratic A (fun i => v a i) := by
  unfold matrixPair frameMatrix quadratic
  simp only [Finset.mul_sum,Matrix.mulVec, dotProduct]
  trans ∑i,∑a,∑j,A i j*(v a i*v a j)
  · apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Komlos.KMFresh

-- END KMProof/FrameMatrix.lean

-- BEGIN KMProof/SubspaceFrame.lean
noncomputable section
open Finset Matrix
open scoped RealInnerProductSpace
namespace Komlos.KMFresh
variable {ι : Type*} [Fintype ι]

def subspaceFrame (Z : Submodule ℝ (EuclideanSpace ℝ ι)) :
    Fin (Module.finrank ℝ Z) → EuclideanSpace ℝ ι :=
  fun i => (stdOrthonormalBasis ℝ Z i : EuclideanSpace ℝ ι)

lemma subspaceFrame_mem (Z : Submodule ℝ (EuclideanSpace ℝ ι)) (i) :
    subspaceFrame Z i∈Z := (stdOrthonormalBasis ℝ Z i).property

lemma subspaceFrame_orthonormal (Z : Submodule ℝ (EuclideanSpace ℝ ι)) :
    Orthonormal ℝ (subspaceFrame Z) := by
  exact (stdOrthonormalBasis ℝ Z).orthonormal.comp_linearIsometry Z.subtypeₗᵢ

lemma subspaceFrame_norm (Z : Submodule ℝ (EuclideanSpace ℝ ι)) (i) :
    ‖subspaceFrame Z i‖=1 := (subspaceFrame_orthonormal Z).norm_eq_one i

lemma subspaceFrame_trace (Z : Submodule ℝ (EuclideanSpace ℝ ι)) :
    (frameMatrix (subspaceFrame Z)).trace = Module.finrank ℝ Z := by
  simpa using frameMatrix_trace (subspaceFrame Z) (subspaceFrame_norm Z)

lemma frameMatrix_annihilate {κ : Type*} [Fintype κ]
    (v : κ → EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι)
    (hx : ∀a,⟪v a,x⟫=0) : (frameMatrix v) *ᵥ (fun i => x i)=0 := by
  ext i
  change (∑j,(∑a,v a i*v a j)*x j)=0
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  have hh : ∑j,v a j*x j=0 := by
    simpa [PiLp.inner_apply,RCLike.inner_apply, mul_comm] using hx a
  calc
    _ = v a i*(∑j,v a j*x j) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ = 0 := by rw [hh,mul_zero]

end Komlos.KMFresh

-- END KMProof/SubspaceFrame.lean

-- BEGIN KMProof/FrameResidual.lean
noncomputable section
open Finset Matrix
namespace Komlos.KMFresh
variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

omit [Fintype ι] in
lemma frameMatrix_eq_sum (v : κ → EuclideanSpace ℝ ι) :
    frameMatrix v=∑a,vecMulVec (fun i => v a i) (fun i => v a i) := by
  ext i j
  simp [frameMatrix,vecMulVec,Matrix.sum_apply,Matrix.of_apply]

omit [Fintype μ] in
lemma frameMatrix_congruence [DecidableEq ι] (A : Matrix μ ι ℝ) (v : κ → EuclideanSpace ℝ ι) :
    A*frameMatrix v*A.transpose=frameMatrix (fun a => A.toEuclideanLin (v a)) := by
  classical
  rw [frameMatrix_eq_sum,frameMatrix_eq_sum]
  simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,
    Matrix.vecMul_transpose]
  apply Finset.sum_congr rfl
  intro a _
  rfl

lemma matrixPair_sub (G A B : Matrix ι ι ℝ) :
    matrixPair G (A-B)=matrixPair G A-matrixPair G B := by
  simp only [matrixPair,Matrix.sub_apply,mul_sub,Finset.sum_sub_distrib]
lemma matrixPair_smul (G A : Matrix ι ι ℝ) (t : ℝ) :
    matrixPair G (t • A)=t*matrixPair G A := by
  simp only [matrixPair,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma matrixPair_diag_frame [DecidableEq ι] (G : Matrix ι ι ℝ) (v : κ → EuclideanSpace ℝ ι) :
    matrixPair G (Matrix.diagonal (frameMatrix v).diag)=
      ∑a,∑i,G i i*(v a i)^2 := by
  have he : matrixPair G (Matrix.diagonal (frameMatrix v).diag)=∑i,G i i*frameMatrix v i i := by
    simp [matrixPair,Matrix.diagonal_apply,Matrix.diag]
  rw [he]
  simp only [frameMatrix,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma frame_residual_nonpos [DecidableEq ι] (G : Matrix ι ι ℝ)
    (v : κ → EuclideanSpace ℝ ι) (t : ℝ)
    (hv : ∀a,quadratic G (fun i => v a i)≤t*(∑i,G i i*(v a i)^2)) :
    matrixPair G (frameMatrix v-t • Matrix.diagonal (frameMatrix v).diag)≤0 := by
  rw [matrixPair_sub,matrixPair_smul,matrixPair_frame,matrixPair_diag_frame,Finset.mul_sum]
  exact sub_nonpos.mpr (Finset.sum_le_sum (fun a _ => hv a))
end Komlos.KMFresh

-- END KMProof/FrameResidual.lean

-- BEGIN KMProof/ScaledFrame.lean
noncomputable section
open Finset Matrix
open scoped RealInnerProductSpace
namespace Komlos.KMFresh
variable {ι : Type*} [Fintype ι]

def scaledFrame (Z : Submodule ℝ (EuclideanSpace ℝ ι)) (τ : ℝ) : Matrix ι ι ℝ :=
  (τ/(Module.finrank ℝ Z:ℝ)) • frameMatrix (subspaceFrame Z)

omit [Fintype ι] in
lemma scaledFrame_coefficient (Z : Submodule ℝ (EuclideanSpace ℝ ι))
    {τ : ℝ} (hτ : 0<τ) (hZ : τ≤Module.finrank ℝ Z) :
    0≤τ/(Module.finrank ℝ Z:ℝ) ∧ τ/(Module.finrank ℝ Z:ℝ)≤1 := by
  have hd : 0<(Module.finrank ℝ Z:ℝ) := hτ.trans_le hZ
  exact ⟨div_nonneg hτ.le hd.le,(div_le_one hd).mpr hZ⟩

lemma scaledFrame_psd (Z : Submodule ℝ (EuclideanSpace ℝ ι))
    {τ : ℝ} (hτ : 0<τ) (hZ : τ≤Module.finrank ℝ Z) :
    (scaledFrame Z τ).PosSemidef :=
  (frameMatrix_psd (subspaceFrame Z)).smul (scaledFrame_coefficient Z hτ hZ).1

lemma scaledFrame_trace (Z : Submodule ℝ (EuclideanSpace ℝ ι))
    {τ : ℝ} (hτ : 0<τ) (hZ : τ≤Module.finrank ℝ Z) :
    (scaledFrame Z τ).trace=τ := by
  have hd : (Module.finrank ℝ Z:ℝ)≠0 := ne_of_gt (hτ.trans_le hZ)
  simp only [scaledFrame,Matrix.trace_smul,smul_eq_mul,subspaceFrame_trace]
  exact div_mul_cancel₀ _ hd

lemma scaledFrame_diag (Z : Submodule ℝ (EuclideanSpace ℝ ι))
    {τ : ℝ} (hτ : 0<τ) (hZ : τ≤Module.finrank ℝ Z) (i : ι) :
    scaledFrame Z τ i i≤1 := by
  have hc := scaledFrame_coefficient Z hτ hZ
  have hd := frameMatrix_diag_le (subspaceFrame Z) (subspaceFrame_orthonormal Z) i
  change (τ/(Module.finrank ℝ Z:ℝ))*frameMatrix (subspaceFrame Z) i i≤1
  exact (mul_le_mul_of_nonneg_left hd hc.1).trans (by simpa using hc.2)

lemma scaledFrame_annihilate (Z Z₀ : Submodule ℝ (EuclideanSpace ℝ ι))
    (hZ : Z≤Z₀) (τ : ℝ) (x : EuclideanSpace ℝ ι) (hx : x∈Z₀ᗮ) :
    scaledFrame Z τ *ᵥ (fun i => x i)=0 := by
  have he := frameMatrix_annihilate (subspaceFrame Z) x
    (fun a => Z₀.inner_right_of_mem_orthogonal (hZ (subspaceFrame_mem Z a)) hx)
  simp only [scaledFrame,Matrix.smul_mulVec,he,smul_zero]
end Komlos.KMFresh

-- END KMProof/ScaledFrame.lean

-- BEGIN KMProof/AffineResidual.lean
noncomputable section
open Finset Matrix
namespace Komlos.KMFresh
variable {ι μ : Type*} [Fintype ι] [Fintype μ] [DecidableEq μ]

def affineResidual (A : Matrix μ ι ℝ) (t : ℝ) (X : Matrix ι ι ℝ) : Matrix μ μ ℝ :=
  A*X*A.transpose-t • Matrix.diagonal (A*X*A.transpose).diag

omit [Fintype μ] in
lemma affineResidual_smul (A : Matrix μ ι ℝ) (t c : ℝ) (X : Matrix ι ι ℝ) :
    affineResidual A t (c • X)=c • affineResidual A t X := by
  unfold affineResidual
  simp only [Matrix.mul_smul,Matrix.smul_mul]
  have hd : Matrix.diagonal (c • (A*X*A.transpose)).diag =
      c • Matrix.diagonal (A*X*A.transpose).diag := by
    ext i j
    simp [Matrix.diagonal_apply,Matrix.diag]
  rw [hd]
  module

omit [Fintype μ] in
lemma affineResidual_add (A : Matrix μ ι ℝ) (t : ℝ) (X Y : Matrix ι ι ℝ) :
    affineResidual A t (X+Y)=affineResidual A t X+affineResidual A t Y := by
  unfold affineResidual
  ext i j
  by_cases hij:i=j <;> simp [Matrix.mul_add,Matrix.add_mul,Matrix.diag,hij]
  ring

def affineResidualMap (A : Matrix μ ι ℝ) (t : ℝ) : Matrix ι ι ℝ →ₗ[ℝ] Matrix μ μ ℝ where
  toFun := affineResidual A t
  map_add' := affineResidual_add A t
  map_smul' c X := affineResidual_smul A t c X

omit [Fintype μ] in
lemma affineResidual_hermitian (A : Matrix μ ι ℝ) (t : ℝ)
    {X : Matrix ι ι ℝ} (hX : X.IsHermitian) : (affineResidual A t X).IsHermitian := by
  have he : (A*X*A.transpose).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose A hX
  exact he.sub ((Matrix.isHermitian_diagonal _).smul (IsSelfAdjoint.all t))

lemma scaledFrame_residual_nonpos [DecidableEq ι]
    (A : Matrix μ ι ℝ) (G : Matrix μ μ ℝ) (t : ℝ)
    (Z : Submodule ℝ (EuclideanSpace ℝ ι)) {τ : ℝ}
    (hτ : 0<τ) (hZ : τ≤Module.finrank ℝ Z)
    (hq : ∀x∈Z,quadratic G (fun i => A.toEuclideanLin x i)≤
      t*(∑i,G i i*(A.toEuclideanLin x i)^2)) :
    matrixPair G (affineResidual A t (scaledFrame Z τ))≤0 := by
  rw [scaledFrame,affineResidual_smul,matrixPair_smul]
  apply mul_nonpos_of_nonneg_of_nonpos (scaledFrame_coefficient Z hτ hZ).1
  unfold affineResidual
  rw [frameMatrix_congruence]
  exact frame_residual_nonpos G (fun a => A.toEuclideanLin (subspaceFrame Z a)) t
    (fun a => hq _ (subspaceFrame_mem Z a))
end Komlos.KMFresh

-- END KMProof/AffineResidual.lean

-- BEGIN KMProof/MultiplierWitness.lean
noncomputable section
open Finset Matrix
namespace Komlos.KMFresh
variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

omit [DecidableEq J] in
lemma multiplier_witness (d : J → ℕ)
    (A : (j:J) → Matrix (Fin (d j)) (Fin n) ℝ)
    (G : (j:J) → Matrix (Fin (d j)) (Fin (d j)) ℝ)
    (hG : ∀j,(G j).PosSemidef) (t : J → ℝ) (ht : ∀j,0<t j)
    (Z₀ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {τ : ℝ} (hτ : 0<τ)
    (hbudget : τ+(∑j,(d j:ℝ)/t j)≤Module.finrank ℝ Z₀) :
    ∃X:Matrix (Fin n) (Fin n) ℝ,X.PosSemidef ∧ X.trace=τ ∧
      (∀i,X i i≤1) ∧
      (∀x:EuclideanSpace ℝ (Fin n),x∈Z₀ᗮ → X *ᵥ (fun i => x i)=0) ∧
      ∀j,matrixPair (G j) (affineResidual (A j) (t j) X)≤0 := by
  obtain ⟨Z,hZZ,hZ,hq⟩ := simultaneous_good_subspace d G hG
    (fun j => (A j).toEuclideanLin) t ht Z₀ τ hbudget
  refine ⟨scaledFrame Z τ,scaledFrame_psd Z hτ hZ,scaledFrame_trace Z hτ hZ,
    scaledFrame_diag Z hτ hZ,?_,?_⟩
  · intro x hx
    exact scaledFrame_annihilate Z Z₀ hZZ τ x hx
  · intro j
    exact scaledFrame_residual_nonpos (A j) (G j) (t j) Z hτ hZ (hq j)
end Komlos.KMFresh

-- END KMProof/MultiplierWitness.lean

-- BEGIN KMProof/MatrixFamilyDual.lean
noncomputable section
open Finset Matrix
namespace Komlos.KMFresh
variable {J : Type*} [Fintype J] [DecidableEq J] (d : J → ℕ)

abbrev MatrixFamily := (j : J) → Matrix (Fin (d j)) (Fin (d j)) ℝ

def familyComponent (f : MatrixFamily d →ₗ[ℝ] ℝ) (j : J) :
    Matrix (Fin (d j)) (Fin (d j)) ℝ →ₗ[ℝ] ℝ :=
  f.comp (LinearMap.single ℝ (fun j => Matrix (Fin (d j)) (Fin (d j)) ℝ) j)

lemma family_functional_expansion (f : MatrixFamily d →ₗ[ℝ] ℝ) (A : MatrixFamily d) :
    f A=∑j,familyComponent d f j (A j) := by
  conv_lhs => rw [←LinearMap.sum_single_apply (fun j => Matrix (Fin (d j)) (Fin (d j)) ℝ) A]
  simp only [map_sum,familyComponent,LinearMap.comp_apply,LinearMap.single_apply]

omit [Fintype J] in
lemma family_component_positive (f : MatrixFamily d →ₗ[ℝ] ℝ)
    (hf : ∀A:MatrixFamily d,(∀j,(A j).PosSemidef) → 0≤f A) (j : J) :
    ∀A,A.PosSemidef → 0≤familyComponent d f j A := by
  intro A hA
  change 0≤f (Pi.single j A)
  apply hf
  intro k
  by_cases hk:k=j
  · subst k
    simpa [LinearMap.single_apply] using hA
  · simpa only [Pi.single_eq_of_ne hk] using (Matrix.PosSemidef.zero : (0 : Matrix (Fin (d k)) (Fin (d k)) ℝ).PosSemidef)

omit [Fintype J] in
lemma family_dual_psd (f : MatrixFamily d →ₗ[ℝ] ℝ)
    (hf : ∀A:MatrixFamily d,(∀j,(A j).PosSemidef) → 0≤f A) (j : J) :
    (symmetricDual (familyComponent d f j)).PosSemidef :=
  positive_functional_psd _ (family_component_positive d f hf j)

lemma family_dual_represents (f : MatrixFamily d →ₗ[ℝ] ℝ) (A : MatrixFamily d)
    (hA : ∀j,(A j).IsHermitian) :
    f A=∑j,matrixPair (symmetricDual (familyComponent d f j)) (A j) := by
  rw [family_functional_expansion d f A]
  apply Finset.sum_congr rfl
  intro j _
  exact (symmetricDual_represents _ (hA j)).symm
end Komlos.KMFresh

-- END KMProof/MatrixFamilyDual.lean

-- BEGIN KMProof/SdpMap.lean
noncomputable section
open Finset Matrix
namespace Komlos.KMFresh
variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

def sdpDimension (d : J → ℕ) : Option J → ℕ
  | none => n
  | some j => d j

def diagonalMap : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun X := Matrix.diagonal X.diag
  map_add' X Y := by ext i j; by_cases h:i=j <;> simp [Matrix.diag,h]
  map_smul' c X := by ext i j; by_cases h:i=j <;> simp [Matrix.diag,h]

def sdpCoordinateMap (d : J → ℕ) (A : (j:J) → Matrix (Fin (d j)) (Fin n) ℝ) (t : J → ℝ) :
    (j:Option J) → Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
      Matrix (Fin (sdpDimension (n:=n) d j)) (Fin (sdpDimension (n:=n) d j)) ℝ
  | none => diagonalMap
  | some j => affineResidualMap (A j) (t j)

def sdpMap (d : J → ℕ) (A : (j:J) → Matrix (Fin (d j)) (Fin n) ℝ) (t : J → ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] MatrixFamily (sdpDimension (n:=n) d) :=
  LinearMap.pi (sdpCoordinateMap d A t)

def sdpTarget (d : J → ℕ) : MatrixFamily (sdpDimension (n:=n) d)
  | none => 1
  | some _ => 0

omit [Fintype J] [DecidableEq J] in
lemma sdpMap_continuous (d : J → ℕ) (A : (j:J) → Matrix (Fin (d j)) (Fin n) ℝ) (t : J → ℝ) :
    Continuous (sdpMap d A t) := by
  apply continuous_pi
  intro j
  cases j with
  | none => change Continuous (fun X : Matrix (Fin n) (Fin n) ℝ => Matrix.diagonal X.diag); fun_prop
  | some j =>
    change Continuous (fun X : Matrix (Fin n) (Fin n) ℝ => affineResidual (A j) (t j) X)
    unfold affineResidual
    fun_prop

omit [Fintype J] [DecidableEq J] in
lemma sdpMap_hermitian (d : J → ℕ) (A : (j:J) → Matrix (Fin (d j)) (Fin n) ℝ) (t : J → ℝ)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) (j : Option J) :
    (sdpMap d A t X j).IsHermitian := by
  cases j with
  | none => exact Matrix.isHermitian_diagonal _
  | some j => exact affineResidual_hermitian (A j) (t j) hX
end Komlos.KMFresh

-- END KMProof/SdpMap.lean

-- BEGIN KMProof/PsdCompact.lean
noncomputable section
open Finset Matrix
namespace Komlos.KMFresh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma continuous_quadratic (x : ι → ℝ) :
    Continuous (fun A : Matrix ι ι ℝ => quadratic A x) := by
  unfold quadratic Matrix.mulVec dotProduct
  fun_prop

omit [DecidableEq ι] in
lemma isClosed_psd : IsClosed {A : Matrix ι ι ℝ | A.PosSemidef} := by
  have he : {A : Matrix ι ι ℝ | A.PosSemidef} =
      {A | Aᴴ=A} ∩ {A | ∀ x : ι → ℝ, 0 ≤ quadratic A x} := by
    ext A
    simp only [Set.mem_ofPred_eq,Set.mem_inter_iff]
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    simp [Matrix.IsHermitian,quadratic]
  rw [he]
  apply (isClosed_eq (by fun_prop) continuous_id).inter
  simpa only [Set.ofPred_forall] using
    (isClosed_iInter fun x : ι → ℝ =>
      isClosed_le (continuous_const : Continuous (fun _ : Matrix ι ι ℝ => (0:ℝ)))
        (continuous_quadratic x))

omit [Fintype ι] [DecidableEq ι] in
lemma convex_psd : Convex ℝ {A : Matrix ι ι ℝ | A.PosSemidef} := by
  intro A hA B hB a b ha hb _
  exact (hA.smul ha).add (hB.smul hb)

lemma psd_entry_abs_le_trace {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) :
    |A i j| ≤ A.trace := by
  have h0 := hA.trace_nonneg
  have hi := psd_diagonal_le_trace hA i
  have hj := psd_diagonal_le_trace hA j
  have hm := mul_le_mul hi hj hA.diag_nonneg h0
  have hs := psd_entry_square hA i j
  have ha := abs_nonneg (A i j)
  have he := sq_abs (A i j)
  nlinarith

lemma isCompact_psd_trace (T : ℝ) :
    IsCompact {A : Matrix ι ι ℝ | A.PosSemidef ∧ A.trace=T} := by
  have hc : IsClosed {A : Matrix ι ι ℝ | A.PosSemidef ∧ A.trace=T} :=
    isClosed_psd.inter (isClosed_eq (by unfold Matrix.trace; fun_prop) continuous_const)
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ _ : ι => -|T|) (fun _ _ : ι => |T|))).of_isClosed_subset hc
  intro A hA
  constructor
  · intro i j
    have h := psd_entry_abs_le_trace hA.1 i j
    rw [hA.2] at h
    exact (neg_le_neg (le_abs_self T)).trans ((abs_le.mp h).1)
  · intro i j
    have h := psd_entry_abs_le_trace hA.1 i j
    rw [hA.2] at h
    exact (abs_le.mp h).2.trans (le_abs_self T)

lemma isCompact_psd_trace_annihilate (T : ℝ) (W : Set (ι → ℝ)) :
    IsCompact {A : Matrix ι ι ℝ | A.PosSemidef ∧ A.trace=T ∧ ∀x∈W,A *ᵥ x=0} := by
  have hc : IsClosed {A : Matrix ι ι ℝ | ∀x∈W,A *ᵥ x=0} := by
    simpa only [Set.ofPred_forall] using
      (isClosed_biInter fun (x : ι → ℝ) (_hx : x∈W) =>
        isClosed_eq (by change Continuous (fun A : Matrix ι ι ℝ => A *ᵥ x);
                        unfold Matrix.mulVec dotProduct; fun_prop)
          (continuous_const : Continuous (fun _ : Matrix ι ι ℝ => (0 : ι → ℝ))))
  have he : {A : Matrix ι ι ℝ | A.PosSemidef ∧ A.trace=T ∧ ∀x∈W,A *ᵥ x=0} =
      {A | A.PosSemidef ∧ A.trace=T} ∩ {A | ∀x∈W,A *ᵥ x=0} := by
    ext A; simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,and_assoc]
  rw [he]
  exact (isCompact_psd_trace T).inter_right hc

end Komlos.KMFresh

-- END KMProof/PsdCompact.lean

-- BEGIN KMProof/PsdDomain.lean
noncomputable section
open Matrix
namespace Komlos.KMFresh
variable {n : ℕ}

def psdDomain (τ : ℝ) (Z₀ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.PosSemidef ∧ X.trace=τ ∧
    ∀x:EuclideanSpace ℝ (Fin n),x∈Z₀ᗮ → X *ᵥ (fun i => x i)=0}

lemma psdDomain_compact (τ : ℝ) (Z₀ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    IsCompact (psdDomain τ Z₀) := by
  let W : Set (Fin n → ℝ) := {x | WithLp.toLp 2 x∈Z₀ᗮ}
  have he : psdDomain τ Z₀={X | X.PosSemidef ∧ X.trace=τ ∧ ∀x∈W,X *ᵥ x=0} := by
    ext X
    simp only [psdDomain,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1,h2,h3⟩
      exact ⟨h1,h2,fun x hx => h3 (WithLp.toLp 2 x) hx⟩
    · rintro ⟨h1,h2,h3⟩
      exact ⟨h1,h2,fun x hx => h3 (fun i => x i) hx⟩
  rw [he]
  exact isCompact_psd_trace_annihilate τ W

lemma psdDomain_convex (τ : ℝ) (Z₀ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Convex ℝ (psdDomain τ Z₀) := by
  intro X hX Y hY a b ha hb hab
  refine ⟨(hX.1.smul ha).add (hY.1.smul hb),?_,?_⟩
  · simp only [Matrix.trace_add,Matrix.trace_smul,smul_eq_mul,hX.2.1,hY.2.1]
    calc
      a*τ+b*τ=(a+b)*τ := by ring
      _ = τ := by rw [hab,one_mul]
  · intro x hx
    simp only [Matrix.add_mulVec,Matrix.smul_mulVec,hX.2.2 x hx,hY.2.2 x hx,smul_zero,add_zero]
end Komlos.KMFresh

-- END KMProof/PsdDomain.lean

-- BEGIN KMProof/SdpWitness.lean
noncomputable section
open Finset Matrix
namespace Komlos.KMFresh
variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

lemma diagonal_pair_bound {G X : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosSemidef) (hX : ∀i,X i i≤1) :
    matrixPair G (Matrix.diagonal X.diag)≤ matrixPair G 1 := by
  have he : matrixPair G (Matrix.diagonal X.diag)=∑i,G i i*X i i := by
    simp [matrixPair,Matrix.diagonal_apply,Matrix.diag]
  have hf : matrixPair G 1=∑i,G i i := by
    simp [matrixPair,Matrix.one_apply]
  rw [he,hf]
  apply Finset.sum_le_sum
  intro i _
  simpa using mul_le_mul_of_nonneg_left (hX i) (hG.diag_nonneg (i:=i))

omit [DecidableEq J] in
lemma sdp_dual_witness (d : J → ℕ)
    (A : (j:J) → Matrix (Fin (d j)) (Fin n) ℝ)
    (t : J → ℝ) (ht : ∀j,0<t j)
    (Z₀ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {τ : ℝ} (hτ : 0<τ)
    (hbudget : τ+(∑j,(d j:ℝ)/t j)≤Module.finrank ℝ Z₀)
    (G : MatrixFamily (sdpDimension (n:=n) d)) (hG : ∀j,(G j).PosSemidef) :
    ∃Y∈(sdpMap d A t) '' (psdDomain τ Z₀),
      (∑j,matrixPair (G j) (Y j))≤∑j,matrixPair (G j) (sdpTarget (n:=n) d j) := by
  obtain ⟨X,hX,htr,hdiag,hann,hres⟩ := multiplier_witness d A
    (fun j => G (some j)) (fun j => hG (some j)) t ht Z₀ hτ hbudget
  refine ⟨sdpMap d A t X,⟨X,⟨hX,htr,hann⟩,rfl⟩,?_⟩
  rw [Fintype.sum_option,Fintype.sum_option]
  change matrixPair (G none) (Matrix.diagonal X.diag)+
    (∑j,matrixPair (G (some j)) (affineResidual (A j) (t j) X)) ≤
    matrixPair (G none) 1+(∑j,matrixPair (G (some j)) 0)
  have hsum : (∑j,matrixPair (G (some j)) (affineResidual (A j) (t j) X))≤0 :=
    Finset.sum_nonpos (fun j _ => hres j)
  have hz : (∑j,matrixPair (G (some j)) 0)=0 := by simp [matrixPair]
  rw [hz,add_zero]
  have hd := diagonal_pair_bound (hG none) hdiag
  have hh := add_le_add hd hsum
  simp only [add_zero] at hh
  convert hh using 1 <;> rfl
end Komlos.KMFresh

-- END KMProof/SdpWitness.lean

-- BEGIN KMProof/CompactDuality.lean
noncomputable section
namespace Komlos.KMFresh
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

lemma compact_dual_feasible (K T C : Set E) (b : E)
    (hK : Convex ℝ K) (hcK : IsCompact K)
    (hT : Convex ℝ T) (hcT : IsClosed T) (hb : b∈T)
    (hray : ∀c∈C,∀r:ℝ,0≤r → b-r•c∈T)
    (hdual : ∀f : StrongDual ℝ E,(∀c∈C,0≤f c) → ∃x∈K,f x≤f b) :
    ∃x∈K,x∈T := by
  by_contra hn
  have hd : Disjoint K T := by
    rw [Set.disjoint_left]
    intro x hx ht
    exact hn ⟨x,hx,ht⟩
  obtain ⟨f,u,v,hfK,huv,hfT⟩ :=
    geometric_hahn_banach_compact_closed hK hcK hT hcT hd
  have hfc : ∀c∈C,f c≤0 := by
    intro c hc
    by_contra hh
    have hp : 0<f c := lt_of_not_ge hh
    have hbv := hfT b hb
    let r := (f b-v+1)/(f c)
    have hr : 0≤r := div_nonneg (by linarith) hp.le
    have hs := hfT (b-r•c) (hray c hc r hr)
    rw [map_sub,map_smul,smul_eq_mul] at hs
    have he : r*f c=f b-v+1 := by dsimp [r]; exact div_mul_cancel₀ _ hp.ne'
    linarith
  obtain ⟨x,hx,hfx⟩ := hdual (-f) (fun c hc => by simpa using neg_nonneg.mpr (hfc c hc))
  have hk := hfK x hx
  have ht := hfT b hb
  change -f x≤-f b at hfx
  linarith

end Komlos.KMFresh

-- END KMProof/CompactDuality.lean

-- BEGIN KMProof/FamilyFeasibility.lean
noncomputable section
open Finset Matrix
namespace Komlos.KMFresh
variable {J : Type*} [Fintype J] [DecidableEq J] (d : J → ℕ)

omit [Fintype J] [DecidableEq J] in
lemma family_psd_target_closed (B : MatrixFamily d) :
    IsClosed {Y : MatrixFamily d | ∀j,(B j-Y j).PosSemidef} := by
  simpa only [Set.ofPred_forall,Set.preimage_ofPred_eq] using (isClosed_iInter fun j : J =>
    (isClosed_psd (ι:=Fin (d j))).preimage
      (by fun_prop : Continuous (fun Y : MatrixFamily d => B j-Y j)))

omit [Fintype J] [DecidableEq J] in
lemma family_psd_target_convex (B : MatrixFamily d) :
    Convex ℝ {Y : MatrixFamily d | ∀j,(B j-Y j).PosSemidef} := by
  intro X hX Y hY a b ha hb hab j
  have he : B j-(a • X+b • Y) j = a • (B j-X j)+b • (B j-Y j) := by
    ext r s
    simp only [Pi.add_apply,Pi.smul_apply,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    have hh := congrArg (fun t : ℝ => t*B j r s) hab
    nlinarith
  rw [he]
  exact ((hX j).smul ha).add ((hY j).smul hb)

lemma family_dual_test (K : Set (MatrixFamily d)) (B : MatrixFamily d)
    (hB : ∀j,(B j).IsHermitian) (hK : ∀x∈K,∀j,(x j).IsHermitian)
    (htest : ∀G:MatrixFamily d,(∀j,(G j).PosSemidef) →
      ∃x∈K,(∑j,matrixPair (G j) (x j))≤∑j,matrixPair (G j) (B j))
    (f : MatrixFamily d →ₗ[ℝ] ℝ)
    (hf : ∀G:MatrixFamily d,(∀j,(G j).PosSemidef) → 0≤f G) :
    ∃x∈K,f x≤f B := by
  obtain ⟨x,hx,hh⟩ := htest (fun j => symmetricDual (familyComponent d f j))
    (family_dual_psd d f hf)
  refine ⟨x,hx,?_⟩
  rw [family_dual_represents d f x (hK x hx),family_dual_represents d f B hB]
  exact hh

lemma matrix_family_feasible (K : Set (MatrixFamily d))
    (hK : Convex ℝ K) (hcK : IsCompact K) (B : MatrixFamily d)
    (hB : ∀j,(B j).IsHermitian) (hHerm : ∀x∈K,∀j,(x j).IsHermitian)
    (htest : ∀G:MatrixFamily d,(∀j,(G j).PosSemidef) →
      ∃x∈K,(∑j,matrixPair (G j) (x j))≤∑j,matrixPair (G j) (B j)) :
    ∃x∈K,∀j,(B j-x j).PosSemidef := by
  let (j : J) : LocallyConvexSpace ℝ (Matrix (Fin (d j)) (Fin (d j)) ℝ) := by
    change LocallyConvexSpace ℝ (Fin (d j) → Fin (d j) → ℝ)
    infer_instance
  let C : Set (MatrixFamily d) := {G | ∀j,(G j).PosSemidef}
  let T : Set (MatrixFamily d) := {Y | ∀j,(B j-Y j).PosSemidef}
  have hb : B∈T := by intro j; simp only [sub_self]; exact Matrix.PosSemidef.zero
  have hray : ∀c∈C,∀r:ℝ,0≤r → B-r•c∈T := by
    intro c hc r hr j
    simpa only [Pi.sub_apply,Pi.smul_apply,sub_sub_cancel] using (hc j).smul hr
  exact compact_dual_feasible K T C B hK hcK
    (family_psd_target_convex d B) (family_psd_target_closed d B) hb hray
    (fun f hf => family_dual_test d K B hB hHerm htest f.toLinearMap hf)
end Komlos.KMFresh

-- END KMProof/FamilyFeasibility.lean

-- BEGIN KMProof/AffineSdp.lean
noncomputable section
open Finset Matrix
namespace Komlos.KMFresh
variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

lemma affine_sdp_exists (d : J → ℕ)
    (A : (j:J) → Matrix (Fin (d j)) (Fin n) ℝ)
    (t : J → ℝ) (ht : ∀j,0<t j)
    (Z₀ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {τ : ℝ} (hτ : 0<τ)
    (hbudget : τ+(∑j,(d j:ℝ)/t j)≤Module.finrank ℝ Z₀) :
    ∃X:Matrix (Fin n) (Fin n) ℝ,X.PosSemidef ∧ X.trace=τ ∧
      (∀i,X i i≤1) ∧
      (∀x:EuclideanSpace ℝ (Fin n),x∈Z₀ᗮ → X *ᵥ (fun i => x i)=0) ∧
      ∀j,(t j • Matrix.diagonal (A j*X*(A j).transpose).diag-
        A j*X*(A j).transpose).PosSemidef := by
  let K := (sdpMap d A t) '' (psdDomain τ Z₀)
  have hK : Convex ℝ K := (psdDomain_convex τ Z₀).linear_image (sdpMap d A t)
  have hcK : IsCompact K := (psdDomain_compact τ Z₀).image (sdpMap_continuous d A t)
  have hB : ∀j,(sdpTarget (n:=n) d j).IsHermitian := by
    intro j
    cases j <;> simp only [sdpTarget]
    · exact Matrix.isHermitian_one
    · exact Matrix.isHermitian_zero
  have hHerm : ∀Y∈K,∀j,(Y j).IsHermitian := by
    rintro Y ⟨X,hX,rfl⟩ j
    exact sdpMap_hermitian d A t hX.1.isHermitian j
  obtain ⟨Y,hY,hout⟩ := matrix_family_feasible (sdpDimension (n:=n) d) K hK hcK
    (sdpTarget (n:=n) d) hB hHerm (sdp_dual_witness d A t ht Z₀ hτ hbudget)
  obtain ⟨X,hX,rfl⟩ := hY
  refine ⟨X,hX.1,hX.2.1,?_,hX.2.2,?_⟩
  · intro i
    have hh := (hout none).diag_nonneg (i:=i)
    change 0≤(1-Matrix.diagonal X.diag) i i at hh
    simpa using hh
  · intro j
    have hh := hout (some j)
    change (0-affineResidual (A j) (t j) X).PosSemidef at hh
    have he : 0-affineResidual (A j) (t j) X=
        t j • Matrix.diagonal (A j*X*(A j).transpose).diag-A j*X*(A j).transpose := by
      unfold affineResidual
      abel
    have hh' : (0-affineResidual (A j) (t j) X).PosSemidef := by
      convert hh using 1
      rfl
    rw [he] at hh'
    exact hh'
end Komlos.KMFresh

-- END KMProof/AffineSdp.lean

-- BEGIN KMProof/SdpBudgetAlgebra.lean

namespace Komlos.KMFresh

lemma affine_dimension_ratio (d h k μ P : ℝ)
    (hk : 0 < k) (_hμ : 0 < μ) (hP : 0 < P)
    (hd : d * μ ≤ 2 * k * h) :
    d / (64 * P * k / μ) ≤ h / (32 * P) := by
  rw [div_div_eq_mul_div]
  apply (div_le_div_iff₀ (by positivity : 0 < 64 * P * k) (by positivity : 0 < 32 * P)).mpr
  have hm := mul_le_mul_of_nonneg_right hd (show 0 ≤ 32 * P by positivity)
  nlinarith

lemma affine_total_ratio {P : ℕ} (hP : 0 < P) (d : Fin P → ℕ)
    (h : ℝ) (k μ : Fin P → ℝ) (hk : ∀ p, 0 < k p) (hμ : ∀ p, 0 < μ p)
    (hd : ∀ p, (d p : ℝ) * μ p ≤ 2 * k p * h) :
    (∑ p, (d p : ℝ) / (64 * (P : ℝ) * k p / μ p)) ≤ h / 32 := by
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  calc
    _ ≤ ∑ _p : Fin P, h / (32 * (P : ℝ)) := by
      apply Finset.sum_le_sum
      intro p _
      exact affine_dimension_ratio (d p) h (k p) (μ p) P (hk p) (hμ p) hPR (hd p)
    _ = h / 32 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

lemma complete_sdp_budget {P : ℕ} (hP : 0 < P) (d : Fin P → ℕ)
    (h : ℝ) (k μ : Fin P → ℝ) (hk : ∀ p, 0 < k p) (hμ : ∀ p, 0 < μ p)
    (hd : ∀ p, (d p : ℝ) * μ p ≤ 2 * k p * h) :
    h / 8 + (h / 8 + ∑ p, (d p : ℝ) / (64 * (P : ℝ) * k p / μ p)) ≤ (9 / 32 : ℝ) * h := by
  have hs := affine_total_ratio hP d h k μ hk hμ hd
  linarith

end Komlos.KMFresh

-- END KMProof/SdpBudgetAlgebra.lean

-- BEGIN KMProof/RowCovariance.lean

open Matrix

namespace Komlos.KMFresh

lemma row_covariance_exists {h P : ℕ} (hh : 0 < h) (hP : 0 < P)
    (d : Fin P → ℕ) (A : (p : Fin P) → Matrix (Fin (d p)) (Fin h) ℝ)
    (k μ : Fin P → ℝ) (hk : ∀ p, 0 < k p) (hμ : ∀ p, 0 < μ p)
    (hd : ∀ p, (d p : ℝ) * μ p ≤ 2 * k p * (h : ℝ))
    (Z : Submodule ℝ (EuclideanSpace ℝ (Fin h)))
    (hZ : (9 / 32 : ℝ) * h ≤ Module.finrank ℝ Z) :
    ∃ X : Matrix (Fin h) (Fin h) ℝ, X.PosSemidef ∧ X.trace = (h : ℝ) / 8 ∧
      (∀ i, X i i ≤ 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin h), x ∈ Zᗮ → X *ᵥ (fun i => x i) = 0) ∧
      ((8 : ℝ) • Matrix.diagonal X.diag - X).PosSemidef ∧
      ∀ p, ((64 * (P : ℝ) * k p / μ p) • Matrix.diagonal (A p * X * (A p).transpose).diag -
        A p * X * (A p).transpose).PosSemidef := by
  classical
  let dims : Option (Fin P) → ℕ := fun j => j.elim h d
  let mats : (j : Option (Fin P)) → Matrix (Fin (dims j)) (Fin h) ℝ := fun j =>
    match j with
    | none => by change Matrix (Fin h) (Fin h) ℝ; exact 1
    | some p => A p
  let coeff : Option (Fin P) → ℝ := fun j => j.elim 8 (fun p => 64 * (P : ℝ) * k p / μ p)
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have ht : ∀ j, 0 < coeff j := by
    intro j
    cases j with
    | none => norm_num [coeff]
    | some p => dsimp [coeff]; exact div_pos (mul_pos (mul_pos (by norm_num) hPR) (hk p)) (hμ p)
  have he : (∑ j : Option (Fin P), (dims j : ℝ) / coeff j) =
      (h : ℝ) / 8 + ∑ p, (d p : ℝ) / (64 * (P : ℝ) * k p / μ p) := by
    simp [dims, coeff, Fintype.sum_option]
  have hb : (h : ℝ) / 8 + (∑ j : Option (Fin P), (dims j : ℝ) / coeff j) ≤ Module.finrank ℝ Z := by
    rw [he]
    exact (complete_sdp_budget hP d h k μ hk hμ hd).trans hZ
  obtain ⟨X, hX, htrace, hdiag, hker, hspec⟩ :=
    affine_sdp_exists dims mats coeff ht Z (by positivity : (0 : ℝ) < h / 8) hb
  refine ⟨X, hX, htrace, hdiag, hker, ?_, ?_⟩
  · have hh0 := hspec none
    simp only [mats, coeff, Option.elim_none] at hh0
    have hh : ((8 : ℝ) • Matrix.diagonal ((1 : Matrix (Fin h) (Fin h) ℝ) * X * (1 : Matrix (Fin h) (Fin h) ℝ).transpose).diag -
        (1 : Matrix (Fin h) (Fin h) ℝ) * X * (1 : Matrix (Fin h) (Fin h) ℝ).transpose).PosSemidef := by
      convert hh0 using 1 <;> rfl
    simpa only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] using hh
  · intro p
    have hh0 := hspec (some p)
    simp only [mats, coeff, Option.elim_some] at hh0
    convert hh0 using 1 <;> rfl

end Komlos.KMFresh

-- END KMProof/RowCovariance.lean

-- BEGIN KMProof/InjectionMatrix.lean

open Matrix

namespace Komlos.KMFresh

noncomputable def injectionMatrix {h n : ℕ} (e : Fin h ↪ Fin n) : Matrix (Fin n) (Fin h) ℝ :=
  fun i j => if i = e j then 1 else 0

lemma injectionMatrix_isometry {h n : ℕ} (e : Fin h ↪ Fin n) :
    (injectionMatrix e).transpose * injectionMatrix e = 1 := by
  classical
  ext i j
  simp [injectionMatrix, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    mul_ite, e.injective.eq_iff, eq_comm]

noncomputable def extendMatrix {h n : ℕ} (e : Fin h ↪ Fin n)
    (X : Matrix (Fin h) (Fin h) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  injectionMatrix e * X * (injectionMatrix e).transpose

lemma extendMatrix_psd {h n : ℕ} (e : Fin h ↪ Fin n)
    {X : Matrix (Fin h) (Fin h) ℝ} (hX : X.PosSemidef) : (extendMatrix e X).PosSemidef := by
  have h := hX.mul_mul_conjTranspose_same (injectionMatrix e)
  simpa only [extendMatrix, Matrix.conjTranspose_eq_transpose_of_trivial] using h

lemma extendMatrix_trace {h n : ℕ} (e : Fin h ↪ Fin n)
    (X : Matrix (Fin h) (Fin h) ℝ) : (extendMatrix e X).trace = X.trace := by
  unfold extendMatrix
  rw [Matrix.trace_mul_cycle, injectionMatrix_isometry, Matrix.one_mul]

lemma injectionMatrix_pullback {h n : ℕ} (e : Fin h ↪ Fin n) (x : Fin n → ℝ) :
    (injectionMatrix e).transpose *ᵥ x = fun j => x (e j) := by
  classical
  funext j
  simp [injectionMatrix, Matrix.mulVec, dotProduct]

lemma extendMatrix_apply_image {h n : ℕ} (e : Fin h ↪ Fin n)
    (X : Matrix (Fin h) (Fin h) ℝ) (i j : Fin h) :
    extendMatrix e X (e i) (e j) = X i j := by
  classical
  simp [extendMatrix, injectionMatrix, Matrix.mul_apply, e.injective.eq_iff]

lemma extendMatrix_apply_not_mem {h n : ℕ} (e : Fin h ↪ Fin n)
    (X : Matrix (Fin h) (Fin h) ℝ) (i j : Fin n) (hi : ∀ k, i ≠ e k) :
    extendMatrix e X i j = 0 := by
  classical
  simp [extendMatrix, injectionMatrix, Matrix.mul_apply, hi]

end Komlos.KMFresh

-- END KMProof/InjectionMatrix.lean

-- BEGIN KMProof/AliveEmbedding.lean

namespace Komlos.KMFresh

noncomputable def aliveExtend {n : ℕ} (A : Finset (Fin n))
    (z : Fin (Fintype.card A) → ℝ) (i : Fin n) : ℝ := by
  classical
  exact if h : i ∈ A then z ((Fintype.equivFin A) ⟨i, h⟩) else 0

lemma aliveExtend_mem {n : ℕ} (A : Finset (Fin n))
    (z : Fin (Fintype.card A) → ℝ) (i : A) :
    aliveExtend A z i.val = z ((Fintype.equivFin A) i) := by
  classical
  simp [aliveExtend, i.property]

lemma aliveExtend_not_mem {n : ℕ} (A : Finset (Fin n))
    (z : Fin (Fintype.card A) → ℝ) (i : Fin n) (hi : i ∉ A) :
    aliveExtend A z i = 0 := by
  classical
  simp only [aliveExtend, dif_neg hi]

lemma aliveExtend_sum_sq {n : ℕ} (A : Finset (Fin n))
    (z : Fin (Fintype.card A) → ℝ) :
    ∑ i : Fin n, aliveExtend A z i ^ 2 = ∑ j, z j ^ 2 := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i ∈ A)
    (fun i => aliveExtend A z i ^ 2)
  have hn : (∑ i : {i : Fin n // i ∉ A}, aliveExtend A z i.val ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [aliveExtend_not_mem A z i.val i.property]
    norm_num
  rw [hn, add_zero] at h
  rw [← h]
  simp only [aliveExtend_mem]
  have hu : @Finset.univ A (Subtype.fintype (fun i : Fin n => i ∈ A)) =
      @Finset.univ A (Finset.Subtype.fintype A) := by ext i; simp
  rw [hu]
  exact (Fintype.equivFin A).sum_comp (fun j => z j ^ 2)

lemma aliveExtend_sum_mul {n : ℕ} (A : Finset (Fin n))
    (x : Fin n → ℝ) (z : Fin (Fintype.card A) → ℝ) :
    ∑ i : Fin n, x i * aliveExtend A z i =
      ∑ j : Fin (Fintype.card A), x ((Fintype.equivFin A).symm j).val * z j := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i ∈ A)
    (fun i => x i * aliveExtend A z i)
  have hn : (∑ i : {i : Fin n // i ∉ A}, x i.val * aliveExtend A z i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [aliveExtend_not_mem A z i.val i.property, mul_zero]
  rw [hn, add_zero] at h
  rw [← h]
  simp only [aliveExtend_mem]
  have hu : @Finset.univ A (Subtype.fintype (fun i : Fin n => i ∈ A)) =
      @Finset.univ A (Finset.Subtype.fintype A) := by ext i; simp
  rw [hu]
  have he := (Fintype.equivFin A).sum_comp
    (fun j => x ((Fintype.equivFin A).symm j).val * z j)
  simpa only [Equiv.symm_apply_apply] using he

end Komlos.KMFresh

-- END KMProof/AliveEmbedding.lean

-- BEGIN KMProof/AliveMatrix.lean

open Matrix

namespace Komlos.KMFresh

noncomputable def aliveInjection {n : ℕ} (A : Finset (Fin n)) : Fin (Fintype.card A) ↪ Fin n where
  toFun j := ((Fintype.equivFin A).symm j).val
  inj' := by
    intro i j h
    exact (Fintype.equivFin A).symm.injective (Subtype.ext h)

lemma aliveInjection_mem {n : ℕ} (A : Finset (Fin n)) (j : Fin (Fintype.card A)) :
    aliveInjection A j ∈ A := ((Fintype.equivFin A).symm j).property

lemma aliveInjection_range {n : ℕ} (A : Finset (Fin n)) (i : Fin n) :
    (∃ j, aliveInjection A j = i) ↔ i ∈ A := by
  constructor
  · rintro ⟨j, rfl⟩
    exact aliveInjection_mem A j
  · intro hi
    refine ⟨(Fintype.equivFin A) ⟨i, hi⟩, ?_⟩
    change ((Fintype.equivFin A).symm ((Fintype.equivFin A) ⟨i, hi⟩)).val = i
    rw [Equiv.symm_apply_apply]

noncomputable def aliveMatrix {n : ℕ} (A : Finset (Fin n))
    (X : Matrix (Fin (Fintype.card A)) (Fin (Fintype.card A)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  extendMatrix (aliveInjection A) X

lemma aliveMatrix_psd {n : ℕ} (A : Finset (Fin n))
    {X : Matrix (Fin (Fintype.card A)) (Fin (Fintype.card A)) ℝ} (hX : X.PosSemidef) :
    (aliveMatrix A X).PosSemidef := extendMatrix_psd _ hX

lemma aliveMatrix_trace {n : ℕ} (A : Finset (Fin n))
    (X : Matrix (Fin (Fintype.card A)) (Fin (Fintype.card A)) ℝ) :
    (aliveMatrix A X).trace = X.trace := extendMatrix_trace _ X

lemma aliveMatrix_diagonal {n : ℕ} (A : Finset (Fin n))
    (X : Matrix (Fin (Fintype.card A)) (Fin (Fintype.card A)) ℝ)
    (hX : ∀ i, X i i ≤ 1) (i : Fin n) : aliveMatrix A X i i ≤ 1 := by
  classical
  by_cases hi : i ∈ A
  · obtain ⟨j, rfl⟩ := (aliveInjection_range A i).mpr hi
    exact (extendMatrix_apply_image (aliveInjection A) X j j).le.trans (hX j)
  · have he : ∀ j, i ≠ aliveInjection A j := by
      intro j h
      exact hi (h.symm ▸ aliveInjection_mem A j)
    rw [aliveMatrix, extendMatrix_apply_not_mem _ X i i he]
    norm_num

lemma aliveMatrix_frozen_column {n : ℕ} (A : Finset (Fin n))
    (X : Matrix (Fin (Fintype.card A)) (Fin (Fintype.card A)) ℝ)
    (i j : Fin n) (hj : j ∉ A) : aliveMatrix A X i j = 0 := by
  classical
  have he : ∀ k, j ≠ aliveInjection A k := by
    intro k h
    exact hj (h.symm ▸ aliveInjection_mem A k)
  simp [aliveMatrix, extendMatrix, injectionMatrix, Matrix.mul_apply, he]

lemma aliveMatrix_frozen_kernel {n : ℕ} (A : Finset (Fin n))
    (X : Matrix (Fin (Fintype.card A)) (Fin (Fintype.card A)) ℝ)
    (j : Fin n) (hj : j ∉ A) : aliveMatrix A X *ᵥ Pi.single j 1 = 0 := by
  classical
  rw [Matrix.mulVec_single_one]
  funext i
  exact aliveMatrix_frozen_column A X i j hj

end Komlos.KMFresh

-- END KMProof/AliveMatrix.lean

-- BEGIN KMProof/ExtendedCovariance.lean

open Matrix

namespace Komlos.KMFresh

lemma extendMatrix_diagonal {h n : ℕ} (e : Fin h ↪ Fin n)
    (X : Matrix (Fin h) (Fin h) ℝ) :
    extendMatrix e (Matrix.diagonal X.diag) = Matrix.diagonal (extendMatrix e X).diag := by
  classical
  ext i j
  by_cases hi : ∃ a, e a = i
  · obtain ⟨a, rfl⟩ := hi
    by_cases hj : ∃ b, e b = j
    · obtain ⟨b, rfl⟩ := hj
      simp only [extendMatrix_apply_image, Matrix.diagonal_apply, Matrix.diag,
        e.injective.eq_iff]
    · have hje : ∀ b, j ≠ e b := by simpa only [eq_comm, not_exists] using hj
      have hij : e a ≠ j := by intro he; exact hj ⟨a, he⟩
      simp [extendMatrix, injectionMatrix, Matrix.mul_apply, hje,
        Matrix.diagonal_apply, hij]
  · have hie : ∀ a, i ≠ e a := by simpa only [eq_comm, not_exists] using hi
    rw [extendMatrix_apply_not_mem e _ i j hie]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.diag]
      exact (extendMatrix_apply_not_mem e X i i hie).symm
    · simp [hij]

lemma extendMatrix_base_psd {h n : ℕ} (e : Fin h ↪ Fin n)
    (X : Matrix (Fin h) (Fin h) ℝ) (t : ℝ)
    (hb : (t • Matrix.diagonal X.diag - X).PosSemidef) :
    (t • Matrix.diagonal (extendMatrix e X).diag - extendMatrix e X).PosSemidef := by
  have hh := extendMatrix_psd e hb
  have he : extendMatrix e (t • Matrix.diagonal X.diag - X) =
      t • Matrix.diagonal (extendMatrix e X).diag - extendMatrix e X := by
    simp only [extendMatrix, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul]
    rw [← extendMatrix, extendMatrix_diagonal]
    rfl
  rw [he] at hh
  exact hh

lemma extendMatrix_affine {h n d : ℕ} (e : Fin h ↪ Fin n)
    (X : Matrix (Fin h) (Fin h) ℝ) (A : Matrix (Fin d) (Fin n) ℝ) :
    A * extendMatrix e X * A.transpose =
      (A * injectionMatrix e) * X * (A * injectionMatrix e).transpose := by
  simp only [extendMatrix, Matrix.transpose_mul, Matrix.mul_assoc]

lemma extendMatrix_kernel {h n : ℕ} (e : Fin h ↪ Fin n)
    (X : Matrix (Fin h) (Fin h) ℝ) (x : Fin n → ℝ)
    (hx : X *ᵥ (fun i => x (e i)) = 0) : extendMatrix e X *ᵥ x = 0 := by
  simp only [extendMatrix, ← Matrix.mulVec_mulVec, injectionMatrix_pullback, hx,
    Matrix.mulVec_zero]

end Komlos.KMFresh

-- END KMProof/ExtendedCovariance.lean

-- BEGIN KMProof/FullCovariance.lean

open Matrix

namespace Komlos.KMFresh

lemma full_covariance_exists {n P : ℕ} (alive : Finset (Fin n))
    (hh : 0 < Fintype.card alive) (hP : 0 < P)
    (d : Fin P → ℕ) (A : (p : Fin P) → Matrix (Fin (d p)) (Fin n) ℝ)
    (k μ : Fin P → ℝ) (hk : ∀ p, 0 < k p) (hμ : ∀ p, 0 < μ p)
    (hd : ∀ p, (d p : ℝ) * μ p ≤ 2 * k p * (Fintype.card alive : ℝ))
    (Z : Submodule ℝ (EuclideanSpace ℝ (Fin (Fintype.card alive))))
    (hZ : (9 / 32 : ℝ) * Fintype.card alive ≤ Module.finrank ℝ Z) :
    ∃ Y : Matrix (Fin n) (Fin n) ℝ, Y.PosSemidef ∧
      Y.trace = (Fintype.card alive : ℝ) / 8 ∧ (∀ i, Y i i ≤ 1) ∧
      (∀ j, j ∉ alive → Y *ᵥ Pi.single j 1 = 0) ∧
      (∀ a : Fin n → ℝ,
        WithLp.toLp 2 (fun i => a (aliveInjection alive i)) ∈ Zᗮ → Y *ᵥ a = 0) ∧
      ((8 : ℝ) • Matrix.diagonal Y.diag - Y).PosSemidef ∧
      ∀ p, ((64 * (P : ℝ) * k p / μ p) • Matrix.diagonal (A p * Y * (A p).transpose).diag -
        A p * Y * (A p).transpose).PosSemidef := by
  classical
  let E := injectionMatrix (aliveInjection alive)
  obtain ⟨X, hX, htrace, hdiag, hker, hbase, haff⟩ :=
    row_covariance_exists hh hP d (fun p => A p * E) k μ hk hμ hd Z hZ
  refine ⟨aliveMatrix alive X, aliveMatrix_psd alive hX, ?_,
    aliveMatrix_diagonal alive X hdiag, ?_, ?_, ?_, ?_⟩
  · exact (aliveMatrix_trace alive X).trans htrace
  · intro j hj
    exact aliveMatrix_frozen_kernel alive X j hj
  · intro a ha
    exact extendMatrix_kernel (aliveInjection alive) X a
      (hker (WithLp.toLp 2 (fun i => a (aliveInjection alive i))) ha)
  · exact extendMatrix_base_psd (aliveInjection alive) X 8 hbase
  · intro p
    have he := extendMatrix_affine (aliveInjection alive) X (A p)
    change A p * aliveMatrix alive X * (A p).transpose =
      (A p * E) * X * (A p * E).transpose at he
    rw [he]
    exact haff p

end Komlos.KMFresh

-- END KMProof/FullCovariance.lean

-- BEGIN KMProof/ConstraintSpan.lean

namespace Komlos.KMFresh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def blockedVectors {R : Type*} (x : E) (a g : R → E)
    (large dangerous : Finset R) : Finset E := by
  classical
  exact insert x (large.image a ∪ dangerous.image g)

noncomputable def blockedSpace {R : Type*} (x : E) (a g : R → E)
    (large dangerous : Finset R) : Submodule ℝ E :=
  Submodule.span ℝ (blockedVectors x a g large dangerous : Set E)

noncomputable def allowedSpace {R : Type*} (x : E) (a g : R → E)
    (large dangerous : Finset R) : Submodule ℝ E :=
  (blockedSpace x a g large dangerous)ᗮ

omit [FiniteDimensional ℝ E] in
lemma blockedSpace_finrank {R : Type*} (x : E) (a g : R → E)
    (large dangerous : Finset R) :
    Module.finrank ℝ (blockedSpace x a g large dangerous) ≤ 1 + large.card + dangerous.card := by
  classical
  have hs := finrank_span_finset_le_card (R := ℝ) (blockedVectors x a g large dangerous)
  have hc : (blockedVectors x a g large dangerous).card ≤ 1 + large.card + dangerous.card := by
    unfold blockedVectors
    have hi := Finset.card_insert_le x (large.image a ∪ dangerous.image g)
    have hu := Finset.card_union_le (large.image a) (dangerous.image g)
    have hl := Finset.card_image_le (s := large) (f := a)
    have hd := Finset.card_image_le (s := dangerous) (f := g)
    omega
  exact hs.trans hc

lemma allowedSpace_budget {R : Type*} (x : E) (a g : R → E)
    (large dangerous : Finset R)
    (hh : (16 : ℝ) < Module.finrank ℝ E)
    (hl : (large.card : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 32)
    (hd : (dangerous.card : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 64) :
    (9 / 32 : ℝ) * Module.finrank ℝ E ≤
      (Module.finrank ℝ (allowedSpace x a g large dangerous) : ℝ) := by
  have hs := blockedSpace_finrank x a g large dangerous
  have he := (blockedSpace x a g large dangerous).finrank_add_finrank_orthogonal
  have hsR : (Module.finrank ℝ (blockedSpace x a g large dangerous) : ℝ) ≤
      1 + (large.card : ℝ) + dangerous.card := by exact_mod_cast hs
  have heR : (Module.finrank ℝ (blockedSpace x a g large dangerous) : ℝ) +
      (Module.finrank ℝ (allowedSpace x a g large dangerous) : ℝ) = Module.finrank ℝ E := by
    exact_mod_cast he
  linarith

omit [FiniteDimensional ℝ E] in
lemma blocked_state_mem {R : Type*} (x : E) (a g : R → E)
    (large dangerous : Finset R) : x ∈ (allowedSpace x a g large dangerous)ᗮ := by
  classical
  apply (blockedSpace x a g large dangerous).le_orthogonal_orthogonal
  exact Submodule.subset_span (by simp [blockedVectors])

omit [FiniteDimensional ℝ E] in
lemma blocked_large_mem {R : Type*} (x : E) (a g : R → E)
    (large dangerous : Finset R) (r : R) (hr : r ∈ large) :
    a r ∈ (allowedSpace x a g large dangerous)ᗮ := by
  classical
  apply (blockedSpace x a g large dangerous).le_orthogonal_orthogonal
  exact Submodule.subset_span (by
    simp only [blockedVectors, Finset.mem_coe, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inl ⟨r, hr, rfl⟩))

omit [FiniteDimensional ℝ E] in
lemma blocked_dangerous_mem {R : Type*} (x : E) (a g : R → E)
    (large dangerous : Finset R) (r : R) (hr : r ∈ dangerous) :
    g r ∈ (allowedSpace x a g large dangerous)ᗮ := by
  classical
  apply (blockedSpace x a g large dangerous).le_orthogonal_orthogonal
  exact Submodule.subset_span (by
    simp only [blockedVectors, Finset.mem_coe, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    exact Or.inr (Or.inr ⟨r, hr, rfl⟩))

end Komlos.KMFresh

-- END KMProof/ConstraintSpan.lean

-- BEGIN KMProof/StateCovariance.lean

open Matrix

namespace Komlos.KMFresh

lemma state_covariance_exists {R : Type*} {n P : ℕ} (alive : Finset (Fin n))
    (x : Fin n → ℝ) (a g : R → Fin n → ℝ) (large dangerous : Finset R)
    (hh : (16 : ℝ) < Fintype.card alive) (hP : 0 < P)
    (hl : (large.card : ℝ) ≤ (Fintype.card alive : ℝ) / 32)
    (hdanger : (dangerous.card : ℝ) ≤ (Fintype.card alive : ℝ) / 64)
    (d : Fin P → ℕ) (A : (p : Fin P) → Matrix (Fin (d p)) (Fin n) ℝ)
    (k μ : Fin P → ℝ) (hk : ∀ p, 0 < k p) (hμ : ∀ p, 0 < μ p)
    (hd : ∀ p, (d p : ℝ) * μ p ≤ 2 * k p * (Fintype.card alive : ℝ)) :
    ∃ Y : Matrix (Fin n) (Fin n) ℝ, Y.PosSemidef ∧
      Y.trace = (Fintype.card alive : ℝ) / 8 ∧ (∀ i, Y i i ≤ 1) ∧
      (∀ j, j ∉ alive → Y *ᵥ Pi.single j 1 = 0) ∧ Y *ᵥ x = 0 ∧
      (∀ r ∈ large, Y *ᵥ a r = 0) ∧ (∀ r ∈ dangerous, Y *ᵥ g r = 0) ∧
      ((8 : ℝ) • Matrix.diagonal Y.diag - Y).PosSemidef ∧
      ∀ p, ((64 * (P : ℝ) * k p / μ p) • Matrix.diagonal (A p * Y * (A p).transpose).diag -
        A p * Y * (A p).transpose).PosSemidef := by
  let restrict : (Fin n → ℝ) → EuclideanSpace ℝ (Fin (Fintype.card alive)) :=
    fun v => WithLp.toLp 2 (fun i => v (aliveInjection alive i))
  let Z := allowedSpace (restrict x) (fun r => restrict (a r)) (fun r => restrict (g r)) large dangerous
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (Fintype.card alive))) =
      Fintype.card alive := by simp
  have hZ : (9 / 32 : ℝ) * Fintype.card alive ≤ Module.finrank ℝ Z := by
    have he := allowedSpace_budget (restrict x) (fun r => restrict (a r))
      (fun r => restrict (g r)) large dangerous
      (by simpa only [hdim] using hh) (by simpa only [hdim] using hl)
      (by simpa only [hdim] using hdanger)
    simpa only [hdim] using he
  have hpos : 0 < Fintype.card alive := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 16) hh)
  obtain ⟨Y, hY, htr, hdiag, hfrozen, hker, hbase, haff⟩ :=
    full_covariance_exists alive hpos hP d A k μ hk hμ hd Z hZ
  refine ⟨Y, hY, htr, hdiag, hfrozen, ?_, ?_, ?_, hbase, haff⟩
  · exact hker x (blocked_state_mem (restrict x) (fun r => restrict (a r))
      (fun r => restrict (g r)) large dangerous)
  · intro r hr
    exact hker (a r) (blocked_large_mem (restrict x) (fun r => restrict (a r))
      (fun r => restrict (g r)) large dangerous r hr)
  · intro r hr
    exact hker (g r) (blocked_dangerous_mem (restrict x) (fun r => restrict (a r))
      (fun r => restrict (g r)) large dangerous r hr)

end Komlos.KMFresh

-- END KMProof/StateCovariance.lean

-- BEGIN KMProof/RowSelection.lean

namespace Komlos.KMFresh

noncomputable def selectedRow {R : Type*} (S : Finset R) : Fin (Fintype.card S) ↪ R where
  toFun j := ((Fintype.equivFin S).symm j).val
  inj' := by
    intro i j h
    exact (Fintype.equivFin S).symm.injective (Subtype.ext h)

lemma selectedRow_mem {R : Type*} (S : Finset R) (j : Fin (Fintype.card S)) :
    selectedRow S j ∈ S := ((Fintype.equivFin S).symm j).property

lemma selectedRow_surj {R : Type*} (S : Finset R) (r : R) (hr : r ∈ S) :
    ∃ j, selectedRow S j = r := by
  refine ⟨(Fintype.equivFin S) ⟨r, hr⟩, ?_⟩
  change ((Fintype.equivFin S).symm ((Fintype.equivFin S) ⟨r, hr⟩)).val = r
  rw [Equiv.symm_apply_apply]

lemma selectedRow_sum {R : Type*} (S : Finset R) (f : R → ℝ) :
    ∑ j : Fin (Fintype.card S), f (selectedRow S j) = ∑ r ∈ S, f r := by
  classical
  apply Finset.sum_bij (fun j _ => selectedRow S j)
  · intro j _
    exact selectedRow_mem S j
  · intro i _ j _ h
    exact (selectedRow S).injective h
  · intro r hr
    obtain ⟨j, hj⟩ := selectedRow_surj S r hr
    exact ⟨j, Finset.mem_univ j, hj⟩
  · intro j _
    rfl

lemma selectedRow_sum_supported {R : Type*} [Fintype R] (S : Finset R) (f : R → ℝ)
    (hf : ∀ r, r ∉ S → f r = 0) :
    ∑ j : Fin (Fintype.card S), f (selectedRow S j) = ∑ r, f r := by
  rw [selectedRow_sum]
  exact Finset.sum_subset (Finset.subset_univ S) (fun r _ hr => hf r hr)

end Komlos.KMFresh

-- END KMProof/RowSelection.lean

-- BEGIN KMProof/ScaleStateCovariance.lean

open Matrix

namespace Komlos.KMFresh

noncomputable def scaleMediumMatrix {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β : Fin (q + 1) → ℝ)
    (x : Fin n → ℝ) (p : Fin (q + 1)) :
    Matrix (Fin (Fintype.card (mediumRows (fun r i => scaleEntry q p (A r i))
      ρ ((4 : ℝ)^p.val) (μ p) x))) (Fin n) ℝ :=
  fun j i =>
    let r := selectedRow (mediumRows (fun r i => scaleEntry q p (A r i))
      ρ ((4 : ℝ)^p.val) (μ p) x) j
    scaleEntry q p (A r i) - 2 * β p * (scaleEntry q p (A r i))^2 * x i

lemma scale_state_covariance_exists {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β : Fin (q + 1) → ℝ)
    (s : AdaptiveState (Fin (q + 1) × R) n)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2)
    (hμ : ∀ p, 0 < μ p) (hh : (16 : ℝ) < (aliveSet ρ s.x).card)
    (hgood : ∀ p i, i ∈ aliveSet ρ s.x →
      ∑ r ∈ (scaleLocalState s p).hit, (scaleEntry q p (A r i))^2 ≤ μ p / (64 * ((q + 1 : ℕ) : ℝ))) :
    ∃ Y : Matrix (Fin n) (Fin n) ℝ, Y.PosSemidef ∧
      Y.trace = ((aliveSet ρ s.x).card : ℝ) / 8 ∧ (∀ i, Y i i ≤ 1) ∧
      (∀ j, j ∉ aliveSet ρ s.x → Y *ᵥ Pi.single j 1 = 0) ∧ Y *ᵥ s.x = 0 ∧
      (∀ z ∈ scaleLarge A q ρ s.x, Y *ᵥ scaleRows A q z = 0) ∧
      (∀ z ∈ scaleDangerous (fun p r i => scaleEntry q p (A r i)) ρ
        (fun p => (4 : ℝ)^p.val) μ s,
        Y *ᵥ (fun i => scaleRows A q z i - 2 * β z.1 * (scaleRows A q z i)^2 * s.x i) = 0) ∧
      ((8 : ℝ) • Matrix.diagonal Y.diag - Y).PosSemidef ∧
      ∀ p, ((64 * ((q + 1 : ℕ) : ℝ) * (4 : ℝ)^p.val / μ p) •
        Matrix.diagonal (scaleMediumMatrix A q ρ μ β s.x p * Y *
          (scaleMediumMatrix A q ρ μ β s.x p).transpose).diag -
        scaleMediumMatrix A q ρ μ β s.x p * Y *
          (scaleMediumMatrix A q ρ μ β s.x p).transpose).PosSemidef := by
  classical
  let d : Fin (q + 1) → ℕ := fun p => Fintype.card
    (mediumRows (fun r i => scaleEntry q p (A r i)) ρ ((4 : ℝ)^p.val) (μ p) s.x)
  have hd : ∀ p, (d p : ℝ) * μ p ≤
      2 * (4 : ℝ)^p.val * (Fintype.card (aliveSet ρ s.x) : ℝ) := by
    intro p
    have he := mediumRows_count (fun r i => scaleEntry q p (A r i)) ρ ((4 : ℝ)^p.val) (μ p) s.x
      (fun i => single_scale_column_bound A q p i (fun r => ha r i) (hA i))
    simpa only [d, Fintype.card_coe] using he
  have hl := scaleLarge_count A q ρ s.x ha hA
  have hD := scaleDangerous_count (fun p r i => scaleEntry q p (A r i)) ρ
    (fun p => (4 : ℝ)^p.val) μ s (Nat.succ_pos q) hμ hgood
  have he := state_covariance_exists (aliveSet ρ s.x) s.x (scaleRows A q)
    (fun z i => scaleRows A q z i - 2 * β z.1 * (scaleRows A q z i)^2 * s.x i)
    (scaleLarge A q ρ s.x)
    (scaleDangerous (fun p r i => scaleEntry q p (A r i)) ρ (fun p => (4 : ℝ)^p.val) μ s)
    (by simpa only [Fintype.card_coe] using hh) (Nat.succ_pos q)
    (by simpa only [Fintype.card_coe] using hl) (by simpa only [Fintype.card_coe] using hD)
    d (scaleMediumMatrix A q ρ μ β s.x) (fun p => (4 : ℝ)^p.val) μ
    (fun p => by positivity) hμ hd
  simpa only [Fintype.card_coe] using he

end Komlos.KMFresh

-- END KMProof/ScaleStateCovariance.lean

-- BEGIN KMProof/SignLaw.lean
noncomputable section
open Finset
namespace Komlos.KMFresh

def boolSign (b : Bool) : ℝ := if b then 1 else -1
lemma boolSign_sq (b : Bool) : boolSign b^2=1 := by cases b <;> norm_num [boolSign]
lemma boolSign_not (b : Bool) : boolSign (!b) = -boolSign b := by cases b <;> norm_num [boolSign]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def flipSignCoordinate (i : ι) : (ι → Bool) ≃ (ι → Bool) :=
  { toFun := fun s j => if j=i then !(s j) else s j
    invFun := fun s j => if j=i then !(s j) else s j
    left_inv := by intro s; funext j; by_cases hj:j=i <;> simp [hj]
    right_inv := by intro s; funext j; by_cases hj:j=i <;> simp [hj] }

lemma sign_coordinate_mean (i : ι) :
    (FiniteLaw.uniform (ι → Bool)).mean (fun s => boolSign (s i))=0 := by
  have hh := FiniteLaw.uniform_mean_equiv (flipSignCoordinate i) (fun s => boolSign (s i))
  have he : (fun s => boolSign (flipSignCoordinate i s i)) =
      (fun s => (-1:ℝ)*boolSign (s i)) := by funext s; simp [flipSignCoordinate,boolSign_not]
  rw [he,FiniteLaw.mean_mul] at hh
  linarith

lemma sign_pair_mean (i j : ι) :
    (FiniteLaw.uniform (ι → Bool)).mean (fun s => boolSign (s i)*boolSign (s j)) =
      if i=j then 1 else 0 := by
  by_cases hij:i=j
  · subst j
    simp only [ite_true]
    simpa only [←pow_two,boolSign_sq] using (FiniteLaw.uniform (ι → Bool)).mean_const 1
  · rw [if_neg hij]
    have hh := FiniteLaw.uniform_mean_equiv (flipSignCoordinate i)
      (fun s => boolSign (s i)*boolSign (s j))
    have he : (fun s => boolSign (flipSignCoordinate i s i)*boolSign (flipSignCoordinate i s j)) =
        (fun s => (-1:ℝ)*(boolSign (s i)*boolSign (s j))) := by
      funext s
      simp [flipSignCoordinate,Ne.symm hij,boolSign_not]
    rw [he,FiniteLaw.mean_mul] at hh
    linarith

lemma sign_linear_mean (a : ι → ℝ) :
    (FiniteLaw.uniform (ι → Bool)).mean (fun s => ∑i,a i*boolSign (s i))=0 := by
  unfold FiniteLaw.mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  have hh := sign_coordinate_mean i
  change (∑s,(FiniteLaw.uniform (ι → Bool)).weight s*boolSign (s i))=0 at hh
  calc
    _ = a i*(∑s,(FiniteLaw.uniform (ι → Bool)).weight s*boolSign (s i)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
    _ = 0 := by rw [hh,mul_zero]

end Komlos.KMFresh

-- END KMProof/SignLaw.lean

-- BEGIN KMProof/OrthonormalSampler.lean
noncomputable section
open Finset
open scoped RealInnerProductSpace
namespace Komlos.KMFresh
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

def orthonormalSample (v : ι → E) (c : ι → ℝ) (s : ι → Bool) : E :=
  ∑i,(c i*boolSign (s i)) • v i

omit [DecidableEq ι] in
lemma orthonormalSample_norm (v : ι → E) (hv : Orthonormal ℝ v)
    (c : ι → ℝ) (hc : ∑i,(c i)^2=1) (s : ι → Bool) :
    ‖orthonormalSample v c s‖=1 := by
  have hh := hv.inner_sum (fun i => c i*boolSign (s i))
    (fun i => c i*boolSign (s i)) Finset.univ
  change ⟪orthonormalSample v c s,orthonormalSample v c s⟫ = _ at hh
  rw [real_inner_self_eq_norm_sq] at hh
  have he : (∑i,star (c i*boolSign (s i))*(c i*boolSign (s i)))=1 := by
    simpa only [star_trivial,←pow_two,mul_pow,boolSign_sq,mul_one] using hc
  change ‖orthonormalSample v c s‖^2 = ∑i,star (c i*boolSign (s i))*(c i*boolSign (s i)) at hh
  rw [he] at hh
  nlinarith [norm_nonneg (orthonormalSample v c s)]

omit [DecidableEq ι] in
lemma orthonormalSample_inner (v : ι → E) (c : ι → ℝ) (s : ι → Bool) (a : E) :
    ⟪a,orthonormalSample v c s⟫ = ∑i,(c i*⟪a,v i⟫)*boolSign (s i) := by
  simp only [orthonormalSample,inner_sum,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma orthonormalSample_mean (v : ι → E) (c : ι → ℝ) (a : E) :
    (FiniteLaw.uniform (ι → Bool)).mean (fun s => ⟪a,orthonormalSample v c s⟫)=0 := by
  simp_rw [orthonormalSample_inner]
  exact sign_linear_mean _

lemma orthonormalSample_covariance (v : ι → E) (c : ι → ℝ) (a : E) :
    (FiniteLaw.uniform (ι → Bool)).mean (fun s => ⟪a,orthonormalSample v c s⟫^2)=
      ∑i,(c i)^2*⟪a,v i⟫^2 := by
  simp_rw [orthonormalSample_inner]
  simpa only [mul_pow] using (FiniteLaw.uniform (ι → Bool)).mean_linear_square
    (fun i s => boolSign (s i)) (fun i => c i*⟪a,v i⟫) sign_pair_mean

omit [DecidableEq ι] in
lemma orthonormalSample_mem (v : ι → E) (c : ι → ℝ) (s : ι → Bool)
    (Z : Submodule ℝ E) (hv : ∀i,v i∈Z) : orthonormalSample v c s∈Z :=
  Submodule.sum_mem Z (fun i _ => Z.smul_mem _ (hv i))
end Komlos.KMFresh

-- END KMProof/OrthonormalSampler.lean

-- BEGIN KMProof/SpectralSampler.lean
noncomputable section
open Finset
open scoped RealInnerProductSpace
namespace Komlos.KMFresh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def spectralCoefficient {T : E →ₗ[ℝ] E} (hT : T.IsPositive)
    (i : Fin (Module.finrank ℝ E)) : ℝ :=
  Real.sqrt (hT.isSymmetric.eigenvalues rfl i)/Real.sqrt (T.trace ℝ E)

def spectralSample {T : E →ₗ[ℝ] E} (hT : T.IsPositive)
    (s : Fin (Module.finrank ℝ E) → Bool) : E :=
  orthonormalSample (hT.isSymmetric.eigenvectorBasis rfl) (spectralCoefficient hT) s

lemma spectralCoefficient_square {T : E →ₗ[ℝ] E} (hT : T.IsPositive)
    (ht : 0<T.trace ℝ E) (i : Fin (Module.finrank ℝ E)) :
    (spectralCoefficient hT i)^2=hT.isSymmetric.eigenvalues rfl i/T.trace ℝ E := by
  rw [spectralCoefficient,div_pow,Real.sq_sqrt (hT.nonneg_eigenvalues rfl i),Real.sq_sqrt ht.le]

lemma spectralCoefficient_sum {T : E →ₗ[ℝ] E} (hT : T.IsPositive)
    (ht : 0<T.trace ℝ E) : ∑i,(spectralCoefficient hT i)^2=1 := by
  simp_rw [spectralCoefficient_square hT ht]
  rw [←Finset.sum_div]
  have he : T.trace ℝ E = ∑i,hT.isSymmetric.eigenvalues rfl i := by
    simpa using hT.isSymmetric.trace_eq_sum_eigenvalues rfl
  rw [←he,div_self ht.ne']

lemma spectralSample_norm {T : E →ₗ[ℝ] E} (hT : T.IsPositive)
    (ht : 0<T.trace ℝ E) (s) : ‖spectralSample hT s‖=1 :=
  orthonormalSample_norm _ (hT.isSymmetric.eigenvectorBasis rfl).orthonormal _
    (spectralCoefficient_sum hT ht) s

lemma spectralSample_mean {T : E →ₗ[ℝ] E} (hT : T.IsPositive) (a : E) :
    (FiniteLaw.uniform (Fin (Module.finrank ℝ E) → Bool)).mean
      (fun s => ⟪a,spectralSample hT s⟫)=0 :=
  orthonormalSample_mean _ _ a

lemma spectralSample_covariance {T : E →ₗ[ℝ] E} (hT : T.IsPositive)
    (ht : 0<T.trace ℝ E) (a : E) :
    (FiniteLaw.uniform (Fin (Module.finrank ℝ E) → Bool)).mean
      (fun s => ⟪a,spectralSample hT s⟫^2)=⟪a,T a⟫/T.trace ℝ E := by
  change (FiniteLaw.uniform _).mean (fun s => ⟪a,orthonormalSample _ _ s⟫^2)=_
  rw [orthonormalSample_covariance,positive_spectral_quadratic hT,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [spectralCoefficient_square hT ht,real_inner_comm a]
  ring

lemma spectralSample_kernel {T : E →ₗ[ℝ] E} (hT : T.IsPositive)
    (a : E) (ha : T a=0) (s) : ⟪a,spectralSample hT s⟫=0 := by
  rw [spectralSample,orthonormalSample_inner]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : hT.isSymmetric.eigenvalues rfl i=0
  · simp [spectralCoefficient,hi]
  · have he := hT.isSymmetric a (hT.isSymmetric.eigenvectorBasis rfl i)
    rw [ha,hT.isSymmetric.apply_eigenvectorBasis] at he
    simp only [inner_zero_left,real_inner_smul_right] at he
    have hz : ⟪a,hT.isSymmetric.eigenvectorBasis rfl i⟫=0 := by
      exact (mul_eq_zero.mp he.symm).resolve_left hi
    rw [hz,mul_zero,zero_mul]
end Komlos.KMFresh

-- END KMProof/SpectralSampler.lean

-- BEGIN KMProof/SamplerSymmetry.lean
noncomputable section
open Finset
namespace Komlos.KMFresh
variable {ι : Type*} [Fintype ι]

def negateSigns : (ι → Bool) ≃ (ι → Bool) where
  toFun s i := !(s i)
  invFun s i := !(s i)
  left_inv s := by funext i; simp
  right_inv s := by funext i; simp

lemma uniform_odd_mean [DecidableEq ι] (f : (ι → Bool) → ℝ)
    (hf : ∀s,f (fun i => !(s i))= -f s) :
    (FiniteLaw.uniform (ι → Bool)).mean f=0 := by
  have hh := FiniteLaw.uniform_mean_equiv (negateSigns (ι:=ι)) f
  have he : (fun s => f (negateSigns s)) = fun s => (-1:ℝ)*f s := by
    funext s
    simpa [negateSigns] using hf s
  rw [he,FiniteLaw.mean_mul] at hh
  linarith

lemma orthonormalSample_negate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (c : ι → ℝ) (s : ι → Bool) :
    orthonormalSample v c (fun i => !(s i)) = -orthonormalSample v c s := by
  simp only [orthonormalSample,boolSign_not,mul_neg,neg_smul,Finset.sum_neg_distrib]

lemma uniform_odd_even_product [DecidableEq ι] (L Q : (ι → Bool) → ℝ)
    (hL : ∀s,L (fun i => !(s i))= -L s)
    (hQ : ∀s,Q (fun i => !(s i))=Q s) :
    (FiniteLaw.uniform (ι → Bool)).mean (fun s => L s*Q s)=0 := by
  apply uniform_odd_mean
  intro s
  rw [hL,hQ,neg_mul]
end Komlos.KMFresh

-- END KMProof/SamplerSymmetry.lean

-- BEGIN KMProof/MatrixSampler.lean
noncomputable section
open Finset Matrix
open scoped RealInnerProductSpace
namespace Komlos.KMFresh

abbrev matrixPositive {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) :=
  Matrix.isPositive_toEuclideanLin_iff.mpr hX

def matrixSignEquiv (n : ℕ) :
    (Fin n → Bool) ≃ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) → Bool) :=
  Equiv.arrowCongr (finCongr (by simp)).symm (Equiv.refl Bool)

def matrixSample {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (s : Fin n → Bool) : EuclideanSpace ℝ (Fin n) :=
  spectralSample (matrixPositive hX) (matrixSignEquiv n s)

lemma matrixSample_norm {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (ht : 0<X.trace) (s : Fin n → Bool) : ‖matrixSample hX s‖=1 := by
  apply spectralSample_norm
  simpa only [euclidean_trace] using ht

lemma matrixSample_mean {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (a : EuclideanSpace ℝ (Fin n)) :
    (FiniteLaw.uniform (Fin n → Bool)).mean (fun s => ⟪a,matrixSample hX s⟫)=0 := by
  rw [show (fun s => ⟪a,matrixSample hX s⟫) =
    (fun s => ⟪a,spectralSample (matrixPositive hX) (matrixSignEquiv n s)⟫) from rfl]
  exact (FiniteLaw.uniform_mean_equiv (matrixSignEquiv n)
    (fun r => ⟪a,spectralSample (matrixPositive hX) r⟫)).trans (spectralSample_mean _ a)

lemma matrixSample_covariance {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (ht : 0<X.trace) (a : EuclideanSpace ℝ (Fin n)) :
    (FiniteLaw.uniform (Fin n → Bool)).mean (fun s => ⟪a,matrixSample hX s⟫^2)=
      quadratic X (fun i => a i)/X.trace := by
  change (FiniteLaw.uniform _).mean
    (fun s => ⟪a,spectralSample (matrixPositive hX) (matrixSignEquiv n s)⟫^2)=_
  have ht' : 0<X.toEuclideanLin.trace ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [euclidean_trace] using ht
  have he := (FiniteLaw.uniform_mean_equiv (matrixSignEquiv n)
    (fun r => ⟪a,spectralSample (matrixPositive hX) r⟫^2)).trans
      (spectralSample_covariance (matrixPositive hX) ht' a)
  simpa only [euclidean_quadratic,euclidean_trace] using he

lemma matrixSample_kernel {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (a : EuclideanSpace ℝ (Fin n)) (ha : X *ᵥ (fun i => a i)=0) (s : Fin n → Bool) :
    ⟪a,matrixSample hX s⟫=0 := by
  apply spectralSample_kernel
  ext i
  exact congrFun ha i

lemma matrixSample_negate {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (s : Fin n → Bool) : matrixSample hX (fun i => !(s i)) = -matrixSample hX s := by
  unfold matrixSample spectralSample
  have he : matrixSignEquiv n (fun i => !(s i)) = fun i => !(matrixSignEquiv n s i) := by
    rfl
  rw [he,orthonormalSample_negate]
end Komlos.KMFresh

-- END KMProof/MatrixSampler.lean

-- BEGIN KMProof/ScaleCovarianceChoice.lean

open Matrix

namespace Komlos.KMFresh

noncomputable def scaleGood {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ : Fin (q + 1) → ℝ)
    (s : AdaptiveState (Fin (q + 1) × R) n) : Prop :=
  ∀ p i, i ∈ aliveSet ρ s.x →
    ∑ r ∈ (scaleLocalState s p).hit, (scaleEntry q p (A r i))^2 ≤ μ p / (64 * ((q + 1 : ℕ) : ℝ))

noncomputable def scaleRunning {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ : Fin (q + 1) → ℝ)
    (s : AdaptiveState (Fin (q + 1) × R) n) : Prop :=
  (16 * ((q + 1 : ℕ) : ℝ) < ((aliveSet ρ s.x).card : ℝ)) ∧ scaleGood A q ρ μ s

structure ScaleMatrixData {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β : Fin (q + 1) → ℝ)
    (s : AdaptiveState (Fin (q + 1) × R) n) where
  matrix : Matrix (Fin n) (Fin n) ℝ
  psd : matrix.PosSemidef
  trace : matrix.trace = ((aliveSet ρ s.x).card : ℝ) / 8
  diagonal : ∀ i, matrix i i ≤ 1
  frozen : ∀ j, j ∉ aliveSet ρ s.x → matrix *ᵥ Pi.single j 1 = 0
  state : matrix *ᵥ s.x = 0
  large : ∀ z ∈ scaleLarge A q ρ s.x, matrix *ᵥ scaleRows A q z = 0
  dangerous : ∀ z ∈ scaleDangerous (fun p r i => scaleEntry q p (A r i)) ρ
      (fun p => (4 : ℝ)^p.val) μ s,
      matrix *ᵥ (fun i => scaleRows A q z i - 2 * β z.1 * (scaleRows A q z i)^2 * s.x i) = 0
  base : ((8 : ℝ) • Matrix.diagonal matrix.diag - matrix).PosSemidef
  affine : ∀ p, ((64 * ((q + 1 : ℕ) : ℝ) * (4 : ℝ)^p.val / μ p) •
      Matrix.diagonal (scaleMediumMatrix A q ρ μ β s.x p * matrix *
        (scaleMediumMatrix A q ρ μ β s.x p).transpose).diag -
      scaleMediumMatrix A q ρ μ β s.x p * matrix *
        (scaleMediumMatrix A q ρ μ β s.x p).transpose).PosSemidef

noncomputable def chooseScaleMatrix {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (s : AdaptiveState (Fin (q + 1) × R) n) (hs : scaleRunning A q ρ μ s) :
    ScaleMatrixData A q ρ μ β s := Classical.choice (by
  have hp : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le q)
  have hh : (16 : ℝ) < ((aliveSet ρ s.x).card : ℝ) := by linarith [hs.1]
  obtain ⟨Y, hY, ht, hd, hf, hx, hl, hD, hb, haff⟩ :=
    scale_state_covariance_exists A q ρ μ β s ha hA hμ hh hs.2
  exact ⟨⟨Y, hY, ht, hd, hf, hx, hl, hD, hb, haff⟩⟩)

noncomputable def scaleDirection {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (s : AdaptiveState (Fin (q + 1) × R) n) (ω : Fin n → Bool) : Fin n → ℝ := by
  classical
  exact if hs : scaleRunning A q ρ μ s then
    fun i => matrixSample (chooseScaleMatrix A q ρ μ β ha hA hμ s hs).psd ω i
  else 0

lemma scaleDirection_running {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (s : AdaptiveState (Fin (q + 1) × R) n) (hs : scaleRunning A q ρ μ s) (ω : Fin n → Bool) :
    scaleDirection A q ρ μ β ha hA hμ s ω =
      fun i => matrixSample (chooseScaleMatrix A q ρ μ β ha hA hμ s hs).psd ω i := by
  classical
  simp only [scaleDirection, dif_pos hs]

end Komlos.KMFresh

-- END KMProof/ScaleCovarianceChoice.lean

-- BEGIN KMProof/MatrixCovariance.lean
noncomputable section
open Finset Matrix
open scoped RealInnerProductSpace
namespace Komlos.KMFresh

lemma euclidean_inner_sum {n : ℕ} (a : Fin n → ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ⟪WithLp.toLp 2 a,v⟫=∑i,a i*v i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma matrixSample_sum_covariance {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (ht : 0<X.trace) (a : Fin n → ℝ) :
    (FiniteLaw.uniform (Fin n → Bool)).mean (fun s => (∑i,a i*matrixSample hX s i)^2)=
      quadratic X a/X.trace := by
  simpa only [euclidean_inner_sum] using matrixSample_covariance hX ht (WithLp.toLp 2 a)

lemma matrixSample_coordinate_variance {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (ht : 0<X.trace) (i : Fin n) :
    (FiniteLaw.uniform (Fin n → Bool)).mean (fun s => (matrixSample hX s i)^2)=X i i/X.trace := by
  have hh := matrixSample_sum_covariance hX ht (Pi.single i 1)
  simpa [quadratic,Pi.single_apply] using hh

lemma quadratic_diagonal_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℝ) (t : ℝ) (hd : (t • Matrix.diagonal X.diag-X).PosSemidef)
    (a : ι → ℝ) : quadratic X a≤t*(∑i,X i i*(a i)^2) := by
  have hh := psd_quadratic_nonneg hd a
  have he : quadratic (t • Matrix.diagonal X.diag-X) a=
      t*(∑i,X i i*(a i)^2)-quadratic X a := by
    unfold quadratic
    rw [Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul]
    simp only [smul_eq_mul]
    congr 2
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mulVec_diagonal,Matrix.diag]
    ring
  rw [he] at hh
  linarith

lemma matrixSample_variance_bound {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (ht : 0<X.trace) (t : ℝ)
    (hd : (t • Matrix.diagonal X.diag-X).PosSemidef) (a : Fin n → ℝ) :
    (FiniteLaw.uniform (Fin n → Bool)).mean (fun s => (∑i,a i*matrixSample hX s i)^2)≤
      t*(∑i,(a i)^2*(FiniteLaw.uniform (Fin n → Bool)).mean (fun s => (matrixSample hX s i)^2)) := by
  rw [matrixSample_sum_covariance hX ht]
  simp_rw [matrixSample_coordinate_variance hX ht]
  have hh := div_le_div_of_nonneg_right (quadratic_diagonal_bound X t hd a) ht.le
  apply hh.trans_eq
  rw [Finset.mul_sum,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end Komlos.KMFresh

-- END KMProof/MatrixCovariance.lean

-- BEGIN KMProof/ModifiedRows.lean

namespace Komlos.KMFresh

lemma modified_coefficient_abs (a x β : ℝ) (ha : |a| ≤ 1) (hx : |x| ≤ 1)
    (hβ : 0 ≤ β) : |a - 2 * β * a ^ 2 * x| ≤ (1 + 2 * β) * |a| := by
  have ha0 := abs_nonneg a
  have he := sq_abs a
  have hs : a ^ 2 ≤ |a| := by nlinarith
  have hxmul : a ^ 2 * |x| ≤ a ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg a)]
  have hmul : 2 * β * (a ^ 2 * |x|) ≤ 2 * β * |a| :=
    mul_le_mul_of_nonneg_left (hxmul.trans hs) (by positivity)
  calc
    |a - 2 * β * a ^ 2 * x| ≤ |a| + |2 * β * a ^ 2 * x| := abs_sub _ _
    _ = |a| + 2 * β * (a ^ 2 * |x|) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * β * a ^ 2)]
      ring
    _ ≤ (1 + 2 * β) * |a| := by nlinarith

lemma modified_coefficient_sq (a x β : ℝ) (ha : |a| ≤ 1) (hx : |x| ≤ 1)
    (hβ : 0 ≤ β) (hβsmall : β ≤ 1 / 64) :
    (a - 2 * β * a ^ 2 * x) ^ 2 ≤ 2 * a ^ 2 := by
  have hc := modified_coefficient_abs a x β ha hx hβ
  have ha0 := abs_nonneg a
  have he := sq_abs a
  have hb : |a - 2 * β * a ^ 2 * x| ≤ (33 / 32 : ℝ) * |a| := by
    nlinarith [mul_le_mul_of_nonneg_right hβsmall ha0]
  have h0 := abs_nonneg (a - 2 * β * a ^ 2 * x)
  have hs := sq_abs (a - 2 * β * a ^ 2 * x)
  have hm := mul_self_le_mul_self h0 hb
  nlinarith [sq_nonneg a]

end Komlos.KMFresh

-- END KMProof/ModifiedRows.lean

-- BEGIN KMProof/RowMoments.lean

namespace Komlos.KMFresh

noncomputable def rowLinear {I : Type*} [Fintype I] (a x : I → ℝ) (β : ℝ) (v : I → ℝ) : ℝ :=
  ∑ i, (a i - 2 * β * a i ^ 2 * x i) * v i
noncomputable def rowQuadratic {I : Type*} [Fintype I] (a : I → ℝ) (β : ℝ) (v : I → ℝ) : ℝ :=
  β * ∑ i, a i ^ 2 * v i ^ 2

lemma rowQuadratic_mean {I Ω : Type*} [Fintype I] [Fintype Ω]
    (P : FiniteLaw Ω) (a : I → ℝ) (β : ℝ) (v : Ω → I → ℝ) :
    P.mean (fun ω => rowQuadratic a β (v ω)) =
      β * ∑ i, a i ^ 2 * P.mean (fun ω => v ω i ^ 2) := by
  unfold rowQuadratic
  rw [P.mean_mul]
  congr 1
  unfold FiniteLaw.mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma rowLinear_variance {I Ω : Type*} [Fintype I] [Fintype Ω]
    (P : FiniteLaw Ω) (a x : I → ℝ) (β : ℝ) (v : Ω → I → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hx : ∀ i, |x i| ≤ 1)
    (hβ : 0 ≤ β) (hsmall : β ≤ 1 / 64)
    (hcov : ∀ c : I → ℝ, P.mean (fun ω => (∑ i, c i * v ω i) ^ 2) ≤
      8 * ∑ i, c i ^ 2 * P.mean (fun ω => v ω i ^ 2)) :
    P.mean (fun ω => rowLinear a x β (v ω) ^ 2) ≤
      16 * ∑ i, a i ^ 2 * P.mean (fun ω => v ω i ^ 2) := by
  have hs : (∑ i, (a i - 2 * β * a i ^ 2 * x i) ^ 2 * P.mean (fun ω => v ω i ^ 2)) ≤
      2 * ∑ i, a i ^ 2 * P.mean (fun ω => v ω i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hm := mul_le_mul_of_nonneg_right (modified_coefficient_sq (a i) (x i) β (ha i) (hx i) hβ hsmall)
      (P.mean_nonneg (fun ω => sq_nonneg (v ω i)))
    nlinarith
  have hc := hcov (fun i => a i - 2 * β * a i ^ 2 * x i)
  change P.mean (fun ω => rowLinear a x β (v ω) ^ 2) ≤ _ at hc
  linarith

lemma row_drift_dominates_variance {I Ω : Type*} [Fintype I] [Fintype Ω]
    (P : FiniteLaw Ω) (a x : I → ℝ) (β : ℝ) (v : Ω → I → ℝ)
    (hβ : 0 ≤ β)
    (hv : P.mean (fun ω => rowLinear a x β (v ω) ^ 2) ≤
      16 * ∑ i, a i ^ 2 * P.mean (fun ω => v ω i ^ 2)) :
    β / 16 * P.mean (fun ω => rowLinear a x β (v ω) ^ 2) ≤
      P.mean (fun ω => rowQuadratic a β (v ω)) := by
  rw [rowQuadratic_mean]
  have hm := mul_le_mul_of_nonneg_left hv (show 0 ≤ β / 16 by positivity)
  nlinarith

end Komlos.KMFresh

-- END KMProof/RowMoments.lean

-- BEGIN KMProof/RowBounds.lean

namespace Komlos.KMFresh

lemma rowQuadratic_nonneg {I : Type*} [Fintype I] (a v : I → ℝ) (β : ℝ)
    (hβ : 0 ≤ β) : 0 ≤ rowQuadratic a β v := by
  unfold rowQuadratic
  positivity

lemma rowQuadratic_le_one {I : Type*} [Fintype I] (a v : I → ℝ) (β : ℝ)
    (hβ : 0 ≤ β) (hβone : β ≤ 1) (ha : ∀ i, |a i| ≤ 1)
    (hv : ∑ i, v i ^ 2 = 1) : rowQuadratic a β v ≤ 1 := by
  have hs : (∑ i, a i ^ 2 * v i ^ 2) ≤ 1 := by
    rw [← hv]
    apply Finset.sum_le_sum
    intro i _
    have hi := ha i
    have he := sq_abs (a i)
    have h0 := abs_nonneg (a i)
    have hb : a i ^ 2 ≤ 1 := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (sq_nonneg (v i))
  unfold rowQuadratic
  have hn : 0 ≤ ∑ i, a i ^ 2 * v i ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
  nlinarith

lemma modified_coefficient_three (a x β : ℝ) (ha : |a| ≤ 1) (hx : |x| ≤ 1)
    (hβ : 0 ≤ β) (hβone : β ≤ 1) : |a - 2 * β * a ^ 2 * x| ≤ 3 := by
  have h := modified_coefficient_abs a x β ha hx hβ
  have h0 := abs_nonneg a
  have hm := mul_le_mul_of_nonneg_right hβone h0
  nlinarith

lemma rowLinear_abs_bound {I : Type*} [Fintype I] (a x v : I → ℝ) (β : ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hx : ∀ i, |x i| ≤ 1)
    (hβ : 0 ≤ β) (hβone : β ≤ 1) (hv : ∑ i, v i ^ 2 = 1) :
    |rowLinear a x β v| ≤ 3 * Real.sqrt (Fintype.card I : ℝ) := by
  have hc : (∑ i, (a i - 2 * β * a i ^ 2 * x i) ^ 2) ≤ 9 * (Fintype.card I : ℝ) := by
    calc
      _ ≤ ∑ _i : I, (9 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := modified_coefficient_three (a i) (x i) β (ha i) (hx i) hβ hβone
        have h0 := abs_nonneg (a i - 2 * β * a i ^ 2 * x i)
        have he := sq_abs (a i - 2 * β * a i ^ 2 * x i)
        nlinarith
      _ = _ := by simp [mul_comm]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => a i - 2 * β * a i ^ 2 * x i) v
  rw [hv, mul_one] at hh
  change rowLinear a x β v ^ 2 ≤ _ at hh
  have hs := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ Fintype.card I)
  have hp := Real.sqrt_nonneg (Fintype.card I : ℝ)
  have he := sq_abs (rowLinear a x β v)
  have h0 := abs_nonneg (rowLinear a x β v)
  nlinarith

end Komlos.KMFresh

-- END KMProof/RowBounds.lean

-- BEGIN KMProof/RowSymmetry.lean

namespace Komlos.KMFresh

lemma rowLinear_neg {I : Type*} [Fintype I] (a x v : I → ℝ) (β : ℝ) :
    rowLinear a x β (fun i => -v i) = -rowLinear a x β v := by
  simp only [rowLinear, mul_neg, Finset.sum_neg_distrib]

lemma rowQuadratic_neg {I : Type*} [Fintype I] (a v : I → ℝ) (β : ℝ) :
    rowQuadratic a β (fun i => -v i) = rowQuadratic a β v := by
  simp only [rowQuadratic, neg_sq]

lemma row_mixed_odd {I : Type*} [Fintype I] (a x v : I → ℝ) (β : ℝ) :
    rowLinear a x β (fun i => -v i) * rowQuadratic a β (fun i => -v i) =
      -(rowLinear a x β v * rowQuadratic a β v) := by
  rw [rowLinear_neg, rowQuadratic_neg, neg_mul]

lemma rowLinear_mean_zero {I Ω : Type*} [Fintype I] [Fintype Ω]
    (P : FiniteLaw Ω) (a x : I → ℝ) (β : ℝ) (v : Ω → I → ℝ)
    (hm : ∀ c : I → ℝ, P.mean (fun ω => ∑ i, c i * v ω i) = 0) :
    P.mean (fun ω => rowLinear a x β (v ω)) = 0 :=
  hm (fun i => a i - 2 * β * a i ^ 2 * x i)

end Komlos.KMFresh

-- END KMProof/RowSymmetry.lean

-- BEGIN KMProof/SampledRowMoments.lean
noncomputable section
open Matrix Finset
namespace Komlos.KMFresh

lemma matrixSample_square_sum {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (ht : 0 < X.trace) (s : Fin n → Bool) :
    (∑i,(matrixSample hX s i)^2)=1 := by
  rw [←EuclideanSpace.real_norm_sq_eq, matrixSample_norm hX ht]
  norm_num

lemma sampled_row_mean_zero {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (a x : Fin n → ℝ) (β : ℝ) :
    (FiniteLaw.uniform (Fin n → Bool)).mean
      (fun s => rowLinear a x β (fun i => matrixSample hX s i))=0 := by
  apply rowLinear_mean_zero
  intro c
  simpa only [euclidean_inner_sum] using matrixSample_mean hX (WithLp.toLp 2 c)

lemma sampled_row_mixed_zero {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (a x : Fin n → ℝ) (β : ℝ) :
    (FiniteLaw.uniform (Fin n → Bool)).mean
      (fun s => rowLinear a x β (fun i => matrixSample hX s i) *
        rowQuadratic a β (fun i => matrixSample hX s i))=0 := by
  apply uniform_odd_mean
  intro s
  simp only [matrixSample_negate, PiLp.neg_apply]
  exact row_mixed_odd a x (fun i => matrixSample hX s i) β

lemma sampled_row_drift {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (ht : 0 < X.trace)
    (hbase : ((8:ℝ) • Matrix.diagonal X.diag-X).PosSemidef)
    (a x : Fin n → ℝ) {β : ℝ} (hβ : 0 ≤ β) (hsmall : β ≤ 1/64)
    (ha : ∀i,|a i| ≤ 1) (hx : ∀i,|x i| ≤ 1) :
    β/16*(FiniteLaw.uniform (Fin n → Bool)).mean
      (fun s => rowLinear a x β (fun i => matrixSample hX s i)^2) ≤
    (FiniteLaw.uniform (Fin n → Bool)).mean
      (fun s => rowQuadratic a β (fun i => matrixSample hX s i)) := by
  apply row_drift_dominates_variance _ _ _ _ _ hβ
  exact rowLinear_variance _ a x β _ ha hx hβ hsmall
    (fun c => matrixSample_variance_bound hX ht 8 hbase c)
end Komlos.KMFresh

-- END KMProof/SampledRowMoments.lean

-- BEGIN KMProof/ScaleDirectionProperties.lean

open Matrix
open scoped RealInnerProductSpace

namespace Komlos.KMFresh

lemma chosenScaleMatrix_trace_pos {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (s : AdaptiveState (Fin (q + 1) × R) n) (hs : scaleRunning A q ρ μ s) :
    0 < (chooseScaleMatrix A q ρ μ β ha hA hμ s hs).matrix.trace := by
  rw [(chooseScaleMatrix A q ρ μ β ha hA hμ s hs).trace]
  have hp : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  have hc : (0 : ℝ) < (aliveSet ρ s.x).card := lt_trans (by positivity : (0 : ℝ) < 16 * ((q + 1 : ℕ) : ℝ)) hs.1
  positivity

lemma scaleDirection_geometry {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (s : AdaptiveState (Fin (q + 1) × R) n) (hs : scaleRunning A q ρ μ s) (ω : Fin n → Bool) :
    (∑ i, (scaleDirection A q ρ μ β ha hA hμ s ω i)^2) = 1 ∧
    (∀ i, i ∉ aliveSet ρ s.x → scaleDirection A q ρ μ β ha hA hμ s ω i = 0) ∧
    (∑ i, s.x i * scaleDirection A q ρ μ β ha hA hμ s ω i) = 0 ∧
    ∀ z ∈ scaleLarge A q ρ s.x,
      (∑ i, scaleRows A q z i * scaleDirection A q ρ μ β ha hA hμ s ω i) = 0 := by
  rw [scaleDirection_running A q ρ μ β ha hA hμ s hs ω]
  let D := chooseScaleMatrix A q ρ μ β ha hA hμ s hs
  refine ⟨matrixSample_square_sum D.psd (chosenScaleMatrix_trace_pos A q ρ μ β ha hA hμ s hs) ω,
    ?_, ?_, ?_⟩
  · intro i hi
    have he := matrixSample_kernel D.psd (EuclideanSpace.single i (1 : ℝ)) (D.frozen i hi) ω
    simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using he
  · have he := matrixSample_kernel D.psd (WithLp.toLp 2 s.x) D.state ω
    simpa only [euclidean_inner_sum] using he
  · intro z hz
    have he := matrixSample_kernel D.psd (WithLp.toLp 2 (scaleRows A q z)) (D.large z hz) ω
    simpa only [euclidean_inner_sum] using he

lemma scaleDirection_dangerous {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (s : AdaptiveState (Fin (q + 1) × R) n) (hs : scaleRunning A q ρ μ s) (ω : Fin n → Bool)
    (z : Fin (q + 1) × R)
    (hz : z ∈ scaleDangerous (fun p r i => scaleEntry q p (A r i)) ρ
      (fun p => (4 : ℝ)^p.val) μ s) :
    (∑ i, (scaleRows A q z i - 2 * β z.1 * (scaleRows A q z i)^2 * s.x i) *
      scaleDirection A q ρ μ β ha hA hμ s ω i) = 0 := by
  rw [scaleDirection_running A q ρ μ β ha hA hμ s hs ω]
  let D := chooseScaleMatrix A q ρ μ β ha hA hμ s hs
  have he := matrixSample_kernel D.psd
    (WithLp.toLp 2 (fun i => scaleRows A q z i - 2 * β z.1 * (scaleRows A q z i)^2 * s.x i))
    (D.dangerous z hz) ω
  simpa only [euclidean_inner_sum] using he

end Komlos.KMFresh

-- END KMProof/ScaleDirectionProperties.lean

-- BEGIN KMProof/PhaseIncrement.lean

namespace Komlos.KMFresh

lemma phasePotential_next_cap {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b lam : R → ℝ) (s : AdaptiveState R n) (r : R)
    (hl : ¬rowLarge A ρ k s.x r)
    (hhit : r ∈ s.hit → 2 * b r ≤ rowRegularizer A ρ β s.x r) :
    phasePotential A ρ k μ β b lam s r ≤
      cappedExponential (lam r) (2 * b r) (rowRegularizer A ρ β s.x r) := by
  classical
  by_cases hh : r ∈ s.hit
  · rw [phasePotential_hit A ρ k μ β b lam s r hh]
    simp only [cappedExponential, min_eq_right (hhit hh)]
    exact le_rfl
  · simp only [phasePotential, if_neg hh, if_neg hl]
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl

lemma phasePotential_medium_increment {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b lam : R → ℝ) (s s' : AdaptiveState R n) (r : R) (Δ : ℝ)
    (hr : r ∉ s.hit) (hm : rowMedium A ρ k μ s.x r)
    (hl' : ¬rowLarge A ρ k s'.x r)
    (hhit' : r ∈ s'.hit → 2 * b r ≤ rowRegularizer A ρ β s'.x r)
    (hlam : 0 ≤ lam r) (hz : rowRegularizer A ρ β s.x r ≤ 2 * b r)
    (hz' : rowRegularizer A ρ β s'.x r ≤ rowRegularizer A ρ β s.x r + Δ)
    (hΔ : |lam r * Δ| ≤ 1) :
    phasePotential A ρ k μ β b lam s' r - phasePotential A ρ k μ β b lam s r ≤
      (lam r * Real.exp (lam r * rowRegularizer A ρ β s.x r)) * (Δ + lam r * Δ^2) := by
  have hn := phasePotential_next_cap A ρ k μ β b lam s' r hl' hhit'
  rw [phasePotential_medium A ρ k μ β b lam s r hr hm]
  exact (sub_le_sub_right hn _).trans (capped_exponential_increment hlam hz hz' hΔ)

lemma phasePotential_hit_increment {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b lam : R → ℝ) (s s' : AdaptiveState R n) (r : R)
    (hh : r ∈ s.hit) (hmono : s.hit ⊆ s'.hit) :
    phasePotential A ρ k μ β b lam s' r - phasePotential A ρ k μ β b lam s r = 0 := by
  rw [phasePotential_hit A ρ k μ β b lam s' r (hmono hh),
    phasePotential_hit A ρ k μ β b lam s r hh, sub_self]

lemma phasePotential_activation_bound {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b lam : R → ℝ) (s : AdaptiveState R n) (r : R)
    (hh : r ∉ s.hit) (hlam : 0 ≤ lam r)
    (hz : rowRegularizer A ρ β s.x r ≤ b r) :
    phasePotential A ρ k μ β b lam s r ≤ Real.exp (lam r * b r) := by
  classical
  simp only [phasePotential, if_neg hh]
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hz) hlam

end Komlos.KMFresh

-- END KMProof/PhaseIncrement.lean

-- BEGIN KMProof/AdaptiveInvariants.lean

namespace Komlos.KMFresh

lemma adaptiveStep_stopped {R Ω : Type*} [Fintype R] {n : ℕ}
    (running : AdaptiveState R n → Prop)
    (direction : AdaptiveState R n → Ω → Fin n → ℝ)
    (newHit : (Fin n → ℝ) → R → Prop) (t : ℝ)
    (s : AdaptiveState R n) (ω : Ω) (h : ¬running s) :
    adaptiveStep running direction newHit t s ω = s := by
  classical
  simp only [adaptiveStep, if_neg h]

lemma adaptiveStep_box {R Ω : Type*} [Fintype R] {n : ℕ}
    (running : AdaptiveState R n → Prop)
    (direction : AdaptiveState R n → Ω → Fin n → ℝ)
    (newHit : (Fin n → ℝ) → R → Prop) (t ρ : ℝ)
    (s : AdaptiveState R n) (ω : Ω) (ht : 0 ≤ t) (htρ : t ≤ ρ)
    (hx : ∀ i, |s.x i| ≤ 1)
    (hunit : running s → ∑ i, direction s ω i ^ 2 = 1)
    (hsupport : running s → ∀ i, i ∉ aliveSet ρ s.x → direction s ω i = 0) :
    ∀ i, |(adaptiveStep running direction newHit t s ω).x i| ≤ 1 := by
  classical
  by_cases hr : running s
  · rw [adaptiveStep_x running direction newHit t s ω hr]
    exact supported_step_box ρ t s.x (direction s ω) ht htρ hx (hunit hr) (hsupport hr)
  · rw [adaptiveStep_stopped running direction newHit t s ω hr]
    exact hx

lemma adaptiveStep_energy {R Ω : Type*} [Fintype R] {n : ℕ}
    (running : AdaptiveState R n → Prop)
    (direction : AdaptiveState R n → Ω → Fin n → ℝ)
    (newHit : (Fin n → ℝ) → R → Prop) (t : ℝ)
    (s : AdaptiveState R n) (ω : Ω) (hr : running s)
    (hortho : ∑ i, s.x i * direction s ω i = 0)
    (hunit : ∑ i, direction s ω i ^ 2 = 1) :
    ∑ i, (adaptiveStep running direction newHit t s ω).x i ^ 2 =
      (∑ i, s.x i ^ 2) + t ^ 2 := by
  rw [adaptiveStep_x running direction newHit t s ω hr]
  exact square_mass_step s.x (direction s ω) t hortho hunit

end Komlos.KMFresh

-- END KMProof/AdaptiveInvariants.lean

-- BEGIN KMProof/RegularizedStep.lean

namespace Komlos.KMFresh

lemma adaptiveStep_hit_iff {R Ω : Type*} [Fintype R] {n : ℕ}
    (running : AdaptiveState R n → Prop)
    (direction : AdaptiveState R n → Ω → Fin n → ℝ)
    (newHit : (Fin n → ℝ) → R → Prop) (t : ℝ)
    (s : AdaptiveState R n) (ω : Ω) (hrun : running s) (r : R) :
    r ∈ (adaptiveStep running direction newHit t s ω).hit ↔
      r ∈ s.hit ∨ newHit (fun i => s.x i + t * direction s ω i) r := by
  classical
  simp only [adaptiveStep, if_pos hrun, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]

lemma adaptive_regularized_new_hit {R Ω : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (ρ : ℝ) (k μ β b : R → ℝ)
    (running : AdaptiveState R n → Prop)
    (direction : AdaptiveState R n → Ω → Fin n → ℝ) (t : ℝ)
    (s : AdaptiveState R n) (ω : Ω) (hrun : running s) (r : R)
    (hr : r ∉ s.hit)
    (hh : r ∈ (adaptiveStep running direction (regularizedHit A ρ k μ β b) t s ω).hit) :
    2 * b r ≤ rowRegularizer A ρ β
      (adaptiveStep running direction (regularizedHit A ρ k μ β b) t s ω).x r := by
  have he := (adaptiveStep_hit_iff running direction (regularizedHit A ρ k μ β b)
    t s ω hrun r).mp hh
  have hz := (he.resolve_left hr).2
  rw [adaptiveStep_x running direction (regularizedHit A ρ k μ β b) t s ω hrun]
  exact hz

lemma adaptive_regularized_medium_increment {R Ω : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (ρ : ℝ) (k μ β b lam : R → ℝ)
    (running : AdaptiveState R n → Prop)
    (direction : AdaptiveState R n → Ω → Fin n → ℝ) (t : ℝ)
    (s : AdaptiveState R n) (ω : Ω) (hrun : running s) (r : R) (Δ : ℝ)
    (hr : r ∉ s.hit) (hm : rowMedium A ρ k μ s.x r)
    (hl' : ¬rowLarge A ρ k
      (adaptiveStep running direction (regularizedHit A ρ k μ β b) t s ω).x r)
    (hlam : 0 ≤ lam r) (hz : rowRegularizer A ρ β s.x r ≤ 2 * b r)
    (hz' : rowRegularizer A ρ β
      (adaptiveStep running direction (regularizedHit A ρ k μ β b) t s ω).x r ≤
      rowRegularizer A ρ β s.x r + Δ) (hΔ : |lam r * Δ| ≤ 1) :
    phasePotential A ρ k μ β b lam
      (adaptiveStep running direction (regularizedHit A ρ k μ β b) t s ω) r -
      phasePotential A ρ k μ β b lam s r ≤
      (lam r * Real.exp (lam r * rowRegularizer A ρ β s.x r)) * (Δ + lam r * Δ^2) := by
  apply phasePotential_medium_increment A ρ k μ β b lam s _ r Δ hr hm hl'
    (fun hh => adaptive_regularized_new_hit A ρ k μ β b running direction t s ω hrun r hr hh)
    hlam hz hz' hΔ

end Komlos.KMFresh

-- END KMProof/RegularizedStep.lean

-- BEGIN KMProof/RegularizerBounds.lean

namespace Komlos.KMFresh

lemma rowRegularizer_le_energy {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (β : R → ℝ) (x : Fin n → ℝ) (r : R) (hβ : 0 ≤ β r) :
    rowRegularizer A ρ β x r ≤ rowDiscrepancy A x r + β r * rowEnergy A ρ x r := by
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hβ
  apply Finset.sum_le_sum
  intro i _
  have hh := mul_le_mul_of_nonneg_left (show 1 - x i ^ 2 ≤ 1 by nlinarith [sq_nonneg (x i)])
    (sq_nonneg (A r i))
  simpa only [mul_one] using hh

lemma rowRegularizer_activation {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k β b : R → ℝ) (x : Fin n → ℝ) (r : R)
    (hβ : 0 ≤ β r) (hbudget : β r * (64 * k r) ≤ b r)
    (hdisc : rowDiscrepancy A x r = 0) (hl : ¬rowLarge A ρ k x r) :
    rowRegularizer A ρ β x r ≤ b r := by
  have he := rowRegularizer_le_energy A ρ β x r hβ
  rw [hdisc, zero_add] at he
  exact he.trans ((mul_le_mul_of_nonneg_left (le_of_not_gt hl) hβ).trans hbudget)

end Komlos.KMFresh

-- END KMProof/RegularizerBounds.lean

-- BEGIN KMProof/BlockedRows.lean

namespace Komlos.KMFresh

lemma rowDiscrepancy_step {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (x v : Fin n → ℝ) (t : ℝ) (r : R) :
    rowDiscrepancy A (fun i => x i + t * v i) r =
      rowDiscrepancy A x r + t * ∑ i, A r i * v i := by
  unfold rowDiscrepancy
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma blocked_row_unchanged {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (x v : Fin n → ℝ) (t : ℝ) (r : R) (hblock : ∑ i, A r i * v i = 0) :
    rowDiscrepancy A (fun i => x i + t * v i) r = rowDiscrepancy A x r := by
  rw [rowDiscrepancy_step, hblock, mul_zero, add_zero]

lemma blocked_regularizer_decreases {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Finset I) (a x v : I → ℝ) (t β : ℝ)
    (hBA : B ⊆ A) (hβ : 0 ≤ β)
    (hy : ∀ i ∈ A, |x i + t * v i| ≤ 1)
    (hsupport : ∀ i, i ∉ A → v i = 0)
    (hblock : ∑ i ∈ A, (a i - 2 * β * a i ^ 2 * x i) * v i = 0) :
    activeRegularizer B a (fun i => x i + t * v i) β ≤ activeRegularizer A a x β := by
  have he := activeRegularizer_step A a x v t β hsupport
  rw [hblock, mul_zero, zero_sub] at he
  have hQ : 0 ≤ ∑ i ∈ A, β * a i ^ 2 * v i ^ 2 := by
    exact Finset.sum_nonneg (fun i _ => by positivity)
  have hdec : activeRegularizer A a (fun i => x i + t * v i) β ≤ activeRegularizer A a x β := by
    nlinarith [mul_nonneg (sq_nonneg t) hQ]
  exact (activeRegularizer_freeze A B a _ β hBA hβ hy).trans hdec

end Komlos.KMFresh

-- END KMProof/BlockedRows.lean

-- BEGIN KMProof/RowStateInvariant.lean

namespace Komlos.KMFresh

noncomputable def rowStateValid {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b : R → ℝ) (s : AdaptiveState R n) : Prop :=
  (∀ i, |s.x i| ≤ 1) ∧
  (∀ r, rowLarge A ρ k s.x r → rowDiscrepancy A s.x r = 0) ∧
  ∀ r, rowMedium A ρ k μ s.x r → r ∉ s.hit → rowRegularizer A ρ β s.x r < 2 * b r

lemma rowStateValid_initial {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b : R → ℝ) (hβ : ∀ r, 0 ≤ β r) (hb : ∀ r, 0 < b r)
    (hbudget : ∀ r, β r * (64 * k r) ≤ b r) :
    rowStateValid A ρ k μ β b ⟨0, ∅⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp
  · intro r _
    simp [rowDiscrepancy]
  · intro r hm _
    have hd : rowDiscrepancy A (0 : Fin n → ℝ) r = 0 := by simp [rowDiscrepancy]
    have hz := rowRegularizer_activation A ρ k β b 0 r (hβ r) (hbudget r) hd (not_lt_of_ge hm.2)
    exact hz.trans_lt (by linarith [hb r])

lemma rowStateValid_step {R Ω : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (ρ : ℝ) (k μ β b : R → ℝ)
    (running : AdaptiveState R n → Prop)
    (direction : AdaptiveState R n → Ω → Fin n → ℝ) (t : ℝ)
    (s : AdaptiveState R n) (ω : Ω) (hs : rowStateValid A ρ k μ β b s)
    (ht : 0 ≤ t) (htρ : t ≤ ρ)
    (hunit : running s → ∑ i, direction s ω i ^ 2 = 1)
    (hsupp : running s → ∀ i, i ∉ aliveSet ρ s.x → direction s ω i = 0)
    (hblock : running s → ∀ r, rowLarge A ρ k s.x r → ∑ i, A r i * direction s ω i = 0) :
    rowStateValid A ρ k μ β b
      (adaptiveStep running direction (regularizedHit A ρ k μ β b) t s ω) := by
  classical
  by_cases hrun : running s
  · have hfix : ∀ i, i ∉ aliveSet ρ s.x → s.x i + t * direction s ω i = s.x i := by
      intro i hi
      rw [hsupp hrun i hi, mul_zero, add_zero]
    refine ⟨adaptiveStep_box running direction (regularizedHit A ρ k μ β b) t ρ s ω ht htρ hs.1 hunit hsupp,
      ?_, ?_⟩
    · intro r hr
      rw [adaptiveStep_x running direction (regularizedHit A ρ k μ β b) t s ω hrun] at hr ⊢
      have hold : rowLarge A ρ k s.x r := by
        by_contra hn
        exact rowLarge_no_reentry A ρ k s.x _ r hfix hn hr
      rw [blocked_row_unchanged A s.x (direction s ω) t r (hblock hrun r hold)]
      exact hs.2.1 r hold
    · intro r hm hnot
      by_contra hn
      have hnew : regularizedHit A ρ k μ β b
          (adaptiveStep running direction (regularizedHit A ρ k μ β b) t s ω).x r :=
        ⟨hm, le_of_not_gt hn⟩
      rw [adaptiveStep_x running direction (regularizedHit A ρ k μ β b) t s ω hrun] at hnew
      exact hnot ((adaptiveStep_hit_iff running direction (regularizedHit A ρ k μ β b)
        t s ω hrun r).mpr (Or.inr hnew))
  · rw [adaptiveStep_stopped running direction (regularizedHit A ρ k μ β b) t s ω hrun]
    exact hs

end Komlos.KMFresh

-- END KMProof/RowStateInvariant.lean

-- BEGIN KMProof/AdaptiveHistory.lean

namespace Komlos.KMFresh

lemma adaptiveHistory_snoc {S Ω : Type*} (initial : S)
    (step : ℕ → S → Ω → S) (k : ℕ) (h : Fin k → Ω) (ω : Ω) :
    adaptiveHistory initial step (k + 1) (Fin.snoc h ω) =
      step k (adaptiveHistory initial step k h) ω := by
  simp [adaptiveHistory]

lemma adaptiveHistory_invariant {S Ω : Type*} (initial : S)
    (step : ℕ → S → Ω → S) (P : ℕ → S → Prop) (h0 : P 0 initial)
    (hs : ∀ k s ω, P k s → P (k + 1) (step k s ω)) :
    ∀ k h, P k (adaptiveHistory initial step k h) := by
  intro k
  induction k with
  | zero => intro h; exact h0
  | succ k ih =>
    intro h
    exact hs k _ _ (ih (Fin.init h))

lemma adaptiveHistory_stops {S Ω : Type*} (initial : S)
    (step : ℕ → S → Ω → S) (running : S → Prop) (energy : S → ℝ)
    (ε M : ℝ) (N : ℕ) (h0 : 0 ≤ energy initial)
    (habsorbed : ∀ k s ω, ¬running s → ¬running (step k s ω))
    (hgrowth : ∀ k s ω, running s → energy (step k s ω) = energy s + ε)
    (hbound : ∀ h, energy (adaptiveHistory initial step N h) ≤ M)
    (hN : M < N * ε) :
    ∀ h, ¬running (adaptiveHistory initial step N h) := by
  have hi : ∀ k h, ¬running (adaptiveHistory initial step k h) ∨
      (k : ℝ) * ε ≤ energy (adaptiveHistory initial step k h) := by
    apply adaptiveHistory_invariant initial step
      (fun k s => ¬running s ∨ (k : ℝ) * ε ≤ energy s)
    · exact Or.inr (by simpa using h0)
    · intro k s ω hs
      rcases hs with hs | hs
      · exact Or.inl (habsorbed k s ω hs)
      · by_cases hr : running s
        · apply Or.inr
          rw [hgrowth k s ω hr]
          push_cast
          linarith
        · exact Or.inl (habsorbed k s ω hr)
  intro h hr
  rcases hi N h with hn | hn
  · exact hn hr
  · have hb := hbound h
    linarith

end Komlos.KMFresh

-- END KMProof/AdaptiveHistory.lean

-- BEGIN KMProof/ScaleHistory.lean

namespace Komlos.KMFresh

noncomputable def scaleStep {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) : AdaptiveState (Fin (q + 1) × R) n → (Fin n → Bool) → AdaptiveState (Fin (q + 1) × R) n :=
  adaptiveStep (scaleRunning A q ρ μ) (scaleDirection A q ρ μ β ha hA hμ)
    (regularizedHit (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1)) t

noncomputable def scaleHistory {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) : (k : ℕ) → (Fin k → (Fin n → Bool)) → AdaptiveState (Fin (q + 1) × R) n :=
  adaptiveHistory ⟨0, ∅⟩ (fun _ => scaleStep A q ρ μ β b ha hA hμ t)

lemma scaleStep_valid {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) (ht : 0 ≤ t) (htρ : t ≤ ρ)
    (s : AdaptiveState (Fin (q + 1) × R) n) (ω : Fin n → Bool)
    (hs : rowStateValid (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1) s) :
    rowStateValid (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1)
      (scaleStep A q ρ μ β b ha hA hμ t s ω) := by
  apply rowStateValid_step (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
    (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1)
    (scaleRunning A q ρ μ) (scaleDirection A q ρ μ β ha hA hμ) t s ω hs ht htρ
  · intro hr
    exact (scaleDirection_geometry A q ρ μ β ha hA hμ s hr ω).1
  · intro hr
    exact (scaleDirection_geometry A q ρ μ β ha hA hμ s hr ω).2.1
  · intro hr z hz
    apply (scaleDirection_geometry A q ρ μ β ha hA hμ s hr ω).2.2.2 z
    classical
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩

end Komlos.KMFresh

-- END KMProof/ScaleHistory.lean

-- BEGIN KMProof/PhaseStepBound.lean

namespace Komlos.KMFresh

noncomputable def phaseProxyWeight {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β lam : R → ℝ) (s : AdaptiveState R n) (r : R) : ℝ := by
  classical
  exact if rowMedium A ρ k μ s.x r ∧ r ∉ s.hit then
    lam r * Real.exp (lam r * rowRegularizer A ρ β s.x r) else 0

lemma phase_step_bound {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b lam : R → ℝ) (s s' : AdaptiveState R n) (r : R) (Δ : ℝ)
    (hs : rowStateValid A ρ k μ β b s)
    (hhit : r ∈ s'.hit ↔ r ∈ s.hit ∨ regularizedHit A ρ k μ β b s'.x r)
    (henergy : rowEnergy A ρ s'.x r ≤ rowEnergy A ρ s.x r)
    (hlarge : rowLarge A ρ k s.x r → rowDiscrepancy A s'.x r = 0)
    (hβ : 0 ≤ β r) (hb : 0 < b r) (hbudget : β r * (64 * k r) ≤ b r)
    (hlam : 0 ≤ lam r)
    (hinc : rowRegularizer A ρ β s'.x r ≤ rowRegularizer A ρ β s.x r + Δ)
    (hΔ : |lam r * Δ| ≤ 1) :
    phasePotential A ρ k μ β b lam s' r - phasePotential A ρ k μ β b lam s r ≤
      phaseProxyWeight A ρ k μ β lam s r * (Δ + lam r * Δ^2) := by
  classical
  by_cases hh : r ∈ s.hit
  · have hh' := hhit.mpr (Or.inl hh)
    rw [phasePotential_hit A ρ k μ β b lam s' r hh',
      phasePotential_hit A ρ k μ β b lam s r hh, sub_self]
    simp only [phaseProxyWeight, hh, not_true_eq_false, and_false, if_false, zero_mul]
    exact le_rfl
  have hnew : r ∈ s'.hit → regularizedHit A ρ k μ β b s'.x r :=
    fun h => (hhit.mp h).resolve_left hh
  by_cases hl : rowLarge A ρ k s.x r
  · have hnotm : ¬rowMedium A ρ k μ s.x r := fun hm => not_lt_of_ge hm.2 hl
    simp only [phaseProxyWeight, hnotm, false_and, if_false, zero_mul]
    have hold : phasePotential A ρ k μ β b lam s r = Real.exp (lam r * b r) := by
      simp only [phasePotential, if_neg hh, if_pos hl]
    rw [hold]
    apply sub_nonpos.mpr
    by_cases hl' : rowLarge A ρ k s'.x r
    · have hn : r ∉ s'.hit := fun hr => not_lt_of_ge (hnew hr).1.2 hl'
      simp only [phasePotential, if_neg hn, if_pos hl']
      exact le_rfl
    · have hz := rowRegularizer_activation A ρ k β b s'.x r hβ hbudget (hlarge hl) hl'
      have hn : r ∉ s'.hit := by
        intro hr
        have he := (hnew hr).2
        linarith
      exact phasePotential_activation_bound A ρ k μ β b lam s' r hn hlam hz
  have hl' : ¬rowLarge A ρ k s'.x r := by
    have he : rowEnergy A ρ s.x r ≤ 64 * k r := le_of_not_gt hl
    exact not_lt_of_ge (henergy.trans he)
  by_cases ht : rowTiny A ρ μ s.x r
  · have ht' : rowTiny A ρ μ s'.x r := henergy.trans ht
    have hn : r ∉ s'.hit := fun hr => not_lt_of_ge ht' (hnew hr).1.1
    have hm : ¬rowMedium A ρ k μ s.x r := fun hm => not_lt_of_ge ht hm.1
    simp only [phasePotential, if_neg hh, if_neg hn, if_neg hl, if_neg hl', if_pos ht,
      if_pos ht', sub_self, phaseProxyWeight, hm, false_and, if_false, zero_mul]
    exact le_rfl
  · have hm : rowMedium A ρ k μ s.x r := ⟨lt_of_not_ge ht, le_of_not_gt hl⟩
    rw [phaseProxyWeight, if_pos ⟨hm, hh⟩]
    exact phasePotential_medium_increment A ρ k μ β b lam s s' r Δ hh hm hl'
      (fun hr => (hnew hr).2) hlam (hs.2.2 r hm hh).le hinc hΔ

end Komlos.KMFresh

-- END KMProof/PhaseStepBound.lean

-- BEGIN KMProof/ActualRowIncrement.lean

namespace Komlos.KMFresh

lemma supported_rowLinear {n : ℕ} (S : Finset (Fin n)) (a x v : Fin n → ℝ) (β : ℝ)
    (hs : ∀ i, i ∉ S → v i = 0) :
    rowLinear a x β v = ∑ i ∈ S, (a i - 2 * β * a i ^ 2 * x i) * v i := by
  unfold rowLinear
  apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
  intro i _ hi
  rw [hs i hi, mul_zero]

lemma supported_rowQuadratic {n : ℕ} (S : Finset (Fin n)) (a v : Fin n → ℝ) (β : ℝ)
    (hs : ∀ i, i ∉ S → v i = 0) :
    rowQuadratic a β v = ∑ i ∈ S, β * a i ^ 2 * v i ^ 2 := by
  unfold rowQuadratic
  rw [Finset.mul_sum]
  simp only [mul_assoc]
  apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
  intro i _ hi
  simp only [hs i hi, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]

lemma actual_row_increment {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (β : R → ℝ) (x v : Fin n → ℝ) (t : ℝ) (r : R)
    (hβ : 0 ≤ β r) (hy : ∀ i, |x i + t * v i| ≤ 1)
    (hs : ∀ i, i ∉ aliveSet ρ x → v i = 0) :
    rowRegularizer A ρ β (fun i => x i + t * v i) r ≤
      rowRegularizer A ρ β x r + t * rowLinear (A r) x (β r) v -
        t ^ 2 * rowQuadratic (A r) (β r) v := by
  have he := activeRegularizer_step (aliveSet ρ x) (A r) x v t (β r) hs
  rw [← supported_rowLinear (aliveSet ρ x) (A r) x v (β r) hs,
    ← supported_rowQuadratic (aliveSet ρ x) (A r) v (β r) hs] at he
  have hf := activeRegularizer_freeze (aliveSet ρ x) (aliveSet ρ (fun i => x i + t * v i))
    (A r) (fun i => x i + t * v i) (β r) (supported_step_alive ρ t x v hs) hβ (fun i _ => hy i)
  change rowRegularizer A ρ β (fun i => x i + t * v i) r ≤ _ at hf
  change activeRegularizer (aliveSet ρ x) (A r) (fun i => x i + t * v i) (β r) -
    rowRegularizer A ρ β x r = _ at he
  linarith

end Komlos.KMFresh

-- END KMProof/ActualRowIncrement.lean

-- BEGIN KMProof/ActualPhaseStep.lean

namespace Komlos.KMFresh

lemma phaseProxyWeight_bound {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b lam : R → ℝ) (s : AdaptiveState R n) (r : R)
    (hs : rowStateValid A ρ k μ β b s) (hlam : 0 ≤ lam r) :
    0 ≤ phaseProxyWeight A ρ k μ β lam s r ∧
      phaseProxyWeight A ρ k μ β lam s r ≤ lam r * Real.exp (lam r * (2 * b r)) := by
  classical
  unfold phaseProxyWeight
  split_ifs with hm
  · exact exponential_weight_bound hlam (hs.2.2 r hm.1 hm.2).le
  · exact ⟨le_rfl, mul_nonneg hlam (Real.exp_pos _).le⟩

lemma actual_phase_step_bound {R Ω : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (ρ : ℝ) (k μ β b lam : R → ℝ)
    (running : AdaptiveState R n → Prop)
    (direction : AdaptiveState R n → Ω → Fin n → ℝ) (t : ℝ)
    (s : AdaptiveState R n) (ω : Ω) (hrun : running s) (r : R)
    (hs : rowStateValid A ρ k μ β b s) (ht : 0 ≤ t) (htρ : t ≤ ρ)
    (hunit : ∑ i, direction s ω i ^ 2 = 1)
    (hsupp : ∀ i, i ∉ aliveSet ρ s.x → direction s ω i = 0)
    (hblock : rowLarge A ρ k s.x r → ∑ i, A r i * direction s ω i = 0)
    (hβ : 0 ≤ β r) (hb : 0 < b r) (hbudget : β r * (64 * k r) ≤ b r)
    (hlam : 0 ≤ lam r)
    (hΔ : |lam r * (t * rowLinear (A r) s.x (β r) (direction s ω) -
      t^2 * rowQuadratic (A r) (β r) (direction s ω))| ≤ 1) :
    phasePotential A ρ k μ β b lam
      (adaptiveStep running direction (regularizedHit A ρ k μ β b) t s ω) r -
      phasePotential A ρ k μ β b lam s r ≤
    phaseProxyWeight A ρ k μ β lam s r *
      ((t * rowLinear (A r) s.x (β r) (direction s ω) -
        t^2 * rowQuadratic (A r) (β r) (direction s ω)) +
        lam r * (t * rowLinear (A r) s.x (β r) (direction s ω) -
          t^2 * rowQuadratic (A r) (β r) (direction s ω))^2) := by
  have hy := supported_step_box ρ t s.x (direction s ω) ht htρ hs.1 hunit hsupp
  have hfix : ∀ i, i ∉ aliveSet ρ s.x → s.x i + t * direction s ω i = s.x i := by
    intro i hi
    rw [hsupp i hi, mul_zero, add_zero]
  apply phase_step_bound A ρ k μ β b lam s _ r _ hs
  · simpa only [adaptiveStep_x running direction (regularizedHit A ρ k μ β b) t s ω hrun] using
      adaptiveStep_hit_iff running direction (regularizedHit A ρ k μ β b) t s ω hrun r
  · rw [adaptiveStep_x running direction (regularizedHit A ρ k μ β b) t s ω hrun]
    exact rowEnergy_decreases A ρ s.x _ r hfix
  · intro hl
    rw [adaptiveStep_x running direction (regularizedHit A ρ k μ β b) t s ω hrun,
      blocked_row_unchanged A s.x (direction s ω) t r (hblock hl)]
    exact hs.2.1 r hl
  · exact hβ
  · exact hb
  · exact hbudget
  · exact hlam
  · rw [adaptiveStep_x running direction (regularizedHit A ρ k μ β b) t s ω hrun]
    have he := actual_row_increment A ρ β s.x (direction s ω) t r hβ hy hsupp
    linarith
  · exact hΔ

end Komlos.KMFresh

-- END KMProof/ActualPhaseStep.lean

-- BEGIN KMProof/AffineCovariance.lean
noncomputable section
open Finset Matrix
namespace Komlos.KMFresh

lemma quadratic_congruence {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ) :
    quadratic (A*X*A.transpose) c=quadratic X (c ᵥ* A) := by
  unfold quadratic
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.mulVec_transpose]

lemma matrixSample_affine_covariance {n m : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (ht : 0<X.trace) (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) :
    (FiniteLaw.uniform (Fin n → Bool)).mean
      (fun s => (∑j,c j*(A *ᵥ (fun i => matrixSample hX s i)) j)^2)=
        quadratic (A*X*A.transpose) c/X.trace := by
  have he (s : Fin n → Bool) : (∑j,c j*(A *ᵥ (fun i => matrixSample hX s i)) j)=
      ∑i,(c ᵥ* A) i*matrixSample hX s i :=
    Matrix.dotProduct_mulVec c A (fun i => matrixSample hX s i)
  simp_rw [he]
  rw [matrixSample_sum_covariance hX ht,quadratic_congruence]

lemma covariance_diagonal_domination {Ω : Type*} [Fintype Ω] {m : ℕ}
    (P : FiniteLaw Ω) (v : Ω → Fin m → ℝ) (Y : Matrix (Fin m) (Fin m) ℝ)
    {T : ℝ} (hT : 0<T)
    (hc : ∀a:Fin m→ℝ,P.mean (fun ω => (∑i,a i*v ω i)^2)=quadratic Y a/T)
    (t : ℝ) (hd : (t • Matrix.diagonal Y.diag-Y).PosSemidef) (a : Fin m → ℝ) :
    P.mean (fun ω => (∑i,a i*v ω i)^2)≤t*(∑i,(a i)^2*P.mean (fun ω => (v ω i)^2)) := by
  have hv (i : Fin m) : P.mean (fun ω => (v ω i)^2)=Y i i/T := by
    simpa [quadratic,Pi.single_apply] using hc (Pi.single i 1)
  rw [hc]
  simp_rw [hv]
  have hh := div_le_div_of_nonneg_right (quadratic_diagonal_bound Y t hd a) hT.le
  apply hh.trans_eq
  rw [Finset.mul_sum,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma matrixSample_affine_variance {n m : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (ht : 0<X.trace) (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ)
    (hd : (t • Matrix.diagonal (A*X*A.transpose).diag-A*X*A.transpose).PosSemidef)
    (c : Fin m → ℝ) :
    (FiniteLaw.uniform (Fin n → Bool)).mean
      (fun s => (∑j,c j*(A *ᵥ (fun i => matrixSample hX s i)) j)^2)≤
      t*(∑j,(c j)^2*(FiniteLaw.uniform (Fin n → Bool)).mean
        (fun s => ((A *ᵥ (fun i => matrixSample hX s i)) j)^2)) :=
  covariance_diagonal_domination (FiniteLaw.uniform _) _ _ ht
    (matrixSample_affine_covariance hX ht A) t hd c
end Komlos.KMFresh

-- END KMProof/AffineCovariance.lean

-- BEGIN KMProof/ProxyMoments.lean
noncomputable section
namespace Komlos.KMFresh

def scalarIncrement (ε L Q : ℝ) : ℝ := Real.sqrt ε*L-ε*Q
def scalarProxy (ε lam L Q : ℝ) : ℝ :=
  scalarIncrement ε L Q+lam*(scalarIncrement ε L Q)^2

lemma scalarProxy_expansion {ε : ℝ} (hε : 0≤ε) (lam L Q : ℝ) :
    scalarProxy ε lam L Q = Real.sqrt ε*L-ε*Q+lam*ε*L^2-
      (2*lam*Real.sqrt ε*ε)*(L*Q)+(lam*ε^2)*Q^2 := by
  unfold scalarProxy scalarIncrement
  ring_nf
  rw [Real.sq_sqrt hε]
  ring

lemma scalarProxy_mean {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (L Q : Ω → ℝ) {ε : ℝ} (hε : 0≤ε) (lam : ℝ)
    (hL : P.mean L=0) (hLQ : P.mean (fun ω => L ω*Q ω)=0) :
    P.mean (fun ω => scalarProxy ε lam (L ω) (Q ω)) =
      -ε*P.mean Q+lam*ε*P.mean (fun ω => (L ω)^2)+
        lam*ε^2*P.mean (fun ω => (Q ω)^2) := by
  simp_rw [scalarProxy_expansion hε,FiniteLaw.mean_add,FiniteLaw.mean_sub,FiniteLaw.mean_mul]
  simp only [FiniteLaw.mean_add,FiniteLaw.mean_sub,FiniteLaw.mean_mul]
  rw [hL,hLQ]
  ring

lemma scalarProxy_remainder {ε lam K L Q : ℝ} (hε : 0≤ε) (hε1 : ε≤1)
    (hlam : 0≤lam) (hK : 0≤K) (hL : |L|≤K) (hQ0 : 0≤Q) (hQ : Q≤K) :
    |scalarProxy ε lam L Q-Real.sqrt ε*L|≤(K+4*lam*K^2)*ε := by
  have hs := Real.sqrt_nonneg ε
  have hs2 := Real.sq_sqrt hε
  have hs1 : Real.sqrt ε≤1 := by nlinarith
  have heps : ε≤Real.sqrt ε := by nlinarith
  have hla := abs_le.mp hL
  have hdb : |scalarIncrement ε L Q|≤2*Real.sqrt ε*K := by
    unfold scalarIncrement
    calc
      |Real.sqrt ε*L-ε*Q|≤|Real.sqrt ε*L|+|ε*Q| := abs_sub _ _
      _ ≤ Real.sqrt ε*K+ε*K := by
        rw [abs_mul,abs_of_nonneg hs,abs_of_nonneg (mul_nonneg hε hQ0)]
        exact add_le_add (mul_le_mul_of_nonneg_left hL hs) (mul_le_mul_of_nonneg_left hQ hε)
      _ ≤ _ := by nlinarith
  have hd2 : (scalarIncrement ε L Q)^2≤4*ε*K^2 := by
    have h := sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤2*Real.sqrt ε*K) |>.mpr hdb
    rw [sq_abs] at h
    nlinarith [mul_nonneg (sq_nonneg K) (sq_nonneg (Real.sqrt ε))]
  have he : scalarProxy ε lam L Q-Real.sqrt ε*L = -ε*Q+lam*(scalarIncrement ε L Q)^2 := by
    unfold scalarProxy scalarIncrement
    ring
  rw [he]
  calc
    _ ≤ |-ε*Q|+|lam*(scalarIncrement ε L Q)^2| := abs_add_le _ _
    _ = ε*Q+lam*(scalarIncrement ε L Q)^2 := by
      rw [abs_mul,abs_neg,abs_of_nonneg hε,abs_of_nonneg hQ0,
        abs_of_nonneg (mul_nonneg hlam (sq_nonneg _))]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hd2 hlam,mul_le_mul_of_nonneg_left hQ hε]
end Komlos.KMFresh

-- END KMProof/ProxyMoments.lean

-- BEGIN KMProof/WeightedProxy.lean
noncomputable section
open Finset
namespace Komlos.KMFresh
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

lemma weightedProxy_drift (P : FiniteLaw Ω) (L Q : I → Ω → ℝ) (g : I → ℝ)
    {ε lam θ K : ℝ} (hε : 0≤ε) (hlam : 0≤lam) (hlθ : lam≤θ/2)
    (hg : ∀i,0≤g i) (hL : ∀i,P.mean (L i)=0)
    (hLQ : ∀i,P.mean (fun ω => L i ω*Q i ω)=0)
    (hQ : ∀i,θ*P.mean (fun ω => (L i ω)^2)≤P.mean (Q i))
    (hQ2 : ∀i,P.mean (fun ω => (Q i ω)^2)≤K^2) :
    P.mean (fun ω => ∑i,g i*scalarProxy ε lam (L i ω) (Q i ω)) ≤
      -(θ/2)*ε*(∑i,g i*P.mean (fun ω => (L i ω)^2))+
        (lam*ε^2*K^2)*(∑i,g i) := by
  rw [P.mean_sum]
  simp_rw [P.mean_mul,scalarProxy_mean P _ _ hε lam (hL _) (hLQ _)]
  calc
    _ ≤ ∑i,g i*(-(θ/2)*ε*P.mean (fun ω => (L i ω)^2)+lam*ε^2*K^2) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hg i)
      have ha := P.mean_nonneg (fun ω => sq_nonneg (L i ω))
      have h1 := mul_le_mul_of_nonneg_left (hQ i) hε
      have h2 := mul_le_mul_of_nonneg_right hlθ (mul_nonneg hε ha)
      have h3 := mul_le_mul_of_nonneg_left (hQ2 i) (mul_nonneg hlam (sq_nonneg ε))
      nlinarith
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma weighted_linear_variance (P : FiniteLaw Ω) (L : I → Ω → ℝ) (g : I → ℝ)
    {α G : ℝ} (hα : 0≤α) (hg : ∀i,0≤g i) (hG : ∀i,g i≤G)
    (hc : P.mean (fun ω => (∑i,g i*L i ω)^2)≤
      α*(∑i,(g i)^2*P.mean (fun ω => (L i ω)^2))) :
    P.mean (fun ω => (∑i,g i*L i ω)^2)≤
      α*G*(∑i,g i*P.mean (fun ω => (L i ω)^2)) := by
  apply hc.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hα
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_right (hG i) (hg i)
  have h2 := mul_le_mul_of_nonneg_right h (P.mean_nonneg (fun ω => sq_nonneg (L i ω)))
  nlinarith
end Komlos.KMFresh

-- END KMProof/WeightedProxy.lean

-- BEGIN KMProof/WeightedRemainder.lean
noncomputable section
open Finset
namespace Komlos.KMFresh
variable {I : Type*} [Fintype I]
lemma weighted_linear_abs (L g : I → ℝ) {K : ℝ}
    (hg : ∀i,0≤g i) (hL : ∀i,|L i|≤K) :
    |∑i,g i*L i|≤K*∑i,g i := by
  calc
    _ ≤ ∑i,|g i*L i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑i,K*g i := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (hg i)]
      nlinarith [mul_le_mul_of_nonneg_left (hL i) (hg i)]
    _ = _ := by rw [Finset.mul_sum]

lemma weighted_proxy_remainder (L Q g : I → ℝ) {ε lam K : ℝ}
    (hε : 0≤ε) (hε1 : ε≤1) (hlam : 0≤lam) (hK : 0≤K)
    (hg : ∀i,0≤g i) (hL : ∀i,|L i|≤K)
    (hQ0 : ∀i,0≤Q i) (hQ : ∀i,Q i≤K) :
    |(∑i,g i*scalarProxy ε lam (L i) (Q i))-Real.sqrt ε*(∑i,g i*L i)|≤
      ((K+4*lam*K^2)*(∑i,g i))*ε := by
  have he : (∑i,g i*scalarProxy ε lam (L i) (Q i))-Real.sqrt ε*(∑i,g i*L i) =
      ∑i,g i*(scalarProxy ε lam (L i) (Q i)-Real.sqrt ε*L i) := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  have hh := weighted_linear_abs (fun i => scalarProxy ε lam (L i) (Q i)-Real.sqrt ε*L i) g hg
    (fun i => scalarProxy_remainder hε hε1 hlam hK (hL i) (hQ0 i) (hQ i))
  calc
    _ ≤ ((K+4*lam*K^2)*ε)*(∑i,g i) := hh
    _ = _ := by ring
end Komlos.KMFresh

-- END KMProof/WeightedRemainder.lean

-- BEGIN KMProof/RemainderSquare.lean
noncomputable section
namespace Komlos.KMFresh

lemma remainder_square_bound {ε M R A Y : ℝ} (hε : 0≤ε) (hε1 : ε≤1)
    (hM : 0≤M) (hR : 0≤R) (hA : |A|≤M)
    (hY : |Y-Real.sqrt ε*A|≤R*ε) :
    Y^2≤ε*A^2+(2*M*R+R^2)*ε*Real.sqrt ε := by
  let r := Y-Real.sqrt ε*A
  have hr : |r|≤R*ε := hY
  have hs := Real.sqrt_nonneg ε
  have hs2 := Real.sq_sqrt hε
  have he : ε≤Real.sqrt ε := by nlinarith
  have har : A*r≤M*(R*ε) := by
    calc
      A*r≤|A*r| := le_abs_self _
      _ = |A| * |r| := abs_mul _ _
      _ ≤ M*(R*ε) := mul_le_mul hA hr (abs_nonneg r) hM
  have hcross := mul_le_mul_of_nonneg_left har (mul_nonneg (by norm_num : (0:ℝ)≤2) hs)
  have hr2 : r^2≤(R*ε)^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg r) (mul_nonneg hR hε)).mpr hr
    simpa only [sq_abs] using hh
  have he2 := mul_le_mul_of_nonneg_left he (mul_nonneg (sq_nonneg R) hε)
  have hid : Y^2=ε*A^2+2*Real.sqrt ε*(A*r)+r^2 := by
    dsimp [r]
    nlinarith [congrArg (fun t:ℝ => t*A^2) hs2]
  nlinarith

lemma mean_remainder_square {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (A Y : Ω → ℝ) {ε M R : ℝ} (hε : 0≤ε) (hε1 : ε≤1)
    (hM : 0≤M) (hR : 0≤R) (hA : ∀ω,|A ω|≤M)
    (hY : ∀ω,|Y ω-Real.sqrt ε*A ω|≤R*ε) :
    P.mean (fun ω => (Y ω)^2)≤ε*P.mean (fun ω => (A ω)^2)+
      (2*M*R+R^2)*ε*Real.sqrt ε := by
  have hh := P.mean_mono (fun ω => remainder_square_bound hε hε1 hM hR (hA ω) (hY ω))
  simpa only [P.mean_add,P.mean_mul,P.mean_const] using hh
end Komlos.KMFresh

-- END KMProof/RemainderSquare.lean

-- BEGIN KMProof/FiniteProxyBound.lean
noncomputable section
namespace Komlos.KMFresh

lemma finite_proxy_exponential {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (A Y : Ω → ℝ) {ε δ θ B S C₁ M R : ℝ}
    (hε : 0≤ε) (hε1 : ε≤1) (hδ : 0≤δ) (hS : 0 ≤ S)
    (hC : 0≤C₁) (hM : 0≤M) (hR : 0≤R)
    (hA : ∀ω,|A ω|≤M) (hrem : ∀ω,|Y ω-Real.sqrt ε*A ω|≤R*ε)
    (hmean : P.mean Y≤-(θ/2)*ε*S+C₁*ε^2)
    (hvar : P.mean (fun ω => (A ω)^2)≤B*S)
    (hcancel : δ^2*B≤δ*(θ/2))
    (hsmall : δ*(M+R)*Real.sqrt ε≤1) :
    P.mean (fun ω => Real.exp (δ*Y ω))≤
      Real.exp ((δ*C₁+δ^2*(2*M*R+R^2))*ε*Real.sqrt ε) := by
  have hs := Real.sqrt_nonneg ε
  have hs2 := Real.sq_sqrt hε
  have he : ε≤Real.sqrt ε := by nlinarith
  have hab (ω : Ω) : |Y ω|≤(M+R)*Real.sqrt ε := by
    calc
      |Y ω| = |(Y ω-Real.sqrt ε*A ω)+Real.sqrt ε*A ω| := by congr 1; ring
      _ ≤ |Y ω-Real.sqrt ε*A ω|+|Real.sqrt ε*A ω| := abs_add_le _ _
      _ ≤ R*ε+Real.sqrt ε*M := by
        rw [abs_mul,abs_of_nonneg hs]
        exact add_le_add (hrem ω) (mul_le_mul_of_nonneg_left (hA ω) hs)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he hR]
  have hb (ω : Ω) : |δ*Y ω|≤1 := by
    rw [abs_mul,abs_of_nonneg hδ]
    exact (mul_le_mul_of_nonneg_left (hab ω) hδ).trans (by nlinarith [hsmall])
  have hq := mean_remainder_square P A Y hε hε1 hM hR hA hrem
  have hv := mul_le_mul_of_nonneg_left hvar hε
  have hq' : P.mean (fun ω => (Y ω)^2)≤B*(ε*S)+(2*M*R+R^2)*ε*Real.sqrt ε := by
    nlinarith
  have hm' : P.mean Y≤-(θ/2)*(ε*S)+C₁*ε^2 := by nlinarith [hmean]
  have hh := P.proxy_exp_bound Y hδ hm' hq' hcancel (mul_nonneg hε hS) hb
  have he2 := mul_le_mul_of_nonneg_left he (mul_nonneg (mul_nonneg hδ hC) hε)
  calc
    _ ≤ 1+δ*(C₁*ε^2)+δ^2*((2*M*R+R^2)*ε*Real.sqrt ε) := hh
    _ ≤ 1+(δ*C₁+δ^2*(2*M*R+R^2))*ε*Real.sqrt ε := by nlinarith
    _ ≤ _ := by
      have he := Real.add_one_le_exp ((δ*C₁+δ^2*(2*M*R+R^2))*ε*Real.sqrt ε)
      convert he using 1
      ring
end Komlos.KMFresh

-- END KMProof/FiniteProxyBound.lean

-- BEGIN KMProof/WeightedProxyExponential.lean
noncomputable section
open Finset
namespace Komlos.KMFresh

def proxyErrorConstant (δ lam K D : ℝ) : ℝ :=
  δ*(lam*K^2*D)+δ^2*(2*(K*D)*((K+4*lam*K^2)*D)+((K+4*lam*K^2)*D)^2)

lemma weighted_proxy_exponential {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FiniteLaw Ω) (L Q : I → Ω → ℝ) (g : I → ℝ)
    {ε δ lam θ K D B : ℝ} (hε : 0≤ε) (hε1 : ε≤1) (hδ : 0≤δ)
    (hlam : 0≤lam) (hlθ : lam≤θ/2) (hK : 0≤K) (hD : 0≤D)
    (hg : ∀i,0≤g i) (hgD : (∑i,g i)≤D)
    (hL : ∀i ω,|L i ω|≤K) (hQ0 : ∀i ω,0≤Q i ω) (hQ : ∀i ω,Q i ω≤K)
    (hLm : ∀i,P.mean (L i)=0) (hLQ : ∀i,P.mean (fun ω => L i ω*Q i ω)=0)
    (hdrift : ∀i,θ*P.mean (fun ω => (L i ω)^2)≤P.mean (Q i))
    (hcov : P.mean (fun ω => (∑i,g i*L i ω)^2)≤
      B*(∑i,g i*P.mean (fun ω => (L i ω)^2)))
    (hcancel : δ^2*B≤δ*(θ/2))
    (hsmall : δ*(K*D+(K+4*lam*K^2)*D)*Real.sqrt ε≤1) :
    P.mean (fun ω => Real.exp (δ*(∑i,g i*scalarProxy ε lam (L i ω) (Q i ω))))≤
      Real.exp (proxyErrorConstant δ lam K D*ε*Real.sqrt ε) := by
  let A : Ω → ℝ := fun ω => ∑i,g i*L i ω
  let Y : Ω → ℝ := fun ω => ∑i,g i*scalarProxy ε lam (L i ω) (Q i ω)
  let S := ∑i,g i*P.mean (fun ω => (L i ω)^2)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => mul_nonneg (hg i) (P.mean_nonneg (fun ω => sq_nonneg (L i ω))))
  have hQ2 (i) : P.mean (fun ω => (Q i ω)^2)≤K^2 := by
    have hh := P.mean_mono (fun ω => (sq_le_sq₀ (hQ0 i ω) hK).mpr (hQ i ω))
    simpa only [P.mean_const] using hh
  have hmean : P.mean Y≤-(θ/2)*ε*S+(lam*K^2*D)*ε^2 := by
    have hh := weightedProxy_drift P L Q g hε hlam hlθ hg hLm hLQ hdrift hQ2
    have hd := mul_le_mul_of_nonneg_left hgD (mul_nonneg (mul_nonneg hlam (sq_nonneg ε)) (sq_nonneg K))
    dsimp [Y,S]
    nlinarith
  have hA (ω) : |A ω|≤K*D :=
    (weighted_linear_abs (fun i => L i ω) g hg (fun i => hL i ω)).trans
      (mul_le_mul_of_nonneg_left hgD hK)
  have hR (ω) : |Y ω-Real.sqrt ε*A ω|≤((K+4*lam*K^2)*D)*ε := by
    have hh := weighted_proxy_remainder (fun i => L i ω) (fun i => Q i ω) g
      hε hε1 hlam hK hg (fun i => hL i ω) (fun i => hQ0 i ω) (fun i => hQ i ω)
    apply hh.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgD (by positivity)) hε
  exact finite_proxy_exponential P A Y hε hε1 hδ hS (by positivity) (by positivity)
    (by positivity) hA hR hmean hcov hcancel hsmall
end Komlos.KMFresh

-- END KMProof/WeightedProxyExponential.lean

-- BEGIN KMProof/SampledRowProxy.lean
noncomputable section
open Matrix Finset
namespace Komlos.KMFresh

def modifiedRowMatrix {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (β : ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun r i => A r i-2*β*(A r i)^2*x i

lemma sampled_row_proxy_exponential {n m : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (ht : 0 < X.trace)
    (hbase : ((8:ℝ) • Matrix.diagonal X.diag-X).PosSemidef)
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    {β α G D ε δ lam : ℝ} (hβ : 0 ≤ β) (hβsmall : β ≤ 1/64)
    (ha : ∀r i,|A r i| ≤ 1) (hx : ∀i,|x i| ≤ 1)
    (hα : 0 ≤ α) (hD : 0 ≤ D)
    (haff : (α • Matrix.diagonal
      (modifiedRowMatrix A x β * X * (modifiedRowMatrix A x β).transpose).diag-
      modifiedRowMatrix A x β * X * (modifiedRowMatrix A x β).transpose).PosSemidef)
    (g : Fin m → ℝ) (hg : ∀r,0 ≤ g r) (hgG : ∀r,g r ≤ G) (hgD : (∑r,g r) ≤ D)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ) (hlam : 0 ≤ lam)
    (hlθ : lam ≤ (β/16)/2) (hcancel : δ^2*(α*G) ≤ δ*((β/16)/2))
    (hsmall : δ*((3*Real.sqrt (n:ℝ)+1)*D+
      ((3*Real.sqrt (n:ℝ)+1)+4*lam*(3*Real.sqrt (n:ℝ)+1)^2)*D)*Real.sqrt ε ≤ 1) :
    (FiniteLaw.uniform (Fin n → Bool)).mean (fun s => Real.exp (δ*(∑r,g r*
      scalarProxy ε lam (rowLinear (A r) x β (fun i => matrixSample hX s i))
        (rowQuadratic (A r) β (fun i => matrixSample hX s i))))) ≤
    Real.exp (proxyErrorConstant δ lam (3*Real.sqrt (n:ℝ)+1) D*ε*Real.sqrt ε) := by
  apply weighted_proxy_exponential _ _ _ g hε hε1 hδ hlam hlθ (by positivity) hD hg hgD
  · intro r s
    have hh := rowLinear_abs_bound (A r) x (fun i => matrixSample hX s i) β
      (ha r) hx hβ (by linarith) (matrixSample_square_sum hX ht s)
    simp only [Fintype.card_fin] at hh
    linarith
  · intro r s
    exact rowQuadratic_nonneg _ _ β hβ
  · intro r s
    have hh := rowQuadratic_le_one (A r) (fun i => matrixSample hX s i) β
      hβ (by linarith) (ha r) (matrixSample_square_sum hX ht s)
    have hn := Real.sqrt_nonneg (n:ℝ)
    linarith
  · exact fun r => sampled_row_mean_zero hX (A r) x β
  · exact fun r => sampled_row_mixed_zero hX (A r) x β
  · exact fun r => sampled_row_drift hX ht hbase (A r) x hβ hβsmall (ha r) hx
  · apply weighted_linear_variance _ _ g hα hg hgG
    exact matrixSample_affine_variance hX ht (modifiedRowMatrix A x β) α haff g
  · exact hcancel
  · exact hsmall
end Komlos.KMFresh

-- END KMProof/SampledRowProxy.lean

-- BEGIN KMProof/ProxyWeightBounds.lean
noncomputable section
namespace Komlos.KMFresh

lemma bounded_weights_sum {I : Type*} [Fintype I] (g : I → ℝ) {G : ℝ}
    (hg : ∀i,g i ≤ G) : (∑i,g i) ≤ (Fintype.card I:ℝ)*G := by
  simpa using Finset.sum_le_sum (fun i (_:i∈Finset.univ) => hg i)

lemma weighted_proxy_weight_bound {w lam z b : ℝ}
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (hlam : 0 ≤ lam) (hz : z ≤ 2*b) :
    0 ≤ w*(lam*Real.exp (lam*z)) ∧ w*(lam*Real.exp (lam*z)) ≤ lam*Real.exp (lam*(2*b)) := by
  have he : Real.exp (lam*z) ≤ Real.exp (lam*(2*b)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz hlam)
  constructor
  · positivity
  · have h1 := mul_le_mul_of_nonneg_right hw1 (mul_nonneg hlam (Real.exp_pos (lam*z)).le)
    have h2 := mul_le_mul_of_nonneg_left he hlam
    nlinarith
end Komlos.KMFresh

-- END KMProof/ProxyWeightBounds.lean

-- BEGIN KMProof/ActualMediumProxy.lean
noncomputable section
open Matrix Finset
namespace Komlos.KMFresh
variable {R : Type*} [Fintype R] {n : ℕ}

def columnPhaseWeight (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ)
    (μ β _b lam : Fin (q+1) → ℝ) (s : AdaptiveState (Fin (q+1) × R) n)
    (p : Fin (q+1)) (j : Fin n) (r : R) : ℝ :=
  (scaleEntry q p (A r j))^2 * phaseProxyWeight (scaleRows A q) ρ
    (fun z => (4:ℝ)^z.1.val) (fun z => μ z.1) (fun z => β z.1) (fun z => lam z.1) s (p,r)

def columnProxy (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ)
    (μ β b lam : Fin (q+1) → ℝ)
    (ha : ∀r i,|A r i| ≤ 1) (hA : ∀i,∑r,(A r i)^2 ≤ 2) (hμ : ∀p,0 < μ p)
    (ε : ℝ) (s : AdaptiveState (Fin (q+1) × R) n) (p : Fin (q+1)) (j : Fin n)
    (ω : Fin n → Bool) : ℝ :=
  ∑r,columnPhaseWeight A q ρ μ β b lam s p j r * scalarProxy ε (lam p)
    (rowLinear (fun i => scaleEntry q p (A r i)) s.x (β p)
      (scaleDirection A q ρ μ β ha hA hμ s ω))
    (rowQuadratic (fun i => scaleEntry q p (A r i)) (β p)
      (scaleDirection A q ρ μ β ha hA hμ s ω))

omit [Fintype R] in
lemma columnPhaseWeight_bounds (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ)
    (μ β b lam : Fin (q+1) → ℝ) (s : AdaptiveState (Fin (q+1) × R) n)
    (hs : rowStateValid (scaleRows A q) ρ (fun z => (4:ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1) s)
    (p : Fin (q+1)) (j : Fin n) (hlam : 0 ≤ lam p) (r : R) :
    0 ≤ columnPhaseWeight A q ρ μ β b lam s p j r ∧
      columnPhaseWeight A q ρ μ β b lam s p j r ≤ lam p*Real.exp (lam p*(2*b p)) := by
  have hg := phaseProxyWeight_bound (scaleRows A q) ρ (fun z => (4:ℝ)^z.1.val)
    (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1) (fun z => lam z.1) s (p,r) hs hlam
  have hw : (scaleEntry q p (A r j))^2 ≤ 1 := by
    have hh := scaleEntry_abs_le q p (A r j)
    have ha := abs_nonneg (scaleEntry q p (A r j))
    have he := sq_abs (scaleEntry q p (A r j))
    nlinarith
  constructor
  · exact mul_nonneg (sq_nonneg _) hg.1
  · have hh := mul_le_mul_of_nonneg_right hw hg.1
    dsimp [columnPhaseWeight]
    nlinarith [hg.2]

lemma columnPhaseWeight_supported (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ)
    (μ β b lam : Fin (q+1) → ℝ) (s : AdaptiveState (Fin (q+1) × R) n)
    (p : Fin (q+1)) (j : Fin n) (r : R)
    (hr : r ∉ mediumRows (fun r i => scaleEntry q p (A r i)) ρ ((4:ℝ)^p.val) (μ p) s.x) :
    columnPhaseWeight A q ρ μ β b lam s p j r=0 := by
  classical
  have hm : ¬rowMedium (scaleRows A q) ρ (fun z => (4:ℝ)^z.1.val) (fun z => μ z.1) s.x (p,r) := by
    simpa only [mediumRows,Finset.mem_filter,Finset.mem_univ,true_and,
      rowMedium,rowEnergy,scaleRows] using hr
  simp only [columnPhaseWeight,phaseProxyWeight,hm,false_and,if_false,mul_zero]

lemma columnProxy_mgf_running (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ)
    (μ β b lam : Fin (q+1) → ℝ)
    (ha : ∀r i,|A r i| ≤ 1) (hA : ∀i,∑r,(A r i)^2 ≤ 2) (hμ : ∀p,0 < μ p)
    (s : AdaptiveState (Fin (q+1) × R) n) (hrun : scaleRunning A q ρ μ s)
    (hs : rowStateValid (scaleRows A q) ρ (fun z => (4:ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1) s)
    (p : Fin (q+1)) (j : Fin n) {ε δ : ℝ}
    (hβ : 0 ≤ β p) (hβsmall : β p ≤ 1/64) (hlam : 0 ≤ lam p)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ) (hlθ : lam p ≤ (β p/16)/2)
    (hcancel : δ^2*((64*((q+1:ℕ):ℝ)*(4:ℝ)^p.val/μ p)*(lam p*Real.exp (lam p*(2*b p)))) ≤ δ*((β p/16)/2))
    (hsmall : δ*((3*Real.sqrt (n:ℝ)+1)*((Fintype.card R:ℝ)*(lam p*Real.exp (lam p*(2*b p))))+
      ((3*Real.sqrt (n:ℝ)+1)+4*lam p*(3*Real.sqrt (n:ℝ)+1)^2)*
        ((Fintype.card R:ℝ)*(lam p*Real.exp (lam p*(2*b p)))))*Real.sqrt ε ≤ 1) :
    (FiniteLaw.uniform (Fin n → Bool)).mean
      (fun ω => Real.exp (δ*columnProxy A q ρ μ β b lam ha hA hμ ε s p j ω)) ≤
      Real.exp (proxyErrorConstant δ (lam p) (3*Real.sqrt (n:ℝ)+1)
        ((Fintype.card R:ℝ)*(lam p*Real.exp (lam p*(2*b p))))*ε*Real.sqrt ε) := by
  classical
  let S := mediumRows (fun r i => scaleEntry q p (A r i)) ρ ((4:ℝ)^p.val) (μ p) s.x
  let C := chooseScaleMatrix A q ρ μ β ha hA hμ s hrun
  let M : Matrix (Fin (Fintype.card S)) (Fin n) ℝ := fun r i => scaleEntry q p (A (selectedRow S r) i)
  let g := fun r => columnPhaseWeight A q ρ μ β b lam s p j (selectedRow S r)
  let G := lam p*Real.exp (lam p*(2*b p))
  have hG : 0 ≤ G := mul_nonneg hlam (Real.exp_pos _).le
  have hg (r) := columnPhaseWeight_bounds A q ρ μ β b lam s hs p j hlam (selectedRow S r)
  have hd : (∑r,g r) ≤ (Fintype.card R:ℝ)*G := by
    have h1 := bounded_weights_sum g (fun r => (hg r).2)
    simp only [Fintype.card_fin] at h1
    have hc : (Fintype.card S:ℝ) ≤ (Fintype.card R:ℝ) := by
      exact_mod_cast (show Fintype.card S ≤ Fintype.card R by simpa only [Fintype.card_coe] using S.card_le_univ)
    exact h1.trans (mul_le_mul_of_nonneg_right hc hG)
  have haff : ((64*((q+1:ℕ):ℝ)*(4:ℝ)^p.val/μ p) • Matrix.diagonal
      (modifiedRowMatrix M s.x (β p)*C.matrix*(modifiedRowMatrix M s.x (β p)).transpose).diag-
      modifiedRowMatrix M s.x (β p)*C.matrix*(modifiedRowMatrix M s.x (β p)).transpose).PosSemidef := C.affine p
  have hμp := (hμ p).le
  have hh := sampled_row_proxy_exponential C.psd (chosenScaleMatrix_trace_pos A q ρ μ β ha hA hμ s hrun)
    C.base M s.x hβ hβsmall (fun r i => scaleEntry_abs_le q p _) hs.1
    (by positivity : 0 ≤ 64*((q+1:ℕ):ℝ)*(4:ℝ)^p.val/μ p) (mul_nonneg (Nat.cast_nonneg _) hG)
    haff g (fun r => (hg r).1) (fun r => (hg r).2) hd hε hε1 hδ hlam hlθ hcancel hsmall
  have he (ω : Fin n → Bool) : columnProxy A q ρ μ β b lam ha hA hμ ε s p j ω =
      ∑r,g r*scalarProxy ε (lam p) (rowLinear (M r) s.x (β p) (fun i => matrixSample C.psd ω i))
        (rowQuadratic (M r) (β p) (fun i => matrixSample C.psd ω i)) := by
    unfold columnProxy
    rw [scaleDirection_running A q ρ μ β ha hA hμ s hrun ω]
    symm
    apply selectedRow_sum_supported S (fun r => columnPhaseWeight A q ρ μ β b lam s p j r *
      scalarProxy ε (lam p) (rowLinear (fun i => scaleEntry q p (A r i)) s.x (β p) (fun i => matrixSample C.psd ω i))
        (rowQuadratic (fun i => scaleEntry q p (A r i)) (β p) (fun i => matrixSample C.psd ω i)))
    intro r hr
    rw [columnPhaseWeight_supported A q ρ μ β b lam s p j r hr,zero_mul]
  simpa only [he] using hh
end Komlos.KMFresh

-- END KMProof/ActualMediumProxy.lean

-- BEGIN KMProof/IncrementBounds.lean
noncomputable section
namespace Komlos.KMFresh

lemma scalarIncrement_abs {ε K L Q : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hK : 0 ≤ K) (hL : |L| ≤ K) (hQ0 : 0 ≤ Q) (hQ : Q ≤ K) :
    |scalarIncrement ε L Q| ≤ 2*K*Real.sqrt ε := by
  have hs := Real.sqrt_nonneg ε
  have hs2 := Real.sq_sqrt hε
  have heps : ε ≤ Real.sqrt ε := by nlinarith
  unfold scalarIncrement
  calc
    |Real.sqrt ε*L-ε*Q| ≤ |Real.sqrt ε*L|+|ε*Q| := abs_sub _ _
    _ ≤ Real.sqrt ε*K+ε*K := by
      rw [abs_mul,abs_of_nonneg hs,abs_of_nonneg (mul_nonneg hε hQ0)]
      exact add_le_add (mul_le_mul_of_nonneg_left hL hs) (mul_le_mul_of_nonneg_left hQ hε)
    _ ≤ _ := by nlinarith

lemma scalarIncrement_cap_small {ε K L Q lam : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hK : 0 ≤ K) (hL : |L| ≤ K)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ K) (hlam : 0 ≤ lam)
    (hsmall : (2*lam*K)*Real.sqrt ε ≤ 1) :
    |lam*scalarIncrement ε L Q| ≤ 1 := by
  rw [abs_mul,abs_of_nonneg hlam]
  have hh := mul_le_mul_of_nonneg_left (scalarIncrement_abs hε hε1 hK hL hQ0 hQ) hlam
  nlinarith
end Komlos.KMFresh

-- END KMProof/IncrementBounds.lean

-- BEGIN KMProof/ExponentialHistory.lean
noncomputable section
namespace Komlos.KMFresh
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

lemma exponential_history_step (Y : (n : ℕ) → History Ω n → ℝ) (δ c : ℝ)
    (hc : 0<c)
    (hstep : ∀n h,(FiniteLaw.uniform Ω).mean
      (fun x => Real.exp (δ*(Y (n+1) (Fin.snoc h x)-Y n h)))≤c) :
    ∀n h,(FiniteLaw.uniform Ω).mean
      (fun x => Real.exp (δ*Y (n+1) (Fin.snoc h x))/c^(n+1))≤
      Real.exp (δ*Y n h)/c^n := by
  intro n h
  have he (x : Ω) : Real.exp (δ*Y (n+1) (Fin.snoc h x))/c^(n+1) =
      (Real.exp (δ*Y n h)/c^(n+1))*
        Real.exp (δ*(Y (n+1) (Fin.snoc h x)-Y n h)) := by
    rw [div_mul_eq_mul_div,←Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  rw [FiniteLaw.mean_mul]
  calc
    _ ≤ (Real.exp (δ*Y n h)/c^(n+1))*c :=
      mul_le_mul_of_nonneg_left (hstep n h) (by positivity)
    _ = _ := by rw [pow_succ]; field_simp

lemma exponential_history_maximal (Y : (n : ℕ) → History Ω n → ℝ)
    (δ c a : ℝ) (hc : 0<c) (ha : 0<a)
    (hstep : ∀n h,(FiniteLaw.uniform Ω).mean
      (fun x => Real.exp (δ*(Y (n+1) (Fin.snoc h x)-Y n h)))≤c) (n : ℕ) :
    (FiniteLaw.uniform (History Ω n)).prob
      (historyHit (fun k h => Real.exp (δ*Y k h)/c^k) a n)≤
      Real.exp (δ*Y 0 Fin.elim0)/a := by
  simpa using history_maximal_bound (fun k h => Real.exp (δ*Y k h)/c^k) ha
    (fun k h => by positivity) (exponential_history_step Y δ c hc hstep) n

end Komlos.KMFresh

-- END KMProof/ExponentialHistory.lean

-- BEGIN KMProof/ExponentialCrossing.lean
noncomputable section
namespace Komlos.KMFresh
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

lemma exponential_crossing_bound (Y : (n : ℕ) → History Ω n → ℝ)
    {δ η ξ : ℝ} (hδ : 0≤δ) (hη : 0≤η) (hY0 : Y 0 Fin.elim0=0)
    (hstep : ∀n h,(FiniteLaw.uniform Ω).mean
      (fun x => Real.exp (δ*(Y (n+1) (Fin.snoc h x)-Y n h)))≤Real.exp η) (N : ℕ) :
    (FiniteLaw.uniform (History Ω N)).prob
      (fun h => ∃k:ℕ,∃hk:k≤N,ξ≤Y k (historyPrefix h k hk))≤
      Real.exp ((N:ℝ)*η-δ*ξ) := by
  classical
  let c := Real.exp η
  let a := Real.exp (δ*ξ)/c^N
  have hc : 0<c := Real.exp_pos η
  have hc1 : 1≤c := Real.one_le_exp_iff.mpr hη
  have ha : 0<a := by dsimp [a]; positivity
  have hh := exponential_history_maximal Y δ c a hc ha hstep N
  have hevent : ∀h,(∃k:ℕ,∃hk:k≤N,ξ≤Y k (historyPrefix h k hk)) →
      historyHit (fun k h => Real.exp (δ*Y k h)/c^k) a N h := by
    rintro h ⟨k,hk,hy⟩
    apply historyHit_of_prefix _ _ hk h
    apply historyHit_of_current
    change Real.exp (δ*ξ)/c^N≤Real.exp (δ*Y k (historyPrefix h k hk))/c^k
    calc
      _ ≤ Real.exp (δ*ξ)/c^k :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (pow_pos hc k)
          (pow_le_pow_right₀ hc1 hk)
      _ ≤ _ := div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy hδ)) (pow_nonneg hc.le k)
  have hp := (FiniteLaw.uniform (History Ω N)).prob_mono hevent
  apply (hp.trans hh).trans_eq
  rw [hY0,mul_zero,Real.exp_zero]
  dsimp [a,c]
  rw [one_div_div,←Real.exp_nat_mul,←Real.exp_sub]
end Komlos.KMFresh

-- END KMProof/ExponentialCrossing.lean

-- BEGIN KMProof/ProxyTail.lean
noncomputable section
namespace Komlos.KMFresh
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

lemma proxy_crossing_tail (Y : (n : ℕ) → History Ω n → ℝ)
    {δ η p : ℝ} (hδ : 0<δ) (hη : 0≤η) (hp : 0<p)
    (hY0 : Y 0 Fin.elim0=0)
    (hstep : ∀n h,(FiniteLaw.uniform Ω).mean
      (fun x => Real.exp (δ*(Y (n+1) (Fin.snoc h x)-Y n h)))≤Real.exp η)
    (N : ℕ) (herror : (N:ℝ)*η≤1) :
    (FiniteLaw.uniform (History Ω N)).prob
      (fun h => ∃k:ℕ,∃hk:k≤N,(1-Real.log p)/δ≤Y k (historyPrefix h k hk))≤p := by
  have hh := exponential_crossing_bound Y hδ.le hη hY0 hstep N (ξ:=(1-Real.log p)/δ)
  apply hh.trans
  have he : δ*((1-Real.log p)/δ)=1-Real.log p := by field_simp
  rw [he]
  calc
    Real.exp ((N:ℝ)*η-(1-Real.log p))≤Real.exp (Real.log p) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = p := Real.exp_log hp
end Komlos.KMFresh

-- END KMProof/ProxyTail.lean

-- BEGIN KMProof/HistoryAccumulation.lean
noncomputable section
namespace Komlos.KMFresh
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def historyAccumulation (F : (n:ℕ) → History Ω n → Ω → ℝ) :
    (n:ℕ) → History Ω n → ℝ
  | 0,_ => 0
  | n+1,h => historyAccumulation F n (Fin.init h)+F n (Fin.init h) (h (Fin.last n))

omit [Fintype Ω] [Nonempty Ω] in
lemma historyAccumulation_snoc (F : (n:ℕ) → History Ω n → Ω → ℝ)
    (n : ℕ) (h : History Ω n) (x : Ω) :
    historyAccumulation F (n+1) (Fin.snoc h x)=historyAccumulation F n h+F n h x := by
  simp [historyAccumulation]

lemma accumulated_proxy_tail (F : (n:ℕ) → History Ω n → Ω → ℝ)
    {δ η p : ℝ} (hδ : 0<δ) (hη : 0≤η) (hp : 0<p)
    (hstep : ∀n h,(FiniteLaw.uniform Ω).mean (fun x => Real.exp (δ*F n h x))≤Real.exp η)
    (N : ℕ) (herror : (N:ℝ)*η≤1) :
    (FiniteLaw.uniform (History Ω N)).prob
      (fun h => ∃k:ℕ,∃hk:k≤N,(1-Real.log p)/δ≤historyAccumulation F k (historyPrefix h k hk))≤p := by
  apply proxy_crossing_tail (historyAccumulation F) hδ hη hp rfl _ N herror
  intro n h
  simpa only [historyAccumulation_snoc,add_sub_cancel_left] using hstep n h
end Komlos.KMFresh

-- END KMProof/HistoryAccumulation.lean

-- BEGIN KMProof/PotentialLedger.lean
noncomputable section
open Finset
namespace Komlos.KMFresh
variable {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]

omit [Fintype Ω] [Nonempty Ω] in
lemma potential_ledger (φ : (n:ℕ) → History Ω n → I → ℝ)
    (F : (n:ℕ) → History Ω n → Ω → ℝ) (B : ℝ)
    (h0 : ∀i,φ 0 Fin.elim0 i≤B)
    (hstep : ∀n h x,(∑i,φ (n+1) (Fin.snoc h x) i)≤(∑i,φ n h i)+F n h x)
    (n : ℕ) (h : History Ω n) :
    (∑i,φ n h i)≤(Fintype.card I:ℝ)*B+historyAccumulation F n h := by
  induction n with
  | zero =>
    have he : h=Fin.elim0 := by funext i; exact Fin.elim0 i
    subst h
    simpa [historyAccumulation] using Finset.sum_le_sum (fun i (_:i∈Finset.univ) => h0 i)
  | succ n ih =>
    have hh := hstep n (Fin.init h) (h (Fin.last n))
    rw [Fin.snoc_init_self] at hh
    have hi := ih (Fin.init h)
    change (∑i,φ (n+1) h i)≤(Fintype.card I:ℝ)*B+
      (historyAccumulation F n (Fin.init h)+F n (Fin.init h) (h (Fin.last n)))
    linarith

omit [Fintype Ω] [Nonempty Ω] in
lemma hit_count_le_potential (φ : I → ℝ) (hit : I → Prop) [DecidablePred hit] {H : ℝ}
    (hφ : ∀i,0≤φ i) (hhit : ∀i,hit i → H≤φ i) :
    H*((Finset.univ.filter hit).card:ℝ)≤∑i,φ i := by
  classical
  calc
    H*((Finset.univ.filter hit).card:ℝ)=∑i∈Finset.univ.filter hit,H := by simp [mul_comm]
    _ ≤ ∑i∈Finset.univ.filter hit,φ i := Finset.sum_le_sum (fun i hi => hhit i (Finset.mem_filter.mp hi).2)
    _ ≤ ∑i,φ i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hφ i)

omit [Fintype Ω] [Nonempty Ω] in
lemma potential_hit_count (φ : (n:ℕ) → History Ω n → I → ℝ)
    (F : (n:ℕ) → History Ω n → Ω → ℝ) (B H : ℝ) (hH : 0<H)
    (h0 : ∀i,φ 0 Fin.elim0 i≤B)
    (hstep : ∀n h x,(∑i,φ (n+1) (Fin.snoc h x) i)≤(∑i,φ n h i)+F n h x)
    (n : ℕ) (h : History Ω n) (hit : I → Prop) [DecidablePred hit]
    (hφ : ∀i,0≤φ n h i) (hhit : ∀i,hit i → H≤φ n h i) :
    ((Finset.univ.filter hit).card:ℝ)≤
      ((Fintype.card I:ℝ)*B+historyAccumulation F n h)/H := by
  classical
  apply (le_div_iff₀ hH).mpr
  rw [mul_comm]
  exact (hit_count_le_potential _ hit hφ hhit).trans (potential_ledger φ F B h0 hstep n h)
end Komlos.KMFresh

-- END KMProof/PotentialLedger.lean

-- BEGIN KMProof/WeightedLedger.lean
noncomputable section
open Finset
namespace Komlos.KMFresh
variable {I : Type*} [Fintype I]

lemma weighted_hit_mass_le (φ w : I → ℝ) (hit : I → Prop) [DecidablePred hit]
    (H : ℝ) (hφ : ∀i,0 ≤ φ i) (hhit : ∀i,hit i → H*w i ≤ φ i) :
    H*(∑i∈Finset.univ.filter hit,w i) ≤ ∑i,φ i := by
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum (fun i hi => hhit i (Finset.mem_filter.mp hi).2)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hφ i))

lemma weighted_potential_count (φ w : I → ℝ) (hit : I → Prop) [DecidablePred hit]
    {H B U : ℝ} (hH : 0 < H) (hφ : ∀i,0 ≤ φ i)
    (hhit : ∀i,hit i → H*w i ≤ φ i) (hledger : (∑i,φ i) ≤ B+U) :
    (∑i∈Finset.univ.filter hit,w i) ≤ (B+U)/H := by
  apply (le_div_iff₀ hH).mpr
  rw [mul_comm]
  exact (weighted_hit_mass_le φ w hit H hφ hhit).trans hledger
end Komlos.KMFresh

-- END KMProof/WeightedLedger.lean

-- BEGIN KMProof/TotalLedger.lean
noncomputable section
namespace Komlos.KMFresh
variable {Ω I : Type*} [Fintype I]

lemma total_potential_ledger (φ : (n:ℕ) → History Ω n → I → ℝ)
    (F : (n:ℕ) → History Ω n → Ω → ℝ) (B : ℝ)
    (h0 : (∑i,φ 0 Fin.elim0 i) ≤ B)
    (hstep : ∀n h x,(∑i,φ (n+1) (Fin.snoc h x) i) ≤ (∑i,φ n h i)+F n h x)
    (n : ℕ) (h : History Ω n) :
    (∑i,φ n h i) ≤ B+historyAccumulation F n h := by
  induction n with
  | zero =>
    have he : h=Fin.elim0 := by funext i; exact Fin.elim0 i
    subst h
    simpa [historyAccumulation] using h0
  | succ n ih =>
    have hh := hstep n (Fin.init h) (h (Fin.last n))
    rw [Fin.snoc_init_self] at hh
    have hi := ih (Fin.init h)
    change (∑i,φ (n+1) h i) ≤ B+
      (historyAccumulation F n (Fin.init h)+F n (Fin.init h) (h (Fin.last n)))
    linarith

variable [Fintype Ω] [Nonempty Ω]
lemma weighted_potential_tail (φ : (n:ℕ) → History Ω n → I → ℝ)
    (F : (n:ℕ) → History Ω n → Ω → ℝ) (w : I → ℝ)
    (hit : (n:ℕ) → History Ω n → I → Prop) [∀n h, DecidablePred (hit n h)]
    (B H δ η p : ℝ) (hδ : 0 < δ) (hη : 0 ≤ η) (hp : 0 < p)
    (h0 : (∑i,φ 0 Fin.elim0 i) ≤ B)
    (hstep : ∀n h x,(∑i,φ (n+1) (Fin.snoc h x) i) ≤ (∑i,φ n h i)+F n h x)
    (hφ : ∀n h i,0 ≤ φ n h i)
    (hhit : ∀n h i,hit n h i → H*w i ≤ φ n h i)
    (hmgf : ∀n h,(FiniteLaw.uniform Ω).mean (fun x => Real.exp (δ*F n h x)) ≤ Real.exp η)
    (N : ℕ) (herror : (N:ℝ)*η ≤ 1) :
    (FiniteLaw.uniform (History Ω N)).prob
      (fun h => ∃k:ℕ,∃hk:k ≤ N,
        B+(1-Real.log p)/δ ≤ H*(∑i∈Finset.univ.filter (hit k (historyPrefix h k hk)),w i)) ≤ p := by
  classical
  apply le_trans (FiniteLaw.prob_mono _ ?_) (accumulated_proxy_tail F hδ hη hp hmgf N herror)
  rintro h ⟨k,hk,hbad⟩
  refine ⟨k,hk,?_⟩
  have hcount := weighted_hit_mass_le (φ k (historyPrefix h k hk)) w
    (hit k (historyPrefix h k hk)) H (hφ k _) (hhit k _)
  have hledger := total_potential_ledger φ F B h0 hstep k (historyPrefix h k hk)
  linarith
end Komlos.KMFresh

-- END KMProof/TotalLedger.lean

-- BEGIN KMProof/ActualMediumLedger.lean
noncomputable section
open Finset
namespace Komlos.KMFresh
variable {R : Type*} [Fintype R] {n : ℕ}

def columnRowPotential (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ)
    (μ β b lam : Fin (q+1) → ℝ) (s : AdaptiveState (Fin (q+1) × R) n)
    (p : Fin (q+1)) (j : Fin n) (r : R) : ℝ :=
  (scaleEntry q p (A r j))^2 * phasePotential (scaleRows A q) ρ
    (fun z => (4:ℝ)^z.1.val) (fun z => μ z.1) (fun z => β z.1)
    (fun z => b z.1) (fun z => lam z.1) s (p,r)

lemma columnProxy_stopped (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ)
    (μ β b lam : Fin (q+1) → ℝ)
    (ha : ∀r i,|A r i| ≤ 1) (hA : ∀i,∑r,(A r i)^2 ≤ 2) (hμ : ∀p,0 < μ p)
    (ε : ℝ) (s : AdaptiveState (Fin (q+1) × R) n) (p : Fin (q+1)) (j : Fin n)
    (hrun : ¬scaleRunning A q ρ μ s) (ω : Fin n → Bool) :
    columnProxy A q ρ μ β b lam ha hA hμ ε s p j ω=0 := by
  classical
  simp [columnProxy,scaleDirection,hrun,rowLinear,rowQuadratic,scalarProxy,scalarIncrement]

lemma columnRowPotential_initial (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ)
    (μ β b lam : Fin (q+1) → ℝ) (p : Fin (q+1)) (j : Fin n)
    (hβ : 0 ≤ β p) (hbudget : β p*(64*(4:ℝ)^p.val) ≤ b p) (hlam : 0 ≤ lam p) :
    (∑r,columnRowPotential A q ρ μ β b lam ⟨0,∅⟩ p j r) ≤
      (∑r,(scaleEntry q p (A r j))^2)*Real.exp (lam p*b p) := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  by_cases hl : rowLarge (scaleRows A q) ρ (fun z => (4:ℝ)^z.1.val) 0 (p,r)
  · simp [phasePotential,hl]
  · apply phasePotential_activation_bound (scaleRows A q) ρ (fun z => (4:ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1) (fun z => lam z.1) ⟨0,∅⟩ (p,r)
      (by simp) hlam
    exact rowRegularizer_activation (scaleRows A q) ρ (fun z => (4:ℝ)^z.1.val)
      (fun z => β z.1) (fun z => b z.1) 0 (p,r) hβ hbudget (by simp [rowDiscrepancy]) hl

lemma columnRowPotential_step (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ)
    (μ β b lam : Fin (q+1) → ℝ)
    (ha : ∀r i,|A r i| ≤ 1) (hA : ∀i,∑r,(A r i)^2 ≤ 2) (hμ : ∀p,0 < μ p)
    (s : AdaptiveState (Fin (q+1) × R) n)
    (hs : rowStateValid (scaleRows A q) ρ (fun z => (4:ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1) s)
    (p : Fin (q+1)) (j : Fin n) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hρ : Real.sqrt ε ≤ ρ) (hβ : 0 ≤ β p) (hβsmall : β p ≤ 1/64)
    (hb : 0 < b p) (hbudget : β p*(64*(4:ℝ)^p.val) ≤ b p) (hlam : 0 ≤ lam p)
    (hsmall : (2*lam p*(3*Real.sqrt (n:ℝ)+1))*Real.sqrt ε ≤ 1)
    (ω : Fin n → Bool) :
    (∑r,columnRowPotential A q ρ μ β b lam (scaleStep A q ρ μ β b ha hA hμ (Real.sqrt ε) s ω) p j r) ≤
      (∑r,columnRowPotential A q ρ μ β b lam s p j r)+columnProxy A q ρ μ β b lam ha hA hμ ε s p j ω := by
  classical
  by_cases hrun : scaleRunning A q ρ μ s
  · have hgeom := scaleDirection_geometry A q ρ μ β ha hA hμ s hrun ω
    have hh (r : R) := actual_phase_step_bound (scaleRows A q) ρ (fun z => (4:ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1) (fun z => lam z.1)
      (scaleRunning A q ρ μ) (scaleDirection A q ρ μ β ha hA hμ) (Real.sqrt ε) s ω hrun (p,r)
      hs (Real.sqrt_nonneg ε) hρ hgeom.1 hgeom.2.1
      (fun hz => hgeom.2.2.2 (p,r) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩))
      hβ hb hbudget hlam
    have hbound (r : R) : |lam p*scalarIncrement ε
        (rowLinear (scaleRows A q (p,r)) s.x (β p) (scaleDirection A q ρ μ β ha hA hμ s ω))
        (rowQuadratic (scaleRows A q (p,r)) (β p) (scaleDirection A q ρ μ β ha hA hμ s ω))| ≤ 1 := by
      apply scalarIncrement_cap_small (K := 3*Real.sqrt (n:ℝ)+1) hε hε1 (by positivity)
      · have ht := rowLinear_abs_bound (scaleRows A q (p,r)) s.x _ (β p)
          (fun i => scaleEntry_abs_le q p _) hs.1 hβ (by linarith) hgeom.1
        simp only [Fintype.card_fin] at ht
        linarith
      · exact rowQuadratic_nonneg _ _ _ hβ
      · have ht := rowQuadratic_le_one (scaleRows A q (p,r)) _ (β p) hβ (by linarith)
          (fun i => scaleEntry_abs_le q p _) hgeom.1
        have hn := Real.sqrt_nonneg (n:ℝ)
        linarith
      · exact hlam
      · exact hsmall
    have hd (r : R) := hh r (by simpa only [Real.sq_sqrt hε,scalarIncrement] using hbound r)
    dsimp [columnRowPotential,columnProxy,columnPhaseWeight,scaleStep,scalarProxy,scalarIncrement]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    have hr := mul_le_mul_of_nonneg_left (hd r) (sq_nonneg (scaleEntry q p (A r j)))
    simp only [Real.sq_sqrt hε] at hr
    rw [show scaleRows A q (p,r)=(fun i => scaleEntry q p (A r i)) from rfl] at hr
    nlinarith
  · rw [columnProxy_stopped A q ρ μ β b lam ha hA hμ ε s p j hrun ω,add_zero]
    have he : scaleStep A q ρ μ β b ha hA hμ (Real.sqrt ε) s ω=s := by
      simp [scaleStep,adaptiveStep,hrun]
    rw [he]
end Komlos.KMFresh

-- END KMProof/ActualMediumLedger.lean

-- BEGIN KMProof/ScaleHistoryInvariant.lean

namespace Komlos.KMFresh

lemma scaleHistory_valid {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) (ht : 0 ≤ t) (htρ : t ≤ ρ)
    (hβ : ∀ p, 0 ≤ β p) (hb : ∀ p, 0 < b p)
    (hbudget : ∀ p, β p * (64 * (4 : ℝ)^p.val) ≤ b p)
    (k : ℕ) (ω : Fin k → (Fin n → Bool)) :
    rowStateValid (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1)
      (scaleHistory A q ρ μ β b ha hA hμ t k ω) := by
  apply adaptiveHistory_invariant ⟨0, ∅⟩ (fun _ => scaleStep A q ρ μ β b ha hA hμ t)
    (fun _ s => rowStateValid (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1) s)
  · exact rowStateValid_initial (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1)
      (fun z => hβ z.1) (fun z => hb z.1) (fun z => hbudget z.1)
  · intro _ s ω hs
    exact scaleStep_valid A q ρ μ β b ha hA hμ t ht htρ s ω hs

lemma scaleHistory_snoc {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) (k : ℕ) (ω : Fin k → (Fin n → Bool)) (u : Fin n → Bool) :
    scaleHistory A q ρ μ β b ha hA hμ t (k + 1) (Fin.snoc ω u) =
      scaleStep A q ρ μ β b ha hA hμ t (scaleHistory A q ρ μ β b ha hA hμ t k ω) u :=
  adaptiveHistory_snoc _ _ k ω u

end Komlos.KMFresh

-- END KMProof/ScaleHistoryInvariant.lean

-- BEGIN KMProof/ActualMediumTail.lean
noncomputable section
open Finset
namespace Komlos.KMFresh
variable {R : Type*} [Fintype R] {n : ℕ}

lemma actual_medium_tail (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ)
    (μ β b lam : Fin (q+1) → ℝ)
    (ha : ∀r i,|A r i| ≤ 1) (hA : ∀i,∑r,(A r i)^2 ≤ 2) (hμ : ∀p,0 < μ p)
    (hβ : ∀p,0 ≤ β p) (hb : ∀p,0 < b p)
    (hbudget : ∀p,β p*(64*(4:ℝ)^p.val) ≤ b p)
    (p : Fin (q+1)) (j : Fin n) {ε δ prob : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : Real.sqrt ε ≤ ρ)
    (hδ : 0 < δ) (hprob : 0 < prob) (hβsmall : β p ≤ 1/64) (hlam : 0 ≤ lam p)
    (hlθ : lam p ≤ (β p/16)/2)
    (hcancel : δ^2*((64*((q+1:ℕ):ℝ)*(4:ℝ)^p.val/μ p)*(lam p*Real.exp (lam p*(2*b p)))) ≤ δ*((β p/16)/2))
    (hcap : (2*lam p*(3*Real.sqrt (n:ℝ)+1))*Real.sqrt ε ≤ 1)
    (hsmall : δ*((3*Real.sqrt (n:ℝ)+1)*((Fintype.card R:ℝ)*(lam p*Real.exp (lam p*(2*b p))))+
      ((3*Real.sqrt (n:ℝ)+1)+4*lam p*(3*Real.sqrt (n:ℝ)+1)^2)*
        ((Fintype.card R:ℝ)*(lam p*Real.exp (lam p*(2*b p)))))*Real.sqrt ε ≤ 1)
    (N : ℕ)
    (herror : (N:ℝ)*(proxyErrorConstant δ (lam p) (3*Real.sqrt (n:ℝ)+1)
      ((Fintype.card R:ℝ)*(lam p*Real.exp (lam p*(2*b p))))*ε*Real.sqrt ε) ≤ 1) :
    (FiniteLaw.uniform (History (Fin n → Bool) N)).prob (fun h => ∃k:ℕ,∃hk:k ≤ N,
      ((∑r,(scaleEntry q p (A r j))^2)*Real.exp (lam p*b p)+(1-Real.log prob)/δ)/
        Real.exp (lam p*(2*b p)) ≤
      ∑r∈(scaleLocalState (scaleHistory A q ρ μ β b ha hA hμ (Real.sqrt ε) k (historyPrefix h k hk)) p).hit,
        (scaleEntry q p (A r j))^2) ≤ prob := by
  classical
  let T := scaleHistory A q ρ μ β b ha hA hμ (Real.sqrt ε)
  let w := fun r => (scaleEntry q p (A r j))^2
  let φ := fun k h r => columnRowPotential A q ρ μ β b lam (T k h) p j r
  let F := fun k h ω => columnProxy A q ρ μ β b lam ha hA hμ ε (T k h) p j ω
  let B := (∑r,w r)*Real.exp (lam p*b p)
  let H := Real.exp (lam p*(2*b p))
  let η := proxyErrorConstant δ (lam p) (3*Real.sqrt (n:ℝ)+1)
    ((Fintype.card R:ℝ)*(lam p*Real.exp (lam p*(2*b p))))*ε*Real.sqrt ε
  have hη : 0 ≤ η := by dsimp [η,proxyErrorConstant]; positivity
  have hv k h := scaleHistory_valid A q ρ μ β b ha hA hμ (Real.sqrt ε)
    (Real.sqrt_nonneg ε) hρ hβ hb hbudget k h
  have h0 : (∑r,φ 0 Fin.elim0 r) ≤ B :=
    columnRowPotential_initial A q ρ μ β b lam p j (hβ p) (hbudget p) hlam
  have hstep k h ω : (∑r,φ (k+1) (Fin.snoc h ω) r) ≤ (∑r,φ k h r)+F k h ω := by
    dsimp [φ,T,F]
    rw [scaleHistory_snoc]
    exact columnRowPotential_step A q ρ μ β b lam ha hA hμ _ (hv k h) p j hε.le hε1 hρ
      (hβ p) hβsmall (hb p) (hbudget p) hlam hcap ω
  have hφ k h r : 0 ≤ φ k h r :=
    mul_nonneg (sq_nonneg _) (phasePotential_nonneg _ _ _ _ _ _ _ _ _)
  have hhit k h r (hr : (p,r)∈(T k h).hit) : H*w r ≤ φ k h r := by
    dsimp [φ,columnRowPotential]
    rw [phasePotential_hit _ _ _ _ _ _ _ _ _ hr]
    dsimp [H,w]
    exact le_of_eq (mul_comm _ _)
  have hmgf k h : (FiniteLaw.uniform (Fin n → Bool)).mean (fun ω => Real.exp (δ*F k h ω)) ≤ Real.exp η := by
    by_cases hrun : scaleRunning A q ρ μ (T k h)
    · exact columnProxy_mgf_running A q ρ μ β b lam ha hA hμ _ hrun (hv k h) p j
        (hβ p) hβsmall hlam hε.le hε1 hδ.le hlθ hcancel hsmall
    · have he (ω) : F k h ω=0 := columnProxy_stopped A q ρ μ β b lam ha hA hμ ε _ p j hrun ω
      simp only [he,mul_zero,Real.exp_zero,FiniteLaw.mean_const]
      exact Real.one_le_exp hη
  have ht := weighted_potential_tail φ F w (fun k h r => (p,r)∈(T k h).hit)
    B H δ η prob hδ hη hprob h0 hstep hφ hhit hmgf N herror
  apply (FiniteLaw.prob_mono _ ?_).trans ht
  rintro h ⟨k,hk,hbad⟩
  refine ⟨k,hk,?_⟩
  have hb' := (div_le_iff₀ (Real.exp_pos (lam p*(2*b p)))).mp hbad
  dsimp [B,H,w]
  simpa only [scaleLocalState,mul_comm] using hb'
end Komlos.KMFresh

-- END KMProof/ActualMediumTail.lean

-- BEGIN KMProof/MediumCap.lean

namespace Komlos.KMFresh

lemma row_after_nontiny_bound {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b : R → ℝ) (s s' : AdaptiveState R n) (r : R)
    (hs : rowStateValid A ρ k μ β b s)
    (hcap : rowMedium A ρ k μ s.x r → rowRegularizer A ρ β s.x r ≤ 2 * b r + 1)
    (hβ : 0 ≤ β r) (hb : 0 < b r) (hbudget : β r * (64 * k r) ≤ b r)
    (ht : ¬rowTiny A ρ μ s.x r) (hl' : ¬rowLarge A ρ k s'.x r)
    (hlarge : rowLarge A ρ k s.x r → rowDiscrepancy A s'.x r = 0)
    (hsmall : rowMedium A ρ k μ s.x r → r ∉ s.hit →
      rowRegularizer A ρ β s'.x r ≤ rowRegularizer A ρ β s.x r + 1)
    (hblocked : rowMedium A ρ k μ s.x r → r ∈ s.hit →
      rowRegularizer A ρ β s'.x r ≤ rowRegularizer A ρ β s.x r) :
    rowRegularizer A ρ β s'.x r ≤ 2 * b r + 1 := by
  by_cases hl : rowLarge A ρ k s.x r
  · have hz := rowRegularizer_activation A ρ k β b s'.x r hβ hbudget (hlarge hl) hl'
    linarith
  · have hm : rowMedium A ρ k μ s.x r := ⟨lt_of_not_ge ht, le_of_not_gt hl⟩
    by_cases hr : r ∈ s.hit
    · exact (hblocked hm hr).trans (hcap hm)
    · have hz := hs.2.2 r hm hr
      have hn := hsmall hm hr
      linarith

lemma medium_cap_next {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b : R → ℝ) (s s' : AdaptiveState R n) (r : R)
    (hs : rowStateValid A ρ k μ β b s)
    (hcap : rowMedium A ρ k μ s.x r → rowRegularizer A ρ β s.x r ≤ 2 * b r + 1)
    (hβ : 0 ≤ β r) (hb : 0 < b r) (hbudget : β r * (64 * k r) ≤ b r)
    (henergy : rowEnergy A ρ s'.x r ≤ rowEnergy A ρ s.x r)
    (hlarge : rowLarge A ρ k s.x r → rowDiscrepancy A s'.x r = 0)
    (hsmall : rowMedium A ρ k μ s.x r → r ∉ s.hit →
      rowRegularizer A ρ β s'.x r ≤ rowRegularizer A ρ β s.x r + 1)
    (hblocked : rowMedium A ρ k μ s.x r → r ∈ s.hit →
      rowRegularizer A ρ β s'.x r ≤ rowRegularizer A ρ β s.x r)
    (hm' : rowMedium A ρ k μ s'.x r) :
    rowRegularizer A ρ β s'.x r ≤ 2 * b r + 1 := by
  have ht : ¬rowTiny A ρ μ s.x r := fun ht => not_lt_of_ge (henergy.trans ht) hm'.1
  exact row_after_nontiny_bound A ρ k μ β b s s' r hs hcap hβ hb hbudget ht
    (not_lt_of_ge hm'.2) hlarge hsmall hblocked

lemma tiny_entry_regularizer_bound {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (β βtiny b μ : R → ℝ) (x : Fin n → ℝ) (r : R)
    (hβ : 0 ≤ β r) (hβtiny : 0 ≤ βtiny r) (hx : ∀ i, |x i| ≤ 1)
    (hZ : rowRegularizer A ρ β x r ≤ 2 * b r + 1)
    (htiny : rowEnergy A ρ x r ≤ μ r) (hmass : βtiny r * μ r ≤ b r) :
    rowRegularizer A ρ βtiny x r ≤ 3 * b r + 1 := by
  have hd := (rowRegularizer_ge_discrepancy A ρ β x r hβ hx).trans hZ
  have he := rowRegularizer_le_energy A ρ βtiny x r hβtiny
  have hm := (mul_le_mul_of_nonneg_left htiny hβtiny).trans hmass
  linarith

end Komlos.KMFresh

-- END KMProof/MediumCap.lean

-- BEGIN KMProof/ScaleBlocking.lean

namespace Komlos.KMFresh

lemma mem_scaleDangerous {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ : Fin (q + 1) → ℝ)
    (s : AdaptiveState (Fin (q + 1) × R) n) (z : Fin (q + 1) × R) :
    z ∈ scaleDangerous (fun p r i => scaleEntry q p (A r i)) ρ
      (fun p => (4 : ℝ)^p.val) μ s ↔
    rowMedium (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val) (fun z => μ z.1) s.x z ∧ z ∈ s.hit := by
  classical
  constructor
  · intro hz
    have hd := (Finset.mem_filter.mp hz).2
    have hm := (Finset.mem_filter.mp hd).1
    have hh := (Finset.mem_filter.mp hd).2
    exact ⟨(Finset.mem_filter.mp hm).2, (Finset.mem_filter.mp hh).2⟩
  · rintro ⟨hm, hh⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ z, ?_⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ z.2, hm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ z.2, hh⟩

lemma scaleStep_hit_regularizer_decreases {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) (ht : 0 ≤ t) (htρ : t ≤ ρ)
    (s : AdaptiveState (Fin (q + 1) × R) n) (ω : Fin n → Bool)
    (hrun : scaleRunning A q ρ μ s) (hx : ∀ i, |s.x i| ≤ 1)
    (z : Fin (q + 1) × R) (hβ : 0 ≤ β z.1)
    (hm : rowMedium (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val) (fun z => μ z.1) s.x z)
    (hhit : z ∈ s.hit) :
    rowRegularizer (scaleRows A q) ρ (fun z => β z.1)
      (scaleStep A q ρ μ β b ha hA hμ t s ω).x z ≤
    rowRegularizer (scaleRows A q) ρ (fun z => β z.1) s.x z := by
  have hg := scaleDirection_geometry A q ρ μ β ha hA hμ s hrun ω
  have hd := scaleDirection_dangerous A q ρ μ β ha hA hμ s hrun ω z
    ((mem_scaleDangerous A q ρ μ s z).mpr ⟨hm, hhit⟩)
  have hlinear : rowLinear (scaleRows A q z) s.x (β z.1)
      (scaleDirection A q ρ μ β ha hA hμ s ω) = 0 := hd
  rw [supported_rowLinear (aliveSet ρ s.x) (scaleRows A q z) s.x
    (scaleDirection A q ρ μ β ha hA hμ s ω) (β z.1) hg.2.1] at hlinear
  have hy := supported_step_box ρ t s.x (scaleDirection A q ρ μ β ha hA hμ s ω)
    ht htρ hx hg.1 hg.2.1
  change rowRegularizer _ _ _ (adaptiveStep _ _ _ _ s ω).x z ≤ _
  rw [adaptiveStep_x _ _ _ t s ω hrun]
  exact blocked_regularizer_decreases (aliveSet ρ s.x)
    (aliveSet ρ (fun i => s.x i + t * scaleDirection A q ρ μ β ha hA hμ s ω i))
    (scaleRows A q z) s.x (scaleDirection A q ρ μ β ha hA hμ s ω) t (β z.1)
    (supported_step_alive ρ t s.x _ hg.2.1) hβ (fun i _ => hy i) hg.2.1 hlinear

end Komlos.KMFresh

-- END KMProof/ScaleBlocking.lean

-- BEGIN KMProof/SmallRowIncrement.lean

namespace Komlos.KMFresh

lemma unit_row_increment_le_one {n : ℕ} (a x v : Fin n → ℝ) (β t : ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hx : ∀ i, |x i| ≤ 1)
    (hβ : 0 ≤ β) (hβone : β ≤ 1) (hv : ∑ i, v i^2 = 1)
    (ht : 0 ≤ t) (_htone : t ≤ 1) (hsmall : 2 * (3 * Real.sqrt (n : ℝ) + 1) * t ≤ 1) :
    t * rowLinear a x β v - t^2 * rowQuadratic a β v ≤ 1 := by
  have hL := rowLinear_abs_bound a x v β ha hx hβ hβone hv
  simp only [Fintype.card_fin] at hL
  have hQ := rowQuadratic_nonneg a v β hβ
  have hLt := mul_le_mul_of_nonneg_left ((le_abs_self (rowLinear a x β v)).trans hL) ht
  have hn := Real.sqrt_nonneg (n : ℝ)
  have hquad := mul_nonneg (sq_nonneg t) hQ
  nlinarith

lemma scaleStep_small_regularizer {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) (htρ : t ≤ ρ)
    (hsmall : 2 * (3 * Real.sqrt (n : ℝ) + 1) * t ≤ 1)
    (s : AdaptiveState (Fin (q + 1) × R) n) (ω : Fin n → Bool)
    (hrun : scaleRunning A q ρ μ s) (hx : ∀ i, |s.x i| ≤ 1)
    (z : Fin (q + 1) × R) (hβ : 0 ≤ β z.1) (hβone : β z.1 ≤ 1) :
    rowRegularizer (scaleRows A q) ρ (fun z => β z.1)
      (scaleStep A q ρ μ β b ha hA hμ t s ω).x z ≤
    rowRegularizer (scaleRows A q) ρ (fun z => β z.1) s.x z + 1 := by
  have hg := scaleDirection_geometry A q ρ μ β ha hA hμ s hrun ω
  have hy := supported_step_box ρ t s.x (scaleDirection A q ρ μ β ha hA hμ s ω)
    ht htρ hx hg.1 hg.2.1
  have he := actual_row_increment (scaleRows A q) ρ (fun z => β z.1) s.x
    (scaleDirection A q ρ μ β ha hA hμ s ω) t z hβ hy hg.2.1
  have hi := unit_row_increment_le_one (scaleRows A q z) s.x
    (scaleDirection A q ρ μ β ha hA hμ s ω) (β z.1) t
    (fun i => scaleEntry_abs_le q z.1 (A z.2 i)) hx hβ hβone hg.1 ht htone hsmall
  change rowRegularizer _ _ _ (adaptiveStep _ _ _ _ s ω).x z ≤ _
  rw [adaptiveStep_x _ _ _ t s ω hrun]
  linarith

end Komlos.KMFresh

-- END KMProof/SmallRowIncrement.lean

-- BEGIN KMProof/ScaleMediumCap.lean

namespace Komlos.KMFresh

lemma scaleStep_medium_cap {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) (htρ : t ≤ ρ)
    (hsmall : 2 * (3 * Real.sqrt (n : ℝ) + 1) * t ≤ 1)
    (hβ : ∀ p, 0 ≤ β p) (hβone : ∀ p, β p ≤ 1) (hb : ∀ p, 0 < b p)
    (hbudget : ∀ p, β p * (64 * (4 : ℝ)^p.val) ≤ b p)
    (s : AdaptiveState (Fin (q + 1) × R) n) (ω : Fin n → Bool)
    (hs : rowStateValid (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1) s)
    (hcap : ∀ z, rowMedium (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val) (fun z => μ z.1) s.x z →
      rowRegularizer (scaleRows A q) ρ (fun z => β z.1) s.x z ≤ 2 * b z.1 + 1)
    (z : Fin (q + 1) × R)
    (hm' : rowMedium (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val) (fun z => μ z.1)
      (scaleStep A q ρ μ β b ha hA hμ t s ω).x z) :
    rowRegularizer (scaleRows A q) ρ (fun z => β z.1)
      (scaleStep A q ρ μ β b ha hA hμ t s ω).x z ≤ 2 * b z.1 + 1 := by
  by_cases hr : scaleRunning A q ρ μ s
  · have hg := scaleDirection_geometry A q ρ μ β ha hA hμ s hr ω
    have hfix : ∀ i, i ∉ aliveSet ρ s.x → s.x i + t * scaleDirection A q ρ μ β ha hA hμ s ω i = s.x i := by
      intro i hi
      rw [hg.2.1 i hi, mul_zero, add_zero]
    apply medium_cap_next (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1) s _ z hs (hcap z)
      (hβ z.1) (hb z.1) (hbudget z.1) _ _ _ _ hm'
    · change rowEnergy _ _ (adaptiveStep _ _ _ _ s ω).x z ≤ _
      rw [adaptiveStep_x _ _ _ t s ω hr]
      exact rowEnergy_decreases (scaleRows A q) ρ s.x _ z hfix
    · intro hl
      have hz : z ∈ scaleLarge A q ρ s.x := by
        classical
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hl⟩
      change rowDiscrepancy _ (adaptiveStep _ _ _ _ s ω).x z = _
      rw [adaptiveStep_x _ _ _ t s ω hr,
        blocked_row_unchanged (scaleRows A q) s.x _ t z (hg.2.2.2 z hz)]
      exact hs.2.1 z hl
    · intro _ _
      exact scaleStep_small_regularizer A q ρ μ β b ha hA hμ t ht htone htρ hsmall s ω hr hs.1 z (hβ z.1) (hβone z.1)
    · intro hm hh
      exact scaleStep_hit_regularizer_decreases A q ρ μ β b ha hA hμ t ht htρ s ω hr hs.1 z (hβ z.1) hm hh
  · have he : scaleStep A q ρ μ β b ha hA hμ t s ω = s := adaptiveStep_stopped _ _ _ t s ω hr
    rw [he] at hm' ⊢
    exact hcap z hm'

lemma scaleHistory_medium_cap {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) (htρ : t ≤ ρ)
    (hsmall : 2 * (3 * Real.sqrt (n : ℝ) + 1) * t ≤ 1)
    (hβ : ∀ p, 0 ≤ β p) (hβone : ∀ p, β p ≤ 1) (hb : ∀ p, 0 < b p)
    (hbudget : ∀ p, β p * (64 * (4 : ℝ)^p.val) ≤ b p)
    (k : ℕ) (ω : Fin k → (Fin n → Bool)) (z : Fin (q + 1) × R)
    (hm : rowMedium (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val) (fun z => μ z.1)
      (scaleHistory A q ρ μ β b ha hA hμ t k ω).x z) :
    rowRegularizer (scaleRows A q) ρ (fun z => β z.1)
      (scaleHistory A q ρ μ β b ha hA hμ t k ω).x z ≤ 2 * b z.1 + 1 := by
  induction k generalizing z with
  | zero =>
    have hd : rowDiscrepancy (scaleRows A q) (0 : Fin n → ℝ) z = 0 := by simp [rowDiscrepancy]
    have he := rowRegularizer_activation (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
      (fun z => β z.1) (fun z => b z.1) 0 z (hβ z.1) (hbudget z.1) hd (not_lt_of_ge hm.2)
    change rowRegularizer (scaleRows A q) ρ (fun z => β z.1) 0 z ≤ _
    linarith [hb z.1]
  | succ k ih =>
    have hs := scaleHistory_valid A q ρ μ β b ha hA hμ t ht htρ hβ hb hbudget k (Fin.init ω)
    exact scaleStep_medium_cap A q ρ μ β b ha hA hμ t ht htone htρ hsmall hβ hβone hb hbudget
      _ (ω (Fin.last k)) hs (fun z hz => ih (Fin.init ω) z hz) z hm

end Komlos.KMFresh

-- END KMProof/ScaleMediumCap.lean

-- BEGIN KMProof/ScaleTinyEntry.lean

namespace Komlos.KMFresh

lemma scaleStep_tiny_persistent {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) (s : AdaptiveState (Fin (q + 1) × R) n) (ω : Fin n → Bool)
    (z : Fin (q + 1) × R)
    (htiny : rowTiny (scaleRows A q) ρ (fun z => μ z.1) s.x z) :
    rowTiny (scaleRows A q) ρ (fun z => μ z.1)
      (scaleStep A q ρ μ β b ha hA hμ t s ω).x z := by
  by_cases hr : scaleRunning A q ρ μ s
  · change rowTiny _ _ _ (adaptiveStep _ _ _ _ s ω).x _
    rw [adaptiveStep_x _ _ _ t s ω hr]
    apply rowTiny_persistent (scaleRows A q) ρ (fun z => μ z.1) s.x _ z _ htiny
    intro i hi
    rw [(scaleDirection_geometry A q ρ μ β ha hA hμ s hr ω).2.1 i hi, mul_zero, add_zero]
  · have he : scaleStep A q ρ μ β b ha hA hμ t s ω = s := adaptiveStep_stopped _ _ _ t s ω hr
    rw [he]
    exact htiny

lemma scaleStep_tiny_entry {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b βtiny : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) (htρ : t ≤ ρ)
    (hsmall : 2 * (3 * Real.sqrt (n : ℝ) + 1) * t ≤ 1)
    (s : AdaptiveState (Fin (q + 1) × R) n) (ω : Fin n → Bool)
    (hs : rowStateValid (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1) s)
    (z : Fin (q + 1) × R) (hβ : 0 ≤ β z.1) (hβone : β z.1 ≤ 1) (hb : 0 < b z.1)
    (hbudget : β z.1 * (64 * (4 : ℝ)^z.1.val) ≤ b z.1)
    (hcap : rowMedium (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val) (fun z => μ z.1) s.x z →
      rowRegularizer (scaleRows A q) ρ (fun z => β z.1) s.x z ≤ 2 * b z.1 + 1)
    (hβtiny : 0 ≤ βtiny z.1) (hμupper : μ z.1 ≤ 64 * (4 : ℝ)^z.1.val)
    (hmass : βtiny z.1 * μ z.1 ≤ b z.1)
    (hold : ¬rowTiny (scaleRows A q) ρ (fun z => μ z.1) s.x z)
    (hnew : rowTiny (scaleRows A q) ρ (fun z => μ z.1)
      (scaleStep A q ρ μ β b ha hA hμ t s ω).x z) :
    rowRegularizer (scaleRows A q) ρ (fun z => βtiny z.1)
      (scaleStep A q ρ μ β b ha hA hμ t s ω).x z ≤ 3 * b z.1 + 1 := by
  have hr : scaleRunning A q ρ μ s := by
    by_contra hn
    have he : scaleStep A q ρ μ β b ha hA hμ t s ω = s := adaptiveStep_stopped _ _ _ t s ω hn
    rw [he] at hnew
    exact hold hnew
  have hg := scaleDirection_geometry A q ρ μ β ha hA hμ s hr ω
  have hbox := adaptiveStep_box (scaleRunning A q ρ μ) (scaleDirection A q ρ μ β ha hA hμ)
    (regularizedHit (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
      (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1)) t ρ s ω ht htρ hs.1
      (fun _ => hg.1) (fun _ => hg.2.1)
  apply tiny_entry_regularizer_bound (scaleRows A q) ρ (fun z => β z.1) (fun z => βtiny z.1)
    (fun z => b z.1) (fun z => μ z.1) _ z hβ hβtiny hbox _ hnew hmass
  apply row_after_nontiny_bound (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
    (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1) s _ z hs hcap hβ hb hbudget hold
    (not_lt_of_ge (hnew.trans hμupper))
  · intro hl
    have hz : z ∈ scaleLarge A q ρ s.x := by
      classical
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hl⟩
    change rowDiscrepancy _ (adaptiveStep _ _ _ _ s ω).x z = _
    rw [adaptiveStep_x _ _ _ t s ω hr,
      blocked_row_unchanged (scaleRows A q) s.x _ t z (hg.2.2.2 z hz)]
    exact hs.2.1 z hl
  · intro _ _
    exact scaleStep_small_regularizer A q ρ μ β b ha hA hμ t ht htone htρ hsmall s ω hr hs.1 z hβ hβone
  · intro hm hh
    exact scaleStep_hit_regularizer_decreases A q ρ μ β b ha hA hμ t ht htρ s ω hr hs.1 z hβ hm hh

end Komlos.KMFresh

-- END KMProof/ScaleTinyEntry.lean

-- BEGIN KMProof/ActualTinyIncrement.lean

namespace Komlos.KMFresh

noncomputable def actualTinyIncrement {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β _b βtiny : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (ε : ℝ) (s : AdaptiveState (Fin (q + 1) × R) n) (ω : Fin n → Bool)
    (z : Fin (q + 1) × R) : ℝ := by
  classical
  exact if scaleRunning A q ρ μ s ∧ rowTiny (scaleRows A q) ρ (fun z => μ z.1) s.x z then
    scalarIncrement ε
      (rowLinear (scaleRows A q z) s.x (βtiny z.1) (scaleDirection A q ρ μ β ha hA hμ s ω))
      (rowQuadratic (scaleRows A q z) (βtiny z.1) (scaleDirection A q ρ μ β ha hA hμ s ω))
  else 0

lemma actualTinyIncrement_before {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b βtiny : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (ε : ℝ) (s : AdaptiveState (Fin (q + 1) × R) n) (ω : Fin n → Bool)
    (z : Fin (q + 1) × R) (ht : ¬rowTiny (scaleRows A q) ρ (fun z => μ z.1) s.x z) :
    actualTinyIncrement A q ρ μ β b βtiny ha hA hμ ε s ω z = 0 := by
  classical
  simp only [actualTinyIncrement, ht, and_false, if_false]

lemma actualTinyIncrement_dominates {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b βtiny : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (ε : ℝ) (hε : 0 ≤ ε) (hερ : Real.sqrt ε ≤ ρ)
    (s : AdaptiveState (Fin (q + 1) × R) n) (ω : Fin n → Bool)
    (z : Fin (q + 1) × R) (hβt : 0 ≤ βtiny z.1) (hx : ∀ i, |s.x i| ≤ 1)
    (ht : rowTiny (scaleRows A q) ρ (fun z => μ z.1) s.x z) :
    rowRegularizer (scaleRows A q) ρ (fun z => βtiny z.1)
      (scaleStep A q ρ μ β b ha hA hμ (Real.sqrt ε) s ω).x z ≤
    rowRegularizer (scaleRows A q) ρ (fun z => βtiny z.1) s.x z +
      actualTinyIncrement A q ρ μ β b βtiny ha hA hμ ε s ω z := by
  classical
  by_cases hr : scaleRunning A q ρ μ s
  · have hg := scaleDirection_geometry A q ρ μ β ha hA hμ s hr ω
    have hy := supported_step_box ρ (Real.sqrt ε) s.x (scaleDirection A q ρ μ β ha hA hμ s ω)
      (Real.sqrt_nonneg ε) hερ hx hg.1 hg.2.1
    have he := actual_row_increment (scaleRows A q) ρ (fun z => βtiny z.1) s.x
      (scaleDirection A q ρ μ β ha hA hμ s ω) (Real.sqrt ε) z hβt hy hg.2.1
    rw [Real.sq_sqrt hε] at he
    change rowRegularizer _ _ _ (adaptiveStep _ _ _ _ s ω).x z ≤ _
    rw [adaptiveStep_x _ _ _ (Real.sqrt ε) s ω hr]
    simp only [actualTinyIncrement, hr, ht, and_self, if_true, scalarIncrement]
    linarith
  · have he : scaleStep A q ρ μ β b ha hA hμ (Real.sqrt ε) s ω = s :=
      adaptiveStep_stopped _ _ _ _ s ω hr
    rw [he]
    simp only [actualTinyIncrement, hr, false_and, if_false, add_zero]
    exact le_rfl

end Komlos.KMFresh

-- END KMProof/ActualTinyIncrement.lean

-- BEGIN KMProof/ActivationLedger.lean
noncomputable section
namespace Komlos.KMFresh
variable {Ω : Type*}

lemma activation_ledger (active : (k:ℕ) → History Ω k → Prop)
    (Z : (k:ℕ) → History Ω k → ℝ) (F : (k:ℕ) → History Ω k → Ω → ℝ) (B : ℝ)
    (h0 : active 0 Fin.elim0 → Z 0 Fin.elim0 ≤ B)
    (hpersist : ∀k h x,active k h → active (k+1) (Fin.snoc h x))
    (hzero : ∀k h x,¬active k h → F k h x=0)
    (hentry : ∀k h x,¬active k h → active (k+1) (Fin.snoc h x) → Z (k+1) (Fin.snoc h x) ≤ B)
    (hstep : ∀k h x,active k h → Z (k+1) (Fin.snoc h x) ≤ Z k h+F k h x)
    (k : ℕ) (h : History Ω k) :
    (¬active k h → historyAccumulation F k h=0) ∧
      (active k h → Z k h ≤ B+historyAccumulation F k h) := by
  induction k with
  | zero =>
    have he : h=Fin.elim0 := by funext i; exact Fin.elim0 i
    subst h
    simp only [historyAccumulation,add_zero]
    exact ⟨fun _ => True.intro,h0⟩
  | succ k ih =>
    let g := Fin.init h
    let x := h (Fin.last k)
    have he : Fin.snoc g x=h := Fin.snoc_init_self h
    have hi := ih g
    by_cases ha : active k g
    · have hn := hpersist k g x ha
      rw [he] at hn
      refine ⟨fun hh => (hh hn).elim,fun _ => ?_⟩
      have hz := hstep k g x ha
      rw [he] at hz
      have hb := hi.2 ha
      change Z (k+1) h ≤ B+(historyAccumulation F k g+F k g x)
      linarith
    · have hu : historyAccumulation F (k+1) h=0 := by
        change historyAccumulation F k g+F k g x=0
        rw [hi.1 ha,hzero k g x ha,add_zero]
      refine ⟨fun _ => hu,fun hn => ?_⟩
      have hz := hentry k g x ha (by simpa only [he] using hn)
      simpa only [he,hu,add_zero] using hz

variable [Fintype Ω] [Nonempty Ω]
lemma activated_history_tail (active : (k:ℕ) → History Ω k → Prop)
    (Z : (k:ℕ) → History Ω k → ℝ) (F : (k:ℕ) → History Ω k → Ω → ℝ) (B : ℝ)
    (h0 : active 0 Fin.elim0 → Z 0 Fin.elim0 ≤ B)
    (hpersist : ∀k h x,active k h → active (k+1) (Fin.snoc h x))
    (hzero : ∀k h x,¬active k h → F k h x=0)
    (hentry : ∀k h x,¬active k h → active (k+1) (Fin.snoc h x) → Z (k+1) (Fin.snoc h x) ≤ B)
    (hstep : ∀k h x,active k h → Z (k+1) (Fin.snoc h x) ≤ Z k h+F k h x)
    {δ η p : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hp : 0 < p)
    (hmgf : ∀k h,(FiniteLaw.uniform Ω).mean (fun x => Real.exp (δ*F k h x)) ≤ Real.exp η)
    (N : ℕ) (herror : (N:ℝ)*η ≤ 1) :
    (FiniteLaw.uniform (History Ω N)).prob (fun h => ∃k:ℕ,∃hk:k ≤ N,
      active k (historyPrefix h k hk) ∧ B+(1-Real.log p)/δ ≤ Z k (historyPrefix h k hk)) ≤ p := by
  apply (FiniteLaw.prob_mono _ ?_).trans (accumulated_proxy_tail F hδ hη hp hmgf N herror)
  rintro h ⟨k,hk,ha,hz⟩
  refine ⟨k,hk,?_⟩
  have hb := (activation_ledger active Z F B h0 hpersist hzero hentry hstep k (historyPrefix h k hk)).2 ha
  linarith
end Komlos.KMFresh

-- END KMProof/ActivationLedger.lean

-- BEGIN KMProof/ActualTinyLedger.lean

namespace Komlos.KMFresh

lemma actual_tiny_ledger {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b βtiny : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (hβ : ∀ p, 0 ≤ β p) (hβone : ∀ p, β p ≤ 1) (hb : ∀ p, 0 < b p)
    (hbudget : ∀ p, β p * (64 * (4 : ℝ)^p.val) ≤ b p)
    (ε : ℝ) (hε : 0 ≤ ε) (hεone : ε ≤ 1) (hερ : Real.sqrt ε ≤ ρ)
    (hsmall : 2 * (3 * Real.sqrt (n : ℝ) + 1) * Real.sqrt ε ≤ 1)
    (z : Fin (q + 1) × R) (hβtiny : 0 ≤ βtiny z.1)
    (hμupper : μ z.1 ≤ 64 * (4 : ℝ)^z.1.val) (hmass : βtiny z.1 * μ z.1 ≤ b z.1)
    (k : ℕ) (h : History (Fin n → Bool) k) :
    let T := scaleHistory A q ρ μ β b ha hA hμ (Real.sqrt ε)
    let F := fun k h ω => actualTinyIncrement A q ρ μ β b βtiny ha hA hμ ε (T k h) ω z
    (¬rowTiny (scaleRows A q) ρ (fun z => μ z.1) (T k h).x z → historyAccumulation F k h = 0) ∧
    (rowTiny (scaleRows A q) ρ (fun z => μ z.1) (T k h).x z →
      rowRegularizer (scaleRows A q) ρ (fun z => βtiny z.1) (T k h).x z ≤
        (3 * b z.1 + 1) + historyAccumulation F k h) := by
  let T := scaleHistory A q ρ μ β b ha hA hμ (Real.sqrt ε)
  let F := fun k h ω => actualTinyIncrement A q ρ μ β b βtiny ha hA hμ ε (T k h) ω z
  have htone : Real.sqrt ε ≤ 1 := by nlinarith [Real.sq_sqrt hε, Real.sqrt_nonneg ε]
  have hv k h := scaleHistory_valid A q ρ μ β b ha hA hμ (Real.sqrt ε)
    (Real.sqrt_nonneg ε) hερ hβ hb hbudget k h
  apply activation_ledger (fun k h => rowTiny (scaleRows A q) ρ (fun z => μ z.1) (T k h).x z)
    (fun k h => rowRegularizer (scaleRows A q) ρ (fun z => βtiny z.1) (T k h).x z)
    F (3 * b z.1 + 1)
  · intro htiny
    have he := rowRegularizer_le_energy (scaleRows A q) ρ (fun z => βtiny z.1) 0 z hβtiny
    have hd : rowDiscrepancy (scaleRows A q) (0 : Fin n → ℝ) z = 0 := by simp [rowDiscrepancy]
    rw [hd, zero_add] at he
    have hh := (mul_le_mul_of_nonneg_left htiny hβtiny).trans hmass
    change βtiny z.1 * rowEnergy (scaleRows A q) ρ 0 z ≤ b z.1 at hh
    change rowRegularizer (scaleRows A q) ρ (fun z => βtiny z.1) 0 z ≤ _
    linarith [hb z.1]
  · intro k h ω htiny
    dsimp [T]
    rw [scaleHistory_snoc]
    exact scaleStep_tiny_persistent A q ρ μ β b ha hA hμ (Real.sqrt ε) _ ω z htiny
  · intro k h ω htiny
    exact actualTinyIncrement_before A q ρ μ β b βtiny ha hA hμ ε _ ω z htiny
  · intro k h ω hold hnew
    dsimp [T] at hnew ⊢
    rw [scaleHistory_snoc] at hnew ⊢
    exact scaleStep_tiny_entry A q ρ μ β b βtiny ha hA hμ (Real.sqrt ε) (Real.sqrt_nonneg ε)
      htone hερ hsmall _ ω (hv k h) z (hβ z.1) (hβone z.1) (hb z.1) (hbudget z.1)
      (fun hm => scaleHistory_medium_cap A q ρ μ β b ha hA hμ (Real.sqrt ε)
        (Real.sqrt_nonneg ε) htone hερ hsmall hβ hβone hb hbudget k h z hm)
      hβtiny hμupper hmass hold hnew
  · intro k h ω htiny
    dsimp [T]
    rw [scaleHistory_snoc]
    exact actualTinyIncrement_dominates A q ρ μ β b βtiny ha hA hμ ε hε hερ _ ω z hβtiny (hv k h).1 htiny

end Komlos.KMFresh

-- END KMProof/ActualTinyLedger.lean

-- BEGIN KMProof/TinyRowMoments.lean

namespace Komlos.KMFresh

lemma tiny_modified_coefficient_sq (a x β : ℝ) (ha : |a| ≤ 1) (hx : |x| ≤ 1)
    (hβ : 0 ≤ β) (hβone : β ≤ 1) :
    (a - 2 * β * a ^ 2 * x) ^ 2 ≤ 9 * a ^ 2 := by
  have hc := modified_coefficient_abs a x β ha hx hβ
  have ha0 := abs_nonneg a
  have he := sq_abs a
  have hb : |a - 2 * β * a ^ 2 * x| ≤ 3 * |a| := by
    nlinarith [mul_le_mul_of_nonneg_right hβone ha0]
  have h0 := abs_nonneg (a - 2 * β * a ^ 2 * x)
  have hs := sq_abs (a - 2 * β * a ^ 2 * x)
  have hm := mul_self_le_mul_self h0 hb
  nlinarith

lemma tiny_row_variance {I Ω : Type*} [Fintype I] [Fintype Ω]
    (P : FiniteLaw Ω) (a x : I → ℝ) (β : ℝ) (v : Ω → I → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hx : ∀ i, |x i| ≤ 1)
    (hβ : 0 ≤ β) (hβone : β ≤ 1)
    (hcov : ∀ c : I → ℝ, P.mean (fun ω => (∑ i, c i * v ω i) ^ 2) ≤
      8 * ∑ i, c i ^ 2 * P.mean (fun ω => v ω i ^ 2)) :
    P.mean (fun ω => rowLinear a x β (v ω) ^ 2) ≤
      72 * ∑ i, a i ^ 2 * P.mean (fun ω => v ω i ^ 2) := by
  have hs : (∑ i, (a i - 2 * β * a i ^ 2 * x i) ^ 2 * P.mean (fun ω => v ω i ^ 2)) ≤
      9 * ∑ i, a i ^ 2 * P.mean (fun ω => v ω i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hm := mul_le_mul_of_nonneg_right (tiny_modified_coefficient_sq (a i) (x i) β (ha i) (hx i) hβ hβone)
      (P.mean_nonneg (fun ω => sq_nonneg (v ω i)))
    nlinarith
  have hc := hcov (fun i => a i - 2 * β * a i ^ 2 * x i)
  change P.mean (fun ω => rowLinear a x β (v ω) ^ 2) ≤ _ at hc
  linarith

lemma tiny_drift_dominates_variance {I Ω : Type*} [Fintype I] [Fintype Ω]
    (P : FiniteLaw Ω) (a x : I → ℝ) (β : ℝ) (v : Ω → I → ℝ)
    (hβ : 0 ≤ β)
    (hv : P.mean (fun ω => rowLinear a x β (v ω) ^ 2) ≤
      72 * ∑ i, a i ^ 2 * P.mean (fun ω => v ω i ^ 2)) :
    β / 72 * P.mean (fun ω => rowLinear a x β (v ω) ^ 2) ≤
      P.mean (fun ω => rowQuadratic a β (v ω)) := by
  rw [rowQuadratic_mean]
  have hm := mul_le_mul_of_nonneg_left hv (show 0 ≤ β / 72 by positivity)
  nlinarith

end Komlos.KMFresh

-- END KMProof/TinyRowMoments.lean

-- BEGIN KMProof/SampledTinyProxy.lean
noncomputable section
open Matrix Finset
namespace Komlos.KMFresh

lemma sampled_tiny_increment_mgf {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (ht : 0 < X.trace)
    (hbase : ((8:ℝ) • Matrix.diagonal X.diag-X).PosSemidef)
    (a x : Fin n → ℝ) {β ε δ : ℝ} (hβ : 0 ≤ β) (hβone : β ≤ 1)
    (ha : ∀i,|a i| ≤ 1) (hx : ∀i,|x i| ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ)
    (hcancel : δ^2 ≤ δ*((β/72)/2))
    (hsmall : δ*(2*(3*Real.sqrt (n:ℝ)+1))*Real.sqrt ε ≤ 1) :
    (FiniteLaw.uniform (Fin n → Bool)).mean (fun s => Real.exp
      (δ*scalarIncrement ε (rowLinear a x β (fun i => matrixSample hX s i))
        (rowQuadratic a β (fun i => matrixSample hX s i)))) ≤
    Real.exp ((δ^2*(3*(3*Real.sqrt (n:ℝ)+1)^2))*ε*Real.sqrt ε) := by
  let P := FiniteLaw.uniform (Fin n → Bool)
  let L := fun s => rowLinear a x β (fun i => matrixSample hX s i)
  let Q := fun s => rowQuadratic a β (fun i => matrixSample hX s i)
  let K := 3*Real.sqrt (n:ℝ)+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL (s) : |L s| ≤ K := by
    have hh := rowLinear_abs_bound a x (fun i => matrixSample hX s i) β ha hx hβ hβone
      (matrixSample_square_sum hX ht s)
    simp only [Fintype.card_fin] at hh
    dsimp [K,L]
    linarith
  have hQ0 (s) : 0 ≤ Q s := rowQuadratic_nonneg _ _ β hβ
  have hQ (s) : Q s ≤ K := by
    have hh := rowQuadratic_le_one a (fun i => matrixSample hX s i) β hβ hβone ha
      (matrixSample_square_sum hX ht s)
    dsimp [K,Q]
    have hn := Real.sqrt_nonneg (n:ℝ)
    linarith
  have hd : (β/72)*P.mean (fun s => (L s)^2) ≤ P.mean Q := by
    apply tiny_drift_dominates_variance _ _ _ _ _ hβ
    exact tiny_row_variance _ a x β _ ha hx hβ hβone
      (fun c => matrixSample_variance_bound hX ht 8 hbase c)
  have hm : P.mean (fun s => scalarIncrement ε (L s) (Q s)) = -ε*P.mean Q := by
    simp only [scalarIncrement,P.mean_sub,P.mean_mul,sampled_row_mean_zero hX a x β,mul_zero,zero_sub,neg_mul,P,L]
  have hs : 0 ≤ P.mean (fun s => (L s)^2) := P.mean_nonneg (fun s => sq_nonneg _)
  have hmean : P.mean (fun s => scalarIncrement ε (L s) (Q s)) ≤
      -((β/72)/2)*ε*P.mean (fun s => (L s)^2)+0*ε^2 := by
    rw [hm]
    have hh := mul_le_mul_of_nonneg_left hd hε
    have hh0 := mul_nonneg (mul_nonneg (show 0 ≤ β/72 by positivity) hε) hs
    nlinarith
  have hr (s) : |scalarIncrement ε (L s) (Q s)-Real.sqrt ε*L s| ≤ K*ε := by
    dsimp [scalarIncrement]
    rw [sub_sub_cancel_left,abs_neg,abs_mul,abs_of_nonneg hε,abs_of_nonneg (hQ0 s)]
    nlinarith [mul_le_mul_of_nonneg_left (hQ s) hε]
  have hh := finite_proxy_exponential P L (fun s => scalarIncrement ε (L s) (Q s))
    (B := 1) hε hε1 hδ hs (by norm_num : (0:ℝ) ≤ 0) hK hK hL hr hmean
    (by simp only [one_mul]; exact le_refl _) (by simpa using hcancel)
    (by dsimp [K]; nlinarith [hsmall])
  convert hh using 1
  dsimp [K]
  ring
end Komlos.KMFresh

-- END KMProof/SampledTinyProxy.lean

-- BEGIN KMProof/ActualTinyMGF.lean

namespace Komlos.KMFresh

lemma actualTinyIncrement_mgf {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b βtiny : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (s : AdaptiveState (Fin (q + 1) × R) n) (z : Fin (q + 1) × R)
    (hx : ∀ i, |s.x i| ≤ 1) {ε δ : ℝ}
    (hβt : 0 ≤ βtiny z.1) (hβt1 : βtiny z.1 ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ)
    (hcancel : δ^2 ≤ δ*((βtiny z.1/72)/2))
    (hsmall : δ*(2*(3*Real.sqrt (n:ℝ)+1))*Real.sqrt ε ≤ 1) :
    (FiniteLaw.uniform (Fin n → Bool)).mean (fun ω => Real.exp
      (δ*actualTinyIncrement A q ρ μ β b βtiny ha hA hμ ε s ω z)) ≤
    Real.exp ((δ^2*(3*(3*Real.sqrt (n:ℝ)+1)^2))*ε*Real.sqrt ε) := by
  classical
  by_cases hr : scaleRunning A q ρ μ s ∧ rowTiny (scaleRows A q) ρ (fun z => μ z.1) s.x z
  · let C := chooseScaleMatrix A q ρ μ β ha hA hμ s hr.1
    have hh := sampled_tiny_increment_mgf C.psd
      (chosenScaleMatrix_trace_pos A q ρ μ β ha hA hμ s hr.1) C.base
      (scaleRows A q z) s.x hβt hβt1 (fun i => scaleEntry_abs_le q z.1 (A z.2 i))
      hx hε hε1 hδ hcancel hsmall
    simpa only [actualTinyIncrement, if_pos hr,
      scaleDirection_running A q ρ μ β ha hA hμ s hr.1] using hh
  · simp only [actualTinyIncrement, if_neg hr, mul_zero, Real.exp_zero,
      FiniteLaw.mean_const]
    exact Real.one_le_exp (by positivity)

end Komlos.KMFresh

-- END KMProof/ActualTinyMGF.lean

-- BEGIN KMProof/ActualTinyTail.lean

noncomputable section
namespace Komlos.KMFresh

lemma actual_tiny_tail {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b βtiny : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (hβ : ∀ p, 0 ≤ β p) (hβone : ∀ p, β p ≤ 1) (hb : ∀ p, 0 < b p)
    (hbudget : ∀ p, β p * (64 * (4 : ℝ)^p.val) ≤ b p)
    (ε : ℝ) (hε : 0 ≤ ε) (hεone : ε ≤ 1) (hερ : Real.sqrt ε ≤ ρ)
    (hsmall : 2 * (3 * Real.sqrt (n : ℝ) + 1) * Real.sqrt ε ≤ 1)
    (z : Fin (q + 1) × R) (hβtiny : 0 ≤ βtiny z.1)
    (hμupper : μ z.1 ≤ 64 * (4 : ℝ)^z.1.val) (hmass : βtiny z.1 * μ z.1 ≤ b z.1)
    (hβtiny1 : βtiny z.1 ≤ 1) {δ prob : ℝ} (hδ : 0 < δ) (hp : 0 < prob)
    (hcancel : δ^2 ≤ δ*((βtiny z.1/72)/2))
    (hmgfsmall : δ*(2*(3*Real.sqrt (n:ℝ)+1))*Real.sqrt ε ≤ 1)
    (N : ℕ) (herror : (N:ℝ)*((δ^2*(3*(3*Real.sqrt (n:ℝ)+1)^2))*ε*Real.sqrt ε) ≤ 1) :
    let T := scaleHistory A q ρ μ β b ha hA hμ (Real.sqrt ε)
    (FiniteLaw.uniform (History (Fin n → Bool) N)).prob (fun h => ∃k:ℕ,∃hk:k ≤ N,
      rowTiny (scaleRows A q) ρ (fun z => μ z.1) (T k (historyPrefix h k hk)).x z ∧
      (3*b z.1+1)+(1-Real.log prob)/δ ≤
        rowRegularizer (scaleRows A q) ρ (fun z => βtiny z.1) (T k (historyPrefix h k hk)).x z) ≤ prob := by
  classical
  let T := scaleHistory A q ρ μ β b ha hA hμ (Real.sqrt ε)
  let F := fun k h ω => actualTinyIncrement A q ρ μ β b βtiny ha hA hμ ε (T k h) ω z
  have hmgf k h : (FiniteLaw.uniform (Fin n → Bool)).mean (fun ω => Real.exp (δ*F k h ω)) ≤
      Real.exp ((δ^2*(3*(3*Real.sqrt (n:ℝ)+1)^2))*ε*Real.sqrt ε) := by
    have hv := scaleHistory_valid A q ρ μ β b ha hA hμ (Real.sqrt ε)
      (Real.sqrt_nonneg ε) hερ hβ hb hbudget k h
    exact actualTinyIncrement_mgf A q ρ μ β b βtiny ha hA hμ (T k h) z hv.1
      hβtiny hβtiny1 hε hεone hδ.le hcancel hmgfsmall
  apply (FiniteLaw.prob_mono _ ?_).trans
    (accumulated_proxy_tail F hδ (by positivity) hp hmgf N herror)
  rintro h ⟨k,hk,ht,hz⟩
  refine ⟨k,hk,?_⟩
  have hbnd := (actual_tiny_ledger A q ρ μ β b βtiny ha hA hμ hβ hβone hb hbudget
    ε hε hεone hερ hsmall z hβtiny hμupper hmass k (historyPrefix h k hk)).2 ht
  change rowRegularizer _ _ _ _ z ≤ (3*b z.1+1)+historyAccumulation F k (historyPrefix h k hk) at hbnd
  linarith

end Komlos.KMFresh

-- END KMProof/ActualTinyTail.lean

-- BEGIN KMProof/ActualGoodHistory.lean

noncomputable section
namespace Komlos.KMFresh
variable {R : Type*} [Fintype R] {n : ℕ}

structure MediumTailConditions (q n rows : ℕ) (μ β b lam : Fin (q+1) → ℝ)
    (ε : ℝ) (N : ℕ) (p : Fin (q+1)) where
  delta : ℝ
  positive : 0 < delta
  beta_small : β p ≤ 1/64
  lambda_nonneg : 0 ≤ lam p
  lambda_drift : lam p ≤ (β p/16)/2
  cancel : delta^2*((64*((q+1:ℕ):ℝ)*(4:ℝ)^p.val/μ p)*(lam p*Real.exp (lam p*(2*b p)))) ≤ delta*((β p/16)/2)
  cap : (2*lam p*(3*Real.sqrt (n:ℝ)+1))*Real.sqrt ε ≤ 1
  small : delta*((3*Real.sqrt (n:ℝ)+1)*((rows:ℝ)*(lam p*Real.exp (lam p*(2*b p))))+
      ((3*Real.sqrt (n:ℝ)+1)+4*lam p*(3*Real.sqrt (n:ℝ)+1)^2)*
        ((rows:ℝ)*(lam p*Real.exp (lam p*(2*b p)))))*Real.sqrt ε ≤ 1
  error : (N:ℝ)*(proxyErrorConstant delta (lam p) (3*Real.sqrt (n:ℝ)+1)
      ((rows:ℝ)*(lam p*Real.exp (lam p*(2*b p))))*ε*Real.sqrt ε) ≤ 1
  threshold : ∀d:ℝ,d ≤ 2*(4:ℝ)^p.val →
    (d*Real.exp (lam p*b p)+(1-Real.log (confidence n))/delta)/Real.exp (lam p*(2*b p)) ≤
      μ p/(64*((q+1:ℕ):ℝ))

structure TinyTailConditions (q n : ℕ) (μ b βtiny : Fin (q+1) → ℝ)
    (ε : ℝ) (N : ℕ) (p : Fin (q+1)) where
  delta : ℝ
  positive : 0 < delta
  beta_nonneg : 0 ≤ βtiny p
  beta_one : βtiny p ≤ 1
  mu_upper : μ p ≤ 64*(4:ℝ)^p.val
  mass : βtiny p*μ p ≤ b p
  cancel : delta^2 ≤ delta*((βtiny p/72)/2)
  small : delta*(2*(3*Real.sqrt (n:ℝ)+1))*Real.sqrt ε ≤ 1
  error : (N:ℝ)*((delta^2*(3*(3*Real.sqrt (n:ℝ)+1)^2))*ε*Real.sqrt ε) ≤ 1

lemma actual_good_history (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b lam βtiny : Fin (q+1) → ℝ)
    (ha : ∀r i,|A r i| ≤ 1) (hA : ∀i,∑r,(A r i)^2 ≤ 2) (hμ : ∀p,0 < μ p)
    (hβ : ∀p,0 ≤ β p) (hβone : ∀p,β p ≤ 1) (hb : ∀p,0 < b p)
    (hbudget : ∀p,β p*(64*(4:ℝ)^p.val) ≤ b p)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1) (hρ : Real.sqrt ε ≤ ρ)
    (hraw : 2*(3*Real.sqrt (n:ℝ)+1)*Real.sqrt ε ≤ 1)
    (N : ℕ) (hR : Fintype.card R ≤ 2*n^3) (hP : q+1 ≤ n+2)
    (eligible tinyEligible : Fin (q+1) → Prop)
    (hm : ∀p,eligible p → MediumTailConditions q n (Fintype.card R) μ β b lam ε N p)
    (ht : ∀p,tinyEligible p → TinyTailConditions q n μ b βtiny ε N p)
    (rowBound : Fin (q+1) → ℝ)
    (hrowBound : ∀p (hp:tinyEligible p),3*b p+1+(1-Real.log (confidence n))/(ht p hp).delta ≤ rowBound p)
    (hinactive : ∀p,¬eligible p → ∀k (h:History (Fin n → Bool) k) j,
      (∑r∈(scaleLocalState (scaleHistory A q ρ μ β b ha hA hμ (Real.sqrt ε) k h) p).hit,
        (scaleEntry q p (A r j))^2) ≤ μ p/(64*((q+1:ℕ):ℝ))) :
    ∃h : History (Fin n → Bool) N,
      (∀p j k (hk:k ≤ N),
        (∑r∈(scaleLocalState (scaleHistory A q ρ μ β b ha hA hμ (Real.sqrt ε) k (historyPrefix h k hk)) p).hit,
          (scaleEntry q p (A r j))^2) ≤ μ p/(64*((q+1:ℕ):ℝ))) ∧
      (∀p r,tinyEligible p → ∀k (hk:k ≤ N),
        rowTiny (scaleRows A q) ρ (fun z => μ z.1)
          (scaleHistory A q ρ μ β b ha hA hμ (Real.sqrt ε) k (historyPrefix h k hk)).x (p,r) →
        rowRegularizer (scaleRows A q) ρ (fun z => βtiny z.1)
          (scaleHistory A q ρ μ β b ha hA hμ (Real.sqrt ε) k (historyPrefix h k hk)).x (p,r) < rowBound p) := by
  classical
  let T := scaleHistory A q ρ μ β b ha hA hμ (Real.sqrt ε)
  apply exists_good_history_events n q N hR hP
    (fun p j k h => ∑r∈(scaleLocalState (T k h) p).hit,(scaleEntry q p (A r j))^2)
    (fun p r k h => rowRegularizer (scaleRows A q) ρ (fun z => βtiny z.1) (T k h).x (p,r))
    (fun p r k h => rowTiny (scaleRows A q) ρ (fun z => μ z.1) (T k h).x (p,r))
    tinyEligible (fun p => μ p/(64*((q+1:ℕ):ℝ))) rowBound
  · intro p j
    by_cases he : eligible p
    · let C := hm p he
      have hh := actual_medium_tail A q ρ μ β b lam ha hA hμ hβ hb hbudget p j hε hεone hρ
        C.positive (confidence_pos n) C.beta_small C.lambda_nonneg C.lambda_drift C.cancel C.cap C.small N C.error
      apply (FiniteLaw.prob_mono _ ?_).trans hh
      rintro h ⟨k,hk,hbad⟩
      refine ⟨k,hk,?_⟩
      have hmass := single_scale_column_bound A q p j (fun r => ha r j) (hA j)
      exact (C.threshold _ hmass).trans hbad.le
    · have hf : (fun h : History (Fin n → Bool) N => ∃k:ℕ,∃hk:k ≤ N,
          μ p/(64*((q+1:ℕ):ℝ)) < ∑r∈(scaleLocalState (T k (historyPrefix h k hk)) p).hit,
            (scaleEntry q p (A r j))^2) = (fun _ => False) := by
        funext h
        apply propext
        constructor
        · rintro ⟨k,hk,hbad⟩
          exact (not_lt_of_ge (hinactive p he k (historyPrefix h k hk) j)) hbad
        · exact False.elim
      rw [hf,FiniteLaw.prob_false]
      exact (confidence_pos n).le
  · intro p r he
    let C := ht p he
    have hh := actual_tiny_tail A q ρ μ β b βtiny ha hA hμ hβ hβone hb hbudget
      ε hε.le hεone hρ hraw (p,r) C.beta_nonneg C.mu_upper C.mass C.beta_one
      C.positive (confidence_pos n) C.cancel C.small N C.error
    apply (FiniteLaw.prob_mono _ ?_).trans hh
    rintro h ⟨k,hk,ha,hbad⟩
    exact ⟨k,hk,ha,(hrowBound p he).trans hbad⟩

end Komlos.KMFresh

-- END KMProof/ActualGoodHistory.lean

-- BEGIN KMProof/SmallStep.lean

namespace Komlos.KMFresh

lemma exists_small_step (ρ K : ℝ) (hρ : 0 < ρ) (hK : 0 ≤ K) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t ≤ ρ ∧ K * t ≤ 1 := by
  let t := min (1 : ℝ) (min ρ (1 / (K + 1)))
  have hd : 0 < K + 1 := by linarith
  have ht : 0 < t := lt_min zero_lt_one (lt_min hρ (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htρ : t ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have htd : t ≤ 1 / (K + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hm := (le_div_iff₀ hd).mp htd
  refine ⟨t, ht, ht1, htρ, ?_⟩
  nlinarith

lemma exists_small_epsilon (ρ K : ℝ) (hρ : 0 < ρ) (hK : 0 ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ Real.sqrt ε ≤ ρ ∧ K * Real.sqrt ε ≤ 1 := by
  obtain ⟨t, ht, ht1, htρ, hKt⟩ := exists_small_step ρ K hρ hK
  refine ⟨t ^ 2, sq_pos_of_pos ht, ?_, ?_, ?_⟩
  · nlinarith
  · simpa only [Real.sqrt_sq ht.le] using htρ
  · simpa only [Real.sqrt_sq ht.le] using hKt

end Komlos.KMFresh

-- END KMProof/SmallStep.lean

-- BEGIN KMProof/WalkHorizon.lean

namespace Komlos.KMFresh

noncomputable def walkHorizon (n : ℕ) (ε : ℝ) : ℕ := ⌊(n : ℝ) / ε⌋₊ + 1

lemma walkHorizon_lower (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (n : ℝ) < (walkHorizon n ε : ℝ) * ε := by
  have h := Nat.lt_floor_add_one ((n : ℝ) / ε)
  have hm := (div_lt_iff₀ hε).mp h
  simpa only [walkHorizon, Nat.cast_add, Nat.cast_one] using hm

lemma walkHorizon_upper (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (walkHorizon n ε : ℝ) * ε ≤ (n : ℝ) + ε := by
  have h := Nat.floor_le (show 0 ≤ (n : ℝ) / ε by positivity)
  have hm := (le_div_iff₀ hε).mp h
  unfold walkHorizon
  push_cast
  nlinarith

lemma walkHorizon_time (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    (walkHorizon n ε : ℝ) * ε ≤ (n : ℝ) + 1 := by
  have h := walkHorizon_upper n hε
  linarith

lemma walkHorizon_error (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    (walkHorizon n ε : ℝ) * (ε * Real.sqrt ε) ≤ ((n : ℝ) + 1) * Real.sqrt ε := by
  have h := mul_le_mul_of_nonneg_right (walkHorizon_time n hε hεone) (Real.sqrt_nonneg ε)
  simpa only [mul_assoc] using h

end Komlos.KMFresh

-- END KMProof/WalkHorizon.lean

-- BEGIN KMProof/UniformStep.lean
noncomputable section
namespace Komlos.KMFresh

lemma exists_uniform_epsilon {I : Type*} [Fintype I]
    (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (A C : I → ℝ) (hC : ∀i,0 ≤ C i) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ Real.sqrt ε ≤ ρ ∧
      (∀i,A i*Real.sqrt ε ≤ 1) ∧
      (∀i,(walkHorizon n ε:ℝ)*(C i*ε*Real.sqrt ε) ≤ 1) := by
  let K := (∑i,|A i|)+((n:ℝ)+1)*(∑i,C i)
  have hsum : 0 ≤ ∑i,C i := Finset.sum_nonneg (fun i _ => hC i)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨ε,hε,hε1,hερ,hKe⟩ := exists_small_epsilon ρ K hρ hK
  refine ⟨ε,hε,hε1,hερ,?_,?_⟩
  · intro i
    have hi : |A i| ≤ ∑j,|A j| := Finset.single_le_sum (fun j _ => abs_nonneg (A j)) (Finset.mem_univ i)
    have hik : A i ≤ K := by dsimp [K]; have h := le_abs_self (A i); nlinarith
    exact (mul_le_mul_of_nonneg_right hik (Real.sqrt_nonneg ε)).trans hKe
  · intro i
    have hi : C i ≤ ∑j,C j := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
    have hik : ((n:ℝ)+1)*C i ≤ K := by
      have hm := mul_le_mul_of_nonneg_left hi (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)
      have ha : 0 ≤ ∑j,|A j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
      dsimp [K]
      linarith
    have ht := mul_le_mul_of_nonneg_left (walkHorizon_error n hε hε1) (hC i)
    have hb := (mul_le_mul_of_nonneg_right hik (Real.sqrt_nonneg ε)).trans hKe
    nlinarith
end Komlos.KMFresh

-- END KMProof/UniformStep.lean

-- BEGIN KMProof/TailConditionStep.lean

noncomputable section
namespace Komlos.KMFresh

structure MediumTailCore (q n rows : ℕ) (μ β b lam : Fin (q+1) → ℝ)
    (p : Fin (q+1)) where
  delta : ℝ
  positive : 0 < delta
  beta_small : β p ≤ 1/64
  lambda_nonneg : 0 ≤ lam p
  lambda_drift : lam p ≤ (β p/16)/2
  cancel : delta^2*((64*((q+1:ℕ):ℝ)*(4:ℝ)^p.val/μ p)*(lam p*Real.exp (lam p*(2*b p)))) ≤ delta*((β p/16)/2)
  threshold : ∀d:ℝ,d ≤ 2*(4:ℝ)^p.val →
    (d*Real.exp (lam p*b p)+(1-Real.log (confidence n))/delta)/Real.exp (lam p*(2*b p)) ≤
      μ p/(64*((q+1:ℕ):ℝ))

structure TinyTailCore (q n : ℕ) (μ b βtiny : Fin (q+1) → ℝ)
    (p : Fin (q+1)) where
  delta : ℝ
  positive : 0 < delta
  beta_nonneg : 0 ≤ βtiny p
  beta_one : βtiny p ≤ 1
  mu_upper : μ p ≤ 64*(4:ℝ)^p.val
  mass : βtiny p*μ p ≤ b p
  cancel : delta^2 ≤ delta*((βtiny p/72)/2)

lemma exists_tail_condition_step (q n rows : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (μ β b lam βtiny : Fin (q+1) → ℝ)
    (eligible tinyEligible : Fin (q+1) → Prop)
    (M : ∀p,eligible p → MediumTailCore q n rows μ β b lam p)
    (T : ∀p,tinyEligible p → TinyTailCore q n μ b βtiny p) :
    ∃ε:ℝ, 0 < ε ∧ ε ≤ 1 ∧ Real.sqrt ε ≤ ρ ∧
      2*(3*Real.sqrt (n:ℝ)+1)*Real.sqrt ε ≤ 1 ∧
      ∃ (M' : ∀p,eligible p → MediumTailConditions q n rows μ β b lam ε (walkHorizon n ε) p)
        (T' : ∀p,tinyEligible p → TinyTailConditions q n μ b βtiny ε (walkHorizon n ε) p),
        (∀p hp,(M' p hp).delta=(M p hp).delta) ∧ (∀p hp,(T' p hp).delta=(T p hp).delta) := by
  classical
  let K := 3*Real.sqrt (n:ℝ)+1
  let dm := fun p => if h:eligible p then (M p h).delta else 0
  let dt := fun p => if h:tinyEligible p then (T p h).delta else 0
  let G := fun p => lam p*Real.exp (lam p*(2*b p))
  let D := fun p => (rows:ℝ)*G p
  let A : Fin (q+1) × Fin 4 → ℝ := fun i =>
    if i.2=0 then 2*lam i.1*K else
    if i.2=1 then dm i.1*(K*D i.1+(K+4*lam i.1*K^2)*D i.1) else
    if i.2=2 then dt i.1*(2*K) else 2*K
  let C : Fin (q+1) × Fin 4 → ℝ := fun i =>
    if i.2=0 then |proxyErrorConstant (dm i.1) (lam i.1) K (D i.1)| else
    if i.2=1 then (dt i.1)^2*(3*K^2) else 0
  have hC i : 0 ≤ C i := by dsimp [C]; split_ifs <;> positivity
  obtain ⟨ε,he,he1,her,hA,herr⟩ := exists_uniform_epsilon ρ hρ n A C hC
  have hraw : 2*(3*Real.sqrt (n:ℝ)+1)*Real.sqrt ε ≤ 1 := by
    simpa only [A,show (3:Fin 4)≠0 by decide,show (3:Fin 4)≠1 by decide,
      show (3:Fin 4)≠2 by decide,if_false,K] using hA (0,3)
  have hm : ∀p (hp:eligible p), ∃c : MediumTailConditions q n rows μ β b lam ε (walkHorizon n ε) p,
      c.delta=(M p hp).delta := by
    intro p hp
    let m := M p hp
    have hd : dm p=m.delta := by simp only [dm,dif_pos hp,m]
    refine ⟨⟨m.delta,m.positive,m.beta_small,m.lambda_nonneg,m.lambda_drift,m.cancel,?_,?_,?_,m.threshold⟩,rfl⟩
    · simpa only [A,if_pos rfl,K] using hA (p,0)
    · simpa only [A,show (1:Fin 4)≠0 by decide,if_false,if_pos rfl,if_true,hd,K,D,G] using hA (p,1)
    · have hh := herr (p,0)
      simp only [C,if_pos rfl,hd] at hh
      have hc : 0 ≤ proxyErrorConstant m.delta (lam p) K (D p) := by
        dsimp [proxyErrorConstant,D,G,K]
        have hl := m.lambda_nonneg
        have hδ := m.positive.le
        positivity
      rw [abs_of_nonneg hc] at hh
      exact hh
  have ht : ∀p (hp:tinyEligible p), ∃c : TinyTailConditions q n μ b βtiny ε (walkHorizon n ε) p,
      c.delta=(T p hp).delta := by
    intro p hp
    let t := T p hp
    have hd : dt p=t.delta := by simp only [dt,dif_pos hp,t]
    refine ⟨⟨t.delta,t.positive,t.beta_nonneg,t.beta_one,t.mu_upper,t.mass,t.cancel,?_,?_⟩,rfl⟩
    · simpa only [A,show (2:Fin 4)≠0 by decide,show (2:Fin 4)≠1 by decide,
        if_false,if_pos rfl,if_true,hd,K] using hA (p,2)
    · simpa only [C,show (1:Fin 4)≠0 by decide,if_false,if_pos rfl,if_true,hd,K] using herr (p,1)

  exact ⟨ε,he,he1,her,hraw,(fun p hp => (hm p hp).choose),(fun p hp => (ht p hp).choose),
    (fun p hp => (hm p hp).choose_spec),(fun p hp => (ht p hp).choose_spec)⟩

end Komlos.KMFresh

-- END KMProof/TailConditionStep.lean

-- BEGIN KMProof/ProxyParameters.lean
noncomputable section
namespace Komlos.KMFresh

lemma proxy_delta_pos {θ α G : ℝ} (hθ : 0 < θ) (hα : 0 < α) (hG : 0 < G) :
    0 < θ/(4*α*G) := div_pos hθ (by positivity)

lemma proxy_delta_cancel {θ α G : ℝ} (hθ : 0 ≤ θ) (hα : 0 < α) (hG : 0 < G) :
    (θ/(4*α*G))^2*(α*G) ≤ (θ/(4*α*G))*(θ/2) := by
  have he : (θ/(4*α*G))^2*(α*G) = (θ/(4*α*G))*(θ/4) := by
    field_simp
  rw [he]
  apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)

lemma exponential_count_threshold {d lam b θ α p : ℝ}
    (_hlam : 0 < lam) (hθ : 0 < θ) (_hα : 0 < α) :
    (d * Real.exp (lam*b)+(1-Real.log p)/(θ/(4*α*(lam * Real.exp (lam*(2*b)))))) /
      Real.exp (lam*(2*b)) =
    d * Real.exp (-(lam*b))+4*α*lam*(1-Real.log p)/θ := by
  have he : Real.exp (lam*(2*b))=Real.exp (lam*b)*Real.exp (lam*b) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he, Real.exp_neg]
  field_simp
end Komlos.KMFresh

-- END KMProof/ProxyParameters.lean

-- BEGIN KMProof/ScaleDepth.lean

namespace Komlos.KMFresh

noncomputable def scaleDepth (ell : ℝ) : ℕ := ⌈5 * Real.log ell / Real.log 2⌉₊
noncomputable def scaleCount (ell : ℝ) : ℕ := scaleDepth ell + 1

lemma scaleDepth_lower (ell : ℝ) :
    5 * Real.log ell ≤ (scaleDepth ell : ℝ) * Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (div_le_iff₀ h2).mp (Nat.le_ceil _)

lemma scaleDepth_upper {ell : ℝ} (hell : 1 ≤ ell) :
    (scaleDepth ell : ℝ) * Real.log 2 < 5 * Real.log ell + Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : 0 ≤ 5 * Real.log ell / Real.log 2 := by
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hell)) h2.le
  have hc := Nat.ceil_lt_add_one h0
  have hm := mul_lt_mul_of_pos_right hc h2
  have hd : 5 * Real.log ell / Real.log 2 * Real.log 2 = 5 * Real.log ell :=
    div_mul_cancel₀ _ h2.ne'
  change (scaleDepth ell : ℝ) * Real.log 2 < _ at hm
  nlinarith

lemma scaleDepth_power_bounds {ell : ℝ} (hell : 1 ≤ ell) :
    ell ^ 5 ≤ (2 : ℝ) ^ scaleDepth ell ∧
      (2 : ℝ) ^ scaleDepth ell ≤ 2 * ell ^ 5 := by
  have he : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  constructor
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simpa only [Real.log_pow, Nat.cast_ofNat] using scaleDepth_lower ell
  · apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    have hu := scaleDepth_upper hell
    norm_num only [Nat.cast_ofNat] at *
    linarith

lemma scaleDepth_four_bounds {ell : ℝ} (hell : 1 ≤ ell) :
    ell ^ 10 ≤ (4 : ℝ) ^ scaleDepth ell ∧
      (4 : ℝ) ^ scaleDepth ell ≤ 4 * ell ^ 10 := by
  obtain ⟨hl, hu⟩ := scaleDepth_power_bounds hell
  have hp : ((2 : ℝ) ^ scaleDepth ell) ^ 2 = (4 : ℝ) ^ scaleDepth ell := by
    calc
      _ = (2 : ℝ) ^ scaleDepth ell * 2 ^ scaleDepth ell := by ring
      _ = ((2 : ℝ) * 2) ^ scaleDepth ell := (mul_pow _ _ _).symm
      _ = _ := by norm_num
  have h0 : 0 ≤ ell ^ 5 := by positivity
  have h1 : 0 ≤ (2 : ℝ) ^ scaleDepth ell := by positivity
  constructor <;> nlinarith [sq_nonneg ((2 : ℝ) ^ scaleDepth ell - ell ^ 5),
    sq_nonneg (2 * ell ^ 5 - (2 : ℝ) ^ scaleDepth ell)]

end Komlos.KMFresh

-- END KMProof/ScaleDepth.lean

-- BEGIN KMProof/ScaleCountBounds.lean

namespace Komlos.KMFresh

lemma scaleCount_pos (ell : ℝ) : 0 < scaleCount ell := by
  unfold scaleCount
  omega

lemma scaleCount_lower (ell : ℝ) :
    5 * Real.log ell / Real.log 2 ≤ (scaleCount ell : ℝ) := by
  have h := Nat.le_ceil (5 * Real.log ell / Real.log 2)
  unfold scaleCount scaleDepth
  push_cast
  linarith

lemma scaleCount_upper {ell : ℝ} (hell : 1 ≤ Real.log ell) :
    (scaleCount ell : ℝ) ≤ (5 / Real.log 2 + 2) * Real.log ell := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : 0 ≤ 5 * Real.log ell / Real.log 2 := by positivity
  have hc := Nat.ceil_lt_add_one h0
  change (scaleDepth ell : ℝ) < _ at hc
  unfold scaleCount
  push_cast
  have he : 5 * Real.log ell / Real.log 2 = (5 / Real.log 2) * Real.log ell := by ring
  rw [he] at hc
  nlinarith

lemma scaleCount_constant_pos : 0 < (5 / Real.log 2 + 2 : ℝ) := by
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

end Komlos.KMFresh

-- END KMProof/ScaleCountBounds.lean

-- BEGIN KMProof/ScaleCountLimits.lean

open Filter
open scoped Topology

namespace Komlos.KMFresh

lemma log_four_div_sqrt_limit :
    Tendsto (fun x : ℝ => (Real.log x) ^ 4 / Real.sqrt x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have he (x : ℝ) : (Real.log x) ^ (4 : ℝ) = (Real.log x) ^ (4 : ℕ) :=
    Real.rpow_natCast (Real.log x) 4
  simpa only [he, Real.sqrt_eq_rpow] using h

lemma scaleCount_four_div_sqrt_limit :
    Tendsto (fun x : ℝ => (scaleCount x : ℝ) ^ 4 / Real.sqrt x) atTop (𝓝 0) := by
  let C : ℝ := 5 / Real.log 2 + 2
  have hu : ∀ᶠ x : ℝ in atTop,
      (scaleCount x : ℝ) ^ 4 / Real.sqrt x ≤ C ^ 4 * ((Real.log x) ^ 4 / Real.sqrt x) := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx
    have hp := scaleCount_upper hx
    have hp0 : (0 : ℝ) ≤ scaleCount x := Nat.cast_nonneg _
    have hh : (scaleCount x : ℝ) ^ 4 ≤ C ^ 4 * (Real.log x) ^ 4 := by
      calc
        _ ≤ (C * Real.log x) ^ 4 := pow_le_pow_left₀ hp0 hp _
        _ = _ := mul_pow _ _ _
    have hd := div_le_div_of_nonneg_right hh (Real.sqrt_nonneg x)
    calc
      _ ≤ C ^ 4 * (Real.log x) ^ 4 / Real.sqrt x := hd
      _ = C ^ 4 * ((Real.log x) ^ 4 / Real.sqrt x) := by ring
  have hl : ∀ᶠ x : ℝ in atTop, 0 ≤ (scaleCount x : ℝ) ^ 4 / Real.sqrt x :=
    Filter.Eventually.of_forall (fun x => by positivity)
  have hlim : Tendsto (fun x : ℝ => C ^ 4 * ((Real.log x) ^ 4 / Real.sqrt x)) atTop (𝓝 0) := by
    simpa using log_four_div_sqrt_limit.const_mul (C ^ 4)
  exact squeeze_zero' hl hu hlim

end Komlos.KMFresh

-- END KMProof/ScaleCountLimits.lean

-- BEGIN KMProof/ScaleParameters.lean

namespace Komlos.KMFresh

noncomputable def scaleTarget (k ell P : ℝ) : ℝ :=
  Real.sqrt k * Real.sqrt (Real.sqrt ell) * P ^ 2

noncomputable def scaleBeta (k ell P : ℝ) : ℝ := scaleTarget k ell P / (64 * k)
noncomputable def scaleTheta (k ell P : ℝ) : ℝ := scaleTarget k ell P / (1024 * k)
noncomputable def scaleMu (k ell P : ℝ) : ℝ :=
  max (scaleTarget k ell P) ((scaleTarget k ell P) ^ 2 / ell)

lemma scaleTarget_nonneg (k ell P : ℝ) : 0 ≤ scaleTarget k ell P := by
  unfold scaleTarget
  positivity

lemma scaleTarget_pos {k ell P : ℝ} (hk : 0 < k) (hell : 0 < ell) (hP : 0 < P) :
    0 < scaleTarget k ell P := by
  unfold scaleTarget
  positivity

lemma scaleTarget_sq {k : ℝ} (hk : 0 ≤ k) (ell P : ℝ) :
    (scaleTarget k ell P) ^ 2 = k * Real.sqrt ell * P ^ 4 := by
  simp only [scaleTarget, mul_pow, Real.sq_sqrt hk,
    Real.sq_sqrt (Real.sqrt_nonneg ell)]
  ring

lemma scaleTheta_eq (k ell P : ℝ) : scaleTheta k ell P = scaleBeta k ell P / 16 := by
  unfold scaleTheta scaleBeta
  ring

lemma scaleBeta_initial {k : ℝ} (hk : k ≠ 0) (ell P : ℝ) :
    scaleBeta k ell P * (64 * k) = scaleTarget k ell P := by
  unfold scaleBeta
  field_simp

lemma scaleBeta_small {k ell P : ℝ} (hk : 0 < k)
    (hb : scaleTarget k ell P ≤ k) : scaleBeta k ell P ≤ 1 / 64 := by
  unfold scaleBeta
  apply (div_le_iff₀ (by positivity : 0 < 64 * k)).mpr
  nlinarith

lemma scaleMu_le {k ell P : ℝ} (hell : 0 < ell)
    (hb : scaleTarget k ell P ≤ k) (hs : (scaleTarget k ell P) ^ 2 ≤ k * ell) :
    scaleMu k ell P ≤ k := by
  exact max_le hb ((div_le_iff₀ hell).mpr hs)

end Komlos.KMFresh

-- END KMProof/ScaleParameters.lean

-- BEGIN KMProof/ScaleBudgetAlgebra.lean

namespace Komlos.KMFresh

lemma scaleTarget_square_le {k ell P : ℝ} (hk : 0 ≤ k) (hell : 0 ≤ ell)
    (hP : P ^ 4 ≤ Real.sqrt ell) : (scaleTarget k ell P) ^ 2 ≤ k * ell := by
  rw [scaleTarget_sq hk]
  calc
    k * Real.sqrt ell * P ^ 4 ≤ k * Real.sqrt ell * Real.sqrt ell :=
      mul_le_mul_of_nonneg_left hP (mul_nonneg hk (Real.sqrt_nonneg ell))
    _ = k * ell := by rw [mul_assoc, Real.mul_self_sqrt hell]

lemma scaleMu_uniform_le {k ell P : ℝ} (hk : 0 ≤ k) (hell : 0 < ell)
    (hP : P ^ 4 ≤ Real.sqrt ell) (hb : scaleTarget k ell P ≤ k) :
    scaleMu k ell P ≤ k :=
  scaleMu_le hell hb (scaleTarget_square_le hk hell.le hP)

lemma scaleMu_pos {k ell P : ℝ} (hk : 0 < k) (hell : 0 < ell) (hP : 0 < P) :
    0 < scaleMu k ell P :=
  (scaleTarget_pos hk hell hP).trans_le (le_max_left _ _)

lemma scaleMu_target_le (k ell P : ℝ) : scaleTarget k ell P ≤ scaleMu k ell P :=
  le_max_left _ _

lemma scaleMu_square_le {k ell P : ℝ} (hell : 0 < ell) :
    (scaleTarget k ell P) ^ 2 ≤ scaleMu k ell P * ell := by
  exact (div_le_iff₀ hell).mp (le_max_right _ _)

lemma medium_regularizer_initial {I : Type*} (A : Finset I) (a x : I → ℝ)
    (k b β : ℝ) (hβ : 0 ≤ β) (hβk : β * (64 * k) ≤ b)
    (he : ∑ i ∈ A, a i ^ 2 ≤ 64 * k) :
    β * (∑ i ∈ A, a i ^ 2 * (1 - x i ^ 2)) ≤ b := by
  have hs : (∑ i ∈ A, a i ^ 2 * (1 - x i ^ 2)) ≤ ∑ i ∈ A, a i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [mul_nonneg (sq_nonneg (a i)) (sq_nonneg (x i))]
  exact (mul_le_mul_of_nonneg_left (hs.trans he) hβ).trans hβk

end Komlos.KMFresh

-- END KMProof/ScaleBudgetAlgebra.lean

-- BEGIN KMProof/EventualParameters.lean

open Filter
open scoped Topology

namespace Komlos.KMFresh

lemma eventually_scaleCount_four_le :
    ∀ᶠ x : ℝ in atTop, (scaleCount x : ℝ) ^ 4 ≤ Real.sqrt x := by
  have h := scaleCount_four_div_sqrt_limit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hxp
  simpa only [one_mul] using ((div_lt_iff₀ (Real.sqrt_pos.mpr hxp)).mp hx).le

lemma eventually_log_drift_guard :
    ∀ᶠ x : ℝ in atTop, 20480 * Real.log x ≤ Real.sqrt x := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h1 : Tendsto (fun x : ℝ => 20480 * (Real.log x / Real.sqrt x)) atTop (𝓝 0) := by
    simpa using h0.const_mul (20480 : ℝ)
  have h := h1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hxp
  have he : 20480 * (Real.log x / Real.sqrt x) = (20480 * Real.log x) / Real.sqrt x := by ring
  rw [he] at hx
  simpa only [one_mul] using ((div_lt_iff₀ (Real.sqrt_pos.mpr hxp)).mp hx).le

lemma medium_lambda_guard {k ell P : ℝ} (hk : 0 < k) (hell : 0 < ell) (hP : 1 ≤ P)
    (hlog : 20480 * Real.log ell ≤ Real.sqrt ell) :
    10 * Real.log ell / scaleTarget k ell P ≤ scaleTheta k ell P / 2 := by
  have hb := scaleTarget_pos hk hell (by linarith : 0 < P)
  have hs := scaleTarget_sq hk.le ell P
  have hP4 : 1 ≤ P ^ 4 := one_le_pow₀ hP
  have hm := mul_le_mul_of_nonneg_left hP4 (mul_nonneg hk.le (Real.sqrt_nonneg ell))
  have hl := mul_le_mul_of_nonneg_left hlog hk.le
  have ht : scaleTheta k ell P / 2 = scaleTarget k ell P / (2048 * k) := by
    unfold scaleTheta
    ring
  rw [ht]
  apply (div_le_div_iff₀ hb (by positivity : 0 < 2048 * k)).mpr
  nlinarith

end Komlos.KMFresh

-- END KMProof/EventualParameters.lean

-- BEGIN KMProof/NativeLogShape.lean

namespace Komlos.KMFresh

noncomputable def nativeEll (n : ℕ) : ℝ := Real.log ((n : ℝ) + 2)
noncomputable def nativeLogLog (n : ℕ) : ℝ := Real.log (Real.log ((n : ℝ) + 8))
noncomputable def nativeShape (n : ℕ) : ℝ :=
  nativeEll n ^ ((1 : ℝ) / 4) * nativeLogLog n ^ 3

lemma nativeEll_pos (n : ℕ) : 0 < nativeEll n := by
  apply Real.log_pos
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma nativeLogLog_pos (n : ℕ) : 0 < nativeLogLog n := by
  apply Real.log_pos
  apply (Real.lt_log_iff_exp_lt (by positivity : 0 < (n : ℝ) + 8)).mpr
  have h := Real.exp_one_lt_three
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma nativeShape_pos (n : ℕ) : 0 < nativeShape n := by
  unfold nativeShape
  exact mul_pos (Real.rpow_pos_of_pos (nativeEll_pos n) _) (pow_pos (nativeLogLog_pos n) _)

lemma native_log_ell_le_loglog (n : ℕ) : Real.log (nativeEll n) ≤ nativeLogLog n := by
  apply Real.log_le_log (nativeEll_pos n)
  apply Real.log_le_log (by positivity : 0 < (n : ℝ) + 2)
  linarith

end Komlos.KMFresh

-- END KMProof/NativeLogShape.lean

-- BEGIN KMProof/TargetSum.lean

namespace Komlos.KMFresh

lemma sqrt_scale_power (p : ℕ) : Real.sqrt ((4 : ℝ) ^ p) = (2 : ℝ) ^ p := by
  have he : ((2 : ℝ) ^ p) ^ 2 = (4 : ℝ) ^ p := by
    calc
      _ = (2 : ℝ) ^ p * 2 ^ p := by ring
      _ = ((2 : ℝ) * 2) ^ p := (mul_pow _ _ _).symm
      _ = _ := by norm_num
  rw [← he, Real.sqrt_sq (by positivity)]

lemma scaled_target (p : ℕ) (ell P : ℝ) :
    scaleCut p * scaleTarget ((4 : ℝ) ^ p) ell P = Real.sqrt (Real.sqrt ell) * P ^ 2 := by
  unfold scaleTarget
  rw [sqrt_scale_power]
  calc
    _ = ((2 : ℝ) ^ p * scaleCut p) * (Real.sqrt (Real.sqrt ell) * P ^ 2) := by ring
    _ = _ := by rw [scale_inverse, one_mul]

lemma sum_scaled_targets (P : ℕ) (ell : ℝ) :
    (∑ p : Fin P, scaleCut p.val * scaleTarget ((4 : ℝ) ^ p.val) ell P) =
      Real.sqrt (Real.sqrt ell) * (P : ℝ) ^ 3 := by
  simp only [scaled_target, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma nested_sqrt_quarter {ell : ℝ} (hell : 0 ≤ ell) :
    Real.sqrt (Real.sqrt ell) = ell ^ ((1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hell]
  norm_num

end Komlos.KMFresh

-- END KMProof/TargetSum.lean

-- BEGIN KMProof/NativeTargetComparison.lean

open Filter

namespace Komlos.KMFresh

lemma nativeEll_atTop : Tendsto nativeEll atTop atTop := by
  apply Real.tendsto_log_atTop.comp
  exact tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop

lemma native_log_ell_atTop : Tendsto (fun n => Real.log (nativeEll n)) atTop atTop :=
  Real.tendsto_log_atTop.comp nativeEll_atTop

lemma native_scale_sum_bound (n : ℕ) (hn : 1 ≤ Real.log (nativeEll n)) :
    (∑ p : Fin (scaleCount (nativeEll n)), scaleCut p.val *
      scaleTarget ((4 : ℝ) ^ p.val) (nativeEll n) (scaleCount (nativeEll n))) ≤
      (5 / Real.log 2 + 2) ^ 3 * nativeShape n := by
  let C : ℝ := 5 / Real.log 2 + 2
  have hc : 0 < C := scaleCount_constant_pos
  have hp := scaleCount_upper hn
  have hl := native_log_ell_le_loglog n
  have hp' : (scaleCount (nativeEll n) : ℝ) ≤ C * nativeLogLog n :=
    hp.trans (mul_le_mul_of_nonneg_left hl hc.le)
  have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ scaleCount (nativeEll n) by positivity) hp' 3
  rw [sum_scaled_targets, nested_sqrt_quarter (nativeEll_pos n).le]
  have hm := mul_le_mul_of_nonneg_left hpow
    (Real.rpow_pos_of_pos (nativeEll_pos n) ((1 : ℝ) / 4)).le
  unfold nativeShape
  calc
    _ ≤ nativeEll n ^ ((1 : ℝ) / 4) * (C * nativeLogLog n) ^ 3 := hm
    _ = _ := by dsimp [C]; ring

lemma eventually_native_scale_sum_bound :
    ∀ᶠ n : ℕ in atTop,
    (∑ p : Fin (scaleCount (nativeEll n)), scaleCut p.val *
      scaleTarget ((4 : ℝ) ^ p.val) (nativeEll n) (scaleCount (nativeEll n))) ≤
      (5 / Real.log 2 + 2) ^ 3 * nativeShape n := by
  filter_upwards [native_log_ell_atTop.eventually_ge_atTop 1] with n hn
  exact native_scale_sum_bound n hn

end Komlos.KMFresh

-- END KMProof/NativeTargetComparison.lean

-- BEGIN KMProof/NativeConfidence.lean
open Filter
namespace Komlos.KMFresh

lemma scale_count_polynomial_guard (n : ℕ)
    (hfour : (scaleCount (nativeEll n):ℝ)^4 ≤ Real.sqrt (nativeEll n)) :
    scaleCount (nativeEll n) ≤ n+2 := by
  have hp : (scaleCount (nativeEll n):ℝ) ≤ (scaleCount (nativeEll n):ℝ)^4 := by
    exact_mod_cast Nat.le_self_pow (by decide : (4:ℕ) ≠ 0) (scaleCount (nativeEll n))
  have hs := Real.sq_sqrt (nativeEll_pos n).le
  have hs0 := Real.sqrt_nonneg (nativeEll n)
  have hx : (0:ℝ) < (n:ℝ)+2 := by positivity
  have hl := Real.log_le_sub_one_of_pos hx
  change nativeEll n ≤ (n:ℝ)+2-1 at hl
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hb : Real.sqrt (nativeEll n) ≤ (n:ℝ)+2 := by nlinarith
  exact_mod_cast (hp.trans (hfour.trans hb))

lemma eventually_native_confidence_guards :
    ∀ᶠ n : ℕ in atTop, scaleCount (nativeEll n) ≤ n+2 ∧
      1-Real.log (confidence n) ≤ 11*nativeEll n := by
  filter_upwards [nativeEll_atTop.eventually eventually_scaleCount_four_le,
    nativeEll_atTop.eventually_ge_atTop 1] with n hfour hell
  exact ⟨scale_count_polynomial_guard n hfour, confidence_log_bound n hell⟩
end Komlos.KMFresh

-- END KMProof/NativeConfidence.lean

-- BEGIN KMProof/ScaleRatioLimits.lean

open Filter
open scoped Topology

namespace Komlos.KMFresh

lemma scaleCount_additive_upper {x : ℝ} (hx : 0 ≤ Real.log x) :
    (scaleCount x : ℝ) ≤ (5 / Real.log 2) * Real.log x + 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 5 * Real.log x / Real.log 2 by positivity)
  change (scaleDepth x : ℝ) < _ at hc
  unfold scaleCount
  push_cast
  have he : 5 * Real.log x / Real.log 2 = (5 / Real.log 2) * Real.log x := by ring
  rw [he] at hc
  linarith

lemma scaleCount_ratio_limit :
    Tendsto (fun x : ℝ => (scaleCount x : ℝ) / Real.log x) atTop (𝓝 (5 / Real.log 2)) := by
  have hdiv : Tendsto (fun x : ℝ => 2 / Real.log x) atTop (𝓝 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2)).div_atTop Real.tendsto_log_atTop
  have hupper : Tendsto (fun x : ℝ => 5 / Real.log 2 + 2 / Real.log x) atTop (𝓝 (5 / Real.log 2)) := by
    simpa using tendsto_const_nhds.add hdiv
  have hl : ∀ᶠ x : ℝ in atTop, 5 / Real.log 2 ≤ (scaleCount x : ℝ) / Real.log x := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx
    apply (le_div_iff₀ (by linarith : 0 < Real.log x)).mpr
    have hb := scaleCount_lower x
    have he : 5 / Real.log 2 * Real.log x = 5 * Real.log x / Real.log 2 := by ring
    rw [he]
    exact hb
  have hu : ∀ᶠ x : ℝ in atTop, (scaleCount x : ℝ) / Real.log x ≤ 5 / Real.log 2 + 2 / Real.log x := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx
    have hp : 0 < Real.log x := by linarith
    apply (div_le_iff₀ hp).mpr
    have hb := scaleCount_additive_upper (show 0 ≤ Real.log x by linarith)
    have he : (5 / Real.log 2 + 2 / Real.log x) * Real.log x =
        (5 / Real.log 2) * Real.log x + 2 := by
      rw [add_mul, div_mul_cancel₀ _ hp.ne']
    rw [he]
    exact hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper hl hu

end Komlos.KMFresh

-- END KMProof/ScaleRatioLimits.lean

-- BEGIN KMProof/ScaleMarginLimits.lean

open Filter
open scoped Topology

namespace Komlos.KMFresh

lemma log_div_scaleCount_limit :
    Tendsto (fun x : ℝ => Real.log x / (scaleCount x : ℝ)) atTop (𝓝 ((5 / Real.log 2)⁻¹)) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (5 / Real.log 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  simpa only [inv_div] using scaleCount_ratio_limit.inv₀ hc

lemma inverse_log_limit : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop

lemma log_div_scaleCount_six_limit :
    Tendsto (fun x : ℝ => Real.log x / (scaleCount x : ℝ) ^ 6) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => (Real.log x / (scaleCount x : ℝ)) ^ 6 *
      ((Real.log x)⁻¹) ^ 5) atTop (𝓝 0) := by
    simpa using (log_div_scaleCount_limit.pow 6).mul (inverse_log_limit.pow 5)
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx
  have hl : Real.log x ≠ 0 := ne_of_gt (by linarith)
  have hp : (scaleCount x : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (scaleCount_pos x))
  field_simp

end Komlos.KMFresh

-- END KMProof/ScaleMarginLimits.lean

-- BEGIN KMProof/HeavyMarginConditions.lean

open Filter
open scoped Topology

namespace Komlos.KMFresh

lemma scaleMu_sqrt_mass {k ell P : ℝ} (hk : 0 ≤ k) (hell : 0 < ell) :
    k * P ^ 4 ≤ scaleMu k ell P * Real.sqrt ell := by
  have h := scaleMu_square_le (k := k) (P := P) hell
  rw [scaleTarget_sq hk] at h
  apply (mul_le_mul_iff_of_pos_right (Real.sqrt_pos.mpr hell)).mp
  calc
    k * P ^ 4 * Real.sqrt ell = k * Real.sqrt ell * P ^ 4 := by ring
    _ ≤ scaleMu k ell P * ell := h
    _ = scaleMu k ell P * Real.sqrt ell * Real.sqrt ell := by
      rw [mul_assoc, Real.mul_self_sqrt hell.le]

lemma scaleMu_quartic_mass {k ell P : ℝ} (hk : 0 ≤ k) (hell : 0 ≤ ell) :
    k ^ 2 * ell * P ^ 8 ≤ (scaleMu k ell P) ^ 2 * (scaleTarget k ell P) ^ 2 := by
  have hb := scaleTarget_nonneg k ell P
  have hm := scaleMu_target_le k ell P
  have hs : (scaleTarget k ell P) ^ 2 ≤ (scaleMu k ell P) ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hs (sq_nonneg (scaleTarget k ell P))
  have he : ((scaleTarget k ell P) ^ 2) ^ 2 = k ^ 2 * ell * P ^ 8 := by
    rw [scaleTarget_sq hk]
    simp only [mul_pow, Real.sq_sqrt hell]
    ring
  nlinarith

lemma first_heavy_margin {ell : ℝ} (hell : 1024 ≤ ell) :
    1024 * Real.sqrt ell ≤ ell ^ 10 := by
  have h1 : 1 ≤ ell := by linarith
  have h0 : 0 ≤ ell := by linarith
  have hs : Real.sqrt ell ≤ ell := by
    have he := Real.sq_sqrt h0
    have hp := Real.sqrt_nonneg ell
    nlinarith
  have hp := pow_le_pow_right₀ h1 (by decide : (2 : ℕ) ≤ 10)
  have hm := mul_le_mul_of_nonneg_right hell h0
  nlinarith

lemma eventually_second_heavy_margin (C : ℝ) :
    ∀ᶠ ell : ℝ in atTop, 128 * C * Real.log ell ≤ (scaleCount ell : ℝ) ^ 6 := by
  have hlim : Tendsto (fun ell : ℝ => (128 * C) * (Real.log ell / (scaleCount ell : ℝ) ^ 6))
      atTop (𝓝 0) := by
    simpa using log_div_scaleCount_six_limit.const_mul (128 * C)
  have h := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h] with ell he
  have hp : (0 : ℝ) < scaleCount ell := by exact_mod_cast scaleCount_pos ell
  have hid : (128 * C) * (Real.log ell / (scaleCount ell : ℝ) ^ 6) =
      (128 * C * Real.log ell) / (scaleCount ell : ℝ) ^ 6 := by ring
  rw [hid] at he
  simpa only [one_mul] using ((div_lt_iff₀ (by positivity)).mp he).le

end Komlos.KMFresh

-- END KMProof/HeavyMarginConditions.lean

-- BEGIN KMProof/HeavyDangerArithmetic.lean

namespace Komlos.KMFresh

lemma heavy_danger_arithmetic (d k μ b ell P C : ℝ)
    (hk : 0 < k) (hμ : 0 < μ) (hb : 0 < b) (hell : 0 < ell) (hP : 1 ≤ P)
    (hd : d ≤ 8 * k)
    (hμmass : k * P ^ 4 ≤ μ * Real.sqrt ell)
    (hscale : k ^ 2 * ell * P ^ 8 ≤ μ ^ 2 * b ^ 2)
    (hfirst : 1024 * Real.sqrt ell ≤ ell ^ 10)
    (hsecond : 128 * C * Real.log ell ≤ P ^ 6) :
    d / ell ^ 10 + C * P * k ^ 2 * ell * Real.log ell / (μ * b ^ 2) ≤ μ / (64 * P) := by
  have hPpos : 0 < P := by linarith
  have hp4 : P ≤ P ^ 4 := by nlinarith [sq_nonneg P, sq_nonneg (P - 1), sq_nonneg (P ^ 2 - 1)]
  have hsmall : d / ell ^ 10 ≤ μ / (128 * P) := by
    apply (div_le_div_iff₀ (by positivity : 0 < ell ^ 10) (by positivity : 0 < 128 * P)).mpr
    have h1 := mul_le_mul_of_nonneg_left hp4 hk.le
    have h2 := mul_le_mul_of_nonneg_left hfirst hμ.le
    have h3 := mul_le_mul_of_nonneg_right hd (show 0 ≤ 128 * P by positivity)
    nlinarith
  have hlarge : C * P * k ^ 2 * ell * Real.log ell / (μ * b ^ 2) ≤ μ / (128 * P) := by
    apply (div_le_div_iff₀ (by positivity : 0 < μ * b ^ 2) (by positivity : 0 < 128 * P)).mpr
    have hm := mul_le_mul_of_nonneg_left hsecond
      (show 0 ≤ k ^ 2 * ell * P ^ 2 by positivity)
    nlinarith
  have he : μ / (128 * P) + μ / (128 * P) = μ / (64 * P) := by ring
  rw [← he]
  exact add_le_add hsmall hlarge

end Komlos.KMFresh

-- END KMProof/HeavyDangerArithmetic.lean

-- BEGIN KMProof/UniformHeavyBound.lean

open Filter

namespace Komlos.KMFresh

lemma eventually_uniform_heavy_bound (C : ℝ) :
    ∀ᶠ ell : ℝ in atTop, ∀ k d : ℝ, 0 < k → d ≤ 8 * k →
      d / ell ^ 10 +
        C * (scaleCount ell : ℝ) * k ^ 2 * ell * Real.log ell /
          (scaleMu k ell (scaleCount ell) * (scaleTarget k ell (scaleCount ell)) ^ 2) ≤
        scaleMu k ell (scaleCount ell) / (64 * (scaleCount ell : ℝ)) := by
  filter_upwards [eventually_second_heavy_margin C, eventually_ge_atTop (1024 : ℝ)] with ell hs hell
  intro k d hk hd
  have he : 0 < ell := by linarith
  have hP : (1 : ℝ) ≤ scaleCount ell := by exact_mod_cast scaleCount_pos ell
  exact heavy_danger_arithmetic d k (scaleMu k ell (scaleCount ell))
    (scaleTarget k ell (scaleCount ell)) ell (scaleCount ell) C hk
    (scaleMu_pos hk he (by linarith)) (scaleTarget_pos hk he (by linarith)) he hP hd
    (scaleMu_sqrt_mass hk.le he) (scaleMu_quartic_mass hk.le he.le)
    (first_heavy_margin hell) hs

end Komlos.KMFresh

-- END KMProof/UniformHeavyBound.lean

-- BEGIN KMProof/ConfidenceEnvelope.lean
noncomputable section
open Filter
namespace Komlos.KMFresh

lemma confidence_envelope (n : ℕ) (d k μ b P : ℝ)
    (hk : 0 < k) (hμ : 0 < μ) (hb : 0 < b) (hP : 0 ≤ P)
    (hell : 1 ≤ nativeEll n) :
    d*Real.exp (-((10*Real.log (nativeEll n)/b)*b))+
      4*(64*P*k/μ)*(10*Real.log (nativeEll n)/b)*(1-Real.log (confidence n))/(b/(1024*k)) ≤
    d/(nativeEll n)^10+
      28835840*P*k^2*(nativeEll n)*Real.log (nativeEll n)/(μ*b^2) := by
  have he : 0 < nativeEll n := nativeEll_pos n
  have hl : 0 ≤ Real.log (nativeEll n) := Real.log_nonneg hell
  have hc := confidence_log_bound n hell
  change 1-Real.log (confidence n) ≤ 11*nativeEll n at hc
  have hx : (10*Real.log (nativeEll n)/b)*b=10*Real.log (nativeEll n) := by field_simp
  have hexp : Real.exp (10*Real.log (nativeEll n))=(nativeEll n)^10 := by
    simpa only [Nat.cast_ofNat,Real.exp_log he] using Real.exp_nat_mul (Real.log (nativeEll n)) 10
  rw [hx,Real.exp_neg,hexp]
  have hm := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ 4*(64*P*k/μ)*(10*Real.log (nativeEll n)/b)/(b/(1024*k)) by positivity)
  have halg : 4*(64*P*k/μ)*(10*Real.log (nativeEll n)/b)/(b/(1024*k))*(11*nativeEll n)=
      28835840*P*k^2*(nativeEll n)*Real.log (nativeEll n)/(μ*b^2) := by
    field_simp
    ring
  rw [halg] at hm
  calc
    _ = d/(nativeEll n)^10+
      (4*(64*P*k/μ)*(10*Real.log (nativeEll n)/b)/(b/(1024*k)))*(1-Real.log (confidence n)) := by ring
    _ ≤ _ := add_le_add le_rfl hm

lemma eventually_confidence_danger_bound :
    ∀ᶠ n : ℕ in atTop, ∀ k d : ℝ, 0 < k → d ≤ 8*k →
      let ell := nativeEll n
      let P : ℝ := scaleCount ell
      let b := scaleTarget k ell P
      let μ := scaleMu k ell P
      d*Real.exp (-((10*Real.log ell/b)*b))+
        4*(64*P*k/μ)*(10*Real.log ell/b)*(1-Real.log (confidence n))/(b/(1024*k)) ≤ μ/(64*P) := by
  filter_upwards [nativeEll_atTop.eventually (eventually_uniform_heavy_bound 28835840),
    nativeEll_atTop.eventually_ge_atTop 1] with n hu hell
  intro k d hk hd
  dsimp only
  have hP : 0 < (scaleCount (nativeEll n):ℝ) := by exact_mod_cast scaleCount_pos (nativeEll n)
  exact (confidence_envelope n d k _ _ _ hk
    (scaleMu_pos hk (nativeEll_pos n) hP) (scaleTarget_pos hk (nativeEll_pos n) hP)
    hP.le hell).trans (hu k d hk hd)
end Komlos.KMFresh

-- END KMProof/ConfidenceEnvelope.lean

-- BEGIN KMProof/MediumThreshold.lean
noncomputable section
open Filter
namespace Komlos.KMFresh

lemma eventually_medium_threshold :
    ∀ᶠ n : ℕ in atTop, ∀ k d : ℝ, 0 < k → d ≤ 8*k →
      let ell := nativeEll n
      let P : ℝ := scaleCount ell
      let b := scaleTarget k ell P
      let μ := scaleMu k ell P
      let lam := 10*Real.log ell/b
      let θ := b/(1024*k)
      let α := 64*P*k/μ
      let δ := θ/(4*α*(lam*Real.exp (lam*(2*b))))
      (d*Real.exp (lam*b)+(1-Real.log (confidence n))/δ)/Real.exp (lam*(2*b)) ≤ μ/(64*P) := by
  filter_upwards [eventually_confidence_danger_bound,nativeEll_atTop.eventually_ge_atTop 2] with n hu hn
  intro k d hk hd
  let ell := nativeEll n
  let P : ℝ := scaleCount ell
  let b := scaleTarget k ell P
  let μ := scaleMu k ell P
  have hell : 0 < ell := nativeEll_pos n
  have hP : 0 < P := by dsimp [P]; exact_mod_cast scaleCount_pos ell
  have hb : 0 < b := scaleTarget_pos hk hell hP
  have hμ : 0 < μ := scaleMu_pos hk hell hP
  have hl : 0 < Real.log ell := Real.log_pos (by dsimp [ell]; linarith)
  have he := exponential_count_threshold (d := d) (lam := 10*Real.log ell/b) (b := b)
    (θ := b/(1024*k)) (α := 64*P*k/μ) (p := confidence n) (by positivity) (by positivity) (by positivity)
  dsimp only
  change (d*Real.exp ((10*Real.log ell/b)*b)+(1-Real.log (confidence n))/
    ((b/(1024*k))/(4*(64*P*k/μ)*((10*Real.log ell/b)*Real.exp ((10*Real.log ell/b)*(2*b))))))/
      Real.exp ((10*Real.log ell/b)*(2*b)) ≤ μ/(64*P)
  rw [he]
  exact hu k d hk hd
end Komlos.KMFresh

-- END KMProof/MediumThreshold.lean

-- BEGIN KMProof/TinyConfidence.lean
noncomputable section
namespace Komlos.KMFresh

lemma tiny_delta_cancel {β : ℝ} (_hβ : 0 ≤ β) :
    (β/288)^2 ≤ (β/288)*((β/72)/2) := by nlinarith [sq_nonneg β]

lemma tiny_confidence_threshold (n : ℕ) {b : ℝ} (hb : 0 < b)
    (hell : 1 ≤ nativeEll n) :
    (1-Real.log (confidence n))/((nativeEll n/b)/288) ≤ 3168*b := by
  have he : 0 < nativeEll n := nativeEll_pos n
  have hd : 0 < (nativeEll n/b)/288 := by positivity
  apply (div_le_iff₀ hd).mpr
  have hc := confidence_log_bound n hell
  have ha : 3168*b*((nativeEll n/b)/288)=11*nativeEll n := by
    field_simp
    ring
  rw [ha]
  exact hc
end Komlos.KMFresh

-- END KMProof/TinyConfidence.lean

-- BEGIN KMProof/ClippedCoefficient.lean

namespace Komlos.KMFresh

noncomputable def clippedBeta (b k : ℝ) : ℝ := min (b / (64 * k)) (1 / 64)

lemma clippedBeta_nonneg {b k : ℝ} (hb : 0 ≤ b) (hk : 0 < k) : 0 ≤ clippedBeta b k :=
  le_min (div_nonneg hb (by positivity)) (by norm_num)

lemma clippedBeta_le (b k : ℝ) : clippedBeta b k ≤ 1 / 64 := min_le_right _ _

lemma clippedBeta_active {b k : ℝ} (hk : 0 < k) (hb : b ≤ k) : clippedBeta b k = b / (64 * k) := by
  apply min_eq_left
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 64 * k)).mpr
  nlinarith

lemma clippedBeta_budget {b k : ℝ} (hk : 0 < k) : clippedBeta b k * (64 * k) ≤ b := by
  have he := mul_le_mul_of_nonneg_right (min_le_left (b / (64 * k)) (1 / 64))
    (show 0 ≤ 64 * k by positivity)
  rw [div_mul_cancel₀ _ (by positivity : (64 * k) ≠ 0)] at he
  exact he

end Komlos.KMFresh

-- END KMProof/ClippedCoefficient.lean

-- BEGIN KMProof/EffectiveThreshold.lean

namespace Komlos.KMFresh

noncomputable def effectiveMu (k μ b : ℝ) : ℝ := if b ≤ k then μ else 64 * k

lemma effectiveMu_pos {k μ b : ℝ} (hk : 0 < k) (hμ : 0 < μ) : 0 < effectiveMu k μ b := by
  unfold effectiveMu
  split_ifs
  · exact hμ
  · positivity

lemma effectiveMu_active {k μ b : ℝ} (hb : b ≤ k) : effectiveMu k μ b = μ := if_pos hb

lemma effectiveMu_inactive {k μ b : ℝ} (hb : k < b) : effectiveMu k μ b = 64 * k :=
  if_neg (not_le_of_gt hb)

lemma no_inactive_medium {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ b : R → ℝ) (x : Fin n → ℝ) (r : R) (hb : k r < b r) :
    ¬rowMedium A ρ k (fun r => effectiveMu (k r) (μ r) (b r)) x r := by
  intro hm
  have he := effectiveMu_inactive (μ := μ r) hb
  change effectiveMu (k r) (μ r) (b r) < rowEnergy A ρ x r ∧ _ at hm
  rw [he] at hm
  exact not_lt_of_ge hm.2 hm.1

lemma no_inactive_new_hit {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (k μ β b : R → ℝ) (x : Fin n → ℝ) (r : R) (hb : k r < b r) :
    ¬regularizedHit A ρ k (fun r => effectiveMu (k r) (μ r) (b r)) β b x r :=
  fun hh => no_inactive_medium A ρ k μ b x r hb hh.1

lemma inactive_hit_step {R Ω : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (ρ : ℝ) (k μ β b : R → ℝ)
    (running : AdaptiveState R n → Prop)
    (direction : AdaptiveState R n → Ω → Fin n → ℝ) (t : ℝ)
    (s : AdaptiveState R n) (ω : Ω) (r : R) (hb : k r < b r) (hr : r ∉ s.hit) :
    r ∉ (adaptiveStep running direction
      (regularizedHit A ρ k (fun r => effectiveMu (k r) (μ r) (b r)) β b) t s ω).hit := by
  by_cases hrun : running s
  · intro hh
    have he := (adaptiveStep_hit_iff running direction
      (regularizedHit A ρ k (fun r => effectiveMu (k r) (μ r) (b r)) β b) t s ω hrun r).mp hh
    exact no_inactive_new_hit A ρ k μ β b _ r hb (he.resolve_left hr)
  · rw [adaptiveStep_stopped running direction
      (regularizedHit A ρ k (fun r => effectiveMu (k r) (μ r) (b r)) β b) t s ω hrun]
    exact hr

end Komlos.KMFresh

-- END KMProof/EffectiveThreshold.lean

-- BEGIN KMProof/LightParameters.lean

namespace Komlos.KMFresh

lemma light_target_between {k ell P : ℝ} (hell : 1 ≤ ell) (hP : 1 ≤ P)
    (hk : ell ^ 10 ≤ k) (hsmall : P ^ 4 ≤ Real.sqrt ell) :
    ell ≤ scaleTarget k ell P ∧ scaleTarget k ell P ≤ k := by
  have hepos : 0 < ell := by linarith
  have he10 : ell ≤ ell ^ 10 := by
    simpa only [pow_one] using pow_le_pow_right₀ hell (by decide : (1 : ℕ) ≤ 10)
  have hek : ell ≤ k := he10.trans hk
  have hkpos : 0 < k := hepos.trans_le hek
  have hp4 : 1 ≤ P ^ 4 := one_le_pow₀ hP
  have hsqrt : 1 ≤ Real.sqrt ell := by
    have hs := Real.sq_sqrt hepos.le
    have h0 := Real.sqrt_nonneg ell
    nlinarith
  have hb := scaleTarget_nonneg k ell P
  have hsq := scaleTarget_sq hkpos.le ell P
  have hlow : k ≤ (scaleTarget k ell P) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hsqrt hkpos.le
    have h2 := mul_le_mul_of_nonneg_left hp4 (show 0 ≤ k * Real.sqrt ell by positivity)
    nlinarith
  have he2 : ell ^ 2 ≤ ell ^ 10 := pow_le_pow_right₀ hell (by decide : (2 : ℕ) ≤ 10)
  have hhigh := scaleTarget_square_le hkpos.le hepos.le hsmall
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hek hkpos.le]

lemma light_mu_quadratic {k ell P : ℝ} (hell : 0 < ell)
    (hb : ell ≤ scaleTarget k ell P) :
    scaleMu k ell P = (scaleTarget k ell P) ^ 2 / ell := by
  apply max_eq_right
  apply (le_div_iff₀ hell).mpr
  have hp := scaleTarget_nonneg k ell P
  nlinarith

end Komlos.KMFresh

-- END KMProof/LightParameters.lean

-- BEGIN KMProof/ConcreteParameters.lean

noncomputable section
namespace Komlos.KMFresh

def concreteDepth (n : ℕ) : ℕ := scaleDepth (nativeEll n)
def concreteK {n : ℕ} (p : Fin (concreteDepth n+1)) : ℝ := (4:ℝ)^p.val
def concreteB (n : ℕ) (p : Fin (concreteDepth n+1)) : ℝ :=
  scaleTarget (concreteK p) (nativeEll n) (scaleCount (nativeEll n))
def concreteMu (n : ℕ) (p : Fin (concreteDepth n+1)) : ℝ :=
  effectiveMu (concreteK p) (scaleMu (concreteK p) (nativeEll n) (scaleCount (nativeEll n))) (concreteB n p)
def concreteBeta (n : ℕ) (p : Fin (concreteDepth n+1)) : ℝ := clippedBeta (concreteB n p) (concreteK p)
def concreteLambda (n : ℕ) (p : Fin (concreteDepth n+1)) : ℝ := 10*Real.log (nativeEll n)/concreteB n p
def concreteTinyBeta (n : ℕ) (p : Fin (concreteDepth n+1)) : ℝ := nativeEll n/concreteB n p
def concreteEligible (n : ℕ) (p : Fin (concreteDepth n+1)) : Prop := concreteB n p ≤ concreteK p
def concreteTinyEligible (n : ℕ) (p : Fin (concreteDepth n+1)) : Prop :=
  concreteEligible n p ∧ nativeEll n ≤ concreteB n p

lemma concreteK_pos {n : ℕ} (p : Fin (concreteDepth n+1)) : 0 < concreteK p := by
  unfold concreteK
  positivity
lemma concreteB_pos (n : ℕ) (p : Fin (concreteDepth n+1)) : 0 < concreteB n p := by
  apply scaleTarget_pos (concreteK_pos p) (nativeEll_pos n)
  exact_mod_cast scaleCount_pos (nativeEll n)
lemma concreteMu_pos (n : ℕ) (p : Fin (concreteDepth n+1)) : 0 < concreteMu n p := by
  apply effectiveMu_pos (concreteK_pos p)
  apply scaleMu_pos (concreteK_pos p) (nativeEll_pos n)
  exact_mod_cast scaleCount_pos (nativeEll n)
lemma concreteBeta_nonneg (n : ℕ) (p : Fin (concreteDepth n+1)) : 0 ≤ concreteBeta n p :=
  clippedBeta_nonneg (concreteB_pos n p).le (concreteK_pos p)
lemma concreteBeta_small (n : ℕ) (p : Fin (concreteDepth n+1)) : concreteBeta n p ≤ 1/64 :=
  clippedBeta_le _ _
lemma concreteBeta_budget (n : ℕ) (p : Fin (concreteDepth n+1)) :
    concreteBeta n p*(64*(4:ℝ)^p.val) ≤ concreteB n p := clippedBeta_budget (concreteK_pos p)
lemma concreteMu_active (n : ℕ) (p : Fin (concreteDepth n+1)) (hp : concreteEligible n p) :
    concreteMu n p = scaleMu (concreteK p) (nativeEll n) (scaleCount (nativeEll n)) :=
  effectiveMu_active hp
lemma concreteBeta_active (n : ℕ) (p : Fin (concreteDepth n+1)) (hp : concreteEligible n p) :
    concreteBeta n p = concreteB n p/(64*concreteK p) := clippedBeta_active (concreteK_pos p) hp
lemma concreteMu_le (n : ℕ) (p : Fin (concreteDepth n+1))
    (hfour : (scaleCount (nativeEll n):ℝ)^4 ≤ Real.sqrt (nativeEll n))
    (hp : concreteEligible n p) : concreteMu n p ≤ concreteK p := by
  rw [concreteMu_active n p hp]
  exact scaleMu_uniform_le (concreteK_pos p).le (nativeEll_pos n) hfour hp

lemma scaleMu_small {k ell P : ℝ} (hell : 0 < ell) (hb : scaleTarget k ell P ≤ ell) :
    scaleMu k ell P = scaleTarget k ell P := by
  apply max_eq_left
  apply (div_le_iff₀ hell).mpr
  have hp := scaleTarget_nonneg k ell P
  nlinarith

end Komlos.KMFresh

-- END KMProof/ConcreteParameters.lean

-- BEGIN KMProof/ConcreteTailCore.lean

noncomputable section
namespace Komlos.KMFresh

noncomputable def concreteMediumCore (n rows : ℕ)
    (hell : 1 < nativeEll n)
    (hlog : 20480*Real.log (nativeEll n) ≤ Real.sqrt (nativeEll n))
    (hthreshold : ∀ k d : ℝ, 0 < k → d ≤ 8*k →
      let ell := nativeEll n
      let P : ℝ := scaleCount ell
      let b := scaleTarget k ell P
      let μ := scaleMu k ell P
      let lam := 10*Real.log ell/b
      let θ := b/(1024*k)
      let α := 64*P*k/μ
      let δ := θ/(4*α*(lam*Real.exp (lam*(2*b))))
      (d*Real.exp (lam*b)+(1-Real.log (confidence n))/δ)/Real.exp (lam*(2*b)) ≤ μ/(64*P))
    (p : Fin (concreteDepth n+1)) (hp : concreteEligible n p) :
    MediumTailCore (concreteDepth n) n rows (concreteMu n) (concreteBeta n)
      (concreteB n) (concreteLambda n) p := by
  let θ := concreteB n p/(1024*concreteK p)
  let α := 64*(scaleCount (nativeEll n):ℝ)*concreteK p/concreteMu n p
  let G := concreteLambda n p*Real.exp (concreteLambda n p*(2*concreteB n p))
  have hk := concreteK_pos p
  have hb := concreteB_pos n p
  have hm := concreteMu_pos n p
  have hP : (0:ℝ) < scaleCount (nativeEll n) := by exact_mod_cast scaleCount_pos (nativeEll n)
  have hl : 0 < concreteLambda n p := by
    unfold concreteLambda
    exact div_pos (mul_pos (by norm_num) (Real.log_pos hell)) hb
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have hG : 0 < G := mul_pos hl (Real.exp_pos _)
  have ht : θ = concreteBeta n p/16 := by
    rw [concreteBeta_active n p hp]
    dsimp [θ]
    ring
  refine ⟨θ/(4*α*G),proxy_delta_pos hθ hα hG,concreteBeta_small n p,hl.le,?_,?_,?_⟩
  · have h := medium_lambda_guard hk (nativeEll_pos n)
      (show (1:ℝ) ≤ scaleCount (nativeEll n) by exact_mod_cast scaleCount_pos (nativeEll n)) hlog
    change concreteLambda n p ≤ θ/2 at h
    rwa [ht] at h
  · change (θ/(4*α*G))^2*(α*G) ≤ (θ/(4*α*G))*((concreteBeta n p/16)/2)
    rw [←ht]
    exact proxy_delta_cancel hθ.le hα hG
  · intro d hd
    have h := hthreshold (concreteK p) d hk (by change d ≤ 2*concreteK p at hd; nlinarith)
    dsimp only at h
    simpa only [θ,α,G,concreteLambda,concreteMu_active n p hp,concreteB,concreteDepth,scaleCount] using h

noncomputable def concreteTinyCore (n : ℕ)
    (hfour : (scaleCount (nativeEll n):ℝ)^4 ≤ Real.sqrt (nativeEll n))
    (p : Fin (concreteDepth n+1)) (hp : concreteTinyEligible n p) :
    TinyTailCore (concreteDepth n) n (concreteMu n) (concreteB n) (concreteTinyBeta n) p := by
  have he := nativeEll_pos n
  have hb := concreteB_pos n p
  have hk := concreteK_pos p
  have hβ : 0 < concreteTinyBeta n p := div_pos he hb
  have hβ1 : concreteTinyBeta n p ≤ 1 := (div_le_one hb).mpr hp.2
  have hm := concreteMu_le n p hfour hp.1
  refine ⟨concreteTinyBeta n p/288,by positivity,hβ.le,hβ1,?_,?_,tiny_delta_cancel hβ.le⟩
  · change concreteMu n p ≤ 64*concreteK p
    nlinarith
  · rw [concreteMu_active n p hp.1,light_mu_quadratic he hp.2]
    change (nativeEll n/concreteB n p)*((concreteB n p)^2/nativeEll n) ≤ concreteB n p
    have hid : (nativeEll n/concreteB n p)*((concreteB n p)^2/nativeEll n) = concreteB n p := by
      field_simp
    exact hid.le

lemma concreteTinyCore_threshold (n : ℕ)
    (hfour : (scaleCount (nativeEll n):ℝ)^4 ≤ Real.sqrt (nativeEll n))
    (hell : 1 ≤ nativeEll n) (p : Fin (concreteDepth n+1)) (hp : concreteTinyEligible n p) :
    3*concreteB n p+1+(1-Real.log (confidence n))/(concreteTinyCore n hfour p hp).delta ≤
      3171*concreteB n p+1 := by
  have h := tiny_confidence_threshold n (concreteB_pos n p) hell
  change 3*concreteB n p+1+(1-Real.log (confidence n))/((nativeEll n/concreteB n p)/288) ≤ _
  linarith

end Komlos.KMFresh

-- END KMProof/ConcreteTailCore.lean

-- BEGIN KMProof/InactiveHistory.lean

namespace Komlos.KMFresh

lemma scaleHistory_no_hit {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) (z : Fin (q + 1) × R)
    (hnever : ∀ x, ¬rowMedium (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val) (fun z => μ z.1) x z)
    (k : ℕ) (ω : Fin k → (Fin n → Bool)) :
    z ∉ (scaleHistory A q ρ μ β b ha hA hμ t k ω).hit := by
  classical
  induction k with
  | zero => exact Finset.notMem_empty z
  | succ k ih =>
    let s := scaleHistory A q ρ μ β b ha hA hμ t k (Fin.init ω)
    let u := ω (Fin.last k)
    have hn : z ∉ s.hit := ih (Fin.init ω)
    change z ∉ (scaleStep A q ρ μ β b ha hA hμ t s u).hit
    by_cases hr : scaleRunning A q ρ μ s
    · intro hh
      have he := (adaptiveStep_hit_iff (scaleRunning A q ρ μ) (scaleDirection A q ρ μ β ha hA hμ)
        (regularizedHit (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
          (fun z => μ z.1) (fun z => β z.1) (fun z => b z.1)) t s u hr z).mp hh
      exact hnever _ (he.resolve_left hn).1
    · have he : scaleStep A q ρ μ β b ha hA hμ t s u = s := adaptiveStep_stopped _ _ _ t s u hr
      rw [he]
      exact hn

lemma scaleHistory_inactive_no_hit {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2)
    (hμ : ∀ p, 0 < effectiveMu ((4 : ℝ)^p.val) (μ p) (b p))
    (t : ℝ) (z : Fin (q + 1) × R) (hb : (4 : ℝ)^z.1.val < b z.1)
    (k : ℕ) (ω : Fin k → (Fin n → Bool)) :
    z ∉ (scaleHistory A q ρ (fun p => effectiveMu ((4 : ℝ)^p.val) (μ p) (b p)) β b
      ha hA hμ t k ω).hit := by
  apply scaleHistory_no_hit A q ρ _ β b ha hA hμ t z _ k ω
  intro x
  exact no_inactive_medium (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
    (fun z => μ z.1) (fun z => b z.1) x z hb

end Komlos.KMFresh

-- END KMProof/InactiveHistory.lean

-- BEGIN KMProof/InactiveColumn.lean

namespace Komlos.KMFresh

lemma inactive_column_zero {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q+1) → ℝ)
    (ha : ∀r i,|A r i| ≤ 1) (hA : ∀i,∑r,(A r i)^2 ≤ 2)
    (hμ : ∀p,0 < effectiveMu ((4:ℝ)^p.val) (μ p) (b p))
    (t : ℝ) (p : Fin (q+1)) (hp : (4:ℝ)^p.val < b p)
    (k : ℕ) (h : History (Fin n → Bool) k) (j : Fin n) :
    (∑r∈(scaleLocalState (scaleHistory A q ρ
      (fun p => effectiveMu ((4:ℝ)^p.val) (μ p) (b p)) β b ha hA hμ t k h) p).hit,
      (scaleEntry q p (A r j))^2)=0 := by
  classical
  apply Finset.sum_eq_zero
  intro r hr
  have hh : (p,r)∈(scaleHistory A q ρ
      (fun p => effectiveMu ((4:ℝ)^p.val) (μ p) (b p)) β b ha hA hμ t k h).hit :=
    (Finset.mem_filter.mp hr).2
  exact (scaleHistory_inactive_no_hit A q ρ μ β b ha hA hμ t (p,r) hp k h hh).elim

end Komlos.KMFresh

-- END KMProof/InactiveColumn.lean

-- BEGIN KMProof/ScaleHistoryStops.lean

namespace Komlos.KMFresh

lemma scaleHistory_stops {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) (ht : 0 ≤ t) (htρ : t ≤ ρ)
    (hβ : ∀ p, 0 ≤ β p) (hb : ∀ p, 0 < b p)
    (hbudget : ∀ p, β p * (64 * (4 : ℝ)^p.val) ≤ b p)
    (N : ℕ) (hN : (n : ℝ) < (N : ℝ) * t^2) (ω : Fin N → (Fin n → Bool)) :
    ¬scaleRunning A q ρ μ (scaleHistory A q ρ μ β b ha hA hμ t N ω) := by
  apply adaptiveHistory_stops ⟨0, ∅⟩ (fun _ => scaleStep A q ρ μ β b ha hA hμ t)
    (scaleRunning A q ρ μ) (fun s => ∑ i, s.x i^2) (t^2) n N
  · simp
  · intro _ s u hs
    change ¬scaleRunning A q ρ μ (adaptiveStep _ _ _ _ s u)
    rw [adaptiveStep_stopped _ _ _ t s u hs]
    exact hs
  · intro _ s u hs
    exact adaptiveStep_energy _ _ _ t s u hs
      (scaleDirection_geometry A q ρ μ β ha hA hμ s hs u).2.2.1
      (scaleDirection_geometry A q ρ μ β ha hA hμ s hs u).1
  · intro h
    have hx := (scaleHistory_valid A q ρ μ β b ha hA hμ t ht htρ hβ hb hbudget N h).1
    calc
      (∑ i, (scaleHistory A q ρ μ β b ha hA hμ t N h).x i^2) ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := abs_le.mp (hx i)
        nlinarith
      _ = (n : ℝ) := by simp
  · exact hN

lemma scaleHistory_good_final_size {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ : Fin (q + 1) → ℝ)
    (s : AdaptiveState (Fin (q + 1) × R) n) (hs : ¬scaleRunning A q ρ μ s)
    (hg : scaleGood A q ρ μ s) : ((aliveSet ρ s.x).card : ℝ) ≤ 16 * ((q + 1 : ℕ) : ℝ) := by
  by_contra hn
  exact hs ⟨lt_of_not_ge hn, hg⟩

end Komlos.KMFresh

-- END KMProof/ScaleHistoryStops.lean

-- BEGIN KMProof/ConcreteGoodTrajectory.lean

noncomputable section
namespace Komlos.KMFresh

lemma concrete_good_trajectory {R : Type*} [Fintype R] (n : ℕ)
    (A : R → Fin n → ℝ) (ha : ∀r i,|A r i| ≤ 1) (hA : ∀i,∑r,(A r i)^2 ≤ 2)
    (hR : Fintype.card R ≤ 2*n^3) (ρ : ℝ) (hρ : 0 < ρ)
    (hell : 1 < nativeEll n)
    (hfour : (scaleCount (nativeEll n):ℝ)^4 ≤ Real.sqrt (nativeEll n))
    (hlog : 20480*Real.log (nativeEll n) ≤ Real.sqrt (nativeEll n))
    (hP : concreteDepth n+1 ≤ n+2)
    (hthreshold : ∀ k d : ℝ, 0 < k → d ≤ 8*k →
      let ell := nativeEll n
      let P : ℝ := scaleCount ell
      let b := scaleTarget k ell P
      let μ := scaleMu k ell P
      let lam := 10*Real.log ell/b
      let θ := b/(1024*k)
      let α := 64*P*k/μ
      let δ := θ/(4*α*(lam*Real.exp (lam*(2*b))))
      (d*Real.exp (lam*b)+(1-Real.log (confidence n))/δ)/Real.exp (lam*(2*b)) ≤ μ/(64*P))
    : ∃ε:ℝ, ∃h : History (Fin n → Bool) (walkHorizon n ε),
      0 < ε ∧ ε ≤ 1 ∧ Real.sqrt ε ≤ ρ ∧
      2*(3*Real.sqrt (n:ℝ)+1)*Real.sqrt ε ≤ 1 ∧
      (let T := scaleHistory A (concreteDepth n) ρ (concreteMu n) (concreteBeta n) (concreteB n)
          ha hA (concreteMu_pos n) (Real.sqrt ε)
       (∀p j k (hk:k ≤ walkHorizon n ε),
         (∑r∈(scaleLocalState (T k (historyPrefix h k hk)) p).hit,
           (scaleEntry (concreteDepth n) p (A r j))^2) ≤
             concreteMu n p/(64*((concreteDepth n+1:ℕ):ℝ))) ∧
       (∀p r,concreteTinyEligible n p → ∀k (hk:k ≤ walkHorizon n ε),
         rowTiny (scaleRows A (concreteDepth n)) ρ (fun z => concreteMu n z.1)
           (T k (historyPrefix h k hk)).x (p,r) →
         rowRegularizer (scaleRows A (concreteDepth n)) ρ (fun z => concreteTinyBeta n z.1)
           (T k (historyPrefix h k hk)).x (p,r) < 3171*concreteB n p+1) ∧
       (∀i,|(T (walkHorizon n ε) h).x i| ≤ 1) ∧
       ((aliveSet ρ (T (walkHorizon n ε) h).x).card:ℝ) ≤ 16*((concreteDepth n+1:ℕ):ℝ)) := by
  classical
  let M := concreteMediumCore n (Fintype.card R) hell hlog hthreshold
  let T := concreteTinyCore n hfour
  obtain ⟨ε,he,he1,her,hraw,M',T',hMeq,hTeq⟩ := exists_tail_condition_step
    (concreteDepth n) n (Fintype.card R) ρ hρ (concreteMu n) (concreteBeta n)
    (concreteB n) (concreteLambda n) (concreteTinyBeta n)
    (concreteEligible n) (concreteTinyEligible n) M T
  have hβone p : concreteBeta n p ≤ 1 := (concreteBeta_small n p).trans (by norm_num)
  have hrow p hp : 3*concreteB n p+1+(1-Real.log (confidence n))/(T' p hp).delta ≤
      3171*concreteB n p+1 := by
    rw [hTeq]
    exact concreteTinyCore_threshold n hfour hell.le p hp
  have hi p (hp:¬concreteEligible n p) k (h:History (Fin n → Bool) k) j :
      (∑r∈(scaleLocalState (scaleHistory A (concreteDepth n) ρ (concreteMu n) (concreteBeta n)
        (concreteB n) ha hA (concreteMu_pos n) (Real.sqrt ε) k h) p).hit,
        (scaleEntry (concreteDepth n) p (A r j))^2) ≤
          concreteMu n p/(64*((concreteDepth n+1:ℕ):ℝ)) := by
    have hz := inactive_column_zero A (concreteDepth n) ρ
      (fun p => scaleMu (concreteK p) (nativeEll n) (scaleCount (nativeEll n)))
      (concreteBeta n) (concreteB n) ha hA (concreteMu_pos n) (Real.sqrt ε) p
      (lt_of_not_ge hp) k h j
    change (∑r∈(scaleLocalState (scaleHistory A (concreteDepth n) ρ (concreteMu n) (concreteBeta n)
        (concreteB n) ha hA (concreteMu_pos n) (Real.sqrt ε) k h) p).hit,
        (scaleEntry (concreteDepth n) p (A r j))^2)=0 at hz
    rw [hz]
    exact div_nonneg (concreteMu_pos n p).le (by positivity)
  obtain ⟨h,hc,ht⟩ := actual_good_history A (concreteDepth n) ρ (concreteMu n) (concreteBeta n)
    (concreteB n) (concreteLambda n) (concreteTinyBeta n) ha hA (concreteMu_pos n)
    (concreteBeta_nonneg n) hβone (concreteB_pos n) (concreteBeta_budget n)
    ε he he1 her hraw (walkHorizon n ε) hR hP (concreteEligible n) (concreteTinyEligible n)
    M' T' (fun p => 3171*concreteB n p+1) hrow hi
  have hpref : historyPrefix h (walkHorizon n ε) le_rfl=h := by
    funext i
    rfl
  have hg : scaleGood A (concreteDepth n) ρ (concreteMu n)
      (scaleHistory A (concreteDepth n) ρ (concreteMu n) (concreteBeta n) (concreteB n)
        ha hA (concreteMu_pos n) (Real.sqrt ε) (walkHorizon n ε) h) := by
    intro p j _
    simpa only [hpref] using hc p j (walkHorizon n ε) le_rfl
  have hstop := scaleHistory_stops A (concreteDepth n) ρ (concreteMu n) (concreteBeta n)
    (concreteB n) ha hA (concreteMu_pos n) (Real.sqrt ε) (Real.sqrt_nonneg ε) her
    (concreteBeta_nonneg n) (concreteB_pos n) (concreteBeta_budget n) (walkHorizon n ε)
    (by simpa only [Real.sq_sqrt he.le] using walkHorizon_lower n he) h
  have hsize := scaleHistory_good_final_size A (concreteDepth n) ρ (concreteMu n) _ hstop hg
  have hv := scaleHistory_valid A (concreteDepth n) ρ (concreteMu n) (concreteBeta n)
    (concreteB n) ha hA (concreteMu_pos n) (Real.sqrt ε) (Real.sqrt_nonneg ε) her
    (concreteBeta_nonneg n) (concreteB_pos n) (concreteBeta_budget n) (walkHorizon n ε) h
  exact ⟨ε,h,he,he1,her,hraw,hc,ht,hv.1,hsize⟩

end Komlos.KMFresh

-- END KMProof/ConcreteGoodTrajectory.lean

-- BEGIN KMProof/ConcreteGuards.lean

noncomputable section
open Filter
namespace Komlos.KMFresh

structure ConcreteGuards (n : ℕ) : Prop where
  ell : 1 < nativeEll n
  fourth : (scaleCount (nativeEll n):ℝ)^4 ≤ Real.sqrt (nativeEll n)
  drift : 20480*Real.log (nativeEll n) ≤ Real.sqrt (nativeEll n)
  count : concreteDepth n+1 ≤ n+2
  threshold : ∀ k d : ℝ, 0 < k → d ≤ 8*k →
      let ell := nativeEll n
      let P : ℝ := scaleCount ell
      let b := scaleTarget k ell P
      let μ := scaleMu k ell P
      let lam := 10*Real.log ell/b
      let θ := b/(1024*k)
      let α := 64*P*k/μ
      let δ := θ/(4*α*(lam*Real.exp (lam*(2*b))))
      (d*Real.exp (lam*b)+(1-Real.log (confidence n))/δ)/Real.exp (lam*(2*b)) ≤ μ/(64*P)

lemma eventually_concrete_guards : ∀ᶠ n:ℕ in atTop,ConcreteGuards n := by
  filter_upwards [nativeEll_atTop.eventually_gt_atTop 1,
    nativeEll_atTop.eventually eventually_scaleCount_four_le,
    nativeEll_atTop.eventually eventually_log_drift_guard,
    eventually_native_confidence_guards,eventually_medium_threshold] with n he hf hd hc hm
  refine ⟨he,hf,hd,?_,hm⟩
  exact hc.1

end Komlos.KMFresh

-- END KMProof/ConcreteGuards.lean

-- BEGIN KMProof/ConcreteGeometry.lean

namespace Komlos.KMFresh

lemma concreteB_one (n : ℕ) (hell : 1 ≤ nativeEll n) (p : Fin (concreteDepth n+1)) :
    1 ≤ concreteB n p := by
  have hk : (1:ℝ) ≤ concreteK p := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4)
  have hP : (1:ℝ) ≤ scaleCount (nativeEll n) := by exact_mod_cast scaleCount_pos (nativeEll n)
  have hs : 1 ≤ Real.sqrt (nativeEll n) := by simpa using Real.sqrt_le_sqrt hell
  have hss : 1 ≤ Real.sqrt (Real.sqrt (nativeEll n)) := by simpa using Real.sqrt_le_sqrt hs
  have hsk : 1 ≤ Real.sqrt (concreteK p) := by simpa using Real.sqrt_le_sqrt hk
  have hp2 : (1:ℝ) ≤ (scaleCount (nativeEll n):ℝ)^2 := one_le_pow₀ hP
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hsk hss) hp2

lemma concrete_light_bounds (n : ℕ) (hell : 1 ≤ nativeEll n)
    (hfour : (scaleCount (nativeEll n):ℝ)^4 ≤ Real.sqrt (nativeEll n))
    (p : Fin (concreteDepth n+1)) (hp : p.val = concreteDepth n) :
    nativeEll n ≤ concreteB n p ∧ concreteEligible n p := by
  apply light_target_between hell
    (show (1:ℝ) ≤ scaleCount (nativeEll n) by exact_mod_cast scaleCount_pos (nativeEll n))
  · change (nativeEll n)^10 ≤ (4:ℝ)^p.val
    rw [hp]
    exact (scaleDepth_four_bounds hell).1
  · exact hfour

lemma concrete_ineligible_heavy (n : ℕ) (hell : 1 ≤ nativeEll n)
    (hfour : (scaleCount (nativeEll n):ℝ)^4 ≤ Real.sqrt (nativeEll n))
    (p : Fin (concreteDepth n+1)) (hp : ¬concreteEligible n p) : p.val < concreteDepth n := by
  by_contra hh
  have he : p.val = concreteDepth n := by omega
  exact hp (concrete_light_bounds n hell hfour p he).2

lemma concrete_small_heavy (n : ℕ) (hell : 1 ≤ nativeEll n)
    (hfour : (scaleCount (nativeEll n):ℝ)^4 ≤ Real.sqrt (nativeEll n))
    (p : Fin (concreteDepth n+1)) (hp : concreteB n p < nativeEll n) : p.val < concreteDepth n := by
  by_contra hh
  have he : p.val = concreteDepth n := by omega
  exact not_lt_of_ge (concrete_light_bounds n hell hfour p he).1 hp

lemma concrete_small_mu (n : ℕ) (p : Fin (concreteDepth n+1))
    (hp : concreteEligible n p) (hb : concreteB n p ≤ nativeEll n) :
    concreteMu n p = concreteB n p := by
  rw [concreteMu_active n p hp]
  exact scaleMu_small (nativeEll_pos n) hb

end Komlos.KMFresh

-- END KMProof/ConcreteGeometry.lean

-- BEGIN KMProof/HeavyRows.lean

namespace Komlos.KMFresh

lemma heavy_abs_le_square (a : ℝ) (ha : a = 0 ∨ (1 : ℝ) / 2 ≤ |a|) :
    |a| ≤ 2 * a ^ 2 := by
  rcases ha with rfl | ha
  · norm_num
  · have he := sq_abs a
    nlinarith [sq_nonneg (|a| - 1 / 2)]

lemma heavy_l1_le_energy {I : Type*} (A : Finset I) (a : I → ℝ)
    (ha : ∀ i ∈ A, a i = 0 ∨ (1 : ℝ) / 2 ≤ |a i|) :
    ∑ i ∈ A, |a i| ≤ 2 * ∑ i ∈ A, a i ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => heavy_abs_le_square (a i) (ha i hi))

lemma heavy_future_displacement {I : Type*} (A : Finset I) (a x y : I → ℝ)
    (ha : ∀ i ∈ A, a i = 0 ∨ (1 : ℝ) / 2 ≤ |a i|)
    (hx : ∀ i ∈ A, |x i| ≤ 1) (hy : ∀ i ∈ A, |y i| ≤ 1) :
    |∑ i ∈ A, a i * (y i - x i)| ≤ 4 * ∑ i ∈ A, a i ^ 2 := by
  calc
    |∑ i ∈ A, a i * (y i - x i)| ≤ ∑ i ∈ A, |a i * (y i - x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ A, (2 * |a i|) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hd : |y i - x i| ≤ 2 := by
        calc
          |y i - x i| ≤ |y i| + |x i| := abs_sub _ _
          _ ≤ 2 := by linarith [hx i hi, hy i hi]
      nlinarith [mul_le_mul_of_nonneg_left hd (abs_nonneg (a i))]
    _ = 2 * ∑ i ∈ A, |a i| := (Finset.mul_sum ..).symm
    _ ≤ 4 * ∑ i ∈ A, a i ^ 2 := by
      have h := heavy_l1_le_energy A a ha
      linarith

end Komlos.KMFresh

-- END KMProof/HeavyRows.lean

-- BEGIN KMProof/ContinuationBound.lean

namespace Komlos.KMFresh

noncomputable def continuationBound {I : Type*} [Fintype I]
    (S : Finset I) (a x : I → ℝ) : ℝ :=
  (∑ i, a i * x i) + ∑ i ∈ S, (|a i| - a i * x i)

lemma continuation_summand_nonneg {a x : ℝ} (hx : |x| ≤ 1) : 0 ≤ |a| - a * x := by
  have he := (le_abs_self (a * x)).trans ((abs_mul a x).le.trans
    (mul_le_mul_of_nonneg_left hx (abs_nonneg a)))
  simpa only [mul_one] using sub_nonneg.mpr he

lemma discrepancy_le_continuation {I : Type*} [Fintype I]
    (S : Finset I) (a x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    (∑ i, a i * x i) ≤ continuationBound S a x :=
  le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => continuation_summand_nonneg (hx i)))

lemma continuationBound_le {I : Type*} [Fintype I]
    (S : Finset I) (a x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    continuationBound S a x ≤ (∑ i, a i * x i) + 2 * ∑ i ∈ S, |a i| := by
  apply add_le_add le_rfl
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have he := neg_le_abs (a i * x i)
  have hm := mul_le_mul_of_nonneg_left (hx i) (abs_nonneg (a i))
  rw [← abs_mul, mul_one] at hm
  linarith

lemma continuationBound_fixed {I : Type*} [Fintype I]
    (S : Finset I) (a x y : I → ℝ) (hfix : ∀ i, i ∉ S → y i = x i) :
    continuationBound S a y = continuationBound S a x := by
  have he : (∑ i, (a i * y i - a i * x i)) = ∑ i ∈ S, (a i * y i - a i * x i) := by
    apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro i _ hi
    rw [hfix i hi, sub_self]
  simp only [Finset.sum_sub_distrib] at he
  unfold continuationBound
  simp only [Finset.sum_sub_distrib]
  linarith

lemma continuationBound_mono {I : Type*} [Fintype I]
    (S T : Finset I) (a x y : I → ℝ) (hTS : T ⊆ S)
    (hfix : ∀ i, i ∉ S → y i = x i) (hy : ∀ i, |y i| ≤ 1) :
    continuationBound T a y ≤ continuationBound S a x := by
  rw [← continuationBound_fixed S a x y hfix]
  apply add_le_add le_rfl
  exact Finset.sum_le_sum_of_subset_of_nonneg hTS
    (fun i _ _ => continuation_summand_nonneg (hy i))

end Komlos.KMFresh

-- END KMProof/ContinuationBound.lean

-- BEGIN KMProof/HeavyContinuation.lean

namespace Komlos.KMFresh

lemma heavy_continuation_bound {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (x : Fin n → ℝ) (r : R) (hx : ∀ i, |x i| ≤ 1)
    (ha : ∀ i, A r i = 0 ∨ (1 : ℝ)/2 ≤ |A r i|) :
    continuationBound (aliveSet ρ x) (A r) x ≤ rowDiscrepancy A x r + 4 * rowEnergy A ρ x r := by
  have he := continuationBound_le (aliveSet ρ x) (A r) x hx
  have hh := heavy_l1_le_energy (aliveSet ρ x) (A r) (fun i _ => ha i)
  change continuationBound (aliveSet ρ x) (A r) x ≤ _
  unfold rowDiscrepancy rowEnergy
  linarith

lemma row_continuation_mono {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (x y : Fin n → ℝ) (r : R)
    (hfix : ∀ i, i ∉ aliveSet ρ x → y i = x i) (hy : ∀ i, |y i| ≤ 1) :
    continuationBound (aliveSet ρ y) (A r) y ≤ continuationBound (aliveSet ρ x) (A r) x :=
  continuationBound_mono _ _ _ _ _ (aliveSet_shrinks ρ x y hfix) hfix hy

end Komlos.KMFresh

-- END KMProof/HeavyContinuation.lean

-- BEGIN KMProof/ScaleHeavyBound.lean

namespace Komlos.KMFresh

lemma scaleEntry_heavy_lower (q : ℕ) (p : Fin (q + 1)) (hp : p.val < q) (a : ℝ) :
    scaleEntry q p a = 0 ∨ (1 : ℝ)/2 ≤ |scaleEntry q p a| := by
  have he : scaleEntry q p a = normalizedHeavy p.val a := by
    simp only [scaleEntry, rawScale, if_pos hp, normalizedHeavy]
  rw [he]
  exact (normalizedHeavy_lower p.val a).imp_right le_of_lt

lemma scaleHistory_heavy_continuation {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) (ht : 0 ≤ t) (htρ : t ≤ ρ)
    (hβ : ∀ p, 0 ≤ β p) (hb : ∀ p, 0 < b p)
    (hbudget : ∀ p, β p * (64 * (4 : ℝ)^p.val) ≤ b p)
    (z : Fin (q + 1) × R) (hp : z.1.val < q)
    (k : ℕ) (ω : Fin k → (Fin n → Bool))
    (hl : ¬rowLarge (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val)
      (scaleHistory A q ρ μ β b ha hA hμ t k ω).x z) :
    continuationBound (aliveSet ρ (scaleHistory A q ρ μ β b ha hA hμ t k ω).x)
      (scaleRows A q z) (scaleHistory A q ρ μ β b ha hA hμ t k ω).x ≤ 256 * (4 : ℝ)^z.1.val := by
  have hheavy : ∀ i, scaleRows A q z i = 0 ∨ (1 : ℝ)/2 ≤ |scaleRows A q z i| :=
    fun i => scaleEntry_heavy_lower q z.1 hp (A z.2 i)
  induction k with
  | zero =>
    have he := heavy_continuation_bound (scaleRows A q) ρ (0 : Fin n → ℝ) z (by intro i; simp) hheavy
    have hd : rowDiscrepancy (scaleRows A q) (0 : Fin n → ℝ) z = 0 := by simp [rowDiscrepancy]
    rw [hd, zero_add] at he
    have hbnd : rowEnergy (scaleRows A q) ρ (0 : Fin n → ℝ) z ≤ 64 * (4 : ℝ)^z.1.val := le_of_not_gt hl
    change continuationBound (aliveSet ρ (0 : Fin n → ℝ)) (scaleRows A q z) 0 ≤ _
    linarith
  | succ k ih =>
    let s := scaleHistory A q ρ μ β b ha hA hμ t k (Fin.init ω)
    let u := ω (Fin.last k)
    have hs := scaleHistory_valid A q ρ μ β b ha hA hμ t ht htρ hβ hb hbudget k (Fin.init ω)
    change ¬rowLarge _ _ _ (scaleStep A q ρ μ β b ha hA hμ t s u).x z at hl
    change continuationBound (aliveSet ρ (scaleStep A q ρ μ β b ha hA hμ t s u).x)
      (scaleRows A q z) (scaleStep A q ρ μ β b ha hA hμ t s u).x ≤ _
    by_cases hr : scaleRunning A q ρ μ s
    · have hg := scaleDirection_geometry A q ρ μ β ha hA hμ s hr u
      have hy := (scaleStep_valid A q ρ μ β b ha hA hμ t ht htρ s u hs).1
      by_cases hold : rowLarge (scaleRows A q) ρ (fun z => (4 : ℝ)^z.1.val) s.x z
      · have hz : z ∈ scaleLarge A q ρ s.x := by
          classical
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hold⟩
        have hd : rowDiscrepancy (scaleRows A q) (scaleStep A q ρ μ β b ha hA hμ t s u).x z = 0 := by
          change rowDiscrepancy _ (adaptiveStep _ _ _ _ s u).x z = _
          rw [adaptiveStep_x _ _ _ t s u hr,
            blocked_row_unchanged (scaleRows A q) s.x _ t z (hg.2.2.2 z hz)]
          exact hs.2.1 z hold
        have he := heavy_continuation_bound (scaleRows A q) ρ _ z hy hheavy
        rw [hd, zero_add] at he
        have hbnd := le_of_not_gt hl
        change rowEnergy (scaleRows A q) ρ _ z ≤ 64 * (4 : ℝ)^z.1.val at hbnd
        linarith
      · have he := row_continuation_mono (scaleRows A q) ρ s.x
          (scaleStep A q ρ μ β b ha hA hμ t s u).x z (fun i hi => by
            change (adaptiveStep _ _ _ _ s u).x i = _
            rw [adaptiveStep_x _ _ _ t s u hr]
            dsimp only
            rw [hg.2.1 i hi, mul_zero, add_zero]) hy
        exact he.trans (ih (Fin.init ω) hold)
    · have he : scaleStep A q ρ μ β b ha hA hμ t s u = s := adaptiveStep_stopped _ _ _ t s u hr
      rw [he] at hl ⊢
      exact ih (Fin.init ω) hl

end Komlos.KMFresh

-- END KMProof/ScaleHeavyBound.lean

-- BEGIN KMProof/ScaleSmallTinyBound.lean

namespace Komlos.KMFresh

lemma scaleHistory_small_tiny_continuation {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (q : ℕ) (ρ : ℝ) (μ β b : Fin (q + 1) → ℝ)
    (ha : ∀ r i, |A r i| ≤ 1) (hA : ∀ i, ∑ r, A r i ^ 2 ≤ 2) (hμ : ∀ p, 0 < μ p)
    (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) (htρ : t ≤ ρ)
    (hsmall : 2 * (3 * Real.sqrt (n : ℝ) + 1) * t ≤ 1)
    (hβ : ∀ p, 0 ≤ β p) (hβone : ∀ p, β p ≤ 1) (hb : ∀ p, 0 < b p)
    (hbudget : ∀ p, β p * (64 * (4 : ℝ)^p.val) ≤ b p)
    (z : Fin (q + 1) × R) (hp : z.1.val < q) (hμb : μ z.1 = b z.1)
    (hbupper : b z.1 ≤ 64 * (4 : ℝ)^z.1.val)
    (k : ℕ) (ω : Fin k → (Fin n → Bool))
    (htiny : rowTiny (scaleRows A q) ρ (fun z => μ z.1)
      (scaleHistory A q ρ μ β b ha hA hμ t k ω).x z) :
    continuationBound (aliveSet ρ (scaleHistory A q ρ μ β b ha hA hμ t k ω).x)
      (scaleRows A q z) (scaleHistory A q ρ μ β b ha hA hμ t k ω).x ≤ 7 * b z.1 + 1 := by
  have hheavy : ∀ i, scaleRows A q z i = 0 ∨ (1 : ℝ)/2 ≤ |scaleRows A q z i| :=
    fun i => scaleEntry_heavy_lower q z.1 hp (A z.2 i)
  induction k with
  | zero =>
    have he := heavy_continuation_bound (scaleRows A q) ρ (0 : Fin n → ℝ) z (by intro i; simp) hheavy
    have hd : rowDiscrepancy (scaleRows A q) (0 : Fin n → ℝ) z = 0 := by simp [rowDiscrepancy]
    rw [hd, zero_add] at he
    change rowEnergy (scaleRows A q) ρ (0 : Fin n → ℝ) z ≤ μ z.1 at htiny
    rw [hμb] at htiny
    change continuationBound (aliveSet ρ (0 : Fin n → ℝ)) (scaleRows A q z) 0 ≤ _
    linarith [hb z.1]
  | succ k ih =>
    let s := scaleHistory A q ρ μ β b ha hA hμ t k (Fin.init ω)
    let u := ω (Fin.last k)
    have hs := scaleHistory_valid A q ρ μ β b ha hA hμ t ht htρ hβ hb hbudget k (Fin.init ω)
    have hy := (scaleStep_valid A q ρ μ β b ha hA hμ t ht htρ s u hs).1
    change rowTiny _ _ _ (scaleStep A q ρ μ β b ha hA hμ t s u).x z at htiny
    change continuationBound (aliveSet ρ (scaleStep A q ρ μ β b ha hA hμ t s u).x)
      (scaleRows A q z) (scaleStep A q ρ μ β b ha hA hμ t s u).x ≤ _
    by_cases hold : rowTiny (scaleRows A q) ρ (fun z => μ z.1) s.x z
    · have hfix : ∀ i, i ∉ aliveSet ρ s.x → (scaleStep A q ρ μ β b ha hA hμ t s u).x i = s.x i := by
        intro i hi
        by_cases hr : scaleRunning A q ρ μ s
        · change (adaptiveStep _ _ _ _ s u).x i = _
          rw [adaptiveStep_x _ _ _ t s u hr]
          dsimp only
          rw [(scaleDirection_geometry A q ρ μ β ha hA hμ s hr u).2.1 i hi, mul_zero, add_zero]
        · have he : scaleStep A q ρ μ β b ha hA hμ t s u = s := adaptiveStep_stopped _ _ _ t s u hr
          rw [he]
      exact (row_continuation_mono (scaleRows A q) ρ s.x _ z hfix hy).trans (ih (Fin.init ω) hold)
    · have hentry := scaleStep_tiny_entry A q ρ μ β b (fun _ => 0) ha hA hμ t ht htone htρ hsmall
        s u hs z (hβ z.1) (hβone z.1) (hb z.1) (hbudget z.1)
        (fun hm => scaleHistory_medium_cap A q ρ μ β b ha hA hμ t ht htone htρ hsmall
          hβ hβone hb hbudget k (Fin.init ω) z hm)
        (by norm_num) (by rw [hμb]; exact hbupper) (by simpa using (hb z.1).le) hold htiny
      have hd : rowDiscrepancy (scaleRows A q) (scaleStep A q ρ μ β b ha hA hμ t s u).x z ≤ 3 * b z.1 + 1 := by
        simpa only [rowRegularizer, activeRegularizer, zero_mul, add_zero, rowDiscrepancy] using hentry
      have he := heavy_continuation_bound (scaleRows A q) ρ _ z hy hheavy
      change rowEnergy (scaleRows A q) ρ _ z ≤ μ z.1 at htiny
      rw [hμb] at htiny
      linarith

end Komlos.KMFresh

-- END KMProof/ScaleSmallTinyBound.lean

-- BEGIN KMProof/RegularizerLower.lean

namespace Komlos.KMFresh
lemma discrepancy_le_regularizer {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (ρ : ℝ) (β : R → ℝ) (x : Fin n → ℝ) (r : R)
    (hβ : 0 ≤ β r) (hx : ∀ i, |x i| ≤ 1) :
    rowDiscrepancy A x r ≤ rowRegularizer A ρ β x r := by
  apply le_add_of_nonneg_right
  apply mul_nonneg hβ
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (sq_nonneg _)
  have hh := abs_le.mp (hx i)
  nlinarith
end Komlos.KMFresh

-- END KMProof/RegularizerLower.lean

-- BEGIN KMProof/ConcreteRowBound.lean

namespace Komlos.KMFresh

lemma concrete_history_row_bound {R : Type*} [Fintype R] {n : ℕ}
    (A : R → Fin n → ℝ) (ρ : ℝ)
    (ha : ∀r i, |A r i| ≤ 1) (hA : ∀i, ∑r, A r i^2 ≤ 2)
    (hell : 1 ≤ nativeEll n)
    (hfour : (scaleCount (nativeEll n):ℝ)^4 ≤ Real.sqrt (nativeEll n))
    (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) (htρ : t ≤ ρ)
    (hraw : 2*(3*Real.sqrt (n:ℝ)+1)*t ≤ 1)
    (N : ℕ) (ω : Fin N → (Fin n → Bool))
    (htiny : ∀p r, concreteTinyEligible n p →
      rowTiny (scaleRows A (concreteDepth n)) ρ (fun z => concreteMu n z.1)
        (scaleHistory A (concreteDepth n) ρ (concreteMu n) (concreteBeta n) (concreteB n)
          ha hA (concreteMu_pos n) t N ω).x (p,r) →
      rowRegularizer (scaleRows A (concreteDepth n)) ρ (fun z => concreteTinyBeta n z.1)
        (scaleHistory A (concreteDepth n) ρ (concreteMu n) (concreteBeta n) (concreteB n)
          ha hA (concreteMu_pos n) t N ω).x (p,r) < 3171*concreteB n p+1)
    (z : Fin (concreteDepth n+1) × R) :
    rowDiscrepancy (scaleRows A (concreteDepth n))
      (scaleHistory A (concreteDepth n) ρ (concreteMu n) (concreteBeta n) (concreteB n)
        ha hA (concreteMu_pos n) t N ω).x z ≤ 3200*concreteB n z.1 := by
  let q := concreteDepth n
  let s := scaleHistory A q ρ (concreteMu n) (concreteBeta n) (concreteB n)
    ha hA (concreteMu_pos n) t N ω
  have hb := concreteB_pos n z.1
  have hb1 := concreteB_one n hell z.1
  have hβone : ∀p, concreteBeta n p ≤ 1 := fun p => (concreteBeta_small n p).trans (by norm_num)
  have hv := scaleHistory_valid A q ρ (concreteMu n) (concreteBeta n) (concreteB n)
    ha hA (concreteMu_pos n) t ht htρ (concreteBeta_nonneg n) (concreteB_pos n) (concreteBeta_budget n) N ω
  change rowDiscrepancy (scaleRows A q) s.x z ≤ _
  by_cases hl : rowLarge (scaleRows A q) ρ (fun z => (4:ℝ)^z.1.val) s.x z
  · rw [hv.2.1 z hl]
    positivity
  by_cases he : concreteEligible n z.1
  · by_cases hti : rowTiny (scaleRows A q) ρ (fun z => concreteMu n z.1) s.x z
    · by_cases hs : nativeEll n ≤ concreteB n z.1
      · have hh := htiny z.1 z.2 ⟨he,hs⟩ hti
        have hd := discrepancy_le_regularizer (scaleRows A q) ρ (fun z => concreteTinyBeta n z.1) s.x z
          (div_nonneg (nativeEll_pos n).le hb.le) hv.1
        linarith
      · have hs' := lt_of_not_ge hs
        have hp := concrete_small_heavy n hell hfour z.1 hs'
        have hm := concrete_small_mu n z.1 he hs'.le
        have hu : concreteB n z.1 ≤ 64*(4:ℝ)^z.1.val := by
          have hk := concreteK_pos z.1
          change concreteB n z.1 ≤ concreteK z.1 at he
          change concreteB n z.1 ≤ 64*concreteK z.1
          nlinarith
        have hh := scaleHistory_small_tiny_continuation A q ρ (concreteMu n) (concreteBeta n) (concreteB n)
          ha hA (concreteMu_pos n) t ht htone htρ hraw (concreteBeta_nonneg n) hβone
          (concreteB_pos n) (concreteBeta_budget n) z hp hm hu N ω hti
        have hd := discrepancy_le_continuation (aliveSet ρ s.x) (scaleRows A q z) s.x hv.1
        change rowDiscrepancy (scaleRows A q) s.x z ≤ _ at hd
        linarith
    · have hm : rowMedium (scaleRows A q) ρ (fun z => (4:ℝ)^z.1.val)
          (fun z => concreteMu n z.1) s.x z := ⟨lt_of_not_ge hti,le_of_not_gt hl⟩
      have hh := scaleHistory_medium_cap A q ρ (concreteMu n) (concreteBeta n) (concreteB n)
        ha hA (concreteMu_pos n) t ht htone htρ hraw (concreteBeta_nonneg n) hβone
        (concreteB_pos n) (concreteBeta_budget n) N ω z hm
      have hd := discrepancy_le_regularizer (scaleRows A q) ρ (fun z => concreteBeta n z.1) s.x z
        (concreteBeta_nonneg n z.1) hv.1
      linarith
  · have hp := concrete_ineligible_heavy n hell hfour z.1 he
    have hh := scaleHistory_heavy_continuation A q ρ (concreteMu n) (concreteBeta n) (concreteB n)
      ha hA (concreteMu_pos n) t ht htρ (concreteBeta_nonneg n) (concreteB_pos n)
      (concreteBeta_budget n) z hp N ω hl
    have hd := discrepancy_le_continuation (aliveSet ρ s.x) (scaleRows A q z) s.x hv.1
    change rowDiscrepancy (scaleRows A q) s.x z ≤ _ at hd
    have hk : (4:ℝ)^z.1.val < concreteB n z.1 := lt_of_not_ge he
    linarith

end Komlos.KMFresh

-- END KMProof/ConcreteRowBound.lean

-- BEGIN KMProof/Rounding.lean

namespace Komlos.KMFresh

noncomputable def roundSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

lemma roundSign_sign (x : ℝ) : roundSign x = 1 ∨ roundSign x = -1 := by
  unfold roundSign
  split_ifs <;> simp

lemma roundSign_error (x : ℝ) (hx : |x| ≤ 1) :
    |roundSign x - x| = 1 - |x| := by
  unfold roundSign
  split_ifs with h
  · rw [abs_of_nonneg h, abs_of_nonneg]
    linarith [(abs_le.mp hx).2]
  · have hn : x ≤ 0 := le_of_lt (lt_of_not_ge h)
    have he : -1 - x ≤ 0 := by linarith [(abs_le.mp hx).1]
    rw [abs_of_nonpos hn, abs_of_nonpos he]
    ring

lemma roundSign_frozen_error (x ρ : ℝ) (hx : |x| ≤ 1)
    (hf : 1 - ρ ≤ |x|) : |roundSign x - x| ≤ ρ := by
  rw [roundSign_error x hx]
  linarith

lemma roundSign_error_le_two (x : ℝ) (hx : |x| ≤ 1) :
    |roundSign x - x| ≤ 2 := by
  rw [roundSign_error x hx]
  have := abs_nonneg x
  linarith

lemma rounded_isSignVector {n : ℕ} (x : Fin n → ℝ) :
    Komlos.IsSignVector (fun i => roundSign (x i)) := by
  intro i
  exact roundSign_sign (x i)

lemma weighted_rounding_error {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (a x : I → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ha : ∀ i, |a i| ≤ 1) (hx : ∀ i, |x i| ≤ 1)
    (hf : ∀ i, i ∉ A → 1 - ρ ≤ |x i|) :
    |(∑ i, a i * roundSign (x i)) - ∑ i, a i * x i| ≤
      (Fintype.card I : ℝ) * ρ + 2 * A.card := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (a i * roundSign (x i) - a i * x i)| ≤
        ∑ i, |a i * roundSign (x i) - a i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : I, (ρ + if i ∈ A then 2 else 0) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul]
      have hm := mul_le_mul_of_nonneg_right (ha i) (abs_nonneg (roundSign (x i) - x i))
      simp only [one_mul] at hm
      by_cases hi : i ∈ A
      · simp only [hi, if_true]
        have he := roundSign_error_le_two (x i) (hx i)
        linarith
      · simp only [hi, if_false, add_zero]
        exact hm.trans (roundSign_frozen_error (x i) ρ (hx i) (hf i hi))
    _ = _ := by
      simp [Finset.sum_add_distrib, Finset.sum_ite_mem, mul_comm]

end Komlos.KMFresh

-- END KMProof/Rounding.lean

-- BEGIN KMProof/ScaleReconstruction.lean

namespace Komlos.KMFresh

lemma scale_row_reconstruct {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (q : ℕ) (x : Fin n → ℝ) (r : R) (ha : ∀i, |A r i| ≤ 1) :
    (∑p : Fin (q+1),scaleCut p.val*rowDiscrepancy (scaleRows A q) x (p,r)) =
      rowDiscrepancy A x r := by
  simp only [rowDiscrepancy,scaleRows,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [←mul_assoc,←Finset.sum_mul]
  rw [scaleFamily_reconstruct q (A r i) (ha i)]

lemma scale_row_bound {R : Type*} {n : ℕ} (A : R → Fin n → ℝ)
    (q : ℕ) (x : Fin n → ℝ) (r : R) (ha : ∀i, |A r i| ≤ 1)
    (b : Fin (q+1) → ℝ) (C : ℝ)
    (h : ∀p,rowDiscrepancy (scaleRows A q) x (p,r) ≤ C*b p) :
    rowDiscrepancy A x r ≤ C*(∑p,scaleCut p.val*b p) := by
  rw [←scale_row_reconstruct A q x r ha,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  have hh := mul_le_mul_of_nonneg_left (h p) (show 0 ≤ scaleCut p.val by unfold scaleCut; positivity)
  nlinarith

lemma concrete_scale_sum_ge_count (n : ℕ) (hell : 1 ≤ nativeEll n) :
    (scaleCount (nativeEll n):ℝ) ≤
      ∑p : Fin (concreteDepth n+1),scaleCut p.val*concreteB n p := by
  change (scaleCount (nativeEll n):ℝ) ≤ ∑p : Fin (scaleCount (nativeEll n)),
    scaleCut p.val*scaleTarget ((4:ℝ)^p.val) (nativeEll n) (scaleCount (nativeEll n))
  rw [sum_scaled_targets]
  have hs : 1 ≤ Real.sqrt (nativeEll n) := by simpa using Real.sqrt_le_sqrt hell
  have hss : 1 ≤ Real.sqrt (Real.sqrt (nativeEll n)) := by simpa using Real.sqrt_le_sqrt hs
  have hP : (1:ℝ) ≤ scaleCount (nativeEll n) := by exact_mod_cast scaleCount_pos (nativeEll n)
  have hp3 : (scaleCount (nativeEll n):ℝ) ≤ (scaleCount (nativeEll n):ℝ)^3 := by
    exact_mod_cast Nat.le_self_pow (by decide : (3:ℕ) ≠ 0) (scaleCount (nativeEll n))
  have hm := mul_le_mul_of_nonneg_right hss (show (0:ℝ) ≤ (scaleCount (nativeEll n):ℝ)^3 by positivity)
  nlinarith

lemma round_concrete_rows {R : Type*} {n : ℕ} (A : R → Fin n → ℝ) (x : Fin n → ℝ)
    (ha : ∀r i, |A r i| ≤ 1) (hx : ∀i, |x i| ≤ 1)
    (hell : 1 ≤ nativeEll n)
    (halive : (aliveSet (1/((n:ℝ)+1)) x).card ≤ 16*(concreteDepth n+1))
    (hrows : ∀z : Fin (concreteDepth n+1) × R,
      rowDiscrepancy (scaleRows A (concreteDepth n)) x z ≤ 3200*concreteB n z.1) :
    ∀r, rowDiscrepancy A (fun i => roundSign (x i)) r ≤
      3233*(∑p : Fin (concreteDepth n+1),scaleCut p.val*concreteB n p) := by
  intro r
  let S := ∑p : Fin (concreteDepth n+1),scaleCut p.val*concreteB n p
  have hs := concrete_scale_sum_ge_count n hell
  have hP : (1:ℝ) ≤ scaleCount (nativeEll n) := by exact_mod_cast scaleCount_pos (nativeEll n)
  have hr := scale_row_bound A (concreteDepth n) x r (ha r) (concreteB n) 3200 (fun p => hrows (p,r))
  have he := weighted_rounding_error (aliveSet (1/((n:ℝ)+1)) x) (A r) x (1/((n:ℝ)+1))
    (by positivity) (ha r) hx (fun i hi => le_of_not_gt (fun hh => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hh⟩)))
  simp only [Fintype.card_fin] at he
  have hn : (n:ℝ)*(1/((n:ℝ)+1)) ≤ 1 := by
    rw [mul_one_div]
    apply (div_le_one (by positivity : (0:ℝ) < (n:ℝ)+1)).mpr
    linarith
  have hc : ((aliveSet (1/((n:ℝ)+1)) x).card:ℝ) ≤ 16*(scaleCount (nativeEll n):ℝ) := by
    exact_mod_cast halive
  have hd := le_abs_self ((∑i,A r i*roundSign (x i))-∑i,A r i*x i)
  change rowDiscrepancy A (fun i => roundSign (x i)) r ≤ _
  change rowDiscrepancy A (fun i => roundSign (x i)) r-rowDiscrepancy A x r ≤
    |rowDiscrepancy A (fun i => roundSign (x i)) r-rowDiscrepancy A x r| at hd
  change |rowDiscrepancy A (fun i => roundSign (x i)) r-rowDiscrepancy A x r| ≤ _ at he
  linarith

end Komlos.KMFresh

-- END KMProof/ScaleReconstruction.lean

-- BEGIN KMProof/SignedRows.lean

namespace Komlos.KMFresh

def signedRows {R C : Type*} (A : R → C → ℝ) : Sum R R → C → ℝ :=
  Sum.elim A (fun i j => -A i j)

lemma signedRows_energy {R C : Type*} [Fintype R] (A : R → C → ℝ) (j : C) :
    ∑ i : Sum R R, signedRows A i j ^ 2 = 2 * ∑ i : R, A i j ^ 2 := by
  simp only [Fintype.sum_sum_type, signedRows, Sum.elim_inl, Sum.elim_inr, neg_sq]
  ring

lemma signedRows_column_bound {R C : Type*} [Fintype R] (A : R → C → ℝ)
    (h : ∀ j, ∑ i, A i j ^ 2 ≤ 1) (j : C) :
    ∑ i : Sum R R, signedRows A i j ^ 2 ≤ 2 := by
  rw [signedRows_energy]
  linarith [h j]

lemma signedRows_one_sided {R C : Type*} [Fintype C] (A : R → C → ℝ)
    (x : C → ℝ) (B : ℝ) (h : ∀ i, ∑ j, signedRows A i j * x j ≤ B) :
    ∀ i, |∑ j, A i j * x j| ≤ B := by
  intro i
  have hp := h (Sum.inl i)
  have hn := h (Sum.inr i)
  simp only [signedRows, Sum.elim_inl] at hp
  simp only [signedRows, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at hn
  exact abs_le.mpr ⟨by linarith, hp⟩

end Komlos.KMFresh

-- END KMProof/SignedRows.lean

-- BEGIN KMProof/FiniteMatrixBound.lean

noncomputable section
open Filter
namespace Komlos.KMFresh

lemma finite_matrix_bound {R : Type*} [Fintype R] (n : ℕ) (hg : ConcreteGuards n)
    (A : R → Fin n → ℝ) (ha : ∀r i,|A r i| ≤ 1)
    (hA : ∀i,∑r,(A r i)^2 ≤ 1) (hR : Fintype.card R ≤ n^3) :
    ∃e : Fin n → ℝ, Komlos.IsSignVector e ∧
      ∀r, |∑i,e i*A r i| ≤
        3233*(∑p : Fin (concreteDepth n+1),scaleCut p.val*concreteB n p) := by
  classical
  let B := signedRows A
  have hB : ∀r i,|B r i| ≤ 1 := by
    intro r i
    cases r with
    | inl r => exact ha r i
    | inr r => simpa only [B,signedRows,Sum.elim_inr,abs_neg] using ha r i
  have hcol := signedRows_column_bound A hA
  have hcard : Fintype.card (Sum R R) ≤ 2*n^3 := by
    rw [Fintype.card_sum]
    omega
  let ρ : ℝ := 1/((n:ℝ)+1)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨ε,ω,he,he1,her,hraw,hcolumns,htiny,hbox,halive⟩ :=
    concrete_good_trajectory n B hB hcol hcard ρ hρ hg.ell hg.fourth hg.drift hg.count hg.threshold
  let N := walkHorizon n ε
  let s := scaleHistory B (concreteDepth n) ρ (concreteMu n) (concreteBeta n) (concreteB n)
    hB hcol (concreteMu_pos n) (Real.sqrt ε) N ω
  have htone : Real.sqrt ε ≤ 1 := by simpa using Real.sqrt_le_sqrt he1
  have hpref : historyPrefix ω N le_rfl = ω := by funext i; rfl
  have htiny' : ∀p r,concreteTinyEligible n p →
      rowTiny (scaleRows B (concreteDepth n)) ρ (fun z => concreteMu n z.1) s.x (p,r) →
      rowRegularizer (scaleRows B (concreteDepth n)) ρ (fun z => concreteTinyBeta n z.1) s.x (p,r) <
        3171*concreteB n p+1 := by
    intro p r hp hh
    have h := htiny p r hp N le_rfl
    simpa only [hpref] using h hh
  have hrows z := concrete_history_row_bound B ρ hB hcol hg.ell.le hg.fourth
    (Real.sqrt ε) (Real.sqrt_nonneg ε) htone her hraw N ω htiny' z
  have hsize : (aliveSet (1/((n:ℝ)+1)) s.x).card ≤ 16*(concreteDepth n+1) := by
    have hc : (aliveSet ρ s.x).card ≤ 16*(concreteDepth n+1) := by
      exact_mod_cast halive
    exact hc
  have hround := round_concrete_rows B s.x hB hbox hg.ell.le hsize hrows
  have habs := signedRows_one_sided A (fun i => roundSign (s.x i))
    (3233*(∑p : Fin (concreteDepth n+1),scaleCut p.val*concreteB n p)) hround
  refine ⟨(fun i => roundSign (s.x i)),rounded_isSignVector s.x,?_⟩
  intro r
  simpa only [mul_comm] using habs r

lemma eventually_finite_matrix_bound :
    ∀ᶠ n : ℕ in atTop, ∀ (R : Type*) [Fintype R] (A : R → Fin n → ℝ),
      (∀r i,|A r i| ≤ 1) → (∀i,∑r,(A r i)^2 ≤ 1) → Fintype.card R ≤ n^3 →
      ∃e : Fin n → ℝ, Komlos.IsSignVector e ∧
        ∀r, |∑i,e i*A r i| ≤
          3233*(∑p : Fin (concreteDepth n+1),scaleCut p.val*concreteB n p) := by
  filter_upwards [eventually_concrete_guards] with n hn
  intro R _ A ha hA hR
  exact finite_matrix_bound n hn A ha hA hR

end Komlos.KMFresh

-- END KMProof/FiniteMatrixBound.lean

-- BEGIN KMProof/NativeColumns.lean

namespace Komlos.KMFresh

lemma native_column_energy {n m : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin m))
    (hv : ∀ i, ‖v i‖ ≤ 1) (i : Fin n) : ∑ j, v i j ^ 2 ≤ 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq]
  nlinarith [hv i, norm_nonneg (v i)]

lemma native_entry_bound {n m : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin m))
    (hv : ∀ i, ‖v i‖ ≤ 1) (i : Fin n) (j : Fin m) : |v i j| ≤ 1 := by
  have hs : v i j ^ 2 ≤ ∑ k, v i k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (v i k)) (Finset.mem_univ j)
  have he := native_column_energy v hv i
  have ha := abs_nonneg (v i j)
  have hab := sq_abs (v i j)
  nlinarith

lemma native_trivial_sign_bound {n m : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin m))
    (hv : ∀ i, ‖v i‖ ≤ 1) :
    ∃ ε : Fin n → ℝ, Komlos.IsSignVector ε ∧
      ∀ j, |∑ i, ε i * v i j| ≤ (n : ℝ) := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro i
    exact Or.inl rfl
  · intro j
    calc
      |∑ i : Fin n, 1 * v i j| ≤ ∑ i : Fin n, |1 * v i j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simpa using native_entry_bound v hv i j
      _ = n := by simp

end Komlos.KMFresh

-- END KMProof/NativeColumns.lean

-- BEGIN KMProof/InputTruncation.lean

namespace Komlos.KMFresh

noncomputable def truncateEntry (δ a : ℝ) : ℝ := if δ < |a| then a else 0

lemma truncateEntry_abs_le (δ a : ℝ) : |truncateEntry δ a| ≤ |a| := by
  unfold truncateEntry
  split_ifs
  · exact le_rfl
  · simp

lemma truncateEntry_error (δ a : ℝ) (hδ : 0 ≤ δ) : |a - truncateEntry δ a| ≤ δ := by
  unfold truncateEntry
  split_ifs with h
  · simpa using hδ
  · simpa using le_of_not_gt h

lemma truncateEntry_nonzero (δ a : ℝ) (h : truncateEntry δ a ≠ 0) :
    δ < |truncateEntry δ a| := by
  unfold truncateEntry at h ⊢
  split_ifs with ha
  · exact ha
  · simp only [if_neg ha] at h
    exact False.elim (h rfl)

lemma truncateEntry_sq_le (δ a : ℝ) : (truncateEntry δ a) ^ 2 ≤ a ^ 2 := by
  have h := truncateEntry_abs_le δ a
  have h0 := abs_nonneg (truncateEntry δ a)
  have h1 := abs_nonneg a
  have he0 := sq_abs (truncateEntry δ a)
  have he1 := sq_abs a
  nlinarith

lemma truncation_sign_error {I : Type*} [Fintype I] (a ε : I → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hε : ∀ i, |ε i| ≤ 1) :
    |(∑ i, ε i * a i) - ∑ i, ε i * truncateEntry δ (a i)| ≤
      (Fintype.card I : ℝ) * δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (ε i * a i - ε i * truncateEntry δ (a i))| ≤
        ∑ i, |ε i * a i - ε i * truncateEntry δ (a i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : I, δ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul]
      calc
        |ε i| * |a i - truncateEntry δ (a i)| ≤
            1 * |a i - truncateEntry δ (a i)| :=
          mul_le_mul_of_nonneg_right (hε i) (abs_nonneg _)
        _ ≤ δ := by simpa using truncateEntry_error δ (a i) hδ
    _ = _ := by simp

lemma truncation_column_energy {R C : Type*} [Fintype R]
    (A : R → C → ℝ) (δ : ℝ) (j : C) :
    ∑ i, (truncateEntry δ (A i j)) ^ 2 ≤ ∑ i, A i j ^ 2 := by
  exact Finset.sum_le_sum (fun i _ => truncateEntry_sq_le δ (A i j))

end Komlos.KMFresh

-- END KMProof/InputTruncation.lean

-- BEGIN KMProof/SparseReduction.lean

namespace Komlos.KMFresh

noncomputable def retainedRows {R C : Type*} [Fintype R] [Fintype C]
    (A : R → C → ℝ) (δ : ℝ) : Finset R := by
  classical
  exact Finset.univ.filter (fun i => ∃ j, truncateEntry δ (A i j) ≠ 0)

lemma retained_row_energy {R C : Type*} [Fintype R] [Fintype C]
    (A : R → C → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (i : R)
    (hi : i ∈ retainedRows A δ) :
    δ ^ 2 ≤ ∑ j, (truncateEntry δ (A i j)) ^ 2 := by
  classical
  obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2
  have ht := truncateEntry_nonzero δ (A i j) hj
  have he := sq_abs (truncateEntry δ (A i j))
  have hs : δ ^ 2 ≤ (truncateEntry δ (A i j)) ^ 2 := by nlinarith
  exact hs.trans (Finset.single_le_sum (fun k _ => sq_nonneg (truncateEntry δ (A i k))) (Finset.mem_univ j))

lemma retained_row_count {R C : Type*} [Fintype R] [Fintype C]
    (A : R → C → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hcol : ∀ j, ∑ i, A i j ^ 2 ≤ 1) :
    ((retainedRows A δ).card : ℝ) * δ ^ 2 ≤ (Fintype.card C : ℝ) := by
  classical
  calc
    ((retainedRows A δ).card : ℝ) * δ ^ 2 =
        ∑ _i ∈ retainedRows A δ, δ ^ 2 := by simp
    _ ≤ ∑ i ∈ retainedRows A δ, ∑ j, (truncateEntry δ (A i j)) ^ 2 :=
      Finset.sum_le_sum (fun i hi => retained_row_energy A δ hδ i hi)
    _ ≤ ∑ i : R, ∑ j : C, (truncateEntry δ (A i j)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
    _ = ∑ j : C, ∑ i : R, (truncateEntry δ (A i j)) ^ 2 := Finset.sum_comm
    _ ≤ ∑ _j : C, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact (truncation_column_energy A δ j).trans (hcol j)
    _ = _ := by simp

lemma omitted_row_zero {R C : Type*} [Fintype R] [Fintype C]
    (A : R → C → ℝ) (δ : ℝ) (i : R)
    (hi : i ∉ retainedRows A δ) (j : C) : truncateEntry δ (A i j) = 0 := by
  classical
  by_contra h
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, j, h⟩)

end Komlos.KMFresh

-- END KMProof/SparseReduction.lean

-- BEGIN KMProof/NativeReduction.lean

namespace Komlos.KMFresh

lemma native_retained_rows_bound {n m : ℕ} (hn : 0 < n)
    (v : Fin n → EuclideanSpace ℝ (Fin m)) (hv : ∀ i, ‖v i‖ ≤ 1) :
    (retainedRows (fun j i => v i j) (1 / (n : ℝ))).card ≤ n ^ 3 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he := retained_row_count (fun j i => v i j) (1 / (n : ℝ))
    (by positivity) (native_column_energy v hv)
  simp only [Fintype.card_fin] at he
  have hid : (1 / (n : ℝ)) ^ 2 * (n : ℝ) ^ 2 = 1 := by field_simp [ne_of_gt hnR]
  have hb : ((retainedRows (fun j i => v i j) (1 / (n : ℝ))).card : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc
      _ = (((retainedRows (fun j i => v i j) (1 / (n : ℝ))).card : ℝ) *
          (1 / (n : ℝ)) ^ 2) * (n : ℝ) ^ 2 := by rw [mul_assoc, hid, mul_one]
      _ ≤ (n : ℝ) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right he (sq_nonneg _)
      _ = _ := by ring
  exact_mod_cast hb

lemma native_truncation_error {n m : ℕ} (hn : 0 < n)
    (v : Fin n → EuclideanSpace ℝ (Fin m)) (ε : Fin n → ℝ)
    (hε : Komlos.IsSignVector ε) (j : Fin m) :
    |(∑ i, ε i * v i j) - ∑ i, ε i * truncateEntry (1 / (n : ℝ)) (v i j)| ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsign : ∀ i, |ε i| ≤ 1 := by
    intro i
    rcases hε i with h | h <;> rw [h] <;> norm_num
  have he := truncation_sign_error (fun i => v i j) ε (1 / (n : ℝ)) (by positivity) hsign
  simpa [Fintype.card_fin, ne_of_gt hnR] using he

end Komlos.KMFresh

-- END KMProof/NativeReduction.lean

-- BEGIN KMProof/ReductionTransfer.lean

namespace Komlos.KMFresh

lemma native_reduction_transfer {n m : ℕ} (hn : 0 < n)
    (v : Fin n → EuclideanSpace ℝ (Fin m)) (ε : Fin n → ℝ)
    (hε : Komlos.IsSignVector ε) (B : ℝ) (hB : 0 ≤ B)
    (hrows : ∀ r ∈ retainedRows (fun j i => v i j) (1 / (n : ℝ)),
      |∑ i, ε i * truncateEntry (1 / (n : ℝ)) (v i r)| ≤ B) :
    ∀ r, |∑ i, ε i * v i r| ≤ B + 1 := by
  classical
  intro r
  have ht : |∑ i, ε i * truncateEntry (1 / (n : ℝ)) (v i r)| ≤ B := by
    by_cases hr : r ∈ retainedRows (fun j i => v i j) (1 / (n : ℝ))
    · exact hrows r hr
    · have hz : ∀ i, truncateEntry (1 / (n : ℝ)) (v i r) = 0 :=
        omitted_row_zero (fun j i => v i j) (1 / (n : ℝ)) r hr
      simpa only [hz, mul_zero, Finset.sum_const_zero, abs_zero] using hB
  have he := native_truncation_error hn v ε hε r
  calc
    |∑ i, ε i * v i r| =
        |((∑ i, ε i * v i r) - ∑ i, ε i * truncateEntry (1 / (n : ℝ)) (v i r)) +
          ∑ i, ε i * truncateEntry (1 / (n : ℝ)) (v i r)| := by rw [sub_add_cancel]
    _ ≤ |(∑ i, ε i * v i r) - ∑ i, ε i * truncateEntry (1 / (n : ℝ)) (v i r)| +
          |∑ i, ε i * truncateEntry (1 / (n : ℝ)) (v i r)| := abs_add_le _ _
    _ ≤ B + 1 := by linarith

end Komlos.KMFresh

-- END KMProof/ReductionTransfer.lean

-- BEGIN KMProof/FiniteInitialRange.lean

namespace Komlos.KMFresh

lemma extend_native_sign_bound (B : ℕ → ℝ) (hB : ∀ n, 0 < B n) (K : ℝ) (N : ℕ)
    (hlarge : ∀ n ≥ N, ∀ m (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀ i, ‖v i‖ ≤ 1) → ∃ ε : Fin n → ℝ, Komlos.IsSignVector ε ∧
        ∀ j, |∑ i, ε i * v i j| ≤ K * B n) :
    ∃ C : ℝ, 0 < C ∧ ∀ n m (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀ i, ‖v i‖ ≤ 1) → ∃ ε : Fin n → ℝ, Komlos.IsSignVector ε ∧
        ∀ j, |∑ i, ε i * v i j| ≤ C * B n := by
  let S : ℝ := ∑ n ∈ Finset.range N, (n : ℝ) / B n
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n _ => div_nonneg (Nat.cast_nonneg n) (hB n).le)
  let C : ℝ := |K| + 1 + S
  have hC : 0 < C := by dsimp [C]; have := abs_nonneg K; linarith
  have hKC : K ≤ C := by dsimp [C]; have := le_abs_self K; linarith
  refine ⟨C, hC, ?_⟩
  intro n m v hv
  by_cases hn : N ≤ n
  · obtain ⟨ε, hs, he⟩ := hlarge n hn m v hv
    refine ⟨ε, hs, fun j => (he j).trans ?_⟩
    exact mul_le_mul_of_nonneg_right hKC (hB n).le
  · obtain ⟨ε, hs, he⟩ := native_trivial_sign_bound v hv
    have hm : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
    have hterm : (n : ℝ) / B n ≤ S :=
      Finset.single_le_sum (fun k _ => div_nonneg (Nat.cast_nonneg k) (hB k).le) hm
    have hSC : S ≤ C := by dsimp [C]; have := abs_nonneg K; linarith
    have hnb : (n : ℝ) ≤ C * B n := (div_le_iff₀ (hB n)).mp (hterm.trans hSC)
    exact ⟨ε, hs, fun j => (he j).trans hnb⟩

end Komlos.KMFresh

-- END KMProof/FiniteInitialRange.lean

-- BEGIN KMProof/NativeBounds.lean

noncomputable section
open Filter
namespace Komlos.KMFresh

lemma eventually_native_bound :
    ∀ᶠ n:ℕ in atTop, ∀m (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀i,‖v i‖ ≤ 1) → ∃e : Fin n → ℝ,Komlos.IsSignVector e ∧
      ∀j,|∑i,e i*v i j| ≤ (3234*(5/Real.log 2+2)^3)*nativeShape n := by
  classical
  filter_upwards [eventually_finite_matrix_bound,eventually_native_scale_sum_bound,
    nativeEll_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0:ℕ)] with n hf hs hell hn
  intro m v hv
  let S := retainedRows (fun j i => v i j) (1/(n:ℝ))
  let A : S → Fin n → ℝ := fun r i => truncateEntry (1/(n:ℝ)) (v i r)
  have ha r i : |A r i| ≤ 1 := (truncateEntry_abs_le _ _).trans (native_entry_bound v hv i r)
  have hcol i : (∑r,A r i^2) ≤ 1 := by
    have hsub : (∑r:S,A r i^2) = ∑r∈S,(truncateEntry (1/(n:ℝ)) (v i r))^2 := by
      exact Finset.sum_coe_sort S (fun r => (truncateEntry (1/(n:ℝ)) (v i r))^2)
    rw [hsub]
    have hh : (∑r∈S,(truncateEntry (1/(n:ℝ)) (v i r))^2) ≤
        ∑r:Fin m,(truncateEntry (1/(n:ℝ)) (v i r))^2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun r => sq_nonneg _)
    exact hh.trans ((truncation_column_energy (fun j i => v i j) (1/(n:ℝ)) i).trans
      (native_column_energy v hv i))
  have hcard : Fintype.card S ≤ n^3 := by
    simpa only [Fintype.card_coe] using native_retained_rows_bound hn v hv
  obtain ⟨e,he,hrows⟩ := hf S A ha hcol hcard
  let B := ∑p : Fin (concreteDepth n+1),scaleCut p.val*concreteB n p
  have hB : 1 ≤ B := by
    have hh := concrete_scale_sum_ge_count n hell
    have hp : (1:ℝ) ≤ scaleCount (nativeEll n) := by exact_mod_cast scaleCount_pos (nativeEll n)
    exact hp.trans hh
  have htransfer := native_reduction_transfer hn v e he (3233*B) (by positivity)
    (fun r hr => hrows ⟨r,hr⟩)
  have hsum : B ≤ (5/Real.log 2+2)^3*nativeShape n := hs
  refine ⟨e,he,fun j => (htransfer j).trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 3234)
  nlinarith

lemma native_uniform_bound : ∃C:ℝ,0<C ∧ ∀n m (v : Fin n → EuclideanSpace ℝ (Fin m)),
    (∀i,‖v i‖ ≤ 1) → ∃e : Fin n → ℝ,Komlos.IsSignVector e ∧
      ∀j,|∑i,e i*v i j| ≤ C*nativeShape n := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp eventually_native_bound
  exact extend_native_sign_bound nativeShape nativeShape_pos (3234*(5/Real.log 2+2)^3) N hN

end Komlos.KMFresh

-- END KMProof/NativeBounds.lean

-- BEGIN KMProof/NativeConclusion.lean

namespace Komlos

theorem KMFresh.native_bansal_jiang_komlos_bound :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)), (∀ i, ‖v i‖ ≤ 1) →
        ∃ ε : Fin n → ℝ, IsSignVector ε ∧
          ∀ j, |∑ i, ε i * v i j| ≤
            C * Real.log (n + 2) ^ ((1 : ℝ) / 4) *
              Real.log (Real.log (n + 8)) ^ γ := by
  obtain ⟨C,hC,hbound⟩ := KMFresh.native_uniform_bound
  refine ⟨C,3,hC,by norm_num,?_⟩
  intro n m v hv
  obtain ⟨e,he,hrows⟩ := hbound n m v hv
  refine ⟨e,he,fun j => ?_⟩
  have hr : Real.log (Real.log ((n:ℝ)+8)) ^ (3:ℝ) = Real.log (Real.log ((n:ℝ)+8)) ^ (3:ℕ) := Real.rpow_natCast _ _
  rw [hr]
  simpa only [KMFresh.nativeShape,KMFresh.nativeEll,KMFresh.nativeLogLog,
    mul_assoc] using hrows j

end Komlos

-- END KMProof/NativeConclusion.lean

-- BEGIN Canonical.lean

namespace Komlos

theorem bansal_jiang_komlos_bound :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)), (∀ i, ‖v i‖ ≤ 1) →
        ∃ ε : Fin n → ℝ, IsSignVector ε ∧
          ∀ j, |∑ i, ε i * v i j| ≤
            C * Real.log (n + 2) ^ ((1 : ℝ) / 4) *
              Real.log (Real.log (n + 8)) ^ γ := by
  exact KMFresh.native_bansal_jiang_komlos_bound

end Komlos

-- END Canonical.lean

open Komlos

theorem solution :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)), (∀ i, ‖v i‖ ≤ 1) →
        ∃ ε : Fin n → ℝ, IsSignVector ε ∧
          ∀ j, |∑ i, ε i * v i j| ≤
            C * Real.log (n + 2) ^ ((1 : ℝ) / 4) *
              Real.log (Real.log (n + 8)) ^ γ := by
  exact Komlos.bansal_jiang_komlos_bound
