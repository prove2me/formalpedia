-- Prove2me | solution 1 for JMMS.isRecurrentAction_and_isExtensivelyAmenable_IETOf
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T12:48:30.730341+00:00
-- url     : https://prove2.me/submissions/a5baaaa5-0371-4b12-a02a-81a0601a62de

import Mathlib
import Definitions.Def_IntervalExchange
import Theorems.Thm_JMMS_isExtensivelyAmenable_of_isRecurrentAction
import Theorems.Thm_MarkovMixing_polya_recurrence
import Theorems.Thm_LyonsPeres_isTransientNetwork_iff_and_isTransientNetwork_of_isRoughEmbedding

section

open IntervalExchange

namespace JMMS.IETP52

open Classical

/-! ## Part 1: generic Markov-chain bookkeeping -/

section Markov

variable {V : Type*} (P : V → V → ℝ) (x : V)

/-- The (sub-probability) of being at `y` at time `t` without having visited `x` at times
`1, …, t`, the chain being at `x` at time `0`. -/
noncomputable def av : ℕ → V → ℝ
  | 0, y => if y = x then 1 else 0
  | t + 1, y => if y = x then 0 else ∑' z, av t z * P z y

variable {P}

lemma hasSum_of_fiber {α β : Type*} (K : α × β → ℝ) (hK : 0 ≤ K) (s : α → ℝ)
    (hs : ∀ a, HasSum (fun b => K (a, b)) (s a)) (hsum : Summable s) (g : β → ℝ)
    (hg : ∀ b, HasSum (fun a => K (a, b)) (g b)) : HasSum g (∑' a, s a) := by
  have hKs : Summable K := by
    rw [summable_prod_of_nonneg hK]
    refine ⟨fun a => (hs a).summable, ?_⟩
    simpa [(hs _).tsum_eq] using hsum
  have h1 : HasSum K (∑' a, s a) := by
    have := hKs.hasSum
    rwa [hKs.tsum_prod' (fun a => (hs a).summable), tsum_congr fun a => (hs a).tsum_eq] at this
  have h2 : HasSum (K ∘ (Equiv.prodComm β α)) (∑' a, s a) :=
    (Equiv.hasSum_iff (Equiv.prodComm β α)).mpr h1
  exact h2.prod_fiberwise fun b => hg b

variable (hP0 : ∀ a b, 0 ≤ P a b) (hP1 : ∀ a, HasSum (P a) 1)
include hP0

lemma av_nonneg : ∀ t y, 0 ≤ av P x t y
  | 0, y => by simp only [av]; split_ifs <;> norm_num
  | t + 1, y => by
    simp only [av]
    split_ifs
    · exact le_rfl
    · exact tsum_nonneg fun z => mul_nonneg (av_nonneg t z) (hP0 z y)

include hP1

lemma P_le_one (a b : V) : P a b ≤ 1 :=
  le_hasSum (hP1 a) b fun c _ => hP0 a c

lemma summable_F (t : ℕ) (ih : Summable (av P x t)) :
    Summable (fun p : V × V => av P x t p.1 * P p.1 p.2) := by
  have hK : 0 ≤ (fun p : V × V => av P x t p.1 * P p.1 p.2) := by
    intro p
    exact mul_nonneg (av_nonneg x hP0 t p.1) (hP0 _ _)
  refine (summable_prod_of_nonneg hK).mpr ⟨fun a => ?_, ?_⟩
  · exact (hP1 a).summable.mul_left (av P x t a)
  refine ih.congr fun a => ?_
  show av P x t a = ∑' y, av P x t a * P a y
  rw [tsum_mul_left, (hP1 a).tsum_eq, mul_one]

/-- Summability of `av t` and the identity `∑ (av (t+1)) + f_t = ∑ (av t)`. -/
lemma av_summable : ∀ t, Summable (av P x t)
  | 0 => by
    refine summable_of_ne_finset_zero (s := {x}) fun y hy => ?_
    simp only [Finset.mem_singleton] at hy
    simp [av, hy]
  | t + 1 => by
    have ih := av_summable t
    have hF := summable_F x hP0 hP1 t ih
    have hG : Summable (fun y => ∑' z, av P x t z * P z y) := hF.prod_symm.prod
    refine Summable.of_nonneg_of_le (fun y => av_nonneg x hP0 (t + 1) y) (fun y => ?_) hG
    simp only [av]
    split_ifs
    · exact tsum_nonneg fun z => mul_nonneg (av_nonneg x hP0 t z) (hP0 z y)
    · exact le_rfl

lemma av_step (t : ℕ) :
    ∑' y, av P x (t + 1) y + ∑' z, av P x t z * P z x = ∑' y, av P x t y := by
  have ih := av_summable x hP0 hP1 t
  have hF := summable_F x hP0 hP1 t ih
  have hG : Summable (fun y => ∑' z, av P x t z * P z y) := hF.prod_symm.prod
  have e1 := hG.tsum_eq_add_tsum_ite x
  have e2 : ∑' y, av P x (t + 1) y = ∑' y, if y = x then 0 else ∑' z, av P x t z * P z y :=
    tsum_congr fun y => rfl
  rw [e2, add_comm, ← e1]
  rw [Summable.tsum_comm' (f := fun z y => av P x t z * P z y) hF
    (fun z => (hP1 z).summable.mul_left (av P x t z))
    (fun y => (hF.prod_symm.prod_factor y))]
  exact tsum_congr fun z => by rw [tsum_mul_left, (hP1 z).tsum_eq, mul_one]

omit hP0 hP1 in
lemma avoidProb_eq_av : ∀ k y, avoidProb P x (k + 1) y = av P x (k + 1) y
  | 0, y => by
    simp only [avoidProb, av]
    split_ifs with h
    · rfl
    · rw [tsum_eq_single x]
      · simp
      · intro z hz; simp [hz]
  | k + 1, y => by
    simp only [avoidProb]
    rw [show av P x (k + 2) y = if y = x then 0 else ∑' z, av P x (k + 1) z * P z y from rfl]
    split_ifs
    · rfl
    · exact tsum_congr fun z => by rw [avoidProb_eq_av k z]

omit hP0 hP1 in
lemma firstReturnProb_eq (t : ℕ) : firstReturnProb P x t = ∑' z, av P x t z * P z x := by
  cases t with
  | zero =>
    simp only [firstReturnProb, av]
    rw [tsum_eq_single x]
    · simp
    · intro z hz; simp [hz]
  | succ k =>
    simp only [firstReturnProb]
    exact tsum_congr fun z => by rw [avoidProb_eq_av x k z]

lemma partial_sum (t : ℕ) :
    ∑ n ∈ Finset.range t, firstReturnProb P x n = 1 - ∑' y, av P x t y := by
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, av]
    rw [tsum_eq_single x]
    · simp
    · intro z hz; simp [hz]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, firstReturnProb_eq x, ← av_step x hP0 hP1 t]
    ring

/-- The path-sum description of `av`. -/
lemma path_hasSum : ∀ (t : ℕ) (y : V),
    HasSum (fun ω : Fin (t + 1) → V =>
      if (ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ ({x} : Set V)) ∧ ω (Fin.last t) = y
      then MarkovMixing.pathWeightC P ω else 0) (av P x t y)
  | 0, y => by
    by_cases hy : y = x
    · subst hy
      have : (fun ω : Fin 1 → V =>
          if (ω 0 = y ∧ ∀ i : Fin 1, i ≠ 0 → ω i ∉ ({y} : Set V)) ∧ ω (Fin.last 0) = y
          then MarkovMixing.pathWeightC P ω else 0) = fun ω => if ω = fun _ => y then 1 else 0 := by
        funext ω
        have hw : MarkovMixing.pathWeightC P ω = 1 := by simp [MarkovMixing.pathWeightC]
        have e : (ω = fun _ => y) ↔ ω 0 = y := by
          constructor
          · intro h; rw [h]
          · intro h; funext i; rw [Subsingleton.elim i 0, h]
        rw [hw]
        have : Fin.last 0 = 0 := rfl
        simp only [this]
        by_cases h : ω 0 = y
        · have h' : ω = fun _ => y := e.mpr h
          rw [if_pos h', if_pos]
          refine ⟨⟨h, fun i hi => absurd (Subsingleton.elim i 0) hi⟩, h⟩
        · have h' : ¬ ω = fun _ => y := fun h' => h (e.mp h')
          rw [if_neg h', if_neg]
          exact fun hh => h hh.2
      rw [this]
      have : av P y 0 y = 1 := by simp [av]
      rw [this]
      exact hasSum_ite_eq _ _
    · have : av P x 0 y = 0 := by simp [av, hy]
      rw [this]
      convert hasSum_zero with ω
      split_ifs with h
      · exact absurd (h.2.symm.trans (show ω (Fin.last 0) = x from h.1.1)) hy
      · rfl
  | t + 1, y => by
    by_cases hy : y = x
    · subst hy
      have : av P y (t + 1) y = 0 := by simp [av]
      rw [this]
      convert hasSum_zero with ω
      split_ifs with h
      · exact absurd h.2 (h.1.2 _ (Fin.last_pos.ne'))
      · rfl
    have ih := path_hasSum t
    -- the paths of length `t`, weighted by the last step to `y`
    let g : (Fin (t + 1) → V) → ℝ := fun ω' =>
      (if ω' 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω' i ∉ ({x} : Set V)
        then MarkovMixing.pathWeightC P ω' else 0) * P (ω' (Fin.last t)) y
    have hg : HasSum g (∑' z, av P x t z * P z y) := by
      refine hasSum_of_fiber (fun p : V × (Fin (t + 1) → V) =>
          (if (p.2 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → p.2 i ∉ ({x} : Set V)) ∧
            p.2 (Fin.last t) = p.1 then MarkovMixing.pathWeightC P p.2 else 0) * P p.1 y)
        ?_ (fun z => av P x t z * P z y) (fun z => (ih z).mul_right _) ?_ g ?_
      · intro p
        refine mul_nonneg ?_ (hP0 _ _)
        dsimp only
        split_ifs
        · exact Finset.prod_nonneg fun i _ => hP0 _ _
        · exact le_rfl
      · refine Summable.of_nonneg_of_le (fun z => mul_nonneg (av_nonneg x hP0 t z) (hP0 z y))
          (fun z => ?_) (av_summable x hP0 hP1 t)
        exact mul_le_of_le_one_right (av_nonneg x hP0 t z) (P_le_one hP0 hP1 z y)
      · intro ω'
        convert hasSum_ite_eq (ω' (Fin.last t)) (g ω') using 1
        funext z
        dsimp only [g]
        by_cases hz : z = ω' (Fin.last t)
        · subst hz; simp
        · simp [hz, Ne.symm hz]
    have key : ∀ (y' : V) (ω' : Fin (t + 1) → V),
        (if ((Fin.snoc (α := fun _ => V) ω' y') 0 = x ∧ ∀ i : Fin (t + 2), i ≠ 0 →
            (Fin.snoc (α := fun _ => V) ω' y') i ∉ ({x} : Set V)) ∧
            (Fin.snoc (α := fun _ => V) ω' y') (Fin.last (t + 1)) = y
          then MarkovMixing.pathWeightC P (Fin.snoc (α := fun _ => V) ω' y') else 0) =
          if y' = y then g ω' else 0 := by
      intro y' ω'
      have hw : MarkovMixing.pathWeightC P (Fin.snoc (α := fun _ => V) ω' y') =
          MarkovMixing.pathWeightC P ω' * P (ω' (Fin.last t)) y' := by
        simp only [MarkovMixing.pathWeightC]
        rw [Fin.prod_univ_castSucc]
        congr 1
        · refine Finset.prod_congr rfl fun i _ => ?_
          rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        · rw [Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last]
      have h0 : (Fin.snoc (α := fun _ => V) ω' y') 0 = ω' 0 := by
        rw [show (0 : Fin (t + 2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
      have hall : (∀ i : Fin (t + 2), i ≠ 0 → (Fin.snoc (α := fun _ => V) ω' y') i ∉ ({x} : Set V))
          ↔ (∀ i : Fin (t + 1), i ≠ 0 → ω' i ∉ ({x} : Set V)) ∧ y' ≠ x := by
        rw [Fin.forall_fin_succ']
        simp [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hw, h0, Fin.snoc_last]
      by_cases hy' : y' = y
      · subst hy'
        simp only [g, if_true]
        by_cases hc : ω' 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω' i ∉ ({x} : Set V)
        · rw [if_pos ⟨⟨hc.1, hall.mpr ⟨hc.2, hy⟩⟩, by simp⟩, if_pos hc]
        · rw [if_neg, if_neg hc, zero_mul]
          exact fun h => hc ⟨h.1.1, (hall.mp h.1.2).1⟩
      · rw [if_neg hy', if_neg]
        exact fun h => hy' h.2
    let e := Fin.snocEquiv (fun _ : Fin (t + 2) => V)
    rw [← e.hasSum_iff]
    have hinj : Function.Injective (fun ω' : Fin (t + 1) → V => (y, ω')) :=
      fun a b h => (Prod.ext_iff.mp h).2
    rw [← hinj.hasSum_iff]
    · convert hg using 1
      · funext ω'
        exact (key y ω').trans (if_pos rfl)
      · simp [av, hy]
    · rintro ⟨y', ω'⟩ hp
      have hy' : y' ≠ y := fun h => hp ⟨ω', by simp [h]⟩
      exact (key y' ω').trans (if_neg hy')

lemma returnTailC_eq [Countable V] [DecidableEq V] (t : ℕ) :
    MarkovMixing.returnTailC P x t = ∑' y, av P x t y := by
  let g : (Fin (t + 1) → V) → ℝ := fun ω =>
    if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ ({x} : Set V)
    then MarkovMixing.pathWeightC P ω else 0
  have hg : HasSum g (∑' y, av P x t y) := by
    refine hasSum_of_fiber (fun p : V × (Fin (t + 1) → V) =>
        if (p.2 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → p.2 i ∉ ({x} : Set V)) ∧
          p.2 (Fin.last t) = p.1 then MarkovMixing.pathWeightC P p.2 else 0)
      ?_ (av P x t) (fun y => by convert path_hasSum x hP0 hP1 t y) (av_summable x hP0 hP1 t) g ?_
    · intro p
      dsimp only
      split_ifs
      · exact Finset.prod_nonneg fun i _ => hP0 _ _
      · exact le_rfl
    · intro ω
      convert hasSum_ite_eq (ω (Fin.last t)) (g ω) using 1
      funext z
      dsimp only [g]
      by_cases hz : z = ω (Fin.last t)
      · subst hz; simp
      · simp [hz, Ne.symm hz]
  unfold MarkovMixing.returnTailC MarkovMixing.setAvoidTailC
  rw [← hg.tsum_eq]
  exact tsum_congr fun ω => by simp only [g]; congr

lemma isRecurrentChain_of_recurrent [Countable V] [DecidableEq V]
    (h : MarkovMixing.Recurrent P x) : IsRecurrentChain P x := by
  have hf : ∀ n, 0 ≤ firstReturnProb P x n := fun n => by
    rw [firstReturnProb_eq x]
    exact tsum_nonneg fun z => mul_nonneg (av_nonneg x hP0 n z) (hP0 z x)
  unfold IsRecurrentChain
  rw [hasSum_iff_tendsto_nat_of_nonneg hf]
  have h2 : Filter.Tendsto (fun t => 1 - MarkovMixing.returnTailC P x t) Filter.atTop
      (nhds (1 - 0)) := tendsto_const_nhds.sub h
  rw [sub_zero] at h2
  refine h2.congr fun t => ?_
  rw [partial_sum x hP0 hP1, returnTailC_eq x hP0 hP1]

end Markov

section Translate

variable {V : Type*} [AddCommGroup V] {P : V → V → ℝ}

lemma av_translate (hT : ∀ a b v : V, P (a + v) (b + v) = P a b) (x v : V) :
    ∀ t y, av P (x + v) t (y + v) = av P x t y
  | 0, y => by simp [av]
  | t + 1, y => by
    simp only [av, add_left_inj]
    split_ifs
    · rfl
    · rw [← (Equiv.addRight v).tsum_eq]
      exact tsum_congr fun z => by simp [av_translate hT x v t z, hT]

lemma isRecurrentChain_translate (hT : ∀ a b v : V, P (a + v) (b + v) = P a b) (x v : V)
    (h : IsRecurrentChain P x) : IsRecurrentChain P (x + v) := by
  unfold IsRecurrentChain at *
  convert h using 1
  funext t
  rw [firstReturnProb_eq, firstReturnProb_eq, ← (Equiv.addRight v).tsum_eq]
  exact tsum_congr fun z => by simp [av_translate hT x v t z, hT]

end Translate

/-! ## Part 2: simple random walk on `ℤ²` -/

section SRW

abbrev Z2 := Fin 2 → ℤ

def adj (u v : Z2) : Prop :=
  ∃ j : Fin 2, (∀ i : Fin 2, i ≠ j → v i = u i) ∧ (v j = u j + 1 ∨ v j = u j - 1)

lemma srw_eq (u v : Z2) : MarkovMixing.srwZ 2 u v = if adj u v then 1 / 4 else 0 := by
  unfold MarkovMixing.srwZ adj
  split_ifs <;> norm_num

lemma adj_symm {u v : Z2} (h : adj u v) : adj v u := by
  obtain ⟨j, h1, h2⟩ := h
  exact ⟨j, fun i hi => (h1 i hi).symm, by omega⟩

lemma adj_translate (u v w : Z2) : adj (u + w) (v + w) ↔ adj u v := by
  unfold adj
  simp only [Pi.add_apply, add_left_inj]
  constructor
  · rintro ⟨j, h1, h2⟩; exact ⟨j, h1, by omega⟩
  · rintro ⟨j, h1, h2⟩; exact ⟨j, h1, by omega⟩

lemma srw_translate (u v w : Z2) :
    MarkovMixing.srwZ 2 (u + w) (v + w) = MarkovMixing.srwZ 2 u v := by
  rw [srw_eq, srw_eq, adj_translate]

lemma srw_symm (u v : Z2) : MarkovMixing.srwZ 2 u v = MarkovMixing.srwZ 2 v u := by
  rw [srw_eq, srw_eq]
  congr 1
  exact propext ⟨adj_symm, adj_symm⟩

lemma srw_nonneg (u v : Z2) : 0 ≤ MarkovMixing.srwZ 2 u v := by
  rw [srw_eq]; split_ifs <;> norm_num

lemma srw_hasSum_zero : HasSum (MarkovMixing.srwZ 2 0) 1 := by
  have hs : ∀ v ∉ ({![1, 0], ![-1, 0], ![0, 1], ![0, -1]} : Finset Z2),
      MarkovMixing.srwZ 2 0 v = 0 := by
    intro v hv
    rw [srw_eq, if_neg]
    rintro ⟨j, h1, h2⟩
    apply hv
    simp only [Finset.mem_insert, Finset.mem_singleton]
    fin_cases j
    · have := h1 1 (by decide)
      simp only [Pi.zero_apply] at this h2
      simp only [Fin.zero_eta] at h2
      rcases h2 with h2 | h2
      · left; funext i; fin_cases i <;> simp [this, h2]
      · right; left; funext i; fin_cases i <;> simp [this, h2]
    · have := h1 0 (by decide)
      simp only [Pi.zero_apply] at this h2
      simp only [Fin.mk_one] at h2
      rcases h2 with h2 | h2
      · right; right; left; funext i; fin_cases i <;> simp [this, h2]
      · right; right; right; funext i; fin_cases i <;> simp [this, h2]
  convert hasSum_sum_of_ne_finset_zero hs using 1
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [srw_eq]
  rw [if_pos ⟨0, by decide, by decide⟩, if_pos ⟨0, by decide, by decide⟩,
    if_pos ⟨1, by decide, by decide⟩, if_pos ⟨1, by decide, by decide⟩]
  · norm_num
  · infer_instance

lemma srw_hasSum (u : Z2) : HasSum (MarkovMixing.srwZ 2 u) 1 := by
  have : MarkovMixing.srwZ 2 u = (MarkovMixing.srwZ 2 0) ∘ (Equiv.subRight u) := by
    funext v
    simp only [Function.comp_apply, Equiv.subRight_apply]
    rw [← srw_translate 0 (v - u) u]
    simp
  rw [this, Equiv.hasSum_iff]
  exact srw_hasSum_zero

/-! ### Monotone lattice paths in `ℤ²` -/

lemma sign_cases {d : ℤ} (h : d ≠ 0) : d.sign = 1 ∨ d.sign = -1 := by
  rcases lt_or_gt_of_ne h with h | h
  · right; exact Int.sign_eq_neg_one_of_neg h
  · left; exact Int.sign_eq_one_of_pos h

lemma abs_sign_mul (d : ℤ) (m : ℕ) (h : d = 0 → m = 0) : |d.sign * (m : ℤ)| = m := by
  by_cases hd : d = 0
  · simp [h hd]
  · rcases sign_cases hd with e | e <;> simp [e]

/-- The `k`-th point of the monotone path from `u` to `v`: first along coordinate `0`, then
along coordinate `1`. -/
def pt (u v : Z2) (k : ℕ) : Z2 :=
  ![u 0 + (v 0 - u 0).sign * ((min k (v 0 - u 0).natAbs : ℕ) : ℤ),
    u 1 + (v 1 - u 1).sign * ((k - (v 0 - u 0).natAbs : ℕ) : ℤ)]

def plen (u v : Z2) : ℕ := (v 0 - u 0).natAbs + (v 1 - u 1).natAbs

def lpath (u v : Z2) : List Z2 := (List.range (plen u v + 1)).map (pt u v)

lemma pt_zero (u v : Z2) : pt u v 0 = u := by
  funext i; fin_cases i <;> simp [pt]

lemma pt_plen (u v : Z2) : pt u v (plen u v) = v := by
  funext i
  fin_cases i
  · simp only [pt, plen, Fin.zero_eta, Matrix.cons_val_zero]
    rw [min_eq_right (Nat.le_add_right _ _), Int.sign_mul_natAbs]; ring
  · simp only [pt, plen, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [Nat.add_sub_cancel_left, Int.sign_mul_natAbs]; ring

lemma pt_adj (u v : Z2) (k : ℕ) (hk : k < plen u v) : adj (pt u v k) (pt u v (k + 1)) := by
  unfold plen at hk
  by_cases ha : k < (v 0 - u 0).natAbs
  · have hd : v 0 - u 0 ≠ 0 := by intro h; rw [h] at ha; simp at ha
    refine ⟨0, fun i hi => ?_, ?_⟩
    · fin_cases i
      · exact absurd rfl hi
      · simp only [pt, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [show k + 1 - (v 0 - u 0).natAbs = 0 by omega, show k - (v 0 - u 0).natAbs = 0 by omega]
    · simp only [pt, Matrix.cons_val_zero]
      rw [show min (k + 1) (v 0 - u 0).natAbs = k + 1 by omega,
        show min k (v 0 - u 0).natAbs = k by omega]
      rcases sign_cases hd with e | e <;> rw [e] <;> push_cast <;> [left; right] <;> ring
  · have hd : v 1 - u 1 ≠ 0 := by intro h; rw [h] at hk; simp at hk; omega
    refine ⟨1, fun i hi => ?_, ?_⟩
    · fin_cases i
      · simp only [pt, Fin.zero_eta, Matrix.cons_val_zero]
        rw [show min (k + 1) (v 0 - u 0).natAbs = (v 0 - u 0).natAbs by omega,
          show min k (v 0 - u 0).natAbs = (v 0 - u 0).natAbs by omega]
      · exact absurd rfl hi
    · simp only [pt, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [show k + 1 - (v 0 - u 0).natAbs = (k - (v 0 - u 0).natAbs) + 1 by omega]
      rcases sign_cases hd with e | e <;> rw [e] <;> push_cast <;> [left; right] <;> ring

lemma pt_l1 (u v : Z2) (k : ℕ) (hk : k ≤ plen u v) :
    |pt u v k 0 - u 0| + |pt u v k 1 - u 1| = k := by
  unfold plen at hk
  simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero, add_sub_cancel_left]
  rw [abs_sign_mul _ _ (fun h => by rw [h]; simp), abs_sign_mul _ _ (fun h => by
    rw [h] at hk; simp at hk; omega)]
  omega

lemma pt_bound (u v : Z2) (k : ℕ) (hk : k ≤ plen u v) (i : Fin 2) :
    |pt u v k i - u i| ≤ |v i - u i| := by
  unfold plen at hk
  fin_cases i
  · simp only [pt, Fin.zero_eta, Matrix.cons_val_zero, add_sub_cancel_left]
    rw [abs_sign_mul _ _ (fun h => by rw [h]; simp), Int.abs_eq_natAbs]
    exact_mod_cast min_le_right _ _
  · simp only [pt, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, add_sub_cancel_left]
    rw [abs_sign_mul _ _ (fun h => by rw [h] at hk; simp at hk; omega), Int.abs_eq_natAbs]
    exact_mod_cast (by omega : k - (v 0 - u 0).natAbs ≤ (v 1 - u 1).natAbs)

lemma lpath_chain (u v : Z2) : (lpath u v).IsChain adj := by
  unfold lpath
  rw [List.isChain_map, List.isChain_range_succ]
  intro m hm
  exact pt_adj u v m hm

lemma lpath_nodup (u v : Z2) : (lpath u v).Nodup := by
  unfold lpath
  refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
  rw [List.mem_range] at ha hb
  have h1 := pt_l1 u v a (by omega)
  have h2 := pt_l1 u v b (by omega)
  rw [hab] at h1
  exact_mod_cast h1.symm.trans h2

lemma lpath_length (u v : Z2) : (lpath u v).length = plen u v + 1 := by
  simp [lpath]

lemma lpath_head (u v : Z2) : (lpath u v).head? = some u := by
  simp [lpath, List.range_succ_eq_map, pt_zero]

lemma lpath_last (u v : Z2) : (lpath u v).getLast? = some v := by
  simp [lpath, List.range_succ, pt_plen]

lemma lpath_mem (u v w : Z2) (hw : w ∈ lpath u v) (i : Fin 2) : |w i - u i| ≤ |v i - u i| := by
  unfold lpath at hw
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
  rw [List.mem_range] at hk
  exact pt_bound u v k (by omega) i

lemma plen_pos {u v : Z2} (h : u ≠ v) : 1 ≤ plen u v := by
  by_contra h'
  apply h
  have h0 : (v 0 - u 0).natAbs = 0 := by unfold plen at h'; omega
  have h1 : (v 1 - u 1).natAbs = 0 := by unfold plen at h'; omega
  funext i; fin_cases i
  · simp at h0 ⊢; omega
  · simp at h1 ⊢; omega

/-- Edges of a chain are related. -/
lemma pathEdges_of_chain {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.IsChain R → ∀ e ∈ pathEdges l, R e.1 e.2
  | [], _, e, he => by simp [pathEdges] at he
  | [a], _, e, he => by simp [pathEdges] at he
  | a :: b :: l, h, e, he => by
    simp only [pathEdges, List.tail_cons, List.zip_cons_cons, List.mem_cons] at he
    rw [List.isChain_cons_cons] at h
    rcases he with rfl | he
    · exact h.1
    · exact pathEdges_of_chain h.2 e he

lemma pathEdges_length {α : Type*} (l : List α) : (pathEdges l).length = l.length - 1 := by
  simp [pathEdges]

lemma srw_reach (u v : Z2) : Relation.ReflTransGen (fun a b => 0 < MarkovMixing.srwZ 2 a b) u v := by
  have : ∀ k ≤ plen u v, Relation.ReflTransGen (fun a b => 0 < MarkovMixing.srwZ 2 a b) u
      (pt u v k) := by
    intro k
    induction k with
    | zero => intro _; rw [pt_zero]
    | succ k ih =>
      intro hk
      refine (ih (by omega)).tail ?_
      rw [srw_eq, if_pos (pt_adj u v k (by omega))]
      norm_num
  simpa [pt_plen] using this _ le_rfl

lemma srw_isNetwork : IsNetwork (MarkovMixing.srwZ 2) := by
  refine ⟨srw_nonneg, srw_symm, fun u => ⟨u + ![1, 0], ?_⟩, fun u => (srw_hasSum u).summable,
    srw_reach⟩
  rw [srw_eq, if_pos]
  · norm_num
  · refine ⟨0, fun i hi => ?_, Or.inl (by simp)⟩
    fin_cases i
    · exact absurd rfl hi
    · simp

lemma srw_networkWalk : networkWalk (MarkovMixing.srwZ 2) = MarkovMixing.srwZ 2 := by
  funext u v
  rw [networkWalk, (srw_hasSum u).tsum_eq, div_one]

lemma srw_not_transient : ¬ IsTransientNetwork (MarkovMixing.srwZ 2) := by
  rintro ⟨a, ha⟩
  apply ha
  rw [srw_networkWalk]
  have h0 : IsRecurrentChain (MarkovMixing.srwZ 2) (0 : Z2) :=
    isRecurrentChain_of_recurrent (0 : Z2) srw_nonneg srw_hasSum
      (MarkovMixing.polya_recurrence.1 2 (by norm_num) le_rfl)
  have := isRecurrentChain_translate (fun a b v => srw_translate a b v) 0 a h0
  simpa using this

/-! ### Symmetric choice of paths -/

def key (u : Z2) : Lex (ℤ × ℤ) := toLex (u 0, u 1)

lemma key_inj {u v : Z2} (h : key u = key v) : u = v := by
  have h' : (u 0, u 1) = (v 0, v 1) := toLex.injective h
  simp only [Prod.mk.injEq] at h'
  funext i; fin_cases i
  · exact h'.1
  · exact h'.2

def Q (u v : Z2) : List Z2 := if key u < key v then lpath u v else (lpath v u).reverse

lemma Q_swap {u v : Z2} (h : u ≠ v) : Q v u = (Q u v).reverse := by
  unfold Q
  rcases lt_trichotomy (key u) (key v) with h1 | h1 | h1
  · rw [if_pos h1, if_neg (lt_asymm h1)]
  · exact absurd (key_inj h1) h
  · rw [if_neg (lt_asymm h1), if_pos h1, List.reverse_reverse]

lemma plen_symm (u v : Z2) : plen v u = plen u v := by
  unfold plen
  rw [← Int.natAbs_neg (u 0 - v 0), ← Int.natAbs_neg (u 1 - v 1), neg_sub, neg_sub]

lemma Q_spec {u v : Z2} (h : u ≠ v) :
    2 ≤ (Q u v).length ∧ (Q u v).head? = some u ∧ (Q u v).getLast? = some v ∧ (Q u v).Nodup ∧
      (Q u v).IsChain adj ∧ (pathEdges (Q u v)).length = plen u v ∧
      ∀ w ∈ Q u v, ∀ i, |w i - u i| ≤ 2 * |v i - u i| ∧ |w i - v i| ≤ 2 * |v i - u i| := by
  have hp := plen_pos h
  unfold Q
  split_ifs
  · refine ⟨by rw [lpath_length]; omega, lpath_head u v, lpath_last u v, lpath_nodup u v,
      lpath_chain u v, by rw [pathEdges_length, lpath_length]; omega, fun w hw i => ?_⟩
    have h1 := lpath_mem u v w hw i
    have h2 : |w i - v i| ≤ |w i - u i| + |v i - u i| := by
      have := abs_sub_le (w i) (u i) (v i)
      rwa [abs_sub_comm (u i) (v i)] at this
    constructor <;> linarith [abs_nonneg (v i - u i)]
  · refine ⟨by rw [List.length_reverse, lpath_length, plen_symm]; omega, ?_, ?_, ?_, ?_, ?_, fun w hw i => ?_⟩
    · rw [List.head?_reverse, lpath_last]
    · rw [List.getLast?_reverse, lpath_head]
    · exact List.nodup_reverse.mpr (lpath_nodup v u)
    · rw [List.isChain_reverse]
      exact (lpath_chain v u).imp fun a b hab => adj_symm hab
    · rw [pathEdges_length, List.length_reverse, lpath_length, plen_symm]; omega
    · rw [List.mem_reverse] at hw
      have h1 := lpath_mem v u w hw i
      rw [abs_sub_comm (u i) (v i)] at h1
      have h2 : |w i - u i| ≤ |w i - v i| + |v i - u i| := abs_sub_le (w i) (v i) (u i)
      constructor <;> linarith [abs_nonneg (v i - u i)]

lemma srw_of_adj {u v : Z2} (h : adj u v) : MarkovMixing.srwZ 2 u v = 1 / 4 := by
  rw [srw_eq, if_pos h]

end SRW

/-! ## Part 3: the network of the walk on an orbit -/

section Orbit

variable {G X : Type*} [Group G] [MulAction G X] (μ : G →₀ ℝ)

lemma wk_eq (x y : X) :
    walkKernel (μ : G → ℝ) x y = ∑ g ∈ μ.support, if g • x = y then μ g else 0 := by
  unfold walkKernel
  rw [tsum_eq_sum]
  intro g hg
  rw [Finsupp.notMem_support_iff.mp hg]
  simp

variable {μ} (hμ : ThompsonAmenability.IsProbability μ)
include hμ

omit [Group G] [MulAction G X] in
lemma sum_supp : ∑ g ∈ μ.support, μ g = 1 := by
  simpa [Finsupp.sum] using hμ.2

lemma wk_nonneg (x y : X) : 0 ≤ walkKernel (μ : G → ℝ) x y := by
  rw [wk_eq]
  exact Finset.sum_nonneg fun g _ => by split_ifs; exacts [hμ.1 g, le_rfl]

lemma wk_le_one (x y : X) : walkKernel (μ : G → ℝ) x y ≤ 1 := by
  rw [wk_eq, ← sum_supp hμ]
  exact Finset.sum_le_sum fun g _ => by split_ifs; exacts [le_rfl, hμ.1 g]

lemma wk_ge {g : G} (hg : g ∈ μ.support) (x : X) : μ g ≤ walkKernel (μ : G → ℝ) x (g • x) := by
  rw [wk_eq]
  have := Finset.single_le_sum (f := fun g' => if g' • x = g • x then μ g' else 0)
    (fun g' _ => by split_ifs; exacts [hμ.1 g', le_rfl]) hg
  simpa using this

omit hμ in
lemma wk_pos_exists {x y : X} (h : 0 < walkKernel (μ : G → ℝ) x y) :
    ∃ g ∈ μ.support, g • x = y := by
  by_contra hc
  push Not at hc
  rw [wk_eq, Finset.sum_eq_zero fun g hg => if_neg (hc g hg)] at h
  exact lt_irrefl _ h

lemma wk_hasSum (x : X) : HasSum (walkKernel (μ : G → ℝ) x) 1 := by
  have : walkKernel (μ : G → ℝ) x = fun y => ∑ g ∈ μ.support, if g • x = y then μ g else 0 :=
    funext (wk_eq μ x)
  rw [this, ← sum_supp hμ]
  refine hasSum_sum fun g _ => ?_
  convert hasSum_ite_eq (g • x) (μ g) using 1
  funext y
  simp only [eq_comm]

omit hμ in
lemma wk_symm (hs : IsSymmetric μ) (x y : X) :
    walkKernel (μ : G → ℝ) x y = walkKernel (μ : G → ℝ) y x := by
  unfold walkKernel
  conv_rhs => rw [← (Equiv.inv G).tsum_eq]
  refine tsum_congr fun g => ?_
  simp only [Equiv.inv_apply, inv_smul_eq_iff]
  rw [hs g]
  simp only [eq_comm]

omit hμ in
/-- The orbit of `x₀` under the subgroup generated by the support of `μ`. -/
def orb (x₀ : X) : Set X := {y | ∃ h ∈ Subgroup.closure (μ.support : Set G), h • x₀ = y}

omit hμ in
lemma smul_mem_orb {x₀ x : X} (hx : x ∈ orb (μ := μ) x₀) {g : G}
    (hg : g ∈ Subgroup.closure (μ.support : Set G)) : g • x ∈ orb (μ := μ) x₀ := by
  obtain ⟨h, hh, rfl⟩ := hx
  exact ⟨g * h, Subgroup.mul_mem _ hg hh, mul_smul _ _ _⟩

lemma wk_out {x₀ x y : X} (hx : x ∈ orb (μ := μ) x₀) (hy : y ∉ orb (μ := μ) x₀) :
    walkKernel (μ : G → ℝ) x y = 0 := by
  by_contra hne
  obtain ⟨g, hg, rfl⟩ := wk_pos_exists (lt_of_le_of_ne (wk_nonneg hμ x y) (Ne.symm hne))
  exact hy (smul_mem_orb hx (Subgroup.subset_closure hg))

/-- The conductances of the walk restricted to the orbit. -/
noncomputable def cond (μ : G →₀ ℝ) (x₀ : X) : orb (μ := μ) x₀ → orb (μ := μ) x₀ → ℝ :=
  fun a b => walkKernel (μ : G → ℝ) (a : X) b

lemma cond_hasSum (x₀ : X) (a : orb (μ := μ) x₀) : HasSum (cond μ x₀ a) 1 := by
  have hsupp : Function.support (walkKernel (μ : G → ℝ) (a : X)) ⊆ orb (μ := μ) x₀ := by
    intro y hy
    by_contra hy'
    exact hy (wk_out hμ a.2 hy')
  exact (hasSum_subtype_iff_of_support_subset hsupp).mpr (wk_hasSum hμ (a : X))

lemma cond_isNetwork (hs : IsSymmetric μ) (x₀ : X) : IsNetwork (cond μ x₀) := by
  have hR : ∀ a b : orb (μ := μ) x₀, 0 < cond μ x₀ a b → 0 < cond μ x₀ b a := by
    intro a b h
    simpa [cond, wk_symm hs] using h
  have key : ∀ h ∈ Subgroup.closure (μ.support : Set G), ∀ a b : orb (μ := μ) x₀,
      b.1 = h • a.1 →
      Relation.ReflTransGen (fun a b : orb (μ := μ) x₀ => 0 < cond μ x₀ a b) a b := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem g hg =>
      intro a b hb
      refine Relation.ReflTransGen.single ?_
      have hpos : 0 < μ g := lt_of_le_of_ne (hμ.1 g) (Ne.symm (Finsupp.mem_support_iff.mp hg))
      show 0 < walkKernel (μ : G → ℝ) (a : X) b
      rw [hb]
      exact hpos.trans_le (wk_ge hμ hg _)
    | one =>
      intro a b hb
      rw [one_smul] at hb
      rw [Subtype.ext hb]
    | mul g h hg hh ihg ihh =>
      intro a b hb
      let m : orb (μ := μ) x₀ := ⟨h • (a : X), smul_mem_orb a.2 hh⟩
      exact (ihh a m rfl).trans (ihg m b (by rw [hb, mul_smul]))
    | inv g hg ih =>
      intro a b hb
      have h1 := Relation.reflTransGen_swap.mpr (ih b a (by rw [hb, smul_inv_smul]))
      exact Relation.ReflTransGen.mono (fun x y (h : 0 < cond μ x₀ y x) => hR y x h) a b h1
  refine ⟨fun a b => wk_nonneg hμ _ _, fun a b => wk_symm hs _ _, fun a => ?_,
    fun a => (cond_hasSum hμ x₀ a).summable, fun a b => ?_⟩
  · obtain ⟨g, hg⟩ : μ.support.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have := sum_supp hμ
      rw [hne, Finset.sum_empty] at this
      exact zero_ne_one this
    have hpos : 0 < μ g := lt_of_le_of_ne (hμ.1 g) (Ne.symm (Finsupp.mem_support_iff.mp hg))
    exact ⟨⟨g • (a : X), smul_mem_orb a.2 (Subgroup.subset_closure hg)⟩,
      hpos.trans_le (wk_ge hμ hg _)⟩
  · obtain ⟨h₁, hh₁, e₁⟩ := a.2
    obtain ⟨h₂, hh₂, e₂⟩ := b.2
    refine key (h₂ * h₁⁻¹) (Subgroup.mul_mem _ hh₂ (Subgroup.inv_mem _ hh₁)) a b ?_
    rw [← e₁, ← e₂, mul_smul, inv_smul_smul]

lemma cond_networkWalk (x₀ : X) : networkWalk (cond μ x₀) = cond μ x₀ := by
  funext a b
  rw [networkWalk, (cond_hasSum hμ x₀ a).tsum_eq, div_one]

end Orbit

/-! ### Restricting a chain to an invariant set (from the Theorem 4.2 solution) -/

section Restrict

variable {V : Type*} (P : V → V → ℝ) (O : Set V)

theorem avoidProb_restrict (hP : ∀ x ∈ O, ∀ y ∉ O, P x y = 0) (x₀ : O) :
    ∀ k (y : V), (y ∉ O → avoidProb P x₀ k y = 0) ∧
      ∀ hy : y ∈ O, avoidProb (fun a b : O => P a b) x₀ k ⟨y, hy⟩ = avoidProb P x₀ k y
  | 0, y => by simp [avoidProb]
  | 1, y => by
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · have : y ≠ (x₀ : V) := fun h => hy (h ▸ x₀.2)
      simp [avoidProb, this, hP _ x₀.2 y hy]
    · simp only [avoidProb, Subtype.ext_iff]
  | k + 2, y => by
    have ih := avoidProb_restrict hP x₀ (k + 1)
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · have : y ≠ (x₀ : V) := fun h => hy (h ▸ x₀.2)
      simp only [avoidProb, this, if_false]
      refine (tsum_congr fun z => ?_).trans tsum_zero
      by_cases hz : z ∈ O
      · simp [hP z hz y hy]
      · simp [(ih z).1 hz]
    · simp only [avoidProb, Subtype.ext_iff]
      split_ifs with h
      · rfl
      · rw [← tsum_subtype_eq_of_support_subset (s := O)]
        · exact tsum_congr fun z => by rw [(ih z).2 z.2]
        · intro z hz
          by_contra hzO
          exact hz (by simp [(ih z).1 hzO])

theorem firstReturnProb_restrict (hP : ∀ x ∈ O, ∀ y ∉ O, P x y = 0) (x₀ : O) (k : ℕ) :
    firstReturnProb (fun a b : O => P a b) x₀ k = firstReturnProb P x₀ k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [firstReturnProb]
    rw [← tsum_subtype_eq_of_support_subset (s := O)]
    · exact tsum_congr fun z => by rw [(avoidProb_restrict P O hP x₀ (k + 1) z).2 z.2]
    · intro z hz
      by_contra hzO
      exact hz (by simp [(avoidProb_restrict P O hP x₀ (k + 1) z).1 hzO])

end Restrict

/-! ## Part 4: embedding a finitely generated group of rank `≤ 2` in `ℤ²` -/

section Embed

lemma exists_embedding {A : Type*} [AddCommGroup A] [AddGroup.FG A]
    (hrk : ∀ n : ℕ, (∃ f : (Fin n → ℤ) →+ A, Function.Injective f) → n ≤ 2) :
    ∃ ψ : A → Z2, Function.Injective ψ ∧
      ∀ s : A, ∃ L : ℕ, ∀ a : A, ∀ i, |ψ (a + s) i - ψ a i| ≤ L := by
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  set T := DirectSum ι fun i => ZMod (p i ^ e i)
  have : Finite T := Finite.of_injective (fun x : T => (fun i => x i)) DFunLike.coe_injective
  have hn : n ≤ 2 := by
    refine hrk n ⟨f.symm.toAddMonoidHom.comp ((AddMonoidHom.inl (Fin n →₀ ℤ) T).comp
      (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).symm.toLinearMap.toAddMonoidHom), ?_⟩
    intro a b h
    have h1 := congrArg Prod.fst (f.symm.injective h)
    exact (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).symm.injective h1
  let N : ℕ := Nat.card T
  have hN : 0 < N := Nat.card_pos
  let ιT : T → ℤ := fun t => ((Finite.equivFin T t : Fin N) : ℕ)
  have hι0 : ∀ t, 0 ≤ ιT t := fun t => Int.natCast_nonneg _
  have hι1 : ∀ t, ιT t < N := fun t => by
    simp only [ιT]; exact_mod_cast (Finite.equivFin T t).isLt
  have hιinj : Function.Injective ιT := by
    intro a b h
    simp only [ιT, Nat.cast_inj] at h
    exact (Finite.equivFin T).injective (Fin.ext h)
  let zc : A → Fin 2 → ℤ := fun a j => if h : j.val < n then (f a).1 ⟨j, h⟩ else 0
  have hzc_add : ∀ a b j, zc (a + b) j = zc a j + zc b j := by
    intro a b j
    simp only [zc]
    split_ifs
    · simp [map_add]
    · simp
  let ψ : A → Z2 := fun a => ![N * zc a 0 + ιT (f a).2, N * zc a 1]
  refine ⟨ψ, ?_, fun s => ?_⟩
  · intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [ψ, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    have hr : ιT (f a).2 = ιT (f b).2 := by
      have e1 := congrArg (· % (N : ℤ)) h0
      rw [add_comm, Int.add_mul_emod_self_left, add_comm, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (hι0 _) (hι1 _), Int.emod_eq_of_lt (hι0 _) (hι1 _)] at e1
      exact e1
    have hz0 : zc a 0 = zc b 0 := by
      rw [hr] at h0
      exact mul_left_cancel₀ hNz (add_right_cancel h0)
    have hz1 : zc a 1 = zc b 1 := mul_left_cancel₀ hNz h1
    apply f.injective
    refine Prod.ext ?_ (hιinj hr)
    ext j
    have hj : j.val < 2 := lt_of_lt_of_le j.isLt hn
    have key : ∀ c : A, zc c ⟨j.val, hj⟩ = (f c).1 j := fun c => by
      simp only [zc, dif_pos j.isLt]
    rw [← key a, ← key b]
    rcases (by omega : j.val = 0 ∨ j.val = 1) with hj0 | hj1
    · have : (⟨j.val, hj⟩ : Fin 2) = 0 := Fin.ext hj0
      rw [this]; exact hz0
    · have : (⟨j.val, hj⟩ : Fin 2) = 1 := Fin.ext hj1
      rw [this]; exact hz1
  · refine ⟨N * ((zc s 0).natAbs + (zc s 1).natAbs + 1), fun a i => ?_⟩
    have bnd : |ψ (a + s) i - ψ a i| ≤ N * |zc s i| + N := by
      fin_cases i
      · simp only [ψ, Fin.zero_eta, Matrix.cons_val_zero]
        rw [hzc_add, map_add, Prod.snd_add]
        have h1 : N * (zc a 0 + zc s 0) + ιT ((f a).2 + (f s).2) - (N * zc a 0 + ιT (f a).2) =
            N * zc s 0 + (ιT ((f a).2 + (f s).2) - ιT (f a).2) := by ring
        rw [h1]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg N)]
        have := hι0 ((f a).2 + (f s).2); have := hι1 ((f a).2 + (f s).2)
        have := hι0 (f a).2; have := hι1 (f a).2
        have : |ιT ((f a).2 + (f s).2) - ιT (f a).2| ≤ N := abs_le.mpr ⟨by linarith, by linarith⟩
        linarith
      · simp only [ψ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hzc_add, show (N : ℤ) * (zc a 1 + zc s 1) - N * zc a 1 = N * zc s 1 by ring,
          abs_mul, abs_of_nonneg (Int.natCast_nonneg N)]
        linarith [Int.natCast_nonneg N]
    refine bnd.trans ?_
    push_cast
    have hNn : (0 : ℤ) ≤ N := Int.natCast_nonneg N
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;>
      nlinarith [abs_nonneg (zc s 0), abs_nonneg (zc s 1)]

end Embed


/-- Every element of `IET` has finitely many angles (from the Theorem 1.9 solution). -/
theorem angles_finite_of_mem_IET {g : Equiv.Perm UnitAddCircle} (hg : g ∈ IET) :
    (angles g).Finite := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.2.1
  | one => exact (Set.finite_singleton 0).subset (by rintro _ ⟨x, rfl⟩; simp)
  | mul g h _ _ hg hh =>
    refine (hg.add hh).subset ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨g (h x) - h x, ⟨h x, rfl⟩, h x - x, ⟨x, rfl⟩, ?_⟩
    simp [Equiv.Perm.mul_apply]
  | inv g _ hg =>
    refine hg.neg.subset ?_
    rintro _ ⟨x, rfl⟩
    rw [Set.mem_neg]
    exact ⟨g⁻¹ x, by simp⟩

/-! ## Part 5: the rough embedding and the conclusion -/

section Rough

lemma isRoughEmbedding_of {V : Type*} (c : V → V → ℝ) (hc1 : ∀ a b, c a b ≤ 1) (φ : V → Z2)
    (hφ : Function.Injective φ) (L : ℕ)
    (hL : ∀ a b, 0 < c a b → ∀ i, |φ b i - φ a i| ≤ L) :
    IsRoughEmbedding c (MarkovMixing.srwZ 2) φ := by
  let R : ℤ := 2 * L
  let box : Z2 → Finset Z2 := fun w => Fintype.piFinset fun i => Finset.Icc (w i - R) (w i + R)
  have hbox_card : ∀ w, (box w).card = (4 * L + 1) ^ 2 := by
    intro w
    simp only [box, Fintype.card_piFinset, Int.card_Icc, Fin.prod_univ_two]
    have : ∀ i, w i + R + 1 - (w i - R) = ((4 * L + 1 : ℕ) : ℤ) := by
      intro i; simp only [R]; push_cast; ring
    rw [this, this, Int.toNat_natCast, sq]
  refine ⟨8 * (L : ℝ), ((4 * L + 1) ^ 2) ^ 2, fun x y => Q (φ x) (φ y), ?_, ?_⟩
  · intro x y hxy hpos
    have hne : φ x ≠ φ y := hφ.ne hxy
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := Q_spec hne
    refine ⟨h1, h2, h3, h4, fun e he => ?_, ?_, Q_swap hne⟩
    · rw [srw_of_adj (pathEdges_of_chain h5 e he)]; norm_num
    · let l := (pathEdges (Q (φ x) (φ y))).map fun e : Z2 × Z2 => 1 / MarkovMixing.srwZ 2 e.1 e.2
      have hsum : l.sum ≤ l.length • (4 : ℝ) := by
        refine List.sum_le_card_nsmul _ _ fun r hr => ?_
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
        rw [srw_of_adj (pathEdges_of_chain h5 e he)]; norm_num
      rw [List.length_map, h6, nsmul_eq_mul] at hsum
      show l.sum ≤ _
      have hplen : (plen (φ x) (φ y) : ℝ) ≤ 2 * L := by
        have a0 := hL x y hpos 0
        have a1 := hL x y hpos 1
        rw [Int.abs_eq_natAbs] at a0 a1
        unfold plen
        have : (φ y 0 - φ x 0).natAbs + (φ y 1 - φ x 1).natAbs ≤ 2 * L := by omega
        exact_mod_cast this
      have hc : 1 ≤ 1 / c x y := by
        rw [le_div_iff₀ hpos, one_mul]; exact hc1 x y
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      calc _ ≤ _ := hsum
        _ ≤ 2 * L * 4 := by nlinarith
        _ = 8 * L * 1 := by ring
        _ ≤ 8 * L * (1 / c x y) := by apply mul_le_mul_of_nonneg_left hc; positivity
  · intro u v _
    let T : Set V := φ ⁻¹' (box u : Set Z2)
    have hTfin : T.Finite := (box u).finite_toSet.preimage hφ.injOn
    have hsub : {p : V × V | p.1 ≠ p.2 ∧ 0 < c p.1 p.2 ∧
        (u, v) ∈ pathEdges (Q (φ p.1) (φ p.2))} ⊆ T ×ˢ T := by
      rintro ⟨x, y⟩ ⟨hxy, hpos, he⟩
      have hne : φ x ≠ φ y := hφ.ne hxy
      have hu : u ∈ Q (φ x) (φ y) := (List.of_mem_zip he).1
      have hw := (Q_spec hne).2.2.2.2.2.2 u hu
      simp only [Set.mem_prod, Set.mem_preimage, T, box, Finset.mem_coe, Fintype.mem_piFinset,
        Finset.mem_Icc, R]
      refine ⟨fun i => ?_, fun i => ?_⟩ <;>
      · have hb := hL x y hpos i
        have hw1 := abs_le.mp (hw i).1
        have hw2 := abs_le.mp (hw i).2
        have hb' := abs_le.mp hb
        have : |φ y i - φ x i| ≤ L := hb
        have hv := abs_nonneg (φ y i - φ x i)
        constructor <;> linarith
    have hT : T.ncard ≤ (box u).card := by
      have := Set.ncard_le_ncard_of_injOn φ (fun a ha => ha) hφ.injOn (box u).finite_toSet
      rwa [Set.ncard_coe_finset] at this
    refine ⟨?_, (hTfin.prod hTfin).subset hsub⟩
    calc _ ≤ (T ×ˢ T).ncard := Set.ncard_le_ncard hsub (hTfin.prod hTfin)
      _ = T.ncard * T.ncard := Set.ncard_prod
      _ ≤ (box u).card * (box u).card := Nat.mul_le_mul hT hT
      _ = ((4 * L + 1) ^ 2) ^ 2 := by rw [hbox_card]; ring

end Rough

theorem isRecurrentAction_IETOf (Λ : AddSubgroup UnitAddCircle) (hΛ : Λ.FG)
    (hrk : rationalRank Λ ≤ 2) : IsRecurrentAction ↥(IETOf Λ) UnitAddCircle := by
  intro μ hμ hs x₀
  have : AddGroup.FG Λ := (AddGroup.fg_iff_addSubgroup_fg Λ).mpr hΛ
  obtain ⟨ψ, hψ, hjump⟩ := exists_embedding (A := Λ) (fun n ⟨f, hf⟩ => by
    have : (n : ℕ∞) ≤ rationalRank Λ :=
      le_iSup₂_of_le (f := fun (d : ℕ) (_ : ∃ f : (Fin d → ℤ) →+ Λ, Function.Injective f) =>
        (d : ℕ∞)) n ⟨f, hf⟩ le_rfl
    exact_mod_cast this.trans hrk)
  have hx₀ : x₀ ∈ orb (μ := μ) x₀ := ⟨1, Subgroup.one_mem _, one_smul _ _⟩
  have hdiff : ∀ y ∈ orb (μ := μ) x₀, y - x₀ ∈ Λ := by
    rintro y ⟨h, -, rfl⟩
    exact h.2.2 x₀
  let φ : orb (μ := μ) x₀ → Z2 := fun y => ψ ⟨y.1 - x₀, hdiff y.1 y.2⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val (hψ hab)
    simp only [sub_left_inj] at this
    exact Subtype.ext this
  -- the jumps of the walk are angles of the elements of `supp μ`
  let S : Set Λ := {s | ∃ g ∈ μ.support, (s : UnitAddCircle) ∈ angles (g : Equiv.Perm UnitAddCircle)}
  have hSfin : S.Finite := by
    have h1 : (⋃ g ∈ (μ.support : Set ↥(IETOf Λ)), angles (g : Equiv.Perm UnitAddCircle)).Finite :=
      μ.support.finite_toSet.biUnion fun g _ => angles_finite_of_mem_IET g.2.1
    refine (h1.preimage Subtype.val_injective.injOn).subset ?_
    rintro s ⟨g, hg, hs⟩
    exact Set.mem_biUnion (x := g) hg hs
  choose Lf hLf using hjump
  obtain ⟨L, hL⟩ := (hSfin.image Lf).bddAbove
  have hedge : ∀ a b : orb (μ := μ) x₀, 0 < cond μ x₀ a b → ∀ i, |φ b i - φ a i| ≤ L := by
    intro a b hab i
    obtain ⟨g, hg, hgb⟩ := wk_pos_exists hab
    have hmem : b.1 - a.1 ∈ Λ := by rw [← hgb]; exact g.2.2 a.1
    let s : Λ := ⟨b.1 - a.1, hmem⟩
    have hsS : s ∈ S := ⟨g, hg, a.1, by
      show (g : Equiv.Perm UnitAddCircle) a.1 - a.1 = b.1 - a.1
      rw [← hgb]; rfl⟩
    have e : (⟨b.1 - x₀, hdiff b.1 b.2⟩ : Λ) = ⟨a.1 - x₀, hdiff a.1 a.2⟩ + s :=
      Subtype.ext (by simp [s])
    calc |φ b i - φ a i| = |ψ (⟨a.1 - x₀, hdiff a.1 a.2⟩ + s) i - ψ ⟨a.1 - x₀, hdiff a.1 a.2⟩ i| := by
          simp only [φ]; rw [e]
      _ ≤ Lf s := hLf s _ i
      _ ≤ L := by exact_mod_cast hL ⟨s, hsS, rfl⟩
  have hrough := isRoughEmbedding_of (cond μ x₀) (fun a b => wk_le_one hμ _ _) φ hφ L hedge
  have htr := (LyonsPeres.isTransientNetwork_iff_and_isTransientNetwork_of_isRoughEmbedding
    (cond μ x₀) (MarkovMixing.srwZ 2) (cond_isNetwork hμ hs x₀) srw_isNetwork).2 φ hrough
  have hrec : IsRecurrentChain (networkWalk (cond μ x₀)) ⟨x₀, hx₀⟩ := by
    by_contra h
    exact srw_not_transient (htr ⟨_, h⟩)
  rw [cond_networkWalk hμ] at hrec
  have e : firstReturnProb (cond μ x₀) ⟨x₀, hx₀⟩ = firstReturnProb (walkKernel (μ : ↥(IETOf Λ) → ℝ)) x₀ :=
    funext (firstReturnProb_restrict (walkKernel (μ : ↥(IETOf Λ) → ℝ)) (orb (μ := μ) x₀)
      (fun x hx y hy => wk_out hμ hx hy) ⟨x₀, hx₀⟩)
  unfold IsRecurrentChain at hrec ⊢
  rwa [e] at hrec

end JMMS.IETP52

namespace JMMS

open IETP52 in
theorem chk_isRecurrentAction_and_isExtensivelyAmenable_IETOf (Λ : AddSubgroup UnitAddCircle)
    (hΛ : Λ.FG) (hrk : rationalRank Λ ≤ 2) :
    IsRecurrentAction ↥(IETOf Λ) UnitAddCircle ∧
      IsExtensivelyAmenable ↥(IETOf Λ) UnitAddCircle := by
  have h := isRecurrentAction_IETOf Λ hΛ hrk
  exact ⟨h, isExtensivelyAmenable_of_isRecurrentAction h⟩

end JMMS
end

open IntervalExchange
open JMMS in
theorem solution (Λ : AddSubgroup UnitAddCircle)
    (hΛ : Λ.FG) (hrk : rationalRank Λ ≤ 2) :
    IsRecurrentAction ↥(IETOf Λ) UnitAddCircle ∧
      IsExtensivelyAmenable ↥(IETOf Λ) UnitAddCircle :=
  JMMS.chk_isRecurrentAction_and_isExtensivelyAmenable_IETOf Λ hΛ hrk
