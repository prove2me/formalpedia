-- Prove2me | solution 1 for KellyReversibility.PartialBalance.partial_balance_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T18:17:08.071137+00:00
-- url     : https://prove2.me/submissions/6068f20d-81fc-463a-a9bc-37c8f37bba6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyReversibility_PartialBalance_Core
import Definitions.Def_KellyReversibility_PartialBalance_ExitEntryChains

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace KPB3d8

open Function KellyReversibility.PartialBalance KellyStochasticNetworks

theorem rtg_mono {α : Type*} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

theorem last_entry {α : Type*} (r : α → α → Prop) (B : Set α) {y k : α}
    (h : Relation.ReflTransGen r y k) (hy : y ∉ B) (hk : k ∈ B) :
    ∃ l s, l ∉ B ∧ s ∈ B ∧ r l s ∧
      Relation.ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ r a b) s k := by
  induction h with
  | refl => exact absurd hk hy
  | @tail b c _ hbc ih =>
    by_cases hb : b ∈ B
    · obtain ⟨l, s, hl, hs, hls, hp⟩ := ih hb
      exact ⟨l, s, hl, hs, hls, hp.tail ⟨hb, hk, hbc⟩⟩
    · exact ⟨b, c, hb, hk, hbc, Relation.ReflTransGen.refl⟩

theorem first_exit {α : Type*} (r : α → α → Prop) (B : Set α) {y k : α}
    (h : Relation.ReflTransGen r k y) (hy : y ∉ B) (hk : k ∈ B) :
    ∃ l s, l ∉ B ∧ s ∈ B ∧ r s l ∧
      Relation.ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ r a b) k s := by
  obtain ⟨l, s, hl, hs, hls, hp⟩ :=
    last_entry (fun a b => r b a) B (Relation.reflTransGen_swap.2 h) hy hk
  refine ⟨l, s, hl, hs, hls, ?_⟩
  have := (Relation.reflTransGen_swap (r := fun a b => a ∈ B ∧ b ∈ B ∧ r b a)).2 hp
  exact rtg_mono (fun a b hab => by
    simp only [Function.swap] at hab
    exact ⟨hab.2.1, hab.1, hab.2.2⟩) this

/-- Uniqueness of a stationary vector for a strictly positive kernel. -/
theorem uniq_pos {T : Type*} [Fintype T] (M : T → T → ℝ) (hM : ∀ t t', 0 < M t t')
    (μ ν : T → ℝ) (hμ : ∀ t, 0 < μ t) (hμs : ∑ t, μ t = 1) (hνs : ∑ t, ν t = 1)
    (hμb : ∀ t', ∑ t, μ t * M t t' = μ t') (hνb : ∀ t', ∑ t, ν t * M t t' = ν t') : ν = μ := by
  rcases isEmpty_or_nonempty T with hT | hT
  · funext t; exact (IsEmpty.false t).elim
  set h : T → ℝ := fun t => ν t / μ t with hh
  obtain ⟨t0, -, ht0⟩ := Finset.exists_max_image Finset.univ h Finset.univ_nonempty
  have hν : ∀ t, ν t = h t * μ t := fun t => by simp only [hh]; field_simp [(hμ t).ne']
  have hsum : ∑ t, μ t * M t t0 * (h t0 - h t) = 0 := by
    have e1 : ∑ t, μ t * M t t0 * (h t0 - h t) =
        h t0 * ∑ t, μ t * M t t0 - ∑ t, ν t * M t t0 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [hν t]; ring
    rw [e1, hμb, hνb, hν t0]; ring
  have hall : ∀ t, h t = h t0 := by
    intro t
    have hnn : ∀ t ∈ Finset.univ, 0 ≤ μ t * M t t0 * (h t0 - h t) := fun t _ =>
      mul_nonneg (mul_pos (hμ t) (hM t t0)).le (sub_nonneg.2 (ht0 t (Finset.mem_univ _)))
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum t (Finset.mem_univ _)
    rcases mul_eq_zero.1 hz with h1 | h1
    · exact absurd h1 (mul_pos (hμ t) (hM t t0)).ne'
    · linarith
  have hc : h t0 = 1 := by
    have : ∑ t, ν t = h t0 * ∑ t, μ t := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => by rw [hν t, hall t])
    rw [hνs, hμs] at this; linarith
  funext t; rw [hν t, hall t, hc, one_mul]

section Gen

variable {T : Type*} [Fintype T] [DecidableEq T]

theorem mpow_nonneg (R : Matrix T T ℝ) (hR : ∀ s t, 0 ≤ R s t) (n : ℕ) :
    ∀ s t, 0 ≤ (R ^ n) s t := by
  induction n with
  | zero => intro s t; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro s t; rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih s l) (hR l t))

theorem mpow_pos_of_rtg (R : Matrix T T ℝ) (hR : ∀ s t, 0 ≤ R s t) {x y : T}
    (h : Relation.ReflTransGen (fun a b => 0 < R a b) x y) : ∃ n, 0 < (R ^ n) x y := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [pow_succ, Matrix.mul_apply]
    exact lt_of_lt_of_le (mul_pos hn hbc)
      (Finset.single_le_sum (f := fun l => (R ^ n) x l * R l c)
        (fun l _ => mul_nonneg (mpow_nonneg R hR n x l) (hR l c)) (Finset.mem_univ b))

theorem partial_id (R : Matrix T T ℝ) (v d : T → ℝ) (hbal : Matrix.vecMul v R + d = v)
    (M : ℕ) : (∑ n ∈ Finset.range M, Matrix.vecMul d (R ^ n)) + Matrix.vecMul v (R ^ M) = v := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, pow_succ', ← Matrix.vecMul_vecMul]
    have e : Matrix.vecMul v R = v - d := by rw [eq_sub_iff_add_eq]; exact hbal
    rw [e, Matrix.sub_vecMul]
    convert ih using 1
    abel

theorem vecMul_pow_nonneg (R : Matrix T T ℝ) (hR : ∀ s t, 0 ≤ R s t) (d : T → ℝ)
    (hd : ∀ t, 0 ≤ d t) (n : ℕ) (t : T) : 0 ≤ Matrix.vecMul d (R ^ n) t :=
  Finset.sum_nonneg (fun s _ => mul_nonneg (hd s) (mpow_nonneg R hR n s t))

theorem summable_row (R : Matrix T T ℝ) (hR : ∀ s t, 0 ≤ R s t) (v d : T → ℝ)
    (hv : ∀ t, 0 ≤ v t) (hd : ∀ t, 0 ≤ d t) (hbal : Matrix.vecMul v R + d = v)
    (k : T) (r : ℕ) (hk : 0 < Matrix.vecMul d (R ^ r) k) (l : T) :
    Summable (fun n => (R ^ n) k l) := by
  apply summable_of_sum_range_le (c := v l / Matrix.vecMul d (R ^ r) k)
  · exact fun n => mpow_nonneg R hR n k l
  · intro M
    rw [le_div_iff₀ hk]
    have h1 : ∀ n, (R ^ n) k l * Matrix.vecMul d (R ^ r) k ≤
        Matrix.vecMul d (R ^ (r + n)) l := by
      intro n
      rw [pow_add, ← Matrix.vecMul_vecMul, mul_comm]
      show _ ≤ ∑ s, Matrix.vecMul d (R ^ r) s * (R ^ n) s l
      exact Finset.single_le_sum (f := fun s => Matrix.vecMul d (R ^ r) s * (R ^ n) s l)
        (fun s _ => mul_nonneg (vecMul_pow_nonneg R hR d hd r s) (mpow_nonneg R hR n s l))
        (Finset.mem_univ k)
    have h2 := congrFun (partial_id R v d hbal (r + M)) l
    rw [Finset.sum_range_add] at h2
    simp only [Finset.sum_apply, Pi.add_apply] at h2
    have h3 : 0 ≤ Matrix.vecMul v (R ^ (r + M)) l := vecMul_pow_nonneg R hR v hv _ l
    have h4 : 0 ≤ ∑ n ∈ Finset.range r, Matrix.vecMul d (R ^ n) l :=
      Finset.sum_nonneg (fun n _ => vecMul_pow_nonneg R hR d hd n l)
    rw [Finset.sum_mul]
    calc ∑ n ∈ Finset.range M, (R ^ n) k l * Matrix.vecMul d (R ^ r) k
        ≤ ∑ n ∈ Finset.range M, Matrix.vecMul d (R ^ (r + n)) l :=
          Finset.sum_le_sum (fun n _ => h1 n)
      _ ≤ v l := by linarith

theorem green_flux (R : Matrix T T ℝ) (hR : ∀ s t, 0 ≤ R s t) (v d : T → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hbal : Matrix.vecMul v R + d = v)
    (hsum : ∀ s, (d s ≠ 0 ∨ v s ≠ 0) → ∀ l, Summable (fun n => (R ^ n) s l)) (t : T) :
    ∑ s, d s * ∑' n, (R ^ n) s t = v t := by
  have hhs : HasSum (fun n => Matrix.vecMul d (R ^ n) t) (v t) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => vecMul_pow_nonneg R hR d hd n t)]
    have hp : ∀ M, ∑ n ∈ Finset.range M, Matrix.vecMul d (R ^ n) t =
        v t - Matrix.vecMul v (R ^ M) t := by
      intro M
      have := congrFun (partial_id R v d hbal M) t
      simp only [Pi.add_apply, Finset.sum_apply] at this
      linarith
    simp_rw [hp]
    have h0 : Filter.Tendsto (fun M => Matrix.vecMul v (R ^ M) t) Filter.atTop (nhds 0) := by
      have : Filter.Tendsto (fun M => ∑ s, v s * (R ^ M) s t) Filter.atTop
          (nhds (∑ s : T, (0 : ℝ))) := by
        apply tendsto_finsetSum
        intro s _
        by_cases hs : v s = 0
        · simp [hs]
        · simpa using ((hsum s (Or.inr hs) t).tendsto_atTop_zero).const_mul (v s)
      simpa [Matrix.vecMul, dotProduct] using this
    simpa using h0.const_sub (v t)
  rw [← hhs.tsum_eq]
  simp only [Matrix.vecMul, dotProduct]
  rw [Summable.tsum_finsetSum]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [tsum_mul_left]
  · intro s _
    by_cases hs : d s = 0
    · simp [hs]
    · exact (hsum s (Or.inl hs) t).mul_left (d s)

end Gen

section Chain

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem qnn (q : S → S → ℝ) (hq : IsRateMatrix q) (s t : S) : 0 ≤ q s t := by
  by_cases h : s = t
  · subst h; rw [hq.2 s]
  · exact hq.1 s t h

theorem P_nonneg (q : S → S → ℝ) (hq : IsRateMatrix q) (htot : ∀ s, 0 < ∑ k, q s k)
    (s t : S) : 0 ≤ jumpProb q s t :=
  div_nonneg (qnn q hq s t) (htot s).le

theorem R_nonneg (q : S → S → ℝ) (hq : IsRateMatrix q) (htot : ∀ s, 0 < ∑ k, q s k)
    (B : Set S) (s t : S) : 0 ≤ restrictMatrix (jumpProb q) B s t := by
  unfold restrictMatrix
  split_ifs
  · exact P_nonneg q hq htot s t
  · exact le_rfl

theorem R_pos (q : S → S → ℝ) (htot : ∀ s, 0 < ∑ k, q s k) (B : Set S) {s t : S}
    (hs : s ∈ B) (ht : t ∈ B) (h : 0 < q s t) : 0 < restrictMatrix (jumpProb q) B s t := by
  unfold restrictMatrix
  rw [if_pos ⟨hs, ht⟩]
  exact div_pos h (htot s)

theorem wP (q : S → S → ℝ) (π : S → ℝ) (htot : ∀ s, 0 < ∑ k, q s k) (s t : S) :
    π s * (∑ k, q s k) * jumpProb q s t = π s * q s t := by
  unfold jumpProb
  have h := (htot s).ne'
  field_simp

open Classical in
noncomputable def vB (q : S → S → ℝ) (π : S → ℝ) (B : Set S) : S → ℝ :=
  fun s => if s ∈ B then π s * ∑ k, q s k else 0

open Classical in
noncomputable def dB (q : S → S → ℝ) (π : S → ℝ) (B : Set S) : S → ℝ :=
  fun t => if t ∈ B then ∑ s, (if s ∈ B then 0 else π s * q s t) else 0

theorem vB_nonneg (q : S → S → ℝ) (π : S → ℝ) (hq : IsRateMatrix q) (hπ : ∀ s, 0 < π s)
    (B : Set S) (s : S) : 0 ≤ vB q π B s := by
  unfold vB
  split_ifs
  · exact mul_nonneg (hπ s).le (Finset.sum_nonneg (fun k _ => qnn q hq s k))
  · exact le_rfl

theorem dB_nonneg (q : S → S → ℝ) (π : S → ℝ) (hq : IsRateMatrix q) (hπ : ∀ s, 0 < π s)
    (B : Set S) (t : S) : 0 ≤ dB q π B t := by
  unfold dB
  split_ifs
  · refine Finset.sum_nonneg (fun s _ => ?_)
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hπ s).le (qnn q hq s t)
  · exact le_rfl

theorem flux_bal (q : S → S → ℝ) (π : S → ℝ) (htot : ∀ s, 0 < ∑ k, q s k)
    (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t) (B : Set S) :
    Matrix.vecMul (vB q π B) (restrictMatrix (jumpProb q) B) + dB q π B = vB q π B := by
  classical
  funext t
  simp only [Pi.add_apply, Matrix.vecMul, dotProduct, vB, dB, restrictMatrix]
  by_cases ht : t ∈ B
  · simp only [ht, and_true, if_true]
    rw [hbal t, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases hs : s ∈ B
    · simp only [hs, if_true, add_zero]; exact wP q π htot s t
    · simp only [hs, if_false, zero_mul, zero_add]
  · simp [ht]

theorem row_summable (q : S → S → ℝ) (π : S → ℝ) (hq : IsRateMatrix q) (hπ : ∀ s, 0 < π s)
    (htot : ∀ s, 0 < ∑ k, q s k) (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t)
    (B : Set S) {k : S} (hk : ∃ l s0, l ∉ B ∧ s0 ∈ B ∧ 0 < q l s0 ∧
      Relation.ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ 0 < q a b) s0 k) (m : S) :
    Summable (fun n => ((restrictMatrix (jumpProb q) B) ^ n) k m) := by
  classical
  obtain ⟨l, s0, hl, hs0, hls, hp⟩ := hk
  have hR := R_nonneg q hq htot B
  obtain ⟨r, hr⟩ := mpow_pos_of_rtg _ hR
    (rtg_mono (fun a b h => R_pos q htot B h.1 h.2.1 h.2.2) hp)
  have hd0 : 0 < dB q π B s0 := by
    unfold dB
    rw [if_pos hs0]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun s => if s ∈ B then (0 : ℝ) else π s * q s s0) ?_ (Finset.mem_univ l))
    · simp only [hl, if_false]; exact mul_pos (hπ l) hls
    · intro s _
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hπ s).le (qnn q hq s s0)
  refine summable_row _ hR (vB q π B) (dB q π B) (vB_nonneg q π hq hπ B)
    (dB_nonneg q π hq hπ B) (flux_bal q π htot hbal B) k r ?_ m
  exact lt_of_lt_of_le (mul_pos hd0 hr) (Finset.single_le_sum
    (f := fun s => dB q π B s * ((restrictMatrix (jumpProb q) B) ^ r) s k)
    (fun s _ => mul_nonneg (dB_nonneg q π hq hπ B s) (mpow_nonneg _ hR r s k))
    (Finset.mem_univ s0))

theorem dB_ne_zero_mem (q : S → S → ℝ) (π : S → ℝ) (B : Set S) (s : S)
    (h : dB q π B s ≠ 0 ∨ vB q π B s ≠ 0) : s ∈ B := by
  classical
  by_contra hs
  rcases h with h | h
  · exact h (by unfold dB; rw [if_neg hs])
  · exact h (by unfold vB; rw [if_neg hs])

/-- The flux identity `d · G_B = v`. -/
theorem green_B (q : S → S → ℝ) (π : S → ℝ) (hq : IsRateMatrix q) (hπ : ∀ s, 0 < π s)
    (htot : ∀ s, 0 < ∑ k, q s k) (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t)
    (B : Set S) (hrow : ∀ k ∈ B, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) B) ^ n) k m))
    (t : S) :
    ∑ s, dB q π B s * ∑' n, ((restrictMatrix (jumpProb q) B) ^ n) s t = vB q π B t :=
  green_flux _ (R_nonneg q hq htot B) _ _ (dB_nonneg q π hq hπ B) (flux_bal q π htot hbal B)
    (fun s hs => hrow s (dB_ne_zero_mem q π B s hs)) t

theorem entrance_eq (q : S → S → ℝ) (A : Set S) (k i : S)
    (hs : ∀ l, Summable (fun n => ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k l)) :
    entranceProb q A k i =
      ∑ l, (∑' n, ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k l) * jumpProb q l i := by
  unfold entranceProb
  simp only [Matrix.mul_apply]
  rw [Summable.tsum_finsetSum (fun l _ => (hs l).mul_right _)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [tsum_mul_right]

open Classical in
theorem tsum_sub (B : Set S) (f : S → ℝ) : ∑' k : B, f k = ∑ k, if k ∈ B then f k else 0 := by
  rw [tsum_subtype, tsum_fintype]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [Set.indicator_apply]

end Chain

theorem hk_of_path {α : Type*} (q : α → α → ℝ) (r : α → α → Prop) (hr : ∀ x y, r x y → 0 < q x y)
    (B : Set α) {y k : α} (h : Relation.ReflTransGen r y k) (hy : y ∉ B) (hk : k ∈ B) :
    ∃ l s0, l ∉ B ∧ s0 ∈ B ∧ 0 < q l s0 ∧
      Relation.ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ 0 < q a b) s0 k := by
  obtain ⟨l, s0, hl, hs0, hls, hp⟩ := last_entry r B h hy hk
  exact ⟨l, s0, hl, hs0, hr _ _ hls,
    rtg_mono (fun x z hxz => ⟨hxz.1, hxz.2.1, hr _ _ hxz.2.2⟩) hp⟩

section Chain2

variable {S : Type*} [Fintype S] [DecidableEq S]

open Classical in
noncomputable def Hf (q : S → S → ℝ) (A : Set S) (i' j' : S) : ℝ :=
  ∑ k, if k ∈ A then 0 else jumpProb q j' k * entranceProb q A k i'

open Classical in
noncomputable def Kf (q : S → S → ℝ) (A : Set S) (j' k : S) : ℝ :=
  ∑ i, if i ∈ A then entranceProb q A k i * greenWithin q A i j' *
    (exitRate q A j' / ∑ k', q j' k') else 0

open Classical in
theorem entry_expand (q : S → S → ℝ) (A : Set S) (i i' : A) :
    entryChain q A i i' = ∑ j', if j' ∈ A then greenWithin q A i j' * Hf q A i' j' else 0 := by
  have hin : ∀ j' : S, (∑' k : (Aᶜ : Set S), jumpProb q j' k * entranceProb q A k i') =
      Hf q A i' j' := by
    intro j'
    rw [tsum_sub Aᶜ (fun k => jumpProb q j' k * entranceProb q A k i')]
    unfold Hf
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k ∈ A <;> simp [hk]
  unfold entryChain
  simp only [hin]
  exact tsum_sub A (fun j' => greenWithin q A i j' * Hf q A i' j')

open Classical in
theorem exit_expand (q : S → S → ℝ) (A : Set S) (j j' : A) :
    exitChain q A j j' =
      ∑ k, if k ∈ A then 0 else q j k / exitRate q A j * Kf q A j' k := by
  have hin : ∀ k : S, (∑' i : A, entranceProb q A k i * greenWithin q A i j' *
      (exitRate q A j' / ∑ k', q j' k')) = Kf q A j' k := by
    intro k
    rw [tsum_sub A (fun i => entranceProb q A k i * greenWithin q A i j' *
      (exitRate q A j' / ∑ k', q j' k'))]
    rfl
  unfold exitChain
  simp only [hin]
  rw [tsum_sub Aᶜ (fun k => q j k / exitRate q A j * Kf q A j' k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : k ∈ A <;> simp [hk]

open Classical in
theorem exitRate_eq (q : S → S → ℝ) (A : Set S) (t : S) :
    exitRate q A t = ∑ k, (if k ∈ A then 0 else q t k) := by
  unfold exitRate
  rw [tsum_sub Aᶜ (fun k => q t k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : k ∈ A <;> simp [hk]

open Classical in
theorem entrance_flux (q : S → S → ℝ) (π : S → ℝ) (hq : IsRateMatrix q) (hπ : ∀ s, 0 < π s)
    (htot : ∀ s, 0 < ∑ k, q s k) (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t)
    (A : Set S)
    (hrowC : ∀ k ∈ Aᶜ, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k m))
    (i : S) :
    ∑ k, dB q π Aᶜ k * entranceProb q A k i = ∑ l, (if l ∈ A then 0 else π l * q l i) := by
  have h1 : ∀ k, dB q π Aᶜ k * entranceProb q A k i =
      ∑ l, dB q π Aᶜ k *
        ((∑' n, ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k l) * jumpProb q l i) := by
    intro k
    rw [← Finset.mul_sum]
    by_cases hk : k ∈ Aᶜ
    · rw [entrance_eq q A k i (hrowC k hk)]
    · simp only [dB, hk, if_false, zero_mul]
  rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have h2 := green_B q π hq hπ htot hbal Aᶜ hrowC l
  calc ∑ k, dB q π Aᶜ k * ((∑' n, ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k l) * jumpProb q l i)
      = (∑ k, dB q π Aᶜ k * ∑' n, ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k l) *
          jumpProb q l i := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_); ring
    _ = _ := by
        rw [h2]; unfold vB
        by_cases hl : l ∈ A
        · simp [hl]
        · simp only [Set.mem_compl_iff, hl, not_false_eq_true, ↓reduceIte]
          exact wP q π htot l i

open Classical in
theorem entry_flux (q : S → S → ℝ) (π : S → ℝ) (hq : IsRateMatrix q) (hπ : ∀ s, 0 < π s)
    (htot : ∀ s, 0 < ∑ k, q s k) (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t)
    (A : Set S)
    (hrowA : ∀ k ∈ A, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) A) ^ n) k m))
    (hrowC : ∀ k ∈ Aᶜ, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k m))
    (i' : S) :
    ∑ i, dB q π A i * (∑ j', if j' ∈ A then greenWithin q A i j' * Hf q A i' j' else 0) =
      ∑ l, (if l ∈ A then 0 else π l * q l i') := by
  have h1 : ∀ i, dB q π A i *
      (∑ j', if j' ∈ A then greenWithin q A i j' * Hf q A i' j' else 0) =
      ∑ j', ∑ k, dB q π A i * greenWithin q A i j' *
        (if j' ∈ A then (if k ∈ A then 0 else jumpProb q j' k * entranceProb q A k i')
          else 0) := by
    intro i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    by_cases hj : j' ∈ A
    · simp only [hj, if_true, Hf, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    · simp [hj]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]
  have h2 : ∀ j', ∑ i, ∑ k, dB q π A i * greenWithin q A i j' *
      (if j' ∈ A then (if k ∈ A then 0 else jumpProb q j' k * entranceProb q A k i') else 0) =
      ∑ k, vB q π A j' *
        (if j' ∈ A then (if k ∈ A then 0 else jumpProb q j' k * entranceProb q A k i')
          else 0) := by
    intro j'
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← green_B q π hq hπ htot hbal A hrowA j', Finset.sum_mul]
    rfl
  rw [Finset.sum_congr rfl (fun j' _ => h2 j'), Finset.sum_comm,
    ← entrance_flux q π hq hπ htot hbal A hrowC i']
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : k ∈ A
  · simp [hk, dB]
  · have e : ∀ j', vB q π A j' *
        (if j' ∈ A then (if k ∈ A then 0 else jumpProb q j' k * entranceProb q A k i')
          else 0) = (if j' ∈ A then π j' * q j' k else 0) * entranceProb q A k i' := by
      intro j'
      by_cases hj : j' ∈ A
      · simp only [vB, hj, hk, if_true, if_false]; rw [← wP q π htot j' k]; ring
      · simp [vB, hj]
    rw [Finset.sum_congr rfl (fun j' _ => e j'), ← Finset.sum_mul]
    congr 1
    simp only [dB, Set.mem_compl_iff, hk, not_false_eq_true, ↓reduceIte]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases hs : s ∈ A <;> simp [hs]

open Classical in
theorem exit_term (q : S → S → ℝ) (hq : IsRateMatrix q) (A : Set S) (j k : S) (hk : k ∉ A)
    (a K : ℝ) : a * exitRate q A j * (q j k / exitRate q A j * K) = a * q j k * K := by
  by_cases hx : exitRate q A j = 0
  · have hz : q j k = 0 := by
      rw [exitRate_eq] at hx
      have hnn : ∀ l ∈ Finset.univ, 0 ≤ (if l ∈ A then (0:ℝ) else q j l) := fun l _ => by
        split_ifs
        · exact le_rfl
        · exact qnn q hq j l
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hx k (Finset.mem_univ _)
      simpa [hk] using this
    simp [hx, hz]
  · field_simp

theorem exitRate_nonneg (q : S → S → ℝ) (hq : IsRateMatrix q) (A : Set S) (j : S) :
    0 ≤ exitRate q A j := by
  classical
  rw [exitRate_eq]
  exact Finset.sum_nonneg (fun l _ => by
    split_ifs
    · exact le_rfl
    · exact qnn q hq j l)

open Classical in
theorem exit_flux (q : S → S → ℝ) (π : S → ℝ) (hq : IsRateMatrix q) (hπ : ∀ s, 0 < π s)
    (htot : ∀ s, 0 < ∑ k, q s k) (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t)
    (A : Set S)
    (hrowA : ∀ k ∈ A, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) A) ^ n) k m))
    (hrowC : ∀ k ∈ Aᶜ, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k m))
    (j' : S) (hj' : j' ∈ A) :
    ∑ j, (if j ∈ A then π j * exitRate q A j else 0) *
      (∑ k, if k ∈ A then 0 else q j k / exitRate q A j * Kf q A j' k) =
    π j' * exitRate q A j' := by
  have h1 : ∀ j, (if j ∈ A then π j * exitRate q A j else 0) *
      (∑ k, if k ∈ A then 0 else q j k / exitRate q A j * Kf q A j' k) =
      ∑ k, (if j ∈ A then (if k ∈ A then 0 else π j * q j k * Kf q A j' k) else 0) := by
    intro j
    by_cases hj : j ∈ A
    · simp only [hj, if_true, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs
      · simp
      · rename_i hk
        exact exit_term q hq A j k hk (π j) _
    · simp [hj]
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  have h2 : ∀ k, ∑ j, (if j ∈ A then (if k ∈ A then 0 else π j * q j k * Kf q A j' k)
      else 0) = dB q π Aᶜ k * Kf q A j' k := by
    intro k
    by_cases hk : k ∈ A
    · simp [hk, dB]
    · simp only [dB, Set.mem_compl_iff, hk, not_false_eq_true, ↓reduceIte, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      by_cases hs : s ∈ A <;> simp [hs]
  rw [Finset.sum_congr rfl (fun k _ => h2 k)]
  have h3 : ∑ k, dB q π Aᶜ k * Kf q A j' k =
      ∑ i, dB q π A i * greenWithin q A i j' * (exitRate q A j' / ∑ k', q j' k') := by
    simp only [Kf, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i ∈ A
    · simp only [hi, if_true]
      have := entrance_flux q π hq hπ htot hbal A hrowC i
      calc ∑ k, dB q π Aᶜ k * (entranceProb q A k i * greenWithin q A i j' *
            (exitRate q A j' / ∑ k', q j' k'))
          = (∑ k, dB q π Aᶜ k * entranceProb q A k i) *
              (greenWithin q A i j' * (exitRate q A j' / ∑ k', q j' k')) := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_); ring
        _ = _ := by rw [this]; simp only [dB, hi, if_true]; ring
    · simp [hi, dB]
  rw [h3, ← Finset.sum_mul]
  have h5 : ∑ i, dB q π A i * greenWithin q A i j' = vB q π A j' :=
    green_B q π hq hπ htot hbal A hrowA j'
  rw [h5]
  simp only [vB, hj', if_true]
  have := (htot j').ne'
  field_simp

end Chain2

theorem fullBalance_iff {S : Type*} [Fintype S] (π : S → ℝ) (q : S → S → ℝ) :
    FullBalance π q ↔ ∀ j, π j * ∑ k, q j k = ∑ k, π k * q k j := by
  simp [FullBalance, tsum_fintype]

theorem the_stat_of_pos {T : Type*} [Finite T] (M : T → T → ℝ) (hM : ∀ t t', 0 < M t t')
    (μ : T → ℝ) (hμ : ∀ t, 0 < μ t) (hs : IsStationaryDist M μ) : IsTheStationaryDist M μ := by
  haveI := Fintype.ofFinite T
  refine ⟨hs, fun ν hν => ?_⟩
  obtain ⟨-, hμs, hμb⟩ := hs
  obtain ⟨-, hνs, hνb⟩ := hν
  rw [tsum_fintype] at hμs hνs
  simp only [tsum_fintype] at hμb hνb
  exact uniq_pos M hM μ ν hμ hμs hνs hμb hνb

theorem rtg_sub {α : Type*} {B : Set α} (r : α → α → Prop) {x y : B}
    (h : Relation.ReflTransGen (fun a b : B => r a b) x y) :
    Relation.ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ r a b) (x : α) y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact ih.tail ⟨b.2, c.2, hbc⟩

open Classical in
theorem exists_pos_term {S : Type*} [Fintype S] (A : Set S) (f : S → ℝ)
    (h : 0 < ∑ k, (if k ∈ A then 0 else f k)) : ∃ k, k ∉ A ∧ 0 < f k := by
  by_contra hc
  push_neg at hc
  have : ∑ k, (if k ∈ A then (0 : ℝ) else f k) ≤ 0 := Finset.sum_nonpos (fun k _ => by
    split_ifs with hk
    · exact le_rfl
    · exact hc k hk)
  linarith

section Stat

variable {S : Type*} [Fintype S] [DecidableEq S]

open Classical in
theorem sum_e_eq (q : S → S → ℝ) (π : S → ℝ)
    (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t) (A : Set S) :
    ∑ s, dB q π A s = ∑ s, (if s ∈ A then π s * exitRate q A s else 0) := by
  have hsplit1 : ∀ t, ∑ k, q t k =
      ∑ k, (if k ∈ A then q t k else 0) + ∑ k, (if k ∈ A then 0 else q t k) := by
    intro t; rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_); split_ifs <;> simp
  have hsplit2 : ∀ t, ∑ s, π s * q s t =
      ∑ s, (if s ∈ A then π s * q s t else 0) + ∑ s, (if s ∈ A then 0 else π s * q s t) := by
    intro t; rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_); split_ifs <;> simp
  have hx : ∀ t, (if t ∈ A then π t * exitRate q A t else 0) = dB q π A t +
      ((if t ∈ A then ∑ s, (if s ∈ A then π s * q s t else 0) else 0) -
        (if t ∈ A then π t * ∑ k, (if k ∈ A then q t k else 0) else 0)) := by
    intro t
    by_cases ht : t ∈ A
    · simp only [ht, if_true, dB]
      rw [exitRate_eq]
      have := hbal t
      rw [hsplit1 t, hsplit2 t] at this
      linarith
    · simp [ht, dB]
  rw [Finset.sum_congr rfl (fun t _ => hx t), Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have l1 : ∀ t, (if t ∈ A then ∑ s, (if s ∈ A then π s * q s t else 0) else 0) =
      ∑ s, (if s ∈ A ∧ t ∈ A then π s * q s t else 0) := by
    intro t; by_cases ht : t ∈ A <;> simp [ht]
  have l2 : ∀ t, (if t ∈ A then π t * ∑ k, (if k ∈ A then q t k else 0) else 0) =
      ∑ k, (if t ∈ A ∧ k ∈ A then π t * q t k else 0) := by
    intro t; by_cases ht : t ∈ A <;> simp [ht, Finset.mul_sum, mul_ite]
  rw [Finset.sum_congr rfl (fun t _ => l1 t), Finset.sum_congr rfl (fun t _ => l2 t),
    Finset.sum_comm (f := fun t s => if s ∈ A ∧ t ∈ A then π s * q s t else 0)]
  ring

open Classical in
theorem entry_stat (q : S → S → ℝ) (π : S → ℝ) (hq : IsRateMatrix q) (hπ : ∀ s, 0 < π s)
    (htot : ∀ s, 0 < ∑ k, q s k) (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t)
    (A : Set S)
    (hrowA : ∀ k ∈ A, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) A) ^ n) k m))
    (hrowC : ∀ k ∈ Aᶜ, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k m))
    (hSig : 0 < ∑ s, dB q π A s) :
    IsStationaryDist (entryChain q A) (fun t : A => dB q π A t / ∑ s, dB q π A s) := by
  refine ⟨fun t => div_nonneg (dB_nonneg q π hq hπ A t) hSig.le, ?_, fun t' => ?_⟩
  · rw [tsum_sub A (fun t => dB q π A t / ∑ s, dB q π A s)]
    have hz : ∀ t, (if t ∈ A then dB q π A t / ∑ s, dB q π A s else 0) =
        dB q π A t / ∑ s, dB q π A s := by
      intro t
      by_cases ht : t ∈ A
      · rw [if_pos ht]
      · rw [if_neg ht]; simp [dB, ht]
    rw [Finset.sum_congr rfl (fun t _ => hz t), ← Finset.sum_div, div_self hSig.ne']
  · have hexp : ∀ t : A, dB q π A t / (∑ s, dB q π A s) * entryChain q A t t' =
        (fun x : S => dB q π A x / (∑ s, dB q π A s) *
          ∑ j', if j' ∈ A then greenWithin q A x j' * Hf q A t' j' else 0) t := by
      intro t; rw [entry_expand]
    show ∑' t : A, dB q π A t / (∑ s, dB q π A s) * entryChain q A t t' =
      dB q π A t' / ∑ s, dB q π A s
    rw [tsum_congr hexp, tsum_sub A (fun x : S => dB q π A x / (∑ s, dB q π A s) *
          ∑ j', if j' ∈ A then greenWithin q A x j' * Hf q A t' j' else 0)]
    have hz : ∀ t, (if t ∈ A then dB q π A t / (∑ s, dB q π A s) *
        (∑ j', if j' ∈ A then greenWithin q A t j' * Hf q A t' j' else 0) else 0) =
        dB q π A t * (∑ j', if j' ∈ A then greenWithin q A t j' * Hf q A t' j' else 0) /
          (∑ s, dB q π A s) := by
      intro t
      by_cases ht : t ∈ A
      · rw [if_pos ht]; ring
      · rw [if_neg ht]; simp [dB, ht]
    rw [Finset.sum_congr rfl (fun t _ => hz t), ← Finset.sum_div,
      entry_flux q π hq hπ htot hbal A hrowA hrowC t']
    have : dB q π A t' = ∑ l, (if l ∈ A then 0 else π l * q l t') := by
      unfold dB; rw [if_pos t'.2]
    rw [this]

open Classical in
theorem exit_stat (q : S → S → ℝ) (π : S → ℝ) (hq : IsRateMatrix q) (hπ : ∀ s, 0 < π s)
    (htot : ∀ s, 0 < ∑ k, q s k) (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t)
    (A : Set S)
    (hrowA : ∀ k ∈ A, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) A) ^ n) k m))
    (hrowC : ∀ k ∈ Aᶜ, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k m))
    (hSig : 0 < ∑ s, (if s ∈ A then π s * exitRate q A s else 0)) :
    IsStationaryDist (exitChain q A) (fun t : A => π t * exitRate q A t /
      ∑ s, (if s ∈ A then π s * exitRate q A s else 0)) := by
  refine ⟨fun t => div_nonneg (mul_nonneg (hπ t).le (exitRate_nonneg q hq A t)) hSig.le, ?_, fun t' => ?_⟩
  · rw [tsum_sub A (fun t => π t * exitRate q A t / ∑ s, (if s ∈ A then π s * exitRate q A s else 0))]
    have hz : ∀ t, (if t ∈ A then π t * exitRate q A t /
        ∑ s, (if s ∈ A then π s * exitRate q A s else 0) else 0) =
        (if t ∈ A then π t * exitRate q A t else 0) /
          ∑ s, (if s ∈ A then π s * exitRate q A s else 0) := by
      intro t
      by_cases ht : t ∈ A
      · rw [if_pos ht, if_pos ht]
      · rw [if_neg ht, if_neg ht, zero_div]
    rw [Finset.sum_congr rfl (fun t _ => hz t), ← Finset.sum_div, div_self hSig.ne']
  · have hexp : ∀ t : A, π t * exitRate q A t /
        (∑ s, (if s ∈ A then π s * exitRate q A s else 0)) * exitChain q A t t' =
        (fun x : S => π x * exitRate q A x / (∑ s, (if s ∈ A then π s * exitRate q A s else 0)) *
          ∑ k, if k ∈ A then 0 else q x k / exitRate q A x * Kf q A t' k) t := by
      intro t; rw [exit_expand]
    show ∑' t : A, π t * exitRate q A t /
        (∑ s, (if s ∈ A then π s * exitRate q A s else 0)) * exitChain q A t t' =
      π t' * exitRate q A t' / ∑ s, (if s ∈ A then π s * exitRate q A s else 0)
    rw [tsum_congr hexp, tsum_sub A (fun x : S => π x * exitRate q A x /
          (∑ s, (if s ∈ A then π s * exitRate q A s else 0)) *
          ∑ k, if k ∈ A then 0 else q x k / exitRate q A x * Kf q A t' k)]
    have hz : ∀ t, (if t ∈ A then π t * exitRate q A t /
        (∑ s, (if s ∈ A then π s * exitRate q A s else 0)) *
        (∑ k, if k ∈ A then 0 else q t k / exitRate q A t * Kf q A t' k) else 0) =
        (if t ∈ A then π t * exitRate q A t else 0) *
          (∑ k, if k ∈ A then 0 else q t k / exitRate q A t * Kf q A t' k) /
          (∑ s, (if s ∈ A then π s * exitRate q A s else 0)) := by
      intro t
      by_cases ht : t ∈ A
      · rw [if_pos ht, if_pos ht]; ring
      · rw [if_neg ht, if_neg ht]; simp
    rw [Finset.sum_congr rfl (fun t _ => hz t), ← Finset.sum_div,
      exit_flux q π hq hπ htot hbal A hrowA hrowC t' t'.2]

theorem green_nonneg (q : S → S → ℝ) (hq : IsRateMatrix q) (htot : ∀ s, 0 < ∑ k, q s k)
    (B : Set S) (i s : S) : 0 ≤ greenWithin q B i s :=
  tsum_nonneg (fun n => mpow_nonneg _ (R_nonneg q hq htot B) n i s)

theorem entrance_nonneg (q : S → S → ℝ) (hq : IsRateMatrix q) (htot : ∀ s, 0 < ∑ k, q s k)
    (A : Set S) (k i : S) : 0 ≤ entranceProb q A k i :=
  tsum_nonneg (fun n => by
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg
      (mpow_nonneg _ (R_nonneg q hq htot Aᶜ) n k l) (P_nonneg q hq htot l i)))

end Stat

section SibGen

/-- Maximum principle: two balanced vectors, one positive, are proportional. -/
theorem uniq_of_irred {S : Type*} [Fintype S] [DecidableEq S] (q : S → S → ℝ)
    (hq : IsRateMatrix q) (hirr : IsIrreducible q) (π p : S → ℝ) (hπ : ∀ a, 0 < π a)
    (hbπ : ∀ j, π j * ∑ k, q j k = ∑ k, π k * q k j)
    (hbp : ∀ j, p j * ∑ k, q j k = ∑ k, p k * q k j) :
    ∃ c : ℝ, ∀ a, p a = c * π a := by
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨0, fun a => (IsEmpty.false a).elim⟩
  set r : S → ℝ := fun a => p a / π a with hr
  obtain ⟨a0, -, ha0⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
  have hpr : ∀ a, p a = r a * π a := fun a => by
    simp only [hr]; field_simp [(hπ a).ne']
  -- closure under predecessors of the max set
  have hclose : ∀ a, r a = r a0 → ∀ k, 0 < q k a → r k = r a0 := by
    intro a ha k hk
    have h1 := hbp a
    have h2 := hbπ a
    have hsum : ∑ l, π l * q l a * (r a - r l) = 0 := by
      have e1 : ∑ l, π l * q l a * (r a - r l) =
          r a * (∑ l, π l * q l a) - ∑ l, p l * q l a := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [hpr l]; ring
      rw [e1, ← h1, ← h2, hpr a]; ring
    have hnn : ∀ l ∈ Finset.univ, 0 ≤ π l * q l a * (r a - r l) := by
      intro l _
      by_cases hl : l = a
      · subst hl; simp [hq.2 l]
      · have := hq.1 l a hl
        have h3 : r l ≤ r a := by rw [ha]; exact ha0 l (Finset.mem_univ _)
        have := (hπ l).le
        positivity
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum k (Finset.mem_univ _)
    have : r a - r k = 0 := by
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h (mul_pos (hπ k) hk).ne'
      · exact h
    linarith
  have hall : ∀ k, r k = r a0 := by
    intro k
    have hp := hirr k a0
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | head hab _ ih => exact hclose _ ih _ hab
  exact ⟨r a0, fun a => by rw [hpr a, hall a]⟩

/-- Existence of a positive balanced vector. -/
theorem exists_pos_balanced {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (q : S → S → ℝ) (hq : IsRateMatrix q) (hirr : IsIrreducible q) :
    ∃ w : S → ℝ, (∀ a, 0 < w a) ∧ ∀ j, w j * ∑ k, q j k = ∑ k, w k * q k j := by
  have hqnn : ∀ j k, 0 ≤ q j k := fun j k => by
    by_cases h : j = k
    · subst h; rw [hq.2 j]
    · exact hq.1 j k h
  let G : Matrix S S ℝ := fun k j => q k j - if k = j then ∑ l, q k l else 0
  have hG1 : G.mulVec (fun _ => (1 : ℝ)) = 0 := by
    funext k
    simp [G, Matrix.mulVec, dotProduct, Finset.sum_sub_distrib]
  have hdet : G.det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨fun _ => 1, fun h => by simpa using congrFun h (Classical.arbitrary S), hG1⟩
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hvbal : ∀ j, v j * ∑ k, q j k = ∑ k, v k * q k j := by
    intro j
    have := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, G, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at this
    linarith
  set w : S → ℝ := fun a => |v a| with hw
  have hwle : ∀ j, w j * ∑ k, q j k ≤ ∑ k, w k * q k j := by
    intro j
    have hout : 0 ≤ ∑ k, q j k := Finset.sum_nonneg (fun k _ => hqnn j k)
    calc w j * ∑ k, q j k = |v j * ∑ k, q j k| := by
          rw [abs_mul, abs_of_nonneg hout]
      _ = |∑ k, v k * q k j| := by rw [hvbal j]
      _ ≤ ∑ k, |v k * q k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, w k * q k j := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [abs_mul, abs_of_nonneg (hqnn k j)]
  have htot : ∑ j, w j * ∑ k, q j k = ∑ j, ∑ k, w k * q k j := by
    rw [Finset.sum_comm (f := fun j k => w k * q k j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
  have hweq : ∀ j, w j * ∑ k, q j k = ∑ k, w k * q k j := by
    intro j
    exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hwle j)).1 htot j (Finset.mem_univ _)
  have hwnn : ∀ a, 0 ≤ w a := fun a => abs_nonneg _
  -- zero set closed under predecessors
  have hclose : ∀ a, w a = 0 → ∀ k, 0 < q k a → w k = 0 := by
    intro a ha k hk
    have h := hweq a
    rw [ha, zero_mul] at h
    have hnn : ∀ l ∈ Finset.univ, 0 ≤ w l * q l a := fun l _ => mul_nonneg (hwnn l) (hqnn l a)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h.symm k (Finset.mem_univ _)
    rcases mul_eq_zero.1 hz with h' | h'
    · exact h'
    · exact absurd h' hk.ne'
  have hpos : ∀ a, 0 < w a := by
    intro a
    rcases (hwnn a).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hv0
      funext k
      have hk : w k = 0 := by
        have hp := hirr k a
        induction hp using Relation.ReflTransGen.head_induction_on with
        | refl => exact h.symm
        | head hab _ ih => exact hclose _ ih _ hab
      simpa [hw] using hk
  exact ⟨w, hpos, hweq⟩

theorem the_of_eq {S : Type*} [Fintype S] [DecidableEq S] (q : S → S → ℝ)
    (hq : IsRateMatrix q) (hirr : IsIrreducible q) (π : S → ℝ) (h : IsEquilibriumDist q π) :
    IsTheEquilibriumDist q π := by
  refine ⟨h, fun p hp => ?_⟩
  obtain ⟨hπpos, hπsum, hπbal⟩ := h
  obtain ⟨hppos, hpsum, hpbal⟩ := hp
  rw [fullBalance_iff] at hπbal hpbal
  obtain ⟨c, hc⟩ := uniq_of_irred q hq hirr π p hπpos hπbal hpbal
  rw [tsum_fintype] at hπsum hpsum
  have : c = 1 := by
    have : ∑ a, p a = c * ∑ a, π a := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => hc a)
    rw [hpsum, hπsum] at this; linarith
  funext a; rw [hc a, this, one_mul]

theorem exists_the {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] (q : S → S → ℝ)
    (hq : IsRateMatrix q) (hirr : IsIrreducible q) :
    ∃ p, IsTheEquilibriumDist q p := by
  obtain ⟨w, hpos, hbal⟩ := exists_pos_balanced q hq hirr
  have hs : 0 < ∑ a, w a := Finset.sum_pos (fun a _ => hpos a) Finset.univ_nonempty
  refine ⟨fun a => w a / ∑ b, w b, the_of_eq q hq hirr _ ⟨fun a => div_pos (hpos a) hs, ?_, ?_⟩⟩
  · rw [tsum_fintype, ← Finset.sum_div, div_self hs.ne']
  · rw [fullBalance_iff]
    intro j
    have := hbal j
    simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    rw [this]



end SibGen

open Classical in
theorem ipb_iff {S : Type*} [Fintype S] (q : S → S → ℝ) (π : S → ℝ) (A : Set S) (n : S)
    (hb : π n * ∑ k, q n k = ∑ k, π k * q k n) :
    (π n * ∑ k, (if k ∈ A then 0 else q n k) = ∑ k, (if k ∈ A then 0 else π k * q k n)) ↔
    (π n * ∑ k, (if k ∈ A then q n k else 0) = ∑ k, (if k ∈ A then π k * q k n else 0)) := by
  have h1 : ∑ k, q n k =
      ∑ k, (if k ∈ A then q n k else 0) + ∑ k, (if k ∈ A then 0 else q n k) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun k _ => ?_); split_ifs <;> simp
  have h2 : ∑ k, π k * q k n =
      ∑ k, (if k ∈ A then π k * q k n else 0) + ∑ k, (if k ∈ A then 0 else π k * q k n) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun k _ => ?_); split_ifs <;> simp
  rw [h1, h2, mul_add] at hb
  constructor <;> intro h <;> linarith

open Classical in
theorem fsum_sub {S : Type*} [Fintype S] (B : Set S) [Fintype B] (f : S → ℝ) :
    ∑ k : B, f k = ∑ k, if k ∈ B then f k else 0 := by
  rw [← tsum_sub B f, tsum_fintype]

open Classical in
theorem cond_bal_iff {S : Type*} [Fintype S] (q : S → S → ℝ) (π : S → ℝ) (A : Set S)
    [Fintype A] (hZ : 0 < ∑' k : A, π k) :
    (∀ t : A, condDist π A t * ∑ k : A, truncatedRates q A t k =
      ∑ k : A, condDist π A k * truncatedRates q A k t) ↔
    ∀ n ∈ A, π n * ∑ k, (if k ∈ A then q n k else 0) =
      ∑ k, (if k ∈ A then π k * q k n else 0) := by
  have key : ∀ t : A, (condDist π A t * ∑ k : A, truncatedRates q A t k =
      ∑ k : A, condDist π A k * truncatedRates q A k t) ↔
      (π t * ∑ k, (if k ∈ A then q t k else 0) =
        ∑ k, (if k ∈ A then π k * q k t else 0)) := by
    intro t
    have eL : condDist π A t * ∑ k : A, truncatedRates q A t k =
        (π t * ∑ k, (if k ∈ A then q t k else 0)) / ∑' m : A, π m := by
      unfold condDist truncatedRates
      rw [fsum_sub A (fun k => q t k)]; ring
    have eR : ∑ k : A, condDist π A k * truncatedRates q A k t =
        (∑ k, (if k ∈ A then π k * q k t else 0)) / ∑' m : A, π m := by
      unfold condDist truncatedRates
      rw [fsum_sub A (fun k => π k / (∑' m : A, π m) * q k t), Finset.sum_div]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs
      · ring
      · simp
    rw [eL, eR, div_left_inj' hZ.ne']
  constructor
  · intro h n hn; exact (key ⟨n, hn⟩).1 (h ⟨n, hn⟩)
  · intro h t; exact (key t).2 (h t t.2)

open Classical in
theorem esd_eq {S : Type*} [Fintype S] (π : S → ℝ) (A : Set S) (c : ℝ) (n : S) :
    exitScaledDist π A c n = (∑ k, if k ∈ A then π k else c * π k)⁻¹ *
      (if n ∈ A then π n else c * π n) := by
  have hC : (∑' k : (Aᶜ : Set S), π k) = ∑ k, (if k ∈ A then 0 else π k) := by
    rw [tsum_sub Aᶜ π]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k ∈ A <;> simp [hk]
  have hB : (∑ k, if k ∈ A then π k else 0) + c * ∑ k, (if k ∈ A then 0 else π k) =
      ∑ k, if k ∈ A then π k else c * π k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k ∈ A <;> simp [hk]
  unfold exitScaledDist
  rw [tsum_sub A π, hC, hB]

open Classical in
theorem esd_equil_iff {S : Type*} [Fintype S] (π : S → ℝ) (hπ : ∀ s, 0 < π s) (A : Set S)
    (c : ℝ) (hc0 : 0 < c) (n0 : S) (q' : S → S → ℝ) :
    IsEquilibriumDist q' (exitScaledDist π A c) ↔
      ∀ n, (if n ∈ A then π n else c * π n) * ∑ k, q' n k =
        ∑ k, (if k ∈ A then π k else c * π k) * q' k n := by
  have hp0 : ∀ n, 0 < (if n ∈ A then π n else c * π n) := fun n => by
    split_ifs
    · exact hπ n
    · exact mul_pos hc0 (hπ n)
  have hB : 0 < ∑ k, (if k ∈ A then π k else c * π k) :=
    lt_of_lt_of_le (hp0 n0) (Finset.single_le_sum (f := fun k => if k ∈ A then π k else c * π k)
      (fun k _ => (hp0 k).le) (Finset.mem_univ n0))
  have e : ∀ n, ∑ k, exitScaledDist π A c k * q' k n =
      (∑ k, if k ∈ A then π k else c * π k)⁻¹ *
        ∑ k, (if k ∈ A then π k else c * π k) * q' k n := by
    intro n; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => ?_); rw [esd_eq]; ring
  have hbal : FullBalance (exitScaledDist π A c) q' ↔
      ∀ n, (if n ∈ A then π n else c * π n) * ∑ k, q' n k =
        ∑ k, (if k ∈ A then π k else c * π k) * q' k n := by
    rw [fullBalance_iff]
    refine forall_congr' (fun n => ?_)
    rw [e n, esd_eq, mul_assoc]
    exact mul_right_inj' (inv_ne_zero hB.ne')
  constructor
  · intro h; exact hbal.1 h.2.2
  · intro h
    refine ⟨fun n => by rw [esd_eq]; exact mul_pos (inv_pos.2 hB) (hp0 n), ?_, hbal.2 h⟩
    rw [tsum_fintype]
    simp only [esd_eq]
    rw [← Finset.mul_sum, inv_mul_cancel₀ hB.ne']


section NewGen

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Neumann identity `f G = f + (f G) R` for `G = ∑ R^n`. -/
theorem neumann (R : Matrix T T ℝ) (f : T → ℝ)
    (hs : ∀ s, f s ≠ 0 → ∀ l, Summable (fun n => (R ^ n) s l)) (t : T) :
    ∑ s, f s * ∑' n, (R ^ n) s t = f t + ∑ l, (∑ s, f s * ∑' n, (R ^ n) s l) * R l t := by
  have key : ∀ s, f s * ∑' n, (R ^ n) s t =
      f s * (if s = t then 1 else 0) + ∑ l, (f s * ∑' n, (R ^ n) s l) * R l t := by
    intro s
    by_cases hf : f s = 0
    · simp [hf]
    have hsum := hs s hf
    rw [(hsum t).tsum_eq_zero_add]
    simp only [pow_zero, Matrix.one_apply, pow_succ, Matrix.mul_apply]
    rw [Summable.tsum_finsetSum (fun l _ => (hsum l).mul_right _)]
    simp only [tsum_mul_right]
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [Finset.sum_congr rfl (fun s _ => key s), Finset.sum_add_distrib]
  congr 1
  · simp [mul_ite]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.sum_mul]

end NewGen

section NewChain

variable {S : Type*} [Fintype S] [DecidableEq S]

open Classical in
theorem ng_supp (P : Matrix S S ℝ) (B : Set S) (f : S → ℝ)
    (hfB : ∀ t, t ∉ B → f t = 0)
    (hs : ∀ s, f s ≠ 0 → ∀ l, Summable (fun n => ((restrictMatrix P B) ^ n) s l))
    (t : S) (ht : t ∉ B) :
    ∑ s, f s * ∑' n, ((restrictMatrix P B) ^ n) s t = 0 := by
  rw [neumann _ f hs t, hfB t ht]
  simp [restrictMatrix, ht]

open Classical in
/-- Gluing two Neumann blocks gives a `jumpProb`-invariant vector. -/
theorem lift_inv (P : Matrix S S ℝ) (A : Set S) (z y h f : S → ℝ)
    (hz : ∀ t, z t = h t + ∑ l, z l * restrictMatrix P A l t)
    (hy : ∀ t, y t = f t + ∑ l, y l * restrictMatrix P Aᶜ l t)
    (hh : ∀ t, h t = if t ∈ A then ∑ s, y s * P s t else 0)
    (hf : ∀ t, f t = if t ∈ A then 0 else ∑ s, z s * P s t) :
    (∀ t, t ∉ A → z t = 0) ∧ (∀ t, t ∈ A → y t = 0) ∧
      ∀ t, z t + y t = ∑ s, (z s + y s) * P s t := by
  have hz0 : ∀ t, t ∉ A → z t = 0 := by
    intro t ht
    rw [hz t, hh t, if_neg ht]
    simp [restrictMatrix, ht]
  have hy0 : ∀ t, t ∈ A → y t = 0 := by
    intro t ht
    rw [hy t, hf t, if_pos ht]
    simp [restrictMatrix, ht]
  refine ⟨hz0, hy0, fun t => ?_⟩
  simp only [add_mul, Finset.sum_add_distrib]
  by_cases ht : t ∈ A
  · rw [hy0 t ht, add_zero, hz t, hh t, if_pos ht, add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hl : l ∈ A
    · simp [restrictMatrix, hl, ht]
    · simp [hz0 l hl]
  · rw [hz0 t ht, zero_add, hy t, hf t, if_neg ht]
    congr 1
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hl : l ∈ A
    · simp [hy0 l hl]
    · simp [restrictMatrix, hl, ht]

theorem inv_prop (q : S → S → ℝ) (hq : IsRateMatrix q) (hirr : IsIrreducible q)
    (π : S → ℝ) (hπ : ∀ s, 0 < π s) (htot : ∀ s, 0 < ∑ k, q s k)
    (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t) (w : S → ℝ)
    (hw : ∀ t, w t = ∑ s, w s * jumpProb q s t) :
    ∃ c : ℝ, ∀ s, w s = c * (π s * ∑ k, q s k) := by
  have hbp : ∀ j, (w j / ∑ k, q j k) * ∑ k, q j k = ∑ k, (w k / ∑ k', q k k') * q k j := by
    intro j
    rw [div_mul_cancel₀ _ (htot j).ne', hw j]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold jumpProb; ring
  obtain ⟨c, hc⟩ := uniq_of_irred q hq hirr π (fun s => w s / ∑ k, q s k) hπ hbal hbp
  refine ⟨c, fun s => ?_⟩
  have := hc s
  rw [div_eq_iff (htot s).ne'] at this
  rw [this]; ring

open Classical in
/-- `∑ f E = (f G_{Aᶜ}) P` for `f` supported on `Aᶜ`. -/
theorem fE_eq (q : S → S → ℝ) (A : Set S) (f : S → ℝ) (hfA : ∀ k, k ∈ A → f k = 0)
    (hrowC : ∀ k ∈ Aᶜ, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k m))
    (i : S) :
    ∑ k, f k * entranceProb q A k i =
      ∑ l, (∑ k, f k * ∑' n, ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k l) * jumpProb q l i := by
  have h1 : ∀ k, f k * entranceProb q A k i =
      ∑ l, f k * ((∑' n, ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k l) * jumpProb q l i) := by
    intro k
    rw [← Finset.mul_sum]
    by_cases hk : k ∈ A
    · simp [hfA k hk]
    · rw [entrance_eq q A k i (hrowC k hk)]
  rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

end NewChain

section Main

variable {S : Type*} [Fintype S] [DecidableEq S]

open Classical in
theorem qz_of_exit (q : S → S → ℝ) (hq : IsRateMatrix q) (A : Set S) (j k : S) (hk : k ∉ A)
    (hx : exitRate q A j = 0) : q j k = 0 := by
  rw [exitRate_eq] at hx
  have hnn : ∀ l ∈ Finset.univ, 0 ≤ (if l ∈ A then (0:ℝ) else q j l) := fun l _ => by
    split_ifs
    · exact le_rfl
    · exact qnn q hq j l
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hx k (Finset.mem_univ _)
  simpa [hk] using this

open Classical in
theorem norm_eq (A : Set S) (ν : A → ℝ) (g : S → ℝ) (c : ℝ) (hν : ∀ t : A, ν t = c * g t)
    (hs : ∑' t : A, ν t = 1) (hF : 0 < ∑ s, (if s ∈ A then g s else 0)) :
    ν = fun t : A => g t / ∑ s, (if s ∈ A then g s else 0) := by
  have h1 : ∑' t : A, ν t = c * ∑ s, (if s ∈ A then g s else 0) := by
    rw [tsum_congr hν, tsum_mul_left, tsum_sub A g]
  rw [hs] at h1
  funext t
  rw [hν t, eq_div_iff hF.ne']
  linear_combination (-(g t)) * h1

open Classical in
theorem exit_unique (q : S → S → ℝ) (hq : IsRateMatrix q) (hirr : IsIrreducible q)
    (π : S → ℝ) (hπ : ∀ s, 0 < π s) (htot : ∀ s, 0 < ∑ k, q s k)
    (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t) (A : Set S)
    (hrowA : ∀ k ∈ A, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) A) ^ n) k m))
    (hrowC : ∀ k ∈ Aᶜ, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k m))
    (ν : A → ℝ) (hν : IsStationaryDist (exitChain q A) ν) :
    ∃ c : ℝ, ∀ t : A, ν t = c * (π t * exitRate q A t) := by
  obtain ⟨ν', hν'def⟩ : ∃ ν' : S → ℝ, ν' = fun s => if hs : s ∈ A then ν ⟨s, hs⟩ else 0 :=
    ⟨_, rfl⟩
  have hνν : ∀ t : A, ν t = ν' t := fun t => by simp [hν'def, t.2]
  have hν'0 : ∀ s, s ∉ A → ν' s = 0 := fun s hs => by simp [hν'def, hs]
  obtain ⟨f, hfdef⟩ : ∃ f : S → ℝ,
      f = fun k => if k ∈ A then 0 else ∑ j, ν' j * (q j k / exitRate q A j) := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : S → ℝ,
      y = fun t => ∑ s, f s * ∑' n, ((restrictMatrix (jumpProb q) Aᶜ) ^ n) s t := ⟨_, rfl⟩
  obtain ⟨h, hhdef⟩ : ∃ h : S → ℝ,
      h = fun t => if t ∈ A then ∑ s, y s * jumpProb q s t else 0 := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : S → ℝ,
      z = fun t => ∑ s, h s * ∑' n, ((restrictMatrix (jumpProb q) A) ^ n) s t := ⟨_, rfl⟩
  have hfA : ∀ k, k ∈ A → f k = 0 := fun k hk => by simp [hfdef, hk]
  have hhA : ∀ k, k ∉ A → h k = 0 := fun k hk => by simp [hhdef, hk]
  have hfs : ∀ s, f s ≠ 0 → ∀ l,
      Summable (fun n => ((restrictMatrix (jumpProb q) Aᶜ) ^ n) s l) := fun s hs =>
    hrowC s (fun hA => hs (hfA s hA))
  have hhs : ∀ s, h s ≠ 0 → ∀ l,
      Summable (fun n => ((restrictMatrix (jumpProb q) A) ^ n) s l) := fun s hs =>
    hrowA s (by by_contra hA; exact hs (hhA s hA))
  have hz0 : ∀ t, t ∉ A → z t = 0 := fun t ht => by
    rw [hzdef]; exact ng_supp _ A h hhA hhs t ht
  have hkey : ∀ j' : S, j' ∈ A → ν' j' = z j' * (exitRate q A j' / ∑ k', q j' k') := by
    intro j' hj'
    rw [← hνν ⟨j', hj'⟩, ← hν.2.2 ⟨j', hj'⟩]
    have e1 : ∀ t : A, ν t * exitChain q A t ⟨j', hj'⟩ = (fun x : S => ν' x *
        ∑ k, if k ∈ A then 0 else q x k / exitRate q A x * Kf q A j' k) t := by
      intro t; rw [exit_expand, hνν t]
    rw [tsum_congr e1, tsum_sub A (fun x : S => ν' x *
        ∑ k, if k ∈ A then 0 else q x k / exitRate q A x * Kf q A j' k)]
    have e2 : ∀ x, (if x ∈ A then ν' x * ∑ k, (if k ∈ A then 0 else
        q x k / exitRate q A x * Kf q A j' k) else 0) =
        ∑ k, ν' x * (if k ∈ A then 0 else q x k / exitRate q A x * Kf q A j' k) := by
      intro x
      by_cases hx : x ∈ A
      · rw [if_pos hx, Finset.mul_sum]
      · rw [if_neg hx, hν'0 x hx]; simp
    rw [Finset.sum_congr rfl (fun x _ => e2 x), Finset.sum_comm]
    have e3 : ∀ k, ∑ x, ν' x * (if k ∈ A then 0 else q x k / exitRate q A x * Kf q A j' k) =
        f k * Kf q A j' k := by
      intro k
      by_cases hk : k ∈ A
      · simp [hk, hfdef]
      · simp only [hk, if_false, hfdef, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [Finset.sum_congr rfl (fun k _ => e3 k)]
    simp only [Kf, Finset.mul_sum]
    rw [Finset.sum_comm, hzdef, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i ∈ A
    · simp only [hi, if_true]
      have hfe := fE_eq q A f hfA hrowC i
      have hhi : h i = ∑ l, (∑ k, f k * ∑' n, ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k l) *
          jumpProb q l i := by
        rw [hhdef, hydef]; simp only [hi, if_true]
      calc ∑ k, f k * (entranceProb q A k i * greenWithin q A i j' *
            (exitRate q A j' / ∑ k', q j' k'))
          = (∑ k, f k * entranceProb q A k i) * greenWithin q A i j' *
              (exitRate q A j' / ∑ k', q j' k') := by
            rw [Finset.sum_mul, Finset.sum_mul]
            exact Finset.sum_congr rfl (fun k _ => by ring)
        _ = h i * (∑' n, ((restrictMatrix (jumpProb q) A) ^ n) i j') *
              (exitRate q A j' / ∑ k', q j' k') := by
            rw [hfe, ← hhi]; rfl
    · simp [hi, hhA i hi]
  have hz' : ∀ t, z t = h t + ∑ l, z l * restrictMatrix (jumpProb q) A l t := fun t => by
    rw [hzdef]; exact neumann _ h hhs t
  have hy' : ∀ t, y t = f t + ∑ l, y l * restrictMatrix (jumpProb q) Aᶜ l t := fun t => by
    rw [hydef]; exact neumann _ f hfs t
  have hh' : ∀ t, h t = if t ∈ A then ∑ s, y s * jumpProb q s t else 0 := fun t => by
    rw [hhdef]
  have hf' : ∀ t, f t = if t ∈ A then 0 else ∑ s, z s * jumpProb q s t := by
    intro t
    by_cases ht : t ∈ A
    · simp [hfdef, ht]
    · rw [hfdef]
      simp only [ht, if_false]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      by_cases hs : s ∈ A
      · rw [hkey s hs]
        unfold jumpProb
        by_cases hx : exitRate q A s = 0
        · rw [qz_of_exit q hq A s t ht hx]; simp
        · have := (htot s).ne'
          field_simp
      · rw [hν'0 s hs, hz0 s hs]; simp
  obtain ⟨-, hy0, hw⟩ := lift_inv (jumpProb q) A z y h f hz' hy' hh' hf'
  obtain ⟨c, hc⟩ := inv_prop q hq hirr π hπ htot hbal (fun t => z t + y t) hw
  refine ⟨c, fun t => ?_⟩
  rw [hνν t, hkey t t.2]
  have := hc t
  rw [hy0 t t.2, add_zero] at this
  rw [this]
  have := (htot t).ne'
  field_simp

open Classical in
theorem entry_unique (q : S → S → ℝ) (hq : IsRateMatrix q) (hirr : IsIrreducible q)
    (π : S → ℝ) (hπ : ∀ s, 0 < π s) (htot : ∀ s, 0 < ∑ k, q s k)
    (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t) (A : Set S)
    (hrowA : ∀ k ∈ A, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) A) ^ n) k m))
    (hrowC : ∀ k ∈ Aᶜ, ∀ m, Summable (fun n => ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k m))
    (ν : A → ℝ) (hν : IsStationaryDist (entryChain q A) ν) :
    ∃ c : ℝ, ∀ t : A, ν t = c * dB q π A t := by
  obtain ⟨ν', hν'def⟩ : ∃ ν' : S → ℝ, ν' = fun s => if hs : s ∈ A then ν ⟨s, hs⟩ else 0 :=
    ⟨_, rfl⟩
  have hνν : ∀ t : A, ν t = ν' t := fun t => by simp [hν'def, t.2]
  have hν'0 : ∀ s, s ∉ A → ν' s = 0 := fun s hs => by simp [hν'def, hs]
  obtain ⟨z, hzdef⟩ : ∃ z : S → ℝ,
      z = fun t => ∑ s, ν' s * ∑' n, ((restrictMatrix (jumpProb q) A) ^ n) s t := ⟨_, rfl⟩
  have hzs : ∀ s, ν' s ≠ 0 → ∀ l,
      Summable (fun n => ((restrictMatrix (jumpProb q) A) ^ n) s l) := fun s hs =>
    hrowA s (by by_contra hA; exact hs (hν'0 s hA))
  have hz0 : ∀ t, t ∉ A → z t = 0 := fun t ht => by
    rw [hzdef]; exact ng_supp _ A ν' hν'0 hzs t ht
  obtain ⟨f, hfdef⟩ : ∃ f : S → ℝ,
      f = fun k => if k ∈ A then 0 else ∑ s, z s * jumpProb q s k := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : S → ℝ,
      y = fun t => ∑ s, f s * ∑' n, ((restrictMatrix (jumpProb q) Aᶜ) ^ n) s t := ⟨_, rfl⟩
  obtain ⟨h, hhdef⟩ : ∃ h : S → ℝ,
      h = fun t => if t ∈ A then ∑ s, y s * jumpProb q s t else 0 := ⟨_, rfl⟩
  have hfA : ∀ k, k ∈ A → f k = 0 := fun k hk => by simp [hfdef, hk]
  have hfs : ∀ s, f s ≠ 0 → ∀ l,
      Summable (fun n => ((restrictMatrix (jumpProb q) Aᶜ) ^ n) s l) := fun s hs =>
    hrowC s (fun hA => hs (hfA s hA))
  have hkey : ∀ i' : S, i' ∈ A → ν' i' = h i' := by
    intro i' hi'
    rw [← hνν ⟨i', hi'⟩, ← hν.2.2 ⟨i', hi'⟩]
    have e1 : ∀ t : A, ν t * entryChain q A t ⟨i', hi'⟩ = (fun x : S => ν' x *
        ∑ j', if j' ∈ A then greenWithin q A x j' * Hf q A i' j' else 0) t := by
      intro t; rw [entry_expand, hνν t]
    rw [tsum_congr e1, tsum_sub A (fun x : S => ν' x *
        ∑ j', if j' ∈ A then greenWithin q A x j' * Hf q A i' j' else 0)]
    have e2 : ∀ x, (if x ∈ A then ν' x * ∑ j', (if j' ∈ A then
        greenWithin q A x j' * Hf q A i' j' else 0) else 0) =
        ∑ j', ν' x * (if j' ∈ A then greenWithin q A x j' * Hf q A i' j' else 0) := by
      intro x
      by_cases hx : x ∈ A
      · rw [if_pos hx, Finset.mul_sum]
      · rw [if_neg hx, hν'0 x hx]; simp
    rw [Finset.sum_congr rfl (fun x _ => e2 x), Finset.sum_comm]
    have e3 : ∀ j', ∑ x, ν' x * (if j' ∈ A then greenWithin q A x j' * Hf q A i' j' else 0) =
        ∑ k, (if k ∈ A then 0 else z j' * jumpProb q j' k * entranceProb q A k i') := by
      intro j'
      by_cases hj : j' ∈ A
      · simp only [hj, if_true]
        have e : ∑ x, ν' x * (greenWithin q A x j' * Hf q A i' j') = z j' * Hf q A i' j' := by
          rw [hzdef, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun x _ => by unfold greenWithin; ring)
        rw [e, Hf, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        split_ifs <;> ring
      · simp [hj, hz0 j' hj]
    rw [Finset.sum_congr rfl (fun j' _ => e3 j'), Finset.sum_comm]
    have e4 : ∀ k, ∑ j', (if k ∈ A then 0 else z j' * jumpProb q j' k * entranceProb q A k i') =
        f k * entranceProb q A k i' := by
      intro k
      by_cases hk : k ∈ A
      · simp [hk, hfdef]
      · simp only [hk, if_false, hfdef, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun k _ => e4 k), fE_eq q A f hfA hrowC i', hhdef, hydef]
    simp only [hi', if_true]
  have hz' : ∀ t, z t = h t + ∑ l, z l * restrictMatrix (jumpProb q) A l t := by
    intro t
    have hzt : ∀ t, z t = ∑ s, ν' s * ∑' n, ((restrictMatrix (jumpProb q) A) ^ n) s t :=
      fun t => by rw [hzdef]
    rw [hzt t, neumann _ ν' hzs t]
    simp only [← hzt]
    congr 1
    by_cases ht : t ∈ A
    · exact hkey t ht
    · rw [hν'0 t ht, hhdef]; simp [ht]
  have hy' : ∀ t, y t = f t + ∑ l, y l * restrictMatrix (jumpProb q) Aᶜ l t := fun t => by
    rw [hydef]; exact neumann _ f hfs t
  have hh' : ∀ t, h t = if t ∈ A then ∑ s, y s * jumpProb q s t else 0 := fun t => by
    rw [hhdef]
  have hf' : ∀ t, f t = if t ∈ A then 0 else ∑ s, z s * jumpProb q s t := fun t => by
    rw [hfdef]
  obtain ⟨-, hy0, hw⟩ := lift_inv (jumpProb q) A z y h f hz' hy' hh' hf'
  obtain ⟨c, hc⟩ := inv_prop q hq hirr π hπ htot hbal (fun t => z t + y t) hw
  refine ⟨c, fun t => ?_⟩
  rw [hνν t, hkey t t.2, hhdef]
  simp only [t.2, if_true, dB, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  by_cases hs : s ∈ A
  · simp [hs, hy0 s hs]
  · have := hc s
    rw [hz0 s hs, zero_add] at this
    simp only [hs, if_false, this]
    unfold jumpProb
    have := (htot s).ne'
    field_simp

open Classical in
theorem pb_iff (q : S → S → ℝ) (π : S → ℝ) (A : Set S) :
    IsPartialBalance π q A ↔ ∀ n ∈ A, π n * ∑ k, (if k ∈ A then q n k else 0) =
      ∑ k, (if k ∈ A then π k * q k n else 0) := by
  unfold IsPartialBalance
  refine forall_congr' (fun n => imp_congr_right (fun _ => ?_))
  rw [tsum_sub A (fun k => q n k), tsum_sub A (fun k => π k * q k n)]

open Classical in
theorem sW_iff (q : S → S → ℝ) (π : S → ℝ) (A : Set S) (c : ℝ) (hc1 : c ≠ 1)
    (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t) :
    (∀ n, π n * ∑ k, scaleWithin q A c n k = ∑ k, π k * scaleWithin q A c k n) ↔
    ∀ n ∈ A, π n * ∑ k, (if k ∈ A then q n k else 0) =
      ∑ k, (if k ∈ A then π k * q k n else 0) := by
  have hout : ∀ n, n ∈ A → ∑ k, scaleWithin q A c n k =
      ∑ k, q n k + (c - 1) * ∑ k, (if k ∈ A then q n k else 0) := by
    intro n hn
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k ∈ A <;> simp [scaleWithin, hn, hk] <;> ring
  have hout' : ∀ n, n ∉ A → ∑ k, scaleWithin q A c n k = ∑ k, q n k := by
    intro n hn
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [scaleWithin, hn]
  have hin : ∀ n, n ∈ A → ∑ k, π k * scaleWithin q A c k n =
      ∑ k, π k * q k n + (c - 1) * ∑ k, (if k ∈ A then π k * q k n else 0) := by
    intro n hn
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k ∈ A <;> simp [scaleWithin, hn, hk] <;> ring
  have hin' : ∀ n, n ∉ A → ∑ k, π k * scaleWithin q A c k n = ∑ k, π k * q k n := by
    intro n hn
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [scaleWithin, hn]
  have hc : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  constructor
  · intro h n hn
    have h1 := h n
    rw [hout n hn, hin n hn] at h1
    have h0 := hbal n
    apply mul_left_cancel₀ hc
    linear_combination h1 - h0
  · intro h n
    by_cases hn : n ∈ A
    · rw [hout n hn, hin n hn]
      linear_combination hbal n + (c - 1) * h n hn
    · rw [hout' n hn, hin' n hn]
      exact hbal n

open Classical in
theorem sE_iff (q : S → S → ℝ) (π : S → ℝ) (A : Set S) (c : ℝ) (hc1 : c ≠ 1)
    (hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t) :
    (∀ n, (if n ∈ A then π n else c * π n) * ∑ k, scaleExit q A c n k =
      ∑ k, (if k ∈ A then π k else c * π k) * scaleExit q A c k n) ↔
    ∀ n ∈ A, π n * ∑ k, (if k ∈ A then 0 else q n k) =
      ∑ k, (if k ∈ A then 0 else π k * q k n) := by
  have hout : ∀ n, n ∈ A → ∑ k, scaleExit q A c n k =
      ∑ k, q n k + (c - 1) * ∑ k, (if k ∈ A then 0 else q n k) := by
    intro n hn
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k ∈ A <;> simp [scaleExit, hn, hk] <;> ring
  have hout' : ∀ n, n ∉ A → ∑ k, scaleExit q A c n k = ∑ k, q n k := by
    intro n hn
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [scaleExit, hn]
  have hin : ∀ n, n ∈ A →
      ∑ k, (if k ∈ A then π k else c * π k) * scaleExit q A c k n =
      ∑ k, π k * q k n + (c - 1) * ∑ k, (if k ∈ A then 0 else π k * q k n) := by
    intro n hn
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k ∈ A <;> simp [scaleExit, hn, hk] <;> ring
  have hin' : ∀ n, n ∉ A →
      ∑ k, (if k ∈ A then π k else c * π k) * scaleExit q A c k n =
      c * ∑ k, π k * q k n := by
    intro n hn
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k ∈ A <;> simp [scaleExit, hn, hk] <;> ring
  have hc : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  constructor
  · intro h n hn
    have h1 := h n
    rw [if_pos hn, hout n hn, hin n hn] at h1
    have h0 := hbal n
    apply mul_left_cancel₀ hc
    linear_combination h1 - h0
  · intro h n
    by_cases hn : n ∈ A
    · rw [if_pos hn, hout n hn, hin n hn]
      linear_combination hbal n + (c - 1) * h n hn
    · rw [if_neg hn, hout' n hn, hin' n hn]
      linear_combination c * hbal n

theorem sW_rate (q : S → S → ℝ) (hq : IsRateMatrix q) (A : Set S) (c : ℝ) (hc0 : 0 < c) :
    IsRateMatrix (scaleWithin q A c) := by
  classical
  refine ⟨fun n k hnk => ?_, fun n => ?_⟩
  · unfold scaleWithin
    split_ifs
    · exact mul_nonneg hc0.le (hq.1 n k hnk)
    · exact hq.1 n k hnk
  · unfold scaleWithin; rw [hq.2]; simp

theorem sE_rate (q : S → S → ℝ) (hq : IsRateMatrix q) (A : Set S) (c : ℝ) (hc0 : 0 < c) :
    IsRateMatrix (scaleExit q A c) := by
  classical
  refine ⟨fun n k hnk => ?_, fun n => ?_⟩
  · unfold scaleExit
    split_ifs
    · exact mul_nonneg hc0.le (hq.1 n k hnk)
    · exact hq.1 n k hnk
  · unfold scaleExit; rw [hq.2]; simp

theorem sW_irred (q : S → S → ℝ) (A : Set S) (c : ℝ) (hc0 : 0 < c) (hirr : IsIrreducible q) :
    IsIrreducible (scaleWithin q A c) := by
  classical
  exact fun x y => rtg_mono (fun u v h => by
    unfold scaleWithin
    split_ifs
    · exact mul_pos hc0 h
    · exact h) (hirr x y)

theorem sE_irred (q : S → S → ℝ) (A : Set S) (c : ℝ) (hc0 : 0 < c) (hirr : IsIrreducible q) :
    IsIrreducible (scaleExit q A c) := by
  classical
  exact fun x y => rtg_mono (fun u v h => by
    unfold scaleExit
    split_ifs
    · exact mul_pos hc0 h
    · exact h) (hirr x y)

end Main

section Parts

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem part_one (q : S → S → ℝ) (hq : IsRateMatrix q) (hirr : IsIrreducible q)
    (π : S → ℝ) (hπ : IsEquilibriumDist q π)
    (A : Set S) (hA : A.Nonempty) (hAirr : IsIrreducible (truncatedRates q A))
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≠ 1) :
    List.TFAE
      [ IsPartialBalance π q A,
        IsTheEquilibriumDist (truncatedRates q A) (condDist π A),
        IsTheEquilibriumDist (scaleWithin q A c) π,
        IsTheEquilibriumDist (scaleExit q A c) (exitScaledDist π A c),
        ∀ p : A → ℝ, IsTheEquilibriumDist (truncatedRates q A) p →
          reversedRates p (truncatedRates q A) = truncatedRates (reversedRates π q) A ] := by
  classical
  have hpos := hπ.1
  have hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t := (fullBalance_iff π q).1 hπ.2.2
  obtain ⟨n0, hn0⟩ := hA
  have hZ : 0 < ∑' k : A, π k := by
    rw [tsum_sub _ π]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun s => if s ∈ A then π s else 0) ?_ (Finset.mem_univ n0))
    · simp only [hn0, if_true]; exact hpos _
    · intro s _
      split_ifs
      · exact (hpos s).le
      · exact le_rfl
  have hrateA : IsRateMatrix (truncatedRates q A) :=
    ⟨fun x y hxy => hq.1 _ _ (fun h => hxy (Subtype.ext h)), fun x => hq.2 _⟩
  have hipb := pb_iff q π A
  have hcond : FullBalance (condDist π A) (truncatedRates q A) ↔
      ∀ n ∈ A, π n * ∑ k, (if k ∈ A then q n k else 0) =
        ∑ k, (if k ∈ A then π k * q k n else 0) := by
    rw [fullBalance_iff]; exact cond_bal_iff q π _ hZ
  have hcondeq : IsEquilibriumDist (truncatedRates q A) (condDist π A) ↔
      IsPartialBalance π q A := by
    rw [hipb]
    constructor
    · intro h; exact hcond.1 h.2.2
    · intro h
      refine ⟨fun t => div_pos (hpos t) hZ, ?_, hcond.2 h⟩
      unfold condDist
      rw [tsum_div_const, div_self hZ.ne']
  have hesd : IsEquilibriumDist (scaleExit q A c) (exitScaledDist π A c) ↔
      IsPartialBalance π q A := by
    rw [esd_equil_iff π hpos _ c hc0 n0, sE_iff q π A c hc1 hbal, hipb]
    exact forall_congr' (fun n => imp_congr_right (fun _ => ipb_iff q π _ n (hbal n)))
  have hsw : IsEquilibriumDist (scaleWithin q A c) π ↔ IsPartialBalance π q A := by
    rw [hipb, ← sW_iff q π A c hc1 hbal, ← fullBalance_iff]
    constructor
    · intro h; exact h.2.2
    · intro h; exact ⟨hpos, hπ.2.1, h⟩
  tfae_have 1 → 2 := fun h => the_of_eq _ hrateA hAirr _ (hcondeq.2 h)
  tfae_have 2 → 1 := fun h => hcondeq.1 h.1
  tfae_have 1 → 3 := fun h => the_of_eq _ (sW_rate q hq A c hc0) (sW_irred q A c hc0 hirr) _
    (hsw.2 h)
  tfae_have 3 → 1 := fun h => hsw.1 h.1
  tfae_have 1 → 4 := fun h => the_of_eq _ (sE_rate q hq A c hc0) (sE_irred q A c hc0 hirr) _
    (hesd.2 h)
  tfae_have 4 → 1 := fun h => hesd.1 h.1
  tfae_have 2 → 5 := by
    intro h p hp
    obtain rfl := hp.2 _ h.1
    funext x y
    simp only [reversedRates, truncatedRates, condDist]
    have h1 := (hpos x).ne'
    have h2 := (hpos y).ne'
    have h3' := hZ.ne'
    field_simp
  tfae_have 5 → 1 := by
    intro h
    rw [hipb]
    intro n hn
    haveI : Nonempty A := ⟨⟨n, hn⟩⟩
    obtain ⟨p, hp⟩ := exists_the (truncatedRates q A) hrateA hAirr
    have hrev := h p hp
    have hpx := (hp.1.1 ⟨n, hn⟩).ne'
    have hπx := (hpos n).ne'
    have e : ∀ y : A, p y * truncatedRates q A y ⟨n, hn⟩ =
        (π y * q y n / π n) * p ⟨n, hn⟩ := by
      intro y
      have := congrFun (congrFun hrev ⟨n, hn⟩) y
      change p y * truncatedRates q A y ⟨n, hn⟩ / p ⟨n, hn⟩ =
        π y * q y n / π n at this
      rw [← this, div_mul_cancel₀ _ hpx]
    have hb := (fullBalance_iff _ _).1 hp.1.2.2 ⟨n, hn⟩
    rw [Finset.sum_congr rfl (fun y _ => e y), ← Finset.sum_mul] at hb
    have h2 : ∑ k : A, truncatedRates q A ⟨n, hn⟩ k =
        ∑ y : A, π y * q y n / π n := by
      apply mul_left_cancel₀ hpx; rw [hb]; ring
    have h3' : ∑ k : A, truncatedRates q A ⟨n, hn⟩ k =
        ∑ k, (if k ∈ A then q n k else 0) := fsum_sub _ (fun k => q n k)
    have h4 : ∑ y : A, π y * q y n / π n =
        (∑ k, (if k ∈ A then π k * q k n else 0)) / π n := by
      rw [fsum_sub _ (fun y => π y * q y n / π n), Finset.sum_div]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs
      · rfl
      · simp
    rw [h3', h4] at h2
    rw [h2]; field_simp
  tfae_finish

theorem part_two (q : S → S → ℝ) (hq : IsRateMatrix q) (hirr : IsIrreducible q)
    (π : S → ℝ) (hπ : IsEquilibriumDist q π)
    (A : Set S) (hA : A.Nonempty) (hC : Aᶜ.Nonempty) :
    IsPartialBalance π q A ↔
      ∃ μ : A → ℝ, IsTheStationaryDist (exitChain q A) μ ∧
        IsTheStationaryDist (entryChain q A) μ := by
  classical
  obtain ⟨a0, ha0⟩ := hA
  obtain ⟨k0, hk0⟩ := hC
  have hpos := hπ.1
  have hbal : ∀ t, π t * ∑ k, q t k = ∑ k, π k * q k t := (fullBalance_iff π q).1 hπ.2.2
  have htot : ∀ s, 0 < ∑ k, q s k := by
    intro s
    have : ∃ t, t ≠ s := by
      by_cases hs : s ∈ A
      · exact ⟨k0, fun h => hk0 (h ▸ hs)⟩
      · exact ⟨a0, fun h => hs (h ▸ ha0)⟩
    obtain ⟨t, hts⟩ := this
    rcases (hirr s t).cases_head with h | ⟨c, hc, -⟩
    · exact absurd h.symm hts
    · exact lt_of_lt_of_le hc (Finset.single_le_sum (f := fun k => q s k)
        (fun k _ => qnn q hq s k) (Finset.mem_univ c))
  have hrowA : ∀ k ∈ A, ∀ m,
      Summable (fun n => ((restrictMatrix (jumpProb q) A) ^ n) k m) :=
    fun k hk m => row_summable q π hq hpos htot hbal A
      (hk_of_path q (fun a b => 0 < q a b) (fun x y h => h) A (hirr k0 k) hk0 hk) m
  have hrowC : ∀ k ∈ Aᶜ, ∀ m,
      Summable (fun n => ((restrictMatrix (jumpProb q) Aᶜ) ^ n) k m) :=
    fun k hk m => row_summable q π hq hpos htot hbal Aᶜ
      (hk_of_path q (fun a b => 0 < q a b) (fun x y h => h) Aᶜ (hirr a0 k)
        (fun h => h ha0) hk) m
  obtain ⟨l, s1, hl, hs1, hsl, -⟩ := first_exit (fun a b => 0 < q a b) A (hirr a0 k0) hk0 ha0
  have hxs : 0 < exitRate q A s1 := by
    rw [exitRate_eq]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun k => if k ∈ A then (0 : ℝ) else q s1 k) ?_ (Finset.mem_univ l))
    · simp only [hl, if_false]; exact hsl
    · intro k _
      split_ifs
      · exact le_rfl
      · exact qnn q hq s1 k
  have hSigx : 0 < ∑ s, (if s ∈ A then π s * exitRate q A s else 0) := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun s => if s ∈ A then
      π s * exitRate q A s else 0) ?_ (Finset.mem_univ s1))
    · simp only [hs1, if_true]; exact mul_pos (hpos _) hxs
    · intro s _
      split_ifs
      · exact mul_nonneg (hpos s).le (exitRate_nonneg q hq A s)
      · exact le_rfl
  have hSigeq := sum_e_eq q π hbal A
  have hSige : 0 < ∑ s, dB q π A s := hSigeq ▸ hSigx
  have hSE := entry_stat q π hq hpos htot hbal A hrowA hrowC hSige
  have hSX := exit_stat q π hq hpos htot hbal A hrowA hrowC hSigx
  have hdB : ∀ t ∈ A, dB q π A t = ∑ l, (if l ∈ A then 0 else π l * q l t) := fun t ht => by
    unfold dB; rw [if_pos ht]
  have hTX : IsTheStationaryDist (exitChain q A) (fun t : A => π t * exitRate q A t /
      ∑ s, (if s ∈ A then π s * exitRate q A s else 0)) := by
    refine ⟨hSX, fun ν hν => ?_⟩
    obtain ⟨c, hc⟩ := exit_unique q hq hirr π hpos htot hbal A hrowA hrowC ν hν
    exact norm_eq A ν (fun s => π s * exitRate q A s) c hc hν.2.1 hSigx
  have hTE : IsTheStationaryDist (entryChain q A) (fun t : A => dB q π A t /
      ∑ s, dB q π A s) := by
    refine ⟨hSE, fun ν hν => ?_⟩
    obtain ⟨c, hc⟩ := entry_unique q hq hirr π hpos htot hbal A hrowA hrowC ν hν
    have hdBs : ∑ s, dB q π A s = ∑ s, (if s ∈ A then dB q π A s else 0) :=
      Finset.sum_congr rfl (fun s _ => by
        by_cases hs : s ∈ A
        · rw [if_pos hs]
        · rw [if_neg hs]; simp [dB, hs])
    have := norm_eq A ν (dB q π A) c hc hν.2.1 (hdBs ▸ hSige)
    rw [this, ← hdBs]
  rw [pb_iff q π A]
  constructor
  · intro hpb
    have hex : ∀ t ∈ A, dB q π A t = π t * exitRate q A t := fun t ht => by
      rw [hdB t ht, exitRate_eq]
      exact ((ipb_iff q π A t (hbal t)).2 (hpb t ht)).symm
    have hμeq : (fun t : A => dB q π A t / ∑ s, dB q π A s) = (fun t : A =>
        π t * exitRate q A t / ∑ s, (if s ∈ A then π s * exitRate q A s else 0)) := by
      funext t; rw [hSigeq, hex t t.2]
    refine ⟨_, hTX, ?_⟩
    rw [← hμeq]
    exact hTE
  · rintro ⟨μ, h1, h2⟩ n hn
    have e1 := h1.2 _ hSX
    have e2 := h2.2 _ hSE
    have h' := congrFun (e2.trans e1.symm) ⟨n, hn⟩
    change dB q π A n / (∑ s, dB q π A s) =
      π n * exitRate q A n / ∑ s, (if s ∈ A then π s * exitRate q A s else 0) at h'
    rw [hSigeq] at h'
    have h'' := (div_left_inj' hSigx.ne').1 h'
    rw [hdB n hn, exitRate_eq] at h''
    exact (ipb_iff q π A n (hbal n)).1 h''.symm

end Parts

end KPB3d8

open KellyReversibility.PartialBalance KellyStochasticNetworks in
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : IsRateMatrix q) (hirr : IsIrreducible q)
    (π : S → ℝ) (hπ : IsEquilibriumDist q π)
    (A : Set S) (hA : A.Nonempty) (hAirr : IsIrreducible (truncatedRates q A))
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≠ 1) :
    List.TFAE
      [ IsPartialBalance π q A,
        IsTheEquilibriumDist (truncatedRates q A) (condDist π A),
        IsTheEquilibriumDist (scaleWithin q A c) π,
        IsTheEquilibriumDist (scaleExit q A c) (exitScaledDist π A c),
        ∀ p : A → ℝ, IsTheEquilibriumDist (truncatedRates q A) p →
          reversedRates p (truncatedRates q A) = truncatedRates (reversedRates π q) A ] ∧
    (Aᶜ.Nonempty →
      (IsPartialBalance π q A ↔
        ∃ μ : A → ℝ, IsTheStationaryDist (exitChain q A) μ ∧
          IsTheStationaryDist (entryChain q A) μ)) := by
  exact ⟨KPB3d8.part_one q hq hirr π hπ A hA hAirr c hc0 hc1,
    fun hC => KPB3d8.part_two q hq hirr π hπ A hA hC⟩
