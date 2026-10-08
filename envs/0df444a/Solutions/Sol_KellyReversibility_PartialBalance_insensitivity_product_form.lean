-- Prove2me | solution 1 for KellyReversibility.PartialBalance.insensitivity_product_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:28:46.784813+00:00
-- url     : https://prove2.me/submissions/de92fb9c-9559-469e-9bfc-fe57536ca501

import Mathlib
import Definitions.Def_KellyReversibility_PartialBalance_Core
import Definitions.Def_KellyReversibility_PartialBalance_Spatial
import Definitions.Def_KellyReversibility_PartialBalance_Insensitivity

set_option autoImplicit false

namespace KPB6e7

open Function KellyReversibility.PartialBalance KellyStochasticNetworks

/-! ## Generic finite Markov chain facts -/

theorem fullBalance_iff {S : Type*} [Fintype S] (π : S → ℝ) (q : S → S → ℝ) :
    FullBalance π q ↔ ∀ j, π j * ∑ k, q j k = ∑ k, π k * q k j := by
  simp [FullBalance, tsum_fintype]

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


/-! ## Spatial-process facts -/

section Spatial

variable {ι : Type*} [DecidableEq ι] {X N : ι → Type*}

theorem rtg_mono {α : Type*} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

theorem frozen_rate (q : (∀ i, X i) → (∀ i, X i) → ℝ) (hq : IsRateMatrix q) (j : ι)
    (x : ∀ i, X i) : IsRateMatrix (frozenRates q j x) :=
  ⟨fun a b hab => hq.1 _ _ (fun h => hab (update_injective x j h)), fun a => hq.2 _⟩

theorem frozen_irred (q : (∀ i, X i) → (∀ i, X i) → ℝ)
    (h3 : ∀ (j : ι) (m : X j) (n : ∀ i, X i),
      Relation.ReflTransGen
        (fun a b : (∀ i, X i) => (∃ m' : X j, b = update a j m') ∧ 0 < q a b) n (update n j m))
    (j : ι) (x : ∀ i, X i) : IsIrreducible (frozenRates q j x) := by
  intro a b
  have key : ∀ v, Relation.ReflTransGen
      (fun a b : (∀ i, X i) => (∃ m' : X j, b = update a j m') ∧ 0 < q a b) (update x j a) v →
      v = update x j (v j) ∧ Relation.ReflTransGen (fun u w => 0 < frozenRates q j x u w) a (v j) := by
    intro v hv
    induction hv with
    | refl =>
      refine ⟨by simp, ?_⟩
      rw [update_self]
    | @tail u w _ hst ih =>
      obtain ⟨⟨m', hm'⟩, hpos⟩ := hst
      obtain ⟨hb, hr⟩ := ih
      subst hm'
      refine ⟨?_, ?_⟩
      · simp only [update_self]
        conv_lhs => rw [hb]
        rw [update_idem]
      rw [update_self]
      refine hr.tail ?_
      show 0 < q (update x j (u j)) (update x j m')
      rw [hb, update_idem] at hpos
      exact hpos
  have := (key _ (h3 j b (update x j a))).2
  simpa using this

theorem full_irred [Fintype ι] (q : (∀ i, X i) → (∀ i, X i) → ℝ)
    (h3 : ∀ (j : ι) (m : X j) (n : ∀ i, X i),
      Relation.ReflTransGen
        (fun a b : (∀ i, X i) => (∃ m' : X j, b = update a j m') ∧ 0 < q a b) n (update n j m)) :
    IsIrreducible q := by
  intro x x'
  have key : ∀ T : Finset ι, Relation.ReflTransGen (fun a b => 0 < q a b) x
      (fun i => if i ∈ T then x' i else x i) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using (Relation.ReflTransGen.refl : Relation.ReflTransGen (fun a b => 0 < q a b) x x)
    | insert i T hi ih =>
      have e : (fun k => if k ∈ insert i T then x' k else x k) =
          update (fun k => if k ∈ T then x' k else x k) i (x' i) := by
        funext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk, update_of_ne hk]
      rw [e]
      exact ih.trans (rtg_mono (fun a b h => h.2) (h3 i (x' i) _))
  simpa using key Finset.univ

theorem reduce_update (f : ∀ i, X i → N i) (x : ∀ i, X i) (j : ι) (y : X j) :
    reduce f (update x j y) = update (reduce f x) j (f j y) := by
  funext i
  by_cases h : i = j
  · subst h; simp [reduce]
  · simp [reduce, update_of_ne h]

theorem prod_update [Fintype ι] (P : ∀ i, X i → ℝ) (x : ∀ i, X i) (j : ι) (y : X j) :
    ∏ i, P i (update x j y i) = P j y * ∏ i ∈ Finset.univ.erase j, P i (x i) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun i => P i (update x j y i)) (Finset.mem_univ j)]
  simp only [update_self]
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [update_of_ne (Finset.ne_of_mem_erase hi)]

theorem sum_single_site [Fintype ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (x : ∀ i, X i) (g : (∀ i, X i) → ℝ) (hg0 : g x = 0)
    (hg : ∀ k, g k ≠ 0 → ∃ j, ∃ m : X j, k = update x j m) :
    ∑ k, g k = ∑ j, ∑ m : X j, g (update x j m) := by
  rw [show (∑ j, ∑ m : X j, g (update x j m)) = ∑ jm : (Σ j, X j), g (update x jm.1 jm.2) from
    (Fintype.sum_sigma (fun jm : (Σ j, X j) => g (update x jm.1 jm.2))).symm]
  symm
  refine Finset.sum_bij_ne_zero (fun jm _ _ => update x jm.1 jm.2) (fun _ _ _ => Finset.mem_univ _)
    ?_ ?_ (fun _ _ _ => rfl)
  · rintro ⟨j, m⟩ - h1 ⟨j', m'⟩ - h2 heq
    simp only at heq h1 h2
    by_cases hj : j = j'
    · subst hj
      have := update_injective x j heq
      subst this; rfl
    · exfalso
      have hm : m = x j := by
        have := congrFun heq j
        rw [update_self, update_of_ne hj] at this
        exact this
      apply h1; rw [hm, update_eq_self]; exact hg0
  · intro k _ hk
    obtain ⟨j, m, rfl⟩ := hg k hk
    exact ⟨⟨j, m⟩, Finset.mem_univ _, hk, rfl⟩

theorem full_of_site [Fintype ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (q : (∀ i, X i) → (∀ i, X i) → ℝ)
    (h1 : ∀ n n' : (∀ i, X i), q n n' ≠ 0 → ∃ (j : ι) (m : X j), n' = update n j m)
    (hq0 : ∀ x, q x x = 0) (π : (∀ i, X i) → ℝ) (hsite : ∀ j, SitePartialBalance π q j) :
    ∀ x, π x * ∑ k, q x k = ∑ k, π k * q k x := by
  intro x
  have e1 := sum_single_site x (fun k => q x k) (hq0 x) (fun k hk => h1 x k hk)
  have e2 := sum_single_site x (fun k => π k * q k x) (by simp [hq0]) (by
    intro k hk
    have : q k x ≠ 0 := fun h => hk (by simp [h])
    obtain ⟨j, m, hm⟩ := h1 k x this
    refine ⟨j, k j, ?_⟩
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · rw [update_of_ne hij, hm, update_of_ne hij])
  rw [e1, e2, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => hsite j x)

theorem sum_prod_form [Fintype ι] [∀ i, Fintype (X i)] [∀ i, Fintype (N i)]
    [∀ i, DecidableEq (N i)] (f : ∀ i, X i → N i) (P : ∀ i, X i → ℝ)
    (hP1 : ∀ (i : ι) (m : N i), ∑ y ∈ Finset.univ.filter (fun y => f i y = m), P i y = 1)
    (πn : (∀ i, N i) → ℝ) :
    ∑ x, πn (reduce f x) * ∏ i, P i (x i) = ∑ n, πn n := by
  rw [← Finset.sum_fiberwise Finset.univ (reduce f) (fun x => πn (reduce f x) * ∏ i, P i (x i))]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hfil : Finset.univ.filter (fun x => reduce f x = n) =
      Fintype.piFinset (fun i => Finset.univ.filter (fun y => f i y = n i)) := by
    ext x; simp [Fintype.mem_piFinset, reduce, funext_iff]
  calc ∑ x ∈ Finset.univ.filter (fun x => reduce f x = n), πn (reduce f x) * ∏ i, P i (x i)
      = ∑ x ∈ Fintype.piFinset (fun i => Finset.univ.filter (fun y => f i y = n i)),
          πn n * ∏ i, P i (x i) := by
        rw [← hfil]
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [(Finset.mem_filter.1 hx).2]
    _ = πn n * ∏ i, ∑ y ∈ Finset.univ.filter (fun y => f i y = n i), P i y := by
        rw [← Finset.mul_sum, Finset.prod_univ_sum]
    _ = πn n := by simp [hP1]

end Spatial

/-! ## Cut argument (pure finite algebra) -/

theorem cut {T M : Type*} [Fintype T] [Fintype M] [DecidableEq M] (g : T → M)
    (Q : T → T → ℝ) (p P : T → ℝ)
    (hbal : ∀ y, p y * ∑ z, Q y z = ∑ z, p z * Q z y)
    (hfac : ∀ y, p y = (∑ y' ∈ Finset.univ.filter (fun y' => g y' = g y), p y') * P y) (a : M) :
    (∑ y ∈ Finset.univ.filter (fun y => g y = a), p y) *
        ∑ b, ∑ y ∈ Finset.univ.filter (fun y => g y = a),
          P y * ∑ z ∈ Finset.univ.filter (fun z => g z = b), Q y z
      = ∑ b, (∑ y ∈ Finset.univ.filter (fun y => g y = b), p y) *
        ∑ y ∈ Finset.univ.filter (fun y => g y = b),
          P y * ∑ z ∈ Finset.univ.filter (fun z => g z = a), Q y z := by
  have hfac' : ∀ m, ∀ y ∈ Finset.univ.filter (fun y => g y = m),
      p y = (∑ y' ∈ Finset.univ.filter (fun y' => g y' = m), p y') * P y := by
    intro m y hy
    have hy' : g y = m := (Finset.mem_filter.1 hy).2
    rw [hfac y, hy']
  have fib : ∀ F : T → ℝ, ∑ b, ∑ z ∈ Finset.univ.filter (fun z => g z = b), F z = ∑ z, F z :=
    fun F => Finset.sum_fiberwise _ _ _
  have common : ∑ y ∈ Finset.univ.filter (fun y => g y = a), ∑ z, p z * Q z y
      = ∑ z, p z * ∑ y ∈ Finset.univ.filter (fun y => g y = a), Q z y := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun z _ => (Finset.mul_sum _ _ _).symm)
  have lhs : (∑ y ∈ Finset.univ.filter (fun y => g y = a), p y) *
        ∑ b, ∑ y ∈ Finset.univ.filter (fun y => g y = a),
          P y * ∑ z ∈ Finset.univ.filter (fun z => g z = b), Q y z
      = ∑ z, p z * ∑ y ∈ Finset.univ.filter (fun y => g y = a), Q z y := by
    rw [Finset.sum_comm, ← common, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have e : ∑ b, P y * ∑ z ∈ Finset.univ.filter (fun z => g z = b), Q y z = P y * ∑ z, Q y z := by
      rw [← Finset.mul_sum, fib]
    rw [e, ← hbal y, hfac' a y hy]; ring
  rw [lhs]
  symm
  calc ∑ b, (∑ y ∈ Finset.univ.filter (fun y => g y = b), p y) *
        ∑ y ∈ Finset.univ.filter (fun y => g y = b),
          P y * ∑ z ∈ Finset.univ.filter (fun z => g z = a), Q y z
      = ∑ b, ∑ z ∈ Finset.univ.filter (fun z => g z = b),
          p z * ∑ y ∈ Finset.univ.filter (fun y => g y = a), Q z y := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun z hz => ?_)
        rw [hfac' b z hz]; ring
    _ = _ := fib _


/-! ## Reduced process -/

section Reduced

variable {ι : Type*} [DecidableEq ι] {X N : ι → Type*} [∀ i, Fintype (X i)]
  [∀ i, DecidableEq (N i)]

theorem red_eq (q : (∀ i, X i) → (∀ i, X i) → ℝ) (f : ∀ i, X i → N i) (P : ∀ i, X i → ℝ)
    (s : ∀ i, N i → X i) (hs : ∀ (i : ι) (m : N i), f i (s i m) = m) (j : ι)
    (hA1 : RatesFactorThrough q f j) (x : ∀ i, X i) (a b : N j) :
    reducedRate q f P s (update (reduce f x) j a) j b =
      if b = a then 0 else
        ∑ y ∈ Finset.univ.filter (fun y => f j y = a),
          P j y * ∑ z ∈ Finset.univ.filter (fun z => f j z = b), frozenRates q j x y z := by
  unfold reducedRate
  simp only [update_self]
  split_ifs with h
  · rfl
  · refine Finset.sum_congr rfl (fun y _ => ?_)
    congr 1
    refine Finset.sum_congr rfl (fun z _ => ?_)
    unfold frozenRates
    have := hA1 (update (fun i => s i (update (reduce f x) j a i)) j y) (update x j y) z
      (by simp) (by
        intro i hi
        simp [update_of_ne hi, hs, reduce])
    simpa [update_idem] using this

theorem site_balance [Fintype ι] [∀ i, DecidableEq (X i)] [∀ i, Fintype (N i)]
    (q : (∀ i, X i) → (∀ i, X i) → ℝ) (hrate : IsRateMatrix q)
    (h3 : ∀ (j : ι) (m : X j) (n : ∀ i, X i),
      Relation.ReflTransGen
        (fun a b : (∀ i, X i) => (∃ m' : X j, b = update a j m') ∧ 0 < q a b) n (update n j m))
    (f : ∀ i, X i → N i) (s : ∀ i, N i → X i) (hs : ∀ (i : ι) (m : N i), f i (s i m) = m)
    (P : ∀ i, X i → ℝ) (hPpos : ∀ (i : ι) (y : X i), 0 < P i y)
    (j : ι) (hA1 : RatesFactorThrough q f j) (hA2 : SufficientReduction q f P j)
    (πn : (∀ i, N i) → ℝ) (hπn_pos : ∀ n, 0 < πn n)
    (hpb : ∀ n : ∀ i, N i, πn n * (∑ m : N j, reducedRate q f P s n j m) =
        ∑ m : N j, πn (update n j m) * reducedRate q f P s (update n j m) j (n j)) :
    SitePartialBalance (fun x => πn (reduce f x) * ∏ i, P i (x i)) q j := by
  intro x
  haveI : Nonempty (X j) := ⟨x j⟩
  obtain ⟨p, hp⟩ := exists_the _ (frozen_rate q hrate j x) (frozen_irred q h3 j x)
  have hfac := hA2 x p hp
  have hbal := (fullBalance_iff _ _).1 hp.1.2.2
  have hppos := hp.1.1
  let C : N j → Finset (X j) := fun m => Finset.univ.filter (fun y => f j y = m)
  let c : N j → ℝ := fun m => ∑ y ∈ C m, p y
  let R' : N j → N j → ℝ := fun a b => ∑ y ∈ C a, P j y * ∑ z ∈ C b, frozenRates q j x y z
  let Rd : N j → N j → ℝ := fun a b => reducedRate q f P s (update (reduce f x) j a) j b
  let d : N j → ℝ := fun m => πn (update (reduce f x) j m)
  have hRd : ∀ a b, Rd a b = if b = a then 0 else R' a b :=
    fun a b => red_eq q f P s hs j hA1 x a b
  have hcut : ∀ a, c a * ∑ b, R' a b = ∑ b, c b * R' b a :=
    fun a => cut (f j) _ p (P j) hbal hfac a
  have hcpos : ∀ m, 0 < c m := by
    intro m
    have hmem : s j m ∈ C m := Finset.mem_filter.2 ⟨Finset.mem_univ _, hs j m⟩
    exact lt_of_lt_of_le (hppos _) (Finset.single_le_sum (fun y _ => (hppos y).le) hmem)
  have hsum1 : ∀ a, ∑ b, Rd a b = ∑ b, R' a b - R' a a := by
    intro a
    have e : ∀ b, Rd a b = R' a b - if b = a then R' a b else 0 := by
      intro b; rw [hRd]; split_ifs <;> ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hsum2 : ∀ a, ∑ b, c b * Rd b a = ∑ b, c b * R' b a - c a * R' a a := by
    intro a
    have e : ∀ b, c b * Rd b a = c b * R' b a - if a = b then c b * R' b a else 0 := by
      intro b; rw [hRd]; split_ifs <;> ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hcbal : ∀ a, c a * ∑ b, Rd a b = ∑ b, c b * Rd b a := by
    intro a
    rw [hsum1, hsum2, mul_sub, hcut a]
  have hd : ∀ a, d a * ∑ b, Rd a b = ∑ b, d b * Rd b a := by
    intro a
    have := hpb (update (reduce f x) j a)
    simp only [update_idem, update_self] at this
    exact this
  have hfrz : ∀ y z, f j y ≠ f j z → 0 ≤ frozenRates q j x y z :=
    fun y z h => (frozen_rate q hrate j x).1 y z (fun e => h (e ▸ rfl))
  have hR'nn : ∀ a b, a ≠ b → 0 ≤ R' a b := by
    intro a b hab
    refine Finset.sum_nonneg (fun y hy => mul_nonneg (hPpos j y).le
      (Finset.sum_nonneg (fun z hz => hfrz y z ?_)))
    rw [(Finset.mem_filter.1 hy).2, (Finset.mem_filter.1 hz).2]; exact hab
  have hRdrate : IsRateMatrix Rd := by
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [hRd, if_neg (Ne.symm hab)]; exact hR'nn a b hab
    · rw [hRd, if_pos rfl]
  have hRdirr : IsIrreducible Rd := by
    have map : ∀ y z, Relation.ReflTransGen (fun u v => 0 < frozenRates q j x u v) y z →
        Relation.ReflTransGen (fun u v => 0 < Rd u v) (f j y) (f j z) := by
      intro y z h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | @tail u v _ hst ih =>
        by_cases huv : f j u = f j v
        · rw [← huv]; exact ih
        · refine ih.tail ?_
          rw [hRd, if_neg (Ne.symm huv)]
          have hvmem : v ∈ C (f j v) := Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
          have humem : u ∈ C (f j u) := Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
          calc 0 < P j u * frozenRates q j x u v := mul_pos (hPpos j u) hst
            _ ≤ P j u * ∑ z ∈ C (f j v), frozenRates q j x u z :=
                mul_le_mul_of_nonneg_left
                  (Finset.single_le_sum (f := fun z => frozenRates q j x u z)
                    (fun z hz => hfrz u z (by rw [(Finset.mem_filter.1 hz).2]; exact huv)) hvmem)
                  (hPpos j u).le
            _ ≤ R' (f j u) (f j v) :=
                Finset.single_le_sum (f := fun y => P j y * ∑ z ∈ C (f j v), frozenRates q j x y z)
                  (fun y hy => mul_nonneg (hPpos j y).le (Finset.sum_nonneg (fun z hz => hfrz y z (by
                    rw [(Finset.mem_filter.1 hy).2, (Finset.mem_filter.1 hz).2]; exact huv))))
                  humem
    intro a b
    have := map (s j a) (s j b) (frozen_irred q h3 j x (s j a) (s j b))
    rwa [hs, hs] at this
  obtain ⟨K, hK⟩ := uniq_of_irred Rd hRdrate hRdirr c d hcpos hcbal hd
  have hform : ∀ y, πn (reduce f (update x j y)) * ∏ i, P i (update x j y i) =
      K * (∏ i ∈ Finset.univ.erase j, P i (x i)) * p y := by
    intro y
    rw [reduce_update, prod_update, hfac y]
    have := hK (f j y)
    change πn (update (reduce f x) j (f j y)) =
      K * ∑ y' ∈ Finset.univ.filter (fun y' => f j y' = f j y), p y' at this
    rw [this]; ring
  have hx : πn (reduce f x) * ∏ i, P i (x i) =
      K * (∏ i ∈ Finset.univ.erase j, P i (x i)) * p (x j) := by
    have := hform (x j); rwa [update_eq_self] at this
  have hb := hbal (x j)
  simp only [frozenRates, update_eq_self] at hb
  beta_reduce
  rw [hx]
  simp only [hform]
  rw [mul_assoc, hb, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by ring)

end Reduced

end KPB6e7

open Function KellyReversibility.PartialBalance in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X N : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]
    (q : (∀ i, X i) → (∀ i, X i) → ℝ) (hsp : IsSpatialProcess (⊤ : SimpleGraph ι) q)
    (f : ∀ i, X i → N i) (s : ∀ i, N i → X i) (hs : ∀ (i : ι) (m : N i), f i (s i m) = m)
    (P : ∀ i, X i → ℝ) (hP0 : ∀ (i : ι) (y : X i), 0 ≤ P i y)
    (hP1 : ∀ (i : ι) (m : N i), ∑ y ∈ Finset.univ.filter (fun y => f i y = m), P i y = 1)
    (hA1 : ∀ j : ι, RatesFactorThrough q f j) (hA2 : ∀ j : ι, SufficientReduction q f P j)
    (πn : (∀ i, N i) → ℝ) (hπn_pos : ∀ n, 0 < πn n) (hπn_sum : ∑ n, πn n = 1)
    (hpb : ∀ (j : ι) (n : ∀ i, N i),
      πn n * (∑ m : N j, reducedRate q f P s n j m) =
        ∑ m : N j, πn (update n j m) * reducedRate q f P s (update n j m) j (n j)) :
    IsTheEquilibriumDist q (fun x => πn (reduce f x) * ∏ i, P i (x i)) ∧
      ∀ j : ι, SitePartialBalance (fun x => πn (reduce f x) * ∏ i, P i (x i)) q j := by
  obtain ⟨hrate, h1, -, h3⟩ := hsp
  have hne : Nonempty (∀ i, N i) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hπn_sum
  have hPpos : ∀ (i : ι) (y : X i), 0 < P i y := by
    intro i y
    obtain ⟨n₀⟩ := hne
    haveI : Nonempty (X i) := ⟨y⟩
    obtain ⟨p, hp⟩ := KPB6e7.exists_the _ (KPB6e7.frozen_rate q hrate i (fun k => s k (n₀ k)))
      (KPB6e7.frozen_irred q h3 i (fun k => s k (n₀ k)))
    have h := hA2 i _ p hp y
    have hpy := hp.1.1 y
    rcases (hP0 i y).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', mul_zero] at h; linarith
  have hsite : ∀ j, SitePartialBalance (fun x => πn (reduce f x) * ∏ i, P i (x i)) q j :=
    fun j => KPB6e7.site_balance q hrate h3 f s hs P hPpos j (hA1 j) (hA2 j) πn hπn_pos (hpb j)
  have hpos : ∀ x : (∀ i, X i), 0 < πn (reduce f x) * ∏ i, P i (x i) :=
    fun x => mul_pos (hπn_pos _) (Finset.prod_pos (fun i _ => hPpos i (x i)))
  refine ⟨KPB6e7.the_of_eq q hrate (KPB6e7.full_irred q h3) _ ⟨hpos, ?_, ?_⟩, hsite⟩
  · simp only [tsum_fintype]
    rw [KPB6e7.sum_prod_form f P hP1 πn, hπn_sum]
  · rw [KPB6e7.fullBalance_iff]
    exact KPB6e7.full_of_site q h1 hrate.2 _ hsite
