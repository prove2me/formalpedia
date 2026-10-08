-- Prove2me | solution 1 for KellyReversibility.PartialBalance.spatial_partial_balance_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:51:49.887259+00:00
-- url     : https://prove2.me/submissions/66e41f96-db7a-4a7e-b8c3-b61a4ab3202a

import Mathlib
import Definitions.Def_KellyReversibility_PartialBalance_Core
import Definitions.Def_KellyReversibility_PartialBalance_Spatial

set_option autoImplicit false

namespace KPB3e7

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

end Spatial

section Site

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → Type*}
  [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]

theorem cond_eq (π : (∀ i, N i) → ℝ) (j : ι) (n : ∀ i, N i) (a : N j) :
    condProb π j (update n j a) = π (update n j a) / ∑ m, π (update n j m) := by
  unfold condProb; simp only [update_idem]

theorem hZ (π : (∀ i, N i) → ℝ) (hpos : ∀ s, 0 < π s) (j : ι) (n : ∀ i, N i) :
    0 < ∑ m, π (update n j m) :=
  Finset.sum_pos (fun m _ => hpos _) ⟨n j, Finset.mem_univ _⟩

theorem pb_iff (π : (∀ i, N i) → ℝ) (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι) :
    SitePartialBalance π q j ↔ ∀ (n : ∀ i, N i) (x : N j),
      π (update n j x) * ∑ y, frozenRates q j n x y =
        ∑ y, π (update n j y) * frozenRates q j n y x := by
  constructor
  · intro h n x
    have := h (update n j x)
    simpa only [frozenRates, update_idem] using this
  · intro h n
    have := h n (n j)
    simpa only [frozenRates, update_eq_self] using this

theorem cond_dist (π : (∀ i, N i) → ℝ) (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι)
    (hpos : ∀ s, 0 < π s) (h : SitePartialBalance π q j) (n : ∀ i, N i) :
    IsEquilibriumDist (frozenRates q j n) (fun a => condProb π j (update n j a)) := by
  have hz := hZ π hpos j n
  refine ⟨fun a => ?_, ?_, ?_⟩
  · show 0 < condProb π j (update n j a)
    rw [cond_eq]; exact div_pos (hpos _) hz
  · rw [tsum_fintype]; simp only [cond_eq]; rw [← Finset.sum_div, div_self hz.ne']
  · rw [fullBalance_iff]; intro x
    simp only [cond_eq, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [(pb_iff π q j).1 h n x]

theorem site_iff (j : ι) (n k : ∀ i, N i) :
    (∀ i, i ≠ j → n i = k i) ↔ ∃ m, k = update n j m := by
  constructor
  · intro h
    refine ⟨k j, funext fun i => ?_⟩
    by_cases hi : i = j
    · subst hi; simp
    · rw [update_of_ne hi]; exact (h i hi).symm
  · rintro ⟨m, rfl⟩ i hi
    rw [update_of_ne hi]

theorem sum_site (j : ι) (n : ∀ i, N i) (f : (∀ i, N i) → ℝ) (P : (∀ i, N i) → Prop)
    {dP : DecidablePred P} (hP : ∀ k, P k ↔ ∃ m, k = update n j m) :
    ∑ k, (if P k then f k else 0) = ∑ m, f (update n j m) := by
  rw [← Finset.sum_filter]
  have e : Finset.univ.filter P = Finset.univ.image (update n j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hP]
    constructor <;> rintro ⟨m, hm⟩ <;> exact ⟨m, hm.symm⟩
  rw [e, Finset.sum_image (fun a _ b _ h => update_injective n j h)]

theorem sum_scaled_out (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι) (c : ℝ) (n : ∀ i, N i) :
    ∑ k, siteScaled q j c n k = ∑ k, q n k + (c - 1) * ∑ m, q n (update n j m) := by
  have hpt : ∀ k, siteScaled q j c n k =
      q n k + (c - 1) * (if (∀ i, i ≠ j → n i = k i) then q n k else 0) := by
    intro k
    simp only [siteScaled]
    split_ifs with h1 h2 <;>
      first | ring1 | (exfalso; exact h2 h1) | (exfalso; exact h1 h2)
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_site j n (fun k => q n k) _ (site_iff j n)]

theorem sum_scaled_in (π : (∀ i, N i) → ℝ) (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι) (c : ℝ)
    (n : ∀ i, N i) :
    ∑ k, π k * siteScaled q j c k n =
      ∑ k, π k * q k n + (c - 1) * ∑ m, π (update n j m) * q (update n j m) n := by
  have hpt : ∀ k, π k * siteScaled q j c k n =
      π k * q k n + (c - 1) * (if (∀ i, i ≠ j → n i = k i) then π k * q k n else 0) := by
    intro k
    have hiff : (∀ i, i ≠ j → k i = n i) ↔ (∀ i, i ≠ j → n i = k i) :=
      ⟨fun h i hi => (h i hi).symm, fun h i hi => (h i hi).symm⟩
    simp only [siteScaled]
    by_cases h1 : ∀ i, i ≠ j → k i = n i
    · rw [if_pos h1, if_pos (hiff.1 h1)]; ring
    · rw [if_neg h1, if_neg (fun h => h1 (hiff.2 h))]; ring
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_site j n (fun k => π k * q k n) _ (site_iff j n)]

theorem scaled_iff (π : (∀ i, N i) → ℝ) (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι) (c : ℝ)
    (hc1 : c ≠ 1) (hbal : ∀ s, π s * ∑ k, q s k = ∑ k, π k * q k s) :
    (∀ s, π s * ∑ k, siteScaled q j c s k = ∑ k, π k * siteScaled q j c k s) ↔
      SitePartialBalance π q j := by
  have hc : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  constructor
  · intro h n
    have h1 := h n
    rw [sum_scaled_out, sum_scaled_in] at h1
    have h0 := hbal n
    apply mul_left_cancel₀ hc
    linear_combination h1 - h0
  · intro h n
    rw [sum_scaled_out, sum_scaled_in]
    linear_combination hbal n + (c - 1) * h n

theorem scaled_rate (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι) (c : ℝ) (hq : IsRateMatrix q)
    (hc0 : 0 < c) : IsRateMatrix (siteScaled q j c) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · simp only [siteScaled]
    split_ifs
    · exact mul_nonneg hc0.le (hq.1 a b hab)
    · exact hq.1 a b hab
  · simp only [siteScaled]
    split_ifs <;> simp [hq.2 a]

theorem scaled_irred (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι) (c : ℝ) (hirr : IsIrreducible q)
    (hc0 : 0 < c) : IsIrreducible (siteScaled q j c) := fun a b =>
  rtg_mono (fun x y h => by
    simp only [siteScaled]
    split_ifs
    · exact mul_pos hc0 h
    · exact h) (hirr a b)

end Site

end KPB3e7

open Function KellyReversibility.PartialBalance KellyStochasticNetworks in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → Type*} [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]
    (G : SimpleGraph ι) (q : (∀ i, N i) → (∀ i, N i) → ℝ) (hsp : IsSpatialProcess G q)
    (π : (∀ i, N i) → ℝ) (hπ : IsEquilibriumDist q π)
    (j : ι) (c : ℝ) (hc0 : 0 < c) (hc1 : c ≠ 1) :
    List.TFAE
      [ SitePartialBalance π q j,
        ∀ n : (∀ i, N i),
          IsTheEquilibriumDist (frozenRates q j n) (fun a => condProb π j (update n j a)),
        IsTheEquilibriumDist (siteScaled q j c) π,
        ∀ (n : ∀ i, N i) (p : N j → ℝ), IsTheEquilibriumDist (frozenRates q j n) p →
          reversedRates p (frozenRates q j n) = frozenRates (reversedRates π q) j n ] := by
  have hrate := hsp.1
  have hirr3 := hsp.2.2.2
  have hpos := hπ.1
  have hbal : ∀ s, π s * ∑ k, q s k = ∑ k, π k * q k s :=
    (KPB3e7.fullBalance_iff π q).1 hπ.2.2
  have hirr : IsIrreducible q := KPB3e7.full_irred q hirr3
  tfae_have 1 → 2 := fun h n =>
    KPB3e7.the_of_eq _ (KPB3e7.frozen_rate q hrate j n) (KPB3e7.frozen_irred q hirr3 j n) _
      (KPB3e7.cond_dist π q j hpos h n)
  tfae_have 2 → 1 := by
    intro h
    rw [KPB3e7.pb_iff]
    intro n x
    have hb := (KPB3e7.fullBalance_iff _ _).1 (h n).1.2.2 x
    simp only [KPB3e7.cond_eq, div_mul_eq_mul_div, ← Finset.sum_div] at hb
    exact (div_left_inj' (KPB3e7.hZ π hpos j n).ne').1 hb
  tfae_have 1 → 3 := fun h =>
    KPB3e7.the_of_eq _ (KPB3e7.scaled_rate q j c hrate hc0) (KPB3e7.scaled_irred q j c hirr hc0) π
      ⟨hpos, hπ.2.1, (KPB3e7.fullBalance_iff _ _).2 ((KPB3e7.scaled_iff π q j c hc1 hbal).2 h)⟩
  tfae_have 3 → 1 := fun h =>
    (KPB3e7.scaled_iff π q j c hc1 hbal).1 ((KPB3e7.fullBalance_iff _ _).1 h.1.2.2)
  tfae_have 1 → 4 := by
    intro h n p hp
    obtain rfl := hp.2 _ (KPB3e7.cond_dist π q j hpos h n)
    have hz := KPB3e7.hZ π hpos j n
    funext x y
    simp only [reversedRates, frozenRates, KPB3e7.cond_eq]
    have h1 := (hpos (update n j x)).ne'
    have h2 := (hpos (update n j y)).ne'
    field_simp
  tfae_have 4 → 1 := by
    intro h
    rw [KPB3e7.pb_iff]
    intro n x
    have : Nonempty (N j) := ⟨n j⟩
    obtain ⟨p, hp⟩ := KPB3e7.exists_the (frozenRates q j n) (KPB3e7.frozen_rate q hrate j n)
      (KPB3e7.frozen_irred q hirr3 j n)
    have hrev := h n p hp
    have hpx := (hp.1.1 x).ne'
    have hπx := (hpos (update n j x)).ne'
    have e : ∀ y, p y * frozenRates q j n y x =
        (π (update n j y) * frozenRates q j n y x / π (update n j x)) * p x := by
      intro y
      have := congrFun (congrFun hrev x) y
      change p y * frozenRates q j n y x / p x =
        π (update n j y) * frozenRates q j n y x / π (update n j x) at this
      rw [← this, div_mul_cancel₀ _ hpx]
    have hb := (KPB3e7.fullBalance_iff _ _).1 hp.1.2.2 x
    have h1 : p x * ∑ y, frozenRates q j n x y =
        p x * ((∑ y, π (update n j y) * frozenRates q j n y x) / π (update n j x)) := by
      rw [hb, Finset.sum_congr rfl (fun y _ => e y), ← Finset.sum_mul, ← Finset.sum_div, mul_comm]
    rw [mul_left_cancel₀ hpx h1]
    field_simp
  tfae_finish
