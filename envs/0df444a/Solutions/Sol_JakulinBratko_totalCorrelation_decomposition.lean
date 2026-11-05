-- Prove2me | solution 1 for JakulinBratko.totalCorrelation_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-05T03:03:49.151694+00:00
-- url     : https://prove2.me/submissions/b92bf1a3-c731-401c-bf04-3d68265f90f5

import Mathlib
import Definitions.Def_JakulinBratko_IsLaw
import Definitions.Def_JakulinBratko_attrMarg
import Definitions.Def_JakulinBratko_marg
import Definitions.Def_JakulinBratko_H
import Definitions.Def_JakulinBratko_I
import Definitions.Def_JakulinBratko_C
import Definitions.Def_JakulinBratko_condLaw
import Definitions.Def_JakulinBratko_condI

noncomputable section

namespace JakulinBratko

open Finset BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
  [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]

/-- `H(∅) = 0`: the empty set of attributes has a single assignment of total mass one. -/
lemma H_empty (P : (∀ i, α i) → ℝ) (hP : IsLaw P) : H P ∅ = 0 := by
  have h1 : ∀ s : (∀ i : (∅ : Finset ι), α i),
      (∑ a with (∅ : Finset ι).restrict a = s, P a) = 1 := by
    intro s
    have hfil : Finset.univ.filter (fun a : (∀ i, α i) => (∅ : Finset ι).restrict a = s)
        = Finset.univ := by
      refine Finset.filter_true_of_mem (fun a _ => ?_)
      funext i
      exact ((Finset.eq_empty_iff_forall_notMem.mp rfl) (i : ι) i.2).elim
    simpa [hfil] using hP.2
  simp [H, marg, h1, Real.logb_one]

/-- The alternating sum `Σ_{V ⊆ W} (-1)^|V| = 0` for nonempty `W`, and `= 1` for `W = ∅`. -/
lemma sum_neg_one_pow_card (W : Finset ι) :
    (∑ V ∈ W.powerset, (-1 : ℝ) ^ V.card) = if W = ∅ then 1 else 0 := by
  classical
  refine Finset.induction_on W ?base ?step
  · simp
  · intro a s ha ih
    rw [powerset_insert, sum_union]
    · rw [if_neg (Finset.ne_empty_of_mem (Finset.mem_insert_self a s))]
      have hinj : Set.InjOn (fun V : Finset ι => insert a V) (s.powerset : Set (Finset ι)) := by
        intro V hV W hW h
        have h' := congrArg (fun t : Finset ι => t.erase a) h
        rw [Finset.erase_insert (Finset.notMem_of_mem_powerset_of_notMem hV ha),
          Finset.erase_insert (Finset.notMem_of_mem_powerset_of_notMem hW ha)] at h'
        exact h'
      rw [Finset.sum_image hinj]
      have h1 : (∑ V ∈ s.powerset, (-1 : ℝ) ^ V.card)
          = -∑ V ∈ s.powerset, (-1 : ℝ) ^ (insert a V).card := by
        rw [← Finset.sum_neg_distrib (fun V : Finset ι => (-1 : ℝ) ^ (insert a V).card)]
        refine Finset.sum_congr rfl (fun V hV => ?_)
        rw [card_insert_of_notMem (Finset.notMem_of_mem_powerset_of_notMem hV ha), pow_succ]
        ring
      rw [h1]
      ring
    · apply Finset.disjoint_left.mpr
      intro t ht1 ht2
      rcases Finset.mem_image.mp ht2 with ⟨u, hu, rfl⟩
      exact ha (Finset.mem_powerset.mp ht1 (Finset.mem_insert_self a u))

/-- For `U ⊆ S`, the alternating sum over the supersets `T` of `U` inside `S` is `1` iff
`U = S` and `0` otherwise. -/
lemma inner_neg_one_sum (S U : Finset ι) (hUS : U ⊆ S) :
    (∑ T ∈ S.powerset.filter (fun T => U ⊆ T), (-1 : ℝ) ^ (T.card - U.card)) = if U = S then 1 else 0 := by
  classical
  refine (Finset.sum_bij (s := S.powerset.filter (fun T => U ⊆ T)) (t := (S \ U).powerset)
    (i := fun T hT => T \ U)
    (g := fun V => (-1 : ℝ) ^ V.card) ?hi ?hinj ?hsurj ?h).trans ?hmain
  · intro T hT
    rw [Finset.mem_powerset]
    exact Finset.sdiff_subset_sdiff (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)
      (Finset.Subset.rfl : U ⊆ U)
  · intro T₁ hT₁ T₂ hT₂ h
    rw [← Finset.union_sdiff_of_subset (Finset.mem_filter.mp hT₁).2, h,
      Finset.union_sdiff_of_subset (Finset.mem_filter.mp hT₂).2]
  · intro V hV
    refine ⟨U ∪ V, ?hinUV, ?hUV⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.union_subset hUS
          ((Finset.mem_powerset.mp hV).trans (Finset.sdiff_subset : S \ U ⊆ S)),
        Finset.subset_union_left⟩
    · exact Finset.union_sdiff_cancel_left
        (Disjoint.mono le_rfl (Finset.mem_powerset.mp hV) Finset.disjoint_sdiff)
  · intro T hT
    have hcard : (T \ U).card = T.card - U.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.mem_filter.mp hT).2]
    rw [hcard]
  · rw [sum_neg_one_pow_card]
    by_cases hU : U = S
    · subst hU
      simp
    · have hne : S \ U ≠ ∅ := by
        intro h
        exact hU (Finset.Subset.antisymm hUS (Finset.sdiff_eq_empty_iff_subset.mp h))
      simp [hU, hne]

/-- Möbius inversion on the subset lattice: `H(S) = -Σ_{∅ ≠ T ⊆ S} I(T)`. -/
lemma inversion (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (S : Finset ι) :
    H P S = -∑ T ∈ S.powerset.filter (fun T => T.Nonempty), I P T := by
  classical
  have htotal : (∑ T ∈ S.powerset, I P T) = -H P S := by
    unfold I
    rw [Finset.sum_neg_distrib
      (fun T : Finset ι => ∑ U ∈ T.powerset, (-1 : ℝ) ^ (T.card - U.card) * H P U)]
    congr 1
    calc
      (∑ T ∈ S.powerset, ∑ U ∈ T.powerset, (-1 : ℝ) ^ (T.card - U.card) * H P U)
      = ∑ T ∈ S.powerset, ∑ U ∈ S.powerset,
          (if U ⊆ T then (-1 : ℝ) ^ (T.card - U.card) * H P U else 0) := by
          refine Finset.sum_congr rfl (fun T hT => ?_)
          calc
            (∑ U ∈ T.powerset, (-1 : ℝ) ^ (T.card - U.card) * H P U)
            = ∑ U ∈ S.powerset.filter (fun U => U ⊆ T), (-1 : ℝ) ^ (T.card - U.card) * H P U := by
                congr 1
                ext U
                rw [Finset.mem_filter]
                exact ⟨fun h => ⟨Finset.mem_powerset.mpr
                  ((Finset.mem_powerset.mp h).trans (Finset.mem_powerset.mp hT)), Finset.mem_powerset.mp h⟩,
                  fun h => Finset.mem_powerset.mpr h.2⟩
            _ = ∑ U ∈ S.powerset,
                (if U ⊆ T then (-1 : ℝ) ^ (T.card - U.card) * H P U else 0) := by
                rw [Finset.sum_filter (fun U => U ⊆ T) (fun U => (-1 : ℝ) ^ (T.card - U.card) * H P U)]
      _ = ∑ U ∈ S.powerset, ∑ T ∈ S.powerset,
          (if U ⊆ T then (-1 : ℝ) ^ (T.card - U.card) * H P U else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ U ∈ S.powerset, H P U * (if U = S then 1 else 0) := by
          refine Finset.sum_congr rfl (fun U hU => ?_)
          calc
            (∑ T ∈ S.powerset,
                (if U ⊆ T then (-1 : ℝ) ^ (T.card - U.card) * H P U else 0))
            = ∑ T ∈ S.powerset.filter (fun T => U ⊆ T), (-1 : ℝ) ^ (T.card - U.card) * H P U := by
                rw [Finset.sum_filter (fun T => U ⊆ T) (fun T => (-1 : ℝ) ^ (T.card - U.card) * H P U)]
            _ = (∑ T ∈ S.powerset.filter (fun T => U ⊆ T), (-1 : ℝ) ^ (T.card - U.card)) * H P U := by
                rw [← Finset.sum_mul]
            _ = (if U = S then 1 else 0) * H P U := by
                rw [inner_neg_one_sum S U (Finset.mem_powerset.mp hU)]
            _ = H P U * (if U = S then 1 else 0) := by ring
      _ = H P S * (if S = S then 1 else 0) := by
          refine Finset.sum_eq_single (s := S.powerset)
            (f := fun U => H P U * (if U = S then 1 else 0)) S ?h0 ?h1
          · intro b hb hbne
            rw [if_neg hbne, mul_zero]
          · intro hnotmem
            exact (hnotmem (Finset.mem_powerset_self S)).elim
      _ = H P S := by
          rw [if_pos rfl, mul_one]
  have hIempty : I P ∅ = -H P ∅ := by simp [I]
  have hsplit : (∑ T ∈ S.powerset, I P T) =
      I P ∅ + ∑ T ∈ S.powerset.filter (fun T => T.Nonempty), I P T := by
    have hfl : S.powerset.filter (fun T : Finset ι => ¬T.Nonempty) = {∅} := by
      ext T
      rw [Finset.mem_filter, Finset.mem_singleton, Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty]
      exact ⟨fun h => h.2, fun h => by simpa [h]⟩
    calc
      (∑ T ∈ S.powerset, I P T)
      = (∑ T ∈ S.powerset.filter (fun T : Finset ι => T.Nonempty), I P T)
          + ∑ T ∈ S.powerset.filter (fun T : Finset ι => ¬T.Nonempty), I P T := by
          rw [Finset.sum_filter_add_sum_filter_not (s := S.powerset)
            (p := fun T : Finset ι => T.Nonempty) (f := I P)]
      _ = ∑ T ∈ S.powerset.filter (fun T : Finset ι => T.Nonempty), I P T + I P ∅ := by
          rw [hfl]
          simp
      _ = I P ∅ + ∑ T ∈ S.powerset.filter (fun T : Finset ι => T.Nonempty), I P T := by ring
  have hmain : (∑ T ∈ S.powerset.filter (fun T => T.Nonempty), I P T) = -H P S := by
    rw [← htotal, hsplit, hIempty, H_empty P hP]
    ring
  exact by linarith [hmain]

/-- `I({X}) = -H({X})`: interaction information of a singleton is the negative of its entropy. -/
lemma I_singleton (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (X : ι) : I P {X} = -H P {X} := by
  classical
  unfold I
  have hp : (({X} : Finset ι).powerset) = {∅, ({X} : Finset ι)} := by
    ext T
    rw [Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton, Finset.subset_singleton_iff]
  rw [hp]
  simp [H_empty P hP]

/-- Clause (a): the total correlation is the sum of the interaction informations of the subsets
with at least two elements. -/
lemma totalCorrelation_eq (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (S : Finset ι) :
    C P S = ∑ T ∈ S.powerset.filter (fun T => 2 ≤ T.card), I P T := by
  classical
  unfold C
  rw [inversion P hP S]
  rw [sub_neg_eq_add]
  have hsplit1 : (∑ T ∈ S.powerset.filter (fun T : Finset ι => T.Nonempty), I P T)
      = (∑ T ∈ S.powerset.filter (fun T => T.card = 1), I P T)
        + ∑ T ∈ S.powerset.filter (fun T => 2 ≤ T.card), I P T := by
    calc
      (∑ T ∈ S.powerset.filter (fun T : Finset ι => T.Nonempty), I P T)
      = ∑ T ∈ S.powerset.filter (fun T => T.card = 1) ∪ S.powerset.filter (fun T => 2 ≤ T.card),
          I P T := by
          congr 1
          ext T
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
          constructor
          · rintro ⟨hTP, hne⟩
            have hc : 0 < T.card := Finset.card_pos.mpr hne
            have hcase : T.card = 1 ∨ 2 ≤ T.card := by omega
            rcases hcase with h1 | h2
            · exact Or.inl ⟨hTP, h1⟩
            · exact Or.inr ⟨hTP, h2⟩
          · rintro (⟨hTP, hc⟩ | ⟨hTP, hc⟩)
            · exact ⟨hTP, Finset.card_pos.mp (hc.symm ▸ zero_lt_one)⟩
            · exact ⟨hTP, Finset.card_pos.mp (lt_of_lt_of_le zero_lt_two hc)⟩
      _ = (∑ T ∈ S.powerset.filter (fun T => T.card = 1), I P T)
          + ∑ T ∈ S.powerset.filter (fun T => 2 ≤ T.card), I P T := by
          refine Finset.sum_union ?disj
          apply Finset.disjoint_left.mpr
          intro T h1 h2
          rw [Finset.mem_filter] at h1 h2
          omega
  rw [hsplit1]
  have hsing : (∑ T ∈ S.powerset.filter (fun T => T.card = 1), I P T) = ∑ X ∈ S, I P {X} := by
    refine Finset.sum_bij (s := S.powerset.filter (fun T => T.card = 1)) (t := S)
      (f := fun T => I P T) (g := fun X => I P {X})
      (i := fun T hT => Classical.choose (Finset.card_eq_one.mp (Finset.mem_filter.mp hT).2))
      ?hi ?hinj ?hsurj ?hval
    · intro T hT
      have hc := Finset.mem_filter.mp hT
      have hcard := Classical.choose_spec (Finset.card_eq_one.mp (Finset.mem_filter.mp hT).2)
      have hc1 : (Classical.choose (Finset.card_eq_one.mp (Finset.mem_filter.mp hT).2)) ∈ T := by
        exact Eq.mp (congrArg (fun s =>
          (Classical.choose (Finset.card_eq_one.mp (Finset.mem_filter.mp hT).2)) ∈ s) hcard.symm)
          (Finset.mem_singleton_self
            (Classical.choose (Finset.card_eq_one.mp (Finset.mem_filter.mp hT).2)))
      exact (Finset.mem_powerset.mp hc.1) hc1
    · intro T₁ hT₁ T₂ hT₂ h
      have hc₁ := Classical.choose_spec (Finset.card_eq_one.mp (Finset.mem_filter.mp hT₁).2)
      have hc₂ := Classical.choose_spec (Finset.card_eq_one.mp (Finset.mem_filter.mp hT₂).2)
      exact Eq.trans hc₁
        (Eq.trans (congrArg (fun c : ι => ({c} : Finset ι)) h) hc₂.symm)
    · intro X hX
      refine ⟨({X} : Finset ι), ?hinX, ?hX⟩
      · rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.singleton_subset_iff.mpr hX, by simp⟩
      · have hcard := Classical.choose_spec
          (Finset.card_eq_one.mp (by simp : (({X} : Finset ι)).card = 1))
        exact (Finset.mem_singleton.mp
          (Eq.mp (congrArg (fun s : Finset ι => X ∈ s) hcard) (Finset.mem_singleton_self X))).symm
    · intro T hT
      have hcard := Classical.choose_spec (Finset.card_eq_one.mp (Finset.mem_filter.mp hT).2)
      exact congrArg (I P) hcard
  rw [hsing]
  rw [← add_assoc]
  rw [← Finset.sum_add_distrib]
  have hsumzero : (∑ X ∈ S, (H P {X} + I P {X})) = 0 := by
    refine Finset.sum_eq_zero (fun X hX => ?_)
    rw [I_singleton P hP X]
    ring
  rw [hsumzero, zero_add]

/-- The assignments of `insert X U` are in bijection with pairs (assignment of `U`, value of
`X`), when `X ∉ U`. -/
def assignEquiv (U : Finset ι) {X : ι} (hXU : X ∉ U) :
    ((∀ i : ↥U, α i) × α X) ≃ (∀ i : ↥(insert X U), α i) where
  toFun := fun p i =>
    if h : i.1 = X then Eq.rec p.2 h.symm else p.1 ⟨i.1, (Finset.mem_insert.mp i.2).resolve_left h⟩
  invFun := fun z => (fun u => z ⟨u.1, Finset.mem_insert_of_mem u.2⟩, z ⟨X, Finset.mem_insert_self X U⟩)
  left_inv := by
    intro p
    apply Prod.ext
    · funext u
      dsimp
      rw [dif_neg]
      · intro h; exact hXU (h ▸ u.2)
    · dsimp
      rw [dif_pos rfl]
  right_inv := by
    intro z
    funext i
    rcases i with ⟨ival, iprop⟩
    dsimp
    by_cases hi : ival = X
    · subst X
      rw [dif_pos rfl]
    · rw [dif_neg hi]

/-- The restriction of `a` to `insert X U` equals `assignEquiv (u, x)` iff `a` restricts to `u`
on `U` and takes the value `x` at `X`. -/
lemma restrict_assignEquiv_iff (U : Finset ι) {X : ι} (hXU : X ∉ U)
    (a : ∀ i, α i) (u : ∀ i : ↥U, α i) (x : α X) :
    ((insert X U).restrict a = assignEquiv U hXU (u, x)) ↔ U.restrict a = u ∧ a X = x := by
  constructor
  · intro h
    constructor
    · funext u'
      have h' := congrArg (fun f : (∀ i : ↥(insert X U), α i) => f ⟨u'.1, Finset.mem_insert_of_mem u'.2⟩) h
      unfold assignEquiv at h'
      dsimp [Finset.restrict] at h'
      have hne : u'.1 ≠ X := by intro hh; exact hXU (hh ▸ u'.2)
      rwa [dif_neg hne] at h'
    · have h' := congrArg (fun f : (∀ i : ↥(insert X U), α i) => f ⟨X, Finset.mem_insert_self X U⟩) h
      unfold assignEquiv at h'
      dsimp [Finset.restrict] at h'
      simpa using h'
  · rintro ⟨hu, hx⟩
    funext i
    rcases i with ⟨ival, iprop⟩
    dsimp [Finset.restrict]
    unfold assignEquiv
    dsimp
    by_cases hi : ival = X
    · rw [dif_pos hi]
      subst X
      simpa using hx
    · rw [dif_neg hi]
      have h' := congrArg (fun f : (∀ i : ↥U, α i) => f ⟨ival, (Finset.mem_insert.mp iprop).resolve_left hi⟩) hu
      simpa using h'

/-- The marginal of `P` on `insert X U` at the assignment `assignEquiv (u, x)` is the mass of the
fiber `U.restrict a = u ∧ a X = x`. -/
lemma marg_assignEquiv (P : (∀ i, α i) → ℝ) (U : Finset ι) {X : ι} (hXU : X ∉ U)
    (u : ∀ i : ↥U, α i) (x : α X) :
    marg P (insert X U) (assignEquiv U hXU (u, x)) = ∑ a with (U.restrict a = u ∧ a X = x), P a := by
  unfold marg
  congr 1
  ext a
  simpa [Finset.mem_filter] using restrict_assignEquiv_iff U hXU a u x

/-- Slicing the marginal on `S` at the attribute `X`: the total mass over the fiber `z ⟨X⟩ = x`
is the single-attribute marginal. -/
lemma sum_marg_slice (P : (∀ i, α i) → ℝ) (S : Finset ι) {X : ι} (hX : X ∈ S) (x : α X) :
    (∑ z : (∀ i : S, α i) with z ⟨X, hX⟩ = x, marg P S z) = attrMarg P X x := by
  classical
  unfold marg attrMarg
  calc
    (∑ z : (∀ i : S, α i) with z ⟨X, hX⟩ = x, ∑ a with S.restrict a = z, P a)
    = ∑ z : (∀ i : S, α i) with z ⟨X, hX⟩ = x, ∑ a, (if S.restrict a = z then P a else 0) := by
        refine Finset.sum_congr rfl (fun z hz => ?_)
        rw [Finset.sum_filter (fun a => S.restrict a = z) P]
    _ = ∑ a, ∑ z : (∀ i : S, α i) with z ⟨X, hX⟩ = x, (if S.restrict a = z then P a else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ a, (if a X = x then P a else 0) := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        by_cases hx : a X = x
        · rw [if_pos hx]
          refine Eq.trans (Finset.sum_eq_single
            (s := Finset.univ.filter (fun z : (∀ i : S, α i) => z ⟨X, hX⟩ = x))
            (f := fun z => if S.restrict a = z then P a else 0) (S.restrict a) ?h0 ?h1) ?h2
          · intro b hb hbne
            rw [if_neg (fun h => hbne h.symm)]
          · intro hnotmem
            have : (S.restrict a) ⟨X, hX⟩ = x := by simpa [Finset.restrict] using hx
            exact (hnotmem (Finset.mem_filter.mpr ⟨Finset.mem_univ (S.restrict a), this⟩)).elim
          · simp
        · rw [if_neg hx]
          refine Finset.sum_eq_zero (fun z hz => ?_)
          rw [if_neg]
          intro h
          apply hx
          calc
            a X = (S.restrict a) ⟨X, hX⟩ := by simp [Finset.restrict]
            _ = z ⟨X, hX⟩ := congrArg (fun f : (∀ i : S, α i) => f ⟨X, hX⟩) h
            _ = x := (Finset.mem_filter.mp hz).2
    _ = ∑ a with a X = x, P a := by rw [Finset.sum_filter (fun a => a X = x) P]



/-- The mass of `condLaw P X x` is `1` when `attrMarg P X x > 0` and `0` otherwise. -/
lemma sum_condLaw (P : (∀ i, α i) → ℝ) (X : ι) (x : α X) :
    (∑ a, condLaw P X x a) = (if attrMarg P X x = 0 then 0 else 1) := by
  classical
  calc
    (∑ a, condLaw P X x a)
    = ∑ a, (if a X = x then P a / attrMarg P X x else 0) := rfl
    _ = ∑ a with a X = x, P a / attrMarg P X x := by
        rw [Finset.sum_filter (fun a => a X = x) (fun a => P a / attrMarg P X x)]
    _ = (∑ a with a X = x, P a) / attrMarg P X x := by rw [Finset.sum_div]
    _ = attrMarg P X x / attrMarg P X x := rfl
    _ = (if attrMarg P X x = 0 then 0 else 1) := by
        by_cases hp : attrMarg P X x = 0
        · rw [hp, div_zero, if_pos rfl]
        · rw [if_neg hp, div_self hp]

/-- The conditional law of a single attribute has entropy `0` when conditioning has no other
attributes. -/
lemma H_condLaw_empty (P : (∀ i, α i) → ℝ) (X : ι) (x : α X) : H (condLaw P X x) ∅ = 0 := by
  classical
  have hfil : ∀ s : (∀ i : ↥(∅ : Finset ι), α i),
      Finset.univ.filter (fun a : (∀ i, α i) => (∅ : Finset ι).restrict a = s) = Finset.univ := by
    intro s
    refine Finset.filter_true_of_mem (fun a _ => ?_)
    funext i
    exact ((Finset.eq_empty_iff_forall_notMem.mp rfl) (i : ι) i.2).elim
  simp only [H, marg]
  simp_rw [hfil]
  rw [sum_condLaw P X x]
  by_cases hp : attrMarg P X x = 0 <;> simp [hp, Real.logb_one, Real.logb_zero]

/-- Nonnegativity of the fiber masses `m`. -/
lemma marg_assignEquiv_nonneg (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (U : Finset ι) {X : ι}
    (hXU : X ∉ U) (u : ∀ i : ↥U, α i) (x : α X) :
    0 ≤ marg P (insert X U) (assignEquiv U hXU (u, x)) := by
  rw [marg_assignEquiv P U hXU u x]
  exact Finset.sum_nonneg (fun a ha => hP.1 a)

/-- The fiber masses `m` are bounded by the single-attribute marginal. -/
lemma marg_assignEquiv_le (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (U : Finset ι) {X : ι}
    (hXU : X ∉ U) (u : ∀ i : ↥U, α i) (x : α X) :
    marg P (insert X U) (assignEquiv U hXU (u, x)) ≤ attrMarg P X x := by
  rw [marg_assignEquiv P U hXU u x]
  unfold attrMarg
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub (fun a ha has => hP.1 a)
  intro a ha
  rw [Finset.mem_filter] at ha ⊢
  exact ⟨Finset.mem_univ a, ha.2.2⟩

/-- The slice sum: summing the fiber masses over the `U`-assignments at a fixed value `x` of `X`
gives the single-attribute marginal. -/
lemma sum_marg_assignEquiv (P : (∀ i, α i) → ℝ) (U : Finset ι) {X : ι} (hXU : X ∉ U) (x : α X) :
    (∑ u : (∀ i : ↥U, α i), marg P (insert X U) (assignEquiv U hXU (u, x))) = attrMarg P X x := by
  classical
  calc
    (∑ u : (∀ i : ↥U, α i), marg P (insert X U) (assignEquiv U hXU (u, x)))
    = ∑ u : (∀ i : ↥U, α i), ∑ a with (U.restrict a = u ∧ a X = x), P a := by
        refine Finset.sum_congr rfl (fun u hu => ?_)
        rw [marg_assignEquiv P U hXU u x]
    _ = ∑ a, ∑ u : (∀ i : ↥U, α i), (if U.restrict a = u ∧ a X = x then P a else 0) := by
        calc
          (∑ u : (∀ i : ↥U, α i), ∑ a with (U.restrict a = u ∧ a X = x), P a)
          = ∑ u : (∀ i : ↥U, α i), ∑ a, (if U.restrict a = u ∧ a X = x then P a else 0) := by
              refine Finset.sum_congr rfl (fun u hu => ?_)
              rw [Finset.sum_filter (fun a => U.restrict a = u ∧ a X = x) P]
          _ = ∑ a, ∑ u : (∀ i : ↥U, α i), (if U.restrict a = u ∧ a X = x then P a else 0) := by
              rw [Finset.sum_comm]
    _ = ∑ a, (if a X = x then P a else 0) := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        by_cases hx : a X = x
        · rw [if_pos hx]
          refine Eq.trans (Finset.sum_eq_single (s := Finset.univ)
            (f := fun u : (∀ i : ↥U, α i) => if U.restrict a = u ∧ a X = x then P a else 0)
            (U.restrict a) ?h0 ?h1) ?h2
          · intro b hb hbne
            rw [if_neg]
            intro hbc
            exact hbne hbc.1.symm
          · intro hnotmem
            exact (hnotmem (Finset.mem_univ (U.restrict a))).elim
          · simp [hx]
        · rw [if_neg hx]
          refine Finset.sum_eq_zero (fun u hu => ?_)
          rw [if_neg]
          rintro ⟨h1, h2⟩
          exact hx h2
    _ = attrMarg P X x := by
        unfold attrMarg
        rw [Finset.sum_filter (fun a => a X = x) P]

/-- The conditional-entropy conversion: `Σ_x p(x) H(P|X=x) = H(P on X ∪ U) − H(X)` written in
the expanded form (with the single-attribute term left as a sum). -/
lemma condEntropy_eq' (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (X : ι) (U : Finset ι) (hXU : X ∉ U) :
    (∑ x : α X, attrMarg P X x * H (condLaw P X x) U)
      = H P (insert X U) + ∑ x : α X, attrMarg P X x * Real.logb 2 (attrMarg P X x) := by
  classical
  let m : (∀ i : ↥U, α i) → α X → ℝ := fun u x => marg P (insert X U) (assignEquiv U hXU (u, x))
  have hmarg : ∀ x u, marg (condLaw P X x) U u = m u x / attrMarg P X x := by
    intro x u
    calc
      marg (condLaw P X x) U u
      = ∑ a with U.restrict a = u ∧ a X = x, P a / attrMarg P X x := by
          unfold marg condLaw
          rw [← Finset.sum_filter (fun a => a X = x) (fun a => P a / attrMarg P X x)]
          congr 1
          ext a
          simp [Finset.mem_filter]
      _ = (∑ a with U.restrict a = u ∧ a X = x, P a) / attrMarg P X x := by
          rw [Finset.sum_div]
      _ = m u x / attrMarg P X x := by
          dsimp [m]
          rw [marg_assignEquiv P U hXU u x]
  have hpx_nonneg : ∀ x, 0 ≤ attrMarg P X x := by
    intro x
    unfold attrMarg
    exact Finset.sum_nonneg (fun a ha => hP.1 a)
  have hLHS : (∑ x : α X, attrMarg P X x * H (condLaw P X x) U)
      = -∑ x : α X, ∑ u : (∀ i : ↥U, α i),
          m u x * Real.logb 2 (m u x / attrMarg P X x) := by
    rw [← Finset.sum_neg_distrib (fun x =>
      ∑ u : (∀ i : ↥U, α i), m u x * Real.logb 2 (m u x / attrMarg P X x))]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    unfold H
    rw [mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [hmarg x u]
    by_cases hp : attrMarg P X x = 0
    · have hm0 : m u x = 0 := by
        exact le_antisymm (by simpa [hp] using marg_assignEquiv_le P hP U hXU u x)
          (by simpa [hp] using marg_assignEquiv_nonneg P hP U hXU u x)
      simp [hm0, hp]
    · rw [← mul_assoc, mul_div_cancel₀ (m u x) hp]
  have hH : H P (insert X U) = -∑ u : (∀ i : ↥U, α i), ∑ x : α X,
      m u x * Real.logb 2 (m u x) := by
    unfold H
    rw [← Fintype.sum_equiv (assignEquiv U hXU)
      (fun p : ((∀ i : ↥U, α i) × α X) =>
        marg P (insert X U) (assignEquiv U hXU p) * Real.logb 2 (marg P (insert X U) (assignEquiv U hXU p)))]
    rw [← Finset.sum_product' (Finset.univ : Finset ((∀ i : ↥U, α i))) (Finset.univ : Finset (α X))
      (fun u x => m u x * Real.logb 2 (m u x))]
    rw [Finset.univ_product_univ]
    intro x
    rfl
  have hlog : (∑ x : α X, ∑ u : (∀ i : ↥U, α i), m u x * Real.logb 2 (attrMarg P X x))
      = ∑ x : α X, attrMarg P X x * Real.logb 2 (attrMarg P X x) := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [← Finset.sum_mul, sum_marg_assignEquiv P U hXU x]
  calc
    (∑ x : α X, attrMarg P X x * H (condLaw P X x) U)
    = -∑ x : α X, ∑ u : (∀ i : ↥U, α i),
        m u x * Real.logb 2 (m u x / attrMarg P X x) := hLHS
    _ = -∑ x : α X, ∑ u : (∀ i : ↥U, α i),
        (m u x * Real.logb 2 (m u x) - m u x * Real.logb 2 (attrMarg P X x)) := by
        refine congrArg Neg.neg ?_
        refine Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun u hu => ?_))
        by_cases hm0 : m u x = 0
        · rw [hm0]
          simp
        · have hpx0 : attrMarg P X x ≠ 0 := by
            intro hpx
            have hmle : m u x ≤ attrMarg P X x := by
              dsimp [m]
              exact marg_assignEquiv_le P hP U hXU u x
            exact hm0 (le_antisymm (by simpa [hpx] using hmle)
              (by simpa [hpx] using marg_assignEquiv_nonneg P hP U hXU u x))
          rw [Real.logb_div hm0 hpx0]
          ring
    _ = -∑ x : α X, ((∑ u : (∀ i : ↥U, α i), m u x * Real.logb 2 (m u x))
        - ∑ u : (∀ i : ↥U, α i), m u x * Real.logb 2 (attrMarg P X x)) := by
        refine congrArg Neg.neg (Finset.sum_congr rfl (fun x hx => ?_))
        rw [Finset.sum_sub_distrib]
    _ = (-∑ x : α X, ∑ u : (∀ i : ↥U, α i), m u x * Real.logb 2 (m u x))
        + ∑ x : α X, ∑ u : (∀ i : ↥U, α i), m u x * Real.logb 2 (attrMarg P X x) := by
        rw [Finset.sum_sub_distrib]
        ring
    _ = H P (insert X U) + ∑ x : α X, attrMarg P X x * Real.logb 2 (attrMarg P X x) := by
        rw [hlog, Finset.sum_comm, hH]

/-- The entropy of a single attribute is the binary entropy of its marginal, summed over all its
values. -/
lemma H_singleton (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (X : ι) :
    H P {X} = -∑ x : α X, attrMarg P X x * Real.logb 2 (attrMarg P X x) := by
  classical
  have h0 : (∑ x : α X, attrMarg P X x * H (condLaw P X x) ∅) = 0 := by
    refine Finset.sum_eq_zero (fun x hx => ?_)
    rw [H_condLaw_empty P X x, mul_zero]
  have hL := condEntropy_eq' P hP X ∅ (by simp : X ∉ (∅ : Finset ι))
  rw [h0] at hL
  have hH' : H P (insert X ∅) = H P {X} := by simp
  rw [hH'] at hL
  linarith

/-- The conditional-entropy conversion: `Σ_x p(x) H(P|X=x) = H(P on X ∪ U) − H(X)`. -/
lemma condEntropy_eq (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (X : ι) (U : Finset ι) (hXU : X ∉ U) :
    (∑ x : α X, attrMarg P X x * H (condLaw P X x) U) = H P (insert X U) - H P {X} := by
  rw [condEntropy_eq' P hP X U hXU, H_singleton P hP X]
  ring

/-- The alternating sum `Σ_{V ⊆ W} (-1)^(|W| − |V|) = 0` for nonempty `W`, and `= 1` for
`W = ∅`. -/
lemma sum_neg_one_pow_sdiff_card (W : Finset ι) :
    (∑ V ∈ W.powerset, (-1 : ℝ) ^ (W.card - V.card)) = if W = ∅ then 1 else 0 := by
  classical
  refine (Finset.sum_bij (s := W.powerset) (t := W.powerset)
    (i := fun V _ => W \ V) (g := fun V => (-1 : ℝ) ^ V.card) ?hi ?hinj ?hsurj ?h).trans
    (sum_neg_one_pow_card W)
  · intro V hV
    rw [Finset.mem_powerset]
    exact (Finset.sdiff_subset : W \ V ⊆ W)
  · intro V₁ hV₁ V₂ hV₂ h
    rw [(Finset.inter_eq_right.mpr (Finset.mem_powerset.mp hV₁)).symm]
    rw [← Finset.sdiff_sdiff_self_left W V₁, h, Finset.sdiff_sdiff_self_left W V₂,
      Finset.inter_eq_right.mpr (Finset.mem_powerset.mp hV₂)]
  · intro V hV
    refine ⟨W \ V, ?hinV, ?hV'⟩
    · rw [Finset.mem_powerset]
      exact (Finset.sdiff_subset : W \ V ⊆ W)
    · rw [Finset.sdiff_sdiff_self_left W V, Finset.inter_eq_right.mpr (Finset.mem_powerset.mp hV)]
  · intro V hV
    have hcard : (W \ V).card = W.card - V.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hV)]
    rw [hcard]

/-- Splitting a sum over the powerset of `insert X S` into the parts avoiding and containing
`X`. -/
lemma sum_powerset_insert_split (S : Finset ι) {X : ι} (hX : X ∉ S) (g : Finset ι → ℝ) :
    (∑ T ∈ (insert X S).powerset, g T) = (∑ U ∈ S.powerset, g U) + ∑ U ∈ S.powerset, g (insert X U) := by
  classical
  rw [powerset_insert]
  rw [Finset.sum_union]
  · rw [Finset.sum_image]
    · intro V hV W hW h
      have h' := congrArg (fun t : Finset ι => t.erase X) h
      rw [Finset.erase_insert (Finset.notMem_of_mem_powerset_of_notMem hV hX),
        Finset.erase_insert (Finset.notMem_of_mem_powerset_of_notMem hW hX)] at h'
      exact h'
  · apply Finset.disjoint_left.mpr
    intro T hT1 hT2
    rcases Finset.mem_image.mp hT2 with ⟨u, hu, rfl⟩
    exact hX (Finset.mem_powerset.mp hT1 (Finset.mem_insert_self X u))

/-- `I(insert X R) + I(R) = -Σ_{U ⊆ R} (-1)^(|R| − |U|) H(insert X U)`. -/
lemma I_split (P : (∀ i, α i) → ℝ) (X : ι) (R : Finset ι) (hXR : X ∉ R) :
    I P (insert X R) + I P R
      = -∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card) * H P (insert X U) := by
  classical
  have himg : (∑ T ∈ R.powerset.image (insert X), (-1 : ℝ) ^ ((insert X R).card - T.card) * H P T)
      = ∑ U ∈ R.powerset, (-1 : ℝ) ^ ((insert X R).card - (insert X U).card) * H P (insert X U) := by
    refine Finset.sum_image ?hinj
    intro V hV W hW h
    have h' := congrArg (fun t : Finset ι => t.erase X) h
    rw [Finset.erase_insert (Finset.notMem_of_mem_powerset_of_notMem hV hXR),
      Finset.erase_insert (Finset.notMem_of_mem_powerset_of_notMem hW hXR)] at h'
    exact h'
  calc
    I P (insert X R) + I P R
    = -(∑ T ∈ R.powerset, (-1 : ℝ) ^ ((insert X R).card - T.card) * H P T
        + ∑ U ∈ R.powerset, (-1 : ℝ) ^ ((insert X R).card - (insert X U).card) * H P (insert X U))
      + -(∑ T ∈ R.powerset, (-1 : ℝ) ^ (R.card - T.card) * H P T) := by
        unfold I
        rw [powerset_insert]
        rw [Finset.sum_union (f := fun T : Finset ι => (-1 : ℝ) ^ ((insert X R).card - T.card) * H P T)]
        · refine congrArg (fun t =>
            -(∑ T ∈ R.powerset, (-1 : ℝ) ^ ((insert X R).card - T.card) * H P T + t)
              + -(∑ T ∈ R.powerset, (-1 : ℝ) ^ (R.card - T.card) * H P T)) himg
        · apply Finset.disjoint_left.mpr
          intro T hT1 hT2
          rcases Finset.mem_image.mp hT2 with ⟨u, hu, rfl⟩
          exact hXR (Finset.mem_powerset.mp hT1 (Finset.mem_insert_self X u))
    _ = -∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card) * H P (insert X U) := by
        rw [card_insert_of_notMem hXR]
        have h1 : (∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card + 1 - U.card) * H P U)
            = -(∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card) * H P U) := by
          rw [← Finset.sum_neg_distrib (fun U : Finset ι => (-1 : ℝ) ^ (R.card - U.card) * H P U)]
          refine Finset.sum_congr rfl (fun U hU => ?_)
          rw [Nat.succ_sub (Finset.card_le_card (Finset.mem_powerset.mp hU)), pow_succ]
          ring
        have h2 : (∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card + 1 - (insert X U).card) * H P (insert X U))
            = ∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card) * H P (insert X U) := by
          refine Finset.sum_congr rfl (fun U hU => ?_)
          rw [card_insert_of_notMem (Finset.notMem_of_mem_powerset_of_notMem hU hXR)]
          rw [Nat.add_sub_add_right]
        rw [h1, h2]
        ring

/-- The conditional interaction information expanded as an alternating sum of joint entropies. -/
lemma condI_eq (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (X : ι) (R : Finset ι) (hR : R.Nonempty)
    (hXR : X ∉ R) :
    condI P X R = -∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card) * H P (insert X U) := by
  classical
  calc
    condI P X R
    = ∑ x : α X, attrMarg P X x *
        (-∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card) * H (condLaw P X x) U) := by
        unfold condI I
        rfl
    _ = -∑ x : α X, ∑ U ∈ R.powerset,
        attrMarg P X x * ((-1 : ℝ) ^ (R.card - U.card) * H (condLaw P X x) U) := by
        rw [← Finset.sum_neg_distrib (fun x : α X => ∑ U ∈ R.powerset,
          attrMarg P X x * ((-1 : ℝ) ^ (R.card - U.card) * H (condLaw P X x) U))]
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [mul_neg, Finset.mul_sum]
    _ = -∑ U ∈ R.powerset, ∑ x : α X,
        attrMarg P X x * ((-1 : ℝ) ^ (R.card - U.card) * H (condLaw P X x) U) := by
        rw [Finset.sum_comm]
    _ = -∑ U ∈ R.powerset,
        ((-1 : ℝ) ^ (R.card - U.card)) * (∑ x : α X, attrMarg P X x * H (condLaw P X x) U) := by
        refine congrArg Neg.neg (Finset.sum_congr rfl (fun U hU => ?_))
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [← mul_assoc]
        ring
    _ = -∑ U ∈ R.powerset,
        ((-1 : ℝ) ^ (R.card - U.card)) * (H P (insert X U) - H P {X}) := by
        refine congrArg Neg.neg (Finset.sum_congr rfl (fun U hU => ?_))
        rw [condEntropy_eq P hP X U (Finset.notMem_of_mem_powerset_of_notMem hU hXR)]
    _ = -∑ U ∈ R.powerset,
        ((-1 : ℝ) ^ (R.card - U.card)) * H P (insert X U)
        + (∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card)) * H P {X} := by
        calc
          -(∑ U ∈ R.powerset, ((-1 : ℝ) ^ (R.card - U.card)) * (H P (insert X U) - H P {X}))
          = -((∑ U ∈ R.powerset, ((-1 : ℝ) ^ (R.card - U.card)) * H P (insert X U))
              - (∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card)) * H P {X}) := by
              congr 1
              calc
                (∑ U ∈ R.powerset, ((-1 : ℝ) ^ (R.card - U.card)) * (H P (insert X U) - H P {X}))
                = ∑ U ∈ R.powerset, (((-1 : ℝ) ^ (R.card - U.card)) * H P (insert X U)
                    - ((-1 : ℝ) ^ (R.card - U.card)) * H P {X}) := by
                    refine Finset.sum_congr rfl (fun U hU => ?_)
                    rw [mul_sub]
                _ = (∑ U ∈ R.powerset, ((-1 : ℝ) ^ (R.card - U.card)) * H P (insert X U))
                    - ∑ U ∈ R.powerset, ((-1 : ℝ) ^ (R.card - U.card)) * H P {X} := by
                    rw [Finset.sum_sub_distrib]
                _ = (∑ U ∈ R.powerset, ((-1 : ℝ) ^ (R.card - U.card)) * H P (insert X U))
                    - (∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card)) * H P {X} := by
                    rw [← Finset.sum_mul]
          _ = -∑ U ∈ R.powerset, ((-1 : ℝ) ^ (R.card - U.card)) * H P (insert X U)
              + (∑ U ∈ R.powerset, (-1 : ℝ) ^ (R.card - U.card)) * H P {X} := by
              ring
    _ = -∑ U ∈ R.powerset,
        ((-1 : ℝ) ^ (R.card - U.card)) * H P (insert X U) := by
        rw [sum_neg_one_pow_sdiff_card R]
        have hne : R ≠ ∅ := by
          rcases hR with ⟨r, hr⟩
          exact Finset.ne_empty_of_mem hr
        rw [if_neg hne, zero_mul, add_zero]

/-- Clause (b): McGill's recursion `I(S) = I(S \ X | X) − I(S \ X)` for `|S| ≥ 2`, `X ∈ S`. -/
lemma mcgill (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (S : Finset ι) (hS : 2 ≤ S.card) (X : ι)
    (hX : X ∈ S) :
    I P S = condI P X (S.erase X) - I P (S.erase X) := by
  classical
  have hXR : X ∉ S.erase X := Finset.notMem_erase X S
  have hRne : (S.erase X).Nonempty := by
    have hc : 1 ≤ (S.erase X).card := by
      have hcard : S.card = (S.erase X).card + 1 := (Finset.card_erase_add_one hX).symm
      omega
    exact Finset.card_pos.mp hc
  have hsplit := I_split P X (S.erase X) hXR
  have hcond := condI_eq P hP X (S.erase X) hRne hXR
  calc
    I P S = I P (insert X (S.erase X)) := by rw [Finset.insert_erase hX]
    _ = -∑ U ∈ (S.erase X).powerset, (-1 : ℝ) ^ ((S.erase X).card - U.card) * H P (insert X U)
        - I P (S.erase X) := by
        linarith [hsplit]
    _ = condI P X (S.erase X) - I P (S.erase X) := by rw [hcond]

/-- Gibbs' inequality for two finite distributions, in natural logarithms, with the equality
case. -/
lemma gibbs {Z : Type*} [Fintype Z] [DecidableEq Z] (m q : Z → ℝ)
    (hm : ∀ z : Z, 0 ≤ m z) (hq : ∀ z : Z, 0 ≤ q z) (hm1 : ∑ z : Z, m z = 1) (hq1 : ∑ z : Z, q z = 1)
    (hsupp : ∀ z : Z, 0 < m z → 0 < q z) :
    0 ≤ ∑ z : Z, m z * Real.log (m z / q z) ∧
      ((∑ z : Z, m z * Real.log (m z / q z) = 0) → m = q) := by
  classical
  have hper : ∀ z : Z, m z - q z ≤ m z * Real.log (m z / q z) := by
    intro z
    by_cases hmz : m z = 0
    · rw [hmz]
      simp only [zero_mul, zero_sub]
      linarith [hq z]
    · have hmp : 0 < m z := lt_of_le_of_ne (hm z) (Ne.symm hmz)
      have hqp : 0 < q z := hsupp z hmp
      have h1 := Real.log_le_sub_one_of_pos (div_pos hqp hmp)
      have h2 : m z * Real.log (m z / q z) = -m z * Real.log (q z / m z) := by
        rw [Real.log_div (ne_of_gt hmp) (ne_of_gt hqp)]
        rw [Real.log_div (ne_of_gt hqp) (ne_of_gt hmp)]
        ring
      have h3 : m z * (q z / m z - 1) = q z - m z := by
        field_simp [hmp]
      rw [h2]
      nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt hmp), h3]
  constructor
  · have hsum : (∑ z : Z, (m z - q z)) ≤ ∑ z : Z, m z * Real.log (m z / q z) := by
      refine Finset.sum_le_sum (fun z hz => hper z)
    rw [Finset.sum_sub_distrib, hm1, hq1] at hsum
    simpa using hsum
  · intro h
    funext z
    have hterm : m z * Real.log (m z / q z) = m z - q z := by
      have hnonneg : ∀ w : Z, 0 ≤ m w * Real.log (m w / q w) - (m w - q w) := by
        intro w
        linarith [hper w]
      have hsum0 : (∑ w : Z, (m w * Real.log (m w / q w) - (m w - q w))) = 0 := by
        rw [Finset.sum_sub_distrib, h, Finset.sum_sub_distrib, hm1, hq1]
        ring
      have hz0 := (Finset.sum_eq_zero_iff_of_nonneg (fun w hw => hnonneg w)).mp hsum0 z (Finset.mem_univ z)
      linarith
    by_cases hmz : m z = 0
    · rw [hmz] at hterm ⊢
      linarith
    · have hmp : 0 < m z := lt_of_le_of_ne (hm z) (Ne.symm hmz)
      have hqp : 0 < q z := hsupp z hmp
      by_contra hne
      have hne' : q z / m z ≠ 1 := by
        intro hq
        apply hne
        have : q z = m z := by
          have hq1' : q z / m z * m z = 1 * m z := congrArg (fun t => t * m z) hq
          rwa [div_mul_cancel₀ (q z) hmz, one_mul] at hq1'
        exact this.symm
      have hlt := Real.log_lt_sub_one_of_pos (div_pos hqp hmp) hne'
      have h2 : m z * Real.log (m z / q z) = -m z * Real.log (q z / m z) := by
        rw [Real.log_div (ne_of_gt hmp) (ne_of_gt hqp)]
        rw [Real.log_div (ne_of_gt hqp) (ne_of_gt hmp)]
        ring
      have h3 : m z * (q z / m z - 1) = q z - m z := by
        field_simp [hmp]
      have hmul : m z * Real.log (q z / m z) < m z * (q z / m z - 1) :=
        mul_lt_mul_of_pos_left hlt hmp
      rw [h2] at hterm
      nlinarith [hterm, hmul, h3]

/-- The total mass of the single-attribute marginal is `1`. -/
lemma sum_attrMarg (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (X : ι) : (∑ x : α X, attrMarg P X x) = 1 := by
  classical
  calc
    (∑ x : α X, attrMarg P X x)
    = ∑ x : α X, ∑ a with a X = x, P a := rfl
    _ = ∑ a, ∑ x : α X, (if a X = x then P a else 0) := by
        calc
          (∑ x : α X, ∑ a with a X = x, P a)
          = ∑ x : α X, ∑ a, (if a X = x then P a else 0) := by
              refine Finset.sum_congr rfl (fun x hx => ?_)
              rw [Finset.sum_filter (fun a => a X = x) P]
          _ = ∑ a, ∑ x : α X, (if a X = x then P a else 0) := by
              rw [Finset.sum_comm]
    _ = ∑ a, P a := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        refine Eq.trans (Finset.sum_eq_single (s := Finset.univ)
          (f := fun x : α X => if a X = x then P a else 0) (a X) ?h0 ?h1) ?h2
        · intro b hb hbne
          rw [if_neg]
          intro h
          exact hbne h.symm
        · intro hnotmem
          exact (hnotmem (Finset.mem_univ (a X))).elim
        · simp
    _ = 1 := hP.2

/-- The total mass of the joint marginal on `S` is `1`. -/
lemma sum_marg (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (S : Finset ι) :
    (∑ s : (∀ i : S, α i), marg P S s) = 1 := by
  classical
  calc
    (∑ s : (∀ i : S, α i), marg P S s)
    = ∑ s : (∀ i : S, α i), ∑ a with S.restrict a = s, P a := rfl
    _ = ∑ a, ∑ s : (∀ i : S, α i), (if S.restrict a = s then P a else 0) := by
        calc
          (∑ s : (∀ i : S, α i), ∑ a with S.restrict a = s, P a)
          = ∑ s : (∀ i : S, α i), ∑ a, (if S.restrict a = s then P a else 0) := by
              refine Finset.sum_congr rfl (fun s hs => ?_)
              rw [Finset.sum_filter (fun a => S.restrict a = s) P]
          _ = ∑ a, ∑ s : (∀ i : S, α i), (if S.restrict a = s then P a else 0) := by
              rw [Finset.sum_comm]
    _ = ∑ a, P a := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        refine Eq.trans (Finset.sum_eq_single (s := Finset.univ)
          (f := fun s : (∀ i : S, α i) => if S.restrict a = s then P a else 0) (S.restrict a) ?h0 ?h1) ?h2
        · intro b hb hbne
          rw [if_neg]
          intro h
          exact hbne h.symm
        · intro hnotmem
          exact (hnotmem (Finset.mem_univ (S.restrict a))).elim
        · simp
    _ = 1 := hP.2

/-- The product of the single-attribute marginals is a probability distribution: its total mass
over the assignments of `S` is `1`. -/
lemma sum_prod_attrMarg (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (S : Finset ι) :
    (∑ s : (∀ i : S, α i), ∏ X : S, attrMarg P X (s X)) = 1 := by
  classical
  calc
    (∑ s : (∀ i : S, α i), ∏ X : S, attrMarg P X (s X))
    = ∏ X : S, ∑ x : α X, attrMarg P X x := by
        rw [Finset.prod_univ_sum (fun _ : S => (Finset.univ : Finset (α _)))
          (fun X x => attrMarg P X x)]
        rw [Fintype.piFinset_univ]
    _ = 1 := by
        rw [Finset.prod_eq_one]
        intro X hX
        exact sum_attrMarg P hP X

/-- The joint marginal at an assignment is bounded by each single-attribute marginal. -/
lemma marg_le_attrMarg (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (S : Finset ι) (X : ι) (hX : X ∈ S)
    (s : ∀ i : S, α i) :
    marg P S s ≤ attrMarg P X (s ⟨X, hX⟩) := by
  classical
  unfold marg attrMarg
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub (fun a ha has => hP.1 a)
  intro a ha
  rw [Finset.mem_filter] at ha ⊢
  exact ⟨Finset.mem_univ a,
    by simpa [Finset.restrict] using congrArg (fun f : (∀ i : S, α i) => f ⟨X, hX⟩) ha.2⟩

/-- `Σ_x (Σ_{s : s X = x} m s)·c x = Σ_s m s·c(s X)`. -/
lemma sum_fiber_mul (S : Finset ι) (m : (∀ i : S, α i) → ℝ) (X : ι) (hX : X ∈ S) (c : α X → ℝ) :
    (∑ x : α X, (∑ s : (∀ i : S, α i) with s ⟨X, hX⟩ = x, m s) * c x)
      = ∑ s : (∀ i : S, α i), m s * c (s ⟨X, hX⟩) := by
  classical
  calc
    (∑ x : α X, (∑ s : (∀ i : S, α i) with s ⟨X, hX⟩ = x, m s) * c x)
    = ∑ x : α X, ∑ s : (∀ i : S, α i), (if s ⟨X, hX⟩ = x then m s * c x else 0) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [Finset.sum_mul]
        rw [Finset.sum_filter (fun s : (∀ i : S, α i) => s ⟨X, hX⟩ = x) (fun s => m s * c x)]
    _ = ∑ s : (∀ i : S, α i), ∑ x : α X, (if s ⟨X, hX⟩ = x then m s * c x else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ s : (∀ i : S, α i), m s * c (s ⟨X, hX⟩) := by
        refine Finset.sum_congr rfl (fun s hs => ?_)
        refine Eq.trans (Finset.sum_eq_single (s := Finset.univ)
          (f := fun x : α X => if s ⟨X, hX⟩ = x then m s * c x else 0) (s ⟨X, hX⟩) ?h0 ?h1) ?h2
        · intro b hb hbne
          rw [if_neg]
          intro h
          exact hbne h.symm
        · intro hnotmem
          exact (hnotmem (Finset.mem_univ (s ⟨X, hX⟩))).elim
        · simp

/-- `∑ X ∈ S, f X = ∑ X : S, f X` via the subtype bijection. -/
lemma sum_attach' (S : Finset ι) (f : ι → ℝ) : (∑ X ∈ S, f X) = ∑ X : S, f (X : ι) := by
  classical
  refine Finset.sum_bij (s := S) (t := Finset.univ)
    (i := fun X hX => (⟨X, hX⟩ : S)) ?hi ?hinj ?hsurj ?hval
  · intro X hX
    exact Finset.mem_univ (⟨X, hX⟩ : S)
  · intro X₁ hX₁ X₂ hX₂ h
    exact congrArg Subtype.val h
  · intro X hX
    refine ⟨X.1, X.2, ?hX'⟩
    exact Subtype.ext rfl
  · intro X hX
    rfl

/-- The total correlation equals the relative entropy of the joint law against the product of its
single-attribute marginals. -/
lemma C_eq_relEnt (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (S : Finset ι) :
    C P S = ∑ s : (∀ i : S, α i),
      marg P S s * Real.logb 2 (marg P S s / ∏ X : S, attrMarg P X (s X)) := by
  classical
  calc
    C P S
    = (∑ X ∈ S, H P {X}) - H P S := rfl
    _ = (∑ X : S, H P {X.1}) - H P S := by rw [sum_attach' S (fun X => H P {X})]
    _ = (-∑ X : S, ∑ x : α X, attrMarg P X x * Real.logb 2 (attrMarg P X x)) - H P S := by
        apply congrArg (fun t => t - H P S)
        rw [← Finset.sum_neg_distrib (fun X : S => ∑ x : α X, attrMarg P X x * Real.logb 2 (attrMarg P X x))]
        refine Finset.sum_congr rfl (fun X hX => ?_)
        exact H_singleton P hP X
    _ = (-∑ X : S, ∑ x : α X, attrMarg P X x * Real.logb 2 (attrMarg P X x))
        + ∑ s : (∀ i : S, α i), marg P S s * Real.logb 2 (marg P S s) := by
        unfold H
        ring
    _ = ∑ s : (∀ i : S, α i), marg P S s * Real.logb 2 (marg P S s)
        - ∑ X : S, ∑ x : α X, attrMarg P X x * Real.logb 2 (attrMarg P X x) := by ring
    _ = ∑ s : (∀ i : S, α i), (marg P S s * Real.logb 2 (marg P S s)
        - marg P S s * ∑ X : S, Real.logb 2 (attrMarg P X (s X))) := by
        have hqterm : (∑ X : S, ∑ x : α X, attrMarg P X x * Real.logb 2 (attrMarg P X x))
            = ∑ s : (∀ i : S, α i), marg P S s * ∑ X : S, Real.logb 2 (attrMarg P X (s X)) := by
          calc
            (∑ X : S, ∑ x : α X, attrMarg P X x * Real.logb 2 (attrMarg P X x))
            = ∑ X : S, ∑ x : α X,
                (∑ s : (∀ i : S, α i) with s X = x, marg P S s) * Real.logb 2 (attrMarg P X x) := by
                refine Finset.sum_congr rfl (fun X hX => Finset.sum_congr rfl (fun x hx => ?_))
                rw [sum_marg_slice P S X.2 x]
            _ = ∑ X : S, ∑ s : (∀ i : S, α i), marg P S s * Real.logb 2 (attrMarg P X (s X)) := by
                refine Finset.sum_congr rfl (fun X hX => ?_)
                rw [sum_fiber_mul S (marg P S) X X.2 (fun x => Real.logb 2 (attrMarg P X x))]
            _ = ∑ s : (∀ i : S, α i), ∑ X : S, marg P S s * Real.logb 2 (attrMarg P X (s X)) := by
                rw [Finset.sum_comm]
            _ = ∑ s : (∀ i : S, α i), marg P S s * ∑ X : S, Real.logb 2 (attrMarg P X (s X)) := by
                refine Finset.sum_congr rfl (fun s hs => ?_)
                rw [← Finset.mul_sum]
        rw [hqterm, Finset.sum_sub_distrib]
    _ = ∑ s : (∀ i : S, α i),
        marg P S s * Real.logb 2 (marg P S s / ∏ X : S, attrMarg P X (s X)) := by
        refine Finset.sum_congr rfl (fun s hs => ?_)
        by_cases hm0 : marg P S s = 0
        · rw [hm0]
          simp
        · have hmp : 0 < marg P S s := by
            exact lt_of_le_of_ne (by unfold marg; exact Finset.sum_nonneg (fun a ha => hP.1 a))
              (Ne.symm hm0)
          have hqpos : ∀ X : S, 0 < attrMarg P X (s X) := by
            intro X
            exact lt_of_lt_of_le hmp (marg_le_attrMarg P hP S X X.2 s)
          have hprodpos : 0 < ∏ X : S, attrMarg P X (s X) := Finset.prod_pos (fun X hX => hqpos X)
          rw [Real.logb_div (ne_of_gt hmp) (ne_of_gt hprodpos)]
          rw [Real.logb_prod (Finset.univ : Finset S) (fun X => attrMarg P X (s X)) (fun X hX => ne_of_gt (hqpos X))]
          rw [← mul_sub]

/-- Clause (c), first half: the total correlation is nonnegative. -/
lemma C_nonneg (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (S : Finset ι) : 0 ≤ C P S := by
  classical
  rw [C_eq_relEnt P hP S]
  have hmpos : ∀ s : (∀ i : S, α i), 0 ≤ marg P S s := by
    intro s
    unfold marg
    exact Finset.sum_nonneg (fun a ha => hP.1 a)
  have hqpos : ∀ s : (∀ i : S, α i), 0 ≤ ∏ X : S, attrMarg P X (s X) := by
    intro s
    exact Finset.prod_nonneg (fun X hX => by
      unfold attrMarg
      exact Finset.sum_nonneg (fun a ha => hP.1 a))
  have hsupp : ∀ s : (∀ i : S, α i), 0 < marg P S s → 0 < ∏ X : S, attrMarg P X (s X) := by
    intro s hmp
    exact Finset.prod_pos (fun X hX => lt_of_lt_of_le hmp (marg_le_attrMarg P hP S X X.2 s))
  have hG := (gibbs (marg P S) (fun s => ∏ X : S, attrMarg P X (s X))
    hmpos hqpos (sum_marg P hP S) (sum_prod_attrMarg P hP S) hsupp).1
  have hconv : (∑ s : (∀ i : S, α i),
      marg P S s * Real.logb 2 (marg P S s / ∏ X : S, attrMarg P X (s X)))
      = (∑ s : (∀ i : S, α i),
        marg P S s * Real.log (marg P S s / ∏ X : S, attrMarg P X (s X))) / Real.log 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [Real.logb]
    ring
  rw [hconv]
  exact div_nonneg hG (le_of_lt (Real.log_pos one_lt_two))

/-- Clause (c), second half: the total correlation vanishes exactly for independent
attributes. -/
lemma C_eq_zero_iff (P : (∀ i, α i) → ℝ) (hP : IsLaw P) (S : Finset ι) :
    (C P S = 0 ↔ ∀ s : (∀ i : S, α i), marg P S s = ∏ X : S, attrMarg P X (s X)) := by
  classical
  have hmpos : ∀ s : (∀ i : S, α i), 0 ≤ marg P S s := by
    intro s
    unfold marg
    exact Finset.sum_nonneg (fun a ha => hP.1 a)
  have hqpos : ∀ s : (∀ i : S, α i), 0 ≤ ∏ X : S, attrMarg P X (s X) := by
    intro s
    exact Finset.prod_nonneg (fun X hX => by
      unfold attrMarg
      exact Finset.sum_nonneg (fun a ha => hP.1 a))
  have hsupp : ∀ s : (∀ i : S, α i), 0 < marg P S s → 0 < ∏ X : S, attrMarg P X (s X) := by
    intro s hmp
    exact Finset.prod_pos (fun X hX => lt_of_lt_of_le hmp (marg_le_attrMarg P hP S X X.2 s))
  constructor
  · intro hC0
    rw [C_eq_relEnt P hP S] at hC0
    have hsumlog : (∑ s : (∀ i : S, α i),
        marg P S s * Real.log (marg P S s / ∏ X : S, attrMarg P X (s X))) = 0 := by
      have h' : (∑ s : (∀ i : S, α i),
          marg P S s * (Real.log (marg P S s / ∏ X : S, attrMarg P X (s X)) / Real.log 2)) = 0 := by
        simpa [Real.logb] using hC0
      have h'' : (∑ s : (∀ i : S, α i),
          marg P S s * Real.log (marg P S s / ∏ X : S, attrMarg P X (s X))) / Real.log 2 = 0 := by
        rw [← h']
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun s hs => ?_)
        ring
      have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
      rcases div_eq_zero_iff.mp h'' with hA | hB
      · exact hA
      · exact (hlog2 hB).elim
    have hEq := (gibbs (marg P S) (fun s => ∏ X : S, attrMarg P X (s X))
      hmpos hqpos (sum_marg P hP S) (sum_prod_attrMarg P hP S) hsupp).2 hsumlog
    intro s
    exact congrFun hEq s
  · intro h
    rw [C_eq_relEnt P hP S]
    refine Finset.sum_eq_zero (fun s hs => ?_)
    rw [h s]
    by_cases hq0 : (∏ X : S, attrMarg P X (s X)) = 0
    · rw [hq0]
      simp
    · have hqpos' : 0 < ∏ X : S, attrMarg P X (s X) :=
        lt_of_le_of_ne (hqpos s) (Ne.symm hq0)
      rw [div_self (ne_of_gt hqpos'), Real.logb_one, mul_zero]

end JakulinBratko

/-- The platform solution: Jakulin–Bratko, arXiv:cs/0308002v3, §2.4, Eqs. (10)–(11). -/
theorem solution (ι : Type*) [Fintype ι] [DecidableEq ι] (α : ι → Type*)
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (hP : JakulinBratko.IsLaw P)
    (S : Finset ι) :
    JakulinBratko.C P S = ∑ T ∈ S.powerset with 2 ≤ T.card, JakulinBratko.I P T ∧
    (2 ≤ S.card → ∀ X ∈ S, JakulinBratko.I P S = JakulinBratko.condI P X (S.erase X) - JakulinBratko.I P (S.erase X)) ∧
    0 ≤ JakulinBratko.C P S ∧
    (JakulinBratko.C P S = 0 ↔ ∀ s : (∀ i : S, α i), JakulinBratko.marg P S s = ∏ X : S, JakulinBratko.attrMarg P X (s X)) := by
  constructor
  · exact JakulinBratko.totalCorrelation_eq P hP S
  · constructor
    · intro hS X hX
      exact JakulinBratko.mcgill P hP S hS X hX
    · constructor
      · exact JakulinBratko.C_nonneg P hP S
      · exact JakulinBratko.C_eq_zero_iff P hP S

