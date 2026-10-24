-- Prove2me | solution 1 for MultiChoiceSecretary.Alg.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T02:12:04.395779+00:00
-- url     : https://prove2.me/submissions/f35662d3-f612-4bd2-985e-a94802d347cb

import Mathlib
import Definitions.Def_MultiChoiceSecretary_Alg_Setting
set_option autoImplicit false


-- BEGIN PMFCore

open scoped BigOperators ENNReal
open MultiChoiceSecretary.Alg SecretaryWD.DiscUpper

namespace SecretaryProof

noncomputable def expectation {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (p a).toReal * f a

noncomputable def RC (S : Finset ℝ) (k r : ℕ) : ℝ :=
  uniformAvg fun π =>
    expectation (alg k S.card (arrivals S π)) fun a =>
      ((a.filter fun t => arrivals S π t ∈ topK S r).card : ℝ)

lemma mass_ne_top {α : Type*} (p : PMF α) (a : α) : p a ≠ ∞ :=
  ne_of_lt ((p.coe_le_one a).trans_lt ENNReal.one_lt_top)

lemma mass_sum {α : Type*} [Fintype α] (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => mass_ne_top p a)]
  have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h, ENNReal.toReal_one]

lemma expectation_const {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) :
    expectation p (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul, mass_sum]

lemma expectation_add {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    expectation p (fun a => f a + g a) = expectation p f + expectation p g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_smul {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) (f : α → ℝ) :
    expectation p (fun a => c * f a) = c * expectation p f := by
  simp only [expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma expectation_mono {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a ≤ g a) : expectation p f ≤ expectation p g := by
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : p a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonneg_left (h a (by simpa using ha)) ENNReal.toReal_nonneg

lemma expectation_nonneg {α : Type*} [Fintype α] (p : PMF α) {f : α → ℝ}
    (h : ∀ a ∈ p.support, 0 ≤ f a) : 0 ≤ expectation p f := by
  simpa only [expectation_const] using expectation_mono p h

lemma expectation_pure {α : Type*} [Fintype α] (a : α) (f : α → ℝ) :
    expectation (PMF.pure a) f = f a := by
  classical
  simp [expectation, PMF.pure_apply, apply_ite]

lemma expectation_bind {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    expectation (p.bind q) f = expectation p (fun a => expectation (q a) f) := by
  classical
  simp only [expectation, PMF.bind_apply, tsum_fintype]
  simp_rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (mass_ne_top p a) (mass_ne_top (q a) _)),
    ENNReal.toReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [Finset.mul_sum, mul_assoc]

lemma expectation_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (f : β → ℝ) :
    expectation (p.map g) f = expectation p (fun a => f (g a)) := by
  rw [PMF.map, expectation_bind]
  simp only [Function.comp_apply, expectation_pure]

lemma uniform_nonneg {n : ℕ} {f : Equiv.Perm (Fin n) → ℝ}
    (h : ∀ π, 0 ≤ f π) : 0 ≤ uniformAvg f := by
  unfold uniformAvg
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun π _ => h π)

lemma RC_nonneg (S : Finset ℝ) (k r : ℕ) : 0 ≤ RC S k r := by
  apply uniform_nonneg
  exact fun π => expectation_nonneg _ (fun a _ => Nat.cast_nonneg _)

lemma stageWith_expectation
    (rec : (m : ℕ) → (Fin m → ℝ) → PMF (Finset (Fin m)))
    (k n : ℕ) (x : Fin n → ℝ) (f : Finset (Fin n) × Finset (Fin n) → ℝ) :
    expectation (stageWith rec k n x) f =
      ∑ m : Fin (n+1), ((n.choose m.val : ℝ) / (2:ℝ)^n) *
        expectation (rec m.val (fun i => x (Fin.castLE m.is_le i))) (fun A =>
          f (A.map (Fin.castLEEmb m.is_le),
            phase2 k x m.val (kth x m.val (k/2)) (A.map (Fin.castLEEmb m.is_le)))) := by
  classical
  rw [stageWith, expectation_bind]
  simp only [expectation_map]
  unfold expectation
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  change (↑((1/2:NNReal)^m.val * (1-1/2)^(n-m.val) *
    (n.choose m.val : NNReal)) : ENNReal).toReal = _
  norm_num only [ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_natCast]
  norm_num
  rw [← pow_add, Nat.add_sub_of_le m.is_le]
  rw [div_pow, one_pow]
  ring

end SecretaryProof
-- END PMFCore

-- BEGIN NativeCapRank

open MultiChoiceSecretary.Alg
namespace SecretaryProof

lemma before_strict {α : Type*} [LinearOrder α] (A : Finset α) {a b : α}
    (ha : a ∈ A) (hab : a < b) :
    (A.filter (· < a)).card < (A.filter (· < b)).card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans hab⟩
  · intro h
    have : a ∈ A.filter (· < b) := by simp [ha, hab]
    rw [← h] at this
    simp at this

lemma first_card_le {α : Type*} [LinearOrder α] (A : Finset α) (c : ℕ) :
    (A.filter fun a => (A.filter (· < a)).card < c).card ≤ c := by
  classical
  let B := A.filter fun a => (A.filter (· < a)).card < c
  have hinj : Function.Injective (fun a : B =>
      (⟨(A.filter (· < a.val)).card, (Finset.mem_filter.mp a.property).2⟩ : Fin c)) := by
    intro a b h
    apply Subtype.ext
    have he := congrArg Fin.val h
    dsimp only at he
    rcases lt_trichotomy a.val b.val with hab | hab | hab
    · have := before_strict A (Finset.mem_filter.mp a.property).1 hab
      omega
    · exact hab
    · have := before_strict A (Finset.mem_filter.mp b.property).1 hab
      omega
  have := Fintype.card_le_of_injective _ hinj
  simpa using this

lemma phase2_card_le {n : ℕ} (k : ℕ) (x : Fin n → ℝ) (m : ℕ)
    (thr : Option ℝ) (S1 : Finset (Fin n)) :
    (phase2 k x m thr S1).card ≤ k - S1.card := by
  classical
  let A := Finset.univ.filter fun t : Fin n => m ≤ t.val ∧ exceeds thr (x t)
  have hEq : phase2 k x m thr S1 = A.filter fun t =>
      (A.filter (· < t)).card < k-S1.card := by
    ext t
    simp only [phase2, Finset.mem_filter, Finset.mem_univ, true_and, A]
    have he : (Finset.univ.filter fun t' : Fin n =>
        m ≤ t'.val ∧ t' < t ∧ exceeds thr (x t')).card =
        ((Finset.univ.filter fun t' : Fin n => m ≤ t'.val ∧ exceeds thr (x t')).filter (· < t)).card := by
      congr 1
      ext t'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [he]
    constructor
    · rintro ⟨hm, ht, hc⟩
      exact ⟨⟨hm, ht⟩, by omega⟩
    · rintro ⟨⟨hm, ht⟩, hc⟩
      exact ⟨hm, ht, by omega⟩
  rw [hEq]
  exact first_card_le A _

lemma fixed_cap_subset {n : ℕ} (k c : ℕ) (x : Fin n → ℝ) (m : ℕ)
    (thr : Option ℝ) (S1 : Finset (Fin n)) (hc : S1.card + c ≤ k) :
    phase2 c x m thr ∅ ⊆ phase2 k x m thr S1 := by
  intro t ht
  simp only [phase2, Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_empty,
    zero_add] at ht ⊢
  exact ⟨ht.1, ht.2.1, by omega⟩

lemma alg_card_le (k n : ℕ) (x : Fin n → ℝ) (B : Finset (Fin n))
    (hB : B ∈ (alg k n x).support) : B.card ≤ k := by
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    match k with
    | 0 => simpa [alg] using hB
    | 1 =>
      have he : B = (SecretaryWD.DiscUpper.classicalSecretary n x).toFinset := by
        simpa [alg] using hB
      rw [he]
      cases SecretaryWD.DiscUpper.classicalSecretary n x <;> simp
    | k+2 =>
      rw [alg] at hB
      simp only [PMF.mem_support_map_iff] at hB
      obtain ⟨p, hp, rfl⟩ := hB
      rw [stageWith] at hp
      simp only [PMF.mem_support_bind_iff] at hp
      obtain ⟨m, _, hm⟩ := hp
      simp only [PMF.mem_support_map_iff] at hm
      obtain ⟨A, hA, rfl⟩ := hm
      have hAc := ih ((k+2)/2) (by omega) m.val
        (fun i => x (Fin.castLE m.is_le i)) A hA
      have hmap : (A.map (Fin.castLEEmb m.is_le)).card ≤ k+2 := by
        rw [Finset.card_map]
        omega
      have hpc := phase2_card_le (k+2) x m.val (kth x m.val ((k+2)/2))
        (A.map (Fin.castLEEmb m.is_le))
      have hu := Finset.card_union_le (A.map (Fin.castLEEmb m.is_le))
        (phase2 (k+2) x m.val (kth x m.val ((k+2)/2)) (A.map (Fin.castLEEmb m.is_le)))
      exact hu.trans (by omega)

lemma prefix_phase2_disjoint {n m : ℕ} (hm : m ≤ n) (A : Finset (Fin m))
    (k : ℕ) (x : Fin n → ℝ) (thr : Option ℝ) :
    Disjoint (A.map (Fin.castLEEmb hm))
      (phase2 k x m thr (A.map (Fin.castLEEmb hm))) := by
  apply Finset.disjoint_left.mpr
  intro t ht hp
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp ht
  have htv : t.val < m := by
    rw [← hi]
    exact i.is_lt
  have hpm : m ≤ t.val := (Finset.mem_filter.mp hp).2.1
  omega

lemma prefix_card_eq {n m : ℕ} (hm : m ≤ n) (A : Finset (Fin m)) :
    (A.map (Fin.castLEEmb hm)).card = A.card := Finset.card_map _

lemma stage_disjoint (k n : ℕ) (x : Fin n → ℝ)
    (p : Finset (Fin n) × Finset (Fin n)) (hp : p ∈ (stage k n x).support) :
    Disjoint p.1 p.2 := by
  rw [stage, stageWith] at hp
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hp
  obtain ⟨m, _, A, _, rfl⟩ := hp
  exact prefix_phase2_disjoint m.is_le A k x _

lemma stage_first_card_le (k n : ℕ) (x : Fin n → ℝ)
    (p : Finset (Fin n) × Finset (Fin n)) (hp : p ∈ (stage k n x).support) :
    p.1.card ≤ k/2 := by
  rw [stage, stageWith] at hp
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hp
  obtain ⟨m, _, A, hA, rfl⟩ := hp
  simpa using alg_card_le (k/2) m.val (fun i => x (Fin.castLE m.is_le i)) A hA

noncomputable def descending (S : Finset ℝ) : Fin S.card → ℝ :=
  Finset.orderEmbOfFin (α := ℝᵒᵈ) S rfl

lemma descending_injective (S : Finset ℝ) : Function.Injective (descending S) :=
  (Finset.orderEmbOfFin (α := ℝᵒᵈ) S rfl).injective

lemma descending_mem (S : Finset ℝ) (i : Fin S.card) : descending S i ∈ S :=
  Finset.orderEmbOfFin_mem (α := ℝᵒᵈ) S rfl i

lemma descending_antitone (S : Finset ℝ) : StrictAnti (descending S) :=
  (Finset.orderEmbOfFin (α := ℝᵒᵈ) S rfl).strictMono

lemma descending_list (S : Finset ℝ) :
    (List.finRange S.card).map (descending S) = S.sort (· ≥ ·) :=
  Finset.listMap_orderEmbOfFin_finRange (α := ℝᵒᵈ) S rfl

lemma descending_topK (S : Finset ℝ) (i : Fin S.card) (r : ℕ) :
    descending S i ∈ topK S r ↔ i.val < r := by
  classical
  have hm : descending S i ∈ S.sort (· ≥ ·) := by
    simpa using descending_mem S i
  rw [topK, List.mem_toFinset, List.mem_take_iff_idxOf_lt hm]
  have he : (S.sort (· ≥ ·)).idxOf (descending S i) = i.val := by
    change (S.sort (· ≥ ·)).idxOf ((S.sort (· ≥ ·))[i.val]'(by rw [Finset.length_sort]; exact i.is_lt)) = i.val
    exact (S.sort_nodup (· ≥ ·)).idxOf_getElem i.val _
  rw [he]

lemma descending_surjective (S : Finset ℝ) (x : ℝ) (hx : x ∈ S) :
    ∃ i : Fin S.card, descending S i = x := by
  obtain ⟨i, hi⟩ := (Finset.orderIsoOfFin (α := ℝᵒᵈ) S rfl).surjective ⟨x,hx⟩
  exact ⟨i, congrArg Subtype.val hi⟩

lemma topK_eq_image (S : Finset ℝ) (r : ℕ) :
    topK S r = (Finset.univ.filter fun i : Fin S.card => i.val < r).image (descending S) := by
  classical
  ext x
  constructor
  · intro hx
    have hxS : x ∈ S := by
      have htake : x ∈ (S.sort (· ≥ ·)).take r := List.mem_toFinset.mp hx
      have hs := List.mem_of_mem_take htake
      simpa using hs
    obtain ⟨i,rfl⟩ := descending_surjective S x hxS
    exact Finset.mem_image.mpr ⟨i, by simpa using (descending_topK S i r).mp hx, rfl⟩
  · rintro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact (descending_topK S i r).mpr (by simpa using hi)

lemma topSum_descending (S : Finset ℝ) (k : ℕ) :
    topSum S k = ∑ i : Fin S.card, if i.val < k then descending S i else 0 := by
  classical
  have he : ∑ x ∈ topK S k, x = topSum S k := by
    unfold topK topSum
    simpa using List.sum_toFinset (fun x : ℝ => x) ((S.sort_nodup (· ≥ ·)).take (i := k))
  rw [← he, topK_eq_image, Finset.sum_image]
  · exact Finset.sum_filter _ _
  · intro i _ j _ h
    exact descending_injective S h

end SecretaryProof
-- END NativeCapRank

-- BEGIN PermutationSplit

open scoped Classical
namespace SecretaryProof
namespace Split

structure Data (α β γ : Type*) where
  label : γ → Bool
  left : α ≃ {x : γ // label x = true}
  right : β ≃ {x : γ // label x = false}

noncomputable def join {α β γ : Type*} (d : Data α β γ) : (α ⊕ β) ≃ γ :=
  Equiv.ofBijective (Sum.elim (fun a => (d.left a).val) (fun b => (d.right b).val)) (by
    constructor
    · intro x y h
      cases x with
      | inl a =>
        cases y with
        | inl a' => exact congrArg Sum.inl (d.left.injective (Subtype.ext h))
        | inr b =>
          have h1 := (d.left a).property
          have h2 := (d.right b).property
          dsimp only [Sum.elim_inl, Sum.elim_inr] at h
          rw [h] at h1
          simp_all
      | inr b =>
        cases y with
        | inl a =>
          have h1 := (d.left a).property
          have h2 := (d.right b).property
          dsimp only [Sum.elim_inl, Sum.elim_inr] at h
          rw [h] at h2
          simp_all
        | inr b' => exact congrArg Sum.inr (d.right.injective (Subtype.ext h))
    · intro x
      cases hx : d.label x with
      | false => exact ⟨Sum.inr (d.right.symm ⟨x,hx⟩), congrArg Subtype.val (d.right.apply_symm_apply _)⟩
      | true => exact ⟨Sum.inl (d.left.symm ⟨x,hx⟩), congrArg Subtype.val (d.left.apply_symm_apply _)⟩)

@[simp] lemma join_inl {α β γ : Type*} (d : Data α β γ) (a : α) :
    join d (Sum.inl a) = (d.left a).val := rfl
@[simp] lemma join_inr {α β γ : Type*} (d : Data α β γ) (b : β) :
    join d (Sum.inr b) = (d.right b).val := rfl

noncomputable def split {α β γ : Type*} (e : (α ⊕ β) ≃ γ) : Data α β γ where
  label := fun x => (e.symm x).isLeft
  left :=
    { toFun := fun a => ⟨e (.inl a), by simp⟩
      invFun := fun x => (e.symm x.val).getLeft (by simpa using x.property)
      left_inv := by intro a; simp
      right_inv := by
        intro x
        apply Subtype.ext
        have h := x.property
        cases he : e.symm x.val with
        | inl a => simpa [he] using e.apply_symm_apply x.val
        | inr b => simp [he] at h }
  right :=
    { toFun := fun b => ⟨e (.inr b), by simp⟩
      invFun := fun x => (e.symm x.val).getRight (by simpa using x.property)
      left_inv := by intro b; simp
      right_inv := by
        intro x
        apply Subtype.ext
        have h := x.property
        cases he : e.symm x.val with
        | inl a => simp [he] at h
        | inr b => simpa [he] using e.apply_symm_apply x.val }

@[simp] theorem join_split {α β γ : Type*} (e : (α ⊕ β) ≃ γ) :
    join (split e) = e := by
  ext x
  cases x <;> rfl

theorem join_injective {α β γ : Type*} : Function.Injective (@join α β γ) := by
  intro d e he
  rcases d with ⟨p, l, r⟩
  rcases e with ⟨q, l', r'⟩
  have hp : p = q := by
    funext x
    cases hx : p x with
    | false =>
      obtain ⟨b, hb⟩ := r.surjective ⟨x,hx⟩
      have hv : (r b).val = x := congrArg Subtype.val hb
      have hh : (r b).val = (r' b).val := congrArg (fun f => f (.inr b)) he
      have hq := (r' b).property
      rw [← hh, hv] at hq
      exact hq.symm
    | true =>
      obtain ⟨a, ha⟩ := l.surjective ⟨x,hx⟩
      have hv : (l a).val = x := congrArg Subtype.val ha
      have hh : (l a).val = (l' a).val := congrArg (fun f => f (.inl a)) he
      have hq := (l' a).property
      rw [← hh, hv] at hq
      exact hq.symm
  subst q
  have hl : l = l' := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    exact congrArg (fun f => f (.inl a)) he
  have hr : r = r' := by
    apply Equiv.ext
    intro b
    apply Subtype.ext
    exact congrArg (fun f => f (.inr b)) he
  subst l'
  subst r'
  rfl

@[simp] theorem split_join {α β γ : Type*} (d : Data α β γ) : split (join d) = d :=
  join_injective (join_split _)

noncomputable def equiv {α β γ : Type*} : ((α ⊕ β) ≃ γ) ≃ Data α β γ where
  toFun := split
  invFun := join
  left_inv := join_split
  right_inv := split_join

noncomputable def sigmaEquiv {α β γ : Type*} : Data α β γ ≃
    Σ p : γ → Bool, (α ≃ {x // p x = true}) × (β ≃ {x // p x = false}) where
  toFun d := ⟨d.label, d.left, d.right⟩
  invFun d := ⟨d.1, d.2.1, d.2.2⟩
  left_inv := by intro d; cases d; rfl
  right_inv := by intro d; cases d with | mk p e => cases e; rfl

noncomputable instance {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] :
    Fintype (Data α β γ) := Fintype.ofEquiv ((α ⊕ β) ≃ γ) equiv

lemma sum_split {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : Data α β γ → ℝ) :
    ∑ e : ((α ⊕ β) ≃ γ), f (split e) =
      ∑ p : γ → Bool, ∑ l : α ≃ {x // p x = true},
        ∑ r : β ≃ {x // p x = false}, f ⟨p,l,r⟩ := by
  classical
  calc
    _ = ∑ d : Data α β γ, f d := Equiv.sum_comp equiv f
    _ = ∑ d : (Σ p : γ → Bool, (α ≃ {x // p x = true}) ×
        (β ≃ {x // p x = false})), f (sigmaEquiv.symm d) :=
      (Equiv.sum_comp sigmaEquiv.symm f).symm
    _ = _ := by simp [Fintype.sum_sigma, Fintype.sum_prod_type, sigmaEquiv]

noncomputable def positions {n m : ℕ} (hm : m ≤ n) :
    (Fin m ⊕ Fin (n-m)) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hm))

@[simp] lemma positions_inl {n m : ℕ} (hm : m ≤ n) (i : Fin m) :
    positions hm (.inl i) = Fin.castLE hm i := by
  apply Fin.ext
  rfl

@[simp] lemma positions_inr_val {n m : ℕ} (hm : m ≤ n) (i : Fin (n-m)) :
    (positions hm (.inr i)).val = m + i.val := rfl

noncomputable def permutation {n m : ℕ} (hm : m ≤ n) :
    Equiv.Perm (Fin n) ≃ Data (Fin m) (Fin (n-m)) (Fin n) :=
  (Equiv.equivCongr (positions hm).symm (Equiv.refl _)).trans equiv

@[simp] theorem permutation_left {n m : ℕ} (hm : m ≤ n)
    (π : Equiv.Perm (Fin n)) (i : Fin m) :
    ((permutation hm π).left i).val = π (Fin.castLE hm i) := rfl

lemma label_true_iff {α β γ : Type*} (d : Data α β γ) (x : γ) :
    d.label x = true ↔ ∃ a, (d.left a).val = x := by
  constructor
  · intro hx
    exact ⟨d.left.symm ⟨x,hx⟩, congrArg Subtype.val (d.left.apply_symm_apply _)⟩
  · rintro ⟨a, rfl⟩
    exact (d.left a).property

lemma prefix_label {n m : ℕ} (hm : m ≤ n) (π : Equiv.Perm (Fin n)) (x : Fin n) :
    (permutation hm π).label x = true ↔ ∃ i : Fin m, π (Fin.castLE hm i) = x := by
  simpa only [permutation_left] using label_true_iff (permutation hm π) x

lemma sum_permutation {n m : ℕ} (hm : m ≤ n)
    (f : Data (Fin m) (Fin (n-m)) (Fin n) → ℝ) :
    ∑ π : Equiv.Perm (Fin n), f (permutation hm π) =
      ∑ p : Fin n → Bool, ∑ l : Fin m ≃ {x // p x = true},
        ∑ r : Fin (n-m) ≃ {x // p x = false}, f ⟨p,l,r⟩ := by
  classical
  calc
    _ = ∑ d : Data (Fin m) (Fin (n-m)) (Fin n), f d :=
      Equiv.sum_comp (permutation hm) f
    _ = ∑ e : ((Fin m ⊕ Fin (n-m)) ≃ Fin n), f (split e) :=
      (Equiv.sum_comp equiv f).symm
    _ = _ := sum_split (α := Fin m) (β := Fin (n-m)) (γ := Fin n) f

lemma label_card {n m : ℕ} (hm : m ≤ n) (π : Equiv.Perm (Fin n)) :
    Fintype.card {x // (permutation hm π).label x = true} = m := by
  simpa using (Fintype.card_congr (permutation hm π).left).symm

lemma bool_card_compl {n : ℕ} (p : Fin n → Bool) :
    Fintype.card {x // p x = false} = n - Fintype.card {x // p x = true} := by
  simpa only [Bool.not_eq_true, Fintype.card_fin] using
    Fintype.card_subtype_compl (fun x => p x = true)

lemma label_fiber_card {n m : ℕ} (_hm : m ≤ n) (p : Fin n → Bool)
    (hp : Fintype.card {x // p x = true} = m) :
    Fintype.card (Fin m ≃ {x // p x = true}) *
      Fintype.card (Fin (n-m) ≃ {x // p x = false}) = m.factorial * (n-m).factorial := by
  have hl : Fintype.card (Fin m) = Fintype.card {x // p x = true} := by simpa using hp.symm
  have hr : Fintype.card (Fin (n-m)) = Fintype.card {x // p x = false} := by
    rw [bool_card_compl, hp, Fintype.card_fin]
  rw [Fintype.card_equiv (Fintype.equivOfCardEq hl),
    Fintype.card_equiv (Fintype.equivOfCardEq hr)]
  simp

lemma binomial_factor {n m : ℕ} (hm : m ≤ n) :
    ((n.choose m : ℝ) / (2:ℝ)^n) * (1 / (n.factorial : ℝ)) =
      (1 / (2:ℝ)^n) * (1 / ((m.factorial : ℝ) * ((n-m).factorial : ℝ))) := by
  have h : (n.choose m : ℝ) * (m.factorial : ℝ) * ((n-m).factorial : ℝ) =
      (n.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hm
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hm0 : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hd : ((n-m).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-m)
  have htwo : (2:ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  nlinarith

lemma weighted_permutation (n : ℕ)
    (f : (m : Fin (n+1)) → Data (Fin m.val) (Fin (n-m.val)) (Fin n) → ℝ) :
    (∑ m : Fin (n+1), ((n.choose m.val : ℝ)/(2:ℝ)^n) *
      ((1/(n.factorial:ℝ)) * ∑ π : Equiv.Perm (Fin n), f m (permutation m.is_le π))) =
    (1/(2:ℝ)^n) * ∑ p : Fin n → Bool, ∑ m : Fin (n+1),
      (1/((m.val.factorial:ℝ)*((n-m.val).factorial:ℝ))) *
      ∑ l : Fin m.val ≃ {x // p x = true},
        ∑ r : Fin (n-m.val) ≃ {x // p x = false}, f m ⟨p,l,r⟩ := by
  simp_rw [sum_permutation]
  have hc : ∀ m : Fin (n+1), ((n.choose m.val : ℝ)/(2:ℝ)^n) * (1/(n.factorial:ℝ)) =
      (1/(2:ℝ)^n) * (1/((m.val.factorial:ℝ)*((n-m.val).factorial:ℝ))) :=
    fun m => binomial_factor m.is_le
  simp_rw [← mul_assoc]
  simp_rw [hc]
  simp_rw [mul_assoc, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma true_card_le {n : ℕ} (p : Fin n → Bool) :
    Fintype.card {x // p x = true} ≤ n := by
  simpa using Fintype.card_subtype_le (fun x : Fin n => p x = true)

lemma fiber_zero {n m : ℕ} (p : Fin n → Bool)
    (hp : Fintype.card {x // p x = true} ≠ m)
    (f : (Fin m ≃ {x // p x = true}) → (Fin (n-m) ≃ {x // p x = false}) → ℝ) :
    (∑ l, ∑ r, f l r) = 0 := by
  let : IsEmpty (Fin m ≃ {x // p x = true}) := ⟨fun e => hp (by
    simpa using (Fintype.card_congr e).symm)⟩
  simp

lemma fiber_one {n m : ℕ} (hm : m ≤ n) (p : Fin n → Bool)
    (hp : Fintype.card {x // p x = true} = m) :
    (1/((m.factorial:ℝ)*((n-m).factorial:ℝ))) *
      (∑ _l : Fin m ≃ {x // p x = true},
        ∑ _r : Fin (n-m) ≃ {x // p x = false}, (1:ℝ)) = 1 := by
  have h := label_fiber_card hm p hp
  have hr : (Fintype.card (Fin m ≃ {x // p x = true}) : ℝ) *
      (Fintype.card (Fin (n-m) ≃ {x // p x = false}) : ℝ) =
      (m.factorial:ℝ)*((n-m).factorial:ℝ) := by exact_mod_cast h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hr]
  have hm0 : (m.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hd0 : ((n-m).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-m)
  exact one_div_mul_cancel (mul_ne_zero hm0 hd0)

lemma fiber_total (n : ℕ) (p : Fin n → Bool) :
    (∑ m : Fin (n+1), (1/((m.val.factorial:ℝ)*((n-m.val).factorial:ℝ))) *
      (∑ _l : Fin m.val ≃ {x // p x = true},
        ∑ _r : Fin (n-m.val) ≃ {x // p x = false}, (1:ℝ))) = 1 := by
  let m₀ : Fin (n+1) := ⟨Fintype.card {x // p x = true}, Nat.lt_succ_of_le (true_card_le p)⟩
  rw [Finset.sum_eq_single m₀]
  · exact fiber_one m₀.is_le p rfl
  · intro m _ hne
    have hn : Fintype.card {x // p x = true} ≠ m.val := by
      intro he
      apply hne
      exact Fin.ext he.symm
    rw [fiber_zero p hn]
    simp
  · simp

lemma label_expectation (n : ℕ) (g : (Fin n → Bool) → ℝ) :
    (∑ m : Fin (n+1), ((n.choose m.val : ℝ)/(2:ℝ)^n) *
      ((1/(n.factorial:ℝ)) * ∑ π : Equiv.Perm (Fin n),
        g (permutation m.is_le π).label)) =
    (1/(2:ℝ)^n) * ∑ p : Fin n → Bool, g p := by
  rw [weighted_permutation n (fun _ d => g d.label)]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  have h := congrArg (fun x : ℝ => x * g p) (fiber_total n p)
  simpa only [Finset.sum_mul, mul_assoc, one_mul] using h

@[simp] theorem permutation_right {n m : ℕ} (hm : m ≤ n)
    (π : Equiv.Perm (Fin n)) (i : Fin (n-m)) :
    ((permutation hm π).right i).val = π (positions hm (.inr i)) := rfl

lemma label_false_iff {α β γ : Type*} (d : Data α β γ) (x : γ) :
    d.label x = false ↔ ∃ a, (d.right a).val = x := by
  constructor
  · intro hx
    exact ⟨d.right.symm ⟨x,hx⟩, congrArg Subtype.val (d.right.apply_symm_apply _)⟩
  · rintro ⟨a, rfl⟩
    exact (d.right a).property

lemma suffix_label {n m : ℕ} (hm : m ≤ n) (π : Equiv.Perm (Fin n)) (t : Fin n) :
    (permutation hm π).label (π t) = false ↔ m ≤ t.val := by
  rw [label_false_iff]
  simp only [permutation_right, π.injective.eq_iff]
  constructor
  · rintro ⟨i,he⟩
    have := congrArg Fin.val he
    simp only [positions_inr_val] at this
    omega
  · intro ht
    refine ⟨⟨t.val-m, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [positions_inr_val]
    omega

end Split
end SecretaryProof
-- END PermutationSplit

-- BEGIN BooleanMoments

namespace SecretaryProof

noncomputable def fairAvg {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ b, f b

theorem fairAvg_add {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    fairAvg (fun b => f b + g b) = fairAvg f + fairAvg g := by
  simp only [fairAvg, Finset.sum_add_distrib, mul_add]

theorem fairAvg_mul_const {n : ℕ} (f : (Fin n → Bool) → ℝ) (c : ℝ) :
    fairAvg (fun b => f b * c) = fairAvg f * c := by
  simp only [fairAvg, Finset.sum_mul, mul_assoc]

theorem fairAvg_const {n : ℕ} (c : ℝ) : fairAvg (n := n) (fun _ => c) = c := by
  simp [fairAvg]

theorem fairAvg_mono {n : ℕ} {f g : (Fin n → Bool) → ℝ} (h : ∀ b, f b ≤ g b) :
    fairAvg f ≤ fairAvg g := by
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => h b)
  positivity

def flip {n : ℕ} (i : Fin n) (b : Fin n → Bool) : Fin n → Bool :=
  Function.update b i (!(b i))

theorem flip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flip i) := by
  intro b
  funext j
  by_cases h : j = i
  · subst j; simp [flip]
  · simp [flip, h]

theorem fairAvg_flip {n : ℕ} (i : Fin n) (f : (Fin n → Bool) → ℝ) :
    fairAvg (fun b => f (flip i b)) = fairAvg f := by
  unfold fairAvg
  congr 1
  exact (show (Fin n → Bool) ≃ (Fin n → Bool) from
    ⟨flip i, flip i, flip_involutive i, flip_involutive i⟩).sum_comp f

def sign (b : Bool) : ℝ := if b then 1 else -1

theorem sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> norm_num [sign]

theorem fairAvg_predictable_sign {n : ℕ} (i : Fin n) (f : (Fin n → Bool) → ℝ)
    (hf : ∀ b, f (flip i b) = f b) :
    fairAvg (fun b => f b * sign (b i)) = 0 := by
  have h := fairAvg_flip i (fun b => f b * sign (b i))
  have he : (fun b => f (flip i b) * sign (flip i b i)) =
      (fun b => (f b * sign (b i)) * (-1)) := by
    funext b
    rw [hf b]
    simp [flip, sign_not]
  rw [he, fairAvg_mul_const] at h
  linarith

theorem fairAvg_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin n → Bool) → ℝ) :
    fairAvg (fun b => ∑ i ∈ s, f i b) = ∑ i ∈ s, fairAvg (f i) := by
  unfold fairAvg
  rw [Finset.sum_comm, Finset.mul_sum]

theorem fairAvg_neg {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    fairAvg (fun b => -f b) = -fairAvg f := by
  simp [fairAvg]

theorem fairAvg_sign {n : ℕ} (i : Fin n) : fairAvg (fun b => sign (b i)) = 0 := by
  simpa using fairAvg_predictable_sign i (fun _ => 1) (fun _ => rfl)

theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by cases b <;> norm_num [sign]

theorem predictable_cross_zero {n : ℕ} (i j : Fin n) (hij : i < j)
    (a : Fin n → (Fin n → Bool) → ℝ)
    (ha : ∀ i j, i ≤ j → ∀ b, a i (flip j b) = a i b) :
    fairAvg (fun b => (a i b * sign (b i)) * (a j b * sign (b j))) = 0 := by
  have h := fairAvg_predictable_sign j (fun b => a i b * sign (b i) * a j b) (by
    intro b
    rw [ha i j hij.le b, ha j j le_rfl b]
    simp [flip, ne_of_lt hij])
  simpa only [mul_assoc] using h

theorem predictable_sum_mean {n : ℕ}
    (a : Fin n → (Fin n → Bool) → ℝ)
    (ha : ∀ i j, i ≤ j → ∀ b, a i (flip j b) = a i b) :
    fairAvg (fun b => ∑ i, a i b * sign (b i)) = 0 := by
  rw [fairAvg_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact fairAvg_predictable_sign i (a i) (ha i i le_rfl)

theorem predictable_sum_second {n : ℕ}
    (a : Fin n → (Fin n → Bool) → ℝ)
    (ha : ∀ i j, i ≤ j → ∀ b, a i (flip j b) = a i b) :
    fairAvg (fun b => (∑ i, a i b * sign (b i)) ^ 2) =
      ∑ i, fairAvg (fun b => (a i b) ^ 2) := by
  simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
  rw [fairAvg_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [fairAvg_sum, Finset.sum_eq_single i]
  · congr 1
    funext b
    have h := sign_sq (b i)
    nlinarith
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · have hz := predictable_cross_zero j i h a ha
      simpa only [mul_comm] using hz
    · exact predictable_cross_zero i j h a ha
  · simp

theorem fairAvg_abs_le_sqrt {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    fairAvg (fun b => |f b|) ≤ Real.sqrt (fairAvg (fun b => f b ^ 2)) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n → Bool))
    (fun b => |f b|) (fun _ => (1 : ℝ))
  simp only [mul_one, sq_abs, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hc : 0 ≤ (1 / (2 : ℝ)^n)^2 := sq_nonneg _
  have hh := mul_le_mul_of_nonneg_left h hc
  push_cast at hh
  have hr : (1 / (2 : ℝ)^n)^2 * ((∑ b, f b ^ 2) * (2 : ℝ)^n) =
      (1 / (2 : ℝ)^n) * ∑ b, f b ^ 2 := by
    field_simp
  rw [hr, ← mul_pow] at hh
  apply (Real.le_sqrt (by unfold fairAvg; positivity) (by unfold fairAvg; positivity)).2
  exact hh

def heads {n : ℕ} (b : Fin n → Bool) (t : ℕ) : ℕ :=
  (Finset.univ.filter fun i => i.val < t ∧ b i = true).card

theorem heads_flip {n : ℕ} (b : Fin n → Bool) (j : Fin n) (t : ℕ) (ht : t ≤ j.val) :
    heads (flip j b) t = heads b t := by
  unfold heads
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i.val < t
  · have hij : i ≠ j := by intro h; subst j; omega
    simp [hi, flip, hij]
  · simp [hi]

def active {n : ℕ} (ell : ℕ) (i : Fin n) (b : Fin n → Bool) : ℝ :=
  if heads b i.val < ell then 1 else 0

theorem active_predictable {n : ℕ} (ell : ℕ) (i j : Fin n) (hij : i ≤ j)
    (b : Fin n → Bool) : active ell i (flip j b) = active ell i b := by
  unfold active
  rw [heads_flip b j i.val hij]

theorem active_sq {n : ℕ} (ell : ℕ) (i : Fin n) (b : Fin n → Bool) :
    active ell i b ^ 2 = active ell i b := by
  unfold active
  split <;> norm_num

def stoppedDifference {n : ℕ} (ell : ℕ) (b : Fin n → Bool) : ℝ :=
  ∑ i, active ell i b * sign (b i)

def inspected {n : ℕ} (ell : ℕ) (b : Fin n → Bool) : ℝ :=
  ∑ i, active ell i b

theorem stopped_mean {n : ℕ} (ell : ℕ) : fairAvg (stoppedDifference (n := n) ell) = 0 :=
  predictable_sum_mean _ (active_predictable ell)

theorem stopped_second {n : ℕ} (ell : ℕ) :
    fairAvg (fun b : Fin n → Bool => stoppedDifference ell b ^ 2) = fairAvg (inspected (n := n) ell) := by
  unfold stoppedDifference
  rw [predictable_sum_second _ (active_predictable ell)]
  simp_rw [active_sq]
  exact (fairAvg_sum Finset.univ (active ell)).symm

theorem heads_strict {n : ℕ} (b : Fin n → Bool) (i j : Fin n)
    (hij : i < j) (hi : b i = true) : heads b i.val < heads b j.val := by
  unfold heads
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨lt_trans hx.1 hij, hx.2⟩
  · intro he
    have hj : i ∈ Finset.univ.filter (fun x : Fin n => x.val < j.val ∧ b x = true) := by
      simp [hij, hi]
    rw [← he] at hj
    simp at hj

def acceptedHeads {n : ℕ} (ell : ℕ) (b : Fin n → Bool) : ℝ :=
  ∑ i, active ell i b * (if b i then 1 else 0)

theorem acceptedHeads_le {n : ℕ} (ell : ℕ) (b : Fin n → Bool) :
    acceptedHeads ell b ≤ ell := by
  let A := Finset.univ.filter fun i : Fin n => heads b i.val < ell ∧ b i = true
  have hc : A.card ≤ ell := by
    have h := Finset.card_le_card_of_injOn (fun i : Fin n => heads b i.val)
      (s := A) (t := Finset.range ell) (by
        intro i hi
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2.1) (by
        intro i hi j hj he
        dsimp only at he
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have hh := heads_strict b i j h (Finset.mem_filter.mp hi).2.2
          omega
        · have hh := heads_strict b j i h (Finset.mem_filter.mp hj).2.2
          omega)
    simpa using h
  have he : acceptedHeads ell b = (A.card : ℝ) := by
    unfold acceptedHeads
    simp only [A, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    unfold active
    split <;> cases hb : b i <;> simp_all
  rw [he]
  exact_mod_cast hc

theorem stopped_difference_identity {n : ℕ} (ell : ℕ) (b : Fin n → Bool) :
    stoppedDifference ell b = 2 * acceptedHeads ell b - inspected ell b := by
  unfold stoppedDifference acceptedHeads inspected
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hb : b i <;> simp [sign] ; ring

theorem inspected_mean_le {n : ℕ} (ell : ℕ) :
    fairAvg (inspected (n := n) ell) ≤ 2 * ell := by
  have he : (fun b : Fin n → Bool => inspected ell b) =
      (fun b => acceptedHeads ell b * 2 - stoppedDifference ell b) := by
    funext b
    linarith [stopped_difference_identity ell b]
  have hh := fairAvg_mono (fun b : Fin n → Bool => acceptedHeads_le ell b)
  rw [fairAvg_const] at hh
  change fairAvg (fun b => inspected ell b) ≤ _
  rw [he]
  simp only [sub_eq_add_neg, fairAvg_add, fairAvg_neg, fairAvg_mul_const, stopped_mean,
    neg_zero, add_zero]
  linarith

theorem stopped_abs_le {n : ℕ} (ell : ℕ) :
    fairAvg (fun b : Fin n → Bool => |stoppedDifference ell b|) ≤ Real.sqrt (2 * ell) := by
  calc
    _ ≤ Real.sqrt (fairAvg (fun b => stoppedDifference ell b ^ 2)) := fairAvg_abs_le_sqrt _
    _ ≤ Real.sqrt (2 * ell) := by
      rw [stopped_second]
      exact Real.sqrt_le_sqrt (inspected_mean_le ell)

theorem head_rank_image {n : ℕ} (b : Fin n → Bool) :
    (Finset.univ.filter (fun i => b i = true)).image (fun i => heads b i.val) =
      Finset.range ((Finset.univ.filter (fun i => b i = true)).card) := by
  classical
  let S := Finset.univ.filter fun i : Fin n => b i = true
  have hinj : Set.InjOn (fun i => heads b i.val) (S : Set (Fin n)) := by
    intro i hi j hj he
    dsimp only at he
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hh := heads_strict b i j h (Finset.mem_filter.mp hi).2
      omega
    · have hh := heads_strict b j i h (Finset.mem_filter.mp hj).2
      omega
  have hsub : S.image (fun i => heads b i.val) ⊆ Finset.range S.card := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    apply Finset.mem_range.mpr
    unfold heads
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.2⟩
    · intro he
      rw [← he] at hi
      simp at hi
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_range, Finset.card_image_of_injOn hinj]

theorem acceptedHeads_exact {n : ℕ} (ell : ℕ) (b : Fin n → Bool) :
    acceptedHeads ell b = (min ell (heads b n) : ℕ) := by
  classical
  let S := Finset.univ.filter fun i : Fin n => b i = true
  let A := Finset.univ.filter fun i : Fin n => heads b i.val < ell ∧ b i = true
  have htotal : S.card = heads b n := by
    unfold heads
    congr 1
    ext i
    simp [S]
  have hinj : Set.InjOn (fun i => heads b i.val) (A : Set (Fin n)) := by
    intro i hi j hj he
    dsimp only at he
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hh := heads_strict b i j h (Finset.mem_filter.mp hi).2.2
      omega
    · have hh := heads_strict b j i h (Finset.mem_filter.mp hj).2.2
      omega
  have himage : A.image (fun i => heads b i.val) = Finset.range (min ell S.card) := by
    ext r
    constructor
    · intro hr
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
      have hm := (Finset.mem_filter.mp hi).2
      apply Finset.mem_range.mpr
      apply lt_min hm.1
      have hmem : heads b i.val ∈ S.image (fun i => heads b i.val) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm.2⟩, rfl⟩
      rw [head_rank_image] at hmem
      exact Finset.mem_range.mp hmem
    · intro hr
      have hm := lt_min_iff.mp (Finset.mem_range.mp hr)
      have hmem : r ∈ S.image (fun i => heads b i.val) := by
        rw [head_rank_image]
        exact Finset.mem_range.mpr hm.2
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hmem
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
      exact ⟨he ▸ hm.1, (Finset.mem_filter.mp hi).2⟩
  have hc := congrArg Finset.card himage
  rw [Finset.card_image_of_injOn hinj, Finset.card_range, htotal] at hc
  have he : acceptedHeads ell b = (A.card : ℝ) := by
    unfold acceptedHeads
    simp only [A, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    unfold active
    split <;> cases hb : b i <;> simp_all
  rw [he, hc]

theorem heads_mono {n : ℕ} (b : Fin n → Bool) {r t : ℕ} (h : r ≤ t) :
    heads b r ≤ heads b t := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨lt_of_lt_of_le hi.1 h, hi.2⟩

def failures {n : ℕ} (ell : ℕ) (b : Fin n → Bool) : ℝ :=
  inspected ell b - acceptedHeads ell b

theorem inspected_of_missing {n : ℕ} (ell : ℕ) (b : Fin n → Bool)
    (h : heads b n < ell) : inspected ell b = n := by
  unfold inspected
  have he : ∀ i : Fin n, active ell i b = 1 := by
    intro i
    unfold active
    exact if_pos (lt_of_le_of_lt (heads_mono b i.isLt.le) h)
  simp [he]

theorem failures_deviation_le {n : ℕ} (ell : ℕ) (b : Fin n → Bool) (hn : 2 * ell ≤ n) :
    |failures ell b - ell| ≤ |stoppedDifference ell b| := by
  have hid := stopped_difference_identity ell b
  have hex := acceptedHeads_exact ell b
  unfold failures
  by_cases h : ell ≤ heads b n
  · rw [min_eq_left h] at hex
    have he : inspected ell b - acceptedHeads ell b - ell = -stoppedDifference ell b := by
      linarith
    rw [he, abs_neg]
  · have hlt : heads b n < ell := Nat.lt_of_not_ge h
    rw [min_eq_right hlt.le] at hex
    have ht := inspected_of_missing ell b hlt
    have hnr : 2 * (ell : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hhr : (heads b n : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hlt.le
    rw [abs_of_nonneg (by linarith : 0 ≤ inspected ell b - acceptedHeads ell b - ell),
      abs_of_nonpos (by linarith : stoppedDifference ell b ≤ 0)]
    linarith

theorem failures_abs_le {n : ℕ} (ell : ℕ) (hn : 2 * ell ≤ n) :
    fairAvg (fun b : Fin n → Bool => |failures ell b - ell|) ≤ Real.sqrt (2 * ell) :=
  (fairAvg_mono (fun b => failures_deviation_le ell b hn)).trans (stopped_abs_le ell)

theorem heads_le_length {n : ℕ} (b : Fin n → Bool) : heads b n ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ.trans (Fintype.card_fin n))

theorem full_difference {n : ℕ} (b : Fin n → Bool) :
    stoppedDifference (n + 1) b = 2 * (heads b n : ℝ) - n := by
  have hh := acceptedHeads_exact (n + 1) b
  rw [min_eq_right (by have := heads_le_length b; omega)] at hh
  have ht := inspected_of_missing (n + 1) b (by have := heads_le_length b; omega)
  linarith [stopped_difference_identity (n + 1) b]

theorem heads_mean (n : ℕ) : fairAvg (fun b : Fin n → Bool => (heads b n : ℝ)) = n / 2 := by
  have h := stopped_mean (n := n) (n + 1)
  have he : (stoppedDifference (n + 1) : (Fin n → Bool) → ℝ) =
      (fun b => (heads b n : ℝ) * 2 + (-(n : ℝ))) := by
    funext b
    rw [full_difference]
    ring
  rw [he, fairAvg_add, fairAvg_mul_const, fairAvg_const] at h
  linarith

theorem heads_centered_abs (n : ℕ) :
    fairAvg (fun b : Fin n → Bool => |(heads b n : ℝ) - n / 2|) ≤ Real.sqrt (n : ℝ) / 2 := by
  have ht : fairAvg (inspected (n := n) (n + 1)) = n := by
    have he : inspected (n := n) (n + 1) = fun _ => (n : ℝ) := by
      funext b
      exact inspected_of_missing (n + 1) b (by have := heads_le_length b; omega)
    rw [he, fairAvg_const]
  have h := fairAvg_abs_le_sqrt (stoppedDifference (n := n) (n + 1))
  rw [stopped_second, ht] at h
  have he : (fun b : Fin n → Bool => |stoppedDifference (n + 1) b|) =
      (fun b => |(heads b n : ℝ) - n / 2| * 2) := by
    funext b
    rw [full_difference]
    have he : 2 * (heads b n : ℝ) - n = ((heads b n : ℝ) - n / 2) * 2 := by ring
    rw [he, abs_mul]
    norm_num
  rw [he, fairAvg_mul_const] at h
  linarith

theorem truncated_heads_bound (k : ℕ) :
    (k : ℝ) / 2 - Real.sqrt (k : ℝ) / 4 - 1 / 2 ≤
      fairAvg (fun b : Fin k → Bool => (min (heads b k) (k / 2) : ℕ)) := by
  have hf : (k : ℝ) / 2 - 1 / 2 ≤ (k / 2 : ℕ) := by
    have hn : k ≤ 2 * (k / 2) + 1 := by omega
    have hr : (k : ℝ) ≤ 2 * (k / 2 : ℕ) + 1 := by exact_mod_cast hn
    linarith
  have hp : ∀ b : Fin k → Bool,
      (heads b k : ℝ) / 2 + (k : ℝ) / 4 - |(heads b k : ℝ) - k / 2| / 2 - 1 / 2 ≤
        (min (heads b k) (k / 2) : ℕ) := by
    intro b
    rw [Nat.cast_min]
    apply le_min
    · linarith [le_abs_self (-((heads b k : ℝ) - k / 2)), abs_neg ((heads b k : ℝ) - k / 2)]
    · linarith [le_abs_self ((heads b k : ℝ) - k / 2)]
  have h := fairAvg_mono hp
  have he : (fun b : Fin k → Bool =>
      (heads b k : ℝ) / 2 + (k : ℝ) / 4 - |(heads b k : ℝ) - k / 2| / 2 - 1 / 2) =
      (fun b => (heads b k : ℝ) * (1/2) +
        (|(heads b k : ℝ) - k / 2| * (-(1/2)) + ((k : ℝ)/4-1/2))) := by
    funext b
    ring
  rw [he, fairAvg_add, fairAvg_add, fairAvg_mul_const, fairAvg_mul_const,
    fairAvg_const, heads_mean] at h
  linarith [heads_centered_abs k]

def truncate {n : ℕ} (r : ℕ) (b : Fin n → Bool) (i : Fin n) : Bool :=
  if i.val < r then b i else false

theorem heads_truncate_before {n : ℕ} (r t : ℕ) (h : t ≤ r) (b : Fin n → Bool) :
    heads (truncate r b) t = heads b t := by
  unfold heads
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i.val < t
  · simp [truncate, hi, lt_of_lt_of_le hi h]
  · simp [hi]

theorem heads_truncate_all {n : ℕ} (r : ℕ) (b : Fin n → Bool) :
    heads (truncate r b) n = heads b r := by
  unfold heads
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i.val < r <;> simp [truncate, hi]

theorem prefix_accepted_exact {n : ℕ} (ell r : ℕ) (b : Fin n → Bool) :
    (∑ i : Fin n, if i.val < r then active ell i b * (if b i then 1 else 0) else 0) =
      (min ell (heads b r) : ℕ) := by
  have h := acceptedHeads_exact ell (truncate r b)
  rw [heads_truncate_all] at h
  rw [← h]
  unfold acceptedHeads
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < r
  · have he : active ell i (truncate r b) = active ell i b := by
      unfold active
      rw [heads_truncate_before r i.val hi.le]
    simp [truncate, hi, he]
  · simp [truncate, hi]

theorem active_head_mean {n : ℕ} (ell : ℕ) (i : Fin n) :
    fairAvg (fun b => active ell i b * (if b i then 1 else 0)) =
      fairAvg (active ell i) / 2 := by
  have he : (fun b : Fin n → Bool => active ell i b * (if b i then 1 else 0)) =
      (fun b => (active ell i b * sign (b i)) * (1/2) + active ell i b * (1/2)) := by
    funext b
    cases hb : b i <;> simp [sign] ; ring
  rw [he, fairAvg_add, fairAvg_mul_const, fairAvg_mul_const,
    fairAvg_predictable_sign i (active ell i) (active_predictable ell i i le_rfl)]
  ring

theorem active_head_antitone {n : ℕ} (ell : ℕ) (i j : Fin n) (hij : i ≤ j) :
    fairAvg (fun b => active ell j b * (if b j then 1 else 0)) ≤
      fairAvg (fun b => active ell i b * (if b i then 1 else 0)) := by
  rw [active_head_mean, active_head_mean]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply fairAvg_mono
  intro b
  have h := heads_mono b hij
  unfold active
  split <;> split <;> simp_all
  omega

theorem antitone_prefix_average {k r : ℕ} (hr : r ≤ k) (hk : 0 < k)
    (d : Fin k → ℝ) (hd : Antitone d) :
    (r : ℝ) / k * (∑ i, d i) ≤ ∑ i : Fin k, if i.val < r then d i else 0 := by
  let P := Finset.univ.filter fun i : Fin k => i.val < r
  let Q := Finset.univ.filter fun i : Fin k => ¬i.val < r
  have hcP : P.card = r := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_fin_lt_of_le hr
  have hc : P.card + Q.card = k := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
      (p := fun i => i.val < r)
    simpa [P, Q] using h
  have hs : (∑ i ∈ P, d i) + ∑ i ∈ Q, d i = ∑ i, d i := by
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hpair : ∑ i ∈ P, ∑ j ∈ Q, d j ≤ ∑ i ∈ P, ∑ j ∈ Q, d i := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    apply hd
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    omega
  simp only [Finset.sum_const, nsmul_eq_mul] at hpair
  rw [← Finset.mul_sum] at hpair
  have he : (∑ i : Fin k, if i.val < r then d i else 0) = ∑ i ∈ P, d i := by
    rw [Finset.sum_filter]
  rw [he]
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hkr).2
  have hcr : (P.card : ℝ) + Q.card = (k : ℝ) := by exact_mod_cast hc
  rw [hcP] at hpair hcr
  have hm1 := congrArg (fun x : ℝ => (r : ℝ) * x) hs
  have hm2 := congrArg (fun x : ℝ => x * (∑ i ∈ P, d i)) hcr
  nlinarith

theorem truncated_prefix_scaling {k r : ℕ} (hr : r ≤ k) (hk : 0 < k) (ell : ℕ) :
    (r : ℝ) / k * fairAvg (fun b : Fin k → Bool => (min (heads b k) ell : ℕ)) ≤
      fairAvg (fun b : Fin k → Bool => (min (heads b r) ell : ℕ)) := by
  let d := fun i : Fin k => fairAvg (fun b => active ell i b * (if b i then 1 else 0))
  have hd : Antitone d := by
    intro i j hij
    exact active_head_antitone ell i j hij
  have ht : fairAvg (fun b : Fin k → Bool => (min (heads b k) ell : ℕ)) = ∑ i, d i := by
    have he : (fun b : Fin k → Bool => ((min (heads b k) ell : ℕ) : ℝ)) = acceptedHeads ell := by
      funext b
      rw [acceptedHeads_exact, min_comm]
    rw [he]
    exact fairAvg_sum Finset.univ _
  have hp : fairAvg (fun b : Fin k → Bool => (min (heads b r) ell : ℕ)) =
      ∑ i : Fin k, if i.val < r then d i else 0 := by
    have he : (fun b : Fin k → Bool => ((min (heads b r) ell : ℕ) : ℝ)) =
        (fun b => ∑ i : Fin k, if i.val < r then active ell i b * (if b i then 1 else 0) else 0) := by
      funext b
      rw [prefix_accepted_exact, min_comm]
    rw [he, fairAvg_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < r <;> simp [hi, d, fairAvg_const]
  rw [ht, hp]
  exact antitone_prefix_average hr hk d hd

theorem fairAvg_equiv {n : ℕ} (e : (Fin n → Bool) ≃ (Fin n → Bool))
    (f : (Fin n → Bool) → ℝ) : fairAvg (fun b => f (e b)) = fairAvg f := by
  unfold fairAvg
  rw [e.sum_comp]

theorem fairAvg_permute {n : ℕ} (p : Equiv.Perm (Fin n)) (f : (Fin n → Bool) → ℝ) :
    fairAvg (fun b => f (fun i => b (p i))) = fairAvg f := by
  let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
    { toFun := fun b i => b (p i)
      invFun := fun b i => b (p.symm i)
      left_inv := by intro b; funext i; simp
      right_inv := by intro b; funext i; simp }
  exact fairAvg_equiv e f

namespace RankSwapAudit

noncomputable def eligible {n : ℕ} (ell : ℕ) (b : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => b i = false ∧ heads b i.val < ell

lemma swapped_heads_le {n : ℕ} (b : Fin n → Bool) (i j : Fin n)
    (hij : i ≤ j) (hj : b j = false) (t : ℕ) :
    heads (fun x => b (Equiv.swap i j x)) t ≤ heads b t := by
  classical
  unfold heads
  apply Finset.card_le_card_of_injOn (Equiv.swap i j)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨?_, hx.2⟩
    by_cases hxi : x = i
    · subst x
      simp [hj] at hx
    by_cases hxj : x = j
    · subst x
      simpa using lt_of_le_of_lt (show i.val ≤ j.val from hij) hx.1
    · simpa [Equiv.swap_apply_of_ne_of_ne hxi hxj] using hx.1
  · exact (Equiv.swap i j).injective.injOn

lemma swapped_heads_after {n : ℕ} (b : Fin n → Bool) (i j : Fin n)
    (hij : i ≤ j) (t : ℕ) (hjt : j.val < t) :
    heads (fun x => b (Equiv.swap i j x)) t = heads b t := by
  classical
  unfold heads
  apply Finset.card_bij (fun x _ => Equiv.swap i j x)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨?_, hx.2⟩
    by_cases hxi : x = i
    · subst x; simpa using hjt
    by_cases hxj : x = j
    · subst x; simpa using lt_of_le_of_lt (show i.val ≤ j.val from hij) hjt
    · simpa [Equiv.swap_apply_of_ne_of_ne hxi hxj] using hx.1
  · intro x _ y _ h
    exact (Equiv.swap i j).injective h
  · intro y hy
    refine ⟨Equiv.swap i j y, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    refine ⟨?_, by simpa using hy.2⟩
    by_cases hyi : y = i
    · subst y; simpa using hjt
    by_cases hyj : y = j
    · subst y; simpa using lt_of_le_of_lt (show i.val ≤ j.val from hij) hjt
    · simpa [Equiv.swap_apply_of_ne_of_ne hyi hyj] using hy.1

lemma swap_le_right {n : ℕ} (i j z : Fin n) (hij : i ≤ j) (hz : z ≤ j) :
    Equiv.swap i j z ≤ j := by
  by_cases hzi : z = i
  · subst z; simp
  by_cases hzj : z = j
  · subst z; simpa using hij
  · simpa [Equiv.swap_apply_of_ne_of_ne hzi hzj] using hz

lemma eligible_swapped_iff {n : ℕ} (ell : ℕ) (b : Fin n → Bool) (i j z : Fin n)
    (hij : i ≤ j) (hj : j ∈ eligible ell b) :
    z ∈ eligible ell (fun x => b (Equiv.swap i j x)) ↔
      Equiv.swap i j z ∈ eligible ell b := by
  classical
  have hj' : b j = false ∧ heads b j.val < ell := by simpa [eligible] using hj
  by_cases hz : z ≤ j
  · have hs := swap_le_right i j z hij hz
    have ha : heads b z.val < ell := lt_of_le_of_lt
      (heads_mono b (show z.val ≤ j.val from hz)) hj'.2
    have hb : heads b (Equiv.swap i j z).val < ell := lt_of_le_of_lt
      (heads_mono b (show (Equiv.swap i j z).val ≤ j.val from hs)) hj'.2
    have hc : heads (fun x => b (Equiv.swap i j x)) z.val < ell :=
      lt_of_le_of_lt (swapped_heads_le b i j hij hj'.1 z.val) ha
    simp [eligible, hb, hc]
  · have hjz : j.val < z.val := show j < z from lt_of_not_ge hz
    have hzi : z ≠ i := by intro h; subst z; exact hz hij
    have hzj : z ≠ j := by intro h; subst z; exact hz le_rfl
    have hs : Equiv.swap i j z = z := Equiv.swap_apply_of_ne_of_ne hzi hzj
    simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and, hs,
      swapped_heads_after b i j hij z.val hjz]

lemma eligible_swapped_card {n : ℕ} (ell : ℕ) (b : Fin n → Bool) (i j : Fin n)
    (hij : i ≤ j) (hj : j ∈ eligible ell b) :
    (eligible ell (fun x => b (Equiv.swap i j x))).card = (eligible ell b).card := by
  classical
  apply Finset.card_bij (fun x _ => Equiv.swap i j x)
  · intro x hx
    exact (eligible_swapped_iff ell b i j x hij hj).mp hx
  · intro x _ y _ h
    exact (Equiv.swap i j).injective h
  · intro y hy
    refine ⟨Equiv.swap i j y, ?_, by simp⟩
    apply (eligible_swapped_iff ell b i j _ hij hj).mpr
    simpa using hy

noncomputable def probability {n : ℕ} (ell c : ℕ) (i : Fin n) (b : Fin n → Bool) : ℝ :=
  if i ∈ eligible ell b then (min c (eligible ell b).card : ℕ) / ((eligible ell b).card : ℝ) else 0

lemma probability_nonneg {n : ℕ} (ell c : ℕ) (i : Fin n) (b : Fin n → Bool) :
    0 ≤ probability ell c i b := by
  unfold probability
  split
  · positivity
  · exact le_rfl

lemma probability_swap {n : ℕ} (ell c : ℕ) (b : Fin n → Bool) (i j : Fin n)
    (hij : i ≤ j) :
    probability ell c j b ≤ probability ell c i (fun x => b (Equiv.swap i j x)) := by
  classical
  by_cases hj : j ∈ eligible ell b
  · have hi : i ∈ eligible ell (fun x => b (Equiv.swap i j x)) := by
      apply (eligible_swapped_iff ell b i j i hij hj).mpr
      simpa using hj
    simp only [probability, if_pos hi, if_pos hj, eligible_swapped_card ell b i j hij hj]
    exact le_rfl
  · simp only [probability, if_neg hj]
    exact probability_nonneg ell c i _

lemma probability_antitone {n : ℕ} (ell c : ℕ) :
    Antitone (fun i : Fin n => fairAvg (probability ell c i)) := by
  intro i j hij
  have h := fairAvg_mono (fun b => probability_swap ell c b i j hij)
  rw [fairAvg_permute (Equiv.swap i j) (probability ell c i)] at h
  exact h

lemma heads_restrict {n N : ℕ} (hn : n ≤ N) (b : Fin N → Bool) (t : ℕ) (ht : t ≤ n) :
    heads (fun i : Fin n => b (Fin.castLE hn i)) t = heads b t := by
  classical
  unfold heads
  apply Finset.card_bij (fun i _ => Fin.castLE hn i)
  · intro i hi
    simpa using hi
  · intro i _ j _ h
    exact Fin.ext (congrArg (fun x : Fin N => x.val) h)
  · intro j hj
    have hj' : j.val < t ∧ b j = true := by simpa using hj
    let i : Fin n := ⟨j.val, lt_of_lt_of_le hj'.1 ht⟩
    refine ⟨i, ?_, Fin.ext rfl⟩
    simpa [i] using hj

lemma eligible_restrict {n N : ℕ} (hn : n ≤ N) (ell : ℕ) (b : Fin N → Bool) (i : Fin n) :
    i ∈ eligible ell (fun j => b (Fin.castLE hn j)) ↔ Fin.castLE hn i ∈ eligible ell b := by
  classical
  simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [heads_restrict hn b i.val (Nat.le_of_lt i.isLt)]
  rfl

lemma eligible_restrict_card {n N : ℕ} (hn : n ≤ N) (ell : ℕ) (b : Fin N → Bool) :
    (eligible ell (fun i : Fin n => b (Fin.castLE hn i))).card ≤ (eligible ell b).card := by
  classical
  apply Finset.card_le_card_of_injOn (Fin.castLE hn)
  · intro i hi
    exact (eligible_restrict hn ell b i).mp hi
  · intro i _ j _ h
    exact Fin.ext (congrArg (fun x : Fin N => x.val) h)

lemma cap_ratio_antitone (c p q : ℕ) (hp : 0 < p) (hpq : p ≤ q) :
    ((min c q : ℕ) : ℝ) / q ≤ ((min c p : ℕ) : ℝ) / p := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  apply (div_le_div_iff₀ hq' hp').mpr
  have h : min c q * p ≤ min c p * q := by
    by_cases hc : c ≤ p
    · rw [min_eq_left hc, min_eq_left (hc.trans hpq)]
      exact Nat.mul_le_mul_left c hpq
    · rw [min_eq_right (Nat.le_of_lt (lt_of_not_ge hc))]
      nlinarith [min_le_right c q]
  exact_mod_cast h

lemma probability_padding {n N : ℕ} (hn : n ≤ N) (ell c : ℕ) (b : Fin N → Bool)
    (i : Fin n) : probability ell c (Fin.castLE hn i) b ≤
      probability ell c i (fun j => b (Fin.castLE hn j)) := by
  classical
  by_cases hi : i ∈ eligible ell (fun j => b (Fin.castLE hn j))
  · have hi' := (eligible_restrict hn ell b i).mp hi
    simp only [probability, if_pos hi, if_pos hi']
    apply cap_ratio_antitone
    · exact Finset.card_pos.mpr ⟨i, hi⟩
    · exact eligible_restrict_card hn ell b
  · have hi' : Fin.castLE hn i ∉ eligible ell b := by
      intro h
      exact hi ((eligible_restrict hn ell b i).mpr h)
    simp [probability, hi, hi']

lemma fairAvg_restrict_add (n d : ℕ) (f : (Fin n → Bool) → ℝ) :
    fairAvg (fun b : Fin (n+d) → Bool => f (fun i => b (Fin.castAdd d i))) = fairAvg f := by
  classical
  let e : (Fin (n+d) → Bool) ≃ ((Fin n → Bool) × (Fin d → Bool)) :=
    { toFun := fun b => (fun i => b (Fin.castAdd d i), fun j => b (Fin.natAdd n j))
      invFun := fun p => Fin.addCases p.1 p.2
      left_inv := by
        intro b
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      right_inv := by intro p; ext i <;> simp }
  have hs : (∑ b : Fin (n+d) → Bool, f (fun i => b (Fin.castAdd d i))) =
      (2 : ℝ)^d * ∑ b : Fin n → Bool, f b := by
    calc
      _ = ∑ p : (Fin n → Bool) × (Fin d → Bool), f p.1 := by
        apply Fintype.sum_equiv e
        intro b
        rfl
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp [← Finset.mul_sum]
  unfold fairAvg
  rw [hs, pow_add]
  have hn : (2 : ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hd : (2 : ℝ)^d ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

lemma fairAvg_restrict {n N : ℕ} (hn : n ≤ N) (f : (Fin n → Bool) → ℝ) :
    fairAvg (fun b : Fin N → Bool => f (fun i => b (Fin.castLE hn i))) = fairAvg f := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact fairAvg_restrict_add n d f

lemma probability_padding_average {n N : ℕ} (hn : n ≤ N) (ell c : ℕ) (i : Fin n) :
    fairAvg (probability ell c (Fin.castLE hn i)) ≤ fairAvg (probability ell c i) := by
  have h := fairAvg_mono (fun b => probability_padding hn ell c b i)
  rw [fairAvg_restrict hn (probability ell c i)] at h
  exact h

noncomputable def yieldPrefix {n : ℕ} (ell c r : ℕ) (b : Fin n → Bool) : ℝ :=
  ((min c (eligible ell b).card : ℕ) : ℝ) / ((eligible ell b).card : ℝ) *
    (((eligible ell b).filter fun i => i.val < r).card : ℝ)

lemma yieldPrefix_eq_sum {n r : ℕ} (hr : r ≤ n) (ell c : ℕ) (b : Fin n → Bool) :
    yieldPrefix ell c r b = ∑ i : Fin r, probability ell c (Fin.castLE hr i) b := by
  classical
  have hc : (Finset.univ.filter fun i : Fin r => Fin.castLE hr i ∈ eligible ell b).card =
      ((eligible ell b).filter fun i => i.val < r).card := by
    apply Finset.card_bij (fun i _ => Fin.castLE hr i)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, i.isLt⟩
    · intro i _ j _ h
      exact Fin.ext (congrArg (fun x : Fin n => x.val) h)
    · intro j hj
      obtain ⟨hjE, hjr⟩ := Finset.mem_filter.mp hj
      refine ⟨⟨j.val, hjr⟩, ?_, Fin.ext rfl⟩
      simpa using hjE
  unfold yieldPrefix probability
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, hc]
  ring

lemma yieldPrefix_padding {n N r : ℕ} (hn : n ≤ N) (hr : r ≤ n) (ell c : ℕ) :
    fairAvg (yieldPrefix (n := N) ell c r) ≤ fairAvg (yieldPrefix (n := n) ell c r) := by
  have heN : yieldPrefix (n := N) ell c r =
      (fun b => ∑ i : Fin r, probability ell c (Fin.castLE (hr.trans hn) i) b) := by
    funext b
    exact yieldPrefix_eq_sum (hr.trans hn) ell c b
  have hen : yieldPrefix (n := n) ell c r =
      (fun b => ∑ i : Fin r, probability ell c (Fin.castLE hr i) b) := by
    funext b
    exact yieldPrefix_eq_sum hr ell c b
  rw [heN, hen, fairAvg_sum, fairAvg_sum]
  apply Finset.sum_le_sum
  intro i _
  exact probability_padding_average hn ell c (Fin.castLE hr i)

lemma sum_prefix_restrict {k r : ℕ} (hr : r ≤ k) (d : Fin k → ℝ) :
    (∑ i : Fin k, if i.val < r then d i else 0) = ∑ i : Fin r, d (Fin.castLE hr i) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun i _ => Fin.castLE hr i)
  · intro i _
    simp
  · intro i _ j _ h
    exact Fin.ext (congrArg (fun x : Fin k => x.val) h)
  · intro j hj
    refine ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i _
    rfl

lemma yieldPrefix_average_eq_sum {n r : ℕ} (hr : r ≤ n) (ell c : ℕ) :
    fairAvg (yieldPrefix (n := n) ell c r) =
      ∑ i : Fin r, fairAvg (probability ell c (Fin.castLE hr i)) := by
  have he : yieldPrefix (n := n) ell c r =
      (fun b => ∑ i : Fin r, probability ell c (Fin.castLE hr i) b) := by
    funext b
    exact yieldPrefix_eq_sum hr ell c b
  rw [he, fairAvg_sum]

lemma yieldPrefix_scaling {n k r : ℕ} (hkn : k ≤ n) (hr : r ≤ k) (hk : 0 < k)
    (ell c : ℕ) :
    (r : ℝ) / k * fairAvg (yieldPrefix (n := n) ell c k) ≤
      fairAvg (yieldPrefix (n := n) ell c r) := by
  rw [yieldPrefix_average_eq_sum hkn, yieldPrefix_average_eq_sum (hr.trans hkn)]
  let d : Fin k → ℝ := fun i => fairAvg (probability ell c (Fin.castLE hkn i))
  have hd : Antitone d := fun i j hij => probability_antitone ell c hij
  have h := antitone_prefix_average hr hk d hd
  rw [sum_prefix_restrict hr d] at h
  exact h

lemma yieldPrefix_mono {n r s : ℕ} (hrs : r ≤ s) (ell c : ℕ) (b : Fin n → Bool) :
    yieldPrefix ell c r b ≤ yieldPrefix ell c s b := by
  unfold yieldPrefix
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast Finset.card_le_card (show
        (eligible ell b).filter (fun i => i.val < r) ⊆
        (eligible ell b).filter (fun i => i.val < s) from by
      intro i hi
      obtain ⟨hiE, hir⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hiE, lt_of_lt_of_le hir hrs⟩)
  · positivity

end RankSwapAudit
theorem min_heads_average_restrict {n r : ℕ} (hr : r ≤ n) (ell : ℕ) :
    fairAvg (fun b : Fin n → Bool => ((min (heads b r) ell : ℕ) : ℝ)) =
      fairAvg (fun b : Fin r → Bool => ((min (heads b r) ell : ℕ) : ℝ)) := by
  have h := RankSwapAudit.fairAvg_restrict hr
    (fun b : Fin r → Bool => ((min (heads b r) ell : ℕ) : ℝ))
  simp_rw [RankSwapAudit.heads_restrict hr _ r le_rfl] at h
  exact h

theorem phase1_marginal_all_dimensions {n k r : ℕ} (hrn : r ≤ n) (hrk : r ≤ k)
    (hk : 0 < k) :
    (r : ℝ) / k * ((k : ℝ)/2 - Real.sqrt (k : ℝ)/4 - 1/2) ≤
      fairAvg (fun b : Fin n → Bool => ((min (k/2) (heads b r) : ℕ) : ℝ)) := by
  have hscale := truncated_prefix_scaling hrk hk (k/2)
  have hbound := mul_le_mul_of_nonneg_left (truncated_heads_bound k)
    (div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg k) : (0 : ℝ) ≤ (r : ℝ)/k)
  have h := hbound.trans hscale
  rw [min_heads_average_restrict hrk] at h
  rw [show (fun b : Fin n → Bool => ((min (k/2) (heads b r) : ℕ) : ℝ)) =
      (fun b => ((min (heads b r) (k/2) : ℕ) : ℝ)) by funext b; rw [min_comm]]
  rw [min_heads_average_restrict hrn]
  exact h

theorem phase1_marginal_scaled {n k r : ℕ} (hrn : r ≤ n) (hrk : r ≤ k)
    (hk : 0 < k) (a : ℝ) (ha : 0 ≤ a) :
    (r : ℝ)*a*(1/2 - 1/(4*Real.sqrt (k : ℝ)) - 1/(2*(k : ℝ))) ≤
      a * fairAvg (fun b : Fin n → Bool => ((min (k/2) (heads b r) : ℕ) : ℝ)) := by
  have hp : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hp
  have hs2 := Real.sq_sqrt hp.le
  have he : ((k : ℝ)/2 - Real.sqrt (k : ℝ)/4 - 1/2)/(k : ℝ) =
      1/2 - 1/(4*Real.sqrt (k : ℝ)) - 1/(2*(k : ℝ)) := by
    field_simp
    nlinarith
  have h := mul_le_mul_of_nonneg_left (phase1_marginal_all_dimensions hrn hrk hk) ha
  have hid : a*((r : ℝ)/k*((k : ℝ)/2-Real.sqrt (k : ℝ)/4-1/2)) =
      (r : ℝ)*a*(1/2 - 1/(4*Real.sqrt (k : ℝ)) - 1/(2*(k : ℝ))) := by
    calc
      _ = (r : ℝ)*a*(((k : ℝ)/2-Real.sqrt (k : ℝ)/4-1/2)/(k : ℝ)) := by ring
      _ = _ := by rw [he]
  rwa [hid] at h

end SecretaryProof
-- END BooleanMoments

-- BEGIN NumericClosure

namespace SecretaryProof

theorem small_coefficient (k : ℕ) (hk : k ≤ 25) :
    1 - 5 / Real.sqrt (k : ℝ) ≤ 0 ∨ k = 0 := by
  by_cases hz : k = 0
  · exact Or.inr hz
  left
  have hp : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hp
  have hb : Real.sqrt (k : ℝ) ≤ 5 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · exact_mod_cast hk
  have : 1 ≤ 5 / Real.sqrt (k : ℝ) := (le_div_iff₀ hs).2 (by simpa using hb)
  linarith

theorem floor_half_bounds (k : ℕ) :
    (k : ℝ) / 2 - 1 / 2 ≤ (k / 2 : ℕ) ∧ (k / 2 : ℕ) ≤ (k : ℝ) / 2 := by
  have h1 : k ≤ 2 * (k / 2) + 1 := by omega
  have h2 : 2 * (k / 2) ≤ k := by omega
  have h1r : (k : ℝ) ≤ 2 * (k / 2 : ℕ) + 1 := by exact_mod_cast h1
  have h2r : 2 * (k / 2 : ℕ) ≤ (k : ℝ) := by exact_mod_cast h2
  constructor <;> linarith

theorem middle_coefficient (k : ℕ) (hk : 26 ≤ k) (hu : k ≤ 60) :
    1 - 5 / Real.sqrt (k : ℝ) ≤
      (k / 2 : ℕ) / (k : ℝ) - Real.sqrt (2 * (k / 2 : ℕ)) / (k : ℝ) := by
  have hp : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hp
  have hs2 := Real.sq_sqrt hp.le
  have hfloor := floor_half_bounds k
  have hsmall : Real.sqrt (2 * (k / 2 : ℕ)) ≤ Real.sqrt (k : ℝ) :=
    Real.sqrt_le_sqrt (by linarith [hfloor.2])
  have hs5 : 5 ≤ Real.sqrt (k : ℝ) := by
    apply (Real.le_sqrt (by norm_num) hp.le).2
    exact_mod_cast (show 25 ≤ k by omega)
  have hs31 : Real.sqrt (k : ℝ) ≤ 31 / 4 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · have : (k : ℝ) ≤ 60 := by exact_mod_cast hu
      linarith
  have hnum : (k : ℝ) + 1 ≤ 8 * Real.sqrt (k : ℝ) := by
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs31)]
  apply (le_sub_iff_add_le).2
  apply (le_div_iff₀ hp).2
  have he : (1 - 5 / Real.sqrt (k : ℝ) + Real.sqrt (2 * (k / 2 : ℕ)) / (k : ℝ)) * (k : ℝ) =
      (k : ℝ) - 5 * Real.sqrt (k : ℝ) + Real.sqrt (2 * (k / 2 : ℕ)) := by
    field_simp
    nlinarith [hs2]
  rw [he]
  linarith [hfloor.1]

theorem large_coefficient (k : ℕ) (hk : 61 ≤ k) :
    1 - 5 / Real.sqrt (k : ℝ) ≤
      (1 - 5 / Real.sqrt (k / 2 : ℕ)) *
        (1 / 2 - 1 / (4 * Real.sqrt (k : ℝ)) - 1 / (2 * (k : ℝ))) +
        (k / 2 : ℕ) / (k : ℝ) - Real.sqrt (2 * (k / 2 : ℕ)) / (k : ℝ) := by
  let s := Real.sqrt (k : ℝ)
  let t := Real.sqrt (k / 2 : ℕ)
  have hp : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hL : 30 ≤ k / 2 := by omega
  have ht : 0 < t := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < k / 2 by omega))
  have hs : 0 < s := Real.sqrt_pos.2 hp
  have hs2 : s ^ 2 = (k : ℝ) := Real.sq_sqrt hp.le
  have ht2 : t ^ 2 = (k / 2 : ℕ) := Real.sq_sqrt (by positivity)
  have hs7 : 7 ≤ s := by
    apply (Real.le_sqrt (by norm_num) hp.le).2
    exact_mod_cast (show 49 ≤ k by omega)
  have ht5 : 5 ≤ t := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    exact_mod_cast (show 25 ≤ k / 2 by omega)
  have hratio : 7 * s ≤ 10 * t := by
    have hnat : 49 * k ≤ 100 * (k / 2) := by omega
    have hr : 49 * (k : ℝ) ≤ 100 * (k / 2 : ℕ) := by exact_mod_cast hnat
    nlinarith
  have hfloor := floor_half_bounds k
  have hu : Real.sqrt (2 * (k / 2 : ℕ)) ≤ s :=
    Real.sqrt_le_sqrt (by linarith [hfloor.2])
  have hrat : 5 / (2 * t) ≤ 25 / (7 * s) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hrec : 1 / (k : ℝ) ≤ 1 / (7 * s) := by
    apply (div_le_div_iff₀ hp (by positivity)).2
    nlinarith
  have hcost : 5 / (2 * t) + 5 / (4 * s) + 1 / (k : ℝ) ≤ 5 / s := by
    calc
      _ ≤ 25 / (7 * s) + 5 / (4 * s) + 1 / (7 * s) := by linarith
      _ ≤ 5 / s := by field_simp; nlinarith
  have ha0 : 0 ≤ 1 - 5 / t := by
    have : 5 / t ≤ 1 := (div_le_one ht).2 ht5
    linarith
  have ha1 : 1 - 5 / t ≤ 1 := by
    have : 0 ≤ 5 / t := by positivity
    linarith
  have hB : 0 ≤ 1 / (4 * s) + 1 / (2 * (k : ℝ)) := by positivity
  have hab := mul_le_mul_of_nonneg_right ha1 hB
  have hlower : 1 / 2 - 1 / (2 * (k : ℝ)) ≤ (k / 2 : ℕ) / (k : ℝ) := by
    apply (le_div_iff₀ hp).2
    field_simp
    linarith [hfloor.1]
  have hu' : Real.sqrt (2 * (k / 2 : ℕ)) / (k : ℝ) ≤ 1 / s := by
    apply (div_le_div_iff₀ hp hs).2
    nlinarith [mul_le_mul_of_nonneg_right hu hs.le]
  change 1 - 5 / s ≤ (1 - 5 / t) * (1 / 2 - 1 / (4 * s) - 1 / (2 * (k : ℝ))) + _ - _
  have he1 : 5 / (2 * t) = (5 / t) / 2 := by ring
  have he2 : 5 / (4 * s) = 1 / (4 * s) + 1 / s := by ring
  have he3 : 1 / (k : ℝ) = 1 / (2 * (k : ℝ)) + 1 / (2 * (k : ℝ)) := by ring
  rw [he1, he2, he3] at hcost
  nlinarith

end SecretaryProof
-- END NumericClosure

-- BEGIN WeightedReduction

namespace SecretaryProof

theorem weighted_nonneg_of_prefix (n : ℕ) (v w : ℕ → ℝ)
    (hv : ∀ i < n, 0 ≤ v i)
    (hmono : ∀ i, i + 1 < n → v (i + 1) ≤ v i)
    (hw : ∀ r ≤ n, 0 ≤ ∑ i ∈ Finset.range r, w i) :
    0 ≤ ∑ i ∈ Finset.range n, v i * w i := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have h := Finset.sum_range_by_parts v w n
  simp only [smul_eq_mul] at h
  rw [h]
  have ha : 0 ≤ v (n - 1) * ∑ i ∈ Finset.range n, w i :=
    mul_nonneg (hv _ (by omega)) (hw n le_rfl)
  have hb : ∑ i ∈ Finset.range (n - 1), (v (i + 1) - v i) *
      ∑ j ∈ Finset.range (i + 1), w j ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hmono i (by omega)))
      (hw (i + 1) (by omega))
  linarith

theorem weighted_prefix_comparison (n : ℕ) (v p q : ℕ → ℝ)
    (hv : ∀ i < n, 0 ≤ v i)
    (hmono : ∀ i, i + 1 < n → v (i + 1) ≤ v i)
    (hp : ∀ r ≤ n, (∑ i ∈ Finset.range r, q i) ≤ ∑ i ∈ Finset.range r, p i) :
    (∑ i ∈ Finset.range n, v i * q i) ≤ ∑ i ∈ Finset.range n, v i * p i := by
  have h := weighted_nonneg_of_prefix n v (fun i => p i - q i) hv hmono (by
    intro r hr
    rw [Finset.sum_sub_distrib]
    exact sub_nonneg.mpr (hp r hr))
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  exact sub_nonneg.mp h

theorem weighted_nonneg_fin : ∀ (n : ℕ) (v w : Fin n → ℝ),
    (∀ i, 0 ≤ v i) → Antitone v →
    (∀ r ≤ n, 0 ≤ ∑ i : Fin n, if i.val < r then w i else 0) →
    0 ≤ ∑ i : Fin n, v i * w i := by
  intro n
  induction n with
  | zero => intro v w hv hm hw; simp
  | succ n ih =>
    intro v w hv hm hw
    have hp : ∀ r ≤ n, 0 ≤ ∑ i : Fin n, if i.val < r then w i.castSucc else 0 := by
      intro r hr
      have h := hw r (by omega)
      rw [Fin.sum_univ_castSucc] at h
      simpa [Fin.val_castSucc, Fin.val_last, Nat.not_lt.mpr hr] using h
    have hrec := ih (fun i => v i.castSucc - v (Fin.last n)) (fun i => w i.castSucc)
      (fun i => sub_nonneg.mpr (hm (Fin.le_last _)))
      (fun i j hij => sub_le_sub_right (hm (Fin.castSucc_le_castSucc_iff.mpr hij)) _) hp
    have htotal : 0 ≤ ∑ i : Fin (n + 1), w i := by
      have h := hw (n + 1) le_rfl
      simpa only [Fin.is_lt, if_true] using h
    have hprod := mul_nonneg (hv (Fin.last n)) htotal
    rw [Fin.sum_univ_castSucc] at hprod ⊢
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at hrec
    nlinarith

theorem weighted_prefix_fin (n : ℕ) (v p q : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hm : Antitone v)
    (hp : ∀ r ≤ n, (∑ i : Fin n, if i.val < r then q i else 0) ≤
      ∑ i : Fin n, if i.val < r then p i else 0) :
    (∑ i, v i * q i) ≤ ∑ i, v i * p i := by
  have h := weighted_nonneg_fin n v (fun i => p i - q i) hv hm (by
    intro r hr
    have he : (fun i : Fin n => if i.val < r then p i - q i else 0) =
        (fun i => (if i.val < r then p i else 0) - (if i.val < r then q i else 0)) := by
      funext i
      split <;> simp
    rw [he, Finset.sum_sub_distrib]
    exact sub_nonneg.mpr (hp r hr))
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  exact sub_nonneg.mp h

theorem sum_enumeration {n : ℕ} (v : Fin n → ℝ) (hv : Function.Injective v)
    (A : Finset ℝ) (hA : A ⊆ Finset.univ.image v) (f : ℝ → ℝ) :
    (∑ i : Fin n, if v i ∈ A then f (v i) else 0) = ∑ x ∈ A, f x := by
  classical
  rw [← Finset.sum_filter]
  have he : (Finset.univ.filter fun i => v i ∈ A).image v = A := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    · intro hx
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hA hx)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi ▸ hx⟩, hi⟩
  calc
    _ = ∑ x ∈ (Finset.univ.filter fun i => v i ∈ A).image v, f x :=
      (Finset.sum_image (fun _ _ _ _ h => hv h)).symm
    _ = ∑ x ∈ A, f x := by rw [he]

theorem selection_value_enumeration {n : ℕ} (x v : Fin n → ℝ)
    (hx : Function.Injective x) (hv : Function.Injective v)
    (hr : Finset.univ.image x = Finset.univ.image v) (A : Finset (Fin n)) :
    (∑ t ∈ A, x t) = ∑ i : Fin n, v i * (if v i ∈ A.image x then 1 else 0) := by
  classical
  have hA : A.image x ⊆ Finset.univ.image v := by
    rw [← hr]
    exact Finset.image_subset_image (Finset.subset_univ A)
  have h := sum_enumeration v hv (A.image x) hA id
  rw [Finset.sum_image (fun _ _ _ _ h => hx h)] at h
  simp only [id_eq] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all

theorem selection_count_enumeration {n : ℕ} (x v : Fin n → ℝ)
    (hx : Function.Injective x) (hv : Function.Injective v)
    (hr : Finset.univ.image x = Finset.univ.image v) (A : Finset (Fin n))
    (T : Finset ℝ) (r : ℕ) (hT : ∀ i, v i ∈ T ↔ i.val < r) :
    ((A.filter fun t => x t ∈ T).card : ℝ) =
      ∑ i : Fin n, if i.val < r then (if v i ∈ A.image x then 1 else 0) else 0 := by
  classical
  have hA : (A.filter fun t => x t ∈ T).image x ⊆ Finset.univ.image v := by
    rw [← hr]
    exact Finset.image_subset_image (Finset.subset_univ _)
  have h := sum_enumeration v hv ((A.filter fun t => x t ∈ T).image x) hA (fun _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_image_of_injective _ hx] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  have hm : v i ∈ (A.filter fun t => x t ∈ T).image x ↔ v i ∈ A.image x ∧ v i ∈ T := by
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨t, ⟨ht, hTt⟩, he⟩
      exact ⟨⟨t, ht, he⟩, he ▸ hTt⟩
    · rintro ⟨⟨t, ht, he⟩, hi⟩
      exact ⟨t, ⟨ht, he ▸ hi⟩, he⟩
  simp only [hm, hT]
  by_cases hi : i.val < r <;> by_cases hm : v i ∈ A.image x <;> simp [hi, hm]

open MultiChoiceSecretary.Alg SecretaryWD.DiscUpper

theorem peer_expectation_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (p : PMF α) (f : α → ι → ℝ) :
    expectation p (fun a => ∑ i, f a i) = ∑ i, expectation p (fun a => f a i) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem peer_uniform_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (f : Equiv.Perm (Fin n) → ι → ℝ) :
    uniformAvg (fun pi => ∑ i, f pi i) = ∑ i, uniformAvg (fun pi => f pi i) := by
  unfold uniformAvg
  rw [Finset.sum_comm, Finset.mul_sum]

theorem peer_uniform_mul {n : ℕ} (c : ℝ) (f : Equiv.Perm (Fin n) → ℝ) :
    uniformAvg (fun pi => c * f pi) = c * uniformAvg f := by
  unfold uniformAvg
  rw [← Finset.mul_sum]
  ring

noncomputable def valueProbability (S : Finset ℝ) (k : ℕ) (z : ℝ) : ℝ :=
  uniformAvg fun pi => expectation (alg k S.card (arrivals S pi))
    (fun A => if z ∈ A.image (arrivals S pi) then 1 else 0)

theorem arrivals_injective (S : Finset ℝ) (pi : Equiv.Perm (Fin S.card)) :
    Function.Injective (arrivals S pi) :=
  (S.orderEmbOfFin rfl).injective.comp pi.injective

theorem arrivals_image (S : Finset ℝ) (pi : Equiv.Perm (Fin S.card)) :
    Finset.univ.image (arrivals S pi) = S := by
  classical
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact S.orderEmbOfFin_mem rfl (pi i)
  · intro hz
    let j := (S.orderIsoOfFin rfl).symm ⟨z, hz⟩
    refine ⟨pi.symm j, ?_⟩
    change S.orderEmbOfFin rfl (pi (pi.symm j)) = z
    rw [pi.apply_symm_apply]
    exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨z,hz⟩)

theorem expectedValue_enumeration (S : Finset ℝ) (k : ℕ) (v : Fin S.card → ℝ)
    (hv : Function.Injective v) (hr : Finset.univ.image v = S) :
    expectedValue S k = ∑ i, v i * valueProbability S k (v i) := by
  classical
  unfold expectedValue
  change uniformAvg (fun pi => expectation (alg k S.card (arrivals S pi))
    (fun A => ∑ t ∈ A, arrivals S pi t)) = _
  have he : ∀ (pi : Equiv.Perm (Fin S.card)) (A : Finset (Fin S.card)), (∑ t ∈ A, arrivals S pi t) =
      ∑ i, v i * (if v i ∈ A.image (arrivals S pi) then 1 else 0) := by
    intro pi A
    exact selection_value_enumeration _ _ (arrivals_injective S pi) hv
      ((arrivals_image S pi).trans hr.symm) A
  simp_rw [he, peer_expectation_sum, expectation_smul]
  rw [peer_uniform_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact peer_uniform_mul _ _

theorem RC_enumeration (S : Finset ℝ) (k r : ℕ) (v : Fin S.card → ℝ)
    (hv : Function.Injective v) (hr : Finset.univ.image v = S)
    (hT : ∀ i, v i ∈ topK S r ↔ i.val < r) :
    RC S k r = ∑ i, if i.val < r then valueProbability S k (v i) else 0 := by
  classical
  unfold RC
  have he : ∀ (pi : Equiv.Perm (Fin S.card)) (A : Finset (Fin S.card)), ((A.filter fun t => arrivals S pi t ∈ topK S r).card : ℝ) =
      ∑ i, if i.val < r then (if v i ∈ A.image (arrivals S pi) then 1 else 0) else 0 := by
    intro pi A
    exact selection_count_enumeration _ _ (arrivals_injective S pi) hv
      ((arrivals_image S pi).trans hr.symm) A _ r hT
  simp_rw [he, peer_expectation_sum]
  rw [peer_uniform_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < r
  · simp only [hi, if_true]
    rfl
  · simp [hi, expectation_const, uniformAvg]

theorem prefix_constant_count {n : ℕ} (r k : ℕ) (hr : r ≤ n) (a : ℝ) :
    (∑ i : Fin n, if i.val < r then (if i.val < k then a else 0) else 0) =
      a * (min r k : ℕ) := by
  have he : (fun i : Fin n => if i.val < r then (if i.val < k then a else 0) else 0) =
      (fun i => if i.val < min r k then a else 0) := by
    funext i
    by_cases hi : i.val < r <;> by_cases hj : i.val < k <;> simp [hi, hj]
  rw [he, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter fun i : Fin n => i.val < min r k).card = min r k := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_fin_lt_of_le ((Nat.min_le_left r k).trans hr)
  rw [hc, mul_comm]

theorem weighted_reduction_with_enumeration (S : Finset ℝ) (k : ℕ) (a : ℝ)
    (hS : ∀ x ∈ S, 0 ≤ x) (v : Fin S.card → ℝ)
    (hv : Function.Injective v) (hr : Finset.univ.image v = S) (hm : Antitone v)
    (hT : ∀ r i, v i ∈ topK S r ↔ i.val < r)
    (hsum : topSum S k = ∑ i, if i.val < k then v i else 0)
    (hcount : ∀ r ≤ S.card, a * (min r k : ℕ) ≤ RC S k r) :
    a * topSum S k ≤ expectedValue S k := by
  classical
  have hv0 : ∀ i, 0 ≤ v i := by
    intro i
    apply hS
    rw [← hr]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hp : ∀ r ≤ S.card,
      (∑ i : Fin S.card, if i.val < r then (if i.val < k then a else 0) else 0) ≤
      ∑ i, if i.val < r then valueProbability S k (v i) else 0 := by
    intro r hrr
    rw [prefix_constant_count r k hrr]
    rw [← RC_enumeration S k r v hv hr (hT r)]
    exact hcount r hrr
  have h := weighted_prefix_fin S.card v (fun i => valueProbability S k (v i))
    (fun i => if i.val < k then a else 0) hv0 hm hp
  rw [← expectedValue_enumeration S k v hv hr] at h
  have he : (∑ i, v i * (if i.val < k then a else 0)) = a * topSum S k := by
    rw [hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp_all [mul_comm]
  rwa [he] at h

theorem weighted_native_reduction (S : Finset ℝ) (k : ℕ) (a : ℝ)
    (hS : ∀ x ∈ S, 0 ≤ x)
    (hcount : ∀ r ≤ S.card, a * (min r k : ℕ) ≤ RC S k r) :
    a * topSum S k ≤ expectedValue S k := by
  classical
  have hr : Finset.univ.image (descending S) = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact descending_mem S i
    · intro hx
      obtain ⟨i, hi⟩ := descending_surjective S x hx
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  exact weighted_reduction_with_enumeration S k a hS (descending S)
    (descending_injective S) hr (descending_antitone S).antitone
    (fun r i => descending_topK S i r) (topSum_descending S k) hcount

namespace SamplingAudit

noncomputable def positions {n : ℕ} (B : Finset (Fin n)) (pi : Equiv.Perm (Fin n)) :
    Finset (Fin n) := Finset.univ.filter fun t => pi t ∈ B

noncomputable def selected {n : ℕ} (B : Finset (Fin n)) (c : ℕ)
    (pi : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  (((positions B pi).sort (· ≤ ·)).take c).toFinset.image pi

lemma positions_card {n : ℕ} (B : Finset (Fin n)) (pi : Equiv.Perm (Fin n)) :
    (positions B pi).card = B.card := by
  classical
  apply Finset.card_bij (fun t _ => pi t)
  · intro t ht
    exact (Finset.mem_filter.mp ht).2
  · intro a _ b _ h
    exact pi.injective h
  · intro b hb
    exact ⟨pi.symm b, by simpa [positions] using hb, pi.apply_symm_apply b⟩

lemma selected_card {n : ℕ} (B : Finset (Fin n)) (c : ℕ)
    (pi : Equiv.Perm (Fin n)) : (selected B c pi).card = min c B.card := by
  classical
  unfold selected
  rw [Finset.card_image_of_injective _ pi.injective,
    List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).take), List.length_take,
    Finset.length_sort, positions_card]

lemma selected_subset {n : ℕ} (B : Finset (Fin n)) (c : ℕ)
    (pi : Equiv.Perm (Fin n)) : selected B c pi ⊆ B := by
  classical
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  have ht' := List.mem_of_mem_take (List.mem_toFinset.mp ht)
  have : t ∈ positions B pi := (Finset.mem_sort _).mp ht'
  exact (Finset.mem_filter.mp this).2

lemma selected_relabel {n : ℕ} (B : Finset (Fin n)) (c : ℕ)
    (pi sigma : Equiv.Perm (Fin n)) (hs : ∀ x, sigma x ∈ B ↔ x ∈ B) :
    selected B c (pi.trans sigma) = (selected B c pi).image sigma := by
  classical
  have hp : positions B (pi.trans sigma) = positions B pi := by
    ext t
    simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.trans_apply, hs]
  unfold selected
  rw [hp, Finset.image_image]
  rfl

lemma uniform_relabel {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (f : Equiv.Perm (Fin n) → ℝ) :
    uniformAvg (fun pi => f (pi.trans sigma)) = uniformAvg f := by
  unfold uniformAvg
  congr 1
  apply Fintype.sum_equiv
    (show Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) from
      { toFun := fun pi => pi.trans sigma
        invFun := fun pi => pi.trans sigma.symm
        left_inv := by intro pi; ext x; simp
        right_inv := by intro pi; ext x; simp })
  intro pi
  rfl

noncomputable def marginal {n : ℕ} (B : Finset (Fin n)) (c : ℕ) (x : Fin n) : ℝ :=
  uniformAvg fun pi => if x ∈ selected B c pi then 1 else 0

lemma marginal_equal {n : ℕ} (B : Finset (Fin n)) (c : ℕ)
    (x y : Fin n) (hx : x ∈ B) (hy : y ∈ B) : marginal B c x = marginal B c y := by
  classical
  let sigma := Equiv.swap x y
  have hs : ∀ z, sigma z ∈ B ↔ z ∈ B := by
    intro z
    by_cases hzx : z = x
    · subst z; simp [sigma, hx, hy]
    by_cases hzy : z = y
    · subst z; simp [sigma, hx, hy]
    simp [sigma, Equiv.swap_apply_of_ne_of_ne hzx hzy]
  unfold marginal
  rw [← uniform_relabel sigma (fun pi => if x ∈ selected B c pi then (1 : ℝ) else 0)]
  congr 1
  funext pi
  rw [selected_relabel B c pi sigma hs]
  have hm : x ∈ (selected B c pi).image sigma ↔ y ∈ selected B c pi := by
    constructor
    · rintro h
      obtain ⟨z, hz, he⟩ := Finset.mem_image.mp h
      have hz' := congrArg sigma he
      have : z = y := by simpa [sigma] using hz'
      simpa [this] using hz
    · intro h
      exact Finset.mem_image.mpr ⟨y, h, by simp [sigma]⟩
  simp only [hm]

lemma marginal_outside {n : ℕ} (B : Finset (Fin n)) (c : ℕ)
    (x : Fin n) (hx : x ∉ B) : marginal B c x = 0 := by
  classical
  have h : ∀ pi, x ∉ selected B c pi := fun pi hx' => hx (selected_subset B c pi hx')
  simp [marginal, h, uniformAvg]

lemma uniform_constant {n : ℕ} (a : ℝ) :
    uniformAvg (fun _ : Equiv.Perm (Fin n) => a) = a := by
  simp [uniformAvg, Fintype.card_perm, Nat.factorial_ne_zero]

lemma marginal_total {n : ℕ} (B : Finset (Fin n)) (c : ℕ) :
    (∑ x : Fin n, marginal B c x) = (min c B.card : ℕ) := by
  classical
  unfold marginal
  rw [← peer_uniform_sum]
  have hc : ∀ pi, (∑ x : Fin n, if x ∈ selected B c pi then (1 : ℝ) else 0) =
      (min c B.card : ℕ) := by
    intro pi
    simp only [← Nat.cast_one (R := ℝ), ← Nat.cast_zero (R := ℝ), ← Nat.cast_ite,
      ← Nat.cast_sum, ← Finset.card_filter]
    simp [selected_card]
  simp_rw [hc]
  exact uniform_constant _

lemma marginal_formula {n : ℕ} (B : Finset (Fin n)) (c : ℕ)
    (x : Fin n) (hx : x ∈ B) :
    marginal B c x = (min c B.card : ℕ) / (B.card : ℝ) := by
  classical
  have hb : (B.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨x, hx⟩
  have hs : (∑ y : Fin n, marginal B c y) = ∑ y ∈ B, marginal B c y := by
    symm
    apply Finset.sum_subset (Finset.subset_univ B)
    intro y _ hy
    exact marginal_outside B c y hy
  have he : (B.card : ℝ) * marginal B c x = (min c B.card : ℕ) := by
    rw [← marginal_total B c, hs]
    have : (∑ y ∈ B, marginal B c y) = ∑ _y ∈ B, marginal B c x := by
      apply Finset.sum_congr rfl
      intro y hy
      exact marginal_equal B c y x hy hx
    rw [this]
    simp
  exact (eq_div_iff hb).mpr (by simpa [mul_comm] using he)

lemma uniform_sum_finset {n : ℕ} {α : Type*} (A : Finset α)
    (f : Equiv.Perm (Fin n) → α → ℝ) :
    uniformAvg (fun pi => ∑ x ∈ A, f pi x) = ∑ x ∈ A, uniformAvg (fun pi => f pi x) := by
  unfold uniformAvg
  rw [Finset.sum_comm, Finset.mul_sum]

lemma selected_intersection_expectation {n : ℕ} (B R : Finset (Fin n)) (c : ℕ) :
    uniformAvg (fun pi => ((selected B c pi ∩ R).card : ℝ)) =
      ((min c B.card : ℕ) / (B.card : ℝ)) * ((B ∩ R).card : ℝ) := by
  classical
  have hi : ∀ pi, ((selected B c pi ∩ R).card : ℝ) =
      ∑ x ∈ R, if x ∈ selected B c pi then (1 : ℝ) else 0 := by
    intro pi
    have he : selected B c pi ∩ R = R.filter (fun x => x ∈ selected B c pi) := by
      ext x
      simp [and_comm]
    rw [he, Finset.card_filter]
    push_cast
    rfl
  simp_rw [hi]
  rw [uniform_sum_finset]
  change (∑ x ∈ R, marginal B c x) = _
  have he : (∑ x ∈ R, marginal B c x) =
      ∑ x ∈ R, if x ∈ B then ((min c B.card : ℕ) / (B.card : ℝ)) else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ B
    · simp [hx, marginal_formula B c x hx]
    · simp [hx, marginal_outside B c x hx]
  rw [he, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hf : R.filter (fun x => x ∈ B) = B ∩ R := by
    ext x
    simp [and_comm]
  rw [hf]
  ring

lemma preceding_card_idx {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (ht : t ∈ A) :
    (A.filter (· < t)).card = (A.sort (· ≤ ·)).idxOf t := by
  classical
  let e := A.orderIsoOfFin rfl
  let j := e.symm ⟨t, ht⟩
  have hc : (A.filter (· < t)).card = (Finset.Iio j).card := by
    apply Finset.card_bij (fun u hu => e.symm ⟨u, (Finset.mem_filter.mp hu).1⟩)
    · intro u hu
      apply Finset.mem_Iio.mpr
      exact e.symm.strictMono (show (⟨u, (Finset.mem_filter.mp hu).1⟩ : A) < ⟨t, ht⟩
        from (Finset.mem_filter.mp hu).2)
    · intro u _ v _ h
      exact congrArg Subtype.val (e.symm.injective h)
    · intro i hi
      refine ⟨(e i).val, ?_, e.symm_apply_apply i⟩
      apply Finset.mem_filter.mpr
      refine ⟨(e i).property, ?_⟩
      have hlt := e.strictMono (Finset.mem_Iio.mp hi)
      have he : e j = ⟨t, ht⟩ := e.apply_symm_apply _
      rw [he] at hlt
      exact hlt
  rw [hc, Fin.card_Iio]
  exact A.orderIsoOfFin_symm_apply rfl ⟨t, ht⟩

lemma selected_mem_iff {n : ℕ} (B : Finset (Fin n)) (c : ℕ)
    (pi : Equiv.Perm (Fin n)) (x : Fin n) :
    x ∈ selected B c pi ↔ x ∈ B ∧
      (B.filter fun y => pi.symm y < pi.symm x).card < c := by
  classical
  have hc : ((positions B pi).filter (· < pi.symm x)).card =
      (B.filter fun y => pi.symm y < pi.symm x).card := by
    apply Finset.card_bij (fun t _ => pi t)
    · intro t ht
      obtain ⟨htB, htx⟩ := Finset.mem_filter.mp ht
      apply Finset.mem_filter.mpr
      exact ⟨(Finset.mem_filter.mp htB).2, by simpa using htx⟩
    · intro u _ v _ h
      exact pi.injective h
    · intro y hy
      obtain ⟨hyB, hyx⟩ := Finset.mem_filter.mp hy
      refine ⟨pi.symm y, ?_, pi.apply_symm_apply y⟩
      exact Finset.mem_filter.mpr ⟨by simpa [positions] using hyB, hyx⟩
  by_cases hx : x ∈ B
  · have ht : pi.symm x ∈ positions B pi := by simpa [positions] using hx
    have hm : x ∈ selected B c pi ↔
        pi.symm x ∈ ((positions B pi).sort (· ≤ ·)).take c := by
      unfold selected
      constructor
      · intro h
        obtain ⟨t, ht, he⟩ := Finset.mem_image.mp h
        have : t = pi.symm x := by rw [← he]; simp
        simpa [this] using List.mem_toFinset.mp ht
      · intro h
        exact Finset.mem_image.mpr ⟨pi.symm x, List.mem_toFinset.mpr h, pi.apply_symm_apply x⟩
    rw [hm, List.mem_take_iff_idxOf_lt (by simpa using ht),
      ← preceding_card_idx _ _ ht, hc]
    simp [hx]
  · have hs : x ∉ selected B c pi := fun h => hx (selected_subset B c pi h)
    simp [hx, hs]

lemma order_fiber_average {q : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (e : Fin q ≃ β) (f : (Fin q ≃ β) → ℝ) :
    (1 / (q.factorial : ℝ)) * (∑ r : Fin q ≃ β, f r) =
      uniformAvg (fun pi => f (pi.trans e)) := by
  classical
  unfold uniformAvg
  congr 1
  symm
  apply Fintype.sum_equiv
    (show Equiv.Perm (Fin q) ≃ (Fin q ≃ β) from
      { toFun := fun pi => pi.trans e
        invFun := fun r => r.trans e.symm
        left_inv := by intro pi; ext x; simp
        right_inv := by intro r; ext x; simp })
  intro pi
  rfl

lemma paired_order_fiber_average {p q : ℕ} {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : Fin p ≃ α) (d : Fin q ≃ β) (f : (Fin p ≃ α) → (Fin q ≃ β) → ℝ) :
    (1 / ((p.factorial : ℝ) * (q.factorial : ℝ))) *
      (∑ l : Fin p ≃ α, ∑ r : Fin q ≃ β, f l r) =
    uniformAvg (fun pi => uniformAvg (fun rho => f (pi.trans e) (rho.trans d))) := by
  classical
  rw [← order_fiber_average e (fun l => uniformAvg (fun rho => f l (rho.trans d)))]
  simp_rw [← order_fiber_average d (f _)]
  simp only [← Finset.mul_sum]
  ring

end SamplingAudit
theorem rank_induction_from_recurrences
    (hphase2 : ∀ (k : ℕ), 2 ≤ k → ∀ (S : Finset ℝ) (r : ℕ), r ≤ S.card →
      ((min r k : ℕ) : ℝ) / k * ((k/2 : ℕ) - Real.sqrt (2*(k/2 : ℕ))) ≤ RC S k r)
    (hrecursive : ∀ (k : ℕ), 61 ≤ k →
      (∀ (S : Finset ℝ) (r : ℕ), r ≤ S.card →
        (1-5/Real.sqrt (k/2 : ℕ)) * (min r (k/2) : ℕ) ≤ RC S (k/2) r) →
      ∀ (S : Finset ℝ) (r : ℕ), r ≤ S.card →
        (min r k : ℕ) * ((1-5/Real.sqrt (k/2 : ℕ)) *
          (1/2-1/(4*Real.sqrt (k : ℝ))-1/(2*(k : ℝ))) +
          (k/2 : ℕ)/(k : ℝ)-Real.sqrt (2*(k/2 : ℕ))/(k : ℝ)) ≤ RC S k r) :
    ∀ (k : ℕ) (S : Finset ℝ) (r : ℕ), r ≤ S.card →
      (1-5/Real.sqrt (k : ℝ)) * (min r k : ℕ) ≤ RC S k r := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro S r hr
    by_cases hk0 : k = 0
    · subst k
      simpa using RC_nonneg S 0 r
    by_cases hsmall : k ≤ 25
    · have hc := (small_coefficient k hsmall).resolve_right hk0
      exact (mul_nonpos_of_nonpos_of_nonneg hc (Nat.cast_nonneg _)).trans (RC_nonneg S k r)
    by_cases hmid : k ≤ 60
    · have hc := middle_coefficient k (by omega) hmid
      have hb := hphase2 k (by omega) S r hr
      calc
        _ ≤ ((k/2 : ℕ)/(k : ℝ)-Real.sqrt (2*(k/2 : ℕ))/(k : ℝ)) * (min r k : ℕ) :=
          mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
        _ = ((min r k : ℕ) : ℝ)/k*((k/2 : ℕ)-Real.sqrt (2*(k/2 : ℕ))) := by ring
        _ ≤ _ := hb
    · have hk : 61 ≤ k := by omega
      have hih := ih (k/2) (by omega)
      have hb := hrecursive k hk hih S r hr
      have hc := mul_le_mul_of_nonneg_right (large_coefficient k hk)
        (Nat.cast_nonneg (min r k) : (0 : ℝ) ≤ (min r k : ℕ))
      exact hc.trans (by simpa only [mul_comm] using hb)

theorem native_topK_mono (S : Finset ℝ) {r s : ℕ} (hrs : r ≤ s) :
    topK S r ⊆ topK S s := by
  classical
  rw [topK_eq_image, topK_eq_image]
  apply Finset.image_subset_image
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    lt_of_lt_of_le (Finset.mem_filter.mp hi).2 hrs⟩

theorem native_RC_mono (S : Finset ℝ) (k : ℕ) {r s : ℕ} (hrs : r ≤ s) :
    RC S k r ≤ RC S k s := by
  classical
  unfold RC uniformAvg
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro pi _
  apply expectation_mono
  intro A _
  exact_mod_cast Finset.card_le_card (show
      A.filter (fun t => arrivals S pi t ∈ topK S r) ⊆
      A.filter (fun t => arrivals S pi t ∈ topK S s) from by
    intro t ht
    obtain ⟨htA, htR⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨htA, native_topK_mono S hrs htR⟩)

end SecretaryProof
-- END WeightedReduction

-- BEGIN FixedCap

open MultiChoiceSecretary.Alg
open scoped Classical
namespace SecretaryProof

lemma before_orderIso {α : Type*} [LinearOrder α] (A : Finset α) (i : Fin A.card) :
    (A.filter (· < (A.orderIsoOfFin rfl i).val)).card = i.val := by
  classical
  let e := A.orderIsoOfFin rfl
  have h : (A.filter (· < (e i).val)).card = (Finset.Iio i).card := by
    apply Finset.card_bij (fun a ha => e.symm ⟨a,(Finset.mem_filter.mp ha).1⟩)
    · intro a ha
      simp only [Finset.mem_Iio]
      have ht : (⟨a,(Finset.mem_filter.mp ha).1⟩ : A) < e i := (Finset.mem_filter.mp ha).2
      simpa using e.symm.strictMono ht
    · intro a ha b hb he
      have := congrArg (fun j => (e j).val) he
      simpa using this
    · intro j hj
      refine ⟨(e j).val, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨(e j).property, e.lt_iff_lt.mpr (Finset.mem_Iio.mp hj)⟩
      · exact e.symm_apply_apply j
  simpa only [Fin.card_Iio] using h

lemma first_card_eq {α : Type*} [LinearOrder α] (A : Finset α) (c : ℕ) :
    (A.filter fun a => (A.filter (· < a)).card < c).card = min c A.card := by
  classical
  let e := A.orderIsoOfFin rfl
  have h : (A.filter fun a => (A.filter (· < a)).card < c).card =
      (Finset.univ.filter fun i : Fin A.card => i.val < c).card := by
    apply Finset.card_bij (fun a ha => e.symm ⟨a,(Finset.mem_filter.mp ha).1⟩)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hb := before_orderIso A (e.symm ⟨a,(Finset.mem_filter.mp ha).1⟩)
      change (A.filter (· < (e (e.symm ⟨a,(Finset.mem_filter.mp ha).1⟩)).val)).card = _ at hb
      simp only [OrderIso.apply_symm_apply] at hb
      rw [← hb]
      exact (Finset.mem_filter.mp ha).2
    · intro a ha b hb he
      have := congrArg (fun j => (e j).val) he
      simpa using this
    · intro j hj
      refine ⟨(e j).val, ?_, e.symm_apply_apply j⟩
      exact Finset.mem_filter.mpr ⟨(e j).property, by
        rw [before_orderIso]
        exact (Finset.mem_filter.mp hj).2⟩
  rw [h]
  have he : {i : Fin A.card // i.val < c} ≃ Fin (min c A.card) :=
    { toFun := fun i => ⟨i.val.val, lt_min i.property i.val.isLt⟩
      invFun := fun i => ⟨⟨i.val,(lt_min_iff.mp i.isLt).2⟩,(lt_min_iff.mp i.isLt).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_subtype, Fintype.card_fin] using Fintype.card_congr he

noncomputable def eligibleRanks {n : ℕ} (ell : ℕ) (b : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => b i = false ∧ heads b i.val < ell

lemma eligibleRanks_card {n : ℕ} (ell : ℕ) (b : Fin n → Bool) :
    ((eligibleRanks ell b).card : ℝ) = failures ell b := by
  classical
  unfold failures inspected acceptedHeads eligibleRanks
  rw [← Finset.sum_sub_distrib]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro i _
  unfold active
  cases b i <;> by_cases hh : heads b i.val < ell <;> simp [hh]

lemma eligibleRanks_concentration {n : ℕ} (ell : ℕ) (hn : 2*ell ≤ n) :
    fairAvg (fun b : Fin n → Bool => |((eligibleRanks ell b).card : ℝ) - ell|) ≤
      Real.sqrt (2*ell) := by
  simpa only [eligibleRanks_card] using failures_abs_le ell hn

lemma descending_greater_card (Y : Finset ℝ) (i : Fin Y.card) :
    (Y.filter fun y => descending Y i < y).card = i.val := by
  exact before_orderIso (α := ℝᵒᵈ) Y i

lemma descending_get (Y : Finset ℝ) (i : Fin Y.card) :
    (Y.sort (· ≥ ·))[i.val]? = some (descending Y i) := by
  rw [← descending_list]
  simp

lemma threshold_exceeds_iff (Y : Finset ℝ) (z : ℝ) (hz : z ∉ Y)
    (ell : ℕ) (hell : 0 < ell) :
    exceeds ((Y.sort (· ≥ ·))[ell-1]?) z ↔
      (Y.filter fun y => z < y).card < ell := by
  classical
  by_cases he : ell ≤ Y.card
  · let i : Fin Y.card := ⟨ell-1, by omega⟩
    rw [show ell-1 = i.val from rfl, descending_get]
    change descending Y i < z ↔ _
    have hi := descending_greater_card Y i
    have hne : z ≠ descending Y i := by
      intro h
      exact hz (h ▸ descending_mem Y i)
    constructor
    · intro hlt
      have hs : (Y.filter fun y => z < y) ⊆ (Y.filter fun y => descending Y i < y) := by
        intro y hy
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
          hlt.trans (Finset.mem_filter.mp hy).2⟩
      have := Finset.card_le_card hs
      change (Y.filter fun y => descending Y i < y).card = ell-1 at hi
      omega
    · intro hc
      by_contra hn
      have hlt : z < descending Y i := lt_of_le_of_ne (le_of_not_gt hn) hne
      have hs : (Y.filter fun y => descending Y i < y) ⊂ (Y.filter fun y => z < y) := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨?_, ?_⟩
        · intro y hy
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
            hlt.trans (Finset.mem_filter.mp hy).2⟩
        · intro heq
          have hm : descending Y i ∈ Y.filter (fun y => z < y) := by
            simp [descending_mem, hlt]
          rw [← heq] at hm
          simp at hm
      have := Finset.card_lt_card hs
      change (Y.filter fun y => descending Y i < y).card = ell-1 at hi
      omega
  · have hn : Y.card ≤ ell-1 := by omega
    rw [List.getElem?_eq_none (by simpa using hn)]
    simp only [exceeds, true_iff]
    exact lt_of_le_of_lt (Finset.card_filter_le _ _) (by omega)

noncomputable def sampledValues (S : Finset ℝ) (b : Fin S.card → Bool) : Finset ℝ :=
  (Finset.univ.filter fun i => b i = true).image (descending S)

lemma descending_mem_sampled (S : Finset ℝ) (b : Fin S.card → Bool) (i : Fin S.card) :
    descending S i ∈ sampledValues S b ↔ b i = true := by
  classical
  simp only [sampledValues, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, he⟩
    exact (descending_injective S he) ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

lemma sampled_greater_card (S : Finset ℝ) (b : Fin S.card → Bool) (i : Fin S.card) :
    ((sampledValues S b).filter fun y => descending S i < y).card = heads b i.val := by
  classical
  have he : ((sampledValues S b).filter fun y => descending S i < y) =
      (Finset.univ.filter fun j => j.val < i.val ∧ b j = true).image (descending S) := by
    ext y
    simp only [sampledValues, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hlt⟩
      exact ⟨j, ⟨(descending_antitone S).lt_iff_gt.mp hlt, hj⟩, rfl⟩
    · rintro ⟨j, ⟨hji, hj⟩, rfl⟩
      exact ⟨⟨j, hj, rfl⟩, descending_antitone S hji⟩
  rw [he, Finset.card_image_of_injective _ (descending_injective S)]
  rfl

lemma sampled_threshold_eligible (S : Finset ℝ) (b : Fin S.card → Bool)
    (ell : ℕ) (hell : 0 < ell) (i : Fin S.card) (hi : b i = false) :
    exceeds (((sampledValues S b).sort (· ≥ ·))[ell-1]?) (descending S i) ↔
      heads b i.val < ell := by
  rw [threshold_exceeds_iff _ _ (by simp [descending_mem_sampled, hi]) ell hell,
    sampled_greater_card]

lemma qCount_exceeds (S Y : Finset ℝ) (ell : ℕ) :
    qCount S Y ell = ((S \ Y).filter fun z =>
      exceeds ((Y.sort (· ≥ ·))[ell-1]?) z).card := by
  unfold qCount
  cases (Y.sort (· ≥ ·))[ell-1]? <;> simp [exceeds]

lemma sampled_qCount (S : Finset ℝ) (b : Fin S.card → Bool) (ell : ℕ)
    (hell : 0 < ell) :
    qCount S (sampledValues S b) ell = (eligibleRanks ell b).card := by
  classical
  rw [qCount_exceeds]
  have he : ((S \ sampledValues S b).filter fun z =>
      exceeds (((sampledValues S b).sort (· ≥ ·))[ell-1]?) z) =
      (eligibleRanks ell b).image (descending S) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_image]
    constructor
    · rintro ⟨⟨hz, hn⟩, ht⟩
      obtain ⟨i, rfl⟩ := descending_surjective S z hz
      have hi : b i = false := by simpa [descending_mem_sampled] using hn
      refine ⟨i, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi,
        (sampled_threshold_eligible S b ell hell i hi).mp ht⟩
    · rintro ⟨i, hi, rfl⟩
      have hi' := (Finset.mem_filter.mp hi).2
      exact ⟨⟨descending_mem S i, by simp [descending_mem_sampled, hi'.1]⟩,
        (sampled_threshold_eligible S b ell hell i hi'.1).mpr hi'.2⟩
  rw [he, Finset.card_image_of_injective _ (descending_injective S)]

lemma fin_prefix_card {n k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter fun i : Fin n => i.val < k).card = k := by
  classical
  let e : {i : Fin n // i.val < k} ≃ Fin k :=
    { toFun := fun i => ⟨i.val.val, i.property⟩
      invFun := fun i => ⟨⟨i.val, i.isLt.trans_le hk⟩, i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_subtype, Fintype.card_fin] using Fintype.card_congr e

lemma eligible_prefix_dichotomy {n k : ℕ} (hk : k ≤ n) (ell : ℕ)
    (b : Fin n → Bool) :
    (eligibleRanks ell b).filter (fun i => i.val < k) = eligibleRanks ell b ∨
    k - (ell-1) ≤ ((eligibleRanks ell b).filter fun i => i.val < k).card := by
  classical
  by_cases hh : ell ≤ heads b k
  · left
    apply Finset.filter_eq_self.mpr
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    by_contra hn
    have hm := heads_mono b (show k ≤ i.val by omega)
    omega
  · right
    have he : (eligibleRanks ell b).filter (fun i => i.val < k) =
        Finset.univ.filter (fun i : Fin n => i.val < k ∧ b i = false) := by
      ext i
      simp only [eligibleRanks, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hfalse, _⟩, hlt⟩
        exact ⟨hlt,hfalse⟩
      · rintro ⟨hlt,hfalse⟩
        have hm := heads_mono b (Nat.le_of_lt hlt)
        exact ⟨⟨hfalse, by omega⟩, hlt⟩
    rw [he]
    have hc := (Finset.univ.filter fun i : Fin n => i.val < k).card_filter_add_card_filter_not
      (fun i : Fin n => b i = true)
    have he1 : ((Finset.univ.filter fun i : Fin n => i.val < k).filter fun i => b i = true) =
        Finset.univ.filter (fun i : Fin n => i.val < k ∧ b i = true) := by ext i; simp
    have he2 : ((Finset.univ.filter fun i : Fin n => i.val < k).filter fun i => ¬ b i = true) =
        Finset.univ.filter (fun i : Fin n => i.val < k ∧ b i = false) := by ext i; simp
    rw [he1, he2, fin_prefix_card hk] at hc
    change heads b k + _ = k at hc
    omega

lemma cap_fraction_bound {q t c ell : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t)
    (he : 0 ≤ ell) (hec : ell ≤ c) (htq : t ≤ q)
    (hd : t = q ∨ c+1 ≤ t) :
    ell - |q-ell| ≤ min c q / q * t := by
  by_cases hq0 : q = 0
  · subst q
    have ht0 : t = 0 := le_antisymm htq ht
    simp [ht0, abs_of_nonneg he]
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  by_cases hqc : q ≤ c
  · have ht0 : t = q := hd.resolve_right (by linarith)
    rw [min_eq_right hqc, ht0, div_self hq0, one_mul]
    have hab : ell-q ≤ |q-ell| := by
      simpa only [neg_sub] using neg_le_abs (q-ell)
    linarith
  · have hcq : c < q := lt_of_not_ge hqc
    have hct : c ≤ t := hd.elim (fun h => by rw [h]; linarith) (fun h => by linarith)
    rw [min_eq_left (le_of_lt hcq), abs_of_nonneg (by linarith : 0 ≤ q-ell)]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hqp).mpr
    have hmul : c*c ≤ c*t := mul_le_mul_of_nonneg_left hct (by linarith)
    nlinarith [sq_nonneg (q-ell)]

noncomputable def rankYield {n : ℕ} (ell c r : ℕ) (b : Fin n → Bool) : ℝ :=
  (min c (eligibleRanks ell b).card : ℕ) /
    ((eligibleRanks ell b).card : ℝ) *
      (((eligibleRanks ell b).filter fun i => i.val < r).card : ℝ)

lemma rankYield_top_budget {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (b : Fin n → Bool) :
    (k/2 : ℕ) - |((eligibleRanks (k/2) b).card : ℝ) - (k/2 : ℕ)| ≤
      rankYield (k/2) (k-k/2) k b := by
  have hc : k/2 ≤ k-k/2 := by omega
  have htq := Finset.card_filter_le (eligibleRanks (k/2) b) (fun i => i.val < k)
  have hd := eligible_prefix_dichotomy hkn (k/2) b
  have hd' : (((eligibleRanks (k/2) b).filter fun i => i.val < k).card : ℝ) =
      ((eligibleRanks (k/2) b).card : ℝ) ∨
      (k-k/2 : ℕ) + (1:ℝ) ≤ (((eligibleRanks (k/2) b).filter fun i => i.val < k).card : ℝ) := by
    rcases hd with h | h
    · left
      rw [h]
    · right
      have hn : k-k/2+1 ≤ ((eligibleRanks (k/2) b).filter fun i => i.val < k).card := by omega
      exact_mod_cast hn
  simpa only [rankYield, Nat.cast_min] using
    cap_fraction_bound (q := ((eligibleRanks (k/2) b).card : ℝ))
      (t := (((eligibleRanks (k/2) b).filter fun i => i.val < k).card : ℝ))
      (c := (k-k/2 : ℕ)) (ell := (k/2 : ℕ))
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast hc) (by exact_mod_cast htq) hd'

lemma rankYield_top_budget_average {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    (k/2 : ℕ) - Real.sqrt (2*(k/2 : ℕ)) ≤
      fairAvg (rankYield (n := n) (k/2) (k-k/2) k) := by
  have hm := fairAvg_mono (fun b : Fin n → Bool => rankYield_top_budget hk hkn b)
  have hc := eligibleRanks_concentration (n := n) (k/2) (by omega)
  simp only [sub_eq_add_neg, fairAvg_add, fairAvg_neg, fairAvg_const] at hm
  simp only [sub_eq_add_neg] at hc
  linarith

lemma rankYield_eq_audit {n : ℕ} (ell c r : ℕ) :
    rankYield (n := n) ell c r = RankSwapAudit.yieldPrefix ell c r := rfl

lemma rankYield_all_rank {n k r : ℕ} (hk : 2 ≤ k) (hrn : r ≤ n) :
    (min r k : ℕ) / (k:ℝ) * ((k/2 : ℕ) - Real.sqrt (2*(k/2 : ℕ))) ≤
      fairAvg (rankYield (n := n) (k/2) (k-k/2) r) := by
  let N := max n k
  have hkn : k ≤ N := le_max_right _ _
  have hnN : n ≤ N := le_max_left _ _
  have hsr : min r k ≤ r := min_le_left _ _
  have hsk : min r k ≤ k := min_le_right _ _
  have hsn : min r k ≤ n := hsr.trans hrn
  have htop := rankYield_top_budget_average (n := N) hk hkn
  have hscale := RankSwapAudit.yieldPrefix_scaling hkn hsk (show 0 < k by omega)
    (k/2) (k-k/2)
  have hpad := RankSwapAudit.yieldPrefix_padding hnN hsn (k/2) (k-k/2)
  have hmono := fairAvg_mono (fun b : Fin n → Bool =>
    RankSwapAudit.yieldPrefix_mono hsr (k/2) (k-k/2) b)
  rw [rankYield_eq_audit] at htop ⊢
  exact (mul_le_mul_of_nonneg_left htop (by positivity)).trans
    (hscale.trans (hpad.trans hmono))

end SecretaryProof
-- END FixedCap

-- BEGIN RankInduction

open MultiChoiceSecretary.Alg SecretaryWD.DiscUpper
open scoped Classical
namespace SecretaryProof

noncomputable def postcompose {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun π := π.trans e
  invFun π := π.trans e.symm
  left_inv π := by ext i; simp
  right_inv π := by ext i; simp

lemma uniformAvg_postcompose {n : ℕ} (e : Equiv.Perm (Fin n))
    (f : Equiv.Perm (Fin n) → ℝ) :
    uniformAvg (fun π => f (π.trans e)) = uniformAvg f := by
  unfold uniformAvg
  congr 1
  exact Equiv.sum_comp (postcompose e) f

lemma enumeration_average (S : Finset ℝ) (e : Fin S.card ≃ S)
    (f : (Fin S.card → ℝ) → ℝ) :
    uniformAvg (fun π => f (fun i => (e (π i)).val)) =
      uniformAvg (fun π => f (arrivals S π)) := by
  let σ : Equiv.Perm (Fin S.card) := e.trans (S.orderIsoOfFin rfl).toEquiv.symm
  have hx (π : Equiv.Perm (Fin S.card)) :
      (fun i => (e (π i)).val) = arrivals S (π.trans σ) := by
    funext i
    simp [arrivals, σ, Finset.orderEmbOfFin]
  simp_rw [hx]
  exact uniformAvg_postcompose σ (fun π => f (arrivals S π))

noncomputable def sampledEquiv (S : Finset ℝ) (b : Fin S.card → Bool) :
    {i : Fin S.card // b i = true} ≃ sampledValues S b :=
  Equiv.ofBijective (fun i : {i : Fin S.card // b i = true} =>
    (⟨descending S i.val, (descending_mem_sampled S b i.val).mpr i.property⟩ : sampledValues S b)) (by
      constructor
      · intro i j hij
        apply Subtype.ext
        exact descending_injective S (congrArg (fun z : sampledValues S b => z.val) hij)
      · intro y
        have hy : y.val ∈ sampledValues S b := y.property
        simp only [sampledValues, Finset.mem_image] at hy
        obtain ⟨i, hi, he⟩ := hy
        exact ⟨⟨i,(Finset.mem_filter.mp hi).2⟩, Subtype.ext he⟩)

@[simp] lemma sampledEquiv_val (S : Finset ℝ) (b : Fin S.card → Bool)
    (i : {i : Fin S.card // b i = true}) :
    (sampledEquiv S b i).val = descending S i.val := rfl

lemma enumeration_RC (m : ℕ) (S : Finset ℝ) (e : Fin m ≃ S) (k r : ℕ) :
    uniformAvg (fun π : Equiv.Perm (Fin m) =>
      expectation (alg k m (fun i => (e (π i)).val)) (fun A =>
        ((A.filter fun i => (e (π i)).val ∈ topK S r).card : ℝ))) = RC S k r := by
  have hm : m = S.card := by simpa using Fintype.card_congr e
  subst m
  unfold RC
  exact enumeration_average S e (fun x => expectation (alg k S.card x)
    (fun A => ((A.filter fun i => x i ∈ topK S r).card : ℝ)))

lemma mem_topK_greater_card (S : Finset ℝ) (z : ℝ) (hz : z ∈ S) (r : ℕ) :
    z ∈ topK S r ↔ (S.filter fun y => z < y).card < r := by
  obtain ⟨i,rfl⟩ := descending_surjective S z hz
  rw [descending_topK, descending_greater_card]

lemma topK_subset_native (S : Finset ℝ) (r : ℕ) : topK S r ⊆ S := by
  intro z hz
  simp only [topK, List.mem_toFinset] at hz
  simpa only [Finset.mem_sort] using (List.mem_of_mem_take hz)

lemma topK_upward (S : Finset ℝ) (r : ℕ) {x y : ℝ}
    (hx : x ∈ topK S r) (hy : y ∈ S) (hxy : x < y) : y ∈ topK S r := by
  rw [mem_topK_greater_card S y hy r]
  have hxc := (mem_topK_greater_card S x (topK_subset_native S r hx) r).mp hx
  have hs : (S.filter fun z => y < z) ⊆ (S.filter fun z => x < z) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
      hxy.trans (Finset.mem_filter.mp hz).2⟩
  exact (Finset.card_le_card hs).trans_lt hxc

lemma topK_inter_subset (S Y : Finset ℝ) (r : ℕ) (hYS : Y ⊆ S) :
    Y ∩ topK S r = topK Y (Y ∩ topK S r).card := by
  classical
  ext x
  by_cases hxY : x ∈ Y
  · rw [mem_topK_greater_card Y x hxY]
    constructor
    · intro hx
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro y hy
        have hy' := Finset.mem_filter.mp hy
        exact Finset.mem_inter.mpr ⟨hy'.1,
          topK_upward S r (Finset.mem_inter.mp hx).2 (hYS hy'.1) hy'.2⟩
      · intro he
        have : x ∈ Y.filter (fun y => x < y) := by rw [he]; exact hx
        simp at this
    · intro hc
      by_contra hx
      have hs : Y ∩ topK S r ⊆ Y.filter (fun y => x < y) := by
        intro y hy
        have hy' := Finset.mem_inter.mp hy
        refine Finset.mem_filter.mpr ⟨hy'.1, ?_⟩
        by_contra hn
        have hle : y ≤ x := le_of_not_gt hn
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hx (Finset.mem_inter.mpr ⟨hxY,
            topK_upward S r hy'.2 (hYS hxY) hlt⟩)
        · exact hx (heq ▸ hy)
      have := Finset.card_le_card hs
      omega
  · have hxT : x ∉ topK Y (Y ∩ topK S r).card :=
      fun h => hxY (topK_subset_native Y _ h)
    simp [hxY, hxT]

lemma sampledValues_subset (S : Finset ℝ) (b : Fin S.card → Bool) : sampledValues S b ⊆ S := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact descending_mem S i

lemma sampled_top_card (S : Finset ℝ) (b : Fin S.card → Bool) (r : ℕ) :
    (sampledValues S b ∩ topK S r).card = heads b r := by
  classical
  have he : sampledValues S b ∩ topK S r =
      (Finset.univ.filter fun i : Fin S.card => i.val < r ∧ b i = true).image (descending S) := by
    ext x
    simp only [Finset.mem_inter, sampledValues, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, ht⟩
      exact ⟨i, ⟨(descending_topK S i r).mp ht,hi⟩,rfl⟩
    · rintro ⟨i, ⟨ht,hi⟩,rfl⟩
      exact ⟨⟨i,hi,rfl⟩,(descending_topK S i r).mpr ht⟩
  rw [he, Finset.card_image_of_injective _ (descending_injective S)]
  rfl

lemma sampled_top_eq (S : Finset ℝ) (b : Fin S.card → Bool) (r : ℕ) :
    sampledValues S b ∩ topK S r = topK (sampledValues S b) (heads b r) := by
  rw [← sampled_top_card S b r]
  exact topK_inter_subset S _ r (sampledValues_subset S b)

lemma prefix_order_average (S : Finset ℝ) (b : Fin S.card → Bool) (m : ℕ)
    (e : Fin m ≃ {i : Fin S.card // b i = true}) (k r : ℕ) :
    (1/(m.factorial:ℝ)) * (∑ l : Fin m ≃ {i : Fin S.card // b i = true},
      expectation (alg k m (fun i => descending S (l i).val))
        (fun A => ((A.filter fun i => descending S (l i).val ∈ topK S r).card : ℝ))) =
      RC (sampledValues S b) k (heads b r) := by
  classical
  rw [SamplingAudit.order_fiber_average e]
  have hx (l : Fin m ≃ {i : Fin S.card // b i = true}) (i : Fin m) :
      descending S (l i).val ∈ topK S r ↔
      descending S (l i).val ∈ topK (sampledValues S b) (heads b r) := by
    rw [← sampled_top_eq]
    simp only [Finset.mem_inter]
    exact ⟨fun h => ⟨(descending_mem_sampled S b _).mpr (l i).property,h⟩, fun h => h.2⟩
  simp_rw [hx]
  exact enumeration_RC m (sampledValues S b) (e.trans (sampledEquiv S b)) k (heads b r)

lemma prefix_values_split (S : Finset ℝ) {m : ℕ} (hm : m ≤ S.card)
    (π : Equiv.Perm (Fin S.card)) :
    (Finset.univ.filter fun t : Fin S.card => t.val < m).image (fun t => descending S (π t)) =
      sampledValues S (Split.permutation hm π).label := by
  classical
  ext z
  simp only [sampledValues, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨π t, ?_, rfl⟩
    apply (Split.prefix_label hm π (π t)).mpr
    exact ⟨⟨t.val,ht⟩, congrArg π (Fin.ext rfl)⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨t,ht⟩ := (Split.prefix_label hm π i).mp hi
    exact ⟨Fin.castLE hm t, t.isLt, congrArg (descending S) ht⟩

lemma prefixSorted_split (S : Finset ℝ) {m : ℕ} (hm : m ≤ S.card)
    (π : Equiv.Perm (Fin S.card)) :
    prefixSorted (fun t => descending S (π t)) m =
      (sampledValues S (Split.permutation hm π).label).sort (· ≥ ·) := by
  classical
  have hi : Function.Injective (fun t => descending S (π t)) :=
    (descending_injective S).comp π.injective
  unfold prefixSorted
  rw [← Finset.image_val_of_injOn hi.injOn, prefix_values_split S hm π]
  rfl

lemma kth_split (S : Finset ℝ) {m : ℕ} (hm : m ≤ S.card)
    (π : Equiv.Perm (Fin S.card)) (ell : ℕ) :
    kth (fun t => descending S (π t)) m ell =
      (((sampledValues S (Split.permutation hm π).label).sort (· ≥ ·))[ell-1]?) := by
  unfold kth
  rw [prefixSorted_split]

lemma filter_union_card {α : Type*} [DecidableEq α] (A B : Finset α)
    (P : α → Prop) [DecidablePred P] (h : Disjoint A B) :
    ((A ∪ B).filter P).card = (A.filter P).card + (B.filter P).card := by
  rw [Finset.filter_union, Finset.card_union_of_disjoint (h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

lemma filter_map_card {n m : ℕ} (hm : m ≤ n) (A : Finset (Fin m))
    (P : Fin n → Prop) [DecidablePred P] :
    ((A.map (Fin.castLEEmb hm)).filter P).card =
      (A.filter fun i => P (Fin.castLE hm i)).card := by
  rw [Finset.filter_map, Finset.card_map]
  rfl

lemma stage_count_lower {k n : ℕ} (hk : 2 ≤ k) (x : Fin n → ℝ)
    (P : Fin n → Prop) [DecidablePred P] :
    (∑ m : Fin (n+1), ((n.choose m.val:ℝ)/(2:ℝ)^n) *
      (expectation (alg (k/2) m.val (fun i => x (Fin.castLE m.is_le i)))
        (fun A => ((A.filter fun i => P (Fin.castLE m.is_le i)).card : ℝ)) +
       ((phase2 (k-k/2) x m.val (kth x m.val (k/2)) ∅).filter P).card)) ≤
    expectation (alg k n x) (fun A => ((A.filter P).card : ℝ)) := by
  obtain ⟨j,rfl⟩ : ∃ j, k = j+2 := ⟨k-2, by omega⟩
  rw [alg, expectation_map, stageWith_expectation]
  apply Finset.sum_le_sum
  intro m _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← expectation_const (alg ((j+2)/2) m.val (fun i => x (Fin.castLE m.is_le i)))
    (((phase2 (j+2-(j+2)/2) x m.val (kth x m.val ((j+2)/2)) ∅).filter P).card : ℝ),
    ← expectation_add]
  apply expectation_mono
  intro A hA
  have hc := alg_card_le ((j+2)/2) m.val (fun i => x (Fin.castLE m.is_le i)) A hA
  have hs := fixed_cap_subset (j+2) (j+2-(j+2)/2) x m.val (kth x m.val ((j+2)/2))
    (A.map (Fin.castLEEmb m.is_le)) (by rw [Finset.card_map]; omega)
  have hp := Finset.card_le_card (Finset.filter_subset_filter P hs)
  rw [filter_union_card _ _ P (prefix_phase2_disjoint m.is_le A (j+2) x _),
    Nat.cast_add, filter_map_card]
  exact add_le_add_right (Nat.cast_le.mpr hp) _

lemma suffix_before_card {n m : ℕ} (hm : m ≤ n) (P : Fin n → Prop) [DecidablePred P]
    (i : Fin (n-m)) :
    (Finset.univ.filter fun t : Fin n => m ≤ t.val ∧
      t < Split.positions hm (.inr i) ∧ P t).card =
    (Finset.univ.filter fun j : Fin (n-m) => j < i ∧ P (Split.positions hm (.inr j))).card := by
  classical
  apply Finset.card_bij (fun t ht => (⟨t.val-m, by
    have := (Finset.mem_filter.mp ht).2.1
    omega⟩ : Fin (n-m)))
  · intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · change t.val-m < i.val
      have hv : t.val < m+i.val := ht'.2.1
      omega
    · have he : Split.positions hm (.inr (⟨t.val-m, by omega⟩ : Fin (n-m))) = t := by
        apply Fin.ext
        simp only [Split.positions_inr_val]
        omega
      simpa only [he] using ht'.2.2
  · intro t ht u hu he
    have ht' := (Finset.mem_filter.mp ht).2.1
    have hu' := (Finset.mem_filter.mp hu).2.1
    have hv := congrArg Fin.val he
    change t.val-m = u.val-m at hv
    apply Fin.ext
    omega
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    refine ⟨Split.positions hm (.inr j), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [Split.positions_inr_val],
        by change m+j.val < m+i.val; omega, hj'.2⟩
    · apply Fin.ext
      simp only [Split.positions_inr_val]
      omega

lemma phase2_suffix_mem {n m : ℕ} (hm : m ≤ n) (x : Fin n → ℝ)
    (thr : Option ℝ) (c : ℕ) (i : Fin (n-m)) :
    Split.positions hm (.inr i) ∈ phase2 c x m thr ∅ ↔
      exceeds thr (x (Split.positions hm (.inr i))) ∧
      (Finset.univ.filter fun j : Fin (n-m) => j < i ∧
        exceeds thr (x (Split.positions hm (.inr j)))).card < c := by
  classical
  simp only [phase2, Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_empty,
    zero_add, Split.positions_inr_val]
  rw [suffix_before_card hm (fun t => exceeds thr (x t)) i]
  simp

lemma suffix_permutation_count {q : ℕ} (ρ : Equiv.Perm (Fin q)) (v : Fin q → ℝ)
    (thr : Option ℝ) (i : Fin q) :
    (Finset.univ.filter fun j : Fin q => j < i ∧ exceeds thr (v (ρ j))).card =
    ((Finset.univ.filter fun y : Fin q => exceeds thr (v y)).filter
      fun y => ρ.symm y < i).card := by
  classical
  apply Finset.card_bij (fun j _ => ρ j)
  · intro j hj
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ρ.symm_apply_apply, and_comm]
      using hj
  · intro j _ l _ h
    exact ρ.injective h
  · intro y hy
    refine ⟨ρ.symm y, ?_, ρ.apply_symm_apply y⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ρ.apply_symm_apply, and_comm]
      using hy

lemma phase2_suffix_selected {n m : ℕ} (hm : m ≤ n) (x : Fin n → ℝ)
    (v : Fin (n-m) → ℝ) (ρ : Equiv.Perm (Fin (n-m))) (thr : Option ℝ) (c : ℕ)
    (hx : ∀ i, x (Split.positions hm (.inr i)) = v (ρ i)) (i : Fin (n-m)) :
    Split.positions hm (.inr i) ∈ phase2 c x m thr ∅ ↔
      ρ i ∈ SamplingAudit.selected (Finset.univ.filter fun y => exceeds thr (v y)) c ρ := by
  classical
  rw [phase2_suffix_mem, SamplingAudit.selected_mem_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ρ.symm_apply_apply]
  simp_rw [hx]
  rw [suffix_permutation_count]

lemma phase2_selected_card {n m : ℕ} (hm : m ≤ n) (x : Fin n → ℝ)
    (v : Fin (n-m) → ℝ) (ρ : Equiv.Perm (Fin (n-m))) (thr : Option ℝ) (c : ℕ)
    (P : Fin n → Prop) [DecidablePred P] (Q : Fin (n-m) → Prop) [DecidablePred Q]
    (hx : ∀ i, x (Split.positions hm (.inr i)) = v (ρ i))
    (hP : ∀ i, P (Split.positions hm (.inr i)) ↔ Q (ρ i)) :
    ((phase2 c x m thr ∅).filter P).card =
      ((SamplingAudit.selected (Finset.univ.filter fun y => exceeds thr (v y)) c ρ).filter Q).card := by
  classical
  apply Finset.card_bij (fun t ht => ρ (⟨t.val-m, by
    have := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2.1
    omega⟩ : Fin (n-m)))
  · intro t ht
    have ht' := Finset.mem_filter.mp ht
    have htm := (Finset.mem_filter.mp ht'.1).2.1
    let i : Fin (n-m) := ⟨t.val-m, by omega⟩
    have he : Split.positions hm (.inr i) = t := by
      apply Fin.ext
      change m+(t.val-m) = t.val
      omega
    apply Finset.mem_filter.mpr
    exact ⟨(phase2_suffix_selected hm x v ρ thr c hx i).mp (he ▸ ht'.1),
      (hP i).mp (he ▸ ht'.2)⟩
  · intro t ht u hu he
    have htm := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2.1
    have hum := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2.1
    have hv := congrArg Fin.val (ρ.injective he)
    change t.val-m = u.val-m at hv
    exact Fin.ext (by omega)
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    let i := ρ.symm y
    refine ⟨Split.positions hm (.inr i), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨(phase2_suffix_selected hm x v ρ thr c hx i).mpr
        (by simpa [i] using hy'.1), (hP i).mpr (by simpa [i] using hy'.2)⟩
    · calc
        ρ _ = ρ i := by
          apply congrArg ρ
          apply Fin.ext
          change (m+i.val)-m = i.val
          omega
        _ = y := ρ.apply_symm_apply y

noncomputable def orderPermutation {n m : ℕ} (hm : m ≤ n) (b : Fin n → Bool)
    (l : Fin m ≃ {i // b i = true}) (e : Fin (n-m) ≃ {i // b i = false}) :
    Equiv.Perm (Fin n) := (Split.permutation hm).symm ⟨b,l,e⟩

@[simp] lemma orderPermutation_split {n m : ℕ} (hm : m ≤ n) (b : Fin n → Bool)
    (l : Fin m ≃ {i // b i = true}) (e : Fin (n-m) ≃ {i // b i = false}) :
    Split.permutation hm (orderPermutation hm b l e) = ⟨b,l,e⟩ :=
  (Split.permutation hm).apply_symm_apply _

lemma orderPermutation_right {n m : ℕ} (hm : m ≤ n) (b : Fin n → Bool)
    (l : Fin m ≃ {i // b i = true}) (e : Fin (n-m) ≃ {i // b i = false})
    (i : Fin (n-m)) :
    orderPermutation hm b l e (Split.positions hm (.inr i)) = (e i).val := by
  have h := Split.permutation_right hm (orderPermutation hm b l e) i
  exact h.symm.trans (congrArg (fun d : Split.Data (Fin m) (Fin (n-m)) (Fin n) => (d.right i).val) (orderPermutation_split hm b l e))

lemma orderPermutation_left {n m : ℕ} (hm : m ≤ n) (b : Fin n → Bool)
    (l : Fin m ≃ {i // b i = true}) (e : Fin (n-m) ≃ {i // b i = false})
    (i : Fin m) :
    orderPermutation hm b l e (Fin.castLE hm i) = (l i).val := by
  have h := Split.permutation_left hm (orderPermutation hm b l e) i
  exact h.symm.trans (congrArg (fun d : Split.Data (Fin m) (Fin (n-m)) (Fin n) => (d.left i).val) (orderPermutation_split hm b l e))

lemma suffix_eligible_card (S : Finset ℝ) (b : Fin S.card → Bool) {q : ℕ}
    (e : Fin q ≃ {i // b i = false}) (ell : ℕ) (hell : 0 < ell)
    (R : Fin S.card → Prop) [DecidablePred R] :
    (Finset.univ.filter fun j : Fin q =>
      exceeds (((sampledValues S b).sort (· ≥ ·))[ell-1]?) (descending S (e j).val) ∧
        R (e j).val).card = ((eligibleRanks ell b).filter R).card := by
  classical
  apply Finset.card_bij (fun j _ => (e j).val)
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (e j).property, (sampled_threshold_eligible S b ell hell (e j).val (e j).property).mp hj'.1⟩,
      hj'.2⟩
  · intro j _ k _ h
    exact e.injective (Subtype.ext h)
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi)
    have hfalse := (Finset.mem_filter.mp hi'.1).2.1
    refine ⟨e.symm ⟨i,hfalse⟩, ?_, congrArg Subtype.val (e.apply_symm_apply _)⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [e.apply_symm_apply]
    exact ⟨(sampled_threshold_eligible S b ell hell i hfalse).mpr
      (Finset.mem_filter.mp hi'.1).2.2, hi'.2⟩

noncomputable def suffixCount (S : Finset ℝ) {m : ℕ} (hm : m ≤ S.card)
    (b : Fin S.card → Bool) (l : Fin m ≃ {i // b i = true})
    (e : Fin (S.card-m) ≃ {i // b i = false}) (ell c r : ℕ) : ℕ :=
  let π := orderPermutation hm b l e
  ((phase2 c (fun t => descending S (π t)) m
    (kth (fun t => descending S (π t)) m ell) ∅).filter fun t => (π t).val < r).card

lemma suffix_order_average (S : Finset ℝ) {m : ℕ} (hm : m ≤ S.card)
    (b : Fin S.card → Bool) (l : Fin m ≃ {i // b i = true})
    (e : Fin (S.card-m) ≃ {i // b i = false}) (ell c r : ℕ) (hell : 0 < ell) :
    uniformAvg (fun ρ : Equiv.Perm (Fin (S.card-m)) =>
      (suffixCount S hm b l (ρ.trans e) ell c r : ℝ)) = rankYield ell c r b := by
  classical
  let thr := (((sampledValues S b).sort (· ≥ ·))[ell-1]?)
  let v := fun j : Fin (S.card-m) => descending S (e j).val
  let B := Finset.univ.filter fun j : Fin (S.card-m) => exceeds thr (v j)
  let R := Finset.univ.filter fun j : Fin (S.card-m) => (e j).val.val < r
  have hc (ρ : Equiv.Perm (Fin (S.card-m))) :
      suffixCount S hm b l (ρ.trans e) ell c r = (SamplingAudit.selected B c ρ ∩ R).card := by
    let π := orderPermutation hm b l (ρ.trans e)
    have hl : (Split.permutation hm π).label = b :=
      congrArg Split.Data.label (orderPermutation_split hm b l (ρ.trans e))
    have ht : kth (fun t => descending S (π t)) m ell = thr := by
      rw [kth_split S hm π ell, hl]
    unfold suffixCount
    change ((phase2 c (fun t => descending S (π t)) m _ ∅).filter _).card = _
    rw [ht]
    have h := phase2_selected_card hm (fun t => descending S (π t)) v ρ thr c
      (fun t => (π t).val < r) (fun j => (e j).val.val < r)
      (fun i => congrArg (descending S) (orderPermutation_right hm b l (ρ.trans e) i))
      (fun i => by rw [orderPermutation_right]; rfl)
    rw [h]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and, B, R]
  simp_rw [hc]
  rw [SamplingAudit.selected_intersection_expectation]
  have hb : B.card = (eligibleRanks ell b).card := by
    have h := suffix_eligible_card S b e ell hell (fun _ => True)
    simpa [B, v, thr] using h
  have hbr : (B ∩ R).card = ((eligibleRanks ell b).filter fun i => i.val < r).card := by
    have h := suffix_eligible_card S b e ell hell (fun i => i.val < r)
    have he : B ∩ R = Finset.univ.filter fun j : Fin (S.card-m) =>
        exceeds thr (v j) ∧ (e j).val.val < r := by
      ext j
      simp [B, R]
    rw [he]
    exact h
  rw [hb, hbr]
  rfl

lemma joint_fiber_law (n : ℕ)
    (f : (m : Fin (n+1)) → Split.Data (Fin m.val) (Fin (n-m.val)) (Fin n) → ℝ)
    (g : (Fin n → Bool) → ℝ)
    (hf : ∀ (m : Fin (n+1)) (b : Fin n → Bool), Fintype.card {i // b i = true} = m.val →
      (1/((m.val.factorial:ℝ)*((n-m.val).factorial:ℝ))) *
      (∑ l : Fin m.val ≃ {i // b i = true}, ∑ e : Fin (n-m.val) ≃ {i // b i = false},
        f m ⟨b,l,e⟩) = g b) :
    (∑ m : Fin (n+1), ((n.choose m.val:ℝ)/(2:ℝ)^n) *
      uniformAvg (fun π => f m (Split.permutation m.is_le π))) = fairAvg g := by
  unfold uniformAvg fairAvg
  rw [Split.weighted_permutation n f]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  let m₀ : Fin (n+1) := ⟨Fintype.card {i // b i = true}, Nat.lt_succ_of_le (Split.true_card_le b)⟩
  rw [Finset.sum_eq_single m₀]
  · exact hf m₀ b rfl
  · intro m _ hne
    have hn : Fintype.card {i // b i = true} ≠ m.val := by
      intro he
      apply hne
      exact Fin.ext he.symm
    rw [Split.fiber_zero b hn]
    simp
  · simp

lemma uniformAvg_add {n : ℕ} (f g : Equiv.Perm (Fin n) → ℝ) :
    uniformAvg (fun π => f π + g π) = uniformAvg f + uniformAvg g := by
  simp only [uniformAvg, Finset.sum_add_distrib, mul_add]

lemma uniformAvg_mono {n : ℕ} {f g : Equiv.Perm (Fin n) → ℝ}
    (h : ∀ π, f π ≤ g π) : uniformAvg f ≤ uniformAvg g := by
  unfold uniformAvg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun π _ => h π)) (by positivity)

noncomputable def prefixCount (S : Finset ℝ) {m : ℕ} (b : Fin S.card → Bool)
    (l : Fin m ≃ {i // b i = true}) (k r : ℕ) : ℝ :=
  expectation (alg k m (fun i => descending S (l i).val))
    (fun A => ((A.filter fun i => (l i).val.val < r).card : ℝ))

lemma prefixCount_average (S : Finset ℝ) {m : ℕ} (b : Fin S.card → Bool)
    (l : Fin m ≃ {i // b i = true}) (k r : ℕ) :
    uniformAvg (fun π : Equiv.Perm (Fin m) => prefixCount S b (π.trans l) k r) =
      RC (sampledValues S b) k (heads b r) := by
  have h := prefix_order_average S b m l k r
  rw [SamplingAudit.order_fiber_average l] at h
  simpa only [prefixCount, descending_topK] using h

noncomputable def jointValue (S : Finset ℝ) (m : Fin (S.card+1))
    (d : Split.Data (Fin m.val) (Fin (S.card-m.val)) (Fin S.card)) (k r : ℕ) : ℝ :=
  prefixCount S d.label d.left (k/2) r +
    (suffixCount S m.is_le d.label d.left d.right (k/2) (k-k/2) r : ℝ)

lemma jointValue_fair (S : Finset ℝ) (k r : ℕ) (hk : 2 ≤ k) :
    (∑ m : Fin (S.card+1), ((S.card.choose m.val:ℝ)/(2:ℝ)^S.card) *
      uniformAvg (fun π => jointValue S m (Split.permutation m.is_le π) k r)) =
    fairAvg (fun b => RC (sampledValues S b) (k/2) (heads b r) +
      rankYield (k/2) (k-k/2) r b) := by
  apply joint_fiber_law S.card (fun m d => jointValue S m d k r)
  intro m b hb
  let l : Fin m.val ≃ {i // b i = true} := Fintype.equivOfCardEq (by simpa using hb.symm)
  let e : Fin (S.card-m.val) ≃ {i // b i = false} := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Split.bool_card_compl, hb])
  rw [SamplingAudit.paired_order_fiber_average l e]
  change uniformAvg (fun π => uniformAvg (fun ρ =>
    prefixCount S b (π.trans l) (k/2) r +
      (suffixCount S m.is_le b (π.trans l) (ρ.trans e) (k/2) (k-k/2) r : ℝ))) = _
  simp_rw [uniformAvg_add, SamplingAudit.uniform_constant,
    suffix_order_average S m.is_le b _ e (k/2) (k-k/2) r (by omega)]
  rw [prefixCount_average, SamplingAudit.uniform_constant]

lemma orderPermutation_permutation {n m : ℕ} (hm : m ≤ n) (π : Equiv.Perm (Fin n)) :
    orderPermutation hm (Split.permutation hm π).label
      (Split.permutation hm π).left (Split.permutation hm π).right = π := by
  exact (Split.permutation hm).symm_apply_apply π

lemma RC_descending (S : Finset ℝ) (k r : ℕ) :
    RC S k r = uniformAvg (fun π => expectation (alg k S.card (fun t => descending S (π t)))
      (fun A => ((A.filter fun t => (π t).val < r).card : ℝ))) := by
  have h := enumeration_average S (Finset.orderIsoOfFin (α := ℝᵒᵈ) S rfl).toEquiv
    (fun x => expectation (alg k S.card x) (fun A => ((A.filter fun t => x t ∈ topK S r).card : ℝ)))
  change uniformAvg (fun π => expectation (alg k S.card (fun t => descending S (π t)))
    (fun A => ((A.filter fun t => descending S (π t) ∈ topK S r).card : ℝ))) = RC S k r at h
  simpa only [descending_topK] using h.symm

lemma uniformAvg_sum_weight {n : ℕ} {α : Type*} [Fintype α]
    (w : α → ℝ) (f : α → Equiv.Perm (Fin n) → ℝ) :
    (∑ a, w a * uniformAvg (f a)) = uniformAvg (fun π => ∑ a, w a * f a π) := by
  unfold uniformAvg
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma RC_stage_lower (S : Finset ℝ) (k r : ℕ) (hk : 2 ≤ k) :
    fairAvg (fun b => RC (sampledValues S b) (k/2) (heads b r) +
      rankYield (k/2) (k-k/2) r b) ≤ RC S k r := by
  rw [← jointValue_fair S k r hk, uniformAvg_sum_weight, RC_descending]
  apply uniformAvg_mono
  intro π
  have h := stage_count_lower hk (fun t => descending S (π t)) (fun t => (π t).val < r)
  convert h using 1
  simp only [jointValue, prefixCount, suffixCount, Split.permutation_left,
    orderPermutation_permutation]
  apply Finset.sum_congr rfl
  intro m _
  congr 2

lemma native_phase2_lower (k : ℕ) (hk : 2 ≤ k) (S : Finset ℝ) (r : ℕ) (hr : r ≤ S.card) :
    (min r k : ℕ)/(k:ℝ) * ((k/2 : ℕ)-Real.sqrt (2*(k/2 : ℕ))) ≤ RC S k r := by
  have h := RC_stage_lower S k r hk
  rw [fairAvg_add] at h
  have hp := fairAvg_mono (fun b : Fin S.card → Bool => RC_nonneg (sampledValues S b) (k/2) (heads b r))
  rw [fairAvg_const] at hp
  have hy := rankYield_all_rank hk hr
  linarith

lemma native_recursive_lower (k : ℕ) (hk : 61 ≤ k)
    (ih : ∀ (S : Finset ℝ) (r : ℕ), r ≤ S.card →
      (1-5/Real.sqrt (k/2 : ℕ)) * (min r (k/2) : ℕ) ≤ RC S (k/2) r)
    (S : Finset ℝ) (r : ℕ) (hr : r ≤ S.card) :
    (min r k : ℕ) * ((1-5/Real.sqrt (k/2 : ℕ)) *
      (1/2-1/(4*Real.sqrt (k : ℝ))-1/(2*(k : ℝ))) +
      (k/2 : ℕ)/(k : ℝ)-Real.sqrt (2*(k/2 : ℕ))/(k : ℝ)) ≤ RC S k r := by
  let s := min r k
  let a : ℝ := 1-5/Real.sqrt (k/2 : ℕ)
  have hs : s ≤ S.card := (min_le_left _ _).trans hr
  have hsk : s ≤ k := min_le_right _ _
  have ha : 0 ≤ a := by
    have hL : (25:ℝ) ≤ (k/2 : ℕ) := by exact_mod_cast (show 25 ≤ k/2 by omega)
    have hsq : (5:ℝ) ≤ Real.sqrt (k/2 : ℕ) :=
      (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; omega)
    have hdiv : 5/Real.sqrt (k/2 : ℕ) ≤ 1 :=
      (div_le_one (by linarith : (0:ℝ) < Real.sqrt (k/2 : ℕ))).mpr hsq
    dsimp [a]
    linarith
  have hp := fairAvg_mono (fun b : Fin S.card → Bool =>
    ih (sampledValues S b) (heads b s) (by
      rw [← sampled_top_card S b s]
      exact Finset.card_le_card Finset.inter_subset_left))
  have hp' : a * fairAvg (fun b : Fin S.card → Bool => ((min (k/2) (heads b s) : ℕ) : ℝ)) ≤
      fairAvg (fun b => RC (sampledValues S b) (k/2) (heads b s)) := by
    change fairAvg (fun b : Fin S.card → Bool => a * (min (heads b s) (k/2) : ℕ)) ≤ _ at hp
    have he : (fun b : Fin S.card → Bool => a * (min (heads b s) (k/2) : ℕ)) =
        (fun b => (min (k/2) (heads b s) : ℕ) * a) := by
      funext b
      rw [min_comm, mul_comm]
    rw [he, fairAvg_mul_const] at hp
    simpa only [mul_comm] using hp
  have hm := phase1_marginal_scaled hs hsk (show 0 < k by omega) a ha
  have hy := rankYield_all_rank (n := S.card) (k := k) (r := s) (by omega) hs
  rw [min_eq_left hsk] at hy
  have hj := RC_stage_lower S k s (by omega)
  rw [fairAvg_add] at hj
  have hsum := (add_le_add (hm.trans hp') hy).trans hj
  have hout : (s:ℝ) * (a * (1/2-1/(4*Real.sqrt (k:ℝ))-1/(2*(k:ℝ))) +
      (k/2:ℕ)/(k:ℝ)-Real.sqrt (2*(k/2:ℕ))/(k:ℝ)) ≤ RC S k s := by
    calc
      _ = (s:ℝ)*a*(1/2-1/(4*Real.sqrt (k:ℝ))-1/(2*(k:ℝ))) +
          (s:ℝ)/(k:ℝ)*((k/2:ℕ)-Real.sqrt (2*(k/2:ℕ))) := by ring
      _ ≤ _ := hsum
  exact hout.trans (native_RC_mono S k (min_le_left r k))

lemma strong_rank_bound (k : ℕ) (S : Finset ℝ) (r : ℕ) (hr : r ≤ S.card) :
    (1-5/Real.sqrt (k:ℝ)) * (min r k : ℕ) ≤ RC S k r :=
  rank_induction_from_recurrences native_phase2_lower native_recursive_lower k S r hr

end SecretaryProof
-- END RankInduction

-- BEGIN NativeRoot

namespace MultiChoiceSecretary.Alg

theorem theorem_2_1 (S : Finset ℝ) (hS : ∀ x ∈ S, 0 ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    (1 - 5 / Real.sqrt k) * topSum S k ≤ expectedValue S k := by
  exact (fun (_ : 1 ≤ k) => SecretaryProof.weighted_native_reduction S k (1-5/Real.sqrt k) hS
    (fun r hr => SecretaryProof.strong_rank_bound k S r hr)) hk

end MultiChoiceSecretary.Alg

theorem solution (S : Finset ℝ) (hS : ∀ x ∈ S, 0 ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    (1 - 5 / Real.sqrt k) * MultiChoiceSecretary.Alg.topSum S k ≤
      MultiChoiceSecretary.Alg.expectedValue S k :=
  MultiChoiceSecretary.Alg.theorem_2_1 S hS k hk
-- END NativeRoot
