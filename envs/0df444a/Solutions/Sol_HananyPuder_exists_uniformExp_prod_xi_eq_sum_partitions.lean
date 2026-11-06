-- Prove2me | solution 1 for HananyPuder.exists_uniformExp_prod_xi_eq_sum_partitions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T23:00:22.236165+00:00
-- url     : https://prove2.me/submissions/a57107bf-ec3b-4612-892b-ca5b6d1bf133

import Mathlib
import Definitions.Def_StrongConv

open Equiv Finset

namespace HananyPuder.W2HP

theorem card_perm_extend {α D : Type*} [Fintype α] [DecidableEq α] [Fintype D]
    (ι κ : D ↪ α) :
    Fintype.card {σ : Perm α // ∀ d, σ (ι d) = κ d} =
      (Fintype.card α - Fintype.card D).factorial := by
  classical
  let e : {x // x ∈ Set.range ι} ≃ {x // x ∈ Set.range κ} :=
    (Equiv.ofInjective ι ι.injective).symm.trans (Equiv.ofInjective κ κ.injective)
  let σ₀ : Perm α := e.extendSubtype
  have h0 : ∀ d, σ₀ (ι d) = κ d := by
    intro d
    have := e.extendSubtype_apply_of_mem (ι d) ⟨d, rfl⟩
    simp only [σ₀, this, e, Equiv.trans_apply]
    rw [show (⟨ι d, ⟨d, rfl⟩⟩ : {x // x ∈ Set.range ι}) = Equiv.ofInjective ι ι.injective d from rfl,
      Equiv.symm_apply_apply]
    rfl
  let E1 : {σ : Perm α // ∀ d, σ (ι d) = κ d} ≃
      {τ : Perm α // ∀ a, ¬ (a ∉ Set.range ι) → τ a = a} :=
    { toFun := fun σ => ⟨σ₀⁻¹ * σ.1, by
        rintro a ha
        obtain ⟨d, rfl⟩ := not_not.1 ha
        simp [Perm.mul_apply, σ.2 d, ← h0 d]⟩
      invFun := fun τ => ⟨σ₀ * τ.1, by
        intro d
        simp [Perm.mul_apply, τ.2 (ι d) (by simp), h0 d]⟩
      left_inv := fun σ => by ext; simp
      right_inv := fun τ => by ext; simp }
  rw [Fintype.card_congr (E1.trans (Perm.subtypeEquivSubtypePerm _).symm), Fintype.card_perm,
    Fintype.card_subtype_compl, Fintype.card_range]

set_option linter.unusedSectionVars false

section Core

open Classical

variable {S B : Type*} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]

/-- Disjoint cycles of lengths `e β`, as points `(β, i)`. -/
abbrev Cyc (e : B → ℕ) := Σ β : B, Fin (e β)

/-- The cyclic successor `(β, i) ↦ (β, i + 1 mod e β)`. -/
def nxt (e : B → ℕ) (t : Cyc e) : Cyc e :=
  ⟨t.1, ⟨(t.2.1 + 1) % e t.1, Nat.mod_lt _ t.2.pos⟩⟩

theorem nxt_injective (e : B → ℕ) : Function.Injective (nxt e) := by
  rintro ⟨β, i⟩ ⟨β', i'⟩ h
  simp only [nxt, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h⟩ := h
  have h := Fin.mk.inj_iff.1 (eq_of_heq h)
  have h2 : i.1 + 1 ≡ i'.1 + 1 [MOD e β] := h
  have h3 := Nat.ModEq.add_right_cancel' 1 h2
  unfold Nat.ModEq at h3
  rw [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt i'.2] at h3
  exact Sigma.ext rfl (heq_of_eq (Fin.ext h3))

theorem sig_eq {e : B → ℕ} {β β' : B} {i i' : ℕ} (hi : i < e β) (hi' : i' < e β')
    (h1 : β = β') (h2 : i = i') : (⟨β, ⟨i, hi⟩⟩ : Cyc e) = ⟨β', ⟨i', hi'⟩⟩ := by
  subst h1 h2; rfl

/-- `σ` acts on the image of `ι` as the cyclic successor. -/
def Compat {N : ℕ} (e : B → ℕ) (σ : Perm (Fin N)) (ι : Cyc e ↪ Fin N) : Prop :=
  ∀ t, σ (ι t) = ι (nxt e t)

variable {N : ℕ} {e : B → ℕ} {σ : Perm (Fin N)} {ι : Cyc e ↪ Fin N}

theorem pow_compat (h : Compat e σ ι) (n : ℕ) (β : B) (i : Fin (e β)) :
    (σ ^ n) (ι ⟨β, i⟩) = ι ⟨β, ⟨(i.1 + n) % e β, Nat.mod_lt _ i.pos⟩⟩ := by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt i.2]
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, h]
    simp only [nxt]
    congr 3
    rw [Nat.mod_add_mod, add_assoc]

theorem pow_eq_self_iff_dvd {z : Fin N} {n : ℕ} :
    (σ ^ n) z = z ↔ Function.minimalPeriod σ z ∣ n := by
  rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
  rfl

theorem minimalPeriod_eq_of {z : Fin N} {m : ℕ} (h : ∀ n : ℕ, (σ ^ n) z = z ↔ m ∣ n) :
    Function.minimalPeriod σ z = m := by
  apply Nat.dvd_antisymm
  · rw [← pow_eq_self_iff_dvd]; exact (h m).2 dvd_rfl
  · exact (h _).1 (pow_eq_self_iff_dvd.2 dvd_rfl)

theorem pow_mod_minimalPeriod (z : Fin N) (n : ℕ) :
    (σ ^ (n % Function.minimalPeriod σ z)) z = (σ ^ n) z := by
  have := Function.iterate_mod_minimalPeriod_eq (f := σ) (x := z) (n := n)
  simpa only [Perm.iterate_eq_pow] using this

theorem pow_inj_lt_minimalPeriod {z : Fin N} {i i' : ℕ} (hi : i < Function.minimalPeriod σ z)
    (hi' : i' < Function.minimalPeriod σ z) (h : (σ ^ i) z = (σ ^ i') z) : i = i' := by
  have := Function.iterate_injOn_Iio_minimalPeriod (f := σ) (x := z) hi hi'
  simp only [Perm.iterate_eq_pow] at this
  exact this h

theorem compat_sameCycle (h : Compat e σ ι) {β β' : B} (hb : β = β') (i : Fin (e β))
    (i' : Fin (e β')) : σ.SameCycle (ι ⟨β, i⟩) (ι ⟨β', i'⟩) := by
  subst hb
  refine ⟨((e β - i.1 + i'.1 : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, pow_compat h]
  congr
  have : i.1 + (e β - i.1 + i'.1) = e β + i'.1 := by have := i.2; omega
  rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt i'.2]

theorem compat_eq_of_sameCycle (h : Compat e σ ι) {β β' : B} {i : Fin (e β)}
    {i' : Fin (e β')} (hs : σ.SameCycle (ι ⟨β, i⟩) (ι ⟨β', i'⟩)) : β = β' := by
  obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
  rw [pow_compat h] at hn
  exact congrArg Sigma.fst (ι.injective hn)

theorem compat_minimalPeriod (h : Compat e σ ι) (β : B) (i : Fin (e β)) :
    Function.minimalPeriod σ (ι ⟨β, i⟩) = e β := by
  apply minimalPeriod_eq_of
  intro n
  rw [pow_compat h]
  constructor
  · intro hn
    have h1 := Fin.mk.inj_iff.1 (eq_of_heq (Sigma.mk.inj_iff.1 (ι.injective hn)).2)
    have h2 : i.1 + n ≡ i.1 + 0 [MOD e β] := by
      unfold Nat.ModEq; rw [h1, add_zero, Nat.mod_eq_of_lt i.2]
    exact Nat.modEq_zero_iff_dvd.1 (h2.add_left_cancel' i.1)
  · rintro ⟨c, rfl⟩
    congr
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.2]

theorem compat_eq_pow (h : Compat e σ ι) (β : B) (i : Fin (e β)) :
    ι ⟨β, i⟩ = (σ ^ i.1) (ι ⟨β, ⟨0, i.pos⟩⟩) := by
  rw [pow_compat h]
  congr
  simp [Nat.mod_eq_of_lt i.2]

/-- The number of `σ` with `Compat e σ ι`. -/
theorem card_compat (ι : Cyc e ↪ Fin N) :
    (univ.filter fun σ : Perm (Fin N) => Compat e σ ι).card =
      (N - ∑ β, e β).factorial := by
  classical
  let κ : Cyc e ↪ Fin N := ⟨ι ∘ nxt e, ι.injective.comp (nxt_injective e)⟩
  have := card_perm_extend ι κ
  rw [Fintype.card_subtype] at this
  rw [Fintype.card_fin, Fintype.card_sigma] at this
  convert this using 3
  · rfl
  · simp

theorem sum_card_compat (hN : ∑ β, e β ≤ N) :
    ∑ σ : Perm (Fin N), (univ.filter fun ι : Cyc e ↪ Fin N => Compat e σ ι).card =
      N.factorial := by
  classical
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp_rw [← sum_filter, ← card_eq_sum_ones, card_compat, sum_const, card_univ,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_sigma, Fintype.card_fin, smul_eq_mul]
  rw [mul_comm]
  exact Nat.factorial_mul_descFactorial hN

/-- `y` has type `(b, e)` under `σ`: the points `y x`, `y x'` lie in one cycle iff `b x = b x'`,
and the cycle through `y x` has length `e (b x)`. -/
def IsType (b : S → B) (e : B → ℕ) (σ : Perm (Fin N)) (y : S → Fin N) : Prop :=
  (∀ x x', b x = b x' ↔ σ.SameCycle (y x) (y x')) ∧
    ∀ x, Function.minimalPeriod σ (y x) = e (b x)

/-- Exponent vectors: `0` at the representative of each block, `< e` elsewhere. -/
def Kset (b : S → B) (r : B → S) (e : B → ℕ) : Finset (S → ℕ) :=
  Fintype.piFinset fun x => if r (b x) = x then {0} else range (e (b x))

theorem Kset_lt {b : S → B} {r : B → S} (he : ∀ β, 0 < e β) {k : S → ℕ}
    (hk : k ∈ Kset b r e) (x : S) : k x < e (b x) := by
  have := Fintype.mem_piFinset.1 hk x
  split_ifs at this with h
  · rw [mem_singleton.1 this]; exact he _
  · exact mem_range.1 this

theorem Kset_rep {b : S → B} {r : B → S} (hr : ∀ β, b (r β) = β) {k : S → ℕ}
    (hk : k ∈ Kset b r e) (β : B) : k (r β) = 0 := by
  have := Fintype.mem_piFinset.1 hk (r β)
  rw [if_pos (by rw [hr])] at this
  exact mem_singleton.1 this

theorem card_Kset (b : S → B) (r : B → S) (e : B → ℕ) :
    (Kset b r e).card = ∏ x, if r (b x) = x then 1 else e (b x) := by
  rw [Kset, Fintype.card_piFinset]
  congr 1; ext x
  split_ifs <;> simp

/-- The `y` determined by cycles `ι` and exponents `k`. -/
def toY (b : S → B) (ι : Cyc e ↪ Fin N) (k : S → ℕ) (hk : ∀ x, k x < e (b x)) : S → Fin N :=
  fun x => ι ⟨b x, ⟨k x, hk x⟩⟩

theorem card_type (b : S → B) (r : B → S) (hr : ∀ β, b (r β) = β) (he : ∀ β, 0 < e β)
    (σ : Perm (Fin N)) :
    (univ.filter (IsType b e σ)).card =
      (univ.filter fun ι : Cyc e ↪ Fin N => Compat e σ ι).card * (Kset b r e).card := by
  rw [← card_product]
  symm
  refine card_bij (fun a ha => toY b a.1 a.2 (Kset_lt he (mem_product.1 ha).2)) ?_ ?_ ?_
  · -- lands in the type
    rintro ⟨ι, k⟩ ha
    obtain ⟨h1, h2⟩ := mem_product.1 ha
    have hc : Compat e σ ι := (mem_filter.1 h1).2
    refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
    · intro x x'
      constructor
      · intro hb; exact compat_sameCycle hc hb _ _
      · intro hs; exact compat_eq_of_sameCycle hc hs
    · intro x
      exact compat_minimalPeriod hc _ _
  · rintro ⟨ι, k⟩ ha ⟨ι', k'⟩ ha' heq
    obtain ⟨h1, h2⟩ := mem_product.1 ha
    obtain ⟨h1', h2'⟩ := mem_product.1 ha'
    have hc : Compat e σ ι := (mem_filter.1 h1).2
    have hc' : Compat e σ ι' := (mem_filter.1 h1').2
    have hy : ∀ x, ι ⟨b x, ⟨k x, Kset_lt he h2 x⟩⟩ = ι' ⟨b x, ⟨k' x, Kset_lt he h2' x⟩⟩ :=
      fun x => congrFun heq x
    have h0 : ∀ β, ι ⟨β, ⟨0, he β⟩⟩ = ι' ⟨β, ⟨0, he β⟩⟩ := by
      intro β
      have := hy (r β)
      rwa [sig_eq _ (he β) (hr β) (Kset_rep hr h2 β),
        sig_eq _ (he β) (hr β) (Kset_rep hr h2' β)] at this
    have hι : ι = ι' := by
      ext ⟨β, i⟩
      rw [compat_eq_pow hc, compat_eq_pow hc', h0]
    subst hι
    refine Prod.ext rfl (funext fun x => ?_)
    have := sigma_mk_injective (ι.injective (hy x))
    exact Fin.mk.inj_iff.1 this
  · intro y hy
    obtain ⟨hT1, hT2⟩ := (mem_filter.1 hy).2
    have hper : ∀ β, Function.minimalPeriod σ (y (r β)) = e β := by
      intro β; rw [hT2, hr]
    have hinj : Function.Injective (fun t : Cyc e => (σ ^ t.2.1) (y (r t.1))) := by
      rintro ⟨β, i⟩ ⟨β', i'⟩ h
      simp only at h
      have hs : σ.SameCycle (y (r β)) (y (r β')) := by
        have : σ.SameCycle (y (r β)) ((σ ^ i'.1) (y (r β'))) := by
          rw [← h]; exact Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)
        exact Perm.sameCycle_pow_right.1 this
      have hb := (hT1 _ _).2 hs
      rw [hr, hr] at hb
      subst hb
      have := pow_inj_lt_minimalPeriod (by rw [hper]; exact i.2) (by rw [hper]; exact i'.2) h
      exact Sigma.ext rfl (heq_of_eq (Fin.ext this))
    let ι : Cyc e ↪ Fin N := ⟨fun t => (σ ^ t.2.1) (y (r t.1)), hinj⟩
    have hc : Compat e σ ι := by
      rintro ⟨β, i⟩
      show σ ((σ ^ i.1) (y (r β))) = (σ ^ ((i.1 + 1) % e β)) (y (r β))
      rw [← Perm.mul_apply, ← pow_succ']
      have := pow_mod_minimalPeriod (σ := σ) (y (r β)) (i.1 + 1)
      rw [hper] at this
      exact this.symm
    have hsc : ∀ x, σ.SameCycle (y (r (b x))) (y x) := fun x => (hT1 _ _).1 (hr _)
    choose n hn using fun x => (hsc x).exists_nat_pow_eq
    let k : S → ℕ := fun x => n x % e (b x)
    have hk : k ∈ Kset b r e := by
      refine Fintype.mem_piFinset.2 fun x => ?_
      split_ifs with h
      · have := hn x
        rw [h, pow_eq_self_iff_dvd, hT2] at this
        exact mem_singleton.2 (Nat.mod_eq_zero_of_dvd this)
      · exact mem_range.2 (Nat.mod_lt _ (he _))
    refine ⟨(ι, k), mem_product.2 ⟨mem_filter.2 ⟨mem_univ _, hc⟩, hk⟩, ?_⟩
    funext x
    simp only [toY, ι, Function.Embedding.coeFn_mk, k]
    have := pow_mod_minimalPeriod (σ := σ) (y (r (b x))) (n x)
    rw [hper] at this
    rw [this, hn]

theorem sum_card_type (b : S → B) (r : B → S) (hr : ∀ β, b (r β) = β) (he : ∀ β, 0 < e β)
    (hN : ∑ β, e β ≤ N) :
    ∑ σ : Perm (Fin N), (univ.filter (IsType b e σ)).card =
      N.factorial * ∏ x, if r (b x) = x then 1 else e (b x) := by
  simp_rw [card_type b r hr he, ← sum_mul, sum_card_compat hN, card_Kset]

end Core

section Outer

open Classical

variable {S : Type*} [Fintype S] [DecidableEq S] {N : ℕ}

/-- The block of `x`, as an element of the set of parts. -/
def blk (P : Finpartition (univ : Finset S)) (x : S) : P.parts :=
  ⟨P.part x, P.part_mem.2 (mem_univ x)⟩

/-- A chosen representative of a part. -/
noncomputable def rep (P : Finpartition (univ : Finset S)) (A : P.parts) : S :=
  (P.nonempty_of_mem_parts A.2).choose

theorem rep_mem (P : Finpartition (univ : Finset S)) (A : P.parts) : rep P A ∈ A.1 :=
  (P.nonempty_of_mem_parts A.2).choose_spec

theorem blk_eq_iff_mem (P : Finpartition (univ : Finset S)) (x : S) (A : P.parts) :
    blk P x = A ↔ x ∈ A.1 := by
  rw [Subtype.ext_iff]; exact P.part_eq_iff_mem A.2

theorem blk_rep (P : Finpartition (univ : Finset S)) (A : P.parts) : blk P (rep P A) = A :=
  (blk_eq_iff_mem P _ A).2 (rep_mem P A)

theorem blk_eq_blk (P : Finpartition (univ : Finset S)) (x x' : S) :
    blk P x = blk P x' ↔ x' ∈ P.part x := by
  rw [eq_comm, blk_eq_iff_mem]; rfl

theorem finpartition_eq_of (P Q : Finpartition (univ : Finset S))
    (h : ∀ x x', x' ∈ P.part x ↔ x' ∈ Q.part x) : P = Q := by
  have hpart : ∀ x, P.part x = Q.part x := fun x => Finset.ext (h x)
  ext t
  constructor
  · intro ht
    obtain ⟨x, -, rfl⟩ := P.part_surjOn (Finset.mem_coe.2 ht)
    rw [hpart]; exact Q.part_mem.2 (mem_univ x)
  · intro ht
    obtain ⟨x, -, rfl⟩ := Q.part_surjOn (Finset.mem_coe.2 ht)
    rw [← hpart]; exact P.part_mem.2 (mem_univ x)

theorem minimalPeriod_pow_apply (σ : Perm (Fin N)) (z : Fin N) (n : ℕ) :
    Function.minimalPeriod σ ((σ ^ n) z) = Function.minimalPeriod σ z := by
  apply minimalPeriod_eq_of
  intro m
  rw [← pow_eq_self_iff_dvd, ← Perm.mul_apply, pow_mul_comm, Perm.mul_apply,
    (σ ^ n).injective.eq_iff]

theorem sameCycle_minimalPeriod {σ : Perm (Fin N)} {z z' : Fin N} (h : σ.SameCycle z z') :
    Function.minimalPeriod σ z' = Function.minimalPeriod σ z := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  exact minimalPeriod_pow_apply σ z n

/-- The partition of `S` by the cycles of `σ` containing the points `y x`. -/
noncomputable def cyclePart (σ : Perm (Fin N)) (y : S → Fin N) :
    Finpartition (univ : Finset S) :=
  Finpartition.ofSetoid (Setoid.comap y (Perm.SameCycle.setoid σ))

theorem mem_cyclePart {σ : Perm (Fin N)} {y : S → Fin N} {x x' : S} :
    x' ∈ (cyclePart σ y).part x ↔ σ.SameCycle (y x) (y x') :=
  Finpartition.mem_part_ofSetoid_iff_rel

theorem sum_isType (j : S → ℕ) (hj : ∀ x, 0 < j x) (σ : Perm (Fin N)) (y : S → Fin N) :
    (∑ P : Finpartition (univ : Finset S),
      ∑ e ∈ Fintype.piFinset (fun A : P.parts => (A.1.gcd j).divisors),
        if IsType (blk P) e σ y then 1 else 0) =
      if (∀ x, (σ ^ j x) (y x) = y x) then 1 else 0 := by
  split_ifs with hfix
  · rw [sum_eq_single (cyclePart σ y)]
    · set P := cyclePart σ y with hP
      have hrepA : ∀ (A : P.parts) x, x ∈ A.1 → σ.SameCycle (y (rep P A)) (y x) := by
        intro A x hx
        apply mem_cyclePart.1
        rw [← hP, P.part_eq_of_mem A.2 (rep_mem P A)]
        exact hx
      let e₀ : P.parts → ℕ := fun A => Function.minimalPeriod σ (y (rep P A))
      rw [sum_eq_single e₀]
      · rw [if_pos]
        refine ⟨fun x x' => ?_, fun x => ?_⟩
        · rw [blk_eq_blk]; exact mem_cyclePart
        · show Function.minimalPeriod σ (y x) = Function.minimalPeriod σ (y (rep P (blk P x)))
          exact sameCycle_minimalPeriod (hrepA _ x (P.mem_part (mem_univ x)))
      · intro e _ hne
        rw [if_neg]
        intro ht; apply hne
        funext A
        have := ht.2 (rep P A)
        rw [blk_rep] at this
        exact this.symm
      · intro hnot; exfalso; apply hnot
        rw [Fintype.mem_piFinset]
        intro A
        rw [Nat.mem_divisors]
        constructor
        · apply Finset.dvd_gcd
          intro x hx
          show Function.minimalPeriod σ (y (rep P A)) ∣ j x
          rw [← sameCycle_minimalPeriod (hrepA A x hx)]
          exact pow_eq_self_iff_dvd.1 (hfix x)
        · rw [Ne, Finset.gcd_eq_zero_iff]
          intro h; exact (hj _).ne' (h _ (rep_mem P A))
    · intro P _ hP
      apply sum_eq_zero
      intro e _
      rw [if_neg]
      intro ht; apply hP
      apply finpartition_eq_of
      intro x x'
      rw [← blk_eq_blk, ht.1, mem_cyclePart]
    · intro h; exact absurd (mem_univ _) h
  · apply sum_eq_zero
    intro P _
    apply sum_eq_zero
    intro e he
    rw [if_neg]
    intro ht; apply hfix; intro x
    rw [pow_eq_self_iff_dvd, ht.2]
    have := Fintype.mem_piFinset.1 he (blk P x)
    exact (Nat.dvd_of_mem_divisors this).trans (Finset.gcd_dvd (P.mem_part (mem_univ x)))

theorem prod_rep_ite (P : Finpartition (univ : Finset S)) (e : P.parts → ℕ) :
    (∏ x, if rep P (blk P x) = x then 1 else e (blk P x)) =
      ∏ A : P.parts, e A ^ (A.1.card - 1) := by
  rw [← prod_fiberwise univ (blk P)]
  refine prod_congr rfl fun A _ => ?_
  have hfil : (univ.filter fun x => blk P x = A) = A.1 := by
    ext x; simp [blk_eq_iff_mem]
  rw [hfil, prod_congr rfl (g := fun x => if rep P A = x then 1 else e A)
    (fun x hx => by rw [(blk_eq_iff_mem P x A).2 hx])]
  rw [← mul_prod_erase _ _ (rep_mem P A), if_pos rfl, one_mul,
    prod_congr rfl (g := fun _ => e A) (fun x hx => if_neg (ne_of_mem_erase hx).symm),
    prod_const, card_erase_of_mem (rep_mem P A)]

theorem sum_e_le (j : S → ℕ) (hj : ∀ x, 0 < j x) (P : Finpartition (univ : Finset S))
    (e : P.parts → ℕ) (he : e ∈ Fintype.piFinset fun A : P.parts => (A.1.gcd j).divisors) :
    ∑ A, e A ≤ ∑ x, j x := by
  calc ∑ A, e A ≤ ∑ A : P.parts, j (rep P A) :=
        sum_le_sum fun A _ => Nat.le_of_dvd (hj _)
          ((Nat.dvd_of_mem_divisors (Fintype.mem_piFinset.1 he A)).trans
            (Finset.gcd_dvd (rep_mem P A)))
    _ = ∑ x ∈ univ.image (rep P), j x :=
        (sum_image fun A _ B _ h => by simpa [blk_rep] using congrArg (blk P) h).symm
    _ ≤ ∑ x, j x := sum_le_sum_of_subset (subset_univ _)

theorem sum_card_fix (j : S → ℕ) (hj : ∀ x, 0 < j x) (hN : ∑ x, j x ≤ N) :
    ∑ σ : Perm (Fin N), (univ.filter fun y : S → Fin N => ∀ x, (σ ^ j x) (y x) = y x).card =
      N.factorial * ∑ P : Finpartition (univ : Finset S),
        ∏ A ∈ P.parts, ∑ e ∈ (A.gcd j).divisors, e ^ (A.card - 1) := by
  calc _ = ∑ σ : Perm (Fin N), ∑ y : S → Fin N, ∑ P : Finpartition (univ : Finset S),
          ∑ e ∈ Fintype.piFinset (fun A : P.parts => (A.1.gcd j).divisors),
            (if IsType (blk P) e σ y then 1 else 0) := by
        refine sum_congr rfl fun σ _ => ?_
        rw [card_eq_sum_ones, sum_filter]
        refine sum_congr rfl fun y _ => ?_
        rw [sum_isType j hj]
    _ = ∑ σ : Perm (Fin N), ∑ P : Finpartition (univ : Finset S),
          ∑ e ∈ Fintype.piFinset (fun A : P.parts => (A.1.gcd j).divisors),
            ∑ y : S → Fin N, (if IsType (blk P) e σ y then 1 else 0) := by
        refine sum_congr rfl fun σ _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun P _ => ?_
        rw [sum_comm]
    _ = ∑ P : Finpartition (univ : Finset S),
          ∑ e ∈ Fintype.piFinset (fun A : P.parts => (A.1.gcd j).divisors),
            ∑ σ : Perm (Fin N), ∑ y : S → Fin N, (if IsType (blk P) e σ y then 1 else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun P _ => ?_
        rw [sum_comm]
    _ = ∑ P : Finpartition (univ : Finset S),
          ∑ e ∈ Fintype.piFinset (fun A : P.parts => (A.1.gcd j).divisors),
            N.factorial * ∏ A : P.parts, e A ^ (A.1.card - 1) := by
        refine sum_congr rfl fun P _ => sum_congr rfl fun e he => ?_
        rw [← prod_rep_ite, ← sum_card_type (blk P) (rep P) (blk_rep P)
          (fun A => Nat.pos_of_mem_divisors (Fintype.mem_piFinset.1 he A))
          ((sum_e_le j hj P e he).trans hN)]
        refine sum_congr rfl fun σ _ => ?_
        rw [card_eq_sum_ones, sum_filter]
    _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun P _ => ?_
        rw [← mul_sum, ← prod_coe_sort, prod_univ_sum]

end Outer

/-- `∏ₓ ξ_{j x}(σ)` counts the `y : S → [N]` with `σ^{j x} (y x) = y x` for all `x`. -/
theorem prod_xi_eq_card {S : Type*} [Fintype S] [DecidableEq S] {N : ℕ} (j : S → ℕ)
    (σ : Perm (Fin N)) :
    ∏ x, StrongConv.xi (j x) σ =
      (univ.filter fun y : S → Fin N => ∀ x, (σ ^ j x) (y x) = y x).card := by
  have : (univ.filter fun y : S → Fin N => ∀ x, (σ ^ j x) (y x) = y x) =
      Fintype.piFinset fun x => univ.filter fun z => (σ ^ j x) z = z := by
    ext y; simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset]
  rfl

end HananyPuder.W2HP

open HananyPuder.W2HP

theorem HananyPuder.W2HP.rem73_dev {K : ℕ} (a : Fin K → ℕ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      StrongConv.uniformExp (fun σ : Equiv.Perm (Fin N) =>
          ∏ t : Fin K, ((StrongConv.xi ((t : ℕ) + 1) σ : ℕ) : ℝ) ^ a t) =
        ∑ P : Finpartition (Finset.univ : Finset (Σ t : Fin K, Fin (a t))),
          ∏ A ∈ P.parts, ∑ e ∈ (A.gcd fun x => (x.1 : ℕ) + 1).divisors, (e : ℝ) ^ (A.card - 1) := by
  refine ⟨∑ x : (Σ t : Fin K, Fin (a t)), ((x.1 : ℕ) + 1), fun N hN => ?_⟩
  have h1 : ∀ σ : Perm (Fin N), ∏ t : Fin K, ((StrongConv.xi ((t : ℕ) + 1) σ : ℕ) : ℝ) ^ a t =
      ((∏ x : (Σ t : Fin K, Fin (a t)), StrongConv.xi ((x.1 : ℕ) + 1) σ : ℕ) : ℝ) := by
    intro σ
    push_cast
    rw [Fintype.prod_sigma]
    simp [prod_const]
  unfold StrongConv.uniformExp
  simp_rw [h1, prod_xi_eq_card]
  rw [← Nat.cast_sum, sum_card_fix (fun x : (Σ t : Fin K, Fin (a t)) => (x.1 : ℕ) + 1)
    (fun _ => Nat.succ_pos _) hN, Fintype.card_perm, Fintype.card_fin]
  push_cast
  field_simp

theorem solution {K : ℕ} (a : Fin K → ℕ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      StrongConv.uniformExp (fun σ : Equiv.Perm (Fin N) =>
          ∏ t : Fin K, ((StrongConv.xi ((t : ℕ) + 1) σ : ℕ) : ℝ) ^ a t) =
        ∑ P : Finpartition (Finset.univ : Finset (Σ t : Fin K, Fin (a t))),
          ∏ A ∈ P.parts, ∑ e ∈ (A.gcd fun x => (x.1 : ℕ) + 1).divisors, (e : ℝ) ^ (A.card - 1) :=
  HananyPuder.W2HP.rem73_dev a
