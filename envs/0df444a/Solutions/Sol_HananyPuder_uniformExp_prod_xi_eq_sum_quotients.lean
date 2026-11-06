-- Prove2me | solution 1 for HananyPuder.uniformExp_prod_xi_eq_sum_quotients
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T23:25:01.507868+00:00
-- url     : https://prove2.me/submissions/d6c3a370-61ee-4c8d-9e81-9765e461b801

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4

open Equiv Finset

namespace HananyPuder.W2HP.HP102

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

section Graph

open Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] {d N : ℕ}
  (lab : E → Fin d) (tl hd : E → V)

/-- The block of `x`, as an element of the set of parts. -/
def blk (P : Finpartition (univ : Finset V)) (x : V) : P.parts :=
  ⟨P.part x, P.part_mem.2 (mem_univ x)⟩

/-- A chosen representative of a part. -/
noncomputable def rep (P : Finpartition (univ : Finset V)) (A : P.parts) : V :=
  (P.nonempty_of_mem_parts A.2).choose

theorem rep_mem (P : Finpartition (univ : Finset V)) (A : P.parts) : rep P A ∈ A.1 :=
  (P.nonempty_of_mem_parts A.2).choose_spec

theorem blk_rep (P : Finpartition (univ : Finset V)) (A : P.parts) : blk P (rep P A) = A :=
  Subtype.ext ((P.part_eq_iff_mem A.2).2 (rep_mem P A))

theorem blk_eq_iff (P : Finpartition (univ : Finset V)) (x x' : V) :
    blk P x = blk P x' ↔ P.part x = P.part x' := Subtype.ext_iff

theorem part_eq_part_iff (P : Finpartition (univ : Finset V)) (x x' : V) :
    P.part x = P.part x' ↔ x' ∈ P.part x := by
  rw [eq_comm, P.part_eq_iff_mem (P.part_mem.2 (mem_univ x))]

theorem finpartition_eq_of (P Q : Finpartition (univ : Finset V))
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

/-- `f` is a homomorphism: every edge `e` is mapped by `σ_{lab e}` from `f (tl e)` to
`f (hd e)`. -/
def Hom (σ : Fin d → Perm (Fin N)) (f : V → Fin N) : Prop :=
  ∀ e, σ (lab e) (f (tl e)) = f (hd e)

/-- Fold-freeness for an abstract labelled graph. -/
def FF (P : Finpartition (univ : Finset V)) : Prop :=
  ∀ e e', lab e = lab e' → (P.part (tl e) = P.part (tl e') ↔ P.part (hd e) = P.part (hd e'))

/-- The number of quotient edges of label `j`. -/
def QE (P : Finpartition (univ : Finset V)) (j : Fin d) : ℕ :=
  ((univ.filter fun e => lab e = j).image fun e => (P.part (tl e), P.part (hd e))).card

/-- The kernel of `f` is `P`. -/
def KerIs (P : Finpartition (univ : Finset V)) (f : V → Fin N) : Prop :=
  ∀ x x', f x = f x' ↔ P.part x = P.part x'

theorem sum_kerIs (f : V → Fin N) :
    ∑ P : Finpartition (univ : Finset V), (if KerIs P f then 1 else 0) = 1 := by
  let P₀ : Finpartition (univ : Finset V) := Finpartition.ofSetoid (Setoid.ker f)
  have h0 : KerIs P₀ f := by
    intro x x'
    rw [part_eq_part_iff, Finpartition.mem_part_ofSetoid_iff_rel]
    rfl
  rw [sum_eq_single P₀]
  · rw [if_pos h0]
  · intro P _ hP
    rw [if_neg]
    intro hk; apply hP
    apply finpartition_eq_of
    intro x x'
    rw [← part_eq_part_iff, ← part_eq_part_iff, ← hk, ← h0]
  · intro h; exact absurd (mem_univ _) h

theorem ff_of_hom {σ : Fin d → Perm (Fin N)} {f : V → Fin N} {P : Finpartition (univ : Finset V)}
    (hf : Hom lab tl hd σ f) (hk : KerIs P f) : FF lab tl hd P := by
  intro e e' hl
  rw [← hk, ← hk, ← hf e, ← hf e', hl]
  exact (σ (lab e')).injective.eq_iff.symm

/-- Compatibility of an injection of the blocks with `σ`. -/
def Compat (P : Finpartition (univ : Finset V)) (σ : Fin d → Perm (Fin N)) (g : P.parts ↪ Fin N) :
    Prop :=
  ∀ e, σ (lab e) (g (blk P (tl e))) = g (blk P (hd e))

theorem card_hom_kerIs (P : Finpartition (univ : Finset V)) (σ : Fin d → Perm (Fin N)) :
    (univ.filter fun f : V → Fin N => Hom lab tl hd σ f ∧ KerIs P f).card =
      (univ.filter fun g : P.parts ↪ Fin N => Compat lab tl hd P σ g).card := by
  symm
  refine card_bij' (fun g _ => fun x => g (blk P x))
    (fun f hf => ⟨fun A => f (rep P A), ?_⟩) ?_ ?_ ?_ ?_
  · intro A B h
    have hk := (mem_filter.1 hf).2.2
    rw [← blk_rep P A, ← blk_rep P B, blk_eq_iff]
    exact (hk _ _).1 h
  · intro g hg
    refine mem_filter.2 ⟨mem_univ _, (mem_filter.1 hg).2, fun x x' => ?_⟩
    rw [g.injective.eq_iff, blk_eq_iff]
  · intro f hf
    have hk := (mem_filter.1 hf).2.2
    refine mem_filter.2 ⟨mem_univ _, fun e => ?_⟩
    show σ (lab e) (f (rep P (blk P (tl e)))) = f (rep P (blk P (hd e)))
    have h1 : ∀ x, f (rep P (blk P x)) = f x := fun x =>
      (hk _ _).2 ((blk_eq_iff P _ _).1 (blk_rep P (blk P x)))
    rw [h1, h1]
    exact (mem_filter.1 hf).2.1 e
  · intro g _
    ext A
    simp [blk_rep]
  · intro f hf
    have hk := (mem_filter.1 hf).2.2
    funext x
    exact (hk _ _).2 ((blk_eq_iff P _ _).1 (blk_rep P (blk P x)))

/-- The quotient edges of label `j`, as pairs of blocks. -/
def QD (P : Finpartition (univ : Finset V)) (j : Fin d) : Finset (P.parts × P.parts) :=
  (univ.filter fun e => lab e = j).image fun e => (blk P (tl e), blk P (hd e))

theorem card_QD (P : Finpartition (univ : Finset V)) (j : Fin d) :
    (QD lab tl hd P j).card = QE lab tl hd P j := by
  unfold QD QE
  have hinj : Function.Injective (Prod.map (Subtype.val : P.parts → Finset V)
      (Subtype.val : P.parts → Finset V)) := fun a b h =>
    Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  rw [← card_image_of_injective _ hinj, image_image]
  rfl

theorem QD_fst_iff {P : Finpartition (univ : Finset V)} (hP : FF lab tl hd P) {j : Fin d}
    {x y : P.parts × P.parts} (hx : x ∈ QD lab tl hd P j) (hy : y ∈ QD lab tl hd P j) :
    x.1 = y.1 ↔ x.2 = y.2 := by
  obtain ⟨e, he, rfl⟩ := mem_image.1 hx
  obtain ⟨e', he', rfl⟩ := mem_image.1 hy
  simp only [blk_eq_iff]
  exact hP e e' ((mem_filter.1 he).2.trans (mem_filter.1 he').2.symm)

theorem card_perm_compat_j {P : Finpartition (univ : Finset V)} (hP : FF lab tl hd P)
    (g : P.parts ↪ Fin N) (j : Fin d) :
    (univ.filter fun τ : Perm (Fin N) =>
        ∀ e, lab e = j → τ (g (blk P (tl e))) = g (blk P (hd e))).card =
      (N - QE lab tl hd P j).factorial := by
  let D := QD lab tl hd P j
  let ι : D ↪ Fin N := ⟨fun x => g x.1.1, by
    intro x y h
    have h1 : x.1.1 = y.1.1 := g.injective h
    exact Subtype.ext (Prod.ext h1 ((QD_fst_iff lab tl hd hP x.2 y.2).1 h1))⟩
  let κ : D ↪ Fin N := ⟨fun x => g x.1.2, by
    intro x y h
    have h1 : x.1.2 = y.1.2 := g.injective h
    exact Subtype.ext (Prod.ext ((QD_fst_iff lab tl hd hP x.2 y.2).2 h1) h1)⟩
  have := card_perm_extend ι κ
  rw [Fintype.card_subtype, Fintype.card_fin, Fintype.card_coe, card_QD] at this
  rw [← this]
  congr 1
  ext τ
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro h ⟨x, hx⟩
    obtain ⟨e, he, rfl⟩ := mem_image.1 hx
    exact h e (mem_filter.1 he).2
  · intro h e he
    exact h ⟨_, mem_image.2 ⟨e, mem_filter.2 ⟨mem_univ _, he⟩, rfl⟩⟩

theorem card_compat {P : Finpartition (univ : Finset V)} (hP : FF lab tl hd P)
    (g : P.parts ↪ Fin N) :
    (univ.filter fun σ : Fin d → Perm (Fin N) => Compat lab tl hd P σ g).card =
      ∏ j, (N - QE lab tl hd P j).factorial := by
  have : (univ.filter fun σ : Fin d → Perm (Fin N) => Compat lab tl hd P σ g) =
      Fintype.piFinset fun j => univ.filter fun τ : Perm (Fin N) =>
        ∀ e, lab e = j → τ (g (blk P (tl e))) = g (blk P (hd e)) := by
    ext σ
    rw [mem_filter, Fintype.mem_piFinset]
    constructor
    · intro h j; exact mem_filter.2 ⟨mem_univ _, fun e he => by subst he; exact h.2 e⟩
    · intro h; exact ⟨mem_univ _, fun e => (mem_filter.1 (h _)).2 e rfl⟩
  rw [this, Fintype.card_piFinset]
  exact prod_congr rfl fun j _ => card_perm_compat_j lab tl hd hP g j

theorem sum_card_hom :
    ∑ σ : Fin d → Perm (Fin N), (univ.filter (Hom lab tl hd σ)).card =
      ∑ P ∈ (univ : Finset (Finpartition (univ : Finset V))).filter (FF lab tl hd),
        N.descFactorial P.parts.card * ∏ j, (N - QE lab tl hd P j).factorial := by
  calc _ = ∑ σ : Fin d → Perm (Fin N), ∑ P : Finpartition (univ : Finset V),
        (univ.filter fun f : V → Fin N => Hom lab tl hd σ f ∧ KerIs P f).card := by
        refine sum_congr rfl fun σ _ => ?_
        simp_rw [card_eq_sum_ones, sum_filter]
        rw [sum_comm]
        refine sum_congr rfl fun f _ => ?_
        by_cases h : Hom lab tl hd σ f
        · rw [if_pos h]; simp only [h, true_and]; exact (sum_kerIs f).symm
        · rw [if_neg h]; symm; apply sum_eq_zero; intro P _; rw [if_neg (fun hh => h hh.1)]
    _ = ∑ P : Finpartition (univ : Finset V), ∑ σ : Fin d → Perm (Fin N),
        (univ.filter fun f : V → Fin N => Hom lab tl hd σ f ∧ KerIs P f).card := sum_comm
    _ = ∑ P ∈ (univ : Finset (Finpartition (univ : Finset V))).filter (FF lab tl hd),
        ∑ σ : Fin d → Perm (Fin N),
        (univ.filter fun f : V → Fin N => Hom lab tl hd σ f ∧ KerIs P f).card := by
        rw [sum_filter]
        refine sum_congr rfl fun P _ => ?_
        split_ifs with hP
        · rfl
        · apply sum_eq_zero; intro σ _
          rw [card_eq_zero, filter_eq_empty_iff]
          rintro f - ⟨hf, hk⟩
          exact hP (ff_of_hom lab tl hd hf hk)
    _ = _ := by
        refine sum_congr rfl fun P hP => ?_
        have hP := (mem_filter.1 hP).2
        simp_rw [card_hom_kerIs, card_eq_sum_ones, sum_filter]
        rw [sum_comm]
        simp_rw [← sum_filter, ← card_eq_sum_ones, card_compat lab tl hd hP, sum_const, card_univ,
          Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe, smul_eq_mul]

end Graph

theorem prod_Ico_one_eq_range (N k : ℕ) :
    ∏ i ∈ Ico 1 k, (1 - (i : ℝ) / N) = ∏ i ∈ range k, (1 - (i : ℝ) / N) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [range_eq_Ico, prod_eq_prod_Ico_succ_bot hk]
    simp

theorem descFactorial_eq_real (N k : ℕ) (hN : 0 < N) :
    (N.descFactorial k : ℝ) = (N : ℝ) ^ k * ∏ i ∈ Ico 1 k, (1 - (i : ℝ) / N) := by
  rw [prod_Ico_one_eq_range]
  have hN' : (N : ℝ) ≠ 0 := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, prod_range_succ]
    by_cases hk : k ≤ N
    · rw [Nat.cast_mul, Nat.cast_sub hk, ih]
      field_simp
      ring
    · have h0 : N.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
      rw [h0, Nat.cast_zero, eq_comm, mul_eq_zero] at ih
      rcases ih with ih | ih
      · exact absurd (pow_eq_zero_iff'.1 ih).1 hN'
      · rw [h0, ih]; simp

theorem term_eq {d : ℕ} (N v : ℕ) (e : Fin d → ℕ) (he : ∀ j, e j ≤ N) :
    ((N.descFactorial v * ∏ j, (N - e j).factorial : ℕ) : ℝ) / ((N.factorial : ℝ) ^ d) =
      ((1 : ℝ) / N) ^ (((∑ j, e j : ℕ) : ℤ) - v) *
        (∏ i ∈ Ico 1 v, (1 - (i : ℝ) / N)) / ∏ j, ∏ i ∈ Ico 1 (e j), (1 - (i : ℝ) / N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have he0 : ∀ j, e j = 0 := fun j => Nat.le_zero.1 (he j)
    simp only [he0, Nat.sub_zero, Nat.factorial_zero, prod_const_one, mul_one, sum_const_zero,
      Nat.cast_one, one_pow, div_one, Nat.cast_zero, div_zero, sub_zero, prod_const_one]
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · simp
    · obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
      rw [Nat.zero_descFactorial_succ, zero_zpow]
      · simp
      · omega
  · have hN' : (N : ℝ) ≠ 0 := by positivity
    have hQ : ∀ j, ∏ i ∈ Ico 1 (e j), (1 - (i : ℝ) / N) ≠ 0 := by
      intro j h
      have := descFactorial_eq_real N (e j) hN
      rw [h, mul_zero, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt] at this
      exact absurd (he j) (not_le.2 this)
    have hfac : ((N.factorial : ℝ)) ^ d =
        ∏ j, ((N - e j).factorial : ℝ) * (N.descFactorial (e j) : ℝ) := by
      rw [← Fin.prod_const d (N.factorial : ℝ)]
      refine prod_congr rfl fun j _ => ?_
      rw [← Nat.cast_mul, Nat.factorial_mul_descFactorial (he j)]
    have hfpos : ∀ j, ((N - e j).factorial : ℝ) ≠ 0 := fun j => by positivity
    rw [hfac, prod_mul_distrib, Nat.cast_mul, Nat.cast_prod]
    simp_rw [descFactorial_eq_real N _ hN]
    rw [prod_mul_distrib, prod_pow_eq_pow_sum, zpow_sub₀ (by simpa using hN'), zpow_natCast,
      zpow_natCast, one_div_pow, one_div_pow]
    have h1 : ∏ j, ((N - e j).factorial : ℝ) ≠ 0 := prod_ne_zero_iff.2 fun j _ => hfpos j
    have h2 : ∏ j, ∏ i ∈ Ico 1 (e j), (1 - (i : ℝ) / N) ≠ 0 := prod_ne_zero_iff.2 fun j _ => hQ j
    field_simp

section Cycle

open Classical

variable {d N : ℕ}

/-- The permutation by which a letter moves a walk one step forward. -/
def rho (σ : Fin d → Perm (Fin N)) (x : Fin d × Bool) : Perm (Fin N) :=
  if x.2 then σ x.1 else (σ x.1)⁻¹

/-- The walk product of the first `p` letters (first letter applied first). -/
def pre (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (p : ℕ) : Perm (Fin N) :=
  ((K.take p).map (rho σ)).reverse.prod

theorem pre_zero (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) : pre σ K 0 = 1 := by
  simp [pre]

theorem pre_succ (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (p : ℕ)
    (hp : p < K.length) : pre σ K (p + 1) = rho σ K[p] * pre σ K p := by
  rw [pre, pre, List.take_add_one, List.getElem?_eq_getElem hp]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one]

/-- The cyclic successor on `Fin n`. -/
def cnxt {n : ℕ} (p : Fin n) : Fin n :=
  ⟨((p : ℕ) + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt p.2)⟩

/-- The edge condition at position `p` of a cycle labelled by `K`. -/
def Step (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (h : Fin K.length → Fin N)
    (p : Fin K.length) : Prop :=
  σ (K[p]).1 (h (if (K[p]).2 then p else cnxt p)) = h (if (K[p]).2 then cnxt p else p)

theorem step_iff (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (h : Fin K.length → Fin N)
    (p : Fin K.length) : Step σ K h p ↔ h (cnxt p) = rho σ K[p] (h p) := by
  unfold Step rho
  by_cases hb : (K[p]).2 = true
  · rw [if_pos hb, if_pos hb, if_pos hb, eq_comm]
  · rw [if_neg hb, if_neg hb, if_neg hb, Perm.eq_inv_iff_eq]

theorem card_cycle (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) (hn : 0 < K.length) :
    (univ.filter fun h : Fin K.length → Fin N => ∀ p, Step σ K h p).card =
      (univ.filter fun y : Fin N => pre σ K K.length y = y).card := by
  have hfw : ∀ h : Fin K.length → Fin N, (∀ p, Step σ K h p) →
      ∀ k (hk : k < K.length), h ⟨k, hk⟩ = pre σ K k (h ⟨0, hn⟩) := by
    intro h hs k
    induction k with
    | zero => intro hk; simp [pre_zero]
    | succ k ih =>
      intro hk
      have h1 := (step_iff σ K h ⟨k, by omega⟩).1 (hs _)
      have h2 : cnxt (⟨k, by omega⟩ : Fin K.length) = ⟨k + 1, hk⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hk)
      rw [h2] at h1
      rw [h1, ih (by omega), pre_succ σ K k (by omega), Perm.mul_apply]
      rfl
  obtain ⟨m, hm⟩ : ∃ m, K.length = m + 1 := ⟨K.length - 1, by omega⟩
  have hclose : ∀ h : Fin K.length → Fin N, (∀ p, Step σ K h p) →
      pre σ K K.length (h ⟨0, hn⟩) = h ⟨0, hn⟩ := by
    intro h hs
    have h1 := (step_iff σ K h ⟨m, by omega⟩).1 (hs _)
    have h2 : cnxt (⟨m, by omega⟩ : Fin K.length) = ⟨0, hn⟩ :=
      Fin.ext (by simp only [cnxt]; rw [← hm, Nat.mod_self])
    rw [h2] at h1
    have h3 := hfw h hs m (by omega)
    rw [congrArg (pre σ K) hm, pre_succ σ K m (by omega), Perm.mul_apply, ← h3, h1]
    rfl
  refine card_bij' (fun h _ => h ⟨0, hn⟩) (fun y _ => fun p => pre σ K p y) ?_ ?_ ?_ ?_
  · intro h hh
    exact mem_filter.2 ⟨mem_univ _, hclose h (mem_filter.1 hh).2⟩
  · intro y hy
    have hy := (mem_filter.1 hy).2
    refine mem_filter.2 ⟨mem_univ _, fun p => (step_iff σ K _ p).2 ?_⟩
    by_cases hp : (p : ℕ) + 1 < K.length
    · have h2 : cnxt p = ⟨(p : ℕ) + 1, hp⟩ := Fin.ext (Nat.mod_eq_of_lt hp)
      rw [h2]
      show pre σ K ((p : ℕ) + 1) y = _
      rw [pre_succ σ K p p.2, Perm.mul_apply]
      rfl
    · have hp' : (p : ℕ) + 1 = K.length := by omega
      have h2 : cnxt p = ⟨0, hn⟩ := Fin.ext (by simp only [cnxt]; rw [hp', Nat.mod_self])
      rw [h2]
      show pre σ K 0 y = _
      rw [pre_zero, Perm.one_apply]
      conv_lhs => rw [← hy, ← hp']
      rw [pre_succ σ K p p.2, Perm.mul_apply]
      rfl
  · intro h hh
    funext p
    exact (hfw h (mem_filter.1 hh).2 p p.2).symm
  · intro y _
    simp [pre_zero]

end Cycle

section Free

open Classical

variable {d N : ℕ}

theorem lift_inv_mk (σ : Fin d → Perm (Fin N)) (K : List (Fin d × Bool)) :
    FreeGroup.lift σ⁻¹ (FreeGroup.mk K) = (pre σ K K.length)⁻¹ := by
  rw [FreeGroup.lift_mk, pre, List.take_length, List.prod_inv_reverse, List.map_reverse,
    List.reverse_reverse, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  rcases x with ⟨i, b⟩
  cases b <;> simp [rho]

theorem card_fix_inv (W : Perm (Fin N)) :
    (univ.filter fun y : Fin N => W⁻¹ y = y).card = (univ.filter fun y : Fin N => W y = y).card := by
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and]
  rw [Perm.inv_eq_iff_eq, eq_comm]

theorem card_fix_conj (G W : Perm (Fin N)) :
    (univ.filter fun y : Fin N => (G * W * G⁻¹) y = y).card =
      (univ.filter fun y : Fin N => W y = y).card := by
  refine card_bij' (fun y _ => G⁻¹ y) (fun y _ => G y) ?_ ?_ ?_ ?_
  · intro y hy
    have hy := (mem_filter.1 hy).2
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rw [Perm.mul_apply, Perm.mul_apply] at hy
    rw [Perm.eq_inv_iff_eq, hy]
  · intro y hy
    have hy := (mem_filter.1 hy).2
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    simp [Perm.mul_apply, hy]
  · intro y _; simp
  · intro y _; simp

theorem mk_cycleWord (L : List (Fin d × Bool)) (j : ℕ) :
    FreeGroup.mk (cycleWord L j) = FreeGroup.mk L ^ j := by
  induction j with
  | zero => simp [cycleWord]; rfl
  | succ j ih =>
    rw [cycleWord, List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, pow_succ']
    rw [← ih]
    rfl

theorem conj_reduceCyclically (w : FreeGroup (Fin d)) :
    ∃ G : FreeGroup (Fin d),
      w = G * FreeGroup.mk (FreeGroup.reduceCyclically w.toWord) * G⁻¹ := by
  refine ⟨FreeGroup.mk (FreeGroup.reduceCyclically.conjugator w.toWord), ?_⟩
  rw [FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk,
    FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically, FreeGroup.mk_toWord]

theorem reduceCyclically_ne_nil {w : FreeGroup (Fin d)} (hw : w ≠ 1) :
    FreeGroup.reduceCyclically w.toWord ≠ [] := by
  intro h
  obtain ⟨G, hG⟩ := conj_reduceCyclically w
  rw [h] at hG
  apply hw
  rw [hG]
  show G * 1 * G⁻¹ = 1
  group

theorem xi_eq_card_fix (σ : Fin d → Perm (Fin N)) (w : FreeGroup (Fin d)) (j : ℕ) :
    StrongConv.xi j (FreeGroup.lift σ⁻¹ w) =
      (univ.filter fun y : Fin N =>
        pre σ (cycleWord (FreeGroup.reduceCyclically w.toWord) j)
          (cycleWord (FreeGroup.reduceCyclically w.toWord) j).length y = y).card := by
  obtain ⟨G, hG⟩ := conj_reduceCyclically w
  rw [← card_fix_inv, ← lift_inv_mk, mk_cycleWord, map_pow, StrongConv.xi]
  conv_lhs => rw [hG, map_mul, map_mul, map_inv (FreeGroup.lift (σ⁻¹)) G, conj_pow]
  convert card_fix_conj _ _ using 2

theorem cycleWord_length_pos {L : List (Fin d × Bool)} (hL : L ≠ []) (j : ℕ) :
    0 < (cycleWord L (j + 1)).length := by
  rw [cycleWord, List.replicate_succ, List.flatten_cons, List.length_append]
  have := List.length_pos_iff.2 hL
  omega

variable {r : ℕ} {α : Fin r → ℕ}

theorem hom_iff (σ : Fin d → Perm (Fin N)) (L : List (Fin d × Bool)) (f : CycleVert L α → Fin N)
    (c : Σ i : Fin r, Fin (α i)) (p : Fin (cycleWord L ((c.1 : ℕ) + 1)).length) :
    σ (edgeLetter (⟨c, p⟩ : CycleVert L α)).1 (f (edgeTail ⟨c, p⟩)) = f (edgeHead ⟨c, p⟩) ↔
      Step σ (cycleWord L ((c.1 : ℕ) + 1)) (fun q => f ⟨c, q⟩) p := by
  unfold Step edgeTail edgeHead
  by_cases hb : (edgeLetter (⟨c, p⟩ : CycleVert L α)).2 = true
  · have hb' : ((cycleWord L ((c.1 : ℕ) + 1))[p]).2 = true := hb
    rw [if_pos hb, if_pos hb, if_pos hb', if_pos hb']
    rfl
  · have hb' : ¬ ((cycleWord L ((c.1 : ℕ) + 1))[p]).2 = true := hb
    rw [if_neg hb, if_neg hb, if_neg hb', if_neg hb']
    rfl

theorem card_hom_eq_prod (σ : Fin d → Perm (Fin N)) (L : List (Fin d × Bool)) :
    (univ.filter (Hom (fun e : CycleVert L α => (edgeLetter e).1) edgeTail edgeHead σ)).card =
      ∏ c : (Σ i : Fin r, Fin (α i)),
        (univ.filter fun h : Fin (cycleWord L ((c.1 : ℕ) + 1)).length → Fin N =>
          ∀ p, Step σ (cycleWord L ((c.1 : ℕ) + 1)) h p).card := by
  rw [← Fintype.card_piFinset]
  refine card_equiv (Equiv.piCurry fun _ _ => Fin N) fun f => ?_
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · intro hf c p
    exact (hom_iff σ L f c p).1 (hf ⟨c, p⟩)
  · rintro hf ⟨c, p⟩
    exact (hom_iff σ L f c p).2 (hf c p)

theorem prod_xi_eq_card_hom (σ : Fin d → Perm (Fin N)) (w : FreeGroup (Fin d)) (hw : w ≠ 1) :
    ∏ i : Fin r, StrongConv.xi ((i : ℕ) + 1) (FreeGroup.lift σ⁻¹ w) ^ α i =
      (univ.filter (Hom (fun e : CycleVert (FreeGroup.reduceCyclically w.toWord) α =>
        (edgeLetter e).1) edgeTail edgeHead σ)).card := by
  rw [card_hom_eq_prod, Fintype.prod_sigma]
  refine prod_congr rfl fun i _ => ?_
  dsimp only
  rw [prod_eq_pow_card (b := (univ.filter fun h : Fin (cycleWord (FreeGroup.reduceCyclically
    w.toWord) ((i : ℕ) + 1)).length → Fin N => ∀ p, Step σ (cycleWord
      (FreeGroup.reduceCyclically w.toWord) ((i : ℕ) + 1)) h p).card) (fun y _ => by congr),
    card_univ, Fintype.card_fin]
  congr 1
  rw [card_cycle σ _ (cycleWord_length_pos (reduceCyclically_ne_nil hw) _), xi_eq_card_fix]

end Free

end HananyPuder.W2HP.HP102

open StrongConv HananyPuder HananyPuder.W2HP.HP102

theorem HananyPuder.W2HP.hp102_dev {d r : ℕ} (w : FreeGroup (Fin d)) (hw : w ≠ 1)
    (α : Fin r → ℕ) (hα : 0 < ∑ i, α i) (N : ℕ)
    (hN : ∀ P : Finpartition (Finset.univ :
        Finset (CycleVert (FreeGroup.reduceCyclically w.toWord) α)),
      IsFoldFree P → ∀ j, quotEdge P j ≤ N) :
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ∏ i : Fin r, ((xi ((i : ℕ) + 1) (FreeGroup.lift σ w) : ℕ) : ℝ) ^ α i) =
      ∑ P ∈ (Finset.univ : Finset (Finpartition (Finset.univ :
          Finset (CycleVert (FreeGroup.reduceCyclically w.toWord) α)))).filter IsFoldFree,
        ((1 : ℝ) / N) ^ (((∑ j, quotEdge P j : ℕ) : ℤ) - quotVert P) *
          (∏ i ∈ Finset.Ico 1 (quotVert P), (1 - (i : ℝ) / N)) /
          ∏ j : Fin d, ∏ i ∈ Finset.Ico 1 (quotEdge P j), (1 - (i : ℝ) / N) := by
  classical
  unfold uniformExp
  rw [Fintype.card_pi, Fintype.card_perm, Fintype.card_fin, prod_const, card_univ,
    Fintype.card_fin, ← Equiv.sum_comp (Equiv.inv (Fin d → Equiv.Perm (Fin N)))]
  have key : ∀ σ : Fin d → Equiv.Perm (Fin N),
      ∏ i : Fin r, ((xi ((i : ℕ) + 1) (FreeGroup.lift (Equiv.inv _ σ) w) : ℕ) : ℝ) ^ α i =
        (((univ.filter (Hom (fun e : CycleVert (FreeGroup.reduceCyclically w.toWord) α =>
          (edgeLetter e).1) edgeTail edgeHead σ)).card : ℕ) : ℝ) := by
    intro σ
    rw [← prod_xi_eq_card_hom σ w hw]
    push_cast
    rfl
  simp_rw [key]
  rw [← Nat.cast_sum, sum_card_hom, Nat.cast_sum, sum_div]
  refine sum_congr (filter_congr fun P _ => Iff.rfl) fun P hP => ?_
  have hP' : IsFoldFree P := (mem_filter.1 hP).2
  rw [Nat.cast_pow]
  exact term_eq N P.parts.card (fun j => QE _ _ _ P j) (hN P hP')

theorem solution {d r : ℕ} (w : FreeGroup (Fin d)) (hw : w ≠ 1)
    (α : Fin r → ℕ) (hα : 0 < ∑ i, α i) (N : ℕ)
    (hN : ∀ P : Finpartition (Finset.univ :
        Finset (HananyPuder.CycleVert (FreeGroup.reduceCyclically w.toWord) α)),
      HananyPuder.IsFoldFree P → ∀ j, HananyPuder.quotEdge P j ≤ N) :
    StrongConv.uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ∏ i : Fin r, ((StrongConv.xi ((i : ℕ) + 1) (FreeGroup.lift σ w) : ℕ) : ℝ) ^ α i) =
      ∑ P ∈ (Finset.univ : Finset (Finpartition (Finset.univ :
          Finset (HananyPuder.CycleVert (FreeGroup.reduceCyclically w.toWord) α)))).filter
            HananyPuder.IsFoldFree,
        ((1 : ℝ) / N) ^ (((∑ j, HananyPuder.quotEdge P j : ℕ) : ℤ) - HananyPuder.quotVert P) *
          (∏ i ∈ Finset.Ico 1 (HananyPuder.quotVert P), (1 - (i : ℝ) / N)) /
          ∏ j : Fin d, ∏ i ∈ Finset.Ico 1 (HananyPuder.quotEdge P j), (1 - (i : ℝ) / N) :=
  HananyPuder.W2HP.hp102_dev w hw α hα N hN
