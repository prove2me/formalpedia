-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T14:51:15.906792+00:00
-- url     : https://prove2.me/submissions/97988e93-80d6-47ed-ae39-0d347565bc90

import Mathlib
import Definitions.Def_BooneHigman_Steinberg

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u


/-!
## Section 4.1: conjugation with an unused index (Lemma 4.2)

For `J ⊆ Fin n` and `k ∉ J`, a "root word" built only from generators `x_ab(s)` with
`a, b ∈ J` conjugates the column/row products `C_k(c)`, `R_k(r)` by its induced matrix `A`
(resp. `A⁻¹`).
-/

section Lemma42

variable {n : ℕ} {R : Type u} [Ring R]

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation by a fixed element distributes over a `Finset.noncommProd`. -/
theorem conj_noncommProd {ι G : Type*} [Group G] (w : G) (s : Finset ι)
    (f : ι → G) (comm : (s : Set ι).Pairwise (Function.onFun Commute f)) :
    w * s.noncommProd f comm * w⁻¹ =
      s.noncommProd (fun i => w * f i * w⁻¹)
        (fun i hi j hj hij => (comm hi hj hij).conj w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.noncommProd_empty]; group
  | insert a s ha ih =>
    have hsub : (↑s : Set ι) ⊆ ↑(insert a s) := Finset.coe_subset.mpr (Finset.subset_insert a s)
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha,
      Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    have heq : w * (f a * s.noncommProd f (comm.mono hsub)) * w⁻¹ =
        (w * f a * w⁻¹) * (w * s.noncommProd f (comm.mono hsub) * w⁻¹) := by
      group
    rw [heq, ih]

/-- Relation (12) lifted to an actual group-level identity (not just at the matrix image). -/
theorem steinberg_x_add (i j : Fin n) (hij : i ≠ j) (a b : R) :
    SteinbergGroup.x i j hij a * SteinbergGroup.x i j hij b = SteinbergGroup.x i j hij (a + b) := by
  have hmem : steinAddRelator (⟨i, j, hij, a, b⟩ : SteinAddParam n R) ∈ steinRelations n R :=
    Or.inl (Or.inl (Set.mem_range_self _))
  have h1 := PresentedGroup.one_of_mem hmem
  unfold steinAddRelator at h1
  simp only [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

/-- Relation (13) lifted to an actual group-level identity (not just at the matrix image). -/
theorem steinberg_x_chain (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    SteinbergGroup.x i j hij a * SteinbergGroup.x j k hjk b *
        (SteinbergGroup.x i j hij a)⁻¹ * (SteinbergGroup.x j k hjk b)⁻¹ =
      SteinbergGroup.x i k hik (a * b) := by
  have hmem : steinChainRelator (⟨i, j, k, hij, hjk, hik, a, b⟩ : SteinChainParam n R) ∈
      steinRelations n R := Or.inl (Or.inr (Set.mem_range_self _))
  have h1 := PresentedGroup.one_of_mem hmem
  unfold steinChainRelator at h1
  simp only [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

theorem steinberg_x_zero (i j : Fin n) (hij : i ≠ j) :
    SteinbergGroup.x i j hij (0 : R) = 1 := by
  have h := steinberg_x_add i j hij (0 : R) (0 : R)
  rw [add_zero] at h
  calc SteinbergGroup.x i j hij (0 : R)
      = (SteinbergGroup.x i j hij (0 : R))⁻¹ *
        (SteinbergGroup.x i j hij (0 : R) * SteinbergGroup.x i j hij (0 : R)) := by group
    _ = (SteinbergGroup.x i j hij (0 : R))⁻¹ * SteinbergGroup.x i j hij (0 : R) := by rw [h]
    _ = 1 := by group

theorem steinberg_x_inv (i j : Fin n) (hij : i ≠ j) (a : R) :
    (SteinbergGroup.x i j hij a)⁻¹ = SteinbergGroup.x i j hij (-a) := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, steinberg_x_add, neg_add_cancel, steinberg_x_zero]

/-- The row-case commutator identity: conjugating `x_ka(r)` by `x_ab(s)` gives
`x_kb(-r s) * x_ka(r)`. -/
theorem steinberg_x_row_chain (k a b : Fin n) (hka : k ≠ a) (hab : a ≠ b) (hkb : k ≠ b)
    (r s : R) :
    SteinbergGroup.x a b hab s * SteinbergGroup.x k a hka r * (SteinbergGroup.x a b hab s)⁻¹ =
      SteinbergGroup.x k b hkb (-(r * s)) * SteinbergGroup.x k a hka r := by
  have h := steinberg_x_chain k a b hka hab hkb r s
  have hcomm : SteinbergGroup.x a b hab s * SteinbergGroup.x k a hka r *
      (SteinbergGroup.x a b hab s)⁻¹ * (SteinbergGroup.x k a hka r)⁻¹ =
      SteinbergGroup.x k b hkb (-(r * s)) := by
    rw [show SteinbergGroup.x a b hab s * SteinbergGroup.x k a hka r *
        (SteinbergGroup.x a b hab s)⁻¹ * (SteinbergGroup.x k a hka r)⁻¹ =
        (SteinbergGroup.x k a hka r * SteinbergGroup.x a b hab s *
          (SteinbergGroup.x k a hka r)⁻¹ * (SteinbergGroup.x a b hab s)⁻¹)⁻¹ by group]
    rw [h, steinberg_x_inv]
  calc SteinbergGroup.x a b hab s * SteinbergGroup.x k a hka r * (SteinbergGroup.x a b hab s)⁻¹
      = (SteinbergGroup.x a b hab s * SteinbergGroup.x k a hka r *
          (SteinbergGroup.x a b hab s)⁻¹ * (SteinbergGroup.x k a hka r)⁻¹) *
        SteinbergGroup.x k a hka r := by group
    _ = SteinbergGroup.x k b hkb (-(r * s)) * SteinbergGroup.x k a hka r := by rw [hcomm]


set_option backward.isDefEq.respectTransparency false in
/-- If `w` commutes with every factor of `columnElem J k hk c`, it fixes it under conjugation. -/
theorem columnElem_conj_eq_self (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (c : Fin n → R) (w : SteinbergGroup n R)
    (hcomm : ∀ i (hi : i ∈ J), Commute w (SteinbergGroup.x i k (hk i hi) (c i))) :
    w * columnElem J k hk c * w⁻¹ = columnElem J k hk c := by
  unfold columnElem
  rw [conj_noncommProd]
  refine Finset.noncommProd_congr rfl (fun i hi => ?_) _
  simp only [dif_pos (hk i hi)]
  have := (hcomm i hi).eq
  calc w * SteinbergGroup.x i k (hk i hi) (c i) * w⁻¹
      = SteinbergGroup.x i k (hk i hi) (c i) * w * w⁻¹ := by rw [this]
    _ = SteinbergGroup.x i k (hk i hi) (c i) := by group

set_option backward.isDefEq.respectTransparency false in
/-- Lemma 4.2, column case, for a single generator `w = x_ab(s)` with `a, b ∈ J`: conjugation
updates only the `a`-coordinate of `c`, to `c_a + s c_b`.

**Proof strategy** (worked out by hand, not yet formalized): write `T := (J.erase b).erase a`.
By two applications of `Finset.noncommProd_erase_mul`,
`columnElem J k hk d = T.noncommProd (...) * x_ak(d a) * x_bk(d b)` for any `d`. Every factor of
the `T`-part commutes with `w = x_ab(s)` (by `steinberg_x_commute`, since each index of `T` is
`≠ a, b`), so it is fixed under conjugation (`columnElem_conj_eq_self`-style argument). The `x_ak`
factor also commutes with `w` (shown via `steinberg_x_commute` with roots `(a,b)` and `(a,k)`), so
is unchanged. Only `x_bk(c_b)` is affected: conjugating it by `x_ab(s)` gives, via the chain
relation, `x_ak(s * c_b) * x_bk(c_b)` (`elemUnit_chain`/the `steinChainRelator` identity lifted to
the group, analogous to `steinberg_x_commute`'s lift of `steinDisjRelator`). The new `x_ak(s c_b)`
factor commutes with every `T`-factor (same argument) so can be moved next to the unchanged
`x_ak(c_a)` factor and combined via the additivity relation into `x_ak(c_a + s c_b)`, giving
exactly `columnElem J k hk (Function.update c a (c a + s * c b))`. -/
theorem lemma_4_2_column_gen (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (a b : Fin n) (hab : a ≠ b) (ha : a ∈ J) (hb : b ∈ J) (s : R) (c : Fin n → R) :
    SteinbergGroup.x a b hab s * columnElem J k hk c * (SteinbergGroup.x a b hab s)⁻¹ =
      columnElem J k hk (Function.update c a (c a + s * c b)) := by
  classical
  set w := SteinbergGroup.x a b hab s with hw_def
  set T := (J.erase b).erase a with hT_def
  set f : Fin n → SteinbergGroup n R :=
    fun i => if h : i ≠ k then SteinbergGroup.x i k h (c i) else 1 with hf_def
  set c' := Function.update c a (c a + s * c b) with hc'_def
  set f' : Fin n → SteinbergGroup n R :=
    fun i => if h : i ≠ k then SteinbergGroup.x i k h (c' i) else 1 with hf'_def
  have haT : a ∈ J.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
  have hbT : b ∉ T := fun hmem => Finset.notMem_erase b J (Finset.mem_of_mem_erase hmem)
  have haT2 : a ∉ T := Finset.notMem_erase a (J.erase b)
  have haibT : a ∉ insert b T := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact hab h
    · exact haT2 h
  have hJeq : insert a (insert b T) = J := by
    rw [Finset.insert_comm, Finset.insert_erase haT, Finset.insert_erase hb]
  -- f and c agree with f' and c' on T (both equal c there, since T excludes a)
  have hTc : ∀ i ∈ T, f i = f' i := by
    intro i hi
    have hia : i ≠ a := fun h => haT2 (h ▸ hi)
    simp only [hf_def, hf'_def, hc'_def, Function.update_of_ne hia]
  -- helper commute facts
  have hcomm_T : ∀ i ∈ T, Commute w (f i) := by
    intro i hi
    have hik : i ≠ k := hk i (by rw [← hJeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi))
    have hib : i ≠ b := fun h => hbT (h ▸ hi)
    simp only [hf_def, dif_pos hik]
    rw [hw_def]
    exact steinberg_x_commute a b i k hab hik (hk a ha) hib.symm s (c i)
  have hcomm_a : Commute w (f a) := by
    simp only [hf_def, dif_pos (hk a ha)]
    rw [hw_def]
    exact steinberg_x_commute a b a k hab (hk a ha) (hk a ha) hab.symm s (c a)
  have hchain_b : w * f b * w⁻¹ = SteinbergGroup.x a k (hk a ha) (s * c b) * f b := by
    simp only [hf_def, dif_pos (hk b hb)]
    rw [hw_def]
    have := steinberg_x_chain a b k hab (hk b hb) (hk a ha) s (c b)
    calc SteinbergGroup.x a b hab s * SteinbergGroup.x b k (hk b hb) (c b) *
          (SteinbergGroup.x a b hab s)⁻¹
        = (SteinbergGroup.x a b hab s * SteinbergGroup.x b k (hk b hb) (c b) *
            (SteinbergGroup.x a b hab s)⁻¹ * (SteinbergGroup.x b k (hk b hb) (c b))⁻¹) *
          SteinbergGroup.x b k (hk b hb) (c b) := by group
      _ = SteinbergGroup.x a k (hk a ha) (s * c b) * SteinbergGroup.x b k (hk b hb) (c b) := by
          rw [this]
  -- assemble: J = insert a (insert b T)
  have hTsubJ : T ⊆ J := (Finset.erase_subset a (J.erase b)).trans (Finset.erase_subset b J)
  have hTsub : (↑T : Set (Fin n)) ⊆ ↑J := Finset.coe_subset.mpr hTsubJ
  have hcomm : (↑J : Set (Fin n)).Pairwise (Function.onFun Commute f) := by
    intro i hi j hj hij
    simp only [Function.onFun, hf_def, dif_pos (hk i hi), dif_pos (hk j hj)]
    exact steinberg_col_commute k (hk i hi) (hk j hj) hij (c i) (c j)
  have hcomm' : (↑J : Set (Fin n)).Pairwise (Function.onFun Commute f') := by
    intro i hi j hj hij
    simp only [Function.onFun, hf'_def, dif_pos (hk i hi), dif_pos (hk j hj)]
    exact steinberg_col_commute k (hk i hi) (hk j hj) hij (c' i) (c' j)
  have hcommT : (↑T : Set (Fin n)).Pairwise (Function.onFun Commute f) := hcomm.mono hTsub
  have hcommT' : (↑T : Set (Fin n)).Pairwise (Function.onFun Commute f') := hcomm'.mono hTsub
  have hdecomp : J.noncommProd f hcomm = f a * (f b * T.noncommProd f hcommT) := by
    rw [Finset.noncommProd_congr hJeq.symm (fun _ _ => rfl) hcomm]
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ haibT,
      Finset.noncommProd_insert_of_notMem _ _ _ _ hbT]
  have hdecomp' : J.noncommProd f' hcomm' = f' a * (f' b * T.noncommProd f' hcommT') := by
    rw [Finset.noncommProd_congr hJeq.symm (fun _ _ => rfl) hcomm']
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ haibT,
      Finset.noncommProd_insert_of_notMem _ _ _ _ hbT]
  show w * J.noncommProd f hcomm * w⁻¹ = J.noncommProd f' hcomm'
  rw [hdecomp, hdecomp']
  have hTfix : w * T.noncommProd f hcommT * w⁻¹ = T.noncommProd f' hcommT' := by
    rw [conj_noncommProd]
    refine Finset.noncommProd_congr rfl (fun i hi => ?_) _
    rw [(hcomm_T i hi).eq, mul_assoc, mul_inv_cancel, mul_one]
    exact hTc i hi
  have hTfinal : T.noncommProd f hcommT = T.noncommProd f' hcommT' :=
    Finset.noncommProd_congr rfl (fun i hi => hTc i hi) hcommT
  calc w * (f a * (f b * T.noncommProd f hcommT)) * w⁻¹
      = (w * f a * w⁻¹) * (w * f b * w⁻¹) * (w * T.noncommProd f hcommT * w⁻¹) := by group
    _ = f a * (SteinbergGroup.x a k (hk a ha) (s * c b) * f b) * T.noncommProd f' hcommT' := by
        rw [hcomm_a.eq, hchain_b, hTfix]; group
    _ = SteinbergGroup.x a k (hk a ha) (c a + s * c b) * f b * T.noncommProd f' hcommT' := by
        have hcomb : SteinbergGroup.x a k (hk a ha) (c a) * SteinbergGroup.x a k (hk a ha) (s * c b) =
            SteinbergGroup.x a k (hk a ha) (c a + s * c b) := steinberg_x_add a k (hk a ha) (c a) (s * c b)
        simp only [hf_def, dif_pos (hk a ha)]
        rw [← hcomb]
        group
    _ = f' a * (f' b * T.noncommProd f' hcommT') := by
        have hfa' : SteinbergGroup.x a k (hk a ha) (c a + s * c b) = f' a := by
          simp only [hf'_def, dif_pos (hk a ha), hc'_def, Function.update_self]
        have hfb' : f b = f' b := by
          simp only [hf_def, hf'_def, dif_pos (hk b hb), hc'_def,
            Function.update_of_ne (Ne.symm hab)]
        rw [hfa', hfb']; group

/-- A word in `steinSub J` has matrix identity outside the `J × J` block. -/
theorem steinSub_matrix_trivial_outside (J : Finset (Fin n)) (w : SteinbergGroup n R)
    (hw : w ∈ steinSub J) (i j : Fin n) (hij : i ∉ J ∨ j ∉ J) :
    (steinPi w : Matrix (Fin n) (Fin n) R) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  induction hw using Subgroup.closure_induction generalizing i j with
  | mem x hx =>
      obtain ⟨p, q, hpq, s, hp, hq, rfl⟩ := hx
      rw [steinPi_x]
      show (elemUnit p q hpq s : Matrix (Fin n) (Fin n) R) i j = (1 : Matrix (Fin n) (Fin n) R) i j
      show (1 + Matrix.single p q s) i j = (1 : Matrix (Fin n) (Fin n) R) i j
      have hsingle : Matrix.single p q s i j = 0 := by
        unfold Matrix.single
        rcases hij with hi | hj
        · have hne : p ≠ i := fun h => hi (h ▸ hp)
          simp [Matrix.of_apply, hne]
        · have hne : q ≠ j := fun h => hj (h ▸ hq)
          simp [Matrix.of_apply, hne]
      simp [hsingle]
  | one => simp
  | mul x y hx hy ihx ihy =>
      rw [map_mul]
      show ((steinPi x : Matrix (Fin n) (Fin n) R) * (steinPi y : Matrix (Fin n) (Fin n) R)) i j =
        (1 : Matrix (Fin n) (Fin n) R) i j
      rw [Matrix.mul_apply]
      rcases hij with hi | hj
      · have hrow : ∀ l, (steinPi x : Matrix (Fin n) (Fin n) R) i l = if i = l then 1 else 0 := by
          intro l
          rw [ihx i l (Or.inl hi), Matrix.one_apply]
        simp only [hrow, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq Finset.univ i (fun l => (steinPi y : Matrix (Fin n) (Fin n) R) l j)]
        simp only [Finset.mem_univ, if_true]
        rw [ihy i j (Or.inl hi), Matrix.one_apply]
      · have hcol : ∀ l, (steinPi y : Matrix (Fin n) (Fin n) R) l j = if l = j then 1 else 0 := by
          intro l
          rw [ihy l j (Or.inr hj), Matrix.one_apply]
        simp only [hcol, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ j (fun l => (steinPi x : Matrix (Fin n) (Fin n) R) i l)]
        simp only [Finset.mem_univ, if_true]
        rw [ihx i j (Or.inr hj), Matrix.one_apply]
  | inv x hx ihx =>
      have hX1 : (steinPi x : Matrix (Fin n) (Fin n) R) * (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) =
          1 := by
        rw [show (steinPi x : Matrix (Fin n) (Fin n) R) * (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) =
          ((steinPi x * steinPi x⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) from
          (Units.val_mul _ _).symm, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
      have h1X : (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) * (steinPi x : Matrix (Fin n) (Fin n) R) =
          1 := by
        rw [show (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) * (steinPi x : Matrix (Fin n) (Fin n) R) =
          ((steinPi x⁻¹ * steinPi x : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) from
          (Units.val_mul _ _).symm, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      rcases hij with hi | hj
      · have heq := congrFun (congrFun hX1 i) j
        rw [Matrix.mul_apply] at heq
        have hrow : ∀ l, (steinPi x : Matrix (Fin n) (Fin n) R) i l = if i = l then 1 else 0 := by
          intro l
          rw [ihx i l (Or.inl hi), Matrix.one_apply]
        simp only [hrow, ite_mul, one_mul, zero_mul] at heq
        rw [Finset.sum_ite_eq Finset.univ i (fun l => (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) l j)] at heq
        simp only [Finset.mem_univ, if_true] at heq
        rw [heq, Matrix.one_apply]
      · have heq := congrFun (congrFun h1X i) j
        rw [Matrix.mul_apply] at heq
        have hcol : ∀ l, (steinPi x : Matrix (Fin n) (Fin n) R) l j = if l = j then 1 else 0 := by
          intro l
          rw [ihx l j (Or.inr hj), Matrix.one_apply]
        simp only [hcol, mul_ite, mul_one, mul_zero] at heq
        rw [Finset.sum_ite_eq' Finset.univ j
          (fun l => (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i l)] at heq
        simp only [Finset.mem_univ, if_true] at heq
        rw [heq, Matrix.one_apply]

/-- `steinPi`'s matrix coercion turns group multiplication into matrix multiplication. -/
theorem steinPi_mul_coe (p q : SteinbergGroup n R) :
    (steinPi p : Matrix (Fin n) (Fin n) R) * (steinPi q : Matrix (Fin n) (Fin n) R) =
      (steinPi (p * q) : Matrix (Fin n) (Fin n) R) := by
  rw [map_mul, Units.val_mul]

/-- `columnElem` only depends on its argument's values on `J`. -/
theorem columnElem_congr (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (c1 c2 : Fin n → R) (h : ∀ i ∈ J, c1 i = c2 i) :
    columnElem J k hk c1 = columnElem J k hk c2 := by
  unfold columnElem
  refine Finset.noncommProd_congr rfl (fun i hi => ?_) _
  simp only [dif_pos (hk i hi), h i hi]

/-- For `w ∈ steinSub J`, the matrix-action sum over `J` matches `steinPi`'s actual matrix
product (which formally sums over all of `Fin n`), since the extra terms vanish. -/
theorem steinSub_matrix_sum_restrict (J : Finset (Fin n)) (x y : SteinbergGroup n R)
    (hx : x ∈ steinSub J) (hy : y ∈ steinSub J) (l : Fin n) (hl : l ∈ J) (i : Fin n) :
    ∑ p, (steinPi x : Matrix (Fin n) (Fin n) R) i p * (steinPi y : Matrix (Fin n) (Fin n) R) p l =
      ∑ p ∈ J, (steinPi x : Matrix (Fin n) (Fin n) R) i p *
        (steinPi y : Matrix (Fin n) (Fin n) R) p l := by
  symm
  apply Finset.sum_subset (Finset.subset_univ J)
  intro p _ hpJ
  have hpl : p ≠ l := fun h => hpJ (h ▸ hl)
  rw [steinSub_matrix_trivial_outside J y hy p l (Or.inl hpJ), Matrix.one_apply_ne hpl, mul_zero]

set_option maxHeartbeats 1000000 in
/-- Lemma 4.2, column case, general form: conjugating `C_k(c)` by any root word `w` using only
indices in `J` multiplies `c` by `w`'s induced matrix `A` on `J`. -/
theorem lemma_4_2_column (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (w : SteinbergGroup n R) (hw : w ∈ steinSub J) (c : Fin n → R) :
    w * columnElem J k hk c * w⁻¹ =
      columnElem J k hk (fun i => ∑ j ∈ J, (steinPi w : Matrix (Fin n) (Fin n) R) i j * c j) := by
  induction hw using Subgroup.closure_induction generalizing c with
  | mem x hx =>
      obtain ⟨a, b, hab, s, ha, hb, rfl⟩ := hx
      rw [lemma_4_2_column_gen J k hk a b hab ha hb s c]
      apply columnElem_congr
      intro i hi
      rw [steinPi_x]
      show Function.update c a (c a + s * c b) i =
        ∑ j ∈ J, (elemUnit a b hab s : Matrix (Fin n) (Fin n) R) i j * c j
      have hval : ∀ j, (elemUnit a b hab s : Matrix (Fin n) (Fin n) R) i j =
          (if i = j then (1:R) else 0) + s * (if i = a then (1:R) else 0) *
            (if j = b then (1:R) else 0) := by
        intro j
        show (1 : Matrix (Fin n) (Fin n) R) i j + Matrix.single a b s i j = _
        rw [Matrix.one_apply]
        congr 1
        show (if a = i ∧ b = j then s else 0) =
          s * (if i = a then (1:R) else 0) * (if j = b then (1:R) else 0)
        by_cases hia : i = a
        · by_cases hjb : j = b
          · rw [if_pos ⟨hia.symm, hjb.symm⟩, if_pos hia, if_pos hjb, mul_one, mul_one]
          · rw [if_neg (fun h => hjb h.2.symm), if_pos hia, if_neg hjb, mul_one, mul_zero]
        · rw [if_neg (fun h => hia h.1.symm), if_neg hia, mul_zero, zero_mul]
      simp only [hval, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq J i c, if_pos hi]
      have hsum_b : (∑ x ∈ J, (s * if x = b then (1:R) else 0) * c x) = s * c b := by
        rw [show (∑ x ∈ J, (s * if x = b then (1:R) else 0) * c x) =
          ∑ x ∈ J, s * (if x = b then c x else 0) by
          refine Finset.sum_congr rfl (fun x _ => ?_); by_cases hxb : x = b <;> simp [hxb]]
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_ite_eq' J b c, if_pos hb]
      by_cases hia : i = a
      · rw [if_pos hia, mul_one, hsum_b, hia, Function.update_self]
      · rw [if_neg hia, mul_zero, Finset.sum_eq_zero (fun j _ => by simp), add_zero,
          Function.update_of_ne hia]
  | one =>
      rw [show steinPi (1 : SteinbergGroup n R) = 1 from map_one steinPi]
      simp only [one_mul, inv_one, mul_one]
      apply columnElem_congr
      intro i hi
      rw [Units.val_one]
      show c i = ∑ j ∈ J, (1 : Matrix (Fin n) (Fin n) R) i j * c j
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq J i c, if_pos hi]
  | mul x y hx hy ihx ihy =>
      rw [show x * y * columnElem J k hk c * (x * y)⁻¹ =
        x * (y * columnElem J k hk c * y⁻¹) * x⁻¹ by group, ihy c, ihx]
      rw [map_mul]
      apply columnElem_congr
      intro i hi
      show ∑ j ∈ J, (steinPi x : Matrix (Fin n) (Fin n) R) i j *
            ∑ l ∈ J, (steinPi y : Matrix (Fin n) (Fin n) R) j l * c l =
          ∑ j ∈ J, ((steinPi x * steinPi y : (Matrix (Fin n) (Fin n) R)ˣ) :
            Matrix (Fin n) (Fin n) R) i j * c j
      rw [show ((steinPi x * steinPi y : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) =
          (steinPi x : Matrix (Fin n) (Fin n) R) * (steinPi y : Matrix (Fin n) (Fin n) R) from
          Units.val_mul _ _]
      calc ∑ j ∈ J, (steinPi x : Matrix (Fin n) (Fin n) R) i j *
            ∑ l ∈ J, (steinPi y : Matrix (Fin n) (Fin n) R) j l * c l
          = ∑ j ∈ J, ∑ l ∈ J, (steinPi x : Matrix (Fin n) (Fin n) R) i j *
              ((steinPi y : Matrix (Fin n) (Fin n) R) j l * c l) := by
            simp [Finset.mul_sum]
        _ = ∑ l ∈ J, ∑ j ∈ J, (steinPi x : Matrix (Fin n) (Fin n) R) i j *
              (steinPi y : Matrix (Fin n) (Fin n) R) j l * c l := by
            rw [Finset.sum_comm]; simp [mul_assoc]
        _ = ∑ l ∈ J, (∑ j ∈ J, (steinPi x : Matrix (Fin n) (Fin n) R) i j *
              (steinPi y : Matrix (Fin n) (Fin n) R) j l) * c l := by
            simp [Finset.sum_mul]
        _ = ∑ l ∈ J, ((steinPi x : Matrix (Fin n) (Fin n) R) *
              (steinPi y : Matrix (Fin n) (Fin n) R)) i l * c l := by
            refine Finset.sum_congr rfl (fun l hl => ?_)
            rw [Matrix.mul_apply, ← steinSub_matrix_sum_restrict J x y hx hy l hl i]
  | inv x hx ihx =>
      have hinv_undo : ∀ i ∈ J,
          ∑ j ∈ J, (steinPi x : Matrix (Fin n) (Fin n) R) i j *
            (∑ l ∈ J, (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) j l * c l) = c i := by
        intro i hi
        calc ∑ j ∈ J, (steinPi x : Matrix (Fin n) (Fin n) R) i j *
              ∑ l ∈ J, (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) j l * c l
            = ∑ l ∈ J, ((steinPi x : Matrix (Fin n) (Fin n) R) *
                (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R)) i l * c l := by
              calc ∑ j ∈ J, (steinPi x : Matrix (Fin n) (Fin n) R) i j *
                    ∑ l ∈ J, (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) j l * c l
                  = ∑ j ∈ J, ∑ l ∈ J, (steinPi x : Matrix (Fin n) (Fin n) R) i j *
                      ((steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) j l * c l) := by
                    simp only [Finset.mul_sum]
                _ = ∑ l ∈ J, ∑ j ∈ J, (steinPi x : Matrix (Fin n) (Fin n) R) i j *
                      (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) j l * c l := by
                    rw [Finset.sum_comm]; simp only [mul_assoc]
                _ = ∑ l ∈ J, (∑ j ∈ J, (steinPi x : Matrix (Fin n) (Fin n) R) i j *
                      (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) j l) * c l := by
                    simp only [Finset.sum_mul]
                _ = ∑ l ∈ J, ((steinPi x : Matrix (Fin n) (Fin n) R) *
                      (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R)) i l * c l := by
                    refine Finset.sum_congr rfl (fun l hl => ?_)
                    rw [Matrix.mul_apply, ← steinSub_matrix_sum_restrict J x x⁻¹ hx
                        (Subgroup.inv_mem _ hx) l hl i]
          _ = ∑ l ∈ J, (if i = l then (1:R) else 0) * c l := by
              rw [steinPi_mul_coe, mul_inv_cancel,
                show steinPi (1 : SteinbergGroup n R) = 1 from map_one steinPi, Units.val_one]
              simp only [Matrix.one_apply]
          _ = c i := by
              simp only [ite_mul, one_mul, zero_mul]
              rw [Finset.sum_ite_eq J i c, if_pos hi]
      have key := ihx (fun i => ∑ j ∈ J, (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i j * c j)
      rw [columnElem_congr J k hk _ c hinv_undo] at key
      rw [inv_inv]
      rw [show x⁻¹ * columnElem J k hk c * x =
        x⁻¹ * (x * columnElem J k hk (fun i => ∑ j ∈ J,
          (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i j * c j) * x⁻¹) * x by rw [key],
        map_inv]
      group

/-- `rowElem` only depends on its argument's values on `J`. -/
theorem rowElem_congr (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (r1 r2 : Fin n → R) (h : ∀ i ∈ J, r1 i = r2 i) :
    rowElem J k hk r1 = rowElem J k hk r2 := by
  unfold rowElem
  refine Finset.noncommProd_congr rfl (fun i hi => ?_) _
  simp only [dif_pos (hk i hi), h i hi]

set_option backward.isDefEq.respectTransparency false in
/-- Lemma 4.2, row case, for a single generator `w = x_ab(s)` with `a, b ∈ J`: conjugation
updates only the `b`-coordinate of `r`, to `r_b - r_a s`. -/
theorem lemma_4_2_row_gen (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (a b : Fin n) (hab : a ≠ b) (ha : a ∈ J) (hb : b ∈ J) (s : R) (r : Fin n → R) :
    SteinbergGroup.x a b hab s * rowElem J k hk r * (SteinbergGroup.x a b hab s)⁻¹ =
      rowElem J k hk (Function.update r b (r b - r a * s)) := by
  classical
  set w := SteinbergGroup.x a b hab s with hw_def
  set T := (J.erase b).erase a with hT_def
  have haJb : a ∈ J.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
  have hbJ : b ∈ J := hb
  have hTsubJ : T ⊆ J := (Finset.erase_subset a (J.erase b)).trans (Finset.erase_subset b J)
  have hTsubJcoe : (↑T : Set (Fin n)) ⊆ ↑J := Finset.coe_subset.mpr hTsubJ
  have hcomm : ∀ i (hi : i ∈ J), ∀ j (hj : j ∈ J), i ≠ j →
      Commute (SteinbergGroup.x k i (hk i hi).symm (r i))
        (SteinbergGroup.x k j (hk j hj).symm (r j)) :=
    fun i hi j hj hij => steinberg_row_commute k (hk i hi) (hk j hj) hij (r i) (r j)
  have hTc : ∀ i ∈ T, (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1) i =
      (fun i => if h : i ≠ k then
        SteinbergGroup.x k i h.symm (Function.update r b (r b - r a * s) i) else 1) i := by
    intro i hi
    have hib : i ≠ b := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    simp only [dif_pos (hk i (hTsubJ hi)), Function.update_of_ne hib]
  have hbT : b ∉ T := fun hmem => Finset.notMem_erase b J (Finset.mem_of_mem_erase hmem)
  have haT2 : a ∉ T := Finset.notMem_erase a (J.erase b)
  have haibT : a ∉ insert b T := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact hab h
    · exact haT2 h
  have hJeq : insert a (insert b T) = J := by
    rw [Finset.insert_comm, Finset.insert_erase haJb, Finset.insert_erase hb]
  have hcommJ : (↑J : Set (Fin n)).Pairwise
      (Function.onFun Commute (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i)
        else 1)) :=
    fun i hi j hj hij => by
      simp only [Function.onFun, dif_pos (hk i hi), dif_pos (hk j hj)]
      exact hcomm i hi j hj hij
  have hcommJ' : (↑J : Set (Fin n)).Pairwise
      (Function.onFun Commute (fun i => if h : i ≠ k then
        SteinbergGroup.x k i h.symm (Function.update r b (r b - r a * s) i) else 1)) :=
    fun i hi j hj hij => by
      simp only [Function.onFun, dif_pos (hk i hi), dif_pos (hk j hj)]
      exact steinberg_row_commute k (hk i hi) (hk j hj) hij _ _
  have hcommT : (↑T : Set (Fin n)).Pairwise
      (Function.onFun Commute (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i)
        else 1)) := hcommJ.mono hTsubJcoe
  have hdecomp : J.noncommProd
      (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1) hcommJ =
      (if h : a ≠ k then SteinbergGroup.x k a h.symm (r a) else 1) *
      ((if h : b ≠ k then SteinbergGroup.x k b h.symm (r b) else 1) *
        T.noncommProd (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1)
          hcommT) := by
    rw [Finset.noncommProd_congr hJeq.symm (fun _ _ => rfl) hcommJ]
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ haibT,
      Finset.noncommProd_insert_of_notMem _ _ _ _ hbT]
  have hdecomp' : J.noncommProd (fun i => if h : i ≠ k then
      SteinbergGroup.x k i h.symm (Function.update r b (r b - r a * s) i) else 1) hcommJ' =
      (if h : a ≠ k then SteinbergGroup.x k a h.symm
          (Function.update r b (r b - r a * s) a) else 1) *
      ((if h : b ≠ k then SteinbergGroup.x k b h.symm
          (Function.update r b (r b - r a * s) b) else 1) *
        T.noncommProd (fun i => if h : i ≠ k then
          SteinbergGroup.x k i h.symm (Function.update r b (r b - r a * s) i) else 1)
          (hcommJ'.mono hTsubJcoe)) := by
    rw [Finset.noncommProd_congr hJeq.symm (fun _ _ => rfl) hcommJ']
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ haibT,
      Finset.noncommProd_insert_of_notMem _ _ _ _ hbT]
  show w * J.noncommProd
    (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1) hcommJ * w⁻¹ =
    J.noncommProd (fun i => if h : i ≠ k then
      SteinbergGroup.x k i h.symm (Function.update r b (r b - r a * s) i) else 1) hcommJ'
  rw [hdecomp, hdecomp']
  simp only [dif_pos (hk a ha), dif_pos (hk b hb)]
  have hTfix : w * T.noncommProd
      (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1) hcommT * w⁻¹ =
      T.noncommProd (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1)
        hcommT := by
    rw [show w * T.noncommProd
        (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1) hcommT * w⁻¹ =
        T.noncommProd
          (fun i => w * (if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1) * w⁻¹)
          (fun i hi j hj hij => (hcommT hi hj hij).conj w) from conj_noncommProd w T _ hcommT]
    refine Finset.noncommProd_congr rfl (fun i hi => ?_)
      (fun i hi j hj hij => (hcommT hi hj hij).conj w)
    have hcommi : Commute w (if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1) := by
      have hik : i ≠ k := hk i (hTsubJ hi)
      have hia : i ≠ a := fun h => haT2 (h ▸ hi)
      have hib : i ≠ b := fun h => hbT (h ▸ hi)
      simp only [dif_pos hik]
      exact steinberg_x_commute a b k i hab hik.symm hia.symm (hk b hb) s (r i)
    rw [hcommi.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [show w * (SteinbergGroup.x k a (hk a ha).symm (r a) *
        (SteinbergGroup.x k b (hk b hb).symm (r b) *
          T.noncommProd (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1)
            hcommT)) * w⁻¹ =
      (w * SteinbergGroup.x k a (hk a ha).symm (r a) * w⁻¹) *
        (w * SteinbergGroup.x k b (hk b hb).symm (r b) * w⁻¹) *
        (w * T.noncommProd
          (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1) hcommT * w⁻¹) by
      group]
  rw [hTfix]
  have hgfix : w * SteinbergGroup.x k b (hk b hb).symm (r b) * w⁻¹ =
      SteinbergGroup.x k b (hk b hb).symm (r b) := by
    have : Commute w (SteinbergGroup.x k b (hk b hb).symm (r b)) :=
      steinberg_x_commute a b k b hab (hk b hb).symm hab (hk b hb) s (r b)
    rw [this.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hgtransform : w * SteinbergGroup.x k a (hk a ha).symm (r a) * w⁻¹ =
      SteinbergGroup.x k b (hk b hb).symm (-(r a * s)) *
        SteinbergGroup.x k a (hk a ha).symm (r a) :=
    steinberg_x_row_chain k a b (hk a ha).symm hab (hk b hb).symm (r a) s
  rw [hgfix, hgtransform]
  have hswap := (steinberg_row_commute k (hk b hb) (hk a ha) hab.symm (-(r a * s)) (r a)).eq
  have hcommT' : (↑T : Set (Fin n)).Pairwise (Function.onFun Commute (fun i => if h : i ≠ k then
      SteinbergGroup.x k i h.symm (Function.update r b (r b - r a * s) i) else 1)) :=
    hcommJ'.mono hTsubJcoe
  calc SteinbergGroup.x k b (hk b hb).symm (-(r a * s)) * SteinbergGroup.x k a (hk a ha).symm (r a)
        * SteinbergGroup.x k b (hk b hb).symm (r b) *
          T.noncommProd (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1)
            hcommT
      = SteinbergGroup.x k a (hk a ha).symm (r a) *
          (SteinbergGroup.x k b (hk b hb).symm (-(r a * s)) *
            SteinbergGroup.x k b (hk b hb).symm (r b)) *
          T.noncommProd (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1)
            hcommT := by rw [hswap]; group
    _ = SteinbergGroup.x k a (hk a ha).symm (r a) *
          SteinbergGroup.x k b (hk b hb).symm (r b - r a * s) *
          T.noncommProd (fun i => if h : i ≠ k then SteinbergGroup.x k i h.symm (r i) else 1)
            hcommT := by
        rw [steinberg_x_add, show -(r a * s) + r b = r b - r a * s by abel]
    _ = SteinbergGroup.x k a (hk a ha).symm (Function.update r b (r b - r a * s) a) *
          (SteinbergGroup.x k b (hk b hb).symm
              (Function.update r b (r b - r a * s) b) *
            T.noncommProd (fun i => if h : i ≠ k then
              SteinbergGroup.x k i h.symm (Function.update r b (r b - r a * s) i) else 1)
              hcommT') := by
        rw [mul_assoc]
        simp only [Function.update_self, Function.update_of_ne hab]
        congr 1
        congr 1
        refine Finset.noncommProd_congr rfl (fun i hi => hTc i hi) hcommT

set_option maxHeartbeats 1000000 in
/-- Lemma 4.2, row case, general form: conjugating `R_k(r)` by any root word `w` using only
indices in `J` multiplies `r` by `w`'s induced matrix's inverse on `J`. -/
theorem lemma_4_2_row (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (w : SteinbergGroup n R) (hw : w ∈ steinSub J) (r : Fin n → R) :
    w * rowElem J k hk r * w⁻¹ =
      rowElem J k hk (fun j => ∑ i ∈ J, r i * (steinPi w⁻¹ : Matrix (Fin n) (Fin n) R) i j) := by
  induction hw using Subgroup.closure_induction generalizing r with
  | mem x hx =>
      obtain ⟨a, b, hab, s, ha, hb, rfl⟩ := hx
      rw [lemma_4_2_row_gen J k hk a b hab ha hb s r]
      apply rowElem_congr
      intro j hj
      rw [show (SteinbergGroup.x a b hab s)⁻¹ = SteinbergGroup.x a b hab (-s) from
        steinberg_x_inv a b hab s, steinPi_x]
      show Function.update r b (r b - r a * s) j =
        ∑ i ∈ J, r i * (elemUnit a b hab (-s) : Matrix (Fin n) (Fin n) R) i j
      have hentry : ∀ i, (elemUnit a b hab (-s) : Matrix (Fin n) (Fin n) R) i j =
          (if i = j then (1:R) else 0) + (if i = a ∧ j = b then -s else 0) := by
        intro i
        show (1 : Matrix (Fin n) (Fin n) R) i j + Matrix.single a b (-s) i j = _
        rw [Matrix.one_apply]
        congr 1
        show (if a = i ∧ b = j then -s else 0) = if i = a ∧ j = b then -s else 0
        by_cases hia : i = a
        · by_cases hjb : j = b
          · rw [if_pos ⟨hia.symm, hjb.symm⟩, if_pos ⟨hia, hjb⟩]
          · rw [if_neg (fun h => hjb h.2.symm), if_neg (fun h => hjb h.2)]
        · rw [if_neg (fun h => hia h.1.symm), if_neg (fun h => hia h.1)]
      by_cases hjb : j = b
      · have hja : ¬(j = a) := fun h => hab (h ▸ hjb ▸ rfl)
        have : ∀ i, r i * (elemUnit a b hab (-s) : Matrix (Fin n) (Fin n) R) i j =
            (if i = j then r i else 0) + (if i = a then r i * (-s) else 0) := by
          intro i
          rw [hentry]
          by_cases hij : i = j
          · have hia : ¬(i = a) := fun h => hja (h ▸ hij.symm)
            rw [if_pos hij, if_neg (fun h => hia h.1), if_pos hij, if_neg hia, add_zero, add_zero,
              mul_one]
          · by_cases hia : i = a
            · rw [if_neg hij, if_pos ⟨hia, hjb⟩, if_neg hij, if_pos hia, zero_add, zero_add]
            · rw [if_neg hij, if_neg (fun h => hia h.1), if_neg hij, if_neg hia, add_zero,
                mul_zero]
        simp only [this, Finset.sum_add_distrib]
        rw [Finset.sum_ite_eq' J j r, if_pos hj, Finset.sum_ite_eq' J a (fun i => r i * (-s)),
          if_pos ha, hjb, Function.update_self, mul_neg, ← sub_eq_add_neg]
      · have : ∀ i, r i * (elemUnit a b hab (-s) : Matrix (Fin n) (Fin n) R) i j =
            if i = j then r i else 0 := by
          intro i
          rw [hentry]
          have hab2 : ¬(i = a ∧ j = b) := fun h => hjb h.2
          simp [hab2]
        simp only [this]
        rw [Finset.sum_ite_eq' J j r, if_pos hj, Function.update_of_ne hjb]
  | one =>
      rw [inv_one, show steinPi (1 : SteinbergGroup n R) = 1 from map_one steinPi]
      simp only [one_mul, inv_one, mul_one]
      apply rowElem_congr
      intro j hj
      rw [Units.val_one]
      show r j = ∑ i ∈ J, r i * (1 : Matrix (Fin n) (Fin n) R) i j
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' J j r, if_pos hj]
  | mul x y hx hy ihx ihy =>
      rw [show x * y * rowElem J k hk r * (x * y)⁻¹ =
        x * (y * rowElem J k hk r * y⁻¹) * x⁻¹ by group, ihy r, ihx]
      rw [mul_inv_rev, map_mul]
      apply rowElem_congr
      intro j hj
      show ∑ i ∈ J, (∑ l ∈ J, r l * (steinPi y⁻¹ : Matrix (Fin n) (Fin n) R) l i) *
            (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i j =
          ∑ i ∈ J, r i * ((steinPi y⁻¹ * steinPi x⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) :
            Matrix (Fin n) (Fin n) R) i j
      rw [show ((steinPi y⁻¹ * steinPi x⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) :
          Matrix (Fin n) (Fin n) R) =
          (steinPi y⁻¹ : Matrix (Fin n) (Fin n) R) * (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) from
          Units.val_mul _ _]
      calc ∑ i ∈ J, (∑ l ∈ J, r l * (steinPi y⁻¹ : Matrix (Fin n) (Fin n) R) l i) *
            (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i j
          = ∑ i ∈ J, ∑ l ∈ J, (r l * (steinPi y⁻¹ : Matrix (Fin n) (Fin n) R) l i) *
              (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i j := by
            simp only [Finset.sum_mul]
        _ = ∑ l ∈ J, ∑ i ∈ J, r l * ((steinPi y⁻¹ : Matrix (Fin n) (Fin n) R) l i *
              (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i j) := by
            rw [Finset.sum_comm]; simp only [mul_assoc]
        _ = ∑ l ∈ J, r l * (∑ i ∈ J, (steinPi y⁻¹ : Matrix (Fin n) (Fin n) R) l i *
              (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i j) := by
            simp only [Finset.mul_sum]
        _ = ∑ l ∈ J, r l * ((steinPi y⁻¹ : Matrix (Fin n) (Fin n) R) *
              (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R)) l j := by
            refine Finset.sum_congr rfl (fun l hl => ?_)
            rw [Matrix.mul_apply, ← steinSub_matrix_sum_restrict J y⁻¹ x⁻¹
              (Subgroup.inv_mem _ hy) (Subgroup.inv_mem _ hx) j hj l]
  | inv x hx ihx =>
      have hinv_undo : ∀ j ∈ J,
          ∑ i ∈ J, (∑ l ∈ J, r l * (steinPi x : Matrix (Fin n) (Fin n) R) l i) *
            (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i j = r j := by
        intro j hj
        calc ∑ i ∈ J, (∑ l ∈ J, r l * (steinPi x : Matrix (Fin n) (Fin n) R) l i) *
              (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i j
            = ∑ l ∈ J, r l * ((steinPi x : Matrix (Fin n) (Fin n) R) *
                (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R)) l j := by
              calc ∑ i ∈ J, (∑ l ∈ J, r l * (steinPi x : Matrix (Fin n) (Fin n) R) l i) *
                    (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i j
                  = ∑ i ∈ J, ∑ l ∈ J, (r l * (steinPi x : Matrix (Fin n) (Fin n) R) l i) *
                      (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i j := by
                    simp only [Finset.sum_mul]
                _ = ∑ l ∈ J, ∑ i ∈ J, r l * ((steinPi x : Matrix (Fin n) (Fin n) R) l i *
                      (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i j) := by
                    rw [Finset.sum_comm]; simp only [mul_assoc]
                _ = ∑ l ∈ J, r l * (∑ i ∈ J, (steinPi x : Matrix (Fin n) (Fin n) R) l i *
                      (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R) i j) := by
                    simp only [Finset.mul_sum]
                _ = ∑ l ∈ J, r l * ((steinPi x : Matrix (Fin n) (Fin n) R) *
                      (steinPi x⁻¹ : Matrix (Fin n) (Fin n) R)) l j := by
                    refine Finset.sum_congr rfl (fun l hl => ?_)
                    rw [Matrix.mul_apply, ← steinSub_matrix_sum_restrict J x x⁻¹ hx
                      (Subgroup.inv_mem _ hx) j hj l]
          _ = ∑ l ∈ J, r l * (if l = j then (1:R) else 0) := by
              rw [steinPi_mul_coe, mul_inv_cancel,
                show steinPi (1 : SteinbergGroup n R) = 1 from map_one steinPi, Units.val_one]
              simp only [Matrix.one_apply]
          _ = r j := by
              simp only [mul_ite, mul_one, mul_zero]
              rw [Finset.sum_ite_eq' J j r, if_pos hj]
      have key := ihx (fun j => ∑ i ∈ J, r i * (steinPi x : Matrix (Fin n) (Fin n) R) i j)
      rw [rowElem_congr J k hk _ r hinv_undo] at key
      rw [inv_inv]
      rw [show x⁻¹ * rowElem J k hk r * x =
        x⁻¹ * (x * rowElem J k hk (fun j => ∑ i ∈ J,
          r i * (steinPi x : Matrix (Fin n) (Fin n) R) i j) * x⁻¹) * x by rw [key]]
      group

end Lemma42

end FiniteAlgebraicEnvelopes
end OAI

open OAI.FiniteAlgebraicEnvelopes

universe u

theorem solution {n : ℕ} {R : Type u} [Ring R] (J : Finset (Fin n)) (k : Fin n)
    (hk : ∀ i ∈ J, i ≠ k) (w : SteinbergGroup n R) (hw : w ∈ steinSub J) (c r : Fin n → R) :
    w * columnElem J k hk c * w⁻¹ =
      columnElem J k hk
        (fun i => ∑ j ∈ J, (steinPi w : Matrix (Fin n) (Fin n) R) i j * c j) ∧
    w * rowElem J k hk r * w⁻¹ =
      rowElem J k hk
        (fun j => ∑ i ∈ J, r i * (steinPi w⁻¹ : Matrix (Fin n) (Fin n) R) i j) :=
  ⟨OAI.FiniteAlgebraicEnvelopes.lemma_4_2_column J k hk w hw c,
   OAI.FiniteAlgebraicEnvelopes.lemma_4_2_row J k hk w hw r⟩
