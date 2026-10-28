-- Prove2me | solution 1 for IntractableCoding.Weights.subspace_reduction_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:36:21.98703+00:00
-- url     : https://prove2.me/submissions/72738e58-b4ab-4895-9251-12caf279843f

import Mathlib
import Definitions.Def_IntractableCoding_Weights_Reductions

namespace IntractableCoding.Weights
open PricingWithTips

variable (I : ThreeDMInstance)

lemma mem_triples_iff (abc : Fin I.1 × Fin I.1 × Fin I.1) :
    abc ∈ triples I ↔ I.2 abc.1 abc.2.1 abc.2.2 = true := by
  obtain ⟨a, b, c⟩ := abc
  unfold triples
  simp [List.mem_filter, List.mem_flatMap, List.mem_map]

lemma triples_nodup : (triples I).Nodup := by
  unfold triples
  apply List.Nodup.filter
  rw [List.nodup_flatMap]
  refine ⟨fun a _ => ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun b _ => ?_, ?_⟩
    · exact (List.nodup_finRange _).map (fun c c' h => by simpa using h)
    · rw [List.pairwise_iff_get]
      intro i j hij
      simp only [Function.onFun, List.disjoint_left]
      intro x hx hx'
      simp only [List.mem_map, List.mem_finRange, true_and] at hx hx'
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨c', h⟩ := hx'
      have := (Prod.mk.inj h).1
      have h2 := (Prod.mk.inj (Prod.mk.inj h).2).1
      have : (List.finRange I.1).get i = (List.finRange I.1).get j := by
        simp only [List.get_eq_getElem] at *
        exact h2 ▸ rfl
      rw [(List.nodup_finRange _).get_inj_iff] at this
      exact absurd this (ne_of_lt hij)
  · rw [List.pairwise_iff_get]
    intro i j hij
    simp only [Function.onFun, List.disjoint_left]
    intro x hx hx'
    simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hx hx'
    obtain ⟨b, c, rfl⟩ := hx
    obtain ⟨b', c', h⟩ := hx'
    have h1 := (Prod.mk.inj h).1
    have : (List.finRange I.1).get i = (List.finRange I.1).get j := by
      simp only [List.get_eq_getElem] at *
      exact h1 ▸ rfl
    rw [(List.nodup_finRange _).get_inj_iff] at this
    exact absurd this (ne_of_lt hij)


lemma get_injective : Function.Injective fun r : Fin (tCount I) => (triples I).get r := by
  intro r r' h
  exact (List.nodup_iff_injective_get.mp (triples_nodup I)) h

lemma exists_get_of_edge (a b c : Fin I.1) (h : I.2 a b c = true) :
    ∃ r : Fin (tCount I), (triples I).get r = (a, b, c) := by
  have : (a, b, c) ∈ triples I := (mem_triples_iff I (a, b, c)).mpr h
  exact List.mem_iff_get.mp this

lemma edge_of_get (r : Fin (tCount I)) :
    I.2 ((triples I).get r).1 ((triples I).get r).2.1 ((triples I).get r).2.2 = true :=
  (mem_triples_iff I _).mp (List.get_mem _ _)

/-- column embeddings -/
def colA (a : Fin I.1) : Fin (3 * I.1) := ⟨a.val, by omega⟩
def colB (b : Fin I.1) : Fin (3 * I.1) := ⟨I.1 + b.val, by omega⟩
def colC (c : Fin I.1) : Fin (3 * I.1) := ⟨2 * I.1 + c.val, by omega⟩

lemma incidence_colA (r : Fin (tCount I)) (a : Fin I.1) :
    incidence I r (colA I a) = if ((triples I).get r).1 = a then 1 else 0 := by
  unfold incidence colA
  simp only
  congr 1
  apply propext
  constructor
  · rintro (h | h | h)
    · exact Fin.ext h.symm
    · exfalso; omega
    · exfalso; omega
  · intro h; left; exact congrArg Fin.val h.symm

lemma incidence_colB (r : Fin (tCount I)) (b : Fin I.1) :
    incidence I r (colB I b) = if ((triples I).get r).2.1 = b then 1 else 0 := by
  unfold incidence colB
  simp only
  congr 1
  apply propext
  constructor
  · rintro (h | h | h)
    · exfalso; omega
    · exact Fin.ext (by omega)
    · exfalso; omega
  · intro h; right; left; rw [h]

lemma incidence_colC (r : Fin (tCount I)) (c : Fin I.1) :
    incidence I r (colC I c) = if ((triples I).get r).2.2 = c then 1 else 0 := by
  unfold incidence colC
  simp only
  congr 1
  apply propext
  constructor
  · rintro (h | h | h)
    · exfalso; omega
    · exfalso; omega
    · exact Fin.ext (by omega)
  · intro h; right; right; rw [h]

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-- support of a 0/1 vector -/
def supp {ι : Type} [Fintype ι] (x : ι → ZMod 2) : Finset ι := Finset.univ.filter fun i => x i = 1

lemma hammingNorm_eq_card_supp {ι : Type} [Fintype ι] (x : ι → ZMod 2) :
    hammingNorm x = (supp x).card := by
  unfold hammingNorm supp
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases zmod2_cases (x i) with h | h <;> simp [h]

lemma sum_mul_ite {ι : Type} [Fintype ι] (x : ι → ZMod 2) (P : ι → Prop) [DecidablePred P] :
    (∑ i, x i * (if P i then 1 else 0)) = (((supp x).filter P).card : ZMod 2) := by
  have : ∀ i, x i * (if P i then (1 : ZMod 2) else 0) = if (x i = 1 ∧ P i) then 1 else 0 := by
    intro i
    rcases zmod2_cases (x i) with h | h <;> simp [h]
  simp_rw [this]
  rw [Finset.sum_boole]
  congr 2
  unfold supp
  ext i
  simp [Finset.mem_filter]

lemma vecMul_incidence_colA (x : Fin (tCount I) → ZMod 2) (a : Fin I.1) :
    Matrix.vecMul x (incidence I) (colA I a) =
      (((supp x).filter fun r : Fin (tCount I) => ((triples I).get r).1 = a).card : ZMod 2) := by
  simp only [Matrix.vecMul, dotProduct, incidence_colA]
  exact sum_mul_ite x _

lemma vecMul_incidence_colB (x : Fin (tCount I) → ZMod 2) (b : Fin I.1) :
    Matrix.vecMul x (incidence I) (colB I b) =
      (((supp x).filter fun r : Fin (tCount I) => ((triples I).get r).2.1 = b).card : ZMod 2) := by
  simp only [Matrix.vecMul, dotProduct, incidence_colB]
  exact sum_mul_ite x _

lemma vecMul_incidence_colC (x : Fin (tCount I) → ZMod 2) (c : Fin I.1) :
    Matrix.vecMul x (incidence I) (colC I c) =
      (((supp x).filter fun r : Fin (tCount I) => ((triples I).get r).2.2 = c).card : ZMod 2) := by
  simp only [Matrix.vecMul, dotProduct, incidence_colC]
  exact sum_mul_ite x _

/-- Counting lemma: fibers of a map `f : S → Fin n` with all fibers odd. -/
lemma card_le_of_fibers_odd {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι) (n : ℕ)
    (f : ι → Fin n) (hodd : ∀ a : Fin n, Odd ((S.filter fun r => f r = a).card)) :
    n ≤ S.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  calc n = ∑ a : Fin n, 1 := by simp
    _ ≤ ∑ a : Fin n, (S.filter fun r => f r = a).card :=
        Finset.sum_le_sum fun a _ => (hodd a).pos

lemma fibers_eq_one_of_odd {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι) (n : ℕ)
    (f : ι → Fin n) (hodd : ∀ a : Fin n, Odd ((S.filter fun r => f r = a).card))
    (hcard : S.card ≤ n) : ∀ a : Fin n, (S.filter fun r => f r = a).card = 1 := by
  have hsum := Finset.card_eq_sum_card_fiberwise (f := f) (s := S) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  have h1 : ∀ a ∈ (Finset.univ : Finset (Fin n)), 1 ≤ (S.filter fun r => f r = a).card :=
    fun a _ => (hodd a).pos
  have h2 : ∑ a : Fin n, 1 = ∑ a : Fin n, (S.filter fun r => f r = a).card := by
    apply le_antisymm (Finset.sum_le_sum h1)
    rw [← hsum]; simpa using hcard
  have := (Finset.sum_eq_sum_iff_of_le h1).mp h2
  intro a
  exact (this a (Finset.mem_univ a)).symm

lemma fibers_eq_one_of_injOn {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι) (n : ℕ)
    (f : ι → Fin n) (hinj : Set.InjOn f S) (hcard : n ≤ S.card) :
    ∀ a : Fin n, (S.filter fun r => f r = a).card = 1 := by
  have hle : S.card ≤ n := by
    have := Finset.card_le_univ (S.image f)
    rw [Finset.card_image_of_injOn hinj, Fintype.card_fin] at this
    exact this
  have himg : S.image f = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Fintype.card_fin]
    exact le_antisymm hle hcard
  intro a
  have ha : a ∈ S.image f := by rw [himg]; exact Finset.mem_univ a
  obtain ⟨r, hr, hra⟩ := Finset.mem_image.mp ha
  rw [Finset.card_eq_one]
  refine ⟨r, ?_⟩
  ext r'
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hr', hra'⟩
    exact hinj hr' hr (hra'.trans hra.symm)
  · rintro rfl; exact ⟨hr, hra⟩

lemma card_sum_eq (S : Finset (Fin (tCount I))) :
    ∑ a : Fin I.1, (S.filter fun r : Fin (tCount I) => ((triples I).get r).1 = a).card = S.card :=
  (Finset.card_eq_sum_card_fiberwise (f := fun r => ((triples I).get r).1) (s := S)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm

lemma exists_unique_of_card_one {ι : Type} [DecidableEq ι] (S : Finset ι) (P : ι → Prop)
    [DecidablePred P] (h : (S.filter P).card = 1) : ∃! r, r ∈ S ∧ P r := by
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp h
  have hmem : ∀ r', r' ∈ S ∧ P r' ↔ r' = r := by
    intro r'
    rw [← Finset.mem_singleton, ← hr, Finset.mem_filter]
  exact ⟨r, (hmem r).mpr rfl, fun r' h' => (hmem r').mp h'⟩


lemma vecMul_eq_one_of_fibers (x : Fin (tCount I) → ZMod 2)
    (hA : ∀ a : Fin I.1, ((supp x).filter fun r : Fin (tCount I) => ((triples I).get r).1 = a).card = 1)
    (hB : ∀ b : Fin I.1, ((supp x).filter fun r : Fin (tCount I) => ((triples I).get r).2.1 = b).card = 1)
    (hC : ∀ c : Fin I.1, ((supp x).filter fun r : Fin (tCount I) => ((triples I).get r).2.2 = c).card = 1) :
    Matrix.vecMul x (incidence I) = fun _ => 1 := by
  funext j
  rcases lt_or_ge j.val I.1 with h | h
  · have : j = colA I ⟨j.val, h⟩ := Fin.ext rfl
    rw [this, vecMul_incidence_colA, hA]; simp
  · rcases lt_or_ge j.val (2 * I.1) with h2 | h2
    · have : j = colB I ⟨j.val - I.1, by omega⟩ := Fin.ext (by simp [colB]; omega)
      rw [this, vecMul_incidence_colB, hB]; simp
    · have : j = colC I ⟨j.val - 2 * I.1, by omega⟩ := Fin.ext (by simp [colC]; omega)
      rw [this, vecMul_incidence_colC, hC]; simp

lemma fibers_odd_of_vecMul_eq_one (x : Fin (tCount I) → ZMod 2)
    (hxB : Matrix.vecMul x (incidence I) = fun _ => 1) :
    (∀ a : Fin I.1, Odd ((supp x).filter fun r : Fin (tCount I) => ((triples I).get r).1 = a).card) ∧
    (∀ b : Fin I.1, Odd ((supp x).filter fun r : Fin (tCount I) => ((triples I).get r).2.1 = b).card) ∧
    (∀ c : Fin I.1, Odd ((supp x).filter fun r : Fin (tCount I) => ((triples I).get r).2.2 = c).card) := by
  refine ⟨fun a => ?_, fun b => ?_, fun c => ?_⟩
  · rw [← ZMod.natCast_eq_one_iff_odd, ← vecMul_incidence_colA, hxB]
  · rw [← ZMod.natCast_eq_one_iff_odd, ← vecMul_incidence_colB, hxB]
  · rw [← ZMod.natCast_eq_one_iff_odd, ← vecMul_incidence_colC, hxB]

/-- the forward direction of the matching lemma -/
theorem exists_vec_of_threeDMYes (h : ThreeDMYes I) :
    ∃ x : Fin (tCount I) → ZMod 2,
      hammingNorm x = I.1 ∧ Matrix.vecMul x (incidence I) = fun _ => 1 := by
  classical
  obtain ⟨A, hA1, hA2⟩ := h
  let x : Fin (tCount I) → ZMod 2 := fun r =>
    if A.assigned ((triples I).get r).1 = some ((triples I).get r).2 then 1 else 0
  have hsupp : ∀ r, r ∈ supp x ↔
      A.assigned ((triples I).get r).1 = some ((triples I).get r).2 := by
    intro r
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, x]
    split_ifs with h <;> simp [h]
  have hA : ∀ a : Fin I.1, ((supp x).filter fun r : Fin (tCount I) => ((triples I).get r).1 = a).card = 1 := by
    intro a
    obtain ⟨s, d, hsd⟩ := hA1 a
    have hedge := hA2 a s d hsd
    obtain ⟨r, hr⟩ := exists_get_of_edge I a s d hedge
    rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    refine Finset.ext fun (r' : Fin (tCount I)) => ?_
    rw [Finset.mem_filter, Finset.mem_singleton, hsupp]
    constructor
    · rintro ⟨h1, h2⟩
      apply get_injective I
      show (triples I).get r' = (triples I).get r
      rw [h2] at h1
      rw [hsd] at h1
      have := Option.some.inj h1
      rw [hr]
      exact Prod.ext h2 this.symm
    · rintro rfl
      rw [hr]
      exact ⟨hsd, rfl⟩
  have hcard : (supp x).card = I.1 := by
    rw [← card_sum_eq I, Finset.sum_congr rfl (fun a _ => hA a)]
    simp
  have hB : ∀ b : Fin I.1, ((supp x).filter fun r : Fin (tCount I) => ((triples I).get r).2.1 = b).card = 1 := by
    apply fibers_eq_one_of_injOn (supp x) I.1 _ ?_ hcard.ge
    intro r hr r' hr' h
    rw [Finset.mem_coe, hsupp] at hr hr'
    have e1 : A.assigned ((triples I).get r).1 =
        some (((triples I).get r).2.1, ((triples I).get r).2.2) := hr
    have h' : ((triples I).get r).2.1 = ((triples I).get r').2.1 := h
    have e2 : A.assigned ((triples I).get r').1 =
        some (((triples I).get r).2.1, ((triples I).get r').2.2) := by
      rw [h']; exact hr'
    have hb := A.store_unique e1 e2
    apply get_injective I
    show (triples I).get r = (triples I).get r'
    have : some ((triples I).get r).2 = some ((triples I).get r').2 := by
      rw [← hr, ← hr', hb]
    exact Prod.ext hb (Option.some.inj this)
  have hC : ∀ c : Fin I.1, ((supp x).filter fun r : Fin (tCount I) => ((triples I).get r).2.2 = c).card = 1 := by
    apply fibers_eq_one_of_injOn (supp x) I.1 _ ?_ hcard.ge
    intro r hr r' hr' h
    rw [Finset.mem_coe, hsupp] at hr hr'
    have e1 : A.assigned ((triples I).get r).1 =
        some (((triples I).get r).2.1, ((triples I).get r).2.2) := hr
    have h' : ((triples I).get r).2.2 = ((triples I).get r').2.2 := h
    have e2 : A.assigned ((triples I).get r').1 =
        some (((triples I).get r').2.1, ((triples I).get r).2.2) := by
      rw [h']; exact hr'
    have hb := A.courier_unique e1 e2
    apply get_injective I
    show (triples I).get r = (triples I).get r'
    have : some ((triples I).get r).2 = some ((triples I).get r').2 := by
      rw [← hr, ← hr', hb]
    exact Prod.ext hb (Option.some.inj this)
  refine ⟨x, ?_, vecMul_eq_one_of_fibers I x hA hB hC⟩
  rw [hammingNorm_eq_card_supp]; exact hcard

/-- the backward direction, from a vector of weight at most `n` -/
theorem threeDMYes_of_vec (x : Fin (tCount I) → ZMod 2) (hx : hammingNorm x ≤ I.1)
    (hxB : Matrix.vecMul x (incidence I) = fun _ => 1) : ThreeDMYes I := by
  classical
  obtain ⟨oA, oB, oC⟩ := fibers_odd_of_vecMul_eq_one I x hxB
  have hcard : (supp x).card ≤ I.1 := by rw [← hammingNorm_eq_card_supp]; exact hx
  have hA := fibers_eq_one_of_odd (supp x) I.1 _ oA hcard
  have hB := fibers_eq_one_of_odd (supp x) I.1 _ oB hcard
  have hC := fibers_eq_one_of_odd (supp x) I.1 _ oC hcard
  have hA' := fun a => exists_unique_of_card_one _ _ (hA a)
  have hB' := fun b => exists_unique_of_card_one _ _ (hB b)
  have hC' := fun c => exists_unique_of_card_one _ _ (hC c)
  choose ra hra using hA'
  refine ⟨{ assigned := fun a => some ((triples I).get (ra a)).2,
            store_unique := ?_, courier_unique := ?_ }, ?_, ?_⟩
  · intro b₁ b₂ s d₁ d₂ h1 h2
    simp only [Option.some.injEq] at h1 h2
    have u := (hB' s).unique ⟨(hra b₁).1.1, by rw [h1]⟩ ⟨(hra b₂).1.1, by rw [h2]⟩
    calc b₁ = ((triples I).get (ra b₁)).1 := (hra b₁).1.2.symm
      _ = ((triples I).get (ra b₂)).1 := by rw [u]
      _ = b₂ := (hra b₂).1.2
  · intro b₁ b₂ s₁ s₂ d h1 h2
    simp only [Option.some.injEq] at h1 h2
    have u := (hC' d).unique ⟨(hra b₁).1.1, by rw [h1]⟩ ⟨(hra b₂).1.1, by rw [h2]⟩
    calc b₁ = ((triples I).get (ra b₁)).1 := (hra b₁).1.2.symm
      _ = ((triples I).get (ra b₂)).1 := by rw [u]
      _ = b₂ := (hra b₂).1.2
  · intro b; exact ⟨_, _, rfl⟩
  · intro b s d h
    simp only [Allocation.Trades, Option.some.injEq] at h
    have := edge_of_get I (ra b)
    rw [(hra b).1.2, h] at this
    exact this

theorem matching_iff_rows_sum_ones' :
    ThreeDMYes I ↔ ∃ x : Fin (tCount I) → ZMod 2,
      hammingNorm x = I.1 ∧ Matrix.vecMul x (incidence I) = fun _ => 1 :=
  ⟨exists_vec_of_threeDMYes I, fun ⟨x, hx, hxB⟩ => threeDMYes_of_vec I x hx.le hxB⟩

theorem coset_reduction_iff' : ThreeDMYes I ↔ CosetWeightsYes (cosetOf3DM I) :=
  ⟨fun h => by
    obtain ⟨x, hx, hxB⟩ := exists_vec_of_threeDMYes I h
    exact ⟨x, hx.le, hxB⟩,
   fun ⟨x, hx, hxB⟩ => threeDMYes_of_vec I x hx hxB⟩


lemma hammingNorm_eq_sum {ι : Type} [Fintype ι] (y : ι → ZMod 2) :
    hammingNorm y = ∑ i, if y i ≠ 0 then 1 else 0 := by
  unfold hammingNorm; rw [Finset.card_filter]

lemma hammingNorm_split (t m : ℕ) (x : Fin (t + m) → ZMod 2) :
    hammingNorm x = hammingNorm (fun i : Fin t => x (Fin.castAdd m i)) +
      hammingNorm (fun i : Fin m => x (Fin.natAdd t i)) := by
  simp only [hammingNorm_eq_sum]; rw [Fin.sum_univ_add]

lemma vecMul_subspaceMatrix (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2)
    (j : Fin (3 * I.1 * (tCount I + 1))) :
    Matrix.vecMul x (subspaceMatrix I) j =
      Matrix.vecMul (firstPart I x) (subspaceTop I) j + lastPart I x j := by
  simp only [Matrix.vecMul, dotProduct, subspaceMatrix, firstPart, lastPart]
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl; intro i _
    rw [Matrix.of_apply]
    have hl : Fin.append (subspaceTop I) (1 : Matrix (Fin (3 * I.1 * (tCount I + 1)))
        (Fin (3 * I.1 * (tCount I + 1))) (ZMod 2)) (Fin.castAdd _ i) = subspaceTop I i :=
      Fin.append_left _ _ i
    rw [hl]
  · have hr : ∀ i, Fin.append (subspaceTop I) (1 : Matrix (Fin (3 * I.1 * (tCount I + 1)))
        (Fin (3 * I.1 * (tCount I + 1))) (ZMod 2)) (Fin.natAdd _ i) =
          (1 : Matrix (Fin (3 * I.1 * (tCount I + 1))) (Fin (3 * I.1 * (tCount I + 1))) (ZMod 2)) i :=
      fun i => Fin.append_right _ _ i
    simp_rw [Matrix.of_apply, hr]
    simp [Matrix.one_apply]

lemma lastPart_eq (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2)
    (hx : Matrix.vecMul x (subspaceMatrix I) = 0) :
    lastPart I x = Matrix.vecMul (firstPart I x) (subspaceTop I) := by
  funext j
  have := congrFun hx j
  rw [vecMul_subspaceMatrix, Pi.zero_apply] at this
  rw [eq_neg_of_add_eq_zero_right this, ZMod.neg_eq_self_mod_two]

lemma vecMul_top_left (x₀ : Fin (tCount I) → ZMod 2) (j : Fin (3 * I.1 * (tCount I + 1)))
    (i : Fin (3 * I.1)) (hij : j.val = i.val) :
    Matrix.vecMul x₀ (subspaceTop I) j = Matrix.vecMul x₀ (incidence I) i := by
  simp only [Matrix.vecMul, dotProduct, subspaceTop]
  have hj : j.val < 3 * I.1 := hij ▸ i.isLt
  apply Finset.sum_congr rfl; intro r _; rw [dif_pos hj]
  congr 2; exact Fin.ext hij

lemma vecMul_top_right (x₀ : Fin (tCount I) → ZMod 2) (j : Fin (3 * I.1 * (tCount I + 1)))
    (q : Fin (3 * I.1)) (r : Fin (tCount I)) (hj : j.val = 3 * I.1 + (r.val + tCount I * q.val)) :
    Matrix.vecMul x₀ (subspaceTop I) j = x₀ r := by
  simp only [Matrix.vecMul, dotProduct, subspaceTop]
  have hj' : ¬ j.val < 3 * I.1 := by omega
  simp_rw [dif_neg hj']
  have key : ∀ r' : Fin (tCount I), ((j.val - 3 * I.1) % tCount I = r'.val) ↔ r' = r := by
    intro r'
    rw [hj, Nat.add_sub_cancel_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]
    exact ⟨fun h => Fin.ext h.symm, fun h => by rw [h]⟩
  simp_rw [key]
  simp [Finset.sum_ite_eq']

lemma hammingNorm_vecMul_top (x₀ : Fin (tCount I) → ZMod 2) :
    hammingNorm (Matrix.vecMul x₀ (subspaceTop I)) =
      hammingNorm (Matrix.vecMul x₀ (incidence I)) + 3 * I.1 * hammingNorm x₀ := by
  have hc : 3 * I.1 + 3 * I.1 * tCount I = 3 * I.1 * (tCount I + 1) := by ring
  rw [hammingNorm_eq_sum, ← Equiv.sum_comp (finCongr hc), Fin.sum_univ_add]
  congr 1
  · rw [hammingNorm_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [vecMul_top_left I x₀ _ i (by simp)]
  · rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    have : ∀ (q : Fin (3 * I.1)) (r : Fin (tCount I)),
        (if Matrix.vecMul x₀ (subspaceTop I)
            (finCongr hc (Fin.natAdd (3 * I.1) (finProdFinEquiv (q, r)))) ≠ 0 then 1 else 0) =
          if x₀ r ≠ 0 then 1 else 0 := by
      intro q r
      rw [vecMul_top_right I x₀ _ q r (by simp; ring)]
    simp_rw [this]
    rw [← hammingNorm_eq_sum]
    simp

theorem weight_identity' (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2)
    (hx : Matrix.vecMul x (subspaceMatrix I) = 0) :
    hammingNorm (lastPart I x) =
        hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) +
          3 * I.1 * hammingNorm (firstPart I x) ∧
      hammingNorm x =
        hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) +
          (3 * I.1 + 1) * hammingNorm (firstPart I x) := by
  have h1 : hammingNorm (lastPart I x) =
      hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) +
        3 * I.1 * hammingNorm (firstPart I x) := by
    rw [lastPart_eq I x hx, hammingNorm_vecMul_top]
  refine ⟨h1, ?_⟩
  have h2 := hammingNorm_split (tCount I) (3 * I.1 * (tCount I + 1)) x
  change hammingNorm x = hammingNorm (firstPart I x) + hammingNorm (lastPart I x) at h2
  rw [h2, h1]; ring

theorem weight_quotient_remainder' (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2)
    (hx : Matrix.vecMul x (subspaceMatrix I) = 0) :
    hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) ≤ 3 * I.1 ∧
      hammingNorm (firstPart I x) = hammingNorm x / (3 * I.1 + 1) ∧
      hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) = hammingNorm x % (3 * I.1 + 1) ∧
      (hammingNorm x = 3 * I.1 ^ 2 + 4 * I.1 →
        hammingNorm (firstPart I x) = I.1 ∧
          hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) = 3 * I.1) := by
  obtain ⟨-, h2⟩ := weight_identity' I x hx
  have hle : hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) ≤ 3 * I.1 := by
    have := hammingNorm_le_card_fintype (x := Matrix.vecMul (firstPart I x) (incidence I))
    simpa using this
  have hlt : hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) < 3 * I.1 + 1 := by omega
  have hdiv : hammingNorm x / (3 * I.1 + 1) = hammingNorm (firstPart I x) := by
    rw [h2, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlt, zero_add]
  have hmod : hammingNorm x % (3 * I.1 + 1) =
      hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) := by
    rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  refine ⟨hle, hdiv.symm, hmod.symm, fun hw => ?_⟩
  have e1 : 3 * I.1 ^ 2 + 4 * I.1 = 3 * I.1 + (3 * I.1 + 1) * I.1 := by ring
  rw [hw, e1, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add] at hdiv
  rw [hw, e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)] at hmod
  exact ⟨hdiv.symm, hmod.symm⟩


lemma hammingNorm_const_one (m : ℕ) : hammingNorm (fun _ : Fin m => (1 : ZMod 2)) = m := by
  rw [hammingNorm_eq_sum]; simp

lemma eq_one_of_hammingNorm_eq_card (m : ℕ) (y : Fin m → ZMod 2) (hy : hammingNorm y = m) :
    y = fun _ => 1 := by
  have h : (Finset.univ.filter fun i => y i ≠ 0) = Finset.univ := by
    rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
    exact hy
  funext i
  have hi : i ∈ Finset.univ.filter fun i => y i ≠ 0 := by rw [h]; exact Finset.mem_univ i
  rw [Finset.mem_filter] at hi
  rcases zmod2_cases (y i) with h0 | h1
  · exact absurd h0 hi.2
  · exact h1

theorem subspace_reduction_iff' : ThreeDMYes I ↔ SubspaceWeightsYes (subspaceOf3DM I) := by
  constructor
  · intro h
    obtain ⟨x₀, hx₀, hxB⟩ := exists_vec_of_threeDMYes I h
    let x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2 :=
      Fin.append x₀ (Matrix.vecMul x₀ (subspaceTop I))
    have hfirst : firstPart I x = x₀ := by
      funext i; simp only [firstPart, x, Fin.append_left]
    have hlast : lastPart I x = Matrix.vecMul x₀ (subspaceTop I) := by
      funext i; simp only [lastPart, x, Fin.append_right]
    have hxA : Matrix.vecMul x (subspaceMatrix I) = 0 := by
      funext j
      rw [vecMul_subspaceMatrix, hfirst, hlast, Pi.zero_apply]
      exact (show ∀ a : ZMod 2, a + a = 0 by decide) _
    refine ⟨x, ?_, hxA⟩
    show hammingNorm x = 3 * I.1 ^ 2 + 4 * I.1
    obtain ⟨-, h2⟩ := weight_identity' I x hxA
    rw [h2, hfirst, hxB, hammingNorm_const_one, hx₀]; ring
  · rintro ⟨x, hx, hxA⟩
    change hammingNorm x = 3 * I.1 ^ 2 + 4 * I.1 at hx
    obtain ⟨-, -, -, h4⟩ := weight_quotient_remainder' I x hxA
    obtain ⟨h0, hB⟩ := h4 hx
    have := eq_one_of_hammingNorm_eq_card (3 * I.1) _ hB
    exact threeDMYes_of_vec I (firstPart I x) h0.le this

end IntractableCoding.Weights

open IntractableCoding.Weights PricingWithTips in
theorem solution (I : ThreeDMInstance) :
    ThreeDMYes I ↔ SubspaceWeightsYes (subspaceOf3DM I) :=
  subspace_reduction_iff' I
