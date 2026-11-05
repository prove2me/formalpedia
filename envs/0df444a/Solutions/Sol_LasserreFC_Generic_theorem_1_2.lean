-- Prove2me | solution 1 for LasserreFC.Generic.theorem_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:37:31.296146+00:00
-- url     : https://prove2.me/submissions/9e830b3b-5d94-469a-b036-e518fedcff3b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LasserreFC_Generic_Setting
import Definitions.Def_LasserreFC_Generic_Homog
import Definitions.Def_LasserreFC_Generic_Cond43
import Theorems.Thm_LasserreFC_Generic_proposition_4_1
import Theorems.Thm_LasserreFC_Generic_proposition_4_2
import Theorems.Thm_LasserreFC_Generic_proposition_4_5
import Theorems.Thm_LasserreFC_Generic_appendix_A_R
import Theorems.Thm_LasserreFC_Generic_appendix_A_D
import Theorems.Thm_LasserreFC_Generic_discriminant_2_1
import Theorems.Thm_LasserreFC_Generic_discriminant_generic

namespace LasserreFC.Generic.T12Red

open MvPolynomial LasserreFC.Generic

variable {n m1 m2 : ℕ}

abbrev Slot (m1 m2 : ℕ) : Type := Option (Fin m1 ⊕ Fin m2)

def slotPoly (P : POP n m1 m2) : Slot m1 m2 → MvPolynomial (Fin n) ℝ
  | none => P.f
  | some (Sum.inl i) => P.h i
  | some (Sum.inr j) => P.g j

def slotDeg (d0 : ℕ) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) : Slot m1 m2 → ℕ
  | none => d0
  | some (Sum.inl i) => d i
  | some (Sum.inr j) => d' j

def slotVar : Slot m1 m2 → (Fin n →₀ ℕ) → CoefIdx n m1 m2
  | none, α => Sum.inl α
  | some (Sum.inl i), α => Sum.inr (Sum.inl (i, α))
  | some (Sum.inr j), α => Sum.inr (Sum.inr (j, α))

def idxSlot : CoefIdx n m1 m2 → Slot m1 m2 × (Fin n →₀ ℕ)
  | Sum.inl α => (none, α)
  | Sum.inr (Sum.inl (i, α)) => (some (Sum.inl i), α)
  | Sum.inr (Sum.inr (j, α)) => (some (Sum.inr j), α)

lemma slotVar_idxSlot (v : CoefIdx n m1 m2) : slotVar (idxSlot v).1 (idxSlot v).2 = v := by
  rcases v with α | ⟨i, α⟩ | ⟨j, α⟩ <;> rfl

lemma coeffs_slotVar (P : POP n m1 m2) (t : Slot m1 m2) (α : Fin n →₀ ℕ) :
    coeffs P (slotVar t α) = (slotPoly P t).coeff α := by
  rcases t with _ | i | j <;> rfl

lemma coeffs_eq (P : POP n m1 m2) (v : CoefIdx n m1 m2) :
    coeffs P v = (slotPoly P (idxSlot v).1).coeff (idxSlot v).2 := by
  conv_lhs => rw [← slotVar_idxSlot v]
  exact coeffs_slotVar P _ _

lemma slotDeg_le {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ} {P : POP n m1 m2}
    (h : P.Admissible d0 d d') (t : Slot m1 m2) :
    (slotPoly P t).totalDegree ≤ slotDeg d0 d d' t := by
  rcases t with _ | i | j
  · exact h.1
  · exact h.2.1 i
  · exact h.2.2 j

lemma slotDeg_pos {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ} (hd0 : 0 < d0) (hd : ∀ i, 0 < d i)
    (hd' : ∀ j, 0 < d' j) (t : Slot m1 m2) : 0 < slotDeg d0 d d' t := by
  rcases t with _ | i | j
  · exact hd0
  · exact hd i
  · exact hd' j

def ofSlots (E : Slot m1 m2 → MvPolynomial (Fin n) ℝ) : POP n m1 m2 :=
  ⟨E none, fun i => E (some (Sum.inl i)), fun j => E (some (Sum.inr j))⟩

lemma slotPoly_ofSlots (E : Slot m1 m2 → MvPolynomial (Fin n) ℝ) (t : Slot m1 m2) :
    slotPoly (ofSlots E) t = E t := by
  rcases t with _ | i | j <;> rfl

lemma adm_ofSlots {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ}
    (E : Slot m1 m2 → MvPolynomial (Fin n) ℝ) (h : ∀ t, (E t).totalDegree ≤ slotDeg d0 d d' t) :
    (ofSlots E).Admissible d0 d d' :=
  ⟨h none, fun i => h (some (Sum.inl i)), fun j => h (some (Sum.inr j))⟩

/-- the pull-back of a polynomial in the coefficients of a tuple along a slot assignment -/
noncomputable def pull {τ : Type*} (s : τ → Slot m1 m2)
    (R : MvPolynomial (τ × (Fin n →₀ ℕ)) ℝ) : MvPolynomial (CoefIdx n m1 m2) ℝ :=
  rename (fun c => slotVar (s c.1) c.2) R

lemma eval_pull {τ : Type*} (P : POP n m1 m2) (s : τ → Slot m1 m2)
    (R : MvPolynomial (τ × (Fin n →₀ ℕ)) ℝ) :
    eval (coeffs P) (pull s R) = eval (tupleCoeffs (fun c => slotPoly P (s c))) R := by
  unfold pull
  rw [eval_rename]
  have : (coeffs P ∘ fun c : τ × (Fin n →₀ ℕ) => slotVar (s c.1) c.2) =
      tupleCoeffs (fun c => slotPoly P (s c)) := funext fun c => coeffs_slotVar P _ _
  rw [this]

lemma realize {τ : Type*} {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ}
    (s : τ → Slot m1 m2) (hs : Function.Injective s) (Q : τ → MvPolynomial (Fin n) ℝ)
    (hQ : ∀ c, (Q c).totalDegree ≤ slotDeg d0 d d' (s c)) :
    ∃ P : POP n m1 m2, P.Admissible d0 d d' ∧ (fun c => slotPoly P (s c)) = Q := by
  classical
  refine ⟨ofSlots (Function.extend s Q 0), adm_ofSlots _ ?_, ?_⟩
  · intro t
    by_cases ht : ∃ c, s c = t
    · obtain ⟨c, rfl⟩ := ht
      rw [hs.extend_apply]
      exact hQ c
    · rw [Function.extend_apply' _ _ _ ht]
      simp
  · funext c
    rw [slotPoly_ofSlots, hs.extend_apply]

/-- "`A` holds off a proper Zariski-closed subset of the admissible data" -/
def GenGood (d0 : ℕ) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) (A : POP n m1 m2 → Prop) : Prop :=
  ∃ ϕ : MvPolynomial (CoefIdx n m1 m2) ℝ,
    (∃ P : POP n m1 m2, P.Admissible d0 d d' ∧ eval (coeffs P) ϕ ≠ 0) ∧
    ∀ P : POP n m1 m2, P.Admissible d0 d d' → eval (coeffs P) ϕ ≠ 0 → A P

lemma genGood_of {τ : Type*} {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ}
    (s : τ → Slot m1 m2) (hs : Function.Injective s)
    (R : MvPolynomial (τ × (Fin n →₀ ℕ)) ℝ) (B : (τ → MvPolynomial (Fin n) ℝ) → Prop)
    (A : POP n m1 m2 → Prop)
    (hgood : ∀ Q : τ → MvPolynomial (Fin n) ℝ, (∀ c, (Q c).totalDegree ≤ slotDeg d0 d d' (s c)) →
      eval (tupleCoeffs Q) R ≠ 0 → B Q)
    (hgen : ∃ Q : τ → MvPolynomial (Fin n) ℝ, (∀ c, (Q c).totalDegree ≤ slotDeg d0 d d' (s c)) ∧
      eval (tupleCoeffs Q) R ≠ 0)
    (hA : ∀ P : POP n m1 m2, P.Admissible d0 d d' → B (fun c => slotPoly P (s c)) → A P) :
    GenGood d0 d d' A := by
  refine ⟨pull s R, ?_, ?_⟩
  · obtain ⟨Q, hQ, hne⟩ := hgen
    obtain ⟨P, hP, hPQ⟩ := realize s hs Q hQ
    refine ⟨P, hP, ?_⟩
    rw [eval_pull, hPQ]
    exact hne
  · intro P hP hne
    rw [eval_pull] at hne
    exact hA P hP (hgood _ (fun c => slotDeg_le hP (s c)) hne)

lemma genGood_mono {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ} {A B : POP n m1 m2 → Prop}
    (h : GenGood d0 d d' A) (hAB : ∀ P, P.Admissible d0 d d' → A P → B P) : GenGood d0 d d' B := by
  obtain ⟨ϕ, hg, hgood⟩ := h
  exact ⟨ϕ, hg, fun P hP hne => hAB P hP (hgood P hP hne)⟩

/-- simultaneous genericity: finitely many polynomials, each nonzero at some admissible
datum, are simultaneously nonzero at one admissible datum. -/
lemma simul {ι : Type*} [Fintype ι] {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ}
    (ϕ : ι → MvPolynomial (CoefIdx n m1 m2) ℝ)
    (hgen : ∀ l, ∃ P : POP n m1 m2, P.Admissible d0 d d' ∧ eval (coeffs P) (ϕ l) ≠ 0) :
    ∃ P₀ : POP n m1 m2, P₀.Admissible d0 d d' ∧ ∀ l, eval (coeffs P₀) (ϕ l) ≠ 0 := by
  classical
  choose Pl hPl hne using hgen
  let S : Slot m1 m2 → Finset (Fin n →₀ ℕ) :=
    fun t => Finset.univ.biUnion (fun l => (slotPoly (Pl l) t).support)
  let T : (CoefIdx n m1 m2 → ℝ) → POP n m1 m2 :=
    fun x => ofSlots (fun t => ∑ α ∈ S t, monomial α (x (slotVar t α)))
  have hTadm : ∀ x, (T x).Admissible d0 d d' := by
    intro x
    apply adm_ofSlots
    intro t
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le ?_)
    intro α hα
    refine (totalDegree_monomial_le _ _).trans ?_
    obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.mp hα
    exact (le_totalDegree hl).trans (slotDeg_le (hPl l) t)
  have hTcoeff : ∀ x v, coeffs (T x) v =
      if (idxSlot v).2 ∈ S (idxSlot v).1 then x v else 0 := by
    intro x v
    rw [coeffs_eq, slotPoly_ofSlots, coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs <;> simp [slotVar_idxSlot]
  let g : CoefIdx n m1 m2 → MvPolynomial (CoefIdx n m1 m2) ℝ :=
    fun v => if (idxSlot v).2 ∈ S (idxSlot v).1 then X v else 0
  have hevalg : ∀ x l, eval x (bind₁ g (ϕ l)) = eval (coeffs (T x)) (ϕ l) := by
    intro x l
    have h1 := aeval_bind₁ x g (ϕ l)
    rw [aeval_eq_eval, aeval_eq_eval] at h1
    have h2 : (fun i => (aeval x) (g i)) = coeffs (T x) := by
      funext v
      rw [hTcoeff, aeval_eq_eval]
      simp only [g]
      split_ifs <;> simp
    rw [h1, ← h2]
    simp [aeval_eq_eval]
  have hTfix : ∀ l, coeffs (T (coeffs (Pl l))) = coeffs (Pl l) := by
    intro l
    funext v
    rw [hTcoeff]
    split_ifs with hv
    · rfl
    · rw [coeffs_eq]
      by_contra hc
      apply hv
      exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, mem_support_iff.mpr (Ne.symm hc)⟩
  have hψ : ∀ l, bind₁ g (ϕ l) ≠ 0 := by
    intro l h0
    have := hevalg (coeffs (Pl l)) l
    rw [h0, hTfix, map_zero] at this
    exact hne l this.symm
  have hprod : (∏ l, bind₁ g (ϕ l)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun l _ => hψ l)
  obtain ⟨x, hx⟩ : ∃ x, eval x (∏ l, bind₁ g (ϕ l)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hprod (MvPolynomial.funext (fun x => by rw [hcon x, map_zero]))
  refine ⟨T x, hTadm x, fun l => ?_⟩
  rw [← hevalg]
  rw [map_prod] at hx
  exact (Finset.prod_ne_zero_iff.mp hx) l (Finset.mem_univ _)

lemma genGood_forall {ι : Type*} [Fintype ι] {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ}
    (A : ι → POP n m1 m2 → Prop) (h : ∀ l, GenGood d0 d d' (A l)) :
    GenGood d0 d d' (fun P => ∀ l, A l P) := by
  classical
  choose ϕ hg hgood using h
  refine ⟨∏ l, ϕ l, ?_, ?_⟩
  · obtain ⟨P₀, hP₀, hne⟩ := simul ϕ hg
    refine ⟨P₀, hP₀, ?_⟩
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun l _ => hne l)
  · intro P hP hne l
    rw [map_prod] at hne
    exact hgood l P hP ((Finset.prod_ne_zero_iff.mp hne) l (Finset.mem_univ _))

lemma genGood_and {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ} {A B : POP n m1 m2 → Prop}
    (hA : GenGood d0 d d' A) (hB : GenGood d0 d d' B) : GenGood d0 d d' (fun P => A P ∧ B P) := by
  have := genGood_forall (ι := Bool) (fun b => if b then A else B) (fun b => by cases b <;> simpa)
  refine genGood_mono this (fun P _ h => ⟨by simpa using h true, by simpa using h false⟩)

end LasserreFC.Generic.T12Red

namespace LasserreFC.Generic.T12Red

open MvPolynomial LasserreFC.Generic

variable {n m1 m2 : ℕ}

lemma sys45_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (D0 : ℕ)
    (p0 : MvPolynomial (Fin n) ℝ) (D : ι → ℕ) (p : ι → MvPolynomial (Fin n) ℝ) (Dq : ℕ)
    (q : MvPolynomial (Fin n) ℝ) :
    Sys45 D0 p0 (fun i => D (e i)) (fun i => p (e i)) Dq q ↔ Sys45 D0 p0 D p Dq q := by
  unfold Sys45
  have hmat : ∀ xt, gradMat45 D0 p0 (fun i => D (e i)) (fun i => p (e i)) xt =
      (gradMat45 D0 p0 D p xt).submatrix (Equiv.refl _) (e.optionCongr) := by
    intro xt; ext k c; cases c <;> rfl
  have hcard : Fintype.card ι' = Fintype.card ι := Fintype.card_congr e
  simp only [hmat, Matrix.rank_submatrix, hcard]
  constructor
  · rintro ⟨xt, h0, hr, hp, hq⟩
    exact ⟨xt, h0, hr, fun i => by simpa using hp (e.symm i), hq⟩
  · rintro ⟨xt, h0, hr, hp, hq⟩
    exact ⟨xt, h0, hr, fun i => hp (e i), hq⟩

lemma sys410_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (D0 : ℕ)
    (p0 : MvPolynomial (Fin n) ℝ) (D : ι → ℕ) (p : ι → MvPolynomial (Fin n) ℝ) :
    Sys410 D0 p0 (fun i => D (e i)) (fun i => p (e i)) ↔ Sys410 D0 p0 D p := by
  unfold Sys410
  have hmat : ∀ xt y, Ptilde D0 p0 (fun i => D (e i)) (fun i => p (e i)) xt y =
      (Ptilde D0 p0 D p xt y).submatrix (Equiv.refl _) (Equiv.sumCongr e.optionCongr e) := by
    intro xt y
    ext k c
    rcases k with k | k <;> rcases c with (_ | c) | c <;> rfl
  have hcard : Fintype.card ι' = Fintype.card ι := Fintype.card_congr e
  simp only [hmat, Matrix.rank_submatrix, hcard]
  constructor
  · rintro ⟨xt, h0, y, hy, hr, hp, hq⟩
    exact ⟨xt, h0, y, hy, hr, fun i => by simpa using hp (e.symm i),
      fun i => by simpa using hq (e.symm i)⟩
  · rintro ⟨xt, h0, y, hy, hr, hp, hq⟩
    exact ⟨xt, h0, y, hy, hr, fun i => hp (e i), fun i => hq (e i)⟩

/-- the slot of a constraint `h_i` or `g_j` (`j ∈ J`) -/
def slotOf (J : Finset (Fin m2)) : Fin m1 ⊕ J → Slot m1 m2 :=
  Sum.elim (fun i => some (Sum.inl i)) (fun j => some (Sum.inr j.1))

lemma slotOf_injective (J : Finset (Fin m2)) : Function.Injective (slotOf (m1 := m1) J) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · simp only [slotOf, Sum.elim_inl, Option.some.injEq, Sum.inl.injEq] at hab; rw [hab]
  · simp [slotOf] at hab
  · simp [slotOf] at hab
  · simp only [slotOf, Sum.elim_inr, Option.some.injEq, Sum.inr.injEq] at hab
    rw [Subtype.ext hab]

lemma slotOf_ne_none (J : Finset (Fin m2)) (e : Fin m1 ⊕ J) : slotOf J e ≠ none := by
  rcases e with e | e <;> simp [slotOf]

lemma slotPoly_slotOf (P : POP n m1 m2) (J : Finset (Fin m2)) (e : Fin m1 ⊕ J) :
    slotPoly P (slotOf J e) = consPoly P J e := by
  rcases e with e | e <;> rfl

lemma slotDeg_slotOf (d0 : ℕ) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) (J : Finset (Fin m2))
    (e : Fin m1 ⊕ J) : slotDeg d0 d d' (slotOf J e) = consDeg d d' J e := by
  rcases e with e | e <;> rfl

noncomputable def eJ (J : Finset (Fin m2)) : Fin (m1 + J.card) ≃ Fin m1 ⊕ J :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) J.equivFin.symm)

lemma aeval_ofReal (u : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) :
    aeval (fun k => (u k : ℂ)) p = ((eval u p : ℝ) : ℂ) := by
  rw [show (fun k => (u k : ℂ)) = (algebraMap ℝ ℂ) ∘ u from rfl, aeval_algebraMap_apply]
  rfl

section atoms

variable {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ}

/-- `m₁ > n`: generically `K = ∅` (a resultant of `h₁, …, h_{n+1}`). -/
lemma atom_big (hm : n < m1) (hd0 : 0 < d0) (hd : ∀ i, 0 < d i) (hd' : ∀ j, 0 < d' j) :
    GenGood d0 d d' (fun P : POP n m1 m2 => ∀ u, u ∉ P.K) := by
  classical
  let s : Fin (n + 2) → Slot m1 m2 :=
    Fin.cons none (fun i : Fin (n + 1) => some (Sum.inl (Fin.castLE hm i)))
  have hs : Function.Injective s := by
    refine Fin.cons_injective_iff.mpr ⟨?_, ?_⟩
    · rintro ⟨i, hi⟩; simp at hi
    · intro a b hab
      simp only [Option.some.injEq, Sum.inl.injEq] at hab
      exact Fin.castLE_injective _ hab
  let dd : Fin (n + 2) → ℕ := fun c => slotDeg d0 d d' (s c)
  have hdd : ∀ c, 0 < dd c := fun c => slotDeg_pos hd0 hd hd' _
  obtain ⟨R, hR⟩ := proposition_4_1 (n := n) (k := n) le_rfl dd
  refine genGood_of s hs R
    (fun Q => ¬ Sys44 (Q 0) (fun i : Fin n => Q i.succ.castSucc) (Q (Fin.last (n + 1)))) _
    (fun Q hQ hne => (hR Q hQ).2 hne) ?_ ?_
  · obtain ⟨Q, hQ, hns⟩ := appendix_A_R (n := n) (k := n) le_rfl dd hdd
    exact ⟨Q, hQ, fun h0 => hns ((hR Q hQ).1.mp h0)⟩
  · intro P _ hB u hu
    apply hB
    refine ⟨fun k => (u k : ℂ), ?_, ?_, ?_⟩
    · exact (Matrix.rank_le_card_height _).trans (by simp)
    · intro i
      simp only [s]
      rw [← Fin.succ_castSucc, Fin.cons_succ]
      simp only [slotPoly]
      rw [aeval_ofReal, hu.1]
      simp
    · simp only [s]
      rw [← Fin.succ_last, Fin.cons_succ]
      simp only [slotPoly]
      rw [aeval_ofReal, hu.1]
      simp

/-- Condition 4.3 (a) for one `J`, via Proposition 4.1 with `k = n`. -/
lemma atom_a (hm : m1 ≤ n) (hd0 : 0 < d0) (hd : ∀ i, 0 < d i) (hd' : ∀ j, 0 < d' j)
    (J : Finset (Fin m2)) (hJ : J.card = n - m1 + 1) :
    GenGood d0 d d' (fun P : POP n m1 m2 => ¬ ∃ xt : Fin (n + 1) → ℂ, xt ≠ 0 ∧
      ∀ e, eval xt (homog (consDeg d d' J e) (consPoly P J e)) = 0) := by
  classical
  have hc : n + 1 = m1 + J.card := by omega
  let eA : Fin (n + 1) ≃ Fin m1 ⊕ J := (finCongr hc).trans (eJ J)
  let s : Fin (n + 2) → Slot m1 m2 := Fin.cons none (fun i => slotOf J (eA i))
  have hs : Function.Injective s := by
    refine Fin.cons_injective_iff.mpr ⟨?_, ?_⟩
    · rintro ⟨i, hi⟩; exact slotOf_ne_none J _ hi
    · exact (slotOf_injective J).comp eA.injective
  let dd : Fin (n + 2) → ℕ := fun c => slotDeg d0 d d' (s c)
  have hdd : ∀ c, 0 < dd c := fun c => slotDeg_pos hd0 hd hd' _
  obtain ⟨R, hR⟩ := proposition_4_1 (n := n) (k := n) le_rfl dd
  refine genGood_of s hs R
    (fun Q => ¬ Sys45 (dd 0) (Q 0) (fun i : Fin n => dd i.succ.castSucc)
      (fun i : Fin n => Q i.succ.castSucc) (dd (Fin.last (n + 1))) (Q (Fin.last (n + 1)))) _
    (fun Q hQ hne h => hne ((hR Q hQ).1.mpr h)) ?_ ?_
  · obtain ⟨Q, hQ, hns⟩ := appendix_A_R (n := n) (k := n) le_rfl dd hdd
    exact ⟨Q, hQ, fun h0 => hns ((hR Q hQ).1.mp h0)⟩
  · intro P _ hB ⟨xt, hxt, hz⟩
    apply hB
    have hsi : ∀ i : Fin n, s i.succ.castSucc = slotOf J (eA i.castSucc) := by
      intro i; simp only [s]; rw [← Fin.succ_castSucc, Fin.cons_succ]
    have hsl : s (Fin.last (n + 1)) = slotOf J (eA (Fin.last n)) := by
      simp only [s]; rw [← Fin.succ_last, Fin.cons_succ]
    refine ⟨xt, hxt, (Matrix.rank_le_card_height _).trans (by simp), ?_, ?_⟩
    · intro i
      simp only [dd, hsi, slotPoly_slotOf, slotDeg_slotOf]
      exact hz _
    · simp only [dd, hsl, slotPoly_slotOf, slotDeg_slotOf]
      exact hz _

/-- Condition 4.3 (b) for one `J`, via the discriminant of §2.4. -/
lemma atom_b (hm : m1 ≤ n) (hd0 : 0 < d0) (hd : ∀ i, 0 < d i) (hd' : ∀ j, 0 < d' j)
    (J : Finset (Fin m2)) (hJ : J.card ≤ n - m1) :
    GenGood d0 d d' (fun P : POP n m1 m2 => ¬ ∃ xt : Fin (n + 1) → ℂ, xt ≠ 0 ∧
      (∀ e, eval xt (homog (consDeg d d' J e) (consPoly P J e)) = 0) ∧
      (Matrix.of fun (k : Fin (n + 1)) (e : Fin m1 ⊕ J) =>
          hgrad (consDeg d d' J e) (consPoly P J e) xt k).rank < m1 + J.card) := by
  classical
  have hmn : m1 + J.card ≤ n := by omega
  let s : Fin (m1 + J.card) → Slot m1 m2 := fun i => slotOf J (eJ J i)
  have hs : Function.Injective s := (slotOf_injective J).comp (eJ J).injective
  let dd : Fin (m1 + J.card) → ℕ := fun c => slotDeg d0 d d' (s c)
  have hdd : ∀ c, 0 < dd c := fun c => slotDeg_pos hd0 hd hd' _
  obtain ⟨R, hR⟩ := discriminant_2_1 hmn dd
  refine genGood_of s hs R
    (fun Q => ¬ ∃ xt : Fin (n + 1) → ℂ, xt ≠ 0 ∧
            (∀ i, eval xt (homog (dd i) (Q i)) = 0) ∧
            (Matrix.of fun (k : Fin (n + 1)) (i : Fin (m1 + J.card)) =>
              hgrad (dd i) (Q i) xt k).rank < m1 + J.card) _
    (fun Q hQ hne h => hne ((hR Q hQ).mpr h)) ?_ ?_
  · obtain ⟨Q, hQ, hns⟩ := discriminant_generic hmn dd hdd
    exact ⟨Q, hQ, fun h0 => hns ((hR Q hQ).mp h0)⟩
  · intro P _ hB ⟨xt, hxt, hz, hr⟩
    apply hB
    refine ⟨xt, hxt, ?_, ?_⟩
    · intro i
      simp only [dd, s, slotPoly_slotOf, slotDeg_slotOf]
      exact hz _
    · have hmat : (Matrix.of fun (k : Fin (n + 1)) (i : Fin (m1 + J.card)) =>
          hgrad (dd i) ((fun c => slotPoly P (s c)) i) xt k) =
          (Matrix.of fun (k : Fin (n + 1)) (e : Fin m1 ⊕ J) =>
            hgrad (consDeg d d' J e) (consPoly P J e) xt k).submatrix (Equiv.refl _) (eJ J) := by
        ext k i
        simp [dd, s, slotPoly_slotOf, slotDeg_slotOf]
      rw [hmat, Matrix.rank_submatrix]
      exact hr

/-- Condition 4.3 (c) for one `J` and one `c`, via Proposition 4.1. -/
lemma atom_c (hm : m1 ≤ n) (hd0 : 0 < d0) (hd : ∀ i, 0 < d i) (hd' : ∀ j, 0 < d' j)
    (J : Finset (Fin m2)) (hJ : J.card ≤ n - m1) (c : Fin m1 ⊕ J) :
    GenGood d0 d d' (fun P : POP n m1 m2 =>
      ¬ Sys45 d0 P.f (fun e : {e : Fin m1 ⊕ J // e ≠ c} => consDeg d d' J e.1)
        (fun e => consPoly P J e.1) (consDeg d d' J c) (consPoly P J c)) := by
  classical
  let k := Fintype.card {e : Fin m1 ⊕ J // e ≠ c}
  have hk : k ≤ n := by
    have h1 : k < Fintype.card (Fin m1 ⊕ J) := Fintype.card_subtype_lt (x := c) (by simp)
    have h2 : Fintype.card (Fin m1 ⊕ J) = m1 + J.card := by simp
    omega
  let ec : Fin k ≃ {e : Fin m1 ⊕ J // e ≠ c} := (Fintype.equivFin _).symm
  let s : Fin (k + 2) → Slot m1 m2 :=
    Fin.cons none (Fin.snoc (fun i => slotOf J (ec i).1) (slotOf J c))
  have hs : Function.Injective s := by
    refine Fin.cons_injective_iff.mpr ⟨?_, ?_⟩
    · rintro ⟨i, hi⟩
      revert hi
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact slotOf_ne_none J c
      · rw [Fin.snoc_castSucc]; exact slotOf_ne_none J _
    · refine Fin.snoc_injective_iff.mpr ⟨?_, ?_⟩
      · intro a b hab
        exact ec.injective (Subtype.ext (slotOf_injective J hab))
      · rintro ⟨i, hi⟩
        exact (ec i).2 (slotOf_injective J hi)
  let dd : Fin (k + 2) → ℕ := fun c => slotDeg d0 d d' (s c)
  have hdd : ∀ c, 0 < dd c := fun c => slotDeg_pos hd0 hd hd' _
  obtain ⟨R, hR⟩ := proposition_4_1 (n := n) (k := k) hk dd
  refine genGood_of s hs R
    (fun Q => ¬ Sys45 (dd 0) (Q 0) (fun i : Fin k => dd i.succ.castSucc)
      (fun i : Fin k => Q i.succ.castSucc) (dd (Fin.last (k + 1))) (Q (Fin.last (k + 1)))) _
    (fun Q hQ hne h => hne ((hR Q hQ).1.mpr h)) ?_ ?_
  · obtain ⟨Q, hQ, hns⟩ := appendix_A_R (n := n) (k := k) hk dd hdd
    exact ⟨Q, hQ, fun h0 => hns ((hR Q hQ).1.mp h0)⟩
  · intro P _ hB h
    apply hB
    have hs0 : s 0 = none := rfl
    have hsi : ∀ i : Fin k, s i.succ.castSucc = slotOf J (ec i).1 := by
      intro i; simp only [s]; rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.snoc_castSucc]
    have hsl : s (Fin.last (k + 1)) = slotOf J c := by
      simp only [s]; rw [← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
    simp only [dd, hs0, hsi, hsl, slotPoly_slotOf, slotDeg_slotOf]
    exact (sys45_equiv ec d0 P.f (fun e : {e : Fin m1 ⊕ J // e ≠ c} => consDeg d d' J e.1)
      (fun e => consPoly P J e.1) _ _).mpr h

/-- Condition 4.3 (d) for one `J`, via Proposition 4.2. -/
lemma atom_d (hm : m1 ≤ n) (hd0 : 0 < d0) (hd : ∀ i, 0 < d i) (hd' : ∀ j, 0 < d' j)
    (J : Finset (Fin m2)) (hJ : J.card ≤ n - m1) :
    GenGood d0 d d' (fun P : POP n m1 m2 =>
      ¬ Sys410 d0 P.f (consDeg d d' J) (consPoly P J)) := by
  classical
  have hk : m1 + J.card ≤ n := by omega
  let s : Fin (m1 + J.card + 1) → Slot m1 m2 := Fin.cons none (fun i => slotOf J (eJ J i))
  have hs : Function.Injective s := by
    refine Fin.cons_injective_iff.mpr ⟨?_, ?_⟩
    · rintro ⟨i, hi⟩; exact slotOf_ne_none J _ hi
    · exact (slotOf_injective J).comp (eJ J).injective
  let dd : Fin (m1 + J.card + 1) → ℕ := fun c => slotDeg d0 d d' (s c)
  have hdd : ∀ c, 0 < dd c := fun c => slotDeg_pos hd0 hd hd' _
  obtain ⟨R, hR⟩ := proposition_4_2 (n := n) (k := m1 + J.card) hk dd
  refine genGood_of s hs R
    (fun Q => ¬ Sys410 (dd 0) (Q 0) (fun i : Fin (m1 + J.card) => dd i.succ)
      (fun i : Fin (m1 + J.card) => Q i.succ)) _
    (fun Q hQ hne h => hne ((hR Q hQ).1.mpr h)) ?_ ?_
  · obtain ⟨Q, hQ, hns⟩ := appendix_A_D (n := n) (k := m1 + J.card) hk dd hdd
    exact ⟨Q, hQ, fun h0 => hns ((hR Q hQ).1.mp h0)⟩
  · intro P _ hB h
    apply hB
    have hs0 : s 0 = none := rfl
    have hsi : ∀ i, s i.succ = slotOf J (eJ J i) := fun i => Fin.cons_succ _ _ _
    simp only [dd, hs0, hsi, slotPoly_slotOf, slotDeg_slotOf]
    exact (sys410_equiv (eJ J) d0 P.f (consDeg d d' J) (consPoly P J)).mpr h

end atoms

end LasserreFC.Generic.T12Red

namespace LasserreFC.Generic.T12Red

open MvPolynomial LasserreFC.Generic

variable {n m1 m2 : ℕ}

lemma genGood_cond43 {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ} (hm : m1 ≤ n) (hd0 : 0 < d0)
    (hd : ∀ i, 0 < d i) (hd' : ∀ j, 0 < d' j) :
    GenGood d0 d d' (fun P : POP n m1 m2 => Cond43 P d0 d d') := by
  classical
  have ha := genGood_forall (ι := {J : Finset (Fin m2) // J.card = n - m1 + 1})
    (fun J P => ¬ ∃ xt : Fin (n + 1) → ℂ, xt ≠ 0 ∧
      ∀ e, eval xt (homog (consDeg d d' J.1 e) (consPoly P J.1 e)) = 0)
    (fun J => atom_a hm hd0 hd hd' J.1 J.2)
  have hb := genGood_forall (ι := {J : Finset (Fin m2) // J.card ≤ n - m1})
    (fun J (P : POP n m1 m2) => ¬ ∃ xt : Fin (n + 1) → ℂ, xt ≠ 0 ∧
      (∀ e, eval xt (homog (consDeg d d' J.1 e) (consPoly P J.1 e)) = 0) ∧
      (Matrix.of fun (k : Fin (n + 1)) (e : Fin m1 ⊕ J.1) =>
          hgrad (consDeg d d' J.1 e) (consPoly P J.1 e) xt k).rank < m1 + J.1.card)
    (fun J => atom_b hm hd0 hd hd' J.1 J.2)
  have hc := genGood_forall (ι := {J : Finset (Fin m2) // J.card ≤ n - m1})
    (fun J (P : POP n m1 m2) => ∀ c : Fin m1 ⊕ J.1,
      ¬ Sys45 d0 P.f (fun e : {e : Fin m1 ⊕ J.1 // e ≠ c} => consDeg d d' J.1 e.1)
        (fun e => consPoly P J.1 e.1) (consDeg d d' J.1 c) (consPoly P J.1 c))
    (fun J => genGood_forall _ (fun c => atom_c hm hd0 hd hd' J.1 J.2 c))
  have hdd := genGood_forall (ι := {J : Finset (Fin m2) // J.card ≤ n - m1})
    (fun J (P : POP n m1 m2) => ¬ Sys410 d0 P.f (consDeg d d' J.1) (consPoly P J.1))
    (fun J => atom_d hm hd0 hd hd' J.1 J.2)
  refine genGood_mono (genGood_and ha (genGood_and hb (genGood_and hc hdd))) ?_
  rintro P - ⟨h1, h2, h3, h4⟩
  exact ⟨fun J hJ => h1 ⟨J, hJ⟩, fun J hJ => h2 ⟨J, hJ⟩, fun J hJ => h3 ⟨J, hJ⟩,
    fun J hJ => h4 ⟨J, hJ⟩⟩

lemma conclude {d0 : ℕ} {d : Fin m1 → ℕ} {d' : Fin m2 → ℕ} {A : POP n m1 m2 → Prop}
    (h : GenGood d0 d d' A) :
    ∃ (L : ℕ) (ϕ : Fin L → MvPolynomial (CoefIdx n m1 m2) ℝ),
      (∃ P₀ : POP n m1 m2, P₀.Admissible d0 d d' ∧
        ∀ l, MvPolynomial.eval (coeffs P₀) (ϕ l) ≠ 0) ∧
      ∀ P : POP n m1 m2, P.Admissible d0 d d' →
        (∀ l, MvPolynomial.eval (coeffs P) (ϕ l) ≠ 0) → A P := by
  obtain ⟨ϕ, ⟨P₀, hP₀, hne⟩, hgood⟩ := h
  exact ⟨1, fun _ => ϕ, ⟨P₀, hP₀, fun _ => hne⟩, fun P hP h => hgood P hP (h 0)⟩

end LasserreFC.Generic.T12Red

open MvPolynomial LasserreFC.Generic LasserreFC.Generic.T12Red in
theorem solution {n m1 m2 : ℕ} (d0 : ℕ) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ)
    (hd0 : 0 < d0) (hd : ∀ i, 0 < d i) (hd' : ∀ j, 0 < d' j) :
    ∃ (L : ℕ) (ϕ : Fin L → MvPolynomial (CoefIdx n m1 m2) ℝ),
      (∃ P₀ : POP n m1 m2, P₀.Admissible d0 d d' ∧
        ∀ l, MvPolynomial.eval (coeffs P₀) (ϕ l) ≠ 0) ∧
      ∀ P : POP n m1 m2, P.Admissible d0 d d' →
        (∀ l, MvPolynomial.eval (coeffs P) (ϕ l) ≠ 0) →
        ∀ u ∈ P.K, IsLocalMinOn (fun x => eval x P.f) P.K u → OptCond P u := by
  by_cases hm : m1 ≤ n
  · exact conclude (genGood_mono (genGood_cond43 hm hd0 hd hd')
      (fun P hP hC => proposition_4_5 hm P d0 d d' hP hC))
  · exact conclude (genGood_mono (atom_big (lt_of_not_ge hm) hd0 hd hd')
      (fun P _ hK u hu => absurd hu (hK u)))
