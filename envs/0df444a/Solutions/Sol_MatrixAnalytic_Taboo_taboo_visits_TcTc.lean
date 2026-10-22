-- Prove2me | solution 1 for MatrixAnalytic.Taboo.taboo_visits_TcTc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:58:47.627983+00:00
-- url     : https://prove2.me/submissions/f5a23ad6-d2ac-4d34-a0d9-cad38f542ec4

import Mathlib
import Definitions.Def_MatrixAnalytic_Taboo_Chain
import Definitions.Def_MatrixAnalytic_Taboo_TabooMatrices
open MatrixAnalytic.Taboo

open scoped ENNReal


lemma g70ma_pw_snoc {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) {n : ℕ}
    (ω : Fin (n + 1) → S) (k : S) :
    pathWeightE P (Fin.snoc ω k : Fin (n + 2) → S) = pathWeightE P ω * ennP P (ω (Fin.last n)) k := by
  unfold pathWeightE
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma g70ma_pw_cons {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) {n : ℕ}
    (ω : Fin (n + 1) → S) (k : S) :
    pathWeightE P (Fin.cons k ω : Fin (n + 2) → S) = ennP P k (ω 0) * pathWeightE P ω := by
  unfold pathWeightE
  rw [Fin.prod_univ_succ]
  congr 1

/-- tsum over paths of length n+2 split as snoc. -/
lemma g70ma_tsum_snoc {S : Type*} [Countable S] {n : ℕ} (f : (Fin (n + 2) → S) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → S, f ω = ∑' ω : Fin (n + 1) → S, ∑' k : S, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => S)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma g70ma_tsum_cons {S : Type*} [Countable S] {n : ℕ} (f : (Fin (n + 2) → S) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → S, f ω = ∑' k : S, ∑' ω : Fin (n + 1) → S, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => S)).tsum_eq, ENNReal.tsum_prod']
  rfl

open Classical in
lemma g70ma_inD_eq {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (D : Set S) :
    ∀ n : ℕ, ∀ i ∈ D, ∀ j ∈ D,
    (∑' ω : Fin (n + 1) → S,
      if ω 0 = i ∧ ω (Fin.last n) = j ∧ ∀ m : Fin (n + 1), ω m ∈ D then pathWeightE P ω else 0)
      = subPow (ennP P) D n i j := by
  intro n
  induction n with
  | zero =>
    intro i hi j hj
    simp only [subPow]
    rw [← (Equiv.funUnique (Fin 1) S).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    by_cases hij : i = j
    · subst hij
      rw [tsum_eq_single i]
      · simp [hi, pathWeightE]
      · intro b hb; simp [Fin.last, hb]
    · rw [if_neg hij]
      apply ENNReal.tsum_eq_zero.mpr
      intro b
      simp only [Fin.last]
      split_ifs with h
      · exact absurd (h.1.symm.trans (by simpa using h.2.1)) hij
      · rfl
  | succ n ih =>
    intro i hi j hj
    rw [g70ma_tsum_snoc]
    simp only [subPow]
    have : ∀ k : D, subPow (ennP P) D n i k * ennP P k j =
        ∑' ω : Fin (n + 1) → S, (if ω 0 = i ∧ ω (Fin.last n) = k ∧ ∀ m : Fin (n + 1), ω m ∈ D
          then pathWeightE P ω else 0) * ennP P k j := by
      intro k
      rw [← ih i hi k k.2, ENNReal.tsum_mul_right]
    simp_rw [this]
    conv_rhs => rw [ENNReal.tsum_comm]
    refine tsum_congr fun (ω : Fin (n+1) → S) => ?_
    have h0 : ∀ k, (Fin.snoc ω k : Fin (n + 2) → S) 0 = ω 0 := fun k => by
      have : (0 : Fin (n + 2)) = (0 : Fin (n+1)).castSucc := rfl
      rw [this, Fin.snoc_castSucc]
    have hall : ∀ k, (∀ m : Fin (n + 2), (Fin.snoc ω k : Fin (n + 2) → S) m ∈ D) ↔
        (∀ m, ω m ∈ D) ∧ k ∈ D := fun k => by
      rw [Fin.forall_fin_succ']; simp
    simp_rw [h0, hall, Fin.snoc_last, g70ma_pw_snoc]
    by_cases hc : ω 0 = i ∧ ∀ m, ω m ∈ D
    · rw [tsum_eq_single j, tsum_eq_single (⟨ω (Fin.last n), hc.2 _⟩ : D)]
      · simp [hc, hj]
      · intro b hb
        rw [if_neg]; · simp
        intro h; exact hb (Subtype.ext h.2.1.symm)
      · intro b hb
        rw [if_neg]; intro h; exact hb h.2.1
    · rw [ENNReal.tsum_eq_zero.mpr, ENNReal.tsum_eq_zero.mpr]
      · intro b; rw [if_neg]; · simp
        intro h; exact hc ⟨h.1, h.2.2⟩
      · intro b; rw [if_neg]; intro h; exact hc ⟨h.1, h.2.2.1⟩


/-- Latouche & Ramaswami, Eq. (5.23) (p. 117). Under the standing assumptions of Chapter 5 (an
irreducible, aperiodic chain on a countable state space `S` with transition matrix `P`), for every
subset `T` with complement `Tᶜ = S ∖ T`, `ₜR_{TᶜTᶜ} = N_{Tᶜ} = Σ_{ν ≥ 0} P_{Tᶜ}^ν`: for
`i, j ∉ T`, the expected number of visits to `j` from `i` before the first visit to `T` equals the
expected sojourn time `[N_{Tᶜ}]_{ij}` in `j` before the first passage to `T`, and both equal
`Σ_ν [P_{Tᶜ}^ν]_{ij}`. -/
theorem solution {S : Type*} [Countable S] [DecidableEq S]
    (P : S → S → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P) (hape : AperiodicC P)
    (T : Set S) :
    ∀ i ∉ T, ∀ j ∉ T,
      tabooR P T i j = sojournN P Tᶜ i j ∧ sojournN P Tᶜ i j = seriesInv (ennP P) Tᶜ i j := by
  intro i hi j hj
  constructor
  · unfold tabooR tabooP sojournN
    refine tsum_congr fun n => tsum_congr fun ω => ?_
    congr 1
    apply propext
    constructor
    · rintro ⟨h0, hl, hm⟩
      refine ⟨h0, hl, fun m => ?_⟩
      by_cases m0 : m = 0
      · subst m0; rw [h0]; exact hi
      by_cases ml : m = Fin.last n
      · subst ml; rw [hl]; exact hj
      exact hm m m0 ml
    · rintro ⟨h0, hl, hm⟩
      exact ⟨h0, hl, fun m _ _ => hm m⟩
  · unfold sojournN seriesInv
    exact tsum_congr fun n => g70ma_inD_eq P Tᶜ n i hi j hj


