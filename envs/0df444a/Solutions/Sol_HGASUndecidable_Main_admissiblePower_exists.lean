-- Prove2me | solution 1 for HGASUndecidable.Main.admissiblePower_exists
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:29:07.080837+00:00
-- url     : https://prove2.me/submissions/b74da98e-d827-49db-ae67-24200e14281a

import Definitions.Def_HGASUndecidable_Main_Compactification

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

private lemma totalDegree_finset_sum_le {σ R ι : Type*} [CommSemiring R]
    (s : Finset ι) (f : ι → MvPolynomial σ R) (b : ℕ)
    (h : ∀ i ∈ s, (f i).totalDegree ≤ b) :
    (∑ i ∈ s, f i).totalDegree ≤ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (MvPolynomial.totalDegree_add _ _).trans
        (max_le (h i (Finset.mem_insert_self i s))
          (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))))

private lemma preal_totalDegree_le {n : ℕ} (p : CPoly n) :
    (preal p).totalDegree ≤ p.totalDegree := by
  apply totalDegree_finset_sum_le
  intro m hm
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans
    (MvPolynomial.le_totalDegree hm)

private lemma pimag_totalDegree_le {n : ℕ} (p : CPoly n) :
    (pimag p).totalDegree ≤ p.totalDegree := by
  apply totalDegree_finset_sum_le
  intro m hm
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans
    (MvPolynomial.le_totalDegree hm)

private lemma le_foldl_max (l : List ℕ) (b : ℕ) : b ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => simp
  | cons y l ih =>
      simp only [List.foldl_cons]
      exact (Nat.le_max_left _ _).trans (ih (max b y))

private lemma mem_foldl_max_le (l : List ℕ) (b x : ℕ) (hx : x ∈ l) :
    x ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => simp at hx
  | cons y l ih =>
      simp only [List.mem_cons] at hx
      simp only [List.foldl_cons]
      rcases hx with rfl | hx
      · exact (Nat.le_max_right _ _).trans (le_foldl_max l (max b x))
      · exact ih _ hx

private lemma totalDegree_le_listFold {n : ℕ} (l : List (RPoly n)) (p : RPoly n)
    (hp : p ∈ l) : p.totalDegree ≤ (l.map MvPolynomial.totalDegree).foldl max 0 := by
  apply mem_foldl_max_le
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

private lemma polyVariable_totalDegree_le (n k : ℕ) :
    (polyVariable n k).totalDegree ≤ 1 := by
  unfold polyVariable
  split_ifs <;> simp

private lemma cvariable_totalDegree_le (n k : ℕ) :
    (cvariable n k).totalDegree ≤ 1 := by
  unfold cvariable
  calc
    (polyVariable n k + MvPolynomial.C Complex.I * polyVariable n (k + 1)).totalDegree
        ≤ max (polyVariable n k).totalDegree
          (MvPolynomial.C Complex.I * polyVariable n (k + 1)).totalDegree :=
      MvPolynomial.totalDegree_add _ _
    _ ≤ 1 := max_le (polyVariable_totalDegree_le n k)
      ((MvPolynomial.totalDegree_mul _ _).trans (by
        simp only [MvPolynomial.totalDegree_C, zero_add]
        exact polyVariable_totalDegree_le n (k + 1)))

private lemma omega_totalDegree_le (a : DiophantineData) (l : Fin (a.q + a.r)) :
    (omega a l).totalDegree ≤ 1 := by
  unfold omega clockR
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [show (primeAt l.val : CPoly (ns a)) = MvPolynomial.C (primeAt l.val : ℂ) by simp]
  simp only [MvPolynomial.totalDegree_C, zero_add]
  exact polyVariable_totalDegree_le _ _

private lemma oscillatorEquation_totalDegree_le (a : DiophantineData) (e : ℕ) :
    (-4 * MvPolynomial.C Complex.I *
      (∑ l, (rhs a e l : CPoly (ns a)) * omega a (Fin.natAdd a.q l)) *
        oscillator a).totalDegree ≤ 2 := by
  have hsum : (∑ l, (rhs a e l : CPoly (ns a)) *
      omega a (Fin.natAdd a.q l)).totalDegree ≤ 1 := by
    apply totalDegree_finset_sum_le
    intro l hl
    apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [show (rhs a e l : CPoly (ns a)) = MvPolynomial.C (rhs a e l : ℂ) by simp]
    simp only [MvPolynomial.totalDegree_C, zero_add]
    exact omega_totalDegree_le a (Fin.natAdd a.q l)
  have hconst : (-4 * MvPolynomial.C Complex.I : CPoly (ns a)).totalDegree = 0 := by
    rw [show (-4 * MvPolynomial.C Complex.I : CPoly (ns a)) =
      MvPolynomial.C (-4 * Complex.I) by
        rw [show (-4 * MvPolynomial.C Complex.I : CPoly (ns a)) =
          (-(4 : CPoly (ns a))) * MvPolynomial.C Complex.I by rfl]
        rw [show (4 : CPoly (ns a)) = MvPolynomial.C (4 : ℂ) by
          exact (map_ofNat (MvPolynomial.C : ℂ →+* CPoly (ns a)) 4).symm]
        simp]
    exact MvPolynomial.totalDegree_C _
  have hosc : (oscillator a).totalDegree ≤ 1 := cvariable_totalDegree_le _ _
  calc
    (-4 * MvPolynomial.C Complex.I *
      (∑ l, (rhs a e l : CPoly (ns a)) * omega a (Fin.natAdd a.q l)) *
        oscillator a).totalDegree
        ≤ (-4 * MvPolynomial.C Complex.I *
          (∑ l, (rhs a e l : CPoly (ns a)) * omega a (Fin.natAdd a.q l))).totalDegree +
          (oscillator a).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ ((-4 * MvPolynomial.C Complex.I : CPoly (ns a)).totalDegree +
          (∑ l, (rhs a e l : CPoly (ns a)) * omega a (Fin.natAdd a.q l)).totalDegree) +
          (oscillator a).totalDegree :=
      Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
    _ ≤ 2 := by omega

private lemma normalizedOscillatorEquation_totalDegree_le (a : DiophantineData) (e : ℕ) :
    (-((4 * MvPolynomial.C Complex.I *
      (∑ l, (rhs a e l : CPoly (ns a)) * omega a (Fin.natAdd a.q l))) *
        oscillator a)).totalDegree ≤ 2 := by
  simpa only [neg_mul] using oscillatorEquation_totalDegree_le a e

private lemma systemList_totalDegree_le (a : DiophantineData) (e : ℕ) (p : RPoly (ns a))
    (hp : p ∈ systemList a e) :
    p.totalDegree ≤ max (((systemList a 0).map MvPolynomial.totalDegree).foldl max 0) 2 := by
  simp only [systemList, List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · exact (totalDegree_le_listFold (systemList a 0) p (by
      simp only [systemList, List.mem_append]
      exact Or.inl (Or.inl hp))).trans (Nat.le_max_left _ _)
  · simp [splitComplex] at hp
    rcases hp with rfl | rfl
    · exact (preal_totalDegree_le _).trans
        ((normalizedOscillatorEquation_totalDegree_le a e).trans (Nat.le_max_right _ _))
    · exact (pimag_totalDegree_le _).trans
        ((normalizedOscillatorEquation_totalDegree_le a e).trans (Nat.le_max_right _ _))
  · exact (totalDegree_le_listFold (systemList a 0) p (by
      simp only [systemList, List.mem_append]
      exact Or.inr hp)).trans (Nat.le_max_left _ _)

end HGASUndecidable.Main

open HGASUndecidable.Main

theorem solution (a : DiophantineData) :
    ∃ M : ℕ, admissiblePower a M := by
  let B := max (testDegree a)
    (max (((systemList a 0).map MvPolynomial.totalDegree).foldl max 0) 2)
  refine ⟨2 * B, ⟨B, by omega⟩, ?_, ?_⟩
  · dsimp [B]
    omega
  · intro e i
    unfold systemPolys
    generalize hp : (systemList a e)[i.val]? = op
    cases op with
    | none => simp
    | some p =>
        simp only [Option.getD_some]
        have hmem : p ∈ systemList a e := List.mem_of_getElem? hp
        have hdeg := systemList_totalDegree_le a e p hmem
        dsimp [B]
        omega
