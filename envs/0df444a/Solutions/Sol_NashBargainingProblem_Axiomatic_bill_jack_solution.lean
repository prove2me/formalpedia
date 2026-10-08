-- Prove2me | solution 1 for NashBargainingProblem.Axiomatic.bill_jack_solution
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:27:19.955898+00:00
-- url     : https://prove2.me/submissions/6c011a28-c725-4df9-a49b-2616747319e1

import Mathlib
import Definitions.Def_NashBargainingProblem_Axiomatic_BillJack

set_option autoImplicit false
set_option linter.unusedVariables false



open NashBargainingProblem.Axiomatic

namespace NashWork

def ubb : BillGood → ℤ | .book => 2 | .whip => 2 | .ball => 2 | .bat => 2 | .box => 4
def ubj : BillGood → ℤ | .book => 4 | .whip => 2 | .ball => 1 | .bat => 2 | .box => 1
def ujb : JackGood → ℤ | .pen => 10 | .toy => 4 | .knife => 6 | .hat => 2
def ujj : JackGood → ℤ | .pen => 1 | .toy => 1 | .knife => 2 | .hat => 2

def G1 (e : Finset BillGood × Finset JackGood) : ℤ := (∑ y ∈ e.2, ujb y) - ∑ x ∈ e.1, ubb x
def G2 (e : Finset BillGood × Finset JackGood) : ℤ := (∑ x ∈ e.1, ubj x) - ∑ y ∈ e.2, ujj y

theorem finite_check : ∀ e : Finset BillGood × Finset JackGood,
    5 * G1 e + 12 * G2 e ≤ 120 ∧ (5 * G1 e + 12 * G2 e = 120 →
      e.1 = {BillGood.book, BillGood.whip, BillGood.ball, BillGood.bat} ∧
      e.2 = {JackGood.pen, JackGood.toy, JackGood.knife}) := by
  decide +kernel

theorem finite_check' : ∀ e : Finset BillGood × Finset JackGood,
    (G1 e = 12 ∧ G2 e = 5) ↔
      (e.1 = {BillGood.book, BillGood.whip, BillGood.ball, BillGood.bat} ∧
      e.2 = {JackGood.pen, JackGood.toy, JackGood.knife}) := by
  decide +kernel

theorem gain_eq (e : Finset BillGood × Finset JackGood) :
    billJackGain e = ((G1 e : ℝ), (G2 e : ℝ)) := by
  have h1 : ∀ y, jackGoodUtilBill y = (ujb y : ℝ) := by intro y; cases y <;> simp [jackGoodUtilBill, ujb]
  have h2 : ∀ x, billGoodUtilBill x = (ubb x : ℝ) := by intro x; cases x <;> simp [billGoodUtilBill, ubb]
  have h3 : ∀ x, billGoodUtilJack x = (ubj x : ℝ) := by intro x; cases x <;> simp [billGoodUtilJack, ubj]
  have h4 : ∀ y, jackGoodUtilJack y = (ujj y : ℝ) := by intro y; cases y <;> simp [jackGoodUtilJack, ujj]
  simp only [billJackGain, G1, G2, h1, h2, h3, h4]
  push_cast
  rfl

/-- The polygon lies in this convex set: below the line `5 u₁ + 12 u₂ = 120`, touching it only at
`(12, 5)`. -/
def BJK : Set (ℝ × ℝ) :=
  {u | 5 * u.1 + 12 * u.2 ≤ 120 ∧ (5 * u.1 + 12 * u.2 = 120 → u = ((12 : ℝ), (5 : ℝ)))}

theorem BJK_convex : Convex ℝ BJK := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  simp only [BJK, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  have hle : 5 * (a * u.1 + b * v.1) + 12 * (a * u.2 + b * v.2) ≤ 120 := by nlinarith
  refine ⟨hle, fun heq => ?_⟩
  rcases ha.eq_or_lt with ha0 | ha0
  · have hb1 : b = 1 := by linarith
    subst hb1
    rw [← ha0] at heq ⊢
    have := hv2 (by linarith)
    rw [this]
    ext <;> simp
  rcases hb.eq_or_lt with hb0 | hb0
  · have ha1 : a = 1 := by linarith
    subst ha1
    rw [← hb0] at heq ⊢
    have := hu2 (by linarith)
    rw [this]
    ext <;> simp
  have hfu : 5 * u.1 + 12 * u.2 = 120 := by nlinarith
  have hfv : 5 * v.1 + 12 * v.2 = 120 := by nlinarith
  rw [hu2 hfu, hv2 hfv]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    linarith

theorem gains_mem_BJK (e : Finset BillGood × Finset JackGood) : billJackGain e ∈ BJK := by
  rw [gain_eq]
  show 5 * (G1 e : ℝ) + 12 * (G2 e : ℝ) ≤ 120 ∧
    (5 * (G1 e : ℝ) + 12 * (G2 e : ℝ) = 120 → ((G1 e : ℝ), (G2 e : ℝ)) = ((12 : ℝ), (5 : ℝ)))
  obtain ⟨h1, h2⟩ := finite_check e
  have h1' : (5 * (G1 e : ℝ) + 12 * (G2 e : ℝ)) ≤ 120 := by exact_mod_cast h1
  refine ⟨h1', fun heq => ?_⟩
  have heq' : 5 * G1 e + 12 * G2 e = 120 := by exact_mod_cast heq
  have := (finite_check' e).2 (h2 heq')
  obtain ⟨hg1, hg2⟩ := this
  ext
  · simp only [hg1]; norm_num
  · simp only [hg2]; norm_num

theorem hull_sub_BJK : billJackSet ⊆ BJK :=
  convexHull_min (by rintro _ ⟨e, rfl⟩; exact gains_mem_BJK e) BJK_convex

theorem bill_jack_solution :
    ((12 : ℝ), (5 : ℝ)) ∈ billJackSet ∧
    (∀ s ∈ billJackSet, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ ((12 : ℝ), (5 : ℝ)) →
      s.1 * s.2 < 12 * 5) ∧
    ((12 : ℝ), (5 : ℝ)) ∈ billJackSet.extremePoints ℝ ∧
    ∀ (X : Finset BillGood) (Y : Finset JackGood),
      billJackGain (X, Y) = ((12 : ℝ), (5 : ℝ)) ↔
        X = {BillGood.book, BillGood.whip, BillGood.ball, BillGood.bat} ∧
        Y = {JackGood.pen, JackGood.toy, JackGood.knife} := by
  have h3 : ∀ (X : Finset BillGood) (Y : Finset JackGood),
      billJackGain (X, Y) = ((12 : ℝ), (5 : ℝ)) ↔
        X = {BillGood.book, BillGood.whip, BillGood.ball, BillGood.bat} ∧
        Y = {JackGood.pen, JackGood.toy, JackGood.knife} := by
    intro X Y
    rw [gain_eq]
    simp only [Prod.mk.injEq]
    have : ((G1 (X, Y) : ℝ) = 12 ∧ (G2 (X, Y) : ℝ) = 5) ↔ (G1 (X, Y) = 12 ∧ G2 (X, Y) = 5) := by
      constructor
      · rintro ⟨a, b⟩; exact ⟨by exact_mod_cast a, by exact_mod_cast b⟩
      · rintro ⟨a, b⟩; exact ⟨by exact_mod_cast a, by exact_mod_cast b⟩
    rw [this]
    exact finite_check' (X, Y)
  have hmem : ((12 : ℝ), (5 : ℝ)) ∈ billJackSet := by
    have := (h3 {BillGood.book, BillGood.whip, BillGood.ball, BillGood.bat}
      {JackGood.pen, JackGood.toy, JackGood.knife}).2 ⟨rfl, rfl⟩
    rw [← this]
    exact subset_convexHull ℝ _ ⟨_, rfl⟩
  refine ⟨hmem, ?_, ?_, h3⟩
  · intro s hs h1 h2 hne
    obtain ⟨hs1, hs2⟩ := hull_sub_BJK hs
    have hlt : 5 * s.1 + 12 * s.2 < 120 :=
      lt_of_le_of_ne hs1 (fun h => hne (hs2 h))
    nlinarith [sq_nonneg (5 * s.1 - 12 * s.2)]
  · refine ⟨hmem, ?_⟩
    intro x1 hx1 x2 hx2 hseg
    obtain ⟨a, b, ha, hb, hab, hx⟩ := hseg
    obtain ⟨hx11, hx12⟩ := hull_sub_BJK hx1
    obtain ⟨hx21, hx22⟩ := hull_sub_BJK hx2
    have h1 := congrArg Prod.fst hx
    have h2 := congrArg Prod.snd hx
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
    have e1 : 5 * x1.1 + 12 * x1.2 = 120 := by nlinarith
    have e2 : 5 * x2.1 + 12 * x2.2 = 120 := by nlinarith
    exact hx12 e1

end NashWork

open NashBargainingProblem.Axiomatic

theorem solution :
    ((12 : ℝ), (5 : ℝ)) ∈ billJackSet ∧
    (∀ s ∈ billJackSet, 0 ≤ s.1 → 0 ≤ s.2 → s ≠ ((12 : ℝ), (5 : ℝ)) →
      s.1 * s.2 < 12 * 5) ∧
    ((12 : ℝ), (5 : ℝ)) ∈ billJackSet.extremePoints ℝ ∧
    ∀ (X : Finset BillGood) (Y : Finset JackGood),
      billJackGain (X, Y) = ((12 : ℝ), (5 : ℝ)) ↔
        X = {BillGood.book, BillGood.whip, BillGood.ball, BillGood.bat} ∧
        Y = {JackGood.pen, JackGood.toy, JackGood.knife} :=
  NashWork.bill_jack_solution

#print axioms solution
