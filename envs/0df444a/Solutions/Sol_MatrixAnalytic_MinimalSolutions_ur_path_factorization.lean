-- Prove2me | solution 1 for MatrixAnalytic.MinimalSolutions.ur_path_factorization
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T14:11:16.555514+00:00
-- url     : https://prove2.me/submissions/c657f4fb-0d60-4d77-ad42-adb5b66049e5

import Mathlib
import Theorems.Thm_MatrixAnalytic_Nonhomogeneous_UGR_relations
import Theorems.Thm_MatrixAnalytic_Nonhomogeneous_minimal_solutions
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage

open scoped ENNReal
open MatrixAnalytic

section UrpfTransfer
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

def urpf_e : ℕ × ι → (Σ _ : ℕ, ι) := fun x => ⟨x.1, x.2⟩

omit [Countable ι] [DecidableEq ι] in
lemma urpf_e_inj (u v : ℕ × ι) : urpf_e u = urpf_e v ↔ u = v := by
  constructor
  · intro h
    simp only [urpf_e, Sigma.mk.injEq, heq_eq_eq] at h
    exact Prod.ext h.1 h.2
  · rintro rfl; rfl

def urpf_E (t : ℕ) : (Fin t → ℕ × ι) ≃ (Fin t → Σ _ : ℕ, ι) where
  toFun ω s := urpf_e (ω s)
  invFun ω s := ((ω s).1, (ω s).2)
  left_inv ω := rfl
  right_inv ω := rfl

omit [Countable ι] [DecidableEq ι] in
@[simp] lemma urpf_E_apply (t : ℕ) (ω : Fin t → ℕ × ι) (s : Fin t) :
    urpf_E t ω s = urpf_e (ω s) := rfl

def urpf_eqv : ℕ × ι ≃ (Σ _ : ℕ, ι) where
  toFun := urpf_e
  invFun x := (x.1, x.2)
  left_inv _ := rfl
  right_inv _ := rfl

def urpf_A1 : (n : ℕ) → ι → ι → ℝ := fun n => if n = 0 then B else A₁

noncomputable abbrev urpf_P : (Σ _ : ℕ, ι) → (Σ _ : ℕ, ι) → ℝ :=
  Nonhomogeneous.ndqbdP (ι := fun _ => ι) (fun _ => A₀) (urpf_A1 B A₁) (fun _ => A₂)

omit [Countable ι] [DecidableEq ι] in
lemma urpf_Peq (x y : ℕ × ι) :
    urpf_P B A₀ A₁ A₂ (urpf_e x) (urpf_e y) = MinimalSolutions.qbdP B A₀ A₁ A₂ x y := by
  obtain ⟨a, i⟩ := x
  obtain ⟨b, j⟩ := y
  simp only [urpf_P, urpf_e, Nonhomogeneous.ndqbdP, MinimalSolutions.qbdP, urpf_A1, cast_eq]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases b with _ | _ | b <;> simp
  · by_cases h1 : b = a + 1
    · subst h1; simp [ha.ne']
    by_cases h2 : b = a
    · subst h2; simp [ha.ne']
    by_cases h3 : b + 1 = a
    · subst h3; simp
    simp [h1, h2, h3, ha.ne']

omit [Countable ι] [DecidableEq ι] in
lemma urpf_Peq' (x y : Σ _ : ℕ, ι) :
    urpf_P B A₀ A₁ A₂ x y = MinimalSolutions.qbdP B A₀ A₁ A₂ (x.1, x.2) (y.1, y.2) :=
  urpf_Peq B A₀ A₁ A₂ (x.1, x.2) (y.1, y.2)

lemma urpf_fe (T : Set (ℕ × ι)) (T' : Set (Σ _ : ℕ, ι)) (hT : ∀ z, urpf_e z ∈ T' ↔ z ∈ T)
    (x y : ℕ × ι) :
    MinimalSolutions.firstEntrance (MinimalSolutions.qbdP B A₀ A₁ A₂) T x y =
      Nonhomogeneous.firstEntrance (urpf_P B A₀ A₁ A₂) T' (urpf_e x) (urpf_e y) := by
  classical
  unfold MinimalSolutions.firstEntrance Nonhomogeneous.firstEntrance
  refine tsum_congr fun t => ?_
  rw [← (urpf_E (ι := ι) (t + 2)).tsum_eq]
  refine tsum_congr fun ω => ?_
  have hc : ((urpf_E (t + 2)) ω 0 = urpf_e x ∧ (urpf_E (t + 2)) ω (Fin.last (t + 1)) = urpf_e y ∧
      urpf_e y ∈ T' ∧ ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → (urpf_E (t + 2)) ω m ∉ T') ↔
      (ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
        ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T) := by
    simp only [urpf_E_apply, urpf_e_inj, hT]
  by_cases h : ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
      ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
  · rw [if_pos h, if_pos (hc.mpr h)]
    unfold MinimalSolutions.pathWeightE Nonhomogeneous.pathWeightE
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [urpf_E_apply, urpf_Peq]
  · rw [if_neg h, if_neg (fun h' => h (hc.mp h'))]

lemma urpf_ev (T : Set (ℕ × ι)) (T' : Set (Σ _ : ℕ, ι)) (hT : ∀ z, urpf_e z ∈ T' ↔ z ∈ T)
    (x y : ℕ × ι) :
    MinimalSolutions.expVisitsAvoid (MinimalSolutions.qbdP B A₀ A₁ A₂) T x y =
      Nonhomogeneous.expVisitsAvoid (urpf_P B A₀ A₁ A₂) T' (urpf_e x) (urpf_e y) := by
  classical
  unfold MinimalSolutions.expVisitsAvoid Nonhomogeneous.expVisitsAvoid
  refine tsum_congr fun t => ?_
  rw [← (urpf_E (ι := ι) (t + 1)).tsum_eq]
  refine tsum_congr fun ω => ?_
  have hc : ((urpf_E (t + 1)) ω 0 = urpf_e x ∧ (urpf_E (t + 1)) ω (Fin.last t) = urpf_e y ∧
      ∀ m : Fin (t + 1), m ≠ 0 → (urpf_E (t + 1)) ω m ∉ T') ↔
      (ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ T) := by
    simp only [urpf_E_apply, urpf_e_inj, hT]
  by_cases h : ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ T
  · rw [if_pos h, if_pos (hc.mpr h)]
    unfold MinimalSolutions.pathWeightE Nonhomogeneous.pathWeightE
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [urpf_E_apply, urpf_Peq]
  · rw [if_neg h, if_neg (fun h' => h (hc.mp h'))]

lemma urpf_stepPow (t : ℕ) (x y : ℕ × ι) :
    Nonhomogeneous.stepPow (urpf_P B A₀ A₁ A₂) t (urpf_e x) (urpf_e y) =
      MinimalSolutions.stepPow (MinimalSolutions.qbdP B A₀ A₁ A₂) t x y := by
  induction t generalizing y with
  | zero =>
    simp only [Nonhomogeneous.stepPow, MinimalSolutions.stepPow, urpf_e_inj]
  | succ t ih =>
    simp only [Nonhomogeneous.stepPow, MinimalSolutions.stepPow]
    rw [← (urpf_eqv (ι := ι)).tsum_eq]
    refine tsum_congr fun z => ?_
    show Nonhomogeneous.stepPow _ t (urpf_e x) (urpf_e z) *
      urpf_P B A₀ A₁ A₂ (urpf_e z) (urpf_e y) = _
    rw [ih, urpf_Peq]

omit [Countable ι] in
lemma urpf_pow (M : ι → ι → ℝ≥0∞) (ν : ℕ) :
    MinimalSolutions.matPowE M ν = Nonhomogeneous.matPowE M ν := by
  induction ν with
  | zero => rfl
  | succ ν ih =>
    show MinimalSolutions.matMulE (MinimalSolutions.matPowE M ν) M =
      Nonhomogeneous.matMulE (Nonhomogeneous.matPowE M ν) M
    rw [ih]; rfl

omit [Countable ι] in
lemma urpf_S (M : ι → ι → ℝ≥0∞) :
    MinimalSolutions.seriesInvE M = Nonhomogeneous.seriesInvE M := by
  unfold MinimalSolutions.seriesInvE Nonhomogeneous.seriesInvE
  simp only [urpf_pow]

end UrpfTransfer

open MatrixAnalytic.MinimalSolutions in
theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    (∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matR (qbdP B A₀ A₁ A₂) = matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂))) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨fun i => (hι.false i).elim, ?_⟩
    funext i; exact (hι.false i).elim
  set P := urpf_P B A₀ A₁ A₂ with hPd
  have eU : matU (qbdP B A₀ A₁ A₂) = Nonhomogeneous.matU P 1 := by
    funext i j
    refine urpf_fe B A₀ A₁ A₂ (level 0 ∪ level 1)
      (Nonhomogeneous.levelsUpTo 1) (fun z => ?_) (1, i) (1, j)
    simp only [urpf_e, Nonhomogeneous.levelsUpTo, level, Set.mem_union, Set.mem_setOf_eq]
    omega
  have eR : matR (qbdP B A₀ A₁ A₂) = Nonhomogeneous.matR P 0 := by
    funext i j
    refine urpf_ev B A₀ A₁ A₂ (level 0)
      (Nonhomogeneous.levelsUpTo 0) (fun z => ?_) (0, i) (1, j)
    simp only [urpf_e, Nonhomogeneous.levelsUpTo, level, Set.mem_setOf_eq]
    omega
  have eM : @matMulE ι = @Nonhomogeneous.matMulE ι ι ι := rfl
  have eE : @ennMat ι = @Nonhomogeneous.ennMat ι ι := rfl
  have eS : @seriesInvE ι _ = @Nonhomogeneous.seriesInvE ι _ :=
    funext fun M => urpf_S M
  rw [eU, eR, eM, eE, eS]
  have hP' : Nonhomogeneous.IsStochasticC P := by
    refine ⟨fun x y => by rw [hPd, urpf_Peq']; exact hP.1 _ _, fun z => ?_⟩
    rw [← (urpf_eqv (ι := ι)).hasSum_iff]
    have : (P z ∘ urpf_eqv) = qbdP B A₀ A₁ A₂ (z.1, z.2) := by
      funext y; exact urpf_Peq' B A₀ A₁ A₂ z _
    rw [this]; exact hP.2 _
  have hirr' : Nonhomogeneous.IrreducibleC P := by
    intro x y
    obtain ⟨t, ht⟩ := hirr (x.1, x.2) (y.1, y.2)
    exact ⟨t, by rw [hPd]; exact (urpf_stepPow B A₀ A₁ A₂ t (x.1, x.2) (y.1, y.2)).symm ▸ ht⟩
  have hUGR := Nonhomogeneous.UGR_relations (ι := fun _ => ι) (fun _ => A₀) (urpf_A1 B A₁)
    (fun _ => A₂) P rfl hP' hirr'
  have hMS := Nonhomogeneous.minimal_solutions (ι := fun _ => ι) (fun _ => A₀) (urpf_A1 B A₁)
    (fun _ => A₂) P rfl hP' hirr'
  exact ⟨hMS.2.1.1 0, hUGR.2.2.1 0⟩
