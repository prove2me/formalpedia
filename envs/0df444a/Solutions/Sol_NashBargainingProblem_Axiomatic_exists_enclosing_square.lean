-- Prove2me | solution 1 for NashBargainingProblem.Axiomatic.exists_enclosing_square
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:27:11.452362+00:00
-- url     : https://prove2.me/submissions/d6a02e50-cf1c-4ce6-a7b7-dc5de8d50f46

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NashWork

def Qh (h : ℝ) : Set (ℝ × ℝ) := {u | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h}

theorem Qh_isCompact (h : ℝ) : IsCompact (Qh h) := by
  have hcl : IsClosed (Qh h) := by
    refine IsClosed.inter (isClosed_le continuous_const (continuous_fst.add continuous_snd))
      (IsClosed.inter (isClosed_le (continuous_fst.add continuous_snd) continuous_const)
        (isClosed_le (continuous_fst.sub continuous_snd).abs continuous_const))
  refine (isCompact_Icc (a := -(2 * |h| + 2)) (b := 2 * |h| + 2) |>.prod
    (isCompact_Icc (a := -(2 * |h| + 2)) (b := 2 * |h| + 2))).of_isClosed_subset hcl ?_
  rintro ⟨x, y⟩ ⟨h1, h2, h3⟩
  simp only [Set.mem_prod, Set.mem_Icc] at *
  have hh : h ≤ |h| := le_abs_self h
  have hh' : -|h| ≤ h := neg_abs_le h
  rw [abs_le] at h3
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [abs_nonneg h]

theorem Qh_convex (h : ℝ) : Convex ℝ (Qh h) := by
  intro u hu v hv a b ha hb hab
  obtain ⟨hu1, hu2, hu3⟩ := hu
  obtain ⟨hv1, hv2, hv3⟩ := hv
  rw [abs_le] at hu3 hv3
  simp only [Qh, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · rw [abs_le]; constructor <;> nlinarith

theorem Qh_symm (h : ℝ) (a b : ℝ) : (a, b) ∈ Qh h ↔ (b, a) ∈ Qh h := by
  simp only [Qh, Set.mem_setOf_eq, add_comm a b, abs_sub_comm a b]

theorem exists_enclosing_square (S : Set (ℝ × ℝ))
    (hS_compact : IsCompact S) (hS_le : ∀ u ∈ S, u.1 + u.2 ≤ 2) :
    ∃ h : ℝ, 0 < h ∧
      S ⊆ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ∧
      IsCompact {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ∧
      Convex ℝ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ∧
      (∀ a b : ℝ,
        (a, b) ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ↔
        (b, a) ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h}) := by
  obtain ⟨R, hR⟩ := hS_compact.isBounded.exists_norm_le
  have hbd : ∀ u ∈ S, |u.1| ≤ |R| ∧ |u.2| ≤ |R| := by
    intro u hu
    have hn : ‖u‖ ≤ |R| := (hR u hu).trans (le_abs_self R)
    rw [Prod.norm_def, max_le_iff] at hn
    exact ⟨by simpa using hn.1, by simpa using hn.2⟩
  have hR0 : 0 ≤ |R| := abs_nonneg R
  refine ⟨2 * |R| + 2, by positivity, ?_, Qh_isCompact _, Qh_convex _, Qh_symm _⟩
  intro u hu
  obtain ⟨h1, h2⟩ := hbd u hu
  rw [abs_le] at h1 h2
  refine ⟨?_, hS_le u hu, ?_⟩
  · linarith
  · rw [abs_le]; constructor <;> linarith

end NashWork

theorem solution (S : Set (ℝ × ℝ))
    (hS_compact : IsCompact S) (hS_le : ∀ u ∈ S, u.1 + u.2 ≤ 2) :
    ∃ h : ℝ, 0 < h ∧
      S ⊆ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ∧
      IsCompact {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ∧
      Convex ℝ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ∧
      (∀ a b : ℝ,
        (a, b) ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h} ↔
        (b, a) ∈ {u : ℝ × ℝ | 2 - 2 * h ≤ u.1 + u.2 ∧ u.1 + u.2 ≤ 2 ∧ |u.1 - u.2| ≤ h}) :=
  NashWork.exists_enclosing_square S hS_compact hS_le

#print axioms solution
