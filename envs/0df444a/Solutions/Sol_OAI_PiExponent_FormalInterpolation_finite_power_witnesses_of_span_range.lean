-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_power_witnesses_of_span_range
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:18:40.838952+00:00
-- url     : https://prove2.me/submissions/af4f6875-2e9d-4278-89a3-3c75395773ae

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

section

open OAI.PiExponent.FormalInterpolation

namespace PiL15

theorem jet_pderiv {m K : Nat} (φ : Fin K → MvPolynomial (Fin (m + 1)) Complex →ₐ[Complex] MvPowerSeries (Fin (m + 1)) Complex) (v : Fin (m + 1) → Rat) (H : Real) (i : Fin m) (F : MvPolynomial (Fin (m + 1)) Complex) (hjet : ∀ j (a : Fin (m + 1) →₀ Nat), (∑ k, (v k : Real) * (a k : Real)) < H → MvPowerSeries.coeff a (φ j F) = 0) (hcomm : ∀ j, φ j (MvPolynomial.pderiv i.succ F) = MvPowerSeries.pderiv Complex i.succ (φ j F)) : ∀ j (a : Fin (m + 1) →₀ Nat), (∑ k, (v k : Real) * (a k : Real)) < H - (v i.succ : Real) → MvPowerSeries.coeff a (φ j (MvPolynomial.pderiv i.succ F)) = 0 := by
  classical
  intro j a ha
  rw [hcomm, MvPowerSeries.coeff_pderiv, hjet j _ ?_, zero_mul]
  have : ∑ k, (v k : Real) * (((a + Finsupp.single i.succ 1 : Fin (m + 1) →₀ ℕ) k : ℕ) : Real) =
      (∑ k, (v k : Real) * (a k : Real)) + v i.succ := by
    simp only [Finsupp.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib, Finsupp.single_apply]
    congr 1
    rw [Finset.sum_eq_single i.succ]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [this]; linarith

universe u v w

theorem witnesses {R : Type u} [CommSemiring R]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {α : Type w}
    (x : ι → R) (P : α → Prop) (g : α → R)
    (h : ∀ i : ι, ∃ e : Nat, 0 < e ∧
      x i ^ e ∈ Ideal.span (Set.range (fun a : {a // P a} => g a.1))) :
    ∃ k : Nat, ∃ f : Fin k → {a // P a},
      ∀ i : ι, ∃ e : Nat, 0 < e ∧
        x i ^ e ∈ Ideal.span (Set.range (fun j : Fin k => g (f j).1)) := by
  classical
  choose e he hmem using h
  have hfin : ∀ i, ∃ T : Finset R, (T : Set R) ⊆ Set.range (fun a : {a // P a} => g a.1) ∧
      x i ^ e i ∈ Ideal.span (T : Set R) := fun i =>
    Submodule.mem_span_finite_of_mem_span (hmem i)
  choose T hTsub hTmem using hfin
  have hpre : ∀ i, ∀ t ∈ T i, ∃ p : {a // P a}, g p.1 = t := fun i t ht => hTsub i ht
  choose pre hpre' using hpre
  let U : Finset {a // P a} := Finset.univ.biUnion fun i => (T i).attach.image fun t => pre i t.1 t.2
  refine ⟨U.card, fun j => (U.equivFin.symm j).1, fun i => ⟨e i, he i, ?_⟩⟩
  refine Ideal.span_mono ?_ (hTmem i)
  intro t ht
  have hU : pre i t ht ∈ U := by
    simp only [U, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_attach]
    exact ⟨i, ⟨t, ht⟩, rfl⟩
  refine ⟨U.equivFin ⟨pre i t ht, hU⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hpre' i t ht

theorem chain {σ R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [DecidableEq σ] (D : Derivation R S S) (g : σ → S) (p : MvPolynomial σ R) (i : σ) (hg : ∀ j, D (g j) = if j = i then 1 else 0) : MvPolynomial.aeval g (MvPolynomial.pderiv i p) = D (MvPolynomial.aeval g p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    have e1 : MvPolynomial.pderiv i (p * MvPolynomial.X j) =
        p * MvPolynomial.pderiv i (MvPolynomial.X j) + MvPolynomial.X j * MvPolynomial.pderiv i p := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have e2 : D (MvPolynomial.aeval g p * g j) =
        MvPolynomial.aeval g p * D (g j) + g j * D (MvPolynomial.aeval g p) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [e1, map_add, map_mul, map_mul, hp, map_mul, MvPolynomial.aeval_X, e2, hg j]
    by_cases h : j = i
    · subst h; simp [MvPolynomial.pderiv_X_self]
    · simp [MvPolynomial.pderiv_X_of_ne h, h]

end PiL15

end

open OAI OAI.PiExponent OAI.PiExponent.FormalInterpolation

universe u v w


theorem solution
    {R : Type u} [CommSemiring R]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {α : Type w}
    (x : ι → R) (P : α → Prop) (g : α → R)
    (h : ∀ i : ι, ∃ e : Nat, 0 < e ∧
      x i ^ e ∈ Ideal.span (Set.range (fun a : {a // P a} => g a.1))) :
    ∃ k : Nat, ∃ f : Fin k → {a // P a},
      ∀ i : ι, ∃ e : Nat, 0 < e ∧
        x i ^ e ∈ Ideal.span (Set.range (fun j : Fin k => g (f j).1)) := by
  apply PiL15.witnesses <;> assumption
