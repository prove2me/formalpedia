-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.polynomialJet_mem_monomialIdeal_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:22:45.771987+00:00
-- url     : https://prove2.me/submissions/6d4808b4-4879-4707-be5a-3265ccae81cc

import Mathlib
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets

open OAI.PiExponent OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

noncomputable def pieJinv {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval (jetCoordinate c T)

theorem pie_eval₂_alg {m : ℕ} (f : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ)
    (x : MvPolynomial (Fin (m + 1)) ℂ) (p : Polynomial ℂ) :
    f (Polynomial.eval₂ MvPolynomial.C x p) = Polynomial.eval₂ MvPolynomial.C (f x) p := by
  have := (Polynomial.aeval_algHom_apply f x p).symm
  simpa [Polynomial.aeval_def, MvPolynomial.algebraMap_eq] using this

theorem pie_J_jc {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) (i : Fin (m + 1)) :
    polynomialJet c T (jetCoordinate c T i) = MvPolynomial.X i := by
  have h0 : polynomialJet c T (MvPolynomial.X 0 - 1) = MvPolynomial.X 0 := by
    simp [polynomialJet]
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa [jetCoordinate] using h0
  · simp only [jetCoordinate, Fin.cases_succ, map_sub, pie_eval₂_alg, h0]
    simp [polynomialJet]
    ring

theorem pie_Jinv_J {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) (i : Fin (m + 1)) :
    pieJinv c T (polynomialJet c T (MvPolynomial.X i)) = MvPolynomial.X i := by
  have h0 : pieJinv c T (MvPolynomial.X 0) = MvPolynomial.X 0 - 1 := by
    simp [pieJinv, jetCoordinate]
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [polynomialJet, pieJinv, jetCoordinate]
  · simp only [polynomialJet, MvPolynomial.aeval_X, Fin.cases_succ, map_add, pie_eval₂_alg, h0]
    simp [pieJinv, jetCoordinate]
    ring

noncomputable def pieJeq {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) :
    MvPolynomial (Fin (m + 1)) ℂ ≃ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ :=
  AlgEquiv.ofAlgHom (polynomialJet c T) (pieJinv c T)
    (MvPolynomial.algHom_ext (fun i => by
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      simp only [pieJinv, MvPolynomial.aeval_X]; exact pie_J_jc c T i))
    (MvPolynomial.algHom_ext (fun i => by
      simp only [AlgHom.comp_apply, AlgHom.id_apply]; exact pie_Jinv_J c T i))

theorem pie_map_local {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ) :
    (localJetIdeal c T e).map (pieJeq c T) =
      Ideal.span (Set.range (fun i : Fin (m + 1) => MvPolynomial.X i ^ e i)) := by
  rw [localJetIdeal, Ideal.map_span, ← Set.range_comp]
  congr 2
  funext i
  simp [pieJeq, pie_J_jc]

theorem pie_mem_iff {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ) (k : ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    P ∈ localJetIdeal c T e ^ k ↔
      polynomialJet c T P ∈
        Ideal.span (Set.range (fun i : Fin (m + 1) => MvPolynomial.X i ^ e i)) ^ k := by
  rw [← pie_map_local, ← Ideal.map_pow]
  change _ ↔ (pieJeq c T) P ∈ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro h; exact ⟨P, h, rfl⟩
  · rintro ⟨Q, hQ, hQP⟩
    have := (pieJeq c T).injective hQP
    rw [← this]; exact hQ

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i)
    (k : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ) :
    P ∈ localJetIdeal c T e ^ k ↔
      polynomialJet c T P ∈
        Ideal.span (Set.range (fun i : Fin (m + 1) => MvPolynomial.X i ^ e i)) ^ k :=
  pie_mem_iff c T e k P
