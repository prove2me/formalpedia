-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.lie_traceForm_nondegenerate_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T10:26:43.137842+00:00
-- url     : https://prove2.me/submissions/9f7ff7a4-b6bd-4408-b147-6cd1d4538ed9

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpCInst

set_option autoImplicit false

theorem solution
    (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    (crd : Matrix.GeneralLinearGroup n K → (n × n) ⊕ (n × n) → K)
    (hcrd : ∀ g, crd g = Sum.elim (fun ij => (g : Matrix n n K) ij.1 ij.2)
      (fun ij => ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ij.1 ij.2))
    (lie : Set (Matrix.GeneralLinearGroup n K) → Set (Matrix n n K))
    (hlie : ∀ Z X, X ∈ lie Z ↔ ∀ f : MvPolynomial ((n × n) ⊕ (n × n)) K,
      (∀ g ∈ Z, MvPolynomial.eval (crd g) f = 0) →
        ∑ v, MvPolynomial.eval (crd 1) (MvPolynomial.pderiv v f) *
          Sum.elim (fun ij => X ij.1 ij.2) (fun ij => -X ij.1 ij.2) v = 0)
    (G : Subgroup (Matrix.GeneralLinearGroup n K))
    (hG : ∀ W : Submodule K (n → K),
      (∀ g ∈ G, ∀ v ∈ W, Matrix.mulVec (g : Matrix n n K) v ∈ W) → W = ⊥ ∨ W = ⊤) :
    (∀ H : Subgroup (Matrix.GeneralLinearGroup n K),
      (∀ g ∈ G, ∀ X ∈ lie H,
        (g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ∈ lie H) →
        ∀ X ∈ lie H, (∀ Y ∈ lie H, (X * Y).trace = 0) → X = 0) ∧
    ((∀ φ : Matrix n n K →ₗ[K] Matrix n n K,
        (∀ X : Matrix n n K, X.trace = 0 → (φ X).trace = 0) →
        (∀ g ∈ G, ∀ X : Matrix n n K, X.trace = 0 →
          φ ((g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
            (g : Matrix n n K) * φ X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) →
        ∃ c : K, ∀ X : Matrix n n K, X.trace = 0 → φ X = c • X) →
      lie {g | g ∈ G ∧ (g : Matrix n n K).det = 1} = {0} ∨
        lie {g | g ∈ G ∧ (g : Matrix n n K).det = 1} = {X | X.trace = 0}) ∧
    (∀ B : Matrix n n K, (∀ g ∈ G, (g : Matrix n n K).transpose * B * g = B) →
      (∀ φ : Matrix n n K →ₗ[K] Matrix n n K,
        (∀ X : Matrix n n K, X.transpose * B + B * X = 0 → (φ X).transpose * B + B * φ X = 0) →
        (∀ g ∈ G, ∀ X : Matrix n n K, X.transpose * B + B * X = 0 →
          φ ((g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
            (g : Matrix n n K) * φ X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) →
        ∃ c : K, ∀ X : Matrix n n K, X.transpose * B + B * X = 0 → φ X = c • X) →
      lie G = {0} ∨ lie G = {X | X.transpose * B + B * X = 0}) := by
  have hc : crd = RamanujanPetersson.AlgGrpA.crd := funext hcrd
  subst hc
  have hL : ∀ Z : Set (Matrix.GeneralLinearGroup n K),
      lie Z = (RamanujanPetersson.AlgGrpB.lieS Z : Set (Matrix n n K)) := by
    intro Z
    ext X
    rw [hlie, SetLike.mem_coe, RamanujanPetersson.AlgGrpB.mem_lieS]
    refine forall_congr' fun f => ?_
    rw [RamanujanPetersson.AlgGrpA.mem_vanI]
    exact Iff.rfl
  refine ⟨?_, ?_, ?_⟩
  · intro H hH X hX hXY
    simp only [hL, SetLike.mem_coe] at hH hX hXY
    exact RamanujanPetersson.AlgGrpC.trace_form_nondegenerate hG hH hX hXY
  · intro hEnd
    have h := RamanujanPetersson.AlgGrpC.lieS_inf_sl_eq_bot_or_eq hG (fun φ h1 h2 =>
      (hEnd φ (fun X hX => RamanujanPetersson.AlgGrpC.mem_slMat.1
          (h1 X (RamanujanPetersson.AlgGrpC.mem_slMat.2 hX)))
        (fun g hg X hX => h2 g hg X (RamanujanPetersson.AlgGrpC.mem_slMat.2 hX))).imp
        fun c hc X hX => hc X (RamanujanPetersson.AlgGrpC.mem_slMat.1 hX))
    have e : {g : Matrix.GeneralLinearGroup n K | g ∈ G ∧ (g : Matrix n n K).det = 1} =
        (G : Set (Matrix.GeneralLinearGroup n K)) ∩ RamanujanPetersson.AlgGrpB.slSet := rfl
    rw [e, hL]
    rcases h with h | h
    · left
      rw [h, Submodule.bot_coe]
    · right
      rw [h]
      ext X
      exact RamanujanPetersson.AlgGrpC.mem_slMat
  · intro B hGB hEnd
    have h := RamanujanPetersson.AlgGrpC.lieS_iso_eq_bot_or_eq (B := B) (G := G)
      (fun g hg => RamanujanPetersson.AlgGrpB.mem_isoSet.2 (hGB g hg)) hG (fun φ h1 h2 =>
      (hEnd φ (fun X hX => RamanujanPetersson.AlgGrpC.mem_isoLie.1
          (h1 X (RamanujanPetersson.AlgGrpC.mem_isoLie.2 hX)))
        (fun g hg X hX => h2 g hg X (RamanujanPetersson.AlgGrpC.mem_isoLie.2 hX))).imp
        fun c hc X hX => hc X (RamanujanPetersson.AlgGrpC.mem_isoLie.1 hX))
    rw [hL]
    rcases h with h | h
    · left
      rw [h, Submodule.bot_coe]
    · right
      rw [h]
      ext X
      exact RamanujanPetersson.AlgGrpC.mem_isoLie
