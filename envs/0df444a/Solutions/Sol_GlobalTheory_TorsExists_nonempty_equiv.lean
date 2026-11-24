-- Prove2me | solution 1 for GlobalTheory.TorsExists.nonempty_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:44:55.363884+00:00
-- url     : https://prove2.me/submissions/8f560aaa-3235-4a8d-84ff-8595ca3d5f7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsUnitField
import Theorems.Thm_GlobalTheory_TorsExists_block_mul_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsExists
variable {Ix : Type} [Fintype Ix] [DecidableEq Ix]
namespace GlobalTheory.TorsExists
theorem _root_.solution {R : Type} [CommRing R] [Nontrivial R] (deg : Ix → ℕ) (D h : Matrix Ix Ix R)
    (hD : IsCx deg D) (hdeg : ∀ p q, deg p ≠ deg q + 1 → h p q = 0) (hh : D * h + h * D = 1) :
    Nonempty ({p // Even (deg p)} ≃ {p // ¬ Even (deg p)}) := by
  obtain ⟨hD1, hD2⟩ := hD
  have e1 : D * h = 1 - h * D := eq_sub_of_add_eq hh
  have e2 : D * h * D = D := by rw [e1, sub_mul, mul_assoc, hD2]; simp
  have e3 : D * h * (h * D) = 0 := by
    have : D * h = 1 - h * D := e1
    have e4 : h * D * (h * D) = h * D := by
      rw [mul_assoc, ← mul_assoc D, e2]
    rw [e1, sub_mul, e4]; simp
  set M := D + h * D * h with hM
  have hMM : M * M = 1 := by
    have : M * M = D * D + (D * h * D) * h + h * (D * h * D) + h * (D * h * (h * D)) * h := by
      rw [hM]; noncomm_ring
    rw [this, hD2, e2, e3, ← hh]; simp
  have hpar : ∀ p q, (Even (deg p) ↔ Even (deg q)) → M p q = 0 := by
    intro p q hpq
    have n1 : deg q ≠ deg p + 1 := fun e => by
      rw [e, Nat.even_add_one] at hpq; tauto
    have n2 : deg p ≠ deg q + 1 := fun e => by
      rw [e, Nat.even_add_one] at hpq; tauto
    rw [hM, Matrix.add_apply, hD1 p q n1, zero_add, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases c1 : deg p = deg s + 1
    · by_cases c2 : deg r = deg s + 1
      · rw [hdeg r q (by omega)]; simp
      · rw [hD1 s r c2]; simp
    · rw [hdeg p s c1]; simp
  exact ⟨Matrix.indexEquivOfInv
    (block_mul_block (fun p => Even (deg p)) (fun p => ¬ Even (deg p)) M hMM
      (fun p r hp hr => hpar p r (by tauto)))
    (block_mul_block (fun p => ¬ Even (deg p)) (fun p => Even (deg p)) M hMM
      (fun p r hp hr => hpar p r (by tauto)))⟩
end GlobalTheory.TorsExists
