-- Prove2me | solution 1 for GlobalTheory.DiagBlock.detPowDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:06:06.200384+00:00
-- url     : https://prove2.me/submissions/80a1915f-537e-428e-b5e8-07762581db3e

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Theorems.Thm_GlobalTheory_DiagBlock_coeff_kill
import Theorems.Thm_GlobalTheory_DiagBlock_kill_det_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
namespace GlobalTheory.DiagBlock
section Kill
variable {R : Type} [CommRing R] {σ : Type}
end Kill
private lemma diag_single_sum_apply (n0 n Y : ℕ) (ρ c : Fin n) :
    (∑ ρ' ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ' => n0 ≤ ρ'.val), Finsupp.single (ρ', ρ') Y) (ρ, c) =
      if n0 ≤ ρ.val ∧ c = ρ then Y else 0 := by
  rw [Finsupp.finsetSum_apply]
  by_cases hρ : n0 ≤ ρ.val
  · rw [Finset.sum_eq_single ρ]
    · by_cases hc : c = ρ
      · subst hc; simp [hρ]
      · simp [hc]
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ ρ, hρ⟩) h
  · rw [if_neg (fun h => hρ h.1)]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hb' : b ≠ ρ := fun h => hρ (h ▸ (Finset.mem_filter.1 hb).2)
    simp [hb']
end GlobalTheory.DiagBlock
end
end

set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
namespace GlobalTheory.DiagBlock
theorem _root_.solution : DetPowDiag := by
  intro R _ n0 n hn Y e he
  classical
  have hS : ∀ x : Fin n × Fin n, (n0 ≤ x.1.val ∧ x.2 ≠ x.1) → e x = 0 := by
    rintro ⟨ρ, c⟩ ⟨h1, h2⟩
    rw [he ρ c h1, if_neg h2]
  have hk := coeff_kill (R := R) (fun x : Fin n × Fin n => n0 ≤ x.1.val ∧ x.2 ≠ x.1)
    ((Matrix.of fun b c : Fin n => (MvPolynomial.X (b, c) : MvPolynomial (Fin n × Fin n) R)).det ^ Y) e
  rw [if_pos hS] at hk
  rw [← hk, kill_det_pow _ hn (fun b c => (b, c)) (fun ρ c => Iff.rfl) Y]
  have hsplit : e = e.filter (fun x => x.1.val < n0) +
      ∑ ρ ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ => n0 ≤ ρ.val), Finsupp.single (ρ, ρ) Y := by
    ext ⟨ρ, c⟩
    rw [Finsupp.add_apply, Finsupp.filter_apply, diag_single_sum_apply]
    by_cases hρ : n0 ≤ ρ.val
    · simp [hρ, he ρ c hρ, not_lt.2 hρ]
    · simp [hρ, not_le.1 hρ]
  conv_lhs => rw [hsplit]
  rw [MvPolynomial.coeff_mul_monomial, mul_one]
end GlobalTheory.DiagBlock
