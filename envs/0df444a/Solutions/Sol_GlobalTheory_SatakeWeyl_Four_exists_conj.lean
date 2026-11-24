-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Four.exists_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:31:33.566826+00:00
-- url     : https://prove2.me/submissions/da6c8643-ab68-4c4b-8188-e1d9465c8519

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2CartanDoubleCosets
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Four
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl.Four
theorem _root_.solution {A D ξ : L} (hA : A ≠ 0) (hD : D ≠ 0) :
    ∃ p ∈ intL L, ∃ r ∈ intL L, ∃ u ∈ intL L, ∃ w ∈ intL L, p * w - r * u = -1 ∧
      !![D, -(A * ξ); 0, A] = !![p, r; u, w] * !![A, A * ξ; 0, D] * !![p, r; u, w] := by
  have mem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  by_cases h1 : ξ ∈ intL L
  · refine ⟨-ξ, neg_mem h1, 1, one_mem _, 1, one_mem _, 0, zero_mem _, by ring, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  by_cases h2 : A * ξ / D ∈ intL L
  · refine ⟨0, zero_mem _, 1, one_mem _, 1, one_mem _, -(A * ξ / D), neg_mem h2, by ring, ?_⟩
    obtain ⟨ζ, hζ⟩ : ∃ ζ, A * ξ = D * ζ := ⟨A * ξ / D, by field_simp⟩
    rw [hζ, mul_div_cancel_left₀ _ hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  have hξ : ξ ≠ 0 := fun e => h1 (e ▸ zero_mem _)
  have inv : ∀ x : L, x ∉ intL L → x⁻¹ ∈ intL L := fun x hx => by
    rw [mem] at hx ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (not_le.1 hx).le
  refine ⟨1, one_mem _, 0, zero_mem _, -(ξ⁻¹ - (A * ξ / D)⁻¹), neg_mem (sub_mem (inv _ h1) (inv _ h2)),
    -1, neg_mem (one_mem _), by ring, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
end GlobalTheory.SatakeWeyl.Four
