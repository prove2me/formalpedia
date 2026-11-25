-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Bes.torus_moves_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:01:18.445151+00:00
-- url     : https://prove2.me/submissions/90c2bd0a-61a5-4d71-b4b1-183046fae8cb

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_TorusMovesCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torusTail_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torusTail_ge
import Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torusTail_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torusDiag_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torusDiag_mid
import Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torusDiag_uh
import Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torus_diagonal_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torus_col_conj
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_block
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselL2FixAtZero_uh_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Bes
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
namespace GlobalTheory.CompanionTheory.Bes
theorem _root_.solution :
    ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ a, c a ≠ 0) → ∃ a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, a * h = h * a) ∧ (∀ m ∈ Formalism.QuantumDeterminants.Nset k r, a * m * a⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r ∧ a⁻¹ * m * a ∈ Formalism.QuantumDeterminants.Nset k r ∧ PI.BesselL2FixAtZero.psiGen k r z (fun _ => 1) (a * m * a⁻¹) = PI.BesselL2FixAtZero.psiGen k r z c m) := by
  intro k r z c hz hc
  have hU := torusDiag_uh k hc
  have hd := torusDiag_ne k hc
  refine ⟨Matrix.diagonal (torusDiag k c), hU, fun h hh => ?_, fun m hm => ⟨?_, ?_, ?_⟩⟩
  · have hb := uw_block hh
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hb.2 i j hi]
      split_ifs with e
      · subst e; ring
      · simp
    · by_cases hj : j.val < r ∨ r + k < j.val
      · rw [hb.1 i j hj]
        split_ifs with e
        · subst e; ring
        · simp
      · rw [torusDiag_mid k c i (by omega) (by omega), torusDiag_mid k c j (by omega) (by omega)]
        ring
  · have hm' := (nset_iff m).1 hm
    refine (nset_iff _).2 ⟨uh_mul (uh_mul hU hm'.1) (uh_inv hU), ?_⟩
    rw [torus_diagonal_inv hd]
    exact torus_col_conj (fun i => mul_inv_cancel₀ (hd i)) hm'.2
  · have hm' := (nset_iff m).1 hm
    refine (nset_iff _).2 ⟨uh_mul (uh_mul (uh_inv hU) hm'.1) hU, ?_⟩
    rw [torus_diagonal_inv hd]
    exact torus_col_conj (fun i => inv_mul_cancel₀ (hd i)) hm'.2
  · unfold PI.BesselL2FixAtZero.psiGen
    congr 4
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.isLt
    have he : torusDiag k c (eI k r a) = c a * torusTail c (a.val + 1) := by
      unfold torusDiag
      rw [if_pos (by simp only [eI]; omega)]
      exact torusTail_succ c a
    beta_reduce
    rw [one_mul, torus_diagonal_inv hd]
    unfold PI.BesselL2FixAtZero.ellA
    split_ifs with h
    · have he' : torusDiag k c (eI k r ⟨a.val + 1, h⟩) = torusTail c (a.val + 1) := by
        unfold torusDiag
        rw [if_pos (by simp only [eI]; omega)]
        rfl
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, he, he']
      have := torusTail_ne hc (a.val + 1)
      field_simp
    · have hzz : Matrix.diagonal (fun i => (torusDiag k c i)⁻¹) *ᵥ z = z := by
        funext i
        rw [Matrix.mulVec_diagonal]
        by_cases hi : i.val < r ∨ r + k < i.val
        · rw [hz i hi, mul_zero]
        · rw [torusDiag_mid k c i (by omega) (by omega), inv_one, one_mul]
      rw [← Matrix.mulVec_mulVec, hzz, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, he,
        torusTail_ge c (by omega), mul_one]
end GlobalTheory.CompanionTheory.Bes
