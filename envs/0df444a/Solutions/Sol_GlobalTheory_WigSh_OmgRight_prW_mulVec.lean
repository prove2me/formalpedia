-- Prove2me | solution 1 for GlobalTheory.WigSh.OmgRight.prW_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:54.408364+00:00
-- url     : https://prove2.me/submissions/65b81e9a-7ada-4df7-a184-ab7479aed8a8

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingMinorInvariant
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HpkConjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open GlobalTheory GlobalTheory.WigSh
open GlobalTheory.LeadingMinorInv
open GlobalTheory.WigSh.OmgRight
namespace GlobalTheory.WigSh.OmgRight
theorem _root_.solution {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {n : Mx k r} (hn : n ∈ Formalism.QuantumDeterminants.Nset k r)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) :
    Formalism.FourierDecayAlt.D.prW k r z (n *ᵥ v) = Formalism.FourierDecayAlt.D.prW k r z v := by
  have key : (fun i : Fin (2 * r + k + 1) => if r ≤ i.val ∧ i.val ≤ r + k then (n *ᵥ v) i else 0) =
      (fun i : Fin (2 * r + k + 1) => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0) := by
    ext i
    split_ifs with hi
    · simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · rw [hn.2.2 i i (by omega) (by omega) (by omega), if_pos rfl, one_mul]
      · intro j _ hji
        by_cases hj1 : j.val < r
        · have e : eI k r ⟨j.val, hj1⟩ = j := by ext; simp [eI]
          have := hn.2.1 ⟨j.val, hj1⟩ i (by simp; omega)
          rw [e, if_neg (Ne.symm hji)] at this
          rw [this, zero_mul]
        · by_cases hj2 : j.val ≤ r + k
          · rw [hn.2.2 i j (by omega) hj2 (by omega), if_neg (Ne.symm hji), zero_mul]
          · have hlt : 2 * r + k - j.val < r := by omega
            have e : esI k r ⟨2 * r + k - j.val, hlt⟩ = j := by ext; simp [esI]; omega
            have := hv ⟨2 * r + k - j.val, hlt⟩
            rw [e] at this
            rw [this, mul_zero]
      · simp
    · rfl
  unfold Formalism.FourierDecayAlt.D.prW
  simp only [key]
end GlobalTheory.WigSh.OmgRight
