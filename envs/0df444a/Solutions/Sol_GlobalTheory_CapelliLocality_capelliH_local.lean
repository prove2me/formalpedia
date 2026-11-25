-- Prove2me | solution 1 for GlobalTheory.CapelliLocality.capelliH_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:02:04.006977+00:00
-- url     : https://prove2.me/submissions/85bf9945-5ed3-4cd4-a90f-9fe0b5c0aec0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CapelliOperatorUnitaryGroupLocal
import Theorems.Thm_GlobalTheory_CapelliLocality_foldr_congr
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_Hinv
import Theorems.Thm_Formalism_REAL_Jm_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory GlobalTheory.CapelliLocality
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.CapelliLocality
theorem _root_.solution : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  intro n ε E _ _ H P Q F₁ F₂ u g hQP hPQ hH hF hg
  have hinv := ioh_Hinv ε H P Q hQP hPQ hH
  have hc : Pᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQP, Matrix.conjTranspose_one]
  have hHK : H * H⁻¹ = 1 := by
    rw [hinv]
    calc H * (Q * Jm ε * Qᴴ) = Pᴴ * (Jm ε * ((P * Q) * (Jm ε * Qᴴ))) := by
          rw [hH]; simp only [Matrix.mul_assoc]
      _ = Pᴴ * Qᴴ := by
          rw [hPQ, Matrix.one_mul, ← Matrix.mul_assoc (Jm ε), Jm_mul_self, Matrix.one_mul]
      _ = 1 := hc
  have hKH : H⁻¹ * H = 1 := mul_eq_one_comm.mp hHK
  have hJ : (Jm ε)ᴴ = Jm ε := by
    unfold Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : ε i <;> simp [h]
  have hHh : Hᴴ = H := by
    rw [hH]
    simp only [Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  unfold capelliH qdetOp qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 : (List.ofFn fun k : Fin n => Formalism.QuantumDeterminants.Top (E := E) (EabH H) (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k)) =
        (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), σ k, k)).map
          fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2 := by
    rw [List.map_ofFn]; rfl
  rw [e1]
  exact foldr_congr H hKH hHK hHh _ hF g hg
end GlobalTheory.CapelliLocality
