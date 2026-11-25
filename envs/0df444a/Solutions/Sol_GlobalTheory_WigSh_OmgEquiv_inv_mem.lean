-- Prove2me | solution 1 for GlobalTheory.WigSh.OmgEquiv.inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:04:35.593905+00:00
-- url     : https://prove2.me/submissions/bff2c4fd-d38d-41cb-af82-5ff39d910ee1

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
namespace GlobalTheory.WigSh.OmgEquiv
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}
private lemma hpk_apply_of_outer {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if i.val + l.val = 2 * r + k then 1 else 0 := by
  have := i.isLt
  have := l.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)
private lemma hpk_apply_of_middle {i : Fin (2 * r + k + 1)} (hi : r ≤ i.val ∧ i.val ≤ r + k) (l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if i = l then (if i.val = r + k then -1 else 1) else 0 := by
  have := i.isLt
  have := l.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)
private lemma hpk_mul_hpk : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have := i.isLt
  have := j.isLt
  by_cases hout : i.val < r ∨ r + k < i.val
  · have hp : 2 * r + k - i.val < 2 * r + k + 1 := by omega
    have hp' : 2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val := by omega
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, hp⟩]
    · rw [hpk_apply_of_outer hout, hpk_apply_of_outer (i := ⟨2 * r + k - i.val, hp⟩) hp']
      simp only [Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega) | norm_num
    · intro l _ hl
      rw [hpk_apply_of_outer hout, if_neg, zero_mul]
      intro e
      exact hl (Fin.ext (show l.val = 2 * r + k - i.val by omega))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hmid : r ≤ i.val ∧ i.val ≤ r + k := by omega
    rw [Finset.sum_eq_single i]
    · rw [hpk_apply_of_middle hmid, hpk_apply_of_middle hmid]
      by_cases hij : i = j
      · subst hij
        by_cases hv : i.val = r + k <;> simp [hv]
      · simp [hij]
    · intro l _ hl
      rw [hpk_apply_of_middle hmid, if_neg (Ne.symm hl), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
private lemma hpk_conjTranspose_hpk_mul_eq_one_of_mem_UH {g : Mx k r} (hg : g ∈ UH (Hpk k r)) :
    Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have e : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [e, hpk_mul_hpk]
private lemma inv_eq_hpk_mul_conjTranspose_mul_hpk {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = Hpk k r * gᴴ * Hpk k r :=
  Matrix.inv_eq_left_inv (hpk_conjTranspose_hpk_mul_eq_one_of_mem_UH hg)
private lemma inv_mul_cancel_of_mem_UH {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ * g = 1 := by
  rw [inv_eq_hpk_mul_conjTranspose_mul_hpk hg]
  exact hpk_conjTranspose_hpk_mul_eq_one_of_mem_UH hg
private lemma mul_inv_cancel_of_mem_UH {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv (h := Matrix.isUnit_det_of_left_inverse (hpk_conjTranspose_hpk_mul_eq_one_of_mem_UH hg))
private lemma inv_mem_UH_jet_harmonics {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have e : gᴴ * Hpk k r * g = Hpk k r := hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [e]
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [mul_inv_cancel_of_mem_UH hg, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
private lemma inv_mulVec_eq_of_mulVec_eq_of_mem_UH {g : Mx k r} (hg : g ∈ UH (Hpk k r)) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : g *ᵥ v = v) : g⁻¹ *ᵥ v = v := by
  calc g⁻¹ *ᵥ v = g⁻¹ *ᵥ (g *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, inv_mul_cancel_of_mem_UH hg, Matrix.one_mulVec]
end GlobalTheory.WigSh.OmgEquiv
namespace GlobalTheory.WigSh
open OmgEquiv
end GlobalTheory.WigSh
end
end

set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.OmgEquiv
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}
namespace GlobalTheory.WigSh.OmgEquiv
theorem _root_.solution {h : Mx k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  simp only [Formalism.QuantumDeterminants.UWset, Set.mem_ofPred_eq] at hh ⊢
  obtain ⟨hU, hb, hz⟩ := hh
  exact ⟨inv_mem_UH_jet_harmonics hU, fun a => ⟨inv_mulVec_eq_of_mulVec_eq_of_mem_UH hU (hb a).1, inv_mulVec_eq_of_mulVec_eq_of_mem_UH hU (hb a).2⟩, inv_mulVec_eq_of_mulVec_eq_of_mem_UH hU hz⟩
end GlobalTheory.WigSh.OmgEquiv
