-- Prove2me | solution 1 for GlobalTheory.WigSh.omg_mul_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:08.724797+00:00
-- url     : https://prove2.me/submissions/a1d9586a-8dd9-484d-9dfc-9fdcb9a4d44e

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
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_hpk_sq
import Theorems.Thm_GlobalTheory_LeadingMinorInv_exists_N
import Theorems.Thm_GlobalTheory_LeadingMinorInv_zhat_eq
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_apply
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_conjTranspose
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_epsI_mul_self
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_eq_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mem_Nset_iff
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_nilpotent_subgroup
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_piI_val

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
namespace GlobalTheory.WigSh
open GlobalTheory.LeadingMinorInv
namespace OmgRight
end OmgRight
open OmgRight
open Matrix in
variable {k r : ℕ} in
private lemma inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH {x : _root_.Formalism.FourierDecayAlt.Q.Mx k r} (hx : x ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) :
    x⁻¹ = _root_.Formalism.QuantumDeterminants.Hpk k r * xᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.inv_eq_UH hx
open Matrix in
variable {k r : ℕ} in
private lemma hpk_mul_hpk_mul_eq_self (X : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) :
    _root_.Formalism.QuantumDeterminants.Hpk k r * (_root_.Formalism.QuantumDeterminants.Hpk k r * X) = X := by
  rw [← Matrix.mul_assoc, _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]
open Matrix in
variable {k r : ℕ} in
private lemma hpk_conjTranspose_eq_self' : (_root_.Formalism.QuantumDeterminants.Hpk k r)ᴴ = _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_conjTranspose
open Matrix in
variable {k r : ℕ} in
private lemma adjugate_upUni_last_apply {m : ℕ} {U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hU : _root_.GlobalTheory.LeadingMinorInv.UpUni U) (a : Fin (m + 1)) :
    U.adjugate (Fin.last m) a = if a = Fin.last m then 1 else 0 := by
  rw [adjugate_apply, det_of_upperTriangular]
  · simp [updateRow_apply, Pi.single_apply, hU.2]
  · intro i j hij
    simp only [updateRow_apply]
    split_ifs with h
    · subst h
      rw [Pi.single_apply, if_neg]
      exact (hij.trans_le (Fin.le_last _)).ne
    · exact hU.1 i j hij
open Matrix in
variable {k r : ℕ} in
private lemma flagMat_mulVec_eq_sum_smul_fvec (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ) :
    _root_.GlobalTheory.LeadingMinorInv.flagMat k r z *ᵥ c = ∑ a, c a • _root_.Formalism.QuantumDeterminants.fvec k r z a := by
  ext i
  simp [mulVec, dotProduct, _root_.GlobalTheory.LeadingMinorInv.flagMat, Finset.sum_apply, mul_comm]
open Matrix in
variable {k r : ℕ} in
private lemma rW_mulVec_adjugate_zhat_single_last_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.GlobalTheory.WigSh.omg k r z z' g = _root_.Formalism.FourierDecayAlt.D.prW k r z'
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) *ᵥ
        ((_root_.Formalism.QuantumDeterminants.Zhat k r z z' g).adjugateᴴ *ᵥ Pi.single (Fin.last r) 1)) := by
  unfold _root_.GlobalTheory.WigSh.omg
  rw [← mulVec_mulVec _ (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z), flagMat_mulVec_eq_sum_smul_fvec]
  simp [mulVec_single_one, conjTranspose_apply]
open Matrix in
variable {k r : ℕ} in
private lemma gram_eq_conjTranspose_hpk_mul_flagMat_mul (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.Formalism.QuantumDeterminants.Zhat k r z z' g = (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') := by
  rw [_root_.GlobalTheory.LeadingMinorInv.zhat_eq]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose_eq_self',
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.Hpk k r), _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]
open Matrix in
variable {k r : ℕ} in
private lemma prW_mulVec_eq_of_mem_nset_of_tail_eq_zero {z' : Fin (2 * r + k + 1) → ℂ} {m : _root_.Formalism.FourierDecayAlt.Q.Mx k r}
    (hm : m ∈ _root_.Formalism.QuantumDeterminants.Nset k r) {p : Fin (2 * r + k + 1) → ℂ}
    (hp : ∀ j : Fin (2 * r + k + 1), r + k < ↑j → p j = 0) :
    _root_.Formalism.FourierDecayAlt.D.prW k r z' (m *ᵥ p) = _root_.Formalism.FourierDecayAlt.D.prW k r z' p := by
  have hNC := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff m).1 hm).2
  have hb : (fun i : Fin (2 * r + k + 1) => if r ≤ ↑i ∧ ↑i ≤ r + k then (m *ᵥ p) i else 0) =
      (fun i : Fin (2 * r + k + 1) => if r ≤ ↑i ∧ ↑i ≤ r + k then p i else 0) := by
    ext i
    split_ifs with hi
    · simp only [mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · rw [hNC i i hi.2 (min_le_left _ _)]
        simp
      · intro j _ hji
        by_cases hj : (j : ℕ) ≤ r + k
        · rw [hNC i j hj (le_trans (min_le_right _ _) hi.1), if_neg (Ne.symm hji)]
          simp
        · rw [hp j (by omega)]
          simp
      · simp
    · rfl
  simp only [_root_.Formalism.FourierDecayAlt.D.prW]
  rw [hb]
open Matrix in
variable {k r : ℕ} in
private lemma mulVec_adjugate_single_last_apply_eq_zero_of_lt (z' : Fin (2 * r + k + 1) → ℂ)
    (Q : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) (j : Fin (2 * r + k + 1))
    (hj : r + k < ↑j) :
    (Q *ᵥ ((Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugateᴴ *ᵥ
      Pi.single (Fin.last r) 1)) j = 0 := by
  have hJP : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) i c,
      (_root_.Formalism.QuantumDeterminants.Hpk k r * X) i c = _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI k r i * X (_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r i) c := by
    intro X i c
    have hJa : ∀ i l, _root_.Formalism.QuantumDeterminants.Hpk k r i l =
        if l = _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r i then _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI k r i else 0 :=
      fun i l => _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_apply i l
    rw [mul_apply]
    simp only [hJa, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hj2 := j.isLt
  obtain ⟨b, hb⟩ : ∃ b : Fin r, (b : ℕ) = 2 * r + k - j := ⟨⟨2 * r + k - j, by omega⟩, rfl⟩
  have hpi : _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r (_root_.Formalism.QuantumDeterminants.eI k r b) = j := by
    have hb2 := b.isLt
    apply Fin.ext
    rw [_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI_val, if_neg] <;> simp only [_root_.Formalism.QuantumDeterminants.eI] <;> omega
  have key : (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')ᴴ *
      (Q * (Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugateᴴ) =
      ((Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugate *
        (Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')))ᴴ := by
    rw [conjTranspose_mul (adjugate _), conjTranspose_mul Qᴴ, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have h1 := congrFun (congrFun key (Fin.castSucc b)) (Fin.last r)
  rw [adjugate_mul] at h1
  simp only [conjTranspose_apply, Matrix.smul_apply, one_apply,
    if_neg (Fin.castSucc_lt_last b).ne', smul_zero, star_zero] at h1
  rw [conjTranspose_mul, hpk_conjTranspose_eq_self', Matrix.mul_assoc, mul_apply,
    Finset.sum_eq_single (_root_.Formalism.QuantumDeterminants.eI k r b)] at h1
  · rw [hJP, hpi] at h1
    have heps := _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI_mul_self (k := k) (r := r) (_root_.Formalism.QuantumDeterminants.eI k r b)
    have hF : (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z')ᴴ (Fin.castSucc b) (_root_.Formalism.QuantumDeterminants.eI k r b) = 1 := by
      simp [conjTranspose_apply, _root_.GlobalTheory.LeadingMinorInv.flagMat, _root_.Formalism.QuantumDeterminants.fvec, _root_.Formalism.QuantumDeterminants.bvec]
    rw [hF, one_mul] at h1
    rw [mulVec_mulVec]
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rcases mul_eq_zero.1 h1 with h | h
    · rw [h, zero_mul] at heps
      exact absurd heps zero_ne_one
    · exact h
  · intro l _ hl
    simp [conjTranspose_apply, _root_.GlobalTheory.LeadingMinorInv.flagMat, _root_.Formalism.QuantumDeterminants.fvec, _root_.Formalism.QuantumDeterminants.bvec, Pi.single_apply, hl]
  · simp
end GlobalTheory.WigSh
end
end

set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open GlobalTheory GlobalTheory.WigSh
open GlobalTheory.LeadingMinorInv
open OmgRight
open Matrix
namespace GlobalTheory.WigSh
namespace _root_.GlobalTheory.WigSh
theorem _root_.solution : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (g m : _root_.Formalism.FourierDecayAlt.Q.Mx k r), _root_.Formalism.QuantumDeterminants.inWb k r z → _root_.Formalism.QuantumDeterminants.inWb k r z' →
    g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) → m ∈ _root_.Formalism.QuantumDeterminants.Nset k r →
    _root_.GlobalTheory.WigSh.omg k r z z' (g * m) = _root_.GlobalTheory.WigSh.omg k r z z' g := by
  intro k r z z' g m _ hz' _ hm
  obtain ⟨U, hU, hmF⟩ := _root_.GlobalTheory.LeadingMinorInv.exists_N k r z' hz' m hm
  have hmUH : m ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff m).1 hm).1
  have hQm : _root_.Formalism.QuantumDeterminants.Hpk k r * (g * m)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z =
      m⁻¹ * (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) := by
    rw [inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH hmUH]
    simp only [conjTranspose_mul, Matrix.mul_assoc, hpk_mul_hpk_mul_eq_self]
  have hC : (m⁻¹ * (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z))ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') =
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
        (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')) * U := by
    rw [conjTranspose_mul m⁻¹, inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH hmUH]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose_eq_self',
      Matrix.mul_assoc, hpk_mul_hpk_mul_eq_self, hmF]
  have he : U.adjugateᴴ *ᵥ Pi.single (Fin.last r) 1 = Pi.single (Fin.last r) 1 := by
    ext a
    simp [mulVec_single_one, conjTranspose_apply, adjugate_upUni_last_apply hU, Pi.single_apply]
  rw [rW_mulVec_adjugate_zhat_single_last_eq, rW_mulVec_adjugate_zhat_single_last_eq, gram_eq_conjTranspose_hpk_mul_flagMat_mul, gram_eq_conjTranspose_hpk_mul_flagMat_mul, hQm, hC, adjugate_mul_distrib, conjTranspose_mul,
    ← mulVec_mulVec _ (adjugate _)ᴴ, he, ← mulVec_mulVec _ m⁻¹]
  exact prW_mulVec_eq_of_mem_nset_of_tail_eq_zero ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.nilpotent_subgroup k r).2.2 m hm)
    (mulVec_adjugate_single_last_apply_eq_zero_of_lt _ _)
end _root_.GlobalTheory.WigSh
end GlobalTheory.WigSh
