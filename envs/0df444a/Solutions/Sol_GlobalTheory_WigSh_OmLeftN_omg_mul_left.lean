-- Prove2me | solution 1 for GlobalTheory.WigSh.OmLeftN.omg_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:19.210909+00:00
-- url     : https://prove2.me/submissions/600e0a88-f600-4a9b-979a-dcb0238b1280

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingMinorInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgMulLeft
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_hpk_sq
import Theorems.Thm_GlobalTheory_LeadingMinorInv_exists_N
import Theorems.Thm_GlobalTheory_LeadingMinorInv_zhat_eq
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_conjTranspose
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mem_Nset_iff

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
namespace GlobalTheory.WigSh.OmLeftN
open Matrix in
variable {k r : ℕ} in
private lemma flagMat_mulVec_eq_sum_fvec (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ) :
    _root_.GlobalTheory.LeadingMinorInv.flagMat k r z *ᵥ c = ∑ a, c a • _root_.Formalism.QuantumDeterminants.fvec k r z a := by
  ext i
  simp [mulVec, dotProduct, _root_.GlobalTheory.LeadingMinorInv.flagMat, Finset.sum_apply, mul_comm]
open Matrix in
variable {k r : ℕ} in
private lemma rW_mulVec_adjugate_zhat_single_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.GlobalTheory.WigSh.omg k r z z' g = _root_.Formalism.FourierDecayAlt.D.prW k r z'
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) *ᵥ
        ((_root_.Formalism.QuantumDeterminants.Zhat k r z z' g).adjugateᴴ *ᵥ Pi.single (Fin.last r) 1)) := by
  unfold _root_.GlobalTheory.WigSh.omg
  rw [← mulVec_mulVec _ (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z), flagMat_mulVec_eq_sum_fvec]
  simp [mulVec_single_one, conjTranspose_apply]
open Matrix in
variable {k r : ℕ} in
private lemma conjTranspose_hpk : (_root_.Formalism.QuantumDeterminants.Hpk k r)ᴴ = _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_conjTranspose
open Matrix in
variable {k r : ℕ} in
private lemma gram_eq_upper_bounds (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.Formalism.QuantumDeterminants.Zhat k r z z' g = (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') := by
  rw [_root_.GlobalTheory.LeadingMinorInv.zhat_eq]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_hpk,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.Hpk k r), _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]
open Matrix in
variable {k r : ℕ} in
private lemma mul_adjugate_conjTranspose_eq_of_det_eq_one {m n : ℕ} (X : Matrix (Fin n) (Fin m) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (Y : Matrix (Fin n) (Fin m) ℂ) (hU : U.det = 1) :
    (X * U) * ((X * U)ᴴ * Y).adjugateᴴ = X * (Xᴴ * Y).adjugateᴴ := by
  rw [conjTranspose_mul, Matrix.mul_assoc Uᴴ, adjugate_mul_distrib, conjTranspose_mul,
    adjugate_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc X U,
    ← Matrix.mul_assoc U, mul_adjugate, hU, one_smul, Matrix.one_mul]
open Matrix in
variable {k r : ℕ} in
private lemma det_eq_one_of_upUni {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : _root_.GlobalTheory.LeadingMinorInv.UpUni U) : U.det = 1 := by
  rw [det_of_upperTriangular (fun i j h => hU.1 i j h)]
  simp [hU.2]
end GlobalTheory.WigSh.OmLeftN
end
end

set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.OmLeftN
open Matrix
namespace GlobalTheory.WigSh.OmLeftN
namespace _root_.GlobalTheory.WigSh.OmLeftN
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g n : _root_.Formalism.FourierDecayAlt.Q.Mx k r) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z)
    (hn : n ∈ _root_.Formalism.QuantumDeterminants.Nset k r) :
    _root_.GlobalTheory.WigSh.omg k r z z' (n * g) = _root_.GlobalTheory.WigSh.omg k r z z' g := by
  obtain ⟨U, hU, hnF⟩ := _root_.GlobalTheory.LeadingMinorInv.exists_N k r z hz n hn
  have hnU : nᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * n = _root_.Formalism.QuantumDeterminants.Hpk k r := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff n).1 hn).1
  have hQ : _root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z =
      _root_.Formalism.QuantumDeterminants.Hpk k r * (n * g)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z * U := by
    have key : nᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * (n * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)) =
        _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z := by
      simp only [← Matrix.mul_assoc, hnU]
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← hnF, key]
  rw [rW_mulVec_adjugate_zhat_single_last, rW_mulVec_adjugate_zhat_single_last, gram_eq_upper_bounds, gram_eq_upper_bounds, mulVec_mulVec, mulVec_mulVec, hQ,
    mul_adjugate_conjTranspose_eq_of_det_eq_one _ _ _ (det_eq_one_of_upUni hU)]
end _root_.GlobalTheory.WigSh.OmLeftN
end GlobalTheory.WigSh.OmLeftN
