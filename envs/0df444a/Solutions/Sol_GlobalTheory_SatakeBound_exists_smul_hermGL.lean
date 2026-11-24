-- Prove2me | solution 1 for GlobalTheory.SatakeBound.exists_smul_hermGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:25:41.394029+00:00
-- url     : https://prove2.me/submissions/c5c81207-b12c-40b1-b75d-d3aeee92d46c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SatakeTrivialRangeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HermiteReductionUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Theorems.Thm_GlobalTheory_SatakeBound_exists_hermMat
import Theorems.Thm_GlobalTheory_SatakeBound_val_hermGL
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitWeil_iwasawa_blockTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open GlobalTheory GlobalTheory.SatakeBound
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {p : 𝒪[k]}
namespace GlobalTheory.SatakeBound
theorem _root_.solution (hp : Irreducible p) {x : GL (Fin n) k} (hx : x ∈ KO k (Fin n)) (a : Fin n → ℕ)
    (c : HermIdx p a) : ∃ (a' : Fin n → ℕ) (c' : HermIdx p a'), ∑ i, a' i = ∑ i, a i ∧
      (hermGL hp a' c' : GL (Fin n) k ⧸ KO k (Fin n)) = x • (hermGL hp a c : GL (Fin n) k ⧸ KO k (Fin n)) := by
  obtain ⟨b, hb, w, hw, e⟩ := iwasawa_blockTriangular k (Fin n) Fin.val (x * hermGL hp a c)
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨W, rfl⟩ := hw
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := X.val * hermMat p a c * (W⁻¹).val
  have hB : b.val = (algebraMap 𝒪[k] k).mapMatrix B := by
    rw [eq_mul_inv_of_mul_eq e.symm, ← map_inv, map_mul, map_mul]
    rfl
  have h1 : ∀ i j, j < i → B i j = 0 := fun i j h => Subtype.ext ((congrFun (congrFun hB i) j).symm.trans (hb h))
  have hd : B.det ≠ 0 := by
    simp only [B, Matrix.det_mul, det_hermMat]
    exact mul_ne_zero (mul_ne_zero (Matrix.isUnits_det_units _).ne_zero (pow_ne_zero _ hp.ne_zero))
      (Matrix.isUnits_det_units _).ne_zero
  rw [Matrix.det_of_isUpperTriangular (M := B) fun _ _ h => h1 _ _ h, Finset.prod_ne_zero_iff] at hd
  obtain ⟨a', c', U, hU⟩ := exists_hermMat hp B h1 fun i => hd i (Finset.mem_univ i)
  refine ⟨a', c', ?_, ?_⟩
  · have h := congrArg Matrix.det hU
    simp only [B, Matrix.det_mul, det_hermMat] at h
    refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hp hp 1 (Matrix.GeneralLinearGroup.det (X * W⁻¹ * U)) _ _ ?_
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul, Units.val_one, h]
    ring
  · have : hermGL hp a' c' = b * Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) U := by
      apply Units.ext
      rw [val_hermGL, hU, map_mul, ← hB]
      rfl
    rw [this, MulAction.Quotient.smul_mk, smul_eq_mul, e, QuotientGroup.mk_mul_of_mem (s := KO k (Fin n)) _ (MonoidHom.mem_range.2 ⟨U, rfl⟩),
      QuotientGroup.mk_mul_of_mem (s := KO k (Fin n)) _ (MonoidHom.mem_range.2 ⟨W, rfl⟩)]
end GlobalTheory.SatakeBound
