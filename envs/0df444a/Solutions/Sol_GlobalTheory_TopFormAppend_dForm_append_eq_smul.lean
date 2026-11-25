-- Prove2me | solution 1 for GlobalTheory.TopFormAppend.dForm_append_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:25:24.688837+00:00
-- url     : https://prove2.me/submissions/4b6436e1-3492-4ce7-965f-63117711115e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KaehlerWedgeFormMapEqSmulOfBasis
import Theorems.Thm_GlobalTheory_TopForm_dForm_eq_det_smul
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_TopForm_isFreeGen_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct
set_option autoImplicit false
open GlobalTheory GlobalTheory.TopFormAppend
namespace GlobalTheory.TopFormAppend
theorem _root_.solution : ∀ {k K L : Type} [CommRing k] [CommRing K] [CommRing L] (cK : k →+* K) (cL : k →+* L)
    (j : K →+* L), j.comp cK = cL → ∀ {n r : ℕ} (x w : Fin n → K) (bK : Module.Basis (Fin n) K (Omega cK)),
    (∀ i, bK i = dFun cK (w i)) → ∀ f : K, dForm cK x = f • dForm cK w → ∀ t : Fin r → L,
    dForm cL (Fin.append t (fun i => j (x i))) = j f • dForm cL (Fin.append t (fun i => j (w i))) := by
  intro k K L _ _ _ cK cL j hc n r x w bK hbK f hf t
  let a : Matrix (Fin n) (Fin n) K := Matrix.of fun i l => bK.repr (dFun cK (x i)) l
  have ha : ∀ i, dFun cK (x i) = ∑ l, a i l • dFun cK (w l) := fun i => by
    conv_lhs => rw [← bK.sum_repr (dFun cK (x i))]
    exact Finset.sum_congr rfl fun l _ => by rw [hbK]; rfl
  have hdet : a.det = f :=
    (isFreeGen_dForm w bK hbK).1 ((dForm_eq_det_smul x w a ha).symm.trans hf)
  have hL : ∀ i, dFun cL (j (x i)) = ∑ l, j (a i l) • dFun cL (j (w l)) := fun i => by
    letI := cK.toAlgebra
    letI := cL.toAlgebra
    letI := j.toAlgebra
    haveI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' hc.symm
    have := congrArg (KaehlerDifferential.map k k K L) (ha i)
    rw [map_sum] at this
    simp only [map_smul, KaehlerDifferential.map_D] at this
    refine this.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [← algebraMap_smul L]
    rfl
  let M : Matrix (Fin (r + n)) (Fin (r + n)) L :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 (j.mapMatrix a))
  have hM : M.det = j f := by
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
      ← RingHom.map_det, hdet]
  rw [← hM]
  refine dForm_eq_det_smul _ _ M fun i => ?_
  rw [Fin.sum_univ_add]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [M, Matrix.one_apply, Fin.append_left]
  · simp [M, Fin.append_right, hL]
end GlobalTheory.TopFormAppend
