-- Prove2me | solution 1 for GlobalTheory.BorelModulus.delta_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:48.347518+00:00
-- url     : https://prove2.me/submissions/71f2ab16-a3d9-4843-b2ef-f03bf923c039

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousUniMat
import Theorems.Thm_GlobalTheory_BorelModulus_leftMat_det
import Theorems.Thm_GlobalTheory_BorelModulus_coord_mul
import Theorems.Thm_GlobalTheory_BorelModulus_coord_conj
import Theorems.Thm_GlobalTheory_LGrp_LeviDatum_delta_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_LGrp_modulus_measure
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_WeilM_smul_map_mulVec_pi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Matrix
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.BorelModulus
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.BorelModulus
theorem _root_.solution (q : (borelGL k (Fin n)).Q) :
    (borelGL k (Fin n)).delta q =
      distribHaarChar k (∏ p : Pos n, ((borelGL k (Fin n)).p q p.1.1 * ((borelGL k (Fin n)).p q p.1.2)⁻¹)) := by
  haveI := SplitWeil.secondCountable k
  borelize k
  borelize ↥(borelGL k (Fin n)).U
  let ν : Measure k := Measure.addHaar
  let π : Measure (Pos n → k) := Measure.pi fun _ => ν
  let e := coord k n
  let μ : Measure (borelGL k (Fin n)).U := Measure.map e.symm π
  have hm : ∀ A : Matrix (Pos n) (Pos n) k, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  haveI : μ.Regular := Measure.Regular.map e.symm
  haveI : μ.IsOpenPosMeasure := e.symm.continuous.isOpenPosMeasure_map e.symm.surjective
  haveI : μ.IsMulLeftInvariant := ⟨fun u => by
    have h1 : (fun x => u * x) ∘ e.symm = e.symm ∘ (fun y => y + e u) ∘ (leftMat u.1.val).mulVec := by
      funext y
      apply e.injective
      simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
      rw [coord_mul, Homeomorph.apply_symm_apply]
    have h2 := WeilM.smul_map_mulVec_pi ν (leftMat u.1.val) 1 (by rw [leftMat_det]; rfl)
    rw [map_one, ENNReal.coe_one, one_smul] at h2
    rw [Measure.map_map (measurable_const_mul u) hes, h1,
      ← Measure.map_map hes ((measurable_add_const _).comp (hm _)),
      ← Measure.map_map (measurable_add_const _) (hm _), h2, map_add_right_eq_self]⟩
  haveI : μ.IsHaarMeasure := {}
  set t := (borelGL k (Fin n)).p q
  rw [LeviDatum.delta_apply]
  set g : Subgroup.normalizer ((borelGL k (Fin n)).U : Set (GL (Fin n) k)) := ⟨(borelGL k (Fin n)).s t, _⟩
  set c := distribHaarChar k (∏ p : Pos n, (t p.1.1 * (t p.1.2)⁻¹))
  have hc : Continuous (conjAut (borelGL k (Fin n)).U g) := (conjAut _ g).continuous
  have h3 : (c : ENNReal) • Measure.map (conjAut _ g) μ = μ := by
    have h1 : (conjAut _ g) ∘ e.symm =
        e.symm ∘ (diagonal fun p : Pos n => ((t p.1.1 * (t p.1.2)⁻¹ : kˣ) : k)).mulVec := by
      funext y
      apply e.injective
      simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
      rw [coord_conj, Homeomorph.apply_symm_apply]
    have h2 := WeilM.smul_map_mulVec_pi ν (diagonal fun p : Pos n => ((t p.1.1 * (t p.1.2)⁻¹ : kˣ) : k))
      (∏ p : Pos n, (t p.1.1 * (t p.1.2)⁻¹)) (by rw [det_diagonal, Units.coe_prod])
    rw [Measure.map_map hc.measurable hes, h1, ← Measure.map_map hes (hm _),
      ← Measure.map_smul, h2]
  haveI : LocallyCompactSpace (borelGL k (Fin n)).U := (borelGL k (Fin n)).closed_U.locallyCompactSpace
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : (borelGL k (Fin n)).U)
  have h4 := modulus_measure _ (borelGL k (Fin n)).closed_U μ g K
  have h5 := congrArg (fun m : Measure _ => m (conjAut _ g '' K)) h3
  simp only [Measure.smul_apply, smul_eq_mul] at h5
  rw [Measure.map_apply hc.measurable
    (hK.image hc).isClosed.measurableSet,
    Set.preimage_image_eq _ (conjAut _ g).injective, h4] at h5
  exact (ENNReal.coe_injective ((ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds μ hK1).ne'
    hK.measure_lt_top.ne).1 h5)).symm
end GlobalTheory.BorelModulus
