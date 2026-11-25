-- Prove2me | solution 1 for GlobalTheory.HL.TupleJac.exists_int_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:34:24.496035+00:00
-- url     : https://prove2.me/submissions/28dcf55f-b09e-4ace-a7c6-1f95e2a63b46

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometry
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_ContModel_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_sub_cj_mul_eq_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TupleJac
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.TupleJac
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    ∃ c : Module.Basis (Fin 2) F E, (∀ x, x ∈ L.O ↔ ∀ i, c.repr x i ∈ 𝒪[F]) ∧
      ∀ x, algebraMap F E (Algebra.norm F x) = x * L.cj x := by
  obtain ⟨ω, hω, e, he, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hu : IsUnit (ω - L.cj ω) := IsUnit.of_mul_eq_one e hωe
  have hli : LinearIndependent F ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    simp only [Algebra.smul_def, mul_one] at h
    have h' := congrArg L.cj h
    simp only [map_add, map_mul, AlgEquiv.commutes, map_zero] at h'
    have hb : algebraMap F E b = 0 := hu.mul_left_eq_zero.1 (by linear_combination h - h')
    have ha : algebraMap F E a = 0 := by rw [hb] at h; simpa using h
    exact ⟨hinj (by simpa using ha), hinj (by simpa using hb)⟩
  let c : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [L.rank])
  have hc0 : c 0 = 1 := by simp [c]
  have hc1 : c 1 = ω := by simp [c]
  have hx : ∀ x, x = algebraMap F E (c.repr x 0) + algebraMap F E (c.repr x 1) * ω := by
    intro x
    have := c.sum_repr x
    simp only [Fin.sum_univ_two, hc0, hc1, Algebra.smul_def, mul_one] at this
    exact this.symm
  have hr : ∀ a b : F, c.repr (algebraMap F E a + algebraMap F E b * ω) 0 = a ∧
      c.repr (algebraMap F E a + algebraMap F E b * ω) 1 = b := by
    intro a b
    have : algebraMap F E a + algebraMap F E b * ω = a • c 0 + b • c 1 := by
      simp [hc0, hc1, Algebra.smul_def]
    rw [this]
    simp
  refine ⟨c, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · have h1 := congrArg L.cj (hx x)
    simp only [map_add, map_mul, AlgEquiv.commutes] at h1
    have hb : algebraMap F E (c.repr x 1) ∈ L.O := by
      have : algebraMap F E (c.repr x 1) = (x - L.cj x) * e := by
        linear_combination (-e) * hx x + e * h1 - algebraMap F E (c.repr x 1) * hωe
      rw [this]
      exact L.O.mul_mem (L.O.sub_mem h (GlobalTheory.UnramOrder.cj_mem L h)) he
    have ha : algebraMap F E (c.repr x 0) ∈ L.O := by
      have : algebraMap F E (c.repr x 0) = x - algebraMap F E (c.repr x 1) * ω := by
        linear_combination - hx x
      rw [this]
      exact L.O.sub_mem h (L.O.mul_mem hb hω)
    intro i
    fin_cases i
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 ha
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 hb
  · rw [hx x]
    exact L.O.add_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (h 0))
      (L.O.mul_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (h 1)) hω)
  · obtain ⟨t, ht⟩ := (L.cj_fix (ω + L.cj ω)).1 (by simp [L.cj_cj, add_comm])
    obtain ⟨N, hN⟩ := (L.cj_fix (ω * L.cj ω)).1 (by simp [L.cj_cj, mul_comm])
    obtain ⟨a, b, rfl⟩ : ∃ a b : F, x = algebraMap F E a + algebraMap F E b * ω := ⟨_, _, hx x⟩
    have h2 : (algebraMap F E a + algebraMap F E b * ω) * ω
        = algebraMap F E (-(b * N)) + algebraMap F E (a + b * t) * ω := by
      simp only [map_add, map_mul, map_neg, ht, hN]; ring
    rw [Algebra.norm_eq_matrix_det c, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hc0, hc1, mul_one, h2, (hr _ _).1, (hr _ _).2]
    simp only [map_add, map_mul, map_neg, map_sub, ht, hN, AlgEquiv.commutes]
    ring
end GlobalTheory.HL.TupleJac
