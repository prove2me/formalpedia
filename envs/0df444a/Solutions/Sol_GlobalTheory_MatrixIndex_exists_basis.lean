-- Prove2me | solution 1 for GlobalTheory.MatrixIndex.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:40.894596+00:00
-- url     : https://prove2.me/submissions/0ae9b865-0363-4b05-b16d-22809057522c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanEqMap
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.MatrixIndex
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.MatrixIndex
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    ∃ b : Module.Basis (Fin 2) F E, (∀ x, x ∈ L.O ↔ ∀ i, b.repr x i ∈ 𝒪[F]) ∧
      ∀ x, algebraMap F E (Algebra.norm F x) = x * L.cj x := by
  obtain ⟨ω, hω, e, he, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hint : ∀ a : F, a ∈ 𝒪[F] → algebraMap F E a ∈ L.O := fun a h =>
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 h
  have he' : (L.cj ω - ω) * L.cj e = 1 := by simpa [L.cj_cj] using congrArg L.cj hωe
  have hce : L.cj e = -e := by linear_combination (-e) * he' - (L.cj e) * hωe
  have hli : LinearIndependent F ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    simp only [Algebra.smul_def, mul_one] at h
    have h' := congrArg L.cj h
    simp only [map_add, map_mul, AlgEquiv.commutes, map_zero] at h'
    have ht : algebraMap F E t = 0 := by
      linear_combination e * h - e * h' - algebraMap F E t * hωe
    have hs : algebraMap F E s = 0 := by rw [ht] at h; simpa using h
    exact ⟨GlobalTheory.UnramOrder.algebraMap_inj L (by simpa using hs),
      GlobalTheory.UnramOrder.algebraMap_inj L (by simpa using ht)⟩
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [L.rank])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = ω := by simp [b]
  have hx : ∀ x, x = algebraMap F E (b.repr x 0) + algebraMap F E (b.repr x 1) * ω := by
    intro x
    have := b.sum_repr x
    rw [Fin.sum_univ_two, hb0, hb1] at this
    simpa [Algebra.smul_def] using this.symm
  refine ⟨b, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · have h1 := hx x
    have h2 := congrArg L.cj h1
    simp only [map_add, map_mul, AlgEquiv.commutes] at h2
    have h3 : algebraMap F E (b.repr x 1) = (x - L.cj x) * e := by
      linear_combination -e * h1 + e * h2 - algebraMap F E (b.repr x 1) * hωe
    have h4 : algebraMap F E (b.repr x 1) ∈ L.O := by
      rw [h3]
      exact L.O.mul_mem (L.O.sub_mem h (GlobalTheory.UnramOrder.cj_mem L h)) he
    have h5 : algebraMap F E (b.repr x 0) ∈ L.O := by
      have : algebraMap F E (b.repr x 0) = x - algebraMap F E (b.repr x 1) * ω := by
        linear_combination -h1
      rw [this]
      exact L.O.sub_mem h (L.O.mul_mem h4 hω)
    intro i
    fin_cases i
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 h5
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 h4
  · rw [hx x]
    exact L.O.add_mem (hint _ (h 0)) (L.O.mul_mem (hint _ (h 1)) hω)
  · rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, mul_one, map_sub, map_mul]
    have h1 := hx x
    have h2 := congrArg L.cj h1
    have h3 := hx (x * ω)
    have h4 := congrArg L.cj h3
    simp only [map_add, map_mul, AlgEquiv.commutes] at h2 h4
    generalize algebraMap F E (b.repr x 0) = a at *
    generalize algebraMap F E (b.repr x 1) = c at *
    generalize algebraMap F E (b.repr (x * ω) 0) = a' at *
    generalize algebraMap F E (b.repr (x * ω) 1) = c' at *
    have key : (ω - L.cj ω) * (a * c' - a' * c - x * L.cj x) = 0 := by
      linear_combination (-(L.cj x)) * h3 + x * h4 + (a' + c' * L.cj ω) * h1 - (a' + c' * ω) * h2
    linear_combination e * key - (a * c' - a' * c - x * L.cj x) * hωe
end GlobalTheory.MatrixIndex
