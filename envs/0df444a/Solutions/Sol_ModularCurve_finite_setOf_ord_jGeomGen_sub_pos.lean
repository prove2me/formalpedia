-- Prove2me | solution 1 for ModularCurve.finite_setOf_ord_jGeomGen_sub_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/72f79263-d646-558d-b935-21278bf0074d

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IntermediateField Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "jGeomGen jqModC jqNModC modularFunctionFieldC jqModC_mem ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC nonempty_modularPolynomialData finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC eq_charLGeomPlaceOfPoint_of_ord_pos"
p2m_open "ModularCurve"

section Shortcuts

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

private scoped instance (priority := high) ell1aAlgebraKC : Algebra K ↥(modularFunctionFieldC K N) :=
  inferInstance

private scoped instance (priority := high) ell1aModuleKC : Module K ↥(modularFunctionFieldC K N) :=
  inferInstance

private scoped instance (priority := high) ell1aMulActionKC : MulAction K ↥(modularFunctionFieldC K N) :=
  inferInstance

private scoped instance (priority := high) ell1aAlgebraKJ :
    Algebra K ↥(IntermediateField.adjoin K {jGeomGen K N}) :=
  inferInstance

private scoped instance (priority := high) ell1aAlgebraJC :
    Algebra ↥(IntermediateField.adjoin K {jGeomGen K N}) ↥(modularFunctionFieldC K N) :=
  inferInstance

private scoped instance (priority := high) ell1aModuleJC :
    Module ↥(IntermediateField.adjoin K {jGeomGen K N}) ↥(modularFunctionFieldC K N) :=
  inferInstance

private scoped instance (priority := high) ell1aMulActionJC :
    MulAction ↥(IntermediateField.adjoin K {jGeomGen K N}) ↥(modularFunctionFieldC K N) :=
  inferInstance

private scoped instance (priority := high) ell1aTowerKJC :
    IsScalarTower K ↥(IntermediateField.adjoin K {jGeomGen K N}) ↥(modularFunctionFieldC K N) :=
  inferInstance

private scoped instance (priority := high) ell1aIsIntegralJC
    [FiniteDimensional ↥(IntermediateField.adjoin K {jGeomGen K N}) ↥(modularFunctionFieldC K N)] :
    Algebra.IsIntegral ↥(IntermediateField.adjoin K {jGeomGen K N}) ↥(modularFunctionFieldC K N) :=
  Algebra.IsIntegral.of_finite _ _

end Shortcuts

section JLine

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

private theorem jGeomGen_transcendental : Transcendental K (jGeomGen K N) := by
  have h : Transcendental K
      (algebraMap (modularFunctionFieldC K N) (LaurentSeries K) (jGeomGen K N)) :=
    transcendental_jqModC K
  exact (transcendental_algebraMap_iff
    (algebraMap (modularFunctionFieldC K N) (LaurentSeries K)).injective).mp h

private def jLineEquivC : RatFunc K ≃ₐ[K] ↥(IntermediateField.adjoin K {jGeomGen K N}) :=
  RatFunc.algEquivOfTranscendental (jGeomGen K N) (jGeomGen_transcendental K N)

private def jLineEquivOneC :
    ↥(IntermediateField.adjoin K {jGeomGen K N}) ≃ₐ[K] ↥(modularFunctionFieldC K 1) :=
  (jLineEquivC K N).symm.trans (ratFuncEquivCharLOneC K)

private theorem jLineEquivOneC_commutes (c : K) :
    (jLineEquivOneC K N).toRingEquiv (algebraMap K _ c) = algebraMap K _ c :=
  (jLineEquivOneC K N).commutes c

private theorem ratFuncEquivCharLOneC_X :
    ratFuncEquivCharLOneC K RatFunc.X = (⟨jqModC K, jqModC_mem K 1⟩ : modularFunctionFieldC K 1) := by
  refine Subtype.ext ?_
  show ((RatFunc.algEquivOfTranscendental (jqModC K) (transcendental_jqModC K) RatFunc.X :
      ↥(IntermediateField.adjoin K {jqModC K})) : LaurentSeries K) = jqModC K
  exact RatFunc.algEquivOfTranscendental_X (jqModC K) (transcendental_jqModC K)

private theorem jLineEquivOneC_gen :
    jLineEquivOneC K N (AdjoinSimple.gen K (jGeomGen K N))
      = (⟨jqModC K, jqModC_mem K 1⟩ : modularFunctionFieldC K 1) := by
  rw [jLineEquivOneC, AlgEquiv.trans_apply, jLineEquivC,
    RatFunc.algEquivOfTranscendental_symm_gen, ratFuncEquivCharLOneC_X]

private theorem jLineEquivOneC_gen_sub (a : K) :
    jLineEquivOneC K N (AdjoinSimple.gen K (jGeomGen K N) - algebraMap K _ a)
      = (⟨jqModC K, jqModC_mem K 1⟩ : modularFunctionFieldC K 1)
          - algebraMap K (modularFunctionFieldC K 1) a := by
  rw [map_sub, AlgEquiv.commutes, jLineEquivOneC_gen]

private theorem ratFuncEquivCharLOneC_X_sub_C (a : K) :
    ratFuncEquivCharLOneC K (algebraMap (Polynomial K) (RatFunc K) (X - C a))
      = (⟨jqModC K, jqModC_mem K 1⟩ : modularFunctionFieldC K 1)
          - algebraMap K (modularFunctionFieldC K 1) a := by
  rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_sub, ratFuncEquivCharLOneC_X]
  congr 1
  exact (ratFuncEquivCharLOneC K).commutes a

private def jLinePlaceC (a : K) : Place K ↥(IntermediateField.adjoin K {jGeomGen K N}) :=
  (Place.congrEquiv (jLineEquivOneC K N).toRingEquiv (jLineEquivOneC_commutes K N)).symm
    (charLGeomPlaceOfPoint K a)

private theorem ord_charLGeomPlaceOfPoint_jqModC_sub (a : K) :
    (charLGeomPlaceOfPoint K a).ord
        ((⟨jqModC K, jqModC_mem K 1⟩ : modularFunctionFieldC K 1)
          - algebraMap K (modularFunctionFieldC K 1) a) = 1 := by
  have h := Place.ord_congrRingEquiv (ratFuncEquivCharLOneC K).toRingEquiv
    (fun c => (ratFuncEquivCharLOneC K).commutes c) (RationalFunctionField.placeOfPoint K a)
    (algebraMap (Polynomial K) (RatFunc K) (X - C a))
  rw [RationalFunctionField.ord_placeOfPoint_algebraMap a (X_sub_C_ne_zero a),
    rootMultiplicity_X_sub_C_self, Nat.cast_one] at h
  rw [← ratFuncEquivCharLOneC_X_sub_C]
  exact h

private theorem ord_jLinePlaceC_gen_sub (a : K) :
    (jLinePlaceC K N a).ord (AdjoinSimple.gen K (jGeomGen K N) - algebraMap K _ a) = 1 := by
  have h := Place.ord_congrRingEquiv (jLineEquivOneC K N).toRingEquiv.symm
    (Place.symm_algebraMap_comm (jLineEquivOneC K N).toRingEquiv (jLineEquivOneC_commutes K N))
    (charLGeomPlaceOfPoint K a)
    ((⟨jqModC K, jqModC_mem K 1⟩ : modularFunctionFieldC K 1)
      - algebraMap K (modularFunctionFieldC K 1) a)
  rw [ord_charLGeomPlaceOfPoint_jqModC_sub, ← jLineEquivOneC_gen_sub K N a] at h
  have hss : (jLineEquivOneC K N).toRingEquiv.symm
      ((jLineEquivOneC K N) (AdjoinSimple.gen K (jGeomGen K N) - algebraMap K _ a))
        = AdjoinSimple.gen K (jGeomGen K N) - algebraMap K _ a :=
    (jLineEquivOneC K N).toRingEquiv.symm_apply_apply _
  rw [hss] at h
  exact h

private theorem eq_jLinePlaceC_of_ord_pos {a : K} {u : Place K ↥(IntermediateField.adjoin K {jGeomGen K N})}
    (hu : 0 < u.ord (AdjoinSimple.gen K (jGeomGen K N) - algebraMap K _ a)) :
    u = jLinePlaceC K N a := by
  have h := Place.ord_congrRingEquiv (jLineEquivOneC K N).toRingEquiv
    (jLineEquivOneC_commutes K N) u (AdjoinSimple.gen K (jGeomGen K N) - algebraMap K _ a)
  have h' : 0 < (Place.congrRingEquiv (jLineEquivOneC K N).toRingEquiv
      (jLineEquivOneC_commutes K N) u).ord
        ((⟨jqModC K, jqModC_mem K 1⟩ : modularFunctionFieldC K 1)
          - algebraMap K (modularFunctionFieldC K 1) a) := by
    rw [← jLineEquivOneC_gen_sub K N a]
    rw [← h] at hu
    exact hu
  have heq := eq_charLGeomPlaceOfPoint_of_ord_pos h'
  have hback := (Place.congrEquiv (jLineEquivOneC K N).toRingEquiv
    (jLineEquivOneC_commutes K N)).symm_apply_apply u
  rw [Place.congrEquiv_apply, heq] at hback
  exact hback.symm

end JLine

section Fibre

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

private theorem algebraMap_gen_sub (a : K) :
    algebraMap ↥(IntermediateField.adjoin K {jGeomGen K N}) (modularFunctionFieldC K N)
        (AdjoinSimple.gen K (jGeomGen K N) - algebraMap K _ a)
      = jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a := by
  rw [map_sub, AdjoinSimple.algebraMap_gen, ← IsScalarTower.algebraMap_apply K _ _ a]

variable [FiniteDimensional ↥(IntermediateField.adjoin K {jGeomGen K N}) (modularFunctionFieldC K N)]

private theorem ord_jGeomGen_sub_eq_ramificationIndex {a : K} {w : Place K (modularFunctionFieldC K N)}
    (hw : w.restrict ↥(IntermediateField.adjoin K {jGeomGen K N}) = jLinePlaceC K N a) :
    w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a)
      = w.ramificationIndex ↥(IntermediateField.adjoin K {jGeomGen K N}) := by
  rw [← algebraMap_gen_sub K N a, Place.ord_restrict, hw, ord_jLinePlaceC_gen_sub, mul_one]

private theorem restrict_eq_jLinePlaceC_iff_ord_pos (a : K) (w : Place K (modularFunctionFieldC K N)) :
    w.restrict ↥(IntermediateField.adjoin K {jGeomGen K N}) = jLinePlaceC K N a
      ↔ 0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) := by
  constructor
  · intro hw
    rw [ord_jGeomGen_sub_eq_ramificationIndex K N hw]
    exact_mod_cast w.ramificationIndex_pos (F := ↥(IntermediateField.adjoin K {jGeomGen K N}))
  · intro hpos
    refine eq_jLinePlaceC_of_ord_pos K N ?_
    rw [← algebraMap_gen_sub K N a, Place.ord_restrict] at hpos
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (not_lt.mpr (Int.natCast_nonneg _))

variable [Algebra.IsSeparable ↥(IntermediateField.adjoin K {jGeomGen K N}) (modularFunctionFieldC K N)]

private theorem mem_fiberOver_jLinePlaceC_iff (a : K) (w : Place K (modularFunctionFieldC K N)) :
    w ∈ (jLinePlaceC K N a).fiberOver (modularFunctionFieldC K N)
      ↔ 0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) := by
  rw [Place.mem_fiberOver, restrict_eq_jLinePlaceC_iff_ord_pos]

end Fibre

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos.ModularCurve in

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (hsep : IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (jqNModC K N))
    (a : K) :
    {w : Place K (modularFunctionFieldC K N) |
      0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a)}.Finite := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  obtain ⟨hfd, hs⟩ :=
    finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC K N data hsep
  haveI : FiniteDimensional ↥(IntermediateField.adjoin K {jGeomGen K N})
    (modularFunctionFieldC K N) := hfd
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin K {jGeomGen K N})
    (modularFunctionFieldC K N) := hs
  refine ((jLinePlaceC K N a).fiberOver (modularFunctionFieldC K N)).finite_toSet.subset ?_
  intro w hw
  rw [Finset.mem_coe, mem_fiberOver_jLinePlaceC_iff]
  exact hw

end
p2m_reactivate "P2MW.S_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos.ModularCurve"

end S_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
end P2MW
export P2MW.S_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos (solution)
