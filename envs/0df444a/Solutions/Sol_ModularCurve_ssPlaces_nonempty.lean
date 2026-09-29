-- Prove2me | solution 1 for ModularCurve.ssPlaces_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/32a60420-7799-5639-b892-ff3277b50c50

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Theorems.Thm_ModularCurve_ssJSet_nonempty
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ssPlaces_nonempty
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace SsfrobNE

open ModularCurve AlgebraicCurve

noncomputable section

open AlgebraicCurve IntermediateField Polynomial

namespace ModularCurve

section JLine

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

theorem jGeomGen_transcendental : Transcendental K (jGeomGen K N) := by
  have h : Transcendental K
      (algebraMap (modularFunctionFieldC K N) (LaurentSeries K) (jGeomGen K N)) :=
    transcendental_jqModC K
  exact (transcendental_algebraMap_iff
    (algebraMap (modularFunctionFieldC K N) (LaurentSeries K)).injective).mp h

def jLineEquivC : RatFunc K ≃ₐ[K] ↥(IntermediateField.adjoin K {jGeomGen K N}) :=
  RatFunc.algEquivOfTranscendental (jGeomGen K N) (jGeomGen_transcendental K N)

def jLineEquivOneC :
    ↥(IntermediateField.adjoin K {jGeomGen K N}) ≃ₐ[K] ↥(modularFunctionFieldC K 1) :=
  (jLineEquivC K N).symm.trans (ratFuncEquivCharLOneC K)

theorem jLineEquivOneC_commutes (c : K) :
    (jLineEquivOneC K N).toRingEquiv (algebraMap K _ c) = algebraMap K _ c :=
  (jLineEquivOneC K N).commutes c

theorem ratFuncEquivCharLOneC_X :
    ratFuncEquivCharLOneC K RatFunc.X = (⟨jqModC K, jqModC_mem K 1⟩ : modularFunctionFieldC K 1) := by
  refine Subtype.ext ?_
  show ((RatFunc.algEquivOfTranscendental (jqModC K) (transcendental_jqModC K) RatFunc.X :
      ↥(IntermediateField.adjoin K {jqModC K})) : LaurentSeries K) = jqModC K
  exact RatFunc.algEquivOfTranscendental_X (jqModC K) (transcendental_jqModC K)

theorem jLineEquivOneC_gen :
    jLineEquivOneC K N (AdjoinSimple.gen K (jGeomGen K N))
      = (⟨jqModC K, jqModC_mem K 1⟩ : modularFunctionFieldC K 1) := by
  rw [jLineEquivOneC, AlgEquiv.trans_apply, jLineEquivC,
    RatFunc.algEquivOfTranscendental_symm_gen, ratFuncEquivCharLOneC_X]

theorem jLineEquivOneC_gen_sub (a : K) :
    jLineEquivOneC K N (AdjoinSimple.gen K (jGeomGen K N) - algebraMap K _ a)
      = (⟨jqModC K, jqModC_mem K 1⟩ : modularFunctionFieldC K 1)
          - algebraMap K (modularFunctionFieldC K 1) a := by
  rw [map_sub, AlgEquiv.commutes, jLineEquivOneC_gen]

theorem ratFuncEquivCharLOneC_X_sub_C (a : K) :
    ratFuncEquivCharLOneC K (algebraMap (Polynomial K) (RatFunc K) (X - C a))
      = (⟨jqModC K, jqModC_mem K 1⟩ : modularFunctionFieldC K 1)
          - algebraMap K (modularFunctionFieldC K 1) a := by
  rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_sub, ratFuncEquivCharLOneC_X]
  congr 1
  exact (ratFuncEquivCharLOneC K).commutes a

def jLinePlaceC (a : K) : Place K ↥(IntermediateField.adjoin K {jGeomGen K N}) :=
  (Place.congrEquiv (jLineEquivOneC K N).toRingEquiv (jLineEquivOneC_commutes K N)).symm
    (charLGeomPlaceOfPoint K a)

theorem ord_charLGeomPlaceOfPoint_jqModC_sub (a : K) :
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

theorem ord_jLinePlaceC_gen_sub (a : K) :
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

theorem eq_jLinePlaceC_of_ord_pos {a : K} {u : Place K ↥(IntermediateField.adjoin K {jGeomGen K N})}
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

theorem algebraMap_gen_sub (a : K) :
    algebraMap ↥(IntermediateField.adjoin K {jGeomGen K N}) (modularFunctionFieldC K N)
        (AdjoinSimple.gen K (jGeomGen K N) - algebraMap K _ a)
      = jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a := by
  rw [map_sub, AdjoinSimple.algebraMap_gen, ← IsScalarTower.algebraMap_apply K _ _ a]

variable [FiniteDimensional ↥(IntermediateField.adjoin K {jGeomGen K N}) (modularFunctionFieldC K N)]

theorem ord_jGeomGen_sub_eq_ramificationIndex {a : K} {w : Place K (modularFunctionFieldC K N)}
    (hw : w.restrict ↥(IntermediateField.adjoin K {jGeomGen K N}) = jLinePlaceC K N a) :
    w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a)
      = w.ramificationIndex ↥(IntermediateField.adjoin K {jGeomGen K N}) := by
  rw [← algebraMap_gen_sub K N a, Place.ord_restrict, hw, ord_jLinePlaceC_gen_sub, mul_one]

theorem restrict_eq_jLinePlaceC_iff_ord_pos (a : K) (w : Place K (modularFunctionFieldC K N)) :
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

theorem mem_fiberOver_jLinePlaceC_iff (a : K) (w : Place K (modularFunctionFieldC K N)) :
    w ∈ (jLinePlaceC K N a).fiberOver (modularFunctionFieldC K N)
      ↔ 0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) := by
  rw [Place.mem_fiberOver, restrict_eq_jLinePlaceC_iff_ord_pos]

end Fibre

section Degree

theorem finrank_adjoin_jGeomGen_eq_dedekindPsi (q N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    (K : Type*) [Field K] [Fact q.Prime] [CharP K q] :
    Module.finrank ↥(IntermediateField.adjoin K {jGeomGen K N}) (modularFunctionFieldC K N)
      = dedekindPsi N := by
  have h := relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi K N q hqN
  have hc := IntermediateField.finrank_comap
    (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (modularFunctionFieldC K N).val
  rw [IntermediateField.fieldRange_val] at hc
  have hval : (jGeomGen K N).1 = jqModC K := rfl
  have hmap : IntermediateField.lift (IntermediateField.adjoin K {jGeomGen K N})
      = IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
    rw [IntermediateField.lift_adjoin_simple, hval]
  have hcomap : (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))).comap
      (modularFunctionFieldC K N).val = IntermediateField.adjoin K {jGeomGen K N} := by
    rw [← hmap]
    exact IntermediateField.comap_map _ _
  rw [hcomap] at hc
  exact hc.trans h

theorem inertiaDeg_adjoin_jGeomGen_eq_one (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N]
    [FiniteDimensional ↥(IntermediateField.adjoin K {jGeomGen K N}) (modularFunctionFieldC K N)]
    (w : Place K (modularFunctionFieldC K N)) :
    w.inertiaDeg ↥(IntermediateField.adjoin K {jGeomGen K N}) = 1 := by
  have h := Place.deg_restrict_mul_inertiaDeg (F := ↥(IntermediateField.adjoin K {jGeomGen K N})) w
  exact Nat.eq_one_of_mul_eq_one_left (h.trans (place_deg_eq_one_of_isAlgClosed K N w))

end Degree

section Count

theorem finite_setOf_ord_jGeomGen_sub_pos (K : Type*) [Field K] (N : ℕ) [NeZero N]
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

theorem sum_ord_jGeomGen_sub_eq_dedekindPsi (q N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    (K : Type*) [Field K] [Fact q.Prime] [CharP K q] [IsAlgClosed K]
    (hsep : IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (jqNModC K N))
    (a : K) (T : Finset (Place K (modularFunctionFieldC K N)))
    (hT : ∀ w, w ∈ T ↔ 0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a)) :
    ∑ w ∈ T, w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a)
      = dedekindPsi N := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  obtain ⟨hfd, hs⟩ :=
    finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC K N data hsep
  haveI : FiniteDimensional ↥(IntermediateField.adjoin K {jGeomGen K N})
    (modularFunctionFieldC K N) := hfd
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin K {jGeomGen K N})
    (modularFunctionFieldC K N) := hs
  have hfib : T = (jLinePlaceC K N a).fiberOver (modularFunctionFieldC K N) := by
    ext w
    rw [hT, mem_fiberOver_jLinePlaceC_iff]
  have hfi := Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver
    (F := ↥(IntermediateField.adjoin K {jGeomGen K N})) (F' := modularFunctionFieldC K N)
    (jLinePlaceC K N a)
  rw [finrank_adjoin_jGeomGen_eq_dedekindPsi q N hqN K] at hfi
  rw [hfib, ← hfi]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [inertiaDeg_adjoin_jGeomGen_eq_one K N w, Nat.cast_one, mul_one,
    ord_jGeomGen_sub_eq_ramificationIndex K N (Place.restrict_eq_of_mem_fiberOver _ hw)]

end Count

section Supersingular

theorem jNGeomGen_mem_of_jGeomGen_mem (K : Type*) [Field K] (N : ℕ) [NeZero N]
    {w : Place K (modularFunctionFieldC K N)} (hj : jGeomGen K N ∈ w.toValuationSubring) :
    jNGeomGen K N ∈ w.toValuationSubring := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hfac : Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldC K N)) (jGeomGen K N)
      = (SubringClass.subtype w.toValuationSubring).comp
          (Polynomial.eval₂RingHom (Int.castRingHom w.toValuationSubring) ⟨jGeomGen K N, hj⟩) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp
  refine w.mem_of_eval_monic_eq_zero
    (P := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldC K N))
      (jGeomGen K N)))
    (data.monic.map _) (fun i => ?_) ?_
  · rw [Polynomial.coeff_map, hfac, RingHom.comp_apply]
    exact SetLike.coe_mem _
  · rw [Polynomial.eval_map]
    exact evalModularPair_jGeomGen_eq_zero K N data

theorem mem_ssPlaces_and_evalAt_eq_iff_ord_pos (q N : ℕ) [NeZero N] (K : Type*) [Field K]
    [DecidableEq K] [IsAlgClosed K] {a : K} (ha : a ∈ ssJSet q K)
    (w : Place K (modularFunctionFieldC K N)) :
    (w ∈ ssPlaces q N K ∧ w.evalAt (jGeomGen K N) = a)
      ↔ 0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) := by
  constructor
  · rintro ⟨hss, hev⟩
    rw [mem_ssPlaces_iff, isSupersingularPlace_iff] at hss
    have hc : 0 < w.ord (jGeomGen K N
        - algebraMap K (modularFunctionFieldC K N) (w.evalAt (jGeomGen K N))) :=
      (exists_isCentreOf_of_isRational hss.1 hss.2.1).1
    rwa [hev] at hc
  · intro hpos
    have hrat : w.IsRational :=
      (Place.isRational_iff_deg_eq_one w).mpr (place_deg_eq_one_of_isAlgClosed K N w)
    have hj : jGeomGen K N ∈ w.toValuationSubring := by
      have h := add_mem (w.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero K N a) hpos.le)
        (w.algebraMap_mem' a)
      rwa [sub_add_cancel] at h
    have hjN : jNGeomGen K N ∈ w.toValuationSubring := jNGeomGen_mem_of_jGeomGen_mem K N hj
    have hev : w.evalAt (jGeomGen K N) = a := by
      rw [w.evalAt_congr hj (w.algebraMap_mem' a) (Or.inr hpos), w.evalAt_algebraMap]
    refine ⟨?_, hev⟩
    rw [mem_ssPlaces_iff, isSupersingularPlace_iff]
    refine ⟨hrat, ⟨hj, hjN⟩, ?_⟩
    rw [hev]
    exact ha

end Supersingular

section Interface

theorem finite_setOf_mem_ssPlaces_and_evalAt_eq (q N : ℕ) [NeZero N] (K : Type*) [Field K]
    [DecidableEq K] [IsAlgClosed K]
    (hsep : IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (jqNModC K N))
    {a : K} (ha : a ∈ ssJSet q K) :
    {w : Place K (modularFunctionFieldC K N) |
      w ∈ ssPlaces q N K ∧ w.evalAt (jGeomGen K N) = a}.Finite := by
  refine (finite_setOf_ord_jGeomGen_sub_pos K N hsep a).subset ?_
  intro w hw
  exact (mem_ssPlaces_and_evalAt_eq_iff_ord_pos q N K ha w).mp hw

theorem exists_finset_ssPlaces_fibre_sum_ord_eq_dedekindPsi (q N : ℕ) [NeZero N]
    (hqN : ¬ q ∣ N) (K : Type*) [Field K] [DecidableEq K] [Fact q.Prime] [CharP K q]
    [IsAlgClosed K]
    (hsep : IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (jqNModC K N))
    {a : K} (ha : a ∈ ssJSet q K) :
    ∃ T : Finset (Place K (modularFunctionFieldC K N)),
      (∀ w, w ∈ T ↔ (w ∈ ssPlaces q N K ∧ w.evalAt (jGeomGen K N) = a)) ∧
      (∀ w ∈ T, 0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a)) ∧
      ∑ w ∈ T, w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a)
        = dedekindPsi N := by
  refine ⟨(finite_setOf_mem_ssPlaces_and_evalAt_eq q N K hsep ha).toFinset, fun w => ?_,
    fun w hw => ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hw
    exact (mem_ssPlaces_and_evalAt_eq_iff_ord_pos q N K ha w).mp hw
  · refine sum_ord_jGeomGen_sub_eq_dedekindPsi q N hqN K hsep a _ fun w => ?_
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact mem_ssPlaces_and_evalAt_eq_iff_ord_pos q N K ha w

theorem nonempty_ssPlaces_fibre_engine (q N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    (K : Type*) [Field K] [DecidableEq K] [Fact q.Prime] [CharP K q] [IsAlgClosed K]
    (hsep : IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (jqNModC K N))
    {a : K} (ha : a ∈ ssJSet q K) :
    Nonempty {w : Place K (modularFunctionFieldC K N) //
        w ∈ ssPlaces q N K ∧ w.evalAt (jGeomGen K N) = a} := by
  obtain ⟨T, hT, -, hsum⟩ :=
    exists_finset_ssPlaces_fibre_sum_ord_eq_dedekindPsi q N hqN K hsep ha
  by_contra h
  have hT0 : T = ∅ :=
    Finset.eq_empty_of_forall_notMem fun w hw => h ⟨⟨w, (hT w).mp hw⟩⟩
  rw [hT0, Finset.sum_empty] at hsum
  have hpsi := dedekindPsi_pos N (NeZero.ne N)
  omega

end Interface

end ModularCurve

end

end SsfrobNE

theorem SsfrobNE.nonempty_ssPlaces_fibre_polyU (q N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (K : Type*) [Field K] [DecidableEq K]
    [Fact q.Prime] [CharP K q] [IsAlgClosed K] {a : K} (ha : a ∈ ModularCurve.ssJSet q K) :
    Nonempty {w : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldC K N) //
        w ∈ ModularCurve.ssPlaces q N K ∧ w.evalAt (ModularCurve.jGeomGen K N) = a} := by
  have hN : (N : K) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff K q N).mp h)
  have hsep := ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero K N hN
  exact SsfrobNE.ModularCurve.nonempty_ssPlaces_fibre_engine q N hqN K hsep ha

open AlgebraicCurve ModularCurve

theorem solution
    (q N : ℕ) [Fact q.Prime] [NeZero N] (hqN : ¬ q ∣ N)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] :
    (ssPlaces q N k).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := ModularCurve.ssJSet_nonempty (q := q) (k := k)
  obtain ⟨⟨w, hw, -⟩⟩ := SsfrobNE.nonempty_ssPlaces_fibre_polyU q N hqN k ha
  exact ⟨w, hw⟩

end S_ModularCurve_ssPlaces_nonempty
end P2MW
export P2MW.S_ModularCurve_ssPlaces_nonempty (solution)
