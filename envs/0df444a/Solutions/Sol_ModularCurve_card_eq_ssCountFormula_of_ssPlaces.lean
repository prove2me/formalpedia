-- Prove2me | solution 1 for ModularCurve.card_eq_ssCountFormula_of_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c024a2ca-8a48-5f0d-a013-2e6bf36bb3e9

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_EichlerMass
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_card_places_modularFunctionFieldFullC_over_eq_natCard_moduliPoint_j_eq
import Theorems.Thm_ModularCurve_natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero
import Theorems.Thm_ModularCurve_two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo_of_ne_zero
import Theorems.Thm_ModularCurve_three_mul_natCard_moduliPoint_j_eq_zero_eq_dedekindPsi_add_two_mul_nuThree_of_ne_zero
import Theorems.Thm_ModularCurve_card_eq_of_ssJSet
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_nuTwo_prime
import Theorems.Thm_ModularCurve_nuThree_prime
import Theorems.Thm_ModularCurve_card_eq_ssCountFormula_of_ssPlaces_of_lt_five
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_card_eq_ssCountFormula_of_ssPlaces
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice"
p2m_attr_erase "simp" "PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace SsfrobEDSol

private theorem jNGeomGen_mem_of_jGeomGen_mem (K : Type*) [Field K] (N : ℕ) [NeZero N]
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

private theorem mem_ssPlaces_and_evalAt_eq_iff_ord_pos (q N : ℕ) [NeZero N] (K : Type*) [Field K]
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

private theorem a4f_at (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (F : IntermediateField K (LaurentSeries K)) (E : modularFunctionFieldFullC K N = F)
    (hmem : jqModC K ∈ F) (j₀ : K)
    (S : Finset (Place K F))
    (hS : ∀ P, P ∈ S ↔
      0 < P.ord ((⟨jqModC K, hmem⟩ : F) - algebraMap K F j₀)) :
    S.card = Nat.card {x : ModuliPoint N K // ModuliPoint.j x = j₀} := by
  subst E
  exact ModularCurve.card_places_modularFunctionFieldFullC_over_eq_natCard_moduliPoint_j_eq
    K N hN j₀ S hS

private theorem a4f_at_C (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]
    (q N : ℕ) [Fact q.Prime] [CharP K q] [NeZero N] (hqN : ¬ q ∣ N) (j₀ : K)
    (S : Finset (Place K (modularFunctionFieldC K N)))
    (hS : ∀ P, P ∈ S ↔
      0 < P.ord ((⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N) -
        algebraMap K (modularFunctionFieldC K N) j₀)) :
    S.card = Nat.card {x : ModuliPoint N K // ModuliPoint.j x = j₀} := by
  have hN : (N : K) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff K q N).mp h)
  exact a4f_at K N hN (modularFunctionFieldC K N)
    (modularFunctionFieldC_eq_modularFunctionFieldFullC K q N hqN).symm
    (jqModC_mem K N) j₀ S hS

private theorem fibre_card (k : Type*) [Field k] [IsAlgClosed k] [DecidableEq k]
    (q N : ℕ) [Fact q.Prime] [CharP k q] [NeZero N] (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) {a : k} (ha : a ∈ ssJSet q k) :
    (W.filter (fun w => w.evalAt (jGeomGen k N) = a)).card
      = Nat.card {x : ModuliPoint N k // ModuliPoint.j x = a} := by
  apply a4f_at_C k q N hqN
  intro P
  rw [Finset.mem_filter, hW]
  have hdef : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) = jGeomGen k N := rfl
  rw [hdef]
  exact mem_ssPlaces_and_evalAt_eq_iff_ord_pos q N k ha P

private theorem cast_prime_ne_zero (k : Type*) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (m : ℕ) (hm : ¬ q ∣ m) : (m : k) ≠ 0 :=
  fun h => hm ((CharP.cast_eq_zero_iff k q m).mp h)

private theorem not_dvd_of_lt {q m : ℕ} (hq : Nat.Prime q) (h5 : 5 ≤ q) (hm : m ∈ ({2, 3} : Set ℕ)) :
    ¬ q ∣ m := by
  rcases hm with rfl | rfl <;>
    · intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega

end SsfrobEDSol

open SsfrobEDSol in
theorem solution
    (q N : ℕ) [Fact q.Prime] [NeZero N] (hqN : ¬ q ∣ N)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) :
    (W.card : ℚ) = ssCountFormula N q := by
  have hprime : q.Prime := Fact.out
  rcases Nat.lt_or_ge q 5 with hq5 | hq5
  ·
    exact ModularCurve.card_eq_ssCountFormula_of_ssPlaces_of_lt_five q N hq5 hqN k W hW
  ·
    have hq2 : ¬ q ∣ 2 := not_dvd_of_lt hprime hq5 (by simp)
    have hq3 : ¬ q ∣ 3 := not_dvd_of_lt hprime hq5 (by simp)
    have h2k : (2 : k) ≠ 0 := by
      have := cast_prime_ne_zero k q 2 hq2
      simpa using this
    have h3k : (3 : k) ≠ 0 := by
      have := cast_prime_ne_zero k q 3 hq3
      simpa using this
    have hNk : (N : k) ≠ 0 := cast_prime_ne_zero k q N hqN
    have h1728 : (1728 : k) ≠ 0 := by
      have h12 : ((1728 : ℕ) : k) ≠ 0 := by
        apply cast_prime_ne_zero k q
        intro hdvd
        rcases (Nat.Prime.dvd_mul hprime).mp (by norm_num at hdvd ⊢; exact hdvd :
            q ∣ 2 ^ 6 * 3 ^ 3) with h | h
        · exact hq2 (hprime.dvd_of_dvd_pow h)
        · exact hq3 (hprime.dvd_of_dvd_pow h)
      simpa using h12

    obtain ⟨Sfin, hSfin⟩ : ∃ S : Finset k, ∀ a, a ∈ S ↔ a ∈ ssJSet q k :=
      ⟨(ModularCurve.ssJSet_finite q k).toFinset, fun a => Set.Finite.mem_toFinset _⟩

    have hmaps : ∀ w ∈ W, w.evalAt (jGeomGen k N) ∈ Sfin := by
      intro w hw
      rw [hSfin]
      have hss := (hW w).mp hw
      rw [mem_ssPlaces_iff, isSupersingularPlace_iff] at hss
      exact hss.2.2
    have hpart : W.card = ∑ a ∈ Sfin, (W.filter (fun w => w.evalAt (jGeomGen k N) = a)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps

    have hval : ∀ a ∈ Sfin,
        ((W.filter (fun w => w.evalAt (jGeomGen k N) = a)).card : ℚ)
          = (dedekindPsi N : ℚ)
            + (if a = (1728 : k) then ((nuTwo N : ℚ) - (dedekindPsi N : ℚ)) / 2 else 0)
            + (if a = (0 : k) then (2 * (nuThree N : ℚ) - 2 * (dedekindPsi N : ℚ)) / 3 else 0) := by
      intro a haS
      have ha : a ∈ ssJSet q k := (hSfin a).mp haS
      have hfc := fibre_card k q N hqN W hW ha
      by_cases h17 : a = (1728 : k)
      · subst h17
        have h2c := ModularCurve.two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo_of_ne_zero
          N k hNk h2k h3k
        have h0ne : (1728 : k) ≠ 0 := h1728
        rw [if_pos rfl, if_neg h0ne]
        have : (2 : ℚ) * ((W.filter (fun w => w.evalAt (jGeomGen k N) = (1728 : k))).card : ℚ)
            = (dedekindPsi N : ℚ) + (nuTwo N : ℚ) := by
          rw [hfc]
          exact_mod_cast h2c
        linarith
      · by_cases h0 : a = (0 : k)
        · subst h0
          have h3c := ModularCurve.three_mul_natCard_moduliPoint_j_eq_zero_eq_dedekindPsi_add_two_mul_nuThree_of_ne_zero
            N k hNk h2k h3k
          rw [if_neg h17, if_pos rfl]
          have : (3 : ℚ) * ((W.filter (fun w => w.evalAt (jGeomGen k N) = (0 : k))).card : ℚ)
              = (dedekindPsi N : ℚ) + 2 * (nuThree N : ℚ) := by
            rw [hfc]
            exact_mod_cast h3c
          linarith
        · have hgen := ModularCurve.natCard_moduliPoint_j_eq_eq_dedekindPsi_of_ne_zero
            N k hNk h2k h3k a h0 h17
          rw [if_neg h17, if_neg h0, hfc, hgen]
          ring

    have hsum : (W.card : ℚ)
        = (Sfin.card : ℚ) * (dedekindPsi N : ℚ)
          + (if (1728 : k) ∈ Sfin then ((nuTwo N : ℚ) - (dedekindPsi N : ℚ)) / 2 else 0)
          + (if (0 : k) ∈ Sfin then (2 * (nuThree N : ℚ) - 2 * (dedekindPsi N : ℚ)) / 3 else 0) := by
      rw [hpart]
      push_cast
      rw [Finset.sum_congr rfl hval]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      congr 1
      · congr 1
        rw [Finset.sum_ite_eq' Sfin (1728 : k) (fun _ => ((nuTwo N : ℚ) - (dedekindPsi N : ℚ)) / 2)]
      · rw [Finset.sum_ite_eq' Sfin (0 : k) (fun _ => (2 * (nuThree N : ℚ) - 2 * (dedekindPsi N : ℚ)) / 3)]

    have hmem1728 : ((1728 : k) ∈ Sfin) = (q % 4 = 3) := by
      rw [hSfin]
      exact propext (ModularCurve.ofNat1728_mem_ssJSet_iff q hq5 k)
    have hmem0 : ((0 : k) ∈ Sfin) = (q % 3 = 2) := by
      rw [hSfin]
      exact propext (ModularCurve.zero_mem_ssJSet_iff q hq5 k)
    have hcard : Sfin.card = q / 12 + (if q % 3 = 2 then 1 else 0) + (if q % 4 = 3 then 1 else 0) :=
      ModularCurve.card_eq_of_ssJSet q hq5 k Sfin (fun j => hSfin j)

    have hq2' : q ≠ 2 := by omega
    have hq3' : q ≠ 3 := by omega
    have hnu2 : nuTwo q = if q % 4 = 1 then 2 else 0 := ModularCurve.nuTwo_prime hprime hq2'
    have hnu3 : nuThree q = if q % 3 = 1 then 2 else 0 := ModularCurve.nuThree_prime hprime hq3'

    rw [hsum, hcard, ssCountFormula, eichlerMass, hnu2, hnu3]
    have hq4mod : q % 4 = 1 ∨ q % 4 = 3 := by
      have : ¬ 2 ∣ q := fun h => hq2' ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp h).symm
      omega
    have hq3mod : q % 3 = 1 ∨ q % 3 = 2 := by
      have : ¬ 3 ∣ q := fun h => hq3' ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hprime).mp h).symm
      omega
    rcases hq4mod with h4 | h4 <;> rcases hq3mod with h3 | h3
    ·
      have hq' : q = 12 * (q / 12) + 1 := by omega
      have hdm' : (q : ℚ) = 12 * ((q / 12 : ℕ) : ℚ) + 1 := by exact_mod_cast hq'
      simp only [hmem1728, hmem0, h4, h3]
      rw [hdm']
      push_cast
      norm_num
      ring
    ·
      have hq' : q = 12 * (q / 12) + 5 := by omega
      have hdm' : (q : ℚ) = 12 * ((q / 12 : ℕ) : ℚ) + 5 := by exact_mod_cast hq'
      simp only [hmem1728, hmem0, h4, h3]
      rw [hdm']
      push_cast
      norm_num
      ring
    ·
      have hq' : q = 12 * (q / 12) + 7 := by omega
      have hdm' : (q : ℚ) = 12 * ((q / 12 : ℕ) : ℚ) + 7 := by exact_mod_cast hq'
      simp only [hmem1728, hmem0, h4, h3]
      rw [hdm']
      push_cast
      norm_num
      ring
    ·
      have hq' : q = 12 * (q / 12) + 11 := by omega
      have hdm' : (q : ℚ) = 12 * ((q / 12 : ℕ) : ℚ) + 11 := by exact_mod_cast hq'
      simp only [hmem1728, hmem0, h4, h3]
      rw [hdm']
      push_cast
      norm_num
      ring

end S_ModularCurve_card_eq_ssCountFormula_of_ssPlaces
end P2MW
export P2MW.S_ModularCurve_card_eq_ssCountFormula_of_ssPlaces (solution)
