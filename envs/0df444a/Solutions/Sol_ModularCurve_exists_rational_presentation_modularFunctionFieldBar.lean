-- Prove2me | solution 1 for ModularCurve.exists_rational_presentation_modularFunctionFieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4398fb1b-1992-5068-a671-15ab6c3ffa24

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_QAdicPlace
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_coeffEmb
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_rational_presentation_modularFunctionFieldBar
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 640000

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve
open Polynomial IntermediateField

private abbrev mwBR1jbar (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

private def mwBR1F0 (N : ℕ) [NeZero N] :
    IntermediateField (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  IntermediateField.adjoin (AlgebraicClosure ℚ) {mwBR1jbar N}

private def mwBR1Qj : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ {jq}

private theorem mwBR1_finiteDimensional_F0 (N : ℕ) [NeZero N] :
    FiniteDimensional (mwBR1F0 N) (modularFunctionFieldBar N) := by
  have h := ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full (L := AlgebraicClosure ℚ) N
  exact h

private theorem mwBR1_Qj_le_full (N : ℕ) [NeZero N] :
    mwBR1Qj ≤ modularFunctionFieldFull N := by
  rw [mwBR1Qj, IntermediateField.adjoin_le_iff]
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  exact jq_mem_full N

private theorem mwBR1_bridge_bar (N : ℕ) [NeZero N] :
    IntermediateField.relfinrank
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({coeffEmb (AlgebraicClosure ℚ) jq} : Set (LaurentSeries (AlgebraicClosure ℚ))))
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      = Module.finrank (mwBR1F0 N) (modularFunctionFieldBar N) := by
  have hmap := IntermediateField.relfinrank_map_map (mwBR1F0 N)
    (⊤ : IntermediateField (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).val
  rw [IntermediateField.relfinrank_top_right] at hmap
  have hlift : (mwBR1F0 N).map
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).val
      = IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({coeffEmb (AlgebraicClosure ℚ) jq} : Set (LaurentSeries (AlgebraicClosure ℚ))) := by
    refine le_antisymm ?_ ?_
    · refine IntermediateField.map_le_iff_le_comap.mpr ?_
      refine IntermediateField.adjoin_le_iff.mpr ?_
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      show (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).val (mwBR1jbar N)
        ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({coeffEmb (AlgebraicClosure ℚ) jq} : Set (LaurentSeries (AlgebraicClosure ℚ)))
      exact IntermediateField.subset_adjoin _ _ rfl
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact ⟨mwBR1jbar N, IntermediateField.subset_adjoin _ _ rfl, rfl⟩
  have htop : (⊤ : IntermediateField (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).map
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).val
      = laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, IntermediateField.mem_top, rfl⟩
  exact (congrArg₂ (fun A B => IntermediateField.relfinrank A B) hlift htop).symm.trans hmap

private theorem mwBR1_bridge_q (N : ℕ) [NeZero N] :
    IntermediateField.relfinrank mwBR1Qj (modularFunctionFieldFull N)
      = Module.finrank mwBR1Qj
          (IntermediateField.extendScalars (mwBR1_Qj_le_full N)) := by
  exact IntermediateField.relfinrank_eq_finrank_of_le (mwBR1_Qj_le_full N)

private theorem mwBR1_qside_finrank (N : ℕ) [NeZero N] :
    Module.finrank mwBR1Qj (IntermediateField.extendScalars (mwBR1_Qj_le_full N))
      = Module.finrank (mwBR1F0 N) (modularFunctionFieldBar N) := by
  rw [← mwBR1_bridge_q, ← mwBR1_bridge_bar,
    ModularCurve.relfinrank_laurentBaseChange_modularFunctionFieldFull]
  rfl

private theorem mwBR1_qside_fd (N : ℕ) [NeZero N] :
    FiniteDimensional mwBR1Qj (IntermediateField.extendScalars (mwBR1_Qj_le_full N)) := by
  have hfd := mwBR1_finiteDimensional_F0 N
  have hn : 0 < Module.finrank (mwBR1F0 N) (modularFunctionFieldBar N) :=
    Module.finrank_pos
  rw [← mwBR1_qside_finrank] at hn
  exact Module.finite_of_finrank_pos hn

private def mwBR1n (N : ℕ) [NeZero N] : ℕ :=
  Module.finrank (mwBR1F0 N) (modularFunctionFieldBar N)

private theorem mwBR1n_pos (N : ℕ) [NeZero N] : 0 < mwBR1n N := by
  have hfd := mwBR1_finiteDimensional_F0 N
  exact Module.finrank_pos

private abbrev mwBR1ES (N : ℕ) [NeZero N] :
    IntermediateField mwBR1Qj (LaurentSeries ℚ) :=
  IntermediateField.extendScalars (mwBR1_Qj_le_full N)

private def mwBR1BQ (N : ℕ) [NeZero N] :
    Module.Basis (Fin (mwBR1n N)) mwBR1Qj (mwBR1ES N) :=
  haveI := mwBR1_qside_fd N
  Module.finBasisOfFinrankEq mwBR1Qj (mwBR1ES N) (mwBR1_qside_finrank N)

private def mwBR1x (N : ℕ) [NeZero N] (i : Fin (mwBR1n N)) : LaurentSeries ℚ :=
  (mwBR1BQ N i : LaurentSeries ℚ)

private theorem mwBR1hx (N : ℕ) [NeZero N] (i : Fin (mwBR1n N)) :
    mwBR1x N i ∈ modularFunctionFieldFull N :=
  (mwBR1BQ N i).2

private def mwBR1Phi (N : ℕ) [NeZero N] :
    modularFunctionFieldFull N →+* modularFunctionFieldBar N where
  toFun y := ⟨coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) y.2⟩
  map_one' := by ext; simp
  map_mul' y z := by ext; simp
  map_zero' := by ext; simp
  map_add' y z := by ext; simp

private def mwBR1b (N : ℕ) [NeZero N] (i : Fin (mwBR1n N)) : modularFunctionFieldBar N :=
  mwBR1Phi N ⟨mwBR1x N i, mwBR1hx N i⟩

private def mwBR1W (N : ℕ) [NeZero N] :
    Submodule (mwBR1F0 N) (modularFunctionFieldBar N) :=
  Submodule.span (mwBR1F0 N) (Set.range (mwBR1b N))

private theorem mwBR1_coeffEmb_aeval (r : Polynomial ℚ) :
    coeffEmb (AlgebraicClosure ℚ) (Polynomial.aeval jq r)
      = Polynomial.aeval (coeffEmb (AlgebraicClosure ℚ) jq)
          (r.map (algebraMap ℚ (AlgebraicClosure ℚ))) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

private theorem mwBR1_aeval_mem_adjoin {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : L) (r : Polynomial K) :
    Polynomial.aeval x r ∈ IntermediateField.adjoin K ({x} : Set L) := by
  have h1 : Polynomial.aeval x r ∈ Algebra.adjoin K ({x} : Set L) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨r, rfl⟩
  exact IntermediateField.algebra_adjoin_le_adjoin K _ h1

private theorem mwBR1_coeff_mem (N : ℕ) [NeZero N] (γ : mwBR1Qj) :
    (⟨coeffEmb (AlgebraicClosure ℚ) (γ : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (mwBR1_Qj_le_full N γ.2)⟩ :
      modularFunctionFieldBar N) ∈ mwBR1F0 N := by
  obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff ℚ (γ : LaurentSeries ℚ)).mp γ.2
  rw [mwBR1F0, IntermediateField.mem_adjoin_simple_iff (AlgebraicClosure ℚ)]
  refine ⟨p.map (algebraMap ℚ (AlgebraicClosure ℚ)), q.map (algebraMap ℚ (AlgebraicClosure ℚ)), ?_⟩
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) (γ : LaurentSeries ℚ)
      = (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).val
          (Polynomial.aeval (mwBR1jbar N) (p.map (algebraMap ℚ (AlgebraicClosure ℚ)))
            / Polynomial.aeval (mwBR1jbar N) (q.map (algebraMap ℚ (AlgebraicClosure ℚ))))
  rw [map_div₀, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply,
    hpq, map_div₀, mwBR1_coeffEmb_aeval, mwBR1_coeffEmb_aeval]
  rfl

private theorem mwBR1_expand (N : ℕ) [NeZero N] {y : LaurentSeries ℚ}
    (hy : y ∈ modularFunctionFieldFull N) :
    ∃ γ : Fin (mwBR1n N) → mwBR1Qj,
      y = ∑ i, (γ i : LaurentSeries ℚ) * mwBR1x N i := by
  have hy' : y ∈ mwBR1ES N := hy
  refine ⟨fun i => (mwBR1BQ N).repr ⟨y, hy'⟩ i, ?_⟩
  have h := (mwBR1BQ N).sum_repr ⟨y, hy'⟩
  have h2 : (∑ i, ((mwBR1BQ N).repr ⟨y, hy'⟩ i) • ((mwBR1BQ N) i : LaurentSeries ℚ)) = y := by
    have h3 := congrArg (mwBR1ES N).val h
    rw [map_sum] at h3
    simp only [map_smul] at h3
    exact h3
  conv_lhs => rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, IntermediateField.algebraMap_apply]
  rfl

private theorem mwBR1_imPhi_mem (N : ℕ) [NeZero N] (y : modularFunctionFieldFull N) :
    mwBR1Phi N y ∈ mwBR1W N := by
  obtain ⟨γ, hγ⟩ := mwBR1_expand N y.2
  have hsub : mwBR1Phi N y
      = ∑ i, (⟨⟨coeffEmb (AlgebraicClosure ℚ) (γ i : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (mwBR1_Qj_le_full N (γ i).2)⟩,
          mwBR1_coeff_mem N (γ i)⟩ : mwBR1F0 N) • mwBR1b N i := by
    apply Subtype.ext
    have hcoe : ((mwBR1Phi N y : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
        = coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ) := rfl
    rw [hcoe, hγ, map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Algebra.smul_def, IntermediateField.algebraMap_apply]
    push_cast
    rfl
  rw [hsub]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem mwBR1_one_mem (N : ℕ) [NeZero N] :
    (1 : modularFunctionFieldBar N) ∈ mwBR1W N := by
  have h1 : (1 : modularFunctionFieldBar N) = mwBR1Phi N 1 := (map_one (mwBR1Phi N)).symm
  rw [h1]
  exact mwBR1_imPhi_mem N 1

private theorem mwBR1_W_mul_le (N : ℕ) [NeZero N] :
    mwBR1W N * mwBR1W N ≤ mwBR1W N := by
  unfold mwBR1W
  rw [Submodule.span_mul_span]
  refine Submodule.span_le.mpr ?_
  rintro z ⟨z1, hz1, z2, hz2, rfl⟩
  obtain ⟨i, rfl⟩ := hz1
  obtain ⟨j, rfl⟩ := hz2
  have hb : mwBR1b N i * mwBR1b N j
      = mwBR1Phi N (⟨mwBR1x N i, mwBR1hx N i⟩ * ⟨mwBR1x N j, mwBR1hx N j⟩) := by
    rw [map_mul (mwBR1Phi N)]
    rfl
  have hmem : mwBR1b N i * mwBR1b N j ∈ mwBR1W N := by
    rw [hb]
    exact mwBR1_imPhi_mem N _
  exact hmem

private theorem mwBR1_top_le (N : ℕ) [NeZero N] :
    (⊤ : Submodule (mwBR1F0 N) (modularFunctionFieldBar N)) ≤ mwBR1W N := by
  haveI hfd := mwBR1_finiteDimensional_F0 N
  have hWmul : ∀ u v : modularFunctionFieldBar N, u ∈ mwBR1W N → v ∈ mwBR1W N →
      u * v ∈ mwBR1W N := fun u v hu hv => mwBR1_W_mul_le N (Submodule.mul_mem_mul hu hv)
  intro X _
  have hmem : ∀ (z : LaurentSeries (AlgebraicClosure ℚ))
      (hz : z ∈ Subfield.closure
        (Set.range (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) ∪
          (⇑(coeffEmb (AlgebraicClosure ℚ)) ''
            (modularFunctionFieldFull N : Set (LaurentSeries ℚ))))),
      (⟨z, (mem_laurentBaseChange_iff).mpr hz⟩ : modularFunctionFieldBar N)
        ∈ mwBR1W N := by
    intro z hz
    induction hz using Subfield.closure_induction with
    | mem w hw =>
        rcases hw with ⟨c, rfl⟩ | ⟨y, hy, rfl⟩
        · have he : (⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c,
              (mem_laurentBaseChange_iff).mpr
                (Subfield.subset_closure (Or.inl ⟨c, rfl⟩))⟩ :
              modularFunctionFieldBar N)
              = (⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c,
                  (mwBR1F0 N).algebraMap_mem c⟩ : mwBR1F0 N) • (1 : modularFunctionFieldBar N) := by
            apply Subtype.ext
            rw [Algebra.smul_def, IntermediateField.algebraMap_apply, mul_one]
            rfl
          rw [he]
          exact Submodule.smul_mem _ _ (mwBR1_one_mem N)
        · have he : (⟨coeffEmb (AlgebraicClosure ℚ) y,
              (mem_laurentBaseChange_iff).mpr
                (Subfield.subset_closure (Or.inr ⟨y, hy, rfl⟩))⟩ :
              modularFunctionFieldBar N) = mwBR1Phi N ⟨y, hy⟩ := Subtype.ext rfl
          rw [he]
          exact mwBR1_imPhi_mem N _
    | one =>
        have he : (⟨(1 : LaurentSeries (AlgebraicClosure ℚ)),
            (mem_laurentBaseChange_iff).mpr (one_mem _)⟩ :
            modularFunctionFieldBar N) = 1 := Subtype.ext rfl
        rw [he]
        exact mwBR1_one_mem N
    | add a b ha hb iha ihb =>
        have he : (⟨a + b, (mem_laurentBaseChange_iff).mpr
              (add_mem ha hb)⟩ : modularFunctionFieldBar N)
            = ⟨a, (mem_laurentBaseChange_iff).mpr ha⟩
              + ⟨b, (mem_laurentBaseChange_iff).mpr hb⟩ := Subtype.ext rfl
        rw [he]
        exact Submodule.add_mem _ iha ihb
    | neg a ha iha =>
        have he : (⟨-a, (mem_laurentBaseChange_iff).mpr
              (neg_mem ha)⟩ : modularFunctionFieldBar N)
            = -⟨a, (mem_laurentBaseChange_iff).mpr ha⟩ := Subtype.ext rfl
        rw [he]
        exact Submodule.neg_mem _ iha
    | inv a ha iha =>
        have hinv : (⟨a, (mem_laurentBaseChange_iff).mpr ha⟩ :
            modularFunctionFieldBar N)⁻¹ ∈ mwBR1W N := by
          have h1 := Subalgebra.inv_mem_of_algebraic
            (A := (mwBR1W N).toSubalgebra (mwBR1_one_mem N) hWmul)
            (x := ⟨⟨a, (mem_laurentBaseChange_iff).mpr ha⟩, iha⟩)
            (IsAlgebraic.of_finite (R := mwBR1F0 N) _)
          rwa [Submodule.mem_toSubalgebra] at h1
        have he : (⟨a⁻¹, (mem_laurentBaseChange_iff).mpr
              (inv_mem ha)⟩ : modularFunctionFieldBar N)
            = (⟨a, (mem_laurentBaseChange_iff).mpr ha⟩ :
              modularFunctionFieldBar N)⁻¹ := Subtype.ext rfl
        rw [he]
        exact hinv
    | mul a b ha hb iha ihb =>
        have he : (⟨a * b, (mem_laurentBaseChange_iff).mpr
              (mul_mem ha hb)⟩ : modularFunctionFieldBar N)
            = (⟨a, (mem_laurentBaseChange_iff).mpr ha⟩ :
                modularFunctionFieldBar N)
              * ⟨b, (mem_laurentBaseChange_iff).mpr hb⟩ := Subtype.ext rfl
        rw [he]
        exact hWmul _ _ iha ihb
  have hX := hmem (X : LaurentSeries (AlgebraicClosure ℚ))
    ((mem_laurentBaseChange_iff).mp X.2)
  simpa using hX

private def mwBR1BF (N : ℕ) [NeZero N] :
    Module.Basis (Fin (mwBR1n N)) (mwBR1F0 N) (modularFunctionFieldBar N) :=
  haveI := mwBR1_finiteDimensional_F0 N
  basisOfTopLeSpanOfCardEqFinrank (mwBR1b N) (mwBR1_top_le N)
    (by rw [Fintype.card_fin]; rfl)

private theorem mwBR1_BF_coe (N : ℕ) [NeZero N] : ⇑(mwBR1BF N) = mwBR1b N := by
  haveI := mwBR1_finiteDimensional_F0 N
  exact coe_basisOfTopLeSpanOfCardEqFinrank _ _ _

private theorem mwBR1_coe_b (N : ℕ) [NeZero N] (i : Fin (mwBR1n N)) :
    ((mwBR1b N i : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (mwBR1x N i) := rfl

private theorem mwBR1_coe_aeval_jbar (N : ℕ) [NeZero N] (r : Polynomial (AlgebraicClosure ℚ)) :
    ((Polynomial.aeval (mwBR1jbar N) r : modularFunctionFieldBar N) :
      LaurentSeries (AlgebraicClosure ℚ))
      = Polynomial.aeval (coeffEmb (AlgebraicClosure ℚ) jq) r :=
  (Polynomial.aeval_algHom_apply
    (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).val
    (mwBR1jbar N) r).symm

theorem solution
    (N : ℕ) [NeZero N] :
    ∃ (n : ℕ) (b : Fin n → modularFunctionFieldBar N) (d : Polynomial ℚ)
      (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial ℚ)),
      0 < n ∧ d ≠ 0 ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (i : Fin n),
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • b i = b i) ∧
      (∀ c : Fin n → Polynomial (AlgebraicClosure ℚ),
        (∑ i : Fin n, Polynomial.aeval (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
              (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (c i) * b i) = 0 → ∀ i, c i = 0) ∧
      (∀ x : modularFunctionFieldBar N, ∃ (q : Polynomial (AlgebraicClosure ℚ))
          (c : Fin n → Polynomial (AlgebraicClosure ℚ)), q ≠ 0 ∧
          x * Polynomial.aeval (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
              (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) q
            = ∑ i : Fin n, Polynomial.aeval (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
              (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (c i) * b i) ∧
      (∀ i j : Fin n, b i * b j
          * Polynomial.aeval (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
              (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (d.map (algebraMap ℚ (AlgebraicClosure ℚ)))
          = ∑ k : Fin n, Polynomial.aeval (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange
              (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
              ((A i k j).map (algebraMap ℚ (AlgebraicClosure ℚ))) * b k) := by
  classical
  haveI hfd := mwBR1_finiteDimensional_F0 N
  have hord : (cuspInftyBar N).ord (mwBR1jbar N) = -1 :=
    ModularCurve.ord_cuspInftyBar_coeffEmb_jq N
  have htr : Transcendental (AlgebraicClosure ℚ) (mwBR1jbar N) :=
    Place.transcendental_of_ord_ne_zero (cuspInftyBar N) (by rw [hord]; omega)
  have hinj : Function.Injective (Polynomial.aeval (mwBR1jbar N) :
      Polynomial (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N) :=
    transcendental_iff_injective.mp htr

  choose Γ hΓ using fun i j : Fin (mwBR1n N) =>
    mwBR1_expand N (mul_mem (mwBR1hx N i) (mwBR1hx N j))

  have hrep : ∀ i j k : Fin (mwBR1n N), ∃ (p : Polynomial ℚ) (q : Polynomial ℚ), q ≠ 0 ∧
      Polynomial.aeval jq q ≠ 0 ∧
      (Γ i j k : LaurentSeries ℚ) = Polynomial.aeval jq p / Polynomial.aeval jq q := by
    intro i j k
    obtain ⟨p, q, hpq⟩ :=
      (IntermediateField.mem_adjoin_simple_iff ℚ ((Γ i j k : LaurentSeries ℚ))).mp (Γ i j k).2
    by_cases hq : Polynomial.aeval jq q = 0
    · exact ⟨0, 1, one_ne_zero, by rw [map_one]; exact one_ne_zero,
        by rw [hpq, hq, div_zero, map_zero, zero_div]⟩
    · exact ⟨p, q, fun h0 => hq (by rw [h0, map_zero]), hq, hpq⟩
  choose P Q hQ0 hQa hPQ using hrep
  have hQdvd : ∀ i j k : Fin (mwBR1n N), Q i j k ∣
      ∏ t : Fin (mwBR1n N) × Fin (mwBR1n N) × Fin (mwBR1n N), Q t.1 t.2.1 t.2.2 :=
    fun i j k => Finset.dvd_prod_of_mem _ (Finset.mem_univ (i, j, k))
  refine ⟨mwBR1n N, mwBR1b N,
    ∏ t : Fin (mwBR1n N) × Fin (mwBR1n N) × Fin (mwBR1n N), Q t.1 t.2.1 t.2.2,
    fun i => ((fun k j => P i j k *
      ((∏ t : Fin (mwBR1n N) × Fin (mwBR1n N) × Fin (mwBR1n N), Q t.1 t.2.1 t.2.2) / Q i j k)) :
      Matrix (Fin (mwBR1n N)) (Fin (mwBR1n N)) (Polynomial ℚ)),
    mwBR1n_pos N,
    Finset.prod_ne_zero_iff.mpr fun t _ => hQ0 t.1 t.2.1 t.2.2,
    fun σ i => ModularCurve.arithmeticGalois_smul_coeffEmb (modularFunctionFieldFull N) σ
      (mwBR1hx N i),
    ?_, ?_, ?_⟩
  ·
    intro c hc
    have hli := (mwBR1BF N).linearIndependent
    rw [mwBR1_BF_coe] at hli
    have hg : ∀ i : Fin (mwBR1n N),
        (⟨Polynomial.aeval (mwBR1jbar N) (c i), mwBR1_aeval_mem_adjoin _ _⟩ : mwBR1F0 N)
          • mwBR1b N i
        = Polynomial.aeval (mwBR1jbar N) (c i) * mwBR1b N i := fun i => by
      rw [Algebra.smul_def, IntermediateField.algebraMap_apply]
    have hsum : (∑ i, (⟨Polynomial.aeval (mwBR1jbar N) (c i),
        mwBR1_aeval_mem_adjoin _ _⟩ : mwBR1F0 N) • mwBR1b N i) = 0 := by
      rw [Finset.sum_congr rfl fun i _ => hg i]
      exact hc
    have hz := Fintype.linearIndependent_iff.mp hli _ hsum
    intro i
    have h0 : Polynomial.aeval (mwBR1jbar N) (c i) = 0 := Subtype.ext_iff.mp (hz i)
    exact hinj (h0.trans (map_zero _).symm)
  ·
    intro X
    have hrepX := (mwBR1BF N).sum_repr X
    rw [mwBR1_BF_coe] at hrepX
    have hex : ∀ i : Fin (mwBR1n N), ∃ (p : Polynomial (AlgebraicClosure ℚ))
        (q : Polynomial (AlgebraicClosure ℚ)), q ≠ 0 ∧
        Polynomial.aeval (mwBR1jbar N) q ≠ 0 ∧
        (((mwBR1BF N).repr X i : modularFunctionFieldBar N))
          = Polynomial.aeval (mwBR1jbar N) p / Polynomial.aeval (mwBR1jbar N) q := by
      intro i
      obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff (AlgebraicClosure ℚ)
        (((mwBR1BF N).repr X i : modularFunctionFieldBar N))).mp ((mwBR1BF N).repr X i).2
      by_cases hq : Polynomial.aeval (mwBR1jbar N) q = 0
      · exact ⟨0, 1, one_ne_zero, by rw [map_one]; exact one_ne_zero,
          by rw [hpq, hq, div_zero, map_zero, zero_div]⟩
      · exact ⟨p, q, fun h0 => hq (by rw [h0, map_zero]), hq, hpq⟩
    choose Ps Qs hQs0 hQsa hPQs using hex
    refine ⟨∏ i, Qs i, fun i => Ps i * ∏ k ∈ Finset.univ.erase i, Qs k,
      Finset.prod_ne_zero_iff.mpr fun i _ => hQs0 i, ?_⟩
    rw [← hrepX, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, IntermediateField.algebraMap_apply, hPQs i]
    rw [map_mul, map_prod, map_prod,
      ← Finset.mul_prod_erase Finset.univ (fun k => Polynomial.aeval (mwBR1jbar N) (Qs k))
        (Finset.mem_univ i)]
    field_simp [hQsa i]
  ·
    intro i j
    have hclear : Polynomial.aeval jq
        (∏ t : Fin (mwBR1n N) × Fin (mwBR1n N) × Fin (mwBR1n N), Q t.1 t.2.1 t.2.2)
        * (mwBR1x N i * mwBR1x N j)
        = ∑ k, Polynomial.aeval jq (P i j k *
            ((∏ t : Fin (mwBR1n N) × Fin (mwBR1n N) × Fin (mwBR1n N), Q t.1 t.2.1 t.2.2)
              / Q i j k)) * mwBR1x N k := by
      rw [hΓ i j, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hPQ i j k, map_mul]
      have hdq : Polynomial.aeval jq
          (∏ t : Fin (mwBR1n N) × Fin (mwBR1n N) × Fin (mwBR1n N), Q t.1 t.2.1 t.2.2)
          = Polynomial.aeval jq (Q i j k) * Polynomial.aeval jq
              ((∏ t : Fin (mwBR1n N) × Fin (mwBR1n N) × Fin (mwBR1n N), Q t.1 t.2.1 t.2.2)
                / Q i j k) := by
        rw [← map_mul, EuclideanDomain.mul_div_cancel' (hQ0 i j k) (hQdvd i j k)]
      rw [hdq]
      field_simp [hQa i j k]
    have htrans := congrArg (coeffEmb (AlgebraicClosure ℚ)) hclear
    simp only [map_mul, map_sum, mwBR1_coeffEmb_aeval] at htrans
    apply Subtype.ext
    push_cast
    simp only [Polynomial.map_mul, map_mul,
      MulMemClass.coe_mul, mwBR1_coe_b, mwBR1_coe_aeval_jbar]
    linear_combination htrans

end
end S_ModularCurve_exists_rational_presentation_modularFunctionFieldBar
end P2MW
export P2MW.S_ModularCurve_exists_rational_presentation_modularFunctionFieldBar (solution)
