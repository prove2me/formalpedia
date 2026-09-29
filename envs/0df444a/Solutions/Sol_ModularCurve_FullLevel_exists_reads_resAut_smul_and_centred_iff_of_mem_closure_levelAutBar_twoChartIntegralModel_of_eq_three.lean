-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/01665be2-3dad-5660-9c8e-6873b3926a03

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_sub_mul_sub_mem_span_natCast_of_jqModC_mem_of_jqNModC_mem
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff
import Mathlib
import Theorems.Thm_ModularCurve_FullLevel_exists_qExpand_mem_chartAlgFin_and_forall_mem_closure_levelAutBar_exists_algEquiv_levelField_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField_of_eq_three
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgInf_localization_iff_of_algEquiv_apply_eq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

namespace L2Aux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel IsLocalRing

universe u

section Overlap

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem exists_mid_of_ιFin_eq_ιInf (y : XFin R F j) (y' : XInf R F j)
    (h : (ιFin R F j).base y = (ιInf R F j).base y') :
    ∃ z : XMid R F j, (fFin R F j).base z = y ∧ (fInf R F j).base z = y' := by
  have h' : (colimit.ι (span (fFin R F j) (fInf R F j)) WalkingSpan.left).base y =
      (colimit.ι (span (fFin R F j) (fInf R F j)) WalkingSpan.right).base y' := h
  obtain ⟨k, fi, fj, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff _).1 h'
  rcases k with (_ | _ | _)
  · have hfi : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
    have hfj : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
    subst hfi hfj
    exact ⟨z, h1, h2⟩
  · exact nomatch fj
  · exact nomatch fi

theorem exists_comap_eq_of_ιFin_eq_ιInf (y : XFin R F j) (y' : XInf R F j)
    (h : (ιFin R F j).base y = (ιInf R F j).base y') :
    ∃ z : XMid R F j, y.asIdeal = Ideal.comap (inclFin R F j).toRingHom z.asIdeal ∧
      y'.asIdeal = Ideal.comap (inclInf R F j).toRingHom z.asIdeal := by
  obtain ⟨z, h1, h2⟩ := exists_mid_of_ιFin_eq_ιInf R F j y y' h
  exact ⟨z, by rw [← h1]; rfl, by rw [← h2]; rfl⟩

private theorem _root_.L2Aux.jInvChartInf_mem_of_not_mem_range (y' : XInf R F j)
    (hx : (ιInf R F j).base y' ∉ Set.range (ιFin R F j).base) :
    jInvChartInf R F j ∈ y'.asIdeal := by
  by_contra hj
  letI : Algebra (chartAlgInf R F j) (chartAlgMid R F j) := (inclInf R F j).toRingHom.toAlgebra
  haveI : IsLocalization.Away (jInvChartInf R F j) (chartAlgMid R F j) :=
    isLocalization_away_inclInf R F j
  have hdisj : Disjoint (↑(Submonoid.powers (jInvChartInf R F j)) : Set (chartAlgInf R F j))
      (↑y'.asIdeal : Set (chartAlgInf R F j)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hj (y'.isPrime.mem_of_pow_mem n hn)
  have hmem : y' ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (chartAlgInf R F j) (chartAlgMid R F j))) := by
    rw [PrimeSpectrum.localization_comap_range (chartAlgMid R F j)
      (Submonoid.powers (jInvChartInf R F j))]
    exact hdisj
  obtain ⟨z, hz⟩ := hmem
  apply hx
  have hglue : (ιFin R F j).base ((fFin R F j).base z) = (ιInf R F j).base ((fInf R F j).base z) :=
    congrArg (fun f => f.base z) (glue_condition R F j)
  refine ⟨(fFin R F j).base z, hglue.trans ?_⟩
  show (ιInf R F j).base (PrimeSpectrum.comap (inclInf R F j).toRingHom z) = _
  rw [← hz]
  rfl

p2m_export "L2Aux" "jInvChartInf_mem_of_not_mem_range"

theorem exists_inf_witness (z : XMid R F j) (b : chartAlgFin R F j) :
    ∃ (n : ℕ) (g : chartAlgInf R F j),
      (b : F) * ((jInvChartInf R F j ^ n : chartAlgInf R F j) : F) = (g : F) ∧
      jInvChartInf R F j ^ n ∉ Ideal.comap (inclInf R F j).toRingHom z.asIdeal ∧
      (b ∈ Ideal.comap (inclFin R F j).toRingHom z.asIdeal ↔
        g ∈ Ideal.comap (inclInf R F j).toRingHom z.asIdeal) := by
  have hj0 : j ≠ 0 := Fact.out
  have hb : (b : F) ∈ chartAlg R F (insert j⁻¹⁻¹ {j⁻¹}) := by
    rw [inv_inv]
    exact chartAlg_mono R F (Set.singleton_subset_iff.2 (Set.mem_insert j _)) b.2
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton j⁻¹) (inv_ne_zero hj0) hb
  have hu : IsUnit (inclInf R F j (jInvChartInf R F j) ^ n) := (isUnit_inclInf_jInvChartInf R F j).pow n
  have e1 : ∀ x, (inclInf R F j).toRingHom x = inclInf R F j x := fun _ => rfl
  have e2 : ∀ x, (inclFin R F j).toRingHom x = inclFin R F j x := fun _ => rfl
  refine ⟨n, ⟨j⁻¹ ^ n * b, hn⟩, ?_, ?_, ?_⟩
  · rw [Subalgebra.coe_pow, coe_jInvChartInf]
    ring
  · intro hmem
    rw [Ideal.mem_comap, e1, map_pow] at hmem
    exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  · rw [Ideal.mem_comap, Ideal.mem_comap, e1, e2]
    have hprod : inclInf R F j ⟨j⁻¹ ^ n * b, hn⟩ =
        inclInf R F j (jInvChartInf R F j) ^ n * inclFin R F j b := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_chartIncl, coe_chartIncl, coe_chartIncl,
        coe_jInvChartInf]
    rw [hprod, Ideal.unit_mul_mem_iff_mem _ hu]

theorem jChartFin_mem_of_not_mem_range (y : XFin R F j)
    (hx : (ιFin R F j).base y ∉ Set.range (ιInf R F j).base) :
    jChartFin R F j ∈ y.asIdeal := by
  by_contra hj
  letI : Algebra (chartAlgFin R F j) (chartAlgMid R F j) := (inclFin R F j).toRingHom.toAlgebra
  haveI : IsLocalization.Away (jChartFin R F j) (chartAlgMid R F j) :=
    isLocalization_away_inclFin R F j
  have hdisj : Disjoint (↑(Submonoid.powers (jChartFin R F j)) : Set (chartAlgFin R F j))
      (↑y.asIdeal : Set (chartAlgFin R F j)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hj (y.isPrime.mem_of_pow_mem n hn)
  have hmem : y ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (chartAlgFin R F j) (chartAlgMid R F j))) := by
    rw [PrimeSpectrum.localization_comap_range (chartAlgMid R F j)
      (Submonoid.powers (jChartFin R F j))]
    exact hdisj
  obtain ⟨z, hz⟩ := hmem
  apply hx
  have hglue : (ιFin R F j).base ((fFin R F j).base z) = (ιInf R F j).base ((fInf R F j).base z) :=
    congrArg (fun f => f.base z) (glue_condition R F j)
  refine ⟨(fInf R F j).base z, ?_⟩
  rw [← hglue]
  show (ιFin R F j).base (PrimeSpectrum.comap (inclFin R F j).toRingHom z) = _
  rw [← hz]
  rfl

theorem exists_fin_witness (z : XMid R F j) (b : chartAlgInf R F j) :
    ∃ (n : ℕ) (g : chartAlgFin R F j),
      (b : F) * ((jChartFin R F j ^ n : chartAlgFin R F j) : F) = (g : F) ∧
      jChartFin R F j ^ n ∉ Ideal.comap (inclFin R F j).toRingHom z.asIdeal ∧
      (b ∈ Ideal.comap (inclInf R F j).toRingHom z.asIdeal ↔
        g ∈ Ideal.comap (inclFin R F j).toRingHom z.asIdeal) := by
  have hj0 : j ≠ 0 := Fact.out
  have hb : (b : F) ∈ chartAlg R F (insert j⁻¹ {j}) :=
    chartAlg_mono R F (Set.singleton_subset_iff.2 (Set.mem_insert j⁻¹ _)) b.2
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton j) hj0 hb
  have hu : IsUnit (inclFin R F j (jChartFin R F j) ^ n) := (isUnit_inclFin_jChartFin R F j).pow n
  have e1 : ∀ x, (inclInf R F j).toRingHom x = inclInf R F j x := fun _ => rfl
  have e2 : ∀ x, (inclFin R F j).toRingHom x = inclFin R F j x := fun _ => rfl
  refine ⟨n, ⟨j ^ n * b, hn⟩, ?_, ?_, ?_⟩
  · rw [Subalgebra.coe_pow, coe_jChartFin]
    ring
  · intro hmem
    rw [Ideal.mem_comap, e2, map_pow] at hmem
    exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  · rw [Ideal.mem_comap, Ideal.mem_comap, e1, e2]
    have hprod : inclFin R F j ⟨j ^ n * b, hn⟩ =
        inclFin R F j (jChartFin R F j) ^ n * inclInf R F j b := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_chartIncl, coe_chartIncl, coe_chartIncl,
        coe_jChartFin]
    rw [hprod, Ideal.unit_mul_mem_iff_mem _ hu]

theorem XFin_eq_of_le_of_forall_specializes (y y₂ : XFin R F j) (hle : y.asIdeal ≤ y₂.asIdeal)
    (hcl : ∀ w, (ιFin R F j).base y ⤳ w → w = (ιFin R F j).base y) : y₂ = y := by
  have h1 : y ⤳ y₂ := (PrimeSpectrum.le_iff_specializes y y₂).1 hle
  have h2 : (ιFin R F j).base y ⤳ (ιFin R F j).base y₂ := h1.map (ιFin R F j).continuous
  exact (ιFin R F j).isOpenEmbedding.injective (hcl _ h2)

theorem XInf_eq_of_le_of_forall_specializes (y y₂ : XInf R F j) (hle : y.asIdeal ≤ y₂.asIdeal)
    (hcl : ∀ w, (ιInf R F j).base y ⤳ w → w = (ιInf R F j).base y) : y₂ = y := by
  have h1 : y ⤳ y₂ := (PrimeSpectrum.le_iff_specializes y y₂).1 hle
  have h2 : (ιInf R F j).base y ⤳ (ιInf R F j).base y₂ := h1.map (ιInf R F j).continuous
  exact (ιInf R F j).isOpenEmbedding.injective (hcl _ h2)

end Overlap

section Eval

variable {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] (P : Place K Fb)

noncomputable def resEquiv (hP : P.IsRational) : K ≃+* P.ResidueField :=
  RingEquiv.ofBijective (algebraMap K P.ResidueField) ⟨P.algebraMap_residueField_injective, hP⟩

noncomputable def evalHom (hP : P.IsRational) : P.toValuationSubring →+* K :=
  (resEquiv P hP).symm.toRingHom.comp (residue P.toValuationSubring)

theorem evalHom_apply (hP : P.IsRational) (f : P.toValuationSubring) :
    evalHom P hP f = P.evalAt (f : Fb) := by
  apply (resEquiv P hP).injective
  show resEquiv P hP ((resEquiv P hP).symm (residue _ f)) = algebraMap K P.ResidueField (P.evalAt (f : Fb))
  rw [RingEquiv.apply_symm_apply, Place.algebraMap_evalAt P hP f.2]

theorem evalAt_mul (hP : P.IsRational) {f g : Fb} (hf : f ∈ P.toValuationSubring)
    (hg : g ∈ P.toValuationSubring) : P.evalAt (f * g) = P.evalAt f * P.evalAt g := by
  have h := map_mul (evalHom P hP) ⟨f, hf⟩ ⟨g, hg⟩
  rw [evalHom_apply, evalHom_apply, evalHom_apply] at h
  exact h

end Eval

section Ker

variable {C K : Type*} [CommRing C] [Field K] (e : C →+* K) (A : ValuationSubring K)

noncomputable def toResidue (hA : ∀ c, e c ∈ A) : C →+* ResidueField A :=
  (residue A).comp (e.codRestrict A hA)

theorem toResidue_apply (hA : ∀ c, e c ∈ A) (c : C) :
    toResidue e A hA c = residue A ⟨e c, hA c⟩ := rfl

theorem ker_toResidue (hA : ∀ c, e c ∈ A) (I : Ideal C)
    (hI : ∀ c, A.valuation (e c) < 1 ↔ c ∈ I) : RingHom.ker (toResidue e A hA) = I := by
  ext c
  rw [RingHom.mem_ker, toResidue_apply, ← hI]
  show Ideal.Quotient.mk (maximalIdeal A) _ = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, ValuationSubring.valuation_lt_one_iff]

end Ker

section PlaceNonunits

variable {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] (P : Place K Fb)

theorem algebraMap_residueField_eq (c : K) :
    algebraMap K P.ResidueField c = residue P.toValuationSubring (algebraMap K P.toValuationSubring c) := rfl

theorem mem_nonunits_iff_residue_eq_zero {f : Fb} (hf : f ∈ P.toValuationSubring) :
    f ∈ P.toValuationSubring.nonunits ↔ residue P.toValuationSubring ⟨f, hf⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff]

theorem sub_algebraMap_evalAt_mem_nonunits (hP : P.IsRational) {f : Fb} (hf : f ∈ P.toValuationSubring) :
    f - algebraMap K Fb (P.evalAt f) ∈ P.toValuationSubring.nonunits := by
  have hmem : f - algebraMap K Fb (P.evalAt f) ∈ P.toValuationSubring :=
    sub_mem hf (by rw [← Place.coe_algebraMap]; exact (algebraMap K P.toValuationSubring _).2)
  rw [mem_nonunits_iff_residue_eq_zero P hmem]
  have : (⟨f - algebraMap K Fb (P.evalAt f), hmem⟩ : P.toValuationSubring) =
      ⟨f, hf⟩ - algebraMap K P.toValuationSubring (P.evalAt f) :=
    Subtype.ext (by rw [AddSubgroupClass.coe_sub, Place.coe_algebraMap])
  rw [this, map_sub, ← algebraMap_residueField_eq, Place.algebraMap_evalAt P hP hf, sub_self]

theorem evalAt_eq_of_sub_algebraMap_mem_nonunits (hP : P.IsRational) {f : Fb} (hf : f ∈ P.toValuationSubring)
    {c : K} (h : f - algebraMap K Fb c ∈ P.toValuationSubring.nonunits) : P.evalAt f = c := by
  have hmem : f - algebraMap K Fb c ∈ P.toValuationSubring :=
    sub_mem hf (by rw [← Place.coe_algebraMap]; exact (algebraMap K P.toValuationSubring _).2)
  rw [mem_nonunits_iff_residue_eq_zero P hmem] at h
  have : (⟨f - algebraMap K Fb c, hmem⟩ : P.toValuationSubring) = ⟨f, hf⟩ - algebraMap K P.toValuationSubring c :=
    Subtype.ext (by rw [AddSubgroupClass.coe_sub, Place.coe_algebraMap])
  rw [this, map_sub, sub_eq_zero, ← Place.algebraMap_evalAt P hP hf, ← algebraMap_residueField_eq] at h
  exact P.algebraMap_residueField_injective h

theorem evalAt_eq_zero_iff_mem_nonunits (hP : P.IsRational) {f : Fb} (hf : f ∈ P.toValuationSubring) :
    P.evalAt f = 0 ↔ f ∈ P.toValuationSubring.nonunits := by
  constructor
  · intro h
    have := sub_algebraMap_evalAt_mem_nonunits P hP hf
    rwa [h, map_zero, sub_zero] at this
  · intro h
    exact evalAt_eq_of_sub_algebraMap_mem_nonunits P hP hf (c := 0) (by rwa [map_zero, sub_zero])

theorem mul_mem_nonunits {f g : Fb} (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring.nonunits) :
    f * g ∈ P.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hg ⊢
  rw [Valuation.map_mul]
  calc P.toValuationSubring.valuation f * P.toValuationSubring.valuation g
      ≤ 1 * P.toValuationSubring.valuation g :=
        mul_le_mul_left ((P.toValuationSubring.valuation_le_one_iff f).2 hf) _
    _ = P.toValuationSubring.valuation g := one_mul _
    _ < 1 := hg

end PlaceNonunits

section PlaceTransport

variable {K F₁ F₂ : Type*} [Field K] [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]

theorem mem_nonunits_iff_eq_zero_or_inv_not_mem {L : Type*} [Field L] (A : ValuationSubring L) (x : L) :
    x ∈ A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A := by
  rw [ValuationSubring.mem_nonunits_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← ValuationSubring.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]
    exact (or_iff_right hx).symm

theorem map_mem_nonunits_iff (φ : F₁ →+* F₂) (P₁ : Place K F₁) (P₂ : Place K F₂)
    (h : ∀ g, g ∈ P₁.toValuationSubring ↔ φ g ∈ P₂.toValuationSubring) (g : F₁) :
    g ∈ P₁.toValuationSubring.nonunits ↔ φ g ∈ P₂.toValuationSubring.nonunits := by
  rw [mem_nonunits_iff_eq_zero_or_inv_not_mem, mem_nonunits_iff_eq_zero_or_inv_not_mem,
    map_eq_zero_iff φ φ.injective, ← map_inv₀, ← h]

end PlaceTransport

section GammaH

open scoped MatrixGroups
open CongruenceSubgroup

theorem Gamma_le_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := Gamma_mem.mp hA
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H

theorem GammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaH M H)

end GammaH

end L2Aux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

namespace TEQVAuxIg

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem exists_inf_fraction (z : ↥(XMid R F j)) (g h : ↥(chartAlgFin R F j)) :
    ∃ (N : ℕ) (g' h' : ↥(chartAlgInf R F j)),
      (g' : F) = (g : F) * (j⁻¹) ^ N ∧ (h' : F) = (h : F) * (j⁻¹) ^ N ∧
      (g ∈ Ideal.comap (inclFin R F j).toRingHom z.asIdeal ↔ g' ∈ Ideal.comap (inclInf R F j).toRingHom z.asIdeal) ∧
      (h ∈ Ideal.comap (inclFin R F j).toRingHom z.asIdeal ↔ h' ∈ Ideal.comap (inclInf R F j).toRingHom z.asIdeal) := by
  have hj0 : j ≠ 0 := Fact.out
  have hsub : ∀ b : ↥(chartAlgFin R F j), (b : F) ∈ chartAlg R F (insert j⁻¹⁻¹ {j⁻¹}) := fun b => by
    rw [inv_inv]; exact chartAlg_mono R F (Set.singleton_subset_iff.2 (Set.mem_insert j _)) b.2
  obtain ⟨n₁, hn₁⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton j⁻¹) (inv_ne_zero hj0) (hsub g)
  obtain ⟨n₂, hn₂⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton j⁻¹) (inv_ne_zero hj0) (hsub h)
  have hjI : j⁻¹ ∈ chartAlg R F ({j⁻¹} : Set F) := (jInvChartInf R F j).2
  have hmemg : (g : F) * (j⁻¹) ^ (n₁ + n₂) ∈ chartAlg R F ({j⁻¹} : Set F) := by
    rw [pow_add, show (g : F) * ((j⁻¹) ^ n₁ * (j⁻¹) ^ n₂) = (j⁻¹ ^ n₁ * g) * (j⁻¹) ^ n₂ by ring]
    exact Subalgebra.mul_mem _ hn₁ (Subalgebra.pow_mem _ hjI _)
  have hmemh : (h : F) * (j⁻¹) ^ (n₁ + n₂) ∈ chartAlg R F ({j⁻¹} : Set F) := by
    rw [pow_add, show (h : F) * ((j⁻¹) ^ n₁ * (j⁻¹) ^ n₂) = (j⁻¹) ^ n₁ * ((j⁻¹ ^ n₂ * h)) by ring]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hjI _) hn₂
  have hu : IsUnit (inclInf R F j (jInvChartInf R F j) ^ (n₁ + n₂)) := (isUnit_inclInf_jInvChartInf R F j).pow _
  have e1 : ∀ x, (inclInf R F j).toRingHom x = inclInf R F j x := fun _ => rfl
  have e2 : ∀ x, (inclFin R F j).toRingHom x = inclFin R F j x := fun _ => rfl
  have key : ∀ (b : ↥(chartAlgFin R F j)) (hb : (b : F) * (j⁻¹) ^ (n₁ + n₂) ∈ chartAlg R F ({j⁻¹} : Set F)),
      inclInf R F j ⟨(b : F) * (j⁻¹) ^ (n₁ + n₂), hb⟩ = inclFin R F j b * inclInf R F j (jInvChartInf R F j) ^ (n₁ + n₂) := by
    intro b hb
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_chartIncl, coe_chartIncl, coe_chartIncl, coe_jInvChartInf]
  refine ⟨n₁ + n₂, ⟨_, hmemg⟩, ⟨_, hmemh⟩, rfl, rfl, ?_, ?_⟩
  · rw [Ideal.mem_comap, Ideal.mem_comap, e1, e2, key, Ideal.mul_unit_mem_iff_mem _ hu]
  · rw [Ideal.mem_comap, Ideal.mem_comap, e1, e2, key, Ideal.mul_unit_mem_iff_mem _ hu]

theorem exists_fin_fraction (z : ↥(XMid R F j)) (g h : ↥(chartAlgInf R F j)) :
    ∃ (N : ℕ) (g' h' : ↥(chartAlgFin R F j)),
      (g' : F) = (g : F) * j ^ N ∧ (h' : F) = (h : F) * j ^ N ∧
      (g ∈ Ideal.comap (inclInf R F j).toRingHom z.asIdeal ↔ g' ∈ Ideal.comap (inclFin R F j).toRingHom z.asIdeal) ∧
      (h ∈ Ideal.comap (inclInf R F j).toRingHom z.asIdeal ↔ h' ∈ Ideal.comap (inclFin R F j).toRingHom z.asIdeal) := by
  have hj0 : j ≠ 0 := Fact.out
  have hsub : ∀ b : ↥(chartAlgInf R F j), (b : F) ∈ chartAlg R F (insert j⁻¹ {j}) := fun b =>
    chartAlg_mono R F (Set.singleton_subset_iff.2 (Set.mem_insert j⁻¹ _)) b.2
  obtain ⟨n₁, hn₁⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton j) hj0 (hsub g)
  obtain ⟨n₂, hn₂⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton j) hj0 (hsub h)
  have hjF : j ∈ chartAlg R F ({j} : Set F) := (jChartFin R F j).2
  have hmemg : (g : F) * j ^ (n₁ + n₂) ∈ chartAlg R F ({j} : Set F) := by
    rw [pow_add, show (g : F) * (j ^ n₁ * j ^ n₂) = (j ^ n₁ * g) * j ^ n₂ by ring]
    exact Subalgebra.mul_mem _ hn₁ (Subalgebra.pow_mem _ hjF _)
  have hmemh : (h : F) * j ^ (n₁ + n₂) ∈ chartAlg R F ({j} : Set F) := by
    rw [pow_add, show (h : F) * (j ^ n₁ * j ^ n₂) = j ^ n₁ * ((j ^ n₂ * h)) by ring]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hjF _) hn₂
  have hu : IsUnit (inclFin R F j (jChartFin R F j) ^ (n₁ + n₂)) := (isUnit_inclFin_jChartFin R F j).pow _
  have e1 : ∀ x, (inclInf R F j).toRingHom x = inclInf R F j x := fun _ => rfl
  have e2 : ∀ x, (inclFin R F j).toRingHom x = inclFin R F j x := fun _ => rfl
  have key : ∀ (b : ↥(chartAlgInf R F j)) (hb : (b : F) * j ^ (n₁ + n₂) ∈ chartAlg R F ({j} : Set F)),
      inclFin R F j ⟨(b : F) * j ^ (n₁ + n₂), hb⟩ = inclInf R F j b * inclFin R F j (jChartFin R F j) ^ (n₁ + n₂) := by
    intro b hb
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_chartIncl, coe_chartIncl, coe_chartIncl, coe_jChartFin]
  refine ⟨n₁ + n₂, ⟨_, hmemg⟩, ⟨_, hmemh⟩, rfl, rfl, ?_, ?_⟩
  · rw [Ideal.mem_comap, Ideal.mem_comap, e1, e2, key, Ideal.mul_unit_mem_iff_mem _ hu]
  · rw [Ideal.mem_comap, Ideal.mem_comap, e1, e2, key, Ideal.mul_unit_mem_iff_mem _ hu]

theorem inStalk_iff_fin (y : ↥(XFin R F j)) (f : F) :
    ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = (ιFin R F j).base y →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = (ιFin R F j).base y →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ f * (h : F) = (g : F))) ↔
    ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F) := by
  constructor
  · rintro ⟨hF, -⟩
    exact hF y rfl
  · rintro ⟨g, h, hh, e⟩
    refine ⟨fun y₂ hy₂ => ?_, fun y' hy' => ?_⟩
    · have hyy : y₂ = y := (ιFin R F j).isOpenEmbedding.injective hy₂
      subst hyy
      exact ⟨g, h, hh, e⟩
    · obtain ⟨z, hzy, hzy'⟩ := L2Aux.exists_comap_eq_of_ιFin_eq_ιInf R F j y y' hy'.symm
      obtain ⟨N, g', h', hg', hh', -, hiff⟩ := exists_inf_fraction R F j z g h
      refine ⟨g', h', ?_, ?_⟩
      · rw [hzy']; exact fun hm => hh (by rw [hzy]; exact hiff.2 hm)
      · rw [hh', hg', ← mul_assoc, e]

theorem inMax_iff_fin (y : ↥(XFin R F j)) (f : F) :
    ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = (ιFin R F j).base y →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ g ∈ y₂.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = (ιFin R F j).base y →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ g ∈ y'.asIdeal ∧ f * (h : F) = (g : F))) ↔
    ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F) := by
  constructor
  · rintro ⟨hF, -⟩
    exact hF y rfl
  · rintro ⟨g, h, hh, hg, e⟩
    refine ⟨fun y₂ hy₂ => ?_, fun y' hy' => ?_⟩
    · have hyy : y₂ = y := (ιFin R F j).isOpenEmbedding.injective hy₂
      subst hyy
      exact ⟨g, h, hh, hg, e⟩
    · obtain ⟨z, hzy, hzy'⟩ := L2Aux.exists_comap_eq_of_ιFin_eq_ιInf R F j y y' hy'.symm
      obtain ⟨N, g', h', hg', hh', hiffg, hiffh⟩ := exists_inf_fraction R F j z g h
      refine ⟨g', h', ?_, ?_, ?_⟩
      · rw [hzy']; exact fun hm => hh (by rw [hzy]; exact hiffh.2 hm)
      · rw [hzy']; exact hiffg.1 (by rw [← hzy]; exact hg)
      · rw [hh', hg', ← mul_assoc, e]

theorem inStalk_iff_inf' (y : ↥(XInf R F j)) (f : F) :
    ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = (ιInf R F j).base y →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = (ιInf R F j).base y →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ f * (h : F) = (g : F))) ↔
    ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F) := by
  constructor
  · rintro ⟨-, hI⟩
    exact hI y rfl
  · rintro ⟨g, h, hh, e⟩
    refine ⟨fun y₂ hy₂ => ?_, fun y' hy' => ?_⟩
    · obtain ⟨z, hzy, hzy'⟩ := L2Aux.exists_comap_eq_of_ιFin_eq_ιInf R F j y₂ y hy₂
      obtain ⟨N, g', h', hg', hh', -, hiff⟩ := exists_fin_fraction R F j z g h
      refine ⟨g', h', ?_, ?_⟩
      · rw [hzy]; exact fun hm => hh (by rw [hzy']; exact hiff.2 hm)
      · rw [hh', hg', ← mul_assoc, e]
    · have hyy : y' = y := (ιInf R F j).isOpenEmbedding.injective hy'
      subst hyy
      exact ⟨g, h, hh, e⟩

theorem inMax_iff_inf' (y : ↥(XInf R F j)) (f : F) :
    ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = (ιInf R F j).base y →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ g ∈ y₂.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = (ιInf R F j).base y →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ g ∈ y'.asIdeal ∧ f * (h : F) = (g : F))) ↔
    ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F) := by
  constructor
  · rintro ⟨-, hI⟩
    exact hI y rfl
  · rintro ⟨g, h, hh, hg, e⟩
    refine ⟨fun y₂ hy₂ => ?_, fun y' hy' => ?_⟩
    · obtain ⟨z, hzy, hzy'⟩ := L2Aux.exists_comap_eq_of_ιFin_eq_ιInf R F j y₂ y hy₂
      obtain ⟨N, g', h', hg', hh', hiffg, hiffh⟩ := exists_fin_fraction R F j z g h
      refine ⟨g', h', ?_, ?_, ?_⟩
      · rw [hzy]; exact fun hm => hh (by rw [hzy']; exact hiffh.2 hm)
      · rw [hzy]; exact hiffg.1 (by rw [← hzy']; exact hg)
      · rw [hh', hg', ← mul_assoc, e]
    · have hyy : y' = y := (ιInf R F j).isOpenEmbedding.injective hy'
      subst hyy
      exact ⟨g, h, hh, hg, e⟩

theorem inStalk_iff_inf (y : ↥(XInf R F j)) (f : F) (hcusp : (ιInf R F j).base y ∉ Set.range (ιFin R F j).base) :
    ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = (ιInf R F j).base y →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = (ιInf R F j).base y →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ f * (h : F) = (g : F))) ↔
    ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F) :=
  inStalk_iff_inf' R F j y f

theorem inMax_iff_inf (y : ↥(XInf R F j)) (f : F) (hcusp : (ιInf R F j).base y ∉ Set.range (ιFin R F j).base) :
    ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = (ιInf R F j).base y →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ g ∈ y₂.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = (ιInf R F j).base y →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ g ∈ y'.asIdeal ∧ f * (h : F) = (g : F))) ↔
    ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F) :=
  inMax_iff_inf' R F j y f

private theorem _root_.TEQVAuxIg.jInvChartInf_mem_of_not_mem_range (y : ↥(XInf R F j)) (h : (ιInf R F j).base y ∉ Set.range (ιFin R F j).base) :
    jInvChartInf R F j ∈ y.asIdeal :=
  L2Aux.jInvChartInf_mem_of_not_mem_range R F j y h

p2m_export "TEQVAuxIg" "jInvChartInf_mem_of_not_mem_range"

private theorem _root_.TEQVAuxIg.jChartFin_mem_of_not_mem_range (y : ↥(XFin R F j)) (h : (ιFin R F j).base y ∉ Set.range (ιInf R F j).base) :
    jChartFin R F j ∈ y.asIdeal :=
  L2Aux.jChartFin_mem_of_not_mem_range R F j y h

p2m_export "TEQVAuxIg" "jChartFin_mem_of_not_mem_range"
section Spec

theorem le_of_forall_frac_fin (y₁ y₂ : ↥(XFin R F j))
    (h : ∀ f : F, (∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ f * (h : F) = (g : F)) →
      (∃ g h : ↥(chartAlgFin R F j), h ∉ y₁.asIdeal ∧ f * (h : F) = (g : F))) :
    y₁.asIdeal ≤ y₂.asIdeal := by
  intro b hb
  by_contra hb₂
  have hb0 : (b : F) ≠ 0 := fun h0 => hb₂ (by rw [show b = 0 from Subtype.ext h0]; exact Ideal.zero_mem _)
  obtain ⟨g, k, hk, e⟩ := h (b : F)⁻¹ ⟨1, b, hb₂, by simp [hb0]⟩
  apply hk
  have : k = b * g := Subtype.ext (by
    simp only [Subalgebra.coe_mul]
    rw [← e]; field_simp)
  rw [this]; exact Ideal.mul_mem_right _ _ hb

theorem le_of_forall_frac_inf (y₁ y₂ : ↥(XInf R F j))
    (h : ∀ f : F, (∃ g h : ↥(chartAlgInf R F j), h ∉ y₂.asIdeal ∧ f * (h : F) = (g : F)) →
      (∃ g h : ↥(chartAlgInf R F j), h ∉ y₁.asIdeal ∧ f * (h : F) = (g : F))) :
    y₁.asIdeal ≤ y₂.asIdeal := by
  intro b hb
  by_contra hb₂
  have hb0 : (b : F) ≠ 0 := fun h0 => hb₂ (by rw [show b = 0 from Subtype.ext h0]; exact Ideal.zero_mem _)
  obtain ⟨g, k, hk, e⟩ := h (b : F)⁻¹ ⟨1, b, hb₂, by simp [hb0]⟩
  apply hk
  have : k = b * g := Subtype.ext (by
    simp only [Subalgebra.coe_mul]
    rw [← e]; field_simp)
  rw [this]; exact Ideal.mul_mem_right _ _ hb

theorem specializes_iff_forall_inStalk (x z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) :
    x ⤳ z ↔ ∀ f : F, ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = z →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = z →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ f * (h : F) = (g : F))) → ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = x →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = x →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ f * (h : F) = (g : F))) := by
  have hj0 : j ≠ 0 := Fact.out
  have hoF : IsOpen (Set.range (ιFin R F j).base) := (ιFin R F j).isOpenEmbedding.isOpen_range
  have hoI : IsOpen (Set.range (ιInf R F j).base) := (ιInf R F j).isOpenEmbedding.isOpen_range
  constructor
  · intro hxz f hz
    rcases mem_range_ιFin_or_mem_range_ιInf R F j z with ⟨yz, rfl⟩ | ⟨yz, rfl⟩
    · obtain ⟨yx, rfl⟩ := hxz.mem_open hoF ⟨yz, rfl⟩
      have hle : yx.asIdeal ≤ yz.asIdeal :=
        (PrimeSpectrum.le_iff_specializes yx yz).mpr (((ιFin R F j).isOpenEmbedding.isInducing.specializes_iff).mp hxz)
      rw [inStalk_iff_fin] at hz ⊢
      obtain ⟨g, h, hh, e⟩ := hz
      exact ⟨g, h, fun hh' => hh (hle hh'), e⟩
    · obtain ⟨yx, rfl⟩ := hxz.mem_open hoI ⟨yz, rfl⟩
      have hle : yx.asIdeal ≤ yz.asIdeal :=
        (PrimeSpectrum.le_iff_specializes yx yz).mpr (((ιInf R F j).isOpenEmbedding.isInducing.specializes_iff).mp hxz)
      rw [inStalk_iff_inf'] at hz ⊢
      obtain ⟨g, h, hh, e⟩ := hz
      exact ⟨g, h, fun hh' => hh (hle hh'), e⟩
  · intro h
    by_cases hzF : z ∈ Set.range (ιFin R F j).base
    · obtain ⟨yz, rfl⟩ := hzF
      by_cases hxF : x ∈ Set.range (ιFin R F j).base
      · obtain ⟨yx, rfl⟩ := hxF
        refine ((ιFin R F j).isOpenEmbedding.isInducing.specializes_iff).mpr
          ((PrimeSpectrum.le_iff_specializes yx yz).mp (le_of_forall_frac_fin R F j yx yz fun f hf => ?_))
        have := h f ((inStalk_iff_fin R F j yz f).mpr hf)
        exact (inStalk_iff_fin R F j yx f).mp this
      · exfalso
        rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨yx, rfl⟩ | ⟨yx, rfl⟩
        · exact hxF ⟨yx, rfl⟩
        have hcusp := L2Aux.jInvChartInf_mem_of_not_mem_range R F j yx hxF
        have hjz : ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = (ιFin R F j).base yz →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ j * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = (ιFin R F j).base yz →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ j * (h : F) = (g : F))) := (inStalk_iff_fin R F j yz j).mpr ⟨jChartFin R F j, 1, fun h1 => yz.isPrime.ne_top
          ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩
        obtain ⟨g, k, hk, e⟩ := (inStalk_iff_inf' R F j yx j).mp (h j hjz)
        apply hk
        have : k = jInvChartInf R F j * g := Subtype.ext (by
          rw [Subalgebra.coe_mul, coe_jInvChartInf, ← e]; field_simp)
        rw [this]; exact Ideal.mul_mem_right _ _ hcusp
    · rcases mem_range_ιFin_or_mem_range_ιInf R F j z with hz' | ⟨yz, rfl⟩
      · exact absurd hz' hzF
      by_cases hxI : x ∈ Set.range (ιInf R F j).base
      · obtain ⟨yx, rfl⟩ := hxI
        refine ((ιInf R F j).isOpenEmbedding.isInducing.specializes_iff).mpr
          ((PrimeSpectrum.le_iff_specializes yx yz).mp (le_of_forall_frac_inf R F j yx yz fun f hf => ?_))
        have := h f ((inStalk_iff_inf' R F j yz f).mpr hf)
        exact (inStalk_iff_inf' R F j yx f).mp this
      · exfalso
        rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨yx, rfl⟩ | ⟨yx, rfl⟩
        swap
        · exact hxI ⟨yx, rfl⟩
        have hfin := L2Aux.jChartFin_mem_of_not_mem_range R F j yx hxI
        have hjz : ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = (ιInf R F j).base yz →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ j⁻¹ * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = (ιInf R F j).base yz →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ j⁻¹ * (h : F) = (g : F))) := (inStalk_iff_inf' R F j yz j⁻¹).mpr ⟨jInvChartInf R F j, 1, fun h1 => yz.isPrime.ne_top
          ((Ideal.eq_top_iff_one _).mpr h1), by simp [coe_jInvChartInf]⟩
        obtain ⟨g, k, hk, e⟩ := (inStalk_iff_fin R F j yx j⁻¹).mp (h j⁻¹ hjz)
        apply hk
        have : k = jChartFin R F j * g := Subtype.ext (by
          rw [Subalgebra.coe_mul, coe_jChartFin, ← e]; field_simp)
        rw [this]; exact Ideal.mul_mem_right _ _ hfin

theorem eq_of_forall_inStalk_iff (x z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (h : ∀ f : F, ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = x →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = x →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ f * (h : F) = (g : F))) ↔ ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = z →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = z →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ f * (h : F) = (g : F)))) : x = z := by
  have h1 : x ⤳ z := (specializes_iff_forall_inStalk R F j x z).mpr fun f hf => (h f).mpr hf
  have h2 : z ⤳ x := (specializes_iff_forall_inStalk R F j z x).mpr fun f hf => (h f).mp hf
  exact (h1.antisymm h2).eq

end Spec

end TEQVAuxIg

namespace TEQVAuxIg

section ReadsTransport

open scoped Pointwise

theorem reads_transport {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar] (R : AlgebraicCurve.RegularProlongation A F Fbar)
    (τ : F ≃ₐ[L] F) (hτ : ∀ f : F, τ f ∈ R.integers ↔ f ∈ R.integers)
    {T : Type*} (ι : T → F) (σ : T ≃ T) (hσ : ∀ f : T, ι (σ f) = τ (ι f))
    (InSt InSt' InMx InMx' : T → Prop) (hSt : ∀ f, InSt' (σ f) ↔ InSt f) (hMx : ∀ f, InMx' (σ f) ↔ InMx f)
    (Q : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥A) Fbar)
    (h : ∀ f : T, InSt f → ∃ hR : ι f ∈ R.integers, (R.residue ⟨ι f, hR⟩ : Fbar) ∈ Q.toValuationSubring ∧
            ((R.residue ⟨ι f, hR⟩ : Fbar) ∈ Q.toValuationSubring.nonunits ↔ InMx f)) :
    ∀ f : T, InSt' f → ∃ hR : ι f ∈ R.integers, (R.residue ⟨ι f, hR⟩ : Fbar) ∈ (R.resAut τ hτ • Q).toValuationSubring ∧
            ((R.residue ⟨ι f, hR⟩ : Fbar) ∈ (R.resAut τ hτ • Q).toValuationSubring.nonunits ↔ InMx' f) := by
  intro f hf
  set g := σ.symm f with hg
  have hfg : f = σ g := (σ.apply_symm_apply f).symm
  have hgSt : InSt g := (hSt g).mp (by rw [← hfg]; exact hf)
  obtain ⟨hR, hmem, hiff⟩ := h g hgSt
  have hιf : ι f = τ (ι g) := by rw [hfg, hσ]
  have hR' : ι f ∈ R.integers := by rw [hιf]; exact (hτ _).mpr hR
  have hres : (R.residue ⟨ι f, hR'⟩ : Fbar) = R.resAut τ hτ (R.residue ⟨ι g, hR⟩) := by
    rw [AlgebraicCurve.RegularProlongation.resAut_residue]
    congr 1
    exact Subtype.ext hιf
  refine ⟨hR', ?_, ?_⟩
  · rw [hres]
    exact (AlgebraicCurve.Place.Transport.mem_smul_iff' _ Q _).mpr hmem
  · rw [hres, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀, AlgebraicCurve.Place.Transport.mem_smul_iff', map_eq_zero,
      ← ValuationSubring.mem_nonunits_iff_or, hiff, ← hMx g, ← hfg]

end ReadsTransport

section ClosedTransport

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem closed_transport (σ : F ≃ F) (x x' : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (hx : ∀ z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j), x ⤳ z → z = x)
    (hxx' : ∀ f : F, ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = x' →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = x' →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ f * (h : F) = (g : F))) ↔ ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = x →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ σ.symm f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = x →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ σ.symm f * (h : F) = (g : F))))
    (hsurj : ∀ z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j), ∃ z₀ : ↥(AlgebraicCurve.TwoChartIntegralModel R F j),
      ∀ f : F, ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = z →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = z →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ f * (h : F) = (g : F))) ↔ ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = z₀ →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ σ.symm f * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = z₀ →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ σ.symm f * (h : F) = (g : F)))) :
    ∀ z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j), x' ⤳ z → z = x' := by
  intro z hz
  obtain ⟨z₀, hz₀⟩ := hsurj z
  have hxz₀ : x ⤳ z₀ := by
    rw [specializes_iff_forall_inStalk]
    intro f hf
    have h1 := (hz₀ (σ f)).mpr (by rw [Equiv.symm_apply_apply]; exact hf)
    have h2 := ((specializes_iff_forall_inStalk R F j x' z).mp hz) (σ f) h1
    have h3 := (hxx' (σ f)).mp h2
    rwa [Equiv.symm_apply_apply] at h3
  have hz₀x : z₀ = x := hx z₀ hxz₀
  subst hz₀x
  apply eq_of_forall_inStalk_iff R F j
  intro f
  rw [hz₀ f, hxx' f]

theorem toBase_eq_closedPoint_iff [IsLocalRing R] (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) :
    (AlgebraicCurve.TwoChartIntegralModel.toBase R F j).base x = IsLocalRing.closedPoint R ↔
      ∀ r : R, r ∈ IsLocalRing.maximalIdeal R → ((∀ y₂ : ↥(XFin R F j), (ιFin R F j).base y₂ = x →
        ∃ g h : ↥(chartAlgFin R F j), h ∉ y₂.asIdeal ∧ g ∈ y₂.asIdeal ∧ algebraMap R F r * (h : F) = (g : F)) ∧
      (∀ y' : ↥(XInf R F j), (ιInf R F j).base y' = x →
        ∃ g h : ↥(chartAlgInf R F j), h ∉ y'.asIdeal ∧ g ∈ y'.asIdeal ∧ algebraMap R F r * (h : F) = (g : F))) := by

  have key : ∀ {C : Type u} [CommRing C] [Algebra R C] (y : PrimeSpectrum C),
      PrimeSpectrum.comap (algebraMap R C) y = IsLocalRing.closedPoint R ↔
        ∀ r : R, r ∈ IsLocalRing.maximalIdeal R → algebraMap R C r ∈ y.asIdeal := by
    intro C _ _ y
    constructor
    · intro h r hr
      have : r ∈ (PrimeSpectrum.comap (algebraMap R C) y).asIdeal := by
        rw [h]; exact hr
      exact this
    · intro h
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R C) y.asIdeal = IsLocalRing.maximalIdeal R
      refine le_antisymm (IsLocalRing.le_maximalIdeal ?_) fun r hr => h r hr
      exact Ideal.IsPrime.ne_top inferInstance
  rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · have hb : (AlgebraicCurve.TwoChartIntegralModel.toBase R F j).base ((ιFin R F j).base y) =
        PrimeSpectrum.comap (algebraMap R ↥(chartAlgFin R F j)) y := by
      show ((ιFin R F j) ≫ AlgebraicCurve.TwoChartIntegralModel.toBase R F j).base y = _
      rw [ιFin_toBase]
      rfl
    rw [hb]
    refine (key (C := ↥(chartAlgFin R F j)) y).trans (forall_congr' fun r => forall_congr' fun hr => ?_)
    rw [inMax_iff_fin]
    constructor
    · intro hm
      exact ⟨algebraMap R _ r, 1, fun h1 => y.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), hm, by simp⟩
    · rintro ⟨g, h, hh, hg, e⟩
      have : algebraMap R ↥(chartAlgFin R F j) r * h = g := Subtype.ext (by simpa using e)
      exact (y.isPrime.mem_or_mem (this ▸ hg)).resolve_right hh
  · have hb : (AlgebraicCurve.TwoChartIntegralModel.toBase R F j).base ((ιInf R F j).base y) =
        PrimeSpectrum.comap (algebraMap R ↥(chartAlgInf R F j)) y := by
      show ((ιInf R F j) ≫ AlgebraicCurve.TwoChartIntegralModel.toBase R F j).base y = _
      rw [ιInf_toBase]
      rfl
    rw [hb]
    refine (key (C := ↥(chartAlgInf R F j)) y).trans (forall_congr' fun r => forall_congr' fun hr => ?_)
    rw [inMax_iff_inf']
    constructor
    · intro hm
      exact ⟨algebraMap R _ r, 1, fun h1 => y.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), hm, by simp⟩
    · rintro ⟨g, h, hh, hg, e⟩
      have : algebraMap R ↥(chartAlgInf R F j) r * h = g := Subtype.ext (by simpa using e)
      exact (y.isPrime.mem_or_mem (this ▸ hg)).resolve_right hh

end ClosedTransport

end TEQVAuxIg

namespace TEQVAuxT0

open AlgebraicCurve

theorem centred_transport {L F : Type*} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    (τ : F ≃ₐ[L] F) {T : Type*} (ι : T → F) (σ : T ≃ T) (hσ : ∀ f, ι (σ f) = τ (ι f))
    (InSt InSt' InMx InMx' : T → Prop) (hSt : ∀ f, InSt' (σ f) ↔ InSt f) (hMx : ∀ f, InMx' (σ f) ↔ InMx f)
    (P : Place L F) :
    (P.IsRational ∧ ∀ f, InSt' f → ι f ∈ P.toValuationSubring ∧ P.evalAt (ι f) ∈ A ∧
        (A.valuation (P.evalAt (ι f)) < 1 ↔ InMx' f)) ↔
    ((τ⁻¹ • P).IsRational ∧ ∀ f, InSt f → ι f ∈ (τ⁻¹ • P).toValuationSubring ∧ (τ⁻¹ • P).evalAt (ι f) ∈ A ∧
        (A.valuation ((τ⁻¹ • P).evalAt (ι f)) < 1 ↔ InMx f)) := by
  have hτinv : ∀ f : F, (τ⁻¹).symm f = τ f := fun f => rfl
  constructor
  · rintro ⟨hPr, hPc⟩
    refine ⟨(Place.Transport.isRational_smul_iff τ⁻¹ P).2 hPr, fun f hf => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hPc (σ f) ((hSt f).2 hf)
    rw [hσ] at h1 h2 h3
    refine ⟨(Place.Transport.mem_smul_iff τ⁻¹ P _).2 (by rw [hτinv]; exact h1), ?_, ?_⟩
    · rw [Place.Transport.evalAt_smul_symm τ⁻¹ P hPr, hτinv]; exact h2
    · rw [Place.Transport.evalAt_smul_symm τ⁻¹ P hPr, hτinv]; exact h3.trans (hMx f)
  · rintro ⟨hPr, hPc⟩
    have hPr' : P.IsRational := (Place.Transport.isRational_smul_iff τ⁻¹ P).1 hPr
    refine ⟨hPr', fun f hf => ?_⟩
    have hf' : InSt (σ.symm f) := (hSt (σ.symm f)).1 (by rw [Equiv.apply_symm_apply]; exact hf)
    obtain ⟨h1, h2, h3⟩ := hPc (σ.symm f) hf'
    have e2 : τ (ι (σ.symm f)) = ι f := by rw [← hσ, Equiv.apply_symm_apply]
    rw [Place.Transport.mem_smul_iff τ⁻¹ P, hτinv, e2] at h1
    rw [Place.Transport.evalAt_smul_symm τ⁻¹ P hPr', hτinv, e2] at h2 h3
    refine ⟨h1, h2, h3.trans ?_⟩
    have := hMx (σ.symm f)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm

end TEQVAuxT0

p2m_open "ModularCurve~coeffMap_jqModC~coeffMap_jqNModC AlgebraicCurve"

namespace TEQVAuxIg

theorem mem_ssJSet_iff_of_kronecker
    {A : Type} [CommRing A] {T : Type} [Field T] [Algebra A T]
    (q : ℕ) [Fact q.Prime]
    (ι : T →+* LaurentSeries (AlgebraicClosure ℚ)) (hι : Function.Injective ι)
    (j j' : T)
    (hj : ι j = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq)
    (hj' : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      ι j' = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ q ModularCurve.jq))
    (hj'B : j' ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A T j)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A T j) →+* Ω) :
    φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A T j) ∈ ModularCurve.ssJSet q Ω ↔
      φ ⟨j', hj'B⟩ ∈ ModularCurve.ssJSet q Ω := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : NeZero (1 * q) := by rw [one_mul]; infer_instance

  have hjC : ι j = jqModC (AlgebraicClosure ℚ) := by
    rw [hj]; exact ModularCurve.coeffSemilinearAut.coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  have hNq : jqNModC (AlgebraicClosure ℚ) (1 * q) = jqNModC (AlgebraicClosure ℚ) q := by
    simp only [jqNModC, one_mul]
  have hj'C : ι j' = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
    rw [hj', hNq]; exact ModularCurve.coeffSemilinearAut.coeffMap_jqNModC (algebraMap ℚ (AlgebraicClosure ℚ)) q

  let R : Subring (LaurentSeries (AlgebraicClosure ℚ)) := (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A T j).toSubring.map ι
  have hjR : jqModC (AlgebraicClosure ℚ) ∈ R := ⟨j, (TwoChartIntegralModel.jChartFin A T j).2, hjC⟩
  have hj'R : jqNModC (AlgebraicClosure ℚ) (1 * q) ∈ R := ⟨j', hj'B, hj'C⟩
  have key := ModularCurve.sub_mul_sub_mem_span_natCast_of_jqModC_mem_of_jqNModC_mem q R hjR hj'R
  rw [Ideal.mem_span_singleton'] at key
  obtain ⟨c, hc⟩ := key
  obtain ⟨c', hc'B, hc'⟩ := c.2

  let jF : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A T j) := TwoChartIntegralModel.jChartFin A T j
  let j'F : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A T j) := ⟨j', hj'B⟩
  have hψinj : Function.Injective (ι.comp (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A T j) T)) := hι.comp Subtype.val_injective
  have E : (jF ^ q - j'F) * (jF - j'F ^ q) = ⟨c', hc'B⟩ * (q : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A T j)) := by
    apply hψinj
    have h := congrArg Subtype.val hc
    simp only [Subring.coe_mul, Subring.coe_natCast, SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub] at h
    simp only [map_mul, map_sub, map_pow, map_natCast, RingHom.coe_comp, Function.comp_apply]
    rw [show algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A T j) T jF = j from rfl, show algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A T j) T j'F = j' from rfl,
      show algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A T j) T ⟨c', hc'B⟩ = c' from rfl, hjC, hj'C, hc']
    exact h.symm

  have E' := congrArg φ E
  simp only [map_mul, map_sub, map_pow, map_natCast, CharP.cast_eq_zero, mul_zero] at E'
  rw [mul_eq_zero, sub_eq_zero, sub_eq_zero] at E'
  show φ jF ∈ ssJSet q Ω ↔ φ j'F ∈ ssJSet q Ω
  rcases E' with h1 | h2
  · rw [← h1, ModularCurve.pow_mem_ssJSet_iff]
  · rw [h2, ModularCurve.pow_mem_ssJSet_iff]

end TEQVAuxIg

section FTW5
p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_jqModC~coeffMap_jqNModC ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups
namespace TH1Wanted2

theorem chartAlg_singleton_le_valuationSubring
    {F : Type} [Field F] {T : Type} [Field T] {A₁ : Type} [CommRing A₁] [Algebra A₁ T]
    (emb : T →+* F) (O : ValuationSubring F) (t : T)
    (ht : emb t ∈ O) (hconst : ∀ a : A₁, emb (algebraMap A₁ T a) ∈ O) :
    ∀ c, c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg A₁ T {t} → emb c ∈ O := by
  intro c hc
  let S' : Subalgebra A₁ T :=
    { carrier := {x | emb x ∈ O}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul]; exact mul_mem ha hb
      one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact one_mem O
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add]; exact add_mem ha hb
      zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact zero_mem O
      algebraMap_mem' := hconst }
  have hadj : Algebra.adjoin A₁ ({t} : Set T) ≤ S' := Algebra.adjoin_le (Set.singleton_subset_iff.2 ht)
  let ψ : ↥(Algebra.adjoin A₁ ({t} : Set T)) →+* ↥O :=
    (emb.comp (Algebra.adjoin A₁ ({t} : Set T)).val.toRingHom).codRestrict O (fun s => hadj s.2)
  have hcint : IsIntegral ↥(Algebra.adjoin A₁ ({t} : Set T)) c :=
    (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A₁ T).1 hc
  have hint : IsIntegral ↥O (emb c) :=
    hcint.map_of_comp_eq ψ emb (RingHom.ext fun _ => rfl)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := ↥O) (A := F)).1 hint
  rw [← hy]
  exact y.2

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem inv_mem_and_const_mem_of_gaussPresentation
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →
    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],
    ∀ (j' : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) →
    ∀ (O : ValuationSubring ↥(fieldBar q M')),
      (∀ f : ↥(fieldBar q M'), f ∈ O ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) →
    ((j₁ : ↥(fieldBar q M')))⁻¹ ∈ O ∧ (j₁ : ↥(fieldBar q M')) ∈ O ∧
    ((j' : ↥(fieldBar q M')))⁻¹ ∈ O ∧ (j' : ↥(fieldBar q M')) ∈ O ∧
    (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ O) := by
  classical
  intro F₀ hK1 hLD hRAT instA₁ halg j₁ hj₁ instj₁ j' hj' O hO
  have hjt0 : (j₁ : ↥(fieldBar q M')) ≠ 0 := fun h => (Fact.out : j₁ ≠ 0) (Subtype.ext h)
  have hcoej₁ : ((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [hj₁]; rfl
  have hjq : coeffEmb (AlgebraicClosure ℚ) jq = coeffMap A.subtype (jqModC ↥A) := by
    show (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = (jqModC ↥A).map A.subtype
    rw [map_jqModC, map_jqModC]
  have hred : coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) = jqModC (ResidueField ↥A) := by
    show (jqModC ↥A).map _ = _
    exact map_jqModC _
  have hjκ0 : jqModC (ResidueField ↥A) ≠ 0 := fun h => by
    have h1 := ModularCurve.coeff_jqModC_neg_one (ResidueField ↥A)
    rw [h, HahnSeries.coeff_zero] at h1
    exact zero_ne_one h1
  have hjq0 : coeffEmb (AlgebraicClosure ℚ) jq ≠ 0 := by
    rw [← hcoej₁]
    exact fun h => hjt0 (Subtype.ext h)
  have hcoej' : ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap A.subtype (qExpand ↥A q (jqModC ↥A)) := by
    rw [hj', ModularCurve.coeffMap_qExpand, ← hjq]
    exact (ModularCurve.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) q jq)
  have hred' : coeffMap (IsLocalRing.residue ↥A) (qExpand ↥A q (jqModC ↥A)) ≠ 0 := by
    rw [ModularCurve.coeffMap_qExpand, hred]
    exact fun h => hjκ0 (qExpand_injective (R := ResidueField ↥A) (N := q) (by rw [h, map_zero]))
  have hj'0 : ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    rw [hj']
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ q jq) ≠ 0
    rw [ModularCurve.coeffMap_qExpand]
    exact fun h => hjq0 (qExpand_injective (R := AlgebraicClosure ℚ) (N := q) (h.trans (map_zero _).symm))
  have h1ne : coeffMap (IsLocalRing.residue ↥A) 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    refine (hO _).2 ⟨1, jqModC ↥A, by rw [hred]; exact hjκ0, ?_⟩
    rw [map_one, ← hjq]
    show ((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ * coeffEmb (AlgebraicClosure ℚ) jq = 1
    rw [hcoej₁, inv_mul_cancel₀ hjq0]
  ·
    refine (hO _).2 ⟨jqModC ↥A, 1, h1ne, ?_⟩
    rw [map_one, mul_one, hcoej₁, hjq]
  ·
    refine (hO _).2 ⟨1, qExpand ↥A q (jqModC ↥A), hred', ?_⟩
    rw [map_one, ← hcoej']
    show ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ * _ = 1
    exact inv_mul_cancel₀ hj'0
  ·
    refine (hO _).2 ⟨qExpand ↥A q (jqModC ↥A), 1, h1ne, ?_⟩
    rw [map_one, mul_one, hcoej']
  ·
    intro a
    rw [halg a]
    have haA : ((a : ↥K₁) : AlgebraicClosure ℚ) ∈ A := (hA₁ (a : ↥K₁)).1 a.2
    refine (hO _).2 ⟨HahnSeries.single 0 ⟨_, haA⟩, 1, h1ne, ?_⟩
    rw [map_one, mul_one, coeffMap_single]
    show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((a : ↥K₁) : AlgebraicClosure ℚ) = _
    rw [algebraMap_laurentSeries_eq_single]
    rfl

end TH1Wanted2
end FTW5

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_jqModC~coeffMap_jqNModC ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 256000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],

    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let Centred : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun P x =>
      P.IsRational ∧ ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A ∧
          (A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ InMax x f)

    let GoodPt : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω)

    let Reads : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Prop := fun x Q =>
      ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring ∧
          (R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring.nonunits ↔ InMax x f)

    ∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
        ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
      ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers),
        ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x → ∃ x' : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x' ∧
          (∀ Q, Reads x Q → Reads x' (R.resAut τ hτ • Q)) ∧
          (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), Centred P x' ↔ Centred (τ⁻¹ • P) x) := by

  classical
  intro F₀ hK1 hSTAB hLD hRAT instA₁ halg j₁ hj₁ instj₁ InStalk InMax Centred GoodPt Reads τ hτmem hτ x hx
  have hjt0 : (j₁ : ↥(fieldBar q M')) ≠ 0 := fun h => (Fact.out : j₁ ≠ 0) (Subtype.ext h)

  obtain ⟨j', hj', hj'fin, hj₁fin', hN3⟩ :=
    ModularCurve.FullLevel.exists_qExpand_mem_chartAlgFin_and_forall_mem_closure_levelAutBar_exists_algEquiv_levelField_of_eq_three
      q hq3 M' hqM' hle k₀ K₁ hK₁ A₁ F₀ hK1 hSTAB hLD hRAT halg j₁ hj₁
  obtain ⟨σ, hσ, hσsymm, hσj', hfin_stab, hB'_stab, hplace⟩ := hN3 τ hτmem
  haveI hj'0 : Fact (j' ≠ 0) := ⟨fun h => by
    have h1 : ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by rw [h]; rfl
    rw [hj'] at h1
    exact (ModularCurve.jq_ne_zero) ((qExpand ℚ q).injective ((coeffEmb (AlgebraicClosure ℚ)).injective (by rw [h1, map_zero, map_zero])))⟩
  obtain ⟨j'', hj'', hsw3, hsw4⟩ :=
    ModularCurve.FullLevel.exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField_of_eq_three
      q hq3 M' hqM' hle k₀ K₁ hK₁ A₁ F₀ hK1 hSTAB hLD hRAT halg j₁ hj₁

  have hjj : j'' = j' := by
    apply Subtype.ext; apply Subtype.ext
    show ((j'' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))
    rw [hj'', hj']
  simp only [hjj] at hsw3 hsw4
  clear hjj hj'' j''

  have SF : ∀ (y : ↥(TwoChartIntegralModel.XFin ↥A₁ _ j₁)) (f : type_of% j₁),
      InStalk ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y) f ↔
        ∃ g h : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁), h ∉ y.asIdeal ∧ f * (h : type_of% j₁) = (g : type_of% j₁) :=
    fun y f => TEQVAuxIg.inStalk_iff_fin ↥A₁ _ j₁ y f
  have MF : ∀ (y : ↥(TwoChartIntegralModel.XFin ↥A₁ _ j₁)) (f : type_of% j₁),
      InMax ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y) f ↔
        ∃ g h : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : type_of% j₁) = (g : type_of% j₁) :=
    fun y f => TEQVAuxIg.inMax_iff_fin ↥A₁ _ j₁ y f
  have SI : ∀ (y : ↥(TwoChartIntegralModel.XInf ↥A₁ _ j₁)) (f : type_of% j₁),
      InStalk ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y) f ↔
        ∃ g h : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁), h ∉ y.asIdeal ∧ f * (h : type_of% j₁) = (g : type_of% j₁) :=
    fun y f => TEQVAuxIg.inStalk_iff_inf' ↥A₁ _ j₁ y f
  have MI : ∀ (y : ↥(TwoChartIntegralModel.XInf ↥A₁ _ j₁)) (f : type_of% j₁),
      InMax ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y) f ↔
        ∃ g h : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : type_of% j₁) = (g : type_of% j₁) :=
    fun y f => TEQVAuxIg.inMax_iff_inf' ↥A₁ _ j₁ y f

  obtain ⟨hj₁invW, hj₁W, -, -, hconstW⟩ :=
    TH1Wanted2.inv_mem_and_const_mem_of_gaussPresentation q hq3 M' hqM' A hle k₀ K₁ hK₁ A₁ hA₁ F₀ hK1 hLD hRAT halg j₁ hj₁ j' hj'
      (OIg (lineInfty q)) hIg_inf
  have hFinW : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁), ((b : type_of% j₁) : ↥(fieldBar q M')) ∈ R.integers := fun b => by
    rw [hR]; exact TH1Wanted2.chartAlg_singleton_le_valuationSubring (algebraMap (type_of% j₁) ↥(fieldBar q M')) (OIg (lineInfty q)) j₁ hj₁W hconstW b.1 b.2
  have hInfW : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁), ((b : type_of% j₁) : ↥(fieldBar q M')) ∈ R.integers := fun b => by
    rw [hR]; exact TH1Wanted2.chartAlg_singleton_le_valuationSubring (algebraMap (type_of% j₁) ↥(fieldBar q M')) (OIg (lineInfty q)) j₁⁻¹ hj₁invW hconstW b.1 b.2
  have hWsymm : ∀ f : ↥(fieldBar q M'), τ.symm f ∈ R.integers ↔ f ∈ R.integers := fun f => by
    rw [← hτ (τ.symm f), AlgEquiv.apply_symm_apply]
  have hNUsymm : ∀ f : ↥(fieldBar q M'), f ∈ R.integers.nonunits → τ.symm f ∈ R.integers.nonunits := by
    intro f hf
    rw [ValuationSubring.mem_nonunits_iff_or] at hf ⊢
    rcases hf with hf | hf
    · exact Or.inl (by rw [hf, map_zero])
    · exact Or.inr (by rw [← map_inv₀, hWsymm]; exact hf)
  have hσsymmF : ∀ f, (↑(σ.symm f) : ↥(fieldBar q M')) = τ.symm (f : ↥(fieldBar q M')) := hσsymm

  have hmulNU : ∀ a b : ↥(fieldBar q M'), a ∈ R.integers.nonunits → b ∈ R.integers → a * b ∈ R.integers.nonunits := by
    intro a b ha hb
    rw [ValuationSubring.mem_nonunits_iff] at ha ⊢
    rw [map_mul]
    calc R.integers.valuation a * R.integers.valuation b ≤ R.integers.valuation a * 1 :=
          mul_le_mul_right ((R.integers.valuation_le_one_iff _).2 hb) _
      _ < 1 := by rw [mul_one]; exact ha

  obtain ⟨Φf, hΦfbij, hΦford, hΦfmem, hΦfst, hΦfmx⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_bijective_primes_chartAlgFin_localization_iff_of_forall_mem_iff j₁ σ hfin_stab
  have hint1 : IsIntegral ↥(Algebra.adjoin ↥A₁ ({j₁} : Set _)) j' := hj'fin
  have hint2 : IsIntegral ↥(Algebra.adjoin ↥A₁ ({j'} : Set _)) j₁ := hj₁fin'
  obtain ⟨Φc, hΦcbij, hΦcord, hΦcst, hΦcmx⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_bijective_primes_chartAlgInf_localization_iff_of_algEquiv_apply_eq j₁ j' hint1 hint2 hsw3 hsw4 σ hσj'
  have hsurj : ∀ z : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ _ j₁), ∃ z₀ : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ _ j₁),
      ∀ f, InStalk z f ↔ InStalk z₀ (σ.symm f) := by
    intro z
    by_cases hz : z ∈ Set.range (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base
    · obtain ⟨w, rfl⟩ := hz
      obtain ⟨w₀, hw₀⟩ := hΦfbij.2 ⟨w.asIdeal, w.isPrime⟩
      obtain ⟨v, hvI⟩ : ∃ v : ↥(TwoChartIntegralModel.XFin ↥A₁ _ j₁), v.asIdeal = w₀.1 :=
        ⟨(⟨w₀.1, w₀.2⟩ : PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁)), rfl⟩
      refine ⟨(TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base v, fun f => ?_⟩
      have h1 := hΦfst w₀ f
      rw [hw₀, ← hvI] at h1
      exact (SF w f).trans (h1.trans (SF v (σ.symm f)).symm)
    · obtain ⟨w, rfl⟩ : ∃ w, (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base w = z := by
        rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf ↥A₁ _ j₁ z with h | h
        · exact absurd h hz
        · exact h
      have hwj : TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ∈ w.asIdeal := TEQVAuxIg.jInvChartInf_mem_of_not_mem_range ↥A₁ _ j₁ w hz
      obtain ⟨w₀, hw₀⟩ := hΦcbij.2 ⟨w.asIdeal, w.isPrime, hwj⟩
      obtain ⟨v, hvI⟩ : ∃ v : ↥(TwoChartIntegralModel.XInf ↥A₁ _ j₁), v.asIdeal = w₀.1 :=
        ⟨(⟨w₀.1, w₀.2.1⟩ : PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)), rfl⟩
      refine ⟨(TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base v, fun f => ?_⟩
      have h1 := hΦcst w₀ f
      rw [hw₀, ← hvI] at h1
      exact (SI w f).trans (h1.trans (SI v (σ.symm f)).symm)
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
  by_cases hxfin : x ∈ Set.range (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base
  · obtain ⟨y, hy⟩ := hxfin
    subst hy
    obtain ⟨y', hy'I⟩ : ∃ y' : ↥(TwoChartIntegralModel.XFin ↥A₁ _ j₁), y'.asIdeal = (Φf ⟨y.asIdeal, y.isPrime⟩).1 :=
      ⟨(⟨(Φf ⟨y.asIdeal, y.isPrime⟩).1, (Φf ⟨y.asIdeal, y.isPrime⟩).2⟩ : PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁)), rfl⟩
    have hSt : ∀ f, InStalk ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y') (σ f) ↔ InStalk ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y) f := by
      intro f
      have h1 := hΦfst ⟨y.asIdeal, y.isPrime⟩ (σ f)
      rw [AlgEquiv.symm_apply_apply, ← hy'I] at h1
      exact (SF y' (σ f)).trans (h1.trans (SF y f).symm)
    have hMx : ∀ f, InMax ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y') (σ f) ↔ InMax ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y) f := by
      intro f
      have h1 := hΦfmx ⟨y.asIdeal, y.isPrime⟩ (σ f)
      rw [AlgEquiv.symm_apply_apply, ← hy'I] at h1
      exact (MF y' (σ f)).trans (h1.trans (MF y f).symm)
    have hSt' : ∀ f, InStalk ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y') f ↔ InStalk ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y) (σ.symm f) := by
      intro f
      have h1 := hΦfst ⟨y.asIdeal, y.isPrime⟩ f
      rw [← hy'I] at h1
      exact (SF y' f).trans (h1.trans (SF y (σ.symm f)).symm)
    have hMx' : ∀ f, InMax ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y') f ↔ InMax ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y) (σ.symm f) := by
      intro f
      have h1 := hΦfmx ⟨y.asIdeal, y.isPrime⟩ f
      rw [← hy'I] at h1
      exact (MF y' f).trans (h1.trans (MF y (σ.symm f)).symm)

    have hBr : ∀ f, InStalk ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y) f → (f : ↥(fieldBar q M')) ∈ R.integers.nonunits →
        InMax ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y) f := by
      intro f hf hnu
      obtain ⟨g, h, hh, hfg⟩ := (SF y f).1 hf
      have hgnu : ((g.1 : type_of% j₁) : ↥(fieldBar q M')) ∈ R.integers.nonunits := by
        have : ((g.1 : type_of% j₁) : ↥(fieldBar q M')) = (f : ↥(fieldBar q M')) * ((h.1 : type_of% j₁) : ↥(fieldBar q M')) := by rw [← hfg]; rfl
        rw [this]; exact hmulNU _ _ hnu (hFinW h)
      have hgy : g ∈ y.asIdeal := hx3 y rfl g hgnu
      exact (MF y f).2 ⟨g, h, hh, hgy, hfg⟩
    have hBr' : ∀ f, InStalk ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y') f → (f : ↥(fieldBar q M')) ∈ R.integers.nonunits →
        InMax ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y') f := by
      intro f hf hnu
      refine (hMx' f).2 (hBr _ ((hSt' f).1 hf) ?_)
      rw [hσsymmF]; exact hNUsymm _ hnu
    refine ⟨(TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y', ?_, ?_, ?_⟩
    ·
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      ·
        rw [TEQVAuxIg.toBase_eq_closedPoint_iff ↥A₁ _ j₁] at hx1 ⊢
        intro r hr
        have := hx1 r hr
        have e : σ.symm (algebraMap ↥A₁ _ r) = algebraMap ↥A₁ _ r := σ.symm.commutes r
        exact (hMx' _).2 (by rw [e]; exact this)
      ·
        exact TEQVAuxIg.closed_transport ↥A₁ _ j₁ σ.toEquiv _ _ hx2 hSt' hsurj
      ·
        intro y₂ hy₂ b hb
        have hst : InStalk ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y₂) (b : type_of% j₁) := (SF y₂ b).2 ⟨b, 1, (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top, by simp⟩
        rw [hy₂] at hst
        have hm := hBr' _ hst hb
        rw [← hy₂] at hm
        obtain ⟨g, h, hh, hg, e⟩ := (MF y₂ b).1 hm
        have e' : b * h = g := Subtype.ext e
        exact (y₂.isPrime.mem_or_mem (by rw [e']; exact hg)).resolve_right hh
      ·
        intro y₂ hy₂ b hb
        have hst : InStalk ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y₂) (b : type_of% j₁) := (SI y₂ b).2 ⟨b, 1, (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top, by simp⟩
        rw [hy₂] at hst
        have hm := hBr' _ hst hb
        rw [← hy₂] at hm
        obtain ⟨g, h, hh, hg, e⟩ := (MI y₂ b).1 hm
        have e' : b * h = g := Subtype.ext e
        exact (y₂.isPrime.mem_or_mem (by rw [e']; exact hg)).resolve_right hh
      ·
        intro y₂ hy₂ Ω _ _ _ _ φ' hker hss
        have hyy : y₂ = y' := (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).isOpenEmbedding.injective hy₂
        subst hyy

        let σB : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁) →+* ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁) :=
          { toFun := fun b => ⟨σ b.1, (hfin_stab b.1).1 b.2⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun a b => Subtype.ext (by simp)
            map_zero' := Subtype.ext (by simp)
            map_add' := fun a b => Subtype.ext (by simp) }
        have hσB : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁), (σB b).1 = σ b.1 := fun b => rfl
        have hkerφ : RingHom.ker (φ'.comp σB) = y.asIdeal := by
          ext b
          rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hker, hy'I,
            hΦfmem ⟨y.asIdeal, y.isPrime⟩ (σB b)]
          have e : ∀ hb' : σ.symm (σB b).1 ∈ TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁,
              (⟨σ.symm (σB b).1, hb'⟩ : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁)) = b :=
            fun hb' => Subtype.ext (σ.symm_apply_apply b.1)
          rw [e]
        have h5 := hx5 y rfl Ω (φ'.comp σB) hkerφ
        have hιinj : Function.Injective ((algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ))).comp (algebraMap (type_of% j₁) ↥(fieldBar q M')) :
            (type_of% j₁) →+* LaurentSeries (AlgebraicClosure ℚ)) := by
          intro a b h; exact Subtype.ext (Subtype.ext h)
        have K1 := TEQVAuxIg.mem_ssJSet_iff_of_kronecker q
          ((algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ))).comp (algebraMap (type_of% j₁) ↥(fieldBar q M'))) hιinj j₁ j'
          (by show ((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = _; rw [hj₁]; rfl)
          (by show ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = _; rw [hj'])
          hj'fin Ω φ'
        have K2 := TEQVAuxIg.mem_ssJSet_iff_of_kronecker q
          ((algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ))).comp (algebraMap (type_of% j₁) ↥(fieldBar q M'))) hιinj j₁ j'
          (by show ((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = _; rw [hj₁]; rfl)
          (by show ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = _; rw [hj'])
          hj'fin Ω (φ'.comp σB)
        have e : (φ'.comp σB) ⟨j', hj'fin⟩ = φ' ⟨j', hj'fin⟩ := by
          rw [RingHom.comp_apply]
          congr 1
          exact Subtype.ext hσj'
        rw [e] at K2
        exact h5 (K2.2 (K1.1 hss))
    ·
      intro Q hQ
      exact TEQVAuxIg.reads_transport R τ hτ (fun f => ((f : type_of% j₁) : ↥(fieldBar q M'))) σ.toEquiv hσ
        (InStalk ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y)) (InStalk ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y'))
        (InMax ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y)) (InMax ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y')) hSt hMx Q hQ
    ·
      intro P
      exact TEQVAuxT0.centred_transport A τ (fun f => ((f : type_of% j₁) : ↥(fieldBar q M'))) σ.toEquiv hσ
        (InStalk ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y)) (InStalk ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y'))
        (InMax ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y)) (InMax ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y')) hSt hMx P
  · obtain ⟨y, hy⟩ : ∃ y, (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y = x := by
      rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf ↥A₁ _ j₁ x with h | h
      · exact absurd h hxfin
      · exact h
    subst hy
    have hjinv : TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ∈ y.asIdeal :=
      TEQVAuxIg.jInvChartInf_mem_of_not_mem_range ↥A₁ _ j₁ y hxfin
    obtain ⟨y', hy'I⟩ : ∃ y' : ↥(TwoChartIntegralModel.XInf ↥A₁ _ j₁), y'.asIdeal = (Φc ⟨y.asIdeal, y.isPrime, hjinv⟩).1 :=
      ⟨(⟨(Φc ⟨y.asIdeal, y.isPrime, hjinv⟩).1, (Φc ⟨y.asIdeal, y.isPrime, hjinv⟩).2.1⟩ : PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)), rfl⟩
    have hSt : ∀ f, InStalk ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y') (σ f) ↔ InStalk ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y) f := by
      intro f
      have h1 := hΦcst ⟨y.asIdeal, y.isPrime, hjinv⟩ (σ f)
      rw [AlgEquiv.symm_apply_apply, ← hy'I] at h1
      exact (SI y' (σ f)).trans (h1.trans (SI y f).symm)
    have hMx : ∀ f, InMax ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y') (σ f) ↔ InMax ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y) f := by
      intro f
      have h1 := hΦcmx ⟨y.asIdeal, y.isPrime, hjinv⟩ (σ f)
      rw [AlgEquiv.symm_apply_apply, ← hy'I] at h1
      exact (MI y' (σ f)).trans (h1.trans (MI y f).symm)
    have hSt' : ∀ f, InStalk ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y') f ↔ InStalk ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y) (σ.symm f) := by
      intro f
      have h1 := hΦcst ⟨y.asIdeal, y.isPrime, hjinv⟩ f
      rw [← hy'I] at h1
      exact (SI y' f).trans (h1.trans (SI y (σ.symm f)).symm)
    have hMx' : ∀ f, InMax ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y') f ↔ InMax ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y) (σ.symm f) := by
      intro f
      have h1 := hΦcmx ⟨y.asIdeal, y.isPrime, hjinv⟩ f
      rw [← hy'I] at h1
      exact (MI y' f).trans (h1.trans (MI y (σ.symm f)).symm)

    have hBr : ∀ f, InStalk ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y) f → (f : ↥(fieldBar q M')) ∈ R.integers.nonunits →
        InMax ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y) f := by
      intro f hf hnu
      obtain ⟨g, h, hh, hfg⟩ := (SI y f).1 hf
      have hgnu : ((g.1 : type_of% j₁) : ↥(fieldBar q M')) ∈ R.integers.nonunits := by
        have : ((g.1 : type_of% j₁) : ↥(fieldBar q M')) = (f : ↥(fieldBar q M')) * ((h.1 : type_of% j₁) : ↥(fieldBar q M')) := by rw [← hfg]; rfl
        rw [this]; exact hmulNU _ _ hnu (hInfW h)
      have hgy : g ∈ y.asIdeal := hx4 y rfl g hgnu
      exact (MI y f).2 ⟨g, h, hh, hgy, hfg⟩
    have hBr' : ∀ f, InStalk ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y') f → (f : ↥(fieldBar q M')) ∈ R.integers.nonunits →
        InMax ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y') f := by
      intro f hf hnu
      refine (hMx' f).2 (hBr _ ((hSt' f).1 hf) ?_)
      rw [hσsymmF]; exact hNUsymm _ hnu
    refine ⟨(TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y', ?_, ?_, ?_⟩
    ·
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      ·
        rw [TEQVAuxIg.toBase_eq_closedPoint_iff ↥A₁ _ j₁] at hx1 ⊢
        intro r hr
        have := hx1 r hr
        have e : σ.symm (algebraMap ↥A₁ _ r) = algebraMap ↥A₁ _ r := σ.symm.commutes r
        exact (hMx' _).2 (by rw [e]; exact this)
      ·
        exact TEQVAuxIg.closed_transport ↥A₁ _ j₁ σ.toEquiv _ _ hx2 hSt' hsurj
      ·
        intro y₂ hy₂ b hb
        have hst : InStalk ((TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y₂) (b : type_of% j₁) := (SF y₂ b).2 ⟨b, 1, (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top, by simp⟩
        rw [hy₂] at hst
        have hm := hBr' _ hst hb
        rw [← hy₂] at hm
        obtain ⟨g, h, hh, hg, e⟩ := (MF y₂ b).1 hm
        have e' : b * h = g := Subtype.ext e
        exact (y₂.isPrime.mem_or_mem (by rw [e']; exact hg)).resolve_right hh
      ·
        intro y₂ hy₂ b hb
        have hst : InStalk ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y₂) (b : type_of% j₁) := (SI y₂ b).2 ⟨b, 1, (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top, by simp⟩
        rw [hy₂] at hst
        have hm := hBr' _ hst hb
        rw [← hy₂] at hm
        obtain ⟨g, h, hh, hg, e⟩ := (MI y₂ b).1 hm
        have e' : b * h = g := Subtype.ext e
        exact (y₂.isPrime.mem_or_mem (by rw [e']; exact hg)).resolve_right hh
      ·
        intro y₂ hy₂
        exfalso
        obtain ⟨z, hzy, hzy'⟩ := L2Aux.exists_comap_eq_of_ιFin_eq_ιInf ↥A₁ _ j₁ y₂ y' hy₂
        have hu : IsUnit ((TwoChartIntegralModel.inclInf ↥A₁ _ j₁) (TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁)) := TwoChartIntegralModel.isUnit_inclInf_jInvChartInf ↥A₁ _ j₁
        have hmem : TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ∈ y'.asIdeal := by rw [hy'I]; exact (Φc ⟨y.asIdeal, y.isPrime, hjinv⟩).2.2
        rw [hzy', Ideal.mem_comap] at hmem
        exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
    ·
      intro Q hQ
      exact TEQVAuxIg.reads_transport R τ hτ (fun f => ((f : type_of% j₁) : ↥(fieldBar q M'))) σ.toEquiv hσ
        (InStalk ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y)) (InStalk ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y'))
        (InMax ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y)) (InMax ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y')) hSt hMx Q hQ
    ·
      intro P
      exact TEQVAuxT0.centred_transport A τ (fun f => ((f : type_of% j₁) : ↥(fieldBar q M'))) σ.toEquiv hσ
        (InStalk ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y)) (InStalk ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y'))
        (InMax ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y)) (InMax ((TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y')) hSt hMx P

end S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three (solution)
