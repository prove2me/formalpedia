-- Prove2me | solution 1 for ModularCurve.FullLevel.not_mem_igusaNodes_of_reads_of_goodPt_twoChartIntegralModel_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/595ddeb6-9d6d-52cb-a205-59a7182cb933

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_not_mem_igusaNodes_of_reads_of_goodPt_twoChartIntegralModel_of_eq_two
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

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

theorem jInvChartInf_mem_of_not_mem_range (y' : XInf R F j)
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

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 0 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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

    ∀ (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))),
      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) →

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

    let OffBranch : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      ∀ ℓ : CuspidalType.ProjLine q, ℓ ≠ lineInfty q →
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal) ∧
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal)

    (∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x → ∀ Q, Reads x Q → Q ∉ NIg) := by
  classical
  intro F₀ hK1 hSTAB hLD hRAT instA₁ hA₁alg j₁ hj₁ instj₁ NIg hN InStalk InMax Centred GoodPt Reads OffBranch x hx Q hxQ hQN
  obtain ⟨jmap, hcompat, hNIg⟩ := hN
  obtain ⟨s, hs⟩ := (hNIg Q).1 hQN
  obtain ⟨hsrat, ⟨hjs, -⟩, hss⟩ := (mem_ssPlaces_iff q M' (ResidueField ↥A)).1 ((hW s).1 s.2)
  haveI hcharP : CharP (ResidueField ↥A) q :=
    ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out : q.Prime) hA
  have hjt0 : (j₁ : ↥(fieldBar q M')) ≠ 0 := fun h => (Fact.out : j₁ ≠ 0) (Subtype.ext h)

  haveI : (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')).FiniteIndex := L2Aux.GammaH_finiteIndex _ _
  have hcurve : AlgebraicCurve.IsCurveOver (ResidueField ↥A) ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A)
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) (translation_mem_GammaH _ _)
  have hQrat : Q.IsRational := by
    haveI := hcurve
    haveI : Module.Finite (ResidueField ↥A) Q.ResidueField := AlgebraicCurve.IsCurveOver.finiteResidue Q
    haveI : Algebra.IsIntegral (ResidueField ↥A) Q.ResidueField := Algebra.IsIntegral.of_finite _ _
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := (ResidueField ↥A)) (K := Q.ResidueField)).2

  have hjconst : ∀ c : (ResidueField ↥A), jmap (algebraMap (ResidueField ↥A) _ c) = algebraMap (ResidueField ↥A) _ c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := ↥A) c
    have hfa : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ) ∈ R₀.integers :=
      (R₀.algebraMap_mem_iff _).2 a.2
    obtain ⟨hC, hC'⟩ := hcompat _ hfa
    have e0 : (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ), hfa⟩ : ↥R₀.integers) =
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ), (R₀.algebraMap_mem_iff _).mpr a.2⟩ := rfl
    rw [e0, R₀.residue_algebraMap a] at hC'
    rw [← hC']
    have e1 : (⟨IntermediateField.inclusion hle (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ)), hC⟩ : ↥R.integers) =
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ), (R.algebraMap_mem_iff _).mpr a.2⟩ :=
      Subtype.ext ((IntermediateField.inclusion hle).commutes (a : AlgebraicClosure ℚ))
    rw [e1, R.residue_algebraMap a]

  have hjq : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq := by
    show (jqModC ↥A).map A.subtype = (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ))
    rw [map_jqModC, map_jqModC]
  have hjmem : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [hjq]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  obtain ⟨hjR₀, hjres⟩ := hR₀ (jqModC ↥A) hjmem
  have heltEq : (⟨coeffMap A.subtype (jqModC ↥A), hjmem⟩ : ↥(modularFunctionFieldBar M')) =
      ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :=
    Subtype.ext hjq
  have hR₀res : R₀.residue ⟨_, hjR₀⟩ = jGeomGen (ResidueField ↥A) M' := by
    apply Subtype.ext
    rw [coe_jGeomGen, hjres]
    show (jqModC ↥A).map _ = _
    exact map_jqModC _
  obtain ⟨hjC, hjcompat⟩ := hcompat _ hjR₀
  rw [hR₀res] at hjcompat
  have hj₁R : (j₁ : ↥(fieldBar q M')) ∈ R.integers := by
    rw [hj₁, ← heltEq]; exact hjC
  have hRj₁ : R.residue ⟨(j₁ : ↥(fieldBar q M')), hj₁R⟩ = jmap (jGeomGen (ResidueField ↥A) M') := by
    rw [← hjcompat]
    congr 1
    apply Subtype.ext
    show (j₁ : ↥(fieldBar q M')) = _
    rw [hj₁, ← heltEq]

  have hjQ : jmap (jGeomGen (ResidueField ↥A) M') ∈ Q.toValuationSubring := (hs _).1 hjs
  have hval : Q.evalAt (jmap (jGeomGen (ResidueField ↥A) M')) =
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField ↥A) M') := by
    apply L2Aux.evalAt_eq_of_sub_algebraMap_mem_nonunits Q hQrat hjQ
    rw [← hjconst, ← map_sub]
    exact (L2Aux.map_mem_nonunits_iff jmap _ Q hs _).1
      (L2Aux.sub_algebraMap_evalAt_mem_nonunits _ hsrat hjs)

  have oneF : ∀ y₂ : ↥(TwoChartIntegralModel.XFin ↥A₁ _ j₁), (1 : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁)) ∉ y₂.asIdeal :=
    fun y₂ => (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top
  have oneI : ∀ y₂ : ↥(TwoChartIntegralModel.XInf ↥A₁ _ j₁), (1 : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)) ∉ y₂.asIdeal :=
    fun y₂ => (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top
  by_cases hfin : x ∈ Set.range (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base
  ·
    obtain ⟨y, hy⟩ := hfin
    have hov : ∀ y', (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y' = x →
        ∃ z : TwoChartIntegralModel.XMid ↥A₁ _ j₁,
          y.asIdeal = Ideal.comap (TwoChartIntegralModel.inclFin ↥A₁ _ j₁).toRingHom z.asIdeal ∧
          y'.asIdeal = Ideal.comap (TwoChartIntegralModel.inclInf ↥A₁ _ j₁).toRingHom z.asIdeal :=
      fun y' hy' => L2Aux.exists_comap_eq_of_ιFin_eq_ιInf ↥A₁ _ j₁ y y' (hy.trans hy'.symm)
    have hStalk : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁), InStalk x b.1 := by
      intro b
      refine ⟨fun y₂ _ => ⟨b, 1, oneF y₂, by simp⟩, fun y' hy' => ?_⟩
      obtain ⟨z, hzy, hzy'⟩ := hov y' hy'
      obtain ⟨n, g, hbg, hnot, -⟩ := L2Aux.exists_inf_witness ↥A₁ _ j₁ z b
      exact ⟨g, TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ^ n, by rwa [hzy'], hbg⟩
    have hMax : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁), InMax x b.1 ↔ b ∈ y.asIdeal := by
      intro b
      constructor
      · rintro ⟨hF, -⟩
        obtain ⟨g, h, hh, hg, hbh⟩ := hF y hy
        have hbh' : b * h = g := Subtype.ext hbh
        have hmem : b * h ∈ y.asIdeal := by rw [hbh']; exact hg
        exact (y.isPrime.mem_or_mem hmem).resolve_right hh
      · intro hb
        refine ⟨fun y₂ hy₂ => ?_, fun y' hy' => ?_⟩
        · have hyy : y₂ = y := (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).isOpenEmbedding.injective (hy₂.trans hy.symm)
          subst hyy
          exact ⟨b, 1, oneF y₂, hb, by simp⟩
        · obtain ⟨z, hzy, hzy'⟩ := hov y' hy'
          obtain ⟨n, g, hbg, hnot, hiff⟩ := L2Aux.exists_inf_witness ↥A₁ _ j₁ z b
          refine ⟨g, TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ^ n, by rwa [hzy'], ?_, hbg⟩
          rw [hzy']
          exact hiff.1 (by rw [← hzy]; exact hb)
    have hC := fun b : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁) => hxQ b.1 (hStalk b)

    let toF : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁) →+* ↥(fieldBar q M') :=
      (algebraMap _ ↥(fieldBar q M')).comp (TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁).val.toRingHom
    let e : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁) →+* ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M')) :=
      R.residue.comp (toF.codRestrict R.integers (fun b => (hC b).fst))
    have he : ∀ b, e b = R.residue ⟨(b.1 : ↥(fieldBar q M')), (hC b).fst⟩ := fun b => rfl
    have heQ : ∀ b, e b ∈ Q.toValuationSubring := fun b => by rw [he]; exact (hC b).snd.1
    let φ : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁) →+* (ResidueField ↥A) :=
      (L2Aux.evalHom Q hQrat).comp (e.codRestrict Q.toValuationSubring heQ)
    have hφ : ∀ b, φ b = Q.evalAt (e b) := fun b => L2Aux.evalHom_apply Q hQrat _
    have hker : RingHom.ker φ = y.asIdeal := by
      ext b
      rw [RingHom.mem_ker, hφ, L2Aux.evalAt_eq_zero_iff_mem_nonunits Q hQrat (heQ b), he, ← hMax b]
      exact (hC b).snd.2
    have hgood := hx.2.2.2.2 y hy (ResidueField ↥A) φ hker
    apply hgood
    have hφj : φ (TwoChartIntegralModel.jChartFin ↥A₁ _ j₁) =
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField ↥A) M') := by
      rw [hφ, he, ← hval, ← hRj₁]
      congr 2
    rw [hφj]
    exact hss
  ·
    rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf ↥A₁ _ j₁ x with hfin' | ⟨y', hy'⟩
    · exact absurd hfin' hfin
    have hjinv : TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ∈ y'.asIdeal :=
      L2Aux.jInvChartInf_mem_of_not_mem_range ↥A₁ _ j₁ y' (by rw [hy']; exact hfin)
    have hcoeI : (j₁⁻¹ : _) * ((1 : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)) : _) =
        ((TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)) : _) := by
      rw [TwoChartIntegralModel.coe_jInvChartInf, OneMemClass.coe_one, mul_one]
    have hS2 : InStalk x j₁⁻¹ :=
      ⟨fun y₂ hy₂ => absurd ⟨y₂, hy₂⟩ hfin, fun y₂ _ => ⟨TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁, 1, oneI y₂, hcoeI⟩⟩
    have hM2 : InMax x j₁⁻¹ := by
      refine ⟨fun y₂ hy₂ => absurd ⟨y₂, hy₂⟩ hfin, fun y₂ hy₂ => ?_⟩
      have hyy : y₂ = y' := (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).isOpenEmbedding.injective (hy₂.trans hy'.symm)
      subst hyy
      exact ⟨TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁, 1, oneI y₂, hjinv, hcoeI⟩
    obtain ⟨hRinv, -, hiff⟩ := hxQ j₁⁻¹ hS2
    have hn : R.residue ⟨((j₁⁻¹ : _) : ↥(fieldBar q M')), hRinv⟩ ∈ Q.toValuationSubring.nonunits := hiff.2 hM2
    have hprod : R.residue ⟨(j₁ : ↥(fieldBar q M')), hj₁R⟩ * R.residue ⟨((j₁⁻¹ : _) : ↥(fieldBar q M')), hRinv⟩ = 1 := by
      rw [← map_mul, ← map_one R.residue]
      congr 1
      apply Subtype.ext
      show (j₁ : ↥(fieldBar q M')) * ((j₁⁻¹ : _) : ↥(fieldBar q M')) = 1
      rw [show ((j₁⁻¹ : _) : ↥(fieldBar q M')) = (j₁ : ↥(fieldBar q M'))⁻¹ from rfl, mul_inv_cancel₀ hjt0]
    have hone : (1 : ↥(xHFunctionFieldC (ResidueField ↥A) (q ^ 2 * M') (levelH q M'))) ∈ Q.toValuationSubring.nonunits := by
      rw [← hprod]
      exact L2Aux.mul_mem_nonunits Q (by rw [hRj₁]; exact hjQ) hn
    rw [ValuationSubring.mem_nonunits_iff, map_one] at hone
    exact lt_irrefl _ hone

end S_ModularCurve_FullLevel_not_mem_igusaNodes_of_reads_of_goodPt_twoChartIntegralModel_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_not_mem_igusaNodes_of_reads_of_goodPt_twoChartIntegralModel_of_eq_two (solution)
