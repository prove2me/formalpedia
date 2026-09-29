-- Prove2me | solution 1 for ModularCurve.FullLevel.not_centred_smul_of_comap_igusaGaussRing_ne_of_offBranch_twoChartIntegralModel_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/5bd761d6-390b-5a07-bc2e-78f095afbf1e

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
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coe_mem_fieldBar_of_mem
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_FullLevel_exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Mathlib
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_not_centred_smul_of_comap_igusaGaussRing_ne_of_offBranch_twoChartIntegralModel_of_eq_two
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

namespace TH1Transport

open Polynomial

section Chart

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]

theorem isIntegral_adjoin_map (τ : K →ₐ[A] K) (t b : K)
    (hb : IsIntegral (Algebra.adjoin A ({t} : Set K)) b) :
    IsIntegral (Algebra.adjoin A ({τ t} : Set K)) (τ b) := by
  have hmap : (Algebra.adjoin A ({t} : Set K)).map τ = Algebra.adjoin A {τ t} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
  let φ : Algebra.adjoin A ({t} : Set K) →+* Algebra.adjoin A ({τ t} : Set K) :=
    { toFun := fun s => ⟨τ s, by rw [← hmap]; exact Subalgebra.mem_map.mpr ⟨s, s.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  exact hb.map_of_comp_eq φ τ.toRingHom (by ext s; rfl)

theorem isIntegral_trans_subalgebra (S : Subalgebra A K) (b : K) (hb : IsIntegral (integralClosure S K) b) :
    IsIntegral S b := by
  haveI : IsScalarTower S (integralClosure S K) K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact isIntegral_trans b hb

theorem isIntegral_adjoin_of_isIntegral_adjoin {t t' b : K}
    (ht' : IsIntegral (Algebra.adjoin A ({t} : Set K)) t')
    (hb : IsIntegral (Algebra.adjoin A ({t'} : Set K)) b) :
    IsIntegral (Algebra.adjoin A ({t} : Set K)) b := by
  exact isIntegral_trans_subalgebra (Algebra.adjoin A ({t} : Set K)) b
    (by
      have hle : Algebra.adjoin A ({t'} : Set K) ≤
          (integralClosure (Algebra.adjoin A ({t} : Set K)) K).restrictScalars A := by
        rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
        exact ht'
      have hle' : (Algebra.adjoin A ({t'} : Set K)).toSubring ≤
          (integralClosure (Algebra.adjoin A ({t} : Set K)) K).toSubring := fun x hx => hle hx
      exact hb.map_of_comp_eq (Subring.inclusion hle') (RingHom.id K) (by ext; rfl))

theorem chartAlg_singleton_eq_of_isIntegral {t t' : K}
    (h1 : IsIntegral (Algebra.adjoin A ({t} : Set K)) t') (h2 : IsIntegral (Algebra.adjoin A ({t'} : Set K)) t) :
    AlgebraicCurve.TwoChartIntegralModel.chartAlg A K {t} = AlgebraicCurve.TwoChartIntegralModel.chartAlg A K {t'} := by
  ext b
  rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff, AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff]
  exact ⟨isIntegral_adjoin_of_isIntegral_adjoin h2, isIntegral_adjoin_of_isIntegral_adjoin h1⟩

end Chart

section ModEq

variable {L : Type} [Field L] [CharZero L]

theorem exists_monic_eval₂_coeffEmb (p : ℕ) [Fact p.Prime] [NeZero p] :
    ∃ Φ : Polynomial (Polynomial ℤ), Φ.Monic ∧
      Φ.eval₂ (aeval (ModularCurve.coeffEmb L ModularCurve.jq)).toRingHom
        (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) = 0 ∧
      Φ.eval₂ (aeval (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))).toRingHom
        (ModularCurve.coeffEmb L ModularCurve.jq) = 0 := by
  obtain ⟨data, hsymm⟩ := ModularCurve.exists_modularPolynomialData_evalSymm p
  have h0 : data.Φ.eval₂ (aeval ModularCurve.jq).toRingHom (ModularCurve.qExpand ℚ p ModularCurve.jq) = 0 := by
    have := data.eval_eq_zero
    rwa [ModularCurve.evalAtJ_def] at this
  have h1 : data.Φ.eval₂ (aeval (ModularCurve.qExpand ℚ p ModularCurve.jq)).toRingHom ModularCurve.jq = 0 := by
    rw [← hsymm]; exact h0
  have key : ∀ x y : LaurentSeries ℚ,
      (ModularCurve.coeffEmb L) (data.Φ.eval₂ (aeval x).toRingHom y)
        = data.Φ.eval₂ (aeval (ModularCurve.coeffEmb L x)).toRingHom (ModularCurve.coeffEmb L y) := by
    intro x y
    rw [hom_eval₂]
    congr 1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp
    · simp
  refine ⟨data.Φ, data.monic, ?_, ?_⟩
  · rw [← key, h0, map_zero]
  · rw [← key, h1, map_zero]

end ModEq

section Generic

variable {A T S : Type} [CommRing A] [Field T] [CommRing S] [Algebra A T]

theorem isIntegral_adjoin_of_eval₂_hom (ι : T →+* S) (hι : Function.Injective ι) (a b : T)
    (Φ : Polynomial (Polynomial ℤ)) (hm : Φ.Monic)
    (h : Φ.eval₂ (aeval (ι a)).toRingHom (ι b) = 0) :
    IsIntegral (Algebra.adjoin A ({a} : Set T)) b := by
  let a' : Algebra.adjoin A ({a} : Set T) := ⟨a, Algebra.self_mem_adjoin_singleton A a⟩
  let θ : Polynomial ℤ →+* Algebra.adjoin A ({a} : Set T) := (aeval a').toRingHom
  refine ⟨Φ.map θ, hm.map θ, ?_⟩
  rw [eval₂_map]
  apply hι
  rw [hom_eval₂, map_zero]
  convert h using 2
  refine Polynomial.ringHom_ext (fun n => by simp) ?_
  simp [θ, a']

theorem mem_chartAlg_singleton_iff_map_mem (σ : T ≃ₐ[A] T) {t t' : T}
    (h1 : IsIntegral (Algebra.adjoin A ({t} : Set T)) t') (h2 : IsIntegral (Algebra.adjoin A ({t'} : Set T)) t)
    (hfix : σ t' = t') (b : T) :
    b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg A T {t} ↔
      σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg A T {t} := by
  rw [chartAlg_singleton_eq_of_isIntegral h1 h2, AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff,
    AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff]
  have hfix' : σ.symm t' = t' := by
    conv_lhs => rw [← hfix]
    exact σ.symm_apply_apply t'
  constructor
  · intro hb
    have := isIntegral_adjoin_map (σ : T →ₐ[A] T) t' b hb
    rwa [AlgEquiv.coe_algHom, hfix] at this
  · intro hb
    have := isIntegral_adjoin_map (σ.symm : T →ₐ[A] T) t' (σ b) hb
    rwa [AlgEquiv.coe_algHom, hfix', AlgEquiv.symm_apply_apply] at this

end Generic

section JQ

theorem isIntegral_adjoin_jq_qExpand {A T : Type} [CommRing A] [Field T] [Algebra A T]
    (p : ℕ) [Fact p.Prime] (a b : T)
    (ι : T →+* LaurentSeries (AlgebraicClosure ℚ)) (hι : Function.Injective ι)
    (ha : ι a = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq)
    (hb : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ι b = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ p ModularCurve.jq)) :
    IsIntegral (Algebra.adjoin A ({a} : Set T)) b ∧ IsIntegral (Algebra.adjoin A ({b} : Set T)) a := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨Φ, hm, h1, h2⟩ := exists_monic_eval₂_coeffEmb (L := AlgebraicClosure ℚ) p
  refine ⟨isIntegral_adjoin_of_eval₂_hom ι hι a b Φ hm ?_, isIntegral_adjoin_of_eval₂_hom ι hι b a Φ hm ?_⟩
  · convert h1 using 2 <;> first | rfl | exact Polynomial.ringHom_ext (fun n => by simp) (by simp [ha])
  · convert h2 using 2 <;> first | rfl | exact Polynomial.ringHom_ext (fun n => by simp) (by simp [hb])

end JQ

end TH1Transport

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

end L2Aux

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

namespace TH1AuxIg

section Closure

variable {G : Type*} [Group G]

theorem forall_mem_closure_of_generators (s : Set G) (p : G → Prop)
    (h1 : p 1) (hmul : ∀ x y, p x → p y → p (x * y))
    (hgen : ∀ x ∈ s, p x) (hfin : ∀ x ∈ s, IsOfFinOrder x) :
    ∀ g ∈ Subgroup.closure s, p g := by
  have hpow : ∀ x, p x → ∀ n : ℕ, p (x ^ n) := by
    intro x hx n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hx
  intro g hg
  induction hg using Subgroup.closure_induction'' with
  | mem x hx => exact hgen x hx
  | inv_mem x hx =>
      have h := hfin x hx
      have : x⁻¹ = x ^ (orderOf x - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, tsub_add_cancel_of_le (by exact h.orderOf_pos),
          pow_orderOf_eq_one]
      rw [this]
      exact hpow x (hgen x hx) _
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy

end Closure

section Comap

theorem mem_nonunits_comap_iff
    {F : Type} [Field F] (V : ValuationSubring F) (g : F ≃+* F) (f : F) :
    f ∈ (V.comap g.toRingHom).nonunits ↔ g f ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀, map_eq_zero_iff _ g.injective]

theorem mem_comap_iff'
    {F : Type} [Field F] (V : ValuationSubring F) (g : F ≃+* F) (f : F) :
    f ∈ V.comap g.toRingHom ↔ g f ∈ V :=
  ValuationSubring.mem_comap

end Comap

section W1

theorem closure_comap_igusaRing_perm
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (OIg : CuspidalType.ProjLine q → ValuationSubring ↥(fieldBar q M'))
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))
    (g : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M'))
    (hg : g ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') | ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}) :
    ∃ σ : Equiv.Perm (CuspidalType.ProjLine q), ∀ ℓ, (OIg ℓ).comap g.toAlgHom.toRingHom = OIg (σ ℓ) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨ζ', γ, hγ, rfl⟩ := hx
      exact hIg_perm ζ' γ hγ
  | one => exact ⟨1, fun i => by ext f; rfl⟩
  | mul x y _ _ hx hy =>
      obtain ⟨σ, hσ⟩ := hx
      obtain ⟨ρ, hρ⟩ := hy
      refine ⟨ρ * σ, fun i => ?_⟩
      have : (OIg i).comap (x * y).toAlgHom.toRingHom =
          ((OIg i).comap x.toAlgHom.toRingHom).comap y.toAlgHom.toRingHom := by
        ext f; rfl
      rw [this, hσ, hρ, Equiv.Perm.mul_apply]
  | inv x _ hx =>
      obtain ⟨σ, hσ⟩ := hx
      refine ⟨σ⁻¹, fun i => ?_⟩
      have h := hσ (σ⁻¹ i)
      rw [show σ (σ⁻¹ i) = i from by simp] at h
      have : ((OIg (σ⁻¹ i)).comap x.toAlgHom.toRingHom).comap x⁻¹.toAlgHom.toRingHom = OIg (σ⁻¹ i) := by
        ext f
        show x (x⁻¹ f) ∈ OIg (σ⁻¹ i) ↔ f ∈ OIg (σ⁻¹ i)
        rw [show x (x⁻¹ f) = f from by simp]
      rw [← this, h]

end W1

section LevelAut

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem isOfFinOrder_levelAutBar (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ζ : Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    IsOfFinOrder (levelAutBar q M' ζ γ) := by
  obtain ⟨G, hGfin, hmem, -⟩ := ModularCurve.FullLevel.exists_finite_subgroup_forall_levelAutBar_mem q M' hqM' ζ
  haveI := hGfin
  have h : IsOfFinOrder (⟨levelAutBar q M' ζ γ, hmem γ hγ⟩ : ↥G) := isOfFinOrder_of_finite _
  exact MonoidHom.isOfFinOrder G.subtype h

end LevelAut

section W2

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem exists_qExpand_and_forall_closure_exists_algEquiv_restrict
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) :
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
    ∃ j' : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀),
      ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) ∧
      ∀ g ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') | ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
        ∃ σ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ≃ₐ[↥A₁] ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀),
          (∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), ((σ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) = g (f : ↥(fieldBar q M'))) ∧
          (∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), ((σ.symm f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) = g.symm (f : ↥(fieldBar q M'))) ∧
          σ j' = j' := by
  intro F₀ hK1 hSTAB hLD hRAT instA halg
  haveI : IsScalarTower ↥k₀ (AlgebraicClosure ℚ) ↥(fieldBar q M') := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  have hjq : ∀ (N : ℕ) [NeZero N], coeffEmb (AlgebraicClosure ℚ) jq ∈
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 N)) := by
    intro N _
    refine coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) ?_
    rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact modularFunctionField_le_full N (jq_mem N)
  have hcoe : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) =
      qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq) :=
    ModularCurve.coeffSemilinearAut.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) q jq
  have hj'mem : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) ∈ fieldBar q M' := by
    rw [hcoe]
    exact ModularCurve.FullLevel.qExpand_coe_mem_fieldBar_of_mem q M' hqM' _ (hjq (q * M'))
  let j'F : ↥(fieldBar q M') := ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq), hj'mem⟩
  have hj'T : j'F ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) :=
    (le_sup_right : F₀ ≤ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) (hRAT j'F ⟨qExpand ℚ q jq, rfl⟩)

  have hfix : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → levelAutBar q M' ζ' γ j'F = j'F := fun ζ' γ hγ =>
    ModularCurve.FullLevel.levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0 q M' hqM' ζ' γ hγ
      (coeffEmb (AlgebraicClosure ℚ) jq) (hjq M') j'F hcoe

  have hstab : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∀ f : ↥(fieldBar q M'), f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → levelAutBar q M' ζ' γ f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) := by
    intro ζ' γ hγ
    let τ' : ↥(fieldBar q M') →ₐ[↥k₀] ↥(fieldBar q M') := (levelAutBar q M' ζ' γ).toAlgHom.restrictScalars ↥k₀
    suffices h : (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ≤ ((IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).comap τ' by
      intro f hf
      exact h hf
    refine sup_le ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      rintro f ⟨x, hx, rfl⟩
      show τ' (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x) ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)
      rw [show τ' (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x
        from (levelAutBar q M' ζ' γ).commutes x]
      exact le_sup_left (b := F₀) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
    · intro f hf
      show levelAutBar q M' ζ' γ f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)
      exact le_sup_right (a := IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ)))) (hSTAB ζ' γ hγ f hf)

  have hP : ∀ g ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') | ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
      (∀ f : ↥(fieldBar q M'), f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → g f ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ∧ g j'F = j'F := by
    refine forall_mem_closure_of_generators _ _ ⟨fun f hf => hf, rfl⟩ ?_ ?_ ?_
    · intro x y hx hy
      exact ⟨fun f hf => by rw [AlgEquiv.mul_apply]; exact hx.1 _ (hy.1 f hf), by rw [AlgEquiv.mul_apply, hy.2, hx.2]⟩
    · rintro τ ⟨ζ', γ, hγ, rfl⟩
      exact ⟨hstab ζ' γ hγ, hfix ζ' γ hγ⟩
    · rintro τ ⟨ζ', γ, hγ, rfl⟩
      exact isOfFinOrder_levelAutBar q M' hqM' ζ' γ hγ
  refine ⟨⟨j'F, hj'T⟩, rfl, fun g hg => ?_⟩
  obtain ⟨hg1, hg2⟩ := hP g hg
  obtain ⟨hi1, hi2⟩ := hP g⁻¹ (Subgroup.inv_mem _ hg)
  refine ⟨{ toFun := fun f => ⟨g (f : ↥(fieldBar q M')), hg1 _ f.2⟩
            invFun := fun f => ⟨g⁻¹ (f : ↥(fieldBar q M')), hi1 _ f.2⟩
            left_inv := fun f => Subtype.ext (by simp)
            right_inv := fun f => Subtype.ext (by simp)
            map_mul' := fun a b => Subtype.ext (by simp)
            map_add' := fun a b => Subtype.ext (by simp)
            commutes' := fun a => Subtype.ext (by
              dsimp only
              rw [halg]
              exact g.commutes _) }, fun f => rfl, fun f => ?_, Subtype.ext hg2⟩
  show g⁻¹ (f : ↥(fieldBar q M')) = g.symm (f : ↥(fieldBar q M'))
  rfl

end W2

section W4

open AlgebraicCurve.TwoChartIntegralModel in

theorem isIntegral_adjoin_map' {A : Type*} [CommRing A] {K K' : Type*} [Field K] [Field K'] [Algebra A K] [Algebra A K']
    (τ : K →ₐ[A] K') (t b : K) (hb : IsIntegral (Algebra.adjoin A ({t} : Set K)) b) :
    IsIntegral (Algebra.adjoin A ({τ t} : Set K')) (τ b) := by
  have hmap : (Algebra.adjoin A ({t} : Set K)).map τ = Algebra.adjoin A {τ t} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
  let φ : Algebra.adjoin A ({t} : Set K) →+* Algebra.adjoin A ({τ t} : Set K') :=
    { toFun := fun s => ⟨τ s, by rw [← hmap]; exact Subalgebra.mem_map.mpr ⟨s, s.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  exact hb.map_of_comp_eq φ τ.toRingHom (by ext s; rfl)

theorem mem_chartAlgInf_iff_of_algEquiv {A : Type} [CommRing A] {K K' : Type} [Field K] [Field K'] [Algebra A K]
    [Algebra A K'] (φ : K ≃ₐ[A] K') (t : K) (t' : K') (ht : φ t = t') (y : K) :
    y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A K t ↔
      φ y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A K' t' := by
  subst ht
  rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff, AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff]
  constructor
  · intro h
    have := isIntegral_adjoin_map' (φ : K →ₐ[A] K') t⁻¹ y h
    rwa [AlgEquiv.coe_algHom, map_inv₀] at this
  · intro h
    have := isIntegral_adjoin_map' (φ.symm : K' →ₐ[A] K) (φ t)⁻¹ (φ y) h
    rwa [AlgEquiv.coe_algHom, map_inv₀, AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply] at this

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun s => HahnSeries.coeff s k) h
  simpa [coeffMap_coeff] using this

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in

theorem poleChart_bridge
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
    (∀ c, c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' →
      ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁ ∧
        (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁ ∧ s = 1 + j₁⁻¹ * a) ∧
        s * c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁) ∧
    (∀ c, c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁ →
      ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' ∧
        (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' ∧ s = 1 + j'⁻¹ * a) ∧
        s * c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j')  := by
  intro F₀ hK1 hLD hRAT instA halg j₁ hj₁ instj₁ j' hj'
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  obtain ⟨e, he⟩ := ModularCurve.FullLevel.exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap q M' k₀ K₁ hK₁
    F₀ hK1 (hLD K₁ hK₁) hRAT
  letI algAK : Algebra ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) := ((algebraMap ↥K₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))).comp (algebraMap ↥A₁ ↥K₁)).toAlgebra
  haveI hsc : @IsScalarTower ↥A₁ ↥K₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) inferInstance inferInstance algAK.toSMul :=
    @IsScalarTower.of_algebraMap_eq ↥A₁ ↥K₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) _ _ _ _ _ algAK (fun _ => rfl)
  have hι : Function.Injective (algebraMap ↥K₁ (AlgebraicClosure ℚ)) := fun a b h => Subtype.ext h
  have hιcomp : (algebraMap ↥K₁ (AlgebraicClosure ℚ)).comp (algebraMap ℚ ↥K₁) = algebraMap ℚ (AlgebraicClosure ℚ) :=
    Subsingleton.elim _ _
  have hcc : ∀ x : LaurentSeries ℚ, coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) (coeffEmb ↥K₁ x) =
      coeffEmb (AlgebraicClosure ℚ) x := fun x => by
    show coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) (coeffMap (algebraMap ℚ ↥K₁) x) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) x
    rw [coeffMap_coeffMap, hιcomp]

  have hecomm : ∀ a : ↥A₁, e (algebraMap ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) a) = algebraMap ↥A₁ _ a := by
    intro a
    have h1 := halg a
    have h2 : ((algebraMap ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) a : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries ↥K₁) = HahnSeries.single 0 ((a : ↥K₁)) := by
      rw [← algebraMap_laurentSeries_eq_single]; rfl
    apply Subtype.ext
    apply Subtype.ext
    rw [he, h2, h1, coeffMap_single]
    show HahnSeries.single 0 ((a : ↥K₁) : AlgebraicClosure ℚ) = ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))
    rw [← algebraMap_laurentSeries_eq_single]; rfl
  let eA : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) ≃ₐ[↥A₁] _ := AlgEquiv.ofRingEquiv (f := e) hecomm
  have heA : ∀ f, eA f = e f := fun _ => rfl

  let jK : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) := e.symm j₁
  let j'K : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) := e.symm j'
  have hejK : e jK = j₁ := e.apply_symm_apply j₁
  have hej'K : e j'K = j' := e.apply_symm_apply j'
  have hj₁coe : (((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [hj₁]; rfl
  have hqjq : qExpand ℚ q jq ≠ 0 := by
    intro h0
    have := congrArg (fun s => HahnSeries.coeff s ((q : ℤ) * (-1))) h0
    simp only [qExpand_coeff_mul, coeff_jq_neg_one] at this
    simp at this

  have hjKc : coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((jK : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries ↥K₁) =
      coeffEmb (AlgebraicClosure ℚ) jq := by rw [← he, hejK, hj₁coe]
  have hj'Kc : coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((j'K : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries ↥K₁) =
      coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) := by rw [← he, hej'K, hj']
  haveI : Fact (jK ≠ 0) := ⟨fun h0 => jq_ne_zero (coeffMap_injective (algebraMap ℚ (AlgebraicClosure ℚ))
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective (by
      show coeffEmb (AlgebraicClosure ℚ) jq = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) 0
      rw [← hjKc, h0, map_zero]; simp))⟩
  haveI : Fact (j'K ≠ 0) := ⟨fun h0 => hqjq (coeffMap_injective (algebraMap ℚ (AlgebraicClosure ℚ))
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective (by
      show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) 0
      rw [← hj'Kc, h0, map_zero]; simp))⟩
  obtain ⟨-, -, H3, H4⟩ :=
    ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
      q hq1 ↥K₁ (laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) ↥A₁ jK
      (by apply coeffMap_injective _ hι; rw [hjKc, hcc])
      j'K
      (by apply coeffMap_injective _ hι; rw [hj'Kc, hcc])
  have heAj : eA jK = j₁ := hejK
  have heAj' : eA j'K = j' := hej'K
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have hcK : e.symm c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) j'K := by
      rw [mem_chartAlgInf_iff_of_algEquiv eA j'K j' heAj', heA, e.apply_symm_apply]; exact hc
    obtain ⟨sK, hsK, ⟨aK, haK, hsdef⟩, hsc⟩ := H3 _ hcK
    refine ⟨e sK, ?_, ⟨e aK, ?_, ?_⟩, ?_⟩
    · rw [← heA, ← mem_chartAlgInf_iff_of_algEquiv eA jK j₁ heAj]; exact hsK
    · rw [← heA, ← mem_chartAlgInf_iff_of_algEquiv eA jK j₁ heAj]; exact haK
    · rw [hsdef, map_add, map_one, map_mul, map_inv₀, hejK]
    · have : e sK * c = e (sK * e.symm c) := by rw [map_mul, e.apply_symm_apply]
      rw [this, ← heA, ← mem_chartAlgInf_iff_of_algEquiv eA jK j₁ heAj]; exact hsc
  · have hcK : e.symm c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) jK := by
      rw [mem_chartAlgInf_iff_of_algEquiv eA jK j₁ heAj, heA, e.apply_symm_apply]; exact hc
    obtain ⟨sK, hsK, ⟨aK, haK, hsdef⟩, hsc⟩ := H4 _ hcK
    refine ⟨e sK, ?_, ⟨e aK, ?_, ?_⟩, ?_⟩
    · rw [← heA, ← mem_chartAlgInf_iff_of_algEquiv eA j'K j' heAj']; exact hsK
    · rw [← heA, ← mem_chartAlgInf_iff_of_algEquiv eA j'K j' heAj']; exact haK
    · rw [hsdef, map_add, map_one, map_mul, map_inv₀, hej'K]
    · have : e sK * c = e (sK * e.symm c) := by rw [map_mul, e.apply_symm_apply]
      rw [this, ← heA, ← mem_chartAlgInf_iff_of_algEquiv eA j'K j' heAj']; exact hsc

end W4

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

section ModEq

variable {L : Type} [Field L] [CharZero L]

theorem exists_monic_eval₂_coeffEmb (p : ℕ) [Fact p.Prime] [NeZero p] :
    ∃ Φ : Polynomial (Polynomial ℤ), Φ.Monic ∧
      Φ.eval₂ (aeval (ModularCurve.coeffEmb L ModularCurve.jq)).toRingHom
        (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) = 0 ∧
      Φ.eval₂ (aeval (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))).toRingHom
        (ModularCurve.coeffEmb L ModularCurve.jq) = 0 := by
  obtain ⟨data, hsymm⟩ := ModularCurve.exists_modularPolynomialData_evalSymm p
  have h0 : data.Φ.eval₂ (aeval ModularCurve.jq).toRingHom (ModularCurve.qExpand ℚ p ModularCurve.jq) = 0 := by
    have := data.eval_eq_zero
    rwa [ModularCurve.evalAtJ_def] at this
  have h1 : data.Φ.eval₂ (aeval (ModularCurve.qExpand ℚ p ModularCurve.jq)).toRingHom ModularCurve.jq = 0 := by
    rw [← hsymm]; exact h0
  have key : ∀ x y : LaurentSeries ℚ,
      (ModularCurve.coeffEmb L) (data.Φ.eval₂ (aeval x).toRingHom y)
        = data.Φ.eval₂ (aeval (ModularCurve.coeffEmb L x)).toRingHom (ModularCurve.coeffEmb L y) := by
    intro x y
    rw [hom_eval₂]
    congr 1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp
    · simp
  refine ⟨data.Φ, data.monic, ?_, ?_⟩
  · rw [← key, h0, map_zero]
  · rw [← key, h1, map_zero]

end ModEq

section Generic

variable {A T S : Type} [CommRing A] [Field T] [CommRing S] [Algebra A T]

theorem isIntegral_adjoin_of_eval₂_hom (ι : T →+* S) (hι : Function.Injective ι) (a b : T)
    (Φ : Polynomial (Polynomial ℤ)) (hm : Φ.Monic)
    (h : Φ.eval₂ (aeval (ι a)).toRingHom (ι b) = 0) :
    IsIntegral (Algebra.adjoin A ({a} : Set T)) b := by
  let a' : Algebra.adjoin A ({a} : Set T) := ⟨a, Algebra.self_mem_adjoin_singleton A a⟩
  let θ : Polynomial ℤ →+* Algebra.adjoin A ({a} : Set T) := (aeval a').toRingHom
  refine ⟨Φ.map θ, hm.map θ, ?_⟩
  rw [eval₂_map]
  apply hι
  rw [hom_eval₂, map_zero]
  convert h using 2
  refine Polynomial.ringHom_ext (fun n => by simp) ?_
  simp [θ, a']

end Generic

section JQ

private theorem _root_.TH1AuxIg.isIntegral_adjoin_jq_qExpand {A T : Type} [CommRing A] [Field T] [Algebra A T]
    (p : ℕ) [Fact p.Prime] (a b : T)
    (ι : T →+* LaurentSeries (AlgebraicClosure ℚ)) (hι : Function.Injective ι)
    (ha : ι a = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq)
    (hb : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ι b = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ p ModularCurve.jq)) :
    IsIntegral (Algebra.adjoin A ({a} : Set T)) b ∧ IsIntegral (Algebra.adjoin A ({b} : Set T)) a := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨Φ, hm, h1, h2⟩ := exists_monic_eval₂_coeffEmb (L := AlgebraicClosure ℚ) p
  refine ⟨isIntegral_adjoin_of_eval₂_hom ι hι a b Φ hm ?_, isIntegral_adjoin_of_eval₂_hom ι hι b a Φ hm ?_⟩
  · convert h1 using 2 <;> first | rfl | exact Polynomial.ringHom_ext (fun n => by simp) (by simp [ha])
  · convert h2 using 2 <;> first | rfl | exact Polynomial.ringHom_ext (fun n => by simp) (by simp [hb])

p2m_export "TH1AuxIg" "isIntegral_adjoin_jq_qExpand"
end JQ

section W6

theorem evalAt_algebraMap' {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] (P : Place K Fb) (hP : P.IsRational)
    (c : K) : P.evalAt (algebraMap K Fb c) = c := by
  apply P.algebraMap_residueField_injective
  rw [P.algebraMap_evalAt hP (P.algebraMap_mem' c)]
  rw [show (⟨algebraMap K Fb c, P.algebraMap_mem' c⟩ : ↥P.toValuationSubring) = algebraMap K ↥P.toValuationSubring c from
    Subtype.ext (by rw [Place.coe_algebraMap])]
  rfl

noncomputable def resEquiv' {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] (P : Place K Fb) (hP : P.IsRational) :
    K ≃+* P.ResidueField :=
  RingEquiv.ofBijective (algebraMap K P.ResidueField) ⟨P.algebraMap_residueField_injective, hP⟩

noncomputable def evalHom' {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] (P : Place K Fb) (hP : P.IsRational) :
    ↥P.toValuationSubring →+* K :=
  (resEquiv' P hP).symm.toRingHom.comp (IsLocalRing.residue ↥P.toValuationSubring)

theorem evalHom'_apply {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] (P : Place K Fb) (hP : P.IsRational)
    (f : ↥P.toValuationSubring) : evalHom' P hP f = P.evalAt (f : Fb) := by
  apply (resEquiv' P hP).injective
  show resEquiv' P hP ((resEquiv' P hP).symm (IsLocalRing.residue _ f)) = algebraMap K P.ResidueField (P.evalAt (f : Fb))
  rw [RingEquiv.apply_symm_apply, Place.algebraMap_evalAt P hP f.2]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem mem_and_evalAt_mem_of_qExpand
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
    ∀ (Q : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), Q.IsRational →
      (j' : ↥(fieldBar q M')) ∈ Q.toValuationSubring → Q.evalAt (j' : ↥(fieldBar q M')) ∈ A →
      (j₁ : ↥(fieldBar q M')) ∈ Q.toValuationSubring ∧ Q.evalAt (j₁ : ↥(fieldBar q M')) ∈ A  := by
  intro F₀ hK1 hLD hRAT instA halg j₁ hj₁ instj₁ j' hj' Q hQ hj'Q hj'A
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hj₁coe : (((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [hj₁]; rfl

  letI algAF : Algebra ↥A ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥A (AlgebraicClosure ℚ))).toAlgebra
  have halgA : ∀ a : ↥A, algebraMap ↥A ↥(fieldBar q M') a =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ) := fun _ => rfl

  obtain ⟨-, hint⟩ := isIntegral_adjoin_jq_qExpand (A := ↥A) q (j₁ : ↥(fieldBar q M')) (j' : ↥(fieldBar q M'))
    (algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ)))
    (fun a b h => Subtype.ext h) hj₁coe hj'

  have hS : ∀ z ∈ Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M')), z ∈ Q.toValuationSubring := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        rw [hx]; exact hj'Q
    | algebraMap a => rw [halgA]; exact Q.algebraMap_mem' _
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  let φ : ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M'))) →+* ↥Q.toValuationSubring :=
    { toFun := fun z => ⟨(z : ↥(fieldBar q M')), hS z z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }

  have hint₁ : IsIntegral ↥Q.toValuationSubring ((j₁ : ↥(fieldBar q M'))) :=
    hint.map_of_comp_eq φ (RingHom.id ↥(fieldBar q M')) (by ext z; rfl)
  obtain ⟨J, hJ⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥Q.toValuationSubring) (K := ↥(fieldBar q M'))).mp hint₁
  have hj₁Q : (j₁ : ↥(fieldBar q M')) ∈ Q.toValuationSubring := by rw [← hJ]; exact J.2
  refine ⟨hj₁Q, ?_⟩

  let θ : ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M'))) →+* AlgebraicClosure ℚ :=
    (evalHom' Q hQ).comp φ
  have hθ : ∀ z, θ z = Q.evalAt (z : ↥(fieldBar q M')) := fun z => evalHom'_apply Q hQ (φ z)
  have hθA : ∀ z : ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M'))), θ z ∈ A := by
    intro z
    obtain ⟨z, hz⟩ := z
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [hθ]; exact hj'A
    | algebraMap a =>
        rw [hθ]
        dsimp only
        rw [halgA, evalAt_algebraMap' Q hQ]
        exact a.2
    | add x y hx' hy' hx hy =>
        have : (⟨x + y, Subalgebra.add_mem _ hx' hy'⟩ :
            ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M')))) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
        rw [this, map_add]; exact add_mem hx hy
    | mul x y hx' hy' hx hy =>
        have : (⟨x * y, Subalgebra.mul_mem _ hx' hy'⟩ :
            ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M')))) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
        rw [this, map_mul]; exact mul_mem hx hy
  let θA : ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M'))) →+* ↥A :=
    θ.codRestrict A.toSubring hθA

  obtain ⟨P, hPm, hPj⟩ := hint
  have hJcoe : ((J : ↥Q.toValuationSubring) : ↥(fieldBar q M')) = (j₁ : ↥(fieldBar q M')) := hJ
  have hevJ : Polynomial.eval₂ φ J P = 0 := by
    apply Subtype.val_injective
    have h1 : (((Polynomial.eval₂ φ J P : ↥Q.toValuationSubring)) : ↥(fieldBar q M')) =
        Polynomial.eval₂ ((algebraMap ↥Q.toValuationSubring ↥(fieldBar q M')).comp φ)
          ((algebraMap ↥Q.toValuationSubring ↥(fieldBar q M')) J) P :=
      Polynomial.hom_eval₂ P φ (algebraMap ↥Q.toValuationSubring ↥(fieldBar q M')) J
    rw [h1, show (algebraMap ↥Q.toValuationSubring ↥(fieldBar q M')).comp φ =
        algebraMap ↥(Algebra.adjoin ↥A ({(j' : ↥(fieldBar q M'))} : Set ↥(fieldBar q M'))) ↥(fieldBar q M') from
          RingHom.ext fun z => rfl,
      show (algebraMap ↥Q.toValuationSubring ↥(fieldBar q M')) J = (j₁ : ↥(fieldBar q M')) from hJ, ZeroMemClass.coe_zero]
    exact hPj
  have hint₂ : IsIntegral ↥A (Q.evalAt (j₁ : ↥(fieldBar q M'))) := by
    refine ⟨P.map θA, hPm.map θA, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥A (AlgebraicClosure ℚ)).comp θA = (evalHom' Q hQ).comp φ := by
      ext z; rfl
    have hev : Q.evalAt (j₁ : ↥(fieldBar q M')) = evalHom' Q hQ J := by rw [evalHom'_apply, hJcoe]
    rw [hcomp, hev, ← Polynomial.hom_eval₂, hevJ, map_zero]
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hint₂
  rw [← ha]; exact a.2

end W6

end TH1AuxIg

namespace TH1Wanted2

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

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
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 51200000 in
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

    ∀ g ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
        ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
      (OIg (lineInfty q)).comap g.toAlgHom.toRingHom ≠ OIg (lineInfty q) →
        ∀ x x' : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x → OffBranch x → GoodPt x' → OffBranch x' →
          ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), Centred P x → ¬ Centred (g • P) x' := by

  classical
  intro F₀ hK1 hSTAB hLD hRAT instA₁ halg j₁ hj₁ instj₁ InStalk InMax Centred GoodPt Reads OffBranch g hg hgW x x' hx hoff hx' hoff' P hP hgP
  obtain ⟨hPrat, hPcen⟩ := hP
  obtain ⟨hgPrat, hgPcen⟩ := hgP
  have hjt0 : (j₁ : ↥(fieldBar q M')) ≠ 0 := fun h => (Fact.out : j₁ ≠ 0) (Subtype.ext h)

  obtain ⟨ℓ₀, hℓ₀, hWg⟩ : ∃ ℓ₀ : CuspidalType.ProjLine q, ℓ₀ ≠ lineInfty q ∧
      (OIg (lineInfty q)).comap g.toAlgHom.toRingHom = OIg ℓ₀ := by
    obtain ⟨σp, hσp⟩ := TH1AuxIg.closure_comap_igusaRing_perm q M' OIg hIg_perm g hg
    refine ⟨σp (lineInfty q), fun h => hgW ?_, hσp _⟩
    rw [hσp, h]

  have hnu : ∀ f : ↥(fieldBar q M'), f ∈ (OIg ℓ₀).nonunits ↔ g f ∈ (OIg (lineInfty q)).nonunits := by
    intro f
    rw [← hWg]
    exact TH1AuxIg.mem_nonunits_comap_iff (OIg (lineInfty q)) (g : ↥(fieldBar q M') ≃+* ↥(fieldBar q M')) f

  obtain ⟨j', hj', hW2⟩ :=
    TH1AuxIg.exists_qExpand_and_forall_closure_exists_algEquiv_restrict q hq2 M' hqM' k₀ K₁ hK₁ A₁ F₀ hK1 hSTAB hLD hRAT halg
  obtain ⟨σ, hσ, hσsymm, hσj'⟩ := hW2 g hg

  have hι : Function.Injective ((algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ))).comp (algebraMap (type_of% j₁) ↥(fieldBar q M')) :
      (type_of% j₁) →+* LaurentSeries (AlgebraicClosure ℚ)) := by
    intro a b h
    exact Subtype.ext (Subtype.ext h)

  have hmut := TH1Transport.isIntegral_adjoin_jq_qExpand (A := ↥A₁) q j₁ j'
    ((algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ))).comp (algebraMap (type_of% j₁) ↥(fieldBar q M'))) hι
    (by show ((j₁ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = _; rw [hj₁]; rfl)
    (by show ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = _; rw [hj'])
  have hfin_stab : ∀ b, b ∈ TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁ ↔ σ b ∈ TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁ :=
    fun b => TH1Transport.mem_chartAlg_singleton_iff_map_mem σ hmut.1 hmut.2 hσj' b
  have hσj'inv : σ j'⁻¹ = j'⁻¹ := by rw [map_inv₀, hσj']
  have hself : IsIntegral ↥(Algebra.adjoin ↥A₁ ({j'⁻¹} : Set _)) j'⁻¹ :=
    isIntegral_algebraMap (x := (⟨j'⁻¹, Algebra.self_mem_adjoin_singleton ↥A₁ j'⁻¹⟩ : ↥(Algebra.adjoin ↥A₁ ({j'⁻¹} : Set _))))
  have hB'_stab : ∀ c, c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' ↔ σ c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' :=
    fun c => TH1Transport.mem_chartAlg_singleton_iff_map_mem σ hself hself hσj'inv c

  obtain ⟨hbr3, hbr4⟩ := TH1AuxIg.poleChart_bridge q hq2 M' hqM' A hle k₀ K₁ hK₁ A₁ hA₁ F₀ hK1 hLD hRAT halg j₁ hj₁ j' hj'

  obtain ⟨hj₁invW, hj₁W, hj'invW, hj'W, hconstW⟩ :=
    TH1Wanted2.inv_mem_and_const_mem_of_gaussPresentation q hq2 M' hqM' A hle k₀ K₁ hK₁ A₁ hA₁ F₀ hK1 hLD hRAT halg j₁ hj₁ j' hj'
      (OIg (lineInfty q)) hIg_inf
  have hB'W : ∀ c, c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' → (↑c : ↥(fieldBar q M')) ∈ OIg (lineInfty q) :=
    TH1Wanted2.chartAlg_singleton_le_valuationSubring (algebraMap (type_of% j₁) ↥(fieldBar q M')) (OIg (lineInfty q)) j'⁻¹ hj'invW hconstW
  have hInfW : ∀ c, c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁ → (↑c : ↥(fieldBar q M')) ∈ OIg (lineInfty q) :=
    TH1Wanted2.chartAlg_singleton_le_valuationSubring (algebraMap (type_of% j₁) ↥(fieldBar q M')) (OIg (lineInfty q)) j₁⁻¹ hj₁invW hconstW
  have hW6 : ∀ (Q : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), Q.IsRational →
      (j' : ↥(fieldBar q M')) ∈ Q.toValuationSubring → Q.evalAt (j' : ↥(fieldBar q M')) ∈ A →
      (j₁ : ↥(fieldBar q M')) ∈ Q.toValuationSubring ∧ Q.evalAt (j₁ : ↥(fieldBar q M')) ∈ A :=
    TH1AuxIg.mem_and_evalAt_mem_of_qExpand q hq2 M' hqM' A hle k₀ K₁ hK₁ A₁ hA₁ F₀ hK1 hLD hRAT halg j₁ hj₁ j' hj'

  have hgev : ∀ f : ↥(fieldBar q M'), (g • P).evalAt (g f) = P.evalAt f := fun f => Place.Transport.evalAt_smul g P hPrat f
  have hσF : ∀ f, (↑(σ f) : ↥(fieldBar q M')) = g (f : ↥(fieldBar q M')) := hσ

  have stalkFin : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ _ j₁)) (y : ↥(TwoChartIntegralModel.XFin ↥A₁ _ j₁)),
      (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y = z →
      ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁), InStalk z b.1 := by
    intro z y hy b
    have hov : ∀ y', (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y' = z →
        ∃ zz : TwoChartIntegralModel.XMid ↥A₁ _ j₁,
          y.asIdeal = Ideal.comap (TwoChartIntegralModel.inclFin ↥A₁ _ j₁).toRingHom zz.asIdeal ∧
          y'.asIdeal = Ideal.comap (TwoChartIntegralModel.inclInf ↥A₁ _ j₁).toRingHom zz.asIdeal :=
      fun y' hy' => L2Aux.exists_comap_eq_of_ιFin_eq_ιInf ↥A₁ _ j₁ y y' (hy.trans hy'.symm)
    refine ⟨fun y₂ _ => ⟨b, 1, (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top, by simp⟩, fun y' hy' => ?_⟩
    obtain ⟨zz, hzy, hzy'⟩ := hov y' hy'
    obtain ⟨n, g', hbg, hnot, -⟩ := L2Aux.exists_inf_witness ↥A₁ _ j₁ zz b
    exact ⟨g', TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ^ n, by rwa [hzy'], hbg⟩
  have maxFin : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ _ j₁)) (y : ↥(TwoChartIntegralModel.XFin ↥A₁ _ j₁)),
      (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base y = z →
      ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁), InMax z b.1 ↔ b ∈ y.asIdeal := by
    intro z y hy b
    have hov : ∀ y', (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y' = z →
        ∃ zz : TwoChartIntegralModel.XMid ↥A₁ _ j₁,
          y.asIdeal = Ideal.comap (TwoChartIntegralModel.inclFin ↥A₁ _ j₁).toRingHom zz.asIdeal ∧
          y'.asIdeal = Ideal.comap (TwoChartIntegralModel.inclInf ↥A₁ _ j₁).toRingHom zz.asIdeal :=
      fun y' hy' => L2Aux.exists_comap_eq_of_ιFin_eq_ιInf ↥A₁ _ j₁ y y' (hy.trans hy'.symm)
    constructor
    · rintro ⟨hF, -⟩
      obtain ⟨g', h, hh, hg, hbh⟩ := hF y hy
      have hbh' : b * h = g' := Subtype.ext hbh
      have hmem : b * h ∈ y.asIdeal := by rw [hbh']; exact hg
      exact (y.isPrime.mem_or_mem hmem).resolve_right hh
    · intro hb
      refine ⟨fun y₂ hy₂ => ?_, fun y' hy' => ?_⟩
      · have hyy : y₂ = y :=
          (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).isOpenEmbedding.injective (hy₂.trans hy.symm)
        subst hyy
        exact ⟨b, 1, (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top, hb, by simp⟩
      · obtain ⟨zz, hzy, hzy'⟩ := hov y' hy'
        obtain ⟨n, g', hbg, hnot, hiff⟩ := L2Aux.exists_inf_witness ↥A₁ _ j₁ zz b
        refine ⟨g', TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ^ n, by rwa [hzy'], ?_, hbg⟩
        rw [hzy']
        exact hiff.1 (by rw [← hzy]; exact hb)
  have stalkInf : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ _ j₁)) (y : ↥(TwoChartIntegralModel.XInf ↥A₁ _ j₁)),
      z ∉ Set.range (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base →
      (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y = z →
      ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁), InStalk z b.1 := by
    intro z y hz hy b
    exact ⟨fun y₂ hy₂ => absurd ⟨y₂, hy₂⟩ hz,
      fun y₂ _ => ⟨b, 1, (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top, by simp⟩⟩
  have maxInf : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ _ j₁)) (y : ↥(TwoChartIntegralModel.XInf ↥A₁ _ j₁)),
      z ∉ Set.range (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base →
      (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y = z →
      ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁), InMax z b.1 ↔ b ∈ y.asIdeal := by
    intro z y hz hy b
    constructor
    · rintro ⟨-, hI⟩
      obtain ⟨g', h, hh, hg, hbh⟩ := hI y hy
      have hbh' : b * h = g' := Subtype.ext hbh
      have hmem : b * h ∈ y.asIdeal := by rw [hbh']; exact hg
      exact (y.isPrime.mem_or_mem hmem).resolve_right hh
    · intro hb
      refine ⟨fun y₂ hy₂ => absurd ⟨y₂, hy₂⟩ hz, fun y₂ hy₂ => ?_⟩
      have hyy : y₂ = y :=
        (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).isOpenEmbedding.injective (hy₂.trans hy.symm)
      subst hyy
      exact ⟨b, 1, (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top, hb, by simp⟩
  have stalkB' : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ _ j₁)) (y : ↥(TwoChartIntegralModel.XInf ↥A₁ _ j₁)),
      z ∉ Set.range (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base →
      (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y = z →
      ∀ c, c ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' → InStalk z c := by
    intro z y hz hy c hc
    refine ⟨fun y₂ hy₂ => absurd ⟨y₂, hy₂⟩ hz, fun y₂ hy₂ => ?_⟩
    have hyy : y₂ = y :=
      (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).isOpenEmbedding.injective (hy₂.trans hy.symm)
    subst hyy
    obtain ⟨s, hsI, ⟨a, haI, hsa⟩, hscI⟩ := hbr3 c hc
    have hjinv : TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ∈ y₂.asIdeal :=
      L2Aux.jInvChartInf_mem_of_not_mem_range ↥A₁ _ j₁ y₂ (by rw [hy₂]; exact hz)
    have hs_not : (⟨s, hsI⟩ : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)) ∉ y₂.asIdeal := by
      intro hs
      have hdec : (⟨s, hsI⟩ : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)) =
          1 + TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ * ⟨a, haI⟩ := by
        apply Subtype.ext
        simp [hsa, TwoChartIntegralModel.coe_jInvChartInf]
      have h1 : (1 : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)) ∈ y₂.asIdeal := by
        have := y₂.asIdeal.sub_mem hs (y₂.asIdeal.mul_mem_right ⟨a, haI⟩ hjinv)
        rwa [hdec, add_sub_cancel_right] at this
      exact (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top h1
    exact ⟨⟨s * c, hscI⟩, ⟨s, hsI⟩, hs_not, by simp [mul_comm]⟩

  have noMix : ∀ (Q : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), Q.IsRational → ∀ f : ↥(fieldBar q M'), f ≠ 0 →
      f ∈ Q.toValuationSubring → Q.evalAt f ∈ A → f⁻¹ ∈ Q.toValuationSubring → A.valuation (Q.evalAt f⁻¹) < 1 → False := by
    intro Q hQ f hf0 hfO hfA hfiO hlt
    have hone : Q.evalAt f * Q.evalAt f⁻¹ = 1 := by
      rw [← L2Aux.evalAt_mul Q hQ hfO hfiO, mul_inv_cancel₀ hf0, Place.evalAt_one]
    have h1 : A.valuation (Q.evalAt f * Q.evalAt f⁻¹) < 1 := by
      rw [map_mul]
      calc A.valuation (Q.evalAt f) * A.valuation (Q.evalAt f⁻¹)
          ≤ 1 * A.valuation (Q.evalAt f⁻¹) := mul_le_mul_left ((A.valuation_le_one_iff _).2 hfA) _
        _ = A.valuation (Q.evalAt f⁻¹) := one_mul _
        _ < 1 := hlt
    rw [hone, map_one] at h1
    exact lt_irrefl _ h1

  have cuspVal : ∀ (Q : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')) (z : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ _ j₁)), Centred Q z →
      z ∉ Set.range (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base →
      ((j₁ : ↥(fieldBar q M')))⁻¹ ∈ Q.toValuationSubring ∧ A.valuation (Q.evalAt ((j₁ : ↥(fieldBar q M')))⁻¹) < 1 ∧
      ((j' : ↥(fieldBar q M')))⁻¹ ∈ Q.toValuationSubring ∧ A.valuation (Q.evalAt ((j' : ↥(fieldBar q M')))⁻¹) < 1 := by
    intro Q z hQ hz
    obtain ⟨hQrat, hQcen⟩ := hQ
    obtain ⟨y, hy⟩ : ∃ y, (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y = z := by
      rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf ↥A₁ _ j₁ z with h | h
      · exact absurd h hz
      · exact h
    have hjinv : TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ∈ y.asIdeal :=
      L2Aux.jInvChartInf_mem_of_not_mem_range ↥A₁ _ j₁ y (by rw [hy]; exact hz)
    have hSt : InStalk z j₁⁻¹ := stalkInf z y hz hy (TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁)
    have hMx : InMax z j₁⁻¹ := (maxInf z y hz hy (TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁)).2 hjinv
    obtain ⟨hO1, hA1, hlt1⟩ := hQcen _ hSt
    have hj'inv_mem : j'⁻¹ ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' := TwoChartIntegralModel.subset_chartAlg ↥A₁ _ _ rfl
    obtain ⟨hO2, hA2, hlt2⟩ := hQcen _ (stalkB' z y hz hy _ hj'inv_mem)
    have hcoe1 : ((j₁⁻¹ : _) : ↥(fieldBar q M')) = ((j₁ : ↥(fieldBar q M')))⁻¹ := rfl
    have hcoe2 : ((j'⁻¹ : _) : ↥(fieldBar q M')) = ((j' : ↥(fieldBar q M')))⁻¹ := rfl
    rw [hcoe1] at hO1 hA1 hlt1
    rw [hcoe2] at hO2 hA2 hlt2
    refine ⟨hO1, hlt1.2 hMx, hO2, ?_⟩

    by_contra hnot
    have hval1 : A.valuation (Q.evalAt ((j' : ↥(fieldBar q M')))⁻¹) = 1 :=
      le_antisymm ((A.valuation_le_one_iff _).2 hA2) (not_lt.1 hnot)
    have hne : Q.evalAt ((j' : ↥(fieldBar q M')))⁻¹ ≠ 0 := by
      intro h; rw [h, map_zero] at hval1; exact zero_ne_one hval1
    have hj't0 : (j' : ↥(fieldBar q M')) ≠ 0 := by
      intro h; apply hne
      rw [h, inv_zero, ← L2Aux.evalHom_apply Q hQrat ⟨0, zero_mem _⟩]
      exact map_zero _
    have hj'O : (j' : ↥(fieldBar q M')) ∈ Q.toValuationSubring := by
      by_contra hj'
      have hnu' : ((j' : ↥(fieldBar q M')))⁻¹ ∈ Q.toValuationSubring.nonunits :=
        Q.toValuationSubring.inv_mem_nonunits_iff.2 (Or.inr hj')
      have hmax : (⟨((j' : ↥(fieldBar q M')))⁻¹, hO2⟩ : ↥Q.toValuationSubring) ∈ maximalIdeal ↥Q.toValuationSubring :=
        Q.toValuationSubring.coe_mem_nonunits_iff.1 hnu'
      apply hne
      rw [← L2Aux.evalHom_apply Q hQrat ⟨_, hO2⟩]
      show ((L2Aux.resEquiv Q hQrat).symm.toRingHom.comp (residue Q.toValuationSubring)) ⟨_, hO2⟩ = 0
      rw [RingHom.comp_apply]
      have : residue Q.toValuationSubring ⟨_, hO2⟩ = 0 := by
        show Ideal.Quotient.mk (maximalIdeal ↥Q.toValuationSubring) _ = 0
        exact Ideal.Quotient.eq_zero_iff_mem.2 hmax
      rw [this, map_zero]
    have hj'A : Q.evalAt (j' : ↥(fieldBar q M')) ∈ A := by
      have hone : Q.evalAt (j' : ↥(fieldBar q M')) * Q.evalAt ((j' : ↥(fieldBar q M')))⁻¹ = 1 := by
        rw [← L2Aux.evalAt_mul Q hQrat hj'O hO2, mul_inv_cancel₀ hj't0, Place.evalAt_one]
      have heq : Q.evalAt (j' : ↥(fieldBar q M')) = (Q.evalAt ((j' : ↥(fieldBar q M')))⁻¹)⁻¹ :=
        eq_inv_of_mul_eq_one_left hone
      rw [← A.valuation_le_one_iff, heq, map_inv₀, hval1, inv_one]
    obtain ⟨hj₁O, hj₁A⟩ := hW6 Q hQrat hj'O hj'A
    exact noMix Q hQrat (j₁ : ↥(fieldBar q M')) hjt0 hj₁O hj₁A hO1 (hlt1.2 hMx)

  have finVal : ∀ (Q : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')) (z : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ _ j₁)), Centred Q z →
      z ∈ Set.range (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base →
      (j₁ : ↥(fieldBar q M')) ∈ Q.toValuationSubring ∧ Q.evalAt (j₁ : ↥(fieldBar q M')) ∈ A ∧
      (j' : ↥(fieldBar q M')) ∈ Q.toValuationSubring ∧ Q.evalAt (j' : ↥(fieldBar q M')) ∈ A := by
    intro Q z hQ hz
    obtain ⟨hQrat, hQcen⟩ := hQ
    obtain ⟨y, hy⟩ := hz
    have hj₁mem : j₁ ∈ TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁ := TwoChartIntegralModel.subset_chartAlg ↥A₁ _ _ rfl
    have hj'mem : j' ∈ TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁ :=
      (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff ↥A₁ _).2 hmut.1
    obtain ⟨h1, h2, -⟩ := hQcen j₁ (stalkFin z y hy ⟨j₁, hj₁mem⟩)
    obtain ⟨h3, h4, -⟩ := hQcen j' (stalkFin z y hy ⟨j', hj'mem⟩)
    exact ⟨h1, h2, h3, h4⟩

  by_cases hxfin : x ∈ Set.range (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base
  · by_cases hx'fin : x' ∈ Set.range (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base
    ·
      obtain ⟨y, hy⟩ := hxfin
      obtain ⟨y', hy'⟩ := hx'fin
      obtain ⟨-, -, hx'3, -, -⟩ := hx'
      obtain ⟨b₀, hb₀ℓ, hb₀y⟩ := (hoff ℓ₀ hℓ₀).1 y hy
      have hb₁mem : σ b₀.1 ∈ TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁ := (hfin_stab b₀.1).1 b₀.2
      have hb₁F : (↑(σ b₀.1) : ↥(fieldBar q M')) = g (b₀.1 : ↥(fieldBar q M')) := hσF b₀.1
      have hb₁W : (↑(σ b₀.1) : ↥(fieldBar q M')) ∈ R.integers.nonunits := by
        rw [hR, hb₁F]; exact (hnu _).1 hb₀ℓ
      have hb₁y' : (⟨σ b₀.1, hb₁mem⟩ : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁)) ∈ y'.asIdeal :=
        hx'3 y' hy' ⟨σ b₀.1, hb₁mem⟩ hb₁W
      have hmax' : InMax x' (σ b₀.1) := (maxFin x' y' hy' ⟨σ b₀.1, hb₁mem⟩).2 hb₁y'
      obtain ⟨-, -, hlt'⟩ := hgPcen (σ b₀.1) (stalkFin x' y' hy' ⟨σ b₀.1, hb₁mem⟩)
      have hlt : A.valuation (P.evalAt (b₀.1 : ↥(fieldBar q M'))) < 1 := by
        have := hlt'.2 hmax'
        rwa [hb₁F, hgev] at this
      obtain ⟨-, -, hltx⟩ := hPcen b₀.1 (stalkFin x y hy b₀)
      exact hb₀y ((maxFin x y hy b₀).1 (hltx.1 hlt))
    ·
      obtain ⟨hjinv', hlt', -, -⟩ := cuspVal (g • P) x' ⟨hgPrat, hgPcen⟩ hx'fin
      obtain ⟨y, hy⟩ := hxfin
      have hmem : σ.symm j₁ ∈ TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁ := by
        rw [hfin_stab, AlgEquiv.apply_symm_apply]
        exact TwoChartIntegralModel.subset_chartAlg ↥A₁ _ _ rfl
      obtain ⟨hO, hAval, -⟩ := hPcen (σ.symm j₁) (stalkFin x y hy ⟨σ.symm j₁, hmem⟩)
      rw [hσsymm] at hO hAval
      have e1 : ((j₁ : ↥(fieldBar q M')))⁻¹ = g ((g.symm (j₁ : ↥(fieldBar q M')))⁻¹) := by
        rw [map_inv₀, AlgEquiv.apply_symm_apply]
      rw [e1, Place.Transport.mem_smul_iff'] at hjinv'
      rw [e1, hgev] at hlt'
      have hne : g.symm (j₁ : ↥(fieldBar q M')) ≠ 0 := by
        intro h; exact hjt0 (by simpa using congrArg g h)
      exact noMix P hPrat _ hne hO hAval hjinv' hlt'
  · by_cases hx'fin : x' ∈ Set.range (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base
    ·
      obtain ⟨hjinv, hlt, -, -⟩ := cuspVal P x ⟨hPrat, hPcen⟩ hxfin
      obtain ⟨y', hy'⟩ := hx'fin
      have hmem : σ j₁ ∈ TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁ :=
        (hfin_stab j₁).1 (TwoChartIntegralModel.subset_chartAlg ↥A₁ _ _ rfl)
      obtain ⟨hO, hAval, -⟩ := hgPcen (σ j₁) (stalkFin x' y' hy' ⟨σ j₁, hmem⟩)
      rw [hσF, Place.Transport.mem_smul_iff'] at hO
      rw [hσF, hgev] at hAval
      exact noMix P hPrat (j₁ : ↥(fieldBar q M')) hjt0 hO hAval hjinv hlt
    ·
      obtain ⟨y, hy⟩ : ∃ y, (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y = x := by
        rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf ↥A₁ _ j₁ x with h | h
        · exact absurd h hxfin
        · exact h
      obtain ⟨y', hy'⟩ : ∃ y', (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y' = x' := by
        rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf ↥A₁ _ j₁ x' with h | h
        · exact absurd h hx'fin
        · exact h
      obtain ⟨-, -, -, hx'4, -⟩ := hx'
      obtain ⟨b₀, hb₀ℓ, hb₀y⟩ := (hoff ℓ₀ hℓ₀).2 y hy

      obtain ⟨s', hs'B, ⟨a', ha'B, hs'eq⟩, hc₀B⟩ := hbr4 b₀.1 b₀.2
      have hσc₀B : σ (s' * b₀.1) ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' := (hB'_stab _).1 hc₀B
      have hσs'B : σ s' ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ _ j' := (hB'_stab _).1 hs'B

      obtain ⟨s'', hs''I, ⟨a'', ha''I, hs''eq⟩, hdI⟩ := hbr3 _ hσc₀B
      have hdW : (↑(s'' * σ (s' * b₀.1)) : ↥(fieldBar q M')) ∈ R.integers.nonunits := by
        rw [hR]
        have e1 : (↑(s'' * σ (s' * b₀.1)) : ↥(fieldBar q M')) = (↑s'' : ↥(fieldBar q M')) * ((↑(σ s') : ↥(fieldBar q M')) * (↑(σ b₀.1) : ↥(fieldBar q M'))) := by
          rw [map_mul]; rfl
        rw [e1, ValuationSubring.mem_nonunits_iff, map_mul, map_mul]
        have h1 : (OIg (lineInfty q)).valuation (↑s'' : ↥(fieldBar q M')) ≤ 1 :=
          ((OIg (lineInfty q)).valuation_le_one_iff _).2 (hInfW s'' hs''I)
        have h2 : (OIg (lineInfty q)).valuation (↑(σ s') : ↥(fieldBar q M')) ≤ 1 :=
          ((OIg (lineInfty q)).valuation_le_one_iff _).2 (hB'W _ hσs'B)
        have h3 : (OIg (lineInfty q)).valuation (↑(σ b₀.1) : ↥(fieldBar q M')) < 1 := by
          rw [hσF]; exact (ValuationSubring.mem_nonunits_iff _).1 ((hnu _).1 hb₀ℓ)
        calc (OIg (lineInfty q)).valuation (↑s'' : ↥(fieldBar q M')) *
              ((OIg (lineInfty q)).valuation (↑(σ s') : ↥(fieldBar q M')) * (OIg (lineInfty q)).valuation (↑(σ b₀.1) : ↥(fieldBar q M')))
            ≤ 1 * (1 * (OIg (lineInfty q)).valuation (↑(σ b₀.1) : ↥(fieldBar q M'))) := mul_le_mul' h1 (mul_le_mul_left h2 _)
          _ = (OIg (lineInfty q)).valuation (↑(σ b₀.1) : ↥(fieldBar q M')) := by rw [one_mul, one_mul]
          _ < 1 := h3
      have hdy' : (⟨s'' * σ (s' * b₀.1), hdI⟩ : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)) ∈ y'.asIdeal :=
        hx'4 y' hy' ⟨_, hdI⟩ hdW
      have hs''y' : (⟨s'', hs''I⟩ : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)) ∉ y'.asIdeal := by
        have hjinv' : TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ∈ y'.asIdeal :=
          L2Aux.jInvChartInf_mem_of_not_mem_range ↥A₁ _ j₁ y' (by rw [hy']; exact hx'fin)
        intro hs
        have hdec : (⟨s'', hs''I⟩ : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)) =
            1 + TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ * ⟨a'', ha''I⟩ := by
          apply Subtype.ext
          simp [hs''eq, TwoChartIntegralModel.coe_jInvChartInf]
        have h1 : (1 : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)) ∈ y'.asIdeal := by
          have := y'.asIdeal.sub_mem hs (y'.asIdeal.mul_mem_right ⟨a'', ha''I⟩ hjinv')
          rwa [hdec, add_sub_cancel_right] at this
        exact (Ideal.ne_top_iff_one _).1 y'.isPrime.ne_top h1
      have hmax' : InMax x' (σ (s' * b₀.1)) := by
        refine ⟨fun y₂ hy₂ => absurd ⟨y₂, hy₂⟩ hx'fin, fun y₂ hy₂ => ?_⟩
        have hyy : y₂ = y' :=
          (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).isOpenEmbedding.injective (hy₂.trans hy'.symm)
        subst hyy
        exact ⟨⟨_, hdI⟩, ⟨s'', hs''I⟩, hs''y', hdy', by simp [mul_comm]⟩
      obtain ⟨-, -, hlt'⟩ := hgPcen (σ (s' * b₀.1)) (stalkB' x' y' hx'fin hy' _ hσc₀B)
      have hlt : A.valuation (P.evalAt (↑(s' * b₀.1) : ↥(fieldBar q M'))) < 1 := by
        have := hlt'.2 hmax'
        rwa [hσF, hgev] at this
      obtain ⟨hs'O, hs'A, -⟩ := hPcen s' (stalkB' x y hxfin hy s' hs'B)
      obtain ⟨hb₀O, hb₀A, hb₀lt⟩ := hPcen b₀.1 (stalkInf x y hxfin hy b₀)
      have hcoemul : (↑(s' * b₀.1) : ↥(fieldBar q M')) = (s' : ↥(fieldBar q M')) * (b₀.1 : ↥(fieldBar q M')) := rfl
      rw [hcoemul, L2Aux.evalAt_mul P hPrat hs'O hb₀O, map_mul] at hlt
      have hs'unit : A.valuation (P.evalAt (s' : ↥(fieldBar q M'))) = 1 := by
        obtain ⟨-, -, hjO', hjlt'⟩ := cuspVal P x ⟨hPrat, hPcen⟩ hxfin
        obtain ⟨ha'O, ha'A, -⟩ := hPcen a' (stalkB' x y hxfin hy a' ha'B)
        have hcoe2 : ((j'⁻¹ : _) : ↥(fieldBar q M')) = ((j' : ↥(fieldBar q M')))⁻¹ := rfl
        have e : (s' : ↥(fieldBar q M')) = 1 + ((j' : ↥(fieldBar q M')))⁻¹ * (a' : ↥(fieldBar q M')) := by rw [hs'eq]; rfl
        have hm : ((j' : ↥(fieldBar q M')))⁻¹ * (a' : ↥(fieldBar q M')) ∈ P.toValuationSubring := mul_mem hjO' ha'O
        have hadd : P.evalAt (1 + ((j' : ↥(fieldBar q M')))⁻¹ * (a' : ↥(fieldBar q M'))) = 1 + P.evalAt (((j' : ↥(fieldBar q M')))⁻¹ * (a' : ↥(fieldBar q M'))) := by
          have := map_add (L2Aux.evalHom P hPrat) ⟨1, one_mem _⟩ ⟨_, hm⟩
          rw [L2Aux.evalHom_apply, L2Aux.evalHom_apply, L2Aux.evalHom_apply] at this
          rw [Place.evalAt_one] at this
          exact this
        rw [e, hadd, L2Aux.evalAt_mul P hPrat hjO' ha'O]
        apply Valuation.map_one_add_of_lt
        rw [map_mul]
        calc A.valuation (P.evalAt ((j' : ↥(fieldBar q M')))⁻¹) * A.valuation (P.evalAt (a' : ↥(fieldBar q M')))
            ≤ A.valuation (P.evalAt ((j' : ↥(fieldBar q M')))⁻¹) * 1 := mul_le_mul_right ((A.valuation_le_one_iff _).2 ha'A) _
          _ < 1 := by rw [mul_one]; exact hjlt'
      rw [hs'unit, one_mul] at hlt
      exact hb₀y ((maxInf x y hxfin hy b₀).1 (hb₀lt.1 hlt))

end S_ModularCurve_FullLevel_not_centred_smul_of_comap_igusaGaussRing_ne_of_offBranch_twoChartIntegralModel_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_not_centred_smul_of_comap_igusaGaussRing_ne_of_offBranch_twoChartIntegralModel_of_eq_two (solution)
