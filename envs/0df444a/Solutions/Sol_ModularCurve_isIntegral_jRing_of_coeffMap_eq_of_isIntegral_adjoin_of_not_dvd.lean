-- Prove2me | solution 1 for ModularCurve.isIntegral_jRing_of_coeffMap_eq_of_isIntegral_adjoin_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/34261a3e-d9f3-5e6e-87f4-5a8121432b43

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_FibreModel
import Theorems.Thm_ModularCurve_CharPModel_exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem
import Theorems.Thm_ModularCurve_exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd
import Theorems.Thm_ModularCurve_modularFunctionFieldBar_le
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegral_jRing_of_coeffMap_eq_of_isIntegral_adjoin_of_not_dvd
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq"
p2m_attr_erase "simp" "ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve~jBar ModularCurve.CharPModel Polynomial"

noncomputable section

namespace SEP3

local notation "Qb" => AlgebraicClosure ℚ

theorem coe_jBar (N : ℕ) [NeZero N] :
    ((jBar N : modularFunctionFieldBar N) : LaurentSeries Qb) = jqModC Qb := by
  rw [show ((jBar N : modularFunctionFieldBar N) : LaurentSeries Qb)
      = (jqModC ℚ).map (algebraMap ℚ Qb) from rfl, map_jqModC]

theorem algebraMap_jBar (N : ℕ) [NeZero N] :
    algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries Qb) (jBar N) = jqModC Qb :=
  coe_jBar N

theorem transcendental_jBar (N : ℕ) [NeZero N] :
    Transcendental Qb (jBar N : modularFunctionFieldBar N) := by
  have hinj : Function.Injective (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries Qb)) :=
    (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries Qb)).injective
  refine (transcendental_algebraMap_iff (R := Qb) (a := (jBar N : modularFunctionFieldBar N)) hinj).mp ?_
  rw [algebraMap_jBar]
  exact transcendental_jqModC Qb

theorem mem_of_monic_eval_eq_zero {F : Type*} [Field F] (V : ValuationSubring F) {Q : F[X]}
    (hQ : Q.Monic) (hc : ∀ i, Q.coeff i ∈ V) {u : F} (hu : Q.eval u = 0) : u ∈ V := by
  by_contra hnot
  have hinv : u⁻¹ ∈ V := (V.mem_or_inv_mem u).resolve_left hnot
  have hu0 : u ≠ 0 := fun h => hnot (h ▸ zero_mem V)
  have hQ0 : Q.natDegree ≠ 0 := fun h0 => by
    have hc : Q.coeff 0 = 1 := by
      have := hQ.coeff_natDegree
      rwa [h0] at this
    have h1 : Q = 1 := by
      rw [eq_C_of_natDegree_eq_zero h0, hc, C_1]
    rw [h1, eval_one] at hu
    exact one_ne_zero hu
  obtain ⟨n, hn⟩ : ∃ n, Q.natDegree = n + 1 := Nat.exists_eq_add_one_of_ne_zero hQ0
  rw [eval_eq_sum_range, hn, Finset.sum_range_succ, ← hn, hQ.coeff_natDegree, one_mul, hn] at hu

  have key : u = -(∑ i ∈ Finset.range (n + 1), Q.coeff i * u⁻¹ ^ (n - i)) := by
    have h2 : u ^ (n + 1) = -(∑ i ∈ Finset.range (n + 1), Q.coeff i * u ^ i) := eq_neg_of_add_eq_zero_right hu
    have h3 : u = u ^ (n + 1) * u⁻¹ ^ n := by
      rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ hu0, one_pow, mul_one]
    conv_lhs => rw [h3]
    rw [h2, neg_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [mul_assoc]
    congr 1
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi'
    rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu0, one_pow, one_mul]
  apply hnot
  rw [key]
  exact neg_mem (sum_mem fun i _ => mul_mem (hc i) (pow_mem hinv _))

theorem eval₂_modularPolynomial_jNBar (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldBar N)) (jBar N))
      (jNBar N) = 0 := by
  have hinj : Function.Injective (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries Qb)) :=
    (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries Qb)).injective
  rw [← hinj.eq_iff, map_zero, Polynomial.hom_eval₂]
  have h0 := congrArg (coeffEmb Qb) data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂] at h0
  have hX : algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries Qb) (jNBar N) = coeffEmb Qb (jqN N) := rfl
  have hC : (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries Qb)).comp
      (Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldBar N)) (jBar N))
      = (coeffEmb Qb).comp evalAtJ := by
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        evalAtJ_X]
      rfl
  rw [hC, hX]
  exact h0

theorem jNBar_mem_of_jBar_mem (N : ℕ) [NeZero N] (V : ValuationSubring (modularFunctionFieldBar N))
    (hj : (jBar N : modularFunctionFieldBar N) ∈ V) : (jNBar N : modularFunctionFieldBar N) ∈ V := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hφV : ∀ r : Polynomial ℤ,
      Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldBar N)) (jBar N) r ∈ V := by
    intro r
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
    refine sum_mem fun i _ => mul_mem ?_ (pow_mem hj _)
    rw [eq_intCast]
    exact intCast_mem V _
  refine mem_of_monic_eval_eq_zero V
    (Q := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldBar N)) (jBar N)))
    (data.monic.map _) (fun i => ?_) ?_
  · rw [Polynomial.coeff_map]; exact hφV _
  · rw [Polynomial.eval_map]; exact eval₂_modularPolynomial_jNBar N data

def pack (A : ValuationSubring Qb) (x : LaurentSeries Qb) (hx : ∀ n : ℤ, x.coeff n ∈ A) :
    LaurentSeries A where
  coeff n := ⟨x.coeff n, hx n⟩
  isPWO_support' := x.isPWO_support.mono (by
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    exact fun h0 => hn (Subtype.ext h0))

theorem coeffMap_pack (A : ValuationSubring Qb) (x : LaurentSeries Qb) (hx : ∀ n : ℤ, x.coeff n ∈ A) :
    coeffMap A.subtype (pack A x hx) = x := by
  ext n
  rfl

theorem memLoc {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] (A : ValuationSubring Qb)
    (K : IntermediateField ℚ Qb) {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hqN : ¬ q ∣ N)
    (y : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (g₀ : ↥(modularFunctionFieldBar N))
    (hg₀y : (g₀ : LaurentSeries Qb) = coeffMap (NodeLocalized.coeffSubring A K).subtype y) :
    (g₀ : LaurentSeries Qb) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
  have hcoef : ∀ n : ℤ, (g₀ : LaurentSeries Qb).coeff n ∈ A := fun n => by
    rw [hg₀y, coeffMap_coeff]
    exact (Subring.mem_inf.mp (y.coeff n).2).1
  let g' : ↥(modularFunctionFieldBar (N * q)) :=
    ⟨(g₀ : LaurentSeries Qb), modularFunctionFieldBar_le N (dvd_mul_right N q) g₀.2⟩
  exact (exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd N q hqN A red g').mp
    ⟨pack A (g₀ : LaurentSeries Qb) hcoef, 1, by rw [map_one]; exact one_ne_zero,
      by rw [map_one, mul_one, coeffMap_pack]⟩

theorem poleFree {N : ℕ} [NeZero N] (g₀ : ↥(modularFunctionFieldBar N))
    (hint : IsIntegral ↥(Algebra.adjoin Qb ({jBar N, jNBar N} : Set ↥(modularFunctionFieldBar N))) g₀) :
    ∀ u₀ : Place Qb ↥(modularFunctionFieldBar N),
      jBar N ∈ u₀.toValuationSubring → g₀ ∈ u₀.toValuationSubring := by
  intro u₀ hj
  let S : Subalgebra Qb ↥(modularFunctionFieldBar N) :=
    { u₀.toValuationSubring.toSubring.toSubsemiring with
      algebraMap_mem' := u₀.algebraMap_mem' }
  have hle : Algebra.adjoin Qb ({jBar N, jNBar N} : Set ↥(modularFunctionFieldBar N)) ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro x (rfl | rfl)
    · exact hj
    · exact jNBar_mem_of_jBar_mem N u₀.toValuationSubring hj
  obtain ⟨p, hpm, hp⟩ := hint
  refine mem_of_monic_eval_eq_zero u₀.toValuationSubring
    (Q := p.map (algebraMap _ ↥(modularFunctionFieldBar N))) (hpm.map _) (fun i => ?_) ?_
  · rw [Polynomial.coeff_map]; exact hle (p.coeff i).2
  · rw [Polynomial.eval_map]; exact hp

def E (N : ℕ) [NeZero N] : IntermediateField Qb ↥(modularFunctionFieldBar N) :=
  IntermediateField.adjoin Qb {jBar N}

section KDescent

variable (N : ℕ) [NeZero N] (A : ValuationSubring Qb)

def phiA : Polynomial ↥A →+* ↥(modularFunctionFieldBar N) :=
  Polynomial.eval₂RingHom ((algebraMap Qb ↥(modularFunctionFieldBar N)).comp A.subtype) (jBar N)

theorem algebraMap_valuationSubring_eq : algebraMap ↥A Qb = A.subtype :=
  RingHom.ext fun a => ValuationSubring.algebraMap_apply A a

theorem phiA_map (P : Polynomial ↥A) :
    phiA N A P = Polynomial.aeval (jBar N) (P.map (algebraMap ↥A Qb)) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_valuationSubring_eq]
  rfl

theorem phiA_C (a : ↥A) : phiA N A (C a) = algebraMap Qb ↥(modularFunctionFieldBar N) a := by
  rw [phiA, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl

theorem phiA_X : phiA N A X = jBar N := by
  rw [phiA, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

theorem phiA_injective : Function.Injective (phiA N A) := by
  intro P Q h
  have hinj := transcendental_iff_injective.mp (transcendental_jBar N)
  apply Polynomial.map_injective (algebraMap ↥A Qb)
    (by rw [algebraMap_valuationSubring_eq]; exact Subtype.val_injective)
  apply hinj
  rw [← phiA_map, ← phiA_map, h]

theorem phiA_mem (P : Polynomial ↥A) : phiA N A P ∈ affineBaseFin N A := by
  induction P using Polynomial.induction_on with
  | C a =>
      rw [phiA_C]
      exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a h =>
      rw [pow_succ, ← mul_assoc, map_mul]
      exact mul_mem h (by rw [phiA_X]; exact Subring.subset_closure (Or.inr rfl))

theorem affineBaseFin_le_range : affineBaseFin N A ≤ (phiA N A).range := by
  refine Subring.closure_le.mpr ?_
  rintro x (⟨a, rfl⟩ | hx)
  · exact ⟨C a, phiA_C N A a⟩
  · rw [Set.mem_singleton_iff] at hx
    exact ⟨X, (phiA_X N A).trans hx.symm⟩

def eA : Polynomial ↥A ≃+* ↥(affineBaseFin N A) :=
  RingEquiv.ofBijective ((phiA N A).codRestrict (affineBaseFin N A) (phiA_mem N A))
    ⟨fun P Q h => phiA_injective N A (congrArg Subtype.val h),
     fun x => by
      obtain ⟨P, hP⟩ := affineBaseFin_le_range N A x.2
      exact ⟨P, Subtype.ext hP⟩⟩

theorem coe_eA (P : Polynomial ↥A) :
    ((eA N A P : ↥(affineBaseFin N A)) : ↥(modularFunctionFieldBar N)) = phiA N A P :=
  rfl

theorem mem_E_of_mem_affineBaseFin {x : ↥(modularFunctionFieldBar N)} (hx : x ∈ affineBaseFin N A) :
    x ∈ E N := by
  refine (Subring.closure_le (t := (E N).toSubring)).mpr ?_ hx
  rintro y (⟨a, rfl⟩ | hy)
  · exact IntermediateField.algebraMap_mem (E N) (a : Qb)
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact IntermediateField.mem_adjoin_simple_self Qb (jBar N)

def inclE : ↥(affineBaseFin N A) →+* ↥(E N) where
  toFun x := ⟨x.1, mem_E_of_mem_affineBaseFin N A x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable {N}

theorem exists_polynomial_coeff_minpoly (A : ValuationSubring Qb)
    (g₀ : ↥(modularFunctionFieldBar N)) (p : Polynomial ↥(affineBaseFin N A)) (hpm : p.Monic)
    (hp : Polynomial.eval₂ (affineBaseFin N A).subtype g₀ p = 0) :
    IsIntegral ↥(E N) g₀ ∧
    ∀ i : ℕ, ∃ P : Polynomial ↥A,
      (((minpoly ↥(E N) g₀).coeff i : ↥(E N)) : ↥(modularFunctionFieldBar N))
        = P.eval₂ ((algebraMap Qb ↥(modularFunctionFieldBar N)).comp A.subtype) (jBar N) := by
  classical
  letI : Algebra ↥(affineBaseFin N A) ↥(E N) := (inclE N A).toAlgebra
  haveI : IsScalarTower ↥(affineBaseFin N A) ↥(E N) ↥(modularFunctionFieldBar N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul ↥(affineBaseFin N A) ↥(E N) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr fun x y h => by
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      exact h'
  haveI : IsIntegrallyClosed ↥(affineBaseFin N A) := IsIntegrallyClosed.of_equiv (eA N A)

  have hC : ∀ b : ↥A, phiA N A (C b) = algebraMap Qb ↥(modularFunctionFieldBar N) (b : Qb) := phiA_C N A
  have key : ∀ (b : ↥A) (t : Polynomial Qb) (t' : Polynomial ↥A),
      t'.map (algebraMap ↥A Qb) = b • t →
        phiA N A t' = algebraMap Qb ↥(modularFunctionFieldBar N) (b : Qb) * Polynomial.aeval (jBar N) t := by
    intro b t t' h
    rw [phiA_map, h, Algebra.smul_def, Polynomial.algebraMap_apply, map_mul, Polynomial.aeval_C,
      ValuationSubring.algebraMap_apply]
  haveI : IsFractionRing ↥(affineBaseFin N A) ↥(E N) := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff Qb (z : ↥(modularFunctionFieldBar N))).mp z.2
    obtain ⟨br, hbr, hr⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ↥A) r
    obtain ⟨bs, hbs, hs⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ↥A) s
    have hbr0 : algebraMap Qb ↥(modularFunctionFieldBar N) (br : Qb) ≠ 0 :=
      (_root_.map_ne_zero _).mpr fun h => nonZeroDivisors.ne_zero hbr (Subtype.ext h)
    have hbs0 : algebraMap Qb ↥(modularFunctionFieldBar N) (bs : Qb) ≠ 0 :=
      (_root_.map_ne_zero _).mpr fun h => nonZeroDivisors.ne_zero hbs (Subtype.ext h)
    refine ⟨eA N A (C bs * IsLocalization.integerNormalization (nonZeroDivisors ↥A) r),
      eA N A (C br * IsLocalization.integerNormalization (nonZeroDivisors ↥A) s), Subtype.ext ?_⟩
    rw [IntermediateField.coe_div]
    change (z : ↥(modularFunctionFieldBar N))
        = phiA N A (C bs * IsLocalization.integerNormalization (nonZeroDivisors ↥A) r)
          / phiA N A (C br * IsLocalization.integerNormalization (nonZeroDivisors ↥A) s)
    rw [map_mul, map_mul, key br r _ hr, key bs s _ hs, hC, hC, ← mul_assoc, ← mul_assoc,
      mul_comm (algebraMap Qb ↥(modularFunctionFieldBar N) (bs : Qb)),
      mul_div_mul_left _ _ (mul_ne_zero hbr0 hbs0), hrs]
  have hint₀ : IsIntegral ↥(affineBaseFin N A) g₀ := ⟨p, hpm, hp⟩
  refine ⟨hint₀.tower_top, fun i => ?_⟩
  refine ⟨(eA N A).symm ((minpoly ↥(affineBaseFin N A) g₀).coeff i), ?_⟩
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' (↥(E N)) hint₀, Polynomial.coeff_map]
  change _ = phiA N A ((eA N A).symm ((minpoly ↥(affineBaseFin N A) g₀).coeff i))
  rw [← coe_eA, RingEquiv.apply_symm_apply]
  rfl

end KDescent

section Galois
variable {N : ℕ} [NeZero N]

def tau (K : IntermediateField ℚ Qb) (σ : Qb ≃ₐ[↥K] Qb) :
    ↥(modularFunctionFieldBar N) ≃+* ↥(modularFunctionFieldBar N) :=
  arithmeticRingAut (modularFunctionFieldFull N) (σ.restrictScalars ℚ)

theorem coe_tau (K : IntermediateField ℚ Qb) (σ : Qb ≃ₐ[↥K] Qb) (x : ↥(modularFunctionFieldBar N)) :
    ((tau (N := N) K σ x : ↥(modularFunctionFieldBar N)) : LaurentSeries Qb)
      = coeffMap ((σ.restrictScalars ℚ : Qb ≃ₐ[ℚ] Qb) : Qb →+* Qb) (x : LaurentSeries Qb) :=
  rfl

theorem tau_algebraMap (K : IntermediateField ℚ Qb) (σ : Qb ≃ₐ[↥K] Qb) (a : Qb) :
    tau (N := N) K σ (algebraMap Qb _ a) = algebraMap Qb _ (σ a) :=
  arithmeticRingAut_algebraMap (modularFunctionFieldFull N) (σ.restrictScalars ℚ) a

theorem tau_jBar (K : IntermediateField ℚ Qb) (σ : Qb ≃ₐ[↥K] Qb) :
    tau (N := N) K σ (jBar N) = jBar N :=
  Subtype.ext (coeffMap_coeffEmb (σ.restrictScalars ℚ) jq)

theorem tau_eq_self_of_coeffMap (A : ValuationSubring Qb) (K : IntermediateField ℚ Qb) (σ : Qb ≃ₐ[↥K] Qb)
    (y : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (g₀ : ↥(modularFunctionFieldBar N))
    (hg₀y : (g₀ : LaurentSeries Qb) = coeffMap (NodeLocalized.coeffSubring A K).subtype y) :
    tau (N := N) K σ g₀ = g₀ := by
  apply Subtype.ext
  rw [coe_tau, hg₀y, coeffMap_coeffMap]
  refine coeffMap_congr (RingHom.ext fun a => ?_) y

  have haK : (a : Qb) ∈ K := (Subring.mem_inf.mp a.2).2
  show (σ.restrictScalars ℚ) (a : Qb) = (a : Qb)
  rw [AlgEquiv.restrictScalars_apply]
  exact σ.commutes (⟨(a : Qb), haK⟩ : ↥K)

theorem tau_aeval (K : IntermediateField ℚ Qb) (σ : Qb ≃ₐ[↥K] Qb) (Q : Polynomial Qb) :
    tau (N := N) K σ (Polynomial.aeval (jBar N) Q) = Polynomial.aeval (jBar N) (Q.map (σ : Qb →+* Qb)) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map,
    show (tau (N := N) K σ) (Polynomial.eval₂ (algebraMap Qb _) (jBar N) Q)
      = (tau (N := N) K σ).toRingHom (Polynomial.eval₂ (algebraMap Qb _) (jBar N) Q) from rfl,
    Polynomial.hom_eval₂]

  have h1 : (tau (N := N) K σ).toRingHom (jBar N) = jBar N := tau_jBar K σ
  have h2 : (tau (N := N) K σ).toRingHom.comp (algebraMap Qb _) = (algebraMap Qb _).comp (σ : Qb →+* Qb) :=
    RingHom.ext fun a => tau_algebraMap K σ a
  rw [h1, h2]

theorem map_eq_self_of_minpoly (A : ValuationSubring Qb) (K : IntermediateField ℚ Qb)
    (y : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (g₀ : ↥(modularFunctionFieldBar N))
    (hg₀y : (g₀ : LaurentSeries Qb) = coeffMap (NodeLocalized.coeffSubring A K).subtype y)
    (hint : IsIntegral ↥(E N) g₀)
    (P : ℕ → Polynomial Qb)
    (hP : ∀ i, (((minpoly ↥(E N) g₀).coeff i : ↥(E N)) : ↥(modularFunctionFieldBar N))
        = Polynomial.aeval (jBar N) (P i))
    (σ : Qb ≃ₐ[↥K] Qb) (i : ℕ) :
    (P i).map (σ : Qb →+* Qb) = P i := by
  classical
  have hmmon : (minpoly ↥(E N) g₀).Monic := minpoly.monic hint

  set mF : Polynomial ↥(modularFunctionFieldBar N) :=
    (minpoly ↥(E N) g₀).map (algebraMap ↥(E N) ↥(modularFunctionFieldBar N)) with hmF
  set mσ : Polynomial ↥(modularFunctionFieldBar N) := mF.map (tau (N := N) K σ).toRingHom with hmσ
  have hcoeffF : ∀ j, mF.coeff j = Polynomial.aeval (jBar N) (P j) := fun j => by
    rw [hmF, Polynomial.coeff_map]; exact hP j
  have hcoeffσ : ∀ j, mσ.coeff j = Polynomial.aeval (jBar N) ((P j).map (σ : Qb →+* Qb)) := fun j => by
    rw [hmσ, Polynomial.coeff_map, hcoeffF]; exact tau_aeval K σ (P j)
  have hmFmon : mF.Monic := hmmon.map _
  have hmσmon : mσ.Monic := hmFmon.map _
  have hdegσ : mσ.natDegree = (minpoly ↥(E N) g₀).natDegree := by
    rw [hmσ, hmFmon.natDegree_map, hmF, hmmon.natDegree_map]
  have hevalF : mF.eval g₀ = 0 := by
    have h := minpoly.aeval ↥(E N) g₀
    rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at h
  have hevalσ : mσ.eval g₀ = 0 := by
    have hfix : tau (N := N) K σ g₀ = g₀ := tau_eq_self_of_coeffMap A K σ y g₀ hg₀y
    have h : mσ.eval (tau (N := N) K σ g₀) = (tau (N := N) K σ).toRingHom (mF.eval g₀) := by
      rw [hmσ, Polynomial.eval_map]; exact Polynomial.eval₂_hom _ g₀
    rw [hfix, hevalF, map_zero] at h; exact h

  have hlifts : mσ ∈ Polynomial.lifts (algebraMap ↥(E N) ↥(modularFunctionFieldBar N)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro j
    rw [hcoeffσ]
    exact ⟨⟨_, IntermediateField.algebra_adjoin_le_adjoin Qb _
      (Polynomial.aeval_mem_adjoin_singleton Qb (jBar N))⟩, rfl⟩
  obtain ⟨m', hm'map, -, hm'mon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hmσmon
  have hm'eval : Polynomial.aeval g₀ m' = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hm'map]; exact hevalσ
  have hdvd : minpoly ↥(E N) g₀ ∣ m' := minpoly.dvd ↥(E N) g₀ hm'eval
  have hdeg : m'.natDegree ≤ (minpoly ↥(E N) g₀).natDegree := by
    rw [← hm'mon.natDegree_map (algebraMap ↥(E N) ↥(modularFunctionFieldBar N)), hm'map, hdegσ]
  have heq : m' = minpoly ↥(E N) g₀ :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmmon hm'mon hdvd hdeg
  have hci : mσ.coeff i = mF.coeff i := by
    rw [← hm'map, heq]
  rw [hcoeffσ, hcoeffF] at hci
  exact (transcendental_iff_injective.mp (transcendental_jBar N)) hci

end Galois

theorem mem_of_forall_algEquiv (K : IntermediateField ℚ Qb) (a : Qb)
    (h : ∀ σ : Qb ≃ₐ[↥K] Qb, σ a = a) : a ∈ K := by
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic ↥K Qb := Algebra.IsAlgebraic.tower_top (K := ℚ) ↥K
  haveI : Algebra.IsSeparable ↥K Qb := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Normal ↥K Qb := ⟨fun x => IsAlgClosed.splits _⟩
  haveI : IsGalois ↥K Qb := ⟨⟩
  have hmem : a ∈ IntermediateField.fixedField (⊤ : Subgroup (Qb ≃ₐ[↥K] Qb)) :=
    (IntermediateField.mem_fixedField_iff _ _).mpr fun σ _ => h σ
  rw [InfiniteGalois.fixedField_bot] at hmem
  obtain ⟨k', hk'⟩ := IntermediateField.mem_bot.mp hmem
  rw [← hk']
  exact k'.2

theorem algebraMap_aeval_jBar {N : ℕ} [NeZero N] (Q : Polynomial Qb) :
    algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries Qb) (Polynomial.aeval (jBar N) Q)
      = Q.eval₂ (algebraMap Qb (LaurentSeries Qb)) (jqModC Qb) := by
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq, algebraMap_jBar]

theorem eval₂_mem_jRing (A : ValuationSubring Qb) (K : IntermediateField ℚ Qb)
    (P₀ : Polynomial ↥(NodeLocalized.coeffSubring A K)) :
    P₀.eval₂ (CharPReduction.constSeries (NodeLocalized.coeffSubring A K)) (jqModC Qb)
      ∈ NodeLocalized.jRing A K := by
  rw [Polynomial.eval₂_eq_sum_range]
  refine sum_mem fun n _ => mul_mem ?_ (pow_mem ?_ n)
  · exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  · exact Subring.subset_closure (Or.inr rfl)

theorem kDescent {N : ℕ} [NeZero N] (A : ValuationSubring Qb) (K : IntermediateField ℚ Qb)
    (y : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (g₀ : ↥(modularFunctionFieldBar N))
    (hg₀y : (g₀ : LaurentSeries Qb) = coeffMap (NodeLocalized.coeffSubring A K).subtype y)
    (p : Polynomial ↥(affineBaseFin N A)) (hpm : p.Monic)
    (hp : Polynomial.eval₂ (affineBaseFin N A).subtype g₀ p = 0) :
    IsIntegral ↥(NodeLocalized.jRing A K) (g₀ : LaurentSeries Qb) := by
  classical
  obtain ⟨hintE, hcoef⟩ := exists_polynomial_coeff_minpoly A g₀ p hpm hp
  choose PA hPA using hcoef
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → Polynomial Qb, ∀ i, P i = (PA i).map A.subtype := ⟨_, fun _ => rfl⟩
  have hP : ∀ i, (((minpoly ↥(E N) g₀).coeff i : ↥(E N)) : ↥(modularFunctionFieldBar N))
      = Polynomial.aeval (jBar N) (P i) := fun i => by
    rw [hPA i, hPdef, Polynomial.aeval_def, Polynomial.eval₂_map]

  have hA : ∀ i n, (P i).coeff n ∈ A := fun i n => by
    rw [hPdef, Polynomial.coeff_map]
    exact ((PA i).coeff n).2
  have hK : ∀ i n, (P i).coeff n ∈ K := fun i n =>
    mem_of_forall_algEquiv K _ fun σ => by
      have h := congrArg (fun Q : Polynomial Qb => Q.coeff n)
        (map_eq_self_of_minpoly A K y g₀ hg₀y hintE P hP σ i)
      first | simpa only [Polynomial.coeff_map] using h | (simp only [Polynomial.coeff_map] at h; exact h)
  have hAK : ∀ i n, (P i).coeff n ∈ NodeLocalized.coeffSubring A K := fun i n =>
    Subring.mem_inf.mpr ⟨hA i n, hK i n⟩
  have hlift : ∀ i, ∃ P₀ : Polynomial ↥(NodeLocalized.coeffSubring A K),
      P₀.map (NodeLocalized.coeffSubring A K).subtype = P i := fun i => by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, hAK i n⟩, rfl⟩
  choose P₀ hP₀ using hlift

  have hcoefLS : ∀ i,
      algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries Qb)
          (((minpoly ↥(E N) g₀).coeff i : ↥(E N)) : ↥(modularFunctionFieldBar N))
        = (P₀ i).eval₂ (CharPReduction.constSeries (NodeLocalized.coeffSubring A K)) (jqModC Qb) := fun i => by
    rw [hP i, algebraMap_aeval_jBar, ← hP₀ i, Polynomial.eval₂_map]
    rfl

  have hmLSmon : (((minpoly ↥(E N) g₀).map (algebraMap ↥(E N) ↥(modularFunctionFieldBar N))).map
      (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries Qb))).Monic :=
    ((minpoly.monic hintE).map _).map _
  have hmLSlifts : (((minpoly ↥(E N) g₀).map (algebraMap ↥(E N) ↥(modularFunctionFieldBar N))).map
      (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries Qb)))
        ∈ Polynomial.lifts (NodeLocalized.jRing A K).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨_, eval₂_mem_jRing A K (P₀ n)⟩, ?_⟩
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    exact (hcoefLS n).symm
  obtain ⟨Pf, hPfmap, -, hPfmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hmLSlifts hmLSmon
  refine ⟨Pf, hPfmon, ?_⟩
  rw [← Polynomial.eval_map]
  change (Pf.map (NodeLocalized.jRing A K).subtype).eval
    (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries Qb) g₀) = 0
  rw [hPfmap, Polynomial.eval_map, Polynomial.eval₂_hom, Polynomial.eval_map, ← Polynomial.aeval_def,
    minpoly.aeval, map_zero]

end SEP3

end

theorem solution
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hqN : ¬ q ∣ N)
    (y : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (g₀ : ↥(modularFunctionFieldBar N))
    (hg₀y : (g₀ : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap (NodeLocalized.coeffSubring A K).subtype y)
    (hint : IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩,
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩} :
          Set ↥(modularFunctionFieldBar N))) g₀) :
    IsIntegral (NodeLocalized.jRing A K) (g₀ : LaurentSeries (AlgebraicClosure ℚ)) := by
  obtain ⟨p, hpm, hp⟩ :=
    ModularCurve.CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem
      red hqN g₀ (SEP3.memLoc A K red hqN y g₀ hg₀y) (SEP3.poleFree g₀ hint)
  exact SEP3.kDescent A K y g₀ hg₀y p hpm hp

end S_ModularCurve_isIntegral_jRing_of_coeffMap_eq_of_isIntegral_adjoin_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_isIntegral_jRing_of_coeffMap_eq_of_isIntegral_adjoin_of_not_dvd (solution)
