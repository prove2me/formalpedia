-- Prove2me | solution 1 for OAI.PiExponent.CurveComponentRigidity.coordinate_constant_of_persistent_comparison_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:05:21.740985+00:00
-- url     : https://prove2.me/submissions/5fc59ac0-819e-4f0f-9b0a-feb02951d8e0

import Mathlib
import Definitions.Def_OAIQ068A027

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_LogarithmicObstruction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open scoped LaurentSeries Matrix

open Polynomial

theorem polynomial_logarithmic_equation_impossible {K : Type*} [Field K] [CharZero K]
    (P Q : K[X]) (hQ : Q ≠ 0) (hcop : IsCoprime P Q) {c : K} (hc : c ≠ 0) :
    X * (derivative P * Q - P * derivative Q) ≠ C c * Q ^ 2 := by
  intro heq
  obtain ⟨U, hfactor, hU⟩ := Q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hQ 0
  simp only [map_zero, sub_zero] at hfactor hU
  have hU0 : U.coeff 0 ≠ 0 := fun h => hU (X_dvd_iff.mpr h)
  cases hn : Q.rootMultiplicity 0 with
  | zero =>
      have hQ0 : Q.coeff 0 ≠ 0 := by
        rw [hfactor, hn]
        simpa using hU0
      have hconst := congrArg (fun f : K[X] => f.coeff 0) heq
      have hz : c * (Q.coeff 0) ^ 2 = 0 := by simpa [pow_two] using hconst.symm
      exact (mul_ne_zero hc (pow_ne_zero _ hQ0)) hz
  | succ n =>
      have hQfactor : Q = X ^ (n + 1) * U := by simpa [hn] using hfactor
      have hQ0 : Q.coeff 0 = 0 := by simp [hQfactor]
      have hP0 : P.coeff 0 ≠ 0 := by
        intro hp
        obtain ⟨A, B, hab⟩ := hcop
        have hconst := congrArg (fun f : K[X] => f.coeff 0) hab
        simp [hp, hQ0] at hconst
      have hcancel :
          X * derivative P * U - P * (C (n + 1 : K) * U + X * derivative U) =
            C c * X ^ (n + 1) * U ^ 2 := by
        apply mul_left_cancel₀ (pow_ne_zero (n + 1) (X_ne_zero (R := K)))
        calc
          X ^ (n + 1) *
              (X * derivative P * U - P * (C (n + 1 : K) * U + X * derivative U)) =
              X * (derivative P * Q - P * derivative Q) := by
                rw [hQfactor, derivative_mul, derivative_X_pow_succ]
                ring
          _ = C c * Q ^ 2 := heq
          _ = X ^ (n + 1) * (C c * X ^ (n + 1) * U ^ 2) := by rw [hQfactor]; ring
      have hconst := congrArg (fun f : K[X] => f.coeff 0) hcancel
      have hz : P.coeff 0 * ((n + 1 : K) * U.coeff 0) = 0 := by
        simpa using hconst
      exact (mul_ne_zero hP0 (mul_ne_zero (Nat.cast_add_one_ne_zero n) hU0)) hz

theorem ratFunc_derivation_polynomial {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hDX : D RatFunc.X = 1) (p : K[X]) :
    D (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (derivative p) := by
  simpa [RatFunc.aeval_X_left_eq_algebraMap, hDX] using D.comp_aeval_eq RatFunc.X p

theorem ratFunc_derivation_ne_simple_pole {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hDX : D RatFunc.X = 1) (r : RatFunc K) {c : K} (hc : c ≠ 0) :
    D r ≠ RatFunc.C c / RatFunc.X := by
  intro heq
  have hquot := D.leibniz_div (algebraMap K[X] (RatFunc K) r.num)
    (algebraMap K[X] (RatFunc K) r.denom)
  rw [RatFunc.num_div_denom, ratFunc_derivation_polynomial D hDX,
    ratFunc_derivation_polynomial D hDX] at hquot
  have hder : D r =
      algebraMap K[X] (RatFunc K) (derivative r.num * r.denom - r.num * derivative r.denom) /
        (algebraMap K[X] (RatFunc K) r.denom) ^ 2 := by
    rw [hquot]
    simp only [smul_eq_mul, map_sub, map_mul, div_eq_mul_inv, inv_pow]
    ring
  have hden : algebraMap K[X] (RatFunc K) r.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero r.denom_ne_zero
  have hx : (RatFunc.X : RatFunc K) ≠ 0 := by
    rw [← RatFunc.algebraMap_X]
    exact RatFunc.algebraMap_ne_zero X_ne_zero
  have hcross := (div_eq_div_iff (pow_ne_zero 2 hden) hx).mp (hder.symm.trans heq)
  apply polynomial_logarithmic_equation_impossible r.num r.denom r.denom_ne_zero
    r.isCoprime_num_denom hc
  apply RatFunc.algebraMap_injective K
  simpa only [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, mul_comm] using hcross

theorem derivation_intermediate_smul
    {k F E : Type*} [Field k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (a : F) (z : E) : D (a • z) = d a • z + a • D z := by
  rw [Algebra.smul_def, D.leibniz, hcompat]
  simp only [smul_eq_mul, Algebra.smul_def]
  ring

theorem derivation_basis_coordinates
    {k F E ι : Type*} [Field k] [Field F] [Field E] [Fintype ι]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (b : Module.Basis ι F E) (z : E) (i : ι) :
    b.repr (D z) i = d (b.repr z i) +
      ∑ j, b.repr z j * b.repr (D (b j)) i := by
  classical
  conv_lhs => rw [← b.sum_repr z]
  simp only [map_sum, derivation_intermediate_smul d D hcompat, map_add,
    map_smul, Finset.sum_add_distrib, Finsupp.coe_add, Pi.add_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp [Finsupp.single_apply, eq_comm]

theorem derivation_trace_of_basis
    {k F E ι : Type*} [Field k] [Field F] [Field E] [Fintype ι]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (b : Module.Basis ι F E) (x : E) :
    d (Algebra.trace F E x) = Algebra.trace F E (D x) := by
  classical
  let M := Algebra.leftMulMatrix b x
  let N : Matrix ι ι F := fun i j => b.repr (D (b j)) i
  have hentry (i j : ι) :
      Algebra.leftMulMatrix b (D x) i j + (M * N) i j =
        d (M i j) + (N * M) i j := by
    have hMN : (M * N) i j = ∑ t, M i t * N t j := rfl
    have hNM : (N * M) i j = ∑ t, N i t * M t j := rfl
    have hz := derivation_basis_coordinates d D hcompat b (x * b j) i
    have hm := congrFun (Algebra.leftMulMatrix_mulVec_repr b x (D (b j))) i
    have hl : b.repr (D (x * b j)) i =
        Algebra.leftMulMatrix b (D x) i j + (M * N) i j := by
      rw [hMN, D.leibniz]
      simp only [smul_eq_mul, map_add, Finsupp.add_apply]
      rw [← hm]
      simp only [M, N, Algebra.leftMulMatrix_eq_repr_mul,
        Matrix.mulVec, dotProduct, mul_comm, add_comm]
    rw [hl] at hz
    simpa only [hNM, M, N, Algebra.leftMulMatrix_eq_repr_mul, mul_comm] using hz
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hentry i i)
  have ht : Matrix.trace (Algebra.leftMulMatrix b (D x)) + Matrix.trace (M * N) =
      d (Matrix.trace M) + Matrix.trace (N * M) := by
    simpa only [Matrix.trace, Matrix.diag_apply, Finset.sum_add_distrib, map_sum] using hs
  rw [Matrix.trace_mul_comm M N] at ht
  have ht' := add_right_cancel ht
  simpa only [Algebra.trace_eq_matrix_trace b, M] using ht'.symm

theorem finite_extension_derivation_ne_simple_pole
    {K E : Type*} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E]
    (d : Derivation K (RatFunc K) (RatFunc K)) (D : Derivation K E E)
    (hdX : d RatFunc.X = 1)
    (hcompat : ∀ a : RatFunc K,
      D (algebraMap (RatFunc K) E a) = algebraMap (RatFunc K) E (d a))
    (x : E) {c : K} (hc : c ≠ 0) :
    D x ≠ algebraMap (RatFunc K) E (RatFunc.C c / RatFunc.X) := by
  intro hx
  have ht := derivation_trace_of_basis d D hcompat
    (Module.finBasis (RatFunc K) E) x
  rw [hx, Algebra.trace_algebraMap] at ht
  have hdegree : (Module.finrank (RatFunc K) E : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := RatFunc K) (M := E)))
  apply ratFunc_derivation_ne_simple_pole d hdX (Algebra.trace (RatFunc K) E x)
    (mul_ne_zero hdegree hc)
  calc
    d (Algebra.trace (RatFunc K) E x) =
        Module.finrank (RatFunc K) E • (RatFunc.C c / RatFunc.X) := ht
    _ = RatFunc.C ((Module.finrank (RatFunc K) E : K) * c) / RatFunc.X := by
      simp only [map_mul, map_natCast, nsmul_eq_mul, mul_div_assoc]

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_TranscendenceBasisReduction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open scoped IntermediateField.algebraAdjoinAdjoin

theorem exists_intermediateField_finite_over_simple
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] {Y : E} (hY : Transcendental C Y) :
    ∃ K : IntermediateField C E,
      Transcendental K Y ∧ FiniteDimensional (IntermediateField.adjoin K {Y}) E := by
  classical
  have hsingle : AlgebraicIndepOn C id ({Y} : Set E) := by
    change AlgebraicIndependent C (fun z : ({Y} : Set E) => (z : E))
    rw [algebraicIndependent_singleton_iff ⟨Y, rfl⟩]
    exact hY
  obtain ⟨t, hsub, ht⟩ := exists_isTranscendenceBasis_superset hsingle
  have hYt : Y ∈ t := hsub (Set.mem_singleton Y)
  let s : Set E := t \ {Y}
  let K : IntermediateField C E := IntermediateField.adjoin C s
  have hts : insert Y s = t := by
    ext x
    simp only [s, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨hx, _⟩)
      · exact hYt
      · exact hx
    · intro hx
      by_cases heq : x = Y
      · exact Or.inl heq
      · exact Or.inr ⟨hx, heq⟩
  have hind : AlgebraicIndepOn C id (insert Y s) := by
    rw [hts]
    exact ht.1
  have htr : Transcendental (Algebra.adjoin C s) Y := by
    have hnot : Y ∉ s := by simp [s]
    have hh := (AlgebraicIndepOn.insert_iff hnot).mp hind
    have heq : id '' s = s := Set.image_id s
    rw [heq] at hh
    exact hh.2
  have htrK : Transcendental K Y := by
    intro h
    exact htr (h.restrictScalars (Algebra.adjoin C s))
  refine ⟨K, htrK, ?_⟩
  let L := IntermediateField.adjoin K ({Y} : Set E)
  have hL : L.restrictScalars C = IntermediateField.adjoin C t := by
    dsimp [L, K]
    rw [IntermediateField.adjoin_adjoin_left]
    congr 1
    rw [Set.union_comm, Set.singleton_union, hts]
  have halg : Algebra.IsAlgebraic L E := by
    change Algebra.IsAlgebraic (L.restrictScalars C) E
    rw [hL]
    have hh := ht.isAlgebraic_field
    have heq : Set.range ((↑) : t → E) = t := Subtype.range_coe
    rw [heq] at hh
    exact hh
  let : Algebra.IsAlgebraic L E := halg
  let : IsScalarTower C L E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  let : Algebra.EssFiniteType L E := Algebra.EssFiniteType.of_comp C L E
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Analysis_AlgebraicLogarithmicObstruction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open KaehlerDifferential
open scoped TensorProduct Polynomial nonZeroDivisors IntermediateField

theorem extendDerivation_algebraMap
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale S T]
    (d : Derivation R S S) (s : S) :
    extendDerivation (T := T) d (algebraMap S T s) = algebraMap S T (d s) := by
  simp [extendDerivation, LinearMap.compDer,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Derivation.liftKaehlerDifferential_comp_D]

@[simp]
theorem ratFuncDerivative_X {K : Type*} [Field K] :
    ratFuncDerivative (RatFunc.X : RatFunc K) = 1 := by
  let : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (K[X]⁰)
  change extendDerivation Polynomial.derivative' (RatFunc.X : RatFunc K) = 1
  rw [← RatFunc.algebraMap_X, extendDerivation_algebraMap]
  simp [Polynomial.derivative']

theorem finite_extension_no_logarithmic_differential
    {K E : Type*} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E] (x : E) :
    D K E x ≠ (algebraMap (RatFunc K) E RatFunc.X)⁻¹ •
      D K E (algebraMap (RatFunc K) E RatFunc.X) := by
  let : Algebra.FormallyEtale (RatFunc K) E :=
    Algebra.FormallyEtale.of_isSeparable (RatFunc K) E
  let delta : Derivation K E E := extendDerivation ratFuncDerivative
  have hcompat (a : RatFunc K) :
      delta (algebraMap (RatFunc K) E a) =
        algebraMap (RatFunc K) E (ratFuncDerivative a) :=
    extendDerivation_algebraMap ratFuncDerivative a
  intro heq
  have hd := congrArg delta.liftKaehlerDifferential heq
  simp only [Derivation.liftKaehlerDifferential_comp_D, map_smul, hcompat,
    ratFuncDerivative_X, map_one, smul_eq_mul, mul_one] at hd
  apply finite_extension_derivation_ne_simple_pole ratFuncDerivative delta
    ratFuncDerivative_X hcompat x (c := (1 : K)) one_ne_zero
  simpa only [map_div₀, map_one, one_div, map_inv₀] using hd

theorem adjoin_finite_no_logarithmic_differential
    {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
    (y : E) (hy : Transcendental K y) [FiniteDimensional K⟮y⟯ E] (x : E) :
    D K E x ≠ y⁻¹ • D K E y := by
  let F := K⟮y⟯
  let e : RatFunc K ≃ₐ[K] F := RatFunc.algEquivOfTranscendental y hy
  let : Algebra (RatFunc K) F := e.toRingHom.toAlgebra
  let : Algebra (RatFunc K) E :=
    ((algebraMap F E).comp e.toRingHom).toAlgebra
  let : IsScalarTower (RatFunc K) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K E a = algebraMap F E (e (algebraMap K (RatFunc K) a))
    rw [e.commutes]
    exact IsScalarTower.algebraMap_apply K F E a
  have : Module.Finite (RatFunc K) F :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) F) e.surjective
  have : Module.Finite (RatFunc K) E := Module.Finite.trans F E
  have hX : algebraMap (RatFunc K) E RatFunc.X = y := by
    change ((RatFunc.algEquivOfTranscendental y hy) RatFunc.X : E) = y
    exact RatFunc.algEquivOfTranscendental_X y hy
  simpa only [hX] using finite_extension_no_logarithmic_differential (K := K) x

theorem logarithmic_differential_base_change
    {C K E : Type*} [Field C] [Field K] [Field E]
    [Algebra C K] [Algebra C E] [Algebra K E] [IsScalarTower C K E]
    {x y : E} (h : D C E x = y⁻¹ • D C E y) :
    D K E x = y⁻¹ • D K E y := by
  have hm := congrArg (KaehlerDifferential.map C K E E) h
  simpa only [map_D, map_smul, Algebra.algebraMap_self, RingHom.id_apply] using hm

theorem no_logarithmic_differential_over_intermediateField
    {C E : Type*} [Field C] [CharZero C] [Field E] [Algebra C E]
    (K : IntermediateField C E) (y : E) (hy : Transcendental K y)
    [FiniteDimensional K⟮y⟯ E] (x : E) :
    D C E x ≠ y⁻¹ • D C E y := by
  intro h
  exact adjoin_finite_no_logarithmic_differential y hy x
    (logarithmic_differential_base_change (K := K) h)

theorem isAlgebraic_of_logarithmic_differential
    {C E : Type*} [Field C] [CharZero C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x y : E)
    (h : D C E x = y⁻¹ • D C E y) : IsAlgebraic C y := by
  by_contra hy
  obtain ⟨K, hKy, hfinite⟩ := exists_intermediateField_finite_over_simple C E hy
  have : FiniteDimensional K⟮y⟯ E := hfinite
  exact no_logarithmic_differential_over_intermediateField K y hKy x h

theorem constant_of_logarithmic_differential
    {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x y : E)
    (h : D C E x = y⁻¹ • D C E y) : ∃ c : C, algebraMap C E c = y := by
  have hy := isAlgebraic_of_logarithmic_differential x y h
  have hmem : y ∈ algebraicClosure C E := mem_algebraicClosure_iff.mpr hy
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure C E)] at hmem
  exact IntermediateField.mem_bot.mp hmem

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_DifferentialConstant
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

open KaehlerDifferential

theorem constant_of_differential_eq_zero
    {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x : E) (hx : D C E x = 0) :
    ∃ c : C, algebraMap C E c = x :=
  constant_of_logarithmic_differential (0 : E) x (by simp [hx])

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_NormalBasisRigidity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.NormalBasisRigidity

open Set Submodule Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma exists_normalBasis_subset [Fintype ι] (v : ι → V) (S : Set ι)
    (hS : span K (v '' S) = ⊤) :
    ∃ A : Finset ι, (A : Set ι) ⊆ S ∧ IsNormalBasis (K := K) v A := by
  classical
  let h := linearIndepOn_empty K v
  let A := h.extend (Set.empty_subset S)
  refine ⟨A.toFinset, ?_, ?_, ?_⟩
  · simpa only [Set.coe_toFinset] using h.extend_subset (Set.empty_subset S)
  · simpa only [Set.coe_toFinset] using h.linearIndepOn_extend (Set.empty_subset S)
  · simpa only [Set.coe_toFinset, A] using
      (h.span_image_extend_eq_span_image (Set.empty_subset S)).trans hS

lemma exists_normalBasis_containing [Fintype ι] (v : ι → V)
    (hv : span K (Set.range v) = ⊤) (i : ι) (hi : v i ≠ 0) :
    ∃ A : Finset ι, i ∈ A ∧ IsNormalBasis (K := K) v A := by
  classical
  have h : LinearIndepOn K v ({i} : Set ι) := by
    exact LinearIndepOn.singleton hi
  let A := h.extend (Set.subset_univ _)
  refine ⟨A.toFinset, ?_, ?_, ?_⟩
  · exact Set.mem_toFinset.mpr (h.subset_extend (Set.subset_univ _) (Set.mem_singleton i))
  · simpa only [Set.coe_toFinset] using h.linearIndepOn_extend (Set.subset_univ _)
  · simpa only [Set.coe_toFinset, Set.image_univ, A] using
      (h.span_image_extend_eq_span_image (Set.subset_univ _)).trans (by simpa using hv)

lemma IsNormalBasis.ne_zero [DecidableEq ι] {v : ι → V} {A : Finset ι}
    (hA : IsNormalBasis (K := K) v A) {i : ι} (hi : i ∈ A) : v i ≠ 0 :=
  hA.1.ne_zero hi

lemma exists_normalBasis_omitting [Fintype ι] (v : ι → V) (i : ι)
    (h : span K (v '' {j | j ≠ i}) = ⊤) :
    ∃ A : Finset ι, i ∉ A ∧ IsNormalBasis (K := K) v A := by
  obtain ⟨A, hA, hB⟩ := exists_normalBasis_subset v {j | j ≠ i} h
  exact ⟨A, fun hi => hA hi rfl, hB⟩

lemma mandatory_not_mem_span [Fintype ι] (v : ι → V)
    (hv : span K (Set.range v) = ⊤) (i : ι)
    (hi : ∀ A, IsNormalBasis (K := K) v A → i ∈ A) :
    v i ∉ span K (v '' {j | j ≠ i}) := by
  intro hmem
  have hspan : span K (v '' {j | j ≠ i}) = ⊤ := by
    apply top_unique
    rw [← hv]
    apply span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · subst j
      exact hmem
    · exact subset_span ⟨j, hj, rfl⟩
  obtain ⟨A, hAi, hA⟩ := exists_normalBasis_omitting v i hspan
  exact hAi (hi A hA)

lemma IsNormalBasis.card_eq {v : ι → V} {A : Finset ι}
    (hA : IsNormalBasis (K := K) v A) : A.card = Module.finrank K V := by
  classical
  have hli : LinearIndependent K (fun i : A => v i) := hA.1
  let b : Basis A K V := Basis.mk hli (by
    have hr : Set.range (fun i : A => v i) = v '' (A : Set ι) := by
      ext x
      simp
    rw [hr, hA.2])
  exact (Module.finrank_eq_card_finset_basis b).symm

variable {W : Type*} [AddCommGroup W] [Module K W]

lemma mandatory_coordinate_eq_zero [Fintype ι] (b : Basis ι K V) (q : V →ₗ[K] W)
    (hq : span K (Set.range (fun j => q (b j))) = ⊤) (i : ι)
    (hi : ∀ A, IsNormalBasis (K := K) (fun j => q (b j)) A → i ∈ A)
    (t : V) (ht : q t = 0) : b.repr t i = 0 := by
  classical
  by_contra hti
  let S : Submodule K W := span K ((fun j => q (b j)) '' {j | j ≠ i})
  have hsum : (∑ j ∈ Finset.univ.erase i, b.repr t j • q (b j)) ∈ S := by
    apply S.sum_mem
    intro j hj
    exact S.smul_mem _ (subset_span ⟨j, (Finset.mem_erase.mp hj).1, rfl⟩)
  have hall : (∑ j, b.repr t j • q (b j)) = 0 := by
    calc
      _ = q (∑ j, b.repr t j • b j) := by simp only [map_sum, map_smul]
      _ = 0 := by rw [b.sum_repr, ht]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hall
  have hterm : b.repr t i • q (b i) ∈ S := by
    have heq : b.repr t i • q (b i) = -(∑ j ∈ Finset.univ.erase i,
        b.repr t j • q (b j)) := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hall)
    rw [heq]
    exact S.neg_mem hsum
  exact mandatory_not_mem_span (fun j => q (b j)) hq i hi
    ((S.smul_mem_iff hti).mp hterm)

lemma largest_nontangent_mandatory {m : ℕ}
    (u v : Fin (m + 1) → V) (hu : span K (Set.range u) = ⊤)
    (hvu : ∀ i, i ≠ 0 → v i = u i)
    (hexclude : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := K) u A → IsNormalBasis (K := K) v B →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False)
    (i : Fin (m + 1)) (hi0 : i ≠ 0) (hi : u i ≠ 0)
    (hlarge : ∀ j, i < j → u j = 0)
    (B : Finset (Fin (m + 1))) (hB : IsNormalBasis (K := K) v B) : i ∈ B := by
  classical
  obtain ⟨A, hiA, hA⟩ := exists_normalBasis_containing u hu i hi
  by_contra hiB
  apply hexclude A B hA hB i hi0 hiA hiB
  intro j hj
  have hj0 : j ≠ 0 := by
    intro h
    subst j
    exact (not_lt_of_ge (Fin.zero_le _)) hj
  have hjA : j ∉ A := fun h => hA.ne_zero h (hlarge j hj)
  have hjB : j ∉ B := fun h => hB.ne_zero h ((hvu j hj0).trans (hlarge j hj))
  simp only [hjA, hjB]

lemma weighted_normalBasis_exclusion {m : ℕ}
    (u v : Fin (m + 1) → V) (w cost : Fin (m + 1) → ℝ) (C : ℝ)
    (hcomparison : ∀ A B, IsNormalBasis (K := K) u A →
      IsNormalBasis (K := K) v B → (∏ j ∈ A, w j) ≤ C * ∏ j ∈ B, cost j)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      C * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j)
    (A B : Finset (Fin (m + 1)))
    (hA : IsNormalBasis (K := K) u A) (hB : IsNormalBasis (K := K) v B)
    (i : Fin (m + 1)) (hi0 : i ≠ 0) (hiA : i ∈ A) (hiB : i ∉ B)
    (hlarge : ∀ j, i < j → (j ∈ A ↔ j ∈ B)) : False := by
  exact (not_lt_of_ge (hcomparison A B hA hB))
    (hseparated A B (hA.card_eq.trans hB.card_eq.symm) i hi0 hiA hiB hlarge)

end PiExponent.NormalBasisRigidity

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_NormalFrameBasis
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.NormalBasisRigidity
open Module

variable {K : Type*} [Field K] (m : ℕ) (y : K) (hy : y ≠ 0)

variable {V : Type*} [AddCommGroup V] [Module K V]

lemma mandatory_logarithmic_differential (q : (Fin (m + 1) → K) →ₗ[K] V)
    (hq : Submodule.span K (Set.range (fun j => q (frameBasis m y hy j))) = ⊤)
    (i : Fin m)
    (hi : ∀ A, IsNormalBasis (K := K) (fun j => q (frameBasis m y hy j)) A → i.succ ∈ A)
    (t : Fin (m + 1) → K) (ht : q t = 0) : t i.succ = t 0 / y := by
  have h := mandatory_coordinate_eq_zero (frameBasis m y hy) q hq i.succ hi t ht
  rw [frameBasis_repr_succ] at h
  exact sub_eq_zero.mp h

lemma span_mapped_basis_eq_top {ι U : Type*} [Fintype ι]
    [AddCommGroup U] [Module K U] (b : Basis ι K U) (q : U →ₗ[K] V)
    (hq : Function.Surjective q) :
    Submodule.span K (Set.range (fun j => q (b j))) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨t, rfl⟩ := hq x
  rw [← b.sum_repr t, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

theorem normal_basis_differential_dichotomy
    (q : (Fin (m + 1) → K) →ₗ[K] V) (hq : Function.Surjective q) (hq0 : q ≠ 0)
    (hexclude : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := K) (fun j => q (Pi.basisFun K _ j)) A →
      IsNormalBasis (K := K) (fun j => q (frameBasis m y hy j)) B →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    (∀ t, q t = 0 → t 0 = 0) ∨
      ∃ i : Fin m, ∀ t, q t = 0 → t i.succ = t 0 / y := by
  classical
  let b := Pi.basisFun K (Fin (m + 1))
  let S := Finset.univ.filter (fun i : Fin (m + 1) => i ≠ 0 ∧ q (b i) ≠ 0)
  by_cases hS : S.Nonempty
  · let i := S.max' hS
    have hiS : i ∈ S := Finset.max'_mem _ _
    have hi := (Finset.mem_filter.mp hiS).2
    have hlarge : ∀ j, i < j → q (b j) = 0 := by
      intro j hj
      by_contra hjq
      have hj0 : j ≠ 0 := by
        intro hz
        subst j
        exact (not_lt_of_ge (Fin.zero_le _)) hj
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0, hjq⟩
      exact (not_lt_of_ge (Finset.le_max' _ _ hjS)) hj
    have hvu : ∀ j : Fin (m + 1), j ≠ 0 → q (frameBasis m y hy j) = q (b j) := by
      intro j
      refine Fin.cases ?_ (fun k _ => ?_) j
      · intro hz
        exact (hz rfl).elim
      · rw [frameBasis_succ]
    have hmand : ∀ B, IsNormalBasis (K := K) (fun j => q (frameBasis m y hy j)) B → i ∈ B :=
      largest_nontangent_mandatory (fun j => q (b j))
        (fun j => q (frameBasis m y hy j)) (span_mapped_basis_eq_top b q hq)
        hvu hexclude i hi.1 hi.2 hlarge
    rcases Fin.eq_zero_or_eq_succ i with hz | ⟨j, hj⟩
    · exact (hi.1 hz).elim
    · right
      refine ⟨j, ?_⟩
      intro t ht
      apply mandatory_logarithmic_differential m y hy q
        (span_mapped_basis_eq_top (frameBasis m y hy) q hq) j ?_ t ht
      intro B hB
      rw [← hj]
      exact hmand B hB
  · have hpos : ∀ j : Fin m, q (b j.succ) = 0 := by
      intro j
      by_contra hj
      exact hS ⟨j.succ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.succ_ne_zero _, hj⟩⟩
    have he0 : q (b 0) ≠ 0 := by
      intro he
      apply hq0
      apply b.ext
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact he
      · exact hpos k
    have hqform (t : Fin (m + 1) → K) : q t = t 0 • q (b 0) := by
      calc
        q t = q (∑ j, b.repr t j • b j) := congrArg q (b.sum_repr t).symm
        _ = ∑ j, b.repr t j • q (b j) := by simp only [map_sum, map_smul]
        _ = t 0 • q (b 0) := by
          rw [Fin.sum_univ_succ]
          simp only [hpos, smul_zero, Finset.sum_const_zero, add_zero]
          simp only [b, Pi.basisFun_repr]
    left
    intro t ht
    rw [hqform] at ht
    exact (smul_eq_zero.mp ht).resolve_right he0

end PiExponent.NormalBasisRigidity

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_PolynomialTangentDifferential
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open MvPolynomial KaehlerDifferential

section PolynomialMap
variable {C E ι : Type*} [Field C] [Field E] [Algebra C E] [Fintype ι]

theorem derivation_polynomial_map (φ : MvPolynomial ι C →ₐ[C] E)
    (d : Derivation C E E) (p : MvPolynomial ι C) :
    d (φ p) = ∑ i, φ (pderiv i p) * d (φ (X i)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, hp,
      map_add, pderiv_X, Finset.sum_add_distrib, add_mul, mul_assoc]
    simp only [← Finset.mul_sum]
    simp [Pi.single_apply, mul_comm]

theorem derivation_mem_polynomialTangent (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) (hQ : ∀ p ∈ Q, φ p = 0)
    (d : Derivation C E E) :
    (fun i => d (φ (X i))) ∈ polynomialTangent φ Q := by
  change polynomialJacobian φ Q (fun i => d (φ (X i))) = 0
  ext p
  change (∑ i, φ (pderiv i p.1) * d (φ (X i))) = 0
  rw [← derivation_polynomial_map, hQ p.1 p.2, map_zero]

theorem logarithmic_differential_of_polynomialTangent
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p ∈ Q, φ p = 0) (i j : ι)
    (h : ∀ t ∈ polynomialTangent φ Q, t i = t j / φ (X j)) :
    D C E (φ (X i)) = (φ (X j))⁻¹ • D C E (φ (X j)) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff E _).mp
  intro l
  let d : Derivation C E E := l.compDer (D C E)
  have hd := h (fun i => d (φ (X i))) (derivation_mem_polynomialTangent φ Q hQ d)
  change l (D C E (φ (X i))) = l (D C E (φ (X j))) / φ (X j) at hd
  simpa only [map_sub, map_smul, smul_eq_mul, div_eq_mul_inv,
    sub_eq_zero, mul_comm] using hd

theorem differential_eq_zero_of_polynomialTangent
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p ∈ Q, φ p = 0) (i : ι)
    (h : ∀ t ∈ polynomialTangent φ Q, t i = 0) :
    D C E (φ (X i)) = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff E _).mp
  intro l
  let d : Derivation C E E := l.compDer (D C E)
  exact h (fun i => d (φ (X i))) (derivation_mem_polynomialTangent φ Q hQ d)

end PolynomialMap

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialNormalNonzero
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

open MvPolynomial

theorem totalDegree_pderiv_lt_of_ne_zero
    {C ι : Type*} [CommSemiring C] (p : MvPolynomial ι C) (i : ι)
    (hp : pderiv i p ≠ 0) : (pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hshift (d : ι →₀ ℕ) (hd : d ∈ (pderiv i p).support) :
      d + Finsupp.single i 1 ∈ p.support := by
    apply mem_support_iff.mpr
    intro hz
    have hh := mem_support_iff.mp hd
    apply hh
    rw [coeff_pderiv, hz, zero_mul]
  have hdegree (d : ι →₀ ℕ) (hd : d ∈ (pderiv i p).support) :
      d.sum (fun _ e => e) < p.totalDegree := by
    have hh := le_totalDegree (hshift d hd)
    have he : (d + Finsupp.single i 1).sum (fun _ e => e) =
        d.sum (fun _ e => e) + 1 := by
      rw [Finsupp.sum_add_index']
      · simp
      · intro; rfl
      · intros; rfl
    rw [he] at hh
    omega
  have hpos : 0 < p.totalDegree := by
    obtain ⟨d, hd⟩ := (MvPolynomial.support_nonempty.mpr hp)
    exact (Nat.zero_le _).trans_lt (hdegree d hd)
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hpos]
  exact hdegree

theorem eq_constant_of_pderiv_eq_zero
    {C ι : Type*} [Field C] [CharZero C] (p : MvPolynomial ι C)
    (hp : ∀ i, pderiv i p = 0) : p = MvPolynomial.C (p.coeff 0) := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d
    simp
  · have hex : ∃ i, d i ≠ 0 := by
      by_contra! hh
      exact hd (by ext i; exact hh i)
    obtain ⟨i, hi⟩ := hex
    have he : d - Finsupp.single i 1 + Finsupp.single i 1 = d :=
      Finsupp.sub_add_single_one_cancel hi
    have hh := congrArg (fun q : MvPolynomial ι C =>
      q.coeff (d - Finsupp.single i 1)) (hp i)
    rw [coeff_pderiv, he] at hh
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hh
    have hfactor : (((d i - 1 : ℕ) : C) + 1) ≠ 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (d i - 1)) :
          (((d i - 1 + 1 : ℕ) : C)) ≠ 0)
    have hc : p.coeff d = 0 := (mul_eq_zero.mp hh).resolve_right hfactor
    simpa [coeff_C, Ne.symm hd] using hc

theorem ideal_eq_bot_of_pderiv_stable
    {C ι : Type*} [Field C] [CharZero C] (Q : Ideal (MvPolynomial ι C))
    (hproper : Q ≠ ⊤) (hstable : ∀ p ∈ Q, ∀ i, pderiv i p ∈ Q) : Q = ⊥ := by
  have hall : ∀ n : ℕ, ∀ p : MvPolynomial ι C,
      p.totalDegree = n → p ∈ Q → p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hdegree hp
      have hderiv : ∀ i, pderiv i p = 0 := by
        intro i
        by_contra hn
        have hlt := totalDegree_pderiv_lt_of_ne_zero p i hn
        rw [hdegree] at hlt
        exact hn (ih _ hlt _ rfl (hstable p hp i))
      have hc := eq_constant_of_pderiv_eq_zero p hderiv
      have hcoeff : p.coeff 0 = 0 := by
        by_contra hne
        have hunit : IsUnit (MvPolynomial.C (p.coeff 0) : MvPolynomial ι C) :=
          (isUnit_iff_ne_zero.mpr hne).map (MvPolynomial.C : C →+* MvPolynomial ι C)
        have hmem : MvPolynomial.C (p.coeff 0) ∈ Q := by rw [← hc]; exact hp
        exact hproper (Q.eq_top_of_isUnit_mem hmem hunit)
      simpa [hcoeff] using hc
  apply le_antisymm
  · intro p hp
    exact Ideal.mem_bot.mpr (hall p.totalDegree p rfl hp)
  · exact bot_le

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GenericNormalRigidity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent
open Module MvPolynomial NormalBasisRigidity

variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

theorem polynomialNormal_mkQ_ne_zero_of_kernel
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥) :
    (polynomialTangent φ Q).mkQ ≠ 0 := by
  classical
  intro hzero
  have htop : polynomialTangent φ Q = ⊤ := by
    rw [← Submodule.ker_mkQ (polynomialTangent φ Q), hzero, LinearMap.ker_zero]
  apply hQ
  apply ideal_eq_bot_of_pderiv_stable Q
  · intro h
    have hh := (hker 1).mpr (by rw [h]; trivial)
    exact (one_ne_zero : (1 : E) ≠ 0) (by simpa only [map_one] using hh)
  · intro p hp i
    apply (hker _).mp
    have ht : (Pi.single i 1 : ι → E) ∈ polynomialTangent φ Q := by rw [htop]; trivial
    change polynomialJacobian φ Q (Pi.single i 1) = 0 at ht
    have hh := congrFun ht ⟨p, hp⟩
    simpa [polynomialJacobian, Pi.single_apply] using hh

theorem constant_zeroth_coordinate_of_generic_normal_separation
    [IsAlgClosed C] [Algebra.EssFiniteType C E] {m : ℕ}
    (φ : MvPolynomial (Fin (m + 1)) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥)
    (hy : φ (X (0 : Fin (m + 1))) ≠ 0)
    (hexclude : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := E)
        (fun j => (polynomialTangent φ Q).mkQ (Pi.basisFun E _ j)) A →
      IsNormalBasis (K := E)
        (fun j => (polynomialTangent φ Q).mkQ (frameBasis m (φ (X 0)) hy j)) B →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    ∃ c : C, X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ Q := by
  let q := (polynomialTangent φ Q).mkQ
  have hvan : ∀ p ∈ Q, φ p = 0 := fun p hp => (hker p).mpr hp
  have hd := normal_basis_differential_dichotomy m (φ (X 0)) hy q
    (Submodule.mkQ_surjective _) (polynomialNormal_mkQ_ne_zero_of_kernel φ Q hker hQ) hexclude
  have hconst : ∃ c : C, algebraMap C E c = φ (X (0 : Fin (m + 1))) := by
    rcases hd with hzero | ⟨i, hlog⟩
    · exact constant_of_differential_eq_zero (φ (X 0))
        (differential_eq_zero_of_polynomialTangent φ Q hvan 0
          (fun t ht => hzero t ((Submodule.Quotient.mk_eq_zero _).mpr ht)))
    · exact constant_of_logarithmic_differential (φ (X i.succ)) (φ (X 0))
        (logarithmic_differential_of_polynomialTangent φ Q hvan i.succ 0
          (fun t ht => hlog t ((Submodule.Quotient.mk_eq_zero _).mpr ht)))
  obtain ⟨c, hc⟩ := hconst
  refine ⟨c, (hker _).mp ?_⟩
  simp only [map_sub, MvPolynomial.algHom_C, hc, sub_self]

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_PersistentComponents
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.PersistentComponents

variable {R : Type*} [CommRing R]

theorem prime_height_step {P Q : Ideal R} (hP : P.IsPrime) (hQ : Q.IsPrime)
    (hPQ : P < Q) : P.height + 1 ≤ Q.height := by
  let := hP
  let := hQ
  exact Ideal.height_add_one_le_of_lt_of_isPrime hPQ

theorem exists_adjacent_eq_of_height_bound (P : ℕ → Ideal R) (m : ℕ)
    (hPrime : ∀ i ≤ m + 1, (P i).IsPrime)
    (hstep : ∀ i ≤ m, P i ≤ P (i + 1))
    (hheight : (P (m + 1)).height ≤ m) :
    ∃ i ≤ m, P i = P (i + 1) := by
  by_contra h
  have hneq : ∀ i ≤ m, P i ≠ P (i + 1) := by simpa only [not_exists, not_and] using h
  have hgrowth : ∀ i ≤ m + 1, (i : ℕ∞) ≤ (P i).height := by
    intro i hi
    induction i with
    | zero => exact bot_le
    | succ i ih =>
      have him : i ≤ m := by omega
      have hip : i ≤ m + 1 := by omega
      have hs := prime_height_step (hPrime i hip) (hPrime (i + 1) hi)
        (lt_of_le_of_ne (hstep i him) (hneq i him))
      have hadd : (i : ℕ∞) + 1 ≤ (P i).height + 1 := by
        gcongr
        exact ih hip
      simpa only [Nat.cast_add, Nat.cast_one] using hadd.trans hs
  have hf := (hgrowth (m + 1) le_rfl).trans hheight
  exact (by exact_mod_cast (Nat.not_succ_le_self m) : ¬ ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞)) hf

theorem exists_nested_minimalPrimes (I : ℕ → Ideal R) (hI : Monotone I)
    (n : ℕ) (P : Ideal R) (hP : P.IsPrime) (hIP : I n ≤ P) :
    ∃ Q : ℕ → Ideal R,
      (∀ i ≤ n, Q i ∈ (I i).minimalPrimes) ∧
      (∀ i < n, Q i ≤ Q (i + 1)) ∧ Q n ≤ P := by
  induction n generalizing P with
  | zero =>
    let := hP
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hIP
    refine ⟨fun _ => Q, ?_, ?_, hQP⟩
    · intro i hi
      have hi0 : i = 0 := by omega
      simpa only [hi0] using hQ
    · intro i hi
      omega
  | succ n ih =>
    let := hP
    obtain ⟨Qlast, hQlast, hQlastP⟩ := Ideal.exists_minimalPrimes_le hIP
    obtain ⟨Q, hQ, hstep, hQlastle⟩ :=
      ih Qlast hQlast.isPrime ((hI (Nat.le_succ n)).trans hQlast.le)
    refine ⟨fun i => if i = n + 1 then Qlast else Q i, ?_, ?_, ?_⟩
    · intro i hi
      by_cases hei : i = n + 1
      · simpa [hei] using hQlast
      · simpa [hei] using hQ i (by omega)
    · intro i hi
      have hin : i ≠ n + 1 := by omega
      by_cases hei : i = n
      · simpa [hei] using hQlastle
      · have hip : i + 1 ≠ n + 1 := by omega
        simpa [hin, hip, hei] using hstep i (by omega)
    · simpa [Nat.succ_eq_add_one] using hQlastP

theorem exists_persistent_minimalPrime (I : ℕ → Ideal R) (hI : Monotone I)
    (m : ℕ) (P : Ideal R) (hP : P.IsPrime)
    (hIP : I (m + 2) ≤ P) (hheight : P.height ≤ m) :
    ∃ r < m + 2, ∃ Q : Ideal R,
      Q ∈ (I r).minimalPrimes ∧ I (r + 1) ≤ Q ∧ Q ≤ P := by
  obtain ⟨Q, hQ, hstep, hQP⟩ := exists_nested_minimalPrimes I hI (m + 2) P hP hIP
  have hmono : ∀ i j, i ≤ j → j ≤ m + 2 → Q i ≤ Q j := by
    intro i j hij hj
    induction j with
    | zero =>
      have hi : i = 0 := by omega
      simp only [hi, le_refl]
    | succ j ih =>
      by_cases heq : i = j + 1
      · simp [heq]
      · exact (ih (by omega) (by omega)).trans (hstep j (by omega))
  have hbound : (Q (m + 1)).height ≤ m :=
    (Ideal.height_mono ((hmono (m + 1) (m + 2) (by omega) le_rfl).trans hQP)).trans hheight
  obtain ⟨r, hr, heq⟩ := exists_adjacent_eq_of_height_bound Q m
    (fun i hi => (hQ i (by omega)).isPrime) (fun i hi => hstep i (by omega)) hbound
  refine ⟨r, by omega, Q r, hQ r (by omega), ?_, ?_⟩
  · rw [heq]
    exact (hQ (r + 1) (by omega)).le
  · exact (hmono r (m + 2) (by omega) le_rfl).trans hQP

theorem minimalPrime_persists {I J Q : Ideal R} (hIJ : I ≤ J)
    (hQ : Q ∈ I.minimalPrimes) (hJQ : J ≤ Q) : Q ∈ J.minimalPrimes := by
  refine ⟨⟨hQ.isPrime, hJQ⟩, ?_⟩
  intro P hP hPQ
  exact hQ.2 ⟨hP.1, hIJ.trans hP.2⟩ hPQ

theorem exists_persistent_minimalPrime_pair (I : ℕ → Ideal R) (hI : Monotone I)
    (m : ℕ) (P : Ideal R) (hP : P.IsPrime)
    (hIP : I (m + 2) ≤ P) (hheight : P.height ≤ m) :
    ∃ r < m + 2, ∃ Q : Ideal R,
      Q ∈ (I r).minimalPrimes ∧ Q ∈ (I (r + 1)).minimalPrimes ∧ Q ≤ P := by
  obtain ⟨r, hr, Q, hQ, hnext, hQP⟩ :=
    exists_persistent_minimalPrime I hI m P hP hIP hheight
  exact ⟨r, hr, Q, hQ, minimalPrime_persists (hI (Nat.le_succ r)) hQ hnext, hQP⟩

theorem minimalPrime_height_pos_of_nonzero_mem [IsDomain R] {I Q : Ideal R}
    (hQ : Q ∈ I.minimalPrimes) {F : R} (hF : F ≠ 0) (hFI : F ∈ I) :
    1 ≤ Q.height := by
  have hQbot : Q ≠ ⊥ := by
    intro h
    have hFQ := hQ.le hFI
    simp only [h, Ideal.mem_bot] at hFQ
    exact hF hFQ
  exact Order.one_le_iff_ne_zero.mpr (mt Ideal.height_eq_zero_iff_eq_bot.mp hQbot)

theorem exists_persistent_component_positive_height [IsDomain R]
    (I : ℕ → Ideal R) (hI : Monotone I) (m : ℕ) (P : Ideal R) (hP : P.IsPrime)
    (hIP : I (m + 2) ≤ P) (hheight : P.height ≤ m)
    {F : R} (hF : F ≠ 0) (hFI : F ∈ I 0) :
    ∃ r < m + 2, ∃ Q : Ideal R,
      Q ∈ (I r).minimalPrimes ∧ Q ∈ (I (r + 1)).minimalPrimes ∧ Q ≤ P ∧
      1 ≤ Q.height ∧ Q.height ≤ m := by
  obtain ⟨r, hr, Q, hQr, hQnext, hQP⟩ :=
    exists_persistent_minimalPrime_pair I hI m P hP hIP hheight
  exact ⟨r, hr, Q, hQr, hQnext, hQP,
    minimalPrime_height_pos_of_nonzero_mem hQr hF ((hI (Nat.zero_le r)) hFI),
    (Ideal.height_mono hQP).trans hheight⟩

end PiExponent.PersistentComponents

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContact
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox

noncomputable section

theorem frameWord_mem_derivativeIdeal {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (bound : ℝ) (F : FramePolynomial m) (word : List (Fin (m + 1)))
    (hword : frameWordCost cost word ≤ bound) :
    polynomialFrameWord m word F ∈ frameDerivativeIdeal cost bound F :=
  Ideal.subset_span ⟨word, hword, rfl⟩

theorem frameDerivativeIdeal_mono {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (F : FramePolynomial m) {a b : ℝ} (hab : a ≤ b) :
    frameDerivativeIdeal cost a F ≤ frameDerivativeIdeal cost b F := by
  apply Ideal.span_mono
  intro g hg
  obtain ⟨word, hword, rfl⟩ := hg
  exact ⟨word, hword.trans hab, rfl⟩

theorem polynomial_mem_frameDerivativeIdeal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (bound : ℝ) (F : FramePolynomial m)
    (hbound : 0 ≤ bound) : F ∈ frameDerivativeIdeal cost bound F :=
  frameWord_mem_derivativeIdeal cost bound F [] hbound

theorem polynomialFrame_mem_derivativeIdeal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (bound : ℝ) (F p : FramePolynomial m) (i : Fin (m + 1))
    (hp : p ∈ frameDerivativeIdeal cost bound F) :
    polynomialFrame m i p ∈ frameDerivativeIdeal cost (bound + cost i) F := by
  let I := frameDerivativeIdeal cost (bound + cost i) F
  have hle : frameDerivativeIdeal cost bound F ≤
      polynomialDerivativeCore (polynomialFrame m i) I := by
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨word, hword, rfl⟩ := hg
    refine ⟨?_, ?_⟩
    · exact frameWord_mem_derivativeIdeal cost (bound + cost i) F word
        (hword.trans (le_add_of_nonneg_right (hcost i)))
    · exact frameWord_mem_derivativeIdeal cost (bound + cost i) F (i :: word)
        (by simpa only [frameWordCost_cons, add_comm] using add_le_add_left hword (cost i))
  exact (hle hp).2

theorem polynomialFrameWord_mem_derivativeIdeal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (bound : ℝ) (F p : FramePolynomial m) (word : List (Fin (m + 1)))
    (hp : p ∈ frameDerivativeIdeal cost bound F) :
    polynomialFrameWord m word p ∈
      frameDerivativeIdeal cost (bound + frameWordCost cost word) F := by
  induction word with
  | nil => simpa only [polynomialFrameWord_nil, frameWordCost_nil, add_zero] using hp
  | cons i word ih =>
      have h := polynomialFrame_mem_derivativeIdeal cost hcost
        (bound + frameWordCost cost word) F (polynomialFrameWord m word p) i ih
      simpa only [polynomialFrameWord_cons, frameWordCost_cons, add_assoc,
        add_comm (frameWordCost cost word) (cost i)] using h

theorem derivative_vanishes_on_persistent_ideal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (bound delta : ℝ) (F p : FramePolynomial m)
    (P : Ideal (FramePolynomial m))
    (hp : p ∈ frameDerivativeIdeal cost bound F)
    (hpersist : frameDerivativeIdeal cost (bound + delta) F ≤ P)
    (word : List (Fin (m + 1))) (hword : frameWordCost cost word ≤ delta) :
    polynomialFrameWord m word p ∈ P := by
  apply hpersist
  have hbound : bound + frameWordCost cost word ≤ bound + delta := by linarith
  exact frameDerivativeIdeal_mono cost F hbound
    (polynomialFrameWord_mem_derivativeIdeal cost hcost bound F p word hp)

theorem frameDerivativeIdeal_levels_monotone {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (F : FramePolynomial m) :
    Monotone (fun r : ℕ => frameDerivativeIdeal cost ((r : ℝ) * delta) F) := by
  intro a b hab
  apply frameDerivativeIdeal_mono
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hab) hdelta

theorem exists_persistent_frame_component {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (delta : ℝ) (hdelta : 0 ≤ delta) (F : FramePolynomial m) (hF : F ≠ 0)
    (P : Ideal (FramePolynomial m)) (hP : P.IsPrime) (hheight : P.height ≤ m)
    (hvanish : ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ ((m : ℝ) + 2) * delta →
        polynomialFrameWord m word F ∈ P) :
    ∃ r < m + 2, ∃ Q : Ideal (FramePolynomial m),
      Q ∈ (frameDerivativeIdeal cost ((r : ℝ) * delta) F).minimalPrimes ∧
      Q ∈ (frameDerivativeIdeal cost (((r : ℝ) + 1) * delta) F).minimalPrimes ∧
      Q ≤ P ∧ 1 ≤ Q.height ∧ Q.height ≤ m ∧
      ∀ p ∈ frameDerivativeIdeal cost ((r : ℝ) * delta) F,
        ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ delta →
          polynomialFrameWord m word p ∈ Q := by
  let I : ℕ → Ideal (FramePolynomial m) :=
    fun r => frameDerivativeIdeal cost ((r : ℝ) * delta) F
  have hI : Monotone I := frameDerivativeIdeal_levels_monotone cost delta hdelta F
  have htop : I (m + 2) ≤ P := by
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨word, hword, rfl⟩ := hg
    apply hvanish word
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hword
  have hinitial : F ∈ I 0 := by
    simpa only [I, Nat.cast_zero, zero_mul] using
      polynomial_mem_frameDerivativeIdeal cost 0 F (le_refl 0)
  obtain ⟨r, hr, Q, hQr, hQnext, hQP, hQlo, hQhi⟩ :=
    PiExponent.PersistentComponents.exists_persistent_component_positive_height
      I hI m P hP htop hheight hF hinitial
  refine ⟨r, hr, Q, hQr, ?_, hQP, hQlo, hQhi, ?_⟩
  · simpa only [I, Nat.cast_add, Nat.cast_one] using hQnext
  · intro p hp word hword
    apply derivative_vanishes_on_persistent_ideal cost hcost
      ((r : ℝ) * delta) delta F p Q hp
    · have hb : (r : ℝ) * delta + delta = ((r + 1 : ℕ) : ℝ) * delta := by
        push_cast
        ring
      rw [hb]
      exact hQnext.le
    · exact hword

end
end PiExponentApprox

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveComponentRigidity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveComponentRigidity

open scoped BigOperators
open PiExponentApprox NormalBasisRigidity

theorem coordinate_constant_of_persistent_comparison_q68_oai {m : ℕ}
    (w cost : Fin (m + 1) → ℝ) (M delta : ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (hdelta : 0 ≤ delta)
    (F : FramePolynomial m) (hF : F ≠ 0)
    (P : Ideal (FramePolynomial m)) (hP : P.IsPrime) (hheight : P.height ≤ m)
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (hvanish : ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ ((m : ℝ) + 2) * delta → polynomialFrameWord m word F ∈ P)
    (hcomparison : PersistentNormalComparison w cost M delta F P hY)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      M * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∃ c : ℂ, MvPolynomial.X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ P := by
  obtain ⟨r, hr, Q, hQr, hQnext, hQP, hQlo, hQhi, hpersist⟩ :=
    exists_persistent_frame_component cost hcost delta hdelta F hF P hP hheight hvanish
  let : Q.IsPrime := hQr.isPrime
  have hYQ : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q := fun h => hY (hQP h)
  have hFQ : F ∈ Q := hQr.le
    (polynomial_mem_frameDerivativeIdeal cost ((r : ℝ) * delta) F
      (mul_nonneg (Nat.cast_nonneg r) hdelta))
  have hQ0 : Q ≠ ⊥ := by
    intro h
    exact hF (by simpa only [h, Ideal.mem_bot] using hFQ)
  have hcomp := hcomparison r hr Q inferInstance hQP hQr hQnext hQlo hQhi hpersist
  let : Algebra.EssFiniteType ℂ Q.ResidueField :=
    Algebra.EssFiniteType.comp ℂ (FramePolynomial m) Q.ResidueField
  have hker (p : FramePolynomial m) : primeResidueMap Q p = 0 ↔ p ∈ Q :=
    Ideal.algebraMap_residueField_eq_zero
  obtain ⟨c, hc⟩ := constant_zeroth_coordinate_of_generic_normal_separation
    (primeResidueMap Q) Q hker hQ0 (residueY_ne_zero Q hYQ)
    (weighted_normalBasis_exclusion _ _ w cost M hcomp hseparated)
  exact ⟨c, hQP hc⟩

end PiExponent.CurveComponentRigidity
end

end OAI
end

theorem solution : type_of% @OAI.PiExponent.CurveComponentRigidity.coordinate_constant_of_persistent_comparison_q68_oai := @OAI.PiExponent.CurveComponentRigidity.coordinate_constant_of_persistent_comparison_q68_oai
