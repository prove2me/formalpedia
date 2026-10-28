-- Prove2me | solution 1 for OAI.PiExponent.CoordinateSliceComparison.sliceFamily_mem_minimalPrimes_of_normalBasis_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:04:58.050348+00:00
-- url     : https://prove2.me/submissions/c322b13c-243f-4210-8b60-75cb18251b9b

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

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoordinateFiniteSlice
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CoordinateFiniteSlice

open PiExponentJets.PolynomialLocalResidueResolution

variable {K ι : Type*} [Field K]

theorem complementary_transcendenceBasis
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hB : IsTranscendenceBasis K (fun i : {i // i ∉ A} =>
      algebraMap (MvPolynomial ι K) Q.ResidueField (MvPolynomial.X i.val))) :
    IsTranscendenceBasis K (fun i : {i // i ∉ A} =>
      algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inr i))) := by
  simpa only [Function.comp_def, residueEquiv_coordinate_inr] using (residueEquiv Q A).isTranscendenceBasis hB

theorem splitPrime_mem_minimalPrimes
    (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hQ : Q ∈ I.minimalPrimes) :
    splitPrime Q A ∈ (I.map (coordinateRenaming (K := K) A).toRingHom).minimalPrimes := by
  rw [Ideal.minimalPrimes_map_of_surjective (f := (coordinateRenaming (K := K) A).toRingHom)
    (coordinateRenaming (K := K) A).surjective]
  have hk : RingHom.ker (coordinateRenaming (K := K) A).toRingHom = ⊥ := by
    ext p
    change coordinateRenaming (K := K) A p = 0 ↔ p = 0
    exact (coordinateRenaming (K := K) A).map_eq_zero_iff
  rw [hk, sup_bot_eq]
  exact ⟨Q, hQ, rfl⟩

theorem residueEquiv_symm_coordinate_inl
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : Fin A.card) :
    (residueEquiv Q A).symm
      (algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inl i))) =
      slicePoint Q A i := by
  apply (residueEquiv Q A).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (residueEquiv_coordinate_inl Q A i).symm

theorem residueEquiv_symm_coordinate_inr
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : {i // i ∉ A}) :
    (residueEquiv Q A).symm
      (algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inr i))) =
      residueCoordinates Q i.val := by
  apply (residueEquiv Q A).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (residueEquiv_coordinate_inr Q A i).symm

end PiExponent.CoordinateFiniteSlice

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_SeparablePointLength
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.RamifiedLocalLength.translatedPowerLocalMap_isLocalHom _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.SeparablePointLength

open IsLocalRing TensorProduct

variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coefficientExtension_finite [Module.Finite K E] :
    Module.Finite (MvPolynomial ι K) (MvPolynomial ι E) :=
  Module.Finite.equiv (coefficientBaseChangeEquiv (K := K) (E := E) (ι := ι)).toLinearEquiv

theorem contractedPoint_eq_ker (b : ι → E) :
    contractedPoint (K := K) b = RingHom.ker (MvPolynomial.aeval b).toRingHom := by
  ext p
  change MvPolynomial.aeval b (MvPolynomial.map (algebraMap K E) p) = 0 ↔
    MvPolynomial.aeval b p = 0
  simp [MvPolynomial.aeval_def]

theorem point_mem_minimalPrimes_map [Module.Finite K E]
    (b : ι → E) (I : Ideal (MvPolynomial ι K))
    (hminimal : contractedPoint (K := K) b ∈ I.minimalPrimes) :
    WeightedBezout.pointIdeal b ∈
      (I.map (MvPolynomial.map (algebraMap K E))).minimalPrimes := by
  let : Module.Finite (MvPolynomial ι K) (MvPolynomial ι E) := coefficientExtension_finite
  change WeightedBezout.pointIdeal b ∈
    (I.map (algebraMap (MvPolynomial ι K) (MvPolynomial ι E))).minimalPrimes
  refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.mpr hminimal.1.2⟩, ?_⟩
  intro Q hQ hQP
  let : Q.IsPrime := hQ.1
  have hunder : Q.under (MvPolynomial ι K) ≤ contractedPoint (K := K) b :=
    Ideal.comap_mono hQP
  have hcont : contractedPoint (K := K) b ≤ Q.under (MvPolynomial ι K) :=
    hminimal.2 ⟨inferInstance, Ideal.map_le_iff_le_comap.mp hQ.2⟩ hunder
  exact (Ideal.IsIntegral.mem_minimalPrimes_map_under
    (R := MvPolynomial ι K) (WeightedBezout.pointIdeal b)).2
      ⟨hQ.1, Ideal.map_le_iff_le_comap.mpr hcont⟩ hQP

end PiExponent.SeparablePointLength

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_CoefficientLocalizationMaximal
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable {R A L : Type*} [CommRing R] [CommRing A] [CommRing L]
variable (M : Submonoid R) [Algebra R A] [IsLocalization M A]

include M in

theorem extended_kernel_eq (f : R →+* L) (g : A →+* L)
    (h : g.comp (algebraMap R A) = f) :
    (RingHom.ker f).map (algebraMap R A) = RingHom.ker g := by
  have hk : (RingHom.ker g).comap (algebraMap R A) = RingHom.ker f := by
    ext x
    change g (algebraMap R A x) = 0 ↔ f x = 0
    have he := RingHom.congr_fun h x
    change g (algebraMap R A x) = f x at he
    rw [he]
  rw [← hk]
  exact IsLocalization.map_under M A (RingHom.ker g)

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoordinateSliceLength
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.RamifiedLocalLength.translatedPowerLocalMap_isLocalHom _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W23.affineCoefficient_isLocalization _root_.OAI.PiExponentSiegel.W23.affineQuotient_scalarTower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.CoordinateSliceLength

open PiExponentJets.PolynomialLocalResidueResolution

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

theorem closedPolynomialIdeal_eq_ker :
    closedPolynomialIdeal K α β Q hB =
      RingHom.ker (closedPointEvaluationRingHom K α β Q hB) := by
  unfold closedPolynomialIdeal coefficientClosedPoint
  change ((RingHom.ker (closedPointEvaluationRingHom K α β Q hB)).comap
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom).map
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom = _
  exact Ideal.map_comap_of_surjective _
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).surjective _

theorem map_prime_eq_closedPolynomialIdeal :
    Q.map (rationalizePolynomial K α β) = closedPolynomialIdeal K α β Q hB := by
  have h := extended_kernel_eq
    (PiExponentSiegelAux.W09.coefficientDenominators K α β)
    (algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q))
    ((closedPointEvaluationRingHom K α β Q hB).comp
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom)
    (closedPointEvaluation_original K α β Q hB)
  rw [Ideal.ker_algebraMap_residueField] at h
  unfold closedPolynomialIdeal coefficientClosedPoint
  rw [← h, Ideal.map_map]
  rfl

theorem closedPolynomialIdeal_comap :
    (closedPolynomialIdeal K α β Q hB).comap (rationalizePolynomial K α β) = Q := by
  rw [closedPolynomialIdeal_eq_ker]
  change RingHom.ker ((closedPointEvaluationRingHom K α β Q hB).comp
    (rationalizePolynomial K α β)) = Q
  rw [show (closedPointEvaluationRingHom K α β Q hB).comp
      (rationalizePolynomial K α β) =
      algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q) from
    closedPointEvaluation_original K α β Q hB]
  exact Ideal.ker_algebraMap_residueField Q

theorem closedPolynomialIdeal_mem_minimalPrimes
    (I : Ideal (MvPolynomial (α ⊕ β) K)) (hQ : Q ∈ I.minimalPrimes) :
    closedPolynomialIdeal K α β Q hB ∈
      (I.map (rationalizePolynomial K α β)).minimalPrimes := by
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · rw [← map_prime_eq_closedPolynomialIdeal]
    exact Ideal.map_mono hQ.1.2
  · intro J hJ hJP
    let : J.IsPrime := hJ.1
    have hcont : Q ≤ J.comap (rationalizePolynomial K α β) := by
      apply hQ.2 ⟨inferInstance, Ideal.map_le_iff_le_comap.mp hJ.2⟩
      rw [← closedPolynomialIdeal_comap K α β Q hB]
      exact Ideal.comap_mono hJP
    rw [← map_prime_eq_closedPolynomialIdeal]
    exact Ideal.map_le_iff_le_comap.mpr hcont

theorem splitCoefficientResidue_isScalarTower :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    IsScalarTower K (SplitCoefficientField K β) (SplitResidue K α β Q) := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap K (SplitResidue K α β Q) a =
    ((rationalResidueEquiv (splitLocalBeta K α β Q) hB.1
      (algebraMap K (SplitCoefficientField K β) a)) : SplitResidue K α β Q)
  rw [AlgEquiv.commutes]
  rfl

theorem splitResidue_finite [Finite α] [Finite β] :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    Module.Finite (SplitCoefficientField K β) (SplitResidue K α β Q) := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  let := splitCoefficientResidue_isScalarTower K α β Q hB
  let : Algebra.EssFiniteType K (SplitResidue K α β Q) :=
    Algebra.EssFiniteType.comp K (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q)
  let := Algebra.EssFiniteType.of_comp K (SplitCoefficientField K β)
    (SplitResidue K α β Q)
  let := splitResidue_algebraic K α β Q hB
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem map_rationalize_eq_residueSlice :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    (MvPolynomial.map (algebraMap (SplitCoefficientField K β) (SplitResidue K α β Q))).comp
      (rationalizePolynomial K α β) = residueSlice K α β Q := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  let := splitCoefficientResidue_isScalarTower K α β Q hB
  apply MvPolynomial.ringHom_ext
  · intro a
    change MvPolynomial.map _ (rationalizePolynomial K α β (MvPolynomial.C a)) = _
    have hr : rationalizePolynomial K α β (MvPolynomial.C a) =
        MvPolynomial.C (algebraMap K (SplitCoefficientField K β) a) := by
      change PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
        (algebraMap K (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β) a) = _
      exact (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).commutes a
    rw [hr, MvPolynomial.map_C]
    change MvPolynomial.C _ = MvPolynomial.aeval _ (MvPolynomial.C a)
    rw [MvPolynomial.aeval_C]
    exact congrArg MvPolynomial.C
      (IsScalarTower.algebraMap_apply K (SplitCoefficientField K β) (SplitResidue K α β Q) a).symm
  · intro i
    cases i with
    | inl i => simp [residueSlice]
    | inr i =>
      have hc := closedPointEvaluation_coefficient K α β Q hB (MvPolynomial.X i)
      simp only [closedPointEvaluation, MvPolynomial.aeval_C, MvPolynomial.aeval_X] at hc
      simpa [residueSlice] using congrArg (MvPolynomial.C (σ := α)) hc

theorem closedPolynomialIdeal_eq_contractedPoint :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    closedPolynomialIdeal K α β Q hB =
      SeparablePointLength.contractedPoint (K := SplitCoefficientField K β)
        (slicePoint K α β Q) := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  rw [closedPolynomialIdeal_eq_ker, SeparablePointLength.contractedPoint_eq_ker]
  rfl

include hB in

theorem slicePoint_mem_minimalPrimes [Finite α] [Finite β]
    (I : Ideal (MvPolynomial (α ⊕ β) K)) (hQ : Q ∈ I.minimalPrimes) :
    WeightedBezout.pointIdeal (slicePoint K α β Q) ∈
      (I.map (residueSlice K α β Q)).minimalPrimes := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  let := splitResidue_finite K α β Q hB
  have h := closedPolynomialIdeal_mem_minimalPrimes K α β Q hB I hQ
  rw [closedPolynomialIdeal_eq_contractedPoint K α β Q hB] at h
  have he := SeparablePointLength.point_mem_minimalPrimes_map
    (K := SplitCoefficientField K β) (slicePoint K α β Q)
    (I.map (rationalizePolynomial K α β)) h
  rw [Ideal.map_map, map_rationalize_eq_residueSlice K α β Q hB] at he
  exact he

end PiExponent.CoordinateSliceLength

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

end PolynomialMap

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoordinateTranscendenceBasis
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent
open MvPolynomial
open NormalBasisRigidity

section Linear
variable {K ι : Type*} [Field K] [Fintype ι]

theorem normalBasis_complement_surjective (T : Submodule K (ι → K))
    (A : Finset ι)
    (hA : IsNormalBasis (K := K) (fun i => T.mkQ (Pi.basisFun K ι i)) A) :
    Function.Surjective (fun t : T => fun i : {i // i ∉ A} => t.val i.val) := by
  classical
  have hli : LinearIndependent K (fun i : A => T.mkQ (Pi.basisFun K ι i)) := hA.1
  let b : Module.Basis A K ((ι → K) ⧸ T) := Module.Basis.mk hli (by
    have hr : Set.range (fun i : A => T.mkQ (Pi.basisFun K ι i)) =
        (fun i => T.mkQ (Pi.basisFun K ι i)) '' (A : Set ι) := by ext; simp
    change ⊤ ≤ Submodule.span K (Set.range (fun i : A => T.mkQ (Pi.basisFun K ι i)))
    rw [hr, hA.2])
  intro g
  let u : ι → K := fun i => if hi : i ∈ A then 0 else g ⟨i, hi⟩
  let w : ι → K := ∑ i : A, b.repr (T.mkQ u) i • Pi.basisFun K ι i.val
  have hw : T.mkQ w = T.mkQ u := by
    change T.mkQ (∑ i : A, _) = _
    simp only [map_sum, map_smul]
    simpa only [b, Module.Basis.mk_apply] using b.sum_repr (T.mkQ u)
  have ht : u - w ∈ T := by
    rw [← Submodule.Quotient.mk_eq_zero]
    change T.mkQ (u - w) = 0
    rw [map_sub, hw, sub_self]
  refine ⟨⟨u - w, ht⟩, ?_⟩
  funext i
  have hw0 : w i.val = 0 := by
    dsimp [w]
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro a _
    have hn : a.val ≠ i.val := fun he => i.property (he ▸ a.property)
    simp [Pi.basisFun_apply, Ne.symm hn]
  change u i.val - w i.val = g i
  simp [u, i.property, hw0]

theorem normalBasis_complement_injective (T : Submodule K (ι → K))
    (A : Finset ι)
    (hA : IsNormalBasis (K := K) (fun i => T.mkQ (Pi.basisFun K ι i)) A) :
    Function.Injective (fun t : T => fun i : {i // i ∉ A} => t.val i.val) := by
  classical
  suffices hz : ∀ t : T, (∀ i, i ∉ A → t.val i = 0) → t = 0 by
    intro t u h
    have hd : t - u = 0 := hz (t - u) (by
      intro i hi
      exact sub_eq_zero.mpr (congrFun h ⟨i,hi⟩))
    exact sub_eq_zero.mp hd
  intro t ht
  have he : (∑ a : A, t.val a.val • Pi.basisFun K ι a.val) = t.val := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply]
    by_cases hi : i ∈ A
    · rw [Finset.sum_eq_single (⟨i, hi⟩ : A)]
      · simp
      · intro a _ hn
        have hn' : a.val ≠ i := fun h => hn (Subtype.ext h)
        simp [Ne.symm hn']
      · simp
    · simp [ht i hi, show ∀ a : A, a.val ≠ i from fun a h => hi (h ▸ a.property)]
  have hs : (∑ a : A, t.val a.val • T.mkQ (Pi.basisFun K ι a.val)) = 0 := by
    calc
      _ = T.mkQ (∑ a : A, t.val a.val • Pi.basisFun K ι a.val) := by simp only [map_sum, map_smul]
      _ = 0 := by rw [he]; exact (Submodule.Quotient.mk_eq_zero T).mpr t.property
  have hall := (Fintype.linearIndependent_iff.mp hA.1) _ hs
  apply Subtype.ext
  ext i
  by_cases hi : i ∈ A
  · exact hall ⟨i,hi⟩
  · exact ht i hi

end Linear

section PolynomialChain
variable {C E ι κ : Type*} [Field C] [Field E] [Algebra C E] [Fintype ι] [Fintype κ]

theorem polynomialGradient_mul (φ : MvPolynomial ι C →ₐ[C] E) (t : ι → E)
    (p q : MvPolynomial ι C) :
    (∑ i, φ (pderiv i (p*q)) * t i) =
      φ p * (∑ i, φ (pderiv i q) * t i) +
      φ q * (∑ i, φ (pderiv i p) * t i) := by
  simp only [pderiv_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  conv_lhs => rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem polynomialGradient_rename (φ : MvPolynomial ι C →ₐ[C] E) (t : ι → E)
    (f : κ → ι) (p : MvPolynomial κ C) :
    (∑ i, φ (pderiv i (rename f p)) * t i) =
      ∑ j, φ (rename f (pderiv j p)) * t (f j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, polynomialGradient_mul, hp]
    have hgrad : (∑ i, φ (pderiv i (rename f (X j))) * t i) = t (f j) := by
      simp [Pi.single_apply]
    rw [hgrad]
    let ψ : MvPolynomial κ C →ₐ[C] E := φ.comp (rename f)
    have hR := polynomialGradient_mul ψ (t ∘ f) p (X j)
    change _ = ∑ i, ψ (pderiv i (p * X j)) * (t ∘ f) i
    rw [hR]
    simp [ψ, Pi.single_apply]

end PolynomialChain

section KernelCriterion
variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

omit [CharZero C] in
theorem pderiv_totalDegree_lt_of_pos (p : MvPolynomial ι C) (hp : 0 < p.totalDegree)
    (i : ι) : (pderiv i p).totalDegree < p.totalDegree := by
  classical
  apply lt_of_le_of_lt (show (pderiv i p).totalDegree ≤ p.totalDegree - 1 from ?_)
    (Nat.sub_lt hp (by omega))
  apply Finset.sup_le
  intro m hm
  have hcoeff : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have hh := (mem_support_iff.mp hm)
    rw [coeff_pderiv] at hh
    exact (mul_ne_zero_iff.mp hh).1
  have hb := le_totalDegree (mem_support_iff.mpr hcoeff)
  have hsum : (m + Finsupp.single i 1).sum (fun _ e => e) =
      m.sum (fun _ e => e) + 1 := by
    simp [Finsupp.sum_fintype, Finset.sum_add_distrib]
  rw [hsum] at hb
  omega

theorem eq_C_of_pderiv_eq_zero (p : MvPolynomial ι C)
    (hp : ∀ i, pderiv i p = 0) : p = MvPolynomial.C (p.coeff 0) := by
  classical
  ext m
  by_cases hm : m = 0
  · subst m; simp
  · rw [coeff_C, ite_eq_right (Ne.symm hm)]
    have hex : ∃ i, m i ≠ 0 := by
      by_contra! h
      apply hm
      ext i
      exact h i
    obtain ⟨i, hi'⟩ := hex
    have hc := congrArg (fun p : MvPolynomial ι C => p.coeff (m - Finsupp.single i 1)) (hp i)
    rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hi'] at hc
    have hpos : 0 < ((m - Finsupp.single i 1 : ι →₀ ℕ) i) + 1 := by omega
    have hn : ((((m - Finsupp.single i 1 : ι →₀ ℕ) i) : C) + 1) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hpos)
    rw [MvPolynomial.coeff_zero] at hc
    exact (mul_eq_zero.mp hc).resolve_right hn

theorem algebraicIndependent_of_pderiv_kernel (x : ι → E)
    (hker : ∀ p : MvPolynomial ι C, aeval x p = 0 →
      ∀ i, aeval x (pderiv i p) = 0) : AlgebraicIndependent C x := by
  apply algebraicIndependent_iff.mpr
  intro p
  induction hp : p.totalDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    intro hz
    by_cases hn : n = 0
    · have he := totalDegree_eq_zero_iff_eq_C.mp (hp.trans hn)
      rw [he, aeval_C] at hz
      have hconstant : p.coeff 0 = 0 := (algebraMap C E).injective (by simpa using hz)
      rw [he, hconstant, map_zero]
    · have hpartials : ∀ i, pderiv i p = 0 := by
        intro i
        exact ih _ (hp ▸ pderiv_totalDegree_lt_of_pos p (by omega) i)
          _ rfl (hker p hz i)
      have he := eq_C_of_pderiv_eq_zero p hpartials
      rw [he, aeval_C] at hz
      have hconstant : p.coeff 0 = 0 := (algebraMap C E).injective (by simpa using hz)
      rw [he, hconstant, map_zero]


theorem normalBasis_complement_algebraicIndependent
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hker : ∀ p, φ p = 0 → p ∈ Q)
    (A : Finset ι)
    (hA : IsNormalBasis (K := E)
      (fun i => (polynomialTangent φ Q).mkQ (Pi.basisFun E ι i)) A) :
    AlgebraicIndependent C (fun i : {i // i ∉ A} => φ (X i.val)) := by
  classical
  let x : {i // i ∉ A} → E := fun i => φ (X i.val)
  have hφ (p : MvPolynomial {i // i ∉ A} C) : φ (rename Subtype.val p) = aeval x p := by
    have he : φ.comp (rename Subtype.val) = aeval x := by ext i; simp [x]
    exact AlgHom.congr_fun he p
  apply algebraicIndependent_of_pderiv_kernel
  intro p hp j
  obtain ⟨t,ht⟩ := normalBasis_complement_surjective (polynomialTangent φ Q) A hA
    (Pi.single j 1)
  have hmem : rename Subtype.val p ∈ Q := hker _ ((hφ p).trans hp)
  have heq : (∑ i, φ (pderiv i (rename Subtype.val p)) * t.val i) = 0 := by
    exact congrFun t.property ⟨rename Subtype.val p,hmem⟩
  rw [polynomialGradient_rename] at heq
  have hv : ∀ i : {i // i ∉ A}, t.val i.val = (Pi.single j (1 : E) : {i // i ∉ A} → E) i := by
    intro i
    exact congrFun ht i
  simpa [hv, hφ, Pi.single_apply, x] using heq

end KernelCriterion

section Algebraicity
open KaehlerDifferential
variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

omit [CharZero C] [Fintype ι] in
theorem derivation_eq_zero_of_field_generators
    (x : ι → E) (hgen : IntermediateField.adjoin C (Set.range x) = ⊤)
    (d : Derivation C E E) (hd : ∀ i, d (x i) = 0) : d = 0 := by
  have hp : ∀ a ∈ Algebra.adjoin C (Set.range x), d a = 0 := by
    exact Derivation.eqOn_adjoin (D1 := d) (D2 := 0) (by rintro _ ⟨i,rfl⟩; exact hd i)
  apply Derivation.ext
  intro z
  have hz : z ∈ IntermediateField.adjoin C (Set.range x) := by rw [hgen]; trivial
  obtain ⟨a,ha,b,hb,rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  change d (a / b) = 0
  rw [d.leibniz_div, hp a ha, hp b hb, smul_zero, smul_zero, sub_self, smul_zero]

theorem normalBasis_complement_isAlgebraic
    [Algebra.EssFiniteType C E]
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p ∈ Q, φ p = 0)
    (hgen : IntermediateField.adjoin C (Set.range (fun i => φ (X i))) = ⊤)
    (A : Finset ι)
    (hA : IsNormalBasis (K := E)
      (fun i => (polynomialTangent (φ) Q).mkQ
        (Pi.basisFun (E) ι i)) A) :
    Algebra.IsAlgebraic
      (IntermediateField.adjoin C
        (Set.range (fun i : {i // i ∉ A} => φ (X i.val))))
      (E) := by
  classical
  let K := IntermediateField.adjoin C
    (Set.range (fun i : {i // i ∉ A} => φ (X i.val)))
  have hdzero (d : Derivation K E E) : d = 0 := by
    let dC := d.restrictScalars C
    let t : polynomialTangent (φ) Q :=
      ⟨(fun i => dC (φ (X i))),
        derivation_mem_polynomialTangent _ _ hQ dC⟩
    have ht : t = 0 := normalBasis_complement_injective _ A hA (by
      funext i
      change d (φ (X i.val)) = 0
      let k : K := ⟨φ (X i.val),
        IntermediateField.subset_adjoin C _ (Set.mem_range_self i)⟩
      exact d.map_algebraMap k)
    have hc : ∀ i, dC (φ (X i)) = 0 := by
      intro i
      exact congrFun (congrArg Subtype.val ht) i
    have hh := derivation_eq_zero_of_field_generators (fun i => φ (X i)) hgen dC hc
    ext z
    exact DFunLike.congr_fun hh z
  let : Algebra.EssFiniteType K E := Algebra.EssFiniteType.of_comp C K E
  constructor
  intro z
  have hz : D K E z = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff E _).mp
    intro l
    let d : Derivation K E E := l.compDer (D K E)
    exact DFunLike.congr_fun (hdzero d) z
  exact isAlgebraic_of_logarithmic_differential (C := K) (0 : E) z (by rw [map_zero, hz, smul_zero])

end Algebraicity

section TranscendenceBasis
open scoped IntermediateField.algebraAdjoinAdjoin
variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

theorem normalBasis_complement_isTranscendenceBasis
    [Algebra.EssFiniteType C E]
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p, φ p = 0 ↔ p ∈ Q)
    (hgen : IntermediateField.adjoin C (Set.range (fun i => φ (X i))) = ⊤)
    (A : Finset ι)
    (hA : IsNormalBasis (K := E)
      (fun i => (polynomialTangent φ Q).mkQ (Pi.basisFun E ι i)) A) :
    IsTranscendenceBasis C (fun i : {i // i ∉ A} => φ (X i.val)) := by
  have hind := normalBasis_complement_algebraicIndependent φ Q
    (fun p => (hQ p).mp) A hA
  apply hind.isTranscendenceBasis_iff_isAlgebraic.mpr
  let K := IntermediateField.adjoin C
    (Set.range (fun i : {i // i ∉ A} => φ (X i.val)))
  let : Algebra.IsAlgebraic K E := normalBasis_complement_isAlgebraic φ Q
    (fun p => (hQ p).mpr) hgen A hA
  exact Algebra.IsAlgebraic.trans _ K E

end TranscendenceBasis

variable {C ι : Type*} [Field C] [Fintype ι]


omit [Fintype ι] in

theorem idealResidueMap_field_generation
    (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] :
    IntermediateField.adjoin C
      (Set.range (fun i => algebraMap (MvPolynomial ι C) Q.ResidueField (X i))) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨a,b,hb,hz⟩ := IsFractionRing.div_surjective (MvPolynomial ι C ⧸ Q) z
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
  have he : aeval (fun i => algebraMap (MvPolynomial ι C) Q.ResidueField (X i)) =
      IsScalarTower.toAlgHom C (MvPolynomial ι C) Q.ResidueField := by
    ext i
    simp
  apply (IntermediateField.mem_adjoin_range_iff C _ z).mpr
  refine ⟨a,b,?_⟩
  rw [he]
  simpa only [IsScalarTower.coe_toAlgHom', Ideal.algebraMap_quotient_residueField_mk] using hz.symm

theorem idealResidueNormalBasis_complement_isTranscendenceBasis
    [CharZero C] (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] (A : Finset ι)
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom C (MvPolynomial ι C) Q.ResidueField) Q).mkQ
          (Pi.basisFun Q.ResidueField ι i)) A) :
    IsTranscendenceBasis C
      (fun i : {i // i ∉ A} => algebraMap (MvPolynomial ι C) Q.ResidueField (X i.val)) := by
  let : Algebra.EssFiniteType C Q.ResidueField :=
    .comp C (MvPolynomial ι C) Q.ResidueField
  exact normalBasis_complement_isTranscendenceBasis
    (IsScalarTower.toAlgHom C (MvPolynomial ι C) Q.ResidueField) Q
    (fun _ => Ideal.algebraMap_residueField_eq_zero)
    (idealResidueMap_field_generation Q) A hA

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PointLengthEquiv
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.RamifiedLocalLength.translatedPowerLocalMap_isLocalHom _root_.OAI.PiExponent.SeparablePointLength.pointLocalMap_isLocalHom _root_.OAI.PiExponent.SeparablePointLength.point_liesOver _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.PointLengthEquiv

open PiExponent.WeightedBezout

variable {E F ι : Type*} [Field E] [Field F]

theorem evaluation_map (e : E ≃+* F) (b : ι → E) (p : MvPolynomial ι E) :
    MvPolynomial.aeval (fun i => e (b i)) (MvPolynomial.map e.toRingHom p) =
      e (MvPolynomial.aeval b p) := by
  simpa [MvPolynomial.aeval_def] using
    ((MvPolynomial.eval_map e.toRingHom (fun i => e (b i)) p).trans
      (MvPolynomial.eval₂_comp e.toRingHom b p).symm)

theorem pointIdeal_comap (e : E ≃+* F) (b : ι → E) :
    pointIdeal b = (pointIdeal (fun i => e (b i))).comap
      (MvPolynomial.mapEquiv ι e).toRingHom := by
  ext p
  change MvPolynomial.aeval b p = 0 ↔
    MvPolynomial.aeval (fun i => e (b i)) (MvPolynomial.map e.toRingHom p) = 0
  rw [evaluation_map]
  exact e.map_eq_zero_iff.symm

theorem pointIdeal_map (e : E ≃+* F) (b : ι → E) :
    (pointIdeal b).map (MvPolynomial.mapEquiv ι e).toRingHom =
      pointIdeal (fun i => e (b i)) := by
  rw [pointIdeal_comap e b]
  exact Ideal.map_comap_of_surjective (MvPolynomial.mapEquiv ι e).toRingHom
    (MvPolynomial.mapEquiv ι e).surjective _

theorem point_mem_minimalPrimes_map (e : E ≃+* F) (b : ι → E)
    (I : Ideal (MvPolynomial ι E)) (hI : pointIdeal b ∈ I.minimalPrimes) :
    pointIdeal (fun i => e (b i)) ∈ (I.map (MvPolynomial.map e.toRingHom)).minimalPrimes := by
  let φ := MvPolynomial.mapEquiv ι e
  change pointIdeal (fun i => e (b i)) ∈ (I.map φ.toRingHom).minimalPrimes
  have hker : RingHom.ker φ.toRingHom = ⊥ := by
    ext p
    change φ p = 0 ↔ p = 0
    exact φ.map_eq_zero_iff
  rw [Ideal.minimalPrimes_map_of_surjective (f := φ.toRingHom) φ.surjective, hker, sup_bot_eq]
  exact ⟨pointIdeal b, hI, pointIdeal_map e b⟩

end PiExponent.PointLengthEquiv

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoordinateSliceComparison
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.RamifiedLocalLength.translatedPowerLocalMap_isLocalHom _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CoordinateSliceComparison

open PiExponentJets.PolynomialLocalResidueResolution
open CoordinateFiniteSlice

variable {K ι : Type*} [Field K] [Fintype ι]

omit [Fintype ι] in
theorem splitBasis (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hB : IsTranscendenceBasis K (fun i : {i // i ∉ A} => residueCoordinates Q i.val)) :
    IsTranscendenceBasis K
      (splitResidueBeta K (Fin A.card) {i // i ∉ A} (splitPrime Q A)) :=
  complementary_transcendenceBasis Q A hB

omit [Fintype ι] in
theorem map_residueSlice_eq_enumeratedSliceMap
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    (MvPolynomial.map (residueEquiv Q A).symm.toRingHom).comp
      ((CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A)).comp
        (coordinateRenaming (K := K) A).toRingHom) =
      (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [CoordinateSliceLength.residueSlice, coordinateRenaming,
      WeightedSliceDegree.enumeratedSliceMap, WeightedSliceDegree.sliceMap,
      MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
  · intro i
    obtain ⟨j, rfl⟩ := (coordinateEquiv A).surjective i
    cases j with
    | inl j =>
      simp [RingHom.comp_apply, CoordinateSliceLength.residueSlice]
    | inr j =>
      change MvPolynomial.map (residueEquiv Q A).symm.toRingHom
        (CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A)
          (coordinateRenaming (K := K) A (MvPolynomial.X j.val))) =
        WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q) (MvPolynomial.X j.val)
      rw [coordinateRenaming_X_inr]
      rw [show CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A)
          (MvPolynomial.X (Sum.inr j)) =
          MvPolynomial.C (splitResidueBeta K (Fin A.card) {i // i ∉ A} (splitPrime Q A) j) by
        simp [CoordinateSliceLength.residueSlice]]
      rw [MvPolynomial.map_C, enumeratedSliceMap_X_inr]
      exact congrArg MvPolynomial.C (residueEquiv_symm_coordinate_inr Q A j)

omit [Fintype ι] in
theorem map_splitPoint_eq (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    (fun i => (residueEquiv Q A).symm.toRingEquiv
      (CoordinateSliceLength.slicePoint K (Fin A.card) {i // i ∉ A} (splitPrime Q A) i)) =
      slicePoint Q A := by
  funext i
  exact residueEquiv_symm_coordinate_inl Q A i

omit [Fintype ι] in
theorem map_slice_ideal (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    ((I.map (coordinateRenaming (K := K) A).toRingHom).map
      (CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A))).map
      (MvPolynomial.map (residueEquiv Q A).symm.toRingHom) =
    I.map (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  exact map_residueSlice_eq_enumeratedSliceMap Q A

theorem slicePoint_mem_minimalPrimes
    (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hB : IsTranscendenceBasis K (fun i : {i // i ∉ A} => residueCoordinates Q i.val))
    (hQ : Q ∈ I.minimalPrimes) :
    WeightedBezout.pointIdeal (slicePoint Q A) ∈
      (I.map (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom).minimalPrimes := by
  have h₁ := splitPrime_mem_minimalPrimes Q I A hQ
  have h₂ := CoordinateSliceLength.slicePoint_mem_minimalPrimes K (Fin A.card) {i // i ∉ A}
    (splitPrime Q A) (splitBasis Q A hB) (I.map (coordinateRenaming (K := K) A).toRingHom) h₁
  have h₃ := PointLengthEquiv.point_mem_minimalPrimes_map (residueEquiv Q A).symm.toRingEquiv
    (CoordinateSliceLength.slicePoint K (Fin A.card) {i // i ∉ A} (splitPrime Q A))
    ((I.map (coordinateRenaming (K := K) A).toRingHom).map
      (CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A))) h₂
  rw [map_slice_ideal, map_splitPoint_eq] at h₃
  exact h₃

theorem slicePoint_mem_minimalPrimes_of_normalBasis [CharZero K]
    (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hA : NormalBasisRigidity.IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom K (MvPolynomial ι K) Q.ResidueField) Q).mkQ
        (Pi.basisFun Q.ResidueField ι i)) A)
    (hQ : Q ∈ I.minimalPrimes) :
    WeightedBezout.pointIdeal (slicePoint Q A) ∈
      (I.map (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom).minimalPrimes :=
  slicePoint_mem_minimalPrimes Q I A
    (idealResidueNormalBasis_complement_isTranscendenceBasis Q A hA) hQ

omit [Fintype ι] in
theorem map_span_sliceFamily
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    {J : Type*} (f : J → MvPolynomial ι K) :
    (Ideal.span (Set.range f)).map
      (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom =
    Ideal.span (Set.range (fun j =>
      WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q) (f j))) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

theorem sliceFamily_mem_minimalPrimes_of_normalBasis_q68_oai [CharZero K]
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hA : NormalBasisRigidity.IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom K (MvPolynomial ι K) Q.ResidueField) Q).mkQ
        (Pi.basisFun Q.ResidueField ι i)) A)
    {J : Type*} (f : J → MvPolynomial ι K)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    WeightedBezout.pointIdeal (slicePoint Q A) ∈
      (Ideal.span (Set.range (fun j =>
        WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q) (f j)))).minimalPrimes := by
  have h := slicePoint_mem_minimalPrimes_of_normalBasis Q (Ideal.span (Set.range f)) A hA hQ
  rw [map_span_sliceFamily] at h
  exact h

end PiExponent.CoordinateSliceComparison

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.PiExponent.CoordinateSliceComparison.sliceFamily_mem_minimalPrimes_of_normalBasis_q68_oai.{u_1, u_2, u_3} := @OAI.PiExponent.CoordinateSliceComparison.sliceFamily_mem_minimalPrimes_of_normalBasis_q68_oai.{u_1, u_2, u_3}
