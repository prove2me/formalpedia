-- Prove2me | solution 1 for OAI.SevenEighths.ProbeDetectorInverseMarkedField.source_batch_inverse_marked
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T05:37:15.525256+00:00
-- url     : https://prove2.me/submissions/eb784a4b-0cbc-4609-b80c-e20299e8cf17

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Theorems.Thm_OAI_SevenEighths_DetectorDictionaryInverseMarkedPhysicalRows_fiber_child_rows_le_deleted_sources
import Theorems.Thm_OAI_SevenEighths_DetectorDictionaryInverseMarkedReference_padded_source_energy
import Theorems.Thm_OAI_SevenEighths_DetectorDictionaryInverseMarkedUniform_fiber_inverse_height_uniform

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.StaticReflectionPhases
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalCoefficientClass
local notation "Eis" => ActualEisensteinCubic.O

lemma reflectionConductor_ne_zero (q:ℕ) (hq:q≠0) : reflectionConductor q≠0 := by
  unfold reflectionConductor
  exact_mod_cast Nat.mul_ne_zero (by decide : 2592≠0) hq

lemma reflectionConductor_prime_mem (q:ℕ) (hq:q≠0) (P:Ideal Eis)
    (hP:Prime P) (hd:P∣Ideal.span {reflectionConductor q}) :
    P∈reflectionExcludedPrimes q := by
  apply Finset.mem_union_right
  apply Multiset.mem_toFinset.mpr
  apply (Ideal.mem_normalizedFactors_iff (Ideal.span_singleton_eq_bot.not.mpr
    (reflectionConductor_ne_zero q hq))).mpr
  exact ⟨Ideal.isPrime_of_prime hP,Ideal.dvd_iff_le.mp hd⟩

end CanonicalRowCompletion

open scoped BigOperators Classical

open scoped BigOperators Classical MatrixGroups Matrix

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicTailBudget
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic

theorem constant_absorbed_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, C≤Z^ε := by
  exact (tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop C)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorDyadicGeometry
open HeckeDyadic

lemma uniform_scale_threshold (dmin A : ℝ) (hd : 0<dmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → A≤Z^d := by
  have hh := constant_absorbed_eventually A dmin hd
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hA hZ d hd'
  exact hA.trans (Real.rpow_le_rpow_of_exponent_le hZ hd')

end SevenEighths.HeckeDetectorDyadicGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.Vendor.PrimeNumberTheoremAnd.Sobolev
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

namespace CS

variable {f : CS n E} {R x v : ℝ}

theorem bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRelativePrime
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRelativePrime
open HeckeFamily HeckeDetectorPrimeFamily

theorem idealCoeff_ne_zero_of_coprime (ν : Character) (J : Ideal O)
    (hJ : J≠0) (hc : IsCoprime J ν.modulus) : idealCoeff ν J≠0 := by
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν hg]
  apply MulChar.apply_ne_zero_iff.mpr
  apply (IdealCharacter.isUnit_mk_iff_isCoprime ν.modulus _).mpr
  simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hc

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.HeckeDetectorRelativePrime

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalSignalComparison
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
namespace SevenEighths.PrincipalSignalComparison
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal

variable {κ ι : Type*}

theorem idealCoeff_norm_one_of_coprime (χ : Character) (J : Ideal HeckeFamily.O)
    (hJ : J ≠ ⊥) (hc : IsCoprime J χ.modulus) : ‖idealCoeff χ J‖ = 1 := by
  let := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ χ.modulus) := Fintype.ofFinite _
  have hu : IsUnit (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator J)) :=
    (IdealCharacter.isUnit_mk_iff_isCoprime χ.modulus _).mpr (by
      simpa only [Ideal.span_singleton_generator] using hc)
  obtain ⟨u, hu⟩ := hu
  change ‖IdealCharacter.value χ.modulus χ.residue J‖ = 1
  rw [IdealCharacter.value, if_neg hJ, ← hu]
  exact FiniteRayExpansion.norm_char_unit χ.residue u

open ProbePhysical ActualEisensteinCubic CompletedGauss

open PrincipalMellinResidues

end SevenEighths.PrincipalSignalComparison
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayPoolGood
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical CanonicalQuadraticSieve PrincipalSignalComparison
local notation "Id" => Ideal HeckeFamily.O

theorem prime_coprime_of_norm_gt (η : Character) (P : PrimeIdeal)
    (hN : (η.modulus.absNorm:ℝ)<(P.val.absNorm:ℝ)) : IsCoprime P.val η.modulus := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hηJ hJ
  have hmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have heq := hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hηJ
  have hd : P.val∣η.modulus := Ideal.dvd_iff_le.mpr hηJ
  have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))
    (map_dvd Ideal.absNorm hd)
  exact (not_le_of_gt hN) (by exact_mod_cast hn)

end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialRawDictionary
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialRawDictionary
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeRowClosure
open InverseInitialPoissonBridge InverseInitialConjugateEnergy
open ConcretePrimeRowBridge CompletedGauss UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem fixedBase_zero_unsupported (η : Character) (m f : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (I : Ideal O) (hI : ¬CanonicalQuadraticSieve.Supported I) : fixedBase η m f I=0 := by
  by_cases hi : I=0
  · subst I
    change idealCoeff η 0*_=0
    rw [map_zero,zero_mul]
  let n := ConcretePrimeRowBridge.idealGenerator I
  have hn : n≠0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hi
  have hs : Ideal.span {n}=I := ConcretePrimeRowBridge.span_idealGenerator I
  have he := CanonicalRowCompletion.rowTwist_zero_of_not_supported
    (elementHom η) m f 1 n hmLam hm2 (by rwa [hs])
  change elementCoeff η n*CanonicalRowCompletion.idealRowHom (m^6*f^4*1)
    (Ideal.span {n})=0 at he
  rw [mul_one,hs,←idealCoeff_span η hn,hs] at he
  exact he

end SevenEighths.InverseInitialRawDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialDetectorSource
namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexConjugate
namespace SevenEighths.InverseInitialDetectorSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open InverseInitialRawDictionary InverseInitialConjugateEnergy
local notation "O" => HeckeFamily.O

theorem baseCharacter_coeff (data : RowData) (I : Ideal O) :
    idealCoeff (baseCharacter data) I=fixedBase data.η data.m data.f I := by
  rw [HeckeRowClosure.idealCoeff_eq_row data.η (baseCharacter data) data.m data.f 1
    (data.character_spec ⟨1,one_ne_zero⟩),mul_one]
  rfl

theorem base_nonzero_prime (data : RowData) (P : Ideal O) (hP : Prime P)
    (hN : ((baseCharacter data).modulus.absNorm:ℝ)<(P.absNorm:ℝ)) :
    fixedBase data.η data.m data.f P≠0 := by
  rw [←baseCharacter_coeff]
  exact HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime _ P hP.ne_zero
    (ProbeRaySlots.prime_coprime_of_norm_gt (baseCharacter data) ⟨P,hP⟩ hN)

end SevenEighths.InverseInitialDetectorSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalSlots
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialPhysicalSlots
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open InverseInitialRawDictionary InverseInitialDetectorSource
open InverseInitialConjugateEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

omit [NeZero M] in
theorem livePrime_data (V : ℝ→ℂ) (a b D : ℝ) (hD : 0<D)
    (hV : ∀x,V x≠0 → x∈Set.Icc a b) (P : Ideal O) (hp : P∈livePrimes M H V b D) :
    Prime P ∧ P∈RayQuotient.identityClass M H ∧ a*D≤(P.absNorm:ℝ) ∧ (P.absNorm:ℝ)≤b*D := by
  obtain ⟨hp,hv⟩ := Finset.mem_filter.mp hp
  obtain ⟨_,hp,hr⟩ := Finset.mem_filter.mp hp
  exact ⟨hp,hr,(le_div_iff₀ hD).mp (hV _ hv).1,(div_le_iff₀ hD).mp (hV _ hv).2⟩

omit [NeZero M] in
theorem live_tuple_injective {ι : Type*} [Fintype ι]
    (V : ι→ℝ→ℂ) (a b ell : ι→ℝ) (Z : ℝ) (hZ : 0<Z)
    (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hsep : ∀i j,i≠j → b i*Z^(ell i)<a j*Z^(ell j) ∨
      b j*Z^(ell j)<a i*Z^(ell i))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset
      (fun i=>livePrimes M H (V i) (b i) (Z^(ell i)))) : Function.Injective p := by
  intro i j he
  by_contra hij
  have hi := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
    (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
  have hj := livePrime_data M H (V j) (a j) (b j) (Z^(ell j))
    (Real.rpow_pos_of_pos hZ _) (hV j) (p j) (Fintype.mem_piFinset.mp hp j)
  rw [he] at hi
  rcases hsep i j hij with h|h <;> linarith [hi.2.2.1,hi.2.2.2,hj.2.2.1,hj.2.2.2]

omit [NeZero M] in
theorem live_tuple_admissible {ι : Type*} [Fintype ι]
    (data : RowData) (V : ι→ℝ→ℂ) (a b ell : ι→ℝ) (Z : ℝ) (hZ : 0<Z)
    (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hlarge : ∀i,((baseCharacter data).modulus.absNorm:ℝ)<a i*Z^(ell i))
    (hsep : ∀i j,i≠j → b i*Z^(ell i)<a j*Z^(ell j) ∨
      b j*Z^(ell j)<a i*Z^(ell i))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset
      (fun i=>livePrimes M H (V i) (b i) (Z^(ell i)))) :
    CanonicalQuadraticSieve.Admissible (∏i,p i) := by
  have hd i := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
    (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
  have hs (i : ι) : CanonicalQuadraticSieve.Supported (p i) := by
    by_contra hn
    exact base_nonzero_prime data (p i) (hd i).1 ((hlarge i).trans_le (hd i).2.2.1)
      (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd (p i) hn)
  have hi := live_tuple_injective M H V a b ell Z hZ hV hsep p hp
  have hsprod : CanonicalQuadraticSieve.Supported (∏i,p i) := by
    have hh (S : Finset ι) : CanonicalQuadraticSieve.Supported (∏i∈S,p i) := by
      induction S using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
      | @insert i S hi ih =>
        rw [Finset.prod_insert hi]
        exact (CanonicalQuadraticSieve.supported_mul_iff _ _).mpr ⟨hs i,ih⟩
    exact hh Finset.univ
  refine ⟨hsprod.1,?_,?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      let : (p i).IsMaximal := (Ideal.isPrime_of_prime (hd i).1).isMaximal (hd i).1.ne_zero
      let : (p j).IsMaximal := (Ideal.isPrime_of_prime (hd j).1).isMaximal (hd j).1.ne_zero
      exact (Ideal.isCoprime_of_isMaximal (hi.ne hij)).isRelPrime
    · intro i _
      exact (hd i).1.squarefree
  · intro P hP
    exact hsprod.2 P hP

end SevenEighths.InverseInitialPhysicalSlots

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPolynomial
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialExcludedPolynomial
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge
open InverseInitialExcludedSource IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

theorem prime_product_squarefree (S:Finset (Ideal O))(hS:∀P∈S,Prime P):
    Squarefree (∏P∈S,P) := by
  have hz:(∏P∈S,P)≠0:=Finset.prod_ne_zero_iff.mpr (fun P hP=>(hS P hP).ne_zero)
  apply (squarefree_iff_nodup_normalizedFactors hz).mpr
  have he:normalizedFactors (∏P∈S,P)=S.val:=by
    simpa using normalizedFactors_prod_of_prime (m:=S.val) (fun P hP=>hS P hP)
  rw [he]
  exact S.nodup

end SevenEighths.InverseInitialExcludedPolynomial

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceTuples
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem sum_tuple_original (L:ι→Finset (Ideal O))(f:(ι→Ideal O)→ℂ) :
    (∑q:Tuple L,f (fun i=>(q i).val))=∑q∈Fintype.piFinset L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i,Fintype.mem_piFinset.mp hq i⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i
    exact congrArg Subtype.val (congrFun he i)
  · intro q hq
    refine ⟨fun i=>(q i).val,Fintype.mem_piFinset.mpr (fun i=>(q i).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedOverlap
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedOverlap
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open HeckeFamily InverseInitialExcludedPolynomial
local notation "O"=>ActualEisensteinCubic.O

theorem deleted_zero_outside (χ:Character)(E:Finset (Ideal O))
    (hE:∀Q∈E,Prime Q)(I:Ideal O)(hn:¬outside E I):
    idealCoeff (χ.excludePrimes E hE) I=0 := by
  rw [idealCoeff_excludePrimes]
  apply if_neg
  intro hc
  apply hn
  intro Q hQ hd
  have hu:IsUnit Q:=(hc Q hQ).isRelPrime hd (dvd_refl Q)
  exact (hE Q hQ).not_isUnit hu

end SevenEighths.InverseInitialExcludedOverlap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPeriod
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialExcludedPeriod
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CanonicalCoefficientClass ConcretePrimeRowBridge IdealMobiusDivisorSum
open UniqueFactorizationMonoid HeckeFamily
local notation "O" => ActualEisensteinCubic.O

theorem deletedPeriod_ne_zero (q:ℕ)(hq:q≠0):deletedPeriod q≠0 := by
  unfold deletedPeriod
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hq)

theorem fixed_bad_divides_reflection (q:ℕ)(P:Ideal O)(hP:P∈fixedBadPrimes):
    P∣Ideal.span {reflectionConductor q} := by
  change P∈({Ideal.span {goodLambda},Ideal.span {(2:O)}}:Finset (Ideal O)) at hP
  rcases Finset.mem_insert.mp hP with rfl|hP
  · apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_singleton_le_span_singleton.mpr
    have h3:goodLambda∣(3:O):=CubicEisenstein.halfPrimary_lambda_dvd_three
    apply h3.trans
    refine ⟨(864*q:ℕ),?_⟩
    unfold reflectionConductor
    push_cast
    ring
  · rw [Finset.mem_singleton.mp hP]
    apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_singleton_le_span_singleton.mpr
    refine ⟨(1296*q:ℕ),?_⟩
    unfold reflectionConductor
    push_cast
    ring

theorem excluded_mem_iff (q:ℕ)(hq:q≠0)(P:Ideal O):
    P∈reflectionExcludedPrimes q ↔ Prime P ∧ P∣Ideal.span {reflectionConductor q} := by
  constructor
  · intro hP
    refine ⟨reflectionExcludedPrimes_prime q P hP,?_⟩
    rcases Finset.mem_union.mp hP with hb|hp
    · exact fixed_bad_divides_reflection q P hb
    · exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp)
  · rintro ⟨hp,hd⟩
    exact reflectionConductor_prime_mem q hq P hp hd

theorem excluded_product_divides_reflection (q:ℕ)(hq:q≠0):
    (∏P∈reflectionExcludedPrimes q,P)∣Ideal.span {reflectionConductor q} := by
  apply support_product_dvd (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))
  intro P hP
  apply Multiset.mem_toFinset.mpr
  apply (Ideal.mem_normalizedFactors_iff
    (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))).mpr
  obtain ⟨hp,hd⟩:= (excluded_mem_iff q hq P).mp hP
  exact ⟨Ideal.isPrime_of_prime hp,Ideal.dvd_iff_le.mp hd⟩

theorem deleted_reflection_ideal (q:ℕ):
    Ideal.span {reflectionConductor (deletedPeriod q)}=
      (Ideal.span {reflectionConductor q}:Ideal O)^2 := by
  rw [Ideal.span_singleton_pow]
  congr 1
  unfold reflectionConductor deletedPeriod
  push_cast
  ring_nf

theorem deleted_excluded_eq (q:ℕ)(hq:q≠0):
    reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q := by
  ext P
  rw [excluded_mem_iff _ (deletedPeriod_ne_zero q hq),excluded_mem_iff q hq,
    deleted_reflection_ideal]
  constructor
  · rintro ⟨hp,hd⟩
    exact ⟨hp,hp.dvd_of_dvd_pow hd⟩
  · rintro ⟨hp,hd⟩
    exact ⟨hp,hd.trans (dvd_pow_self _ (by decide:2≠0))⟩

theorem deleted_period_ideal (q:ℕ):
    (Ideal.span {(deletedPeriod q:O)}:Ideal O)=
      Ideal.span {(q:O)}*Ideal.span {reflectionConductor q} := by
  rw [Ideal.span_singleton_mul_span_singleton]
  congr 1
  unfold deletedPeriod reflectionConductor
  push_cast
  ring_nf

theorem deleted_period_le_modulus (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    Ideal.span {(deletedPeriod q:O)}≤
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus := by
  change Ideal.span {(deletedPeriod q:O)}≤χ.modulus*(∏P∈reflectionExcludedPrimes q,P)
  rw [deleted_period_ideal]
  exact Ideal.mul_mono hperiod (Ideal.dvd_iff_le.mp (excluded_product_divides_reflection q hq))

theorem deleted_element_period (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))) := by
  intro x y hxy
  apply HeckeRowClosure.elementHom_periodic
  exact deleted_period_le_modulus χ q hq hperiod (Ideal.mul_le_left hxy)

theorem deleted_base_gates (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    (∀x,‖HeckeRowClosure.elementHom
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))) := by
  exact ⟨deletedPeriod_ne_zero q hq,deleted_excluded_eq q hq,
    HeckeRowClosure.elementHom_norm _,deleted_element_period χ q hq hperiod⟩

end SevenEighths.InverseInitialExcludedPeriod

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedElement
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialExcludedPeriod
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CanonicalCoefficientClass HeckeFamily InverseInitialRayAttachment
local notation "O"=>ActualEisensteinCubic.O

theorem elementCharacter_eq_elementHom (χ:Character)(hproper:χ.modulus≠⊤):
    elementCharacter (idealCoeff χ).toMonoidHom=HeckeRowClosure.elementHom χ := by
  let:Nontrivial (O⧸χ.modulus):=Ideal.Quotient.nontrivial_iff.mpr hproper
  ext z
  change idealCoeff χ (Ideal.span {z})=elementCoeff χ z
  by_cases hz:z=0
  · subst z
    simp only [Ideal.span_singleton_zero,←Ideal.zero_eq_bot,
      elementCoeff,map_zero,MulChar.map_zero]
  · exact idealCoeff_span χ hz

theorem deleted_modulus_proper (χ:Character)(q:ℕ):
    (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus≠⊤ := by
  have htwo:(Ideal.span {(2:O)}:Ideal O)∈reflectionExcludedPrimes q:=
    reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes])
  have hle:(χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus≤
      Ideal.span {(2:O)}:=by
    change χ.modulus*(∏P∈reflectionExcludedPrimes q,P)≤Ideal.span {(2:O)}
    exact Ideal.mul_le_right.trans (Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem (fun P=>P) htwo))
  intro he
  exact twoIdeal_maximal.ne_top (top_le_iff.mp (he ▸ hle))

theorem deleted_physical_element_eq (χ:Character)(q:ℕ):
    elementCharacter (idealCoeff
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom=
      HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)) :=
  elementCharacter_eq_elementHom _ (deleted_modulus_proper χ q)

theorem deleted_physical_base_gates (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    (∀x,‖elementCharacter (idealCoeff
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (elementCharacter (idealCoeff
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom) := by
  rw [deleted_physical_element_eq]
  exact deleted_base_gates χ q hq hperiod

end SevenEighths.InverseInitialExcludedPeriod

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialGates
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace SevenEighths.DetectorDictionaryInverseRawInitialGates
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialRayAttachment InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap InverseInitialExcludedPolynomial
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge UniqueFactorizationMonoid IdealMobiusDivisorSum
open DetectorDictionaryInverseRawGeometry
local notation "O"=>HeckeFamily.O

theorem basePeriod_ne_zero (data:RowData):basePeriod data≠0:=Nat.ne_of_gt (Character.period_pos _)

theorem basePeriod_le (data:RowData):Ideal.span {(basePeriod data:O)}≤(baseCharacter data).modulus:=
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Character.period_mem _))

theorem raw_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (idealCoeff (deletedBase data)).toMonoidHom x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (idealCoeff (deletedBase data)).toMonoidHom):=
  deleted_physical_base_gates (baseCharacter data) (basePeriod data)
    (basePeriod_ne_zero data) (basePeriod_le data)

theorem excluded_divisor_norm (data:RowData)(j:Ideal O)
    (hj:j∈idealDivisors (∏P∈excluded data,P)):
    1≤(j.absNorm:ℝ) ∧ (j.absNorm:ℝ)≤((∏P∈excluded data,P).absNorm:ℝ):=by
  have hP:Squarefree (∏P∈excluded data,P):=
    prime_product_squarefree _ (reflectionExcludedPrimes_prime (basePeriod data))
  have hd: j∣∏P∈excluded data,P:=(mem_idealDivisors hP.ne_zero).mp hj
  have hj0:=ne_zero_of_dvd_ne_zero hP.ne_zero hd
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  · exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)) (map_dvd Ideal.absNorm hd)

end SevenEighths.DetectorDictionaryInverseRawInitialGates

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawConjugateGates
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseRawConjugateGates
open CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRayAttachment InverseInitialExcludedPeriod CanonicalCoefficientClass
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPool
open InverseInitialExcludedOverlap InverseMoment InverseInitialProfile
local notation "O"=>HeckeFamily.O

theorem conjugate_element_apply (η:Ideal O→*ℂ)(x:O):
    elementCharacter (conjugateIdealCharacter η) x=star (elementCharacter η x):=rfl

theorem conjugate_element_factors (η:Ideal O→*ℂ)(Q:Ideal O)
    (h:FactorsModulo Q (elementCharacter η)):
    FactorsModulo Q (elementCharacter (conjugateIdealCharacter η)):=by
  intro x y hxy
  exact congrArg star (h x y hxy)

theorem conjugate_element_norm (η:Ideal O→*ℂ)(x:O):
    ‖elementCharacter (conjugateIdealCharacter η) x‖=‖elementCharacter η x‖:=by
  rw [conjugate_element_apply,norm_star]

theorem raw_conjugate_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (conjugateIdealCharacter
      (idealCoeff (deletedBase data)).toMonoidHom) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)):=by
  obtain ⟨hq,he,hn,hp⟩:=raw_base_gates data
  refine ⟨hq,he,?_,conjugate_element_factors _ _ hp⟩
  intro x
  rw [conjugate_element_norm]
  exact hn x

theorem raw_conjugate_zero_outside (data:RowData)(I:Ideal O)
    (hI:¬outside (excluded data) I):
    conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom I=0:=by
  change star (idealCoeff (deletedBase data) I)=0
  rw [show idealCoeff (deletedBase data) I=0 from
    deleted_zero_outside (InverseInitialDetectorSource.baseCharacter data)
      (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)) I hI,star_zero]

end SevenEighths.DetectorDictionaryInverseRawConjugateGates

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeleted
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialConjugateEnergy InverseInitialPhysicalSlots
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

theorem deletedBase_zero_unsupported (data:RowData)(I:Ideal O)(hI:¬Supported I) :
    idealCoeff (deletedBase data) I=0 := by
  unfold deletedBase excluded
  rw [idealCoeff_excludePrimes,baseCharacter_coeff,
    fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd I hI]
  split_ifs <;> rfl

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceShift
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification Filter IdealMobiusDivisorSum
open DetectorDictionaryInverseRawInitialGates
local notation "O"=>HeckeFamily.O

theorem marked_shift_eventually (data:RowData)(eta:ℝ)(heta:0<eta) :
    ∀ᶠU:ℝ in atTop,1<U ∧
      ∀j∈idealDivisors (∏P∈excluded data,P),∀r:ℝ,
        r-eta≤ shiftedExponent data U r j ∧ shiftedExponent data U r j≤ r ∧
        U^(shiftedExponent data U r j)=U^r/(j.absNorm:ℝ) := by
  have ht:∀ᶠU:ℝ in atTop,((∏P∈excluded data,P).absNorm:ℝ)≤U^eta :=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with U hU ht
  refine ⟨hU,?_⟩
  intro j hj r
  obtain ⟨hn,hnB⟩:=excluded_divisor_norm data j hj
  have hU0:0<U:=zero_lt_one.trans hU
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  have hl0:0≤Real.logb U (j.absNorm:ℝ):=
    div_nonneg (Real.log_nonneg hn) (Real.log_pos hU).le
  have hl:Real.logb U (j.absNorm:ℝ)≤eta:=
    (Real.logb_le_iff_le_rpow hU hn0).mpr (hnB.trans ht)
  refine ⟨by dsimp [shiftedExponent];linarith,by dsimp [shiftedExponent];linarith,?_⟩
  rw [shiftedExponent,Real.rpow_sub hU0,Real.rpow_logb hU0 hU.ne' hn0]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseClippedUniform
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseUniform HeckeInverseAmplification
open InverseMoment InverseInitialClippedColumns InverseInitialOverlapFourier
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem referenceWindow_support : tsupport (referenceWindow : ℝ→ℂ) ⊆
    Set.Icc (1/18 : ℝ) (13/4) :=
  (Classical.choose_spec exists_reference_window).2.1

end SevenEighths.DetectorDictionaryInverseClippedUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.DetectorMomentGates
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open CanonicalCoefficientClass InverseInitialExcludedPeriod CanonicalQuadraticSieve
open InverseInitialRayAttachment CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.ProbeHighRowFamily.instFintypeSumBoolSubtypeMulCharQuotientOIdealComplexMemSubgroupCharacters
theorem sourceMomentConductor_le (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    (j:Sum Bool (RayQuotient.Characters M H)):
    ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)<
      sourceMomentConductorBound M H hH S hS η:=by
  have hh:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset (Sum Bool (RayQuotient.Characters M H))))=>
    (Nat.cast_nonneg (α:=ℝ) (baseCharacter (sourceMomentData M H hH S hS η k)).modulus.absNorm))
      (Finset.mem_univ j)
  unfold sourceMomentConductorBound
  linarith

theorem sourceMoment_large_eventually (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    {Slot:Type*}[Fintype Slot](ell:Slot→ℝ)(hell:∀s,0<ell s):
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→
      ∀j:Sum Bool (RayQuotient.Characters M H),∀s:Slot,
        ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)<
          (Z^d)^(ell s/d):=by
  have ht:∀ᶠZ:ℝ in atTop,∀s:Slot,sourceMomentConductorBound M H hH S hS η<Z^(ell s):=by
    apply Filter.eventually_all.mpr
    intro s
    exact (tendsto_rpow_atTop (hell s)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro d hd j s
  rw [←Real.rpow_mul (by linarith:0≤Z),mul_div_cancel₀ _ hd.ne']
  exact (sourceMomentConductor_le M H hH S hS η j).trans (ht s)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayPoolDisjoint
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical
local notation "Id" => Ideal HeckeFamily.O

lemma annular_power_separation (a b r s : ℝ) (ha : 0<a) (hrs : r<s) :
    ∀ᶠZ : ℝ in atTop,b*Z^r<a*Z^s := by
  have hh := (tendsto_rpow_atTop (show 0<s-r by linarith)).eventually (eventually_gt_atTop (b/a))
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  have ht : b<a*Z^(s-r) := by
    have h := (div_lt_iff₀ ha).mp hZ
    nlinarith
  have hp : 0<Z^r := Real.rpow_pos_of_pos hZ0 _
  calc
    b*Z^r < (a*Z^(s-r))*Z^r := mul_lt_mul_of_pos_right ht hp
    _=a*Z^s := by rw [mul_assoc,←Real.rpow_add hZ0];congr 1;congr 1;ring

end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.DetectorMomentFiberGates
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open HeckeDetectorBatch HeckeDetectorRawFiber HeckeDetectorFiberPartition
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem sourceMoment_fiber_large_eventually
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    {Slot:Type*}[Fintype Slot](ell:Slot→ℝ)(hell:∀s,0<ell s):
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→
      ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S hS η→B.widths=(fun s=>ell s/d)→
      ∀bin j J K,∀hne:(B.fiberRows bin j J K).Nonempty,∀s:Slot,
        ((baseCharacter (B.fiber bin j J K hne).rowData).modulus.absNorm:ℝ)<
          1*(Z^d)^((B.fiber bin j J K hne).widths s):=by
  filter_upwards [sourceMoment_large_eventually M H hH S hS η ell hell] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hw bin j J K hne s
  change ((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(B.widths s)
  rw [hdata,hw,one_mul]
  exact hZ.2 d hd j s

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.DetectorMomentPrimeGeometry
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open HeckeDetectorBatch HeckeDetectorRawFiber HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O

theorem sourceMoment_physical_scale (Z d ell : ℝ) (hZ : 0≤Z) (hd : d≠0) :
    (Z^d)^(ell/d)=Z^ell := by
  rw [←Real.rpow_mul hZ,mul_div_cancel₀ _ hd]

theorem sourceMoment_separation_eventually {Slot : Type*} [Fintype Slot]
    (ell : Slot→ℝ) (hinj : Function.Injective ell) :
    ∀ᶠ Z : ℝ in atTop, 1≤Z ∧ ∀d : ℝ,0<d→∀s t : Slot,s≠t→
      2*(Z^d)^(ell s/d)<1*(Z^d)^(ell t/d) ∨
      2*(Z^d)^(ell t/d)<1*(Z^d)^(ell s/d) := by
  have hs : ∀ᶠ Z : ℝ in atTop,∀s t : Slot,s≠t→
      2*Z^(ell s)<1*Z^(ell t) ∨ 2*Z^(ell t)<1*Z^(ell s) := by
    apply Filter.eventually_all.mpr
    intro s
    apply Filter.eventually_all.mpr
    intro t
    by_cases he : s=t
    · exact Filter.Eventually.of_forall (fun _ h=>False.elim (h he))
    rcases lt_or_gt_of_ne (fun h=>he (hinj h)) with hlt|hlt
    · filter_upwards [ProbeRaySlots.annular_power_separation 1 2 (ell s) (ell t)
        (by norm_num) hlt] with Z hZ _
      exact Or.inl hZ
    · filter_upwards [ProbeRaySlots.annular_power_separation 1 2 (ell t) (ell s)
        (by norm_num) hlt] with Z hZ _
      exact Or.inr hZ
  filter_upwards [hs,eventually_ge_atTop (1:ℝ)] with Z hs hZ
  refine ⟨hZ,?_⟩
  intro d hd s t hst
  simp only [sourceMoment_physical_scale Z d _ (by linarith) hd.ne']
  exact hs s t hst

theorem sourceMoment_fixedBase_norm_one (data : RowData) (P : Ideal O) (hP : Prime P)
    (hlarge : ((baseCharacter data).modulus.absNorm:ℝ)<(P.absNorm:ℝ)) :
    ‖fixedBase data.η data.m data.f P‖=1 := by
  rw [←baseCharacter_coeff]
  exact PrincipalSignalComparison.idealCoeff_norm_one_of_coprime
    (baseCharacter data) P hP.ne_zero
    (ProbeRaySlots.prime_coprime_of_norm_gt (baseCharacter data) ⟨P,hP⟩ hlarge)

theorem sourceMoment_primeProfile_norm {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) (X : ℝ) (ζ : ℂ) (hz : ζ.re≤1)
    (P : Ideal O) : ‖primeProfile F.W X ζ P‖≤1 := by
  by_cases hw : F.W ((P.absNorm:ℝ)/X)=0
  · simp [primeProfile,hw]
  have hx := F.complex_support hw
  have hp : 0<(P.absNorm:ℝ)/X := lt_of_lt_of_le (by norm_num) hx.1
  have hnorm : ‖F.W ((P.absNorm:ℝ)/X)‖≤1 := by
    rw [F.complex_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.bounded _).1]
    exact (F.bounded _).2
  rw [primeProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp]
  have hr : ((P.absNorm:ℝ)/X)^((ζ-1).re)≤1 :=
    (Real.rpow_le_rpow_of_exponent_le hx.1
      (show (ζ-1).re≤0 by simp only [Complex.sub_re,Complex.one_re];linarith)).trans_eq
        (Real.rpow_zero _)
  simpa only [one_mul] using mul_le_mul hnorm hr (Real.rpow_nonneg hp.le _) (by norm_num : (0:ℝ)≤1)

section Live
variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem sourceMoment_live_disjoint {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) {ι : Type*} (ell : ι→ℝ)
    (U : ℝ) (hU : 0<U) (s t : ι)
    (hsep : 2*U^(ell s)<1*U^(ell t) ∨ 2*U^(ell t)<1*U^(ell s)) :
    Disjoint (livePrimes M H F.W 2 (U^(ell s))) (livePrimes M H F.W 2 (U^(ell t))) := by
  apply Finset.disjoint_left.mpr
  intro P hs ht
  have hs' := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support P hs
  have ht' := livePrime_data M H F.W 1 2 (U^(ell t))
    (Real.rpow_pos_of_pos hU _) F.complex_support P ht
  rcases hsep with hsep|hsep <;> linarith [hs'.2.2.1,hs'.2.2.2,ht'.2.2.1,ht'.2.2.2]

theorem sourceMoment_live_denominator {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (hU : 0<U)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=>livePrimes M H F.W 2 (U^(ell s)))) :
    ‖fixedBase data.η data.m data.f (∏s,p s)‖=1 := by
  rw [map_prod,norm_prod]
  apply Finset.prod_eq_one
  intro s _
  have hs := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support (p s) (Fintype.mem_piFinset.mp hp s)
  exact sourceMoment_fixedBase_norm_one data (p s) hs.1 ((hlarge s).trans_le hs.2.2.1)

theorem sourceMoment_live_quotient_norm {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (ζ : ι→ℂ) (hU : 0<U)
    (hz : ∀s,(ζ s).re=17/50)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=>livePrimes M H F.W 2 (U^(ell s)))) :
    ‖star (∏s,primeProfile F.W (U^(ell s)) (ζ s) (p s))/
      fixedBase data.η data.m data.f (∏s,p s)‖≤1 := by
  rw [norm_div,norm_star,sourceMoment_live_denominator M H F data U ell hU hlarge p hp,
    div_one,norm_prod]
  exact Finset.prod_le_one (fun s _=>norm_nonneg _)
    (fun s _=>sourceMoment_primeProfile_norm F _ _ (by rw [hz s];norm_num) _)
end Live

theorem sourceMoment_capacity_eventually {Slot : Type*} [Fintype Slot]
    (ell : Slot→ℝ) (hell : ∀s,0≤ell s) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,1≤Z ∧ ∀d : ℝ,1/200≤d→
      (∀s,1≤2*(Z^d)^(ell s/d)) ∧ ∀selected : Finset Slot,
      (∏s:selected,2*(Z^d)^(ell s/d))≤
        (Z^d)^((∑s:selected,ell s/d)+ε) := by
  have ht := (tendsto_rpow_atTop (show 0<ε/200 by positivity)).eventually
    (eventually_ge_atTop ((2:ℝ)^Fintype.card Slot))
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with Z ht hZ
  refine ⟨hZ,?_⟩
  intro d hd
  have hd0 : 0<d := by linarith
  have hz0 : 0<Z := zero_lt_one.trans_le hZ
  have hu0 : 0<Z^d := Real.rpow_pos_of_pos hz0 _
  have hu1 : 1≤Z^d := Real.one_le_rpow hZ hd0.le
  refine ⟨?_,?_⟩
  · intro s
    have hh : 1≤(Z^d)^(ell s/d) := Real.one_le_rpow hu1 (div_nonneg (hell s) hd0.le)
    linarith
  · intro selected
    have hf : (2:ℝ)^selected.card≤(2:ℝ)^Fintype.card Slot :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ selected)
    have hp : (2:ℝ)^selected.card≤(Z^d)^ε := by
      rw [←Real.rpow_mul hz0.le]
      exact (hf.trans ht).trans (Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith))
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
      ←Real.rpow_sum_of_pos hu0,Real.rpow_add hu0]
    calc
      _ ≤ (Z^d)^ε*(Z^d)^(∑s:selected,ell s/d) :=
        mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hu0.le _)
      _ = _ := mul_comm _ _

section Source
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem sourceMoment_fiber_prime_geometry_eventually
    {Δ : ℝ} {D : Parameters.HighData Δ} (F : ProbeFinalAssembly.SourceData D)
    (η : Character) (εg : ℝ) (hεg : 0<εg) :
    ∀ᶠ Z : ℝ in atTop,1≤Z ∧ ∀d : ℝ,1/200≤d→
      ∀(a ε tstar T allowance : ℝ)(i : ℕ)
      (B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH F.S F.exclusions.prime η→
      B.profile=(fun _ x=>(F.w x:ℂ))→B.upper=(fun _=>2)→
      B.widths=(fun s=>D.ell s/d)→(∀s,(B.external s).re=17/50)→
      ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      let f:=B.fiber bin j J K hne
      (∀s t,s≠t→Disjoint
        (livePrimes M H (f.profile s) (f.upper s) ((Z^d)^(f.widths s)))
        (livePrimes M H (f.profile t) (f.upper t) ((Z^d)^(f.widths t)))) ∧
      ∀selected : Finset (Fin D.N),
        (∀s:selected,1≤2*(Z^d)^(f.widths s)) ∧
        (∏s:selected,2*(Z^d)^(f.widths s))≤
          (Z^d)^((∑s:selected,f.widths s)+εg) ∧
        ∀p : selected→Ideal O,
        p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (f.profile s) (f.upper s) ((Z^d)^(f.widths s)))→
        Function.Injective p ∧ CanonicalQuadraticSieve.Admissible (∏s:selected,p s) ∧
        (∀s:selected,((p s).absNorm:ℝ)≤2*(Z^d)^(f.widths s)) ∧
        ‖fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s:selected,p s)‖=1 ∧
        ‖star (∏s:selected,primeProfile (f.profile s) ((Z^d)^(f.widths s)) (f.external s) (p s))/
          fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s:selected,p s)‖≤1 := by
  filter_upwards [sourceMoment_separation_eventually D.ell D.slots_injective,
    sourceMoment_capacity_eventually D.ell (fun s=>(D.slots_bounds s).1.le) εg hεg,
    sourceMoment_fiber_large_eventually M H hH F.S F.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1)] with Z hsep hcap hlarge
  refine ⟨hsep.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz bin j J K hne
  have hprofile : B.profile=(fun _=>(F.W:ℝ→ℂ)) := by
    rw [hprofile0]
    funext s x
    exact (F.complex_eq x).symm
  have hd0 : 0<d := by linarith
  have hu : 0<Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans_le hsep.1) _
  have hs := hsep.2 d hd0
  have hc := hcap.2 d hd
  have hl := hlarge.2 d hd0 a ε tstar T allowance i B hdata hwidths bin j J K hne
  dsimp only
  change (∀s t,s≠t→Disjoint
      (livePrimes M H (B.profile s) (B.upper s) ((Z^d)^(B.widths s)))
      (livePrimes M H (B.profile t) (B.upper t) ((Z^d)^(B.widths t)))) ∧ _
  refine ⟨?_,?_⟩
  · intro s t hst
    rw [hprofile,hupper,hwidths]
    exact sourceMoment_live_disjoint M H F (fun s=>D.ell s/d) (Z^d) hu s t (hs s t hst)
  · intro selected
    change (∀s:selected,1≤2*(Z^d)^(B.widths s)) ∧
      (∏s:selected,2*(Z^d)^(B.widths s))≤(Z^d)^((∑s:selected,B.widths s)+εg) ∧ _
    refine ⟨?_,?_,?_⟩
    · rw [hwidths]
      exact fun s=>hc.1 s
    · rw [hwidths]
      exact hc.2 selected
    · intro p hp
      have hp' : p∈Fintype.piFinset (fun s:selected=>livePrimes M H F.W 2 ((Z^d)^(D.ell s/d))) := by
        change p∈Fintype.piFinset (fun s:selected=>livePrimes M H (B.profile s) (B.upper s) ((Z^d)^(B.widths s))) at hp
        simpa only [hprofile,hupper,hwidths] using hp
      have hl' : ∀s:selected,((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(D.ell s/d) := by
        intro s
        have hh:=hl s
        change ((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(B.widths s) at hh
        simpa only [hwidths] using hh
      have hs' : ∀s t:selected,s≠t→2*(Z^d)^(D.ell s/d)<1*(Z^d)^(D.ell t/d) ∨
          2*(Z^d)^(D.ell t/d)<1*(Z^d)^(D.ell s/d) := by
        intro s t hst
        exact hs s t (fun he=>hst (Subtype.ext he))
      refine ⟨?_,?_,?_,?_,?_⟩
      · exact live_tuple_injective M H (fun _=>F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=>D.ell s/d) (Z^d) hu (fun _=>F.complex_support) hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · exact live_tuple_admissible M H (B.data j) (fun _=>F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=>D.ell s/d) (Z^d) hu (fun _=>F.complex_support) hl' hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · intro s
        change ((p s).absNorm:ℝ)≤2*(Z^d)^(B.widths s)
        rw [hwidths]
        exact (livePrime_data M H F.W 1 2 ((Z^d)^(D.ell s/d))
          (Real.rpow_pos_of_pos hu _) F.complex_support (p s) (Fintype.mem_piFinset.mp (by simpa only [Fintype.mem_piFinset] using hp') s)).2.2.2
      · exact sourceMoment_live_denominator M H F (B.data j) (Z^d)
          (fun s:selected=>D.ell s/d) hu hl' p (by simpa only [Fintype.mem_piFinset] using hp')
      · change ‖star (∏s:selected,primeProfile (B.profile s) ((Z^d)^(B.widths s)) (B.external s) (p s))/
          fixedBase (B.data j).η (B.data j).m (B.data j).f (∏s:selected,p s)‖≤1
        rw [hprofile,hwidths]
        exact sourceMoment_live_quotient_norm M H F (B.data j) (Z^d)
          (fun s:selected=>D.ell s/d) (fun s:selected=>B.external s) hu (fun s=>hz s) hl' p (by simpa only [Fintype.mem_piFinset] using hp')

end Source
end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferencePrimeGates
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap Filter CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O"=>HeckeFamily.O

theorem deleted_large_eventually {Label Slot:Type*}[Fintype Label][Fintype Slot]
    (data:Label→RowData)(ell:Slot→ℝ)(hell:∀s,0<ell s) :
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)<(Z^d)^(ell s/d) := by
  have ht:∀ᶠZ:ℝ in atTop,∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)<Z^(ell s) := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro s
    exact (tendsto_rpow_atTop (hell s)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro d hd j s
  rw [←Real.rpow_mul (by linarith:0≤Z),mul_div_cancel₀ _ hd.ne']
  exact ht j s

theorem deletedBase_supported (data:RowData)(I:Ideal O)
    (hI:idealCoeff (deletedBase data) I≠0) : CanonicalQuadraticSieve.Supported I := by
  by_contra hn
  exact hI (deletedBase_zero_unsupported data I hn)

theorem deleted_source_live_prime {Δ:ℝ}{D:Parameters.HighData Δ}
    (F:ProbeFinalAssembly.SourceData D)(data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
    (X:ℝ)(hX:0<X)(ζ:ℂ)(hζ:ζ.re≤1)
    (hlarge:((deletedBase data).modulus.absNorm:ℝ)<X)
    (P:Ideal O)(hP:P∈livePrimes M H F.W 2 X) :
    Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧
      ‖star (primeProfile F.W X ζ P)/idealCoeff (deletedBase data) P‖≤1 := by
  have hd:=livePrime_data M H F.W 1 2 X hX F.complex_support P hP
  have hcop:=ProbeRaySlots.prime_coprime_of_norm_gt (deletedBase data) ⟨P,hd.1⟩
    (hlarge.trans_le (by simpa only [one_mul] using hd.2.2.1))
  have hn:=PrincipalSignalComparison.idealCoeff_norm_one_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hne:=HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hout:outside (excluded data) P := by
    by_contra hh
    exact hne (deleted_zero_outside (baseCharacter data) (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data)) P hh)
  refine ⟨hd.1,hout,hne,hn,?_⟩
  rw [norm_div,norm_star,hn,div_one]
  exact ProbeHighRowFamily.sourceMoment_primeProfile_norm F X ζ hζ P

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeletedEnergy
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification HeckeDyadic CanonicalQuadraticSieve
open CanonicalRowCompletion ConcretePrimeRowBridge ConcreteTraceCRT
open InverseInitialDetectorSource
open InverseMoment InverseInitialProfile InverseInitialRawDictionary InverseInitialPhysicalSlots
open InverseInitialConjugateEnergy InverseInitialEnergyCallerWindow InverseInitialExcludedPeriod
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseRawConjugateGates
open IdealMobiusDivisorSum Filter
local notation "O"=>HeckeFamily.O

theorem deletedSelectedSource_tuple {ι:Type*}[Fintype ι](data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (U r bW:ℝ)(b ell:ι→ℝ)(ζ:ι→ℂ)(u:O):
    deletedSelectedSource data M H W V U r 0 0 bW b ell ζ u=
      ∑x:Tuple (fun i=>livePrimes M H (V i) (b i) (U^(ell i))),
        (∏i,star (primeProfile (V i) (U^(ell i)) (ζ i) (x i).val)/
          idealCoeff (deletedBase data) (x i).val)*
        originalTotalPolynomial (originalSource U r bW) (∏i,(x i).val)
          (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u := by
  rw [sum_tuple_original (fun i=>livePrimes M H (V i) (b i) (U^(ell i)))
    (fun x=>(∏i,star (primeProfile (V i) (U^(ell i)) (ζ i) (x i))/
      idealCoeff (deletedBase data) (x i))*
      originalTotalPolynomial (originalSource U r bW) (∏i,x i)
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u)]
  unfold deletedSelectedSource
  apply Finset.sum_congr rfl
  intro x hx
  simp only [star_prod,map_prod,Finset.prod_div_distrib]
  have ht:twistedProfile W 0 0=W:=by
    funext t
    simp [twistedProfile,HeckeDyadic.shift]
  rw [ht]
  rfl

theorem deleted_source_energy {Δ:ℝ}{D:Parameters.HighData Δ}
    (F:ProbeFinalAssembly.SourceData D)
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃degree:ℕ,∀data:RowData,∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U →
    ∀{ι:Type}[Fintype ι],Fintype.card ι≤K →
    ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(ell:ι→ℝ)(ζ:ι→ℂ),
      (∀i,0≤ell i) → (∀i,(ζ i).re≤1) →
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint
        (fun i=>livePrimes M H F.W 2 (U^(ell i)))) →
      (∀i,((deletedBase data).modulus.absNorm:ℝ)<U^(ell i)) →
    ∀r:ℝ,0≤ r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
    ∀j∈idealDivisors (∏P∈excluded data,P),
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U) → ∀θ:ℝ,
      (∑u∈rows,‖deletedSelectedSource data M H (childLogTest W θ) (fun _=>F.W)
        U (shiftedExponent data U r j) 0 0 bo (fun _=>2) ell ζ u‖^2)≤
        C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨eta,heta,degree,henergy⟩:=padded_source_energy W ao bo hao hab hsW hW εm hεm K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩:=raw_conjugate_base_gates data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy (deletedPeriod (basePeriod data)) hq
  obtain ⟨Ushift,hshift⟩:=eventually_atTop.mp (marked_shift_eventually data eta heta)
  refine ⟨C,max U₀ Ushift,hC,lt_max_of_lt_left hU₀,?_⟩
  intro U hU ι inst hK M neM H ell ζ hell hζ hdis hlarge r hr hfirst hsecond j hj rows hrows θ
  have hU0:U₀≤U:=(le_max_left _ _).trans hU
  have hUone:1<U:=hU₀.trans_le hU0
  have hUp:0<U:=zero_lt_one.trans hUone
  have hjshift: r-eta≤ shiftedExponent data U r j ∧ shiftedExponent data U r j≤ r ∧
      U^(shiftedExponent data U r j)=U^r/(j.absNorm:ℝ):=
    (hshift U ((le_max_right _ _).trans hU)).2 j hj r
  let L:ι→Finset (Ideal O):=fun i=>livePrimes M H F.W 2 (U^(ell i))
  let coeff:ι→Ideal O→ℂ:=fun i P=>star (primeProfile F.W (U^(ell i)) (ζ i) P)/
    idealCoeff (deletedBase data) P
  have hg (i:ι)(P:Ideal O)(hP:P∈L i):
      Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧
      ‖coeff i P‖≤1:=
    deleted_source_live_prime F data M H _ (Real.rpow_pos_of_pos hUp _) (ζ i) (hζ i) (hlarge i) P hP
  have hratio (i:ι)(P:Ideal O)(hP:P∈L i):((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2:=
    F.complex_support (Finset.mem_filter.mp hP).2
  have hh:=henergy U hU0 hK L ell coeff hell
    (fun i P hP=>(hg i P hP).1)
    (fun i P hP=>deletedBase_supported data P (hg i P hP).2.2.1)
    hdis hratio (fun i P hP=>(hg i P hP).2.2.2.2)
    (fun i P hP=>by rw [hqset];exact (hg i P hP).2.1)
    (fun _=>F.W) (fun _=>F.complex_support)
    (fun i P hP=>(Finset.mem_filter.mp hP).2)
    (idealCoeff (deletedBase data)).toMonoidHom (idealCoeff_norm_le_one (deletedBase data))
    hperiod (fun I hI=>raw_conjugate_zero_outside data I (by simpa [hqset] using hI))
    r (shiftedExponent data U r j) hr hjshift.1 hjshift.2.1 hfirst hsecond rows hrows θ
  simpa only [deletedSelectedSource_tuple,L,coeff] using hh

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceFiberEnergy
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseMoment InverseInitialProfile
open ConcreteTraceCRT ConcretePrimeRowBridge CanonicalRowCompletion
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseMarkedPhysicalRows
open InverseInitialPhysicalSlots IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O

theorem fiber_reference_energy {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:ProbeFinalAssembly.SourceData D)
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃degree:ℕ,∀data:RowData,∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U →
    ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
      {Label Slot:Type}{a ε tstar T allowance:ℝ}{i:ℕ}
      (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot),
      F.rowData=data → selected.card≤K →
      (∀s∈selected,F.profile s=S.W) → (∀s∈selected,F.upper s=2) →
      (∀s∈selected,0≤F.widths s) → (∀s∈selected,(F.external s).re≤1) →
      (((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected)) →
      (∀s∈selected,((deletedBase data).modulus.absNorm:ℝ)<U^(F.widths s)) →
      0≤F.r → F.r+2*(∑s∈selected,F.widths s)<1 →
      2*F.r+8*(∑s∈selected,F.widths s)<3 → ∀v:ℝ,
      (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest W v) (U^F.r) 0 0*
        F.physicalProduct selected u‖^2)≤C*U^(1+εm)*((1+‖v‖)^degree)^2 := by
  have hsor (b:Bool):Function.support (orientedProfile b W)⊆Set.Icc ao bo := by
    cases b
    · exact hsW
    · intro x hx
      apply hsW
      simpa [orientedProfile] using hx
  have hWor (b:Bool):ContDiff ℝ ∞ (orientedProfile b W) := by
    cases b
    · exact hW
    · exact Complex.conjCLE.contDiff.comp hW
  choose J hj using fun b:Bool=>deleted_source_energy S (orientedProfile b W) ao bo hao hab
    (hsor b) (hWor b) εm hεm K
  refine ⟨∑b:Bool,J b,?_⟩
  intro data
  choose C U₀ hC hU₀ hb using fun b:Bool=>hj b data
  let Tbad:=idealDivisors (∏P∈excluded data,P)
  let Ctotal:ℝ:=((Tbad.card:ℝ)+1)^2*(∑b:Bool,C b)
  have hCsum:0<∑b:Bool,C b:=Finset.sum_pos (fun b _=>hC b) Finset.univ_nonempty
  refine ⟨Ctotal,max (U₀ false) (U₀ true),by dsimp [Ctotal];positivity,
    lt_max_of_lt_left (hU₀ false),?_⟩
  intro U hU M neM H Label Slot a ε tstar T allowance i F selected hdata hK hprofile hupper
    hell hext hdis hlarge hr hfirst hsecond v
  have hUb (b:Bool):U₀ b≤U:=by cases b <;> exact le_trans (by simp) hU
  have hUone:1<U:=(hU₀ false).trans_le (hUb false)
  have hpr (s:selected):F.profile s=S.W:=hprofile s s.property
  have hup (s:selected):F.upper s=2:=hupper s s.property
  have hprof:(fun s:selected=>F.profile s)=(fun _=>(S.W:ℝ→ℂ)):=funext hpr
  have hups:(fun s:selected=>F.upper s)=(fun _=>2):=funext hup
  have hslots:∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (1:ℝ) (F.upper s) := by
    intro s hs x hx
    rw [hprofile s hs] at hx
    rw [hupper s hs]
    exact S.complex_support hx
  have hlarge':∀s∈selected,((deletedBase F.rowData).modulus.absNorm:ℝ)<1*U^(F.widths s):=by
    simpa only [hdata,one_mul] using hlarge
  have hphys:=fiber_child_rows_le_deleted_sources F selected W v bo (fun _=>1) hUone
    (fun x hx=>(hsW hx).2) hslots hlarge'
  rw [hdata] at hphys
  let rows:Finset O:=F.rows.image (fun u=>u.val)
  have hsum (f:O→ℝ):(∑u∈rows,f u)=∑u∈F.rows,f u.val:=
    Finset.sum_image (fun u _ w _ he=>Subtype.ext he)
  have hrows:∀u∈rows,‖eisEmbedding u‖^2≤U := by
    intro u hu
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hu
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact F.row_norm w hw
  have hpow (b:Bool):((1+‖orientedFrequency b v‖)^(J b))^2≤
      ((1+‖v‖)^(∑b:Bool,J b))^2 := by
    have hn:‖orientedFrequency b v‖=‖v‖:=by cases b <;> simp [orientedFrequency]
    rw [hn]
    apply pow_le_pow_left₀ (by positivity)
    apply pow_le_pow_right₀ (by linarith [norm_nonneg v])
    exact Finset.single_le_sum (fun b _=>Nat.zero_le _) (Finset.mem_univ b)
  have hterm (j:Ideal O)(hj:j∈Tbad):
      (∑u∈F.rows,‖deletedSelectedSource data M H
        (childLogTest (orientedProfile F.reverse W) (orientedFrequency F.reverse v))
        (fun s:selected=>F.profile s) U (shiftedExponent data U F.r j)
        0 0 bo (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
        (fun s:selected=>F.external s) u.val‖^2)≤
      (∑b:Bool,C b)*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2 := by
    rw [hprof,hups]
    have hdis':((Finset.univ:Finset selected):Set selected).PairwiseDisjoint
        (fun s:selected=>livePrimes M H S.W 2 (U^(F.widths s))) := by
      have heL:fiberLists F selected=(fun s:selected=>livePrimes M H S.W 2 (U^(F.widths s))) := by
        funext s
        dsimp only [fiberLists]
        rw [hpr s,hup s]
      rwa [heL] at hdis
    have hh:=hb F.reverse U (hUb F.reverse) (by simpa using hK)
      M H (fun s:selected=>F.widths s) (fun s:selected=>F.external s)
      (fun s=>hell s s.property) (fun s=>hext s s.property) hdis'
      (fun s=>hlarge s s.property) F.r hr
      (by simpa only [Finset.sum_coe_sort] using hfirst)
      (by simpa only [Finset.sum_coe_sort] using hsecond) j hj rows hrows (orientedFrequency F.reverse v)
    rw [hsum] at hh
    refine hh.trans ?_
    apply mul_le_mul _ (hpow F.reverse) (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact Finset.single_le_sum (fun b _=>(hC b).le) (Finset.mem_univ F.reverse)
  refine hphys.trans ?_
  change (Tbad.card:ℝ)*(∑j∈Tbad,_)≤_
  calc
    _≤(Tbad.card:ℝ)*(∑j∈Tbad,(∑b:Bool,C b)*U^(1+εm)*
        ((1+‖v‖)^(∑b:Bool,J b))^2):=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _=(Tbad.card:ℝ)^2*(∑b:Bool,C b)*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2:=by
      simp only [Finset.sum_const,nsmul_eq_mul];ring
    _≤Ctotal*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2:=by
      dsimp [Ctotal]
      gcongr
      nlinarith [show 0≤(Tbad.card:ℝ) by positivity]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.DetectorInverseMarkedField
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology SchwartzMap ContDiff
namespace SevenEighths.ProbeDetectorInverseMarkedField
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily ProbeFinalAssembly Filter
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseClippedUniform
local notation "O"=>HeckeFamily.O

variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.ProbeDetectorInverseMarkedField.instFiniteQuotientOIdeal
attribute [local instance] OAI.SevenEighths.ProbeDetectorInverseMarkedField.instFintypeSumBoolSubtypeMulCharQuotientOIdealComplexMemSubgroupCharacters
theorem source_batch_inverse_marked_oai {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀d:ℝ,(1/200:ℝ)≤d →
    ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S.S S.exclusions.prime η →
      B.profile=(fun _ x=>(S.w x:ℂ)) → B.upper=(fun _=>2) →
      B.widths=(fun s=>D.ell s/d) → (∀s,(B.external s).re=17/50) →
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height →
    let F:=B.fiber bin label left right hne;
    ∀selected:Finset (Fin D.N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
    ∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
        ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2)≤
        (C*(1+height)^J)*(Z^d)^(1+D.t) := by
  obtain ⟨Jref,hreference⟩:=fiber_reference_energy S referenceWindow (1/18) (13/4)
    (by norm_num) (by norm_num)
    (fun x hx=>referenceWindow_support (subset_tsupport _ hx)) (referenceWindow.smooth ⊤)
    D.t D.t_pos D.N
  obtain ⟨J,Cfourier,hCfourier,hfourier⟩:=DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform Jref
  refine ⟨J,?_⟩
  intro η
  let data:=sourceMomentData M H hH S.S S.exclusions.prime η
  choose C U₀ hC hU₀ hb using fun label=>hreference (data label)
  let Csum:ℝ:=1+∑label,C label
  have hCsum:0<Csum:=by
    have hh:=Finset.sum_nonneg (fun label (_:label∈Finset.univ)=>(hC label).le)
    dsimp [Csum];linarith
  have hClabel (label):C label≤Csum:=by
    have hh:=Finset.single_le_sum (fun label (_:label∈Finset.univ)=>(hC label).le) (Finset.mem_univ label)
    dsimp [Csum];linarith
  have hscale:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤d → U₀ label≤Z^d := by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (U₀ label) (by norm_num)
  refine ⟨Cfourier*Csum,mul_pos hCfourier hCsum,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),hscale,
    deleted_large_eventually data D.ell (fun s=>(D.slots_bounds s).1),
    sourceMoment_fiber_prime_geometry_eventually M H hH S η D.t D.t_pos] with Z hZ hscale hlarge hgeom
  refine ⟨hZ,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz bin label left right hne
    height hheight F selected hselected hfirst hsecond n hn s hs t ht
  have hd0:0<d:=by linarith
  have hUone:1<Z^d:=Real.one_lt_rpow hZ hd0
  have hUp:0<Z^d:=zero_lt_one.trans hUone
  have hprofile:B.profile=(fun _=>(S.W:ℝ→ℂ)) := by
    rw [hprofile0]
    funext j x
    exact (S.complex_eq x).symm
  have hfd:F.rowData=data label:=by change B.data label=data label;rw [hdata]
  have hfp (j):F.profile j=S.W:=by change B.profile j=S.W;rw [hprofile]
  have hfu (j):F.upper j=2:=by change B.upper j=2;rw [hupper]
  have hfw (j):F.widths j=D.ell j/d:=by change B.widths j=_;rw [hwidths]
  have hfe (j):(F.external j).re≤1:=by change (B.external j).re≤1;rw [hz j];norm_num
  have hdis:((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected) := by
    intro j hj k hk hjk
    exact (hgeom.2 d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz
      bin label left right hne).1 j k (fun he=>hjk (Subtype.ext he))
  have hlargeF:∀j∈selected,((DetectorDictionaryInverseRawInitialGates.deletedBase (data label)).modulus.absNorm:ℝ)<
      (Z^d)^(F.widths j) := by
    intro j hj
    rw [hfw]
    exact hlarge.2 d hd0 label j
  have hr:0≤F.r:=Real.logb_nonneg hUone (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have href (v:ℝ):
      (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest referenceWindow v)
        ((Z^d)^F.r) 0 0*F.physicalProduct selected u‖^2)≤
      (Csum*(Z^d)^(1+D.t))*(1+‖v‖)^(2*Jref) := by
    have hh:=hb label (Z^d) (hscale label d hd) M H F selected hfd
      (by simpa using Finset.card_le_univ selected) (fun j _=>hfp j) (fun j _=>hfu j)
      (fun j hj=>(F.widths_pos j (hselected hj)).le) (fun j _=>hfe j) hdis hlargeF hr hfirst hsecond v
    rw [(show 2*Jref=Jref*2 by omega),pow_mul]

    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (hClabel label) (Real.rpow_nonneg hUp.le _)
  have hh:=hfourier F selected hUp (Csum*(Z^d)^(1+D.t)) (by positivity) href
    n hn s hs height t hheight ht
  convert (preTransparency := .instances) hh using 1 ; ring

end SevenEighths.ProbeDetectorInverseMarkedField

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeDetectorInverseMarkedField.source_batch_inverse_marked_oai := @OAI.SevenEighths.ProbeDetectorInverseMarkedField.source_batch_inverse_marked_oai
