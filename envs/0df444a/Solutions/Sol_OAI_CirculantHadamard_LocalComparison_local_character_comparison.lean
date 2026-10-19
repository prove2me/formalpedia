-- Prove2me | solution 1 for OAI.CirculantHadamard.LocalComparison.local_character_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:48:46.897523+00:00
-- url     : https://prove2.me/submissions/76a69134-89d2-479a-80e3-00cbc275ac9a

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/LocalComparison.lean:L79-L141
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.LocalComparison.local_character_comparison. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjectionPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluationAt
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalComparison
import Theorems.Thm_OAI_CirculantHadamard_LocalComparison_comparison_induction
import Theorems.Thm_OAI_CirculantHadamard_LocalComparison_projected_factor_divisible
import Theorems.Thm_OAI_CirculantHadamard_RamifiedLocal_exists_unit_mul_uniformizer_pow
import Theorems.Thm_OAI_CirculantHadamard_RamifiedLocal_maximal_eq_span_uniformizer

-- ---- from OAI.LinearAlgebra.CirculantHadamard.LocalDVR ----
namespace OAI

universe uR

/-!
# Principal maximal ideals and local factor divisibility

A nonzero principal maximal ideal in a Noetherian local domain gives a DVR
and uniformizer factorizations. Its canonical additive valuation, valued in
`ℕ∞`, splits a product of a prime power and a unit.
-/

noncomputable section

namespace CirculantHadamard.LocalDVR

open IsLocalRing IsDiscreteValuationRing

section PrincipalMaximalIdeal

variable {R : Type uR} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

end PrincipalMaximalIdeal

section Valuation

variable {R : Type uR} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Normalize the additive valuation using the concrete uniformizer relation. -/
theorem addVal_eq_of_unit_mul_uniformizer_pow {π p : R} {u : Rˣ} {D : ℕ}
    (hspan : IsLocalRing.maximalIdeal R = Ideal.span {π}) (hp : p = (u : R) * π ^ D) :
    addVal R p = (D : ℕ∞) :=
  addVal_def p u ((irreducible_iff_uniformizer π).mpr hspan) D hp

end Valuation

end CirculantHadamard.LocalDVR

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.RamifiedEisenstein ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uA uB

/-!
# Eisenstein polynomials for the ramified cyclotomic extension

The maximal ideal is generated by the actual natural prime `p`.  We transport
the integer coefficient divisibilities and prove separately that the constant
term `p` is outside the square of the maximal ideal.  This yields irreducibility
over the local base, and hence the minimal polynomial of an actual primitive
root in any faithful domain extension.
-/

noncomputable section

namespace CirculantHadamard.RamifiedEisenstein

open Polynomial

theorem shifted_monic (A : Type uA) [CommRing A] (p k : ℕ) :
    (shifted A p k).Monic := by
  simpa only [shifted, C_1] using
    (cyclotomic.monic (p ^ (k + 1)) A).comp_X_add_C (1 : A)

theorem shifted_natDegree (A : Type uA) [CommRing A] [IsDomain A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (shifted A p k).natDegree = (p - 1) * p ^ k := by
  rw [shifted, natDegree_comp, show (X + 1 : A[X]) = X + C 1 by simp,
    natDegree_X_add_C, mul_one, natDegree_cyclotomic,
    Nat.totient_prime_pow_succ hp, Nat.mul_comm]

theorem cyclotomic_natDegree (A : Type uA) [CommRing A] [Nontrivial A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (cyclotomic (p ^ (k + 1)) A).natDegree = (p - 1) * p ^ k := by
  rw [natDegree_cyclotomic, Nat.totient_prime_pow_succ hp, Nat.mul_comm]

theorem shifted_coeff_zero (A : Type uA) [CommRing A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (shifted A p k).coeff 0 = (p : A) := by
  rw [shifted, coeff_zero_eq_eval_zero, eval_comp,
    cyclotomic_prime_pow_eq_geom_sum hp, eval_add, eval_X, eval_one, zero_add,
    eval_finsetSum]
  simp only [eval_pow, eval_X, one_pow, Finset.sum_const, Finset.card_range,
    Nat.smul_one_eq_cast]

theorem shifted_isWeaklyEisensteinAt (A : Type uA) [CommRing A]
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (shifted A p k).IsWeaklyEisensteinAt (Ideal.span {(p : A)}) := by
  let : Fact p.Prime := ⟨hp⟩
  have h := (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p k).isWeaklyEisensteinAt.map
    (Int.castRingHom A)
  simpa [shifted, Ideal.submodule_span_eq, Ideal.map_span, Polynomial.map_comp] using h

section Local

variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A] [IsLocalRing A]
  {p : ℕ} (hp : p.Prime) (k : ℕ)
  (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})

include hp hmax

theorem shifted_isEisensteinAt :
    (shifted A p k).IsEisensteinAt (IsLocalRing.maximalIdeal A) := by
  have hp0 : (p : A) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpu : ¬ IsUnit (p : A) :=
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (p : A) hp0 hmax).not_isUnit
  apply (shifted_monic A p k).isEisensteinAt_of_mem_of_notMem
    (Ideal.IsPrime.ne_top inferInstance)
  · intro i hi
    rw [hmax]
    exact (shifted_isWeaklyEisensteinAt A hp k).mem hi
  · rw [shifted_coeff_zero A hp k, hmax, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    intro h
    have h21 : (2 : ℕ) ≤ 1 := (pow_dvd_pow_iff hp0 hpu).mp (by simpa using h)
    exact (by decide : ¬ (2 : ℕ) ≤ 1) h21

theorem shifted_irreducible : Irreducible (shifted A p k) := by
  apply (shifted_isEisensteinAt A hp k hmax).irreducible inferInstance
    (shifted_monic A p k).isPrimitive
  rw [shifted_natDegree A hp k]
  exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k)

theorem cyclotomic_irreducible : Irreducible (cyclotomic (p ^ (k + 1)) A) := by
  apply (MulEquiv.irreducible_iff (Polynomial.algEquivAevalXAddC (1 : A))).mp
  change Irreducible ((cyclotomic (p ^ (k + 1)) A).comp (X + C (1 : A)))
  simpa only [shifted, C_1] using shifted_irreducible A hp k hmax

end Local

section DVR

variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A]
  [IsDiscreteValuationRing A] {p : ℕ} (hp : p.Prime) (k : ℕ)
  (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})

include hp hmax

theorem cyclotomic_prime : Prime (cyclotomic (p ^ (k + 1)) A) :=
  irreducible_iff_prime.mp (cyclotomic_irreducible A hp k hmax)

theorem cyclotomic_adjoinRoot_isDomain :
    IsDomain (AdjoinRoot (cyclotomic (p ^ (k + 1)) A)) :=
  AdjoinRoot.isDomain_of_prime (cyclotomic_prime A hp k hmax)

end DVR

end CirculantHadamard.RamifiedEisenstein

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.RamifiedLocal ----
namespace OAI

universe uA

/-!
# The actual ramified cyclotomic local ring

We adjoin a root of the prime-power cyclotomic polynomial to the given
characteristic-zero DVR. Every maximal ideal of this finite integral extension
is shown to be generated by the actual element `root - 1`.
-/

noncomputable section

namespace CirculantHadamard.RamifiedLocal

open Polynomial

section LocalBase

variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A]
  [IsDiscreteValuationRing A] {p : ℕ} (hp : p.Prime) (k : ℕ)
  (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})

include hp hmax

theorem isDomain : IsDomain (Extension A p k) :=
  RamifiedEisenstein.cyclotomic_adjoinRoot_isDomain A hp k hmax

theorem isLocalRing : IsLocalRing (Extension A p k) := by
  let : IsDomain (Extension A p k) := isDomain A hp k hmax
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Extension A p k)
  let : M.IsMaximal := hM
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨M, hM, ?_⟩
  intro N hN
  let : N.IsMaximal := hN
  exact (maximal_eq_span_uniformizer A hp k hmax N).trans
    (maximal_eq_span_uniformizer A hp k hmax M).symm

variable [IsLocalRing (Extension A p k)]

theorem maximalIdeal_eq_span :
    IsLocalRing.maximalIdeal (Extension A p k) = Ideal.span {uniformizer A p k} :=
  maximal_eq_span_uniformizer A hp k hmax _

omit hmax [CharZero A] [IsLocalRing (Extension A p k)] in
theorem algebraMap_injective [CharZero A] [IsLocalRing (Extension A p k)] : Function.Injective (algebraMap A (Extension A p k)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  apply Polynomial.degree_ne_of_natDegree_ne
  rw [RamifiedEisenstein.cyclotomic_natDegree A hp k]
  exact Nat.ne_of_gt (Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k))

theorem uniformizer_ne_zero : uniformizer A p k ≠ 0 := by
  intro hzero
  have hpS : (p : Extension A p k) ≠ 0 := by
    intro hpzero
    have : algebraMap A (Extension A p k) (p : A) =
        algebraMap A (Extension A p k) 0 := by simpa using hpzero
    exact (Nat.cast_ne_zero.mpr hp.ne_zero : (p : A) ≠ 0)
      (algebraMap_injective A hp k this)
  obtain ⟨u, hu⟩ := exists_unit_mul_uniformizer_pow A hp k hmax
  have hd : (p - 1) * p ^ k ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k))
  exact hpS (by simpa only [hzero, zero_pow hd, mul_zero] using hu)

variable [IsDomain (Extension A p k)]

theorem isDiscreteValuationRing : IsDiscreteValuationRing (Extension A p k) :=
  LocalDVR.isDiscreteValuationRing_of_maximalIdeal_eq_span
    (uniformizer_ne_zero A hp k hmax) (maximalIdeal_eq_span A hp k hmax)

omit [IsLocalRing (Extension A p k)] in
theorem addVal_prime [IsDiscreteValuationRing (Extension A p k)] :
    IsDiscreteValuationRing.addVal (Extension A p k) (p : Extension A p k) =
      (((p - 1) * p ^ k : ℕ) : ℕ∞) := by
  obtain ⟨u, hu⟩ := exists_unit_mul_uniformizer_pow A hp k hmax
  exact LocalDVR.addVal_eq_of_unit_mul_uniformizer_pow
    (maximalIdeal_eq_span A hp k hmax) hu

end LocalBase

end CirculantHadamard.RamifiedLocal

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclicEvaluationProjection ----
namespace OAI

universe uR uS

/-! Evaluation at a root of smaller order factors through the cyclic quotient. -/

noncomputable section

namespace CirculantHadamard

open CyclicRing

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
variable {m n : ℕ} [NeZero m] [NeZero n]

/-- The actual root evaluation is unchanged after reducing the cyclic index.
Both root equations are stated explicitly to match the two evaluation maps. -/
theorem evaluateAt_cyclicProjection (h : m ∣ n)
    (x : S) (hm : x ^ m = 1) (hn : x ^ n = 1) (F : Elem R n) :
    evaluateAt m x hm (cyclicProjection R h F) = evaluateAt n x hn F := by
  refine AddMonoidAlgebra.induction_linear F ?_ ?_ ?_
  · simp
  · intro F G hF hG
    change evaluateAt m x hm (cyclicProjection R h ((F : Elem R n) + G)) =
      evaluateAt n x hn ((F : Elem R n) + G)
    simp only [map_add, hF, hG]
  · intro a r
    simp only [cyclicProjection_single, evaluateAt_single]
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    rw [← pow_eq_pow_mod _ hm]

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.LocalComparison ----
namespace OAI

universe uA

/-!
# Local character comparison in the actual cyclotomic quotient

Starting with a characteristic-zero DVR whose maximal ideal is generated by
the rational prime `p`, all ramified rings needed by the induction are
constructed as the actual cyclotomic quotients. No projection-divisibility,
comparison, or existence-of-valuation premise is taken from the caller.

The conclusion uses membership in the ideal generated by `root - 1` to state
residue one. This is independent of how a local-ring instance is installed and
can be transported directly to a later localization.
-/

noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing Polynomial

variable (A : Type uA) [CommRing A]

theorem orderPValue_projection (p e : ℕ) [NeZero p]
    (F : Elem A (p ^ (e + 2))) :
    orderPValue A p e
        (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) =
      orderPValue A p (e + 1) F :=
  evaluateAt_cyclicProjection _ _ _ _ F

section DVR

variable [IsDomain A] [CharZero A] [IsDiscreteValuationRing A]

/-- Character comparison with every ramified extension constructed from the
input DVR. Both factors are compared, with matching group/scalar exponents. -/
theorem local_character_comparison (p : ℕ) [NeZero p] (hp : p.Prime)
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    (e : ℕ) (b : Aˣ) (F K : Elem A (p ^ (e + 1)))
    (hFK : F * K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A))) :
    OrderPCompared A p e F ∧ OrderPCompared A p e K := by
  let : IsDomain (RamifiedLocal.Extension A p 0) :=
    RamifiedLocal.isDomain A hp 0 hmax
  let : IsLocalRing (RamifiedLocal.Extension A p 0) :=
    RamifiedLocal.isLocalRing A hp 0 hmax
  have hpA : Prime (p : A) :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer (p : A)).mpr hmax).prime
  have hpS : algebraMap A (RamifiedLocal.Extension A p 0) (p : A) ≠ 0 := by
    intro h
    exact hpA.ne_zero (RamifiedLocal.algebraMap_injective A hp 0
      (by simpa only [map_zero] using h))
  have hroot : IsLocalRing.residue (RamifiedLocal.Extension A p 0) (orderPRoot A p) = 1 := by
    have hpi : RamifiedLocal.uniformizer A p 0 ∈
        IsLocalRing.maximalIdeal (RamifiedLocal.Extension A p 0) := by
      rw [RamifiedLocal.maximalIdeal_eq_span A hp 0 hmax]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hz := (IsLocalRing.residue_eq_zero_iff _).mpr hpi
    simpa only [RamifiedLocal.uniformizer, orderPRoot, map_sub, map_one, sub_eq_zero] using hz
  have hc := comparison_induction p (algebraMap A (RamifiedLocal.Extension A p 0))
    hpA hpS (fun k => (orderPValue A p k).toRingHom)
    (fun k a => orderPValue_scalar A p k a)
    (by
      intro U
      change IsLocalRing.residue (RamifiedLocal.Extension A p 0) (orderPValue A p 0 U) =
        IsLocalRing.residue (RamifiedLocal.Extension A p 0)
          (algebraMap A (RamifiedLocal.Extension A p 0) (augmentation (p ^ 1) U))
      simp only [orderPValue, evaluateAt_apply,
        augmentation_apply, map_sum, map_mul, map_pow, hroot, one_pow, mul_one])
    (fun k U => orderPValue_projection A p k U)
    (by
      intro k c U V hUV
      let : IsDomain (RamifiedLocal.Extension A p (k + 1)) :=
        RamifiedLocal.isDomain A hp (k + 1) hmax
      let : IsLocalRing (RamifiedLocal.Extension A p (k + 1)) :=
        RamifiedLocal.isLocalRing A hp (k + 1) hmax
      let : IsDiscreteValuationRing (RamifiedLocal.Extension A p (k + 1)) :=
        RamifiedLocal.isDiscreteValuationRing A hp (k + 1) hmax
      have hpR : (p : RamifiedLocal.Extension A p (k + 1)) ≠ 0 := by
        intro h
        apply hpA.ne_zero
        apply RamifiedLocal.algebraMap_injective A hp (k + 1)
        simpa only [map_natCast, map_zero] using h
      exact projected_factor_divisible hp hpR
        (Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos (k + 1)))
        (RamifiedLocal.addVal_prime A hp (k + 1) hmax) c U V hUV)
    e b F K hFK
  have toCompared {U : Elem A (p ^ (e + 1))}
      (hU : ResidueOneAssociated (IsLocalRing.residue (RamifiedLocal.Extension A p 0))
        (orderPValue A p e U)
        (algebraMap A (RamifiedLocal.Extension A p 0) (augmentation (p ^ (e + 1)) U))) :
      OrderPCompared A p e U := by
    obtain ⟨u, hu, hres⟩ := hU
    refine ⟨u, hu, ?_⟩
    rw [← RamifiedLocal.maximalIdeal_eq_span A hp 0 hmax]
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, hres, map_one, sub_self]
  exact ⟨toCompared hc.1, toCompared hc.2⟩

end DVR

end CirculantHadamard.LocalComparison

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.LocalComparison
open CyclicRing Polynomial


theorem solution.{uA} : type_of% @_root_.OAI.CirculantHadamard.LocalComparison.local_character_comparison.{uA} := @_root_.OAI.CirculantHadamard.LocalComparison.local_character_comparison.{uA}
