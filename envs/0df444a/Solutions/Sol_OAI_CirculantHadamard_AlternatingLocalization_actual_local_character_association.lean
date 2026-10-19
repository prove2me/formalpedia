-- Prove2me | solution 1 for OAI.CirculantHadamard.AlternatingLocalization.actual_local_character_association
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:00:34.963997+00:00
-- url     : https://prove2.me/submissions/6a637272-fc78-4b3e-a861-9d36b0b8cc1f

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingLocalization.lean:L348-L439
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.AlternatingLocalization.actual_local_character_association. The node keeps its source
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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CoefficientEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingLocalization
import Theorems.Thm_OAI_CirculantHadamard_LocalComparison_local_character_comparison

-- ---- from OAI.LinearAlgebra.CirculantHadamard.AlternatingLocalization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uR uK uAZero uS uL uI uk

/-!
# Local representatives of the fixed alternating product

All local rings are actual localizations at maximal ideals. Their maps
into the common fraction field are canonical. The adjoined-root comparison
map is constructed from the actual base-ring inclusion and cyclotomic relation.
Membership in every maximal localization implies membership in the base ring.
-/

noncomputable section

namespace CirculantHadamard.AlternatingLocalization

open scoped BigOperators

section ActualComparisonMap

variable {A₀ : Type uAZero} {R : Type uR} [CommRing A₀] [CommRing R]

/-- Residue characteristic is derived from membership of the rational prime,
not assumed as an independent property of the chosen maximal ideal. -/
theorem residue_charP (m : MaximalSpectrum R) (p : ℕ) (hp : p.Prime)
    (hpm : (p : R) ∈ m.asIdeal) :
    CharP (IsLocalRing.ResidueField (AtMaximal R m)) p := by
  let k := IsLocalRing.ResidueField (AtMaximal R m)
  have hpzero : (p : k) = 0 := by
    have hm : algebraMap R (AtMaximal R m) (p : R) ∈
        IsLocalRing.maximalIdeal (AtMaximal R m) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (AtMaximal R m) m.asIdeal _).mpr hpm
    simpa only [map_natCast] using (IsLocalRing.residue_eq_zero_iff _).mpr hm
  exact (CharP.charP_iff_prime_eq_zero hp).mpr hpzero

/-- A p-th root has residue one at every maximal ideal containing p. -/
theorem residue_root_eq_one (m : MaximalSpectrum R) (p : ℕ) (hp : p.Prime)
    (hpm : (p : R) ∈ m.asIdeal) (rho : R) (hrho : rho ^ p = 1) :
    IsLocalRing.residue (AtMaximal R m) (algebraMap R (AtMaximal R m) rho) = 1 := by
  let k := IsLocalRing.ResidueField (AtMaximal R m)
  let : Fact p.Prime := ⟨hp⟩
  let : CharP k p := residue_charP m p hp hpm
  let r : k := IsLocalRing.residue (AtMaximal R m)
    (algebraMap R (AtMaximal R m) rho)
  have hpow : r ^ p = 1 := by
    dsimp [r]
    rw [← map_pow, ← map_pow, hrho, map_one, map_one]
  have hnil : (r - 1) ^ p = 0 := by rw [sub_pow_char, hpow, one_pow, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hnil)

theorem residue_unit_eq_one_of_span {S : Type uS} {L : Type uL} [CommRing S] [CommRing L]
    [IsLocalRing L] (f : S →+* L) (rho : S) (v : Sˣ)
    (hv : (v : S) - 1 ∈ Ideal.span ({rho - 1} : Set S))
    (hrho : IsLocalRing.residue L (f rho) = 1) :
    IsLocalRing.residue L ((Units.map f.toMonoidHom v : Lˣ) : L) = 1 := by
  let g : S →+* IsLocalRing.ResidueField L := (IsLocalRing.residue L).comp f
  have hspan : Ideal.span ({rho - 1} : Set S) ≤ RingHom.ker g := by
    apply Ideal.span_le.mpr
    intro a ha
    have ha' : a = rho - 1 := Set.mem_singleton_iff.mp ha
    subst a
    change g (rho - 1) = 0
    simp only [map_sub, map_one, RingHom.comp_apply, g, hrho, sub_self]
  have hz := hspan hv
  change g ((v : S) - 1) = 0 at hz
  have hval : g (v : S) = 1 := sub_eq_zero.mp (by simpa only [map_sub, map_one] using hz)
  exact hval

end ActualComparisonMap

section AlternatingUnits

variable {I : Type uI} {R : Type uR} {K : Type uK} {k : Type uk} [DecidableEq I] [CommRing R] [Field K] [Field k]

end AlternatingUnits

section MaximalCover

variable {I : Type uI} {R : Type uR} {K : Type uK} [DecidableEq I] [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

end MaximalCover

section ConcreteComparison

open CyclicRing

variable {A₀ : Type uAZero} {R : Type uR} [CommRing A₀] [CommRing R]

/-- Apply the proved DVR comparison after coefficient localization and map its
actual unit through the cyclotomic quotient into the target maximal localization.
The group order and scalar prime exponent are the same `p ^ (e + 1)`. -/
theorem actual_local_character_association
    (f : A₀ →+* R) (m : MaximalSpectrum R)
    [IsDomain (AtComap f m)] [CharZero (AtComap f m)]
    [IsDiscreteValuationRing (AtComap f m)]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpm : (p : R) ∈ m.asIdeal)
    (hmax : IsLocalRing.maximalIdeal (AtComap f m) =
      Ideal.span {(p : AtComap f m)})
    (rho : R) (hrho : rho ^ p = 1)
    (hroot : (Polynomial.cyclotomic p R).eval rho = 0)
    (n e c : ℕ) [NeZero n] (hn : n = p ^ (e + 1))
    (hrhon : rho ^ n = 1) (hc : IsUnit (c : AtComap f m))
    (F K : Elem A₀ n)
    (hFK : F * K = scalar n ((p : A₀) ^ (e + 1) * (c : A₀))) :
    LocalComparison.ResidueOneAssociated (IsLocalRing.residue (AtMaximal R m))
      (algebraMap R (AtMaximal R m)
        (evaluate f (CyclicPolynomial.powerCharacter n rho hrhon) F))
      (algebraMap R (AtMaximal R m) (evaluate f 1 F)) := by
  subst n
  let A := AtComap f m
  let L := AtMaximal R m
  let φ : A₀ →+* A := algebraMap A₀ A
  let FA := coefficientMap φ (p ^ (e + 1)) F
  let KA := coefficientMap φ (p ^ (e + 1)) K
  have hFA : FA * KA = scalar (p ^ (e + 1))
      ((p : A) ^ (e + 1) * (hc.unit : A)) := by
    dsimp [FA, KA]
    rw [← map_mul, hFK, coefficientMap_scalar, map_mul, map_pow,
      map_natCast, map_natCast]
  obtain ⟨v, hv, hvspan⟩ :=
    (LocalComparison.local_character_comparison A p hp hmax e hc.unit FA KA hFA).1
  let j : RamifiedLocal.Extension A p 0 →+* L :=
    comparisonToLocal f m (p ^ (0 + 1)) rho (by simpa only [Nat.zero_add, pow_one] using hroot)
  have jroot : j (LocalComparison.orderPRoot A p) = algebraMap R L rho := by
    exact comparisonToLocal_root f m _ rho _
  have jcoeff (a : A) : j (algebraMap A (RamifiedLocal.Extension A p 0) a) =
      baseToLocal f m a := by
    exact comparisonToLocal_of f m _ rho _ a
  have evalRoot :
      (j.comp (LocalComparison.orderPValue A p e).toRingHom).comp
          (coefficientMap φ (p ^ (e + 1))) =
        (algebraMap R L).comp
          (evaluate f (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon)) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      change j (evaluateAt (p ^ (e + 1)) (LocalComparison.orderPRoot A p)
          (LocalComparison.orderPRoot_pow_level A p e)
          (coefficientMap φ (p ^ (e + 1)) (AddMonoidAlgebra.single 0 r))) =
        algebraMap R L (evaluate f
          (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon)
          (AddMonoidAlgebra.single 0 r))
      simp only [coefficientMap_single, evaluateAt_single, evaluate_single,
        CyclicPolynomial.powerCharacter_apply, map_mul, map_pow, jroot,
        jcoeff, φ]
      exact congrArg (fun z : L => z * (algebraMap R L rho) ^ (0 : ZMod (p ^ (e + 1))).val)
        (baseToLocal_algebraMap f m r)
    · intro a
      change j (evaluateAt (p ^ (e + 1)) (LocalComparison.orderPRoot A p)
          (LocalComparison.orderPRoot_pow_level A p e)
          (coefficientMap φ (p ^ (e + 1)) (AddMonoidAlgebra.single a 1))) =
        algebraMap R L (evaluate f
          (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon)
          (AddMonoidAlgebra.single a 1))
      simp only [coefficientMap_single, evaluateAt_single, evaluate_single,
        CyclicPolynomial.powerCharacter_apply, map_mul, map_pow, jroot,
        jcoeff, φ]
      exact congrArg (fun z : L => z * (algebraMap R L rho) ^ a.val)
        (baseToLocal_algebraMap f m (1 : A₀))
  have evalOne : j (algebraMap A (RamifiedLocal.Extension A p 0)
      (augmentation (p ^ (e + 1)) FA)) =
        algebraMap R L (evaluate f 1 F) := by
    rw [jcoeff]
    dsimp [FA]
    rw [augmentation_coefficientMap, baseToLocal_algebraMap,
      evaluate_trivial_eq_augmentation]
  have hres : IsLocalRing.residue L
      ((Units.map j.toMonoidHom v : Lˣ) : L) = 1 := by
    apply residue_unit_eq_one_of_span j (LocalComparison.orderPRoot A p) v
    · exact hvspan
    · rw [jroot]
      exact residue_root_eq_one m p hp hpm rho hrho
  refine ⟨Units.map j.toMonoidHom v, ?_, hres⟩
  have heval := DFunLike.congr_fun evalRoot F
  change j (LocalComparison.orderPValue A p e FA) =
    algebraMap R L (evaluate f
      (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon) F) at heval
  rw [← heval]
  change j (LocalComparison.orderPValue A p e FA) =
    j (v : RamifiedLocal.Extension A p 0) * algebraMap R L (evaluate f 1 F)
  simpa only [map_mul, evalOne, Units.coe_map] using congrArg j hv

end ConcreteComparison

section ActualAlternatingProduct

open CyclotomicRings PrimeComponents PrimeCharacterEvaluations CyclicRing

end ActualAlternatingProduct

end CirculantHadamard.AlternatingLocalization

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.AlternatingLocalization
open scoped BigOperators
open CyclicRing


theorem solution.{uR,uAZero} : type_of% @_root_.OAI.CirculantHadamard.AlternatingLocalization.actual_local_character_association.{uR,uAZero} := @_root_.OAI.CirculantHadamard.AlternatingLocalization.actual_local_character_association.{uR,uAZero}
