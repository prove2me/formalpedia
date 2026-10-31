-- Prove2me | solution 1 for HuangN13.N13MumfordFullKummerTwoSurjective.twoSurjective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:25:21.930994+00:00
-- url     : https://prove2.me/submissions/6212640d-3ce9-46b8-8d0b-4c58aaf3d63c

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_HuangN13_N13GaussianGlobalZeroCarrierDlog_actualKummer_trivial
import Theorems.Thm_MazurProof_N13FullNormPairGaussian_norm_gaussianI
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianI_sq
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_sexticToGaussian_bijective
import Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_exists_pade_graph_scalar_of_c_ne_zero
import Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_exists_pade_graph_scalar_of_c_ne_zero_degree_one
import Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_exists_pade_sextic_scalar
import Theorems.Thm_MazurProof_N13MumfordFullKummerIdentityFiber_orientedMumfordFullClass_eq_one_iff_exists_gauge

set_option autoImplicit false

section
section
set_option autoImplicit false
open Algebra Module Polynomial
namespace MazurProof.N13GaussianFieldEquiv
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs
def sexticEquivGaussian : Ls ≃ₐ[ℚ] Lg :=
  AlgEquiv.ofBijective sexticToGaussian
    sexticToGaussian_bijective
end
end MazurProof.N13GaussianFieldEquiv
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GaussianGlobalZeroCarrierDlog
noncomputable section
open N13GaussianGlobalReductionTwo
open N13GaussianLowDegree
open N13GaussianOrderTwo
open N13GaussianNamedUnitSquareclasses
attribute [local instance] MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- The genuine N13 fake-Kummer homomorphism is unconditionally trivial. -/
theorem actualKummer_trivial :
    ∀ P : N13FakeDescentAssembly.G,
      N13FakeDescentAssembly.actualKummer P = 0 := by
  exact HuangN13.N13GaussianGlobalZeroCarrierDlog.actualKummer_trivial
end
end MazurProof.N13GaussianGlobalZeroCarrierDlog
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FullNormPairGaussian
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs
/-- The Gaussian unit transported into the original sextic presentation. -/
def sexticI : Ls :=
  N13GaussianFieldEquiv.sexticEquivGaussian.symm
    N13GaussianFieldEquiv.gaussianI
end
end MazurProof.N13FullNormPairGaussian
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FullNormPairGaussian
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs
@[simp] theorem sexticEquivGaussian_sexticI :
    N13GaussianFieldEquiv.sexticEquivGaussian sexticI =
      N13GaussianFieldEquiv.gaussianI := by
  simp [sexticI]
end
end MazurProof.N13FullNormPairGaussian
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FullNormPairGaussian
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13FullNormPairGaussian.fieldLg MazurProof.N13FullNormPairGaussian.fieldLs
@[simp] theorem sexticI_sq :
    sexticI ^ 2 = -1 := by
  apply N13GaussianFieldEquiv.sexticEquivGaussian.injective
  simp [MazurProof.N13GaussianFieldEquiv.gaussianI_sq]
end
end MazurProof.N13FullNormPairGaussian
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FullNormPairGaussian
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg MazurProof.N13GaussianFieldEquiv.fieldLs MazurProof.N13FullNormPairGaussian.fieldLg MazurProof.N13FullNormPairGaussian.fieldLs
@[simp] theorem norm_sexticI :
    Algebra.norm ℚ sexticI = 1 := by
  calc
    Algebra.norm ℚ sexticI =
        Algebra.norm ℚ
          (N13GaussianFieldEquiv.sexticEquivGaussian
            sexticI) :=
      (Algebra.norm_eq_of_algEquiv
        N13GaussianFieldEquiv.sexticEquivGaussian
        sexticI).symm
    _ = Algebra.norm ℚ
        N13GaussianFieldEquiv.gaussianI := by
      rw [sexticEquivGaussian_sexticI]
    _ = 1 := norm_gaussianI
end
end MazurProof.N13FullNormPairGaussian
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FullNormPairGaussian
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13FullNormPairGaussian.fieldLs
/-- The transported Gaussian element as a sextic-field unit. -/
def sexticIUnit : Lsˣ :=
  Units.mk0 sexticI (by
    intro h
    have hi := sexticI_sq
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hi
    norm_num at hi)
end
end MazurProof.N13FullNormPairGaussian
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FullNormPairGaussian
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13FullNormPairGaussian.fieldLs
@[simp] theorem sexticIUnit_sq :
    sexticIUnit ^ 2 = -1 := by
  apply Units.ext
  exact sexticI_sq
end
end MazurProof.N13FullNormPairGaussian
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FullNormPairGaussian
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13FullNormPair.sexticAlgebraField
@[simp] theorem normUnits_sexticIUnit :
    N13FullNormPair.normUnits sexticIUnit = 1 := by
  apply Units.ext
  exact norm_sexticI
end
end MazurProof.N13FullNormPairGaussian
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FullNormPairGaussian
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13FullNormPair.sexticAlgebraField MazurProof.N13FullNormPairGaussian.fieldLs
/-- The sign pair is the product of the Gaussian square/norm gauge and
the `-1` scalar/cubic gauge. -/
theorem signPair_eq_chi_mul_iota :
    EvenSexticNormPair.signPair
        N13FullNormPair.normUnits (-1)
        N13FullNormPair.minusOne_sq =
      EvenSexticNormPair.chi
          N13FullNormPair.normUnits sexticIUnit *
        EvenSexticNormPair.iota
          N13FullNormPair.normUnits
          N13FullNormPair.scalarUnits
          N13FullNormPair.normUnits_scalarUnits (-1) := by
  apply Subtype.ext
  apply Prod.ext
  · change
      (1 : Lsˣ) =
        sexticIUnit ^ 2 *
          N13FullNormPair.scalarUnits (-1)
    rw [sexticIUnit_sq]
    apply Units.ext
    norm_num [N13FullNormPair.scalarUnits,
      FakeSquareClass.scalarUnitsMap]
  · change
      (-1 : ℚˣ) =
        N13FullNormPair.normUnits sexticIUnit *
          (-1 : ℚˣ) ^ 3
    rw [normUnits_sexticIUnit, one_mul]
    norm_num
end
end MazurProof.N13FullNormPairGaussian
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FullNormPairGaussian
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13FullNormPair.sexticAlgebraField
/-- N13 has no residual sign class in the full norm-pair quotient. -/
@[simp] theorem signClass_eq_one :
    N13FullNormPair.signClass = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [signPair_eq_chi_mul_iota]
  apply Subgroup.mul_mem_sup
  · exact ⟨sexticIUnit, rfl⟩
  · exact ⟨(-1 : ℚˣ), rfl⟩
end
end MazurProof.N13FullNormPairGaussian
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MumfordOrientedFullKummer
noncomputable section
attribute [local instance] MazurProof.N13FullNormPair.sexticAlgebraField MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- In the N13 sextic field the Gaussian unit makes the sign class
gauge-trivial.  Hence the fake kernel is a single full-target fibre. -/
theorem structuralKummer_eq_zero_iff_full_eq_one
    (P : G) :
    N13LowDegreeKummerHom.mumfordKummer P = 0 ↔
      orientedFullKummer P = 1 := by
  constructor
  · intro hP
    rcases
        (structuralKummer_eq_zero_iff_full_eq_one_or_sign P).mp hP with
      hone | hsign
    · exact hone
    · exact hsign.trans
        N13FullNormPairGaussian.signClass_eq_one
  · intro hone
    exact
      (structuralKummer_eq_zero_iff_full_eq_one_or_sign P).mpr
        (Or.inl hone)
end
end MazurProof.N13MumfordOrientedFullKummer
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MumfordFullKummerIdentityFiber
noncomputable section
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13FullNormPair.sexticAlgebraField MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- Coordinate form of the same witness.  The first equation is the
branch-algebra square relation; the second is the orientation/norm-root
compatibility which is lost by the fake target. -/
theorem orientedMumfordFullClass_eq_one_iff_exists_coordinates
    (D : LowRep) :
    N13MumfordOrientedFullKummer.orientedMumfordFullClass D = 1 ↔
      ∃ β : Lˣ, ∃ q : ℚˣ,
        N13MumfordKummerValue.uThetaUnit
              (N13LowDegreeKummerHom.asMumford D) =
            β ^ 2 * N13FullNormPair.scalarUnits q ∧
        N13MumfordOrientedFullKummer.orientationSignUnit D *
              N13MumfordKummerNorm.normRootUnit D =
            N13FullNormPair.normUnits β * q ^ 3 := by
  rw [orientedMumfordFullClass_eq_one_iff_exists_gauge]
  constructor
  · rintro ⟨β, q, hpair⟩
    refine ⟨β, q, ?_, ?_⟩
    · exact congrArg
        (EvenSexticNormPair.fstHom
          N13FullNormPair.normUnits) hpair
    · exact congrArg
        (EvenSexticNormPair.sndHom
          N13FullNormPair.normUnits) hpair
  · rintro ⟨β, q, hfst, hsnd⟩
    refine ⟨β, q, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hfst
    · exact hsnd
end
end MazurProof.N13MumfordFullKummerIdentityFiber
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MumfordFullKummerIdentityFiber
noncomputable section
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13FullNormPair.sexticAlgebraField MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- The actual chosen full Kummer lift therefore supplies the same two
coordinate equations for its chosen low-degree representative. -/
theorem orientedFullKummer_eq_one_iff_exists_coordinates
    (P : G) :
    N13MumfordOrientedFullKummer.orientedFullKummer P = 1 ↔
      ∃ β : Lˣ, ∃ q : ℚˣ,
        N13MumfordKummerValue.uThetaUnit
              (N13LowDegreeKummerHom.asMumford
                (N13LowDegreeKummerHom.representative P)) =
            β ^ 2 * N13FullNormPair.scalarUnits q ∧
        N13MumfordOrientedFullKummer.orientationSignUnit
              (N13LowDegreeKummerHom.representative P) *
              N13MumfordKummerNorm.normRootUnit
                (N13LowDegreeKummerHom.representative P) =
            N13FullNormPair.normUnits β * q ^ 3 := by
  exact
    orientedMumfordFullClass_eq_one_iff_exists_coordinates
      (N13LowDegreeKummerHom.representative P)
end
end MazurProof.N13MumfordFullKummerIdentityFiber
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MumfordFullKummerIdentityFiber
noncomputable section
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13FullNormPair.sexticAlgebraField MazurProof.N13FullNormPairGaussian.fieldLs MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- Multiplying the branch square root by the Gaussian `i` and the scalar
by `-1` preserves the first gauge coordinate and flips the norm-root
coordinate.  Thus every full-gauge witness can be put in the sign convention
needed by the Padé resultant argument, independently of the representative's
original infinity integer. -/
theorem exists_negative_norm_gauge_coordinates
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (hfst :
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q)
    (hsnd :
      N13MumfordOrientedFullKummer.orientationSignUnit D *
            N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3) :
    ∃ β' : Lˣ, ∃ q' : ℚˣ,
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
          β' ^ 2 * N13FullNormPair.scalarUnits q' ∧
      (-1 : ℚˣ) *
            N13MumfordKummerNorm.normRootUnit D =
          N13FullNormPair.normUnits β' * q' ^ 3 := by
  rcases
      N13FullNormPair.ratUnit_sq_eq_one
        (N13MumfordOrientedFullKummer.orientationSignUnit D)
        (N13MumfordOrientedFullKummer.orientationSignUnit_sq D) with
    hplus | hminus
  · refine
      ⟨N13FullNormPairGaussian.sexticIUnit * β,
        -q, ?_, ?_⟩
    · rw [hfst, mul_pow,
        N13FullNormPairGaussian.sexticIUnit_sq,
        scalarUnits_neg]
      simp only [neg_mul, mul_neg, neg_neg]
      simp
    · have hsnd' :
          N13MumfordKummerNorm.normRootUnit D =
            N13FullNormPair.normUnits β * q ^ 3 := by
        simpa only [hplus, one_mul] using hsnd
      rw [hsnd', map_mul,
        N13FullNormPairGaussian.normUnits_sexticIUnit,
        one_mul, neg_pow]
      norm_num
  · exact ⟨β, q, hfst, by
      simpa only [hminus] using hsnd⟩
end
end MazurProof.N13MumfordFullKummerIdentityFiber
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MumfordFullKummerIdentityFiber
noncomputable section
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]
attribute [local instance] MazurProof.N13FullNormPair.sexticAlgebraField MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- A negatively normalized full-gauge witness always yields a finite
ideal square.  The proof chooses a Padé numerator by dimension, separates
the genuine UFD branch `c = 0`, and otherwise treats the quotient algebra
according to its rank `0`, `1`, or `2`.  The chosen square root retains a
literal graph-ideal presentation in every branch. -/
def finiteIdealGraphRootData_of_negative_norm_gauge
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (hfst :
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q)
    (hsnd :
      (-1 : ℚˣ) *
            N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3) :
    FiniteIdealGraphRootData D := by
  let haExists :=
    exists_pade_numerator
      (branchSquarePolynomial β)
  let a := Classical.choose haExists
  have haSpec := Classical.choose_spec haExists
  have ha0 := haSpec.1
  have haKer := haSpec.2
  let hcExists :=
    exists_pade_sextic_scalar
      D β q hfst a ha0 haKer
  let c := Classical.choose hcExists
  have hrelation := Classical.choose_spec hcExists
  let l : ℚ[X] :=
    padeRemainderMap (branchSquarePolynomial β) a
  have haPoly : (a : ℚ[X]) ≠ 0 := by
    exact fun h => ha0 (Subtype.ext h)
  by_cases hc : c = 0
  · have hzeroRelation :
        Polynomial.C (q : ℚ) * l ^ 2 =
          (a : ℚ[X]) ^ 2 * D.toSemi.u := by
      have h := hrelation
      change Classical.choose hcExists = 0 at hc
      rw [hc] at h
      simp only [Polynomial.C_0, zero_mul] at h
      exact sub_eq_zero.mp h
    exact
      finiteIdealGraphRootData_of_zero_pade_scalar
        D q (a : ℚ[X]) l haPoly hzeroRelation
  · by_cases hu0 : D.toSemi.u.natDegree = 0
    · exact
        finiteIdealGraphRootData_of_natDegree_zero
          D hu0
    · by_cases hu1 : D.toSemi.u.natDegree = 1
      · let hbExists :=
          exists_pade_graph_scalar_of_c_ne_zero_degree_one
            D q (a : ℚ[X]) l c hrelation hu1 hc
        let b := Classical.choose hbExists
        have hbSpec := Classical.choose_spec hbExists
        have hb := hbSpec.1
        have hbSq := hbSpec.2.1
        have hgraph := hbSpec.2.2
        exact
          (finitePadeGraphRootData
              D q (a : ℚ[X]) l c b
                hrelation hb hbSq hgraph hc haPoly).toFiniteIdealGraphRootData
            haPoly (padeNumerator_natDegree_le_two a ha0)
      · have hu2 : D.toSemi.u.natDegree = 2 := by
          have hle := D.degree_le_two
          omega
        let hbExists :=
          exists_pade_graph_scalar_of_c_ne_zero
            D β q a ha0 haKer c
              hrelation hsnd hu2 hc
        let b := Classical.choose hbExists
        have hbSpec := Classical.choose_spec hbExists
        have hb := hbSpec.1
        have hbSq := hbSpec.2.1
        have hgraph := hbSpec.2.2
        exact
          (finitePadeGraphRootData
              D q (a : ℚ[X]) l c b
                hrelation hb hbSq hgraph hc haPoly).toFiniteIdealGraphRootData
            haPoly (padeNumerator_natDegree_le_two a ha0)
end
end MazurProof.N13MumfordFullKummerIdentityFiber
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MumfordFullKummerIdentityFiber
noncomputable section
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]
attribute [local instance] MazurProof.N13FullNormPair.sexticAlgebraField MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- The original orientation sign can first be normalized by the Gaussian
unit `i`; the preceding theorem then supplies the finite ideal square. -/
def finiteIdealGraphRootData_of_full_gauge
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (hfst :
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q)
    (hsnd :
      N13MumfordOrientedFullKummer.orientationSignUnit D *
            N13MumfordKummerNorm.normRootUnit D =
        N13FullNormPair.normUnits β * q ^ 3) :
    FiniteIdealGraphRootData D := by
  let hcoordinates :=
    exists_negative_norm_gauge_coordinates
      D β q hfst hsnd
  let β' := Classical.choose hcoordinates
  let hq := Classical.choose_spec hcoordinates
  let q' := Classical.choose hq
  have hcoordinates_spec := Classical.choose_spec hq
  exact
    finiteIdealGraphRootData_of_negative_norm_gauge
      D β' q' hcoordinates_spec.1 hcoordinates_spec.2
end
end MazurProof.N13MumfordFullKummerIdentityFiber
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MumfordFullKummerTwoSurjective
noncomputable section
attribute [local instance] MazurProof.N13FullNormPair.sexticAlgebraField MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- Construct the original chosen generic half from its full-gauge witness.
The representative, coordinate choices, ideal root, and half are retained. -/
def constructedHalfDataOfFullGauge (P : G)
    (hfull : N13MumfordOrientedFullKummer.orientedFullKummer P = 1) :
    ConstructedHalfData P := by
  let D := N13LowDegreeKummerHom.representative P
  let hcoordinates :=
    (N13MumfordFullKummerIdentityFiber.orientedFullKummer_eq_one_iff_exists_coordinates
      P).mp hfull
  let β := Classical.choose hcoordinates
  let hq := Classical.choose_spec hcoordinates
  let q := Classical.choose hq
  have hcoordinates_spec := Classical.choose_spec hq
  let root :=
    N13MumfordFullKummerIdentityFiber.finiteIdealGraphRootData_of_full_gauge
      D β q hcoordinates_spec.1 hcoordinates_spec.2
  let finite :=
    N13MumfordFullKummerIdentityFiber.finiteIdealHalfData
      D root
  refine
    { representative := D
      representative_spec :=
        N13LowDegreeKummerHom.lowClass_representative P
      finite := finite
      double_eq := ?_ }
  exact
    (N13LowDegreeKummerHom.lowClass_representative P).symm.trans
      finite.half_spec
end
end MazurProof.N13MumfordFullKummerTwoSurjective
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MumfordFullKummerTwoSurjective
noncomputable section
attribute [local instance] MazurProof.N13FullNormPair.sexticAlgebraField MazurProof.N13MumfordKummerValue.sexticAlgebraField
/-- Apply the original global full-gauge proof to the retained constructor. -/
def constructedHalfData (P : G) :
    ConstructedHalfData P :=
  constructedHalfDataOfFullGauge P
    ((N13MumfordOrientedFullKummer.structuralKummer_eq_zero_iff_full_eq_one
      P).mp
        (N13GaussianGlobalZeroCarrierDlog.actualKummer_trivial P))
end
end MazurProof.N13MumfordFullKummerTwoSurjective
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MumfordFullKummerTwoSurjective
noncomputable section
/-- Multiplication by two is surjective on the concrete N13 Picard group. -/
theorem twoSurjective :
    N13TwoAdicEndgame.TwoSurjective G := by
  intro P
  let D := constructedHalfData P
  exact ⟨D.finite.half, D.double_eq⟩
end
end MazurProof.N13MumfordFullKummerTwoSurjective
end
end

theorem solution :
    MazurProof.N13TwoAdicEndgame.TwoSurjective MazurProof.N13MumfordFullKummerTwoSurjective.G := by
  exact MazurProof.N13MumfordFullKummerTwoSurjective.twoSurjective
