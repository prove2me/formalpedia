-- Prove2me | solution 1 for HuangN13.N13RationalPointEndgame.affine_x_is_cuspidal_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:46:34.071983+00:00
-- url     : https://prove2.me/submissions/fded9c6a-86de-4d85-a3f5-c435ea3a1449

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_HuangN13_N13MumfordFullKummerTwoSurjective_twoSurjective

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
theorem X_sub_C_ne_one (x : K) :
    (X - C x : K[X]) ≠ 1 := by
  intro h
  have hc := congrArg (fun p : K[X] ↦ p.coeff 1) h
  rw [coeff_one] at hc
  norm_num at hc
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
theorem X_sub_C_injective :
    Function.Injective (fun x : K ↦ (X - C x : K[X])) := by
  intro x y h
  have hc := congrArg (fun p : K[X] ↦ p.coeff 0) h
  simpa using congrArg Neg.neg hc
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
/-- Distinct projective points have distinct balanced representatives. -/
theorem pointMumford_injective :
    Function.Injective (pointMumford M) := by
  intro P Q hPQ
  cases P with
  | infinityPlus =>
      cases Q with
      | infinityPlus => rfl
      | infinityMinus =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, infinityMinusMumford] at hn
      | affine x y h =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, affinePointMumford] at hn
  | infinityMinus =>
      cases Q with
      | infinityPlus =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, infinityMinusMumford] at hn
      | infinityMinus => rfl
      | affine x y h =>
          have hu := congrArg Mumford.u hPQ
          change (1 : K[X]) = X - C x at hu
          exact False.elim (X_sub_C_ne_one x hu.symm)
  | affine x y h =>
      cases Q with
      | infinityPlus =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, affinePointMumford] at hn
      | infinityMinus =>
          have hu := congrArg Mumford.u hPQ
          change X - C x = (1 : K[X]) at hu
          exact False.elim (X_sub_C_ne_one x hu)
      | affine x' y' h' =>
          have hu := congrArg Mumford.u hPQ
          have hv := congrArg Mumford.v hPQ
          change X - C x = X - C x' at hu
          change C y = C y' at hv
          have hx : x = x' := X_sub_C_injective hu
          have hy : y = y' := C_injective hv
          subst x'
          subst y'
          rfl
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N18RouteC.Separated
noncomputable section
theorem nsmul_nsmul_comm
    {G : Type*} [AddCommGroup G]
    (m n : ℕ) (x : G) :
    m • (n • x) = n • (m • x) := by
  calc
    m • (n • x) = (n * m) • x := (mul_nsmul x n m).symm
    _ = (m * n) • x := by rw [Nat.mul_comm]
    _ = n • (m • x) := mul_nsmul x m n
end
end MazurProof.N18RouteC.Separated
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13SmallMumfordRigidity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
open SexticMumford
theorem eq_of_class_eq_of_small
    (D₁ D₂ : Mumford (N13Mumford.model K))
    (_hsmall₁ : D₁.u.natDegree + D₁.nInf ≤ 1)
    (_hsmall₂ : D₂.u.natDegree + D₂.nInf ≤ 1)
    (hclass :
      classOf (N13Mumford.model K)
          (N13Infinity.positiveInfinityOrder K) D₁ =
        classOf (N13Mumford.model K)
          (N13Infinity.positiveInfinityOrder K) D₂) :
    D₁ = D₂ :=
  eq_of_class_eq K D₁ D₂ hclass
end
end MazurProof.N13SmallMumfordRigidity
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13SmallMumfordRigidity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
open SexticMumford
theorem pointMumford_small
    (P : CurvePoint (N13Mumford.model K)) :
    (pointMumford (N13Mumford.model K) P).u.natDegree +
        (pointMumford (N13Mumford.model K) P).nInf ≤ 1 := by
  cases P with
  | infinityPlus =>
      simp [pointMumford, zero]
  | infinityMinus =>
      simp [pointMumford, infinityMinusMumford]
  | affine x y h =>
      simp [pointMumford, affinePointMumford]
end
end MazurProof.N13SmallMumfordRigidity
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13SmallMumfordRigidity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
open SexticMumford
theorem point_class_injective :
    Function.Injective
      (fun P : CurvePoint (N13Mumford.model K) =>
        classOf (N13Mumford.model K)
          (N13Infinity.positiveInfinityOrder K)
          (pointMumford (N13Mumford.model K) P)) := by
  intro P Q hPQ
  apply pointMumford_injective (N13Mumford.model K)
  exact eq_of_class_eq_of_small K _ _
    (pointMumford_small K P) (pointMumford_small K Q) hPQ
end
end MazurProof.N13SmallMumfordRigidity
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MumfordAbelJacobi
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem abelJacobi_injective
    : Function.Injective (abelJacobi K) := by
  exact N13SmallMumfordRigidity.point_class_injective K
end
end MazurProof.N13MumfordAbelJacobi
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicEndgame
noncomputable section
open N18RouteC.Separated
/-- Surjectivity of doubling iterates to every power of two. -/
theorem twoPow_surjective
    {G : Type*} [AddCommGroup G]
    (htwo : TwoSurjective G) :
    ∀ k : ℕ, Function.Surjective (fun P : G => (2 ^ k) • P) := by
  intro k
  induction k with
  | zero =>
      intro P
      exact ⟨P, by simp⟩
  | succ k ih =>
      intro P
      obtain ⟨R, hR⟩ := ih P
      obtain ⟨Q, hQ⟩ := htwo R
      refine ⟨Q, ?_⟩
      calc
        (2 ^ (k + 1)) • Q = 2 • ((2 ^ k) • Q) := by
          rw [pow_succ, mul_nsmul]
        _ = (2 ^ k) • (2 • Q) :=
          N18RouteC.Separated.nsmul_nsmul_comm 2 (2 ^ k) Q
        _ = (2 ^ k) • R := by rw [← hQ]
        _ = P := hR
end
end MazurProof.N13TwoAdicEndgame
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicEndgame
noncomputable section
open N18RouteC.Separated
/-- If doubling is injective, so is multiplication by every power of two. -/
theorem twoPow_injective_of_two_injective
    {G : Type*} [AddCommGroup G]
    (htwo : Function.Injective (fun P : G => 2 • P)) :
    ∀ k : ℕ, Function.Injective (fun P : G => (2 ^ k) • P) := by
  intro k
  induction k with
  | zero =>
      intro P Q hPQ
      simpa using hPQ
  | succ k ih =>
      intro P Q hPQ
      apply ih
      apply htwo
      simpa [pow_succ, mul_nsmul] using hPQ
end
end MazurProof.N13TwoAdicEndgame
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicEndgame
noncomputable section
open N18RouteC.Separated
/-- A finite quotient target makes the old exponent-nineteen detour
unnecessary.  If reduction is surjective, two-divisibility of the source
makes doubling bijective on the finite target.  Compatible halves of every
kernel element therefore remain in the kernel, so separatedness alone makes
reduction injective. -/
theorem reduction_injective_of_finite_target
    {G J₂ : Type*}
    [AddCommGroup G] [AddCommGroup J₂] [Finite J₂]
    (red : G →+ J₂)
    (red_surjective : Function.Surjective red)
    (twoSurjective : TwoSurjective G)
    (separated : NSeparated red.ker 2) :
    Function.Injective red := by
  have twoSurjectiveTarget :
      Function.Surjective (fun z : J₂ => 2 • z) := by
    intro z
    obtain ⟨P, rfl⟩ := red_surjective z
    obtain ⟨Q, hQ⟩ := twoSurjective P
    refine ⟨red Q, ?_⟩
    simpa only [map_nsmul] using congrArg red hQ.symm
  have twoInjectiveTarget :
      Function.Injective (fun z : J₂ => 2 • z) :=
    Finite.injective_iff_surjective.mpr twoSurjectiveTarget
  have twoPowInjectiveTarget :=
    twoPow_injective_of_two_injective twoInjectiveTarget
  intro P Q hPQ
  let z : red.ker :=
    ⟨P - Q, by
      change red (P - Q) = 0
      rw [map_sub, hPQ, sub_self]⟩
  have zInfinitelyDivisible : InfinitelyNSmulDivisible 2 z := by
    intro k
    obtain ⟨R, hR⟩ := twoPow_surjective twoSurjective k (P - Q)
    change (2 ^ k) • R = P - Q at hR
    have hredR : red R = 0 := by
      apply twoPowInjectiveTarget k
      calc
        (2 ^ k) • red R = red ((2 ^ k) • R) := by
          rw [map_nsmul]
        _ = red (P - Q) := by rw [hR]
        _ = 0 := z.2
        _ = (2 ^ k) • (0 : J₂) := by simp
    let r : red.ker := ⟨R, hredR⟩
    refine ⟨r, ?_⟩
    apply Subtype.ext
    exact hR
  have hz : z = 0 :=
    separated z zInfinitelyDivisible
  exact sub_eq_zero.mp (congrArg Subtype.val hz)
end
end MazurProof.N13TwoAdicEndgame
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
  exact HuangN13.N13MumfordFullKummerTwoSurjective.twoSurjective
end
end MazurProof.N13MumfordFullKummerTwoSurjective
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ReductionClassifier
noncomputable section
open N18RouteC.Separated
universe u v
namespace Data
variable {G : Type u} {S : Type v} [AddCommGroup G]
theorem red_surjective (D : Data G S) :
    Function.Surjective D.red :=
  QuotientAddGroup.mk'_surjective D.kernel
end Data
end
end MazurProof.N13ReductionClassifier
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ReductionClassifier
noncomputable section
open N18RouteC.Separated
universe u v
namespace Data
variable {G : Type u} {S : Type v} [AddCommGroup G]
@[simp] theorem quotientClassify_red
    (D : Data G S) (P : G) :
    D.quotientClassify (D.red P) = D.classify P :=
  QuotientAddGroup.quotient_liftOn_mk
    D.classify D.classify_respects_leftRel P
end Data
end
end MazurProof.N13ReductionClassifier
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ReductionClassifier
noncomputable section
open N18RouteC.Separated
universe u v
namespace Data
variable {G : Type u} {S : Type v} [AddCommGroup G]
/-- Finite classification and a separated kernel close the reduction
argument. -/
theorem reduction_injective
    (D : Data G S) [Finite S]
    (twoSurjective :
      N13TwoAdicEndgame.TwoSurjective G)
    (separated : NSeparated D.red.ker 2) :
    Function.Injective D.red :=
  N13TwoAdicEndgame.reduction_injective_of_finite_target
    D.red D.red_surjective twoSurjective separated
end Data
end
end MazurProof.N13ReductionClassifier
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ReductionClassifier
noncomputable section
open N18RouteC.Separated
universe u v
/-- N13 specialization of the abstract classifier endpoint. -/
theorem n13_reduction_injective
    (D : Data G SpecialSet)
    (separated : NSeparated D.red.ker 2) :
    Function.Injective D.red :=
  D.reduction_injective
    N13MumfordFullKummerTwoSurjective.twoSurjective separated
end
end MazurProof.N13ReductionClassifier
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialCuspReduction
noncomputable section
open N13AbelFiberTwoModel
theorem specialCuspEquiv_surjective :
    Function.Surjective specialCuspEquiv :=
  specialCuspEquiv.surjective
end
end MazurProof.N13SpecialCuspReduction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalPointEndgame
noncomputable section
open scoped Sym2
namespace CompatibleReduction
variable (D : CompatibleReduction)
/-- Every rational curve point and some rational cusp have the same
set-valued special Picard class. -/
theorem exists_cusp_classify_eq
    (P : RationalCurvePoint) :
    ∃ c : Cusp13,
      D.classifier.classify (rationalAbel P) =
        D.classifier.classify
          (N13MumfordAbelJacobi.cuspAbelJacobi c) := by
  obtain ⟨c, hc⟩ :=
    N13SpecialCuspReduction.specialCuspEquiv_surjective
      (D.reduceCurve P)
  refine ⟨c, ?_⟩
  calc
    D.classifier.classify (rationalAbel P) =
        specialPointClass (D.reduceCurve P) :=
      D.classify_abel P
    _ =
        specialPointClass
          (N13SpecialCuspReduction.specialCuspEquiv c) := by
      rw [hc]
    _ =
        specialPointClass
          (D.reduceCurve (N13Mumford.cuspPoint c)) := by
      rw [D.reduce_cusp c]
    _ =
        D.classifier.classify
          (N13MumfordAbelJacobi.cuspAbelJacobi c) := by
      exact (D.classify_abel (N13Mumford.cuspPoint c)).symm
end CompatibleReduction
end
end MazurProof.N13RationalPointEndgame
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalPointEndgame
noncomputable section
open scoped Sym2
namespace CompatibleReduction
variable (D : CompatibleReduction)
/-- A separated exact classifier makes every rational point of the
projective N13 curve equal to one of the six rational cusps. -/
theorem curvePoint_eq_cusp
    (separated :
      N18RouteC.Separated.NSeparated
        D.classifier.red.ker 2)
    (P : RationalCurvePoint) :
    ∃ c : Cusp13, P = N13Mumford.cuspPoint c := by
  obtain ⟨c, hclass⟩ :=
    D.exists_cusp_classify_eq P
  have hred :
      D.classifier.red (rationalAbel P) =
        D.classifier.red
          (N13MumfordAbelJacobi.cuspAbelJacobi c) := by
    apply D.classifier.quotientClassify_injective
    simpa only [
      N13ReductionClassifier.Data.quotientClassify_red]
      using hclass
  have hPic :
      rationalAbel P =
        N13MumfordAbelJacobi.cuspAbelJacobi c :=
    (N13ReductionClassifier.n13_reduction_injective
      D.classifier separated) hred
  refine ⟨c, ?_⟩
  exact N13MumfordAbelJacobi.abelJacobi_injective ℚ hPic
end CompatibleReduction
end
end MazurProof.N13RationalPointEndgame
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalPointEndgame
noncomputable section
open scoped Sym2
namespace CompatibleReduction
variable (D : CompatibleReduction)
/-- The exact affine statement consumed by `CyclicExclusion13` follows from
the compatible proper reduction and formal-kernel separatedness. -/
theorem affine_x_is_cuspidal
    (separated :
      N18RouteC.Separated.NSeparated
        D.classifier.red.ker 2) :
    ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y →
      X = 0 ∨ X = -1 := by
  intro X Y hcurve
  let P : RationalCurvePoint :=
    N13Mumford.affineCurvePoint X Y hcurve
  obtain ⟨c, hPc⟩ :=
    D.curvePoint_eq_cusp separated P
  have hx := congrArg affineX? hPc
  cases c with
  | infinityPlus =>
      simp [P, affineX?, N13Mumford.affineCurvePoint,
        N13Mumford.cuspPoint] at hx
  | infinityMinus =>
      simp [P, affineX?, N13Mumford.affineCurvePoint,
        N13Mumford.cuspPoint] at hx
  | zeroPlus =>
      exact Or.inl (by
        simpa [P, affineX?, N13Mumford.affineCurvePoint,
          N13Mumford.cuspPoint] using hx)
  | zeroMinus =>
      exact Or.inl (by
        simpa [P, affineX?, N13Mumford.affineCurvePoint,
          N13Mumford.cuspPoint] using hx)
  | negOnePlus =>
      exact Or.inr (by
        simpa [P, affineX?, N13Mumford.affineCurvePoint,
          N13Mumford.cuspPoint] using hx)
  | negOneMinus =>
      exact Or.inr (by
        simpa [P, affineX?, N13Mumford.affineCurvePoint,
          N13Mumford.cuspPoint] using hx)
end CompatibleReduction
end
end MazurProof.N13RationalPointEndgame
end
end

theorem solution (D : MazurProof.N13RationalPointEndgame.CompatibleReduction) (separated : MazurProof.N18RouteC.Separated.NSeparated D.classifier.red.ker 2) : ∀ X Y : ℚ, MazurProof.N13CurveModel.C13SexticEq X Y → X = 0 ∨ X = -1 := by
  exact MazurProof.N13RationalPointEndgame.CompatibleReduction.affine_x_is_cuspidal (D := D) separated
