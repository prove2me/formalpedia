-- Prove2me | solution 1 for HuangN13.N13MarkedEffectiveData.exists_marked_repaired_data
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:22:18.277935+00:00
-- url     : https://prove2.me/submissions/d5afd598-2d79-448d-b492-d1509f260672

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Theorems.Thm_HuangN13_N13MarkedEffectiveData_exists_effective_data_marked
import Theorems.Thm_MazurProof_SexticMumford_mumfordIdeal_mul_conj_integral

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
@[simp] theorem yClass_sq :
    yClass M ^ 2 = xClass M M.f := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
@[simp] theorem xClass_add (p q : K[X]) :
    xClass M (p + q) = xClass M p + xClass M q := by
  exact map_add (xClassHom M) p q
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
theorem mumford_bezout (D : SemiMumford M) :
    ∃ w a b c : K[X],
      M.f - D.v ^ 2 = D.u * w ∧
      a * D.u + b * (2 * D.v) + c * w = 1 := by
  classical
  obtain ⟨w, hw⟩ := D.curve_dvd
  have hcop : IsCoprime D.u (EuclideanDomain.gcd (2 * D.v) w) := by
    apply isCoprime_of_irreducible_dvd
    · intro hzero
      exact D.u_monic.ne_zero hzero.1
    · intro z hz hzu hzg
      have hz2v : z ∣ 2 * D.v :=
        hzg.trans (EuclideanDomain.gcd_dvd_left (2 * D.v) w)
      have hzw : z ∣ w :=
        hzg.trans (EuclideanDomain.gcd_dvd_right (2 * D.v) w)
      have htwo : IsUnit (2 : K[X]) := by
        have heq : _root_.Polynomial.C (2 : K) = (2 : K[X]) := by
          exact map_natCast (_root_.Polynomial.C : K →+* K[X]) 2
        rw [← heq]
        exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr M.two_ne_zero)
      have hzv : z ∣ D.v := by
        rcases hz.prime.dvd_mul.mp hz2v with hz2 | hzv
        · exact (hz.not_isUnit (isUnit_of_dvd_unit hz2 htwo)).elim
        · exact hzv
      have hzzSub : z * z ∣ M.f - D.v ^ 2 := by
        rw [hw]
        exact mul_dvd_mul hzu hzw
      have hzzSq : z * z ∣ D.v ^ 2 := by
        simpa only [pow_two] using mul_dvd_mul hzv hzv
      have hzzF : z * z ∣ M.f := by
        simpa only [sub_add_cancel] using dvd_add hzzSub hzzSq
      exact ((squarefree_iff_irreducible_sq_not_dvd_of_ne_zero
        M.ne_zero).mp M.squarefree z hz) hzzF
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨w, a,
    b * EuclideanDomain.gcdA (2 * D.v) w,
    b * EuclideanDomain.gcdB (2 * D.v) w, hw, ?_⟩
  rw [← hab, EuclideanDomain.gcd_eq_gcd_ab]
  ring
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
/-- Multiplying the first generator by a polynomial unit does not change a
Mumford ideal.  The divisibility formulation avoids choosing that unit. -/
theorem mumfordIdeal_eq_of_dvd_dvd
    (u u' v : K[X]) (huu' : u ∣ u') (hu'u : u' ∣ u) :
    mumfordIdeal M u v = mumfordIdeal M u' v := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨t, rfl⟩ := hu'u
      rw [xClass_mul]
      exact Ideal.mul_mem_right _ _
        (xClass_mem_mumfordIdeal M u' v)
    · exact ySubClass_mem_mumfordIdeal M u' v
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨t, rfl⟩ := huu'
      rw [xClass_mul]
      exact Ideal.mul_mem_right _ _
        (xClass_mem_mumfordIdeal M u v)
    · exact ySubClass_mem_mumfordIdeal M u v
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
attribute [local instance] MazurProof.SexticMumford.instDecidableEq_fLT
theorem mumfordIdeal_normalize
    (u v : K[X]) :
    mumfordIdeal M (_root_.normalize u) v = mumfordIdeal M u v := by
  exact mumfordIdeal_eq_of_dvd_dvd M (_root_.normalize u) u v
    (associated_normalize u).symm.dvd
    (associated_normalize u).dvd
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
/-- The ideal product at the heart of one Cantor reduction step.

The Bezout condition is exactly the one supplied by `mumford_bezout` for
the semireduced pair `(u,V)` when `w = (f-V²)/u`. -/
theorem mumfordIdeal_mul_cantor
    (u w V : K[X])
    (hcurve : M.f - V ^ 2 = u * w)
    (hbezout :
      ∃ a b c : K[X],
        a * u + b * (2 * V) + c * w = 1) :
    mumfordIdeal M u V * mumfordIdeal M w V =
      Ideal.span ({ySubClass M V} : Set (CoordinateRing M)) := by
  let I := mumfordIdeal M u V
  let J := mumfordIdeal M w V
  let g := ySubClass M V
  apply le_antisymm
  · rw [mumfordIdeal, mumfordIdeal,
      Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · have hfactor :
          xClass M u * xClass M w =
            ySubClass M V * (yClass M + xClass M V) := by
        symm
        calc
          ySubClass M V * (yClass M + xClass M V) =
              xClass M (M.f - V ^ 2) := by
            simp only [ySubClass]
            calc
              (yClass M - xClass M V) *
                  (yClass M + xClass M V) =
                  yClass M ^ 2 - xClass M V ^ 2 := by ring
              _ = xClass M M.f - xClass M V ^ 2 := by
                rw [yClass_sq]
              _ = xClass M (M.f - V ^ 2) := by
                rw [xClass_sub, xClass_pow]
          _ = xClass M (u * w) := by rw [hcurve]
          _ = xClass M u * xClass M w := by rw [xClass_mul]
      rw [hfactor]
      exact Ideal.mul_mem_right (yClass M + xClass M V) _
        (Ideal.subset_span (Set.mem_singleton _))
    · exact Ideal.mul_mem_left _
        (xClass M u) (Ideal.subset_span (Set.mem_singleton _))
    · rw [mul_comm]
      exact Ideal.mul_mem_left _
        (xClass M w) (Ideal.subset_span (Set.mem_singleton _))
    · exact Ideal.mul_mem_left _
        (ySubClass M V) (Ideal.subset_span (Set.mem_singleton _))
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, hbez⟩ := hbezout
    have huI : xClass M u ∈ I :=
      xClass_mem_mumfordIdeal M u V
    have hwJ : xClass M w ∈ J :=
      xClass_mem_mumfordIdeal M w V
    have hgI : g ∈ I :=
      ySubClass_mem_mumfordIdeal M u V
    have hgJ : g ∈ J :=
      ySubClass_mem_mumfordIdeal M w V
    have hug : xClass M u * g ∈ I * J :=
      Ideal.mul_mem_mul huI hgJ
    have hgw : g * xClass M w ∈ I * J :=
      Ideal.mul_mem_mul hgI hwJ
    have hgg : g * g ∈ I * J :=
      Ideal.mul_mem_mul hgI hgJ
    have huw : xClass M u * xClass M w ∈ I * J :=
      Ideal.mul_mem_mul huI hwJ
    have htwoVg : xClass M (2 * V) * g ∈ I * J := by
      have hdifference := Ideal.sub_mem (I * J) huw hgg
      convert hdifference using 1
      change
        xClass M (2 * V) * ySubClass M V =
          xClass M u * xClass M w -
            ySubClass M V * ySubClass M V
      have hxTwo :
          xClass M (2 : K[X]) = (2 : CoordinateRing M) := by
        exact map_natCast (xClassHom M) 2
      calc
        xClass M (2 * V) * ySubClass M V =
            xClass M (M.f - V ^ 2) -
              ySubClass M V ^ 2 := by
          simp only [ySubClass]
          rw [show xClass M (M.f - V ^ 2) =
            yClass M ^ 2 - xClass M V ^ 2 by
              rw [yClass_sq, xClass_sub, xClass_pow]]
          simp only [xClass_mul]
          rw [hxTwo]
          ring
        _ = xClass M (u * w) -
              ySubClass M V ^ 2 := by rw [hcurve]
        _ = xClass M u * xClass M w -
              ySubClass M V * ySubClass M V := by
          rw [xClass_mul, pow_two]
    have ha : xClass M a * (xClass M u * g) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M a) hug
    have hb : xClass M b * (xClass M (2 * V) * g) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M b) htwoVg
    have hc : xClass M c * (g * xClass M w) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M c) hgw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass M a * (xClass M u * g) +
            xClass M b * (xClass M (2 * V) * g) +
            xClass M c * (g * xClass M w) = g := by
      calc
        _ = xClass M
              (a * u + b * (2 * V) + c * w) * g := by
          simp only [xClass_add, xClass_mul]
          ring
        _ = g := by rw [hbez, xClass_one, one_mul]
    rw [heq] at hsum
    exact hsum
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
/-- Bezout transvection for the graph change `v ↦ v + u t`.  It is the
algebraic reason that the cubic boundary step needs no new coprimality
argument. -/
theorem cantorBezout_add_mul
    (D : SemiMumford M) (t w : K[X])
    (hcurve :
      M.f - (D.v + D.u * t) ^ 2 = D.u * w) :
    ∃ a b c : K[X],
      a * D.u + b * (2 * (D.v + D.u * t)) + c * w = 1 := by
  obtain ⟨w₀, a, b, c, hw₀, hbez⟩ := mumford_bezout M D
  have hwEq :
      w₀ = w + 2 * D.v * t + D.u * t ^ 2 := by
    apply mul_left_cancel₀ D.u_monic.ne_zero
    calc
      D.u * w₀ = M.f - D.v ^ 2 := hw₀.symm
      _ = (M.f - (D.v + D.u * t) ^ 2) +
          D.u * (2 * D.v * t + D.u * t ^ 2) := by ring
      _ = D.u * w +
          D.u * (2 * D.v * t + D.u * t ^ 2) := by rw [hcurve]
      _ = D.u * (w + 2 * D.v * t + D.u * t ^ 2) := by ring
  refine ⟨a - 2 * b * t - c * t ^ 2, b + c * t, c, ?_⟩
  rw [hwEq] at hbez
  linear_combination hbez
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
attribute [local instance] MazurProof.SexticMumford.instDecidableEq_fLT
theorem mumfordIdeal_cantorComplementSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    mumfordIdeal M
        (cantorComplementSemi M D V w n hcurve hw).u
        (cantorComplementSemi M D V w n hcurve hw).v =
      mumfordIdeal M w V := by
  change
    mumfordIdeal M (_root_.normalize w) (V % _root_.normalize w) =
      mumfordIdeal M w V
  calc
    mumfordIdeal M (_root_.normalize w) (V % _root_.normalize w) =
        mumfordIdeal M (_root_.normalize w) V :=
      (mumfordIdeal_eq_of_dvd_sub M (_root_.normalize w)
        (V % _root_.normalize w) V
        (normalize_dvd_sub_mod V w)).symm
    _ = mumfordIdeal M w V := mumfordIdeal_normalize M w V
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
theorem mumfordIdeal_mul_cantorComplement
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    mumfordIdeal M D.u D.v *
        mumfordIdeal M
          (cantorComplementSemi M D V w n hcurve hw).u
          (cantorComplementSemi M D V w n hcurve hw).v =
      Ideal.span ({ySubClass M V} : Set (CoordinateRing M)) := by
  rw [← mumfordIdeal_eq_of_dvd_sub M D.u D.v V hcongr,
    mumfordIdeal_cantorComplementSemi M D V w n hcurve hw]
  exact mumfordIdeal_mul_cantor M D.u w V hcurve hbezout
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
theorem mumfordIdealUnit_mul_cantorComplement
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    mumfordIdealUnit M D *
        mumfordIdealUnit M
          (cantorComplementSemi M D V w n hcurve hw) =
      toPrincipalIdeal (CoordinateRing M) (FunctionField M)
        (ySubFunctionUnit M V) := by
  apply Units.ext
  simp only [Units.val_mul, coe_mumfordIdealUnit,
    coe_toPrincipalIdeal, coe_ySubFunctionUnit]
  rw [← FractionalIdeal.coeIdeal_mul,
    mumfordIdeal_mul_cantorComplement M D V w n hcurve hw
      hcongr hbezout,
    FractionalIdeal.coeIdeal_span_singleton]
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
attribute [local instance] MazurProof.SexticMumford.instDecidableEq_fLT
theorem mumfordIdealUnit_complement_mul_conjugate
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    mumfordIdealUnit M
          (cantorComplementSemi M D V w n hcurve hw) *
        mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) =
      toPrincipalIdeal (CoordinateRing M) (FunctionField M)
        (xClassFunctionUnit M (_root_.normalize w)
          (monic_normalize hw).ne_zero) := by
  let E := cantorComplementSemi M D V w n hcurve hw
  apply Units.ext
  simp only [Units.val_mul, coe_mumfordIdealUnit,
    coe_toPrincipalIdeal, coe_xClassFunctionUnit]
  change
    (mumfordIdeal M E.u E.v :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) *
      (mumfordIdeal M E.u (-E.v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      FractionalIdeal.spanSingleton (CoordinateRing M)⁰
        (algebraMap (CoordinateRing M) (FunctionField M)
          (xClass M E.u))
  rw [← FractionalIdeal.coeIdeal_mul,
    mumfordIdeal_mul_conj_integral M E,
    FractionalIdeal.coeIdeal_span_singleton]
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
attribute [local instance] MazurProof.SexticMumford.instDecidableEq_fLT
theorem cantorConjugateSemi_principalRelation
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) *
        toPrincipalIdeal (CoordinateRing M) (FunctionField M)
          (cantorCorrectionUnit M V w hw) =
      mumfordIdealUnit M D := by
  have hprod :=
    mumfordIdealUnit_mul_cantorComplement M D V w n
      hcurve hw hcongr hbezout
  have hnorm :=
    mumfordIdealUnit_complement_mul_conjugate M D V w n
      hcurve hw
  rw [cantorCorrectionUnit, map_mul, map_inv]
  calc
    mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) *
        (toPrincipalIdeal (CoordinateRing M) (FunctionField M)
            (ySubFunctionUnit M V) *
          (toPrincipalIdeal (CoordinateRing M) (FunctionField M)
            (xClassFunctionUnit M (_root_.normalize w)
              (monic_normalize hw).ne_zero))⁻¹) =
      mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) *
        ((mumfordIdealUnit M D *
            mumfordIdealUnit M
              (cantorComplementSemi M D V w n hcurve hw)) *
          (mumfordIdealUnit M
              (cantorComplementSemi M D V w n hcurve hw) *
            mumfordIdealUnit M
              (cantorConjugateSemi M D V w n hcurve hw))⁻¹) := by
        rw [hprod, hnorm]
    _ = mumfordIdealUnit M D := by
      simp [mul_assoc, mul_left_comm, mul_comm]
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
theorem cantorNextSemi_class
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    semiMumfordClass M O
        (cantorNextSemi M O D V w hcurve hw) =
      semiMumfordClass M O D := by
  apply (semiMumfordClass_eq_iff M O
    (cantorNextSemi M O D V w hcurve hw) D).2
  refine ⟨cantorCorrectionUnit M V w hw, ?_, ?_⟩
  · exact cantorConjugateSemi_principalRelation M D V w
      (cantorNextNInf M O D V w hw) hcurve hw hcongr hbezout
  · change
      Multiplicative.ofAdd
          (D.nInf -
              Multiplicative.toAdd
                (O.ordPlus (cantorCorrectionUnit M V w hw)) - 1) *
          O.ordPlus (cantorCorrectionUnit M V w hw) =
        Multiplicative.ofAdd (D.nInf - 1)
    change
      D.nInf -
          Multiplicative.toAdd
            (O.ordPlus (cantorCorrectionUnit M V w hw)) - 1 +
        Multiplicative.toAdd
          (O.ordPlus (cantorCorrectionUnit M V w hw)) =
      D.nInf - 1
    omega
end
end MazurProof.SexticMumford
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13MumfordInfinityBalance
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open MazurProof
open MazurProof.SexticMumford
variable (D : N13Mumford.SemiMumford K)
private theorem adaptedBezout
    (V w : K[X])
    (hcurve : N13Mumford.f K - V ^ 2 = D.u * w)
    (hcongr : D.u ∣ V - D.v) :
    ∃ a b c : K[X],
      a * D.u + b * (2 * V) + c * w = 1 := by
  obtain ⟨t, ht⟩ := hcongr
  have hV : V = D.v + D.u * t := by
    linear_combination ht
  rw [hV]
  exact cantorBezout_add_mul (N13Mumford.model K) D t w
    (by simpa only [N13Mumford.model_f, hV] using hcurve)
end
end MazurProof.N13MumfordInfinityBalance
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13MumfordInfinityBalance
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open MazurProof
open MazurProof.SexticMumford
variable (D : N13Mumford.SemiMumford K)
theorem plusStep_class :
    semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) (plusStep D) =
      semiMumfordClass (N13Mumford.model K)
        (N13Infinity.positiveInfinityOrder K) D := by
  unfold plusStep
  apply cantorNextSemi_class
    (N13Mumford.model K) (N13Infinity.positiveInfinityOrder K)
    D (plusLift D) (plusFactor D)
    (plusFactor_spec D) (plusFactor_ne_zero D)
    (plusLift_congr D)
  exact adaptedBezout D (plusLift D) (plusFactor D)
    (plusFactor_spec D) (plusLift_congr D)
end
end MazurProof.N13MumfordInfinityBalance
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveInfinityRepair
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open SexticMumford N13MumfordInfinityBalance
open Polynomial
theorem repair_class (D : N13Mumford.Mumford K) :
    semiMumfordClass Model (N13Infinity.positiveInfinityOrder K) (repair D) =
      classOf Model (N13Infinity.positiveInfinityOrder K) D := by
  unfold repair
  split
  · simpa only [semiMumfordClass_toSemi] using plusStep_class D.toSemi
  · rfl
end
end MazurProof.N13EffectiveInfinityRepair
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveInfinityRepair
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open SexticMumford N13MumfordInfinityBalance
open Polynomial
theorem repair_of_upper_wall
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    repair D = plusStep D.toSemi := by
  simp only [repair, hwall, if_true]
end
end MazurProof.N13EffectiveInfinityRepair
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveInfinityRepair
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open SexticMumford N13MumfordInfinityBalance
open Polynomial
theorem repair_nInf_of_upper_wall
    (D : N13Mumford.Mumford K) (hwall : D.u.natDegree + D.nInf = 2) :
    (repair D).nInf = -1 := by
  rw [repair_of_upper_wall D hwall, plusStep_nInf D.toSemi D.deg_u]
  simp only [toSemi_nInf, toSemi_u]
  omega
end
end MazurProof.N13EffectiveInfinityRepair
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveInfinityRepair
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open SexticMumford N13MumfordInfinityBalance
open Polynomial
theorem repair_natDegree_le_two (D : N13Mumford.Mumford K) :
    (repair D).u.natDegree ≤ 2 := by
  unfold repair
  split
  · rw [plusStep_natDegree]
    exact plusFactor_natDegree_le_two D.toSemi D.deg_u
  · exact D.deg_u
end
end MazurProof.N13EffectiveInfinityRepair
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveInfinityRepair
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
open SexticMumford N13MumfordInfinityBalance
open Polynomial
theorem repair_effective (D : N13Mumford.Mumford K) :
    EffectiveChamber (repair D) := by
  refine ⟨repair_natDegree_le_two D, ?_⟩
  by_cases hwall : D.u.natDegree + D.nInf = 2
  · rw [repair_nInf_of_upper_wall D hwall]
    have hd := repair_natDegree_le_two D
    omega
  · have hb := D.infinity_bound
    simp only [repair, hwall, if_false, toSemi_nInf, toSemi_u]
    omega
end
end MazurProof.N13EffectiveInfinityRepair
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MarkedEffectiveData
noncomputable section
open Polynomial N13InfinityChartMarking
open N13TwoChartPicardRealization N13EffectiveInfinityRepair N13EffectiveGraphData
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem exists_marked_repaired_data (D : N13Mumford.Mumford Q₂) :
    ∃ R : Data,
      genericRaw R.charts R.infinityOrder =
        SexticMumford.semiMumfordRaw N13TwoChartPicardRealization.Model (repair D) ∧
      R.toGenericPic = SexticMumford.classOf N13TwoChartPicardRealization.Model
        (N13Infinity.positiveInfinityOrder Q₂) D ∧
      AffineVerticallySaturated R.charts ∧
      HasInfinityMultiplicities R.charts
        (positiveMultiplicity (repair D)) (negativeMultiplicity (repair D)) := by
  obtain ⟨R, hraw, hs, hm⟩ := HuangN13.N13MarkedEffectiveData.exists_effective_data_marked (repair D) (repair_effective D)
  refine ⟨R, hraw, ?_, hs, hm⟩
  change genericClass R.charts R.infinityOrder = _
  unfold genericClass
  rw [hraw]
  exact repair_class D
end
end MazurProof.N13MarkedEffectiveData
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem solution (D : MazurProof.N13Mumford.Mumford MazurProof.N13TwoChartPicardRealization.Q₂) :
    ∃ R : MazurProof.N13TwoChartPicardRealization.Data,
      MazurProof.N13TwoChartPicardRealization.genericRaw R.charts R.infinityOrder =
        MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model (MazurProof.N13EffectiveInfinityRepair.repair D) ∧
      R.toGenericPic = MazurProof.SexticMumford.classOf MazurProof.N13TwoChartPicardRealization.Model
        (MazurProof.N13Infinity.positiveInfinityOrder MazurProof.N13TwoChartPicardRealization.Q₂) D ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities R.charts
        (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity (MazurProof.N13EffectiveInfinityRepair.repair D)) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity (MazurProof.N13EffectiveInfinityRepair.repair D)) := by
  exact MazurProof.N13MarkedEffectiveData.exists_marked_repaired_data D
