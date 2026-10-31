-- Prove2me | solution 1 for HuangN13.N13ConstructedRationalPointTheorem.quotient_kernel_separated
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:48:49.207718+00:00
-- url     : https://prove2.me/submissions/00cdb082-3d43-4a0d-a1b6-bc837297f9b9

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_CompatibleReductionCore
import Definitions.Def_HuangN13_DoublingStatementCore
import Definitions.Def_HuangN13_SeparationDataCore
import Theorems.Thm_HuangN13_N13ConstructedKernelDoubling_selected_cross_coefficients
import Theorems.Thm_HuangN13_N13ConstructedMappedSpecialFamily_representative_nonempty
import Theorems.Thm_HuangN13_N13RationalKernelDoublingAdapter_MappedSpecialRepresentative_exists_nearBase
import Theorems.Thm_HuangN13_N13RationalKernelDoublingAdapter_NearBaseFamily_squareJet_sub_double_coord_mem_sq
import Theorems.Thm_MazurProof_N13MumfordCenteredDoublingJet_diskCoord_double_mod_sq_of_cross

set_option autoImplicit false

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicKernelChart
noncomputable section
open N18RouteC.Separated
attribute [local instance] MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
theorem powTwoIdeal_mul (r s : ℕ) :
    powTwoIdeal r * powTwoIdeal s =
      powTwoIdeal (r + s) := by
  simp only [powTwoIdeal,
    Ideal.span_singleton_mul_span_singleton, ← pow_add]
end
end MazurProof.N13TwoAdicKernelChart
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicKernelChart
noncomputable section
open N18RouteC.Separated
attribute [local instance] MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
theorem powTwoIdeal_antitone
    {r s : ℕ} (hrs : r ≤ s) :
    powTwoIdeal s ≤ powTwoIdeal r := by
  rw [powTwoIdeal, powTwoIdeal,
    Ideal.span_singleton_le_iff_mem,
    Ideal.mem_span_singleton]
  exact pow_dvd_pow (2 : R₂) hrs
end
end MazurProof.N13TwoAdicKernelChart
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicKernelChart
noncomputable section
open N18RouteC.Separated
universe u
variable {K : Type u} [AddCommGroup K]
namespace DoublingChart
variable (C : DoublingChart K)
attribute [local instance] MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
theorem coordIdeal_le_powTwoIdeal
    {n : ℕ} {z : K}
    (hz : C.CoordDepth n z) :
    coordIdeal C.coord z ≤ powTwoIdeal n := by
  rw [coordIdeal, Ideal.span_le]
  intro a ha
  obtain ⟨i, rfl⟩ := ha
  exact hz i
end DoublingChart
end
end MazurProof.N13TwoAdicKernelChart
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicKernelChart
noncomputable section
open N18RouteC.Separated
universe u
variable {K : Type u} [AddCommGroup K]
namespace DoublingChart
variable (C : DoublingChart K)
attribute [local instance] MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
private theorem two_mul_mem_next
    {n : ℕ} {a : R₂}
    (ha : a ∈ powTwoIdeal n) :
    a + a ∈ powTwoIdeal (n + 1) := by
  rw [powTwoIdeal, Ideal.mem_span_singleton] at ha ⊢
  obtain ⟨b, hb⟩ := ha
  refine ⟨b, ?_⟩
  rw [hb, pow_succ]
  ring
end DoublingChart
end
end MazurProof.N13TwoAdicKernelChart
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicKernelChart
noncomputable section
open N18RouteC.Separated
universe u
variable {K : Type u} [AddCommGroup K]
namespace DoublingChart
variable (C : DoublingChart K)
attribute [local instance] MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- The diagonal quadratic estimate raises coordinate depth under
doubling. -/
theorem two_nsmul_depth
    {n : ℕ} (hn : 1 ≤ n) {z : K}
    (hz : C.CoordDepth n z) :
    C.CoordDepth (n + 1) (2 • z) := by
  intro i
  have herr :
      C.coord (2 • z) i -
          (C.coord z i + C.coord z i) ∈
        powTwoIdeal (n + n) := by
    rw [← powTwoIdeal_mul]
    exact
      (Ideal.mul_mono
        (C.coordIdeal_le_powTwoIdeal hz)
        (C.coordIdeal_le_powTwoIdeal hz))
        (C.double_error_mem z i)
  have herr' :
      C.coord (2 • z) i -
          (C.coord z i + C.coord z i) ∈
        powTwoIdeal (n + 1) :=
    powTwoIdeal_antitone (by omega) herr
  have hlinear :
      C.coord z i + C.coord z i ∈
        powTwoIdeal (n + 1) :=
    two_mul_mem_next (hz i)
  have hsum :=
    Ideal.add_mem (powTwoIdeal (n + 1)) herr' hlinear
  simpa using hsum
end DoublingChart
end
end MazurProof.N13TwoAdicKernelChart
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicKernelChart
noncomputable section
open N18RouteC.Separated
universe u
variable {K : Type u} [AddCommGroup K]
namespace DoublingChart
variable (C : DoublingChart K)
attribute [local instance] MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- Iterated doubling gains one level of depth at every step. -/
theorem twoPow_depth
    (z : K) :
    ∀ k : ℕ,
      C.CoordDepth (k + 1) ((2 ^ k) • z) := by
  intro k
  induction k with
  | zero =>
      intro i
      simpa only [pow_zero, one_nsmul, zero_add] using
        C.coord_mem_two z i
  | succ k ih =>
      have hstep :
          C.CoordDepth (k + 1 + 1)
            (2 • ((2 ^ k) • z)) :=
        C.two_nsmul_depth (n := k + 1) (by omega) ih
      simpa [pow_succ, mul_nsmul] using hstep
end DoublingChart
end
end MazurProof.N13TwoAdicKernelChart
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicKernelChart
noncomputable section
open N18RouteC.Separated
universe u
variable {K : Type u} [AddCommGroup K]
namespace DoublingChart
variable (C : DoublingChart K)
attribute [local instance] MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
theorem coord_eq_zero_of_all_depth
    {z : K}
    (hz : ∀ n : ℕ, C.CoordDepth n z) :
    C.coord z = 0 := by
  funext i
  by_contra hi
  have hmem :
      C.coord z i ∈
        Ideal.span
          ({(2 : R₂) ^
            (C.coord z i).valuation.succ} : Set R₂) := by
    simpa only [powTwoIdeal] using
      hz (C.coord z i).valuation.succ i
  have hle :
      (C.coord z i).valuation.succ ≤
        (C.coord z i).valuation :=
    (PadicInt.mem_span_pow_iff_le_valuation
      (C.coord z i) hi
      (C.coord z i).valuation.succ).mp hmem
  omega
end DoublingChart
end
end MazurProof.N13TwoAdicKernelChart
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicKernelChart
noncomputable section
open N18RouteC.Separated
universe u
variable {K : Type u} [AddCommGroup K]
namespace DoublingChart
variable (C : DoublingChart K)
include C
attribute [local instance] MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- The unary doubling chart is already sufficient for two-adic
separatedness. -/
theorem separated :
    NSeparated K 2 := by
  intro z hdiv
  have hall : ∀ n : ℕ, C.CoordDepth n z := by
    intro n
    cases n with
    | zero =>
        intro i
        simp [powTwoIdeal]
    | succ k =>
        obtain ⟨y, hy⟩ := hdiv k
        have hdepth := C.twoPow_depth y k
        rw [hy] at hdepth
        simpa [Nat.succ_eq_add_one] using hdepth
  apply C.coord_injective
  rw [C.coord_zero]
  exact C.coord_eq_zero_of_all_depth hall
end DoublingChart
end
end MazurProof.N13TwoAdicKernelChart
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13InfinityBaseChange
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K'] [CharZero K] [CharZero K']
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Canonical balanced representatives commute with rational-to-two-adic
base change. -/
@[simp] theorem normalize_picMapRatToQ₂
    (c :
      SexticMumford.ConcretePic
        (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ)) :
    SexticMumford.normalize
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (picMapRatToQ₂ c) =
      (SexticMumford.normalize
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ) c).mapCoeffs
        ratToQ₂ ratToQ₂_injective
        (map_n13_f ratToQ₂) := by
  apply SexticMumford.normalize_eq_of_class
  calc
    SexticMumford.classOf
          (N13Mumford.model Q₂)
          (N13Infinity.positiveInfinityOrder Q₂)
          ((SexticMumford.normalize
              (N13Mumford.model ℚ)
              (N13Infinity.positiveInfinityOrder ℚ) c).mapCoeffs
            ratToQ₂ ratToQ₂_injective
            (map_n13_f ratToQ₂)) =
        picMapRatToQ₂
          (SexticMumford.classOf
            (N13Mumford.model ℚ)
            (N13Infinity.positiveInfinityOrder ℚ)
            (SexticMumford.normalize
              (N13Mumford.model ℚ)
              (N13Infinity.positiveInfinityOrder ℚ) c)) := by
      rw [picMapRatToQ₂_classOf]
    _ = picMapRatToQ₂ c := by
      rw [SexticMumford.classOf_normalize]
end
end MazurProof.N13InfinityBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13InfinityBaseChange
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K'] [CharZero K] [CharZero K']
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Rational oriented Picard classes remain distinct after extension to
`ℚ₂`.  The proof uses unique balanced normal forms, not a Picard-scheme
separatedness theorem. -/
theorem picMapRatToQ₂_injective :
    Function.Injective picMapRatToQ₂ := by
  intro c d hcd
  have hnormal :
      ((SexticMumford.normalize
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ) c).mapCoeffs
            ratToQ₂ ratToQ₂_injective
            (map_n13_f ratToQ₂) :
          N13Mumford.Mumford Q₂) =
        ((SexticMumford.normalize
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ) d).mapCoeffs
            ratToQ₂ ratToQ₂_injective
            (map_n13_f ratToQ₂) :
          N13Mumford.Mumford Q₂) := by
    rw [← normalize_picMapRatToQ₂,
      ← normalize_picMapRatToQ₂, hcd]
  have hsource :
      SexticMumford.normalize
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ) c =
        SexticMumford.normalize
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ) d :=
    SexticMumford.Mumford.mapCoeffs_injective
      ratToQ₂ ratToQ₂_injective
      (map_n13_f ratToQ₂) hnormal
  calc
    c = SexticMumford.classOf
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ)
          (SexticMumford.normalize
            (N13Mumford.model ℚ)
            (N13Infinity.positiveInfinityOrder ℚ) c) :=
      (SexticMumford.classOf_normalize
        (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ) c).symm
    _ = SexticMumford.classOf
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ)
          (SexticMumford.normalize
            (N13Mumford.model ℚ)
            (N13Infinity.positiveInfinityOrder ℚ) d) := by
      rw [hsource]
    _ = d :=
      SexticMumford.classOf_normalize
        (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ) d
end
end MazurProof.N13InfinityBaseChange
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
@[simp] theorem red_eq_zero_iff (D : Data G S) (P : G) :
    D.red P = 0 ↔ P ∈ D.kernel := by
  simp [red]
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
@[simp] theorem red_ker (D : Data G S) :
    D.red.ker = D.kernel := by
  ext P
  simp
end Data
end
end MazurProof.N13ReductionClassifier
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicAbelChartLaw
noncomputable section
open MvPolynomial
universe u
variable {K : Type u}
variable [AddCommGroup K]
namespace DoublingLaw
variable {coord : K → Fin 2 → R₂}
attribute [local instance] MazurProof.N13TwoAdicAbelChartLaw.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- A unary doubling law upgrades suitable coordinates to the minimal
two-adic kernel chart. -/
def toChart
    (L : DoublingLaw coord)
    (coord_zero : coord 0 = 0)
    (coord_injective : Function.Injective coord)
    (coord_mem_two :
      ∀ z i,
        coord z i ∈ N13TwoAdicKernelChart.powTwoIdeal 1) :
    N13TwoAdicKernelChart.DoublingChart K where
  coord := coord
  coord_zero := coord_zero
  coord_injective := coord_injective
  coord_mem_two := coord_mem_two
  double_error_mem := L.double_error_mem
end DoublingLaw
end
end MazurProof.N13TwoAdicAbelChartLaw
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicAbelChartLaw
noncomputable section
open MvPolynomial
universe u
variable {K : Type u}
variable [AddCommGroup K]
namespace DoublingGeometricData
variable (D : DoublingGeometricData K)
/-- The minimal unary chart attached to disk representatives. -/
def chart :
    N13TwoAdicKernelChart.DoublingChart K :=
  D.law.toChart D.coord_zero D.coord_injective
    D.coord_mem_two
end DoublingGeometricData
end
end MazurProof.N13TwoAdicAbelChartLaw
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicAbelChartLaw
noncomputable section
open MvPolynomial
universe u
variable {K : Type u}
variable [AddCommGroup K]
namespace DoublingGeometricData
variable (D : DoublingGeometricData K)
include D
theorem separated :
    N18RouteC.Separated.NSeparated K 2 :=
  N13TwoAdicKernelChart.DoublingChart.separated (chart D)
end DoublingGeometricData
end
end MazurProof.N13TwoAdicAbelChartLaw
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicAbelChartSection
noncomputable section
universe u
variable {K : Type u} [AddCommGroup K]
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
/-- A faithful Picard realization with the minimal unary doubling law.
The representative at zero and its injectivity both follow from
`realize`. -/
structure DoublingData (K : Type u) [AddCommGroup K] where
  toPic : K →+ Pic₂
  toPic_injective : Function.Injective toPic
  pair : K → DiskPair
  realize :
    ∀ z,
      N13TwoAdicAbelChartPic.DiskPair.centeredPic (pair z) =
        toPic z
  law :
    N13TwoAdicAbelChartLaw.DoublingLaw
      (fun z =>
        N13TwoAdicAbelChartData.DiskPair.coord (pair z))
end
end MazurProof.N13TwoAdicAbelChartSection
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicAbelChartSection
noncomputable section
universe u
variable {K : Type u} [AddCommGroup K]
namespace DoublingData
variable (D : DoublingData K)
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
theorem pair_zero :
    D.pair 0 = N13TwoAdicAbelChartData.basePair := by
  apply N13TwoAdicAbelChartPic.DiskPair.centeredPic_injective
  rw [D.realize, map_zero,
    N13TwoAdicAbelChartPic.DiskPair.centeredPic_basePair]
end DoublingData
end
end MazurProof.N13TwoAdicAbelChartSection
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicAbelChartSection
noncomputable section
universe u
variable {K : Type u} [AddCommGroup K]
namespace DoublingData
variable (D : DoublingData K)
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
theorem pair_injective :
    Function.Injective D.pair := by
  intro z w hzw
  apply D.toPic_injective
  rw [← D.realize z, ← D.realize w, hzw]
end DoublingData
end
end MazurProof.N13TwoAdicAbelChartSection
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicAbelChartSection
noncomputable section
universe u
variable {K : Type u} [AddCommGroup K]
namespace DoublingData
variable (D : DoublingData K)
/-- Picard realization supplies the minimal unary geometric package. -/
def toGeometricData :
    N13TwoAdicAbelChartLaw.DoublingGeometricData K where
  pair := D.pair
  pair_zero := D.pair_zero
  pair_injective := D.pair_injective
  law := D.law
end DoublingData
end
end MazurProof.N13TwoAdicAbelChartSection
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicAbelChartSection
noncomputable section
universe u
variable {K : Type u} [AddCommGroup K]
namespace DoublingData
variable (D : DoublingData K)
include D
theorem separated :
    N18RouteC.Separated.NSeparated K 2 :=
  D.toGeometricData.separated
end DoublingData
end
end MazurProof.N13TwoAdicAbelChartSection
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicAbelChartSection
noncomputable section
universe u
variable {K : Type u} [AddCommGroup K]
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
theorem subgroupToPic_injective
    (H : AddSubgroup RationalPic) :
    Function.Injective (subgroupToPic H) :=
  N13InfinityBaseChange.picMapRatToQ₂_injective.comp
    H.subtype_injective
end
end MazurProof.N13TwoAdicAbelChartSection
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicAbelChartSection
noncomputable section
universe u
variable {K : Type u} [AddCommGroup K]
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
/-- The minimal unary data required for an actual rational reduction
kernel.  The binary polynomial law is deliberately absent. -/
structure RationalKernelDoublingData
    (H : AddSubgroup RationalPic) where
  pair : H → DiskPair
  realize :
    ∀ z,
      N13TwoAdicAbelChartPic.DiskPair.centeredPic (pair z) =
        subgroupToPic H z
  law :
    N13TwoAdicAbelChartLaw.DoublingLaw
      (fun z =>
        N13TwoAdicAbelChartData.DiskPair.coord (pair z))
end
end MazurProof.N13TwoAdicAbelChartSection
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicAbelChartSection
noncomputable section
universe u
variable {K : Type u} [AddCommGroup K]
namespace RationalKernelDoublingData
variable {H : AddSubgroup RationalPic}
def toData (D : RationalKernelDoublingData H) :
    DoublingData H where
  toPic := subgroupToPic H
  toPic_injective := subgroupToPic_injective H
  pair := D.pair
  realize := D.realize
  law := D.law
end RationalKernelDoublingData
end
end MazurProof.N13TwoAdicAbelChartSection
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoAdicAbelChartSection
noncomputable section
universe u
variable {K : Type u} [AddCommGroup K]
namespace RationalKernelDoublingData
variable {H : AddSubgroup RationalPic}
theorem separated (D : RationalKernelDoublingData H) :
    N18RouteC.Separated.NSeparated H 2 :=
  D.toData.separated
end RationalKernelDoublingData
end
end MazurProof.N13TwoAdicAbelChartSection
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
namespace NearBaseFamily
variable {H : AddSubgroup RationalPic}
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
/-- Pointwise existence is sufficient to package a representative family.
Injectivity of the centered disk-pair Picard map later removes dependence
on these choices at the geometric-coordinate level. -/
def ofExists
    (h :
      ∀ z : H, ∃ E : NearBaseMumford,
        E.centeredPic =
          N13TwoAdicAbelChartSection.subgroupToPic H z) :
    NearBaseFamily H where
  graph z := Classical.choose (h z)
  realize_graph z := Classical.choose_spec (h z)
end NearBaseFamily
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
namespace NearBaseFamily
variable {H : AddSubgroup RationalPic}
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
/-- Near-base graph recovery supplies the exact centered Picard realization
required by `RationalKernelDoublingData`. -/
theorem realize
    (F : NearBaseFamily H) (z : H) :
    N13TwoAdicAbelChartPic.DiskPair.centeredPic
        (F.pair z) =
      N13TwoAdicAbelChartSection.subgroupToPic H z := by
  calc
    N13TwoAdicAbelChartPic.DiskPair.centeredPic
          (F.pair z) =
        (F.graph z).centeredPic := by
      simpa [pair] using
        ((F.graph z).centeredPic_eq_diskPair_centeredPic).symm
    _ = N13TwoAdicAbelChartSection.subgroupToPic H z :=
      F.realize_graph z
end NearBaseFamily
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
/-- A literal mapped-special representative for every class in a rational
kernel.  This is the concrete representative producer from which the
abstract near-base family can now be derived. -/
structure MappedSpecialFamily
    (H : AddSubgroup RationalPic) where
  representative :
    ∀ z : H,
      MappedSpecialRepresentative
        (N13TwoAdicAbelChartSection.subgroupToPic H z)
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
namespace MappedSpecialFamily
variable {H : AddSubgroup RationalPic}
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
/-- Concrete graph recovery discharges the entire pointwise near-base
realization field from literal mapped-special representatives. -/
def toNearBaseFamily
    (R : MappedSpecialFamily H) :
    NearBaseFamily H :=
  NearBaseFamily.ofExists
    (fun z => (HuangN13.N13RationalKernelDoublingAdapter.MappedSpecialRepresentative.exists_nearBase (R.representative z)))
end MappedSpecialFamily
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
namespace NearBaseFamily
variable {H : AddSubgroup RationalPic}
/-- Once the unary law is known, the representative family fills the exact
rational-kernel structure used by separatedness. -/
def ofDoublingLaw
    (F : NearBaseFamily H)
    (L : N13TwoAdicAbelChartLaw.DoublingLaw F.coord) :
    N13TwoAdicAbelChartSection.RationalKernelDoublingData H where
  pair := F.pair
  realize := F.realize
  law := by
    change N13TwoAdicAbelChartLaw.DoublingLaw F.coord
    exact L
end NearBaseFamily
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
attribute [local instance] MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT MazurProof.N13RationalKernelDoublingAdapter.instFactPrimeOfNatNat_fLT
/-- Comparison between the canonical representative chosen for `2 • z`
and the tensor square of the representative chosen for `z`.

Exact equality of transitions is unnecessary.  Agreement of their first
jets modulo the square of the moving coordinate ideal is precisely the
congruence consumed by the formal-kernel argument. -/
structure FirstJetDoublingCompatibility
    {H : AddSubgroup RationalPic}
    (F : NearBaseFamily H) : Prop where
  compare :
    ∀ z i,
      F.coord (2 • z) i - F.squareJet z i ∈
        N13TwoAdicKernelChart.coordIdeal F.coord z *
          N13TwoAdicKernelChart.coordIdeal F.coord z
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
namespace FirstJetDoublingCompatibility
variable {H : AddSubgroup RationalPic}
variable {F : NearBaseFamily H}
attribute [local instance] MazurProof.N13RationalKernelDoublingAdapter.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartLaw.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- The representative-comparison congruence and the existing
transition-square congruence add to the required unary doubling law. -/
def toDoublingLaw
    (C : FirstJetDoublingCompatibility F) :
    N13TwoAdicAbelChartLaw.DoublingLaw F.coord where
  double_error_mem z i := by
    let I :=
      N13TwoAdicKernelChart.coordIdeal F.coord z
    change
      F.coord (2 • z) i -
          (F.coord z i + F.coord z i) ∈
        I * I
    have hcompare :
        F.coord (2 • z) i - F.squareJet z i ∈ I * I := by
      simpa [I] using C.compare z i
    have hsquare :
        F.squareJet z i -
            (F.coord z i + F.coord z i) ∈ I * I := by
      simpa [I] using
        HuangN13.N13RationalKernelDoublingAdapter.NearBaseFamily.squareJet_sub_double_coord_mem_sq
          F z i
    have heq :
        (F.coord (2 • z) i - F.squareJet z i) +
            (F.squareJet z i -
              (F.coord z i + F.coord z i)) =
          F.coord (2 • z) i -
            (F.coord z i + F.coord z i) := by
      ring
    rw [← heq]
    exact (I * I).add_mem hcompare hsquare
end FirstJetDoublingCompatibility
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
namespace FirstJetDoublingCompatibility
variable {H : AddSubgroup RationalPic}
variable {F : NearBaseFamily H}
/-- The two geometric producers assemble directly into the exact structure
consumed by the rational-point reduction endpoint. -/
def toRationalKernelDoublingData
    (C : FirstJetDoublingCompatibility F) :
    N13TwoAdicAbelChartSection.RationalKernelDoublingData H :=
  NearBaseFamily.ofDoublingLaw F C.toDoublingLaw
end FirstJetDoublingCompatibility
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
namespace MappedSpecialFamily
variable {H : AddSubgroup RationalPic}
/-- A mapped-special representative family reaches the rational-kernel
doubling structure once the selected doubles agree with transition squares
to first order. -/
def toRationalKernelDoublingData
    (R : MappedSpecialFamily H)
    (C :
      FirstJetDoublingCompatibility R.toNearBaseFamily) :
    N13TwoAdicAbelChartSection.RationalKernelDoublingData H :=
  C.toRationalKernelDoublingData
end MappedSpecialFamily
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
namespace MappedSpecialFamily
variable {H : AddSubgroup RationalPic}
/-- The recovered representatives and their first-jet doubling comparison
imply two-adic separatedness of the rational subgroup. -/
theorem separated
    (R : MappedSpecialFamily H)
    (C :
      FirstJetDoublingCompatibility R.toNearBaseFamily) :
    N18RouteC.Separated.NSeparated H 2 :=
  N13TwoAdicAbelChartSection.RationalKernelDoublingData.separated
    (R.toRationalKernelDoublingData C)
end MappedSpecialFamily
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MumfordCenteredDoublingAdapter
noncomputable section
open MazurProof.N13RationalKernelDoublingAdapter
namespace FirstJetDoublingCompatibility
variable {H : AddSubgroup RationalPic}
attribute [local instance] MazurProof.N13RationalKernelDoublingAdapter.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- Cross coefficients one and three of the centered square supply the
existing first-jet comparison interface.

The hypotheses mention only the two recovered monic quadratics.  Coordinate
doubling follows from the denominator-free reducer; subtracting the existing
square-transition estimate then gives `coord(2z) - squareJet(z)` modulo the
moving coordinate ideal squared. -/
def ofCenteredCrossCoefficients
    (F : NearBaseFamily H)
    (h₁ :
      ∀ z,
        ((F.pair z).u ^ 2 -
          N13AbelChartBase.baseSmoothMumford.u *
            (F.pair (2 • z)).u).coeff 1 ∈
          N13TwoAdicKernelChart.coordIdeal F.coord z *
            N13TwoAdicKernelChart.coordIdeal F.coord z)
    (h₃ :
      ∀ z,
        ((F.pair z).u ^ 2 -
          N13AbelChartBase.baseSmoothMumford.u *
            (F.pair (2 • z)).u).coeff 3 ∈
          N13TwoAdicKernelChart.coordIdeal F.coord z *
            N13TwoAdicKernelChart.coordIdeal F.coord z) :
    N13RationalKernelDoublingAdapter.FirstJetDoublingCompatibility F where
  compare z i := by
    let P := F.pair z
    let Q := F.pair (2 • z)
    let I := N13TwoAdicKernelChart.coordIdeal F.coord z
    have hcoord :
        F.coord (2 • z) i -
              (F.coord z i + F.coord z i) ∈
            I * I := by
      change
        N13TwoAdicAbelChartData.DiskPair.coord Q i -
              (N13TwoAdicAbelChartData.DiskPair.coord P i +
                N13TwoAdicAbelChartData.DiskPair.coord P i) ∈
            N13TwoAdicKernelChart.coordIdeal
                N13TwoAdicAbelChartData.DiskPair.coord P *
              N13TwoAdicKernelChart.coordIdeal
                N13TwoAdicAbelChartData.DiskPair.coord P
      apply
        N13MumfordCenteredDoublingJet.diskCoord_double_mod_sq_of_cross
          P Q
      · change
          ((F.pair z).u ^ 2 -
            N13AbelChartBase.baseSmoothMumford.u *
              (F.pair (2 • z)).u).coeff 1 ∈
            N13TwoAdicKernelChart.coordIdeal F.coord z *
              N13TwoAdicKernelChart.coordIdeal F.coord z
        exact h₁ z
      · change
          ((F.pair z).u ^ 2 -
            N13AbelChartBase.baseSmoothMumford.u *
              (F.pair (2 • z)).u).coeff 3 ∈
            N13TwoAdicKernelChart.coordIdeal F.coord z *
              N13TwoAdicKernelChart.coordIdeal F.coord z
        exact h₃ z
    have hsquare :
        F.squareJet z i -
              (F.coord z i + F.coord z i) ∈
            I * I := by
      simpa [I] using
        HuangN13.N13RationalKernelDoublingAdapter.NearBaseFamily.squareJet_sub_double_coord_mem_sq F z i
    have hsub := (I * I).sub_mem hcoord hsquare
    convert hsub using 1
    ring
end FirstJetDoublingCompatibility
end
end MazurProof.N13MumfordCenteredDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedMappedSpecialFamily
noncomputable section
open N13KernelBaseDivisor N13KernelInfinityMultiplicity N13KernelGraphContraction
open N13KernelBasePic N13TwoChartPicardRealization N13EffectiveGraphData
open N13RationalKernelDoublingAdapter
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
/-- K1 for the constructed specialization's actual kernel. -/
def mappedSpecialFamily : MappedSpecialFamily Kernel where
  representative z := Classical.choice (HuangN13.N13ConstructedMappedSpecialFamily.representative_nonempty z)
end
end MazurProof.N13ConstructedMappedSpecialFamily
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedMappedSpecialFamily
noncomputable section
open N13KernelBaseDivisor N13KernelInfinityMultiplicity N13KernelGraphContraction
open N13KernelBasePic N13TwoChartPicardRealization N13EffectiveGraphData
open N13RationalKernelDoublingAdapter
/-- Existing exact Hensel graph recovery supplies the centered family. -/
def nearBaseFamily : NearBaseFamily Kernel := mappedSpecialFamily.toNearBaseFamily
end
end MazurProof.N13ConstructedMappedSpecialFamily
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedKernelDoubling
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
open N13CenteredNumeratorPoleBounds N13GoodCenteredNumerator
open N13PrincipalHermiteNormalization N13ActualPrincipalNorm N13IntegralMatchedNorm
open N13IntegralHermiteCoefficientBounds
attribute [local instance] _root_.MazurProof.N13ConstructedKernelDoubling.instFactPrimeOfNatNat_fLT
/-- The exact existing unary compatibility, with no new arithmetic input. -/
def forFamily
    {H : AddSubgroup N13RationalKernelDoublingAdapter.RationalPic}
    (L : N13RationalKernelDoublingAdapter.NearBaseFamily H) :
    N13RationalKernelDoublingAdapter.FirstJetDoublingCompatibility L :=
  N13MumfordCenteredDoublingAdapter.FirstJetDoublingCompatibility.ofCenteredCrossCoefficients
    L (fun z => HuangN13.N13ConstructedKernelDoubling.selected_cross_coefficients L z 1)
      (fun z => HuangN13.N13ConstructedKernelDoubling.selected_cross_coefficients L z 3)
end
end MazurProof.N13ConstructedKernelDoubling
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedKernelDoubling
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
open N13CenteredNumeratorPoleBounds N13GoodCenteredNumerator
open N13PrincipalHermiteNormalization N13ActualPrincipalNorm N13IntegralMatchedNorm
open N13IntegralHermiteCoefficientBounds
attribute [local instance] _root_.MazurProof.N13ConstructedKernelDoubling.instFactPrimeOfNatNat_fLT
/-- K2 for the SAME near-base family constructed by K1. -/
def firstJetCompatibility :
    N13RationalKernelDoublingAdapter.FirstJetDoublingCompatibility
      N13ConstructedMappedSpecialFamily.nearBaseFamily :=
  forFamily N13ConstructedMappedSpecialFamily.nearBaseFamily
end
end MazurProof.N13ConstructedKernelDoubling
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedKernelDoubling
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
open N13CenteredNumeratorPoleBounds N13GoodCenteredNumerator
open N13PrincipalHermiteNormalization N13ActualPrincipalNorm N13IntegralMatchedNorm
open N13IntegralHermiteCoefficientBounds
attribute [local instance] _root_.MazurProof.N13ConstructedKernelDoubling.instFactPrimeOfNatNat_fLT
/-- Separation of the actual constructed additive specialization kernel. -/
theorem actual_kernel_separated :
    N18RouteC.Separated.NSeparated N13ConstructedSpecialization.specialization.ker 2 :=
  N13ConstructedMappedSpecialFamily.mappedSpecialFamily.separated firstJetCompatibility
end
end MazurProof.N13ConstructedKernelDoubling
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedRationalPointTheorem
noncomputable section
open N13ConstructedReductionClassifier
theorem quotient_kernel_eq :
    compatibleReduction.classifier.red.ker = N13ConstructedSpecialization.specialization.ker := by
  rw [N13ReductionClassifier.Data.red_ker]
  rfl
end
end MazurProof.N13ConstructedRationalPointTheorem
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedRationalPointTheorem
noncomputable section
open N13ConstructedReductionClassifier
theorem quotient_kernel_separated :
    N18RouteC.Separated.NSeparated compatibleReduction.classifier.red.ker 2 := by
  rw [quotient_kernel_eq]
  exact N13ConstructedKernelDoubling.actual_kernel_separated
end
end MazurProof.N13ConstructedRationalPointTheorem
end
end


set_option autoImplicit false
open Polynomial
theorem solution :
    MazurProof.N18RouteC.Separated.NSeparated MazurProof.N13ConstructedReductionClassifier.compatibleReduction.classifier.red.ker 2 := by
  exact MazurProof.N13ConstructedRationalPointTheorem.quotient_kernel_separated
