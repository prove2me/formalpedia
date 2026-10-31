-- Prove2me | solution 1 for HuangN13.N13EffectiveDataCompatibility.exists_certified_realization
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:27:45.386979+00:00
-- url     : https://prove2.me/submissions/a48753f3-69ea-4b3a-8b0f-91766f9a85ec

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Theorems.Thm_HuangN13_N13MarkedEffectiveData_exists_marked_repaired_data
import Theorems.Thm_MazurProof_N13InfinityBaseChange_infinityCompatible
import Theorems.Thm_MazurProof_SexticMumford_OrientedBaseChange_nonZeroDivisors_le_comap

set_option autoImplicit false

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
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
@[simp] theorem coordinateMap_xClass
    (ι : K →+* K') (hM : M.f.map ι = M'.f) (p : K[X]) :
    coordinateMap ι hM (xClass M p) =
      xClass M' (p.map ι) := by
  exact AdjoinRoot.map_of
    (mapPoly ι) (curvePoly M) (curvePoly M')
      (target_curve_dvd ι hM) p
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
@[simp] theorem coordinateMap_yClass
    (ι : K →+* K') (hM : M.f.map ι = M'.f) :
    coordinateMap ι hM (yClass M) = yClass M' := by
  exact AdjoinRoot.map_root
    (mapPoly ι) (curvePoly M) (curvePoly M')
      (target_curve_dvd ι hM)
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
@[simp] theorem coordinateMap_ySubClass
    (ι : K →+* K') (hM : M.f.map ι = M'.f) (v : K[X]) :
    coordinateMap ι hM (ySubClass M v) =
      ySubClass M' (v.map ι) := by
  simp [ySubClass]
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
/-- A Mumford graph ideal extends to the coefficient-extended graph ideal. -/
theorem map_mumfordIdeal
    (ι : K →+* K') (hM : M.f.map ι = M'.f)
    (u v : K[X]) :
    Ideal.map (coordinateMap ι hM) (mumfordIdeal M u v) =
      mumfordIdeal M' (u.map ι) (v.map ι) := by
  rw [mumfordIdeal, mumfordIdeal, Ideal.map_span, Set.image_pair,
    coordinateMap_xClass, coordinateMap_ySubClass]
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
theorem invFracMap_mumfordIdealUnit
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) :
    invFracMap ι hι hM (mumfordIdealUnit M D.toSemi) =
      mumfordIdealUnit M' (D.mapCoeffs ι hι hM).toSemi := by
  apply Units.ext
  simp only [invFracMap, Units.coe_map, coe_mumfordIdealUnit]
  change
    (FractionalIdeal.extendedHom' (FunctionField M')
      (nonZeroDivisors_le_comap ι hι hM))
        (mumfordIdeal M D.u D.v :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      (mumfordIdeal M'
          (D.u.map ι) (D.v.map ι) :
        FractionalIdeal (CoordinateRing M')⁰ (FunctionField M'))
  calc
    _ =
        (Ideal.map (coordinateMap ι hM)
            (mumfordIdeal M D.u D.v) :
          FractionalIdeal (CoordinateRing M')⁰ (FunctionField M')) :=
      FractionalIdeal.extended_coeIdeal_eq_map
        (FunctionField M')
        (nonZeroDivisors_le_comap ι hι hM)
        (mumfordIdeal M D.u D.v)
    _ = _ := by rw [map_mumfordIdeal]
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
theorem orientedFracMap_mumfordRaw
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) :
    orientedFracMap ι hι hM (mumfordRaw M D) =
      mumfordRaw M' (D.mapCoeffs ι hι hM) := by
  apply Prod.ext
  · change
      invFracMap ι hι hM (mumfordIdealUnit M D.toSemi) =
        mumfordIdealUnit M' (D.mapCoeffs ι hι hM).toSemi
    exact invFracMap_mumfordIdealUnit ι hι hM D
  · rfl
end
end MazurProof.SexticMumford.OrientedBaseChange
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
/-- The quotient map sends the class of a Mumford graph to the class of its
coefficient extension. -/
@[simp] theorem picMap_classOf
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f)
    (O : InfinityOrder M) (O' : InfinityOrder M')
    (hO : InfinityCompatible ι hι hM O O')
    (D : Mumford M) :
    picMap ι hι hM O O' hO (classOf M O D) =
      classOf M' O' (D.mapCoeffs ι hι hM) := by
  change
    Additive.ofMul
        ((QuotientGroup.map
          (principalOriented M O).range
          (principalOriented M' O').range
          (orientedFracMap ι hι hM)
          (principalRange_le_comap ι hι hM O O' hO))
            (QuotientGroup.mk' (principalOriented M O).range
              (mumfordRaw M D))) =
      Additive.ofMul
        (QuotientGroup.mk' (principalOriented M' O').range
          (mumfordRaw M' (D.mapCoeffs ι hι hM)))
  rw [QuotientGroup.map_mk', orientedFracMap_mumfordRaw]
  rfl
end
end MazurProof.SexticMumford.OrientedBaseChange
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
@[simp] theorem picMapRatToQ₂_classOf
    (D : N13Mumford.Mumford ℚ) :
    picMapRatToQ₂
        (SexticMumford.classOf
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ) D) =
      SexticMumford.classOf
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (D.mapCoeffs ratToQ₂ ratToQ₂_injective
          (map_n13_f ratToQ₂)) := by
  exact SexticMumford.OrientedBaseChange.picMap_classOf
    ratToQ₂ ratToQ₂_injective (map_n13_f ratToQ₂)
    (N13Infinity.positiveInfinityOrder ℚ)
    (N13Infinity.positiveInfinityOrder Q₂)
    (infinityCompatible ratToQ₂ ratToQ₂_injective) D
end
end MazurProof.N13InfinityBaseChange
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveDataCompatibility
noncomputable section
open N13OverlapBranchCompatibility N13PrincipalBranchIdeals
open N13TwoChartPicardRealization hiding Q₂
open N13InfinityChartMarking hiding Line B QP
open N13EffectiveInfinityRepair hiding Model
open N13MarkedTensorComparison
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem exists_certified_realization (P : G) :
    ∃ D : Data, Certified D ∧ D.toGenericPic = N13InfinityBaseChange.picMapRatToQ₂ P := by
  obtain ⟨D, hD⟩ := N13MumfordInfinityBalance.classOf_surjective P
  let M := D.mapCoeffs (M' := N13Mumford.model N13InfinityBaseChange.Q₂)
    N13InfinityBaseChange.ratToQ₂
    N13InfinityBaseChange.ratToQ₂_injective
    (by simpa only [N13Mumford.model_f] using
      N13InfinityBaseChange.map_n13_f N13InfinityBaseChange.ratToQ₂)
  obtain ⟨W, hraw, hgeneric, hs, hm⟩ := HuangN13.N13MarkedEffectiveData.exists_marked_repaired_data M
  refine ⟨W, ⟨repair M, repair_effective M, hraw, hs, hm⟩, ?_⟩
  rw [hgeneric]
  change SexticMumford.classOf Model (N13Infinity.positiveInfinityOrder Q₂)
      (D.mapCoeffs N13InfinityBaseChange.ratToQ₂
        N13InfinityBaseChange.ratToQ₂_injective
        (N13InfinityBaseChange.map_n13_f N13InfinityBaseChange.ratToQ₂)) = _
  rw [← N13InfinityBaseChange.picMapRatToQ₂_classOf, hD]
end
end MazurProof.N13EffectiveDataCompatibility
end
end


set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem solution (P : MazurProof.N13EffectiveDataCompatibility.G) :
    ∃ D : MazurProof.N13TwoChartPicardRealization.Data, MazurProof.N13EffectiveDataCompatibility.Certified D ∧ D.toGenericPic = MazurProof.N13InfinityBaseChange.picMapRatToQ₂ P := by
  exact MazurProof.N13EffectiveDataCompatibility.exists_certified_realization P
