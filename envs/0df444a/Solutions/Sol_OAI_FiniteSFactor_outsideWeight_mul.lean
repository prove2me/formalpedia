-- Prove2me | solution 1 for OAI.FiniteSFactor.outsideWeight_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:15:41.259675+00:00
-- url     : https://prove2.me/submissions/d1f06072-8ff4-4fd3-8aa4-43b9d438df4c

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
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
open OAI.FiniteSFactor
namespace OAI.FiniteSFactor
theorem _root_.solution (S : Finset (Ideal O))
    (hprime : ∀ P ∈ S, Prime P) (w : Ideal O → ℂ)
    (I J : Ideal O) (hweight : w (I * J) = w I * w J) :
    outsideWeight S w (I * J) =
      outsideWeight S w I * outsideWeight S w J := by
  classical
  let good (K : Ideal O) : Prop := ∀ P ∈ S, ¬ P ∣ K
  have hleft : good (I * J) → good I := by
    intro h P hP hd
    exact h P hP (dvd_mul_of_dvd_left hd J)
  have hright : good (I * J) → good J := by
    intro h P hP hd
    exact h P hP (dvd_mul_of_dvd_right hd I)
  have hboth : good I → good J → good (I * J) := by
    intro hI hJ P hP hd
    rcases (hprime P hP).dvd_mul.mp hd with hdI | hdJ
    · exact hI P hP hdI
    · exact hJ P hP hdJ
  change (if good (I * J) then w (I * J) else 0) =
    (if good I then w I else 0) * (if good J then w J else 0)
  by_cases hI : good I
  · by_cases hJ : good J
    · have hIJ := hboth hI hJ
      simp [hI, hJ, hIJ, hweight]
    · have hIJ : ¬good (I * J) := fun h => hJ (hright h)
      simp [hI, hJ, hIJ]
  · have hIJ : ¬good (I * J) := fun h => hI (hleft h)
    simp [hI, hIJ]
end OAI.FiniteSFactor
