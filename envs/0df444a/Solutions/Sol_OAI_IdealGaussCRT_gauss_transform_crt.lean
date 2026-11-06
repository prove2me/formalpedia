-- Prove2me | solution 1 for OAI.IdealGaussCRT.gauss_transform_crt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:34.710214+00:00
-- url     : https://prove2.me/submissions/c6353a44-b6dc-4aa6-a41b-72cc7f06b5d3

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_GaussCRT_gauss_sum_crt
import Theorems.Thm_OAI_IdealGaussCRT_gauss_sum_crt
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftFiniteGaussFourier_gauss_transform
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
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
namespace ShortDraftLatticeCount
end ShortDraftLatticeCount
namespace ActualEisensteinCubic
open ShortDraftCusp
end ActualEisensteinCubic
namespace ShortDraftCusp
variable {R : Type*} [CommRing R]
end ShortDraftCusp
namespace ShortDraftLatticeCount
open ActualEisensteinCoordinates
end ShortDraftLatticeCount
namespace AnalyticBridge
end AnalyticBridge
namespace ShortDraftLatticeCount
open ActualEisensteinCoordinates
end ShortDraftLatticeCount
namespace IdealGaussCRT
open AddChar MulChar
private theorem leftAddChar_mulShift {T R S : Type*}
    [CommRing T] [CommRing R] [CommRing S]
    (e : T ≃+* R × S) (ψ : AddChar T ℂ) (h : T) :
    leftAddChar e (ψ.mulShift h) =
      (leftAddChar e ψ).mulShift (e h).1 := by
  ext z
  change ψ (h * e.symm (z, 0)) = ψ (e.symm ((e h).1 * z, 0))
  congr 1
  apply e.injective
  ext <;> simp
private theorem rightAddChar_mulShift {T R S : Type*}
    [CommRing T] [CommRing R] [CommRing S]
    (e : T ≃+* R × S) (ψ : AddChar T ℂ) (h : T) :
    rightAddChar e (ψ.mulShift h) =
      (rightAddChar e ψ).mulShift (e h).2 := by
  ext z
  change ψ (h * e.symm (0, z)) = ψ (e.symm (0, (e h).2 * z))
  congr 1
  apply e.injective
  ext <;> simp
end IdealGaussCRT
namespace ActualEisensteinCubic
section
open ShortDraftLatticeCount
end
open AddChar MulChar
end ActualEisensteinCubic
end
end OAI
end

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
open OAI.IdealGaussCRT
open AddChar MulChar
namespace OAI.IdealGaussCRT
theorem _root_.solution {T R S : Type*}
    [CommRing T] [Field R] [Field S]
    [Fintype T] [Fintype R] [Fintype S]
    (e : T ≃+* R × S)
    (χR : MulChar R ℂ) (χS : MulChar S ℂ)
    (ψ : AddChar T ℂ) (hχR : χR ≠ 1) (hχS : χS ≠ 1)
    (h : T) :
    (∑ x : T, χR (e x).1 * χS (e x).2 * ψ (h * x)) =
      (if (e h).1 = 0 then 0 else
        (χR (e h).1)⁻¹ * gaussSum χR (leftAddChar e ψ)) *
      (if (e h).2 = 0 then 0 else
        (χS (e h).2)⁻¹ * gaussSum χS (rightAddChar e ψ)) := by
  have hbase := gauss_sum_crt e χR χS (ψ.mulShift h)
  simp only [AddChar.mulShift_apply] at hbase
  rw [leftAddChar_mulShift, rightAddChar_mulShift] at hbase
  have hR := ShortDraftFiniteGaussFourier.gauss_transform χR
    (leftAddChar e ψ) hχR (e h).1
  have hS := ShortDraftFiniteGaussFourier.gauss_transform χS
    (rightAddChar e ψ) hχS (e h).2
  have hR' : gaussSum χR ((leftAddChar e ψ).mulShift (e h).1) =
      (if (e h).1 = 0 then 0 else
        (χR (e h).1)⁻¹ * gaussSum χR (leftAddChar e ψ)) := by
    simpa only [gaussSum, AddChar.mulShift_apply] using hR
  have hS' : gaussSum χS ((rightAddChar e ψ).mulShift (e h).2) =
      (if (e h).2 = 0 then 0 else
        (χS (e h).2)⁻¹ * gaussSum χS (rightAddChar e ψ)) := by
    simpa only [gaussSum, AddChar.mulShift_apply] using hS
  rw [hR', hS'] at hbase
  exact hbase
end OAI.IdealGaussCRT
