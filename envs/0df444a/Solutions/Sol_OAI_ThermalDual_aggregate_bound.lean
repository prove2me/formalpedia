-- Prove2me | solution 1 for OAI.ThermalDual.aggregate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:25:52.556811+00:00
-- url     : https://prove2.me/submissions/18160255-5815-4348-9d9d-c049e1d34f83

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Duality.lean:L471-L510
-- (upload_full_project.md Phase 4): solution for node OAI.ThermalDual.aggregate_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality

-- ---- from OAI.InformationTheory.PhotonNumber.Duality ----
namespace OAI

noncomputable section

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end EntropyPhotonNumber.SpectralLogData

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace TensorLp
open EntropyPhotonNumber
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded BeamLadder Annihilation
variable {n : ℕ}

namespace WeightedColumns
variable {ρ σ τ : State n}

end WeightedColumns
end EntropyPhotonNumber

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

end

open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology Complex MeasureTheory

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace ThermalDual

variable {I J : Type*} [Fintype I] [Fintype J]

theorem modes_triangle (q a b : J → ℝ) (hq : ∀ j, 0 ≤ q j)
    (_ha : ∀ j, 0 ≤ a j) (_hb : ∀ j, 0 ≤ b j) (hh : ∀ j, q j ≤ a j+b j) :
    Real.sqrt (∑ j, q j^2) ≤ Real.sqrt (∑ j, a j^2)+Real.sqrt (∑ j, b j^2) := by
  have hs : ∑ j, q j^2 ≤ ∑ j, (a j+b j)^2 := by
    exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (hq j) (hh j) 2)
  have he : (∑ j, (a j+b j)^2)=(∑ j, a j^2)+2*(∑ j, a j*b j)+(∑ j, b j^2) := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    ring_nf
  rw [he] at hs
  have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have hqa := Real.sq_sqrt (show 0 ≤ ∑ j, a j^2 from Finset.sum_nonneg (fun j _ => sq_nonneg (a j)))
  have hqb := Real.sq_sqrt (show 0 ≤ ∑ j, b j^2 from Finset.sum_nonneg (fun j _ => sq_nonneg (b j)))
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith

end ThermalDual

namespace ThermalSpectral
open EntropyPhotonNumber ThermalMetric
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace ThermalDual

section
open EntropyPhotonNumber ThermalMetric ThermalSpectral
open scoped BigOperators
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Fintype K]

end

section
variable {I J : Type*} [Fintype I] [Fintype J]

theorem aggregate_bound (w : I → ℝ) (hw : ∀ i, 0≤w i)
    (q0 g : J → ℝ) (q m : I → J → ℝ) (hq : ∀ j, 0≤q0 j)
    (hg : ∀ j, 0≤g j) (C κ : ℝ) (hC : 0≤C) (hκ : κ ∈ Set.Icc 0 1)
    (hm : ∀ j, (1-κ)*g j^2≤2*∑ i, w i*m i j^2)
    (hmode : ∀ j, q0 j≤Real.sqrt (∑ i, w i*q i j^2)+Real.sqrt ((1-κ)*κ)*g j*C) :
    Real.sqrt (∑ j, q0 j^2)≤Real.sqrt (∑ i, w i*∑ j, q i j^2)+
      Real.sqrt (2*κ)*C*Real.sqrt (∑ i, w i*∑ j, m i j^2) := by
  have hqsum j : 0≤∑ i, w i*q i j^2 := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have hmsum : 0≤∑ i, w i*∑ j, m i j^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
  have hh := modes_triangle q0 (fun j => Real.sqrt (∑ i, w i*q i j^2))
    (fun j => Real.sqrt ((1-κ)*κ)*g j*C) hq (fun _ => Real.sqrt_nonneg _)
    (fun j => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hg j)) hC) hmode
  have hqa : (∑ j, (Real.sqrt (∑ i, w i*q i j^2))^2)=∑ i, w i*∑ j, q i j^2 := by
    simp only [Real.sq_sqrt (hqsum _), Finset.mul_sum]
    exact Finset.sum_comm
  have hgm : (1-κ)*(∑ j, g j^2)≤2*(∑ i, w i*∑ j, m i j^2) := by
    calc
      _ = ∑ j, (1-κ)*g j^2 := Finset.mul_sum ..
      _ ≤ ∑ j, 2*∑ i, w i*m i j^2 := Finset.sum_le_sum (fun j _ => hm j)
      _ = 2*∑ i, w i*∑ j, m i j^2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.mul_sum]
  have hc : (∑ j, (Real.sqrt ((1-κ)*κ)*g j*C)^2) ≤
      (Real.sqrt (2*κ)*C*Real.sqrt (∑ i, w i*∑ j, m i j^2))^2 := by
    simp only [mul_pow, Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hκ.2) hκ.1),
      Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hκ.1), Real.sq_sqrt hmsum]
    calc
      _ = (κ*C^2)*((1-κ)*∑ j, g j^2) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ (κ*C^2)*(2*(∑ i, w i*∑ j, m i j^2)) :=
        mul_le_mul_of_nonneg_left hgm (mul_nonneg hκ.1 (sq_nonneg C))
      _ = _ := by ring
  have hc' := Real.sqrt_le_sqrt hc
  rw [Real.sqrt_sq (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC) (Real.sqrt_nonneg _))] at hc'
  rw [hqa] at hh
  exact hh.trans (add_le_add le_rfl hc')
end

open scoped ComplexConjugate

end ThermalDual

end

end OAI

-- ---- platform node ----
open OAI OAI.ThermalDual
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology Complex MeasureTheory


theorem solution : type_of% @_root_.OAI.ThermalDual.aggregate_bound := @_root_.OAI.ThermalDual.aggregate_bound
