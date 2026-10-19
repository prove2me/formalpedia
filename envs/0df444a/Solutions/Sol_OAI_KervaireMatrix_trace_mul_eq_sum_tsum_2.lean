-- Prove2me | solution 2 for OAI.KervaireMatrix.trace_mul_eq_sum_tsum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:19:21.902216+00:00
-- url     : https://prove2.me/submissions/dc14a194-bf4a-4148-b8e1-44161ea2e2f3

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/MatrixTrace.lean:L92-L109
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireMatrix.trace_mul_eq_sum_tsum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace

-- ---- from OAI.GroupTheory.Kervaire.MatrixTrace ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireMatrix

section
open KervaireRegular
variable {D A : Type*} [Group A]
/-- Matrix equivariance with no countability restriction. -/
theorem matrix_coefficient {T : Operator D A} (hT : InCommutant T)
    (i j : D) (x y : A) : T (delta (j,y)) (i,x) = T (delta (j,1)) (i,x*y⁻¹) := by
  have he : T (delta (j,y)) = right y⁻¹ (T (delta (j,1))) := by
    have h := DFunLike.congr_fun (hT y⁻¹).eq (delta (j,1))
    simpa using h
  rw [he, right_apply]

/-- The reflected matrix coefficient identity for adjoints. -/
theorem star_coefficient {T : Operator D A} (hT : InCommutant T)
    (i j : D) (x : A) :
    star (star T (delta (i,1)) (j,x)) = T (delta (j,1)) (i,x⁻¹) := by
  calc
    star (star T (delta (i,1)) (j,x)) =
        inner ℂ (star T (delta (i,1))) (delta (j,x)) :=
      (inner_delta_right _ _).symm
    _ = inner ℂ (delta (i,1)) (T (delta (j,x))) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    _ = T (delta (j,x)) (i,1) := inner_delta_left _ _
    _ = T (delta (j,1)) (i,x⁻¹) := by simpa using matrix_coefficient hT i j 1 x

variable [Fintype D]

omit [Fintype D] in
/-- All double series below are absolutely summable, even for an uncountable group. -/
theorem summable_product_coefficients {S T : Operator D A} (hS : InCommutant S) (i : D) :
    Summable (fun p : D × A => S (delta (p.1,1)) (i,p.2⁻¹) * T (delta (i,1)) p) := by
  have h := lp.summable_inner (𝕜 := ℂ) (star S (delta (i,1))) (T (delta (i,1)))
  apply h.congr
  rintro ⟨j,x⟩
  rw [RCLike.inner_apply, mul_comm]
  change star (star S (delta (i,1)) (j,x)) * _ = _
  rw [star_coefficient hS]

/-- Trace multiplication expressed by regular matrix coefficients. -/
theorem trace_mul_eq_sum_tsum {S T : Operator D A} (hS : InCommutant S) :
    trace (S*T) = ∑ i : D, ∑ j : D, ∑' x : A,
      S (delta (j,1)) (i,x⁻¹) * T (delta (i,1)) (j,x) := by
  rw [trace_apply]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ (delta (i,1)) (S (T (delta (i,1)))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left, lp.inner_eq_tsum]
  simp only [← ContinuousLinearMap.star_eq_adjoint]
  have he : (∑' p : D × A, inner ℂ (star S (delta (i,1)) p) (T (delta (i,1)) p)) =
      ∑' p : D × A, S (delta (p.1,1)) (i,p.2⁻¹) * T (delta (i,1)) p := by
    apply tsum_congr
    rintro ⟨j,x⟩
    rw [RCLike.inner_apply, mul_comm]
    change star (star S (delta (i,1)) (j,x)) * _ = _
    rw [star_coefficient hS]
  rw [he, (summable_product_coefficients hS i).tsum_prod, tsum_fintype]

end

section
open KervaireRegular
variable {D A : Type*} [Fintype D] [Group A]

end

section
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Group A]

variable [Fintype D]

end

open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireMatrix
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open KervaireRegular


theorem solution : type_of% @_root_.OAI.KervaireMatrix.trace_mul_eq_sum_tsum := @_root_.OAI.KervaireMatrix.trace_mul_eq_sum_tsum
