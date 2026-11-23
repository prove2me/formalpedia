-- Prove2me | solution 1 for GlobalTheory.LGrp.nabs_det_of_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:10.569063+00:00
-- url     : https://prove2.me/submissions/ed859e80-e8a8-4118-b8fd-0b0539019d32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_SmGL_nabs_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.lFactor_zero
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
section
open MeasureTheory Matrix
noncomputable section
namespace GlobalTheory.LGrp
section Rational
open Polynomial
end Rational
section ZetaNonvanishing₂
open ValuativeRel GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable [MeasurableSpace (GL n k)]
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ}
open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
omit [MeasurableSpace (GL n k)] in
private theorem valuation_det_le_one_of_entries_integer {y : GL n k}
    (h : ∀ i j, (y : Matrix n n k) i j ∈ (valuation k).integer) :
    valuation k (GeneralLinearGroup.det y : k) ≤ 1 := by
  set A : Matrix n n (valuation k).integer := Matrix.of fun i j => ⟨(y : Matrix n n k) i j, h i j⟩
  have e : (y : Matrix n n k) = ((valuation k).integer.subtype).mapMatrix A := by
    ext i j
    rfl
  have hd : (GeneralLinearGroup.det y : k) = (valuation k).integer.subtype A.det := by
    rw [GeneralLinearGroup.val_det_apply, RingHom.map_det, ← e]
  rw [hd]
  exact (Valuation.mem_integer_iff _ _).mp (SetLike.coe_mem _)
end ZetaNonvanishing₂
end GlobalTheory.LGrp
end
end

set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open ValuativeRel GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable [MeasurableSpace (GL n k)]
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ}
open MeasureTheory Matrix
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable [MeasurableSpace (GL n k)]
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ}
omit [MeasurableSpace (GL n k)]
namespace GlobalTheory.LGrp
namespace _root_.GlobalTheory.LGrp
theorem _root_.solution {x : GL n k}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det x) = 1 := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff] at hx
  apply _root_.GlobalTheory.SmGL.nabs_eq_one
  have h1 := valuation_det_le_one_of_entries_integer hx.1
  have h2 := valuation_det_le_one_of_entries_integer hx.2
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀] at h2
  have hpos : 0 < valuation k (GeneralLinearGroup.det x : k) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)
end _root_.GlobalTheory.LGrp
end GlobalTheory.LGrp
