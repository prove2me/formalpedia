-- Prove2me | solution 1 for GlobalTheory.LGrp.nabs_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:59.877575+00:00
-- url     : https://prove2.me/submissions/00a9ba34-993e-403e-85f1-4ffb2225a39e

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
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_one
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_zero_iff
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_uniformiser
import Theorems.Thm_GlobalTheory_SplitWeil_one_lt_resCard

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
private theorem smGL_ord_pow_eq_mul (x : kˣ) (m : ℕ) :
    _root_.GlobalTheory.SmGL.ord k (x ^ m) = m * _root_.GlobalTheory.SmGL.ord k x := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp)
  | succ m ih =>
    rw [pow_succ, _root_.GlobalTheory.SmGL.ord_mul, ih]
    push_cast
    ring
open MeasureTheory Matrix in
open ValuativeRel in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
variable [MeasurableSpace (GL n k)] in
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ} in
private theorem exists_unit_ord_eq_one_and_nabs_eq_inv_resCard :
    ∃ ϖ : kˣ, _root_.GlobalTheory.SmGL.ord k ϖ = 1 ∧
      _root_.GlobalTheory.SplitWeil.nabs k ϖ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ)⁻¹ := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (valuation k).integer
  have hp0 : (p : k) ≠ 0 := by
    intro h
    exact hp.ne_zero (Subtype.ext h)
  obtain ⟨y, hy⟩ : ∃ y : k, valuation k y = uniformizer k := valuation_surjective _
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact (uniformizer_pos (R := k)).ne hy
  have hyint : y ∈ (valuation k).integer := by
    rw [Valuation.mem_integer_iff, hy]
    exact uniformizer_lt_one.le
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := (⟨y, hyint⟩ : (valuation k).integer)) (fun h => hy0 (congrArg Subtype.val h)) hp
  have hu0 : ((u : (valuation k).integer) : k) ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  refine ⟨Units.mk0 (p : k) hp0, ?_, _root_.GlobalTheory.SplitWeil.nabs_uniformiser hp rfl⟩
  have hyo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 y hy0) = 1 :=
    _root_.GlobalTheory.SmGL.ord_eq_one hy
  have huo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 _ hu0) = 0 := by
    apply _root_.GlobalTheory.SmGL.ord_eq_zero
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
  have hsplit : Units.mk0 y hy0 = Units.mk0 _ hu0 * Units.mk0 (p : k) hp0 ^ m := by
    ext
    have := congrArg Subtype.val hu
    simpa using this
  rw [hsplit, _root_.GlobalTheory.SmGL.ord_mul, huo, smGL_ord_pow_eq_mul,
    zero_add] at hyo
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hyo with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2
  · omega
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
theorem _root_.solution (x : kˣ) :
    _root_.GlobalTheory.SplitWeil.nabs k x =
      (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-_root_.GlobalTheory.SmGL.ord k x) := by
  obtain ⟨ϖ, hord, habs⟩ := exists_unit_ord_eq_one_and_nabs_eq_inv_resCard (k := k)
  have hq : (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ≠ 0 := by
    have := _root_.GlobalTheory.SplitWeil.one_lt_resCard k
    positivity
  have hinv : _root_.GlobalTheory.SplitWeil.nabs k ϖ⁻¹ = _root_.GlobalTheory.SplitWeil.resCard k := by
    have h := _root_.GlobalTheory.SplitWeil.nabs_mul k ϖ ϖ⁻¹
    rw [mul_inv_cancel, _root_.GlobalTheory.SplitWeil.nabs_one, habs] at h
    exact ((inv_mul_eq_one₀ hq).mp h.symm).symm
  have oinv : _root_.GlobalTheory.SmGL.ord k ϖ⁻¹ = -1 := by
    have h := _root_.GlobalTheory.SmGL.ord_mul k ϖ ϖ⁻¹
    rw [mul_inv_cancel, hord,
      _root_.GlobalTheory.SmGL.ord_eq_zero (x := (1 : kˣ)) (by simp)] at h
    omega
  have key : ∀ m : ℤ, _root_.GlobalTheory.SplitWeil.nabs k (ϖ ^ m) =
      (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) ∧ _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
    intro m
    refine Int.induction_on m ?_ ?_ ?_
    · refine ⟨by simp [_root_.GlobalTheory.SplitWeil.nabs_one], ?_⟩
      rw [zpow_zero]
      exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp)
    · intro i ih
      rw [_root_.zpow_add_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
        ih.1, ih.2, habs, hord]
      refine ⟨?_, rfl⟩
      rw [neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
    · intro i ih
      rw [_root_.zpow_sub_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
        ih.1, ih.2, hinv, oinv]
      refine ⟨?_, by ring⟩
      rw [show -(-(i : ℤ) - 1) = -(-(i : ℤ)) + 1 by ring, zpow_add₀ hq, _root_.zpow_one]
  set o := _root_.GlobalTheory.SmGL.ord k x
  have hy : _root_.GlobalTheory.SmGL.ord k (x * ϖ ^ (-o)) = 0 := by
    rw [_root_.GlobalTheory.SmGL.ord_mul, (key _).2]
    ring
  have hy1 : _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o)) = 1 :=
    _root_.GlobalTheory.SmGL.nabs_eq_one k
      (_root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp hy)
  have hx : x * ϖ ^ (-o) * ϖ ^ o = x := by
    rw [mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]
  calc _root_.GlobalTheory.SplitWeil.nabs k x
      = _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o) * ϖ ^ o) := by rw [hx]
    _ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-o) := by
      rw [_root_.GlobalTheory.SplitWeil.nabs_mul, hy1, (key o).1, one_mul]
end _root_.GlobalTheory.LGrp
end GlobalTheory.LGrp
