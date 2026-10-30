-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.card_integer_representative_le_rank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:01:44.231881+00:00
-- url     : https://prove2.me/submissions/8832ec36-8b56-4e59-a643-2e873e32a4ef

import Mathlib
import Definitions.Def_OAIQ081S114

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutExactBuckets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact integer signatures survive every coefficient-ring reduction

The assignments in this module are integer vectors. In the counting
application they are Boolean vectors or differences of Boolean vectors.
Equality of signatures is an equality in `ℤ`, before any reduction.
No claim about the kernel of a matrix reduced modulo a prime is used.
-/

namespace SubexponentialSAT.SqrtLog.LayoutExactBuckets

open scoped BigOperators
open LayoutPullback

variable {V J R : Type*} [Fintype V] [CommRing R]

theorem signature_sub (A : J → V → ℤ) (x y : V → ℤ) (j : J) :
    signature A (x - y) j = signature A x j - signature A y j := by
  simp [signature, mul_sub, Finset.sum_sub_distrib]

section RationalRowReduction

variable {J' : Type*} [Fintype J']

theorem integer_kernel_of_rational_span (C : J → V → ℤ) (A : J' → V → ℤ)
    (hspan : RationalRowSpan C A) (z : V → ℤ)
    (hz : ∀ j, signature A z j = 0) : ∀ j, signature C z j = 0 := by
  intro j
  obtain ⟨c, hc⟩ := hspan j
  have hA (k : J') : ∑ v, (A k v : ℚ) * (z v : ℚ) = 0 := by
    exact_mod_cast hz k
  have hC : ∑ v, (C j v : ℚ) * (z v : ℚ) = 0 := by
    simp_rw [hc, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, hA, mul_zero]
    simp
  exact_mod_cast hC

end RationalRowReduction

end SubexponentialSAT.SqrtLog.LayoutExactBuckets

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutRowSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Selecting actual integer constraint rows

This module isolates the semantic certificate for row selection. A later finite
minor search may produce the certificate; rational spanning is used only before
reduction, so the actual rows and their integer coefficient bounds are retained.
-/

namespace SubexponentialSAT.SqrtLog.LayoutRowSelection

open scoped BigOperators
open LayoutExactBuckets

universe u v

variable {J : Type u} {V : Type v} [Fintype J] [Fintype V]

omit [Fintype J] [Fintype V] in
theorem rationalRowSpan_of_span_eq {K : Type*} [Fintype K]
    (C : J → V → ℤ) (select : K → J)
    (hspan : Submodule.span ℚ (Set.range (rationalRows C ∘ select)) =
      Submodule.span ℚ (Set.range (rationalRows C))) :
    RationalRowSpan C (fun k => C (select k)) := by
  intro j
  have hj : rationalRows C j ∈
      Submodule.span ℚ (Set.range (rationalRows C ∘ select)) := by
    rw [hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hj
  refine ⟨c, fun v => ?_⟩
  have hv := congrFun hc v
  simpa [rationalRows, Function.comp_def] using hv.symm

omit [Fintype V] in
/-- The number of selected actual rows is exactly the rational constraint rank.
No coefficient rescaling and no modular row-space assertion is involved. -/
theorem exists_actual_row_basis (C : J → V → ℤ) :
    ∃ (K : Type u) (_ : Fintype K) (select : K → J),
      Function.Injective select ∧
      RationalRowSpan C (fun k => C (select k)) ∧
      Fintype.card K = Module.finrank ℚ
        (Submodule.span ℚ (Set.range (rationalRows C))) := by
  obtain ⟨K, select, hinj, hspan, hli⟩ :=
    exists_linearIndependent' ℚ (rationalRows C)
  let _ : Fintype K := Fintype.ofInjective select hinj
  refine ⟨K, inferInstance, select, hinj,
    rationalRowSpan_of_span_eq C select hspan, ?_⟩
  rw [← hspan]
  exact (finrank_span_eq_card hli).symm

end SubexponentialSAT.SqrtLog.LayoutRowSelection

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSignatureBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFinite _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact integer signature ranges for Boolean assignments. -/
namespace SubexponentialSAT.SqrtLog.LayoutSignatureBound

open scoped BigOperators
open LayoutExactBuckets

variable {J V : Type*} [Fintype J] [Fintype V]

omit [Fintype J] in
theorem abs_boolSignature_le (A : J → V → ℤ) (W : ℕ)
    (hA : ∀ j v, |A j v| ≤ (W : ℤ)) (x : V → Bool) (j : J) :
    |boolSignature A x j| ≤ (Fintype.card V * W : ℕ) := by
  unfold boolSignature signature
  calc
    _ ≤ ∑ v, |A j v * (if x v then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : V, (W : ℤ) := by
      apply Finset.sum_le_sum
      intro v _
      cases h : x v <;> simp [ hA j v]
    _ = (Fintype.card V * W : ℕ) := by simp

/-- The number of attained integer labels has the usual height/rank bound,
independently of the characteristic and prime-power precision used later. -/
theorem card_range_boolSignature_le (A : J → V → ℤ) (W : ℕ)
    (hA : ∀ j v, |A j v| ≤ (W : ℤ)) :
    Nat.card (Set.range (boolSignature A)) ≤
      (2 * Fintype.card V * W + 1) ^ Fintype.card J := by
  classical
  let B := Fintype.card V * W
  let enc : Set.range (boolSignature A) → (J → Fin (2 * B + 1)) := fun y j =>
    ⟨(y.val j + (B : ℤ)).toNat, by
      obtain ⟨x, hx⟩ := y.property
      have hb := abs_boolSignature_le A W hA x j
      have hbounds := abs_le.mp hb
      have hy : y.val j = boolSignature A x j := congrFun hx.symm j
      rw [hy]
      dsimp [B]
      omega⟩
  have hinj : Function.Injective enc := by
    intro y z he
    apply Subtype.ext
    funext j
    have heq := congrArg Fin.val (congrFun he j)
    change (y.val j + (B : ℤ)).toNat = (z.val j + (B : ℤ)).toNat at heq
    obtain ⟨x, hx⟩ := y.property
    obtain ⟨w, hw⟩ := z.property
    have hy := abs_le.mp (abs_boolSignature_le A W hA x j)
    have hz := abs_le.mp (abs_boolSignature_le A W hA w j)
    have ey : y.val j = boolSignature A x j := congrFun hx.symm j
    have ez : z.val j = boolSignature A w j := congrFun hw.symm j
    dsimp [B] at heq
    rw [ey, ez] at heq ⊢
    omega
  have hc := Nat.card_le_card_of_injective enc hinj
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun, B, Nat.mul_assoc] using hc

end SubexponentialSAT.SqrtLog.LayoutSignatureBound

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutRankSignature
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime signatures may retain every raw integer row.  A row basis is
used only in this cardinality proof, never computed by the bucket program. -/
namespace SubexponentialSAT.SqrtLog.LayoutSignatureBound

open scoped BigOperators
open LayoutExactBuckets LayoutRowSelection

variable {J K V : Type*} [Fintype J] [Fintype K] [Fintype V]

omit [Fintype J] in
theorem signature_eq_of_rationalRowSpan (C : J → V → ℤ) (A : K → V → ℤ)
    (hspan : RationalRowSpan C A) (x y : V → ℤ)
    (hxy : signature A x = signature A y) : signature C x = signature C y := by
  have hz : ∀ k, signature A (x-y) k = 0 := by
    intro k
    rw [signature_sub, congrFun hxy k, sub_self]
  have hc := integer_kernel_of_rational_span C A hspan (x-y) hz
  funext j
  exact sub_eq_zero.mp (by simpa only [signature_sub] using hc j)

omit [Fintype J] in
theorem card_range_boolSignature_le_selected (C : J → V → ℤ) (select : K → J)
    (hspan : RationalRowSpan C (fun k => C (select k))) :
    Nat.card (Set.range (boolSignature C)) ≤
      Nat.card (Set.range (boolSignature (fun k => C (select k)))) := by
  classical
  let project : Set.range (boolSignature C) →
      Set.range (boolSignature (fun k => C (select k))) := fun y =>
    ⟨fun k => y.val (select k), by
      obtain ⟨x,hx⟩ := y.property
      refine ⟨x, ?_⟩
      funext k
      exact congrFun hx (select k)⟩
  apply Nat.card_le_card_of_injective project
  intro y z h
  apply Subtype.ext
  obtain ⟨x,hx⟩ := y.property
  obtain ⟨w,hw⟩ := z.property
  rw [← hx, ← hw]
  apply signature_eq_of_rationalRowSpan C (fun k => C (select k)) hspan
  funext k
  have hk := congrFun (congrArg Subtype.val h) k
  change y.val (select k) = z.val (select k) at hk
  rw [← hx, ← hw] at hk
  change signature C (fun v => if x v then 1 else 0) (select k) =
    signature C (fun v => if w v then 1 else 0) (select k)
  unfold boolSignature at hk
  exact hk

/-- Rank-sensitive bound for the FULL attained raw-signature set.  The
existential basis contributes no runtime selection or minor enumeration. -/
theorem card_range_boolSignature_le_rank (C : J → V → ℤ) (W : ℕ)
    (hC : ∀ j v, |C j v| ≤ (W : ℤ)) :
    Nat.card (Set.range (boolSignature C)) ≤
      (2 * Fintype.card V * W + 1) ^ LayoutRank.rowRank C := by
  obtain ⟨K, hK, select, hinj, hspan, hcard⟩ := exists_actual_row_basis C
  let _ : Fintype K := hK
  have h1 := card_range_boolSignature_le_selected C select hspan
  have h2 := card_range_boolSignature_le (fun k => C (select k)) W
    (fun k v => hC (select k) v)
  apply h1.trans
  rw [hcard] at h2
  exact h2

end SubexponentialSAT.SqrtLog.LayoutSignatureBound

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatures
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# First occurrences of attained keys

The subtype below is a specification of emissions, not a stored family.
The executable scan checks a candidate against its predecessors one at a time.
The key may be an entire integer row-signature; no coordinate projection occurs.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures

variable {N : ℕ} {κ : Type*} (key : Fin N → κ)

theorem card_representative : Nat.card (Representative key) = Nat.card (Set.range key) :=
  Nat.card_congr (representativeEquiv key)

theorem card_integer_representative {d h : ℕ} (A : Fin d → Fin h → ℤ) :
    Nat.card (Representative (integerKey A)) =
      Nat.card (Set.range (OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.boolSignature A)) := by
  rw [card_representative]
  have hr : Set.range (integerKey A) =
      Set.range (OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.boolSignature A) :=
    (assignmentEquiv h).surjective.range_comp _
  rw [hr]

theorem card_integer_representative_le_rank_oai {d h : ℕ} (A : Fin d → Fin h → ℤ)
    (W : ℕ) (hA : ∀ j i, |A j i| ≤ (W : ℤ)) :
    Nat.card (Representative (integerKey A)) ≤
      (2 * h * W + 1) ^ OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.rowRank A := by
  rw [card_integer_representative]
  simpa using OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.card_range_boolSignature_le_rank A W hA

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.card_integer_representative_le_rank_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.card_integer_representative_le_rank_oai
