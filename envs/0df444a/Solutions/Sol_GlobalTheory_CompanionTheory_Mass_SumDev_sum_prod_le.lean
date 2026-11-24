-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.SumDev.sum_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:52:15.790816+00:00
-- url     : https://prove2.me/submissions/040a8901-a3f8-4100-8ead-67df59d6277d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EulerProductConvergenceBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.SumDev
namespace GlobalTheory.CompanionTheory.Mass.SumDev
theorem _root_.solution {ι X : Type*} (D : Finset ι) (B : Finset X) (e : ι → X → ℝ) (P : ι → X → Prop)
    (a b c : ι → ℝ) (w C' : ℝ) (hw : 0 ≤ w)
    (ha : ∀ v ∈ D, 0 ≤ a v) (hb : ∀ v ∈ D, 0 ≤ b v) (hbc : ∀ v ∈ D, b v * c v = a v)
    (he0 : ∀ v ∈ D, ∀ x ∈ B, 0 ≤ e v x)
    (he : ∀ v ∈ D, ∀ x ∈ B, e v x ≤ a v + if P v x then b v else 0)
    (hcount : ∀ t ⊆ D, w * ((B.filter fun x => ∀ v ∈ t, P v x).card : ℝ) ≤ C' * ∏ v ∈ t, c v) :
    w * ∑ x ∈ B, ∏ v ∈ D, e v x ≤ C' * ∏ v ∈ D, (2 * a v) := by
  have hx : ∀ x ∈ B, ∏ v ∈ D, e v x ≤
      ∑ t ∈ D.powerset, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v := by
    intro x hxB
    calc ∏ v ∈ D, e v x ≤ ∏ v ∈ D, ((if P v x then b v else 0) + a v) := by
          refine Finset.prod_le_prod (fun v hv => he0 v hv x hxB) (fun v hv => ?_)
          rw [add_comm]
          exact he v hv x hxB
      _ = ∑ t ∈ D.powerset, (∏ v ∈ t, (if P v x then b v else 0)) * ∏ v ∈ D \ t, a v :=
          Finset.prod_add _ _ _
      _ = _ := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.prod_ite_zero]
  have ht : ∀ t ∈ D.powerset,
      w * ∑ x ∈ B, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v ≤ C' * ∏ v ∈ D, a v := by
    intro t htD
    rw [Finset.mem_powerset] at htD
    have hA : 0 ≤ ∏ v ∈ D \ t, a v := Finset.prod_nonneg fun v hv => ha v (Finset.sdiff_subset hv)
    have hB : 0 ≤ ∏ v ∈ t, b v := Finset.prod_nonneg fun v hv => hb v (htD hv)
    have hsum : ∑ x ∈ B, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v
        = ((B.filter fun x => ∀ v ∈ t, P v x).card : ℝ) * ((∏ v ∈ t, b v) * ∏ v ∈ D \ t, a v) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp
    have hprod : (∏ v ∈ t, b v) * ∏ v ∈ t, c v = ∏ v ∈ t, a v := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v hv => hbc v (htD hv)
    rw [hsum]
    calc w * (((B.filter fun x => ∀ v ∈ t, P v x).card : ℝ) * ((∏ v ∈ t, b v) * ∏ v ∈ D \ t, a v))
        = (w * ((B.filter fun x => ∀ v ∈ t, P v x).card : ℝ)) * ((∏ v ∈ t, b v) * ∏ v ∈ D \ t, a v) := by
          ring
      _ ≤ (C' * ∏ v ∈ t, c v) * ((∏ v ∈ t, b v) * ∏ v ∈ D \ t, a v) :=
          mul_le_mul_of_nonneg_right (hcount t htD) (mul_nonneg hB hA)
      _ = C' * ((∏ v ∈ D \ t, a v) * ((∏ v ∈ t, b v) * ∏ v ∈ t, c v)) := by ring
      _ = C' * ∏ v ∈ D, a v := by rw [hprod, Finset.prod_sdiff htD]
  calc w * ∑ x ∈ B, ∏ v ∈ D, e v x
      ≤ w * ∑ x ∈ B, ∑ t ∈ D.powerset, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hx) hw
    _ = ∑ t ∈ D.powerset, w * ∑ x ∈ B, (if ∀ v ∈ t, P v x then ∏ v ∈ t, b v else 0) * ∏ v ∈ D \ t, a v := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ t ∈ D.powerset, C' * ∏ v ∈ D, a v := Finset.sum_le_sum ht
    _ = C' * ∏ v ∈ D, (2 * a v) := by
        rw [Finset.sum_const, Finset.card_powerset, Finset.prod_mul_distrib, Finset.prod_const, nsmul_eq_mul]
        push_cast
        ring
end GlobalTheory.CompanionTheory.Mass.SumDev
