-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadricCount.count_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:02.201936+00:00
-- url     : https://prove2.me/submissions/e9712b0f-3540-4843-8567-801a3e403f42

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricCount
open ComplexConjugate
variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.QuadricCount
theorem _root_.solution (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (B : Matrix ι ι k) (s : k) :
    (Nat.card {x : ι → k // quadForm B x = s} : ℂ) * (Fintype.card k : ℂ) =
      ∑ t : k, ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) := by
  classical
  have hprim := AddChar.IsPrimitive.of_ne_one hψ
  have h1 : ∀ x : ι → k, ∑ t : k, ψ (t * (quadForm B x - s)) =
      if quadForm B x = s then (Fintype.card k : ℂ) else 0 := by
    intro x
    rw [AddChar.sum_mulShift _ hprim]
    simp [sub_eq_zero]
  have h2 : ∑ t : k, ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) =
      ∑ x : ι → k, ∑ t : k, ψ (t * (quadForm B x - s)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [h2]
  simp_rw [h1]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const_zero, add_zero, nsmul_eq_mul]
end GlobalTheory.CompanionTheory.SW.QuadricCount
