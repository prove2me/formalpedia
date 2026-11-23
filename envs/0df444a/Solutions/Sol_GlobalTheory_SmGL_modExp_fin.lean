-- Prove2me | solution 1 for GlobalTheory.SmGL.modExp_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:21.633713+00:00
-- url     : https://prove2.me/submissions/32da6ea3-b6b2-430b-84e7-d4c86f750ada

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL
theorem _root_.solution {N : ℕ} (X : Fin N → Type) [∀ i, Fintype (X i)] (hX : ∀ i, Fintype.card (X i) = 1)
    (i : Fin N) : modExp X i = (N : ℤ) - 1 - 2 * (i : ℕ) := by
  have h1 : Finset.univ.filter (fun b => i < b) = Finset.Ioi i := by ext; simp
  have h2 : Finset.univ.filter (fun b => b < i) = Finset.Iio i := by ext; simp
  have := i.2
  simp only [modExp, hX, h1, h2, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, Nat.cast_one,
    nsmul_eq_mul, mul_one]
  omega
end GlobalTheory.SmGL
