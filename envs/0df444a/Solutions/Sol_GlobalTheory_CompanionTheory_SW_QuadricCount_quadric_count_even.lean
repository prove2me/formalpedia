-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadricCount.quadric_count_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:44:57.449794+00:00
-- url     : https://prove2.me/submissions/be58f37d-83a0-42d3-bc72-cda539ebbb5a

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricCount_card_quadric_even

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
theorem _root_.solution : ∀ (k : Type) [Field k] [Fintype k], ringChar k ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 1 ≤ M → ∀ (B : Matrix ι ι k), B.IsSymm → B.det ≠ 0 → ∀ s : k, |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M :=
  fun k _ _ h ι _ _ M hM hM1 B hB hd s => card_quadric_even k h ι M hM hM1 B hB hd s
end GlobalTheory.CompanionTheory.SW.QuadricCount
