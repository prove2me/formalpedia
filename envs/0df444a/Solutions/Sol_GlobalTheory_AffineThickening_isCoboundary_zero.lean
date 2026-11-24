-- Prove2me | solution 1 for GlobalTheory.AffineThickening.isCoboundary_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:20:42.123248+00:00
-- url     : https://prove2.me/submissions/bd8f2817-c5aa-43fd-93ab-66b4499a5f16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}
variable [IsClosedImmersion i] [Surjective i]
  (hK : ∀ U : Y.Opens, IsAffineOpen U → ∀ a b : Γ(Y, U), Lifts i U a 0 → Lifts i U b 0 → a * b = 0)
  {ι : Type*} {f : ι → Γ(Z, ⊤)} {U : ι → Y.Opens} (hU : ∀ j, IsAffineOpen (U j))
  (hD : ∀ j, i ⁻¹ᵁ U j = Z.basicOpen (f j))
  {s : Γ(Z, ⊤)} {σ : ∀ j, Γ(Y, U j)} (hσ : ∀ j, Lifts i (U j) (σ j) s)
omit [IsClosedImmersion i] [Surjective i]
namespace GlobalTheory.AffineThickening
theorem _root_.solution : IsCoboundary i σ 0 :=
  ⟨0, 0, fun _ ↦ Lifts.zero, fun _ ↦ Lifts.zero, fun j k ↦ by simp⟩
end GlobalTheory.AffineThickening
