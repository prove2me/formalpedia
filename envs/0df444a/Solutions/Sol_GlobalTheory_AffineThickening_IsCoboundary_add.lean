-- Prove2me | solution 1 for GlobalTheory.AffineThickening.IsCoboundary.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:19:03.799424+00:00
-- url     : https://prove2.me/submissions/4d4ff7c5-b262-4c9b-9861-4bb3d07520f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_add

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
namespace IsCoboundary
theorem _root_.solution {r r' : Γ(Z, ⊤)} (h : IsCoboundary i σ r) (h' : IsCoboundary i σ r') :
    IsCoboundary i σ (r + r') := by
  obtain ⟨ρ, t, hρ, ht, e⟩ := h
  obtain ⟨ρ', t', hρ', ht', e'⟩ := h'
  refine ⟨fun j ↦ ρ j + ρ' j, fun j ↦ t j + t' j, fun j ↦ (hρ j).add (hρ' j),
    fun j ↦ by simpa using (ht j).add (ht' j), fun j k ↦ ?_⟩
  simp only [map_add]
  linear_combination e j k + e' j k
end IsCoboundary
end GlobalTheory.AffineThickening
