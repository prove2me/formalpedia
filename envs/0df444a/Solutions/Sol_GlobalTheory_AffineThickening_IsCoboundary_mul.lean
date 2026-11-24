-- Prove2me | solution 1 for GlobalTheory.AffineThickening.IsCoboundary.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:07:56.597806+00:00
-- url     : https://prove2.me/submissions/98a079ae-b2ed-4695-9386-b0dfbebbbc07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_res
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_mul
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_sub_zero
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_mul_zero
import Theorems.Thm_GlobalTheory_AffineThickening_exists_lifts
import Theorems.Thm_GlobalTheory_AffineThickening_isAffineOpen_inf

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
include hK hU hD
namespace GlobalTheory.AffineThickening
namespace IsCoboundary
theorem _root_.solution {r : Γ(Z, ⊤)} (r' : Γ(Z, ⊤)) (h : IsCoboundary i σ r) :
    IsCoboundary i σ (r' * r) := by
  obtain ⟨ρ, t, hρ, ht, e⟩ := h
  choose ρ' hρ' using fun j ↦ exists_lifts (i := i) (hU j) r'
  refine ⟨fun j ↦ ρ' j * ρ j, fun j ↦ ρ' j * t j, fun j ↦ (hρ' j).mul (hρ j),
    fun j ↦ Lifts.mul_zero _ (ht j), fun j k ↦ ?_⟩
  have h0 := hK _ (isAffineOpen_inf (hU j) (hD k)) _ _
    (((hρ' j).res inf_le_left).sub_zero ((hρ' k).res inf_le_right)) ((ht k).res inf_le_right)
  simp only [map_mul]
  linear_combination rs inf_le_left (ρ' j) * e j k + h0
end IsCoboundary
end GlobalTheory.AffineThickening
