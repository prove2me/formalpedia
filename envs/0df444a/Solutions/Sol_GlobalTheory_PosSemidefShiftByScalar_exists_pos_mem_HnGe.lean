-- Prove2me | solution 1 for GlobalTheory.PosSemidefShiftByScalar.exists_pos_mem_HnGe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:43:46.2776+00:00
-- url     : https://prove2.me/submissions/e31a2edf-ddc7-4fee-800b-aadbe1184752

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubSmulOne
import Theorems.Thm_GlobalTheory_PosSemidefShiftByScalar_posSemidef_sub_smul_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Unitary
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PosSemidefShiftByScalar
namespace GlobalTheory.PosSemidefShiftByScalar
theorem _root_.solution {N : ℕ} {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    {Z : GlobalTheory.SW.CM Ψ N N} (hZ : Z ∈ GlobalTheory.SW.Hn Ψ N) :
    ∃ δ : ℝ, (0 : ℝ) < δ ∧ Z ∈ GlobalTheory.SW.HnGe Ψ N δ := by
  choose d hd h using fun τ : Ψ => posSemidef_sub_smul_one (hZ τ)
  rcases isEmpty_or_nonempty Ψ with hΨ | hΨ
  · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
  · obtain ⟨τ0, -, hτ0⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
    exact ⟨d τ0, hd τ0, fun τ => h τ _ (hτ0 τ (Finset.mem_univ τ))⟩
end GlobalTheory.PosSemidefShiftByScalar
