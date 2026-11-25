-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.isWtOn_iff_of_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:28.066803+00:00
-- url     : https://prove2.me/submissions/8978d986-758b-43cb-97be-cdd9fb278349

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
import Theorems.Thm_GlobalTheory_KTypeCompare_torus_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.KTypeCompare
theorem _root_.solution (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (hG : ∀ θ, HarishChandraRootData.torus θ ∈ G)
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (ω : Fin n → ℝ) (v : H) :
    PI.UpqRep.IsWtOn G σ ω v ↔ v ∈ HarishChandraRootData.weightSpace σ ω := by
  change _ ↔ ∀ θ : Fin n → ℝ, σ (HarishChandraRootData.torus θ) v = HarishChandraRootData.wtChar ω θ • v
  unfold PI.UpqRep.IsWtOn HarishChandraRootData.wtChar
  simp only [torus_eq]
  constructor
  · intro h θ
    rw [h θ (hG θ), mul_comm Complex.I]
  · intro h θ _
    rw [h θ, mul_comm Complex.I]
end GlobalTheory.KTypeCompare
