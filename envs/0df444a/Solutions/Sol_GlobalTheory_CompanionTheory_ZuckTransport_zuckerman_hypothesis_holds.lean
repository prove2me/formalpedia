-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckTransport.zuckerman_hypothesis_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:02:05.17392+00:00
-- url     : https://prove2.me/submissions/18748049-a628-41c9-b15b-9b8e2fd6168a

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_BetaAtInfinityZero
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZuckermanHypothesis
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckTransport_transport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckTransport
open PI.UpqRep CompanionTheory.LimBd.SchurHpk
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
namespace GlobalTheory.CompanionTheory.ZuckTransport
theorem _root_.solution : ZuckH := by
  intro t hZ k r ε μ U b h hU hg hlt
  obtain ⟨hμ, P, hP, hτ⟩ := hU
  obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩ := hZ _ ε μ U.R.H _ hμ hτ h hg hlt
  cases b
  · exact transport U hP (fun g => g) (fun _ => rfl) (shift false μ) X.Sm X.Hs X.σs hX X.ds X.toSum X.ofSum
  · have hi : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (P * g * P⁻¹)⁻¹ = P * g⁻¹ * P⁻¹ :=
      fun g => by
        rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
          Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1.1), Matrix.mul_assoc]
    obtain ⟨T, h1, h2, h3⟩ :=
      transport U hP (fun g => g⁻¹) hi (shift true μ) Y.Sm Y.Hs Y.σs hY Y.ds Y.toSum Y.ofSum
    refine ⟨T, h1, fun v w hv hw c d => h2 v w hv hw d c, fun s => ?_⟩
    obtain ⟨y, hy, I, _, v, w, c, d, hk, he⟩ := h3 s
    exact ⟨y, hy, I, inferInstance, v, w, d, c, hk, he⟩
end GlobalTheory.CompanionTheory.ZuckTransport
