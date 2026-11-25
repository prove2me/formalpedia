-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckTransport.kfin_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:16:20.943752+00:00
-- url     : https://prove2.me/submissions/712b3dca-6f2e-437f-81fe-ac7ff53095a2

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_BetaAtInfinityZero
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZuckermanHypothesis

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
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {v : H} (c : ℂ)
    (hv : IsKFinHpk (k := k) (r := r) σ v) : IsKFinHpk (k := k) (r := r) σ (c • v) := by
  obtain ⟨S, h1, h2, h3⟩ := hv
  exact ⟨S, h1, S.smul_mem c h2, h3⟩
end GlobalTheory.CompanionTheory.ZuckTransport
