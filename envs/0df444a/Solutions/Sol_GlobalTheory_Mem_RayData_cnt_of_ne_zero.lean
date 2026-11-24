-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.cnt_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:10.003308+00:00
-- url     : https://prove2.me/submissions/d12fd69e-4fe6-4bc5-96a7-cfa33cc1765f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem
open NumberField IsDedekindDomain
attribute [instance] RayData.grp RayData.fin
open GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
namespace GlobalTheory.Mem.RayData
theorem _root_.solution (c : D.G) {n : ℕ} (hn : n ≠ 0) : D.cnt c n =
    (Nat.card {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ I ≠ ⊥ ∧ Ideal.absNorm I = n ∧ D.cls I = c} : ℕ) := by
  rw [cnt]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun I =>
    ⟨fun h => ⟨h.1, fun h0 => hn (by rw [← h.2.1, h0, Ideal.absNorm_bot]), h.2.1, h.2.2⟩,
      fun h => ⟨h.1, h.2.2.1, h.2.2.2⟩⟩)
end GlobalTheory.Mem.RayData
