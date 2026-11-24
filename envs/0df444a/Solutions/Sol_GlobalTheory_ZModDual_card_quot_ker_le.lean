-- Prove2me | solution 1 for GlobalTheory.ZModDual.card_quot_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:38:58.77167+00:00
-- url     : https://prove2.me/submissions/6431231a-0e1a-408c-9a85-ad27f47a4953

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardDualZmodModuleEqCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardKerMulCardEq
import Theorems.Thm_GlobalTheory_ZModDual_card_dual_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ZModDual
namespace GlobalTheory.ZModDual
theorem _root_.solution (n : ℕ) [NeZero n] (A B : Type) [AddCommGroup A] [Module (ZMod n) A]
    [AddCommGroup B] [Module (ZMod n) B] [Finite B]
    (b : A →ₗ[ZMod n] B →ₗ[ZMod n] ZMod n) :
    Nat.card (A ⧸ LinearMap.ker b) ≤ Nat.card (B ⧸ LinearMap.ker b.flip) := by
  set K' := LinearMap.ker b.flip
  have : Finite (B ⧸ K') := Finite.of_surjective K'.mkQ K'.mkQ_surjective
  have : Finite (Module.Dual (ZMod n) B) :=
    Finite.of_injective (fun f : Module.Dual (ZMod n) B => (f : B → ZMod n)) DFunLike.coe_injective
  have hle : LinearMap.range b ≤ K'.dualAnnihilator := by
    rintro _ ⟨a, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    have := LinearMap.congr_fun (LinearMap.mem_ker.1 hy) a
    simpa using this
  calc Nat.card (A ⧸ LinearMap.ker b) = Nat.card (LinearMap.range b) :=
        Nat.card_congr (LinearMap.quotKerEquivRange b).toEquiv
    _ ≤ Nat.card K'.dualAnnihilator :=
        Nat.card_le_card_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ = Nat.card (Module.Dual (ZMod n) (B ⧸ K')) :=
        Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator K').toEquiv.symm
    _ = Nat.card (B ⧸ K') := card_dual_eq n (B ⧸ K')
end GlobalTheory.ZModDual
