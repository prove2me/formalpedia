-- Prove2me | solution 1 for GlobalTheory.IsoLift.exists_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:56:07.163868+00:00
-- url     : https://prove2.me/submissions/79609269-09fd-436a-ac2b-b26d6aa9b184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LevelActionTransitions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModNOfDvdModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsometryLift
import Theorems.Thm_GlobalTheory_IsoLift_step_one
import Theorems.Thm_GlobalTheory_SimLift_modN_of_dvd_modulus
import Theorems.Thm_GlobalTheory_SimLift_modN_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.IsoLift
open GlobalTheory.SimLift GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
namespace GlobalTheory.IsoLift
theorem _root_.solution {N : ℕ} (hN : 0 < N) {f : D.La →ₗ[𝓞 E] D.La} (hf : IsSimMod D N f 1) :
    ∃ s : ℕ → (D.La →ₗ[𝓞 E] D.La), s 0 = f ∧ (∀ k, IsSimMod D (N * k.factorial) (s k) 1) ∧
      ∀ k j, k ≤ j → ∀ a, D.ModN (N * k.factorial) (s j a - s k a) := by
  let T : ℕ → Type := fun k =>
    {x : (D.La →ₗ[𝓞 E] D.La) // IsSimMod D (N * k.factorial) x 1}
  have hstep : ∀ k (x : T k), ∃ y : T (k + 1),
      (∀ a, D.ModN (N * k.factorial) (y.1 a - x.1 a)) := by
    intro k x
    obtain ⟨f', h1, h2⟩ := step_one D (k + 1) k.succ_pos _ (Nat.mul_pos hN k.factorial_pos) _ x.2
    refine ⟨⟨f', ?_⟩, h2⟩
    rwa [Nat.factorial_succ, Nat.mul_comm (k + 1), ← Nat.mul_assoc]
  choose nx hnx using hstep
  let s : ∀ k, T k := fun k => Nat.rec (⟨f, by
    rw [Nat.factorial_zero, Nat.mul_one]; exact hf⟩ : T 0) nx k
  refine ⟨fun k => (s k).1, rfl, fun k => (s k).2, fun k j hkj => ?_⟩
  induction j, hkj using Nat.le_induction with
  | base => exact fun a => ⟨0, by simp⟩
  | succ j hkj ih =>
    have hd : N * k.factorial ∣ N * j.factorial :=
      Nat.mul_dvd_mul_left N (Nat.factorial_dvd_factorial hkj)
    exact fun a => modN_trans D (modN_of_dvd_modulus D hd (hnx j (s j) a)) (ih a)
end GlobalTheory.IsoLift
