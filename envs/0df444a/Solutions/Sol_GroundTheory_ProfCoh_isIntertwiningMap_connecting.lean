-- Prove2me | solution 1 for GroundTheory.ProfCoh.isIntertwiningMap_connecting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:24:40.593465+00:00
-- url     : https://prove2.me/submissions/16c57f3f-e6d7-4628-acb4-bc327994df83

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Theorems.Thm_GroundTheory_ProfCoh_connecting_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
variable {Γ : Type*} [Group Γ] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C] (n : ℕ)
namespace GroundTheory.ProfCoh
theorem _root_.solution {n : ℕ} {f : A →+ B} {h : B →+ C}
    (hh : Function.Surjective h) (hfh : Function.Exact f h) (hf : Function.Injective f)
    (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a) (hhγ : ∀ (γ : Γ) (b : B), h (γ • b) = γ • h b) :
    (torsNRep Γ C n).IsIntertwiningMap (modNRep Γ A n) (connecting hh hfh hf) :=
  ⟨fun γ c => by
    obtain ⟨b, a, hb, ha⟩ := exists_lift hh hfh c
    rw [connecting_spec hh hfh hf c b a hb ha,
      connecting_spec hh hfh hf _ (γ • b) (γ • a) (by rw [hhγ, hb]; rfl)
        (by rw [hfγ, ha, smul_comm])]
    rfl⟩
end GroundTheory.ProfCoh
