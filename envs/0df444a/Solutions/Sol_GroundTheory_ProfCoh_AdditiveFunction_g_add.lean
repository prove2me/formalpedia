-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.g_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:39:03.3492+00:00
-- url     : https://prove2.me/submissions/62535ba8-e0f7-43e2-996c-a6e4518e516c

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_alternating_sum_six
import Theorems.Thm_GroundTheory_ProfCoh_torsNMap_injective
import Theorems.Thm_GroundTheory_ProfCoh_exact_torsNMap_torsNMap
import Theorems.Thm_GroundTheory_ProfCoh_exact_torsNMap_connecting
import Theorems.Thm_GroundTheory_ProfCoh_exact_connecting_modNMap
import Theorems.Thm_GroundTheory_ProfCoh_exact_modNMap_modNMap
import Theorems.Thm_GroundTheory_ProfCoh_modNMap_surjective
import Theorems.Thm_GroundTheory_ProfCoh_isIntertwiningMap_torsNMap
import Theorems.Thm_GroundTheory_ProfCoh_isIntertwiningMap_modNMap
import Theorems.Thm_GroundTheory_ProfCoh_isIntertwiningMap_connecting
import Theorems.Thm_GroundTheory_ProfCoh_finite_torsN_of_exact
import Theorems.Thm_GroundTheory_ProfCoh_finite_modN_of_exact
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq


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
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C] (f : A →+ B)
    (h : B →+ C) (hfγ : ∀ (γ : Γ) (a : A), f (γ • a) = γ • f a)
    (hhγ : ∀ (γ : Γ) (b : B), h (γ • b) = γ • h b) (hf : Function.Injective f)
    (hfh : Function.Exact f h) (hh : Function.Surjective h)
    [Finite (ModN A l)] [Finite (TorsN A l)] [Finite (ModN C l)] [Finite (TorsN C l)] :
    d.g B = d.g A + d.g C := by
  have := finite_torsN_of_exact (n := l) hfh hf
  have := finite_modN_of_exact (n := l) hh hfh
  rw [d.g_eq A, d.g_eq B, d.g_eq C]
  have := d.alternating_sum_six (torsNRep Γ A l) (torsNRep Γ B l) (torsNRep Γ C l)
    (modNRep Γ A l) (modNRep Γ B l) (modNRep Γ C l) (torsNMap l f) (torsNMap l h)
    (connecting hh hfh hf) (modNMap l f) (modNMap l h) (isIntertwiningMap_torsNMap l hfγ)
    (isIntertwiningMap_torsNMap l hhγ) (isIntertwiningMap_connecting hh hfh hf hfγ hhγ)
    (isIntertwiningMap_modNMap l hfγ) (isIntertwiningMap_modNMap l hhγ) (torsNMap_injective hf)
    (exact_torsNMap_torsNMap hfh hf) (exact_torsNMap_connecting hh hfh hf)
    (exact_connecting_modNMap hh hfh hf) (exact_modNMap_modNMap hh hfh) (modNMap_surjective hh)
  linarith
end GroundTheory.ProfCoh.AdditiveFunction
