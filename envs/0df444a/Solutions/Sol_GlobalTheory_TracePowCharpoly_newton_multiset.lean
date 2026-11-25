-- Prove2me | solution 1 for GlobalTheory.TracePowCharpoly.newton_multiset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:52:58.351969+00:00
-- url     : https://prove2.me/submissions/7744b590-3a7c-4a93-a86b-f377abe6427f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEqOfTracePowers
import Theorems.Thm_GlobalTheory_TracePowCharpoly_newton_fn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.TracePowCharpoly
open Polynomial Finset
namespace GlobalTheory.TracePowCharpoly
theorem _root_.solution (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  have hs : s = (univ : Finset (Fin s.toList.length)).val.map (fun i => s.toList.get i) := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h := newton_fn (fun i : Fin s.toList.length => s.toList.get i) k
  rw [← hs] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have e : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ i : Fin s.toList.length, s.toList.get i ^ n := by
    intro n
    conv_lhs => rw [hs]
    rw [Multiset.map_map]
    rfl
  exact (e a.2).symm
end GlobalTheory.TracePowCharpoly
