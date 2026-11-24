-- Prove2me | solution 1 for GlobalTheory.CuspGL.finrank_eq_zero_of_irreducible_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:23:46.904011+00:00
-- url     : https://prove2.me/submissions/689699e8-ccf6-4d1d-acf5-c2df658b8351

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyOfIrreduci
import Theorems.Thm_GlobalTheory_CuspGL_coe_aeval_restrict_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (g : Module.End F V) (hg : Irreducible (LinearMap.charpoly g))
    (W : Submodule F V) (hne : W ≠ ⊤) (hW : ∀ x ∈ W, g x ∈ W) : Module.finrank F W = 0 := by
  by_contra h0
  have hnt : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (Nat.pos_of_ne_zero h0)
  set f : Module.End F W := g.restrict hW with hf
  have hz : aeval f (LinearMap.charpoly g) = 0 := by
    ext x
    rw [hf, coe_aeval_restrict_apply, LinearMap.aeval_self_charpoly]
    simp
  have hd : minpoly F f ∣ LinearMap.charpoly g := minpoly.dvd F f hz
  have hnu : ¬ IsUnit (minpoly F f) := minpoly.not_isUnit F f
  have hd' : LinearMap.charpoly g ∣ minpoly F f := ((hg.dvd_iff.mp hd).resolve_left hnu).dvd
  have hd'' : LinearMap.charpoly g ∣ LinearMap.charpoly f := hd'.trans (LinearMap.minpoly_dvd_charpoly f)
  have hle := natDegree_le_of_dvd hd'' (LinearMap.charpoly_monic f).ne_zero
  rw [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree] at hle
  have := Submodule.finrank_lt hne
  omega
end GlobalTheory.CuspGL
