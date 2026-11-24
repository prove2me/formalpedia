-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.FFStar_FF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:15.736498+00:00
-- url     : https://prove2.me/submissions/19065c34-b3d0-4a0b-a9a1-e023276c5f18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_LatPair_Model_sum_char
import Theorems.Thm_GlobalTheory_LatPair_FFStar_ofDual
import Theorems.Thm_GlobalTheory_LatPair_FF_up
import Theorems.Thm_GlobalTheory_LatPair_Pair_ofDual_red
import Theorems.Thm_GlobalTheory_LatPair_Red_card_eq
import Theorems.Thm_GlobalTheory_LatPair_sum_withLat
import Theorems.Thm_GlobalTheory_LatPair_tr_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.LatPair.Model
theorem _root_.solution [Fintype n] (q : Unif k) {χ : AddChar 𝓀[k] ℂ} (hχ : χ ≠ 1) (φ : Form k n M) :
    FFStar q χ (FF q χ φ) = (SplitWeil.resCard k ^ Fintype.card n : ℂ) • φ - tr φ := by
  classical
  ext P
  obtain ⟨L, hL, f, rfl⟩ : ∃ (L : Submodule 𝒪[k] (n → k)) (_ : L.IsLattice k) (f : _), P = ofDual L f :=
    ⟨P.lat, P.isLat, _, P.ofDual_red.symm⟩
  letI := Fintype.ofFinite (Red L)
  letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))
  have hc : (Fintype.card (Red L) : ℂ) = SplitWeil.resCard k ^ Fintype.card n := by
    rw [← Nat.card_eq_fintype_card, Red.card_eq]; push_cast; rfl
  simp only [FFStar_ofDual, FF_up, Finset.smul_sum, smul_smul, Pi.sub_apply, Pi.smul_apply, tr_apply, ofDual_lat,
    sum_withLat]
  rw [Finset.sum_comm]
  have key : ∀ g : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0},
      ∑ x : {x : Red L // x ≠ 0}, χ (-f.1 x.1) * χ (g.1 x.1) =
        (if g = f then (Fintype.card (Red L) : ℂ) else 0) - 1 := fun g => by
    have h1 := sum_char hχ (g.1 - f.1)
    rw [Fintype.sum_eq_add_sum_subtype_ne _ 0] at h1
    simp only [map_zero, AddChar.map_zero_eq_one, sub_eq_zero, Subtype.val_inj] at h1
    rw [← h1, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← AddChar.map_add_eq_mul, LinearMap.sub_apply, neg_add_eq_sub]
  simp only [← Finset.sum_smul, key, sub_smul, one_smul, Finset.sum_sub_distrib, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hc]
end GlobalTheory.LatPair.Model
