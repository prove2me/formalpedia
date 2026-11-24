-- Prove2me | solution 1 for GlobalTheory.CharacterSumInverse.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:26:28.78938+00:00
-- url     : https://prove2.me/submissions/5ca7f97b-33a4-431b-bcae-cce387c1aa54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CharSumInv
import Theorems.Thm_GlobalTheory_CharacterSumInverse_charSum_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CharacterSumInverse
open scoped BigOperators
namespace GlobalTheory.CharacterSumInverse
theorem _root_.solution : (let d1 : {o : Type} → [inst : CommRing o] → {T : Type} → [inst_1 : CommGroup T] → {M : Type} → [inst_2 : AddCommGroup M] → [inst_3 : Module o M] → [Fintype T] → Representation o T M → o → (T →* oˣ) → M →ₗ[o] M := @(fun {o : Type} [CommRing o] {T : Type} [CommGroup T] {M : Type} [AddCommGroup M] [Module o M] [Fintype T] (ρ : Representation o T M) (u : o) (c : T →* oˣ) ↦ u • ∑ t : T, (↑((c : T → oˣ) t)⁻¹ : o) • (ρ : T → M →ₗ[o] M) t); ∀ {o : Type} [inst : CommRing o] {T : Type} [inst_1 : CommGroup T] {M : Type} [inst_2 : AddCommGroup M] [inst_3 : Module o M] [inst_4 : Fintype T] (ρ : Representation o T M) (u : o) [IsDomain o] [HasEnoughRootsOfUnity o (Monoid.exponent T)] [inst_7 : Fintype (T →* oˣ)], u * (↑(Fintype.card T) : o) = (1 : o) → ∀ (x : M), ∑ c : T →* oˣ, (d1 ρ u c : M → M) x = x) := by
  intro d1 o _ T _ M _ _ _ ρ u _ _ _ hu x
  classical
  simp only [d1, LinearMap.smul_apply, LinearMap.sum_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, charSum_inv]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_one,
    Module.End.one_apply]
  rw [smul_smul, hu, one_smul]
end GlobalTheory.CharacterSumInverse
