-- Prove2me | solution 1 for GlobalTheory.BSP.IsDiscMap.unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:00.832045+00:00
-- url     : https://prove2.me/submissions/155870fc-1994-41e6-b2f0-26fa38ffbbce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemBallOfGaugeLt
import Theorems.Thm_GlobalTheory_BSP_denseRange_ofPre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open GlobalTheory GlobalTheory.BSP
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0}
open scoped NNReal
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0}
namespace GlobalTheory.BSP
namespace _root_.GlobalTheory.BSP.IsDiscMap
theorem _root_.solution {f : A →+* A'}
    {F G : _root_.GlobalTheory.BSP.Disc l u ρ →+* _root_.GlobalTheory.BSP.Disc l u' ρ'}
    (hF : _root_.GlobalTheory.BSP.IsDiscMap f F)
    (hG : _root_.GlobalTheory.BSP.IsDiscMap f G) : F = G := by
  have hFc : Continuous F := AddMonoidHomClass.continuous_of_bound F 1 fun x => by
    simpa using hF.norm_le x
  have hGc : Continuous G := AddMonoidHomClass.continuous_of_bound G 1 fun x => by
    simpa using hG.norm_le x
  have hinv : ∀ H : _root_.GlobalTheory.BSP.Disc l u ρ →+* _root_.GlobalTheory.BSP.Disc l u' ρ',
      _root_.GlobalTheory.BSP.IsDiscMap f H →
      H (_root_.GlobalTheory.BSP.ofPre l u ρ (IsLocalization.Away.invSelf (l : A))) *
        _root_.GlobalTheory.BSP.toDisc l u' ρ' (l : A') = 1 := by
    intro H hH
    rw [← map_natCast f, ← hH.ext, ← map_mul]
    change H (_root_.GlobalTheory.BSP.ofPre l u ρ _ *
      _root_.GlobalTheory.BSP.ofPre l u ρ (algebraMap A _ (l : A))) = 1
    rw [← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one, map_one]
  have hinvEq : F (_root_.GlobalTheory.BSP.ofPre l u ρ (IsLocalization.Away.invSelf (l : A))) =
      G (_root_.GlobalTheory.BSP.ofPre l u ρ (IsLocalization.Away.invSelf (l : A))) := by
    calc _ = F (_root_.GlobalTheory.BSP.ofPre l u ρ (IsLocalization.Away.invSelf (l : A))) *
          (_root_.GlobalTheory.BSP.toDisc l u' ρ' (l : A') *
            G (_root_.GlobalTheory.BSP.ofPre l u ρ (IsLocalization.Away.invSelf (l : A)))) := by
          rw [mul_comm (_root_.GlobalTheory.BSP.toDisc l u' ρ' (l : A')), hinv G hG, mul_one]
      _ = (F (_root_.GlobalTheory.BSP.ofPre l u ρ (IsLocalization.Away.invSelf (l : A))) *
          _root_.GlobalTheory.BSP.toDisc l u' ρ' (l : A')) *
            G (_root_.GlobalTheory.BSP.ofPre l u ρ (IsLocalization.Away.invSelf (l : A))) := by
          rw [mul_assoc]
      _ = _ := by rw [hinv F hF, one_mul]
  have hpre : ∀ y, F (_root_.GlobalTheory.BSP.ofPre l u ρ y) =
      G (_root_.GlobalTheory.BSP.ofPre l u ρ y) := by
    intro y
    obtain ⟨a, n, rfl⟩ := preDisc_exists_eq_algebraMap_mul_invSelf_pow l u ρ y
    rw [map_mul, map_pow, map_mul, map_mul, map_pow, map_pow, hinvEq]
    congr 1
    exact (hF.ext a).trans (hG.ext a).symm
  exact RingHom.ext (congrFun ((_root_.GlobalTheory.BSP.denseRange_ofPre l u ρ).equalizer hFc hGc
    (funext hpre)))
end _root_.GlobalTheory.BSP.IsDiscMap
end GlobalTheory.BSP
