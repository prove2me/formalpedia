-- Prove2me | solution 1 for GlobalTheory.WpFam.CoeffConj.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:36:37.101112+00:00
-- url     : https://prove2.me/submissions/765aca23-7ba0-4b3f-9cc3-a99f74918aad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModularGroupRowVecAndConjRightActions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexAutomorphismWeierstrassTorsionQCoeffs
import Theorems.Thm_GlobalTheory_WpFam_Act_rightActions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
namespace GlobalTheory.WpFam.CoeffConj
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private theorem vmul_dg_apply_zero_and_one {N : ℕ} (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ) :
    _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) 0 = x 0 ∧
      _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) 1 = (a : ZMod N) * x 1 := by
  simp [_root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private theorem ringEquiv_cG_eq (N : ℕ) (g : ℂ ≃+* ℂ) (k : ℕ) :
    g (_root_.GlobalTheory.WpFam.cG N k) = _root_.GlobalTheory.WpFam.cG N k := by
  unfold _root_.GlobalTheory.WpFam.cG
  split_ifs <;> simp [map_ofNat]
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private theorem ringEquiv_cSum_eq_cSum_vmul_dg (N : ℕ) (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ)
    (hg : _root_.GlobalTheory.WpFam.ZetaAct g N a) (e : ℕ) (s : ℂ) (hs : g s = s) (x : Fin 2 → ZMod N)
    (k : ℕ) :
    g (_root_.GlobalTheory.WpFam.cSum N e s x k) =
      _root_.GlobalTheory.WpFam.cSum N e s (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
  obtain ⟨h0, h1⟩ := vmul_dg_apply_zero_and_one x a
  unfold _root_.GlobalTheory.WpFam.ZetaAct at hg
  unfold _root_.GlobalTheory.WpFam.cSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [h0, h1]
  simp only [map_mul, map_pow, map_natCast, map_add, apply_ite g, map_zero, hs, hg]
  rw [mul_neg, mul_left_comm (a : ZMod N)]
end GlobalTheory.WpFam.CoeffConj
end

set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.CoeffConj
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
namespace GlobalTheory.WpFam.CoeffConj
namespace _root_.GlobalTheory.WpFam.CoeffConj
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.ZetaAct g N a → ∀ (x : Fin 2 → ZMod N) (k : ℕ), g (_root_.GlobalTheory.WpFam.cB N x k) = _root_.GlobalTheory.WpFam.cB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k ∧ g (_root_.GlobalTheory.WpFam.cD N x k) = _root_.GlobalTheory.WpFam.cD N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k ∧ g (_root_.GlobalTheory.WpFam.cG N k) = _root_.GlobalTheory.WpFam.cG N k ∧ g (_root_.GlobalTheory.WpFam.cP N x k) = _root_.GlobalTheory.WpFam.cP N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
  intro N _ g a hg x k
  obtain ⟨h0, h1⟩ := vmul_dg_apply_zero_and_one x a
  have hζ := hg
  unfold _root_.GlobalTheory.WpFam.ZetaAct at hζ
  have hG := ringEquiv_cG_eq N g k
  have hB : g (_root_.GlobalTheory.WpFam.cB N x k) =
      _root_.GlobalTheory.WpFam.cB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
    unfold _root_.GlobalTheory.WpFam.cB
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [if_true, h0, h1]
      split_ifs
      · simp only [map_div₀, map_pow, map_sub, map_one, hζ]
      · exact map_zero g
    · simp only [hk, if_false]
      exact ringEquiv_cSum_eq_cSum_vmul_dg N g a hg 1 1 (map_one g) x k
  have hD : g (_root_.GlobalTheory.WpFam.cD N x k) =
      _root_.GlobalTheory.WpFam.cD N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
    unfold _root_.GlobalTheory.WpFam.cD
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [if_true, h0, h1]
      split_ifs
      · simp only [map_div₀, map_pow, map_sub, map_add, map_mul, map_one, hζ]
      · exact map_zero g
    · simp only [hk, if_false]
      exact ringEquiv_cSum_eq_cSum_vmul_dg N g a hg 2 (-1) (by simp) x k
  refine ⟨hB, hD, hG, ?_⟩
  have hzero := (_root_.GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x (_root_.GlobalTheory.WpFam.dg a)
  unfold _root_.GlobalTheory.WpFam.cP
  by_cases hx : x = 0
  · rw [if_pos hx, if_pos (hzero.2 hx), map_zero]
  · have hx' : _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) ≠ 0 := fun h => hx (hzero.1 h)
    simp only [hx, hx', if_false, map_sub, hB, hG]
end _root_.GlobalTheory.WpFam.CoeffConj
end GlobalTheory.WpFam.CoeffConj
