-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Vf2.exists_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:25:24.687971+00:00
-- url     : https://prove2.me/submissions/feb84686-491c-431c-84cd-54ae6cdafeea

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_SkewTwo
import Theorems.Thm_GlobalTheory_ThK_Dbl_Vf2_lag_of
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_mapc_smul
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_mapc_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Vf2
open Matrix GlobalTheory.WeilM PositivityTheory.ThKG.Loc.Cone.Vf
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] {c : A →ₐ[R] A} [Fintype β] [DecidableEq β] {J : Matrix β β A}
namespace GlobalTheory.ThK.Dbl.Vf2
theorem _root_.solution {b b' x y t' : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) (g : UG c (dbl J))
    (hg : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = fromRows x y) (ht : (y + b * (y - x)) * t' = 1) {ε : A} (he : ε * ε = ε)
    (hc : c ε = ε) (hm : ε • (y - x) = y - x) :
    ∃ (s n p : UG c (dbl J)) (t : GL β A), s * s = 1 ∧ g = s * n * s * p ∧ s.1.1 = CC b * SS ε * Ci b ∧
      n.1.1 = CC b * fromBlocks 1 (-((y - x) * t')) 0 1 * Ci b ∧ (n⁻¹).1.1 = CC b * fromBlocks 1 ((y - x) * t') 0 1 * Ci b ∧
      n.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * (1 : GL β A).1 ∧
      p.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * t.1 ∧
      t.1 = y + b * (y - x) ∧ (t⁻¹).1 = t' := by
  have lag := lag_of b1 hb g hg
  set m : Matrix β β A := y - x with hmd
  set t₀ := y + b * m with ht₀
  set T := -(m * t') with hT
  have ht' : t' * t₀ = 1 := mul_eq_one_comm.1 ht
  have sk : Tᵀ * J + J * T.map c = 0 := by
    have a1 : t'ᵀ * t₀ᵀ = 1 := by rw [← transpose_mul, ht, transpose_one]
    have a2 : t₀.map c * t'.map c = 1 := by rw [← mapc_mul, ht, mapc_one]
    rw [hT, transpose_neg, transpose_mul, mapc_neg, mapc_mul]
    linear_combination (norm := noncomm_ring) -(t'ᵀ * lag * t'.map c) + a1 * J * m.map c * t'.map c + t'ᵀ * mᵀ * J * a2
  have e0 : ε * (1 - ε) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have e0' : (1 - ε) * ε = 0 := by rw [mul_comm, e0]
  have e1 : (1 - ε) * (1 - ε) = 1 - ε := by rw [sub_mul, one_mul, e0, sub_zero]
  have hS : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A) * SS ε = 1 := by
    rw [SS, fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, e0, e0', e1, he, ← add_smul]
    simp
  have hSu : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * fromBlocks 0 J J 0 * (SS ε : Matrix (β ⊕ β) (β ⊕ β) A).map c =
      fromBlocks 0 J J 0 := by
    rw [SS, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp only [mapc_smul, mapc_one, map_sub, map_one, hc, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, smul_zero, zero_add, add_zero, smul_smul, e0, e0', e1, he, ← add_smul]
    simp
  have hU : (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks 1 (m * t') 0 1 = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one, hT]; simp
  have hUu : (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * fromBlocks 0 J J 0 *
      (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A).map c = fromBlocks 0 J J 0 := by
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, mapc_one, mapc_zero]
    simp only [transpose_one, transpose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
    rw [add_comm (J * _), sk]
  have hTt : T * t₀ = -m := by rw [hT, Matrix.neg_mul, Matrix.mul_assoc, ht', Matrix.mul_one]
  let s := mkU b1 hb _ _ hS hSu
  let n := mkU b1 hb _ _ hU hUu
  have hs : s.1.1 = CC b * SS ε * Ci b := rfl
  have hn : n.1.1 = CC b * fromBlocks 1 T 0 1 * Ci b := rfl
  have hεT : ε • T = T := by rw [hT, smul_neg, ← Matrix.smul_mul, hm]
  have hεT' : (1 - ε) • T = 0 := by rw [sub_smul, one_smul, hεT, sub_self]
  have hL : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks 1 T 0 1 * SS ε = fromBlocks 1 0 T 1 := by
    rw [SS, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, smul_zero, add_zero, hεT, hεT',
      zero_add, Matrix.add_mul, smul_add, smul_smul, e0, e0', e1, he, zero_smul, ← add_smul]
    simp
  have hD : Ci b * (diagCols β : Matrix (β ⊕ β) β A) = (fromRows 1 0 : Matrix (β ⊕ β) β A) := by
    rw [Ci, diagCols, fromBlocks_mul_fromRows]; simp
  have hD' : CC b * (fromRows 1 0 : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) := by
    rw [CC, diagCols, fromBlocks_mul_fromRows]; simp
  refine ⟨s, n, (s * n * s)⁻¹ * g, ⟨t₀, t', ht, ht'⟩, Subtype.ext (Units.ext s.1.mul_inv), by group, hs, hn, rfl, ?_, ?_, rfl, rfl⟩
  · rw [hn, Matrix.mul_assoc _ (Ci b), hD, Matrix.mul_assoc (CC b), fromBlocks_mul_fromRows]
    simpa using hD'
  · have e : (s * n * s).1.1 = CC b * fromBlocks 1 0 T 1 * Ci b := by
      change s.1.1 * n.1.1 * s.1.1 = _
      rw [hs, hn, ← hL]
      calc CC b * SS ε * Ci b * (CC b * fromBlocks 1 T 0 1 * Ci b) * (CC b * SS ε * Ci b)
          = CC b * (SS ε * (Ci b * CC b) * fromBlocks 1 T 0 1 * (Ci b * CC b) * SS ε) * Ci b := by noncomm_ring
        _ = _ := by rw [Ci_CC, Matrix.mul_one, Matrix.mul_one]
    have e2 : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (s * n * s).1.1 * ((diagCols β : Matrix (β ⊕ β) β A) * t₀) := by
      rw [e, hg, ← Matrix.mul_assoc _ (diagCols β : Matrix (β ⊕ β) β A), Matrix.mul_assoc _ (Ci b), hD, Matrix.mul_assoc (CC b),
        fromBlocks_mul_fromRows, CC, fromBlocks_mul_fromRows, fromRows_mul]
      congr 1
      · linear_combination (norm := noncomm_ring) -((1 + b) * hTt) - ht₀ + hmd
      · linear_combination (norm := noncomm_ring) -(b * hTt) - ht₀
    change ((s * n * s)⁻¹).1.1 * g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * t₀
    rw [Matrix.mul_assoc _ g.1.1, e2, ← Matrix.mul_assoc, show ((s * n * s)⁻¹).1.1 * (s * n * s).1.1 = 1 from (s * n * s).1.inv_mul,
      Matrix.one_mul]
end GlobalTheory.ThK.Dbl.Vf2
