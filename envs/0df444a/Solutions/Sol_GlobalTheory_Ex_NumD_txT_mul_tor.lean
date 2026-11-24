-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.txT_mul_tor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:33.636442+00:00
-- url     : https://prove2.me/submissions/b8c6d793-7f2b-4acf-be4b-a3b1467442c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Theorems.Thm_GlobalTheory_Ex_NumD_vt_mul_tor_shift
import Theorems.Thm_GlobalTheory_Ex_NumD_tor_injective
import Theorems.Thm_GlobalTheory_Ex_NumD_tor_mul_s_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution {m : ℕ} (hm : Odd m) (p p' : N.QT (m ^ 2)) (χ : N.X) (t : Multiplicative N.X →* Oˣ)
    (h : p'.1.1 = p.1.1) (h' : p'.1.2 = p.1.2 * N.tor t) :
    N.txT m p' χ = (t p.1.1 ^ ((m ^ 2 - 1) / 2) * t (Multiplicative.ofAdd (p.1.1.toAdd + m • χ)) : Oˣ) *
      N.txT m p χ := by
  have ht : t ^ (m ^ 2) = 1 := by
    apply N.tor_injective
    have a := N.mem_QT.1 p'.2
    rw [h, h', mul_pow, N.mem_QT.1 p.2, mul_eq_left] at a
    rw [N.tor_pow, a, N.tor_one]
  obtain ⟨j, hj⟩ : Odd (m ^ 2) := hm.pow
  have hd : (m ^ 2 - 1) / 2 = j := by omega
  have hy : t p.1.1 ^ j * t p.1.1 ^ j * t p.1.1 = 1 := by
    rw [← pow_add, ← pow_succ, ← two_mul, ← hj, ← MonoidHom.pow_apply, ht, MonoidHom.one_apply]
  have hb : p'.1.2.b = p.1.2.b := by rw [h', Gt.mul_b, tor_b, mul_one]
  have hs : p'.1.2.s p.1.1.toAdd = t p.1.1 * p.1.2.s p.1.1.toAdd := by
    rw [h', mul_comm p.1.2, N.tor_mul_s_apply]
    rfl
  rw [txT, txT, wQ, wQ, NumB.wS, NumB.wS, hb, h, hs, h', mul_pow, ← N.tor_pow, vt_mul_tor_shift, hd,
    ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [ofAdd_add, ofAdd_toAdd, ofAdd_nsmul, map_mul, map_pow, MonoidHom.pow_apply]
  have a := congrArg Additive.ofMul hy
  apply Additive.ofMul.injective
  simp only [div_pow, mul_pow, ofMul_mul, ofMul_div, ofMul_one] at a ⊢
  linear_combination (norm := abel) -a
end GlobalTheory.Ex.NumD
