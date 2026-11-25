-- Prove2me | solution 1 for GlobalTheory.Ex.RecPeriods.txT_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:32:04.902222+00:00
-- url     : https://prove2.me/submissions/ed744055-d338-4a27-a840-8b19884ff3b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_cubN_mul_exp
import Theorems.Thm_GlobalTheory_Ex_NumD_QT_pow_b
import Theorems.Thm_GlobalTheory_T_mulq_dbl_cubN_relations


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
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.RecPeriods
namespace GlobalTheory.Ex.RecPeriods
theorem _root_.solution {O : Type} [CommRing O] (N : NumD O) (m : ℕ) (p : N.QT (m ^ 2)) (hp : p.1.1 = 1)
    (q p₁ : N.QT m) (hq : q.1.1 = 1) (hq' : q.1.2 = p.1.2 ^ m) :
    N.txT m p p₁.1.1.toAdd =
      (N.ψ p₁.1.1.toAdd * N.wp q p₁ * mulq N.θ N.σ m p₁.1.2.b : Oˣ) * N.uth m p.1.2.b p₁.1.2.b := by
  have a := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB m m p₁.1.2.b p.1.2.b).2.1
  have c := cubN_mul_exp N.cub m m p.1.2.b p₁.1.2.b
  rw [← sq] at c
  have key : N.wQ p / mulq N.θ N.σ m p.1.2.b * (N.ψ p₁.1.1.toAdd * (p.1.2 ^ m).s p₁.1.1.toAdd) =
      N.ψ p₁.1.1.toAdd * N.wp q p₁ * mulq N.θ N.σ m p₁.1.2.b *
        (N.uV (m ^ 2) 1 p.1.2.b p₁.1.2.b * N.wS (m ^ 2) p.1.2.b 1 1) *
        (mulq N.θ N.σ m (p₁.1.2.b * p.1.2.b))⁻¹ := by
    simp only [NumB.uV, N.cub.face, div_one, NumD.wQ, NumD.wp, NumD.tk, hp, hq, hq', toAdd_one, NumD.ψ_zero,
      NumD.Gt.s_zero, NumD.Gt.pow_b, a, c]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_div, ofMul_one]
    module
  replace key := congrArg Units.val key
  simp only [NumD.txT, NumD.vt, NumB.uth, NumB.mth, mul_pow, N.QT_pow_b p₁, NumD.Gt.pow_b]
  simp only [Units.val_mul] at key ⊢
  linear_combination N.th (N.c p₁.1.1.toAdd * p.1.2.b ^ m) * key
end GlobalTheory.Ex.RecPeriods
