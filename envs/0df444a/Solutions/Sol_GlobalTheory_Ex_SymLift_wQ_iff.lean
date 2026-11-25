-- Prove2me | solution 1 for GlobalTheory.Ex.SymLift.wQ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:32:09.269801+00:00
-- url     : https://prove2.me/submissions/a6340f16-bbd7-4e12-95f7-dc55b244acec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactor
import Theorems.Thm_GlobalTheory_Ex_SymLift_odd_root_iff
import Theorems.Thm_GlobalTheory_Ex_SymLift_tk_pow
import Theorems.Thm_GlobalTheory_Ex_NumD_QT_pow_b
import Theorems.Thm_GlobalTheory_T_degenerationData_psi_quadratic_generators_linear
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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.SymLift
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.SymLift
theorem _root_.solution {k : ℕ} (hk : Odd k) (p : N.QT k) (w : Oˣ) :
    w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧
      w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b) := by
  obtain ⟨j, rfl⟩ := hk
  have e : N.wQ p = N.ψ p.1.1.toAdd * mulq N.θ N.σ (2 * j + 1) p.1.2.b /
      (N.tk p p / dbl N.θ N.σ p.1.2.b ^ (2 * j + 1)) ^ j := by
    have : (2 * j + 1 - 1) / 2 = j := by omega
    simp only [NumD.wQ, NumB.wS, NumD.tk, this]
  rw [e, odd_root_iff, eq_div_iff_mul_eq']
  have a := tk_pow N p p
  have b := (GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N 0 p.1.1.toAdd).1
  have c := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB (2 * j + 1) 0 p.1.2.b 1).2.2.1
  rw [← N.QT_pow_b p] at b
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b c ⊢
  linear_combination (norm := module) a + b + c
end GlobalTheory.Ex.SymLift
