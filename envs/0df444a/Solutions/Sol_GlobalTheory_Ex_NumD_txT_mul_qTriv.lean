-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.txT_mul_qTriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:33:33.704155+00:00
-- url     : https://prove2.me/submissions/4658deab-358b-4576-8f87-46602a5552fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Theorems.Thm_GlobalTheory_Ex_NumD_vt_mul_io_shift
import Theorems.Thm_GlobalTheory_Ex_NumD_wQ_mul_qTriv_odd
import Theorems.Thm_GlobalTheory_Ex_NumD_Gt_pow_s
import Theorems.Thm_GlobalTheory_Ex_NumD_c_nsmul
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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (z χ : N.X) :
    N.txT m (p * N.qTriv (m ^ 2) z) χ = N.txT m p (χ + m • z) := by
  have e : (p * N.qTriv (m ^ 2) z).1.2 = p.1.2 * N.io z := rfl
  rw [txT, txT, N.wQ_mul_qTriv_odd hm.pow, e, mul_pow, ← N.io_nsmul, ← N.vt_mul_io_shift, ← mul_assoc,
    ← Units.val_mul]
  congr 2
  have h₁ := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB m 0 p.1.2.b (N.c z)).2.1
  obtain ⟨-, h₂, h₃⟩ := GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N m z
  have h₄ := congrArg (· ^ m) (h₃ p.1.2).1
  have h₅ := Gt.pow_s p.1.2 m (m • z)
  rw [N.c_nsmul] at h₅
  simp only [mul_pow, ← pow_mul, ← sq] at h₄
  rw [Gt.mul_b, io_b, h₁, ← h₂, ← h₄, ← h₅]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel
end GlobalTheory.Ex.NumD
