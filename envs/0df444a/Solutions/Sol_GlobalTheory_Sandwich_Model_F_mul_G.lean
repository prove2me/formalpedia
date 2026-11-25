-- Prove2me | solution 1 for GlobalTheory.Sandwich.Model.F_mul_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:08:44.959186+00:00
-- url     : https://prove2.me/submissions/9791913b-9539-459a-aced-25a0aba828c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MemMixedTsub
import Theorems.Thm_GlobalTheory_Sandwich_Model_mu_ne_zero
import Theorems.Thm_GlobalTheory_Sandwich_Model_isDomain_Ainf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.Model
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε
variable {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)
namespace GlobalTheory.Sandwich.Model
theorem _root_.solution : D.F * D.G = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) := by
  haveI := isDomain_Ainf (p := p) hv
  have hd : D.F.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det D.G_mul_F
    rw [det_mul, h0, mul_zero, det_smul, det_one, mul_one] at this
    exact pow_ne_zero _ (mu_ne_zero hv hε) this.symm
  have h1 : (D.F * D.G - mu ε • 1) * D.F = 0 := by
    rw [sub_mul, mul_assoc, D.G_mul_F]; simp
  have h2 := congrArg (· * D.F.adjugate) h1
  simp only [mul_assoc, mul_adjugate, zero_mul, Matrix.mul_smul, mul_one] at h2
  refine sub_eq_zero.1 (Matrix.ext fun i j => ?_)
  have h3 : D.F.det * (D.F * D.G - mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) i j = 0 :=
    congrFun (congrFun h2 i) j
  exact (mul_eq_zero.1 h3).resolve_left hd
end GlobalTheory.Sandwich.Model
