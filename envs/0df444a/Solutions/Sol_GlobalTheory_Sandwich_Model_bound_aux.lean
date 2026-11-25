-- Prove2me | solution 1 for GlobalTheory.Sandwich.Model.bound_aux
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:02:18.906904+00:00
-- url     : https://prove2.me/submissions/739ac9e1-b670-4d60-8f3e-bff143ed36a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MemMixedTsub
import Theorems.Thm_GlobalTheory_Sandwich_Model_xi_eq
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_ker_theta
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_theta_surj
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_xi_nzd


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
theorem _root_.solution (X Y : Matrix (Fin h) (Fin h) (Ainf p O)) (hXY : X * Y = mu ε • 1)
    (x : Fin h → O) (hx : Y.map (fontaineTheta O p) *ᵥ x = 0) :
    ∃ y, X.map (fontaineTheta O p) *ᵥ y = fontaineTheta O p (nu ε) • x := by
  choose m hm using fun i => ReciprocityTheory.PGsh.Ainf.theta_surj p O hv (x i)
  have h1 : ∀ i, ∃ c, (Y *ᵥ m) i = xi ε * c := by
    intro i
    have : (Y *ᵥ m) i ∈ RingHom.ker (fontaineTheta O p) := by
      rw [RingHom.mem_ker, RingHom.map_mulVec]
      have : (fontaineTheta O p) ∘ m = x := funext hm
      rw [this, hx]; rfl
    rw [ReciprocityTheory.PGsh.Ainf.ker_theta p O hv ε hε, Ideal.mem_span_singleton] at this
    exact this
  choose c hc using h1
  have h2 : Y *ᵥ m = xi ε • c := funext hc
  have h3 : ∀ i, (X *ᵥ c) i = nu ε * m i := by
    intro i
    have h4 := congrFun (congrArg (X *ᵥ ·) h2) i
    simp only [mulVec_mulVec, hXY, mulVec_smul, smul_mulVec, one_mulVec, Pi.smul_apply,
      smul_eq_mul] at h4
    refine sub_eq_zero.1 (ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε _ ?_)
    rw [← xi_eq, ← xi_mul_nu] at *
    linear_combination -h4
  refine ⟨fontaineTheta O p ∘ c, funext fun i => ?_⟩
  rw [← RingHom.map_mulVec, h3, map_mul, hm]; rfl
end GlobalTheory.Sandwich.Model
