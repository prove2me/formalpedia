-- Prove2me | solution 1 for GlobalTheory.AinfXi.dvd_of_dvd_mul_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:14:07.442804+00:00
-- url     : https://prove2.me/submissions/bc208731-e6f5-45d0-b0a9-ed453b25c1a1

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrder
import Theorems.Thm_GlobalTheory_AinfXi_ker_theta
import Theorems.Thm_GlobalTheory_AinfXi_xi_nzd
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_ker_theta
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_theta_xi
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_torsion_free
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
open WittVector Ideal
open GlobalTheory GlobalTheory.AinfXi
open GlobalTheory.Sandwich
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
variable (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (root ε).untilt p)
include hv hε
namespace GlobalTheory.AinfXi
theorem _root_.solution (N : ℕ) (z : Ainf p O) (h : xi ε ^ N ∣ z * p) : xi ε ^ N ∣ z := by
  induction N generalizing z with
  | zero => simp
  | succ N ih =>
    obtain ⟨w, hw⟩ := h
    have h1 : fontaineTheta O p (z * p) = 0 := by
      rw [hw, map_mul, map_pow,
        show fontaineTheta O p (xi ε) = 0 from ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε,
        zero_pow (Nat.succ_ne_zero _), zero_mul]
    rw [map_mul, map_natCast] at h1
    have h0 : fontaineTheta O p z = 0 :=
      ReciprocityTheory.PGsh.Ainf.torsion_free p O hv 1 _ (by rw [pow_one]; exact h1)
    obtain ⟨z1, rfl⟩ := mem_span_singleton'.1 (by rw [← ker_theta hv ε hε]; exact h0)
    have h2 : (z1 * p - xi ε ^ N * w) * xi ε = 0 := by linear_combination hw
    obtain ⟨w', hw'⟩ := ih z1 ⟨w, sub_eq_zero.1 (xi_nzd hv ε hε _ h2)⟩
    exact ⟨w', by rw [hw']; ring⟩
end GlobalTheory.AinfXi
