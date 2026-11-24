-- Prove2me | solution 1 for GlobalTheory.Hk.RaySq.conv_aRay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:53:58.788794+00:00
-- url     : https://prove2.me/submissions/ce5fdd40-66a4-400d-91b5-114ca34a8bd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar
import Theorems.Thm_GlobalTheory_Hk_RaySq_conv_eq
import Theorems.Thm_GlobalTheory_Hk_RaySq_sum_aRay
import Theorems.Thm_GlobalTheory_Hk_RaySq_chi_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
variable {M : ℕ} (D : RayData K M)
namespace GlobalTheory.Hk.RaySq
theorem _root_.solution (ε : D.G → ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 =
      ∑ C ∈ normEq K n, chi D (fun _ => 1) C * r (chi D ε) C := by
  have h1 : ∀ m, ∑ g, aRay D g m = ∑ I ∈ normEq K m, chi D (fun _ => 1) I := by
    intro m
    rw [← sum_aRay D (fun _ => 1) m]
    simp
  have hkey : ∀ I J : Ideal (𝓞 K),
      chi D (fun _ => 1) I * chi D ε J = chi D (fun _ => 1) (I * J) * chi D ε J := by
    intro I J
    rw [chi_mul D (fun _ => 1) (fun _ _ => (mul_one 1).symm) I J, mul_assoc]
    congr 1
    simp only [chi]
    split_ifs <;> simp
  calc _ = ∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2,
        chi D (fun _ => 1) (I * J) * chi D ε J := by
        simp_rw [h1, sum_aRay D ε, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun I _ =>
          Finset.sum_congr rfl fun J _ => hkey I J
    _ = _ := (conv_eq (fun C J => chi D (fun _ => 1) C * chi D ε J) hn).trans
        (by simp only [r, Finset.mul_sum])
end GlobalTheory.Hk.RaySq
