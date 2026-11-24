-- Prove2me | solution 1 for GlobalTheory.CoefTorusWeight.weight_preserved
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:48:37.71003+00:00
-- url     : https://prove2.me/submissions/b20489ff-b43f-44c5-b718-404406ebb685

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceEndomorphismPreservesTorusWei
import Theorems.Thm_GlobalTheory_CoefTorusWeight_coeff_actP_diag
import Theorems.Thm_GlobalTheory_CoefTorusWeight_detTwK_ne_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
open GlobalTheory GlobalTheory.CoefTorusWeight
namespace GlobalTheory.CoefTorusWeight
theorem _root_.solution (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (g : Module.End K (VV K lam))
    (hg : ∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) (v : VV K lam)
    (hv : ∀ m ∈ (v : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) :
    ∀ m ∈ ((g v : VV K lam) : Pol K ι n).support, ∀ τ a,
      ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a := by
  classical
  intro m hm τ0 a0
  let u : Kˣ := Units.mk0 (2 : K) two_ne_zero
  let t : ι → Fin n → Kˣ := fun τ a => if τ = τ0 ∧ a = a0 then u else 1
  have hprod : ∀ m : (ι × Fin n × Fin n) →₀ ℕ,
      (∏ v : ι × Fin n × Fin n, (t v.1 v.2.1 : K) ^ m v) = 2 ^ (∑ s : Fin n, m (τ0, a0, s)) := by
    intro m
    rw [Fintype.prod_prod_type, Finset.prod_eq_single τ0, Fintype.prod_prod_type,
      Finset.prod_eq_single a0, ← Finset.prod_pow_eq_pow_sum]
    · simp [t, u]
    · intro b _ hb
      simp [t, hb]
    · simp
    · intro b _ hb
      simp [t, hb]
    · simp
  set h : ι → GL (Fin n) K := fun τ => diagGL K n (t τ) with hh
  have hco : ∀ (w : VV K lam) (m : (ι × Fin n × Fin n) →₀ ℕ),
      coeff m ((rhoK lam h w : VV K lam) : Pol K ι n)
        = detTwK lam h * (2 ^ (∑ s : Fin n, m (τ0, a0, s)) * coeff m (w : Pol K ι n)) := by
    intro w m
    rw [← hprod]
    exact coeff_actP_diag lam t w m
  have h1 : rhoK lam h v = (detTwK lam h * 2 ^ (lam τ0).natW a0) • v := by
    apply Subtype.ext
    ext m'
    rw [hco, Submodule.coe_smul, coeff_smul, smul_eq_mul, mul_assoc]
    by_cases hm' : m' ∈ (v : Pol K ι n).support
    · rw [hv m' hm']
    · rw [notMem_support_iff.mp hm']
      simp
  have h2 := hg h v
  rw [h1, map_smul] at h2
  have h3 := congrArg (fun w : VV K lam => coeff m (w : Pol K ι n)) h2
  simp only [hco, Submodule.coe_smul, coeff_smul, smul_eq_mul, mul_assoc] at h3
  have h4 := mul_right_cancel₀ (mem_support_iff.mp hm) (mul_left_cancel₀ (detTwK_ne_zero lam h) h3)
  have h5 : (2 : ℕ) ^ (lam τ0).natW a0 = 2 ^ (∑ s : Fin n, m (τ0, a0, s)) := by
    exact_mod_cast h4
  exact (Nat.pow_right_injective le_rfl h5).symm
end GlobalTheory.CoefTorusWeight
