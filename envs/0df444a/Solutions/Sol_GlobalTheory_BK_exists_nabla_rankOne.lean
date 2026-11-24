-- Prove2me | solution 1 for GlobalTheory.BK.exists_nabla_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:04:12.61123+00:00
-- url     : https://prove2.me/submissions/47ee338e-593c-4b1b-823c-b1ae3e22163d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Theorems.Thm_GlobalTheory_BK_exists_eq_mul_add_of_isAdicComplete
import Theorems.Thm_GlobalTheory_BK_exists_mul_frob_E
import Theorems.Thm_GlobalTheory_BK_E_mul_N_Ezpow
import Theorems.Thm_GlobalTheory_BK_Ezpow_neg_mul
import Theorems.Thm_GlobalTheory_BK_phi_bas_rankOne
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_N_E
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_mem_uPow
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_phi
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_smul
import Theorems.Thm_GlobalTheory_BK_PhiMod_lphi_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_smul
import Theorems.Thm_GlobalTheory_BK_PhiMod_raises_lphi
import Theorems.Thm_GlobalTheory_BK_Raises_eq_zero
import Theorems.Thm_GlobalTheory_BK_X_smul_mem_uPow
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_frob_mem_S
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_isAdicComplete_S
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.Hom.onPol_cls
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) {a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
variable {l e}
variable [CompleteSpace K]
namespace GlobalTheory.BK
theorem _root_.solution (j : ℤ) : ∃ γ ∈ S O K e,
    (rankOne O K l e fun _ : ZMod a => j).nabla (Ezpow K l e j • bas ()) =
      γ • Ezpow K l e j • bas () := by
  set P := rankOne O K l e fun _ : ZMod a => j
  obtain ⟨c, hc, hcE⟩ := exists_mul_frob_E (O := O) (K := K) l e
  obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := Nat.exists_eq_succ_of_ne_zero (Fact.out : l.Prime).ne_zero
  obtain ⟨n, hn⟩ : ∃ n, l * e = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (mul_ne_zero (Fact.out : l.Prime).ne_zero (NeZero.ne e))
  have := isAdicComplete_S O K l e
  obtain ⟨γ, hγ⟩ := exists_eq_mul_add_of_isAdicComplete (l : S O K e)
    { toFun := fun x => uIn _ ^ m * ⟨_, frob_mem_S l x.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp [mul_add]) }
    (fun x => Subtype.ext (by simp [mul_left_comm])) (-((j : S O K e) * (e : S O K e) * uIn (S O K e) ^ n * (⟨c, hc⟩ : S O K e)))
  have hγ' : (γ : K⟦X⟧) = (l : K⟦X⟧) * (X ^ m * frob K l γ) +
      -((j : K⟦X⟧) * (e : K⟦X⟧) * (X : K⟦X⟧) ^ n * c) := by
    simpa using congrArg Subtype.val hγ
  refine ⟨γ, γ.2, smul_right_injective _ (X_ne_zero (R := K)) ?_⟩
  have hq : (l : K⟦X⟧) * frob K l (N K (Ezpow K l e (-j)) * Ezpow K l e j) =
      -((j : K⟦X⟧) * (e : K⟦X⟧) * (X : K⟦X⟧) ^ (n + 1) * c) := by
    have h1 : E K l e * (N K (Ezpow K l e (-j)) * Ezpow K l e j) = -((j : K⟦X⟧) * (e : K⟦X⟧) * (X : K⟦X⟧) ^ e) := by
      rw [← mul_assoc, E_mul_N_Ezpow, mul_assoc, Ezpow_neg_mul, N_E]
      push_cast
      ring
    have h2 := congrArg (frob K l) h1
    simp only [map_mul, map_neg, map_pow, frob_X, map_natCast, map_intCast, ← pow_mul, hn] at h2 ⊢
    rw [← hcE]
    linear_combination c * h2
  have hb : (bas () : Vec K a Unit) = Ezpow K l e (-j) • Ezpow K l e j • bas () := by
    rw [smul_smul, Ezpow_neg_mul, one_smul]
  have hl (v : Vec K a Unit) : (l : K) • v = (l : K⟦X⟧) • v := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hR : Raises (P.lphi * mulV K a Unit (Ezpow K l e (-j))) := fun k v hv =>
    P.raises_lphi k _ ((uPow K a Unit _).smul_mem _ hv)
  change P.conn _ = (X : K⟦X⟧) • (γ : K⟦X⟧) • Ezpow K l e j • bas ()
  rw [← sub_eq_zero, smul_smul X]
  refine hR.eq_zero (σ := (id : Unit → Unit)) Function.surjective_id
    (δ := fun _ => P.conn (Ezpow K l e j • bas ()) - (X * (γ : K⟦X⟧)) • Ezpow K l e j • bas ())
    (fun _ => sub_mem (P.conn_mem_uPow _) (by rw [mul_smul]; exact X_smul_mem_uPow _))
    (fun _ => ?_) ()
  have h3 : Ezpow K l e (-j) • P.conn (Ezpow K l e j • bas ()) =
      P.conn (bas ()) - (N K (Ezpow K l e (-j)) * Ezpow K l e j) • bas () := by
    conv_rhs => rw [hb, P.conn_smul, ← hb, mul_smul, add_sub_cancel_left]
  rw [Module.End.mul_apply, mulV_apply, smul_sub, h3, smul_comm _ (X * (γ : K⟦X⟧)), ← hb, map_sub,
    map_sub, P.lphi_apply, ← P.conn_phi, P.lphi_apply, P.lphi_apply, P.phi_smul, P.phi_smul,
    phi_bas_rankOne, hl, hl, smul_smul (l : K⟦X⟧), smul_smul (l : K⟦X⟧), hq, sub_sub, ← add_smul,
    map_mul, frob_X]
  congr 2
  have hX : (X : K⟦X⟧) ^ l = X ^ (m + 1) := by rw [← hm]
  linear_combination X * hγ' - l * frob K l γ * hX
end GlobalTheory.BK
