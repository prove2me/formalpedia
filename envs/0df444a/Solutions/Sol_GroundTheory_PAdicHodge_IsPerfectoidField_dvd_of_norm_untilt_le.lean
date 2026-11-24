-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.dvd_of_norm_untilt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:42:35.412797+00:00
-- url     : https://prove2.me/submissions/22dcc562-587a-474f-9adf-d354b9bc93ad

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_preTilt_ext
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mk_untilt_iterate
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_iterate_succ_pow
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_untilt_iterate_pow
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_eq_zero_iff
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_coeff_ofCompatible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open WittVector
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "φ" => RingEquiv.symm (frobeniusEquiv (PreTilt (normInteger K) p) p)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {a b : 𝒪♭} (hb : b ≠ 0)
    (h : ‖((PreTilt.untilt a : 𝒪) : K)‖ ≤ ‖((PreTilt.untilt b : 𝒪) : K)‖) : b ∣ a := by
  have hbn : ∀ n, ((PreTilt.untilt (φ^[n] b) : 𝒪) : K) ≠ 0 := by
    intro n h0
    apply hb
    have h0' : PreTilt.untilt (φ^[n] b) = 0 := Subtype.ext h0
    rw [← untilt_eq_zero_iff p, ← PreTilt.untilt_iterate_frobeniusEquiv_symm_pow b n, h0',
      zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
  have hle : ∀ n,
      ‖((PreTilt.untilt (φ^[n] a) : 𝒪) : K)‖ ≤ ‖((PreTilt.untilt (φ^[n] b) : 𝒪) : K)‖ := by
    intro n
    have hpn : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hpn, norm_untilt_iterate_pow,
      norm_untilt_iterate_pow]
    exact h
  let y : ℕ → 𝒪 := fun n =>
    ⟨((PreTilt.untilt (φ^[n] a) : 𝒪) : K) / PreTilt.untilt (φ^[n] b), mem_normInteger.2 (by
      rw [norm_div]; exact div_le_one_of_le₀ (hle n) (norm_nonneg _))⟩
  have hy : ∀ n, y (n + 1) ^ p = y n := by
    intro n
    ext
    simp only [y, SubmonoidClass.coe_pow, div_pow]
    rw [← SubmonoidClass.coe_pow, ← SubmonoidClass.coe_pow, untilt_iterate_succ_pow,
      untilt_iterate_succ_pow]
  refine ⟨ofCompatible p y hy, preTilt_ext p fun n => ?_⟩
  rw [map_mul, coeff_ofCompatible, ← mk_untilt_iterate, ← mk_untilt_iterate, ← map_mul]
  congr 1
  ext
  simp only [y, Subring.coe_mul]
  rw [mul_div_cancel₀ _ (hbn n)]
end GroundTheory.PAdicHodge.IsPerfectoidField
