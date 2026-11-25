-- Prove2me | solution 1 for GroundTheory.PAdicHodge.perfectField_of_isPerfectoidField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:38.186651+00:00
-- url     : https://prove2.me/submissions/18f78bf6-c90c-4e27-80fa-130e7bd31eaa

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgClosed
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApprox
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_perfectRing


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
open Polynomial
namespace GroundTheory.PAdicHodge
theorem _root_.solution (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] : PerfectField K := by
  rcases CharP.exists' K with h | ⟨q, hq, hqK⟩
  · infer_instance
  · have hqp : q = p := by
      by_contra hne
      have : NeZero q := ⟨hq.out.ne_zero⟩
      have hdvd : ¬ q ∣ p := fun h =>
        hne ((Nat.prime_dvd_prime_iff_eq hq.out (Fact.out : p.Prime)).1 h)
      have hp0 : (p : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]; exact hdvd
      set u := (p : ZMod q)⁻¹
      have h1 : (p : ZMod q) * u = 1 := mul_inv_cancel₀ hp0
      have h2 := congrArg (ZMod.castHom (dvd_refl q) K) h1
      rw [map_mul, map_one, map_natCast, ZMod.castHom_apply, ZMod.cast_eq_val] at h2
      have h3 : ‖(p : K)‖ * ‖((u.val : ℕ) : K)‖ = 1 := by
        rw [← norm_mul, h2, norm_one]
      have h4 : ‖((u.val : ℕ) : K)‖ ≤ 1 :=
        (isUltrametricDist_iff_forall_norm_natCast_le_one.1 inferInstance) _
      have h5 := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
      nlinarith [norm_nonneg ((u.val : ℕ) : K), norm_nonneg (p : K)]
    subst hqp
    have := IsPerfectoidField.perfectRing (K := K) q
    exact PerfectRing.toPerfectField K q
end GroundTheory.PAdicHodge
