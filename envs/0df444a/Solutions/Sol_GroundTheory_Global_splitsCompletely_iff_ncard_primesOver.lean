-- Prove2me | solution 1 for GroundTheory.Global.splitsCompletely_iff_ncard_primesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:15.865796+00:00
-- url     : https://prove2.me/submissions/c2d8f93d-16ea-4f89-9072-044128d87772

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) :
    SplitsCompletely L v ↔ (v.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  classical
  let _ := Fintype.ofFinite (v.asIdeal.primesOver (𝓞 L))
  have hsum : ∑ q : v.asIdeal.primesOver (𝓞 L), q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) =
      Module.finrank K L := by
    rw [Ideal.sum_ramification_inertia_eq_finrank, ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]
  have key : (v.asIdeal.primesOver (𝓞 L)).ncard = ∑ _q : v.asIdeal.primesOver (𝓞 L), 1 := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]
  rw [key, ← hsum, Finset.sum_eq_sum_iff_of_le (fun q _ => Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 (𝓞 K)).ne'
      (Ideal.inertiaDeg_pos q.1 (𝓞 K)).ne'))]
  constructor
  · intro h q _
    have hq0 : q.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.ne_bot q.2
    have := h ⟨q.1, q.2.1, hq0⟩ q.2.2
    rw [this.1, this.2]
  · intro h w hw
    have := h ⟨w.asIdeal, w.isPrime, hw⟩ (Finset.mem_univ _)
    exact mul_eq_one.mp this.symm
end GroundTheory.Global
