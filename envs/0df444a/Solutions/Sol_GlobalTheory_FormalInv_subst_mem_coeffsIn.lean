-- Prove2me | solution 1 for GlobalTheory.FormalInv.subst_mem_coeffsIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:24.518458+00:00
-- url     : https://prove2.me/submissions/d7f56a5d-7c2e-446e-a455-436926ea3509

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
namespace GlobalTheory.FormalInv
theorem _root_.solution {κ : Type*} {S : Subring R} {w : κ → τ → ℕ} {w' : κ → σ → ℕ}
    {g : κ → ℕ} {a : σ → MvPowerSeries τ R} (ha' : HasSubst a)
    (ha : ∀ k s, a s ∈ weightGe (w k) (w' k s)) (haS : ∀ s, a s ∈ coeffsIn S w g)
    {f : MvPowerSeries σ R} (hf : f ∈ coeffsIn S w' g) : f.subst a ∈ coeffsIn S w g := by
  intro e he
  rw [coeff_subst ha']
  refine finsum_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem) fun d => ?_
  by_cases hd : ∀ k, weight (w' k) d < g k
  · exact S.mul_mem (hf d hd)
      ((coeffsIn S w g).prod_mem (fun s _ => (coeffsIn S w g).pow_mem (haS s) _) e he)
  · obtain ⟨k, hk⟩ := not_forall.1 hd
    have := he k
    simp [prod_pow_mem_weightGe (ha k) d e (by omega)]
end GlobalTheory.FormalInv
