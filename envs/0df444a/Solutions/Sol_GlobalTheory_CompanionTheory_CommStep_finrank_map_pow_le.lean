-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommStep.finrank_map_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:23.744823+00:00
-- url     : https://prove2.me/submissions/08bb92e5-4931-4223-88a9-e95799fb825f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfMemAdjoin
import Theorems.Thm_GlobalTheory_CompanionTheory_CommStep_adjoin_le_sup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommStep
open Module
namespace GlobalTheory.CompanionTheory.CommStep
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) (k : ℕ) :
    finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
        (LinearMap.mulRight ℂ (a 0 ^ k))) ≤
      finrank ℂ (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) +
        finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0 ^ (k + 1)))) := by
  have h := Submodule.map_mono (f := LinearMap.mulRight ℂ (a 0 ^ k))
    (GlobalTheory.CompanionTheory.CommStep.adjoin_le_sup a hc)
  have hcomp : (LinearMap.mulRight ℂ (a 0 ^ k)).comp (LinearMap.mulRight ℂ (a 0)) =
      LinearMap.mulRight ℂ (a 0 ^ (k + 1)) :=
    LinearMap.ext fun b => by
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_succ', mul_assoc]
  rw [Submodule.map_sup, ← Submodule.map_comp, hcomp] at h
  have h1 := Submodule.finrank_mono h
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ))).map
      (LinearMap.mulRight ℂ (a 0 ^ k)))
    ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
      (LinearMap.mulRight ℂ (a 0 ^ (k + 1))))
  have h3 := Submodule.finrank_map_le (LinearMap.mulRight ℂ (a 0 ^ k))
    (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)))
  rw [Subalgebra.finrank_toSubmodule] at h3
  omega
end GlobalTheory.CompanionTheory.CommStep
