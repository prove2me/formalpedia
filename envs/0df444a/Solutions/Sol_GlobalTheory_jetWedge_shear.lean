-- Prove2me | solution 1 for GlobalTheory.jetWedge_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:26.837601+00:00
-- url     : https://prove2.me/submissions/53bcaf32-fc05-4bba-8db1-9a45d259549f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Theorems.Thm_GlobalTheory_jetWedge_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {D : ℕ}
namespace GlobalTheory
theorem _root_.solution (ω : M [⋀^Fin D]→ₗ[A] N) (h : A) (u : M) (v : Fin (D + 1) → A × M) :
    jetWedge ω (fun i => (h * (v i).1, h • (v i).2 + (v i).1 • u)) = h ^ (D + 1) • jetWedge ω v := by
  classical
  let φ : (A × M) →ₗ[A] (A × M) :=
    (h • LinearMap.fst A A M).prod (h • LinearMap.snd A A M + (LinearMap.fst A A M).smulRight u)
  let g : Option M → A × M := fun o => o.elim (1, 0) (fun m => (0, m))
  have hg : Submodule.span A (Set.range g) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, m⟩ -
    have : ((a, m) : A × M) = a • g none + g (some m) := by simp [g]
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩))
      (Submodule.subset_span ⟨some m, rfl⟩)
  have key : ((jetWedge ω).compLinearMap φ).toMultilinearMap
      = (h ^ (D + 1) • jetWedge ω).toMultilinearMap := by
    refine MultilinearMap.ext_of_span_eq_top (g := fun _ => g) (fun _ => hg) fun j => ?_
    change jetWedge ω (fun i => φ (g (j i))) = h ^ (D + 1) • jetWedge ω (fun i => g (j i))
    by_cases hj : ∃ a b, a ≠ b ∧ j a = j b
    · obtain ⟨a, b, hab, hjab⟩ := hj
      rw [(jetWedge ω).map_eq_zero_of_eq _ (i := a) (j := b) (by simp only [hjab]) hab,
        (jetWedge ω).map_eq_zero_of_eq _ (i := a) (j := b) (by simp only [hjab]) hab, smul_zero]
    · push Not at hj
      rw [jetWedge_apply, jetWedge_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      cases hi : j i with
      | some m => simp [φ, g]
      | none =>
        have hk : ∀ k : Fin D, (g (j (i.succAbove k))).1 = 0 := by
          intro k
          cases hk : j (i.succAbove k) with
          | some m => simp [g]
          | none => exact absurd (hk.trans hi.symm) (hj _ _ (Fin.succAbove_ne i k))
        have : (fun k : Fin D => (φ (g (j (i.succAbove k)))).2)
            = fun k : Fin D => h • (g (j (i.succAbove k))).2 := by
          funext k
          simp [φ, hk k]
        rw [this, ω.map_smul_univ (fun _ => h)]
        simp only [φ, g, smul_smul]
        congr 1
        simp
        ring
  exact congrArg (fun F : MultilinearMap A (fun _ : Fin (D + 1) => A × M) N => F v) key
end GlobalTheory
