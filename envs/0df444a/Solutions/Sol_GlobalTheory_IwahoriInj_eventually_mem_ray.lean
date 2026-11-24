-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.eventually_mem_ray
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:26.329265+00:00
-- url     : https://prove2.me/submissions/2fc04bdb-a297-429a-ba65-5f6d5f554408

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_IwahoriInj_eventually_deep
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_mem_unipB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable {g f f' : n → n → ℤ} {i j : n}
variable {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL n k) V}
variable [LinearOrder n]
namespace GlobalTheory.IwahoriInj
theorem _root_.solution {u : GL n k} (hu : u ∈ unipB k n) :
    ∀ᶠ m : ℕ in Filter.atTop, u ∈ grp k (chamber_ray (n := n) m).1 := by
  have key : ∀ u ∈ unipB k n, ∀ᶠ m : ℕ in Filter.atTop, ∀ i j, Deep (ray m i j) (u.val i j) := by
    intro u hu
    simp only [Filter.eventually_all]
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · filter_upwards [eventually_deep (u.val i j)] with m hm
      refine hm.mono ?_
      have h1 : ((Finset.univ.filter (· < i)).card : ℤ) < (Finset.univ.filter (· < j)).card := by
        refine Int.ofNat_lt.2 (Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun a ha => ?_).2
          ⟨i, by simpa using h, by simp⟩))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact ha.trans h
      simp only [ray, if_neg h.not_gt]
      nlinarith
    · simp [((mem_unipB k).1 hu).2, ray, deep_zero_iff]
    · simp [((mem_unipB k).1 hu).1 i j h, deep_zero]
  exact (key u hu).and (key _ (inv_mem hu))
end GlobalTheory.IwahoriInj
