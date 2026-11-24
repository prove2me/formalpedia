-- Prove2me | solution 1 for GlobalTheory.ZH.WtLin.linIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:17.874738+00:00
-- url     : https://prove2.me/submissions/1359d62f-622b-4b45-bac3-84f39cb12aba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffSymmSum
import Theorems.Thm_GlobalTheory_ZH_WtLin_weight_sum
import Theorems.Thm_GlobalTheory_ZH_WtLin_weight_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtLin
namespace GlobalTheory.ZH.WtLin
theorem _root_.solution : (∀ (k : Type) [Field k] (Φ : FibPre k) (N : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec), Φ.Good N q cls F → ∀ a : J → k, (∀ l, ∑ i, constFn Φ.G.hom ((Φ.H 1).U l) (a i) * (F i).f l = 0) → a = 0) := by
  intro k _ Φ N q J _ cls F hG a ha
  classical
  funext i₀
  have key := hG.inj (cls i₀) (hG.short i₀)
    (fun i => if ∃ m, cls i₀ = cls i + N • m then a i else 0)
    (fun i hi => by
      by_contra h
      exact hi (if_neg h))
    (fun l => by
      have h := weight_sum Φ F a (cls i₀) l
      rw [ha l] at h
      refine Eq.trans ?_ (h.symm.trans (weight_zero Φ _ l))
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · rfl
      · have h0 : Φ.wt (F i) (cls i₀) l = 0 := by
          by_contra hne
          exact hi (hG.supp i _ ⟨l, hne⟩).2
        rw [h0, mul_zero, mul_zero])
  have := congrFun key i₀
  rwa [if_pos ⟨0, by simp⟩] at this
end GlobalTheory.ZH.WtLin
