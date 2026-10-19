-- Prove2me | solution 1 for HumanMachine.Accuracy.vstar_convex
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T07:56:16.834238+00:00
-- url     : https://prove2.me/submissions/4f4c3009-5e28-40dd-a652-9b0d98de66e7

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel

open HumanMachine.Alone HumanMachine.Accuracy

namespace HumanMachineValueResearch

theorem optimum_exists (lam mu : ℝ) : ∃ q : ℝ × ℝ, IsOptimal lam mu q.1 q.2 := by
  have hc : Continuous (fun q : ℝ × ℝ => value lam mu q.1 q.2) := by
    unfold value accuracy cost choiceProb
    fun_prop
  obtain ⟨q,hq,hm⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    (show (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1).Nonempty from ⟨(0,0),by simp⟩)
    hc.continuousOn
  refine ⟨q,hq.1,hq.2,?_⟩
  intro pg hpg pb hpb
  exact hm (show (pg,pb) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 from ⟨hpg,hpb⟩)

theorem chosen_optimal (lam mu : ℝ) : IsOptimal lam mu (optPair lam mu).1 (optPair lam mu).2 :=
  Classical.epsilon_spec (optimum_exists lam mu)

theorem choice_bounds (mu pg pb : ℝ) (hm : mu ∈ Set.Icc (0 : ℝ) 1)
    (hg : pg ∈ Set.Icc (0 : ℝ) 1) (hb : pb ∈ Set.Icc (0 : ℝ) 1) :
    choiceProb mu pg pb ∈ Set.Icc (0 : ℝ) 1 := by
  unfold choiceProb
  constructor
  · exact add_nonneg (mul_nonneg hm.1 hg.1) (mul_nonneg (sub_nonneg.mpr hm.2) hb.1)
  · have h1 := mul_le_mul_of_nonneg_left hg.2 hm.1
    have h2 := mul_le_mul_of_nonneg_left hb.2 (sub_nonneg.mpr hm.2)
    nlinarith only [h1,h2]

theorem fixed_strategy_convex (lam pg pb : ℝ) (hlam : 0 ≤ lam)
    (hg : pg ∈ Set.Icc (0 : ℝ) 1) (hb : pb ∈ Set.Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun mu => value lam mu pg pb) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb' hab
  have hJ := Real.strictConcave_binEntropy.concaveOn.2
    (choice_bounds x pg pb hx hg hb) (choice_bounds y pg pb hy hg hb) ha hb' hab
  simp only [smul_eq_mul] at hJ ⊢
  have he : a * choiceProb x pg pb + b * choiceProb y pg pb =
      choiceProb (a*x+b*y) pg pb := by
    unfold choiceProb
    linear_combination pb * hab
  rw [he] at hJ
  have hJ' := mul_le_mul_of_nonneg_left hJ hlam
  have hlinear : (a+b)*(1-pb+lam*Real.binEntropy pb) = 1-pb+lam*Real.binEntropy pb := by rw [hab,one_mul]
  unfold value accuracy cost
  nlinarith only [hJ',hlinear]

end HumanMachineValueResearch

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Boyacı, Canyakmaz and de Véricourt, ESMT Working Paper 20-02 (2020).
theorem solution (lam : ℝ) (hlam : 0 < lam) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (VStar lam) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  let q := optPair lam (a*x+b*y)
  have hq := HumanMachineValueResearch.chosen_optimal lam (a*x+b*y)
  have hc := (HumanMachineValueResearch.fixed_strategy_convex lam q.1 q.2 hlam.le hq.1 hq.2.1).2 hx hy ha hb hab
  have hoptx := (HumanMachineValueResearch.chosen_optimal lam x).2.2 q.1 hq.1 q.2 hq.2.1
  have hopty := (HumanMachineValueResearch.chosen_optimal lam y).2.2 q.1 hq.1 q.2 hq.2.1
  simp only [smul_eq_mul] at hc ⊢
  exact hc.trans (add_le_add (mul_le_mul_of_nonneg_left hoptx ha) (mul_le_mul_of_nonneg_left hopty hb))

#print axioms solution
