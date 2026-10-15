-- Prove2me | solution 1 for OAI.BufferedIsing.DSS.pin_comparison_of_removed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:02:20.691773+00:00
-- url     : https://prove2.me/submissions/814d854c-e4ab-4fb3-9656-ced74da99161

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Influence.lean:L120-L151
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.DSS.pin_comparison_of_removed. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction
import Definitions.Def_OAI_Probability_Ising_GibbsMeasure
import Definitions.Def_OAI_Probability_Ising_Interpolation
import Definitions.Def_OAI_Probability_Ising_FieldUpdate
import Definitions.Def_OAI_Probability_Ising_Influence

-- ---- from OAI.Probability.Ising.GibbsMeasure ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

noncomputable section

variable {V : Type*} [Fintype V]

lemma mass_pos (J : V → V → ℝ) (h : V → ℝ) (σ : V → Bool) : 0 < mass J h σ :=
  Real.exp_pos _

lemma part_pos (J : V → V → ℝ) (h : V → ℝ) : 0 < part J h := by
  classical
  exact Finset.sum_pos (fun σ _ => mass_pos J h σ) Finset.univ_nonempty

lemma average_const (J : V → V → ℝ) (h : V → ℝ) (c : ℝ) :
    average J h (fun _ => c) = c := by
  unfold average
  rw [← Finset.sum_mul]
  exact mul_div_cancel_left₀ c (part_pos J h).ne'

end

end BufferedIsing.DSS

end OAI

-- ---- from OAI.Probability.Ising.FieldUpdate ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

noncomputable section

variable {V : Type*} [Fintype V]

lemma pinMean_self (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) :
    pinMean J h v b v = sgn b := by
  simp only [pinMean, insertSpin_self, average_const]

lemma pinMean_other (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool)
    (o : V) (hov : o ≠ v) :
    pinMean J h v b o = mean (removedCoupling J v) (removedField J h v b) ⟨o, hov⟩ := by
  unfold pinMean mean
  congr 1
  funext η
  exact congrArg sgn (insertSpin_other v b η ⟨o, hov⟩)

end

end BufferedIsing.DSS

end OAI

-- ---- from OAI.Probability.Ising.Influence ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

noncomputable section

universe u

variable {V : Type u} [Fintype V]

lemma pin_comparison_of_removed (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g h : V → ℝ) (hh : 0 ≤ h) (v o : V)
    (H : InfluenceBound (removedCoupling J v)) :
    pinMean J (g + h) v true o - pinMean J (g - h) v false o ≤
      pinMean J h v true o - pinMean J (-h) v false o := by
  by_cases hov : o = v
  · subst o
    simp only [pinMean_self, le_refl]
  · let g' : {u : V // u ≠ v} → ℝ := fun u => g u
    let h' : {u : V // u ≠ v} → ℝ := fun u => h u + (J v u + J u v)
    have hh' : 0 ≤ h' := by
      intro u
      exact add_nonneg (hh u) (add_nonneg (hJ v u) (hJ u v))
    have he1 : removedField J (g + h) v true = g' + h' := by
      ext u
      simp only [removedField, Pi.add_apply, sgn, ↓reduceIte, mul_one, g', h']
      ring
    have he2 : removedField J (g - h) v false = g' - h' := by
      ext u
      simp only [removedField, Pi.sub_apply, sgn, Bool.false_eq_true, ↓reduceIte,
        mul_neg_one, g', h']
      ring
    have he3 : removedField J h v true = h' := by
      ext u
      simp only [removedField, sgn, ↓reduceIte, mul_one, h']
    have he4 : removedField J (-h) v false = -h' := by
      ext u
      simp only [removedField, Pi.neg_apply, sgn, Bool.false_eq_true, ↓reduceIte,
        mul_neg_one, h']
      ring
    simp only [pinMean_other _ _ _ _ _ hov, he1, he2, he3, he4]
    exact H g' h' hh' ⟨o, hov⟩

end

end BufferedIsing.DSS

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing OAI.BufferedIsing.DSS
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V]

theorem solution (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g h : V → ℝ) (hh : 0 ≤ h) (v o : V)
    (H : InfluenceBound (removedCoupling J v)) :
    pinMean J (g + h) v true o - pinMean J (g - h) v false o ≤
      pinMean J h v true o - pinMean J (-h) v false o := by
  first
    | exact OAI.BufferedIsing.DSS.pin_comparison_of_removed J hJ g h hh v o H
    | exact OAI.BufferedIsing.DSS.pin_comparison_of_removed
    | (apply OAI.BufferedIsing.DSS.pin_comparison_of_removed <;> assumption)
    | (intros; apply OAI.BufferedIsing.DSS.pin_comparison_of_removed <;> assumption)
