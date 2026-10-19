-- Prove2me | solution 1 for OAI.ThreeState.HasMean.bind
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:48:58.399071+00:00
-- url     : https://prove2.me/submissions/2ec2e20c-68ef-4256-821a-137730474981

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Expectations.lean:L80-L100
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.HasMean.bind. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations

-- ---- from OAI.Probability.ThreeState.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Three-state symmetric broadcast experiments, posterior advantage and total variation. -/

namespace ThreeState

 
 
 

 
 

 
 
 

 
 
 
end ThreeState
namespace ThreeState

lemma mass_nonneg {α : Type*} (p : PMF α) (a : α) : 0 ≤ mass p a := ENNReal.toReal_nonneg
lemma mass_bind {α β : Type*} (p : PMF α) (k : α → PMF β) (b : β) :
    mass (p.bind k) b = ∑' a, mass p a * mass (k a) b := by
  simp only [mass, PMF.bind_apply, ENNReal.tsum_toReal_eq
    (fun a => ENNReal.mul_ne_top (p.apply_ne_top a) ((k a).apply_ne_top b)), ENNReal.toReal_mul]

 
 
end ThreeState

end OAI

-- ---- from OAI.Probability.ThreeState.Expectations ----
namespace OAI

/-! Expectations, second moments and the regular and Poisson offspring laws. -/

namespace ThreeState
open scoped Classical

 
lemma HasMean.abs {α : Type*} {p : PMF α} {f : α → ℝ} (h : HasMean p f) :
    HasMean p (fun a => |f a|) := by
  simpa only [HasMean, abs_mul, abs_of_nonneg (mass_nonneg p _)] using Summable.abs h

lemma HasMean.of_abs {α : Type*} {p : PMF α} {f : α → ℝ}
    (h : HasMean p (fun a => |f a|)) : HasMean p f := by
  apply summable_norm_iff.mp
  simpa only [HasMean, Real.norm_eq_abs, abs_mul, abs_of_nonneg (mass_nonneg p _)] using h

lemma HasMean.bind {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    (hk : ∀ a, HasMean (k a) f)
    (hp : HasMean p (fun a => mean (k a) (fun b => |f b|))) :
    HasMean (p.bind k) f := by
  have hs : Summable (Function.uncurry (fun a b => mass p a * (mass (k a) b * |f b|))) := by
    apply (summable_prod_of_nonneg (fun ab =>
      mul_nonneg (mass_nonneg p ab.1) (mul_nonneg (mass_nonneg _ _) (abs_nonneg _)))).mpr
    change (∀ a, Summable (fun b => mass p a * (mass (k a) b * |f b|))) ∧
      Summable (fun a => ∑' b, mass p a * (mass (k a) b * |f b|))
    constructor
    · intro a
      exact (hk a).abs.mul_left (mass p a)
    · simpa only [tsum_mul_left, mean, HasMean] using hp
  apply HasMean.of_abs
  apply hs.prod_symm.prod.congr
  intro b
  change (∑' a, mass p a * (mass (k a) b * |f b|)) = mass (p.bind k) b * |f b|
  rw [mass_bind, ← tsum_mul_right]
  congr 1
  funext a
  ring

end ThreeState
namespace ThreeState
open scoped Classical

 

end ThreeState
namespace ThreeState

 
end ThreeState

namespace ThreeState

 
end ThreeState

end OAI

-- ---- platform node ----
open OAI OAI.ThreeState
open scoped Classical


theorem solution : type_of% @_root_.OAI.ThreeState.HasMean.bind := @_root_.OAI.ThreeState.HasMean.bind
