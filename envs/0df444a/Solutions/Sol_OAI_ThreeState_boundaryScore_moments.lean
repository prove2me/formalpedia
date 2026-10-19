-- Prove2me | solution 1 for OAI.ThreeState.boundaryScore_moments
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:52:03.470848+00:00
-- url     : https://prove2.me/submissions/5b14a413-2fa9-4087-bc62-88a291b6d635

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Supercritical.lean:L82-L102
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.boundaryScore_moments. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations
import Definitions.Def_OAI_Probability_ThreeState_Messages
import Definitions.Def_OAI_Probability_ThreeState_Observation
import Definitions.Def_OAI_Probability_ThreeState_Update
import Definitions.Def_OAI_Probability_ThreeState_RadialMoments
import Definitions.Def_OAI_Probability_ThreeState_RadialDerivatives
import Definitions.Def_OAI_Probability_ThreeState_PosteriorMoments
import Definitions.Def_OAI_Probability_ThreeState_PoissonCritical
import Definitions.Def_OAI_Probability_ThreeState_Supercritical
import Theorems.Thm_OAI_ThreeState_HasMean_bind
import Theorems.Thm_OAI_ThreeState_mean_bind

-- ---- from OAI.Probability.ThreeState.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Three-state symmetric broadcast experiments, posterior advantage and total variation. -/

namespace ThreeState

 
 
 

 
 

 
 
 

 
 
 
end ThreeState
namespace ThreeState

lemma mass_nonneg {α : Type*} (p : PMF α) (a : α) : 0 ≤ mass p a := ENNReal.toReal_nonneg
lemma mass_sum {α : Type*} (p : PMF α) : ∑' a, mass p a = 1 := by
  simp only [mass, ← ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a), p.tsum_coe,
    ENNReal.toReal_one]
lemma mass_summable {α : Type*} (p : PMF α) : Summable (mass p) :=
  ENNReal.summable_toReal p.tsum_coe_ne_top

 
 
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

lemma hasMean_const {α : Type*} (p : PMF α) (c : ℝ) : HasMean p (fun _ => c) :=
  (mass_summable p).mul_right c

lemma mean_const {α : Type*} (p : PMF α) (c : ℝ) : mean p (fun _ => c) = c := by
  rw [mean, (mass_summable p).tsum_mul_right, mass_sum, one_mul]

lemma HasMean.add {α : Type*} {p : PMF α} {f g : α → ℝ} (hf : HasMean p f) (hg : HasMean p g) :
    HasMean p (fun a => f a+g a) := by
  simpa only [HasMean, mul_add] using Summable.add hf hg

lemma mean_add {α : Type*} {p : PMF α} {f g : α → ℝ} (hf : HasMean p f) (hg : HasMean p g) :
    mean p (fun a => f a+g a) = mean p f+mean p g := by
  simp only [mean, mul_add, hf.tsum_add hg]

lemma HasMean.mul_const {α : Type*} {p : PMF α} {f : α → ℝ} (hf : HasMean p f) (c : ℝ) :
    HasMean p (fun a => f a*c) := by
  simpa only [HasMean, mul_assoc] using hf.mul_right c

lemma mean_mul_const {α : Type*} (p : PMF α) (f : α → ℝ) (c : ℝ) :
    mean p (fun a => f a*c) = mean p f*c := by
  simp only [mean, ← mul_assoc, tsum_mul_right]

lemma HasMean.const_mul {α : Type*} {p : PMF α} {f : α → ℝ} (hf : HasMean p f) (c : ℝ) :
    HasMean p (fun a => c*f a) := by
  simpa only [mul_comm c] using hf.mul_const c

lemma mean_const_mul {α : Type*} (p : PMF α) (f : α → ℝ) (c : ℝ) :
    mean p (fun a => c*f a) = c*mean p f := by
  simp only [mul_comm c, mean_mul_const]

lemma hasMean_of_square {α : Type*} {p : PMF α} {f : α → ℝ}
    (h : HasMean p (fun a => (f a)^2)) : HasMean p f := by
  apply HasMean.of_abs
  apply Summable.of_nonneg_of_le (fun a => mul_nonneg (mass_nonneg p a) (abs_nonneg _))
    (fun a => mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (|f a|-1), sq_abs (f a)])
      (mass_nonneg p a)) ((hasMean_const p 1).add h)

lemma mass_pure {α : Type*} (a b : α) : mass (PMF.pure a) b = if b=a then 1 else 0 := by
  classical
  by_cases h : b=a <;> simp [mass, PMF.pure_apply, h]

lemma mean_pure {α : Type*} (a : α) (f : α → ℝ) : mean (PMF.pure a) f = f a := by
  classical
  simp [mean, mass_pure]

lemma hasMean_pure {α : Type*} (a : α) (f : α → ℝ) : HasMean (PMF.pure a) f := by
  classical
  simp only [HasMean, mass_pure, ite_mul, one_mul, zero_mul]
  exact summable_of_ne_finset_zero (s := {a}) (fun b hb => by simp at hb; simp [hb])

lemma mean_nonneg {α : Type*} (p : PMF α) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ mean p f := tsum_nonneg (fun a => mul_nonneg (mass_nonneg p a) (hf a))

lemma HasMean.map {α β : Type*} {p : PMF α} {g : α → β} {f : β → ℝ}
    (h : HasMean p (fun a => f (g a))) : HasMean (p.map g) f := by
  change HasMean (p.bind (fun a => PMF.pure (g a))) f
  apply HasMean.bind (fun a => hasMean_pure _ _)
  simpa only [mean_pure] using h.abs

lemma mean_map {α β : Type*} {p : PMF α} {g : α → β} {f : β → ℝ}
    (h : HasMean p (fun a => f (g a))) : mean (p.map g) f = mean p (fun a => f (g a)) := by
  change mean (p.bind (fun a => PMF.pure (g a))) f = _
  rw [mean_bind (fun a => hasMean_pure _ _) (by simpa only [mean_pure] using h.abs)]
  simp only [mean_pure]

end ThreeState
namespace ThreeState
open scoped Classical

lemma HasMean.mono {α : Type*} {p : PMF α} {f g : α → ℝ} (hg : HasMean p g)
    (hf : ∀ a, 0 ≤ f a) (hle : ∀ a, f a ≤ g a) : HasMean p f := by
  exact Summable.of_nonneg_of_le (fun a => mul_nonneg (mass_nonneg p a) (hf a))
    (fun a => mul_le_mul_of_nonneg_left (hle a) (mass_nonneg p a)) hg

lemma mean_le {α : Type*} {p : PMF α} {f g : α → ℝ}
    (hf : HasMean p f) (hg : HasMean p g) (hle : ∀ a, f a ≤ g a) : mean p f ≤ mean p g := by
  exact Summable.tsum_le_tsum (fun a => mul_le_mul_of_nonneg_left (hle a) (mass_nonneg p a)) hf hg

lemma mean_abs_le_one_add_square {α : Type*} {p : PMF α} {f : α → ℝ}
    (hf : HasMean p (fun a => (f a)^2)) :
    mean p (fun a => |f a|) ≤ 1+mean p (fun a => (f a)^2) := by
  have h := mean_le (hasMean_of_square hf).abs ((hasMean_const p 1).add hf)
    (fun a => (show |f a| ≤ 1+(f a)^2 by nlinarith [sq_nonneg (|f a|-1), sq_abs (f a)]))
  simpa only [mean_add (hasMean_const p 1) hf, mean_const] using h

lemma hasMean_bind_square {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    (hk : ∀ a, HasMean (k a) (fun b => (f b)^2))
    (hp : HasMean p (fun a => mean (k a) (fun b => (f b)^2))) :
    HasMean (p.bind k) (fun b => (f b)^2) := by
  apply HasMean.bind hk
  simpa only [abs_sq] using hp

lemma hasMean_bind_abs_of_square {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    (hk : ∀ a, HasMean (k a) (fun b => (f b)^2))
    (hp : HasMean p (fun a => mean (k a) (fun b => (f b)^2))) :
    HasMean p (fun a => mean (k a) (fun b => |f b|)) := by
  exact ((hasMean_const p 1).add hp).mono
    (fun a => mean_nonneg _ (fun b => abs_nonneg _))
    (fun a => mean_abs_le_one_add_square (hk a))

lemma mean_bind_of_square {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    (hk : ∀ a, HasMean (k a) (fun b => (f b)^2))
    (hp : HasMean p (fun a => mean (k a) (fun b => (f b)^2))) :
    mean (p.bind k) f = mean p (fun a => mean (k a) f) :=
  mean_bind (fun a => hasMean_of_square (hk a)) (hasMean_bind_abs_of_square hk hp)

lemma mean_bind_square {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    (hk : ∀ a, HasMean (k a) (fun b => (f b)^2))
    (hp : HasMean p (fun a => mean (k a) (fun b => (f b)^2))) :
    mean (p.bind k) (fun b => (f b)^2) = mean p (fun a => mean (k a) (fun b => (f b)^2)) := by
  apply mean_bind hk
  simpa only [abs_sq] using hp

lemma HasMean.congr {α : Type*} {p : PMF α} {f g : α → ℝ} (hf : HasMean p f)
    (hfg : ∀ a, f a = g a) : HasMean p g := by
  exact Summable.congr hf (fun a => congrArg (fun x => mass p a*x) (hfg a))

lemma mean_congr {α : Type*} (p : PMF α) {f g : α → ℝ} (hfg : ∀ a, f a = g a) :
    mean p f = mean p g := tsum_congr (fun a => congrArg (fun x => mass p a*x) (hfg a))

lemma hasMean_shift_square {α : Type*} {p : PMF α} {f : α → ℝ}
    (hf : HasMean p (fun a => (f a)^2)) (c : ℝ) : HasMean p (fun a => (c+f a)^2) := by
  exact (((hasMean_const p (c^2)).add ((hasMean_of_square hf).const_mul (2*c))).add hf).congr
    (fun a => by ring)

lemma mean_shift_square {α : Type*} {p : PMF α} {f : α → ℝ}
    (hf : HasMean p (fun a => (f a)^2)) (c : ℝ) :
    mean p (fun a => (c+f a)^2) = c^2+2*c*mean p f+mean p (fun a => (f a)^2) := by
  rw [mean_congr p (g := fun a => c^2+(2*c)*f a+(f a)^2) (fun a => by ring),
    mean_add ((hasMean_const p (c^2)).add ((hasMean_of_square hf).const_mul (2*c))) hf,
    mean_add (hasMean_const p (c^2)) ((hasMean_of_square hf).const_mul (2*c)),
    mean_const, mean_const_mul]

lemma hasMean_fintype {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) : HasMean p f :=
  summable_of_hasFiniteSupport (Set.toFinite _)

lemma mean_fintype {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) :
    mean p f = ∑ a, mass p a * f a := tsum_fintype _

 

lemma Moments.hasMean {α : Type*} {p : PMF α} {f : α → ℝ} {m s : ℝ}
    (h : Moments p f m s) : HasMean p f := hasMean_of_square h.square

lemma Moments.map {α β : Type*} {p : PMF α} {f : β → ℝ} {g : α → β} {m s : ℝ}
    (h : Moments p (fun a => f (g a)) m s) : Moments (p.map g) f m s := by
  refine ⟨HasMean.map (g := g) (f := fun b => (f b)^2) h.square, ?_, ?_⟩
  · exact (mean_map (g := g) (f := f) h.hasMean).trans h.first
  · exact (mean_map (g := g) (f := fun b => (f b)^2) h.square).trans h.second

lemma Moments.pure {α : Type*} (a : α) (f : α → ℝ) :
    Moments (PMF.pure a) f (f a) ((f a)^2) :=
  ⟨hasMean_pure _ _, mean_pure _ _, mean_pure _ _⟩

lemma Moments.shift {α : Type*} {p : PMF α} {f : α → ℝ} {m s : ℝ}
    (h : Moments p f m s) (c : ℝ) :
    Moments p (fun a => c+f a) (c+m) (c^2+2*c*m+s) := by
  refine ⟨hasMean_shift_square h.square c, ?_, ?_⟩
  · rw [mean_add (hasMean_const p c) h.hasMean, mean_const, h.first]
  · rw [mean_shift_square h.square, h.first, h.second]

lemma Moments.bind {α β : Type*} {p : PMF α} {k : α → PMF β} {f : β → ℝ}
    {m s : α → ℝ} {M S : ℝ} (hk : ∀ a, Moments (k a) f (m a) (s a))
    (hs : HasMean p s) (hm : mean p m = M) (hS : mean p s = S) :
    Moments (p.bind k) f M S := by
  have hp : HasMean p (fun a => mean (k a) (fun b => (f b)^2)) :=
    hs.congr (fun a => (hk a).second.symm)
  refine ⟨hasMean_bind_square (fun a => (hk a).square) hp, ?_, ?_⟩
  · rw [mean_bind_of_square (fun a => (hk a).square) hp]
    simpa only [(hk _).first] using hm
  · rw [mean_bind_square (fun a => (hk a).square) hp]
    simpa only [(hk _).second] using hS

lemma Moments.independent_add {α β : Type*} {p : PMF α} {q : PMF β}
    {f : α → ℝ} {g : β → ℝ} {m s n t : ℝ}
    (hf : Moments p f m s) (hg : Moments q g n t) :
    Moments (p.bind (fun a => q.map (fun b => (a,b))))
      (fun ab => f ab.1+g ab.2) (m+n) (s+2*m*n+t) := by
  apply Moments.bind (m := fun a => f a+n) (s := fun a => (f a)^2+2*f a*n+t)
    (fun a => Moments.map (g := fun b => (a,b)) (f := fun ab => f ab.1+g ab.2) (hg.shift (f a)))
  · exact (hf.square.add (hf.hasMean.mul_const (2*n))).add (hasMean_const p t) |>.congr
      (fun a => by ring)
  · rw [mean_add hf.hasMean (hasMean_const p n), hf.first, mean_const]
  · have he := mean_add (hf.square.add (hf.hasMean.mul_const (2*n))) (hasMean_const p t)
    rw [mean_congr p (g := fun a => ((f a)^2+f a*(2*n))+t) (fun a => by ring), he,
      mean_add hf.square (hf.hasMean.mul_const (2*n)), mean_mul_const, hf.first, hf.second, mean_const]
    ring

end ThreeState
namespace ThreeState

 
end ThreeState

namespace ThreeState

lemma HasMean.sub {α : Type*} {p : PMF α} {f g : α → ℝ}
    (hf : HasMean p f) (hg : HasMean p g) : HasMean p (fun a => f a-g a) := by
  simpa only [HasMean, mul_sub] using Summable.sub hf hg

lemma mean_sub {α : Type*} {p : PMF α} {f g : α → ℝ}
    (hf : HasMean p f) (hg : HasMean p g) :
    mean p (fun a => f a-g a) = mean p f-mean p g := by
  simp only [mean, mul_sub, hf.tsum_sub hg]

 
end ThreeState

end OAI

-- ---- from OAI.Probability.ThreeState.Supercritical ----
namespace OAI

/-! Boundary score moments and reconstruction above the Kesten–Stigum threshold. -/

namespace ThreeState

lemma multisetScore_coe {α : Type*} (f : α → ℝ) (as : List α) :
    multisetScore f (as : Multiset α) = listScore f as := by
  simp [multisetScore, listScore]

lemma iidList_moments {α : Type*} {p : PMF α} {f : α → ℝ} {m s : ℝ}
    (h : Moments p f m s) (n : ℕ) :
    Moments (iidList p n) (listScore f)
      ((n:ℝ)*m) ((n:ℝ)*s+(n:ℝ)*((n:ℝ)-1)*m^2) := by
  induction n with
  | zero => simpa [iidList, listScore] using Moments.pure ([] : List α) (listScore f)
  | succ n ih =>
    have hi := Moments.independent_add h ih
    have hm := Moments.map (g := fun ab : α × List α => ab.1::ab.2) (f := listScore f) hi
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at hm
    change Moments (iidList p (n+1)) (listScore f)
      (m+(n:ℝ)*m) (s+2*m*((n:ℝ)*m)+((n:ℝ)*s+(n:ℝ)*((n:ℝ)-1)*m^2)) at hm
    convert hm using 1 <;> push_cast <;> ring

lemma iidMultiset_moments {α : Type*} {p : PMF α} {f : α → ℝ} {m s : ℝ}
    (h : Moments p f m s) (n : ℕ) :
    Moments ((iidList p n).map (fun as : List α => (as : Multiset α))) (multisetScore f)
      ((n:ℝ)*m) ((n:ℝ)*s+(n:ℝ)*((n:ℝ)-1)*m^2) := by
  apply Moments.map (g := fun as : List α => (as : Multiset α))
  simpa only [multisetScore_coe] using iidList_moments h n

 

lemma compound_moments {α : Type*} {p : PMF α} {f : α → ℝ} {m s d e : ℝ}
    {offspring : PMF ℕ} (hp : Moments p f m s)
    (hD : Moments offspring (fun k : ℕ => (k:ℝ)) d (e+d)) :
    Moments (offspring.bind (fun k =>
      (iidList p k).map (fun as : List α => (as : Multiset α)))) (multisetScore f)
      (d*m) (d*s+e*m^2) := by
  apply Moments.bind (fun k => iidMultiset_moments hp k)
  · exact ((hD.hasMean.mul_const s).add ((hD.square.sub hD.hasMean).mul_const (m^2))).congr
      (fun k => by ring)
  · rw [mean_mul_const, hD.first]
  · rw [mean_congr offspring (g := fun k => (k:ℝ)*s+((k:ℝ)^2-(k:ℝ))*m^2) (fun k => by ring),
      mean_add (hD.hasMean.mul_const s) ((hD.square.sub hD.hasMean).mul_const (m^2)),
      mean_mul_const, mean_mul_const, mean_sub hD.square hD.hasMean, hD.first, hD.second]
    ring

 

lemma mass_channel (lam : ℝ) (h : Admissible lam) (i j : Spin) :
    mass (channelPMF lam h i) j = channel lam i j := by
  exact ENNReal.toReal_ofReal (channel_nonneg h i j)

lemma channel_score (lam : ℝ) (h : Admissible lam) (i : Spin) :
    mean (channelPMF lam h i) spinScore = lam*spinScore i := by
  rw [mean_fintype]
  simp only [mass_channel]
  fin_cases i <;> simp [Fin.sum_univ_succ, channel, spinScore] <;> ring

 
theorem boundaryScore_moments (offspring : PMF ℕ) (d e lam : ℝ) (h : Admissible lam)
    (hD : Moments offspring (fun k : ℕ => (k:ℝ)) d (e+d)) (n : ℕ) (i : Spin) :
    Moments (observedLaw offspring lam h n i) (boundaryScore n)
      ((d*lam)^n*spinScore i) (scoreSecond d e lam h n i) := by
  induction n generalizing i with
  | zero =>
    change Moments (PMF.pure i) spinScore ((d*lam)^0*spinScore i) ((spinScore i)^2)
    simpa only [pow_zero, one_mul] using Moments.pure i spinScore
  | succ n ih =>
    have hedge : Moments ((channelPMF lam h i).bind (observedLaw offspring lam h n))
        (boundaryScore n) ((d*lam)^n*lam*spinScore i)
        (mean (channelPMF lam h i) (scoreSecond d e lam h n)) := by
      apply Moments.bind ih (hasMean_fintype _ _) ?_ rfl
      rw [mean_const_mul, channel_score]
      ring
    have hh := compound_moments hedge hD
    change Moments (observedLaw offspring lam h (n+1) i) (boundaryScore (n+1))
      (d*((d*lam)^n*lam*spinScore i)) (scoreSecond d e lam h (n+1) i) at hh
    convert hh using 1
    rw [pow_succ]
    ring

 

end ThreeState

namespace ThreeState

 
 

end ThreeState

namespace ThreeState

 

 

 

 

end ThreeState

end OAI

-- ---- platform node ----
open OAI OAI.ThreeState


theorem solution : type_of% @_root_.OAI.ThreeState.boundaryScore_moments := @_root_.OAI.ThreeState.boundaryScore_moments
