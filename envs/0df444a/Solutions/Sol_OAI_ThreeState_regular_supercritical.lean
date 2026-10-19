-- Prove2me | solution 1 for OAI.ThreeState.regular_supercritical
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:58:04.951253+00:00
-- url     : https://prove2.me/submissions/6cfaddc0-7638-4164-812e-d0dc611798e6

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Supercritical.lean:L354-L362
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ThreeState.regular_supercritical.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ThreeState_regular_supercritical) verbatim and is proved by it.
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
import Theorems.Thm_OAI_ThreeState_advantage_eq_tvMass
import Theorems.Thm_OAI_ThreeState_boundaryScore_moments
import Theorems.Thm_OAI_ThreeState_mean_bind
import Theorems.Thm_OAI_ThreeState_posteriorScore_square_le

-- ---- from OAI.Probability.ThreeState.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

lemma mass_bind {α β : Type*} (p : PMF α) (k : α → PMF β) (b : β) :
    mass (p.bind k) b = ∑' a, mass p a * mass (k a) b := by
  simp only [mass, PMF.bind_apply, ENNReal.tsum_toReal_eq
    (fun a => ENNReal.mul_ne_top (p.apply_ne_top a) ((k a).apply_ne_top b)), ENNReal.toReal_mul]

lemma mass_uniform (i : Spin) : mass uniformSpin i = 1/3 := by
  simp [mass, uniformSpin, PMF.ofFintype_apply]

lemma mass_marginal {α : Type*} (law : Spin → PMF α) (y : α) :
    mass (marginal law) y = (∑ i : Spin, mass (law i) y)/3 := by
  simp only [marginal, mass_bind, tsum_fintype, mass_uniform]
  rw [← Finset.mul_sum]
  ring

lemma mass_eq_zero {α : Type*} (p : PMF α) (a : α) : mass p a = 0 ↔ p a = 0 := by
  simp [mass, ENNReal.toReal_eq_zero_iff, p.apply_ne_top a]

lemma marginal_zero {α : Type*} (law : Spin → PMF α) (y : α)
    (h : marginal law y = 0) (i : Spin) : law i y = 0 := by
  apply (mass_eq_zero (law i) y).mp
  have hh : mass (marginal law) y = 0 := (mass_eq_zero _ _).mpr h
  rw [mass_marginal] at hh
  have hs : ∑ j : Spin, mass (law j) y = 0 := by linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mass_nonneg (law j) y)).mp hs i (by simp)

lemma posterior_nonneg {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    0 ≤ posterior law y i := by
  unfold posterior
  split_ifs <;> positivity

lemma posterior_sum {α : Type*} (law : Spin → PMF α) (y : α) :
    ∑ i : Spin, posterior law y i = 1 := by
  classical
  have hn := (marginal law).apply_ne_top y
  by_cases h : marginal law y = 0
  · simp [posterior, h]
  · have hm : mass (marginal law) y ≠ 0 := mt (mass_eq_zero _ _).mp h
    simp only [posterior, ite_eq_right h, ← Finset.sum_div]
    change (∑ i : Spin, mass (law i) y)/(3*mass (marginal law) y) = 1
    have he := mass_marginal law y
    field_simp
    linarith

 
lemma weighted_posterior {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    mass (marginal law) y * (posterior law y i-1/3) =
      (mass (law i) y-mass (marginal law) y)/3 := by
  classical
  by_cases h : marginal law y = 0
  · have hi := marginal_zero law y h i
    simp [mass, h, hi, posterior]
  · have hm : mass (marginal law) y ≠ 0 := mt (mass_eq_zero _ _).mp h
    simp only [posterior, ite_eq_right h]
    change mass (marginal law) y * (mass (law i) y / (3*mass (marginal law) y)-1/3) = _
    field_simp

lemma mass_le_one {α : Type*} (p : PMF α) (a : α) : mass p a ≤ 1 := by
  simpa [mass] using ENNReal.toReal_mono (by finiteness) (p.coe_le_one a)

lemma mass_diff_summable {α : Type*} (p q : PMF α) :
    Summable (fun a => |mass p a-mass q a|) :=
  ((mass_summable p).sub (mass_summable q)).abs

lemma tvMass_nonneg {α : Type*} (p q : PMF α) : 0 ≤ tvMass p q := by
  exact div_nonneg (tsum_nonneg (fun a => abs_nonneg _)) (by norm_num)

lemma tvMass_le_one {α : Type*} (p q : PMF α) : tvMass p q ≤ 1 := by
  have h := (mass_diff_summable p q).tsum_le_tsum
    (fun a => (abs_sub (mass p a) (mass q a)).trans_eq (by
      rw [abs_of_nonneg (mass_nonneg p a), abs_of_nonneg (mass_nonneg q a)]))
    ((mass_summable p).add (mass_summable q))
  rw [(mass_summable p).tsum_add (mass_summable q), mass_sum, mass_sum] at h
  dsimp [tvMass]
  linarith

lemma advantage_nonneg {α : Type*} (law : Spin → PMF α) : 0 ≤ advantage law := by
  rw [advantage_eq_tvMass]
  exact div_nonneg (Finset.sum_nonneg (fun i _ => tvMass_nonneg _ _)) (by norm_num)

lemma advantage_le_one {α : Type*} (law : Spin → PMF α) : advantage law ≤ 1 := by
  rw [advantage_eq_tvMass]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (i : Spin) _ => tvMass_le_one (law i) (marginal law))
  norm_num at h
  linarith

lemma kernel_mass_summable {α β : Type*} (p : PMF α) (k : α → PMF β) (b : β) :
    Summable (fun a => mass p a*mass (k a) b) := by
  apply Summable.of_nonneg_of_le (fun a => mul_nonneg (mass_nonneg p a) (mass_nonneg (k a) b))
    (fun a => mul_le_of_le_one_right (mass_nonneg p a) (mass_le_one (k a) b))
    (mass_summable p)

lemma weighted_kernel_summable {α β : Type*} (p q : PMF α) (k : α → PMF β) (b : β) :
    Summable (fun a => |mass p a-mass q a| *mass (k a) b) := by
  apply Summable.of_nonneg_of_le (fun a => mul_nonneg (abs_nonneg _) (mass_nonneg (k a) b))
    (fun a => mul_le_of_le_one_right (abs_nonneg _) (mass_le_one (k a) b))
    (mass_diff_summable p q)

lemma mass_diff_bind_le {α β : Type*} (p q : PMF α) (k : α → PMF β) (b : β) :
    |mass (p.bind k) b-mass (q.bind k) b| ≤
      ∑' a, |mass p a-mass q a| *mass (k a) b := by
  rw [mass_bind, mass_bind, ← (kernel_mass_summable p k b).tsum_sub (kernel_mass_summable q k b)]
  simp_rw [← sub_mul]
  have hnorm : Summable (fun a => ‖(mass p a-mass q a)*mass (k a) b‖) :=
    (weighted_kernel_summable p q k b).congr (fun a => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mass_nonneg (k a) b)])
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mass_nonneg (k _) b)] using
    norm_tsum_le_tsum_norm hnorm

lemma tvMass_bind_le {α β : Type*} (p q : PMF α) (k : α → PMF β) :
    tvMass (p.bind k) (q.bind k) ≤ tvMass p q := by
  have hrow (a : α) : (∑' b, |mass p a-mass q a| *mass (k a) b) =
      |mass p a-mass q a| := by
    rw [(mass_summable (k a)).tsum_mul_left, mass_sum, mul_one]
  have hs : Summable (Function.uncurry (fun a b => |mass p a-mass q a| *mass (k a) b)) := by
    apply (summable_prod_of_nonneg (fun ab => mul_nonneg (abs_nonneg _) (mass_nonneg _ _))).mpr
    change (∀ a, Summable (fun b => |mass p a-mass q a| * mass (k a) b)) ∧
      Summable (fun a => ∑' b, |mass p a-mass q a| * mass (k a) b)
    constructor
    · intro a
      exact (mass_summable (k a)).mul_left |mass p a-mass q a|
    ·
      simpa only [hrow] using mass_diff_summable p q
  have h := Summable.tsum_le_tsum (mass_diff_bind_le p q k)
    (mass_diff_summable (p.bind k) (q.bind k)) hs.prod_symm.prod
  rw [hs.tsum_comm] at h
  simp_rw [hrow] at h
  exact div_le_div_of_nonneg_right h (by norm_num)

lemma marginal_bind {α β : Type*} (law : Spin → PMF α) (k : α → PMF β) :
    marginal (fun i => (law i).bind k) = (marginal law).bind k := by
  simp only [marginal, PMF.bind_bind]

 
theorem advantage_bind_le {α β : Type*} (law : Spin → PMF α) (k : α → PMF β) :
    advantage (fun i => (law i).bind k) ≤ advantage law := by
  rw [advantage_eq_tvMass, advantage_eq_tvMass, marginal_bind]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => tvMass_bind_le (law i) (marginal law) k))
    (by norm_num)

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

lemma hasMean_fintype {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) : HasMean p f :=
  summable_of_hasFiniteSupport (Set.toFinite _)

lemma mean_fintype {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) :
    mean p f = ∑ a, mass p a * f a := tsum_fintype _

 

lemma Moments.hasMean {α : Type*} {p : PMF α} {f : α → ℝ} {m s : ℝ}
    (h : Moments p f m s) : HasMean p f := hasMean_of_square h.square

lemma Moments.pure {α : Type*} (a : α) (f : α → ℝ) :
    Moments (PMF.pure a) f (f a) ((f a)^2) :=
  ⟨hasMean_pure _ _, mean_pure _ _, mean_pure _ _⟩

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

end ThreeState
namespace ThreeState

 
end ThreeState

namespace ThreeState

 
lemma regular_moments (b : ℕ) :
    Moments (PMF.pure b) (fun k : ℕ => (k : ℝ)) (b:ℝ) ((b:ℝ)^2) :=
  Moments.pure b _

end ThreeState

end OAI

-- ---- from OAI.Probability.ThreeState.Observation ----
namespace OAI

/-! Ordered and unlabelled boundary observations and information degradation. -/

namespace ThreeState

 

 
end ThreeState

namespace ThreeState

end ThreeState
universe u
namespace ThreeState

lemma list_traverse_nil {α β : Type u} (k : α → PMF β) :
    Traversable.traverse k [] = PMF.pure [] := rfl

lemma list_traverse_cons {α β : Type u} (k : α → PMF β) (a : α) (as : List α) :
    Traversable.traverse k (a::as) = (k a).bind (fun b => (Traversable.traverse k as).map (List.cons b)) := by
  rw [List.traverse_cons, seq_eq_bind_map]
  change ((k a).map List.cons).bind _ = _
  rw [PMF.bind_map]
  rfl

lemma iidList_bind_traverse {α β : Type u} (p : PMF α) (k : α → PMF β) (n : ℕ) :
    (iidList p n).bind (Traversable.traverse k) = iidList (p.bind k) n := by
  induction n with
  | zero => simp only [iidList, PMF.pure_bind, list_traverse_nil]
  | succ n ih =>
    simp only [iidList, PMF.bind_bind, PMF.bind_map, Function.comp_def, list_traverse_cons]
    apply congrArg (PMF.bind p)
    funext a
    rw [PMF.bind_comm]
    apply congrArg (PMF.bind (k a))
    funext b
    rw [← PMF.map_bind, ih]

lemma iidList_multiset_bind {α β : Type u} (p : PMF α) (k : α → PMF β) (n : ℕ) :
    ((iidList p n).map (fun as : List α => (as : Multiset α))).bind (Multiset.traverse k) =
      (iidList (p.bind k) n).map (fun bs : List β => (bs : Multiset β)) := by
  rw [PMF.bind_map]
  change (iidList p n).bind (fun as => ((Traversable.traverse k as).map (fun bs : List β => (bs : Multiset β)))) = _
  rw [← PMF.map_bind, iidList_bind_traverse]

 

 
theorem observedLaw_grow (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) :
    (observedLaw offspring lam h n i).bind (grow offspring lam h n) =
      observedLaw offspring lam h (n+1) i := by
  induction n generalizing i with
  | zero => exact PMF.pure_bind i _
  | succ n ih =>
    change (offspring.bind (fun k =>
      (iidList ((channelPMF lam h i).bind (observedLaw offspring lam h n)) k).map
        (fun xs : List (Observation n) => (xs : Multiset (Observation n))))).bind
        (Multiset.traverse (grow offspring lam h n)) =
      offspring.bind (fun k =>
        (iidList ((channelPMF lam h i).bind (observedLaw offspring lam h (n+1))) k).map
          (fun xs : List (Observation (n+1)) => (xs : Multiset (Observation (n+1)))))
    rw [PMF.bind_bind]
    apply congrArg (PMF.bind offspring)
    funext k
    rw [iidList_multiset_bind, PMF.bind_bind]
    have he : (fun j => (observedLaw offspring lam h n j).bind (grow offspring lam h n)) =
        observedLaw offspring lam h (n+1) := funext ih
    rw [he]

 
theorem observedAdvantage_antitone (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    Antitone (fun n => advantage (observedLaw offspring lam h n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have he : observedLaw offspring lam h (n+1) =
      fun i => (observedLaw offspring lam h n i).bind (grow offspring lam h n) := by
    funext i
    exact (observedLaw_grow offspring lam h n i).symm
  rw [he]
  exact advantage_bind_le _ _

 
theorem observedAdvantage_tendsto (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    ∃ L : ℝ, 0 ≤ L ∧ L ≤ 1 ∧
      Filter.Tendsto (fun n => advantage (observedLaw offspring lam h n))
        Filter.atTop (nhds L) := by
  let a := fun n => advantage (observedLaw offspring lam h n)
  have hb : BddBelow (Set.range a) := ⟨0, by rintro x ⟨n,rfl⟩; exact advantage_nonneg _⟩
  refine ⟨⨅ n, a n, ?_, ?_, tendsto_atTop_ciInf (observedAdvantage_antitone offspring lam h) hb⟩
  · exact le_ciInf (fun n => advantage_nonneg _)
  · exact (ciInf_le hb 0).trans (advantage_le_one _)

end ThreeState

end OAI

-- ---- from OAI.Probability.ThreeState.Supercritical ----
namespace OAI

/-! Boundary score moments and reconstruction above the Kesten–Stigum threshold. -/

namespace ThreeState

 

 

lemma mass_channel (lam : ℝ) (h : Admissible lam) (i j : Spin) :
    mass (channelPMF lam h i) j = channel lam i j := by
  exact ENNReal.toReal_ofReal (channel_nonneg h i j)

 
lemma mean_uniform (f : Spin → ℝ) : mean uniformSpin f = (∑ i : Spin, f i)/3 := by
  rw [mean_fintype]
  simp only [mass_uniform, ← Finset.mul_sum]
  ring

lemma mean_uniform_spinScore : mean uniformSpin spinScore = 0 := by
  simp [mean_uniform, Fin.sum_univ_succ, spinScore]

lemma mean_uniform_spinScore_square : mean uniformSpin (fun i => (spinScore i)^2) = 2 := by
  norm_num [mean_uniform, Fin.sum_univ_succ, spinScore]

lemma mean_uniform_channel (lam : ℝ) (h : Admissible lam) (f : Spin → ℝ) :
    mean uniformSpin (fun i => mean (channelPMF lam h i) f) = mean uniformSpin f := by
  simp [mean_fintype, mass_uniform, mass_channel, Fin.sum_univ_succ, channel]
  ring

lemma pow_square_comm (a : ℝ) (n : ℕ) : (a^n)^2 = (a^2)^n := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]

lemma scoreSecond_average_zero (d e lam : ℝ) (h : Admissible lam) :
    mean uniformSpin (scoreSecond d e lam h 0) = 2 := mean_uniform_spinScore_square

lemma scoreSecond_average_succ (d e lam : ℝ) (h : Admissible lam) (n : ℕ) :
    mean uniformSpin (scoreSecond d e lam h (n+1)) =
      d*mean uniformSpin (scoreSecond d e lam h n)+2*e*lam^2*((d*lam)^2)^n := by
  change mean uniformSpin (fun i =>
    d*mean (channelPMF lam h i) (scoreSecond d e lam h n) +
      e*((d*lam)^n*lam*spinScore i)^2) = _
  rw [mean_add (hasMean_fintype _ _) (hasMean_fintype _ _), mean_const_mul,
    mean_uniform_channel]
  congr 1
  rw [mean_congr uniformSpin (g := fun i => (e*lam^2*((d*lam)^2)^n)*(spinScore i)^2)
    (fun i => by rw [mul_pow, mul_pow, pow_square_comm]; ring), mean_const_mul,
    mean_uniform_spinScore_square]
  ring

 

lemma scoreSecond_bound (d e lam C : ℝ) (h : Admissible lam)
    (hd : 0 ≤ d) (hC : 2 ≤ C) (hstep : d*C+2*e*lam^2 ≤ C*(d*lam)^2) (n : ℕ) :
    mean uniformSpin (scoreSecond d e lam h n) ≤ C*((d*lam)^2)^n := by
  induction n with
  | zero => simpa only [scoreSecond_average_zero, pow_zero, mul_one] using hC
  | succ n ih =>
    rw [scoreSecond_average_succ, pow_succ ((d*lam)^2) n]
    have h1 := mul_le_mul_of_nonneg_left ih hd
    have h2 := mul_le_mul_of_nonneg_right hstep (pow_nonneg (sq_nonneg (d*lam)) n)
    nlinarith

lemma boundaryScore_marginal_moments (offspring : PMF ℕ) (d e lam : ℝ) (h : Admissible lam)
    (hD : Moments offspring (fun k : ℕ => (k:ℝ)) d (e+d)) (n : ℕ) :
    Moments (marginal (observedLaw offspring lam h n)) (boundaryScore n) 0
      (mean uniformSpin (scoreSecond d e lam h n)) := by
  apply Moments.bind (fun i => boundaryScore_moments offspring d e lam h hD n i)
    (hasMean_fintype _ _) ?_ rfl
  rw [mean_const_mul, mean_uniform_spinScore, mul_zero]

end ThreeState

namespace ThreeState

lemma HasMean.mul_of_square {α : Type*} {p : PMF α} {f g : α → ℝ}
    (hf : HasMean p (fun a => (f a)^2)) (hg : HasMean p (fun a => (g a)^2)) :
    HasMean p (fun a => f a*g a) := by
  apply HasMean.of_abs
  apply ((hf.add hg).mul_const (1/2)).mono (fun a => abs_nonneg _)
  intro a
  rw [abs_mul]
  nlinarith [sq_nonneg (|f a|-|g a|), sq_abs (f a), sq_abs (g a)]

 
lemma mean_cauchy_square {α : Type*} {p : PMF α} {f g : α → ℝ}
    (hf : HasMean p (fun a => (f a)^2)) (hg : HasMean p (fun a => (g a)^2)) :
    (mean p (fun a => f a*g a))^2 ≤
      mean p (fun a => (f a)^2)*mean p (fun a => (g a)^2) := by
  have hfg := hf.mul_of_square hg
  have hp (t : ℝ) : 0 ≤ mean p (fun a => (g a)^2)*(t*t) +
      (-2*mean p (fun a => f a*g a))*t + mean p (fun a => (f a)^2) := by
    have hn := mean_nonneg p (fun a => sq_nonneg (f a-t*g a))
    have he : mean p (fun a => (f a-t*g a)^2) =
        mean p (fun a => (g a)^2)*(t*t) +
        (-2*mean p (fun a => f a*g a))*t + mean p (fun a => (f a)^2) := by
      rw [mean_congr p (g := fun a => (g a)^2*(t*t)+(f a*g a)*(-2*t)+(f a)^2)
        (fun a => by ring),
        mean_add ((hg.mul_const (t*t)).add (hfg.mul_const (-2*t))) hf,
        mean_add (hg.mul_const (t*t)) (hfg.mul_const (-2*t)), mean_mul_const, mean_mul_const]
      ring
    rwa [he] at hn
  have hd := discrim_le_zero hp
  dsimp [discrim] at hd
  nlinarith

lemma posterior_le_one {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    posterior law y i ≤ 1 := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => posterior_nonneg law y j)
    (Finset.mem_univ i)
  simpa only [posterior_sum] using h

lemma posteriorTV_nonneg {α : Type*} (law : Spin → PMF α) (y : α) :
    0 ≤ posteriorTV law y := by
  exact div_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) (by norm_num)

lemma posteriorTV_le_two {α : Type*} (law : Spin → PMF α) (y : α) :
    posteriorTV law y ≤ 2 := by
  have hh (i : Spin) : |posterior law y i-1/3| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [posterior_nonneg law y i, posterior_le_one law y i]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  norm_num at h
  dsimp [posteriorTV]
  linarith

lemma hasMean_posteriorTV {α : Type*} (law : Spin → PMF α) :
    HasMean (marginal law) (posteriorTV law) :=
  (hasMean_const (marginal law) 2).mono (posteriorTV_nonneg law) (posteriorTV_le_two law)

lemma mean_posteriorTV {α : Type*} (law : Spin → PMF α) :
    mean (marginal law) (posteriorTV law) = advantage law := rfl

lemma hasMean_posteriorScore_square {α : Type*} (law : Spin → PMF α) :
    HasMean (marginal law) (fun y => (posteriorScore law y)^2) :=
  ((hasMean_posteriorTV law).const_mul 12).mono
    (fun y => sq_nonneg (posteriorScore law y)) (posteriorScore_square_le law)

lemma mean_posteriorScore_square_le {α : Type*} (law : Spin → PMF α) :
    mean (marginal law) (fun y => (posteriorScore law y)^2) ≤ 12*advantage law := by
  have h := mean_le (hasMean_posteriorScore_square law) ((hasMean_posteriorTV law).const_mul 12)
    (posteriorScore_square_le law)
  simpa only [mean_const_mul, mean_posteriorTV] using h

lemma weighted_posteriorScore {α : Type*} (law : Spin → PMF α) (y : α) :
    mass (marginal law) y*posteriorScore law y = mass (law 0) y-mass (marginal law) y := by
  have h := weighted_posterior law y 0
  dsimp [posteriorScore]
  linarith

lemma mean_score_correlation {α : Type*} (law : Spin → PMF α) (f : α → ℝ)
    (h0 : HasMean (law 0) f) (hm : HasMean (marginal law) f) :
    mean (marginal law) (fun y => posteriorScore law y*f y) = mean (law 0) f-mean (marginal law) f := by
  unfold mean
  rw [← h0.tsum_sub hm]
  apply tsum_congr
  intro y
  rw [← mul_assoc, weighted_posteriorScore]
  ring

 

theorem advantage_lower_from_score {α : Type*} (law : Spin → PMF α) (f : α → ℝ)
    (h0 : HasMean (law 0) f) (hf : HasMean (marginal law) (fun y => (f y)^2)) :
    (mean (law 0) f-mean (marginal law) f)^2 ≤
      12*advantage law*mean (marginal law) (fun y => (f y)^2) := by
  have h := mean_cauchy_square (hasMean_posteriorScore_square law) hf
  rw [mean_score_correlation law f h0 (hasMean_of_square hf)] at h
  exact h.trans (mul_le_mul_of_nonneg_right (mean_posteriorScore_square_le law)
    (mean_nonneg _ (fun y => sq_nonneg _)))

end ThreeState

namespace ThreeState

 

lemma supercritical_advantage_bound (offspring : PMF ℕ) (d e lam C : ℝ)
    (h : Admissible lam) (hD : Moments offspring (fun k : ℕ => (k:ℝ)) d (e+d))
    (hd : 0 ≤ d) (hq : 0 < (d*lam)^2) (hC : 2 ≤ C)
    (hstep : d*C+2*e*lam^2 ≤ C*(d*lam)^2) (n : ℕ) :
    1/(3*C) ≤ advantage (observedLaw offspring lam h n) := by
  have hm := boundaryScore_marginal_moments offspring d e lam h hD n
  have h0 := boundaryScore_moments offspring d e lam h hD n (0:Spin)
  have hc := advantage_lower_from_score (observedLaw offspring lam h n) (boundaryScore n)
    h0.hasMean hm.square
  rw [h0.first, hm.first, hm.second] at hc
  have hs := scoreSecond_bound d e lam C h hd hC hstep n
  have ha := advantage_nonneg (observedLaw offspring lam h n)
  have hp := pow_pos hq n
  have hu := mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0:ℝ) ≤ 12) ha)
  have he : (((d*lam)^n*spinScore (0:Spin))-0)^2 = 4*((d*lam)^2)^n := by
    simp only [spinScore, ↓reduceIte, sub_zero, mul_pow, pow_square_comm]
    ring
  rw [he] at hc
  have hh : (4:ℝ)*((d*lam)^2)^n ≤
      (12*C*advantage (observedLaw offspring lam h n))*((d*lam)^2)^n := by
    calc
      _ ≤ 12*advantage (observedLaw offspring lam h n) *
          (C*((d*lam)^2)^n) := hc.trans hu
      _ = _ := by ring
  have hh' := (mul_le_mul_iff_left₀ hp).mp hh
  apply (div_le_iff₀ (show 0 < 3*C by linarith)).mpr
  nlinarith

 

theorem reconstructs_supercritical_of_moments (offspring : PMF ℕ) (d e lam : ℝ)
    (h : Admissible lam) (hD : Moments offspring (fun k : ℕ => (k:ℝ)) d (e+d))
    (hd : 0 < d) (he : 0 ≤ e) (hcrit : 1 < d*lam^2) :
    Reconstructs (fun n => advantage (observedLaw offspring lam h n)) := by
  have hgap : 0 < (d*lam)^2-d := by
    have hp := mul_pos hd (sub_pos.mpr hcrit)
    nlinarith
  have hq : 0 < (d*lam)^2 := by linarith
  let C : ℝ := 2+2*e*lam^2/((d*lam)^2-d)
  have hC : 2 ≤ C := by
    dsimp [C]
    have hh : 0 ≤ 2*e*lam^2/((d*lam)^2-d) := by positivity
    linarith
  have hCpos : 0 < C := by linarith
  have hCeq : C*((d*lam)^2-d) = 2*((d*lam)^2-d)+2*e*lam^2 := by
    dsimp [C]
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hgap)]
  have hstep : d*C+2*e*lam^2 ≤ C*(d*lam)^2 := by nlinarith
  obtain ⟨L,hL0,hL1,hL⟩ := observedAdvantage_tendsto offspring lam h
  have hb : 1/(3*C) ≤ L := ge_of_tendsto' hL
    (fun n => supercritical_advantage_bound offspring d e lam C h hD hd.le hq hC hstep n)
  exact ⟨L, (by positivity : 0 < 1/(3*C)).trans_le hb, hL⟩

 

theorem regular_supercritical (b : ℕ) (hb : 2 ≤ b) (lam : ℝ) (h : Admissible lam)
    (hcrit : 1 < (b:ℝ)*lam^2) : Reconstructs (regularAdvantage b lam h) := by
  have hd : 0 < (b:ℝ) := by exact_mod_cast (show 0 < b by omega)
  have he : 0 ≤ (b:ℝ)^2-(b:ℝ) := by
    have hb' : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
    nlinarith
  apply reconstructs_supercritical_of_moments (PMF.pure b) (b:ℝ) ((b:ℝ)^2-(b:ℝ)) lam h
    ?_ hd he hcrit
  simpa only [sub_add_cancel] using regular_moments b

 

end ThreeState

end OAI

-- ---- mission target ----
open OAI OAI.ThreeState

namespace OAI
namespace ThreeState
theorem _root_.solution (b : ℕ) (hb : 2 ≤ b) (lam : ℝ) (h : Admissible lam)
    (hcrit : 1 < (b : ℝ) * lam ^ 2) : Reconstructs (regularAdvantage b lam h) := by
  first
    | exact OAI.ThreeState.regular_supercritical b hb lam h hcrit
    | exact OAI.ThreeState.regular_supercritical
    | (apply OAI.ThreeState.regular_supercritical <;> assumption)
    | (intros; apply OAI.ThreeState.regular_supercritical <;> assumption)
end ThreeState
end OAI
