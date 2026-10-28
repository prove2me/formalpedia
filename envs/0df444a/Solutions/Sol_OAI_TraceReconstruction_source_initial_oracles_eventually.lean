-- Prove2me | solution 1 for OAI.TraceReconstruction.source_initial_oracles_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:02:26.721439+00:00
-- url     : https://prove2.me/submissions/33d26b1c-83f2-409f-9042-c3b9c522e7bc

import Mathlib
import Definitions.Def_OAIQ9Tr002
import Theorems.Thm_OAI_TraceReconstruction_actual_initial_oracles

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Scales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scales

Exact block exponents, deletion reduction, induction depth, backward target scales, and uniform power absorption.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


open Filter
open scoped Topology

open Filter
open scoped Topology


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology

variable {N f g : ℕ → ℝ} {a b : ℝ}

theorem PowerRate.congr (h : PowerRate N f a) (he : f =ᶠ[Filter.atTop] g) : PowerRate N g a := by
  constructor
  · filter_upwards [h.1,he] with t ht he; simpa [←he] using ht
  · exact h.2.congr' (he.mono fun t ht => by simp [ht])

theorem PowerRate.const (hN : Tendsto N Filter.atTop Filter.atTop) {c : ℝ} (hc : 0 < c) :
    PowerRate N (fun _ => c) 0 := by
  exact ⟨Eventually.of_forall (fun _ => hc), (Real.tendsto_log_atTop.comp hN).const_div_atTop _⟩

theorem PowerRate.base (hN : Tendsto N Filter.atTop Filter.atTop) : PowerRate N N 1 := by
  have hn := hN.eventually_gt_atTop 1
  refine ⟨hn.mono fun _ h => by linarith, ?_⟩
  apply tendsto_congr' _ |>.mpr tendsto_const_nhds
  filter_upwards [hn] with t ht
  exact div_self (ne_of_gt (Real.log_pos ht))

theorem PowerRate.mul (hf : PowerRate N f a) (hg : PowerRate N g b) :
    PowerRate N (fun t => f t*g t) (a+b) := by
  refine ⟨by filter_upwards [hf.1,hg.1] with t h ht; positivity, ?_⟩
  apply (hf.2.add hg.2).congr'
  filter_upwards [hf.1,hg.1] with t h ht
  rw [Real.log_mul h.ne' ht.ne',add_div]

theorem PowerRate.div (hf : PowerRate N f a) (hg : PowerRate N g b) :
    PowerRate N (fun t => f t/g t) (a-b) := by
  refine ⟨by filter_upwards [hf.1,hg.1] with t h ht; positivity, ?_⟩
  apply (hf.2.sub hg.2).congr'
  filter_upwards [hf.1,hg.1] with t h ht
  rw [Real.log_div h.ne' ht.ne',sub_div]

theorem PowerRate.rpow (hf : PowerRate N f a) (c : ℝ) :
    PowerRate N (fun t => (f t)^c) (a*c) := by
  refine ⟨by filter_upwards [hf.1] with t h; positivity, ?_⟩
  apply (hf.2.mul_const c).congr'
  filter_upwards [hf.1] with t h
  rw [Real.log_rpow h]
  ring

theorem PowerRate.pow (hf : PowerRate N f a) (c : ℕ) :
    PowerRate N (fun t => (f t)^c) (a*c) := by
  simpa only [Real.rpow_natCast] using hf.rpow (c:ℝ)

theorem PowerRate.sqrt (hf : PowerRate N f a) :
    PowerRate N (fun t => Real.sqrt (f t)) (a/2) := by
  simpa only [Real.sqrt_eq_rpow,div_eq_mul_inv, one_mul] using hf.rpow (1/2:ℝ)

theorem PowerRate.inv (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a) :
    PowerRate N (fun t=>(f t)⁻¹) (-a) := by
  simpa only [one_div,zero_sub] using (PowerRate.const hN (by norm_num : (0:ℝ)<1)).div hf

theorem PowerRate.const_mul (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a)
    {c : ℝ} (hc : 0 < c) : PowerRate N (fun t=>c*f t) a := by
  simpa only [zero_add] using (PowerRate.const hN hc).mul hf

theorem PowerRate.mul_const (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a)
    {c : ℝ} (hc : 0 < c) : PowerRate N (fun t=>f t*c) a := by
  simpa only [add_zero] using hf.mul (PowerRate.const hN hc)

theorem PowerRate.div_const (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a)
    {c : ℝ} (hc : 0 < c) : PowerRate N (fun t=>f t/c) a := by
  simpa only [sub_zero] using hf.div (PowerRate.const hN hc)

theorem PowerRate.upper (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a) :
    PowerUpper N f a := by
  intro b hb
  filter_upwards [hN.eventually_gt_atTop 1,hf.1,hf.2.eventually_lt_const hb] with t hn hp hab
  rw [abs_of_pos hp,←Real.log_le_log_iff hp (Real.rpow_pos_of_pos (by linarith) b),Real.log_rpow (by linarith : 0<N t)]
  exact (div_lt_iff₀ (Real.log_pos hn)).mp hab |>.le

theorem PowerRate.lower (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a) {c : ℝ}
    (hc : c<a) : ∀ᶠ t in Filter.atTop, (N t)^c ≤ f t := by
  filter_upwards [hN.eventually_gt_atTop 1,hf.1,hf.2.eventually_const_lt hc] with t hn hp hac
  rw [←Real.log_le_log_iff (Real.rpow_pos_of_pos (by linarith) c) hp, Real.log_rpow (by linarith : 0<N t)]
  exact (lt_div_iff₀ (Real.log_pos hn)).mp hac |>.le

theorem PowerRate.tendsto_atTop (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a) (ha : 0<a) :
    Tendsto f Filter.atTop Filter.atTop := by
  exact tendsto_atTop_mono' Filter.atTop (hf.lower hN (show a/2<a by linarith))
    ((tendsto_rpow_atTop (show 0<a/2 by linarith)).comp hN)

theorem PowerUpper.mono (hf : PowerUpper N f a) (hab : a≤b) : PowerUpper N f b :=
  fun c hc => hf c (lt_of_le_of_lt hab hc)

theorem PowerUpper.of_abs_le (hg : PowerUpper N g a) (h : ∀ᶠ t in Filter.atTop, |f t|≤|g t|) :
    PowerUpper N f a := by
  intro b hb
  filter_upwards [hg b hb,h] with t ht hh
  exact hh.trans ht

theorem PowerUpper.zero (hN : Tendsto N Filter.atTop Filter.atTop) (a : ℝ) : PowerUpper N (fun _=>0) a := by
  intro b hb
  filter_upwards [hN.eventually_gt_atTop 0] with t ht
  simpa using (Real.rpow_pos_of_pos ht b).le

theorem PowerUpper.mul (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerUpper N f a)
    (hg : PowerUpper N g b) : PowerUpper N (fun t=>f t*g t) (a+b) := by
  intro c hc
  let δ := (c-(a+b))/2
  have hd : 0<δ := by dsimp [δ]; linarith
  filter_upwards [hN.eventually_gt_atTop 0,hf (a+δ) (by linarith),hg (b+δ) (by linarith)] with t hn ht hs
  calc |f t*g t|=|f t| * |g t| := abs_mul _ _
       _ ≤ (N t)^(a+δ)*(N t)^(b+δ) := mul_le_mul ht hs (abs_nonneg _) (by positivity)
       _ = (N t)^c := by rw [←Real.rpow_add hn]; congr 1; dsimp [δ]; ring

theorem PowerUpper.pow (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerUpper N f a)
    (r : ℕ) : PowerUpper N (fun t=>(f t)^r) (a*r) := by
  induction r with
  | zero => simpa using (PowerRate.const hN (by norm_num : (0:ℝ)<1)).upper hN
  | succ r ih =>
    have H := ih.mul hN hf
    convert H using 1
    · ext t; exact pow_succ _ _
    · push_cast; ring

theorem PowerUpper.add (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerUpper N f a)
    (hg : PowerUpper N g a) : PowerUpper N (fun t=>f t+g t) a := by
  intro c hc
  let d := (a+c)/2
  have had : a<d := by dsimp [d]; linarith
  have hdc : d < c := by dsimp [d]; linarith
  have hpow := ((tendsto_rpow_atTop (sub_pos.mpr hdc)).comp hN).eventually_ge_atTop 2
  filter_upwards [hN.eventually_gt_atTop 0,hf d had,hg d had,hpow] with t hn hf hg hp
  calc |f t+g t| ≤ |f t|+|g t| := abs_add_le _ _
       _ ≤ 2*(N t)^d := by linarith
       _ ≤ (N t)^(c-d)*(N t)^d := mul_le_mul_of_nonneg_right hp (by positivity)
       _ = (N t)^c := by rw [←Real.rpow_add hn]; congr 1; ring

theorem PowerUpper.sum {ι : Type*} (hN : Tendsto N Filter.atTop Filter.atTop) (S : Finset ι)
    (f : ι→ℕ→ℝ) (h : ∀i∈S, PowerUpper N (f i) a) :
    PowerUpper N (fun t=>∑i∈S,f i t) a := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using PowerUpper.zero hN a
  | @insert i S hi ih =>
    have hh := (h i (Finset.mem_insert_self _ _)).add hN
      (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using hh

theorem PowerRate.add_const (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a)
    (ha : 0<a) {c : ℝ} (hc : 0 ≤ c) : PowerRate N (fun t=>f t+c) a := by
  have ht := hf.tendsto_atTop hN ha
  have hratio : Tendsto (fun t=>1+c/f t) Filter.atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add (ht.const_div_atTop c))
  have hl : Tendsto (fun t=>Real.log (1+c/f t)/Real.log (N t)) Filter.atTop (𝓝 0) :=
    (hratio.log one_ne_zero).div_atTop (Real.tendsto_log_atTop.comp hN)
  refine ⟨by filter_upwards [hf.1] with t h; positivity, ?_⟩
  have H := hf.2.add hl
  simp only [add_zero] at H
  apply H.congr'
  filter_upwards [hf.1] with t hp
  have hh : 0<1+c/f t := by positivity
  rw [←add_div,←Real.log_mul hp.ne' hh.ne']
  congr 2
  field_simp

theorem PowerRate.of_tendsto (hN : Tendsto N Filter.atTop Filter.atTop)
    {c : ℝ} (hc : 0 < c) (hf : Tendsto f Filter.atTop (𝓝 c)) : PowerRate N f 0 := by
  exact ⟨hf.eventually_const_lt hc,(hf.log hc.ne').div_atTop (Real.tendsto_log_atTop.comp hN)⟩

theorem PowerUpper.tendsto_zero (hN : Tendsto N Filter.atTop Filter.atTop)
    (hf : PowerUpper N f a) (ha : a<0) : Tendsto f Filter.atTop (𝓝 0) := by
  have H := (tendsto_rpow_neg_atTop (show 0< -(a/2) by linarith)).comp hN
  simp only [neg_neg] at H
  exact squeeze_zero_norm' (by simpa only [Real.norm_eq_abs,Function.comp_apply] using hf (a/2) (by linarith)) H

theorem PowerRate.of_ratio (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a)
    {c : ℝ} (hc : 0 < c) (hr : Tendsto (fun t=>g t/f t) Filter.atTop (𝓝 c)) : PowerRate N g a := by
  have hp : ∀ᶠ t in Filter.atTop, 0<g t := by
    filter_upwards [hf.1,hr.eventually_const_lt hc] with t ht hgt
    exact (div_pos_iff.mp hgt).resolve_right (by intro h; linarith [h.2]) |>.1
  refine ⟨hp,?_⟩
  have hh := (hr.log hc.ne').div_atTop (Real.tendsto_log_atTop.comp hN)
  have H := hf.2.add hh
  simp only [add_zero] at H
  apply H.congr'
  filter_upwards [hf.1,hp] with t hf hg
  simp only [Function.comp_apply]
  rw [Real.log_div hg.ne' hf.ne']
  ring

theorem PowerRate.nat_floor (hN : Tendsto N Filter.atTop Filter.atTop) (hf : PowerRate N f a)
    (ha : 0<a) : PowerRate N (fun t=>(⌊f t⌋₊:ℝ)) a := by
  exact hf.of_ratio hN (by norm_num : (0:ℝ)<1)
    (tendsto_nat_floor_div_atTop.comp (hf.tendsto_atTop hN ha))

theorem PowerRate.exp_neg_upper (hN : Tendsto N Filter.atTop Filter.atTop)
    (hf : PowerRate N f a) (ha : 0<a) (c : ℝ) :
    PowerUpper N (fun t=>Real.exp (-f t)) c := by
  intro b hb
  have hh := ((isLittleO_log_rpow_atTop (show 0<a/2 by linarith)).tendsto_div_nhds_zero).comp hN
  have hsmall := (hh.const_mul (-b)).eventually_lt_const (show (-b)*0<1 by simp)
  filter_upwards [hN.eventually_gt_atTop 0,hf.lower hN (show a/2<a by linarith),hsmall] with t hn hl hs
  rw [abs_of_pos (Real.exp_pos _),Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  have hpos := Real.rpow_pos_of_pos hn (a/2)
  have hle : -b*Real.log (N t) ≤ (N t)^(a/2) := by
    have H := (div_lt_iff₀ hpos).mp (show (-b*Real.log (N t))/(N t)^(a/2)<1 by simpa only [mul_div_assoc,Function.comp_apply] using hs)
    linarith
  linarith

end TraceReconstruction

end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Ranks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ranks

Retained subsets, conditional rank experiments, tagged gaps, period geometry, Gaussian Schur estimates, and uniform square sums.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


namespace TraceReconstruction

theorem rankSchurConstant_pos : 0 < rankSchurConstant := by
  have hρ : Real.exp (-(1/1024:ℝ)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  unfold rankSchurConstant
  positivity

end TraceReconstruction

end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Differences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Differences

Tensor gap differences, positional shifts, two-gap elimination, central clipping, disjoint rank regions, and weighted period sums.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section



noncomputable section



noncomputable section



noncomputable section
namespace TraceReconstruction

/-- Constant middle-period tags admit every independent left/unchanged/right
choice without violating slot order or either end boundary. -/
theorem constant_period_safe {u m r : ℕ} (off : Fin m)
    (hoff₁ : 1 ≤ off.val) (hoff₂ : off.val+1 < m) (hm : 3 ≤ m)
    (j : Fin r → Fin u) (hj : StrictMono j) :
    SafeTaggedTuple (periodSlot (fun _ => off) ∘ j) := by
  constructor
  · intro i
    change 1 ≤ (j i).val*m+off.val ∧ (j i).val*m+off.val+1 < u*m
    constructor
    · omega
    · have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt (j i).isLt)
      rw [Nat.succ_mul] at h
      omega
  · intro i h hih
    change (j i).val*m+off.val+3 ≤ (j h).val*m+off.val
    have h := Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr (hj hih))
    rw [Nat.succ_mul] at h
    omega

end TraceReconstruction


noncomputable section

open Filter
open scoped Topology

noncomputable section
noncomputable section
noncomputable section


noncomputable section


noncomputable section


noncomputable section
open scoped Classical


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem difference_order_eq_counts {r : ℕ} (k : Fin r → GapDifference) :
    (∑ h, (k h).order)=firstDifferenceCount k+2*secondDifferenceCount k := by
  classical
  have hd (h) : (k h).order=(if k h=.first then 1 else 0)+
      2*(if k h=.second then 1 else 0) := by cases k h <;> simp [GapDifference.order]
  simp_rw [hd]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  simp [firstDifferenceCount,secondDifferenceCount]

/-- The only signed pattern of order below three is the singleton D term. -/
theorem odd_pattern_linear_or_order_three {r : ℕ} (k : Fin r → GapDifference)
    (hk : Odd (firstDifferenceCount k)) :
    (firstDifferenceCount k=1 ∧ secondDifferenceCount k=0) ∨
      3≤∑ h, (k h).order := by
  rw [difference_order_eq_counts]
  obtain ⟨n,hn⟩ := hk
  omega

end TraceReconstruction


end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Patterns

Pattern serialization, motif norms, flag posteriors, signed rank coefficients, translated binomials, and support geometry.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem first_second_counts_linear {r : ℕ} (k : Fin r → GapDifference)
    (h1 : firstDifferenceCount k=1) (h2 : secondDifferenceCount k=0) :
    ∃ a : Fin r, k=linearPattern a := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h1
  refine ⟨a,funext fun b => ?_⟩
  have hfirst : k b = .first ↔ b=a := by
    have hh := congrArg (fun A : Finset (Fin r) => b∈A) ha
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton] using (iff_of_eq hh)
  have hsecond : k b ≠ .second := by
    have hh := Finset.card_eq_zero.mp h2
    intro hb
    have hmem : b∈(Finset.univ.filter fun b => k b=.second) := by simp [hb]
    rw [hh] at hmem
    exact Finset.notMem_empty _ hmem
  by_cases hb : b=a
  · have hf := hfirst.mpr hb
    simpa [linearPattern,hb] using hf
  · have hf := mt hfirst.mp hb
    cases hk : k b <;> simp_all [linearPattern]

theorem odd_pattern_pair {r : ℕ} (k : Fin r → GapDifference)
    (hk : Odd (firstDifferenceCount k)) (hnl : ¬∃a, k=linearPattern a) :
    ∃ a b : Fin r, a<b ∧ k a≠.unchanged ∧ k b≠.unchanged := by
  classical
  have hp : 0<firstDifferenceCount k := hk.pos
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hp
  have ha' : k a=.first := (Finset.mem_filter.mp ha).2
  by_contra hh
  push Not at hh
  apply hnl
  refine ⟨a,funext fun b => ?_⟩
  by_cases hb : b=a
  · subst b; simp [linearPattern,ha']
  · have hba : k b=.unchanged := by
      rcases lt_or_gt_of_ne hb with hba|hab
      · by_contra hb'
        exact (show k a≠.unchanged by simp [ha']) (hh b a hba hb')
      · exact hh a b hab (by simp [ha'])
    simp [linearPattern,hb,hba]

theorem odd_nonlinear_order {r : ℕ} (k : Fin r → GapDifference)
    (hk : Odd (firstDifferenceCount k)) (hnl : ¬∃a, k=linearPattern a) :
    3≤∑ h, (k h).order := by
  rcases odd_pattern_linear_or_order_three k hk with h|h
  · exact (hnl (first_second_counts_linear k h.1 h.2)).elim
  · exact h

end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialMoments

Initial coefficient tails, primitive conditioning, mark-list oracle densities, pure norm estimates, and moment energies.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
noncomputable section
noncomputable section


noncomputable section
noncomputable section



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem pattern_order_zero {r : ℕ} (k : Fin r → GapDifference)
    (hk : (∑h, (k h).order)=0) : k=unchangedPattern r := by
  funext h
  have hh := Finset.single_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin r))) =>
    Nat.zero_le (k i).order) (Finset.mem_univ h)
  rw [hk] at hh
  have hz : (k h).order=0 := by omega
  cases he : k h <;> simp_all [GapDifference.order,unchangedPattern]

theorem nonconstant_pattern_linear_or_order_two {r : ℕ} (k : Fin r → GapDifference)
    (hk : k≠unchangedPattern r) : (∃h, k=linearPattern h) ∨ 2≤∑h,(k h).order := by
  by_cases hlin : ∃h, k=linearPattern h
  · exact Or.inl hlin
  right
  by_contra hsmall
  have horder : (∑h,(k h).order)=1 := by
    have hn : (∑h,(k h).order)≠0 := fun he => hk (pattern_order_zero k he)
    omega
  have hc := difference_order_eq_counts k
  have hfirst : firstDifferenceCount k=1 := by omega
  have hsecond : secondDifferenceCount k=0 := by omega
  exact hlin (first_second_counts_linear k hfirst hsecond)


end TraceReconstruction


end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialOverlap

Literal periods, count overlap, initial low/high energies, genuine densities, and centered moment bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem initialOverlapLower_pos (q : ℝ) : 0 < initialOverlapLower q := by
  unfold initialOverlapLower
  positivity

end TraceReconstruction



/-! From the actual displaced period words to their conditional oracle
moments.  The coefficient bounds are the rank kernels,
not assumptions on an abstract pair. -/
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialRates

Initial geometric parameters, moment depths, error and overlap rates, and production of the base induction pair.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N q ω w : ℕ → ℝ} {J u m : ℕ → ℕ}

/-- Exact power of the sharp initial rank prefactor; all channel losses are
 subpower at the source's smallest scale. -/
theorem initialPrefactor_rate (hN : Tendsto N atTop atTop)
    {α β : ℝ} (hu : PowerRate N (fun t=>(u t:ℝ)) α)
    (hm : PowerRate N (fun t=>(m t:ℝ)) β) (hq : PowerRate N q 0) (r d : ℕ) :
    PowerRate N (fun t=>initialPrefactorCap (u t) (m t) r d (q t))
      (α/2-β*((d:ℝ)+(r:ℝ)/2)) := by
  have hd : PowerRate N (fun t=>initialDifferenceCap d (q t)) 0 := by
    have H := ((PowerRate.const hN (by positivity : (0:ℝ)<8*((d:ℝ)+1))).div (hq.pow 2)).sqrt.const_mul hN (by norm_num : (0:ℝ)<2)
    simpa only [initialDifferenceCap,zero_mul,zero_sub,neg_zero,zero_div] using H
  have hnum := (((hu.mul hm).const_mul hN (by norm_num : (0:ℝ)<144)).mul_const hN
    (by positivity : (0:ℝ)<(2:ℝ)^(2*r))).mul (hd.pow (2*d+r+2))
  have hden := ((hm.div_const hN (by norm_num : (0:ℝ)<4)).pow d).mul
    (((hu.mul hm).div_const hN (by positivity : (0:ℝ)<2*(r+1:ℝ))).sqrt)
  have H := hnum.div (hden.mul ((hm.div_const hN (by norm_num : (0:ℝ)<4)).sqrt.pow (r+1)))
  convert H using 1
  · ext t; simp only [initialPrefactorCap,Nat.cast_mul]
  · push_cast; ring

theorem periodCentral_rate (hN : Tendsto N atTop atTop) {α : ℝ}
    (hu : PowerRate N (fun t=>(u t:ℝ)) α) {r : ℕ} (hr : 0 < r) :
    PowerRate N (fun t=>periodCentralSumConstant (u t) r) (α*((r:ℝ)-3)/2) := by
  have H := ((hu.div_const hN (by positivity : (0:ℝ)<3*(r+1:ℝ))).inv hN).const_mul hN
    (by positivity : (0:ℝ)<((r+1:ℕ):ℝ)^2)
  have H' := H.mul (((hu.const_mul hN (by norm_num : (0:ℝ)<2)).sqrt.const_mul hN
    (by norm_num : (0:ℝ)<2)).pow (r-1))
  convert H' using 1
  · ext t; simp only [periodCentralSumConstant,Nat.cast_mul,Nat.cast_ofNat]
  · rw [Nat.cast_sub (by omega : 1 ≤ r)]; norm_num; ring

theorem periodBounded_rate (hN : Tendsto N atTop atTop) {α : ℝ}
    (hu : PowerRate N (fun t=>(u t:ℝ)) α) {r : ℕ} (hr : 2 ≤ r) (M : ℕ) :
    PowerRate N (fun t=>periodBoundedSumConstant (u t) r M) (α*((r:ℝ)-4)/2) := by
  have H := (((hu.div_const hN (by positivity : (0:ℝ)<3*(r+1:ℝ))).inv hN).const_mul hN
    (by positivity : (0:ℝ)<((r+1:ℕ):ℝ)^2)).mul_const hN (by positivity : (0:ℝ)<(M:ℝ)+1)
  have H' := H.mul (((hu.const_mul hN (by norm_num : (0:ℝ)<2)).sqrt.const_mul hN
    (by norm_num : (0:ℝ)<2)).pow (r-2))
  convert H' using 1
  · ext t; simp only [periodBoundedSumConstant,Nat.cast_mul,Nat.cast_ofNat]
  · rw [Nat.cast_sub hr]; norm_num; ring

theorem hiddenSigned_rate (hN : Tendsto N atTop atTop) {γ : ℝ} (hγ : 0<γ)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) γ) (hω : PowerRate N ω 0) (s : ℕ) :
    PowerRate N (fun t=>hiddenSignedL2Bound (J t) s (ω t)) (-γ*((s:ℝ)+1/2)) := by
  have hden := (hJ.mul (hω.pow 2)).add_const hN (by simpa using hγ) (by norm_num : (0:ℝ)≤2)
  have hroot := ((PowerRate.const hN (by positivity : (0:ℝ)<4*((s:ℝ)+1))).div hden).sqrt
  have hp := ((hroot.const_mul hN (by norm_num : (0:ℝ)<2)).pow s).pow 2
  have H := (hp.const_mul hN (by positivity : (0:ℝ)<((2:ℝ)^(s*s))^2)).mul hroot
  convert H using 1
  · rfl
  · push_cast; ring

theorem hiddenUnsigned_rate (hN : Tendsto N atTop atTop) {γ : ℝ} (hγ : 0<γ)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) γ) (hω : PowerRate N ω 0) (s : ℕ) :
    PowerRate N (fun t=>hiddenUnsignedL2Bound (J t) s (ω t)) (-γ/2) := by
  have hden := (hJ.mul (hω.pow 2)).add_const hN (by simpa using hγ) (by norm_num : (0:ℝ)≤2)
  have H := (((PowerRate.const hN (by norm_num : (0:ℝ)<4)).div hden).sqrt).const_mul hN
    (by positivity : (0:ℝ)<((2:ℝ)^s)^2)
  convert H using 1
  · rfl
  · ring

/-- The two eliminated large gaps are quantitatively visible in this exponent. -/
theorem initial_central_rate (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    {r : ℕ} (hr : 0 < r) (d : ℕ) :
    PowerRate N (fun t=>initialPrefactorCap (u t) (m t) r d (q t)*periodCentralSumConstant (u t) r)
      (-123/250-(62/125)*(d:ℝ)-(1/500)*(r:ℝ)) := by
  convert (initialPrefactor_rate hN hu hm hq r d).mul (periodCentral_rate hN hu hr) using 1 <;> first | rfl | ring

theorem initial_bounded_rate (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    {r : ℕ} (hr : 2 ≤ r) (d M : ℕ) :
    PowerRate N (fun t=>initialPrefactorCap (u t) (m t) r d (q t)*periodBoundedSumConstant (u t) r M)
      (-369/500-(62/125)*(d:ℝ)-(1/500)*(r:ℝ)) := by
  convert (initialPrefactor_rate hN hu hm hq r d).mul (periodBounded_rate hN hu hr M) using 1 <;> first | rfl | ring

/-- Fixed low degrees already beat the signed and pure source score exponents. -/
theorem initial_signed_pattern_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0)
    {r : ℕ} (hr : 0 < r) (k : Fin r→GapDifference) (hk : Odd (firstDifferenceCount k)) :
    PowerUpper N (fun t=>initialSignedPatternCap (J t) (u t) (m t) r 300 (q t) (ω t) k) (-223/100) := by
  by_cases hlin : ∃a,k=linearPattern a
  · have H := (initial_central_rate hN hu hm hq hr 1).mul
      (hiddenSigned_rate hN (by norm_num) hJ hω 300)
    have hb : -123/250-(62/125)*(1:ℝ)-(1/500)*(r:ℝ)+(-(1/125)*((300:ℝ)+1/2)) ≤ -223/100 := by
      have hh : (0:ℝ) ≤ r := Nat.cast_nonneg r
      linarith
    simpa only [initialSignedPatternCap,ite_eq_left hlin] using (H.upper hN).mono (by simpa using hb)
  · have hd : 3≤∑h,(k h).order := odd_nonlinear_order k hk hlin
    obtain ⟨a,b,hab,_,_⟩ := odd_pattern_pair k hk hlin
    have hr2 : 2 ≤ r := by have := a.isLt; have := b.isLt; have := hab; omega
    have H := (initial_bounded_rate hN hu hm hq hr2 (∑h,(k h).order) (2*(2^300))).mul
      (hiddenUnsigned_rate hN (by norm_num) hJ hω 300)
    have hb : -369/500-(62/125)*(∑h,(k h).order:ℕ)-(1/500)*(r:ℝ)+(-(1/125)/2) ≤ -223/100 := by
      have hd' : (3:ℝ)≤(∑h,(k h).order:ℕ) := by exact_mod_cast hd
      have hr' : (2:ℝ) ≤ r := by exact_mod_cast hr2
      linarith
    simpa only [initialSignedPatternCap,ite_eq_right hlin] using (H.upper hN).mono (by simpa using hb)

theorem initial_pure_pattern_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0)
    {r : ℕ} (hr : 0 < r) (k : Fin r→GapDifference) (hk : k≠unchangedPattern r) :
    PowerUpper N (fun t=>initialPurePatternCap (J t) (u t) (m t) r 300 (q t) (ω t) k) (-37/25) := by
  by_cases hlin : ∃a,k=linearPattern a
  · have H := (initial_central_rate hN hu hm hq hr 1).mul
      (hiddenSigned_rate hN (by norm_num) hJ hω 300)
    have hb : -123/250-(62/125)*(1:ℝ)-(1/500)*(r:ℝ)+(-(1/125)*((300:ℝ)+1/2)) ≤ -37/25 := by
      have hh : (0:ℝ) ≤ r := Nat.cast_nonneg r
      linarith
    simpa only [initialPurePatternCap,ite_eq_left hlin] using (H.upper hN).mono (by simpa using hb)
  · have hd := (nonconstant_pattern_linear_or_order_two k hk).resolve_left hlin
    have H := (initial_central_rate hN hu hm hq hr (∑h,(k h).order)).mul
      (hiddenUnsigned_rate hN (by norm_num) hJ hω 300)
    have hb : -123/250-(62/125)*(∑h,(k h).order:ℕ)-(1/500)*(r:ℝ)+(-(1/125)/2) ≤ -37/25 := by
      have hd' : (2:ℝ)≤(∑h,(k h).order:ℕ) := by exact_mod_cast hd
      have hr' : (0:ℝ) ≤ r := Nat.cast_nonneg r
      linarith
    simpa only [initialPurePatternCap,ite_eq_right hlin] using (H.upper hN).mono (by simpa using hb)

theorem increasingTuple_card_le (u r : ℕ) : Fintype.card (IncreasingTuple u r) ≤ u^r := by
  simpa only [Fintype.card_fun,Fintype.card_fin] using
    Fintype.card_subtype_le (fun v : Fin r→Fin u => StrictMono v)

theorem initialRankTail_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (r : ℕ) (a : ℝ) :
    PowerUpper N (fun t=>initialRankTailCap (u t) (m t) r) a := by
  have hcard : PowerUpper N (fun t=>(Fintype.card (IncreasingTuple (u t) r):ℝ)) ((123/250)*(r:ℝ)) := by
    apply (hu.pow r).upper hN |>.of_abs_le
    exact Eventually.of_forall fun t=>by
      rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (by positivity)]
      exact_mod_cast increasingTuple_card_le (u t) r
  have hpoly := hcard.mul hN (((hu.mul hm).sqrt.const_mul hN
    (by positivity : (0:ℝ)<48*((r+1:ℕ):ℝ))).upper hN)
  have hexpr : PowerRate N (fun t=>(m t:ℝ)/(1024*(u t:ℝ))) (1/250) := by
    convert hm.div (hu.const_mul hN (by norm_num : (0:ℝ)<1024)) using 1; norm_num
  have hexp := hexpr.exp_neg_upper hN (by norm_num) (a/2-((123/250)*(r:ℝ)+(123/250+62/125)/2))
  have H := ((PowerRate.const hN (by norm_num : (0:ℝ)<2)).upper hN).mul hN
    ((hpoly.mul hN hexp).pow hN 2)
  convert H using 1
  · ext t
    simp only [initialRankTailCap,Nat.cast_mul,neg_div]
    ring
  · push_cast; ring

theorem initialMomentRatio_rate (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hw : PowerRate N w 0) :
    PowerRate N (fun t=>initialMomentRatio (u t) (m t) (q t) (w t)) (-1/500) := by
  have H := ((hw.pow 2).mul ((PowerRate.const hN
    (by positivity [rankSchurConstant_pos] : (0:ℝ)<3*rankSchurConstant)).div hq)).mul (hu.div hm).sqrt
  convert H using 1
  · rfl
  · norm_num

theorem initial_fixed_high_tail_rate (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hw : PowerRate N w 0) :
    PowerRate N (fun t=>4*(initialMomentRatio (u t) (m t) (q t) (w t))^3000/
      (1-initialMomentRatio (u t) (m t) (q t) (w t))) (-6) := by
  have hρ := initialMomentRatio_rate hN hu hm hq hw
  have hz := (hρ.upper hN).tendsto_zero hN (by norm_num)
  have hden : PowerRate N (fun t=>1-initialMomentRatio (u t) (m t) (q t) (w t)) 0 := by
    apply PowerRate.of_tendsto hN (by norm_num : (0:ℝ)<1)
    simpa using tendsto_const_nhds.sub hz
  convert ((hρ.pow 3000).const_mul hN (by norm_num : (0:ℝ)<4)).div hden using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem initialSignedDegree_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0) (r : ℕ) :
    PowerUpper N (fun t=>initialSignedDegreeCap (J t) (u t) (m t) r 300 (q t) (ω t)) (-223/100) := by
  by_cases hr : r=0
  · simpa only [initialSignedDegreeCap,ite_eq_left hr] using PowerUpper.zero hN (-223/100)
  have hs : PowerUpper N (fun t=>∑k : Fin r→GapDifference,
      if Odd (firstDifferenceCount k) then initialSignedPatternCap (J t) (u t) (m t) r 300 (q t) (ω t) k else 0) (-223/100) := by
    apply PowerUpper.sum hN Finset.univ
    intro k _
    by_cases hk : Odd (firstDifferenceCount k)
    · simpa only [ite_eq_left hk] using initial_signed_pattern_upper hN hu hm hq hJ hω (by omega) k hk
    · simpa only [ite_eq_right hk] using PowerUpper.zero hN (-223/100)
  have hc : (0:ℝ)<8*(Fintype.card (Fin r→GapDifference):ℝ) := by
    have hp : 0<Fintype.card (Fin r→GapDifference) := Fintype.card_pos_iff.mpr ⟨fun _=>.unchanged⟩
    positivity
  have H := (((PowerRate.const hN hc).upper hN).mul hN hs)
  simp only [zero_add] at H
  simpa only [initialSignedDegreeCap,ite_eq_right hr] using H.add hN (initialRankTail_upper hN hu hm r (-223/100))

theorem initialPureDegree_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0) (r : ℕ) :
    PowerUpper N (fun t=>initialPureDegreeCap (J t) (u t) (m t) r 300 (q t) (ω t)) (-37/25) := by
  by_cases hr : r=0
  · simpa only [initialPureDegreeCap,ite_eq_left hr] using PowerUpper.zero hN (-37/25)
  have hs : PowerUpper N (fun t=>∑k : Fin r→GapDifference,
      if k=unchangedPattern r then 0 else initialPurePatternCap (J t) (u t) (m t) r 300 (q t) (ω t) k) (-37/25) := by
    apply PowerUpper.sum hN Finset.univ
    intro k _
    by_cases hk : k=unchangedPattern r
    · simpa only [ite_eq_left hk] using PowerUpper.zero hN (-37/25)
    · simpa only [ite_eq_right hk] using initial_pure_pattern_upper hN hu hm hq hJ hω (by omega) k hk
  have hc : (0:ℝ)<2*(Fintype.card (Fin r→GapDifference):ℝ) := by
    have hp : 0<Fintype.card (Fin r→GapDifference) := Fintype.card_pos_iff.mpr ⟨fun _=>.unchanged⟩
    positivity
  have H := (((PowerRate.const hN hc).upper hN).mul hN hs)
  simp only [zero_add] at H
  simpa only [initialPureDegreeCap,ite_eq_right hr] using H.add hN (initialRankTail_upper hN hu hm r (-37/25))

theorem initialSignedCap_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0) (hw : PowerRate N w 0) :
    PowerUpper N (fun t=>initialSignedCap (J t) (u t) (m t) 3000 300 (q t) (ω t) (w t)) (-223/100) := by
  have hs : PowerUpper N (fun t=>∑r∈Finset.range 3000,(w t)^(2*r)*
      initialSignedDegreeCap (J t) (u t) (m t) r 300 (q t) (ω t)) (-223/100) := by
    apply PowerUpper.sum hN (Finset.range 3000)
    intro r _
    simpa only [zero_mul,zero_add] using ((hw.pow (2*r)).upper hN).mul hN (initialSignedDegree_upper hN hu hm hq hJ hω r)
  exact hs.add hN ((initial_fixed_high_tail_rate hN hu hm hq hw).upper hN |>.mono (by norm_num))

theorem initialPureCap_upper (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0) (hw : PowerRate N w 0) :
    PowerUpper N (fun t=>initialPureCap (J t) (u t) (m t) 3000 300 (q t) (ω t) (w t)) (-37/25) := by
  have hs : PowerUpper N (fun t=>∑r∈Finset.range 3000,(w t)^(2*r)*
      initialPureDegreeCap (J t) (u t) (m t) r 300 (q t) (ω t)) (-37/25) := by
    apply PowerUpper.sum hN (Finset.range 3000)
    intro r _
    simpa only [zero_mul,zero_add] using ((hw.pow (2*r)).upper hN).mul hN (initialPureDegree_upper hN hu hm hq hJ hω r)
  exact hs.add hN ((initial_fixed_high_tail_rate hN hu hm hq hw).upper hN |>.mono (by norm_num))

/-- Actual scalar budgets, not assumed coefficient bounds: all report- and
 count-independent caps are strictly below the source clipping allowances. -/
theorem initial_score_caps_eventually (hN : Tendsto N atTop atTop)
    (hu : PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm : PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq : PowerRate N q 0)
    (hJ : PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω : PowerRate N ω 0) (hw : PowerRate N w 0) :
    ∀ᶠt in atTop,
      64*initialSignedCap (J t) (u t) (m t) 3000 300 (q t) (ω t) (w t) ≤ (N t)^(-11/5:ℝ) ∧
      64*initialPureCap (J t) (u t) (m t) 3000 300 (q t) (ω t) (w t) ≤ (N t)^(-7/5:ℝ) := by
  have hc := (PowerRate.const hN (by norm_num : (0:ℝ)<64)).upper hN
  have hs := hc.mul hN (initialSignedCap_upper hN hu hm hq hJ hω hw)
  have hp := hc.mul hN (initialPureCap_upper hN hu hm hq hJ hω hw)
  filter_upwards [hs (-11/5) (by norm_num),hp (-7/5) (by norm_num)] with t hs hp
  exact ⟨(le_abs_self _).trans hs,(le_abs_self _).trans hp⟩

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N f g : ℕ→ℝ} {α β : ℝ}

theorem PowerRate.sub_lower (hN : Tendsto N atTop atTop)
    (hf : PowerRate N f α) (hg : PowerRate N g β) (hβα : β<α) :
    PowerRate N (fun t=>f t-g t) α := by
  have hz := ((hg.div hf).upper hN).tendsto_zero hN (sub_neg.mpr hβα)
  apply hf.of_ratio hN (by norm_num : (0:ℝ)<1)
  have H : Tendsto (fun t=>1-g t/f t) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hz
  apply H.congr'
  filter_upwards [hf.1] with t ht
  field_simp [ht.ne']

theorem PowerRate.nat_sub_lower (hN : Tendsto N atTop atTop) {f g : ℕ→ℕ}
    (hf : PowerRate N (fun t=>(f t:ℝ)) α)
    (hg : PowerRate N (fun t=>(g t:ℝ)) β) (hβα : β<α) :
    PowerRate N (fun t=>(f t-g t:ℕ)) α := by
  have H := hf.sub_lower hN hg hβα
  apply H.congr
  filter_upwards [H.1] with t ht
  have hg : g t≤f t := by exact_mod_cast (sub_pos.mp ht).le
  rw [Nat.cast_sub hg]

theorem sourceInitialM_rate (hN : Tendsto N atTop atTop) :
    PowerRate N (fun t=>(sourceInitialM (N t):ℝ)) (62/125) := by
  have H := ((PowerRate.base hN).rpow (62/125)).nat_floor hN (by norm_num)
  simpa only [sourceInitialM,one_mul] using H

theorem sourceInitialK_rate (hN : Tendsto N atTop atTop) :
    PowerRate N (fun t=>(sourceInitialK (N t):ℝ)) (123/250) := by
  have H := ((PowerRate.base hN).rpow (123/250)).nat_floor hN (by norm_num)
  simpa only [sourceInitialK,one_mul] using H

theorem sourceInitialPeriodSize_rate (hN : Tendsto N atTop atTop) :
    PowerRate N (fun t=>(sourceInitialPeriodSize (N t):ℝ)) (62/125) := by
  have hh : PowerRate N (fun t=>(2*sourceInitialM (N t):ℕ)) (62/125) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (sourceInitialM_rate hN).const_mul hN (by norm_num : (0:ℝ)<2)
  exact hh.nat_sub_lower hN (PowerRate.const hN (by norm_num : (0:ℝ)<(1:ℕ))) (by norm_num)

theorem sourceInitialCapacity_rate (hN : Tendsto N atTop atTop) :
    PowerRate N (fun t=>(sourceInitialCapacity (N t):ℝ)) (63/125) := by
  have H := ((PowerRate.base hN).div (sourceInitialPeriodSize_rate hN)).nat_floor hN (by norm_num)
  convert H using 1
  · rfl
  · norm_num

theorem sourceInitialSide_rate (hN : Tendsto N atTop atTop) {q : ℕ→ℝ}
    (hq : PowerRate N q 0) :
    PowerRate N (fun t=>(initialSideCount (q t) (sourceInitialM (N t)):ℝ)) (62/125) := by
  have H := (hq.mul (sourceInitialM_rate hN)).nat_floor hN (by norm_num)
  simpa only [initialSideCount,zero_add] using H

theorem sourceInitialJ_rate (hN : Tendsto N atTop atTop) {q : ℕ→ℝ}
    (hq : PowerRate N q 0) :
    PowerRate N (fun t=>(sourceInitialJ (q t) (N t):ℝ)) (1/125) := by
  have hn := (sourceInitialCapacity_rate hN).sub_lower hN (sourceInitialK_rate hN) (by norm_num)
  have hd := ((sourceInitialSide_rate hN hq).const_mul hN (by norm_num : (0:ℝ)<2)).add_const hN
    (by norm_num) (by norm_num : (0:ℝ)≤1)
  have H := (hn.div hd).nat_floor hN (by norm_num)
  convert H using 1
  · rfl
  · norm_num

theorem initialOverlap_rate (hN : Tendsto N atTop atTop) {q : ℕ→ℝ}
    (_hq : ∀t,0<q t)
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0)) :
    PowerRate N (fun t=>initialOverlapLower (q t)) 0 := by
  refine ⟨Eventually.of_forall (fun t=>initialOverlapLower_pos _),?_⟩
  have H := (hΛ.const_mul (-(32+3*primitivePeriodConstant))).sub
    ((Real.tendsto_log_atTop.comp hN).const_div_atTop (Real.log 1536))
  simp only [mul_zero,sub_zero] at H
  apply H.congr'
  filter_upwards [] with t
  rw [initialOverlapLower,Real.log_div (Real.exp_pos _).ne' (by norm_num),Real.log_exp]
  simp only [zpow_neg,zpow_ofNat,Function.comp_apply]
  ring

theorem deletion_rate_zero (hN : Tendsto N atTop atTop) {q : ℕ→ℝ}
    (hq : ∀t,q t∈Set.Ioc 0 1)
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0)) :
    PowerRate N q 0 := by
  refine ⟨Eventually.of_forall (fun t=>(hq t).1),?_⟩
  apply squeeze_zero_norm' _ hΛ
  filter_upwards [hN.eventually_gt_atTop 1] with t hNt
  have hp := (hq t).1
  have hle := (hq t).2
  have hqinv : 1≤(q t)⁻¹ := (one_le_inv₀ hp).mpr hle
  have hlog : |Real.log (q t)| ≤ (q t)^(-3:ℤ) := by
    rw [abs_of_nonpos (Real.log_nonpos hp.le hle),←Real.log_inv, zpow_neg,zpow_ofNat]
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
    have hcube : (q t)⁻¹ ≤ ((q t)⁻¹)^3 := by nlinarith [sq_nonneg ((q t)⁻¹-1)]
    rw [←inv_pow]
    linarith
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (Real.log_pos hNt)]
  exact div_le_div_of_nonneg_right hlog (Real.log_pos hNt).le

/-- Mechanical realization of the base scalar score budgets from the actual
 integer choices and the unchanged known channel. -/
theorem source_initial_score_caps {q w : ℕ→ℝ} (hN : Tendsto N atTop atTop)
    (hq : ∀t,q t∈Set.Ioc 0 1)
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0))
    (hw : PowerRate N w 0) :
    ∀ᶠt in atTop,
      64*initialSignedCap (sourceInitialJ (q t) (N t)) (sourceInitialK (N t))
        (sourceInitialM (N t)) 3000 300 (q t) (initialOverlapLower (q t)) (w t) ≤ (N t)^(-11/5:ℝ) ∧
      64*initialPureCap (sourceInitialJ (q t) (N t)) (sourceInitialK (N t))
        (sourceInitialM (N t)) 3000 300 (q t) (initialOverlapLower (q t)) (w t) ≤ (N t)^(-7/5:ℝ) := by
  exact initial_score_caps_eventually hN (sourceInitialK_rate hN) (sourceInitialM_rate hN)
    (deletion_rate_zero hN hq hΛ) (sourceInitialJ_rate hN (deletion_rate_zero hN hq hΛ))
    (initialOverlap_rate hN (fun t=>(hq t).1) hΛ) hw

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem sourceInitialOffset_middle (m : ℕ) (hm : 4 ≤ m) :
    |((sourceInitialOffset m hm).val:ℝ)-(m:ℝ)/2| ≤ 2 := by
  have h1 : 2*(m/2) ≤ m := Nat.mul_div_le m 2
  have h2 : m<2*(m/2+1) := by omega
  have h3 : 1 ≤ m/2 := by omega
  simp only [sourceInitialOffset,Nat.cast_sub h3,Nat.cast_one]
  rw [abs_le]
  have hh1 : (2:ℝ)*(m/2:ℕ) ≤ m := by exact_mod_cast h1
  have hh2 : (m:ℝ)<2*((m/2:ℕ)+1) := by exact_mod_cast h2
  constructor <;> linarith

theorem sourceInitialOffset_safe (u m : ℕ) (hm : 4 ≤ m) :
    SafeTaggedTuple (periodSlot (u:=u) (fun _=>sourceInitialOffset m hm)) := by
  have hi := sourceInitialOffset_interior m hm
  exact constant_period_safe _ hi.1 hi.2 (by omega) id strictMono_id

/-- A literal arithmetic margin implies every base window placement condition. -/
theorem initial_anchor_geometry (J K t s : ℕ) (hK : 12*(J+2^s+1) ≤ K) :
    let a : ℤ := (((J*(2*t+1)+K)/2:ℕ):ℤ)-1
    (J*t+J:ℕ) ≤ a ∧ a+(2^s:ℕ) ≤ (J*t+K:ℕ) ∧
    (K:ℝ)/3 ≤ 2*((a-(J*t:ℕ):ℤ)-J)+1 ∧
    (K:ℝ)/3 ≤ 2*K-(2*((a-(J*t:ℕ):ℤ)+(2:ℝ)^s)+1) := by
  have he : (J*(2*t+1)+K)/2=J*t+(J+K)/2 := by
    rw [show J*(2*t+1)+K=2*(J*t)+(J+K) by ring,Nat.mul_add_div (by norm_num)]
  have hlo : 2*((J+K)/2) ≤ J+K := Nat.mul_div_le _ 2
  have hhi : J+K<2*((J+K)/2+1) := by omega
  have hK1 : 12*(J+1) ≤ K := by nlinarith [Nat.zero_le (2^s)]
  dsimp only
  rw [he]
  have hi1 : J+1 ≤ (J+K)/2 := by omega
  have hi2 : (J+K)/2+(2^s:ℕ) ≤ K+1 := by omega
  constructor
  · apply (le_sub_iff_add_le).mpr
    exact_mod_cast (show J*t+J+1 ≤ J*t+(J+K)/2 from by omega)
  constructor
  · push_cast only [Nat.cast_add]
    omega
  have hl : (2:ℝ)*((J+K)/2:ℕ) ≤ J+K := by exact_mod_cast hlo
  have hh : (J:ℝ)+K<2*(((J+K)/2:ℕ)+1) := by exact_mod_cast hhi
  have hk : (12:ℝ)*((J:ℝ)+(2:ℝ)^s+1) ≤ K := by exact_mod_cast hK
  simp only [Nat.cast_add,Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_one,Int.cast_mul,Nat.cast_mul]
  constructor <;> nlinarith [show (0:ℝ) ≤ (2:ℝ)^s by positivity]

/-- Floors in the initial construction waste no more than one long slot. -/
theorem initial_period_count_bounds {N : ℝ} {m K t : ℕ}
    (hL : 0<2*m-1) (hN : 0 ≤ N) (hK : (K:ℝ) ≤ ⌊N/(2*m-1:ℕ)⌋₊) :
    let F : ℕ := ⌊N/(2*m-1:ℕ)⌋₊
    let J : ℕ := ⌊((F:ℝ)-K)/(2*t+1:ℕ)⌋₊
    let P : ℕ := J*(2*t+1)+K
    (P:ℝ)*(2*m-1:ℕ) ≤ N ∧ N<((P:ℝ)+(2*t+1:ℕ)+1)*(2*m-1:ℕ) := by
  dsimp only
  set F : ℕ := ⌊N/(2*m-1:ℕ)⌋₊
  set J : ℕ := ⌊((F:ℝ)-K)/(2*t+1:ℕ)⌋₊
  have hd : (0:ℝ)<(2*t+1:ℕ) := by positivity
  have hl : (0:ℝ)<(2*m-1:ℕ) := by exact_mod_cast hL
  have hjlo := Nat.floor_le (div_nonneg (sub_nonneg.mpr hK) hd.le)
  have hjhi := Nat.lt_floor_add_one (((F:ℝ)-K)/(2*t+1:ℕ))
  change (J:ℝ) ≤ _ at hjlo
  change _<(J:ℝ)+1 at hjhi
  have hflo := Nat.floor_le (div_nonneg hN hl.le)
  have hfhi := Nat.lt_floor_add_one (N/(2*m-1:ℕ))
  change (F:ℝ) ≤ _ at hflo
  change _<(F:ℝ)+1 at hfhi
  have hp : (J:ℝ)*(2*t+1:ℕ)+K ≤ F := by
    have H := (le_div_iff₀ hd).mp hjlo
    linarith
  have hp' : (F:ℝ)<(J:ℝ)*(2*t+1:ℕ)+K+(2*t+1:ℕ) := by
    have H := (div_lt_iff₀ hd).mp hjhi
    nlinarith
  constructor
  · push_cast
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      (mul_le_mul_of_nonneg_right hp hl.le).trans ((le_div_iff₀ hl).mp hflo)
  · have H := (div_lt_iff₀ hl).mp hfhi
    push_cast at hp' ⊢
    nlinarith

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N f g : ℕ→ℝ} {α β : ℝ}

theorem PowerRate.eventually_lt (hN : Tendsto N atTop atTop)
    (hf : PowerRate N f α) (hg : PowerRate N g β) (hab : α<β) :
    ∀ᶠt in atTop, f t<g t := by
  have hz := ((hf.div hg).upper hN).tendsto_zero hN (sub_neg.mpr hab)
  filter_upwards [hz.eventually_lt_const (by norm_num : (0:ℝ)<1),hg.1] with t ht hp
  exact (div_lt_one hp).mp ht

theorem PowerRate.log_base (hN : Tendsto N atTop atTop) :
    PowerRate N (fun t=>Real.log (N t)) 0 := by
  refine ⟨(hN.eventually_gt_atTop 1).mono (fun _ ht=>Real.log_pos ht),?_⟩
  convert
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
      (Real.tendsto_log_atTop.comp hN) using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  simp only [Function.comp_apply,Real.rpow_one]

/-- All floor, seed, count, placement and length restrictions are automatic
 in the actual joint regime; no change of the deletion rate at the base scale. -/
theorem source_initial_geometry {q : ℕ→ℝ} (hN : Tendsto N atTop atTop)
    (hq : ∀t,q t∈Set.Ioc 0 1)
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0)) :
    ∀ᶠt in atTop,SourceInitialGeometry (q t) (N t) := by
  have hm := sourceInitialM_rate hN
  have hK := sourceInitialK_rate hN
  have hqrate := deletion_rate_zero hN hq hΛ
  have hJ := sourceInitialJ_rate hN hqrate
  have hL := sourceInitialPeriodSize_rate hN
  have hF := sourceInitialCapacity_rate hN
  have ht := sourceInitialSide_rate hN hqrate
  have hm128 := (hm.tendsto_atTop hN (by norm_num)).eventually_ge_atTop 128
  have hKm := hK.eventually_lt hN hm (by norm_num)
  have hKF := hK.eventually_lt hN hF (by norm_num)
  have hseed := ((hqrate.pow 3).mul hm).tendsto_atTop hN (by norm_num)
  have hcount := ((hK.mul hm).mul (hqrate.pow 2)).tendsto_atTop hN (by norm_num)
  have hanchor := ((hJ.add_const hN (by norm_num) (by positivity : (0:ℝ)≤2^300+1)).const_mul
    hN (by norm_num : (0:ℝ)<12)).eventually_lt hN hK (by norm_num)
  have hsm := (hK.tendsto_atTop hN (by norm_num)).eventually_gt_atTop ((2*(2^300):ℝ)*(3*3001))
  have hloss : PowerRate N (fun t=>(2*(initialSideCount (q t) (sourceInitialM (N t)):ℝ)+2)*
      (sourceInitialPeriodSize (N t):ℝ)) (124/125) := by
    convert ((ht.const_mul hN (by norm_num : (0:ℝ)<2)).add_const hN
      (by norm_num) (by norm_num : (0:ℝ)≤2)).mul hL using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hloss' := hloss.eventually_lt hN ((PowerRate.base hN).div_const hN (by norm_num : (0:ℝ)<2)) (by norm_num)
  filter_upwards [hN.eventually_gt_atTop 0,hm128,hK.1,hKm,hKF,
    hseed.eventually_ge_atTop 16,hcount.eventually_ge_atTop 8,hanchor,hsm,hloss'] with t hNt hm128 hKpos hKm hKF hs hc ha hsm hloss
  have hmn : 128 ≤ sourceInitialM (N t) := by exact_mod_cast hm128
  have hKn : 0 < sourceInitialK (N t) := by exact_mod_cast hKpos
  have hLpos : 0 < sourceInitialPeriodSize (N t) := by unfold sourceInitialPeriodSize; omega
  have hcnt := initial_period_count_bounds (m:=sourceInitialM (N t))
    (K:=sourceInitialK (N t)) (t:=initialSideCount (q t) (sourceInitialM (N t)))
    (N:=N t) hLpos hNt.le hKF.le
  have hcnt' : (sourceInitialP (q t) (N t):ℝ)*(sourceInitialPeriodSize (N t):ℝ) ≤ N t ∧
      N t<((sourceInitialP (q t) (N t):ℝ)+(2*initialSideCount (q t) (sourceInitialM (N t))+1:ℕ)+1)*
        (sourceInitialPeriodSize (N t):ℝ) := by
    simpa only [sourceInitialP,sourceInitialJ,sourceInitialCapacity,sourceInitialPeriodSize,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hcnt
  refine ⟨hmn,hKn,?_,hs,?_,?_,?_,?_,hcnt'.1⟩
  · exact_mod_cast hKm.le
  · simpa only [Nat.cast_mul] using hc
  · apply (Nat.cast_le (α:=ℝ)).mp
    simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    simpa only [add_assoc] using ha.le
  · apply (lt_div_iff₀ (by norm_num : (0:ℝ)<3*(3000+1))).mpr
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,show (3000+1:ℝ)=3001 by norm_num] using hsm
  · have H := hcnt'.2
    push_cast at H
    nlinarith only [H,hloss]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

theorem sourceInitialWeight_rate {N q : ℕ→ℝ} {k : ℕ→ℕ}
    (hN : Tendsto N atTop atTop) (hq : PowerRate N q 0)
    (hk : PowerRate N (fun t=>(k t:ℝ)) 0) :
    PowerRate N (fun t=>sourceInitialWeight (q t) (k t)) 0 := by
  have H := (hk.const_mul hN (by norm_num : (0:ℝ)<24)).div hq
  convert H using 1
  · ext t
    simp only [sourceInitialWeight,Nat.cast_mul,Nat.cast_ofNat]
    ring
  · norm_num

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

variable {N q w : ℕ→ℝ} {k : ℕ→ℕ}

theorem initialClipFactor_rate (hN : Tendsto N atTop atTop)
    (hq : PowerRate N q 0) (hw : PowerRate N w 0) :
    PowerRate N (fun t=>initialClipFactor (N t) (q t) (w t)) (-1/500) := by
  have hρ := initialMomentRatio_rate hN (sourceInitialK_rate hN) (sourceInitialM_rate hN) hq hw
  have hden := (PowerRate.const hN (by norm_num : (0:ℝ)<1)).sub_lower hN hρ (by norm_num)
  simpa only [initialClipFactor,sub_zero] using (hρ.div hden).const_mul hN (by norm_num : (0:ℝ)<4)

/-- The source moment is genuinely used in clipping: the exponent is linear
 in that moment, not a fixed negative power of the intermediate length. -/
theorem initial_clip_exp_bound (hN : Tendsto N atTop atTop)
    (hq : PowerRate N q 0) (hw : PowerRate N w 0) (hk : ∀ᶠt in atTop,1 ≤ k t) :
    ∀ᶠt in atTop,
      Real.sqrt (6*(initialClipFactor (N t) (q t) (w t))^(k t)) ≤
        Real.exp (-(k t:ℝ)*Real.log (N t)/2000) := by
  have hfac := initialClipFactor_rate hN hq hw
  have hu := hfac.upper hN (-3/2000) (by norm_num)
  filter_upwards [hk,hfac.1,hu,hN.eventually_gt_atTop 1,
    (Real.tendsto_log_atTop.comp hN).eventually_ge_atTop (2000*Real.log 6)] with t hk hp hu hn hlog
  rw [abs_of_pos hp] at hu
  have hh := Real.log_le_log hp hu
  rw [Real.log_rpow (by linarith : 0<N t)] at hh
  have hk' : (1:ℝ) ≤ k t := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ k t)
  have hl : 0 ≤ Real.log (N t) := (Real.log_pos hn).le
  have hg : Real.log 6 ≤ (k t:ℝ)*Real.log (N t)/2000 := by
    change 2000*Real.log 6 ≤ Real.log (N t) at hlog
    nlinarith [mul_nonneg (sub_nonneg.mpr hk') hl]
  have hexp : Real.sqrt (6*initialClipFactor (N t) (q t) (w t)^(k t)) =
      Real.exp ((Real.log 6+(k t:ℝ)*Real.log (initialClipFactor (N t) (q t) (w t)))/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by positivity),Real.log_mul (by norm_num) (pow_pos hp _).ne',Real.log_pow]
    congr 1
    ring
  rw [hexp]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The fixed metadata tails also beat the varying moment times log-scale.
 Their exponents have orders .988 and .008 respectively, while k log N
 has order zero. -/
theorem initial_metadata_exp_bound (hN : Tendsto N atTop atTop)
    (hq : PowerRate N q 0) (hω : PowerRate N (fun t=>initialOverlapLower (q t)) 0)
    (hk : PowerRate N (fun t=>(k t:ℝ)) 0) :
    ∀ᶠt in atTop,
      2*Real.exp (-((sourceInitialK (N t)*sourceInitialM (N t):ℕ):ℝ)*(q t)^4/64)+
        Real.exp (-(sourceInitialJ (q t) (N t):ℝ)*(initialOverlapLower (q t))^4/16) ≤
        3*Real.exp (-(k t:ℝ)*Real.log (N t)) := by
  have hlow : PowerRate N (fun t=>(k t:ℝ)*Real.log (N t)) 0 := by
    simpa using hk.mul (PowerRate.log_base hN)
  have hfirst := (((sourceInitialK_rate hN).mul (sourceInitialM_rate hN)).mul
    (hq.pow 4)).div_const hN (by norm_num : (0:ℝ)<64)
  have hsecond := ((sourceInitialJ_rate hN hq).mul (hω.pow 4)).div_const hN (by norm_num : (0:ℝ)<16)
  filter_upwards [hlow.eventually_lt hN hfirst (by norm_num),hlow.eventually_lt hN hsecond (by norm_num)] with t h1 h2
  have he1 := Real.exp_le_exp.mpr (neg_le_neg h1.le)
  have he2 := Real.exp_le_exp.mpr (neg_le_neg h2.le)
  push_cast
  simp only [neg_div,neg_mul] at he1 he2 ⊢
  linarith

/-- A completely quantitative sufficient moment inequality for the actual
 initial error. This is later discharged by the literal ceiling r_0/2. -/
theorem initial_error_eventually {n A : ℕ→ℝ} (hN : Tendsto N atTop atTop)
    (hn : Tendsto n atTop atTop) (hA : ∀ᶠt in atTop,1 ≤ A t)
    (hq : ∀t,q t∈Set.Ioc 0 1)
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0))
    (hk : PowerRate N (fun t=>(k t:ℝ)) 0) (hk1 : ∀ᶠt in atTop,1 ≤ k t)
    (hmoment : ∀ᶠt in atTop, 10^6*A t*Real.log (n t) ≤ (k t:ℝ)*Real.log (N t)) :
    ∀ᶠt in atTop,
      initialErrorCap (sourceInitialJ (q t) (N t)) (sourceInitialK (N t))
        (sourceInitialM (N t)) (k t) (q t) (initialOverlapLower (q t))
        (sourceInitialWeight (q t) (k t)) ≤ (n t)^(-100*A t) := by
  have hqrate := deletion_rate_zero hN hq hΛ
  have hω := initialOverlap_rate hN (fun t=>(hq t).1) hΛ
  have hw := sourceInitialWeight_rate hN hqrate hk
  have hclip := initial_clip_exp_bound hN hqrate hw hk1
  have hmeta := initial_metadata_exp_bound hN hqrate hω hk
  filter_upwards [hclip,hmeta,hmoment,hA,hn.eventually_gt_atTop 1,
    (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop (Real.log 4)] with t hc hm hmom hA hn hlog
  have hAn : 0 ≤ A t*Real.log (n t) := mul_nonneg (by linarith) (Real.log_pos hn).le
  have he1 : Real.exp (-(k t:ℝ)*Real.log (N t)/2000) ≤ Real.exp (-500*(A t*Real.log (n t))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have he2 : Real.exp (-(k t:ℝ)*Real.log (N t)) ≤ Real.exp (-500*(A t*Real.log (n t))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have herr : initialErrorCap (sourceInitialJ (q t) (N t)) (sourceInitialK (N t))
      (sourceInitialM (N t)) (k t) (q t) (initialOverlapLower (q t))
      (sourceInitialWeight (q t) (k t)) ≤ 4*Real.exp (-500*(A t*Real.log (n t))) := by
    unfold initialErrorCap
    change Real.sqrt (6*initialClipFactor (N t) (q t) (sourceInitialWeight (q t) (k t))^(k t))+_ ≤ _
    nlinarith only [hc,hm,he1,he2]
  apply herr.trans
  rw [Real.rpow_def_of_pos (by linarith : 0<n t)]
  calc
    4*Real.exp (-500*(A t*Real.log (n t))) =
        Real.exp (Real.log 4-500*(A t*Real.log (n t))) := by
      rw [Real.exp_sub,Real.exp_log (by norm_num)]
      rw [show -500*(A t*Real.log (n t)) = -(500*(A t*Real.log (n t))) by ring, Real.exp_neg]
      rfl
    _ ≤ Real.exp (Real.log (n t)*(-100*A t)) := by
      apply Real.exp_le_exp.mpr
      have hAL : Real.log 4 ≤ A t*Real.log (n t) := hlog.trans (le_mul_of_one_le_left (Real.log_pos hn).le hA)
      nlinarith

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical

/-- The actual initial proof, with no oracle or coefficient-bound hypothesis.
 The only moment restriction is the quantitative source ceiling inequality. -/
theorem source_initial_oracles_eventually_oai {N q n A : ℕ→ℝ} {k : ℕ→ℕ}
    (hN : Tendsto N atTop atTop) (hn : Tendsto n atTop atTop)
    (hA : ∀ᶠt in atTop,1 ≤ A t) (hq : ∀t,q t∈Set.Ioc 0 (1/2:ℝ))
    (hΛ : Tendsto (fun t=>(q t)^(-3:ℤ)/Real.log (N t)) atTop (𝓝 0))
    (hk : PowerRate N (fun t=>(k t:ℝ)) 0) (hk1 : ∀ᶠt in atTop,1 ≤ k t)
    (hmoment : ∀ᶠt in atTop,10^6*A t*Real.log (n t) ≤ (k t:ℝ)*Real.log (N t)) :
    ∀ᶠt in atTop,
      SourceInitialGeometry (q t) (N t) ∧
      sourceInitialError (q t) (N t) (k t) ≤ (n t)^(-100*A t) ∧
      Nonempty (OracleTracePair (q t) (sourceInitialWord (q t) (N t) (-1))
        (sourceInitialWord (q t) (N t) 1) (k t) (sourceInitialError (q t) (N t) (k t)) ((N t)^(-11/5:ℝ))) ∧
      Nonempty (OracleTracePair (q t) (sourceInitialPure (q t) (N t))
        (sourceInitialWord (q t) (N t) 1) (k t) (sourceInitialError (q t) (N t) (k t)) ((N t)^(-7/5:ℝ))) := by
  have hq' (t) : q t ∈ Set.Ioc 0 1 := ⟨(hq t).1,by linarith [(hq t).2]⟩
  have hqr := deletion_rate_zero hN hq' hΛ
  have hw := sourceInitialWeight_rate hN hqr hk
  have herr := initial_error_eventually hN hn hA hq' hΛ hk hk1 hmoment
  have hgeo := source_initial_geometry hN hq' hΛ
  have hcap := source_initial_score_caps hN hq' hΛ hw
  have hρ := (initialMomentRatio_rate hN (sourceInitialK_rate hN) (sourceInitialM_rate hN) hqr hw).upper hN |>.tendsto_zero hN (by norm_num)
  have hsmall := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<100)).comp hn).eventually_le_const (by norm_num : (0:ℝ)<1/2)
  filter_upwards [hgeo,hcap,herr,hk1,hA,hn.eventually_gt_atTop 1,hN.eventually_gt_atTop 0,
    hρ.eventually_le_const (by norm_num : (0:ℝ)<1/2),hsmall] with t hg hcap he hk1 ha hnt hNt hρ hsmall
  have hm : 4 ≤ sourceInitialM (N t) := (by norm_num : 4 ≤ 128).trans hg.m_large
  let off := sourceInitialOffset (sourceInitialM (N t)) hm
  have hi := sourceInitialOffset_interior _ hm
  have hanchor := initial_anchor_geometry (sourceInitialJ (q t) (N t)) (sourceInitialK (N t))
    (initialSideCount (q t) (sourceInitialM (N t))) 300 hg.anchor_margin
  change _ ≤ sourceInitialAnchor (q t) (N t) ∧ sourceInitialAnchor (q t) (N t)+(2^300:ℕ) ≤ _ ∧ _ at hanchor
  have he' : sourceInitialError (q t) (N t) (k t) ≤ 1/2 := by
    exact he.trans ((Real.rpow_le_rpow_of_exponent_le hnt.le (by linarith : -100*A t ≤ -100)).trans hsmall)
  have hc : Real.sqrt (6*(4*(initialMomentRatio (sourceInitialK (N t)) (sourceInitialM (N t)) (q t)
      (sourceInitialWeight (q t) (k t))/(1-initialMomentRatio (sourceInitialK (N t))
      (sourceInitialM (N t)) (q t) (sourceInitialWeight (q t) (k t)))))^(k t)) ≤ 1/2 := by
    have ht : 0 ≤ 2*Real.exp (-((sourceInitialK (N t)*sourceInitialM (N t):ℕ):ℝ)*(q t)^4/64)+
      Real.exp (-(sourceInitialJ (q t) (N t):ℝ)*(initialOverlapLower (q t))^4/16) := by positivity
    unfold sourceInitialError initialErrorCap at he'
    linarith only [he',ht]
  have HH := actual_initial_oracles hg.K_pos hg.m_large hg.K_le_m (by norm_num : 0<3000)
    off hi (sourceInitialOffset_middle _ hm) (sourceInitialOffset_safe _ _ hm)
    (sourceInitialAnchor (q t) (N t)) 300 (k t) hk1 (hq t) hg.seed hg.count
    hanchor.1 hanchor.2.1 hanchor.2.2.1 hanchor.2.2.2 hg.smoothing_margin
    (rfl : sourceInitialWeight (q t) (k t)=_) hρ hc
    (Real.rpow_nonneg hNt.le _) (Real.rpow_nonneg hNt.le _) hcap.1 hcap.2
  refine ⟨hg,he,?_,?_⟩
  · simpa only [sourceInitialWord,dite_eq_left hm,sourceInitialP,sourceInitialError,off] using HH.1
  · simpa only [sourceInitialWord,dite_eq_left hm,sourceInitialP,sourceInitialError,sourceInitialPure,
      off,sourceInitialOffset] using HH.2

end TraceReconstruction


end
end
end
end
end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.TraceReconstruction.source_initial_oracles_eventually_oai := @OAI.TraceReconstruction.source_initial_oracles_eventually_oai
