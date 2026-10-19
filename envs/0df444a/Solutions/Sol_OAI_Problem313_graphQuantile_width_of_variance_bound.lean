-- Prove2me | solution 1 for OAI.Problem313.graphQuantile_width_of_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:48:12.014398+00:00
-- url     : https://prove2.me/submissions/4e1ef97b-56e3-4cb7-85fc-c2b9ae727235

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/SharpThreshold.lean:L12-L49
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.graphQuantile_width_of_variance_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOptionExpectation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Quantile
import Theorems.Thm_OAI_Problem313_graphVariance_eq_mean_mul
import Theorems.Thm_OAI_Problem313_logistic_coordinate_width
import Theorems.Thm_OAI_Problem313_unitQuantile_mem_Ioo

-- ---- from OAI.Combinatorics.SharpThreshold.Probability ----
namespace OAI

noncomputable section
namespace Problem313

theorem graphWeight_sum {n : ℕ} (p : ℝ) :
    (∑ x : GraphConfig n, graphWeight p x) = 1 := by
  classical
  unfold graphWeight
  rw [← Fintype.prod_sum (fun (_ : GraphEdge n) (b : Bool) => if b = true then p else 1 - p)]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  simp

theorem graphWeight_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (x : GraphConfig n) : 0 ≤ graphWeight p x := by
  classical
  apply Finset.prod_nonneg
  intro e he
  split_ifs <;> linarith

theorem graphWeight_pos {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x : GraphConfig n) : 0 < graphWeight p x := by
  classical
  apply Finset.prod_pos
  intro e he
  split_ifs <;> linarith

theorem graphMean_not {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) :
    graphMean p (fun x => !(f x)) = 1 - graphMean p f := by
  classical
  simp only [graphMean, boolReal_not, mul_sub, mul_one, Finset.sum_sub_distrib,
    graphWeight_sum]

theorem graphMean_pos {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : GraphConfig n → Bool} (hf : ∃ x, f x = true) : 0 < graphMean p f := by
  classical
  obtain ⟨x, hx⟩ := hf
  apply Finset.sum_pos'
  · intro y hy
    exact mul_nonneg (graphWeight_nonneg hp.le hp1.le y) (boolReal_nonneg (f y))
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    simpa [hx, boolReal] using graphWeight_pos hp hp1 x

theorem graphMean_lt_one {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : GraphConfig n → Bool} (hf : ∃ x, f x = false) : graphMean p f < 1 := by
  obtain ⟨x, hx⟩ := hf
  have ht : ∃ x, (!(f x)) = true := ⟨x, by simp [hx]⟩
  have h := graphMean_pos hp hp1 ht
  rw [graphMean_not] at h
  linarith

theorem graphMean_mem_Ioo {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : GraphConfig n → Bool} (hf : NontrivialGraphProperty f) :
    graphMean p f ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨graphMean_pos hp hp1 hf.1, graphMean_lt_one hp hp1 hf.2⟩

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.RussoReindex ----
namespace OAI

universe u

noncomputable section
open scoped BigOperators
namespace Problem313

variable {ι : Type u} [DecidableEq ι]

variable [Fintype ι]

/-- Splitting a finite Boolean cube at one coordinate. -/
theorem sum_bool_split (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x, g x) = ∑ z : {j : ι // j ≠ i} → Bool,
      (g (russoInsert i true z) + g (russoInsert i false z)) := by
  rw [← (Equiv.funSplitAt i Bool).symm.sum_comp g]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  rfl

/-- The product excluding a coordinate does not depend on that coordinate. -/
theorem prod_erase_russoInsert (p : ℝ) (i : ι) (b c : Bool)
    (z : {j : ι // j ≠ i} → Bool) :
    (∏ j ∈ Finset.univ.erase i, if russoInsert i b z j = true then p else 1-p) =
    ∏ j ∈ Finset.univ.erase i, if russoInsert i c z j = true then p else 1-p := by
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [hji]

/-- A Bernoulli weight factors at a chosen coordinate. -/
theorem prod_russoInsert (p : ℝ) (i : ι) (b : Bool)
    (z : {j : ι // j ≠ i} → Bool) :
    (∏ j, if russoInsert i b z j = true then p else 1-p) =
    (if b = true then p else 1-p) *
      ∏ j ∈ Finset.univ.erase i, if russoInsert i false z j = true then p else 1-p := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => if russoInsert i b z j = true then p else 1-p) (Finset.mem_univ i)]
  rw [prod_erase_russoInsert p i b false]
  simp

/-- Finite reindexing identity behind the Russo--Margulis derivative formula.
No positivity assumptions on the bias or the observable are needed. -/
theorem russo_sum_reindex (p : ℝ) (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x : ι → Bool, (if x i = true then (1 : ℝ) else -1) *
      (∏ j ∈ Finset.univ.erase i, if x j = true then p else 1-p) * g x) =
    ∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) *
      (g (Function.update x i true) - g (Function.update x i false)) := by
  rw [sum_bool_split i, sum_bool_split i]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [russoInsert_self, Bool.false_eq_true,
    ↓reduceIte, update_russoInsert, prod_russoInsert]
  rw [prod_erase_russoInsert p i true false]
  ring

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.Quantile ----
namespace OAI

noncomputable section
namespace Problem313

theorem unitQuantile_set_bddBelow (μ : ℝ → ℝ) (a : ℝ) :
    BddBelow {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p} :=
  ⟨0, fun _ hp => hp.1.1⟩

theorem unitQuantile_set_nonempty {μ : ℝ → ℝ} {a : ℝ}
    (h1 : μ 1 = 1) (ha : a ≤ 1) :
    {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p}.Nonempty := by
  refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩
  simpa only [h1] using ha

theorem unitQuantile_mem {μ : ℝ → ℝ} {a : ℝ}
    (hμ : Continuous μ) (h1 : μ 1 = 1) (ha : a ≤ 1) :
    unitQuantile μ a ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ (unitQuantile μ a) := by
  have hc : IsClosed {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p} :=
    isClosed_Icc.inter (isClosed_le continuous_const hμ)
  exact hc.csInf_mem (unitQuantile_set_nonempty h1 ha) (unitQuantile_set_bddBelow μ a)

theorem unitQuantile_eq_level {μ : ℝ → ℝ} {a : ℝ}
    (hμ : Continuous μ) (h0 : μ 0 = 0) (h1 : μ 1 = 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    μ (unitQuantile μ a) = a := by
  have hq := unitQuantile_mem hμ h1 ha1
  have ha : a ∈ Set.Icc (μ 0) (μ (unitQuantile μ a)) := by
    exact ⟨by simpa only [h0] using ha0, hq.2⟩
  obtain ⟨x, hx, heq⟩ := intermediate_value_Icc hq.1.1 hμ.continuousOn ha
  have hqx : unitQuantile μ a ≤ x := by
    apply csInf_le (unitQuantile_set_bddBelow μ a)
    exact ⟨⟨hx.1, hx.2.trans hq.1.2⟩, heq.ge⟩
  have hxq : x = unitQuantile μ a := le_antisymm hx.2 hqx
  simpa only [hxq] using heq

theorem unitQuantile_mono {μ : ℝ → ℝ} {a b : ℝ}
    (h1 : μ 1 = 1) (hab : a ≤ b) (hb : b ≤ 1) :
    unitQuantile μ a ≤ unitQuantile μ b := by
  apply csInf_le_csInf (unitQuantile_set_bddBelow μ a)
    (unitQuantile_set_nonempty h1 hb)
  intro p hp
  exact ⟨hp.1, hab.trans hp.2⟩

theorem unitQuantile_strictMonoOn {μ : ℝ → ℝ}
    (hμ : Continuous μ) (h0 : μ 0 = 0) (h1 : μ 1 = 1) :
    StrictMonoOn (unitQuantile μ) (Set.Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hle := unitQuantile_mono h1 hab.le hb.2
  refine lt_of_le_of_ne hle ?_
  intro heq
  have haeq := unitQuantile_eq_level hμ h0 h1 ha.1 ha.2
  have hbeq := unitQuantile_eq_level hμ h0 h1 hb.1 hb.2
  rw [heq, hbeq] at haeq
  exact hab.ne haeq.symm

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.MeanEndpoints ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace Problem313

lemma continuous_graphWeight {n : ℕ} (x : GraphConfig n) :
    Continuous (fun p : ℝ => graphWeight p x) := by
  classical
  unfold graphWeight
  apply continuous_finsetProd
  intro e he
  split_ifs <;> fun_prop

lemma continuous_graphMean {n : ℕ} (f : GraphConfig n → Bool) :
    Continuous (fun p : ℝ => graphMean p f) := by
  classical
  unfold graphMean
  apply continuous_finsetSum
  intro x hx
  exact (continuous_graphWeight x).mul continuous_const

lemma increasing_nontrivial_false {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    f (fun _ => false) = false := by
  obtain ⟨x, hx⟩ := hnt.2
  cases h : f (fun _ => false)
  · rfl
  · have hh := hmono (fun _ => false) x (by intro e he; cases he) h
    rw [hx] at hh
    contradiction

lemma increasing_nontrivial_true {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    f (fun _ => true) = true := by
  obtain ⟨x, hx⟩ := hnt.1
  exact hmono x (fun _ => true) (by intro e he; rfl) hx

lemma graphWeight_zero {n : ℕ} (x : GraphConfig n) :
    graphWeight 0 x = if x = (fun _ => false) then 1 else 0 := by
  classical
  by_cases hx : x = (fun _ => false)
  · subst x
    simp [graphWeight]
  · rw [ite_eq_right hx]
    obtain ⟨e, he⟩ : ∃ e, x e = true := by
      by_contra h
      apply hx
      funext e
      cases hxe : x e
      · rfl
      · exact False.elim (h ⟨e, hxe⟩)
    unfold graphWeight
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [he]

lemma graphWeight_one {n : ℕ} (x : GraphConfig n) :
    graphWeight 1 x = if x = (fun _ => true) then 1 else 0 := by
  classical
  by_cases hx : x = (fun _ => true)
  · subst x
    simp [graphWeight]
  · rw [ite_eq_right hx]
    obtain ⟨e, he⟩ : ∃ e, x e = false := by
      by_contra h
      apply hx
      funext e
      cases hxe : x e
      · exact False.elim (h ⟨e, hxe⟩)
      · rfl
    unfold graphWeight
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [he]

lemma graphMean_zero_eq {n : ℕ} (f : GraphConfig n → Bool) :
    graphMean 0 f = boolReal (f (fun _ => false)) := by
  classical
  simp [graphMean, graphWeight_zero]

lemma graphMean_one_eq {n : ℕ} (f : GraphConfig n → Bool) :
    graphMean 1 f = boolReal (f (fun _ => true)) := by
  classical
  simp [graphMean, graphWeight_one]

lemma graphMean_zero_of_increasing_nontrivial {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    graphMean 0 f = 0 := by
  rw [graphMean_zero_eq, increasing_nontrivial_false hmono hnt]
  rfl

lemma graphMean_one_of_increasing_nontrivial {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    graphMean 1 f = 1 := by
  rw [graphMean_one_eq, increasing_nontrivial_true hmono hnt]
  rfl

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.GraphQuantile ----
namespace OAI

noncomputable section
namespace Problem313

theorem graphMean_graphQuantile {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    graphMean (graphQuantile a f) f = a :=
  unitQuantile_eq_level (continuous_graphMean f)
    (graphMean_zero_of_increasing_nontrivial hmono hnt)
    (graphMean_one_of_increasing_nontrivial hmono hnt) ha0 ha1

theorem graphQuantile_mem_Ioo {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    graphQuantile a f ∈ Set.Ioo (0 : ℝ) 1 :=
  unitQuantile_mem_Ioo (continuous_graphMean f)
    (graphMean_zero_of_increasing_nontrivial hmono hnt)
    (graphMean_one_of_increasing_nontrivial hmono hnt) ha0 ha1

theorem graphQuantile_strictMonoOn {n : ℕ} {f : GraphConfig n → Bool}
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f) :
    StrictMonoOn (fun a => graphQuantile a f) (Set.Icc (0 : ℝ) 1) :=
  unitQuantile_strictMonoOn (continuous_graphMean f)
    (graphMean_zero_of_increasing_nontrivial hmono hnt)
    (graphMean_one_of_increasing_nontrivial hmono hnt)

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.Russo ----
namespace OAI

noncomputable section

namespace Problem313

/-- Derivative of the Bernoulli mass of a single graph configuration. -/
theorem hasDerivAt_graphWeight {n : ℕ} (p : ℝ) (x : GraphConfig n) :
    HasDerivAt (fun q => graphWeight q x)
      (∑ e : GraphEdge n, (if x e = true then (1 : ℝ) else -1) *
        ∏ j ∈ Finset.univ.erase e, if x j = true then p else 1 - p) p := by
  classical
  have h (e : GraphEdge n) :
      HasDerivAt (fun q : ℝ => if x e = true then q else 1 - q)
        (if x e = true then (1 : ℝ) else -1) p := by
    split_ifs
    · exact hasDerivAt_id p
    · simpa using (hasDerivAt_id p).const_sub (1 : ℝ)
  simpa only [graphWeight, smul_eq_mul, mul_comm] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun e _ => h e))

/-- The finite product rule for the graph probability polynomial. -/
theorem hasDerivAt_graphMean_raw {n : ℕ} (f : GraphConfig n → Bool) (p : ℝ) :
    HasDerivAt (fun q => graphMean q f)
      (∑ e : GraphEdge n, ∑ x : GraphConfig n,
        ((if x e = true then (1 : ℝ) else -1) *
          ∏ j ∈ Finset.univ.erase e, if x j = true then p else 1 - p) *
          boolReal (f x)) p := by
  classical
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (GraphConfig n)))
    (fun x _ => (hasDerivAt_graphWeight p x).mul_const (boolReal (f x)))
  simp_rw [Finset.sum_mul] at h
  rw [Finset.sum_comm] at h
  exact h

/-- Every increasing property has nonnegative Boolean coordinate differences. -/
theorem increasing_update_false_true {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (x : GraphConfig n) (e : GraphEdge n) :
    f (Function.update x e false) = true → f (Function.update x e true) = true := by
  classical
  apply hf
  intro j hj
  by_cases hje : j = e
  · subst j
    simp
  · simpa [Function.update_of_ne hje] using hj

/-- For an increasing Boolean function the coordinate difference is its pivotal indicator. -/
theorem boolReal_update_sub_eq_indicator {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (x : GraphConfig n) (e : GraphEdge n) :
    boolReal (f (Function.update x e true)) - boolReal (f (Function.update x e false)) =
      if f (Function.update x e true) ≠ f (Function.update x e false) then 1 else 0 := by
  classical
  have h := increasing_update_false_true hf x e
  cases ht : f (Function.update x e true) <;>
    cases he : f (Function.update x e false) <;>
    simp_all [boolReal]

/-- Monotone pivotal influence is the expectation of the oriented coordinate difference. -/
theorem edgeInfluence_eq_sum_boolReal_sub {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (p : ℝ) (e : GraphEdge n) :
    edgeInfluence p f e = ∑ x : GraphConfig n, graphWeight p x *
      (boolReal (f (Function.update x e true)) -
        boolReal (f (Function.update x e false))) := by
  classical
  unfold edgeInfluence
  apply Finset.sum_congr rfl
  intro x _
  rw [boolReal_update_sub_eq_indicator hf]
  split_ifs <;> simp

/-- Russo--Margulis formula with pivotal total influence.
The identity is polynomial, so no restriction to biases in `[0,1]` is necessary. -/
theorem hasDerivAt_graphMean {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (p : ℝ) :
    HasDerivAt (fun q => graphMean q f) (totalInfluence p f) p := by
  classical
  convert hasDerivAt_graphMean_raw f p using 1
  unfold totalInfluence
  apply Finset.sum_congr rfl
  intro e _
  rw [edgeInfluence_eq_sum_boolReal_sub hf]
  exact (russo_sum_reindex p e (fun x => boolReal (f x))).symm

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.ThresholdODE ----
namespace OAI

noncomputable section

namespace Problem313

/-- The symmetric endpoint form used in sharp-threshold estimates. -/
theorem logistic_width_of_hasDerivAt {μ μ' : ℝ → ℝ} {a b C ε : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) (hεone : ε < 1)
    (hcont : ContinuousOn μ (Set.Icc a b))
    (hμ : ∀ x ∈ Set.Icc a b, 0 < μ x ∧ μ x < 1)
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt μ (μ' x) x)
    (hbound : ∀ x ∈ Set.Ioo a b, μ x * (1 - μ x) ≤ C * μ' x)
    (ha : μ a = ε) (hb : μ b = 1 - ε) :
    b - a ≤ 2 * C * Real.log ((1 - ε) / ε) := by
  have h := logistic_coordinate_width hab hcont hμ hd hbound
  rw [ha, hb] at h
  have hsub : 1 - (1 - ε) = ε := by ring
  rw [hsub] at h
  rw [Real.log_div (ne_of_gt (sub_pos.mpr hεone)) (ne_of_gt hε)]
  linarith

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.ThresholdConstants ----
namespace OAI

noncomputable section

namespace Problem313

/-- The logarithmic simplification used in the threshold-width estimate. -/
theorem log_odds_le_two_log_half_inv (ε : ℝ) (hε : 0 < ε)
    (hεhalf : ε < (1 / 2 : ℝ)) :
    Real.log ((1 - ε) / ε) ≤ 2 * Real.log (1 / (2 * ε)) := by
  have hnum : 0 < 1 - ε := by linarith
  have hden : 0 < 2 * ε := by positivity
  have hratio : (1 - ε) / ε ≤ (1 / (2 * ε)) ^ 2 := by
    rw [div_pow, one_pow]
    apply (div_le_div_iff₀ hε (sq_pos_of_pos hden)).2
    nlinarith [mul_nonneg (le_of_lt hε) (sq_nonneg (1 - 2 * ε))]
  have hlog := Real.log_le_log (div_pos hnum hε) hratio
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

/-- Multiplying the logarithmic estimate by a nonnegative constant. -/
theorem threshold_log_conversion (C ε w : ℝ) (hC : 0 ≤ C)
    (hε : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ))
    (hw : w ≤ (2 * C) * Real.log ((1 - ε) / ε)) :
    w ≤ (4 * C) * Real.log (1 / (2 * ε)) := by
  calc
    w ≤ (2 * C) * Real.log ((1 - ε) / ε) := hw
    _ ≤ (2 * C) * (2 * Real.log (1 / (2 * ε))) :=
      mul_le_mul_of_nonneg_left (log_odds_le_two_log_half_inv ε hε hεhalf)
        (by positivity)
    _ = (4 * C) * Real.log (1 / (2 * ε)) := by ring

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.SharpThreshold ----
namespace OAI

noncomputable section
namespace Problem313

/-- The entire threshold-width deduction, with the variance estimate as its only
additional quantitative hypothesis. -/
theorem graphQuantile_width_of_variance_bound {n : ℕ} {f : GraphConfig n → Bool}
    {C ε : ℝ} (hC : 0 ≤ C)
    (hmono : IncreasingGraphProperty f) (hnt : NontrivialGraphProperty f)
    (hε : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ))
    (hvariance : ∀ p ∈ Set.Ioo (0 : ℝ) 1,
      graphVariance p f ≤ C * totalInfluence p f) :
    graphQuantile (1 - ε) f - graphQuantile ε f ≤
      (4 * C) * Real.log (1 / (2 * ε)) := by
  have hεone : ε < 1 := by linarith
  have hother0 : 0 < 1 - ε := by linarith
  have hother1 : 1 - ε < 1 := by linarith
  have ha := graphQuantile_mem_Ioo hmono hnt hε hεone
  have hb := graphQuantile_mem_Ioo hmono hnt hother0 hother1
  have hab : graphQuantile ε f ≤ graphQuantile (1 - ε) f := by
    exact (graphQuantile_strictMonoOn hmono hnt
      ⟨hε.le, hεone.le⟩ ⟨hother0.le, hother1.le⟩ (by linarith)).le
  have hrange : ∀ p ∈ Set.Icc (graphQuantile ε f) (graphQuantile (1 - ε) f),
      p ∈ Set.Ioo (0 : ℝ) 1 := by
    intro p hp
    exact ⟨ha.1.trans_le hp.1, hp.2.trans_lt hb.2⟩
  have hlog : graphQuantile (1 - ε) f - graphQuantile ε f ≤
      2 * C * Real.log ((1 - ε) / ε) := by
    apply logistic_width_of_hasDerivAt
      (μ := fun p => graphMean p f) (μ' := fun p => totalInfluence p f)
      hab hε hεone (continuous_graphMean f).continuousOn
    · intro p hp
      exact graphMean_mem_Ioo (hrange p hp).1 (hrange p hp).2 hnt
    · intro p hp
      exact hasDerivAt_graphMean hmono p
    · intro p hp
      have hv := hvariance p (hrange p (Set.Ioo_subset_Icc_self hp))
      simpa only [graphVariance_eq_mean_mul] using hv
    · exact graphMean_graphQuantile hmono hnt hε.le hεone.le
    · exact graphMean_graphQuantile hmono hnt hother0.le hother1.le
  exact threshold_log_conversion C ε
    (graphQuantile (1 - ε) f - graphQuantile ε f) hC hε hεhalf hlog

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.graphQuantile_width_of_variance_bound := @_root_.OAI.Problem313.graphQuantile_width_of_variance_bound
