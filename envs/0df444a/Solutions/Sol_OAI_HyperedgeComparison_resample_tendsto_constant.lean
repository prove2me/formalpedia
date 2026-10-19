-- Prove2me | solution 1 for OAI.HyperedgeComparison.resample_tendsto_constant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:51:03.979961+00:00
-- url     : https://prove2.me/submissions/83014748-9546-4c88-9130-70db9a179f3f

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison

open OAI OAI.HyperedgeComparison
universe uE uI uV
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
variable {V : Type uV} {E : Type uE}
variable [Fintype E]
theorem hc_adj_symm {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E} {ω : E → Bool}
    {D : Set V} {x y : V} (h : OAI.HyperedgeComparison.Adj H ω D x y) :
    OAI.HyperedgeComparison.Adj H ω D y x := by
  obtain ⟨e, h1, h2, h3, h4⟩ := h
  exact ⟨e, h1, h2, h4, h3⟩

theorem hc_conn_symm {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E} {ω : E → Bool}
    {D : Set V} {x y : V} (h : OAI.HyperedgeComparison.Connected H ω D x y) :
    OAI.HyperedgeComparison.Connected H ω D y x := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (hc_adj_symm hab) ih

theorem hc_conn_trans {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E} {ω : E → Bool}
    {D : Set V} {x y z : V} (h : OAI.HyperedgeComparison.Connected H ω D x y)
    (h' : OAI.HyperedgeComparison.Connected H ω D y z) :
    OAI.HyperedgeComparison.Connected H ω D x z :=
  Relation.ReflTransGen.trans h h'

theorem hc_conn_false {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E}
    {D : Set V} {x y : V} (h : OAI.HyperedgeComparison.Connected H (fun _ => false) D x y) :
    y = x := by
  induction h with
  | refl => rfl
  | tail _ hab _ => obtain ⟨e, h1, _⟩ := hab; simp at h1
theorem hc_law_real_singleton {E : Type*} [Fintype E] (p : E → Set.Icc (0 : ℝ) 1) (ω : E → Bool) :
    (law p).real {ω} = ∏ e, (if ω e then (p e : ℝ) else 1 - (p e : ℝ)) := by
  have hs : ({ω} : Set (E → Bool)) = Set.univ.pi (fun e => {ω e}) := by
    ext η; simp [funext_iff]
  rw [hs, measureReal_def, law, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  cases h : ω e
  · rw [← measureReal_def, bernoulliMeasure_real_apply_of_notMem_of_mem _ (measurableSet_singleton _) (by simp) (by simp)]
    simp
  · rw [← measureReal_def, bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton _) (by simp) (by simp)]
    simp

theorem hc_law_false_pos {E : Type*} [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (hp : ∀ e, (p e : ℝ) < 1) : 0 < (law p).real {fun _ => false} := by
  rw [hc_law_real_singleton]
  exact Finset.prod_pos (fun e _ => by simp only [Bool.false_eq_true, if_false]; linarith [hp e])

theorem hc_integral_ge_point {E : Type*} [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (f : (E → Bool) → ℝ) (hf : ∀ ω, 0 ≤ f ω) (ω0 : E → Bool) :
    (law p).real {ω0} * f ω0 ≤ ∫ ω, f ω ∂law p := by
  rw [integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]
  exact Finset.single_le_sum (f := fun ω => (law p).real {ω} * f ω)
    (fun ω _ => mul_nonneg measureReal_nonneg (hf ω)) (Finset.mem_univ ω0)
open OAI.FiniteResampling OAI.FiniteResampling.Transition in
theorem hc_lower_le {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) (j : I) : lower f ≤ f j :=
  Finset.inf'_le _ (Finset.mem_univ j)

open OAI.FiniteResampling OAI.FiniteResampling.Transition in
theorem hc_le_upper {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) (j : I) : f j ≤ upper f :=
  Finset.le_sup' _ (Finset.mem_univ j)

open OAI.FiniteResampling OAI.FiniteResampling.Transition in
theorem hc_act_sub {I : Type*} [Fintype I] (K : Transition I) (f : I → ℝ) (c : ℝ) (i : I) :
    K.act f i - c = ∑ j, K.weight i j * (f j - c) := by
  simp only [act, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, K.total, one_mul]

open OAI.FiniteResampling OAI.FiniteResampling.Transition in
theorem hc_atom_bounds {I : Type*} [Fintype I] [Nonempty I] (K : Transition I)
    (z : I) (a : ℝ) (ha : ∀ i, a ≤ K.weight i z)
    (f : I → ℝ) (i : I) :
    a * f z + (1-a) * lower f ≤ K.act f i ∧
      K.act f i ≤ a * f z + (1-a) * upper f := by
  constructor
  · have h1 := hc_act_sub K f (lower f) i
    have h2 : K.weight i z * (f z - lower f) ≤ ∑ j, K.weight i j * (f j - lower f) :=
      Finset.single_le_sum (f := fun j => K.weight i j * (f j - lower f))
        (fun j _ => mul_nonneg (K.nonneg i j) (sub_nonneg.mpr (hc_lower_le f j))) (Finset.mem_univ z)
    have h3 : a * (f z - lower f) ≤ K.weight i z * (f z - lower f) :=
      mul_le_mul_of_nonneg_right (ha i) (sub_nonneg.mpr (hc_lower_le f z))
    nlinarith
  · have h1 := hc_act_sub K f (upper f) i
    have h2 : ∑ j, K.weight i j * (f j - upper f) ≤ K.weight i z * (f z - upper f) := by
      have := Finset.single_le_sum (f := fun j => K.weight i j * (upper f - f j))
        (fun j _ => mul_nonneg (K.nonneg i j) (sub_nonneg.mpr (hc_le_upper f j))) (Finset.mem_univ z)
      simp only [mul_sub, Finset.sum_sub_distrib] at this ⊢
      linarith
    have h3 : K.weight i z * (f z - upper f) ≤ a * (f z - upper f) :=
      mul_le_mul_of_nonpos_right (ha i) (sub_nonpos.mpr (hc_le_upper f z))
    nlinarith

open OAI.FiniteResampling OAI.FiniteResampling.Transition in
theorem hc_iter_const {I : Type*} [Fintype I] [Nonempty I] (K : Transition I)
    (z : I) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : ∀ i, a ≤ K.weight i z) (f : I → ℝ) :
    ∃ c : ℝ, lower f ≤ c ∧ c ≤ upper f ∧
      ∀ i, Tendsto (fun n : ℕ => ((K.act)^[n] f) i) atTop (nhds c) := by
  have hlo : ∀ g : I → ℝ, a * g z + (1-a) * lower g ≤ lower (K.act g) := fun g =>
    Finset.le_inf' _ _ (fun i _ => (hc_atom_bounds K z a ha g i).1)
  have hup : ∀ g : I → ℝ, upper (K.act g) ≤ a * g z + (1-a) * upper g := fun g =>
    Finset.sup'_le _ _ (fun i _ => (hc_atom_bounds K z a ha g i).2)
  let fn : ℕ → I → ℝ := fun n => (K.act)^[n] f
  have hsucc : ∀ n, fn (n+1) = K.act (fn n) := fun n => Function.iterate_succ_apply' _ _ _
  let L : ℕ → ℝ := fun n => lower (fn n)
  let U : ℕ → ℝ := fun n => upper (fn n)
  have hLU : ∀ n, L n ≤ U n := fun n => (hc_lower_le (fn n) (Classical.arbitrary I)).trans
    (hc_le_upper (fn n) _)
  have hLmono : Monotone L := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    show lower (fn n) ≤ lower (fn (n+1))
    rw [hsucc]
    have := hlo (fn n)
    have := hc_lower_le (fn n) z
    nlinarith
  have hUanti : Antitone U := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    show upper (fn (n+1)) ≤ upper (fn n)
    rw [hsucc]
    have := hup (fn n)
    have := hc_le_upper (fn n) z
    nlinarith
  have hgap : ∀ n, U n - L n ≤ (1-a)^n * (U 0 - L 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      show upper (fn (n+1)) - lower (fn (n+1)) ≤ _
      rw [hsucc]
      have h1 := hlo (fn n)
      have h2 := hup (fn n)
      have : upper (K.act (fn n)) - lower (K.act (fn n)) ≤ (1-a) * (U n - L n) := by
        simp only [U, L]; nlinarith
      calc _ ≤ (1-a) * (U n - L n) := this
        _ ≤ (1-a) * ((1-a)^n * (U 0 - L 0)) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ = _ := by ring
  have hLU' : ∀ m n, L m ≤ U n := fun m n =>
    (hLmono (le_max_left m n)).trans ((hLU _).trans (hUanti (le_max_right m n)))
  have hbdd : BddAbove (Set.range L) := ⟨U 0, by rintro _ ⟨m, rfl⟩; exact hLU' m 0⟩
  let c := ⨆ n, L n
  have hLc : Tendsto L atTop (nhds c) := tendsto_atTop_ciSup hLmono hbdd
  have hgap0 : Tendsto (fun n => U n - L n) atTop (nhds 0) := by
    have hp : Tendsto (fun n : ℕ => (1-a)^n * (U 0 - L 0)) atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0:ℝ) ≤ 1-a) (by linarith : 1-a < 1)).mul_const (U 0 - L 0)
      simpa using this
    exact squeeze_zero (fun n => sub_nonneg.mpr (hLU n)) hgap hp
  have hUc : Tendsto U atTop (nhds c) := by
    have := hLc.add hgap0
    simp only [add_zero, add_sub_cancel] at this
    exact this
  refine ⟨c, ?_, ?_, fun i => ?_⟩
  · exact le_ciSup hbdd 0
  · exact ciSup_le (fun m => hLU' m 0)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le hLc hUc
      (fun n => hc_lower_le (fn n) i) (fun n => hc_le_upper (fn n) i)

theorem hc_atom {V E : Type*} [Fintype E] [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S : Set V) (hs : s ∉ S)
    (U : ClusterDomain s S) :
    (law p).real {fun _ => false} ≤ (resamplingTransition H p s S).weight U
      ⟨{s}, ⟨by simp, by simpa using hs⟩⟩ := by
  show _ ≤ ∫ ω, ∫ ω', (if nextState H s S U ω ω' = _ then (1:ℝ) else 0) ∂law p ∂law p
  have hin : ∀ ω, (law p).real {fun _ => false} ≤
      ∫ ω', (if nextState H s S U ω ω' = ⟨{s}, ⟨by simp, by simpa using hs⟩⟩ then (1:ℝ) else 0) ∂law p := by
    intro ω
    refine le_trans (le_of_eq ?_) (hc_integral_ge_point p _ (fun ω => by split_ifs <;> norm_num) (fun _ => false))
    rw [if_pos, mul_one]
    apply Subtype.ext
    ext y
    simp only [nextState, Set.mem_singleton_iff]
    constructor
    · intro h; exact hc_conn_false h
    · rintro rfl; exact .refl
  calc (law p).real {fun _ => false} = ∫ _ω, (law p).real {fun _ => false} ∂law p := by simp
    _ ≤ _ := integral_mono (integrable_const _) Integrable.of_finite hin

theorem hc_resample_act {V E : Type*} [Fintype E] [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S : Set V) (G : Set V → ℝ) (U : ClusterDomain s S) :
    resample H p s S G U.1 = (resamplingTransition H p s S).act (fun T => G T.1) U := by
  simp only [FiniteResampling.Transition.act, resamplingTransition]
  have : ∀ T : ClusterDomain s S, (∫ ω, ∫ ω', (if nextState H s S U ω ω' = T then (1:ℝ) else 0) ∂law p ∂law p) * G T.1
      = ∫ ω, ∫ ω', (if nextState H s S U ω ω' = T then G T.1 else 0) ∂law p ∂law p := by
    intro T
    rw [← integral_mul_const]
    congr 1; funext ω
    rw [← integral_mul_const]
    congr 1; funext ω'
    split_ifs <;> simp
  simp only [this]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  unfold resample meanAfterDelete
  congr 1; funext ω
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  congr 1; funext ω'
  rw [Finset.sum_ite_eq]
  simp [nextState]

theorem hc_resample_iter {V E : Type*} [Fintype E] [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S : Set V) (F : Set V → ℝ) (n : ℕ) (U : ClusterDomain s S) :
    ((resample H p s S)^[n] F) U.1 = ((resamplingTransition H p s S).act^[n] (fun T => F T.1)) U := by
  induction n generalizing U with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hc_resample_act]
    congr 1; funext T; exact ih T

theorem hc_resample_tendsto {V E : Type*} [Fintype E] [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (s : V) (S : Set V) (hs : s ∉ S) (F : Set V → ℝ)
    (hF : ∀ U ∈ ClusterDomain s S, 0 ≤ F U) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ U ∈ ClusterDomain s S,
      Tendsto (fun n : ℕ => ((resample H p s S)^[n] F) U) atTop (nhds c) := by
  have : Nonempty (ClusterDomain s S) := ⟨⟨{s}, ⟨by simp, by simpa using hs⟩⟩⟩
  obtain ⟨c, hc1, _, hc⟩ := hc_iter_const (resamplingTransition H p s S) ⟨{s}, ⟨by simp, by simpa using hs⟩⟩
    ((law p).real {fun _ => false}) (hc_law_false_pos p hp) measureReal_le_one
    (hc_atom H p s S hs) (fun T => F T.1)
  refine ⟨c, le_trans ?_ hc1, fun U hU => ?_⟩
  · exact Finset.le_inf' _ _ (fun T _ => hF T.1 T.2)
  · have := hc ⟨U, hU⟩
    simpa only [← hc_resample_iter] using this

theorem solution [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (s : V) (S : Set V) (hs : s ∉ S) (F : Set V → ℝ)
    (hF : ∀ U ∈ ClusterDomain s S, 0 ≤ F U) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ U ∈ ClusterDomain s S,
      Tendsto (fun n : ℕ => ((resample H p s S)^[n] F) U) atTop (nhds c) := by
  exact hc_resample_tendsto H p hp s S hs F hF

