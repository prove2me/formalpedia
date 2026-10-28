-- Prove2me | solution 1 for OAI.EuclideanFiveColor.fullApprox_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T13:05:58.020277+00:00
-- url     : https://prove2.me/submissions/a69bbb7d-f6a3-4620-8127-0fbde9b2be5a

import Mathlib
import Definitions.Def_OAIQ5T4002
import Theorems.Thm_OAI_EuclideanFiveColor_annulus_maps_eventually_forest
import Theorems.Thm_OAI_EuclideanFiveColor_five_sequence_no_accumulation
import Theorems.Thm_OAI_EuclideanFiveColor_fourCenter_compact_finite
import Theorems.Thm_OAI_EuclideanFiveColor_threeCenter_compact_finite

section
-- module Solutions.OAIQ5_T4.Compat
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Transitions
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
lemma transitionSet_measurable (hc : Measurable c) (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) :
    MeasurableSet (transitionSet c i j x R h) := by
  exact measurableSet_ball.inter (((measurableSet_eq_fun hc measurable_const).inter
    (measurableSet_eq_fun (hc.comp (measurable_id.add_const h)) measurable_const)).union
    ((measurableSet_eq_fun hc measurable_const).inter
    (measurableSet_eq_fun (hc.comp (measurable_id.add_const h)) measurable_const)))
lemma transitionSet_finite (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) :
    volume (transitionSet c i j x R h) < ⊤ :=
  (measure_mono (fun _ hq => Metric.ball_subset_closedBall hq.1)).trans_lt
    (isCompact_closedBall x R).measure_lt_top
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Accumulation
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
lemma transitionRatio_mono {i j : Fin k} {x y : ℂ} {R S : ℝ}
    (hB : Metric.ball x R ⊆ Metric.ball y S) (h : ℂ) :
    transitionRatio c i j x R h ≤ transitionRatio c i j y S h := by
  apply ENNReal.div_le_div_right
  exact measure_mono (fun _ hq => ⟨hB hq.1,hq.2⟩)
lemma transitionEdge_closed (i j : Fin k) : IsClosed {x | TransitionEdge c i j x} := by
  apply isClosed_of_closure_subset
  intro x hx
  have hne : i≠j := by
    obtain ⟨y,_,hy⟩ := mem_closure_iff.mp hx Set.univ isOpen_univ (mem_univ _)
    exact hy.1
  refine ⟨hne,fun R hR => ?_⟩
  obtain ⟨y,hyB,hy⟩ := mem_closure_iff.mp hx (Metric.ball x (R/2)) Metric.isOpen_ball
    (Metric.mem_ball_self (by linarith))
  have hB : Metric.ball y (R/2) ⊆ Metric.ball x R := by
    intro z hz
    have ht := dist_triangle z y x
    have hz' : dist z y < R/2 := hz
    have hy' : dist y x < R/2 := hyB
    exact lt_of_le_of_lt ht (by linarith)
  exact (hy.2 (R/2) (by linarith)).trans_le (limsup_le_limsup
    (Eventually.of_forall (transitionRatio_mono c hB)))
lemma missing_edge_lim (i j : Fin k) (hne : i≠j) {x : ℂ}
    (he : ¬TransitionEdge c i j x) : ∃ R>0,
    Tendsto (transitionRatio c i j x R) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
  obtain ⟨R,hR,hr⟩ : ∃ R, 0<R ∧ ¬0<limsup (transitionRatio c i j x R) (𝓝[≠] (0:ℂ)) := by
    have hh : ¬∀ R, 0<R → 0<limsup (transitionRatio c i j x R) (𝓝[≠] (0:ℂ)) :=
      fun hh => he ⟨hne,hh⟩
    push Not at hh
    exact ⟨hh.choose,hh.choose_spec.1,not_lt.mpr hh.choose_spec.2⟩
  refine ⟨R,hR,?_⟩
  have hs : limsup (transitionRatio c i j x R) (𝓝[≠] (0:ℂ))=0 := le_antisymm (not_lt.mp hr) (bot_le)
  exact tendsto_of_le_liminf_of_limsup_le (bot_le) hs.le
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (e : Equiv.Perm (Fin k))
lemma weak_relabel (hw : WeakColoring k c) : WeakColoring k (e ∘ c) := by
  refine ⟨(measurable_of_finite e).comp_aemeasurable hw.1,?_⟩
  exact hw.2.mono fun p hp h => hp (e.injective h)
lemma transitionSet_relabel (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) :
    transitionSet (e ∘ c) (e i) (e j) x R h=transitionSet c i j x R h := by
  ext q
  simp only [transitionSet,Set.mem_ofPred_eq,Function.comp_apply,Equiv.apply_eq_iff_eq]
lemma transitionEdge_relabel (i j : Fin k) (x : ℂ) :
    TransitionEdge (e ∘ c) (e i) (e j) x ↔ TransitionEdge c i j x := by
  have he : transitionRatio (e ∘ c) (e i) (e j) x=transitionRatio c i j x := by
    funext R h
    unfold transitionRatio
    rw [transitionSet_relabel]
  simp only [TransitionEdge,he,ne_eq,Equiv.apply_eq_iff_eq]
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_CyclicCore
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma fiveCenter_closed : IsClosed {x | FiveCenter c x} := by
  change IsClosed {x | ∀i : Fin 5,TransitionEdge c i (i+1) x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => transitionEdge_closed c i (i+1)
include hc in
lemma fiveCenter_discrete (hw : WeakColoring 5 c) : IsDiscrete {x | FiveCenter c x} := by
  apply isDiscrete_iff_discreteTopology.mpr
  apply discreteTopology_of_noAccPts
  intro x hx ha
  obtain ⟨yn,hyn,hy⟩ := mem_closure_iff_seq_limit.mp
    (accPt_principal_iff_clusterPt.mp ha).mem_closure
  exact five_sequence_no_accumulation c hc hw (fun n => (hyn n).1) hx hy
    (fun n => by simpa only [mem_singleton_iff] using (hyn n).2)
include hc in
lemma fiveCenter_compact_finite (hw : WeakColoring 5 c) {K : Set ℂ} (hK : IsCompact K) :
    (K∩{x | FiveCenter c x}).Finite :=
  (hK.inter_right (fiveCenter_closed c)).finite ((fiveCenter_discrete c hc hw).mono inter_subset_right)
end EuclideanFiveColor
end

noncomputable section
open Set
namespace EuclideanFiveColor
lemma cycle_standard_permutation {G : SimpleGraph (Fin 5)} {v : Fin 5}
    {p : G.Walk v v} (hp : p.IsCycle) : ∃e : Equiv.Perm (Fin 5),
    (G.Adj (e 0) (e 1) ∧ G.Adj (e 0) (e 2) ∧ G.Adj (e 1) (e 2)) ∨
    (G.Adj (e 0) (e 1) ∧ G.Adj (e 1) (e 2) ∧ G.Adj (e 2) (e 3) ∧ G.Adj (e 3) (e 0)) ∨
    (∀i : Fin 5,G.Adj (e i) (e (i+1))) := by
  have hl := hp.three_le_length
  have hinj : Function.Injective (fun i : Fin p.length => p.getVert i) := by
    intro i j h
    apply Fin.ext
    exact hp.getVert_injOn' (by change i.val≤p.length-1; omega)
      (by change j.val≤p.length-1; omega) h
  have hle : p.length≤5 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hle)
    (fun i : Fin p.length => p.getVert i) (Fin.castLE_injective hle) hinj
  have hem (n : ℕ) (hn : n<p.length) : e ⟨n,lt_of_lt_of_le hn hle⟩=p.getVert n := he ⟨n,hn⟩
  have h0 : e 0=p.getVert 0 := hem 0 (by omega)
  have h1 : e 1=p.getVert 1 := hem 1 (by omega)
  have h2 : e 2=p.getVert 2 := hem 2 (by omega)
  have h01 : G.Adj (e 0) (e 1) := by rw [h0,h1]; exact p.adj_getVert_succ (by omega)
  have h12 : G.Adj (e 1) (e 2) := by rw [h1,h2]; exact p.adj_getVert_succ (by omega)
  refine ⟨e,?_⟩
  rcases (by omega : p.length=3 ∨ p.length=4 ∨ p.length=5) with hL|hL|hL
  · left
    refine ⟨h01,?_,h12⟩
    have h20 := p.adj_getVert_succ (i := 2) (by omega)
    have hlast : p.getVert 3=p.getVert 0 := by simpa only [hL,SimpleGraph.Walk.getVert_zero] using p.getVert_length
    rw [hlast,← h2,← h0] at h20
    exact h20.symm
  · right; left
    have h3 : e 3=p.getVert 3 := hem 3 (by omega)
    refine ⟨h01,h12,?_,?_⟩
    · rw [h2,h3]; exact p.adj_getVert_succ (by omega)
    · have h30 := p.adj_getVert_succ (i := 3) (by omega)
      have hlast : p.getVert 4=p.getVert 0 := by simpa only [hL,SimpleGraph.Walk.getVert_zero] using p.getVert_length
      rwa [hlast,← h3,← h0] at h30
  · right; right
    have h3 : e 3=p.getVert 3 := hem 3 (by omega)
    have h4 : e 4=p.getVert 4 := hem 4 (by omega)
    have h23 : G.Adj (e 2) (e 3) := by rw [h2,h3]; exact p.adj_getVert_succ (by omega)
    have h34 : G.Adj (e 3) (e 4) := by rw [h3,h4]; exact p.adj_getVert_succ (by omega)
    have h40 : G.Adj (e 4) (e 0) := by
      have h40 := p.adj_getVert_succ (i := 4) (by omega)
      have hlast : p.getVert 5=p.getVert 0 := by simpa only [hL,SimpleGraph.Walk.getVert_zero] using p.getVert_length
      rwa [hlast,← h4,← h0] at h40
    intro i
    fin_cases i
    · exact h01
    · exact h12
    · exact h23
    · exact h34
    · exact h40
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma transitionEdge_unlabel (e : Equiv.Perm (Fin 5)) (i j : Fin 5) (x : ℂ) :
    TransitionEdge (e.symm ∘ c) i j x ↔ TransitionEdge c (e i) (e j) x := by
  simpa only [Equiv.symm_apply_apply] using transitionEdge_relabel c e.symm (e i) (e j) x
lemma cyclicCore_subset_standard : CyclicCore c ⊆ ⋃e,StandardCore c e := by
  intro x hx
  change ¬∀v (p : (transitionGraph c x).Walk v v),¬p.IsCycle at hx
  push Not at hx
  obtain ⟨v,p,hp⟩ := hx
  obtain ⟨e,he⟩ := cycle_standard_permutation hp
  refine mem_iUnion.mpr ⟨e,?_⟩
  change ThreeCenter (e.symm ∘ c) x ∨ FourCenter (e.symm ∘ c) x ∨ FiveCenter (e.symm ∘ c) x
  simp only [ThreeCenter,FourCenter,FiveCenter,transitionEdge_unlabel]
  exact he
include hc in
lemma standardCore_compact_finite (hw : WeakColoring 5 c) {K : Set ℂ} (hK : IsCompact K)
    (e : Equiv.Perm (Fin 5)) : (K∩StandardCore c e).Finite := by
  have hc' : Measurable (e.symm ∘ c) := (measurable_of_finite e.symm).comp hc
  have hw' := weak_relabel c e.symm hw
  exact ((threeCenter_compact_finite _ hc' hw' hK).union
    ((fourCenter_compact_finite _ hc' hw' hK).union
      (fiveCenter_compact_finite _ hc' hw' hK))).subset (by
        intro x hx
        rcases hx.2 with h|h|h
        · exact Or.inl ⟨hx.1,h⟩
        · exact Or.inr (Or.inl ⟨hx.1,h⟩)
        · exact Or.inr (Or.inr ⟨hx.1,h⟩))
include hc in
lemma cyclicCore_compact_finite (hw : WeakColoring 5 c) {K : Set ℂ} (hK : IsCompact K) :
    (K∩CyclicCore c).Finite := by
  have hf : (⋃e,K∩StandardCore c e).Finite := finite_iUnion fun e =>
    standardCore_compact_finite c hc hw hK e
  apply hf.subset
  intro x hx
  obtain ⟨e,he⟩ := mem_iUnion.mp (cyclicCore_subset_standard c hx.2)
  exact mem_iUnion.mpr ⟨e,hx.1,he⟩
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_DiskAverages
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory MeasureTheory.Measure
namespace EuclideanFiveColor
lemma diskLaw_probability {ε : ℝ} (hε : 0<ε) : IsProbabilityMeasure (diskLaw ε) := by
  constructor
  simp only [diskLaw,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume 0 hε).ne'
    ((measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall (0:ℂ) ε).measure_lt_top).ne
lemma colorFn_measurable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (i : Fin k) :
    Measurable (colorFn c i) :=
  measurable_one.piecewise (measurableSet_eq_fun hc measurable_const) measurable_zero
lemma colorFn_nonneg {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (z : ℂ) : 0 ≤ colorFn c i z := by
  simp only [colorFn]; split_ifs <;> norm_num
lemma colorFn_le_one {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (z : ℂ) : colorFn c i z≤1 := by
  simp only [colorFn]; split_ifs <;> norm_num
lemma colorFn_integrable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (i : Fin k)
    {μ : Measure ℂ} [IsFiniteMeasure μ] (q : ℂ) : Integrable (fun v => colorFn c i (q+v)) μ := by
  apply Integrable.of_bound ((colorFn_measurable hc i).comp (measurable_const.add measurable_id)).aestronglyMeasurable 1
  exact Eventually.of_forall fun v => by
    change ‖colorFn c i (q+v)‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (colorFn_nonneg c i (q+v))]
    exact colorFn_le_one c i (q+v)
lemma diskAverage_nonneg {k : ℕ} (c : ℂ → Fin k) (ε : ℝ) (i : Fin k) (q : ℂ) :
    0≤diskAverage c ε i q := integral_nonneg (fun v => colorFn_nonneg c i (q+v))
lemma diskAverage_le_one {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) {ε : ℝ} (hε : 0<ε)
    (i : Fin k) (q : ℂ) : diskAverage c ε i q≤1 := by
  have := diskLaw_probability hε
  simpa only [diskAverage,integral_const,probReal_univ,one_smul] using integral_mono (colorFn_integrable (μ := diskLaw ε) hc i q) (integrable_const (1:ℝ))
    (fun v => colorFn_le_one c i (q+v))
lemma diskAverage_sum {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) {ε : ℝ} (hε : 0<ε)
    (q : ℂ) : ∑ i,diskAverage c ε i q=1 := by
  have := diskLaw_probability hε
  simp only [diskAverage]
  rw [← integral_finsetSum _ (fun i _ => colorFn_integrable (μ := diskLaw ε) hc i q)]
  simp [colorFn]
end EuclideanFiveColor
end

noncomputable section
open scoped Classical symmDiff
open Set Filter Topology MeasureTheory MeasureTheory.Measure
namespace EuclideanFiveColor
lemma volumeReal_ball (q : ℂ) {ε : ℝ} (hε : 0≤ε) : volume.real (Metric.ball q ε)=Real.pi*ε^2 := by
  simp [Measure.real,Complex.volume_ball,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hε,mul_comm]
lemma diskAverage_area {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (ε : ℝ)
    (i : Fin k) (q : ℂ) : diskAverage c ε i q=
      volume.real (Metric.ball q ε ∩ {z | c z=i})/volume.real (Metric.ball (0:ℂ) ε) := by
  have he : (fun v : ℂ => q+v) ⁻¹' Metric.ball q ε = Metric.ball 0 ε := by
    ext v
    simp [Metric.mem_ball,dist_eq_norm]
  have hi := (measurePreserving_add_left (volume : Measure ℂ) q).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft q).measurableEmbedding (colorFn c i) (Metric.ball q ε)
  rw [he] at hi
  unfold diskAverage diskLaw
  rw [integral_smul_measure,ENNReal.toReal_inv,hi]
  have hid : colorFn c i=({z | c z=i} : Set ℂ).indicator (fun _ => (1:ℝ)) := by
    funext v
    simp [colorFn,Set.indicator]
  rw [hid]
  rw [setIntegral_indicator (measurableSet_eq_fun hc measurable_const)]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one,div_eq_mul_inv]
  ring
lemma ball_ne_top (q : ℂ) (r : ℝ) : volume (Metric.ball q r) ≠ ⊤ :=
  ((measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall q r).measure_lt_top).ne
lemma symmDiff_balls_subset_annulus (q z : ℂ) (ε : ℝ) :
    Metric.ball q ε ∆ Metric.ball z ε ⊆
      Metric.ball q (ε+dist q z) \ Metric.ball q (ε-dist q z) := by
  intro v hv
  have h1 := dist_triangle v q z
  have h2 := dist_triangle v z q
  rw [dist_comm z q] at h2
  rcases hv with h|h
  · refine ⟨?_,?_⟩
    · change dist v q < ε+dist q z
      exact lt_of_lt_of_le (show dist v q<ε from h.1) (by linarith [dist_nonneg (x := q) (y := z)])
    · intro hh
      have hz : ε≤dist v z := not_lt.mp h.2
      have hh' : dist v q<ε-dist q z := hh
      linarith
  · refine ⟨?_,?_⟩
    · exact lt_of_le_of_lt h2 (by have hh : dist v z<ε := h.1; linarith)
    · intro hh
      have hz : ε≤dist v q := not_lt.mp h.2
      have hh' : dist v q<ε-dist q z := hh
      linarith [dist_nonneg (x := q) (y := z)]
lemma measure_inter_ball_difference (A : Set ℂ) (hA : MeasurableSet A) (q z : ℂ)
    {ε : ℝ} (hd : dist q z≤ε) :
    |volume.real (Metric.ball q ε ∩ A)-volume.real (Metric.ball z ε ∩ A)|≤
      4*Real.pi*ε*dist q z := by
  have hsub : (Metric.ball q ε ∩ A) ∆ (Metric.ball z ε ∩ A) ⊆
      Metric.ball q ε ∆ Metric.ball z ε := by
    intro v hv
    rcases hv with h|h
    · exact Or.inl ⟨h.1.1,fun hvz => h.2 ⟨hvz,h.1.2⟩⟩
    · exact Or.inr ⟨h.1.1,fun hvz => h.2 ⟨hvz,h.1.2⟩⟩
  have hi := abs_measureReal_sub_le_measureReal_symmDiff' (Metric.isOpen_ball.measurableSet.inter hA).nullMeasurableSet
    (Metric.isOpen_ball.measurableSet.inter hA).nullMeasurableSet
    (measure_ne_top_of_subset inter_subset_left (ball_ne_top q ε))
    (measure_ne_top_of_subset inter_subset_left (ball_ne_top z ε))
  have hm := measureReal_mono (hsub.trans (symmDiff_balls_subset_annulus q z ε))
    (measure_ne_top_of_subset sdiff_subset (ball_ne_top q (ε+dist q z)))
  apply hi.trans (hm.trans_eq ?_)
  rw [measureReal_sdiff (Metric.ball_subset_ball (by linarith [dist_nonneg (x := q) (y := z)]))
    measurableSet_ball (ball_ne_top q (ε+dist q z)),volumeReal_ball q (by linarith [dist_nonneg (x := q) (y := z)]),
    volumeReal_ball q (sub_nonneg.mpr hd)]
  ring
lemma diskAverage_lipschitz {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) {ε : ℝ} (hε : 0<ε)
    (i : Fin k) : LipschitzWith ⟨4/ε,by positivity⟩ (diskAverage c ε i) := by
  apply LipschitzWith.of_dist_le_mul
  intro q z
  change |diskAverage c ε i q-diskAverage c ε i z|≤(4/ε)*dist q z
  by_cases hd : dist q z≤ε
  · rw [diskAverage_area hc,diskAverage_area hc,← sub_div,abs_div,
      volumeReal_ball 0 hε.le,abs_of_pos (by positivity : 0<Real.pi*ε^2)]
    apply (div_le_iff₀ (by positivity : 0<Real.pi*ε^2)).mpr
    have hh := measure_inter_ball_difference {v | c v=i} (measurableSet_eq_fun hc measurable_const) q z hd
    apply hh.trans_eq
    field_simp
  · have hb : |diskAverage c ε i q-diskAverage c ε i z|≤1 := by
      rw [abs_le]
      constructor <;> linarith [diskAverage_nonneg c ε i q,diskAverage_nonneg c ε i z,
        diskAverage_le_one hc hε i q,diskAverage_le_one hc hε i z]
    apply hb.trans
    rw [div_mul_eq_mul_div,le_div_iff₀ hε]
    linarith [not_le.mp hd]
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory MeasureTheory.Measure
namespace EuclideanFiveColor
variable {k : ℕ} {c : ℂ → Fin k}
lemma colorFn_norm_le_one (i : Fin k) (z : ℂ) : ‖colorFn c i z‖≤1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (colorFn_nonneg c i z)]
  exact colorFn_le_one c i z
lemma diskAverage_product {ε : ℝ} (hε : 0<ε) (i j : Fin k) (q : ℂ) :
    diskAverage c ε i q*diskAverage c ε j q =
      ∫ (h : ℂ × ℂ), colorFn c i (q+h.1)*colorFn c j (q+h.2) ∂(diskLaw ε).prod (diskLaw ε) := by
  have := diskLaw_probability hε
  exact (integral_prod_mul _ _).symm
lemma disk_overlap_swap (hc : Measurable c) {ε : ℝ} (hε : 0<ε) (i j : Fin k) (x : ℂ) (r : ℝ) :
    (∫ q in Metric.ball x r, diskAverage c ε i q*diskAverage c ε j q) =
      ∫ (h : ℂ × ℂ), (∫ q in Metric.ball x r, colorFn c i (q+h.1)*colorFn c j (q+h.2))
        ∂(diskLaw ε).prod (diskLaw ε) := by
  have := diskLaw_probability hε
  have : IsFiniteMeasure (volume.restrict (Metric.ball x r)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (ball_ne_top x r).lt_top⟩
  simp_rw [diskAverage_product hε]
  apply integral_integral_swap
  apply Integrable.of_bound
    (((colorFn_measurable hc i).comp (measurable_fst.add measurable_snd.fst)).mul
      ((colorFn_measurable hc j).comp (measurable_fst.add measurable_snd.snd))).aestronglyMeasurable 1
  exact Eventually.of_forall fun z => by
    change ‖colorFn c i _*colorFn c j _‖≤1
    rw [norm_mul]
    exact (mul_le_mul (colorFn_norm_le_one i _) (colorFn_norm_le_one j _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
lemma root_overlap_bound (hc : Measurable c) (i j : Fin k) (x : ℂ) (r R : ℝ) (h₁ h₂ : ℂ)
    (hr : r+‖h₁‖≤R) :
    (∫ q in Metric.ball x r, colorFn c i (q+h₁)*colorFn c j (q+h₂))≤
      volume.real (transitionSet c i j x R (h₂-h₁)) := by
  let T := transitionSet c i j x R (h₂-h₁)
  have hT : MeasurableSet T := transitionSet_measurable c hc i j x R (h₂-h₁)
  have hTf : volume T≠⊤ := (transitionSet_finite c i j x R (h₂-h₁)).ne
  have hI : Integrable (fun q : ℂ => T.indicator (fun _ => (1:ℝ)) (q+h₁)) volume := by
    exact ((integrable_indicator_iff hT).mpr (integrableOn_const (C := (1:ℝ)) hTf)).comp_add_right h₁
  have : IsFiniteMeasure (volume.restrict (Metric.ball x r)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (ball_ne_top x r).lt_top⟩
  have hF : Integrable (fun q : ℂ => colorFn c i (q+h₁)*colorFn c j (q+h₂))
      (volume.restrict (Metric.ball x r)) := by
    apply Integrable.of_bound (((colorFn_measurable hc i).comp (measurable_id.add_const h₁)).mul
      ((colorFn_measurable hc j).comp (measurable_id.add_const h₂))).aestronglyMeasurable 1
    exact Eventually.of_forall fun q => by
      change ‖colorFn c i (q+h₁)*colorFn c j (q+h₂)‖≤1
      rw [norm_mul]
      simpa using mul_le_mul (colorFn_norm_le_one i (q+h₁)) (colorFn_norm_le_one j (q+h₂)) (norm_nonneg _) zero_le_one
  have hle : (∫ q in Metric.ball x r, colorFn c i (q+h₁)*colorFn c j (q+h₂))≤
      ∫ q in Metric.ball x r, T.indicator (fun _ => (1:ℝ)) (q+h₁) := by
    apply integral_mono_ae hF hI.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball] with q hq
    by_cases h1 : c (q+h₁)=i
    · by_cases h2 : c (q+h₂)=j
      · have hmem : q+h₁∈T := by
          refine ⟨?_,Or.inl ⟨h1,?_⟩⟩
          · change dist (q+h₁) x<R
            have he : q+h₁-x=(q-x)+h₁ := by ring
            rw [dist_eq_norm,he]
            have hq' : ‖q-x‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hq
            exact (norm_add_le _ _).trans_lt (by linarith)
          · convert h2 using 1; congr 1; ring
        simp [colorFn,h1,h2,Set.indicator_of_mem hmem]
      · simp only [colorFn,ite_eq_left h1,ite_eq_right h2,mul_zero]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · simp only [colorFn,ite_eq_right h1,zero_mul]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  apply hle.trans
  calc
    (∫ q in Metric.ball x r, T.indicator (fun _ => (1:ℝ)) (q+h₁)) ≤
      ∫ q, T.indicator (fun _ => (1:ℝ)) (q+h₁) :=
        integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun q => Set.indicator_nonneg (fun _ _ => zero_le_one) _) hI
    _ = volume.real T := by
      rw [(measurePreserving_add_right volume h₁).integral_comp
        (MeasurableEquiv.addRight h₁).measurableEmbedding]
      rw [integral_indicator hT]
      simp
lemma root_overlap_zero (i j : Fin k) (hne : i≠j) (x : ℂ) (r : ℝ) (h : ℂ) :
    (∫ q in Metric.ball x r, colorFn c i (q+h)*colorFn c j (q+h))=0 := by
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun q => by
    simp only [colorFn]
    split_ifs with hi hj hj <;> try norm_num
    exact False.elim (hne (hi.symm.trans hj))
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory MeasureTheory.Measure
namespace EuclideanFiveColor
variable {k : ℕ} {c : ℂ → Fin k}
lemma missing_edge_uniform {i j : Fin k} (hne : i≠j) {x : ℂ} {R : ℝ}
    (ht : Tendsto (transitionRatio c i j x R) (𝓝[≠] (0:ℂ)) (𝓝 0))
    {η : ℝ} (hη : 0<η) : ∃ δ>0, ∀ h : ℂ, ‖h‖<δ →
      volume.real (transitionSet c i j x R h)≤η*‖h‖ := by
  have hev : ∀ᶠ h in 𝓝[≠] (0:ℂ), transitionRatio c i j x R h<ENNReal.ofReal η :=
    ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨δ,hδ,fun h hh => ?_⟩
  by_cases hz : h=0
  · subst h
    have he : transitionSet c i j x R 0=∅ := by
      ext q
      simp only [transitionSet,mem_ofPred_eq,add_zero,mem_empty_iff_false,iff_false]
      rintro ⟨_,hh|hh⟩
      · exact hne (hh.1.symm.trans hh.2)
      · exact hne (hh.2.symm.trans hh.1)
    simp [he]
  · have hr : transitionRatio c i j x R h ≤ ENNReal.ofReal η :=
      le_of_lt (hd ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hh,hz⟩)
    have hm := (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hz)).ne'
      ENNReal.ofReal_ne_top).mp hr
    have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hm
    simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_ofReal hη.le,ENNReal.toReal_ofReal (norm_nonneg h)] using hreal
lemma diskLaw_mem_ball {ε : ℝ} (_hε : 0<ε) : ∀ᵐ h ∂diskLaw ε, h∈Metric.ball (0:ℂ) ε := by
  rw [diskLaw,Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr (ball_ne_top 0 ε))]
  exact ae_restrict_mem measurableSet_ball
lemma disk_overlap_bound (hc : Measurable c) {i j : Fin k} (hne : i≠j)
    (x : ℂ) (r R : ℝ) {ε δ η : ℝ} (hε : 0<ε) (hη : 0≤η)
    (hr : r+ε≤R) (hδ : 2*ε≤δ)
    (hd : ∀ h : ℂ, ‖h‖<δ → volume.real (transitionSet c i j x R h)≤η*‖h‖) :
    (∫ q in Metric.ball x r, diskAverage c ε i q*diskAverage c ε j q)≤2*η*ε := by
  have := diskLaw_probability hε
  rw [disk_overlap_swap hc hε]
  have hab : ∀ᵐ h ∂(diskLaw ε).prod (diskLaw ε), h.1∈Metric.ball (0:ℂ) ε ∧ h.2∈Metric.ball (0:ℂ) ε := by
    apply (ae_prod_iff_ae_ae (measurableSet_ball.prod measurableSet_ball)).mpr
    filter_upwards [diskLaw_mem_ball hε] with h₁ hh₁
    filter_upwards [diskLaw_mem_ball hε] with h₂ hh₂
    exact ⟨hh₁,hh₂⟩
  have hh : ∀ᵐ h ∂(diskLaw ε).prod (diskLaw ε),
      (∫ q in Metric.ball x r, colorFn c i (q+h.1)*colorFn c j (q+h.2))≤2*η*ε := by
    filter_upwards [hab] with h hh
    have ha : ‖h.1‖<ε := by simpa only [Metric.mem_ball,dist_zero_right] using hh.1
    have hb : ‖h.2‖<ε := by simpa only [Metric.mem_ball,dist_zero_right] using hh.2
    by_cases he : h.1=h.2
    · rw [he,root_overlap_zero i j hne]
      positivity
    · have hn : ‖h.2-h.1‖ < 2*ε := (norm_sub_le _ _).trans_lt (by linarith)
      apply (root_overlap_bound hc i j x r R h.1 h.2 (by linarith)).trans
      apply (hd _ (hn.trans_le hδ)).trans
      nlinarith
  have hn : 0≤ᵐ[(diskLaw ε).prod (diskLaw ε)]
      fun h => ∫ q in Metric.ball x r, colorFn c i (q+h.1)*colorFn c j (q+h.2) :=
    Eventually.of_forall fun h => integral_nonneg fun q => mul_nonneg (colorFn_nonneg c i _) (colorFn_nonneg c j _)
  simpa using integral_mono_of_nonneg hn (integrable_const (2*η*ε)) hh
lemma missing_edge_overlap (hc : Measurable c) {i j : Fin k} (hne : i≠j) {x : ℂ}
    (he : ¬TransitionEdge c i j x) : ∃ R>0, ∀ r<R,
      Tendsto (fun ε : ℝ => (∫ q in Metric.ball x r, diskAverage c ε i q*diskAverage c ε j q)/ε)
        (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R,hR,ht⟩ := missing_edge_lim c i j hne he
  refine ⟨R,hR,fun r hr => ?_⟩
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ha.trans_le (div_nonneg (integral_nonneg fun q => mul_nonneg (diskAverage_nonneg c ε i q)
      (diskAverage_nonneg c ε j q)) (le_of_lt hε))
  · intro b hb
    obtain ⟨δ,hδ,hd⟩ := missing_edge_uniform hne ht (show 0<b/4 by linarith)
    have hv : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < min (R-r) (δ/2) :=
      (eventually_lt_nhds (lt_min (by linarith) (by linarith))).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hv] with ε hε hv
    have hh := disk_overlap_bound hc hne x r R (show 0<ε from hε) (show 0≤b/4 by linarith)
      (by have := (lt_min_iff.mp hv).1; linarith) (by have := (lt_min_iff.mp hv).2; linarith) hd
    apply (div_le_div_of_nonneg_right hh (le_of_lt hε)).trans_lt
    have hz : ε≠0 := ne_of_gt hε
    field_simp
    linarith
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_PlanarCovers
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped NNReal ENNReal
namespace EuclideanFiveColor
lemma finite_packed_cover {X : Type*} [MetricSpace X] {A : Set X} (hA : TotallyBounded A)
    {ρ : ℝ} (hρ : 0<ρ) : ∃ C : Finset X, (↑C : Set X)⊆A ∧
      (∀ x∈A, ∃ c∈C, dist x c≤ρ) ∧
      (↑C : Set X).Pairwise (fun x y => ρ<dist x y) := by
  classical
  let e : ℝ≥0 := ⟨ρ,hρ.le⟩
  obtain ⟨D,_,hD,hcover⟩ := Metric.exists_finite_isCover_of_totallyBounded
    (s := A) (ε := e/2) (by exact div_ne_zero (ne_of_gt (show (0 : ℝ≥0)<e from hρ)) (by norm_num) : e/2≠0) hA
  have hp : Metric.packingNumber e A≠⊤ := by
    have hh := (Metric.packingNumber_two_mul_le_externalCoveringNumber (e/2) A).trans
      hcover.externalCoveringNumber_le_encard
    have he : 2*(e/2)=e := by ring
    rw [he] at hh
    exact ne_top_of_le_ne_top hD.encard_lt_top.ne hh
  let C := Metric.maximalSeparatedSet e A
  have hCf : C.Finite := Set.encard_ne_top_iff.mp (by
    change (Metric.maximalSeparatedSet e A).encard≠⊤
    rwa [Metric.encard_maximalSeparatedSet hp])
  refine ⟨hCf.toFinset,?_,?_,?_⟩
  · simpa only [Set.Finite.coe_toFinset] using (Metric.maximalSeparatedSet_subset (ε := e) (A := A))
  · intro x hx
    obtain ⟨c,hc,hd⟩ := Metric.isCover_maximalSeparatedSet hp hx
    refine ⟨c,hCf.mem_toFinset.mpr hc,?_⟩
    change edist x c≤(e : ℝ≥0∞) at hd
    exact (ENNReal.ofReal_le_coe (b := e)).mp (by simpa only [edist_dist] using hd)
  · intro x hx y hy hne
    have hd := Metric.isSeparated_maximalSeparatedSet (ε := e) (A := A)
      (hCf.mem_toFinset.mp hx) (hCf.mem_toFinset.mp hy) hne
    exact (ENNReal.coe_lt_ofReal (a := e)).mp (by simpa only [edist_dist] using hd)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory Function
namespace EuclideanFiveColor
variable {k : ℕ} {c : ℂ → Fin k}
lemma diskAverage_product_integrable (hc : Measurable c) {ε : ℝ} (hε : 0<ε)
    (i j : Fin k) (x : ℂ) (r : ℝ) :
    IntegrableOn (fun q => diskAverage c ε i q*diskAverage c ε j q) (Metric.ball x r) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball x r)) := ⟨by simpa using (lt_top_iff_ne_top.mpr (ball_ne_top x r))⟩
  apply Integrable.of_bound (((diskAverage_lipschitz hc hε i).continuous.mul
    (diskAverage_lipschitz hc hε j).continuous).aestronglyMeasurable) 1
  exact Eventually.of_forall fun q => by
    change ‖diskAverage c ε i q*diskAverage c ε j q‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (diskAverage_nonneg c ε i q) (diskAverage_nonneg c ε j q))]
    exact (mul_le_of_le_one_left (diskAverage_nonneg c ε j q)
      (diskAverage_le_one hc hε i q)).trans (diskAverage_le_one hc hε j q)
lemma finite_disk_overlap_cover (hc : Measurable c) {ε α : ℝ} (hε : 0<ε) (hα : 0<α)
    (i j : Fin k) (x : ℂ) {s r : ℝ} (hr : s+α*ε/16 ≤ r) :
    ∃ C : Finset ℂ, (∀ q∈Metric.ball x s,
        α<diskAverage c ε i q → α<diskAverage c ε j q →
        ∃ z∈C, q∈Metric.ball z (α*ε/4)) ∧
      (C.card:ℝ)*(α*ε/4) ≤ (256/(Real.pi*α^3))*
        ((∫ q in Metric.ball x r, diskAverage c ε i q*diskAverage c ε j q)/ε) := by
  classical
  let ρ := α*ε/8
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  let A := {q | q∈Metric.ball x s ∧ α<diskAverage c ε i q ∧ α<diskAverage c ε j q}
  obtain ⟨C,hCA,hcover,hsep⟩ := finite_packed_cover
    (A := A) ((isCompact_closedBall x s).totallyBounded.subset
      (fun _ hq => Metric.ball_subset_closedBall hq.1)) hρ
  have hsub : ∀ z∈C, Metric.ball z (ρ/2)⊆Metric.ball x r := by
    intro z hz q hq
    have hz' := (hCA hz).1
    have hq' : dist q z<ρ/2 := hq
    have hz'' : dist z x < s := hz'
    have hd := dist_triangle q z x
    change dist q x < r
    dsimp [ρ] at hq'
    linarith
  have hlow : ∀ z∈C, ∀ q∈Metric.ball z (ρ/2),
      α^2/4 ≤ diskAverage c ε i q*diskAverage c ε j q := by
    intro z hz q hq
    have hp (a : Fin k) (ha : α<diskAverage c ε a z) : α/2≤diskAverage c ε a q := by
      have hh := (diskAverage_lipschitz hc hε a).dist_le_mul q z
      change |diskAverage c ε a q-diskAverage c ε a z|≤(4/ε)*dist q z at hh
      have hh' := (abs_le.mp hh).1
      have hd : dist q z<ρ/2 := hq
      have hmul : (4/ε)*dist q z<α/2 := by
        calc (4/ε)*dist q z < (4/ε)*(ρ/2) := mul_lt_mul_of_pos_left hd (by positivity)
          _ = α/4 := by dsimp [ρ]; field_simp; ring
          _ < α/2 := by linarith
      linarith
    have hi := hp i (hCA hz).2.1
    have hj := hp j (hCA hz).2.2
    calc α^2/4 = (α/2)*(α/2) := by ring
      _ ≤ _ := mul_le_mul hi hj (by positivity) (diskAverage_nonneg c ε i q)
  have hdj : (↑C : Set ℂ).Pairwise (Disjoint on fun z => Metric.ball z (ρ/2)) := by
    intro z hz w hw hne
    apply Set.disjoint_left.mpr
    intro q hq hq'
    have hh := dist_triangle z q w
    have h₁ : dist q z<ρ/2 := hq
    have h₂ : dist q w<ρ/2 := hq'
    rw [dist_comm z q] at hh
    linarith [hsep hz hw hne]
  have hint : (C.card:ℝ)*(Real.pi*(ρ/2)^2*(α^2/4)) ≤
      ∫ q in Metric.ball x r, diskAverage c ε i q*diskAverage c ε j q := by
    calc (C.card:ℝ)*(Real.pi*(ρ/2)^2*(α^2/4)) =
        ∑ z∈C, ∫ _q in Metric.ball z (ρ/2), (α^2/4) := by
          simp only [setIntegral_const,smul_eq_mul,volumeReal_ball _ (by positivity : 0≤ρ/2)]
          simp
      _ ≤ ∑ z∈C, ∫ q in Metric.ball z (ρ/2), diskAverage c ε i q*diskAverage c ε j q := by
        apply Finset.sum_le_sum
        intro z hz
        apply setIntegral_mono_on (integrableOn_const (ball_ne_top z (ρ/2)))
          (diskAverage_product_integrable hc hε i j z (ρ/2)) measurableSet_ball
        exact hlow z hz
      _ = ∫ q in ⋃ z∈C, Metric.ball z (ρ/2), diskAverage c ε i q*diskAverage c ε j q := by
        exact (integral_biUnion_finset C (fun _ _ => measurableSet_ball) hdj
          (fun z _ => diskAverage_product_integrable hc hε i j z (ρ/2))).symm
      _ ≤ _ := setIntegral_mono_set (diskAverage_product_integrable hc hε i j x r)
        (Eventually.of_forall fun q => mul_nonneg (diskAverage_nonneg c ε i q) (diskAverage_nonneg c ε j q))
        (Eventually.of_forall (fun q hq => by
          obtain ⟨z,hz,hq⟩ := mem_iUnion₂.mp hq
          exact hsub z hz hq))
  refine ⟨C,?_,?_⟩
  · intro q hq hi hj
    obtain ⟨z,hz,hd⟩ := hcover q ⟨hq,hi,hj⟩
    refine ⟨z,hz,?_⟩
    change dist q z<α*ε/4
    dsimp [ρ] at hd
    nlinarith [mul_pos hα hε]
  · have hconst : 0<Real.pi*α^3 := by positivity
    rw [← mul_div_assoc (256/(Real.pi*α^3)) _ ε]
    apply (le_div_iff₀ hε).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hconst).mpr
    dsimp [ρ] at hint
    nlinarith [Real.pi_pos]
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} {c : ℂ → Fin k}
lemma missing_edge_disk_cover (hc : Measurable c) {i j : Fin k} (hne : i≠j) {x : ℂ}
    (he : ¬TransitionEdge c i j x) : ∃ R>0, ∀ s<R, ∀ α>0, ∀ η>0,
      ∃ δ>0, ∀ ε, 0<ε → ε<δ → ∃ C : Finset ℂ,
        (∀ q∈Metric.ball x s, α<diskAverage c ε i q → α<diskAverage c ε j q →
          ∃ z∈C, q∈Metric.ball z (α*ε/4)) ∧ (C.card:ℝ)*(α*ε/4)<η := by
  obtain ⟨R,hR,ht⟩ := missing_edge_overlap hc hne he
  refine ⟨R,hR,fun s hs α hα η hη => ?_⟩
  let r := (s+R)/2
  have hsr : s < r := by dsimp [r]; linarith
  have hrR : r<R := by dsimp [r]; linarith
  have hlim := (ht r hrR).const_mul (256/(Real.pi*α^3))
  rw [mul_zero] at hlim
  have he₁ := hlim.eventually (gt_mem_nhds hη)
  have he₂ : ∀ᶠ ε : ℝ in 𝓝[>] 0, s+α*ε/16 < r := by
    have ht' : Tendsto (fun ε : ℝ => s+α*ε/16) (𝓝[>] 0) (𝓝 s) := by
      have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds (x := s)).add ((hid.const_mul α).div_const 16)
    exact ht'.eventually (gt_mem_nhds hsr)
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhdsWithin_iff.mp (he₁.and he₂)
  refine ⟨δ,hδ,fun ε hε hεδ => ?_⟩
  have hε' := hd (show ε∈Metric.ball 0 δ∩Ioi 0 from ⟨by simpa [Real.dist_eq,abs_of_pos hε] using hεδ,hε⟩)
  obtain ⟨C,hC,hb⟩ := finite_disk_overlap_cover hc hε hα i j x hε'.2.le
  exact ⟨C,hC,hb.trans_lt hε'.1⟩
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_GraphRealization
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace EuclideanFiveColor
/-- The compact contact partition used in the manuscript's annular-crossing proof.
This reuses Mathlib's Hausdorff component quotient and its profinite separation theorem. -/
lemma compact_component_partition {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {I O : Set X} (hI : IsCompact I) (hO : IsCompact O)
    (hno : ∀x∈I, Disjoint (connectedComponent x) O) :
    ∃Z₁ Z₂ : Set X, IsCompact Z₁ ∧ IsCompact Z₂ ∧ Disjoint Z₁ Z₂ ∧
      Z₁∪Z₂=univ ∧ I⊆Z₁ ∧ O⊆Z₂ := by
  let q : X → ConnectedComponents X := ConnectedComponents.mk
  have hq : Continuous q := ConnectedComponents.continuous_coe
  have hid : Disjoint (q '' I) (q '' O) := by
    apply disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    have hxy : y∈connectedComponent x := ConnectedComponents.coe_eq_coe'.mp he
    exact Set.disjoint_left.mp (hno x hx) hxy hy
  have hsub : q '' I⊆(q '' O)ᶜ := Set.disjoint_left.mp hid
  obtain ⟨C,hC,hIC,hCO⟩ := exists_clopen_of_closed_subset_open
    (hI.image hq).isClosed (hO.image hq).isClosed.isOpen_compl hsub
  refine ⟨q ⁻¹' C,q ⁻¹' Cᶜ,(hC.isClosed.preimage hq).isCompact,
    (hC.compl.isClosed.preimage hq).isCompact,?_,?_,?_,?_⟩
  · exact disjoint_compl_right.preimage q
  · simp only [←preimage_union,union_compl_self,preimage_univ]
  · intro x hx
    exact hIC ⟨x,hx,rfl⟩
  · intro x hx hxc
    exact hCO hxc ⟨x,hx,rfl⟩
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
universe u
namespace EuclideanFiveColor
lemma graphRealization_singleton {V : Type u} [Subsingleton V] (G : SimpleGraph V) (a : V) :
    graphRealization G={graphVertex a} := by
  ext p
  constructor
  · rintro ⟨i,j,_,t,_,rfl⟩
    simp [Subsingleton.elim i a,Subsingleton.elim j a]
  · rintro rfl
    exact graphVertex_mem G a
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
universe u
namespace EuclideanFiveColor
lemma graphRealization_of_two_support {V : Type u} [Fintype V]
    {G : SimpleGraph V} {p : V → ℝ} (hn : ∀i,0≤p i) (hs : ∑i,p i=1)
    {a b : V} (hab : a=b ∨ G.Adj a b) (hsupp : ∀j,j≠a → j≠b → p j=0) :
    p∈graphRealization G := by
  by_cases he : a=b
  · subst b
    have ha : p a=1 := by
      have hh : ∑i,p i=p a := Finset.sum_eq_single a (fun i _ hi => hsupp i hi hi) (by simp)
      linarith
    have hp : p=graphVertex a := by
      funext i
      by_cases hi : i=a
      · subst i; simp [graphVertex,ha]
      · simp [graphVertex,hi,hsupp i hi hi]
    rw [hp]; exact graphVertex_mem _ _
  · have he' : b≠a := Ne.symm he
    have hs' : p a+p b=1 := by
      have hh : ∑i∈({a,b} : Finset V),p i=∑i,p i := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
        exact hsupp i hi.1 hi.2
      simpa [he] using hh.trans hs
    refine ⟨a,b,hab,p b,⟨hn _,by linarith [hn a]⟩,?_⟩
    funext i
    rw [graphEdgePoint_apply]
    by_cases hi : i=a
    · subst i; simp [he]; linarith
    · by_cases hj : i=b
      · subst i; simp [he']
      · simp [hi,hj,hsupp i hi hj]

/-- A simplex vector whose positive labels form a clique in a forest is genuinely
in that forest's affine realization, rather than just in the complete graph. -/
theorem simplex_mem_forest {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) {p : V → ℝ} (hn : ∀i,0≤p i) (hs : ∑i,p i=1)
    (hcl : ∀i j,i≠j → 0<p i → 0<p j → G.Adj i j) : p∈graphRealization G := by
  let S : Finset V := Finset.univ.filter fun i => p i≠0
  have hmem (i : V) : i∈S ↔ 0<p i := by simp [S,lt_iff_le_and_ne,hn i,ne_comm]
  have hsum : ∑i∈S,p i=1 := by
    have he : ∑i∈S,p i=∑i,p i := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      simpa [S] using hi
    exact he.trans hs
  have hne : S.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty] at hsum
    norm_num at hsum
  have hcard : S.card≤2 := by
    by_contra hh
    have h3 : 3≤S.card := by omega
    obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq h3
    apply hG.cliqueFree (le_refl 3) T
    refine ⟨?_,hT⟩
    intro i hi j hj hij
    exact hcl i j hij ((hmem i).mp (hTS hi)) ((hmem j).mp (hTS hj))
  by_cases h1 : S.card=1
  · obtain ⟨a,hSa⟩ := Finset.card_eq_one.mp h1
    apply graphRealization_of_two_support hn hs (G:=G) (a:=a) (b:=a) (Or.inl rfl)
    intro j hj _
    by_contra hp
    have hm : j∈S := by simp [S,hp]
    rw [hSa,Finset.mem_singleton] at hm
    exact hj hm
  · have h2 : S.card=2 := by have := hne.card_pos; omega
    obtain ⟨a,b,hab,hS⟩ := Finset.card_eq_two.mp h2
    have ha : 0<p a := (hmem _).mp (by rw [hS]; simp)
    have hb : 0<p b := (hmem _).mp (by rw [hS]; simp)
    apply graphRealization_of_two_support hn hs (Or.inr (hcl a b hab ha hb))
    intro j hja hjb
    by_contra hp
    have hm : j∈S := by simp [S,hp]
    rw [hS] at hm
    simp [hja,hjb] at hm
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology MeasureTheory
namespace EuclideanFiveColor
lemma thresholdTotal_pos {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) (q : ℂ) : 0<thresholdTotal c ε α q := by
  have hs := diskAverage_sum hc hε q
  have hh : 1-5*α ≤ thresholdTotal c ε α q := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5)))
      (fun i _ => le_max_left (diskAverage c ε i q-α) 0)
    simpa [thresholdTotal,thresholdWeight,Finset.sum_sub_distrib,hs] using hh
  linarith
lemma thresholdMap_nonneg {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) (q : ℂ) (i : Fin 5) : 0≤thresholdMap c ε α q i :=
  div_nonneg (le_max_right _ _) (thresholdTotal_pos hc hε hα q).le
lemma thresholdMap_sum {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) (q : ℂ) : ∑i,thresholdMap c ε α q i=1 := by
  unfold thresholdMap
  rw [←Finset.sum_div]
  exact div_self (thresholdTotal_pos hc hε hα q).ne'
lemma thresholdMap_pos {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) (q : ℂ) (i : Fin 5) :
    0<thresholdMap c ε α q i ↔ α<diskAverage c ε i q := by
  rw [thresholdMap,div_pos_iff_of_pos_right (thresholdTotal_pos hc hε hα q)]
  simp [thresholdWeight]
lemma continuous_thresholdMap {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) : Continuous (thresholdMap c ε α) := by
  have hw (i : Fin 5) : Continuous (fun q => thresholdWeight c ε α q i) :=
    ((diskAverage_lipschitz hc hε i).continuous.sub continuous_const).max continuous_const
  have ht : Continuous (thresholdTotal c ε α) := continuous_finsetSum _ (fun i _ => hw i)
  exact continuous_pi fun i => (hw i).div ht (fun q => (thresholdTotal_pos hc hε hα q).ne')
lemma thresholdMap_mem_forest {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) (q : ℂ) {G : SimpleGraph (Fin 5)} (hG : G.IsAcyclic)
    (hb : ∀i j,i≠j → α<diskAverage c ε i q → α<diskAverage c ε j q → G.Adj i j) :
    thresholdMap c ε α q∈graphRealization G := by
  apply simplex_mem_forest hG (thresholdMap_nonneg hc hε hα q) (thresholdMap_sum hc hε hα q)
  intro i j hij hi hj
  exact hb i j hij ((thresholdMap_pos hc hε hα q i).mp hi) ((thresholdMap_pos hc hε hα q j).mp hj)
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma finite_pos_lt {ι : Type*} [Finite ι] (R : ι → ℝ) (hR : ∀i,0<R i) :
    ∃s : ℝ,0 < s ∧ ∀i,s<R i := by
  have hh : ∀ᶠ s : ℝ in 𝓝 0,∀i,s<R i := Filter.eventually_all.mpr fun i => gt_mem_nhds (hR i)
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨δ/2,half_pos hδ,hd ?_⟩
  change dist (δ/2) (0:ℝ)<δ
  rw [Real.dist_eq,sub_zero,abs_of_pos (half_pos hδ)]
  exact half_lt_self hδ
lemma finite_small_scale {ι : Type*} [Finite ι] (P : ι → ℝ → Prop)
    (h : ∀i,∃δ>0,∀ε,0<ε → ε<δ → P i ε) : ∃δ>0,∀ε,0<ε → ε<δ → ∀i,P i ε := by
  choose δ hδ hd using h
  obtain ⟨s,hs,hsi⟩ := finite_pos_lt δ hδ
  exact ⟨s,hs,fun ε hε hεs i => hd i ε hε (hεs.trans (hsi i))⟩

/-- A genuine local forest chart; its exception disks have arbitrarily small total
radius at sufficiently small averaging scale. -/
theorem forest_chart {c : ℂ → Fin 5} (hc : Measurable c) {α : ℝ}
    (hα : 0<α) (hα' : α<1/5) (x : ℂ) (hf : (transitionGraph c x).IsAcyclic) :
    ∃s>0,∀η>0,∃δ>0,∀ε,0<ε → ε<δ → ∃C : Finset ℂ,
      (C.card:ℝ)*(α*ε/4)<η ∧ ∀q∈Metric.ball x s,
      q∉⋃z∈C,Metric.ball z (α*ε/4) → thresholdMap c ε α q∈graphRealization (transitionGraph c x) := by
  have hall : ∀p : Fin 5 × Fin 5,∃R>0, p.1≠p.2 → ¬TransitionEdge c p.1 p.2 x →
      ∀s<R,∀η>0,∃δ>0,∀ε,0<ε → ε<δ → ∃C : Finset ℂ,
        (∀q∈Metric.ball x s,α<diskAverage c ε p.1 q → α<diskAverage c ε p.2 q →
          ∃z∈C,q∈Metric.ball z (α*ε/4)) ∧ (C.card:ℝ)*(α*ε/4)<η := by
    intro p
    by_cases hp : p.1≠p.2 ∧ ¬TransitionEdge c p.1 p.2 x
    · obtain ⟨R,hR,hcov⟩ := missing_edge_disk_cover hc hp.1 hp.2
      exact ⟨R,hR,fun _ _ s hs η hη => hcov s hs α hα η hη⟩
    · exact ⟨1,by norm_num,fun h₁ h₂ => False.elim (hp ⟨h₁,h₂⟩)⟩
  choose R hR hcov using hall
  obtain ⟨s,hs,hsR⟩ := finite_pos_lt R hR
  refine ⟨s,hs,fun η hη => ?_⟩
  let P (p : Fin 5 × Fin 5) (ε : ℝ) : Prop := ∃C : Finset ℂ,
    (C.card:ℝ)*(α*ε/4)<η/25 ∧ (p.1≠p.2 → ¬TransitionEdge c p.1 p.2 x →
      ∀q∈Metric.ball x s,α<diskAverage c ε p.1 q → α<diskAverage c ε p.2 q →
        ∃z∈C,q∈Metric.ball z (α*ε/4))
  have hP : ∀p,∃δ>0,∀ε,0<ε → ε<δ → P p ε := by
    intro p
    by_cases hp : p.1≠p.2 ∧ ¬TransitionEdge c p.1 p.2 x
    · obtain ⟨δ,hδ,hd⟩ := hcov p hp.1 hp.2 s (hsR p) (η/25) (by positivity)
      refine ⟨δ,hδ,fun ε hε hεδ => ?_⟩
      obtain ⟨C,hC,hCr⟩ := hd ε hε hεδ
      exact ⟨C,hCr,fun _ _ => hC⟩
    · refine ⟨1,by norm_num,fun ε _ _ => ⟨∅,by simpa using (show 0<η/25 by positivity),?_⟩⟩
      exact fun h₁ h₂ => False.elim (hp ⟨h₁,h₂⟩)
  obtain ⟨δ,hδ,hd⟩ := finite_small_scale P hP
  refine ⟨δ,hδ,fun ε hε hεδ => ?_⟩
  choose C hCr hC using hd ε hε hεδ
  let T := Finset.univ.biUnion C
  have hr : 0≤α*ε/4 := by positivity
  refine ⟨T,?_,?_⟩
  · have hcard : (T.card:ℝ)≤∑p : Fin 5 × Fin 5,((C p).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := C))
    have hsum : (∑p : Fin 5 × Fin 5,((C p).card:ℝ)*(α*ε/4))<∑_p : Fin 5 × Fin 5,η/25 :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun p _ => hCr p)
    have hb := mul_le_mul_of_nonneg_right hcard hr
    rw [Finset.sum_mul] at hb
    have hsum' : (∑p : Fin 5 × Fin 5,((C p).card:ℝ)*(α*ε/4))<25*(η/25) := by simpa using hsum
    exact hb.trans_lt (by linarith [hsum'])
  · intro q hq hqT
    apply thresholdMap_mem_forest hc hε hα' q hf
    intro i j hij hi hj
    by_contra he
    obtain ⟨z,hz,hqz⟩ := hC (i,j) hij he q hq hi hj
    apply hqT
    exact mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_univ _,hz⟩,hqz⟩⟩
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- Compact local forest control with one Lebesgue radius, chosen before the hole
budget and the disk-average scale. The resulting forest controls the WHOLE nearby
ball off the common exception disks, not merely the compact set. -/
theorem compact_forest_charts {c : ℂ → Fin 5} (hc : Measurable c) {α : ℝ}
    (hα : 0<α) (hα' : α<1/5) (M : Set ℂ) (hM : IsCompact M)
    (hf : ∀x∈M,(transitionGraph c x).IsAcyclic) :
    ∃l>0,∀η>0,∃δ>0,∀ε,0<ε → ε<δ → ∃C : Finset ℂ,
      (C.card:ℝ)*(α*ε/4)<η ∧ ∀a∈M,∃G : SimpleGraph (Fin 5),G.IsAcyclic ∧
      ∀q∈Metric.ball a l,q∉⋃z∈C,Metric.ball z (α*ε/4) → thresholdMap c ε α q∈graphRealization G := by
  choose s hs hchart using fun x : M => forest_chart hc hα hα' x.val (hf x.val x.property)
  have hcover : M⊆⋃x : M,Metric.ball x.val (s x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (hs _)⟩
  obtain ⟨S,hS⟩ := hM.elim_finite_subcover (fun x : M => Metric.ball x.val (s x))
    (fun _ => Metric.isOpen_ball) hcover
  have hS' : M⊆⋃x : S,Metric.ball x.val.val (s x.val) := by
    intro x hx
    obtain ⟨a,ha⟩ := mem_iUnion.mp (hS hx)
    obtain ⟨haS,hxa⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨⟨a,haS⟩,hxa⟩
  obtain ⟨l,hl,hleb⟩ := lebesgue_number_lemma_of_metric hM (fun _ => Metric.isOpen_ball) hS'
  refine ⟨l,hl,fun η hη => ?_⟩
  let β := η/((S.card:ℝ)+1)
  have hβ : 0<β := div_pos hη (by positivity)
  let P (x : S) (ε : ℝ) : Prop := ∃C : Finset ℂ,
    (C.card:ℝ)*(α*ε/4)<β ∧ ∀q∈Metric.ball x.val.val (s x.val),
      q∉⋃z∈C,Metric.ball z (α*ε/4) → thresholdMap c ε α q∈graphRealization (transitionGraph c x.val.val)
  obtain ⟨δ,hδ,hd⟩ := finite_small_scale P (fun x => hchart x.val β hβ)
  refine ⟨δ,hδ,fun ε hε hεδ => ?_⟩
  choose C hCr hC using hd ε hε hεδ
  let T := Finset.univ.biUnion C
  refine ⟨T,?_,?_⟩
  · have hcard : (T.card:ℝ)≤∑p : S,((C p).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := C))
    have hb := mul_le_mul_of_nonneg_right hcard (show 0≤α*ε/4 by positivity)
    rw [Finset.sum_mul] at hb
    have hsum := Finset.sum_le_sum (s:=(Finset.univ : Finset S)) (fun p _ => (hCr p).le)
    have hsum' : (∑p:S,((C p).card:ℝ)*(α*ε/4))≤(S.card:ℝ)*β := by simpa using hsum
    have hβeq : β*((S.card:ℝ)+1)=η := div_mul_cancel₀ η (by positivity)
    exact hb.trans hsum' |>.trans_lt (by nlinarith)
  · intro a ha
    obtain ⟨x,hx⟩ := hleb a ha
    refine ⟨transitionGraph c x.val.val,hf x.val.val x.val.property,fun q hq hqT => ?_⟩
    apply hC x q (hx hq)
    intro hh
    obtain ⟨z,hz⟩ := mem_iUnion.mp hh
    obtain ⟨hzC,hqz⟩ := mem_iUnion.mp hz
    exact hqT (mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,hzC⟩,hqz⟩⟩)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_DiskExtension
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
namespace MarkedDisk

lemma merge {a b : MarkedDisk} {L : Set ℂ} (ha : a.Valid L) (hb : b.Valid L)
    (hab : ¬Disjoint a.closedBall b.closedBall) {η : ℝ} (hη : 0<η) :
    ∃d : MarkedDisk, d.Valid L ∧ a.closedBall⊆d.ball ∧ b.closedBall⊆d.ball ∧
      d.radius≤a.radius+b.radius+η ∧ d.noncoreCost≤a.noncoreCost+b.noncoreCost+η ∧ d.core=(a.core || b.core) := by
  obtain ⟨z,hza,hzb⟩ := Set.not_disjoint_iff.mp hab
  have hd : dist a.center b.center≤a.radius+b.radius :=
    (dist_triangle a.center z b.center).trans (add_le_add (by simpa [closedBall,dist_comm] using hza) hzb)
  let t : ℝ := b.radius/(a.radius+b.radius)
  have hrs : 0<a.radius+b.radius := add_pos ha.1 hb.1
  have ht0 : 0≤t := (div_pos hb.1 hrs).le
  have ht1 : t≤1 := (div_le_one hrs).mpr (by linarith [ha.1])
  let c := AffineMap.lineMap a.center b.center t
  have hca : dist a.center c≤b.radius := by
    rw [dist_left_lineMap,Real.norm_of_nonneg ht0]
    calc t*dist a.center b.center ≤ t*(a.radius+b.radius) := mul_le_mul_of_nonneg_left hd ht0
         _ = b.radius := by dsimp [t]; field_simp
  have hcb : dist b.center c≤a.radius := by
    rw [dist_right_lineMap,Real.norm_of_nonneg (sub_nonneg.mpr ht1)]
    calc (1-t)*dist a.center b.center ≤ (1-t)*(a.radius+b.radius) :=
            mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr ht1)
         _ = a.radius := by dsimp [t]; field_simp; ring
  let d : MarkedDisk := ⟨c,a.radius+b.radius+η,a.core || b.core⟩
  have hA : a.closedBall⊆d.ball := by
    intro q hq
    have hq' : dist q a.center≤a.radius := hq
    change dist q c<a.radius+b.radius+η
    exact lt_of_le_of_lt (dist_triangle q a.center c) (by linarith)
  have hB : b.closedBall⊆d.ball := by
    intro q hq
    have hq' : dist q b.center≤b.radius := hq
    change dist q c<a.radius+b.radius+η
    exact lt_of_le_of_lt (dist_triangle q b.center c) (by linarith)
  refine ⟨d,⟨by dsimp [d]; linarith,?_⟩,hA,hB,le_refl _,?_,rfl⟩
  · intro hc
    have hc' : a.core=true ∨ b.core=true := by cases hca : a.core <;> cases hcb : b.core <;> simp_all [d]
    rcases hc' with hh|hh
    · obtain ⟨x,hx,hxa⟩ := ha.2 hh
      exact ⟨x,hx,hA (Metric.ball_subset_closedBall hxa)⟩
    · obtain ⟨x,hx,hxb⟩ := hb.2 hh
      exact ⟨x,hx,hB (Metric.ball_subset_closedBall hxb)⟩
  · dsimp [noncoreCost,d]
    cases a.core <;> cases b.core <;> simp <;> linarith [ha.1,hb.1]
end MarkedDisk
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
namespace MarkedDisk
lemma erased_pair_sum {D : Type*} [DecidableEq D] (S : Finset D) {a b : D}
    (ha : a∈S) (hb : b∈S) (hab : a≠b) (f : D → ℝ) :
    (∑x∈(S.erase a).erase b,f x)+f a+f b=∑x∈S,f x := by
  have h1 := Finset.sum_erase_add S f ha
  have h2 := Finset.sum_erase_add (S.erase a) f (Finset.mem_erase.mpr ⟨hab.symm,hb⟩)
  linarith
lemma merge_sum_bound {D : Type*} [DecidableEq D] (S : Finset D) {a b d : D}
    (ha : a∈S) (hb : b∈S) (hab : a≠b) (f : D → ℝ) {η : ℝ}
    (hd0 : 0≤f d) (hd : f d≤f a+f b+η) :
    (∑x∈insert d ((S.erase a).erase b),f x)≤(∑x∈S,f x)+η := by
  have hs := erased_pair_sum S ha hb hab f
  by_cases hmem : d∈(S.erase a).erase b
  · rw [Finset.insert_eq_of_mem hmem]
    linarith
  · rw [Finset.sum_insert hmem]
    linarith

/-- Finite disk merging with separate total and non-core radius budgets. Strict
containment at merges, and the retained core witness, are both included. -/
theorem separate (S : Finset MarkedDisk) {L : Set ℂ} (hS : ∀d∈S,d.Valid L)
    {η : ℝ} (hη : 0<η) : ∃T : Finset MarkedDisk,
      (∀d∈T,d.Valid L) ∧ (T : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall) ∧
      (∀d∈S,∃e∈T,d.ball⊆e.ball ∧ (d.core=true → e.core=true)) ∧
      (∑d∈T,d.radius)<(∑d∈S,d.radius)+η ∧
      (∑d∈T,d.noncoreCost)<(∑d∈S,d.noncoreCost)+η := by
  suffices hh : ∀n : ℕ, ∀S : Finset MarkedDisk, S.card=n →
      (∀d∈S,d.Valid L) → ∀η : ℝ,0<η → ∃T : Finset MarkedDisk,
      (∀d∈T,d.Valid L) ∧ (T : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall) ∧
      (∀d∈S,∃e∈T,d.ball⊆e.ball ∧ (d.core=true → e.core=true)) ∧
      (∑d∈T,d.radius)<(∑d∈S,d.radius)+η ∧
      (∑d∈T,d.noncoreCost)<(∑d∈S,d.noncoreCost)+η from hh _ S rfl hS η hη
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hn hS η hη
    by_cases hp : (S : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall)
    · exact ⟨S,hS,hp,fun d hd => ⟨d,hd,Subset.rfl,fun h => h⟩,
        lt_add_of_pos_right _ hη,lt_add_of_pos_right _ hη⟩
    · simp only [Set.Pairwise,Finset.mem_coe] at hp
      push Not at hp
      obtain ⟨a,ha,b,hb,hab,hd⟩ := hp
      obtain ⟨d,hdv,hda,hdb,hdr,hdc,hdcore⟩ := merge (hS a ha) (hS b hb) hd (half_pos hη)
      let R := (S.erase a).erase b
      let S' := insert d R
      have hR : ∀e∈R,e∈S := by intro e he; exact (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).2
      have hS' : ∀e∈S',e.Valid L := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl|he
        · exact hdv
        · exact hS e (hR e he)
      have hcard : S'.card<n := by
        have hc₁ := Finset.card_erase_add_one ha
        have hc₂ := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hab.symm,hb⟩)
        have hc₃ := Finset.card_insert_le d R
        change R.card+1=(S.erase a).card at hc₂
        dsimp only [S']
        omega
      obtain ⟨T,hT,hdis,hcov,hr,hc⟩ := ih S'.card hcard S' rfl hS' (η/2) (half_pos hη)
      refine ⟨T,hT,hdis,?_,?_,?_⟩
      · intro e he
        have he' : ∃f∈S',e.ball⊆f.ball ∧ (e.core=true → f.core=true) := by
          by_cases hea : e=a
          · subst e
            refine ⟨d,Finset.mem_insert_self _ _,fun _ hq => hda (Metric.ball_subset_closedBall hq),?_⟩
            intro ha
            rw [hdcore,ha]
            simp
          · by_cases heb : e=b
            · subst e
              refine ⟨d,Finset.mem_insert_self _ _,fun _ hq => hdb (Metric.ball_subset_closedBall hq),?_⟩
              intro hb
              rw [hdcore,hb]
              simp
            · exact ⟨e,Finset.mem_insert_of_mem (by simp [R,he,hea,heb]),Subset.rfl,fun h => h⟩
        obtain ⟨f,hf,hef,hcore⟩ := he'
        obtain ⟨g,hg,hfg,hcore'⟩ := hcov f hf
        exact ⟨g,hg,hef.trans hfg,fun hec => hcore' (hcore hec)⟩
      · have hb' := merge_sum_bound S ha hb hab radius hdv.1.le hdr
        change (∑x∈S',x.radius)≤(∑x∈S,x.radius)+η/2 at hb'
        linarith
      · have hdc0 : 0≤d.noncoreCost := by unfold noncoreCost; split_ifs <;> linarith [hdv.1]
        have hb' := merge_sum_bound S ha hb hab noncoreCost hdc0 hdc
        change (∑x∈S',x.noncoreCost)≤(∑x∈S,x.noncoreCost)+η/2 at hb'
        linarith
end MarkedDisk
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
lemma diskCone_surjective (c : ℂ) {r : ℝ} (hr : 0 < r) : Function.Surjective (diskCone c hr) := by
  intro q
  by_cases hq : q.val=c
  · obtain ⟨z,hz⟩ := (NormedSpace.sphere_nonempty (x:=c)).mpr hr.le
    refine ⟨(1,⟨z,hz⟩),?_⟩
    apply Subtype.ext
    simpa [diskCone] using hq.symm
  · let d := dist q.val c
    have hd : 0<d := dist_pos.mpr hq
    have hdr : d ≤ r := q.property
    let t : unitInterval := ⟨1-d/r,⟨by rw [sub_nonneg,div_le_one hr]; exact hdr,
      by linarith [div_nonneg hd.le hr.le]⟩⟩
    have hz : (r/d) • (q.val-c)+c∈Metric.sphere c r := by
      rw [Metric.mem_sphere,dist_eq_norm,add_sub_cancel_right,norm_smul,Real.norm_of_nonneg (div_pos hr hd).le]
      rw [←dist_eq_norm]
      change r/d*d=r
      field_simp
    refine ⟨(t,⟨(r/d) • (q.val-c)+c,hz⟩),?_⟩
    apply Subtype.ext
    change (1-(1-d/r)) • (((r/d) • (q.val-c)+c)-c)+c=q.val
    rw [add_sub_cancel_right,smul_smul]
    have he : (1-(1-d/r))*(r/d)=1 := by field_simp; ring
    rw [he,one_smul,sub_add_cancel]
lemma diskCone_fiber (c : ℂ) {r : ℝ} (hr : 0 < r)
    {p q : unitInterval × Metric.sphere c r} (he : diskCone c hr p=diskCone c hr q) :
    p=q ∨ (p.1=1 ∧ q.1=1) := by
  have hv := congrArg Subtype.val he
  have hd := congrArg (fun x : Metric.closedBall c r => dist x.val c) he
  change dist ((1-p.1.val) • (p.2.val-c)+c) c=dist ((1-q.1.val) • (q.2.val-c)+c) c at hd
  rw [cone_dist,cone_dist] at hd
  have ht : p.1=q.1 := Subtype.ext (by nlinarith)
  by_cases h1 : p.1=1
  · exact Or.inr ⟨h1,ht.symm.trans h1⟩
  · left
    apply Prod.ext ht
    have hneq : 1-p.1.val≠0 := by
      intro hh
      apply h1
      apply Subtype.ext
      change p.1.val=1
      linarith
    apply Subtype.ext
    change (1-p.1.val) • (p.2.val-c)+c=(1-q.1.val) • (q.2.val-c)+c at hv
    rw [←ht] at hv
    have hsub : p.2.val-c=q.2.val-c := (smul_right_injective ℂ hneq (add_right_cancel hv))
    exact sub_left_injective hsub

/-- A contraction genuinely extends arbitrary continuous sphere data across a disk. -/
theorem contractible_disk_extension {Y : Type u} [TopologicalSpace Y] [ContractibleSpace Y]
    (c : ℂ) {r : ℝ} (hr : 0 < r) (f : C(Metric.sphere c r,Y)) :
    ∃g : C(Metric.closedBall c r,Y), ∀z : Metric.sphere c r,
      g ⟨z.val,Metric.sphere_subset_closedBall z.property⟩=f z := by
  let : CompactSpace (Metric.sphere c r) := isCompact_iff_compactSpace.mp (isCompact_sphere c r)
  obtain ⟨a,⟨H⟩⟩ := id_nullhomotopic Y
  let F : C(unitInterval × Metric.sphere c r,Y) := H.toContinuousMap.comp
    (ContinuousMap.prodMk ContinuousMap.fst (f.comp ContinuousMap.snd))
  have hf : Function.FactorsThrough F (diskCone c hr) := by
    intro p q he
    rcases diskCone_fiber c hr he with rfl|⟨hp,hq⟩
    · rfl
    · change H (p.1,f p.2)=H (q.1,f q.2)
      rw [hp,hq]
      exact (H.map_one_left (f p.2)).trans (H.map_one_left (f q.2)).symm
  have hquot := IsQuotientMap.of_surjective_continuous (diskCone_surjective c hr) (diskCone c hr).continuous
  refine ⟨hquot.lift F hf,?_⟩
  intro z
  have he : diskCone c hr (0,z)=⟨z.val,Metric.sphere_subset_closedBall z.property⟩ := by
    apply Subtype.ext
    simp [diskCone]
  rw [←he]
  have hh := DFunLike.congr_fun (hquot.lift_comp F hf) (0,z)
  change (hquot.lift F hf) (diskCone c hr (0,z))=H (0,f z) at hh
  exact hh.trans (H.map_zero_left _)
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor

private lemma graphTree_contractible_aux (n : ℕ) :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), Fintype.card V=n →
      G.IsTree → ContractibleSpace (GraphSpace G) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V inst G hcard hG
    rcases subsingleton_or_nontrivial V with hSS|hNT
    · let := hSS
      obtain ⟨a⟩ := hG.nonempty
      let : Nonempty (GraphSpace G) := ⟨⟨graphVertex a,graphVertex_mem G a⟩⟩
      let : Subsingleton (GraphSpace G) := ⟨fun p q => Subtype.ext (by
        have hp := p.property
        have hq := q.property
        simp only [graphRealization_singleton G a,mem_singleton_iff] at hp hq
        exact hp.trans hq.symm)⟩
      infer_instance
    · let := hNT
      obtain ⟨v,hv⟩ := hG.exists_vert_degree_one_of_nontrivial
      obtain ⟨w,hvw,hleaf⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
      let W := {i : V // i≠v}
      let G' : SimpleGraph W := G.induce {i | i≠v}
      have hs : ({v}ᶜ : Set V)={i | i≠v} := by ext i; simp
      have hconn : G'.Connected := by
        have hh := hG.connected.induce_compl_singleton_of_degree_eq_one hv
        rwa [hs] at hh
      have hac : G'.IsAcyclic := hG.isAcyclic.induce _
      have hlt : Fintype.card W<n := by
        rw [←hcard]
        apply Fintype.card_lt_of_injective_not_surjective (Subtype.val : W → V) Subtype.val_injective
        intro hh
        obtain ⟨i,hi⟩ := hh v
        exact i.property hi
      let : ContractibleSpace (GraphSpace G') := ih _ hlt W G' rfl ⟨hconn,hac⟩
      have hn := ((id_nullhomotopic (GraphSpace G')).comp_left
        (graphLeafRetraction hvw hleaf)).comp_right (graphLeafInclusion G v)
      obtain ⟨a,ha⟩ := hn
      apply (contractible_iff_id_nullhomotopic _).mpr
      refine ⟨a,ContinuousMap.Homotopic.trans ⟨graphLeafHomotopy hvw hleaf⟩ ?_⟩
      simpa only [ContinuousMap.id_comp] using ha

/-- Genuine contraction of the geometric probability-simplex realization of a finite tree. -/
theorem graphTree_contractible {V : Type u} [Fintype V] {G : SimpleGraph V} (hG : G.IsTree) :
    ContractibleSpace (GraphSpace G) := graphTree_contractible_aux _ V G rfl hG
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
/-- Forest-valued boundary data extend through an actual spanning tree inside the
complete graph. Isolated labels and empty edge sets are retained. -/
theorem forest_disk_extension {V : Type u} [Fintype V] [Nonempty V]
    (c : ℂ) {r : ℝ} (hr : 0 < r) (f : C(Metric.sphere c r,V → ℝ))
    {G : SimpleGraph V} (hG : G.IsAcyclic) (hf : ∀z,f z∈graphRealization G) :
    ∃g : C(Metric.closedBall c r,GraphSpace (⊤ : SimpleGraph V)), ∀z : Metric.sphere c r,
      (g ⟨z.val,Metric.sphere_subset_closedBall z.property⟩).val=f z := by
  obtain ⟨T,hGT,_,hT⟩ := SimpleGraph.connected_top.exists_isTree_le_of_le_of_isAcyclic
    (show G≤⊤ from le_top) hG
  let : ContractibleSpace (GraphSpace T) := graphTree_contractible hT
  let F : C(Metric.sphere c r,GraphSpace T) := ⟨fun z => ⟨f z,graphRealization_mono hGT (hf z)⟩,
    f.continuous.subtype_mk _⟩
  obtain ⟨g,hg⟩ := contractible_disk_extension c hr F
  let g' : C(Metric.closedBall c r,GraphSpace (⊤ : SimpleGraph V)) :=
    ⟨fun z => ⟨(g z).val,graphRealization_mono le_top (g z).property⟩,
      (continuous_subtype_val.comp g.continuous).subtype_mk _⟩
  exact ⟨g',fun z => congrArg Subtype.val (hg z)⟩
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
lemma diskHoles_open (S : Finset MarkedDisk) : IsOpen (diskHoles S) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball
lemma mem_diskHoles {S : Finset MarkedDisk} {z : ℂ} : z∈diskHoles S ↔ ∃d∈S,z∈d.ball := by
  simp [diskHoles]

/-- Finite closed pasting fills precisely the non-core holes, with actual continuous
tree extensions on their disks and no change outside the original open holes. -/
theorem fill_noncore_disks {V : Type u} [Fintype V] [Nonempty V]
    (Q : Set ℂ) (S : Finset MarkedDisk) (hr : ∀d∈S,0<d.radius)
    (hdis : (S : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall))
    (f : C(ℂ,V → ℝ))
    (hg : ∀z∈Q,z∉diskHoles S → f z∈graphRealization (⊤ : SimpleGraph V))
    (hb : ∀d∈S,d.core=false → (d.closedBall∩Q).Nonempty →
      ∃G : SimpleGraph V,G.IsAcyclic ∧ ∀z∈Metric.sphere d.center d.radius,f z∈graphRealization G) :
    ∃g : C(↥(Q \ coreHoles S),GraphSpace (⊤ : SimpleGraph V)),
      ∀z : ↥(Q \ coreHoles S),z.val∉diskHoles S → (g z).val=f z.val := by
  let D : Finset MarkedDisk := S.filter fun d => d.core=false ∧ (d.closedBall∩Q).Nonempty
  have hD (d : D) : d.val∈S ∧ d.val.core=false ∧ (d.val.closedBall∩Q).Nonempty :=
    Finset.mem_filter.mp d.property
  have hex (d : D) : ∃g : C(Metric.closedBall d.val.center d.val.radius,GraphSpace (⊤ : SimpleGraph V)),
      ∀z : Metric.sphere d.val.center d.val.radius,
        (g ⟨z.val,Metric.sphere_subset_closedBall z.property⟩).val=f z.val := by
    obtain ⟨G,hG,hf⟩ := hb d.val (hD d).1 (hD d).2.1 (hD d).2.2
    exact forest_disk_extension d.val.center (hr _ (hD d).1) (f.restrict _) hG (fun z => hf z.val z.property)
  choose g hg' using hex
  let X := Q \ coreHoles S
  let Z : Option D → Set X := fun i => match i with
    | none => {z | z.val∉diskHoles S}
    | some d => {z | z.val∈d.val.closedBall}
  have hZ : ∀i,IsClosed (Z i) := by
    intro i
    cases i with
    | none => exact (diskHoles_open S).isClosed_compl.preimage continuous_subtype_val
    | some d => exact Metric.isClosed_closedBall.preimage continuous_subtype_val
  have hcov : ⋃i,Z i=univ := by
    apply iUnion_eq_univ_iff.mpr
    intro z
    by_cases hz : z.val∈diskHoles S
    · obtain ⟨d,hd,hzd⟩ := mem_diskHoles.mp hz
      have hdf : d.core=false := by
        cases he : d.core
        · rfl
        · exact False.elim (z.property.2 (mem_coreHoles.mpr ⟨d,hd,he,hzd⟩))
      let d' : D := ⟨d,Finset.mem_filter.mpr ⟨hd,hdf,⟨z.val,Metric.ball_subset_closedBall hzd,z.property.1⟩⟩⟩
      exact ⟨some d',Metric.ball_subset_closedBall hzd⟩
    · exact ⟨none,hz⟩
  let f₀ : C(Z none,GraphSpace (⊤ : SimpleGraph V)) :=
    ⟨fun z => ⟨f z.val.val,hg z.val.val z.val.property.1 z.property⟩,
      (f.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩
  let ψ (d : D) : C(Z (some d),GraphSpace (⊤ : SimpleGraph V)) :=
    ⟨fun z => g d ⟨z.val.val,z.property⟩,
      (g d).continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
  let φ : ∀i,C(Z i,GraphSpace (⊤ : SimpleGraph V)) := fun i => match i with
    | none => f₀
    | some d => ψ d
  have hbd (d : D) (z : X) (h0 : z∈Z none) (h1 : z∈Z (some d)) :
      f₀ ⟨z,h0⟩=ψ d ⟨z,h1⟩ := by
    have hn : z.val∉d.val.ball := fun hz => h0 (mem_diskHoles.mpr ⟨d.val,(hD d).1,hz⟩)
    have hs : z.val∈Metric.sphere d.val.center d.val.radius := by
      change dist z.val d.val.center=d.val.radius
      exact le_antisymm h1 (le_of_not_gt hn)
    apply Subtype.ext
    exact (hg' d ⟨z.val,hs⟩).symm
  have hφ : ∀i j z (hi : z∈Z i) (hj : z∈Z j),φ i ⟨z,hi⟩=φ j ⟨z,hj⟩ := by
    intro i j z hi hj
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some d => exact hbd d z hi hj
    | some d =>
      cases j with
      | none => exact (hbd d z hj hi).symm
      | some e =>
        by_cases hde : d=e
        · subst e; rfl
        · exact False.elim (Set.disjoint_left.mp (hdis (hD d).1 (hD e).1
            (fun he => hde (Subtype.ext he))) hi hj)
  refine ⟨closedCoverMap Z hZ hcov φ hφ,?_⟩
  intro z hz
  change (closedCoverMap Z hZ hcov φ hφ z).val=f z.val
  rw [closedCoverMap_apply Z hZ hcov φ hφ (i:=none) ⟨z,hz⟩]
  rfl
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_GraphCuts
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
/-- Removing the non-tree edge midpoints leaves a contractible graph (tree with half-open stubs). -/
theorem graphCut_contractible {V : Type u} [Fintype V] {T : SimpleGraph V} (hT : T.IsTree) :
    ContractibleSpace (GraphCutSpace T) := by
  let := graphTree_contractible hT
  have hn := ((id_nullhomotopic (GraphSpace T)).comp_left
    (graphCutRetraction T)).comp_right (graphCutInclusion T)
  obtain ⟨a,ha⟩ := hn
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨a,ContinuousMap.Homotopic.trans ⟨graphCutHomotopy T⟩ ?_⟩
  simpa only [ContinuousMap.id_comp] using ha
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u v
namespace EuclideanFiveColor
lemma compact_fiber_partition {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [T1Space Y]
    (f : C(X,Y)) {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (b : Y)
    (hn : ¬FiberCrosses f A B b) :
    ∃K₀ K₁ : Set X, IsCompact K₀ ∧ IsCompact K₁ ∧ Disjoint K₀ K₁ ∧
      K₀∪K₁=f ⁻¹' {b} ∧ Disjoint K₀ B ∧ Disjoint K₁ A := by
  let F : Set X := f ⁻¹' {b}
  have hF : IsClosed F := isClosed_singleton.preimage f.continuous
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let I : Set F := Subtype.val ⁻¹' A
  let O : Set F := Subtype.val ⁻¹' B
  have hI : IsCompact I := (hA.preimage continuous_subtype_val).isCompact
  have hO : IsCompact O := (hB.preimage continuous_subtype_val).isCompact
  have hno : ∀x∈I,Disjoint (connectedComponent x) O := by
    intro x hx
    apply disjoint_left.mpr
    intro y hy hOy
    apply hn
    refine ⟨Subtype.val '' connectedComponent x,
      isClosed_connectedComponent.isCompact.image continuous_subtype_val,
      isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn,?_,?_,?_⟩
    · rintro z ⟨w,hw,rfl⟩; exact w.property
    · exact ⟨x.val,⟨⟨x,mem_connectedComponent,rfl⟩,hx⟩⟩
    · exact ⟨y.val,⟨⟨y,hy,rfl⟩,hOy⟩⟩
  obtain ⟨Z₀,Z₁,hZ₀,hZ₁,hd,hcov,hIZ,hOZ⟩ := compact_component_partition hI hO hno
  refine ⟨Subtype.val '' Z₀,Subtype.val '' Z₁,hZ₀.image continuous_subtype_val,
    hZ₁.image continuous_subtype_val,?_,?_,?_,?_⟩
  · apply disjoint_left.mpr
    rintro x ⟨y,hy,rfl⟩ ⟨z,hz,he⟩
    have hh : z=y := Subtype.ext he
    subst z
    exact disjoint_left.mp hd hy hz
  · rw [←image_union,hcov]
    ext x
    constructor
    · rintro ⟨y,_,rfl⟩; exact y.property
    · intro hx; exact ⟨⟨x,hx⟩,mem_univ _,rfl⟩
  · apply disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ hz
    exact disjoint_left.mp hd hx (hOZ hz)
  · apply disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ hz
    exact disjoint_left.mp hd (hIZ hz) hx

/-- All finitely many non-crossing bad fibers can simultaneously be separated,
 with the prescribed inner/outer closed sets on opposite sides. -/
theorem finite_fiber_separation {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [T1Space Y]
    (f : C(X,Y)) {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hd : Disjoint A B)
    (S : Finset Y) (hn : ∀b∈S,¬FiberCrosses f A B b) :
    ∃C₀ C₁ : Set X, IsCompact C₀ ∧ IsCompact C₁ ∧ Disjoint C₀ C₁ ∧
      A⊆C₀ ∧ B⊆C₁ ∧ f ⁻¹' (↑S : Set Y)⊆C₀∪C₁ := by
  choose K₀ K₁ hK using (fun b : S => compact_fiber_partition f hA hB b.val (hn b.val b.property))
  let Z₀ : Set X := ⋃b : S,K₀ b
  let Z₁ : Set X := ⋃b : S,K₁ b
  have hz₀ : IsCompact Z₀ := isCompact_iUnion fun b => (hK b).1
  have hz₁ : IsCompact Z₁ := isCompact_iUnion fun b => (hK b).2.1
  have hsub₀ (b : S) : K₀ b⊆f ⁻¹' {b.val} := by
    rw [←(hK b).2.2.2.1]; exact subset_union_left
  have hsub₁ (b : S) : K₁ b⊆f ⁻¹' {b.val} := by
    rw [←(hK b).2.2.2.1]; exact subset_union_right
  have h01 : Disjoint Z₀ Z₁ := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨b,hb⟩ := mem_iUnion.mp hx
    obtain ⟨c,hc⟩ := mem_iUnion.mp hy
    have he : b=c := Subtype.ext ((hsub₀ b hb).symm.trans (hsub₁ c hc))
    subst c
    exact disjoint_left.mp (hK b).2.2.1 hb hc
  have h0B : Disjoint Z₀ B := by
    apply disjoint_left.mpr
    intro x hx hB
    obtain ⟨b,hb⟩ := mem_iUnion.mp hx
    exact disjoint_left.mp (hK b).2.2.2.2.1 hb hB
  have h1A : Disjoint Z₁ A := by
    apply disjoint_left.mpr
    intro x hx hA
    obtain ⟨b,hb⟩ := mem_iUnion.mp hx
    exact disjoint_left.mp (hK b).2.2.2.2.2 hb hA
  refine ⟨A∪Z₀,B∪Z₁,hA.isCompact.union hz₀,hB.isCompact.union hz₁,?_,subset_union_left,subset_union_left,?_⟩
  · exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hd,h1A.symm⟩,
      disjoint_union_right.mpr ⟨h0B,h01⟩⟩
  · intro x hx
    let b : S := ⟨f x,hx⟩
    have hh : x∈K₀ b∪K₁ b := by rw [(hK b).2.2.2.1]; rfl
    rcases hh with hh|hh
    · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨b,hh⟩))
    · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨b,hh⟩))
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_HoleApproximation
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
namespace MarkedDisk
lemma noncoreCost_nonneg {d : MarkedDisk} (hd : 0≤d.radius) : 0≤d.noncoreCost := by
  unfold noncoreCost
  split <;> positivity
lemma noncore_radius_le_sum {S : Finset MarkedDisk} (hS : ∀d∈S,0≤d.radius)
    {d : MarkedDisk} (hd : d∈S) (hc : d.core=false) : d.radius≤∑e∈S,e.noncoreCost := by
  have hh := Finset.single_le_sum (fun e he => noncoreCost_nonneg (hS e he)) hd
  simpa [noncoreCost,hc] using hh
lemma sphere_avoids_holes {S : Finset MarkedDisk}
    (hdis : (S : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall))
    {d : MarkedDisk} (hd : d∈S) {z : ℂ} (hz : z∈Metric.sphere d.center d.radius) : z∉diskHoles S := by
  rintro hh
  obtain ⟨e,he,hze⟩ := mem_diskHoles.mp hh
  by_cases hde : d=e
  · subst e
    have hh' : dist z d.center<d.radius := hze
    have hz' : dist z d.center=d.radius := hz
    linarith
  · exact Set.disjoint_left.mp (hdis hd he hde) (Metric.sphere_subset_closedBall hz)
      (Metric.ball_subset_closedBall hze)
lemma sphere_norm_bound {d : MarkedDisk} {R : ℝ}
    (hmeet : (d.closedBall∩Metric.closedBall (0:ℂ) R).Nonempty) {z : ℂ}
    (hz : z∈Metric.sphere d.center d.radius) : dist z 0≤2*d.radius+R := by
  obtain ⟨a,ha,haR⟩ := hmeet
  have hza : dist z a≤2*d.radius := calc
    dist z a≤dist z d.center+dist d.center a := dist_triangle _ _ _
    _ ≤ 2*d.radius := by
      have hh : dist z d.center=d.radius := hz
      have ha' : dist d.center a≤d.radius := by simpa only [closedBall,Metric.mem_closedBall,dist_comm] using ha
      linarith
  exact (dist_triangle z a 0).trans (by change dist a 0≤R at haR; linarith)
end MarkedDisk
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
namespace MarkedDisk
lemma mem_initialDisks {L C : Finset ℂ} {δ u : ℝ} {d : MarkedDisk} :
    d∈initialDisks L C δ u ↔ (∃x∈L,d=⟨x,δ,true⟩) ∨ (∃x∈C,d=⟨x,u,false⟩) := by
  simp [initialDisks,eq_comm]
lemma initialDisks_valid (L C : Finset ℂ) {δ u : ℝ} (hδ : 0<δ) (hu : 0<u) :
    ∀d∈initialDisks L C δ u,d.Valid (L : Set ℂ) := by
  intro d hd
  rcases mem_initialDisks.mp hd with ⟨x,hx,rfl⟩|⟨x,hx,rfl⟩
  · exact ⟨hδ,fun _ => ⟨x,hx,Metric.mem_ball_self hδ⟩⟩
  · exact ⟨hu,by simp⟩
lemma initialDisks_sum (L C : Finset ℂ) (δ u : ℝ) :
    (∑d∈initialDisks L C δ u,d.radius)=(L.card:ℝ)*δ+(C.card:ℝ)*u ∧
    (∑d∈initialDisks L C δ u,d.noncoreCost)=(C.card:ℝ)*u := by
  have hd : Disjoint (L.image (fun x => (⟨x,δ,true⟩ : MarkedDisk)))
      (C.image (fun x => (⟨x,u,false⟩ : MarkedDisk))) := by
    apply Finset.disjoint_left.mpr
    intro d hd he
    obtain ⟨x,hx,hxd⟩ := Finset.mem_image.mp hd
    obtain ⟨y,hy,hyd⟩ := Finset.mem_image.mp he
    have hh := congrArg MarkedDisk.core (hxd.trans hyd.symm)
    exact Bool.noConfusion hh
  have hi (r : ℝ) (b : Bool) : Function.Injective (fun x : ℂ => (⟨x,r,b⟩ : MarkedDisk)) := by
    intro x y h; exact congrArg MarkedDisk.center h
  simp only [initialDisks,Finset.sum_union hd]
  rw [Finset.sum_image (fun x _ y _ h => hi δ true h),Finset.sum_image (fun x _ y _ h => hi u false h),
      Finset.sum_image (fun x _ y _ h => hi δ true h),Finset.sum_image (fun x _ y _ h => hi u false h)]
  simp [noncoreCost]
lemma initial_marked_cover (L C : Finset ℂ) (δ u : ℝ) {x z : ℂ} (hx : x∈C)
    (hz : z∈Metric.ball x u) : z∈diskHoles (initialDisks L C δ u) := by
  exact mem_diskHoles.mpr ⟨⟨x,u,false⟩,mem_initialDisks.mpr (Or.inr ⟨x,hx,rfl⟩),hz⟩
lemma holes_subset_of_cover {S T : Finset MarkedDisk}
    (hcov : ∀d∈S,∃e∈T,d.ball⊆e.ball ∧ (d.core=true → e.core=true)) :
    diskHoles S⊆diskHoles T ∧ coreHoles S⊆coreHoles T := by
  constructor
  · intro z hz
    obtain ⟨d,hd,hzd⟩ := mem_diskHoles.mp hz
    obtain ⟨e,he,hde,_⟩ := hcov d hd
    exact mem_diskHoles.mpr ⟨e,he,hde hzd⟩
  · intro z hz
    obtain ⟨d,hd,hcd,hzd⟩ := mem_coreHoles.mp hz
    obtain ⟨e,he,hde,hc⟩ := hcov d hd
    exact mem_coreHoles.mpr ⟨e,he,hc hcd,hde hzd⟩
end MarkedDisk
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory ContinuousMap
namespace EuclideanFiveColor
open MarkedDisk
/-- Actual small-hole maps on a fixed disk, with arbitrarily small total radii.
The core witnesses lie in the finite actual cyclic core; all other holes have been
filled by genuine tree extensions. -/
theorem small_hole_map {c : ℂ → Fin 5} (hc : Measurable c) {α : ℝ}
    (hα : 0<α) (hα' : α<1/5) (L : Finset ℂ)
    (hL : ∀x∈Metric.closedBall (0:ℂ) 8,¬(transitionGraph c x).IsAcyclic → x∈L)
    {t : ℝ} (ht : 0<t) (ht' : t<1/2) :
    ∃e>0,∀ε,0<ε → ε<e → ∃S : Finset MarkedDisk,
      (∀d∈S,d.Valid (L : Set ℂ)) ∧
      (S : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall) ∧
      (∑d∈S,d.radius)<t ∧
      ∃g : C(↥(Metric.closedBall (0:ℂ) 7 \ coreHoles S),GraphSpace (⊤ : SimpleGraph (Fin 5))),
        ∀z : ↥(Metric.closedBall (0:ℂ) 7 \ coreHoles S),z.val∉diskHoles S →
          (g z).val=thresholdMap c ε α z.val := by
  let δ : ℝ := t/(4*((L.card:ℝ)+1))
  have hδ : 0<δ := div_pos ht (by positivity)
  have hδeq : δ*(4*((L.card:ℝ)+1))=t := div_mul_cancel₀ _ (by positivity)
  have hδbudget : (L.card:ℝ)*δ<t/4 := by nlinarith
  let M := Metric.closedBall (0:ℂ) 8 \ ⋃x∈L,Metric.ball x δ
  have hM : IsCompact M := (isCompact_closedBall (0:ℂ) 8).diff
    (isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball)
  have hf : ∀x∈M,(transitionGraph c x).IsAcyclic := by
    intro x hx
    by_contra hn
    exact hx.2 (mem_iUnion.mpr ⟨x,mem_iUnion.mpr ⟨hL x hx.1 hn,Metric.mem_ball_self hδ⟩⟩)
  obtain ⟨l,hl,hcharts⟩ := compact_forest_charts hc hα hα' M hM hf
  let κ := min (t/4) (l/6)
  have hκ : 0<κ := lt_min (by positivity) (by positivity)
  have hκt : κ≤t/4 := min_le_left _ _
  have hκl : κ≤l/6 := min_le_right _ _
  obtain ⟨e,he,hC⟩ := hcharts κ hκ
  refine ⟨e,he,fun ε hε hεe => ?_⟩
  obtain ⟨C,hCr,hCv⟩ := hC ε hε hεe
  let u := α*ε/4
  have hu : 0<u := by dsimp [u]; positivity
  obtain ⟨S,hS,hdis,hcov,hsum,hcost⟩ := MarkedDisk.separate
    (initialDisks L C δ u) (initialDisks_valid L C hδ hu) hκ
  have htot : (∑d∈S,d.radius)<t := by
    rw [(initialDisks_sum L C δ u).1] at hsum
    change (C.card:ℝ)*u<κ at hCr
    linarith
  have hnrad : ∀d∈S,d.core=false → 2*d.radius<l := by
    rw [(initialDisks_sum L C δ u).2] at hcost
    intro d hd hdf
    have hd' := noncore_radius_le_sum (fun a ha => (hS a ha).1.le) hd hdf
    change (C.card:ℝ)*u<κ at hCr
    linarith
  have hcover := holes_subset_of_cover hcov
  have hMof (z : ℂ) (hz : z∈Metric.closedBall (0:ℂ) 8) (hzS : z∉diskHoles S) : z∈M := by
    refine ⟨hz,?_⟩
    intro hh
    obtain ⟨x,hx⟩ := mem_iUnion.mp hh
    obtain ⟨hxL,hzx⟩ := mem_iUnion.mp hx
    exact hzS (hcover.1 (mem_diskHoles.mpr ⟨⟨x,δ,true⟩,
      mem_initialDisks.mpr (Or.inl ⟨x,hxL,rfl⟩),hzx⟩))
  have hmarked (z : ℂ) (hz : z∉diskHoles S) : z∉⋃x∈C,Metric.ball x u := by
    intro hh
    obtain ⟨x,hx⟩ := mem_iUnion.mp hh
    obtain ⟨hxC,hzx⟩ := mem_iUnion.mp hx
    exact hz (hcover.1 (initial_marked_cover L C δ u hxC hzx))
  let f : C(ℂ,Fin 5 → ℝ) := ⟨thresholdMap c ε α,continuous_thresholdMap hc hε hα'⟩
  have hg : ∀z∈Metric.closedBall (0:ℂ) 7,z∉diskHoles S →
      f z∈graphRealization (⊤ : SimpleGraph (Fin 5)) := by
    intro z hz hzS
    have hzM := hMof z (Metric.closedBall_subset_closedBall (by norm_num) hz) hzS
    obtain ⟨G,hG,hq⟩ := hCv z hzM
    exact graphRealization_mono le_top (hq z (Metric.mem_ball_self hl) (hmarked z hzS))
  have hb : ∀d∈S,d.core=false → (d.closedBall∩Metric.closedBall (0:ℂ) 7).Nonempty →
      ∃G : SimpleGraph (Fin 5),G.IsAcyclic ∧ ∀z∈Metric.sphere d.center d.radius,
        f z∈graphRealization G := by
    intro d hd hdf hmeet
    have hr := (hS d hd).1
    have hsph (z : ℂ) (hz : z∈Metric.sphere d.center d.radius) : z∈Metric.closedBall (0:ℂ) 8 := by
      have hzr := sphere_norm_bound hmeet hz
      have hd' := radius_le_sum (fun a ha => (hS a ha).1.le) hd
      change dist z 0≤8
      linarith
    obtain ⟨a,ha⟩ := (NormedSpace.sphere_nonempty (x:=d.center)).mpr hr.le
    have haM := hMof a (hsph a ha) (sphere_avoids_holes hdis hd ha)
    obtain ⟨G,hG,hq⟩ := hCv a haM
    refine ⟨G,hG,fun z hz => hq z ?_ (hmarked z (sphere_avoids_holes hdis hd hz))⟩
    have hza : dist z a≤2*d.radius := calc
      dist z a≤dist z d.center+dist d.center a := dist_triangle _ _ _
      _ = 2*d.radius := by
        have hz' : dist z d.center=d.radius := hz
        have ha' : dist d.center a=d.radius := by simpa only [Metric.mem_sphere,dist_comm] using ha
        rw [hz',ha']; ring
    exact hza.trans_lt (hnrad d hd hdf)
  obtain ⟨g,hg'⟩ := fill_noncore_disks (Metric.closedBall (0:ℂ) 7) S
    (fun d hd => (hS d hd).1) hdis f hg hb
  exact ⟨S,hS,hdis,htot,g,hg'⟩
end EuclideanFiveColor
end

noncomputable section
open scoped Classical ENNReal
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma unit_from_disk_mem_annulus {d : MarkedDisk} {z q : ℂ}
    (hq : q∈d.closedBall) (hzq : dist z q=1) : z∈diskAnnulus d := by
  have hq' : dist q d.center≤d.radius := hq
  constructor
  · change dist z d.center≤1+d.radius
    exact (dist_triangle z q d.center).trans (by linarith)
  · change ¬ dist z d.center<1-d.radius
    have hh := dist_triangle z d.center q
    rw [dist_comm d.center q,hzq] at hh
    linarith
lemma volume_diskAnnulus {d : MarkedDisk} (h0 : 0≤d.radius) (h1 : d.radius≤1) :
    volume (diskAnnulus d)=ENNReal.ofReal (4*Real.pi*d.radius) := by
  have hsub : Metric.ball d.center (1-d.radius)⊆Metric.closedBall d.center (1+d.radius) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hvol (r : ℝ) (hr : 0 ≤ r) : ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞)=ENNReal.ofReal (r^2*Real.pi) := by
    rw [ENNReal.ofReal_mul (sq_nonneg r),ENNReal.ofReal_pow hr]
    congr 1
    rw [←NNReal.coe_real_pi,ENNReal.ofReal_coe_nnreal]
  rw [diskAnnulus,measure_sdiff hsub Metric.isOpen_ball.measurableSet.nullMeasurableSet (by finiteness),
    Complex.volume_closedBall,Complex.volume_ball,hvol _ (by linarith),hvol _ (by linarith),
    ←ENNReal.ofReal_sub _ (by positivity : 0≤(1-d.radius)^2*Real.pi)]
  congr 1
  ring

lemma volume_holeAnnuli_le {S : Finset MarkedDisk}
    (hS : ∀d∈S,0≤d.radius ∧ d.radius≤1) :
    volume (holeAnnuli S)≤ENNReal.ofReal (4*Real.pi*(∑d∈S,d.radius)) := by
  calc
    volume (holeAnnuli S)≤∑d∈S,volume (diskAnnulus d) := measure_biUnion_finset_le S _
    _ = ∑d∈S,ENNReal.ofReal (4*Real.pi*d.radius) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact volume_diskAnnulus (hS d hd).1 (hS d hd).2
    _ = ENNReal.ofReal (∑d∈S,4*Real.pi*d.radius) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun d hd => mul_nonneg (by positivity) (hS d hd).1)]
    _ = ENNReal.ofReal (4*Real.pi*(∑d∈S,d.radius)) := by rw [Finset.mul_sum]
lemma unit_from_hole_mem_annuli {S : Finset MarkedDisk} {z q : ℂ}
    (hq : q∈diskHoles S) (hzq : dist z q=1) : z∈holeAnnuli S := by
  obtain ⟨d,hd,hqd⟩ := mem_diskHoles.mp hq
  exact mem_iUnion.mpr ⟨d,mem_iUnion.mpr ⟨hd,unit_from_disk_mem_annulus (Metric.ball_subset_closedBall hqd) hzq⟩⟩
lemma holeAnnuli_tendsto_zero (S : ℕ → Finset MarkedDisk)
    (hS : ∀n d,d∈S n → 0≤d.radius)
    (hlim : Tendsto (fun n => ∑d∈S n,d.radius) atTop (𝓝 0)) :
    Tendsto (fun n => volume (holeAnnuli (S n))) atTop (𝓝 0) := by
  have hsmall : ∀ᶠ n in atTop,(∑d∈S n,d.radius)≤1 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  have hbound : ∀ᶠ n in atTop,volume (holeAnnuli (S n))≤ENNReal.ofReal (4*Real.pi*(∑d∈S n,d.radius)) := by
    filter_upwards [hsmall] with n hn
    apply volume_holeAnnuli_le
    exact fun d hd => ⟨hS n d hd,(MarkedDisk.radius_le_sum (hS n) hd).trans hn⟩
  have ht : Tendsto (fun n => ENNReal.ofReal (4*Real.pi*(∑d∈S n,d.radius))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim.const_mul (4*Real.pi))
  apply ENNReal.tendsto_nhds_zero.mpr
  intro a ha
  filter_upwards [hbound,ENNReal.tendsto_nhds_zero.mp ht a ha] with n hn hn'
  exact hn.trans hn'
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory ContinuousMap
namespace EuclideanFiveColor
lemma holeApprox_exists {c : ℂ → Fin 5} (hc : Measurable c) {α : ℝ}
    (hα : 0<α) (hα' : α<1/5) (L : Finset ℂ)
    (hL : ∀x∈Metric.closedBall (0:ℂ) 8,¬(transitionGraph c x).IsAcyclic → x∈L)
    {t : ℝ} (ht : 0<t) (ht' : t<1/2) : Nonempty (HoleApprox c α L t) := by
  obtain ⟨e,he,h⟩ := small_hole_map hc hα hα' L hL ht ht'
  let ε := min (e/2) (t/2)
  have hε : 0<ε := lt_min (by positivity) (by positivity)
  have hεe : ε<e := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεt : ε<t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨S,hS,hdis,hsum,g,hg⟩ := h ε hε hεe
  exact ⟨⟨ε,hε,hεt,S,hS,hdis,hsum,g,hg⟩⟩
namespace HoleApprox
lemma ε_tendsto {c : ℂ → Fin 5} {α : ℝ} {L : Finset ℂ} {t : ℕ → ℝ}
    (a : ∀n,HoleApprox c α L (t n)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => (a n).ε) atTop (𝓝 0) :=
  squeeze_zero (fun n => (a n).ε_pos.le) (fun n => (a n).ε_lt.le) ht
lemma sum_tendsto {c : ℂ → Fin 5} {α : ℝ} {L : Finset ℂ} {t : ℕ → ℝ}
    (a : ∀n,HoleApprox c α L (t n)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ∑d∈(a n).disks,d.radius) atTop (𝓝 0) :=
  squeeze_zero (fun n => Finset.sum_nonneg fun d hd => ((a n).valid d hd).1.le)
    (fun n => (a n).sum_lt.le) ht
lemma annuli_tendsto {c : ℂ → Fin 5} {α : ℝ} {L : Finset ℂ} {t : ℕ → ℝ}
    (a : ∀n,HoleApprox c α L (t n)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => volume (holeAnnuli (a n).disks)) atTop (𝓝 0) :=
  holeAnnuli_tendsto_zero _ (fun n d hd => ((a n).valid d hd).1.le) (sum_tendsto a ht)
end HoleApprox
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_GraphPatches
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u v
namespace EuclideanFiveColor
/-- Patch a map across separated bad fibers. Only the intervening values need lie in
 a contractible subspace; the map is kept on one closed set and made constant on the other. -/
theorem contractible_patch {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [NormalSpace X] (D : Set Y) [ContractibleSpace D]
    (f : C(X,Y)) {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hd : Disjoint A B)
    (hg : ∀x,x∉A → x∉B → f x∈D) :
    ∃a : D, ∃g : C(X,Y), EqOn g (fun _ => a.val) A ∧ EqOn g f B ∧
      ∀x,g x=f x ∨ g x∈D := by
  obtain ⟨t,htB,htA,ht⟩ := exists_continuous_zero_one_of_isClosed hB hA hd.symm
  obtain ⟨a,⟨H⟩⟩ := id_nullhomotopic D
  let S : Fin 3 → Set X := ![{x | t x≤1/3},{x | 1/3≤t x ∧ t x≤2/3},{x | 2/3≤t x}]
  have hS : ∀i,IsClosed (S i) := by
    intro i
    fin_cases i
    · exact isClosed_le t.continuous continuous_const
    · exact (isClosed_le continuous_const t.continuous).inter
        (isClosed_le t.continuous continuous_const)
    · exact isClosed_le continuous_const t.continuous
  have hc : ⋃i,S i=univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    by_cases h0 : t x≤1/3
    · exact ⟨0,h0⟩
    by_cases h1 : t x≤2/3
    · exact ⟨1,⟨(not_le.mp h0).le,h1⟩⟩
    · exact ⟨2,(not_le.mp h1).le⟩
  have hgood (x : S 1) : f x.val∈D := by
    apply hg
    · intro hx
      have he : t x.val=1 := htA hx
      have hh : t x.val≤2/3 := x.property.2
      linarith
    · intro hx
      have he : t x.val=0 := htB hx
      have hh : 1/3≤t x.val := x.property.1
      linarith
  have hτmem (x : S 1) : 3*t x.val-1∈unitInterval := by
    constructor
    · linarith [x.property.1]
    · linarith [x.property.2]
  let τ : C(S 1,unitInterval) := ⟨fun x => ⟨3*t x.val-1,hτmem x⟩,
    ((continuous_const.mul (t.continuous.comp continuous_subtype_val)).sub continuous_const).subtype_mk hτmem⟩
  let φ₁ : C(S 1,Y) := ⟨fun x => (H (τ x,⟨f x.val,hgood x⟩)).val,
    continuous_subtype_val.comp (H.continuous.comp (τ.continuous.prodMk
      ((f.continuous.comp continuous_subtype_val).subtype_mk hgood)))⟩
  let φ : ∀i,C(S i,Y) := fun i => Fin.cases (f.restrict (S 0))
    (fun j => Fin.cases φ₁ (fun j => ContinuousMap.const (S j.succ.succ) a.val) j) i
  have h01 (x : X) (h0 : x∈S 0) (h1 : x∈S 1) : φ 0 ⟨x,h0⟩=φ 1 ⟨x,h1⟩ := by
    have he : t x=1/3 := le_antisymm h0 h1.1
    have hτ : τ ⟨x,h1⟩=0 := by apply Subtype.ext; change 3*t x-1=0; rw [he]; norm_num
    change f x=(H (τ ⟨x,h1⟩,⟨f x,hgood ⟨x,h1⟩⟩)).val
    rw [hτ]
    exact congrArg Subtype.val (H.map_zero_left ⟨f x,hgood ⟨x,h1⟩⟩) |>.symm
  have h12 (x : X) (h1 : x∈S 1) (h2 : x∈S 2) : φ 1 ⟨x,h1⟩=φ 2 ⟨x,h2⟩ := by
    have he : t x=2/3 := le_antisymm h1.2 h2
    have hτ : τ ⟨x,h1⟩=1 := by apply Subtype.ext; change 3*t x-1=1; rw [he]; norm_num
    change (H (τ ⟨x,h1⟩,⟨f x,hgood ⟨x,h1⟩⟩)).val=a.val
    rw [hτ]
    exact congrArg Subtype.val (H.map_one_left ⟨f x,hgood ⟨x,h1⟩⟩)
  have hφ : ∀i j x (hi : x∈S i) (hj : x∈S j),φ i ⟨x,hi⟩=φ j ⟨x,hj⟩ := by
    intro i j x hi hj
    fin_cases i <;> fin_cases j
    · rfl
    · exact h01 x hi hj
    · have h0 : t x≤1/3 := hi; have h2 : 2/3≤t x := hj; linarith
    · exact (h01 x hj hi).symm
    · rfl
    · exact h12 x hi hj
    · have h0 : t x≤1/3 := hj; have h2 : 2/3≤t x := hi; linarith
    · exact (h12 x hj hi).symm
    · rfl
  refine ⟨a,closedCoverMap S hS hc φ hφ,?_,?_,?_⟩
  · intro x hx
    have hx2 : x∈S 2 := by change 2/3≤t x; rw [htA hx]; norm_num
    exact closedCoverMap_apply S hS hc φ hφ ⟨x,hx2⟩
  · intro x hx
    have hx0 : x∈S 0 := by change t x≤1/3; rw [htB hx]; norm_num
    exact closedCoverMap_apply S hS hc φ hφ ⟨x,hx0⟩
  · intro x
    obtain ⟨i,hi⟩ := iUnion_eq_univ_iff.mp hc x
    rw [closedCoverMap_apply S hS hc φ hφ ⟨x,hi⟩]
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (H (τ ⟨x,hi⟩,⟨f x,hgood ⟨x,hi⟩⟩)).property
    · exact Or.inr a.property
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u v
namespace EuclideanFiveColor
/-- If the crossing edges form a forest, the boundary map can be patched to a constant
 on the inner closed set, unchanged on the outer closed set. This replaces the graph-word
 and winding detour for the existential interface-cycle producer. -/
theorem graph_forest_patch {X : Type u} {V : Type v} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [Fintype V] [Nonempty V]
    (f : C(X,GraphSpace (⊤ : SimpleGraph V))) {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hd : Disjoint A B)
    (hforest : (crossingGraph (fun x => (f x).val) A B).IsAcyclic) :
    ∃a : GraphSpace (⊤ : SimpleGraph V), ∃g : C(X,GraphSpace (⊤ : SimpleGraph V)),
      EqOn g (fun _ => a) A ∧ EqOn g f B := by
  let G := crossingGraph (fun x => (f x).val) A B
  obtain ⟨T,hGT,_,hT⟩ := SimpleGraph.connected_top.exists_isTree_le_of_le_of_isAcyclic
    (show G≤⊤ from le_top) hforest
  let f₀ : C(X,V → ℝ) := ⟨fun x => (f x).val,continuous_subtype_val.comp f.continuous⟩
  let S : Finset (V → ℝ) := ((Finset.univ : Finset (V×V)).filter
    (fun a => a.1≠a.2 ∧ ¬T.Adj a.1 a.2)).image (fun a => graphEdgePoint a.1 a.2 (1/2))
  have hn : ∀b∈S,¬FiberCrosses f₀ A B b := by
    intro b hb
    obtain ⟨⟨i,j⟩,hij,rfl⟩ := Finset.mem_image.mp hb
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hij
    intro hh
    exact hij.2 (hGT ⟨hij.1,hh⟩)
  obtain ⟨C₀,C₁,hC₀,hC₁,hCd,hAC,hBC,hSC⟩ := finite_fiber_separation f₀ hA hB hd S hn
  let : ContractibleSpace (GraphCutSpace T) := graphCut_contractible hT
  have hg : ∀x,x∉C₀ → x∉C₁ → f₀ x∈graphCutRealization T := by
    intro x hx₀ hx₁
    refine ⟨(f x).property,?_⟩
    intro i j hij hTij he
    have hm : f₀ x∈S := Finset.mem_image.mpr ⟨(i,j),by simp [hij,hTij],he.symm⟩
    rcases hSC hm with hh|hh
    · exact hx₀ hh
    · exact hx₁ hh
  obtain ⟨a,g,hgA,hgB,hgR⟩ := contractible_patch (graphCutRealization T) f₀ hC₀.isClosed hC₁.isClosed hCd hg
  have hgr (x : X) : g x∈graphRealization (⊤ : SimpleGraph V) := by
    rcases hgR x with hh|hh
    · rw [hh]; exact (f x).property
    · exact hh.1
  let g' : C(X,GraphSpace (⊤ : SimpleGraph V)) := ⟨fun x => ⟨g x,hgr x⟩,g.continuous.subtype_mk hgr⟩
  refine ⟨⟨a.val,a.property.1⟩,g',?_,?_⟩
  · intro x hx
    apply Subtype.ext
    exact hgA (hAC hx)
  · intro x hx
    apply Subtype.ext
    exact hgB (hBC hx)
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
lemma planeAnnulus_compact (x : ℂ) (r R : ℝ) : IsCompact (planeAnnulus x r R) :=
  (isCompact_closedBall x R).diff Metric.isOpen_ball
/-- A forest crossing graph yields an actual extension of the outer boundary over
its disk. This uses compact fiber separation and tree contraction, not graph words. -/
theorem annulus_forest_extension {V : Type u} [Fintype V] [Nonempty V]
    {x : ℂ} {r R : ℝ} (hrR : r<R)
    (f : C(planeAnnulus x r R,GraphSpace (⊤ : SimpleGraph V)))
    (hforest : (crossingGraph (fun z => (f z).val) (annulusInner x r R) (annulusOuter x r R)).IsAcyclic) :
    ∃g : C(Metric.closedBall x R,GraphSpace (⊤ : SimpleGraph V)),
      ∀z : Metric.sphere x R,g ⟨z.val,Metric.sphere_subset_closedBall z.property⟩=
        f ⟨z.val,sphere_mem_annulus hrR.le z.property⟩ := by
  let : CompactSpace (planeAnnulus x r R) := isCompact_iff_compactSpace.mp (planeAnnulus_compact x r R)
  have hA : IsClosed (annulusInner x r R) := isClosed_eq (continuous_subtype_val.dist continuous_const) continuous_const
  have hB : IsClosed (annulusOuter x r R) := isClosed_eq (continuous_subtype_val.dist continuous_const) continuous_const
  have hd : Disjoint (annulusInner x r R) (annulusOuter x r R) := by
    apply disjoint_left.mpr
    intro z hz hz'
    exact hrR.ne (hz.symm.trans hz')
  obtain ⟨a,g,hgA,hgB⟩ := graph_forest_patch f hA hB hd hforest
  let X := Metric.closedBall x R
  let Z : Bool → Set X := fun b => if b then {z | r≤dist z.val x} else {z | dist z.val x ≤ r}
  have hZ : ∀b,IsClosed (Z b) := by
    intro b
    cases b
    · exact isClosed_le (continuous_subtype_val.dist continuous_const) continuous_const
    · exact isClosed_le continuous_const (continuous_subtype_val.dist continuous_const)
  have hcov : ⋃b,Z b=univ := by
    apply iUnion_eq_univ_iff.mpr
    intro z
    rcases le_total (dist z.val x) r with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  let g₁ : C(Z true,GraphSpace (⊤ : SimpleGraph V)) :=
    ⟨fun z => g ⟨z.val.val,mem_planeAnnulus.mpr ⟨z.val.property,z.property⟩⟩,
      g.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
  let φ : ∀b,C(Z b,GraphSpace (⊤ : SimpleGraph V)) := fun b => Bool.casesOn b (ContinuousMap.const _ a) g₁
  have heq (z : X) (h0 : z∈Z false) (h1 : z∈Z true) : φ false ⟨z,h0⟩=φ true ⟨z,h1⟩ := by
    exact (hgA (show (⟨z.val,mem_planeAnnulus.mpr ⟨z.property,h1⟩⟩ : planeAnnulus x r R)∈annulusInner x r R from
      le_antisymm h0 h1)).symm
  have hφ : ∀i j z (hi : z∈Z i) (hj : z∈Z j),φ i ⟨z,hi⟩=φ j ⟨z,hj⟩ := by
    intro i j z hi hj
    cases i <;> cases j
    · rfl
    · exact heq z hi hj
    · exact (heq z hj hi).symm
    · rfl
  refine ⟨closedCoverMap Z hZ hcov φ hφ,fun z => ?_⟩
  have hz : (⟨z.val,Metric.sphere_subset_closedBall z.property⟩ : X)∈Z true := by
    change r≤dist z.val x
    rw [show dist z.val x=R from z.property]
    exact hrR.le
  rw [closedCoverMap_apply Z hZ hcov φ hφ (i:=true) ⟨⟨z.val,Metric.sphere_subset_closedBall z.property⟩,hz⟩]
  exact hgB z.property
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
lemma finite_centers_separation (L : Finset ℂ) : ∃s>0,∀x∈L,∀y∈L,x≠y → s<dist x y := by
  let P := {p : L×L // p.1≠p.2}
  obtain ⟨s,hs,hsp⟩ := finite_pos_lt (fun p : P => dist p.val.1.val p.val.2.val)
    (fun p => dist_pos.mpr (fun he => p.property (Subtype.ext he)))
  refine ⟨s,hs,fun x hx y hy hxy => ?_⟩
  exact hsp ⟨(⟨x,hx⟩,⟨y,hy⟩),fun h => hxy (congrArg Subtype.val h)⟩
lemma mem_centerDisks {L : Finset ℂ} {R : ℝ} {d : MarkedDisk} :
    d∈centerDisks L R ↔ ∃x∈L,d=⟨x,R,false⟩ := by simp [centerDisks,eq_comm]
lemma centerDisks_sum (L : Finset ℂ) (R : ℝ) : (∑d∈centerDisks L R,d.radius)=(L.card:ℝ)*R := by
  rw [centerDisks,Finset.sum_image (fun x _ y _ h => congrArg MarkedDisk.center h)]
  simp
lemma centerDisks_disjoint {L : Finset ℂ} {R : ℝ}
    (hsep : ∀x∈L,∀y∈L,x≠y → 2*R<dist x y) :
    (centerDisks L R : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall) := by
  intro a ha b hb hab
  obtain ⟨x,hx,rfl⟩ := mem_centerDisks.mp ha
  obtain ⟨y,hy,rfl⟩ := mem_centerDisks.mp hb
  have hxy : x≠y := by intro he; subst y; exact hab rfl
  apply disjoint_left.mpr
  intro z hz hz'
  have h1 : dist x z≤R := by simpa only [MarkedDisk.closedBall,Metric.mem_closedBall,dist_comm] using hz
  have h2 : dist z y≤R := hz'
  have hh := dist_triangle x z y
  have hh' := hsep x hx y hy hxy
  linarith
lemma mem_center_holes {L : Finset ℂ} {R : ℝ} {z : ℂ} :
    z∈diskHoles (centerDisks L R) ↔ ∃x∈L,dist z x<R := by
  rw [mem_diskHoles]
  constructor
  · rintro ⟨d,hd,hzd⟩
    obtain ⟨x,hx,rfl⟩ := mem_centerDisks.mp hd
    exact ⟨x,hx,hzd⟩
  · rintro ⟨x,hx,hzx⟩
    exact ⟨⟨x,R,false⟩,mem_centerDisks.mpr ⟨x,hx,rfl⟩,hzx⟩
namespace HoleApprox
lemma outside_centers_in_domain {c : ℂ → Fin 5} {α t R : ℝ} {L : Finset ℂ}
    (a : HoleApprox c α L t) (htR : 2*t<R) (ht1 : 2*t<1) :
    Metric.closedBall (0:ℂ) 5 \ diskHoles (centerDisks (activeCenters L) R)⊆
      Metric.closedBall (0:ℂ) 7 \ coreHoles a.disks := by
  intro z hz
  refine ⟨Metric.closedBall_subset_closedBall (by norm_num) hz.1,?_⟩
  intro hh
  obtain ⟨y,hy⟩ := mem_iUnion.mp (a.cores_near hh)
  obtain ⟨hyL,hzy⟩ := mem_iUnion.mp hy
  change dist z y<2*t at hzy
  have hy0 : dist y 0≤6 := calc
    dist y 0≤dist y z+dist z 0 := dist_triangle _ _ _
    _ ≤ 6 := by rw [dist_comm y z]; have hz0 : dist z 0≤5 := hz.1; linarith
  exact hz.2 (mem_center_holes.mpr ⟨y,Finset.mem_filter.mpr ⟨hyL,hy0⟩,hzy.trans htR⟩)
end HoleApprox
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_FullApproximation
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
/-- Actual finite disk pasting from a closed outside domain. Disks may cross the
boundary of the ambient compact region. -/
theorem finite_disk_paste {Y : Type u} [TopologicalSpace Y] (Q : Set ℂ)
    (S : Finset MarkedDisk)
    (hdis : (S : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall))
    (f : C(↥(Q \ diskHoles S),Y))
    (g : ∀d : S,C(d.val.closedBall,Y))
    (hb : ∀d : S,∀z : Metric.sphere d.val.center d.val.radius,∀hzQ : z.val∈Q,
      ∀hzS : z.val∉diskHoles S,
      g d ⟨z.val,Metric.sphere_subset_closedBall z.property⟩=f ⟨z.val,hzQ,hzS⟩) :
    ∃F : C(Q,Y),∀z : Q,∀hz : z.val∉diskHoles S,F z=f ⟨z.val,z.property,hz⟩ := by
  let Z : Option S → Set Q := fun i => match i with
    | none => {z | z.val∉diskHoles S}
    | some d => {z | z.val∈d.val.closedBall}
  have hZ : ∀i,IsClosed (Z i) := by
    intro i
    cases i with
    | none => exact (diskHoles_open S).isClosed_compl.preimage continuous_subtype_val
    | some d => exact Metric.isClosed_closedBall.preimage continuous_subtype_val
  have hcov : ⋃i,Z i=univ := by
    apply iUnion_eq_univ_iff.mpr
    intro z
    by_cases hz : z.val∈diskHoles S
    · obtain ⟨d,hd,hzd⟩ := mem_diskHoles.mp hz
      exact ⟨some ⟨d,hd⟩,Metric.ball_subset_closedBall hzd⟩
    · exact ⟨none,hz⟩
  let φ₀ : C(Z none,Y) := ⟨fun z => f ⟨z.val.val,z.val.property,z.property⟩,
    f.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
  let φ₁ (d : S) : C(Z (some d),Y) := ⟨fun z => g d ⟨z.val.val,z.property⟩,
    (g d).continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
  let φ : ∀i,C(Z i,Y) := fun i => match i with | none => φ₀ | some d => φ₁ d
  have hbd (d : S) (z : Q) (h0 : z∈Z none) (h1 : z∈Z (some d)) :
      φ none ⟨z,h0⟩=φ (some d) ⟨z,h1⟩ := by
    have hn : z.val∉d.val.ball := fun hz => h0 (mem_diskHoles.mpr ⟨d.val,d.property,hz⟩)
    have hs : z.val∈Metric.sphere d.val.center d.val.radius :=
      le_antisymm h1 (le_of_not_gt hn)
    exact (hb d ⟨z.val,hs⟩ z.property h0).symm
  have hφ : ∀i j z (hi : z∈Z i) (hj : z∈Z j),φ i ⟨z,hi⟩=φ j ⟨z,hj⟩ := by
    intro i j z hi hj
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some d => exact hbd d z hi hj
    | some d =>
      cases j with
      | none => exact (hbd d z hj hi).symm
      | some e =>
        by_cases hde : d=e
        · subst e; rfl
        · exact False.elim (Set.disjoint_left.mp (hdis d.property e.property
            (fun he => hde (Subtype.ext he))) hi hj)
  refine ⟨closedCoverMap Z hZ hcov φ hφ,fun z hz => ?_⟩
  exact closedCoverMap_apply Z hZ hcov φ hφ (i:=none) ⟨z,hz⟩
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory ContinuousMap
namespace EuclideanFiveColor
namespace HoleApprox
/-- Fill all the actual core holes simultaneously when their surrounding crossing
graphs are forests, retaining the threshold map outside the original and outer disks. -/
theorem fill_cores {c : ℂ → Fin 5} {α t R : ℝ} {L : Finset ℂ}
    (a : HoleApprox c α L t) (hR : R<1) (htR : 2*t<R)
    (hsep : ∀x∈L,∀y∈L,x≠y → 2*R<dist x y)
    (hforest : ∀x (hx : x∈activeCenters L),
      (crossingGraph (fun z => (a.annulusMap hR htR hsep hx z).val)
        (annulusInner x (2*t) R) (annulusOuter x (2*t) R)).IsAcyclic) :
    ∃F : C(Metric.closedBall (0:ℂ) 5,GraphSpace (⊤ : SimpleGraph (Fin 5))),
      ∀z : Metric.closedBall (0:ℂ) 5,z.val∉diskHoles a.disks →
        z.val∉diskHoles (centerDisks (activeCenters L) R) →
        (F z).val=thresholdMap c a.ε α z.val := by
  let D := centerDisks (activeCenters L) R
  have hdis : (D : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall) :=
    centerDisks_disjoint fun x hx y hy hxy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  let f : C(↥(Metric.closedBall (0:ℂ) 5 \ diskHoles D),GraphSpace (⊤ : SimpleGraph (Fin 5))) :=
    ⟨fun z => a.map ⟨z.val,a.outside_centers_in_domain htR (htR.trans hR) z.property⟩,
      a.map.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  have hex (d : D) : ∃g : C(d.val.closedBall,GraphSpace (⊤ : SimpleGraph (Fin 5))),
      ∀z : Metric.sphere d.val.center d.val.radius,∀hzQ : z.val∈Metric.closedBall (0:ℂ) 5,
        ∀hzD : z.val∉diskHoles D,
        g ⟨z.val,Metric.sphere_subset_closedBall z.property⟩=f ⟨z.val,hzQ,hzD⟩ := by
    obtain ⟨d,hd⟩ := d
    obtain ⟨x,hx,rfl⟩ := mem_centerDisks.mp hd
    obtain ⟨g,hg⟩ := annulus_forest_extension htR (a.annulusMap hR htR hsep hx) (hforest x hx)
    exact ⟨g,fun z _ _ => hg z⟩
  choose g hg using hex
  obtain ⟨F,hF⟩ := finite_disk_paste (Metric.closedBall (0:ℂ) 5) D hdis f g hg
  refine ⟨F,fun z hzS hzD => ?_⟩
  rw [hF z hzD]
  exact a.agrees _ hzS
/-- The common-exclusion limit contradiction applies to the constructed maps, so
all these actual core fillings exist eventually at any fixed separated outer scale. -/
theorem eventually_fill_cores {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {α R : ℝ} (hα : 0<α) (hα' : α<1/5) {L : Finset ℂ} {t : ℕ → ℝ}
    (a : ∀n,HoleApprox c α L (t n)) (ht : Tendsto t atTop (𝓝 0))
    (hR0 : 0<R) (hR : R<1) (htR : ∀n,2*t n<R)
    (hsep : ∀x∈L,∀y∈L,x≠y → 2*R<dist x y) :
    ∀ᶠ n in atTop,∃F : C(Metric.closedBall (0:ℂ) 5,GraphSpace (⊤ : SimpleGraph (Fin 5))),
      ∀z : Metric.closedBall (0:ℂ) 5,z.val∉diskHoles (a n).disks →
        z.val∉diskHoles (centerDisks (activeCenters L) R) →
        (F z).val=thresholdMap c (a n).ε α z.val := by
  have hrad : Tendsto (fun n => 2*t n) atTop (𝓝 0) := by simpa using ht.const_mul 2
  have h (x : activeCenters L) : ∀ᶠ n in atTop,
      (crossingGraph (fun z => ((a n).annulusMap hR (htR n) hsep x.property z).val)
        (annulusInner x.val (2*t n) R) (annulusOuter x.val (2*t n) R)).IsAcyclic := by
    apply annulus_maps_eventually_forest hc hw hR0 hrad (ε_tendsto a ht)
      (fun n => (a n).ε_pos) (annuli_tendsto a ht)
      (fun _ _ _ => unit_from_hole_mem_annuli) hα hα'
      (fun n => (a n).annulusMap hR (htR n) hsep x.property)
    intro n z hz
    exact (a n).agrees _ hz
  have hall := eventually_all.mpr h
  filter_upwards [hall] with n hn
  exact (a n).fill_cores hR (htR n) hsep (fun x hx => hn ⟨x,hx⟩)
end HoleApprox
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
lemma diskHoles_union (S T : Finset MarkedDisk) : diskHoles (S∪T)=diskHoles S∪diskHoles T := by
  ext z
  simp only [mem_diskHoles,Finset.mem_union,mem_union]
  aesop
lemma disk_radius_sum_union_le (S T : Finset MarkedDisk) (h : ∀d∈S∪T,0≤d.radius) :
    (∑d∈S∪T,d.radius)≤(∑d∈S,d.radius)+(∑d∈T,d.radius) := by
  have hs : (∑d∈S∪T,d.radius)+(∑d∈S∩T,d.radius)=(∑d∈S,d.radius)+(∑d∈T,d.radius) := Finset.sum_union_inter
  have h0 : 0≤∑d∈S∩T,d.radius := Finset.sum_nonneg fun d hd =>
    h d (Finset.mem_union_left T (Finset.mem_inter.mp hd).1)
  linarith
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory ContinuousMap
namespace EuclideanFiveColor
/-- The whole producer, using actual annular crossing fibers and all angular
contradictions: global graph approximants exist at arbitrarily small exception scales. -/
theorem fullApprox_exists_of_finite_core {c : ℂ → Fin 5} (hc : Measurable c)
    (hw : WeakColoring 5 c) {α : ℝ} (hα : 0<α) (hα' : α<1/5)
    (L : Finset ℂ) (hL : ∀x∈Metric.closedBall (0:ℂ) 8,¬(transitionGraph c x).IsAcyclic → x∈L)
    {t : ℝ} (ht : 0<t) : Nonempty (FullApprox c α t) := by
  obtain ⟨s,hs,hsep⟩ := finite_centers_separation L
  let A := activeCenters L
  let R := min (s/4) (min (1/2) (t/(4*((A.card:ℝ)+1))))
  have hR0 : 0<R := lt_min (by positivity) (lt_min (by norm_num) (div_pos ht (by positivity)))
  have hRs : R ≤ s/4 := min_le_left _ _
  have hRhalf : R≤1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hRt : R≤t/(4*((A.card:ℝ)+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hR1 : R<1 := lt_of_le_of_lt hRhalf (by norm_num)
  have hRsep : ∀x∈L,∀y∈L,x≠y → 2*R<dist x y := by
    intro x hx y hy hxy
    have hh := hsep x hx y hy hxy
    linarith
  have hRbudget : (A.card:ℝ)*R<t/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*((A.card:ℝ)+1))).mp hRt
    nlinarith
  let u : ℕ → ℝ := fun n => min (R/4) (min (t/4) (1/((n:ℝ)+1)))
  have hu : ∀n,0<u n := fun n => lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have huR : ∀n,2*u n<R := by
    intro n
    have hh : u n≤R/4 := min_le_left _ _
    linarith
  have hut : ∀n,u n<t := by
    intro n
    have hh : u n≤t/4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hult : ∀n,u n<1/2 := by
    intro n
    have hh := huR n
    linarith
  have hulim : Tendsto u atTop (𝓝 0) :=
    squeeze_zero (fun n => (hu n).le) (fun n => (min_le_right _ _).trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  let a : ∀n,HoleApprox c α L (u n) := fun n => Classical.choice (holeApprox_exists hc hα hα' L hL (hu n) (hult n))
  obtain ⟨n,F,hF⟩ := ((HoleApprox.eventually_fill_cores hc hw hα hα' a hulim hR0 hR1 huR hRsep).exists)
  let D := centerDisks A R
  have hD : ∀d∈D,d.Valid (L : Set ℂ) := by
    intro d hd
    obtain ⟨x,hx,rfl⟩ := mem_centerDisks.mp hd
    exact ⟨hR0,by simp⟩
  have hU : ∀d∈(a n).disks∪D,d.Valid (L : Set ℂ) := by
    intro d hd
    rcases Finset.mem_union.mp hd with hh|hh
    · exact (a n).valid d hh
    · exact hD d hh
  obtain ⟨S,hS,hdis,hcov,hsum,_⟩ := MarkedDisk.separate ((a n).disks∪D) hU (show 0<t/4 by positivity)
  have htS : (∑d∈S,d.radius)<t := by
    have hh := disk_radius_sum_union_le (a n).disks D (fun d hd => (hU d hd).1.le)
    have hDbudget : (∑d∈D,d.radius)<t/4 := by rw [centerDisks_sum]; exact hRbudget
    have hun : u n≤t/4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith [(a n).sum_lt]
  refine ⟨⟨(a n).ε,(a n).ε_pos,(a n).ε_lt.trans (hut n),S,
    fun d hd => (hS d hd).1,hdis,htS,F,?_⟩⟩
  intro z hz
  have hn : z.val∉diskHoles ((a n).disks∪D) := fun hh => hz ((MarkedDisk.holes_subset_of_cover hcov).1 hh)
  rw [diskHoles_union] at hn
  exact hF z (fun hh => hn (Or.inl hh)) (fun hh => hn (Or.inr hh))
/-- The finite core used above is obtained from the proved actual transition core
local-finiteness theorem; no regularity of the original coloring is added. -/
theorem fullApprox_exists_oai {c : ℂ → Fin 5} (hc : Measurable c)
    (hw : WeakColoring 5 c) {α : ℝ} (hα : 0<α) (hα' : α<1/5) {t : ℝ} (ht : 0<t) :
    Nonempty (FullApprox c α t) := by
  let hfin := cyclicCore_compact_finite c hc hw (isCompact_closedBall (0:ℂ) 8)
  exact fullApprox_exists_of_finite_core hc hw hα hα' hfin.toFinset
    (fun x hx hcyc => hfin.mem_toFinset.mpr ⟨hx,hcyc⟩) ht
end EuclideanFiveColor
end

end OAI
end

theorem solution : type_of% @OAI.EuclideanFiveColor.fullApprox_exists_oai := @OAI.EuclideanFiveColor.fullApprox_exists_oai
