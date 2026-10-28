-- Prove2me | solution 1 for OAI.PlanarFPP.ae_eventually_spatial_long_paths
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:43:39.035293+00:00
-- url     : https://prove2.me/submissions/e9353522-024b-4637-a552-0381ca0c415a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Paths
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem pathCost_append (τ : Edge → ℝ) (p : Vertex) (ds es : List Step) :
    pathCost τ p (ds ++ es) =
      pathCost τ p ds + pathCost τ (p + displacement ds) es := by
  induction ds generalizing p with
  | nil => simp [pathCost]
  | cons d ds ih => simp [pathCost, ih, add_assoc]

theorem pathCost_nonneg {τ : Edge → ℝ} (hτ : ∀ e, 0 ≤ τ e)
    (p : Vertex) (ds : List Step) : 0 ≤ pathCost τ p ds := by
  induction ds generalizing p with
  | nil => exact le_refl 0
  | cons d ds ih => exact add_nonneg (hτ _) (ih _)

theorem defect_append (τ : Edge → ℝ) (b m a : ℝ) (p : Vertex) (ds es : List Step) :
    defect τ b m a p (ds ++ es) =
      defect τ b m a p ds + defect τ b m a (p + displacement ds) es := by
  simp [defect, pathCost_append]; ring

theorem minimum_defect (τ : Edge → ℝ) (b m am ap : ℝ) (ha : am ≤ ap)
    (p : Vertex) (ds : List Step) :
    min (defect τ b m ap p ds) (defect τ b m am p ds) =
      defect τ b m ((am + ap) / 2) p ds -
        ((ap - am) / 2) * |transverse b (displacement ds)| := by
  unfold defect support
  by_cases hr : 0 ≤ transverse b (displacement ds)
  · rw [abs_of_nonneg hr, min_eq_left]
    · ring
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha) hr]
  · have hr' : transverse b (displacement ds) ≤ 0 := le_of_not_ge hr
    rw [abs_of_nonpos hr', min_eq_right]
    · ring
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha) hr']

theorem transverse_chunk_witness (τ : Edge → ℝ) (b m am ap η s : ℝ)
    (ha : am ≤ ap) (hs : 0 < s) (hη : 0 < η)
    (hgap : 4 * η ≤ (ap - am) / 2) (p : Vertex) (ds : List Step)
    (hfull : s ≤ |transverse b (displacement ds)|)
    (hcheap : defect τ b m ((am + ap) / 2) p ds < η * s) :
    defect τ b m ap p ds < -η * s ∨ defect τ b m am p ds < -η * s := by
  have hm := minimum_defect τ b m am ap ha p ds
  have hg : 0 ≤ (ap - am) / 2 := by linarith
  have hprod := mul_le_mul_of_nonneg_left hfull hg
  have hprod' := mul_le_mul_of_nonneg_right hgap (le_of_lt hs)
  have : min (defect τ b m ap p ds) (defect τ b m am p ds) < -η * s := by
    nlinarith [mul_pos hη hs]
  exact min_lt_iff.mp this

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ProbabilityFoundations
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Filter

theorem rateOne_ae_positive : ∀ᵐ x ∂expMeasure 1, 0 < x := by
  have hc : (expMeasure 1 (Iic 0)).toReal = 0 := by
    rw [← measureReal_def, ← cdf_eq_real]
    simp [cdf_expMeasure_eq (r := 1) (by norm_num)]
  have hz : expMeasure 1 (Iic 0) = 0 :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.zero_ne_top).mp
      (by simpa using hc)
  simpa only [ae_iff, not_lt, Iic] using hz

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ExponentialEnvironment.ae_positive (h : ExponentialEnvironment P τ) :
    ∀ᵐ ω ∂P, ∀ e, 0 < τ e ω := by
  rw [ae_all_iff]
  intro e
  have hp : ∀ᵐ x ∂Measure.map (τ e) P, 0 < x := by
    rw [h.marginal e]
    exact rateOne_ae_positive
  exact (ae_map_iff (h.measurable e).aemeasurable measurableSet_Ioi).mp hp

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LocalizedEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

theorem mem_internalEdges (e : Edge) (V : Finset Vertex) :
    e ∈ internalEdges V ↔ e.1 ∈ V ∧ edgeEnd e ∈ V := by
  simp [internalEdges]

theorem step_mem_internalEdges (V : Finset Vertex) (p : Vertex) (d : Step)
    (hp : p ∈ V) (hq : p+d.delta ∈ V) : d.edge p ∈ internalEdges V := by
  rw [mem_internalEdges]
  cases d <;> simp_all [Step.edge,Step.delta,edgeEnd,add_assoc]
  all_goals change p+0 ∈ V; simpa using hp

theorem pathIn_cons_iff (p : Vertex) (d : Step) (ds : List Step) (S : Set Vertex) :
    PathIn p (d::ds) S ↔ p ∈ S ∧ PathIn (p+d.delta) ds S := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp),?_⟩
    intro i hi
    have hh := h (i+1) (by simpa using hi)
    simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh
  · rintro ⟨hp,ht⟩ i hi
    cases i with
    | zero => simpa using hp
    | succ i =>
      have hh := ht i (by simpa using hi)
      simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh

theorem pathIn_endpoint (p : Vertex) (ds : List Step) (S : Set Vertex)
    (h : PathIn p ds S) : p+displacement ds ∈ S := by
  simpa using h ds.length le_rfl

theorem pathEdges_subset_internalEdges (V : Finset Vertex) (p : Vertex) (ds : List Step)
    (h : PathIn p ds (V : Set Vertex)) : pathEdges p ds ⊆ internalEdges V := by
  induction ds generalizing p with
  | nil => simp [pathEdges]
  | cons d ds ih =>
    obtain ⟨hp,ht⟩ := (pathIn_cons_iff p d ds _).mp h
    have hq : p+d.delta ∈ V := by simpa using ht 0 (by omega)
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · rw [he]
      exact step_mem_internalEdges V p d hp hq
    · exact ih (p+d.delta) ht he

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PathConcatenation
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

theorem pathIn_append (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (hd : PathIn p ds S) (he : PathIn (p+displacement ds) es S) :
    PathIn p (ds++es) S := by
  intro i hi
  by_cases hid : i ≤ ds.length
  · simpa only [List.take_append, Nat.sub_eq_zero_of_le hid, List.take_zero,
      List.append_nil] using hd i hid
  · have hle : ds.length ≤ i := by omega
    have hie : i-ds.length ≤ es.length := by simp only [List.length_append] at hi; omega
    have hh := he (i-ds.length) hie
    simpa only [List.take_append, List.take_of_length_le hle, displacement_append,
      add_assoc] using hh

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PathSubpaths
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

lemma pathIn_append_left (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (h : PathIn p (ds++es) S) : PathIn p ds S := by
  intro i hi
  have hh := h i (by simp only [List.length_append]; omega)
  simpa only [List.take_append,Nat.sub_eq_zero_of_le hi,List.take_zero,List.append_nil] using hh

lemma pathIn_append_right (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (h : PathIn p (ds++es) S) : PathIn (p+displacement ds) es S := by
  intro i hi
  have hh := h (ds.length+i) (by simp only [List.length_append]; omega)
  simpa only [List.take_append,List.take_of_length_le (show ds.length ≤ ds.length+i by omega),
    Nat.add_sub_cancel_left,displacement_append,add_assoc] using hh

lemma pathIn_reverseSteps (p : Vertex) (ds : List Step) (S : Set Vertex)
    (h : PathIn p ds S) : PathIn (p+displacement ds) (reverseSteps ds) S := by
  induction ds generalizing p with
  | nil => simpa [reverseSteps] using h
  | cons d ds ih =>
    obtain ⟨hp,ht⟩ := (pathIn_cons_iff p d ds S).mp h
    have hi := ih (p+d.delta) ht
    have hend : p+displacement (d::ds)+displacement (reverseSteps ds)=p+d.delta := by
      rw [displacement_cons,displacement_reverseSteps]
      abel
    have hs : PathIn (p+d.delta) [d.reverse] S := by
      apply (pathIn_cons_iff _ _ _ _).mpr
      refine ⟨?_,?_⟩
      · simpa using ht 0 (by omega)
      · intro i _
        simpa using hp
    have he : reverseSteps (d::ds)=reverseSteps ds++[d.reverse] := by simp [reverseSteps]
    rw [he]
    apply pathIn_append _ _ _ _ (by simpa [displacement_cons,add_assoc] using hi)
    simpa only [hend] using hs

lemma path_first_column_up (p : Vertex) (ds : List Step) (X : ℤ)
    (hp : p.1 ≤ X) (hend : X ≤ (p+displacement ds).1) :
    ∃ pre rest : List Step, ds=pre++rest ∧ (p+displacement pre).1=X ∧
      PathIn p pre {z | z.1 ≤ X} := by
  induction ds generalizing p with
  | nil =>
    refine ⟨[],[],rfl,by simpa using le_antisymm hp (by simpa using hend),?_⟩
    intro i _
    simpa using hp
  | cons d ds ih =>
    by_cases he : p.1=X
    · refine ⟨[],d::ds,rfl,by simpa using he,?_⟩
      intro i _
      simpa using hp
    · have hp' : (p+d.delta).1 ≤ X := by
        cases d <;> simp only [Step.delta,Prod.fst_add] <;> omega
      have hend' : X ≤ (p+d.delta+displacement ds).1 := by
        simpa only [displacement_cons,add_assoc] using hend
      obtain ⟨pre,rest,heq,hcol,hin⟩ := ih (p+d.delta) hp' hend'
      refine ⟨d::pre,rest,by simp [heq],by simpa [displacement_cons,add_assoc] using hcol,?_⟩
      exact (pathIn_cons_iff ..).mpr ⟨hp,hin⟩

lemma path_first_column_down (p : Vertex) (ds : List Step) (X : ℤ)
    (hp : X ≤ p.1) (hend : (p+displacement ds).1 ≤ X) :
    ∃ pre rest : List Step, ds=pre++rest ∧ (p+displacement pre).1=X ∧
      PathIn p pre {z | X ≤ z.1} := by
  induction ds generalizing p with
  | nil =>
    refine ⟨[],[],rfl,by simpa using le_antisymm (by simpa using hend) hp,?_⟩
    intro i _
    simpa using hp
  | cons d ds ih =>
    by_cases he : p.1=X
    · refine ⟨[],d::ds,rfl,by simpa using he,?_⟩
      intro i _
      simpa using hp
    · have hp' : X ≤ (p+d.delta).1 := by
        cases d <;> simp only [Step.delta,Prod.fst_add] <;> omega
      have hend' : (p+d.delta+displacement ds).1 ≤ X := by
        simpa only [displacement_cons,add_assoc] using hend
      obtain ⟨pre,rest,heq,hcol,hin⟩ := ih (p+d.delta) hp' hend'
      refine ⟨d::pre,rest,by simp [heq],by simpa [displacement_cons,add_assoc] using hcol,?_⟩
      exact (pathIn_cons_iff ..).mpr ⟨hp,hin⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PathColumnCrossing
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

theorem path_column_subcrossing (p : Vertex) (ds : List Step) (A B : ℤ)
    (hp : p.1 ≤ A) (hAB : A ≤ B) (hend : B ≤ (p+displacement ds).1) :
    ∃ pre mid post : List Step, ds=pre++mid++post ∧
      (p+displacement pre).1=A ∧
      (p+displacement pre+displacement mid).1=B ∧
      PathIn (p+displacement pre) mid {z | A ≤ z.1 ∧ z.1 ≤ B} := by
  obtain ⟨front,post,he,hB,hinB⟩ := path_first_column_up p ds B (hp.trans hAB) hend
  let zB := p+displacement front
  have hrev : zB+displacement (reverseSteps front)=p := by simp [zB]
  obtain ⟨revMid,revPre,heR,hA,hinA⟩ := path_first_column_down zB (reverseSteps front) A
    (by change A ≤ (p+displacement front).1; omega) (by rw [hrev]; exact hp)
  have hfront : front=reverseSteps revPre++reverseSteps revMid := by
    have hh := congrArg reverseSteps heR
    simpa only [reverseSteps_reverse,reverseSteps_append] using hh
  have hfull : zB+displacement revMid+displacement revPre=p := by
    rw [heR,displacement_append,← add_assoc] at hrev
    exact hrev
  have hstart : p+displacement (reverseSteps revPre)=zB+displacement revMid := by
    rw [displacement_reverseSteps,← hfull]
    abel
  have hmid : p+displacement (reverseSteps revPre)+displacement (reverseSteps revMid)=zB := by
    rw [hstart,displacement_reverseSteps]
    abel
  refine ⟨reverseSteps revPre,reverseSteps revMid,post,by rw [he,hfront],?_,?_,?_⟩
  · rw [hstart]
    exact hA
  · rw [hmid]
    exact hB
  · have hl := pathIn_reverseSteps zB revMid {z | A ≤ z.1} hinA
    have hu := pathIn_append_right p (reverseSteps revPre) (reverseSteps revMid) {z | z.1 ≤ B}
      (by rw [← hfront]; exact hinB)
    rw [← hstart] at hl
    intro i hi
    exact ⟨hl i hi,hu i hi⟩

lemma pathIn_middle (p : Vertex) (pre mid post : List Step) (S : Set Vertex)
    (h : PathIn p (pre++mid++post) S) : PathIn (p+displacement pre) mid S :=
  pathIn_append_right p pre mid S (pathIn_append_left p (pre++mid) post S h)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_WitnessDecomposition
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

variable {α : Type*}

theorem first_drop (d : α → ℝ) (η : ℝ) (xs : List α)
    (hstep : ∀ x ∈ xs, -η ≤ d x) (a : ℝ) (ha : -η ≤ a)
    (hdrop : a + total d xs < -η) :
    ∃ pre rest, xs = pre ++ rest ∧ pre ≠ [] ∧
      -2 * η ≤ a + total d pre ∧ a + total d pre < -η := by
  induction xs generalizing a with
  | nil => simp at hdrop; linarith
  | cons x xs ih =>
    have hx := hstep x (by simp)
    have ht : ∀ y ∈ xs, -η ≤ d y := fun y hy => hstep y (by simp [hy])
    by_cases h : a + d x < -η
    · refine ⟨[x], xs, rfl, by simp, ?_, ?_⟩ <;> simp <;> linarith
    · obtain ⟨pre, rest, heq, hne, hlo, hhi⟩ :=
        ih ht (a + d x) (le_of_not_gt h) (by simpa [add_assoc] using hdrop)
      refine ⟨x :: pre, rest, by simp [heq], by simp, ?_, ?_⟩
      · simpa [add_assoc] using hlo
      · simpa [add_assoc] using hhi

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PathWitnesses
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem trace_total_defect (τ : Edge → ℝ) (b m a : ℝ) (p : Vertex) (ds : List Step) :
    total (stepDefect τ b m a) (trace p ds) = defect τ b m a p ds := by
  induction ds generalizing p with
  | nil => simp [trace, defect, pathCost]
  | cons d ds ih =>
    simp [trace, ih, defect, pathCost, stepDefect, traversalEdge]
    ring

theorem support_step_bound (b m a : ℝ) (d : Step) :
    support b m a d.delta ≤ max |m - a * b| |a| := by
  cases d with
  | east =>
    have he : support b m a Step.east.delta = m - a * b := by
      simp [Step.delta, support, transverse]; ring
    rw [he]
    exact (le_abs_self _).trans (le_max_left _ _)
  | west =>
    have he : support b m a Step.west.delta = -(m - a * b) := by
      simp [Step.delta, support, transverse]; ring
    rw [he]
    exact (neg_le_abs _).trans (le_max_left _ _)
  | north =>
    simpa [Step.delta, support, transverse] using (le_abs_self a).trans (le_max_right |m-a*b| |a|)
  | south =>
    simpa [Step.delta, support, transverse] using (neg_le_abs a).trans (le_max_right |m-a*b| |a|)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointMesh
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

lemma meshFloor_bounds (x d : ℤ) (hd : 0 < d) :
    meshFloor x d ≤ x ∧ x < meshFloor x d+d := by
  have h0 := Int.emod_nonneg x (ne_of_gt hd)
  have h1 := Int.emod_lt_of_pos x hd
  have he := Int.emod_add_ediv_mul x d
  dsimp [meshFloor]
  omega

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

lemma spatialWitness_edges (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ)
    (p : StrictPathWitness) (hp : p ∈ spatialWitnessFamily b m₀ am ap K η k m ih) :
    p.edges ⊆ spatialWitnessSupport b k m ih := by
  apply pathEdges_subset_internalEdges
  rcases hp with ⟨hin,_⟩ | ⟨_,_,hin,_⟩
  · intro i hi
    apply Finset.mem_union.mpr
    exact Or.inl ((translatedEndpointBox_finite ..).mem_toFinset.mpr (hin i hi))
  · intro i hi
    exact Finset.mem_union.mpr (Or.inr ((mem_rareFastVertices ..).mpr (hin i hi)))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialChunkGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

lemma spatialTranslate_center (b : ℝ) (k m : ℕ) (ih : ℤ×ℤ) :
    transverse b (spatialTranslate b k m ih) =
      (⌊b*(ih.1*(2 : ℤ)^m)⌋ : ℝ)-b*(ih.1*(2 : ℤ)^m)+(ih.2 : ℝ)*(2 : ℝ)^k := by
  simp [spatialTranslate,transverse]
  ring

lemma spatialChunkIndex_horizontal (b : ℝ) (k m : ℕ) (p : Vertex) :
    0 ≤ p.1-(spatialTranslate b k m (spatialChunkIndex b k m p)).1 ∧
      p.1-(spatialTranslate b k m (spatialChunkIndex b k m p)).1 < (2 : ℤ)^m := by
  have h := meshFloor_bounds p.1 ((2 : ℤ)^m) (by positivity)
  dsimp [spatialChunkIndex,spatialTranslate,meshFloor] at *
  omega

lemma spatialChunkIndex_transverse (b : ℝ) (k m : ℕ) (p : Vertex) :
    0 ≤ transverse b p-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p)) ∧
      transverse b p-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p)) < (2 : ℝ)^k+1 := by
  have hs : (0 : ℝ) < 2^k := by positivity
  have hl := (le_div_iff₀ hs).mp (Int.floor_le (transverse b p/(2 : ℝ)^k))
  have hu := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (transverse b p/(2 : ℝ)^k))
  have hf := Int.floor_le (b*((spatialChunkIndex b k m p).1*(2 : ℤ)^m))
  have hf' := Int.lt_floor_add_one (b*((spatialChunkIndex b k m p).1*(2 : ℤ)^m))
  rw [spatialTranslate_center]
  simp only [spatialChunkIndex,Int.cast_ofNat] at hf hf' ⊢
  constructor <;> nlinarith [hf,hf']

lemma spatial_chunk_vertex_in_box (b : ℝ) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k) (p z : Vertex)
    (hx : |z.1-p.1| ≤ 2*(2 : ℤ)^m)
    (hr : |transverse b z-transverse b p| ≤ (2 : ℝ)^k+1) :
    z-spatialTranslate b k m (spatialChunkIndex b k m p) ∈ endpointBox b 4 4 k m := by
  have hpx := spatialChunkIndex_horizontal b k m p
  have hpr := spatialChunkIndex_transverse b k m p
  have hpxR : 0 ≤ (p.1 : ℝ)-((spatialTranslate b k m (spatialChunkIndex b k m p)).1 : ℝ) ∧
      (p.1 : ℝ)-((spatialTranslate b k m (spatialChunkIndex b k m p)).1 : ℝ) < (2 : ℝ)^m := by
    exact_mod_cast hpx
  have hxR : |(z.1 : ℝ)-(p.1 : ℝ)| ≤ 2*(2 : ℝ)^m := by exact_mod_cast hx
  have hzx := abs_le.mp hxR
  have hzr := abs_le.mp hr
  have htrans : transverse b (z-spatialTranslate b k m (spatialChunkIndex b k m p)) =
      transverse b z-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p)) := by
    simp [transverse]; ring
  constructor
  · simp only [Prod.fst_sub,Int.cast_sub]
    apply abs_le.mpr
    constructor <;> linarith [hpxR.1,hpxR.2,pow_pos (by norm_num : (0 : ℝ) < 2) m]
  · rw [htrans]
    apply abs_le.mpr
    constructor <;> linarith [hpr.1,hpr.2]

lemma spatial_chunk_in_box (b : ℝ) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k) (p : Vertex) (ds : List Step)
    (hchunk : ∀ i ≤ ds.length, |(displacement (ds.take i)).1| ≤ 2*(2 : ℤ)^m ∧
      |transverse b (displacement (ds.take i))| ≤ (2 : ℝ)^k+1) :
    PathIn p ds {z | z-spatialTranslate b k m (spatialChunkIndex b k m p) ∈ endpointBox b 4 4 k m} := by
  intro i hi
  apply spatial_chunk_vertex_in_box b k m hs p
  · simpa only [Prod.fst_add,add_sub_cancel_left] using (hchunk i hi).1
  · simpa only [transverse_add,add_sub_cancel_left] using (hchunk i hi).2

lemma spatialChunkIndex_origin (b : ℝ) (k m : ℕ) : spatialChunkIndex b k m 0=0 := by
  simp [spatialChunkIndex,transverse]

lemma spatialChunkIndex_increment (b : ℝ) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k) (p z : Vertex)
    (hx : |z.1-p.1| ≤ 2*(2 : ℤ)^m)
    (hr : |transverse b z-transverse b p| ≤ (2 : ℝ)^k+1) :
    |(spatialChunkIndex b k m z).1-(spatialChunkIndex b k m p).1| ≤ 3 ∧
      |(spatialChunkIndex b k m z).2-(spatialChunkIndex b k m p).2| ≤ 3 := by
  have hL : (0 : ℤ) < 2^m := by positivity
  have hp := meshFloor_bounds p.1 ((2 : ℤ)^m) hL
  have hz := meshFloor_bounds z.1 ((2 : ℤ)^m) hL
  have hx' := abs_le.mp hx
  constructor
  · change |z.1/(2 : ℤ)^m-p.1/(2 : ℤ)^m| ≤ 3
    dsimp [meshFloor] at hp hz
    apply abs_le.mpr
    constructor <;> nlinarith [hp.1,hp.2,hz.1,hz.2]
  · have hs0 : (0 : ℝ) < 2^k := by positivity
    have hp0 := (le_div_iff₀ hs0).mp (Int.floor_le (transverse b p/(2 : ℝ)^k))
    have hp1 := (div_lt_iff₀ hs0).mp (Int.lt_floor_add_one (transverse b p/(2 : ℝ)^k))
    have hz0 := (le_div_iff₀ hs0).mp (Int.floor_le (transverse b z/(2 : ℝ)^k))
    have hz1 := (div_lt_iff₀ hs0).mp (Int.lt_floor_add_one (transverse b z/(2 : ℝ)^k))
    have hr' := abs_le.mp hr
    have hh : |(⌊transverse b z/(2 : ℝ)^k⌋ : ℝ)-(⌊transverse b p/(2 : ℝ)^k⌋ : ℝ)| ≤ 3 := by
      apply abs_le.mpr
      constructor <;> nlinarith [hr'.1,hr'.2]
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [spatialChunkIndex,Int.cast_abs,Int.cast_sub,Int.cast_ofNat] using hh

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialFirstExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

lemma step_transverse_abs_le (b : ℝ) (hb : |b| ≤ 1) (d : Step) : |transverse b d.delta| ≤ 1 := by
  cases d with
  | east => simpa [Step.delta,transverse] using hb
  | west => simpa [Step.delta,transverse] using hb
  | north => norm_num [Step.delta,transverse]
  | south => norm_num [Step.delta,transverse]

lemma chunk_step_localization (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (v : Vertex)
    (hv : chunkInterior b k m v) (d : Step) :
    |(v+d.delta).1| ≤ 2*(2 : ℤ)^m ∧ |transverse b (v+d.delta)| ≤ (2 : ℝ)^k+1 := by
  have hx := abs_lt.mp hv.1
  constructor
  · cases d <;> simp only [Step.delta,Prod.fst_add] <;> apply abs_le.mpr <;> omega
  · rw [transverse_add]
    exact (abs_add_le _ _).trans (by linarith [hv.2,step_transverse_abs_le b hb d])

lemma proper_chunk_endpoint_localization (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (ds : List Step)
    (hproper : ∀ i < ds.length, chunkInterior b k m (displacement (ds.take i))) :
    |(displacement ds).1| ≤ 2*(2 : ℤ)^m ∧ |transverse b (displacement ds)| ≤ (2 : ℝ)^k+1 := by
  induction ds using List.reverseRecOn with
  | nil =>
    constructor
    · change (0 : ℤ) ≤ 2*(2 : ℤ)^m
      positivity
    · simpa [transverse] using (show (0 : ℝ) ≤ (2 : ℝ)^k+1 by positivity)
  | append_singleton ds d _ih =>
    have h := hproper ds.length (by simp)
    have ht : (ds++[d]).take ds.length=ds := by simp
    rw [ht] at h
    simpa [displacement_append,displacement] using chunk_step_localization b hb k m (displacement ds) h d

lemma proper_chunk_localization (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (ds : List Step)
    (hproper : ∀ i < ds.length, chunkInterior b k m (displacement (ds.take i))) :
    ∀ i ≤ ds.length, |(displacement (ds.take i)).1| ≤ 2*(2 : ℤ)^m ∧
      |transverse b (displacement (ds.take i))| ≤ (2 : ℝ)^k+1 := by
  intro i hi
  rcases lt_or_eq_of_le hi with hi | rfl
  · exact ⟨(hproper i hi).1.le,by linarith [(hproper i hi).2]⟩
  · simpa using proper_chunk_endpoint_localization b hb k m ds hproper

lemma fullSpatialChunk_in_box (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (p : Vertex) (ds : List Step) (h : FullSpatialChunk b k m ds) :
    PathIn p ds {z | z-spatialTranslate b k m (spatialChunkIndex b k m p) ∈ endpointBox b 4 4 k m} :=
  spatial_chunk_in_box b k m hs p ds (proper_chunk_localization b hb k m ds h.1)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialChunks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

lemma chunkIndexTail_length (b : ℝ) (k m : ℕ) (p : Vertex) (blocks : List (List Step)) :
    (chunkIndexTail b k m p blocks).length=blocks.length := by
  induction blocks generalizing p with
  | nil => rfl
  | cons q qs ih => simp [chunkIndexTail,ih]

lemma chunkIndexTail_bounded (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (p : Vertex) (blocks : List (List Step))
    (hfull : ∀ q ∈ blocks, FullSpatialChunk b k m q) :
    BoundedIndexSteps (spatialChunkIndex b k m p) (chunkIndexTail b k m p blocks) := by
  induction blocks generalizing p with
  | nil => trivial
  | cons q qs ih =>
    have hq := proper_chunk_endpoint_localization b hb k m q (hfull q (by simp)).1
    have hinc := spatialChunkIndex_increment b k m hs p (p+displacement q)
      (by simpa only [Prod.fst_add,add_sub_cancel_left] using hq.1)
      (by simpa only [transverse_add,add_sub_cancel_left] using hq.2)
    exact ⟨hinc.1,hinc.2,ih _ (fun v hv => hfull v (by simp [hv]))⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialChunkWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

lemma negative_midpoint_spatial_witness (w : Edge → ℝ) (b m₀ am ap K η : ℝ)
    (ha : am ≤ ap) (k m : ℕ) (ih : ℤ×ℤ) (p : Vertex) (ds : List Step)
    (hin : PathIn p ds {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m})
    (hc : defect w b m₀ ((am+ap)/2) p ds < -η*(2 : ℝ)^k) :
    ∃ q ∈ spatialWitnessFamily b m₀ am ap K η k m ih,
      q.start=p ∧ q.steps=ds ∧ q.Good w := by
  have hid := minimum_defect w b m₀ am ap ha p ds
  have hn : 0 ≤ ((ap-am)/2)*|transverse b (displacement ds)| := mul_nonneg (by linarith) (abs_nonneg _)
  have hmin : min (defect w b m₀ ap p ds) (defect w b m₀ am p ds) < -η*(2 : ℝ)^k := by linarith
  rcases min_lt_iff.mp hmin with hp | hm
  · refine ⟨⟨p,ds,support b m₀ ap (displacement ds)-η*(2 : ℝ)^k⟩,
      Or.inl ⟨hin,Or.inr rfl⟩,rfl,rfl,?_⟩
    change pathCost w p ds < _
    unfold defect at hp
    linarith
  · refine ⟨⟨p,ds,support b m₀ am (displacement ds)-η*(2 : ℝ)^k⟩,
      Or.inl ⟨hin,Or.inl rfl⟩,rfl,rfl,?_⟩
    change pathCost w p ds < _
    unfold defect at hm
    linarith

theorem full_chunk_transverse_witness (w : Edge → ℝ) (b m₀ am ap K η : ℝ)
    (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η) (hgap : 4*η ≤ (ap-am)/2)
    (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k) (p : Vertex) (ds : List Step)
    (hfull : FullSpatialChunk b k m ds)
    (htrans : (2 : ℝ)^k ≤ |transverse b (displacement ds)|)
    (hcheap : defect w b m₀ ((am+ap)/2) p ds < η*(2 : ℝ)^k) :
    ∃ q ∈ spatialWitnessFamily b m₀ am ap K η k m (spatialChunkIndex b k m p),
      q.start=p ∧ q.steps=ds ∧ q.Good w := by
  have hin := fullSpatialChunk_in_box b hb k m hs p ds hfull
  have hc := transverse_chunk_witness w b m₀ am ap η ((2 : ℝ)^k) ha (by positivity) hη hgap p ds htrans hcheap
  rcases hc with hp | hm
  · refine ⟨⟨p,ds,support b m₀ ap (displacement ds)-η*(2 : ℝ)^k⟩,
      Or.inl ⟨hin,Or.inr rfl⟩,rfl,rfl,?_⟩
    change pathCost w p ds < _
    unfold defect at hp
    linarith
  · refine ⟨⟨p,ds,support b m₀ am (displacement ds)-η*(2 : ℝ)^k⟩,
      Or.inl ⟨hin,Or.inl rfl⟩,rfl,rfl,?_⟩
    change pathCost w p ds < _
    unfold defect at hm
    linarith

lemma negative_longitudinal_chunk_not_cheap (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ a η : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (p : Vertex) (ds : List Step)
    (hfull : FullSpatialChunk b k m ds)
    (hx : (displacement ds).1= -2*(2 : ℤ)^m)
    (hscale : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|a| *((2 : ℝ)^k+1)) :
    η*(2 : ℝ)^k < defect w b m₀ a p ds := by
  have hr := (proper_chunk_endpoint_localization b hb k m ds hfull.1).2
  have hc := pathCost_nonneg hw p ds
  have hmul := mul_le_mul_of_nonneg_left hr (abs_nonneg a)
  have hab := le_abs_self (a*transverse b (displacement ds))
  rw [abs_mul] at hab
  unfold defect support
  rw [hx]
  push_cast
  nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialCrossingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

lemma spatialChunkIndex_transverse_column (b : ℝ) (k m : ℕ) (p : Vertex) (i : ℤ) :
    0 ≤ transverse b p-transverse b (spatialTranslate b k m (i,(spatialChunkIndex b k m p).2)) ∧
      transverse b p-transverse b (spatialTranslate b k m (i,(spatialChunkIndex b k m p).2)) < (2 : ℝ)^k+1 := by
  have hs : (0 : ℝ) < 2^k := by positivity
  have hl := (le_div_iff₀ hs).mp (Int.floor_le (transverse b p/(2 : ℝ)^k))
  have hu := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (transverse b p/(2 : ℝ)^k))
  have hf := Int.floor_le (b*(i*(2 : ℤ)^m))
  have hf' := Int.lt_floor_add_one (b*(i*(2 : ℤ)^m))
  rw [spatialTranslate_center]
  simp only [spatialChunkIndex,Int.cast_ofNat] at hf hf' ⊢
  constructor <;> nlinarith [hf,hf']

lemma chunk_subcrossing_region (b : ℝ) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (p z : Vertex)
    (hx : ((spatialChunkIndex b k m p).1+1)*(2 : ℤ)^m ≤ z.1 ∧
      z.1 ≤ ((spatialChunkIndex b k m p).1+2)*(2 : ℤ)^m)
    (hr : |transverse b z-transverse b p| ≤ (2 : ℝ)^k+1) :
    z ∈ rareFastRegion b 1 8 ((2 : ℝ)^k) ((2 : ℤ)^m)
      (spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) := by
  have hcenter := spatialChunkIndex_transverse_column b k m p ((spatialChunkIndex b k m p).1+1)
  have ht : transverse b (z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) =
      transverse b z-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) := by
    simp [transverse]; ring
  have hx' : 0 ≤ (z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 ∧
      (z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 ≤ (2 : ℤ)^m := by
    simp only [spatialTranslate,Prod.fst_add,Prod.fst_sub]
    constructor <;> nlinarith [hx.1,hx.2]
  have hxR : 0 ≤ ((z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 : ℝ) ∧
      ((z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 : ℝ) ≤ (2 : ℝ)^m := by exact_mod_cast hx'
  refine ⟨by simpa using (show -(2 : ℝ)^m ≤ ((z-spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))).1 : ℝ) by linarith [pow_pos (by norm_num : (0 : ℝ)<2) m]),?_,?_⟩
  · push_cast
    nlinarith [hxR.2,pow_pos (by norm_num : (0 : ℝ)<2) m]
  · rw [ht]
    have hcenter' : 0 ≤ transverse b p-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) ∧
        transverse b p-transverse b (spatialTranslate b k m (spatialChunkIndex b k m p+(1,0))) < (2 : ℝ)^k+1 := by
      have he : spatialChunkIndex b k m p+(1,0)=((spatialChunkIndex b k m p).1+1,(spatialChunkIndex b k m p).2) := by ext <;> simp
      rw [he]
      exact hcenter
    have hz := abs_le.mp hr
    apply abs_le.mpr
    constructor <;> nlinarith [hcenter'.1,hcenter'.2]

lemma pathEdges_append (p : Vertex) (ds es : List Step) :
    pathEdges p (ds++es)=pathEdges p ds ∪ pathEdges (p+displacement ds) es := by
  induction ds generalizing p with
  | nil => simp [pathEdges]
  | cons d ds ih => simp [pathEdges,ih,displacement_cons,add_assoc,Finset.insert_union]

lemma pathEdges_middle_subset (p : Vertex) (pre mid post : List Step) :
    pathEdges (p+displacement pre) mid ⊆ pathEdges p (pre++mid++post) := by
  rw [pathEdges_append,pathEdges_append]
  exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialPositiveChunk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

theorem positive_longitudinal_chunk_witness (w : Edge → ℝ) (b m₀ am ap K η : ℝ)
    (hb : |b| ≤ 1) (ha : am ≤ ap) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hscale : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (p : Vertex) (ds : List Step) (hfull : FullSpatialChunk b k m ds)
    (hx : (displacement ds).1=2*(2 : ℤ)^m)
    (hcheap : defect w b m₀ ((am+ap)/2) p ds < η*(2 : ℝ)^k) :
    ∃ q ∈ spatialWitnessFamily b m₀ am ap K η k m (spatialChunkIndex b k m p),
      q.Good w ∧ q.edges ⊆ pathEdges p ds := by
  let ih := spatialChunkIndex b k m p
  let L : ℤ := (2 : ℤ)^m
  let A := (ih.1+1)*L
  let B := (ih.1+2)*L
  have hL : 0 < L := by dsimp [L]; positivity
  have hi := meshFloor_bounds p.1 L hL
  have hidx : ih.1=p.1/L := rfl
  have hpA : p.1 ≤ A := by dsimp [A]; rw [hidx]; dsimp [meshFloor] at hi; nlinarith [hi.2]
  have hAB : A ≤ B := by dsimp [A,B]; nlinarith
  have hend : B ≤ (p+displacement ds).1 := by
    dsimp [B]
    rw [hidx]
    simp only [hx]
    dsimp [meshFloor] at hi
    change p.1/L*L ≤ p.1 ∧ _ at hi
    dsimp [L] at *
    nlinarith [hi.1]
  obtain ⟨pre,mid,post,heq,hpre,hmid,hincols⟩ := path_column_subcrossing p ds A B hpA hAB hend
  let box : Set Vertex := {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m}
  have hin : PathIn p (pre++mid++post) box := by
    rw [← heq]
    exact fullSpatialChunk_in_box b hb k m hs p ds hfull
  have hprebox : PathIn p pre box :=
    pathIn_append_left p pre mid box (pathIn_append_left p (pre++mid) post box hin)
  have hpostbox := pathIn_append_right p (pre++mid) post box hin
  by_cases hnegPre : defect w b m₀ ((am+ap)/2) p pre < -η*(2 : ℝ)^k
  · obtain ⟨q,hq,hqs,hqd,hgood⟩ := negative_midpoint_spatial_witness w b m₀ am ap K η ha k m ih p pre hprebox hnegPre
    refine ⟨q,hq,hgood,?_⟩
    change pathEdges q.start q.steps ⊆ pathEdges p ds
    rw [hqs,hqd,heq,pathEdges_append,pathEdges_append]
    exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  · by_cases hnegPost : defect w b m₀ ((am+ap)/2) (p+displacement (pre++mid)) post < -η*(2 : ℝ)^k
    · obtain ⟨q,hq,hqs,hqd,hgood⟩ := negative_midpoint_spatial_witness w b m₀ am ap K η ha k m ih
        (p+displacement (pre++mid)) post hpostbox hnegPost
      refine ⟨q,hq,hgood,?_⟩
      change pathEdges q.start q.steps ⊆ pathEdges p ds
      rw [hqs,hqd,heq,pathEdges_append]
      exact Finset.subset_union_right
    · have hprelo := le_of_not_gt hnegPre
      have hpostlo := le_of_not_gt hnegPost
      have hsum := hcheap
      rw [heq,defect_append,defect_append] at hsum
      have hmidcheap : defect w b m₀ ((am+ap)/2) (p+displacement pre) mid < 3*η*(2 : ℝ)^k := by linarith
      have hrloc : PathIn p (pre++mid++post) {z | |transverse b z-transverse b p| ≤ (2 : ℝ)^k+1} := by
        rw [← heq]
        intro i hi'
        simpa only [mem_ofPred_eq,transverse_add,add_sub_cancel_left] using
          (proper_chunk_localization b hb k m ds hfull.1 i hi').2
      have hrmid := pathIn_middle p pre mid post _ hrloc
      have hrstart : |transverse b (p+displacement pre)-transverse b p| ≤ (2 : ℝ)^k+1 := by
        simpa using hrmid 0 (by omega)
      have hrend := pathIn_endpoint _ _ _ hrmid
      change |transverse b (p+displacement pre+displacement mid)-transverse b p| ≤ (2 : ℝ)^k+1 at hrend
      have hrd : |transverse b (displacement mid)| ≤ 2*((2 : ℝ)^k+1) := by
        have hh := abs_sub (transverse b (p+displacement pre+displacement mid)-transverse b p)
          (transverse b (p+displacement pre)-transverse b p)
        simp only [transverse_add] at hh hrend
        have he : transverse b p+transverse b (displacement pre)+transverse b (displacement mid)-transverse b p-
            (transverse b p+transverse b (displacement pre)-transverse b p)=transverse b (displacement mid) := by ring
        rw [he] at hh
        simp only [transverse_add] at hrstart
        linarith
      have hdx : (displacement mid).1=L := by
        simp only [Prod.fst_add] at hmid
        dsimp [A,B] at hpre hmid
        nlinarith
      have hac := mul_le_mul_of_nonneg_left hrd (abs_nonneg ((am+ap)/2))
      have haa := le_abs_self (((am+ap)/2)*transverse b (displacement mid))
      rw [abs_mul] at haa
      have hcost : pathCost w (p+displacement pre) mid < m₀*(L : ℝ)+K*(2 : ℝ)^k := by
        unfold defect support at hmidcheap
        rw [hdx] at hmidcheap
        nlinarith
      let q : StrictPathWitness := ⟨p+displacement pre,mid,m₀*(L : ℝ)+K*(2 : ℝ)^k⟩
      refine ⟨q,Or.inr ⟨?_,?_,?_,?_⟩,hcost,?_⟩
      · change (p+displacement pre).1=(spatialTranslate b k m (ih+(1,0))).1
        simpa [A,spatialTranslate,L] using hpre
      · change (p+displacement pre+displacement mid).1=(spatialTranslate b k m (ih+(1,0))).1+(2 : ℤ)^m
        rw [hmid]
        dsimp [B,spatialTranslate,L]
        ring
      · intro i hi'
        exact chunk_subcrossing_region b k m hs p _ (hincols i hi') (hrmid i hi')
      · change m₀*(L : ℝ)+K*(2 : ℝ)^k=m₀*(2 : ℤ)^m+K*(2 : ℝ)^k
        simp [L]
      · change pathEdges (p+displacement pre) mid ⊆ pathEdges p ds
        rw [heq]
        exact pathEdges_middle_subset p pre mid post

theorem cheap_full_spatial_chunk_witness (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (p : Vertex) (ds : List Step) (hfull : FullSpatialChunk b k m ds)
    (hcheap : defect w b m₀ ((am+ap)/2) p ds < η*(2 : ℝ)^k) :
    ∃ q ∈ spatialWitnessFamily b m₀ am ap K η k m (spatialChunkIndex b k m p),
      q.Good w ∧ q.edges ⊆ pathEdges p ds := by
  by_cases hr : (2 : ℝ)^k ≤ |transverse b (displacement ds)|
  · obtain ⟨q,hq,hs',hd',hg⟩ := full_chunk_transverse_witness w b m₀ am ap K η hb ha hη hgap k m hs p ds hfull hr hcheap
    refine ⟨q,hq,hg,?_⟩
    change pathEdges q.start q.steps ⊆ pathEdges p ds
    rw [hs',hd']
  · have hl := (proper_chunk_endpoint_localization b hb k m ds hfull.1).1
    have hx : 2*(2 : ℤ)^m ≤ |(displacement ds).1| := by
      by_contra hh
      exact hfull.2 ⟨lt_of_not_ge hh,lt_of_not_ge hr⟩
    have heq : |(displacement ds).1|=2*(2 : ℤ)^m := le_antisymm hl hx
    rcases eq_or_eq_neg_of_abs_eq heq with hx | hx
    · exact positive_longitudinal_chunk_witness w b m₀ am ap K η hb ha k m hs hscale₂ p ds hfull hx hcheap
    · have hh := negative_longitudinal_chunk_not_cheap w hw b m₀ ((am+ap)/2) η hb k m p ds hfull
        (by simpa using hx) hscale₁
      linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ContiguousWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

lemma trace_append (p : Vertex) (ds es : List Step) :
    trace p (ds++es)=trace p ds++trace (p+displacement ds) es := by
  induction ds generalizing p with
  | nil => simp [trace]
  | cons d ds ih => simp [trace,ih,add_assoc]

lemma trace_split (p : Vertex) (ds : List Step) (xs ys : List Traversal)
    (h : trace p ds=xs++ys) :
    ∃ pre rest : List Step, ds=pre++rest ∧ trace p pre=xs ∧
      trace (p+displacement pre) rest=ys := by
  induction xs generalizing p ds with
  | nil => exact ⟨[],ds,rfl,rfl,by simpa using h⟩
  | cons x xs ih =>
    cases ds with
    | nil => simp [trace] at h
    | cons d ds =>
      obtain ⟨hx,ht⟩ := List.cons.inj h
      obtain ⟨pre,rest,he,hpre,hrest⟩ := ih (p+d.delta) ds ht
      refine ⟨d::pre,rest,by simp [he],?_,?_⟩
      · simp only [trace,hpre,hx]
      · simpa only [displacement_cons,add_assoc] using hrest

lemma trace_edges (p : Vertex) (ds : List Step) :
    ((trace p ds).map traversalEdge).toFinset=pathEdges p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [trace,traversalEdge,pathEdges,ih]

lemma simple_append_edges (p : Vertex) (ds es : List Step)
    (h : ((trace p (ds++es)).map traversalEdge).Nodup) :
    ((trace p ds).map traversalEdge).Nodup ∧
    ((trace (p+displacement ds) es).map traversalEdge).Nodup ∧
    Disjoint (pathEdges p ds) (pathEdges (p+displacement ds) es) := by
  rw [trace_append,List.map_append,List.nodup_append] at h
  refine ⟨h.1,h.2.1,?_⟩
  rw [← trace_edges,← trace_edges]
  exact Finset.disjoint_left.mpr (fun e he hf =>
    h.2.2 e (List.mem_toFinset.mp he) e (List.mem_toFinset.mp hf) rfl)

theorem spatial_negative_prefix_witnesses (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (ha : am ≤ ap) (hη : 0 ≤ η)
    (k m : ℕ) (ih : ℤ×ℤ)
    (hscale : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (p : Vertex) (ds : List Step)
    (hin : PathIn p ds {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m})
    (hsimple : ((trace p ds).map traversalEdge).Nodup) :
    ∃ ws : List StrictPathWitness,
      ws.Pairwise (fun q r => Disjoint q.edges r.edges) ∧
      (∀ q ∈ ws, q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧
        q.Good w ∧ q.edges ⊆ pathEdges p ds) ∧
      -η*(2 : ℝ)^k-2*η*(2 : ℝ)^k*ws.length ≤ defect w b m₀ ((am+ap)/2) p ds := by
  have hηs : 0 ≤ η*(2 : ℝ)^k := mul_nonneg hη (by positivity)
  induction hn : ds.length using Nat.strong_induction_on generalizing p ds with
  | h n rec =>
    by_cases hlo : -η*(2 : ℝ)^k ≤ defect w b m₀ ((am+ap)/2) p ds
    · exact ⟨[],by simp,by simp,by simpa using hlo⟩
    · have hstep : ∀ t ∈ trace p ds, -(η*(2 : ℝ)^k) ≤ stepDefect w b m₀ ((am+ap)/2) t := by
        intro t _
        have ht := hw (traversalEdge t)
        have hs := (support_step_bound b m₀ ((am+ap)/2) t.2).trans hscale
        unfold stepDefect
        linarith
      obtain ⟨xs,ys,he,hne,hxslo,hxshi⟩ := first_drop (stepDefect w b m₀ ((am+ap)/2))
        (η*(2 : ℝ)^k) (trace p ds) hstep 0 (by linarith)
        (by rw [trace_total_defect]; linarith)
      obtain ⟨pre,rest,heq,hpre,hrest⟩ := trace_split p ds xs ys he
      have hpreNe : pre ≠ [] := by intro hz; subst pre; simp [trace] at hpre; exact hne hpre
      have hlen : rest.length < n := by
        have hh := List.length_pos_iff.mpr hpreNe
        rw [heq,List.length_append] at hn
        omega
      have hsimp := simple_append_edges p pre rest (by rw [← heq]; exact hsimple)
      have hin' : PathIn p (pre++rest) {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m} := by rw [← heq]; exact hin
      have hprelo : -2*(η*(2 : ℝ)^k) ≤ defect w b m₀ ((am+ap)/2) p pre := by
        rw [← trace_total_defect,hpre]; simpa using hxslo
      have hprehi : defect w b m₀ ((am+ap)/2) p pre < -η*(2 : ℝ)^k := by
        rw [← trace_total_defect,hpre]; simpa [neg_mul] using hxshi
      obtain ⟨q,hq,hqs,hqd,hqg⟩ := negative_midpoint_spatial_witness w b m₀ am ap K η ha k m ih p pre
        (pathIn_append_left p pre rest _ hin') hprehi
      have hqe : q.edges=pathEdges p pre := by change pathEdges q.start q.steps=_; rw [hqs,hqd]
      obtain ⟨ws,hpair,hws,hbound⟩ := rec rest.length hlen (p+displacement pre) rest
        (pathIn_append_right p pre rest _ hin') hsimp.2.1 rfl
      refine ⟨q::ws,List.pairwise_cons.mpr ⟨?_,hpair⟩,?_,?_⟩
      · intro r hr
        rw [hqe]
        exact hsimp.2.2.mono_right (hws r hr).2.2
      · intro r hr
        rw [heq,pathEdges_append]
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨hq,hqg,by rw [hqe]; exact Finset.subset_union_left⟩
        · exact ⟨(hws r hr).1,(hws r hr).2.1,(hws r hr).2.2.trans Finset.subset_union_right⟩
      · rw [heq,defect_append]
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialWitnessCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

theorem spatial_full_chunk_witnesses (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (p : Vertex) (ds : List Step) (hfull : FullSpatialChunk b k m ds)
    (hsimple : ((trace p ds).map traversalEdge).Nodup) :
    ∃ ws : List StrictPathWitness,
      ws.Pairwise (fun q r => Disjoint q.edges r.edges) ∧
      (∀ q ∈ ws, q ∈ spatialWitnessFamily b m₀ am ap K η k m (spatialChunkIndex b k m p) ∧
        q.Good w ∧ q.edges ⊆ pathEdges p ds) ∧
      η*(2 : ℝ)^k-4*η*(2 : ℝ)^k*ws.length ≤ defect w b m₀ ((am+ap)/2) p ds := by
  have hηs : 0 ≤ η*(2 : ℝ)^k := by positivity
  obtain ⟨ws,hpair,hws,hbasic⟩ := spatial_negative_prefix_witnesses w hw b m₀ am ap K η ha hη.le k m
    (spatialChunkIndex b k m p) hstep p ds (fullSpatialChunk_in_box b hb k m hs p ds hfull) hsimple
  by_cases hempty : ws=[]
  · subst ws
    simp only [List.length_nil,Nat.cast_zero,mul_zero,sub_zero] at hbasic
    by_cases hcheap : defect w b m₀ ((am+ap)/2) p ds < η*(2 : ℝ)^k
    · obtain ⟨q,hq,hg,he⟩ := cheap_full_spatial_chunk_witness w hw b m₀ am ap K η hb ha hη hgap
        k m hs hscale₁ hscale₂ p ds hfull hcheap
      refine ⟨[q],by simp,?_,?_⟩
      · intro r hr
        have heq : r=q := List.mem_singleton.mp hr
        subst r
        exact ⟨hq,hg,he⟩
      · simp only [List.length_singleton,Nat.cast_one,mul_one]
        linarith
    · exact ⟨[],by simp,by simp,by simpa using le_of_not_gt hcheap⟩
  · have hlen : (1 : ℝ) ≤ ws.length := by exact_mod_cast List.length_pos_iff.mpr hempty
    refine ⟨ws,hpair,hws,?_⟩
    nlinarith [mul_le_mul_of_nonneg_left hlen hηs]

theorem spatial_total_witnesses (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (p : Vertex) (blocks : List (List Step)) (rest : List Step)
    (hfull : ∀ q ∈ blocks, FullSpatialChunk b k m q)
    (hrest : ∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i)))
    (hsimple : ((trace p (blocks.flatten++rest)).map traversalEdge).Nodup) :
    ∃ packs : List (List StrictPathWitness),
      packs.length=blocks.length+1 ∧
      List.Forall₂ (fun ws ih => ∀ q ∈ ws,
        q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w)
        packs (spatialChunkIndex b k m p :: chunkIndexTail b k m p blocks) ∧
      packs.flatten.Pairwise (fun q r => Disjoint q.edges r.edges) ∧
      (∀ q ∈ packs.flatten, q.edges ⊆ pathEdges p (blocks.flatten++rest)) ∧
      ((blocks.length : ℝ)-1)*η*(2 : ℝ)^k-4*η*(2 : ℝ)^k*packs.flatten.length ≤
        defect w b m₀ ((am+ap)/2) p (blocks.flatten++rest) := by
  have hηs : 0 ≤ η*(2 : ℝ)^k := by positivity
  induction blocks generalizing p with
  | nil =>
    have hin := spatial_chunk_in_box b k m hs p rest
      (proper_chunk_localization b hb k m rest (fun i hi => hrest i hi.le))
    obtain ⟨ws,hpair,hws,hbound⟩ := spatial_negative_prefix_witnesses w hw b m₀ am ap K η ha hη.le k m
      (spatialChunkIndex b k m p) hstep p rest hin (by simpa using hsimple)
    refine ⟨[ws],rfl,?_,by simpa using hpair,?_,?_⟩
    · exact List.Forall₂.cons (fun q hq => ⟨(hws q hq).1,(hws q hq).2.1⟩) List.Forall₂.nil
    · simpa using (fun q hq => (hws q hq).2.2)
    · simp only [List.length_nil,Nat.cast_zero,zero_sub,neg_mul,one_mul,List.flatten_singleton,List.flatten_nil,List.nil_append]
      nlinarith [mul_nonneg hηs (show (0 : ℝ) ≤ ws.length by positivity)]
  | cons ds blocks rec =>
    have hsim : ((trace p (ds++(blocks.flatten++rest))).map traversalEdge).Nodup := by
      simpa only [List.flatten_cons,List.append_assoc] using hsimple
    have hsplit := simple_append_edges p ds (blocks.flatten++rest) hsim
    obtain ⟨ws,hpair,hws,hbound⟩ := spatial_full_chunk_witnesses w hw b m₀ am ap K η hb ha hη hgap k m hs
      hstep hscale₁ hscale₂ p ds (hfull ds (by simp)) hsplit.1
    obtain ⟨packs,hlen,hassign,hdisj,hedges,htotal⟩ := rec (p+displacement ds)
      (fun q hq => hfull q (by simp [hq])) hsplit.2.1
    refine ⟨ws::packs,by simp [hlen],List.Forall₂.cons ?_ hassign,?_,?_,?_⟩
    · exact fun q hq => ⟨(hws q hq).1,(hws q hq).2.1⟩
    · simp only [List.flatten_cons,List.pairwise_append]
      refine ⟨hpair,hdisj,?_⟩
      intro q hq r hr
      exact hsplit.2.2.mono (hws q hq).2.2 (hedges r hr)
    · intro q hq
      simp only [List.flatten_cons,List.mem_append] at hq
      simp only [List.flatten_cons,List.append_assoc]
      rw [pathEdges_append]
      rcases hq with hq | hq
      · exact (hws q hq).2.2.trans Finset.subset_union_left
      · exact (hedges q hq).trans Finset.subset_union_right
    · simp only [List.flatten_cons,List.append_assoc,List.length_cons,List.length_append,
        Nat.cast_add,Nat.cast_one]
      rw [defect_append]
      linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_WitnessSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

lemma takeWitnessPacks_length {α : Type*} (t : ℕ) (packs : List (List α)) :
    (takeWitnessPacks t packs).length=packs.length := by
  induction packs generalizing t with
  | nil => rfl
  | cons ws packs ih => simp [takeWitnessPacks,ih]

lemma takeWitnessPacks_flatten {α : Type*} (t : ℕ) (packs : List (List α)) :
    (takeWitnessPacks t packs).flatten=packs.flatten.take t := by
  induction packs generalizing t with
  | nil => simp [takeWitnessPacks]
  | cons ws packs ih => simp [takeWitnessPacks,ih,List.take_append]

lemma takeWitnessPacks_assign {α β : Type*} (R : α → β → Prop) (t : ℕ)
    (packs : List (List α)) (is : List β)
    (h : List.Forall₂ (fun ws i => ∀ q ∈ ws, R q i) packs is) :
    List.Forall₂ (fun ws i => ∀ q ∈ ws, R q i) (takeWitnessPacks t packs) is := by
  induction h generalizing t with
  | nil => exact List.Forall₂.nil
  | @cons ws i packs is hws htail ih =>
    exact List.Forall₂.cons (fun q hq => hws q (List.mem_of_mem_take hq)) (ih _)

lemma long_path_witness_count (H a : ℝ) (ha : 0 < a) (N M : ℕ) (hN : 4 ≤ N)
    (hlower : ((N : ℝ)-1)*a-4*a*M ≤ H) (hcheap : H < N*a/2) :
    N/16 ≤ M := by
  have hM : (N : ℝ)/8-1/4 < M := by nlinarith
  have hdiv : ((N/16 : ℕ) : ℝ)*16 ≤ N := by exact_mod_cast Nat.div_mul_le_self N 16
  have hN' : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : ((N/16 : ℕ) : ℝ) ≤ M := by linarith
  exact_mod_cast hh

lemma witnessLabels_length (ns : List ℕ) (is : List (ℤ×ℤ)) (h : ns.length=is.length) :
    (witnessLabels ns is).length=ns.sum := by
  induction ns generalizing is with
  | nil => simp [witnessLabels]
  | cons n ns ih =>
    cases is with
    | nil => simp at h
    | cons i is => simp [witnessLabels,ih is (by simpa using h)]

theorem witnessPacks_strictDisjoint (w : Edge → ℝ) (b m₀ am ap K η : ℝ) (k m : ℕ)
    (packs : List (List StrictPathWitness)) (is : List (ℤ×ℤ))
    (hassign : List.Forall₂ (fun ws ih => ∀ q ∈ ws,
      q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w) packs is)
    (hpair : packs.flatten.Pairwise (fun q r => Disjoint q.edges r.edges)) :
    StrictDisjointPaths (spatialListSupport b k m (witnessLabels (packs.map List.length) is))
      ((witnessLabels (packs.map List.length) is).map (spatialWitnessFamily b m₀ am ap K η k m)) w := by
  let labels := witnessLabels (packs.map List.length) is
  have hlabels : List.Forall₂ (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w)
      packs.flatten labels := by
    clear hpair
    induction hassign with
    | nil => exact List.Forall₂.nil
    | @cons ws i packs is hws htail ih =>
      change List.Forall₂ _ (ws++packs.flatten) ((List.replicate ws.length i)++_)
      induction ws with
      | nil => exact ih
      | cons q qs ih =>
        exact List.Forall₂.cons (hws q (by simp)) (ih (fun r hr => hws r (by simp [hr])))
  refine ⟨packs.flatten,?_,hpair⟩
  have hsupp (ih : ℤ×ℤ) (hi : ih ∈ labels) : spatialWitnessSupport b k m ih ⊆ spatialListSupport b k m labels := by
    intro e he
    exact Finset.mem_biUnion.mpr ⟨ih,List.mem_toFinset.mpr hi,he⟩
  have hall : List.Forall₂ (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧
      q.edges ⊆ spatialListSupport b k m labels ∧ q.Good w) packs.flatten labels := by
    have enrich (ps : List StrictPathWitness) (js : List (ℤ×ℤ))
        (hh : List.Forall₂ (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w) ps js)
        (hsub : ∀ i ∈ js, i ∈ labels) :
        List.Forall₂ (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧
          q.edges ⊆ spatialListSupport b k m labels ∧ q.Good w) ps js := by
      induction hh with
      | nil => exact List.Forall₂.nil
      | @cons q i ps js hq ht rec =>
        exact List.Forall₂.cons
          ⟨hq.1,(spatialWitness_edges b m₀ am ap K η k m i q hq.1).trans (hsupp i (hsub i (by simp))),hq.2⟩
          (rec (fun j hj => hsub j (by simp [hj])))
    exact enrich _ _ hlabels (fun _ hi => hi)
  exact List.forall₂_map_right_iff.mpr hall

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_WitnessEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

lemma spatialNeighbors_card (i : ℤ×ℤ) : (spatialNeighbors i).card ≤ 49 := by
  apply (card_image_le).trans
  norm_num [card_product,Int.card_Icc,Int.toNat]

lemma mem_spatialNeighbors (i j : ℤ×ℤ) (h₁ : |j.1-i.1| ≤ 3) (h₂ : |j.2-i.2| ≤ 3) :
    j ∈ spatialNeighbors i := by
  apply mem_image.mpr
  refine ⟨j-i,?_,by abel⟩
  exact mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp h₁),mem_Icc.mpr (abs_le.mp h₂)⟩

lemma spatialItineraries_card (i : ℤ×ℤ) (n : ℕ) : (spatialItineraries i n).card ≤ 49^n := by
  induction n generalizing i with
  | zero => simp [spatialItineraries]
  | succ n ih =>
    calc
      _ ≤ ∑ j ∈ spatialNeighbors i, ((spatialItineraries j n).image (List.cons j)).card := card_biUnion_le
      _ ≤ ∑ _j ∈ spatialNeighbors i, 49^n := sum_le_sum (fun j _ => card_image_le.trans (ih j))
      _ = (spatialNeighbors i).card * 49^n := by simp
      _ ≤ 49*49^n := Nat.mul_le_mul_right _ (spatialNeighbors_card i)
      _ = _ := by rw [pow_succ]; omega

lemma mem_spatialItineraries (i : ℤ×ℤ) (is : List (ℤ×ℤ)) (h : BoundedIndexSteps i is) :
    is ∈ spatialItineraries i is.length := by
  induction is generalizing i with
  | nil => simp [spatialItineraries]
  | cons j js ih =>
    change j::js ∈ (spatialNeighbors i).biUnion (fun j => (spatialItineraries j js.length).image (List.cons j))
    change |j.1-i.1| ≤ 3 ∧ |j.2-i.2| ≤ 3 ∧ BoundedIndexSteps j js at h
    have hj : j ∈ spatialNeighbors i := mem_spatialNeighbors i j h.1 h.2.1
    have ht : js ∈ spatialItineraries j js.length := ih j h.2.2
    simp only [mem_biUnion,mem_image]
    exact ⟨j,hj,js,ht,rfl⟩

lemma compositionCandidates_card (n t : ℕ) : (compositionCandidates n t).card ≤ 2^(n+t) := by
  induction n generalizing t with
  | zero => simp only [compositionCandidates,card_singleton,Nat.zero_add]; exact Nat.one_le_pow _ _ (by omega)
  | succ n ih =>
    induction t with
    | zero => simp only [compositionCandidates,card_singleton,Nat.add_zero]; exact Nat.one_le_pow _ _ (by omega)
    | succ t ht =>
      rw [compositionCandidates]
      calc
        _ ≤ ((compositionCandidates n (t+1)).image (List.cons 0)).card+
            ((compositionCandidates (n+1) t).image increaseFirst).card := card_union_le ..
        _ ≤ 2^(n+(t+1))+2^(n+1+t) := Nat.add_le_add (card_image_le.trans (ih _)) (card_image_le.trans ht)
        _ = 2^(n+1+(t+1)) := by rw [show n+(t+1)=n+1+t by omega,show n+1+(t+1)=(n+1+t)+1 by omega,pow_succ]; omega

lemma mem_compositionCandidates (n t : ℕ) (ns : List ℕ) (hlen : ns.length=n+1) (hsum : ns.sum=t) :
    ns ∈ compositionCandidates n t := by
  induction n generalizing t ns with
  | zero =>
    cases ns with
    | nil => simp at hlen
    | cons a ns =>
      have he : ns=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst ns
      have ha : a=t := by simpa using hsum
      simp [compositionCandidates,ha]
  | succ n ih =>
    induction t generalizing ns with
    | zero =>
      have hz : ns=List.replicate (n+2) 0 := by
        have zeros (ls : List ℕ) (hh : ls.sum=0) : ls=List.replicate ls.length 0 := by
          induction ls with
          | nil => rfl
          | cons a ls rec =>
            simp only [List.sum_cons] at hh
            have ha : a=0 := by omega
            have ht : ls.sum=0 := by omega
            simp only [List.length_cons,List.replicate_succ]
            exact congrArg₂ List.cons ha (rec ht)
        have he := zeros ns hsum
        simpa [hlen] using he
      simp [compositionCandidates,hz]
    | succ t ht =>
      cases ns with
      | nil => simp at hlen
      | cons a ns =>
        have hlen' : ns.length=n+1 := by simpa using hlen
        cases a with
        | zero =>
          rw [compositionCandidates]
          apply mem_union_left
          exact mem_image.mpr ⟨ns,ih (t+1) ns hlen' (by simpa using hsum),rfl⟩
        | succ a =>
          rw [compositionCandidates]
          apply mem_union_right
          exact mem_image.mpr ⟨a::ns,ht (a::ns) (by simpa using hlen) (by simp only [List.sum_cons] at hsum ⊢; omega),rfl⟩

lemma mem_compositionCover (n t : ℕ) (ns : List ℕ) :
    ns ∈ compositionCover n t ↔ ns.length=n+1 ∧ ns.sum=t := by
  simp only [compositionCover,mem_filter]
  exact ⟨fun h => h.2,fun h => ⟨mem_compositionCandidates n t ns h.1 h.2,h⟩⟩

lemma compositionCover_card (n t : ℕ) (ht : t ≤ n) : (compositionCover n t).card ≤ 4^n := by
  calc
    _ ≤ 2^(n+t) := (card_filter_le ..).trans (compositionCandidates_card n t)
    _ ≤ 2^(n+n) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 4^n := by rw [pow_add,← mul_pow]; norm_num

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialBadPathCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

theorem spatial_bad_path_cover (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ am ap K η : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (N : ℕ) (hN : 4 ≤ N) (hbad : SpatialBadPath w b m₀ ((am+ap)/2) η k m N) :
    ∃ is ∈ spatialItineraries 0 N, ∃ ns ∈ compositionCover N (N/16),
      (0::is).length=ns.length ∧
      StrictDisjointPaths (spatialListSupport b k m (witnessLabels ns (0::is)))
        ((witnessLabels ns (0::is)).map (spatialWitnessFamily b m₀ am ap K η k m)) w := by
  obtain ⟨blocks,rest,hlen,hfull,hrest,hsimple,hcheap⟩ := hbad
  obtain ⟨packs,hplen,hassign,hpair,hedges,hlower⟩ := spatial_total_witnesses w hw b m₀ am ap K η hb ha hη
    hgap k m hs hstep hscale₁ hscale₂ 0 blocks rest hfull hrest hsimple
  have hcount : N/16 ≤ packs.flatten.length :=
    long_path_witness_count (defect w b m₀ ((am+ap)/2) 0 (blocks.flatten++rest)) (η*(2 : ℝ)^k) (by positivity) N _ hN
      (by rw [hlen] at hlower; nlinarith [hlower]) (by nlinarith [hcheap])
  let selected := takeWitnessPacks (N/16) packs
  let ns := selected.map List.length
  let is := chunkIndexTail b k m 0 blocks
  have hilen : is.length=N := by dsimp [is]; rw [chunkIndexTail_length,hlen]
  have his : is ∈ spatialItineraries 0 N := by
    have hh := mem_spatialItineraries (spatialChunkIndex b k m 0) is (chunkIndexTail_bounded b hb k m hs 0 blocks hfull)
    simpa only [spatialChunkIndex_origin,hilen] using hh
  have hnlen : ns.length=N+1 := by simp [ns,selected,takeWitnessPacks_length,hplen,hlen]
  have hnflat : selected.flatten=packs.flatten.take (N/16) := takeWitnessPacks_flatten ..
  have hnsum : ns.sum=N/16 := by
    change (selected.map List.length).sum=_
    rw [← List.length_flatten,hnflat,List.length_take,Nat.min_eq_left hcount]
  have hselected := takeWitnessPacks_assign
    (fun q ih => q ∈ spatialWitnessFamily b m₀ am ap K η k m ih ∧ q.Good w) (N/16) packs _ hassign
  have hselectedPair : selected.flatten.Pairwise (fun q r => Disjoint q.edges r.edges) := by
    rw [hnflat]
    exact hpair.sublist (List.take_sublist ..)
  refine ⟨is,his,ns,(mem_compositionCover ..).mpr ⟨hnlen,hnsum⟩,by simp [hilen,hnlen],?_⟩
  have hc := witnessPacks_strictDisjoint w b m₀ am ap K η k m selected
    (spatialChunkIndex b k m 0::is) hselected hselectedPair
  simpa only [spatialChunkIndex_origin] using hc

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialEntropyProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory Filter
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem spatial_bad_path_probability (henv : ExponentialEnvironment P τ)
    (b m₀ am ap K η p₀ : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η) (hp₀ : 0 ≤ p₀)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (hBK : ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
      (is.map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)} ≤ p₀^is.length)
    (N : ℕ) (hN : 4 ≤ N) :
    P.real {ω | SpatialBadPath (fun e => τ e ω) b m₀ ((am+ap)/2) η k m N} ≤
      (196 : ℝ)^N*p₀^(N/16) := by
  let _ := henv.probability
  let codes := spatialItineraries 0 N ×ˢ compositionCover N (N/16)
  let E (code : List (ℤ×ℤ) × List ℕ) : Set Ω := {ω |
    (0::code.1).length=code.2.length ∧
    StrictDisjointPaths (spatialListSupport b k m (witnessLabels code.2 (0::code.1)))
      ((witnessLabels code.2 (0::code.1)).map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)}
  have hsub : {ω | SpatialBadPath (fun e => τ e ω) b m₀ ((am+ap)/2) η k m N} ≤ᵐ[P]
      ⋃ code ∈ codes,E code := by
    filter_upwards [henv.ae_positive] with ω hp hbad
    obtain ⟨is,his,ns,hns,hlen,hD⟩ := spatial_bad_path_cover (fun e => τ e ω) (fun e => (hp e).le)
      b m₀ am ap K η hb ha hη hgap k m hs hstep hscale₁ hscale₂ N hN hbad
    exact mem_iUnion₂.mpr ⟨(is,ns),mem_product.mpr ⟨his,hns⟩,hlen,hD⟩
  have hE (code : List (ℤ×ℤ) × List ℕ) (hc : code ∈ codes) : P.real (E code) ≤ p₀^(N/16) := by
    have hcomp := (mem_compositionCover ..).mp (mem_product.mp hc).2
    by_cases hlen : (0::code.1).length=code.2.length
    · have hl := witnessLabels_length code.2 (0::code.1) hlen.symm
      rw [hcomp.2] at hl
      have hh := hBK (witnessLabels code.2 (0::code.1))
      rw [hl] at hh
      exact (measureReal_mono (fun _ h => h.2)).trans hh
    · have he : E code=∅ := by
        ext ω
        exact ⟨fun h => (hlen h.1).elim,False.elim⟩
      rw [he,measureReal_empty]
      positivity
  have hcard : (codes.card : ℝ) ≤ (196 : ℝ)^N := by
    have hc : codes.card ≤ 196^N := by
      calc
        _ = (spatialItineraries 0 N).card*(compositionCover N (N/16)).card := card_product ..
        _ ≤ 49^N*4^N := Nat.mul_le_mul (spatialItineraries_card 0 N)
          (compositionCover_card N (N/16) (Nat.div_le_self ..))
        _ = 196^N := by rw [← mul_pow]; norm_num
    exact_mod_cast hc
  calc
    _ ≤ P.real (⋃ code ∈ codes,E code) := ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
    _ ≤ ∑ code ∈ codes,P.real (E code) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _code ∈ codes,p₀^(N/16) := sum_le_sum hE
    _ = (codes.card : ℝ)*p₀^(N/16) := by simp
    _ ≤ (196 : ℝ)^N*p₀^(N/16) := mul_le_mul_of_nonneg_right hcard (by positivity)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_WitnessBorelCantelli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory Filter

lemma entropy_geometric_bound (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) (hr1 : r ≤ 1) (N : ℕ) :
    a^N*(r^16)^(N/16) ≤ (r^15)⁻¹*(a*r)^N := by
  have hrem : N%16 ≤ 15 := by have hh := Nat.mod_lt N (by omega : 0<16); omega
  have hp : r^15 ≤ r^(N%16) := pow_le_pow_of_le_one hr.le hr1 hrem
  have hid : (r^16)^(N/16)*r^(N%16)=r^N := by
    rw [← pow_mul,← pow_add]
    congr 1
    have hh := Nat.mod_add_div N 16
    omega
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ a^N*(r^16)^(N/16) by positivity)
  simp only [mul_assoc] at hh
  rw [hid,← mul_pow] at hh
  calc
    _ ≤ (a*r)^N/r^15 := (le_div_iff₀ (pow_pos hr 15)).mpr (by simpa only [mul_assoc] using hh)
    _ = _ := by ring

theorem summable_witness_entropy (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 196*r < 1) :
    Summable (fun N : ℕ => (196 : ℝ)^N*(r^16)^(N/16)) := by
  have hs := (summable_geometric_of_lt_one (show 0 ≤ 196*r by positivity) hsmall).mul_left ((r^15)⁻¹)
  exact hs.of_nonneg_of_le (fun _ => by positivity) (entropy_geometric_bound 196 r (by norm_num) hr hr1)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ae_eventually_spatial_long_paths_oai (henv : ExponentialEnvironment P τ)
    (b m₀ am ap K η r : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 196*r < 1)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (hBK : ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
      (is.map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)} ≤ (r^16)^is.length) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      ∀ blocks : List (List Step), ∀ rest : List Step,
      blocks.length=N → (∀ q ∈ blocks, FullSpatialChunk b k m q) →
      (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) →
      ((trace 0 (blocks.flatten++rest)).map traversalEdge).Nodup →
      N*η*(2 : ℝ)^k/2 ≤ defect (fun e => τ e ω) b m₀ ((am+ap)/2) 0 (blocks.flatten++rest) := by
  let _ := henv.probability
  let B (N : ℕ) : Set Ω := {ω | SpatialBadPath (fun e => τ e ω) b m₀ ((am+ap)/2) η k m N}
  have hbound (N : ℕ) (hN : 4 ≤ N) : P.real (B N) ≤ (196 : ℝ)^N*(r^16)^(N/16) :=
    spatial_bad_path_probability henv b m₀ am ap K η (r^16) hb ha hη (by positivity)
      hgap k m hs hstep hscale₁ hscale₂ hBK N hN
  have hsum : Summable (fun N => P.real (B N)) := by
    rw [← summable_nat_add_iff 4]
    have hh := (summable_nat_add_iff 4).mpr (summable_witness_entropy r hr hr1 hsmall)
    exact hh.of_nonneg_of_le (fun _ => measureReal_nonneg) (fun n => hbound (n+4) (by omega))
  have ht : (∑' N, P (B N)) ≠ ⊤ := by
    simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hsum.tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem ht] with ω hω
  filter_upwards [hω] with N hN
  intro blocks rest hlen hfull hrest hsimple
  by_contra hc
  exact hN ⟨blocks,rest,hlen,hfull,hrest,hsimple,lt_of_not_ge hc⟩

end PlanarFPP

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PlanarFPP.ae_eventually_spatial_long_paths_oai.{u_1} := @OAI.PlanarFPP.ae_eventually_spatial_long_paths_oai.{u_1}
