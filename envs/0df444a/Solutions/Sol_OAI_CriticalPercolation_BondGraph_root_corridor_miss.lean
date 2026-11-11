-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.root_corridor_miss
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:10.735267+00:00
-- url     : https://prove2.me/submissions/b1bf65e6-9e2f-4049-8568-a054640c328b

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Definitions.Def_OAIQ228B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_fresh_collar_transfer
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_source_hit_probability

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_TailProduct
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma law_eq_infinitePi (q : E → unitInterval) :
    law q = Measure.infinitePi (fun e => bitMeasure (q e)) := by
  change Measure.map id _ = _
  exact Measure.map_id

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ProductConditioning
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma forceOn_map_law (q : E → unitInterval) (S σ : Set E) :
    (law q).map (forceOn S σ)=law (pinnedParameters q S σ) := by
  simp only [law_eq_infinitePi]
  have hm (e : E) : Measurable (fun b : Prop => if e∈S then e∈σ else b) := .of_discrete
  have h := Measure.infinitePi_map_pi (fun e => bitMeasure (q e)) hm
  change (Measure.infinitePi (fun e => bitMeasure (q e))).map
    (fun (ω : E → Prop) e => if e∈S then e∈σ else ω e)=
    Measure.infinitePi (fun e => bitMeasure (pinnedParameters q S σ e))
  rw [h]
  congr 1
  funext e
  by_cases he : e∈S
  · simp only [ite_eq_left he,Measure.map_const,measure_univ,one_smul]
    by_cases hs : e∈σ <;> simp [pinnedParameters,he,hs,bitMeasure]
  · simp [pinnedParameters,he]

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem openGraph_mono {ω ω' : Set E} (h : ω ⊆ ω') :
    G.openGraph ω ≤ G.openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono (Set.image_mono h)

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_HitEvent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Set
open scoped Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma hitEvent_mono_edges (o : V) (A : Set V) {ω ω' : Set E} (h : ω ⊆ ω') :
    ω ∈ G.hitEvent o A → ω' ∈ G.hitEvent o A :=
  fun hω => hω.mono (Set.inter_subset_inter_left A (G.cluster_mono h o))

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_ConditionalGluing
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma seedHitEvent_upper (B T : Set V) : IsUpperSet (G.seedHitEvent B T) := by
  intro ω τ hωτ hω
  obtain ⟨b,hb,hω⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨b,hb,G.hitEvent_mono_edges b T hωτ hω⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CorridorGraph
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma coordinate_ball_bound (f : V → ℝ) (ρ : ℝ) (hρ : 0≤ρ)
    (hf : ∀ ⦃v w⦄, G.fullGraph.Adj v w → |f v-f w|≤ρ)
    {v w : V} {n : ℕ} (hw : w∈G.vertexBall v n) : |f w-f v|≤n*ρ := by
  induction n generalizing w with
  | zero =>
    have he : w=v := hw
    subst w
    simp
  | succ n ih =>
    rcases hw with hw|hw
    · exact (ih hw).trans (by push_cast <;> nlinarith)
    · obtain ⟨u,hu,huw⟩ := Set.mem_iUnion₂.mp hw
      calc
        |f w-f v| ≤ |f w-f u|+|f u-f v| := abs_sub_le _ _ _
        _ ≤ ρ+n*ρ := add_le_add (hf huw.symm) (ih hu)
        _ = _ := by push_cast <;> ring

lemma coordinate_collar_bound (f : V → ℝ) (ρ : ℝ) (hρ : 0≤ρ)
    (hf : ∀ ⦃v w⦄, G.fullGraph.Adj v w → |f v-f w|≤ρ)
    (B : Set V) (c r : ℝ) (hB : ∀ v∈B, |f v-c| ≤ r)
    {w : V} {n : ℕ} (hw : w∈G.vertexCollar B n) : |f w-c| ≤ r+n*ρ := by
  obtain ⟨v,hv,hw⟩ := Set.mem_iUnion₂.mp hw
  calc
    |f w-c| ≤ |f w-f v|+|f v-c| := abs_sub_le _ _ _
    _ ≤ n*ρ+r := add_le_add (G.coordinate_ball_bound f ρ hρ hf hw) (hB v hv)
    _ = _ := add_comm _ _

lemma inducedEdges_mono {S T : Set V} (h : S⊆T) :
    G.inducedEdges S⊆G.inducedEdges T := by
  intro e he v hv
  exact h (he v hv)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_RelayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.Relay

lemma width_lower (i : ℕ) : 2 ≤ width i := le_max_left _ _
lemma width_upper (i : ℕ) : width i ≤ 210 := by
  apply max_le (by norm_num)
  linarith [Nat.cast_nonneg (α := ℝ) i]
lemma width_next (i : ℕ) : width i ≤ width (i+1)+1/2 := by
  have h1 := width_lower (i+1)
  have h2 : 210-((i+1 : ℕ) : ℝ)/2 ≤ width (i+1) := le_max_right _ _
  unfold width at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  exact max_le (by linarith) (by linarith)
lemma width_last (L : ℕ) (hL : 416 ≤ L) : width L=2 := by
  apply max_eq_left
  have : (416 : ℝ) ≤ L := by exact_mod_cast hL
  linarith

lemma selectedSign_cases (u : ℝ) : selectedSign u=-1 ∨ selectedSign u=1 := by
  unfold selectedSign
  split  <;>  simp

lemma selectedSign_abs (u : ℝ) : |selectedSign u|=1 := by
  rcases selectedSign_cases u with h|h  <;>  rw [h]  <;>  norm_num

lemma move_towards_axis (u b : ℝ) (hu : |u| ≤ b) :
    |u+selectedSign u| ≤ max 1 (b-1) := by
  rw [abs_le] at hu ⊢
  have h1 : 1 ≤ max 1 (b-1) := le_max_left _ _
  have h2 : b-1 ≤ max 1 (b-1) := le_max_right _ _
  unfold selectedSign
  split  <;>  constructor  <;>  linarith

lemma full_step_height (i : ℕ) (u σ d e ε : ℝ) (hσ : |σ|=1)
    (hu : |u| ≤ width i+d) (hd₀ : 0 ≤ d) (hd : d+e/4 ≤ 1/4)
    (hε : |ε| ≤ e/4) :
    |u+selectedSign u-σ/4+ε| ≤ width (i+1) := by
  have h1 := width_lower (i+1)
  have h2 := width_next i
  have hs : |σ/4|=1/4 := by rw [abs_div,hσ]; norm_num
  calc
    _  ≤  |u+selectedSign u|+|σ/4|+|ε| :=
      by linarith [abs_add_le (u+selectedSign u-σ/4) ε, abs_sub (u+selectedSign u) (σ/4)]
    _  ≤  max 1 (width i+d-1)+1/4+e/4 := by
      rw [hs]
      linarith [move_towards_axis u (width i+d) hu]
    _  ≤  width (i+1) := by
      rcases le_total 1 (width i+d-1) with hh|hh
      · rw [max_eq_right hh]; linarith
      · rw [max_eq_left hh]; linarith

lemma full_step_time (i : ℕ) (y z d e : ℝ)
    (hy : |y-(i : ℝ)| ≤ (i+1)*e+d) (hz : |z-(y+1)| ≤ e/4)
    (hde : d+e/4 ≤ e) : |z-((i+1 : ℕ) : ℝ)| ≤ (i+2)*e := by
  rw [abs_le] at hy hz ⊢
  push_cast
  constructor  <;>  nlinarith

lemma path_axis_bound (L i : ℕ) (hi : i ≤ L) (y x : ℝ×ℝ) (d e σ : ℝ)
    (hσ : |σ|=1) (he : 0 ≤ e)
    (hyt : |y.1-(i : ℝ)| ≤ (i+1)*e+d)
    (hyz : |y.2-σ*(i : ℝ)/4| ≤ width i+d)
    (hxt : |x.1-y.1| ≤ 100) (hxz : |x.2-y.2| ≤ 100) :
    |x.2-σ*x.1/4| ≤ 210+d+100+((L+1)*e+d+100)/4 := by
  have ht : |x.1-(i : ℝ)| ≤ (L+1)*e+d+100 := by
    have hc : (i : ℝ) ≤ L := by exact_mod_cast hi
    calc
      _  ≤  |x.1-y.1|+|y.1-(i : ℝ)| := abs_sub_le _ _ _
      _  ≤  100+((i+1)*e+d) := add_le_add hxt hyt
      _  ≤  _ := by nlinarith
  have hsame : σ*(i : ℝ)/4-σ*x.1/4=σ*((i : ℝ)-x.1)/4 := by ring
  calc
    _  ≤  |x.2-y.2|+|y.2-σ*(i : ℝ)/4|+|σ*(i : ℝ)/4-σ*x.1/4| := by
      linarith [abs_sub_le x.2 (σ*(i : ℝ)/4) (σ*x.1/4),
        abs_sub_le x.2 y.2 (σ*(i : ℝ)/4)]
    _  ≤  100+(width i+d)+((L+1)*e+d+100)/4 := by
      rw [hsame,abs_div,abs_mul,hσ,one_mul,abs_of_pos (by norm_num : (0:ℝ) < 4),abs_sub_comm (i : ℝ)]
      exact add_le_add (add_le_add hxz hyz) (div_le_div_of_nonneg_right ht (by norm_num))
    _  ≤  _ := by linarith [width_upper i]

lemma band_mem_domain (J T σ : ℝ) (hσ : |σ|=1)
    (x : ℝ×ℝ) (ht : -J ≤ x.1 ∧ x.1 ≤ T+J)
    (hz : |x.2-σ*x.1/4| ≤ 630) : x∈domain J T σ := by
  have ha : |σ|=1 := hσ
  by_cases h0 : x.1 < 0
  · apply Or.inl; apply Or.inl
    have hx : |x.1| ≤ J := by rw [abs_of_neg h0]; linarith [ht.1]
    refine ⟨hx,?_⟩
    calc
      |x.2|  ≤  |x.2-σ*x.1/4|+|σ*x.1/4| := by simpa using abs_sub_le x.2 (σ*x.1/4) 0
      _  ≤  630+J/4 := by
        rw [abs_div,abs_mul,ha,one_mul,abs_of_pos (by norm_num : (0:ℝ) < 4)]
        exact add_le_add hz (div_le_div_of_nonneg_right hx (by norm_num))
      _ = _ := add_comm _ _
  · by_cases h1 : T < x.1
    · apply Or.inl; apply Or.inr
      have hx : |x.1-T| ≤ J := by rw [abs_of_pos (by linarith)]; linarith [ht.2]
      refine ⟨hx,?_⟩
      calc
        _  ≤  |x.2-σ*x.1/4|+|σ*x.1/4-σ*T/4| := abs_sub_le _ _ _
        _ = |x.2-σ*x.1/4|+|x.1-T|/4 := by
          rw [show σ*x.1/4-σ*T/4=σ*(x.1-T)/4 by ring,abs_div,abs_mul,ha,one_mul]
          norm_num
        _  ≤  630+J/4 := add_le_add hz (div_le_div_of_nonneg_right hx (by norm_num))
        _ = _ := add_comm _ _
    · exact Or.inr ⟨by linarith,by linarith,hz⟩

lemma move_path_contained (J : ℝ) (L i : ℕ) (hi : i ≤ L) (hJ : 26200 < J)
    (y x : ℝ×ℝ) (d e σ : ℝ) (hσ : |σ|=1) (he : 0 ≤ e)
    (hsmall : (L+1)*e+d < 1)
    (hyt : |y.1-(i : ℝ)| ≤ (i+1)*e+d)
    (hyz : |y.2-σ*(i : ℝ)/4| ≤ width i+d)
    (hxt : |x.1-y.1| ≤ 100) (hxz : |x.2-y.2| ≤ 100) :
    x∈domain J (L+1/2) σ := by
  have hi' : (i : ℝ) ≤ L := by exact_mod_cast hi
  have hi₀ : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have heL : 0 ≤ (L+1)*e := mul_nonneg (by positivity) he
  apply band_mem_domain J (L+1/2) σ hσ x
  · rw [abs_le] at hyt hxt
    constructor  <;>  nlinarith
  · exact (path_axis_bound L i hi y x d e σ hσ he hyt hyz hxt hxz).trans (by linarith)

lemma last_crossing_height (L : ℕ) (y x : ℝ×ℝ) (d σ : ℝ) (hσ : |σ|=1)
    (hy : |y.2-σ*(L : ℝ)/4| ≤ 2+d) (hx : |x.2-y.2| ≤ 100) (hd : d < 1) :
    |x.2-σ*(L+1/2)/4| < 210 := by
  have he : σ*(L : ℝ)/4-σ*(L+1/2)/4=-σ/8 := by ring
  calc
    _  ≤  |x.2-y.2|+|y.2-σ*(L : ℝ)/4|+|σ*(L : ℝ)/4-σ*(L+1/2)/4| :=
      by linarith [abs_sub_le x.2 (σ*(L : ℝ)/4) (σ*(L+1/2)/4),
        abs_sub_le x.2 y.2 (σ*(L : ℝ)/4)]
    _  ≤  100+(2+d)+1/8 := by
      rw [he,abs_div,abs_neg,hσ]
      norm_num
      linarith
    _  <  _ := by linarith

end CriticalPercolation.Relay
namespace SimpleGraph.Walk
open scoped _root_.SimpleGraph _root_.SimpleGraph.Walk
variable {V : Type*} {H : SimpleGraph V}

lemma exists_first_crossing (f : V → ℝ) (ρ T : ℝ)
    (hf : ∀ ⦃x y⦄, H.Adj x y → |f x-f y| ≤ ρ)
    {a b : V} (w : H.Walk a b) (ha : f a < T) (hb : T ≤ f b) :
    ∃ x∈w.support, T ≤ f x ∧ f x ≤ T+ρ := by
  induction w with
  | nil =>  exact (not_le_of_gt ha hb).elim
  | @cons a c b hac w ih =>
    by_cases hc : T ≤ f c
    · refine ⟨c,?_,hc,?_⟩
      · simp only [_root_.SimpleGraph.Walk.support_cons,List.mem_cons]
        exact Or.inr w.start_mem_support
      · have hh := hf hac
        rw [abs_le] at hh
        linarith
    · obtain ⟨x,hx,h1,h2⟩ := ih (lt_of_not_ge hc) hb
      exact ⟨x,by simp only [_root_.SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hx,h1,h2⟩
end SimpleGraph.Walk
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_RelayMoves
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma walk_reachable_induced (S : Set V) (ω : Set E) {a b : V}
    (w : (G.openGraph ω).Walk a b) (hw : ∀ x∈w.support,x∈S) :
    (G.openGraph (ω∩G.inducedEdges S)).Reachable a b := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a c b hac w ih =>
    have hc : c∈S := hw c (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr w.start_mem_support)
    have ha : a∈S := hw a (by simp)
    exact ((G.open_induced_adj S ω a c).mpr ⟨hac,ha,hc⟩).reachable.trans
      (ih (fun x hx => hw x (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hx)))

lemma relay_collar_bounds (t z : V → ℝ) (σ e ρ : ℝ) (hρ : 0 ≤ ρ)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (R i : ℕ) {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e i) R) :
    |t y-(i : ℝ)| ≤ (i+1)*e+R*ρ ∧ |z y-σ*(i : ℝ)/4| ≤ Relay.width i+R*ρ := by
  exact ⟨G.coordinate_collar_bound t ρ hρ ht _ _ _ (fun _ h => h.1) hy,
    G.coordinate_collar_bound z ρ hρ hz _ _ _ (fun _ h => h.2) hy⟩

lemma full_relay_move (t z : V → ℝ) (σ e ρ J : ℝ) (L R m i : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hi : i<L) (hsmall : (L+1)*e+R*ρ<1)
    (hheight : R*ρ+e/4 ≤ 1/4) (htime : R*ρ+e/4 ≤ e)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e i) R) :
    coordinateMove G t z m e y (Relay.selectedSign (z y-σ*(i : ℝ)/4)) ⊆
      {ω | ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
        G.seedHitEvent (G.vertexBall y m) (relayRegion t z σ e (i+1))} := by
  intro ω hω
  obtain ⟨a,ha,b,w,hw,hbt,hbz⟩ := hω
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R i hy
  have hb : b∈relayRegion t z σ e (i+1) := by
    refine ⟨?_,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
        Relay.full_step_time i (t y) (t b) (R*ρ) e hy'.1 hbt htime
    have hh := Relay.full_step_height i (z y-σ*(i : ℝ)/4) σ (R*ρ) e
      (z b-(z y+Relay.selectedSign (z y-σ*(i : ℝ)/4))) hσ hy'.2
      (mul_nonneg (Nat.cast_nonneg _) hρ) hheight hbz
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring_nf
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,b,G.walk_reachable_induced _ ω w ?_,hb⟩
  intro x hx
  exact Relay.move_path_contained J L i hi.le hJ (t y,z y) (t x,z x)
    (R*ρ) e σ hσ he hsmall hy'.1 hy'.2 (hw x hx).1 (hw x hx).2

lemma last_relay_move (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hL : 416 ≤ L) (hsmall : (L+1)*e+(R+m)*ρ+e/4<1/2)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e L) R) (s : ℝ) :
    coordinateMove G t z m e y s ⊆
      {ω | ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
        G.seedHitEvent (G.vertexBall y m) (relayMark t z (L+1/2) σ ρ)} := by
  intro ω hω
  obtain ⟨a,ha,b,w,hw,hbt,_⟩ := hω
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R L hy
  have hma : |t a-t y| ≤ m*ρ := G.coordinate_ball_bound t ρ hρ ht ha
  have hnR : 0 ≤ (R : ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hnm : 0 ≤ (m : ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hnL : 0 ≤ (L+1 : ℝ)*e := mul_nonneg (by positivity) he
  have hyt := abs_le.mp hy'.1
  have hbt' := abs_le.mp hbt
  have hma' := abs_le.mp hma
  have haT : t a<L+1/2 := by linarith
  have hbT : (L : ℝ)+1/2 ≤ t b := by linarith
  have hadj : ∀ ⦃u v⦄, (G.openGraph ω).Adj u v → |t u-t v| ≤ ρ :=
    fun _ _ h => ht (G.openGraph_mono (Set.subset_univ _) h)
  obtain ⟨x,hx,hx₁,hx₂⟩ := _root_.OAI.SimpleGraph.Walk.exists_first_crossing t ρ (L+1/2) hadj w haT hbT
  have hxz : |z x-σ*(L+1/2)/4|<210 := by
    apply Relay.last_crossing_height L (t y,z y) (t x,z x) (R*ρ) σ hσ
    · simpa only [Relay.width_last L hL] using hy'.2
    · exact (hw x hx).2
    · linarith
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,x,?_,⟨hx₁,hx₂,hxz.le⟩⟩
  apply G.walk_reachable_induced _ ω (w.takeUntil x hx)
  intro v hv
  have hv' : v∈w.support := (w.isSubwalk_takeUntil hx).support_subset hv
  apply Relay.move_path_contained J L L le_rfl hJ (t y,z y) (t v,z v)
    (R*ρ) e σ hσ he _ hy'.1 hy'.2 (hw v hv').1 (hw v hv').2
  linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_RelayScales
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma vertexCollar_mono {S T : Set V} (hST : S⊆T) (R : ℕ) :
    G.vertexCollar S R⊆G.vertexCollar T R := by
  intro y hy
  obtain ⟨v,hv,hy⟩ := Set.mem_iUnion₂.mp hy
  exact Set.mem_iUnion₂.mpr ⟨v,hST hv,hy⟩

lemma initial_mark_subset_relay (t z : V → ℝ) (σ e ρ : ℝ) (hρ : ρ ≤ e) :
    relayMark t z 0 σ ρ⊆relayRegion t z σ e 0 := by
  intro v hv
  obtain ⟨ht₀,ht₁,hz⟩ := hv
  change |t v-(0:ℕ)| ≤ ((0:ℕ)+1)*e ∧ |z v-σ*(0:ℕ)/4| ≤ Relay.width 0
  norm_num [Relay.width] at ht₀ ht₁ hz ⊢
  exact ⟨by rw [abs_of_nonneg ht₀]; linarith,hz⟩

lemma relay_coordinate_scale (L R m : ℕ) (e ρ : ℝ) (he : 0<e) (hρ : 0 ≤ ρ)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) :
    ρ ≤ e ∧ (L+1)*e+R*ρ<1 ∧ R*ρ+e/4 ≤ 1/4 ∧ R*ρ+e/4 ≤ e ∧
      (L+1)*e+(R+m)*ρ+e/4<1/2 := by
  have hR : 0 ≤ (R:ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hm : 0 ≤ (m:ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hL : 0 ≤ (L:ℝ)*e := mul_nonneg (Nat.cast_nonneg _) he.le
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma relay_collar_in_domain (t z : V → ℝ) (σ e ρ J : ℝ) (L R i : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hi : i ≤ L) (hsmall : (L+1)*e+R*ρ<1)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ) :
    G.vertexCollar (relayRegion t z σ e i) R⊆relayDomain t z J (L+1/2) σ := by
  intro y hy
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R i hy
  apply Relay.move_path_contained J L i hi hJ (t y,z y) (t y,z y)
    (R*ρ) e σ hσ he hsmall hy'.1 hy'.2 <;> norm_num

lemma forceOutside_induced (S : Set V) (ω : Set E) :
    BernoulliProduct.forceOn (G.inducedEdges S)ᶜ ∅ ω=ω∩G.inducedEdges S := by
  ext b
  by_cases hb : b∈G.inducedEdges S <;> simp [hb]

lemma corridorRelay_subset (t z : V → ℝ) (σ e ρ : ℝ) (hρe : ρ ≤ e)
    (L i : ℕ) (hi : i ≤ L) : corridorRelay t z σ e ρ L i⊆relayRegion t z σ e i := by
  by_cases h0 : i=0
  · subst i
    simpa [corridorRelay] using initial_mark_subset_relay t z σ e ρ hρe
  · simp only [corridorRelay,ite_eq_right h0,ite_eq_left hi,Subset.rfl]

theorem coordinate_moves_relay_estimates (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (p : unitInterval) (η : ℝ)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p)).real
      (G.coordinateMove t z m e y s)) :
    ∀ i ≤ L,
      G.vertexCollar (corridorRelay t z σ e ρ L i) R⊆relayDomain t z J (L+1/2) σ ∧
      ∀ y∈G.vertexCollar (corridorRelay t z σ e ρ L i) R,
        1-η ≤ (BernoulliProduct.law (fun _ : E => p)).real
          ((BernoulliProduct.forceOn (G.inducedEdges (relayDomain t z J (L+1/2) σ))ᶜ ∅) ⁻¹'
            G.seedHitEvent (G.vertexBall y m) (corridorRelay t z σ e ρ L (i+1))) := by
  obtain ⟨hρe,hsmall,hheight,htime,hlast⟩ := relay_coordinate_scale L R m e ρ he hρ heL hr
  intro i hi
  have hsub := G.vertexCollar_mono (corridorRelay_subset t z σ e ρ hρe L i hi) R
  refine ⟨hsub.trans (G.relay_collar_in_domain t z σ e ρ J L R i hσ he.le hρ hJ hi hsmall ht hz),?_⟩
  intro y hy
  apply (hmove y (Relay.selectedSign (z y-σ*(i:ℝ)/4)) (Relay.selectedSign_abs _)).trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω
  rw [Set.mem_preimage,G.forceOutside_induced]
  by_cases hiL : i<L
  · have hh := G.full_relay_move t z σ e ρ J L R m i hσ he.le hρ hJ hiL hsmall
      hheight htime ht hz (hsub hy) hω
    change ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
      G.seedHitEvent (G.vertexBall y m) (relayRegion t z σ e (i+1)) at hh
    simpa only [corridorRelay,Nat.add_one_ne_zero,ite_false, if_false,ite_eq_left (by omega : i+1 ≤ L)] using hh
  · have hiEq : i=L := by omega
    subst i
    have hh := G.last_relay_move t z σ e ρ J L R m hσ he.le hρ hJ hL hlast ht hz
      (hsub hy) _ hω
    change ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
      G.seedHitEvent (G.vertexBall y m) (relayMark t z (L+1/2) σ ρ) at hh
    simpa only [corridorRelay,Nat.add_one_ne_zero,ite_false, if_false,ite_eq_right (by omega : ¬L+1 ≤ L)] using hh

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FreshRegionLaw
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma trim_law_eq (q r : E → unitInterval) (S : Set E) (h : ∀ e∈S, q e=r e) :
    (law q).map (forceOn Sᶜ ∅)=(law r).map (forceOn Sᶜ ∅) := by
  rw [forceOn_map_law,forceOn_map_law]
  congr 1
  funext e
  by_cases he : e∈S
  · simp [pinnedParameters,he,h e he]
  · simp [pinnedParameters,he]

lemma fresh_region_lower (q r : E → unitInterval) (S : Set E) (h : ∀ e∈S, q e=r e)
    (B : Set (Set E)) (hm : MeasurableSet B) (hu : IsUpperSet B) :
    (law r).real ((forceOn Sᶜ ∅) ⁻¹' B) ≤ (law q).real B := by
  have he : (law r) ((forceOn Sᶜ ∅) ⁻¹' B)=(law q) ((forceOn Sᶜ ∅) ⁻¹' B) := by
    rw [← Measure.map_apply (measurable_forceOn _ _) hm,
      ← Measure.map_apply (measurable_forceOn _ _) hm,trim_law_eq q r S h]
  rw [measureReal_def,he]
  change (law q).real ((forceOn Sᶜ ∅) ⁻¹' B) ≤ _
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  apply hu (a := forceOn Sᶜ ∅ ω) (b := ω) ?_ hω
  intro e he
  by_cases hes : e∈S
  · simpa [forceOn,hes] using he
  · simp [hes] at he

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_SourceRelaySeparation
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma source_outside_relay_collar (t z : V → ℝ) (σ e ρ P : ℝ) (L R m i : ℕ)
    (he : 0<e) (hρ : 0 ≤ ρ) (hi : i ≤ L) (hPi : 1 ≤ P+i)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {a : V} (ha : t a ≤ m*ρ-P) :
    a∉G.vertexCollar (corridorRelay t z σ e ρ L i) R := by
  intro hin
  obtain ⟨hρe,_,_,_,hlast⟩ := relay_coordinate_scale L R m e ρ he hρ heL hr
  have hs := G.vertexCollar_mono (corridorRelay_subset t z σ e ρ hρe L i hi) R hin
  have hb := (G.relay_collar_bounds t z σ e ρ hρ ht hz R i hs).1
  have hi' : (i:ℝ) ≤ L := by exact_mod_cast hi
  have hile : (i+1)*e ≤ (L+1)*e := mul_le_mul_of_nonneg_right (by linarith) he.le
  have hb' := (abs_le.mp hb).1
  nlinarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_RelayProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation
variable {Ω : Type*} [MeasurableSpace Ω]

lemma relay_failure_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ℕ → Set Ω) (κ : ℝ) (N : ℕ)
    (h : ∀ i<N, μ.real (A i\A (i+1)) ≤ κ) :
    μ.real (A 0\A N) ≤ N*κ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hsub : A 0\A (N+1) ⊆ (A 0\A N)∪(A N\A (N+1)) := by
      intro ω hω
      by_cases hn : ω∈A N
      · exact Or.inr ⟨hn,hω.2⟩
      · exact Or.inl ⟨hω.1,hn⟩
    calc
      _ ≤ μ.real ((A 0\A N)∪(A N\A (N+1))) := measureReal_mono hsub
      _ ≤ μ.real (A 0\A N)+μ.real (A N\A (N+1)) := measureReal_union_le _ _
      _ ≤ N*κ+κ := add_le_add (ih (fun i hi => h i (by omega))) (h N (by omega))
      _ = _ := by push_cast <;> ring

lemma relay_miss_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ℕ → Set Ω) (κ η : ℝ) (N : ℕ)
    (hfirst : μ.real (A 0)ᶜ ≤ η)
    (h : ∀ i<N, μ.real (A i\A (i+1)) ≤ κ) :
    μ.real (A N)ᶜ ≤ η+N*κ := by
  have hsub : (A N)ᶜ⊆(A 0)ᶜ∪(A 0\A N) := by
    intro ω hω
    by_cases h0 : ω∈A 0
    · exact Or.inr ⟨h0,hω⟩
    · exact Or.inl h0
  calc
    _ ≤ μ.real ((A 0)ᶜ∪(A 0\A N)) := measureReal_mono hsub
    _ ≤ μ.real (A 0)ᶜ+μ.real (A 0\A N) := measureReal_union_le _ _
    _ ≤ _ := add_le_add hfirst (relay_failure_bound μ A κ N h)

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_RootCorridor
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem root_corridor_miss_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (q : (E⊕G.vertexBall o m) → unitInterval)
    (hwire : ∀ a : G.vertexBall o m, q (Sum.inr a)=1)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) (hto : t o=0) (hzo : z o=0)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q (Sum.inl b)=p')
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.law q).real
      ((G.withSource (G.vertexBall o m)).hitEvent none
        (some '' relayMark t z (L+1/2) σ ρ))ᶜ ≤ η+L*κ := by
  let A := G.vertexBall o m
  let H : ℕ → Set (Set (E⊕A)) := fun i =>
    (G.withSource A).hitEvent none (some '' corridorRelay t z σ e ρ L (i+1))
  have h0 := G.coordinate_moves_relay_estimates t z σ e ρ J L R m
    hσ he hρ hJ hL heL hr ht hz p' η hmove 0 (Nat.zero_le L)
  have ho : o∈G.vertexCollar (corridorRelay t z σ e ρ L 0) R := by
    apply Set.mem_iUnion₂.mpr
    refine ⟨o,?_,G.mem_vertexBall_self o R⟩
    simp only [corridorRelay]
    exact ⟨by simp [hto],by simp [hto,hρ],by simp [hzo]⟩
  have hh0 : 1-η ≤ (BernoulliProduct.law q).real (H 0) := by
    rw [measureReal_def,G.source_hit_probability A _ q hwire]
    exact (h0.2 o ho).trans (BernoulliProduct.fresh_region_lower (fun b => q (Sum.inl b))
      (fun _ => p') (G.inducedEdges (relayDomain t z J (L+1/2) σ)) hq _
      (G.measurableSet_seedHitEvent _ _) (G.seedHitEvent_upper _ _))
  have hfirst : (BernoulliProduct.law q).real (H 0)ᶜ ≤ η := by
    rw [probReal_compl_eq_one_sub ((G.withSource A).measurableSet_hitEvent _ _)]
    linarith
  have hh := relay_miss_bound (BernoulliProduct.law q) H κ η L hfirst (by
    intro i hi
    have hiL : i+1 ≤ L := by omega
    obtain ⟨hcoll,hmean⟩ := G.coordinate_moves_relay_estimates t z σ e ρ J L R m
      hσ he hρ hJ hL heL hr ht hz p' η hmove (i+1) hiL
    apply G.fresh_collar_transfer hc hl A _ _ (G.vertexBall_finite hl o m) q m R hcR
      (G.inducedEdges (relayDomain t z J (L+1/2) σ))
      (fun a ha => G.source_outside_relay_collar t z σ e ρ 0 L R m (i+1) he hρ hiL
        (by push_cast <;> linarith [Nat.cast_nonneg (α := ℝ) i]) heL hr ht hz ?_)
      (G.inducedEdges_mono hcoll) pc p' hpc₀ hpc hpp hppc hq D k M VM hD hM hMbound hVM
      κ η hκ hκ1 hη₀ hη hk hR hmean
    have hb := (abs_le.mp (G.coordinate_ball_bound t ρ hρ ht ha)).2
    simpa [hto] using hb)
  simpa only [H,corridorRelay,Nat.add_one_ne_zero,ite_false, if_false,
    ite_eq_right (by omega : ¬L+1 ≤ L)] using hh

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.root_corridor_miss_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.root_corridor_miss_oai.{u_1, u_2}
