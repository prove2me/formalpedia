-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.subcritical_seedExpectation_bound_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:56:07.947258+00:00
-- url     : https://prove2.me/submissions/6a8b3fb9-e645-441b-aa2c-53e27475bbd3

import Mathlib
import Definitions.Def_OAIQ078B002

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

theorem cluster_mono {ω ω' : Set E} (h : ω ⊆ ω') (v : V) :
    G.cluster ω v ⊆ G.cluster ω' v :=
  fun _ hw => hw.mono (G.openGraph_mono h)

lemma criticalProbability_le_of_pos {p : unitInterval}
    (hp : 0 < G.law p G.percolates) : G.criticalProbability ≤ p :=
  sInf_le hp

lemma law_percolates_eq_zero_of_lt_critical {p : unitInterval}
    (hp : p < G.criticalProbability) : G.law p G.percolates = 0 := by
  by_contra h
  exact (not_le_of_gt hp) (G.criticalProbability_le_of_pos (pos_iff_ne_zero.mpr h))

lemma mem_cluster_finite_witness {ω : Set E} {v w : V} (h : w ∈ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v := by
  classical
  have hr := ((G.openGraph ω).reachable_iff_reflTransGen v w).mp h
  clear h
  induction hr with
  | refl => exact ⟨∅, Set.finite_empty, Set.empty_subset _, .refl _⟩
  | @tail u w hr huw ih =>
      obtain ⟨s, hs, hsω, hvs⟩ := ih
      obtain ⟨⟨e, heω, heq⟩, hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huw
      refine ⟨insert e s, hs.insert e, Set.insert_subset heω hsω, ?_⟩
      have hvu : (G.openGraph (insert e s)).Reachable v u :=
        hvs.mono (G.openGraph_mono (Set.subset_insert _ _))
      apply hvu.trans
      apply SimpleGraph.Adj.reachable
      exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e, Set.mem_insert _ _, heq⟩, hne⟩

end BondGraph

namespace ClusterDeletion
variable {V : Type*}

lemma delete_le (H : SimpleGraph V) (U : Set V) : delete H U ≤ H :=
  fun _ _ h => h.1

lemma roots_mono {H H' : SimpleGraph V} (h : H ≤ H') (S : Set V) :
    roots H S ⊆ roots H' S := by
  rintro v ⟨s, hs, hsv⟩
  exact ⟨s, hs, hsv.mono h⟩

lemma component_mono {H H' : SimpleGraph V} (h : H ≤ H') (s : V) :
    component H s ⊆ component H' s :=
  fun _ hv => hv.mono h

lemma reachable_not_mem_roots {H : SimpleGraph V} {S : Set V} {s v : V}
    (hs : s ∉ roots H S) (hsv : H.Reachable s v) : v ∉ roots H S := by
  rintro ⟨u, hu, huv⟩
  exact hs ⟨u, hu, huv.trans hsv.symm⟩

lemma delete_roots_component (H : SimpleGraph V) (S : Set V) (s : V)
    (hs : s ∉ roots H S) :
    component (delete H (roots H S)) s = component H s := by
  apply Set.Subset.antisymm (component_mono (delete_le _ _) _)
  intro v hv
  have hr := (H.reachable_iff_reflTransGen s v).mp hv
  clear hv
  induction hr with
  | refl => exact .refl _
  | @tail u v hr huv ih =>
      have hsu : H.Reachable s u := (H.reachable_iff_reflTransGen _ _).mpr hr
      have hsv : H.Reachable s v := hsu.trans huv.reachable
      exact ih.trans (SimpleGraph.Adj.reachable
        ⟨huv, reachable_not_mem_roots hs hsu, reachable_not_mem_roots hs hsv⟩)

end ClusterDeletion
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma dependsOn_exact_roots (S U : Set V) :
    DependsOn (fun ω : Set E => ClusterDeletion.roots (G.openGraph ω) S = U)
      (G.incidentEdges U) := by
  intro ω ω' hω
  apply propext
  exact ⟨fun h => G.roots_eq_of_incident h (fun e he => (hω e he).to_iff),
    fun h => G.roots_eq_of_incident h (fun e he => (hω e he).symm.to_iff)⟩

lemma delete_openGraph_dependsOn (U : Set V) :
    DependsOn (fun ω : Set E => ClusterDeletion.delete (G.openGraph ω) U)
      (G.incidentEdges U)ᶜ := by
  intro ω ω' hω
  ext v w
  change ((G.openGraph ω).Adj v w ∧ v ∉ U ∧ w ∉ U) ↔
    ((G.openGraph ω').Adj v w ∧ v ∉ U ∧ w ∉ U)
  by_cases hv : v ∈ U
  · simp [hv]
  by_cases hw : w ∈ U
  · simp [hw]
  simp only [hv, hw, not_false_eq_true, and_self, and_true, openGraph,
    SimpleGraph.fromEdgeSet_adj]
  have he : ∀ e, G.ends e = s(v, w) → e ∈ (G.incidentEdges U)ᶜ := by
    intro e heq
    rintro ⟨x, hxU, hxe⟩
    have := hxe
    simp only [heq, Sym2.mem_iff] at this
    rcases this with rfl | rfl
    · exact hv hxU
    · exact hw hxU
  constructor
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).to_iff.mp heω, heq⟩, hne⟩
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).to_iff.mpr heω, heq⟩, hne⟩

end BondGraph
end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ComponentSelf
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.ClusterDeletion
variable {V : Type*}

lemma roots_singleton (H : SimpleGraph V) (s : V) : roots H {s} = component H s := by
  ext v
  simp [roots, component]

end CriticalPercolation.ClusterDeletion

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Density
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype A] in
lemma density_nonneg {w : E → A → ℝ} (h : ∀ e a, 0 ≤ w e a) (ω : E → A) :
    0 ≤ density w ω := Finset.prod_nonneg fun e _ => h e (ω e)

lemma sum_density [DecidableEq E] (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) :
    ∑ ω, density w ω = 1 := by
  classical
  unfold density
  rw [← Fintype.prod_sum]
  simp [h]

lemma expect_const (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) (c : ℝ) :
    expect w (fun _ => c) = c := by
  classical
  rw [expect, ← Finset.sum_mul, sum_density w h, one_mul]

lemma expect_sub (w : E → A → ℝ) (f g : (E → A) → ℝ) :
    expect w (fun ω => f ω - g ω) = expect w f - expect w g := by
  classical
  simp [expect, mul_sub, Finset.sum_sub_distrib]

lemma expect_mono {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f g : (E → A) → ℝ} (hfg : ∀ ω, f ω ≤ g ω) : expect w f ≤ expect w g := by
  classical
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (density_nonneg hw ω)

omit [Fintype A] in
lemma density_split (w : E → A → ℝ) (P : E → Prop) [DecidablePred P] (ω : E → A) :
    density w ω =
      density (fun e : {e // P e} => w e) (fun e => ω e) *
      density (fun e : {e // ¬ P e} => w e) (fun e => ω e) := by
  exact (Fintype.prod_subtype_mul_prod_subtype P (fun e => w e (ω e))).symm

lemma expect_split (w : E → A → ℝ) (P : E → Prop) [DecidablePred P]
    (f : (E → A) → ℝ) :
    expect w f =
      expect (fun e : {e // P e} => w e) (fun a =>
        expect (fun e : {e // ¬ P e} => w e) (fun b =>
          f ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b)))) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => A)
  unfold expect
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro b _
  have h₁ : (fun i : {e // P e} => e.symm (a, b) i) = a :=
    congrArg Prod.fst (e.apply_symm_apply (a, b))
  have h₂ : (fun i : {e // ¬ P e} => e.symm (a, b) i) = b :=
    congrArg Prod.snd (e.apply_symm_apply (a, b))
  rw [density_split w P, h₁, h₂, mul_assoc]

lemma expect_factor (w : E → A → ℝ) (P : E → Prop) [DecidablePred P]
    (f : ({e // P e} → A) → ℝ) (g : ({e // ¬ P e} → A) → ℝ) :
    expect w (fun ω => f (fun e => ω e) * g (fun e => ω e)) =
      expect (fun e : {e // P e} => w e) f *
        expect (fun e : {e // ¬ P e} => w e) g := by
  classical
  rw [expect_split w P]
  have h₁ : ∀ (a : {e // P e} → A) (b : {e // ¬ P e} → A),
      (fun i : {e // P e} =>
        (Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b) i) = a := by
    intro a b
    exact congrArg Prod.fst ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).apply_symm_apply (a, b))
  have h₂ : ∀ (a : {e // P e} → A) (b : {e // ¬ P e} → A),
      (fun i : {e // ¬ P e} =>
        (Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b) i) = b := by
    intro a b
    exact congrArg Prod.snd ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).apply_symm_apply (a, b))
  simp_rw [h₁, h₂]
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro b _
  ring

lemma expect_indep (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (S : Set E) {f g : (E → A) → ℝ}
    (hf : DependsOn f S) (hg : DependsOn g Sᶜ) :
    expect w (fun ω => f ω * g ω) = expect w f * expect w g := by
  classical
  obtain ⟨f', rfl⟩ := dependsOn_iff_exists_comp.mp hf
  obtain ⟨g', rfl⟩ := dependsOn_iff_exists_comp.mp hg
  have hw₁ : ∀ e : S, ∑ a, w e a = 1 := fun e => hw e
  have hw₂ : ∀ e : {e // e ∉ S}, ∑ a, w e a = 1 := fun e => hw e
  have hf' : expect w (fun ω => f' (fun e => ω e)) =
      expect (fun e : S => w e) f' := by
    have h := expect_factor w (fun e => e ∈ S) f' (fun _ => 1)
    simpa only [mul_one, expect_const _ hw₂] using h
  have hg' : expect w (fun ω => g' (fun e => ω e)) =
      expect (fun e : {e // e ∉ S} => w e) g' := by
    have h := expect_factor w (fun e => e ∈ S) (fun _ => 1) g'
    simp only [one_mul, expect_const _ hw₁] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  change expect w (fun ω => f' (fun e => ω e) * g' (fun e => ω e)) =
    expect w (fun ω => f' (fun e => ω e)) * expect w (fun ω => g' (fun e => ω e))
  rw [hf', hg']
  convert expect_factor w (fun e => e ∈ S) f' g' using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma expect_mul_const (w : E → A → ℝ) (f : (E → A) → ℝ) (c : ℝ) :
    expect w (fun ω => f ω * c) = expect w f * c := by
  classical
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by ext; simp)
  intro ω _
  ring

lemma expect_partition {B : Type*} [Fintype B] [DecidableEq B] (w : E → A → ℝ)
    (r : (E → A) → B) (f : B → (E → A) → ℝ) :
    expect w (fun ω => f (r ω) ω) =
      ∑ b, expect w (fun ω => if r ω = b then f b ω else 0) := by
  classical
  simp only [expect]
  rw [Finset.sum_comm]
  apply Finset.sum_congr (by ext; simp)
  intro ω _
  rw [← Finset.mul_sum]
  simp

lemma expect_exposure {B : Type*} [Fintype B] (w : E → A → ℝ)
    (hw : ∀ e, ∑ a, w e a = 1) (r : (E → A) → B) (D : B → Set E)
    (hr : ∀ b, DependsOn (fun ω => r ω = b) (D b))
    (f : B → (E → A) → ℝ) (hf : ∀ b, DependsOn (f b) (D b)ᶜ) :
    expect w (fun ω => f (r ω) ω) =
      expect w (fun ω => expect w (f (r ω))) := by
  classical
  rw [expect_partition w r f,
    expect_partition w r (fun b _ => expect w (f b))]
  apply Finset.sum_congr (by ext; simp)
  intro b _
  have hi : DependsOn (fun ω => if r ω = b then (1 : ℝ) else 0) (D b) := by
    intro ω ω' hω
    change (if r ω = b then (1 : ℝ) else 0) = (if r ω' = b then 1 else 0)
    have hh : (r ω = b) = (r ω' = b) := hr b hω
    rw [hh]
  have hleft : (fun ω => if r ω = b then f b ω else 0) =
      (fun ω => (if r ω = b then (1 : ℝ) else 0) * f b ω) := by
    funext ω
    split_ifs <;> simp
  have hright : (fun ω => if r ω = b then expect w (f b) else 0) =
      (fun ω => (if r ω = b then (1 : ℝ) else 0) * expect w (f b)) := by
    funext ω
    split_ifs <;> simp
  rw [hleft, hright, expect_indep w hw (D b) hi (hf b), expect_mul_const]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_BitMeasure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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

namespace CriticalPercolation
namespace BernoulliProduct

lemma bitMeasure_real_singleton (p : unitInterval) (b : Prop) :
    (bitMeasure p).real {b} = bitWeight p b := by
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]

variable {E : Type*}

lemma law_const (p : unitInterval) :
    law (fun _ : E => p) = setBernoulli Set.univ p := by
  rw [law, setBernoulli_eq_map]
  rfl

lemma integral_bits_eq_expect [Fintype E] (q : E → unitInterval) (f : (E → Prop) → ℝ) :
    (∫ ω, f ω ∂(Measure.infinitePi fun e => bitMeasure (q e))) =
      FiniteProduct.expect (fun e => bitWeight (q e)) f := by
  rw [Measure.infinitePi_eq_pi, integral_fintype Integrable.of_finite]
  unfold FiniteProduct.expect FiniteProduct.density
  apply Finset.sum_congr rfl
  intro ω _
  rw [smul_eq_mul]
  congr 1
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun e _ => bitMeasure_real_singleton (q e) (ω e))

lemma integral_law_eq_expect [Fintype E] (q : E → unitInterval) (f : Set E → ℝ) :
    (∫ ω, f ω ∂law q) =
      FiniteProduct.expect (fun e => bitWeight (q e)) (fun ω => f {e | ω e}) := by
  rw [law, integral_map MeasurableEquiv.setOfPred.measurable.aemeasurable
    Integrable.of_finite.aestronglyMeasurable, integral_bits_eq_expect]
  rfl

lemma law_map_restrict (q : E → unitInterval) (s : Set E) :
    (law q).map (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set s) =
      law (fun e : s => q e) := by
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    measurable_set_iff.mpr (fun bond => measurable_set_mem bond.val)
  unfold law
  rw [Measure.map_map hmeas MeasurableEquiv.setOfPred.measurable]
  have hcomp : (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set s) ∘
      MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ s.domRestrict := rfl
  rw [hcomp, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_restrict']

end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Distribution
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

lemma expect_zero (w : E → A → ℝ) : expect w (fun _ => 0) = 0 := by
  simp [expect]

lemma expect_sum {J : Type*} [Fintype J] (w : E → A → ℝ)
    (f : J → (E → A) → ℝ) :
    expect w (fun ω => ∑ j, f j ω) = ∑ j, expect w (f j) := by
  classical
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma expect_const_mul (w : E → A → ℝ) (c : ℝ) (f : (E → A) → ℝ) :
    expect w (fun ω => c * f ω) = c * expect w f := by
  simp only [mul_comm c]
  exact expect_mul_const w f c
end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_Weight
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule0

noncomputable section
open Set
open scoped BigOperators Classical

namespace CriticalPercolation.Sharpness
open FiniteProduct

variable {E A : Type*} [Fintype E]

lemma weight_sum (p : ℝ) : ∑ b, weight p b = 1 := by
  simp [weight]

lemma weight_nonneg {p : ℝ} (hp : p ∈ Icc 0 1) (b : Prop) :
    0 ≤ weight p b := by
  by_cases h : b <;> simp [weight, h, hp.1, hp.2]

lemma hasDerivAt_weight (p : ℝ) (b : Prop) :
    HasDerivAt (fun q => weight q b) (if b then 1 else -1) p := by
  by_cases hb : b
  · convert hasDerivAt_id' p using 1 <;> first | rfl | simp [weight, hb]
  · convert (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id' p) using 1 <;>
      first | rfl | (simp only [weight, ite_eq_right hb]; first | rfl | norm_num)

lemma hasDerivAt_density (p : ℝ) (ω : E → Prop) :
    HasDerivAt (fun q => density (fun _ : E => weight q) ω)
      (∑ e, (∏ j ∈ Finset.univ.erase e, weight p (ω j)) *
        (if ω e then 1 else -1)) p := by
  simpa only [density, smul_eq_mul] using
    HasDerivAt.fun_finsetProd (u := Finset.univ)
      (fun (e : E) _ => hasDerivAt_weight p (ω e))

lemma density_score {p : ℝ} (hp : p ∈ Ioo 0 1) (ω : E → Prop) (e : E) :
    (∏ j ∈ Finset.univ.erase e, weight p (ω j)) * (if ω e then 1 else -1) =
      density (fun _ : E => weight p) ω *
        (if ω e then p⁻¹ else -(1-p)⁻¹) := by
  unfold density
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ e)]
  have hp0 : p ≠ 0 := hp.1.ne'
  have hp1 : 1-p ≠ 0 := (sub_pos.mpr hp.2).ne'
  by_cases he : ω e <;> simp [weight, he, hp0, hp1]

lemma hasDerivAt_expect_score {p : ℝ} (hp : p ∈ Ioo 0 1) (f : (E → Prop) → ℝ) :
    HasDerivAt (fun q => expect (fun _ : E => weight q) f)
      (∑ e, expect (fun _ : E => weight p)
        (fun ω => (if ω e then p⁻¹ else -(1-p)⁻¹) * f ω)) p := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun (ω : E → Prop) _ => (hasDerivAt_density p ω).mul_const (f ω))
  convert hd using 1 <;> try rfl
  simp only [expect, Finset.sum_mul, density_score hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma expect_eval_indicator [Fintype A] (w : E → A → ℝ)
    (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) :
    expect w (fun ω => if ω e = b then 1 else 0) = w e b := by
  have hi (ω : E → A) : (if ω e = b then (1:ℝ) else 0) =
      ∏ j, (if j = e then if ω j = b then 1 else 0 else 1) := by simp
  simp only [expect, hi, density, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j a => w j a * (if j = e then if a = b then 1 else 0 else 1))]
  have hs (j : E) :
      (∑ a, w j a * (if j = e then if a = b then 1 else 0 else 1)) =
        if j = e then w e b else 1 := by
    split_ifs with he
    · subst j; simp
    · simp [hw]
  simp only [hs]
  simp

lemma expect_coordinate_mask [Fintype A] (w : E → A → ℝ)
    (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) =
      w e b * expect w (fun ω => f (Function.update ω e b)) := by
  have hid : (fun ω => if ω e = b then f ω else 0) =
      (fun ω => (if ω e = b then (1:ℝ) else 0)*f (Function.update ω e b)) := by
    funext ω
    split_ifs with h
    · have hu : Function.update ω e b = ω := by
        rw [← h]; exact Function.update_eq_self _ _
      simp [hu]
    · simp
  rw [hid]
  have hI : DependsOn (fun ω : E → A => if ω e = b then (1:ℝ) else 0) ({e} : Set E) := by
    intro ω ω' heq
    dsimp only
    rw [heq e (Set.mem_singleton e)]
  have hF : DependsOn (fun ω => f (Function.update ω e b)) ({e} : Set E)ᶜ := by
    intro ω ω' heq
    change f (Function.update ω e b) = f (Function.update ω' e b)
    congr 1
    funext j
    by_cases hj : j = e
    · subst j; simp
    · simp only [Function.update_of_ne hj]
      exact heq j hj
  rw [expect_indep w hw _ hI hF]
  congr 1
  exact expect_eval_indicator w hw e b

lemma score_eq_difference {p : ℝ} (hp : p ∈ Ioo 0 1) (e : E) (f : (E → Prop) → ℝ) :
    expect (fun _ : E => weight p)
      (fun ω => (if ω e then p⁻¹ else -(1-p)⁻¹) * f ω) =
    expect (fun _ : E => weight p) (fun ω => f (Function.update ω e True)) -
      expect (fun _ : E => weight p) (fun ω => f (Function.update ω e False)) := by
  have he : (fun ω => (if ω e then p⁻¹ else -(1-p)⁻¹) * f ω) =
      (fun ω => (if ω e = True then f ω else 0) * p⁻¹ -
        (if ω e = False then f ω else 0) * (1-p)⁻¹) := by
    funext ω
    by_cases h : ω e <;> simp [h, mul_comm]
  rw [he, expect_sub, expect_mul_const, expect_mul_const]
  have h1 : expect (fun _ : E => weight p)
      (fun ω => if ω e = True then f ω else 0) =
      p * expect (fun _ : E => weight p) (fun ω => f (Function.update ω e True)) := by
    convert expect_coordinate_mask (fun _ : E => weight p) (fun _ => weight_sum p) e True f using 1 <;>
      first | (congr 1; funext ω; split_ifs <;> rfl) | simp [weight]
  have h0 : expect (fun _ : E => weight p)
      (fun ω => if ω e = False then f ω else 0) =
      (1-p) * expect (fun _ : E => weight p) (fun ω => f (Function.update ω e False)) := by
    convert expect_coordinate_mask (fun _ : E => weight p) (fun _ => weight_sum p) e False f using 1 <;>
      first | (congr 1; funext ω; split_ifs <;> rfl) | simp [weight]
  rw [h1, h0]
  have hp0 := hp.1.ne'
  have hp1 := (sub_pos.mpr hp.2).ne'
  field_simp

theorem hasDerivAt_expect {p : ℝ} (hp : p ∈ Ioo 0 1) (f : (E → Prop) → ℝ) :
    HasDerivAt (fun q => expect (fun _ : E => weight q) f)
      (∑ e, expect (fun _ : E => weight p)
        (fun ω => f (Function.update ω e True) - f (Function.update ω e False))) p := by
  have hd := hasDerivAt_expect_score hp f
  simpa only [score_eq_difference hp, expect_sub] using hd

omit [Fintype E] in
lemma force_false_subset_true (ω : Set E) (e : E) :
    Set.Subset (Function.update ω e False) (Function.update ω e True) := by
  intro j hj
  change Function.update ω e True j
  change Function.update ω e False j at hj
  by_cases h : j=e
  · subst j; exact of_eq_true (Function.update_self e True ω)
  · erw [Function.update_of_ne h] at hj ⊢
    exact hj

omit [Fintype E] in
lemma indicator_difference (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (e : E) (ω : Set E) :
    (if F (Function.update ω e True) then (1:ℝ) else 0) -
        (if F (Function.update ω e False) then 1 else 0) =
      if pivotal F e ω then 1 else 0 := by
  have hm := hF _ _ (force_false_subset_true ω e)
  by_cases h1 : F (Function.update ω e True) <;>
    by_cases h0 : F (Function.update ω e False) <;> simp_all [pivotal]

theorem hasDerivAt_probability {p : ℝ} (hp : p ∈ Ioo 0 1)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    HasDerivAt (fun q => probability q F) (∑ e, probability p (pivotal F e)) p := by
  have hd := hasDerivAt_expect hp (fun ω => if F ω then (1:ℝ) else 0)
  convert hd using 1 <;> try rfl
  apply Finset.sum_congr rfl
  intro e _
  unfold probability
  congr 1
  funext ω
  exact (indicator_difference F hF e ω).symm

omit [Fintype E] in
lemma closedPivot_iff (F : Set E → Prop) (e : E) (ω : Set E) :
    closedPivot F e ω ↔ ω e = False ∧ pivotal F e ω := by
  have hh : ¬ω e → Function.update ω e False = ω := by
    intro h
    have he : ω e = False := propext (iff_false_intro h)
    rw [← he]
    exact Function.update_eq_self _ _
  by_cases h : ω e
  · simp [closedPivot, h]
  · simp [closedPivot, pivotal, h, hh h, and_comm]

lemma probability_closedPivot (p : ℝ) (F : Set E → Prop) (e : E) :
    probability p (closedPivot F e) = (1-p) * probability p (pivotal F e) := by
  have he : (fun ω : E → Prop => if closedPivot F e ω then (1:ℝ) else 0) =
      (fun ω => if ω e = False then (if pivotal F e ω then 1 else 0) else 0) := by
    funext ω
    erw [closedPivot_iff]
    split_ifs <;> tauto
  unfold probability
  rw [he]
  have hm : expect (fun _ : E => weight p)
      (fun ω => if ω e = False then (if pivotal F e ω then 1 else 0) else 0) =
      (1-p)*expect (fun _ : E => weight p)
        (fun ω => if pivotal F e (Function.update ω e False) then 1 else 0) := by
    convert expect_coordinate_mask (fun _ : E => weight p) (fun _ => weight_sum p)
      e False (fun ω => if pivotal F e ω then 1 else 0) using 1 <;>
      first | (congr 1; funext ω; split_ifs <;> rfl) | simp [weight]
  calc
    _ = (1-p)*expect (fun _ : E => weight p)
        (fun ω => if pivotal F e (Function.update ω e False) then 1 else 0) := by
      convert hm using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
    _ = _ := by
      congr 1
      congr 1
      funext ω
      simp only [pivotal, Function.update_idem]
      congr 1

theorem hasDerivAt_probability_closedPivot {p : ℝ} (hp : p ∈ Ioo 0 1)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    HasDerivAt (fun q => probability q F)
      ((∑ e, probability p (closedPivot F e)) / (1-p)) p := by
  have hd := hasDerivAt_probability hp F hF
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [probability_closedPivot, ← Finset.mul_sum]
  exact mul_div_cancel_left₀ _ (sub_pos.mpr hp.2).ne'

lemma probability_nonneg {p : ℝ} (hp : p ∈ Icc 0 1) (F : Set E → Prop) :
    0 ≤ probability p F := by
  have h := expect_mono (w := fun _ : E => weight p)
    (fun _ b => weight_nonneg hp b)
    (f := fun _ => 0) (g := fun ω => if F ω then 1 else 0)
    (fun _ => by split_ifs <;> norm_num)
  simpa only [expect_const _ (fun _ => weight_sum p) 0, probability] using h

lemma probability_le_one {p : ℝ} (hp : p ∈ Icc 0 1) (F : Set E → Prop) :
    probability p F ≤ 1 := by
  have h := expect_mono (w := fun _ : E => weight p)
    (fun _ b => weight_nonneg hp b)
    (f := fun ω => if F ω then 1 else 0) (g := fun _ => 1)
    (fun _ => by split_ifs <;> norm_num)
  simpa only [expect_const _ (fun _ => weight_sum p) 1, probability] using h

end CriticalPercolation.Sharpness
end
end CurrentModule0

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_HitEvent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

lemma hitEvent_mono_target (o : V) {A A' : Set V} (h : A ⊆ A') :
    G.hitEvent o A ⊆ G.hitEvent o A' :=
  fun _ hω => hω.mono (Set.inter_subset_inter_right _ h)

lemma restrictEdges_openGraph (s : Set E) (ω : Set E) :
    (G.restrictEdges s).openGraph (Subtype.val ⁻¹' ω) = G.openGraph (s ∩ ω) := by
  unfold openGraph restrictEdges
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Subtype.exists]
  constructor
  · rintro ⟨e, hs, hω, rfl⟩
    exact ⟨e, ⟨hs, hω⟩, rfl⟩
  · rintro ⟨e, ⟨hs, hω⟩, rfl⟩
    exact ⟨e, hs, hω, rfl⟩

lemma finite_subset_exhaustion {X : Type*} {U S : Set X}
    (K : Set.FiniteExhaustion U) (hS : S.Finite) (hSU : S ⊆ U) :
    ∃ n, S ⊆ K n := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨0, Set.empty_subset _⟩
  | @insert x S hx hS ih =>
      obtain ⟨n, hn⟩ := ih (Set.Subset.trans (Set.subset_insert _ _) hSU)
      have hxU := hSU (Set.mem_insert x S)
      rw [← K.iUnion_eq, Set.mem_iUnion] at hxU
      obtain ⟨m, hm⟩ := hxU
      exact ⟨max m n, Set.insert_subset (K.mono (le_max_left _ _) hm)
        (Set.Subset.trans hn (K.mono (le_max_right _ _)))⟩

lemma hitEvent_exhaustion (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o A}) = G.hitEvent o A := by
  ext ω
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact G.hitEvent_mono_edges o A Set.inter_subset_right hn
  · rintro ⟨v, hv, hvA⟩
    obtain ⟨s, hs, hsω, hvs⟩ := G.mem_cluster_finite_witness hv
    obtain ⟨n, hn⟩ := finite_subset_exhaustion K hs (Set.subset_univ s)
    exact Set.mem_iUnion.mpr ⟨n, v, G.cluster_mono
      (Set.subset_inter hn hsω) o hvs, hvA⟩

lemma hitEvent_exhaustion_mono (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    Monotone (fun n => {ω | K n ∩ ω ∈ G.hitEvent o A}) := by
  intro m n h ω hω
  exact G.hitEvent_mono_edges o A (Set.inter_subset_inter_left _ (K.mono h)) hω

lemma tendsto_real_hitEvent_exhaustion [Countable E]
    (q : E → unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    Tendsto (fun n => (BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent o A})
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A))) := by
  have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q)
    (G.hitEvent_exhaustion_mono K o A)
  rw [G.hitEvent_exhaustion K o A] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_Link2
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule1
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
namespace Wiring
variable {V : Type*} (H : SimpleGraph V)

lemma link_refl (s b u : V) : link H s b u u := Or.inl (.refl _)

lemma link_trans {s b u v z : V} : link H s b u v → link H s b v z → link H s b u z := by
  rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩) (k | ⟨k1,k2⟩ | ⟨k1,k2⟩)
  · exact Or.inl (h.trans k)
  · exact Or.inr (Or.inl ⟨h.trans k1,k2⟩)
  · exact Or.inr (Or.inr ⟨h.trans k1,k2⟩)
  · exact Or.inr (Or.inl ⟨h1,h2.trans k⟩)
  · exact Or.inr (Or.inl ⟨h1,k2⟩)
  · exact Or.inl (h1.trans k2)
  · exact Or.inr (Or.inr ⟨h1,h2.trans k⟩)
  · exact Or.inl (h1.trans k2)
  · exact Or.inr (Or.inr ⟨h1,k2⟩)

lemma edge_reachable (s b : V) : (SimpleGraph.edge s b).Reachable s b := by
  rcases eq_or_ne s b with rfl | h
  · exact .refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,h⟩)

theorem reachable_sup_edge (s b u v : V) :
    (H ⊔ SimpleGraph.edge s b).Reachable u v ↔ link H s b u v := by
  constructor
  · intro h
    have h' := ((H ⊔ SimpleGraph.edge s b).reachable_iff_reflTransGen u v).mp h
    clear h
    induction h' with
    | refl => exact link_refl H s b u
    | @tail z v _ hz ih =>
      apply link_trans H ih
      rcases hz with hz | hz
      · exact Or.inl hz.reachable
      · rcases ((SimpleGraph.edge_adj _ _ _ _).mp hz).1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr (Or.inl ⟨.refl _,.refl _⟩)
        · exact Or.inr (Or.inr ⟨.refl _,.refl _⟩)
  · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
    · exact h.mono le_sup_left
    · exact (h1.mono le_sup_left).trans ((edge_reachable s b).mono le_sup_right |>.trans
        (h2.mono le_sup_left))
    · exact (h1.mono le_sup_left).trans ((edge_reachable s b).symm.mono le_sup_right |>.trans
        (h2.mono le_sup_left))

end Wiring

open ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

lemma reachesTarget_mono (o : V) (T : Set V) {ω ω' : Set E}
    (h : ω ⊆ ω') : reachesTarget G o T ω → reachesTarget G o T ω' :=
  fun ho => roots_mono (G.openGraph_mono h) T ho

lemma reachesTarget_iff_hitEvent (o : V) (T : Set V) (ω : Set E) :
    reachesTarget G o T ω ↔ ω ∈ G.hitEvent o T := by
  constructor
  · rintro ⟨t, ht, hto⟩
    exact ⟨t, hto.symm, ht⟩
  · rintro ⟨t, hot, ht⟩
    exact ⟨t, ht, hot.symm⟩

lemma openGraph_force_true (ω : Set E) (e : E) (v b : V)
    (he : G.ends e = s(v,b)) :
    G.openGraph (Function.update ω e True) = G.openGraph ω ⊔ SimpleGraph.edge v b := by
  have hs : (Function.update ω e True : Set E) = insert e ω := by
    ext j
    by_cases hje : j = e
    · subst j; erw [Function.update_self]; exact iff_of_true trivial (Set.mem_insert e ω)
    · erw [Function.update_of_ne hje]
      change j ∈ ω ↔ j ∈ insert e ω
      simp [hje]
  erw [hs]
  rw [BondGraph.openGraph,Set.image_insert_eq,he,← Set.singleton_union,SimpleGraph.fromEdgeSet_union]
  exact sup_comm _ _

lemma target_creating_iff (o : V) (T : Set V) (ω : Set E) (e : E)
    (ho : ¬ reachesTarget G o T ω) :
    reachesTarget G o T (Function.update ω e True) ↔
      boundaryReach G (roots (G.openGraph ω) T)
        (delete (G.openGraph ω) (roots (G.openGraph ω) T)) o e := by
  let H := G.openGraph ω
  let R := roots H T
  have hor : o ∉ R := ho
  have hdel : component (delete H R) o = component H o :=
    delete_roots_component H T o hor
  constructor
  · intro hn
    obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective (G.ends e)
    have he : G.ends e = s(a,b) := hab.symm
    obtain ⟨t,ht,hnew⟩ := hn
    rw [openGraph_force_true G ω e a b he] at hnew
    have hh := (Wiring.reachable_sup_edge H a b o t).mp hnew.symm
    rcases hh with hold | ⟨hoa,hbt⟩ | ⟨hob,hat⟩
    · exact (ho ⟨t,ht,hold.symm⟩).elim
    · refine ⟨a,b,he,reachable_not_mem_roots hor hoa,⟨t,ht,hbt.symm⟩,?_⟩
      change a ∈ component (delete H R) o
      rw [hdel]
      exact hoa
    · refine ⟨b,a,?_,reachable_not_mem_roots hor hob,⟨t,ht,hat.symm⟩,?_⟩
      · simpa only [Sym2.eq_swap] using he
      · change b ∈ component (delete H R) o
        rw [hdel]
        exact hob
  · rintro ⟨x,y,he,hx,⟨t,ht,hty⟩,hox⟩
    refine ⟨t,ht,?_⟩
    rw [openGraph_force_true G ω e x y he]
    apply SimpleGraph.Reachable.symm
    apply (Wiring.reachable_sup_edge (G.openGraph ω) x y o t).mpr
    exact Or.inr (Or.inl ⟨hox.mono (delete_le _ _),hty.symm⟩)

lemma boundaryReach_closed (o : V) (T : Set V) (ω : Set E) (e : E)
    (h : boundaryReach G (roots (G.openGraph ω) T)
      (delete (G.openGraph ω) (roots (G.openGraph ω) T)) o e) : ¬ ω e := by
  rintro heω
  obtain ⟨x,y,he,hx,hy,_⟩ := h
  have hxy : x ≠ y := fun heq => hx (heq ▸ hy)
  have ha : (G.openGraph ω).Adj y x := by
    apply SimpleGraph.Adj.symm
    exact ⟨⟨e,heω,he⟩,hxy⟩
  exact hx (roots_closed hy ha)

end CriticalPercolation.Sharpness
end
end CurrentModule1

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BoundaryCount
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule2
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open FiniteProduct ClusterDeletion

lemma expect_exposure_finiteRange {I A B : Type*} [Fintype I] [Fintype A]
    (w : I → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (r : (I → A) → B) (D : B → Set I)
    (hr : ∀ b, DependsOn (fun ω => r ω = b) (D b))
    (f : B → (I → A) → ℝ) (hf : ∀ b, DependsOn (f b) (D b)ᶜ) :
    expect w (fun ω => f (r ω) ω) =
      expect w (fun ω => expect w (f (r ω))) := by
  let : Fintype (Set.range r) := (Set.finite_range r).fintype
  let r' : (I → A) → Set.range r := fun ω => ⟨r ω,ω,rfl⟩
  exact expect_exposure w hw r' (fun b => D b.val)
    (fun b ω ω' hω => by
      apply propext
      simpa only [r',Subtype.ext_iff] using (hr b.val hω).to_iff)
    (fun b => f b.val) (fun b => hf b.val)

variable {V E : Type*} [Fintype E] (G : BondGraph V E)

lemma spatialMarkov (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (T : Set V) (F : Set V → SimpleGraph V → ℝ) :
    expect w (fun ω => F (roots (G.openGraph ω) T)
        (delete (G.openGraph ω) (roots (G.openGraph ω) T))) =
      expect w (fun ω => expect w (fun ω' => F (roots (G.openGraph ω) T)
        (delete (G.openGraph ω') (roots (G.openGraph ω) T)))) := by
  refine expect_exposure_finiteRange w hw
    (fun ω => roots (G.openGraph ω) T) G.incidentEdges
    (G.dependsOn_exact_roots T)
    (fun R ω => F R (delete (G.openGraph ω) R)) ?_
  intro R ω ω' hω
  exact congrArg (F R) (G.delete_openGraph_dependsOn R hω)

omit [Fintype E] in
lemma closedPivot_reachesTarget (o : V) (T : Set V) (ω : Set E) (e : E) :
    closedPivot (reachesTarget G o T) e ω ↔
      o ∉ roots (G.openGraph ω) T ∧
      boundaryReach G (roots (G.openGraph ω) T)
        (delete (G.openGraph ω) (roots (G.openGraph ω) T)) o e := by
  constructor
  · rintro ⟨_,ho,he⟩
    exact ⟨ho,(target_creating_iff G o T ω e ho).mp he⟩
  · rintro ⟨ho,he⟩
    exact ⟨boundaryReach_closed G o T ω e he,ho,
      (target_creating_iff G o T ω e ho).mpr he⟩

lemma sum_closedPivot_eq (p : ℝ) (o : V) (T : Set V) :
    ∑ e, probability p (closedPivot (reachesTarget G o T) e) =
      expect (fun _ : E => weight p) (fun ω =>
        if o ∉ roots (G.openGraph ω) T then
          expect (fun _ : E => weight p) (fun ω' => boundaryCount G o
            (roots (G.openGraph ω) T)
            (delete (G.openGraph ω') (roots (G.openGraph ω) T))) else 0) := by
  have hs := spatialMarkov G (fun _ : E => weight p) (fun _ => weight_sum p)
    T (fun R H => if o ∉ R then boundaryCount G o R H else 0)
  unfold probability
  rw [← expect_sum]
  calc
    _ = expect (fun _ : E => weight p) (fun ω =>
        if o ∉ roots (G.openGraph ω) T then
          boundaryCount G o (roots (G.openGraph ω) T)
            (delete (G.openGraph ω) (roots (G.openGraph ω) T)) else 0) := by
      congr 1
      funext ω
      have he (e : E) : closedPivot (reachesTarget G o T) e ω ↔
          o ∉ roots (G.openGraph ω) T ∧ boundaryReach G (roots (G.openGraph ω) T)
            (delete (G.openGraph ω) (roots (G.openGraph ω) T)) o e :=
        closedPivot_reachesTarget G o T ω e
      simp only [he]
      by_cases ho : o ∈ roots (G.openGraph ω) T
      · simp [ho]
      · simp [ho,boundaryCount]
    _ = _ := by
      rw [hs]
      congr 1
      funext ω
      split_ifs <;> simp only [expect_zero]

lemma exposedFlux_identity (p : ℝ) (o : V) (T : Set V) :
    p * (∑ e, probability p (closedPivot (reachesTarget G o T) e)) =
      expect (fun _ : E => weight p) (fun ω =>
        if o ∉ roots (G.openGraph ω) T then
          boundaryFlux G p o (roots (G.openGraph ω) T) else 0) := by
  rw [sum_closedPivot_eq, ← expect_const_mul]
  congr 1
  funext ω
  split_ifs <;> simp only [boundaryFlux,mul_zero]

theorem derivative_identity {p : ℝ} (hp : p ∈ Ioo 0 1) (o : V) (T : Set V) :
    p * (1-p) * deriv (fun q => probability q (reachesTarget G o T)) p =
      expect (fun _ : E => weight p) (fun ω =>
        if o ∉ roots (G.openGraph ω) T then
          boundaryFlux G p o (roots (G.openGraph ω) T) else 0) := by
  have hd := hasDerivAt_probability_closedPivot hp (reachesTarget G o T)
    (fun _ _ h => reachesTarget_mono G o T h)
  rw [hd.deriv, ← exposedFlux_identity]
  field_simp [(sub_pos.mpr hp.2).ne']

theorem differential_inequality {p a : ℝ} (hp : p ∈ Ioo 0 1) (o : V) (T : Set V)
    (hflux : ∀ R : Set V, T ⊆ R → o ∉ R → a ≤ boundaryFlux G p o R) :
    a * (1-probability p (reachesTarget G o T)) ≤
      p * (1-p) * deriv (fun q => probability q (reachesTarget G o T)) p := by
  rw [derivative_identity G hp o T]
  have hcomp : expect (fun _ : E => weight p)
      (fun ω => if o ∉ roots (G.openGraph ω) T then (1:ℝ) else 0) =
      1-probability p (reachesTarget G o T) := by
    calc
      _ = expect (fun _ : E => weight p) (fun ω =>
          1-(if reachesTarget G o T ω then (1:ℝ) else 0)) := by
        congr 1
        funext ω
        unfold reachesTarget
        by_cases ho : o ∈ roots (G.openGraph ω) T <;> simp [ho]
      _ = _ := by
        rw [expect_sub,expect_const _ (fun _ => weight_sum p)]
        rfl
  rw [← hcomp, ← expect_const_mul]
  apply expect_mono (fun _ b => weight_nonneg ⟨hp.1.le,hp.2.le⟩ b)
  intro ω
  by_cases ho : o ∈ roots (G.openGraph ω) T
  · simp [ho]
  · simp only [ho,not_false_eq_true,if_true,mul_one]
    exact hflux (roots (G.openGraph ω) T) (roots_self _ _) ho

end CriticalPercolation.Sharpness
end
end CurrentModule2

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_CutInside
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule3
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

lemma cut_ends (S : Set V) (e : E) :
    G.ends e = s(cutInside G S e, cutOutside G S e) := by
  unfold cutInside cutOutside
  split_ifs
  · exact (G.ends e).out_eq.symm
  · exact (G.ends e).out_eq.symm.trans (Sym2.eq_swap)

lemma cut_orientation {S : Set V} {e : E} {x y : V}
    (he : G.ends e = s(x,y)) (hx : x ∈ S) (hy : y ∉ S) :
    cutInside G S e = x ∧ cutOutside G S e = y := by
  have h : s((G.ends e).out.1,(G.ends e).out.2) = s(x,y) := (G.ends e).out_eq.trans he
  rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · change (G.ends e).out.1 = x at h1
    change (G.ends e).out.2 = y at h2
    simp only [cutInside,cutOutside,h1,h2,ite_eq_left hx,and_self]
  · change (G.ends e).out.1 = y at h1
    change (G.ends e).out.2 = x at h2
    simp only [cutInside,cutOutside,h1,h2,ite_eq_right hy,and_self]

lemma boundaryReach_iff_cut (S : Set V) (H : SimpleGraph V) (o : V) (e : E) :
    boundaryReach G Sᶜ H o e ↔ IsCut G S e ∧ H.Reachable o (cutInside G S e) := by
  constructor
  · rintro ⟨x,y,he,hx,hy,hr⟩
    change y ∉ S at hy
    have hh := cut_orientation G he (not_not.mp hx) hy
    exact ⟨by simpa only [IsCut,hh.1,hh.2] using And.intro (not_not.mp hx) hy,
      by simpa only [hh.1] using hr⟩
  · rintro ⟨hc,hr⟩
    exact ⟨_,_,cut_ends G S e,not_not.mpr hc.1,hc.2,hr⟩

lemma internalCluster_self (S : Set V) (o : V) (ω : Set E) :
    o ∈ internalCluster G S o ω := .refl _

lemma internalCluster_subset (S : Set V) {o : V} (ho : o ∈ S) (ω : Set E) :
    internalCluster G S o ω ⊆ S := by
  intro v hv
  exact reachable_mem_of_closed (H := delete (G.openGraph ω) Sᶜ)
    (U := S) (fun {_ _} _ h => not_not.mp h.2.2) ho hv

lemma internal_adj_eq {S C : Set V} {ω ω' : Set E}
    (hω : ∀ e ∈ internalIncident G S C, e ∈ ω ↔ e ∈ ω') {x y : V} (hx : x ∈ C) :
    (delete (G.openGraph ω) Sᶜ).Adj x y ↔ (delete (G.openGraph ω') Sᶜ).Adj x y := by
  have hh (e) (he : G.ends e = s(x,y)) (hxS : x ∈ S) (hyS : y ∈ S) :
      e ∈ internalIncident G S C := by
    refine ⟨⟨x,hx,by rw [he]; simp⟩,?_⟩
    intro v hv
    rw [he,Sym2.mem_iff] at hv
    rcases hv with rfl | rfl <;> assumption
  constructor
  · rintro ⟨⟨⟨e,he,hend⟩,hne⟩,hxs,hys⟩
    exact ⟨⟨⟨e,(hω e (hh e hend (not_not.mp hxs) (not_not.mp hys))).mp he,hend⟩,hne⟩,hxs,hys⟩
  · rintro ⟨⟨⟨e,he,hend⟩,hne⟩,hxs,hys⟩
    exact ⟨⟨⟨e,(hω e (hh e hend (not_not.mp hxs) (not_not.mp hys))).mpr he,hend⟩,hne⟩,hxs,hys⟩

lemma internalCluster_eq_of_incident {S C : Set V} {o : V} {ω ω' : Set E}
    (hC : internalCluster G S o ω = C)
    (hω : ∀ e ∈ internalIncident G S C, e ∈ ω ↔ e ∈ ω') :
    internalCluster G S o ω' = C := by
  change component (delete (G.openGraph ω') Sᶜ) o = C
  rw [← roots_singleton]
  exact roots_eq_of_adj_eq_incident
    (by simpa only [roots_singleton, internalCluster] using hC)
    (fun {_ _} hx => internal_adj_eq G hω hx)

lemma dependsOn_internalCluster (S C : Set V) (o : V) :
    DependsOn (fun ω : Set E => internalCluster G S o ω = C) (internalIncident G S C) := by
  intro ω ω' hω
  apply propext
  exact ⟨fun h => internalCluster_eq_of_incident G h (fun e he => (hω e he).to_iff),
    fun h => internalCluster_eq_of_incident G h (fun e he => (hω e he).symm.to_iff)⟩

lemma last_exit {H : SimpleGraph V} {C : Set V} {o v : V}
    (ho : o ∈ C) (hv : v ∉ C) (hr : H.Reachable o v) :
    ∃ x ∈ C, ∃ y ∉ C, H.Adj x y ∧ (delete H C).Reachable y v := by
  have hh : ∀ z, H.Reachable v z →
      (z ∉ C ∧ (delete H C).Reachable v z) ∨
        ∃ x ∈ C, ∃ y ∉ C, H.Adj x y ∧ (delete H C).Reachable y v := by
    intro z hz
    rw [SimpleGraph.reachable_iff_reflTransGen] at hz
    induction hz with
    | refl => exact Or.inl ⟨hv,.refl _⟩
    | @tail a b _ hab ih =>
      rcases ih with ⟨ha,hva⟩ | ih
      · by_cases hb : b ∈ C
        · exact Or.inr ⟨b,hb,a,ha,hab.symm,hva.symm⟩
        · exact Or.inl ⟨hb,hva.trans (SimpleGraph.Adj.reachable ⟨hab,ha,hb⟩)⟩
      · exact Or.inr ih
  exact (hh o hr.symm).resolve_left (fun h => h.1 ho)

lemma internalCluster_exit (S : Set V) (o : V) (ho : o ∈ S) (ω : Set E) {v : V}
    (hv : v ∉ S) (hr : (G.openGraph ω).Reachable o v) :
    ∃ e : E, IsCut G S e ∧ cutInside G S e ∈ internalCluster G S o ω ∧ e ∈ ω ∧
      (delete (G.openGraph ω) (internalCluster G S o ω)).Reachable (cutOutside G S e) v := by
  obtain ⟨x,hx,y,hy,hxy,hyv⟩ := last_exit (internalCluster_self G S o ω)
    (fun hc => hv (internalCluster_subset G S ho ω hc)) hr
  have hxS : x ∈ S := internalCluster_subset G S ho ω hx
  have hyS : y ∉ S := by
    intro hyS
    exact hy (hx.trans (SimpleGraph.Adj.reachable ⟨hxy,not_not.mpr hxS,not_not.mpr hyS⟩))
  obtain ⟨⟨e,he,hend⟩,_hne⟩ := hxy
  obtain ⟨hi,ho'⟩ := cut_orientation G hend hxS hyS
  exact ⟨e,by simpa only [IsCut,hi,ho'] using And.intro hxS hyS,
    by rwa [hi],he,by rwa [ho']⟩

lemma cut_not_internalIncident {S C : Set V} {e : E} (hc : IsCut G S e) :
    e ∉ internalIncident G S C := by
  intro h
  apply hc.2
  apply h.2
  rw [cut_ends G S e]
  simp

lemma delete_update_incident {C : Set V} {e : E} (he : e ∈ G.incidentEdges C)
    (ω : Set E) (b : Prop) :
    delete (G.openGraph (Function.update ω e b)) C = delete (G.openGraph ω) C := by
  apply G.delete_openGraph_dependsOn C
  intro j hj
  have hje : j ≠ e := by rintro rfl; exact hj he
  exact Function.update_of_ne hje _ _

end CriticalPercolation.Sharpness
end
end CurrentModule3

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OpenGraphIso
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma measurable_image_equiv (e : E ≃ E) :
    Measurable (fun ω : Set E => e '' ω) := by
  have he : (fun ω : Set E => e '' ω) = (fun ω => e.symm ⁻¹' ω) := by
    funext ω
    ext i
    simp
  rw [he]
  exact Measurable.of_eval (fun index => measurable_set_mem (e.symm index))

lemma law_map_equiv (p : unitInterval) (e : E ≃ E) :
    (law (fun _ : E => p)).map (fun ω : Set E => e '' ω) = law (fun _ : E => p) := by
  unfold law
  rw [Measure.map_map (measurable_image_equiv e) MeasurableEquiv.setOfPred.measurable]
  have he : (fun ω : Set E => e '' ω) ∘ MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ MeasurableEquiv.piCongrLeft (fun _ : E => Prop) e := by
    funext ω
    ext i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [he, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_piCongrLeft (fun _ : E => bitMeasure p) e]

end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma law_map_aut (p : unitInterval) (φ : G.Aut) :
    (G.law p).map (fun ω : Set E => φ.edge '' ω) = G.law p := by
  simpa only [BernoulliProduct.law_const, law] using
    BernoulliProduct.law_map_equiv p φ.edge

end CriticalPercolation.BondGraph

open Filter Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ContinuousProbability
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule5
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open FiniteProduct ClusterDeletion

variable {E V : Type*} [Fintype E]

lemma continuous_probability (F : Set E → Prop) :
    Continuous (fun p : ℝ => probability p F) := by
  unfold probability expect
  apply continuous_finsetSum
  intro ω _
  apply Continuous.mul _ continuous_const
  exact continuous_iff_continuousAt.mpr (fun p => (hasDerivAt_density p ω).continuousAt)

lemma probability_monotoneOn (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) :
    MonotoneOn (fun p : ℝ => probability p F) (Icc 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    (continuous_probability F).continuousOn
  · intro p hp
    rw [interior_Icc] at hp
    exact (hasDerivAt_probability hp F hF).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    rw [(hasDerivAt_probability hp F hF).deriv]
    exact Finset.sum_nonneg fun e _ => probability_nonneg ⟨hp.1.le,hp.2.le⟩ _

variable (G : BondGraph V E)

omit [Fintype E] in
lemma boundary_event_mono (o : V) (R : Set V) (e : E) {ω ω' : Set E}
    (h : ω ⊆ ω') :
    boundaryReach G R (delete (G.openGraph ω) R) o e →
      boundaryReach G R (delete (G.openGraph ω') R) o e := by
  rintro ⟨x,y,he,hx,hy,hox⟩
  have hdel : delete (G.openGraph ω) R ≤ delete (G.openGraph ω') R := by
    intro a b hh
    exact ⟨G.openGraph_mono h hh.1,hh.2⟩
  exact ⟨x,y,he,hx,hy,hox.mono hdel⟩

lemma boundaryFlux_eq_sum (p : ℝ) (o : V) (R : Set V) :
    boundaryFlux G p o R = p * ∑ e, probability p
      (fun ω => boundaryReach G R (delete (G.openGraph ω) R) o e) := by
  simp only [boundaryFlux,boundaryCount,expect_sum,probability]

lemma boundaryFlux_monotoneOn (o : V) (R : Set V) :
    MonotoneOn (fun p : ℝ => boundaryFlux G p o R) (Icc 0 1) := by
  intro p hp q hq hpq
  simp only [boundaryFlux_eq_sum]
  apply mul_le_mul hpq _ (Finset.sum_nonneg fun e _ => probability_nonneg hp _) hq.1
  apply Finset.sum_le_sum
  intro e _
  exact probability_monotoneOn _ (fun _ _ h => boundary_event_mono G o R e h) hp hq hpq

theorem uniform_escape_lower_bound {p q : ℝ} (hp : p ∈ Ioo 0 1)
    (hpq : p < q) (hq : q < 1) (o : V) (T : Set V)
    (hflux : ∀ R : Set V, T ⊆ R → o ∉ R → 1 ≤ boundaryFlux G p o R) :
    (q-p)/(1+q-p) ≤ probability q (reachesTarget G o T) := by
  let F := reachesTarget G o T
  have hF : ∀ s t, s ⊆ t → F s → F t := fun _ _ h => reachesTarget_mono G o T h
  have hq0 : 0 < q := hp.1.trans hpq
  obtain ⟨c,hc,hderiv⟩ := exists_deriv_eq_slope
    (fun r => probability r F) hpq (continuous_probability F).continuousOn
    (fun r hr => (hasDerivAt_probability ⟨hp.1.trans hr.1,hr.2.trans hq⟩ F hF
      ).differentiableAt.differentiableWithinAt)
  have hc01 : c ∈ Ioo 0 1 := ⟨hp.1.trans hc.1,hc.2.trans hq⟩
  have hd := differential_inequality G hc01 o T (a := 1) (fun R hTR ho =>
    (hflux R hTR ho).trans (boundaryFlux_monotoneOn G o R
      ⟨hp.1.le,hp.2.le⟩ ⟨hc01.1.le,hc01.2.le⟩ hc.1.le))
  have hmono := probability_monotoneOn F hF ⟨hc01.1.le,hc01.2.le⟩
    ⟨hq0.le,hq.le⟩ hc.2.le
  have hdnonneg : 0 ≤ deriv (fun r => probability r F) c := by
    rw [(hasDerivAt_probability hc01 F hF).deriv]
    exact Finset.sum_nonneg fun e _ => probability_nonneg ⟨hc01.1.le,hc01.2.le⟩ _
  have hfactor : c*(1-c) ≤ 1 := by nlinarith [sq_nonneg c]
  have hds : c*(1-c)*deriv (fun r => probability r F) c ≤
      deriv (fun r => probability r F) c := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor hdnonneg
  have hlow : 1-probability q F ≤ deriv (fun r => probability r F) c := by
    change 1*(1-probability c F) ≤ _ at hd
    linarith
  have hdiff := mul_le_mul_of_nonneg_right hlow (sub_pos.mpr hpq).le
  have heq := (eq_div_iff (sub_pos.mpr hpq).ne').mp hderiv
  have hnonneg := probability_nonneg ⟨hp.1.le,hp.2.le⟩ F
  apply (div_le_iff₀ (by linarith : 0 < 1+q-p)).mpr
  change q-p ≤ probability q F * (1+q-p)
  nlinarith

end CriticalPercolation.Sharpness
end
end CurrentModule5

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_SharpnessPhi
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule6
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open FiniteProduct ClusterDeletion

variable {E V : Type*}

lemma probability_eq_real [Fintype E] (p : unitInterval) (F : Set E → Prop) :
    probability (p : ℝ) F = (BernoulliProduct.law (fun _ : E => p)).real {ω | F ω} := by
  rw [← integral_indicator_one (μ := BernoulliProduct.law (fun _ : E => p))
    (s := {ω | F ω}) (.of_discrete), BernoulliProduct.integral_law_eq_expect]
  rfl

variable (G : BondGraph V E)

lemma finite_probability_restrict (p : unitInterval) (K : Set E) (hK : K.Finite)
    (F : Set K → Prop) :
    letI := hK.fintype
    probability (p : ℝ) F = (G.law p).real {ω | F (Subtype.val ⁻¹' ω)} := by
  let := hK.fintype
  rw [probability_eq_real, ← BernoulliProduct.law_map_restrict (fun _ : E => p) K]
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set K)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  simp only [measureReal_def, Measure.map_apply hmeas (.of_discrete)]
  rw [BernoulliProduct.law_const]
  rfl

lemma finite_incident (hG : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.incidentEdges S).Finite := by
  have hh := hS.biUnion (fun v _ => hG v)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext e
  simp only [BondGraph.incidentEdges,Set.mem_ofPred_eq,Set.mem_iUnion,exists_prop]

lemma incident_mono {S T : Set V} (h : S ⊆ T) : G.incidentEdges S ⊆ G.incidentEdges T := by
  rintro e ⟨v,hv,he⟩
  exact ⟨v,h hv,he⟩

lemma delete_restrict_incident {S : Set V} {K : Set E} (hK : G.incidentEdges S ⊆ K)
    (ω : Set E) : delete (G.openGraph (K ∩ ω)) Sᶜ = delete (G.openGraph ω) Sᶜ := by
  ext x y
  constructor
  · exact fun h => ⟨G.openGraph_mono inter_subset_right h.1,h.2⟩
  · rintro ⟨⟨⟨e,he,hend⟩,hne⟩,hx,hy⟩
    refine ⟨⟨⟨e,⟨hK ?_,he⟩,hend⟩,hne⟩,hx,hy⟩
    exact ⟨x,not_not.mp hx,by rw [hend]; simp⟩

lemma boundaryReach_incident {S : Set V} {H : SimpleGraph V} {o : V} {e : E}
    (h : boundaryReach G Sᶜ H o e) : e ∈ G.incidentEdges S := by
  obtain ⟨x,y,he,hx,_hy,_hox⟩ := h
  exact ⟨x,not_not.mp hx,by rw [he]; simp⟩

lemma boundary_measure_support (p : unitInterval) (o : V) (S : Set V) :
    Function.support (fun e => (G.law p).real
      {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e}) ⊆ G.incidentEdges S := by
  intro e he
  by_contra hn
  apply he
  have hh : {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} = ∅ := by
    ext ω
    exact iff_false_intro (fun h => hn (boundaryReach_incident G h))
  change (G.law p).real {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} = 0
  rw [hh,measureReal_empty]

lemma phi_eq_boundaryFlux (p : unitInterval) (o : V) (S : Set V)
    (K : Set E) (hK : K.Finite) (hSK : G.incidentEdges S ⊆ K) :
    letI := hK.fintype
    phi G p o S = boundaryFlux (G.restrictEdges K) (p : ℝ) o Sᶜ := by
  let := hK.fintype
  rw [phi, ← tsum_subtype_eq_of_support_subset ((boundary_measure_support G p o S).trans hSK),
    tsum_fintype, boundaryFlux_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [finite_probability_restrict G p K hK]
  congr 1
  ext ω
  change boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e.val ↔
    boundaryReach (G.restrictEdges K) Sᶜ
      (delete ((G.restrictEdges K).openGraph (Subtype.val ⁻¹' ω)) Sᶜ) o e
  rw [G.restrictEdges_openGraph, delete_restrict_incident G hSK]
  rfl

lemma restricted_escape_le (p : unitInterval) (o : V) (T : Set V)
    (K : Set E) (hK : K.Finite) :
    letI := hK.fintype
    probability (p : ℝ) (reachesTarget (G.restrictEdges K) o T) ≤
      (G.law p).real (G.hitEvent o T) := by
  let := hK.fintype
  rw [finite_probability_restrict G p K hK]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  change reachesTarget (G.restrictEdges K) o T (Subtype.val ⁻¹' ω) at hω
  apply (reachesTarget_iff_hitEvent G o T ω).mp
  apply reachesTarget_mono G o T inter_subset_right
  change o ∈ roots (G.openGraph (K ∩ ω)) T
  simpa only [reachesTarget, G.restrictEdges_openGraph] using hω

end CriticalPercolation.Sharpness
end
end CurrentModule6

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_InfiniteEventSubsetHit
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma infiniteEvent_subset_hit_compl (o : V) (K : Set V) (hK : K.Finite) :
    G.infiniteEvent o ⊆ G.hitEvent o Kᶜ := by
  intro ω hω
  exact (hω.sdiff hK).nonempty

lemma infiniteEvent_eq_iInter_hit_compl
    (K : Set.FiniteExhaustion (Set.univ : Set V)) (o : V) :
    G.infiniteEvent o = ⋂ n, G.hitEvent o (K n)ᶜ := by
  ext ω
  constructor
  · intro hω
    exact Set.mem_iInter.mpr fun n => G.infiniteEvent_subset_hit_compl o (K n) (K.finite n) hω
  · intro hω
    change (G.cluster ω o).Infinite
    intro hfin
    obtain ⟨n, hn⟩ := finite_subset_exhaustion K hfin (Set.subset_univ _)
    obtain ⟨v, hv, hvK⟩ := Set.mem_iInter.mp hω n
    exact hvK (hn hv)

lemma tendsto_real_hit_compl [Countable V] [Countable E]
    (p : unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set V)) (o : V) :
    Tendsto (fun n => (G.law p).real (G.hitEvent o (K n)ᶜ)) atTop
      (𝓝 ((G.law p).real (G.infiniteEvent o))) := by
  have h := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n => (G.measurableSet_hitEvent o (K n)ᶜ).nullMeasurableSet)
    (show Antitone (fun n => G.hitEvent o (K n)ᶜ) from
      fun _ _ h => G.hitEvent_mono_target o (Set.compl_subset_compl.mpr (K.mono h)))
    ⟨0, measure_ne_top _ _⟩
  rw [← G.infiniteEvent_eq_iInter_hit_compl K o] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_InfiniteEscapeLowerBound
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule8
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {E V : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma infinite_escape_lower_bound (hl : G.LocallyFinite)
    (p q : unitInterval) (hp : 0 < (p : ℝ)) (hpq : p < q) (hq : q < 1)
    (o : V) (hflux : ∀ S : Set V, S.Finite → o ∈ S → 1 ≤ phi G p o S) :
    ((q : ℝ)-p)/(1+q-p) ≤ (G.law q).real (G.infiniteEvent o) := by
  let L := (Set.to_countable (Set.univ : Set V)).finiteExhaustion
  apply ge_of_tendsto (G.tendsto_real_hit_compl q L o)
  apply Eventually.of_forall
  intro n
  let K := G.incidentEdges (L n)
  have hK : K.Finite := finite_incident G hl (L.finite n)
  let := hK.fintype
  have hf : ∀ R : Set V, (L n)ᶜ ⊆ R → o ∉ R →
      1 ≤ boundaryFlux (G.restrictEdges K) (p : ℝ) o R := by
    intro R hR ho
    have hsub : Rᶜ ⊆ L n := by
      simpa only [compl_compl] using Set.compl_subset_compl.mpr hR
    have he := phi_eq_boundaryFlux G p o Rᶜ K hK (incident_mono G hsub)
    simp only [compl_compl] at he
    rw [← he]
    exact hflux Rᶜ ((L.finite n).subset hsub) ho
  exact (uniform_escape_lower_bound (G.restrictEdges K)
    ⟨hp, (show (p : ℝ)<q from hpq).trans (show (q : ℝ)<1 from hq)⟩
    hpq hq o (L n)ᶜ hf).trans (restricted_escape_le G q o (L n)ᶜ K hK)

theorem subcritical_finite_size (hl : G.LocallyFinite)
    (p : unitInterval) (hp : p < G.criticalProbability) (o : V) :
    ∃ S : Set V, S.Finite ∧ o ∈ S ∧ phi G p o S < 1 := by
  by_cases hp0 : (p : ℝ) = 0
  · exact ⟨{o},Set.finite_singleton o,Set.mem_singleton o,by simp [phi,hp0]⟩
  have hp_pos : 0 < (p : ℝ) := lt_of_le_of_ne p.property.1 (Ne.symm hp0)
  by_contra h
  have hflux : ∀ S : Set V, S.Finite → o ∈ S → 1 ≤ phi G p o S := by
    intro S hS ho
    exact le_of_not_gt (fun hh => h ⟨S,hS,ho,hh⟩)
  let q : unitInterval := ⟨((p : ℝ)+(G.criticalProbability : ℝ))/2, by
    constructor
    · linarith [p.property.1,G.criticalProbability.property.1]
    · linarith [p.property.2,G.criticalProbability.property.2]⟩
  have hpq : p < q := by
    change (p : ℝ) < ((p : ℝ)+(G.criticalProbability : ℝ))/2
    have hh : (p : ℝ) < G.criticalProbability := hp
    linarith
  have hqc : q < G.criticalProbability := by
    change ((p : ℝ)+(G.criticalProbability : ℝ))/2 < (G.criticalProbability : ℝ)
    have hh : (p : ℝ) < G.criticalProbability := hp
    linarith
  have hq1 : q < 1 := hqc.trans_le G.criticalProbability.property.2
  have hb := infinite_escape_lower_bound G hl p q hp_pos hpq hq1 o hflux
  have hz : (G.law q).real (G.infiniteEvent o) = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr
    apply measure_mono_null (show G.infiniteEvent o ⊆ G.percolates from fun _ hω => ⟨o,hω⟩)
    exact G.law_percolates_eq_zero_of_lt_critical hqc
  rw [hz] at hb
  have hd : 0 < (q : ℝ)-p := sub_pos.mpr hpq
  have hden : 0 < 1+(q : ℝ)-p := by linarith
  exact (not_le_of_gt (div_pos hd hden)) hb

end CriticalPercolation.Sharpness
end
end CurrentModule8

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_DeleteImageIso
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule9
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

lemma measurableSet_boundary (hl : G.LocallyFinite)
    (o : V) (S : Set V) (hS : S.Finite) (e : E) :
    MeasurableSet {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} := by
  let K := G.incidentEdges S
  have hK : K.Finite := finite_incident G hl hS
  let := hK.fintype
  have hm : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set K)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  have he : {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} =
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set K)) ⁻¹'
        {η | boundaryReach G Sᶜ
          (delete ((G.restrictEdges K).openGraph η) Sᶜ) o e} := by
    ext ω
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.restrictEdges_openGraph,
      delete_restrict_incident G (K := K) Subset.rfl]
  rw [he]
  exact hm (.of_discrete)

lemma boundary_image (φ : G.Aut) (S : Set V) (o : V) (e : E) (ω : Set E) :
    boundaryReach G (φ.vertex '' S)ᶜ
      (delete (G.openGraph (φ.edge '' ω)) (φ.vertex '' S)ᶜ) (φ.vertex o) (φ.edge e) ↔
      boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e := by
  have himg : (φ.vertex '' S)ᶜ = φ.vertex '' Sᶜ := by
    ext v
    obtain ⟨x,rfl⟩ := φ.vertex.surjective v
    simp only [Set.mem_compl_iff,Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]
  rw [himg]
  constructor
  · rintro ⟨a,b,he,ha,hb,hr⟩
    obtain ⟨x,rfl⟩ := φ.vertex.surjective a
    obtain ⟨y,rfl⟩ := φ.vertex.surjective b
    have hx : x ∉ Sᶜ := by simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using ha
    have hy : y ∈ Sᶜ := by simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using hb
    rw [φ.preserves,← Sym2.map_mk] at he
    exact ⟨x,y,Sym2.map.injective φ.vertex.injective he,hx,hy,
      (SimpleGraph.Iso.reachable_iff (φ := deleteImageIso G φ ω Sᶜ)).mp hr⟩
  · rintro ⟨x,y,he,hx,hy,hr⟩
    refine ⟨φ.vertex x,φ.vertex y,?_,?_,?_,?_⟩
    · rw [φ.preserves,he,Sym2.map_mk]
    · simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using hx
    · exact ⟨y,hy,rfl⟩
    · exact (SimpleGraph.Iso.reachable_iff (φ := deleteImageIso G φ ω Sᶜ)).mpr hr

lemma boundary_real_image (hl : G.LocallyFinite) (φ : G.Aut) (p : unitInterval)
    (S : Set V) (hS : S.Finite) (o : V) (e : E) :
    (G.law p).real {ω | boundaryReach G (φ.vertex '' S)ᶜ
      (delete (G.openGraph ω) (φ.vertex '' S)ᶜ) (φ.vertex o) (φ.edge e)} =
    (G.law p).real {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} := by
  change (G.law p _).toReal = (G.law p _).toReal
  congr 1
  calc
    _ = (G.law p).map (fun ω : Set E => φ.edge '' ω)
        {ω | boundaryReach G (φ.vertex '' S)ᶜ
          (delete (G.openGraph ω) (φ.vertex '' S)ᶜ) (φ.vertex o) (φ.edge e)} := by
      rw [G.law_map_aut p φ]
    _ = _ := by
      rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
        (measurableSet_boundary G hl _ _ (hS.image _) _)]
      congr 1
      ext ω
      exact boundary_image G φ S o e ω

lemma phi_image (hl : G.LocallyFinite) (φ : G.Aut) (p : unitInterval)
    (S : Set V) (hS : S.Finite) (o : V) :
    phi G p (φ.vertex o) (φ.vertex '' S) = phi G p o S := by
  unfold phi
  congr 1
  rw [← φ.edge.tsum_eq]
  apply tsum_congr
  intro e
  exact boundary_real_image G hl φ p S hS o e

theorem uniform_subcritical_domains [Countable V] [Countable E] [Nonempty V]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : p < G.criticalProbability) :
    ∃ N : ℕ, ∃ a : ℝ, a < 1 ∧ ∀ o : V,
      ∃ S : Set V, S.Finite ∧ o ∈ S ∧ S.ncard ≤ N ∧ phi G p o S ≤ a := by
  obtain ⟨R,hR,horbit⟩ := hq
  have hne : R.Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty V›
    obtain ⟨r,hr,_⟩ := horbit v
    exact ⟨r,hr⟩
  choose D hD hoD hphi using subcritical_finite_size G hl p hp
  obtain ⟨r,hr,hmax⟩ := Set.exists_max_image R (fun o => phi G p o (D o)) hR hne
  let N := ∑ o ∈ hR.toFinset, (D o).ncard
  refine ⟨N,phi G p r (D r),hphi r,?_⟩
  intro o
  obtain ⟨s,hs,φ,rfl⟩ := horbit o
  refine ⟨φ.vertex '' D s,(hD s).image _,⟨s,hoD s,rfl⟩,?_,?_⟩
  · rw [Set.ncard_image_of_injective _ φ.vertex.injective]
    exact Finset.single_le_sum (f := fun o => (D o).ncard)
      (fun _ _ => Nat.zero_le _) (hR.mem_toFinset.mpr hs)
  · rw [phi_image G hl φ p (D s) (hD s) s]
    exact hmax s hs

end CriticalPercolation.Sharpness
end
end CurrentModule9

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_Leak
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule4
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion FiniteProduct

variable {V E : Type*} [Fintype E]

lemma probability_mono_event {p : ℝ} (hp : p ∈ Icc 0 1) {F F' : Set E → Prop}
    (h : ∀ ω, F ω → F' ω) : probability p F ≤ probability p F' := by
  apply expect_mono (fun _ => weight_nonneg hp)
  intro ω
  by_cases hF : F ω
  · simp only [ite_eq_left hF,ite_eq_left (h ω hF),le_refl]
  · simp only [ite_eq_right hF]
    split_ifs <;> norm_num

variable (G : BondGraph V E)

omit [Fintype E] in
lemma leak_nonneg (S C : Set V) (e : E) (v : V) (ω : Set E) :
    0 ≤ leak G S C e v ω := by unfold leak; split_ifs <;> norm_num

omit [Fintype E] in
lemma leak_dependsOn (S C : Set V) (e : E) (v : V) :
    DependsOn (leak G S C e v) (internalIncident G S C)ᶜ := by
  intro ω ω' hω
  by_cases hc : IsCut G S e ∧ cutInside G S e ∈ C
  · have he : ω e = ω' e := hω e (cut_not_internalIncident G hc.1)
    have hg : delete (G.openGraph ω) C = delete (G.openGraph ω') C :=
      G.delete_openGraph_dependsOn C (fun j hj => hω j (fun hD => hj hD.1))
    simp only [leak,ite_eq_left hc]
    change (if ω e ∧ _ then (1:ℝ) else 0) = if ω' e ∧ _ then 1 else 0
    simp only [he,hg]
  · simp only [leak,ite_eq_right hc]

lemma leak_expect (p : ℝ) (S C : Set V) (e : E) (v : V) :
    expect (fun _ : E => weight p) (leak G S C e v) =
      if IsCut G S e ∧ cutInside G S e ∈ C then
        p * probability p (fun ω => (delete (G.openGraph ω) C).Reachable (cutOutside G S e) v)
      else 0 := by
  by_cases hc : IsCut G S e ∧ cutInside G S e ∈ C
  · rw [ite_eq_left hc]
    have heI : e ∈ G.incidentEdges C :=
      ⟨cutInside G S e,hc.2,by rw [cut_ends G S e]; simp⟩
    calc
      _ = expect (fun _ : E => weight p) (fun ω => if ω e = True then
          (if (delete (G.openGraph ω) C).Reachable (cutOutside G S e) v then 1 else 0) else 0) := by
        congr 1
        funext ω
        simp only [leak,ite_eq_left hc]
        change (if ω e ∧ (delete (G.openGraph ω) C).Reachable
          (cutOutside G S e) v then (1:ℝ) else 0) = _
        by_cases he : ω e <;> simp [he]
      _ = weight p True * expect (fun _ : E => weight p) (fun ω =>
          if (delete (G.openGraph (Function.update ω e True)) C).Reachable
            (cutOutside G S e) v then 1 else 0) :=
        by
          convert expect_coordinate_mask (fun _ : E => weight p) (fun _ => weight_sum p)
            e True (fun ω => if (delete (G.openGraph ω) C).Reachable
              (cutOutside G S e) v then (1:ℝ) else 0) using 1
          all_goals try with_reducible_and_instances rfl
          congr 1
          funext ω
          split_ifs <;> rfl
      _ = _ := by
        simp only [weight,if_true]
        congr 1
        unfold probability
        congr 1
        funext ω
        erw [delete_update_incident G heI]
  · rw [ite_eq_right hc]
    calc
      _ = expect (fun _ : E => weight p) (fun _ => 0) := by
        congr 1; funext ω; simp only [leak,ite_eq_right hc]
      _ = 0 := expect_const _ (fun _ => weight_sum p) 0

lemma leak_expect_le {p : ℝ} (hp : p ∈ Icc 0 1) (S C : Set V) (e : E) (v : V) :
    expect (fun _ : E => weight p) (leak G S C e v) ≤
      (if IsCut G S e ∧ cutInside G S e ∈ C then (1:ℝ) else 0) *
        (p * probability p (fun ω => (G.openGraph ω).Reachable (cutOutside G S e) v)) := by
  rw [leak_expect]
  split_ifs
  · simp only [one_mul]
    apply mul_le_mul_of_nonneg_left _ hp.1
    exact probability_mono_event hp (fun _ h => h.mono (delete_le _ _))
  · simp

lemma boundary_probability_cut (p : ℝ) (S : Set V) (o : V) (e : E) :
    probability p (fun ω => boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e) =
      expect (fun _ : E => weight p) (fun ω =>
        if IsCut G S e ∧ cutInside G S e ∈ internalCluster G S o ω then (1:ℝ) else 0) := by
  unfold probability
  congr 1
  funext ω
  simp only [boundaryReach_iff_cut,internalCluster,component,Set.mem_ofPred_eq]
  congr 1

lemma exposed_leak_le {p : ℝ} (hp : p ∈ Icc 0 1) (S : Set V) (o v : V) (e : E) :
    expect (fun _ : E => weight p) (fun ω => leak G S (internalCluster G S o ω) e v ω) ≤
      p * probability p (fun ω => boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e) *
        probability p (fun ω => (G.openGraph ω).Reachable (cutOutside G S e) v) := by
  rw [expect_exposure_finiteRange _ (fun _ => weight_sum p)
    (fun ω => internalCluster G S o ω) (internalIncident G S)
    (fun C => dependsOn_internalCluster G S C o) (fun C => leak G S C e v)
    (fun C => leak_dependsOn G S C e v)]
  calc
    _ ≤ expect (fun _ : E => weight p) (fun ω =>
        (if IsCut G S e ∧ cutInside G S e ∈ internalCluster G S o ω then (1:ℝ) else 0) *
        (p * probability p (fun ω => (G.openGraph ω).Reachable (cutOutside G S e) v))) :=
      expect_mono (fun _ => weight_nonneg hp) (fun _ => leak_expect_le G hp S _ e v)
    _ = _ := by rw [expect_mul_const,← boundary_probability_cut]; ring

theorem simon_lieb {p : ℝ} (hp : p ∈ Icc 0 1) (S : Set V) (o : V) (ho : o ∈ S)
    (v : V) (hv : v ∉ S) :
    probability p (fun ω => (G.openGraph ω).Reachable o v) ≤
      ∑ e, p * probability p (fun ω => boundaryReach G Sᶜ
        (delete (G.openGraph ω) Sᶜ) o e) *
          probability p (fun ω => (G.openGraph ω).Reachable (cutOutside G S e) v) := by
  have hpoint (ω : Set E) : (if (G.openGraph ω).Reachable o v then (1:ℝ) else 0) ≤
      ∑ e, leak G S (internalCluster G S o ω) e v ω := by
    by_cases hr : (G.openGraph ω).Reachable o v
    · rw [ite_eq_left hr]
      obtain ⟨e,hc,hi,he,hv'⟩ := internalCluster_exit G S o ho ω hv hr
      have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset E)) =>
        leak_nonneg G S (internalCluster G S o ω) j v ω) (Finset.mem_univ e)
      have heq : leak G S (internalCluster G S o ω) e v ω = 1 := by
        simp only [leak, ite_eq_left (And.intro hc hi), ite_eq_left (And.intro he hv')]
      rwa [heq] at hh
    · rw [ite_eq_right hr]
      exact Finset.sum_nonneg (fun _ _ => leak_nonneg G S (internalCluster G S o ω) _ v ω)
  calc
    _ ≤ expect (fun _ : E => weight p) (fun ω => ∑ e, leak G S (internalCluster G S o ω) e v ω) :=
      expect_mono (fun _ => weight_nonneg hp) hpoint
    _ = ∑ e, expect (fun _ : E => weight p) (fun ω => leak G S (internalCluster G S o ω) e v ω) :=
      expect_sum _ _
    _ ≤ _ := Finset.sum_le_sum (fun e _ => exposed_leak_le G hp S o v e)

end CriticalPercolation.Sharpness
end
end CurrentModule4

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FiniteSumConnection
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule7
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

lemma finite_sum_connection_le [Fintype E] {p : ℝ} (hp : p ∈ Icc 0 1)
    (A : Finset V) (S : Set V) (hS : S.Finite) (o : V) (ho : o ∈ S)
    (M : ℝ) (hM : ∀ y : V, ∑ v ∈ A,
      probability p (fun ω => (G.openGraph ω).Reachable y v) ≤ M) :
    ∑ v ∈ A, probability p (fun ω => (G.openGraph ω).Reachable o v) ≤
      S.ncard + boundaryFlux G p o Sᶜ * M := by
  let f := fun x y => probability p (fun ω => (G.openGraph ω).Reachable x y)
  let c := fun e => p * probability p (fun ω =>
    boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e)
  have hc : ∀ e, 0 ≤ c e := fun e => mul_nonneg hp.1 (probability_nonneg hp _)
  have hout (v) (hv : v ∉ S) : f o v ≤ ∑ e, c e * f (cutOutside G S e) v :=
    simon_lieb G hp S o ho v hv
  calc
    _ ≤ ∑ v ∈ A, ((if v ∈ S then (1:ℝ) else 0) +
        ∑ e, c e * f (cutOutside G S e) v) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : v ∈ S
      · simp only [ite_eq_left hv]
        exact (probability_le_one hp _).trans (le_add_of_nonneg_right
          (Finset.sum_nonneg fun e _ => mul_nonneg (hc e) (probability_nonneg hp _)))
      · simpa only [ite_eq_right hv,zero_add] using hout v hv
    _ = (A.filter (· ∈ S)).card + ∑ e, c e * ∑ v ∈ A, f (cutOutside G S e) v := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [← Finset.mul_sum]
      congr 1
      simp
    _ ≤ S.ncard + (∑ e, c e) * M := by
      apply add_le_add
      · exact_mod_cast Set.ncard_le_ncard
          (show (↑(A.filter (· ∈ S)) : Set V) ⊆ S from fun v hv => (Finset.mem_filter.mp hv).2) hS
      · rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hM _) (hc e)
    _ = _ := by
      rw [boundaryFlux_eq_sum,Finset.mul_sum]

lemma restricted_boundaryFlux_le_phi (hl : G.LocallyFinite) (p : unitInterval)
    (S : Set V) (hS : S.Finite) (o : V) (K : Set E) (hK : K.Finite) :
    letI := hK.fintype
    boundaryFlux (G.restrictEdges K) (p : ℝ) o Sᶜ ≤ phi G p o S := by
  let := hK.fintype
  let F := fun e => (G.law p).real {ω | boundaryReach G Sᶜ
    (delete (G.openGraph ω) Sᶜ) o e}
  have hF : Summable F := summable_of_hasFiniteSupport
    ((finite_incident G hl hS).subset (boundary_measure_support G p o S))
  rw [boundaryFlux_eq_sum,phi]
  apply mul_le_mul_of_nonneg_left _ p.property.1
  calc
    _ ≤ ∑ e : K, F e.val := by
      apply Finset.sum_le_sum
      intro e _
      rw [finite_probability_restrict G p K hK]
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      change boundaryReach (G.restrictEdges K) Sᶜ
        (delete ((G.restrictEdges K).openGraph (Subtype.val ⁻¹' ω)) Sᶜ) o e at hω
      rw [G.restrictEdges_openGraph] at hω
      have hh : boundaryReach G Sᶜ (delete (G.openGraph (K ∩ ω)) Sᶜ) o e.val := hω
      obtain ⟨x,y,he,hx,hy,hr⟩ := hh
      have hdel : delete (G.openGraph (K ∩ ω)) Sᶜ ≤ delete (G.openGraph ω) Sᶜ :=
        fun _ _ hab => ⟨G.openGraph_mono inter_subset_right hab.1,hab.2⟩
      exact ⟨x,y,he,hx,hy,hr.mono hdel⟩
    _ ≤ ∑' e, F e := by
      simpa only [tsum_fintype,Function.comp_def] using
        (tsum_comp_le_tsum_of_inj hF (fun e => measureReal_nonneg)
          (Subtype.val_injective : Function.Injective (Subtype.val : K → E)))

end CriticalPercolation.Sharpness
end
end CurrentModule7

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_TwoPoint
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule10
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {V E : Type*} (G : BondGraph V E)

lemma hit_singleton_eq (o v : V) :
    G.hitEvent o {v} = {ω | (G.openGraph ω).Reachable o v} := by
  ext ω
  simp only [BondGraph.hitEvent,Set.mem_ofPred_eq,Set.inter_singleton_nonempty,BondGraph.cluster]

lemma twoPoint_nonneg (p : unitInterval) (o v : V) : 0 ≤ twoPoint G p o v := measureReal_nonneg

lemma finite_contraction [Fintype E] [Nonempty V] {p : ℝ} (hp : p ∈ Icc 0 1)
    (N : ℕ) (a : ℝ) (ha : a < 1)
    (hdom : ∀ o : V, ∃ S : Set V, S.Finite ∧ o ∈ S ∧ S.ncard ≤ N ∧
      boundaryFlux G p o Sᶜ ≤ a) (A : Finset V) (o : V) :
    ∑ v ∈ A, probability p (fun ω => (G.openGraph ω).Reachable o v) ≤ N / (1-a) := by
  let f := fun y => ∑ v ∈ A, probability p (fun ω => (G.openGraph ω).Reachable y v)
  have hb : BddAbove (Set.range f) := ⟨A.card,by
    rintro _ ⟨y,rfl⟩
    calc
      _ ≤ ∑ _v ∈ A, (1:ℝ) := Finset.sum_le_sum fun v _ => probability_le_one hp _
      _ = _ := by simp⟩
  let M := sSup (Set.range f)
  have hM : ∀ y, f y ≤ M := fun y => le_csSup hb ⟨y,rfl⟩
  have hM0 : 0 ≤ M := (Finset.sum_nonneg (fun _ _ => probability_nonneg hp _)).trans (hM o)
  have hcon : M ≤ N + a * M := by
    apply csSup_le (Set.range_nonempty f)
    rintro _ ⟨y,rfl⟩
    obtain ⟨S,hS,hy,hn,hphi⟩ := hdom y
    exact (finite_sum_connection_le G hp A S hS y hy M hM).trans
      (add_le_add (Nat.cast_le.mpr hn) (mul_le_mul_of_nonneg_right hphi hM0))
  apply (hM o).trans
  apply (le_div_iff₀ (sub_pos.mpr ha)).mpr
  nlinarith

lemma finite_probability_connection (p : unitInterval) (K : Set E) (hK : K.Finite)
    (o v : V) :
    letI := hK.fintype
    probability (p : ℝ) (fun ω => ((G.restrictEdges K).openGraph ω).Reachable o v) =
      (G.law p).real {ω | K ∩ ω ∈ G.hitEvent o {v}} := by
  let := hK.fintype
  rw [finite_probability_restrict G p K hK,hit_singleton_eq]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq,G.restrictEdges_openGraph]

theorem subcritical_susceptibility [Countable V] [Countable E] [Nonempty V]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : p < G.criticalProbability) :
    ∃ C : ℝ, ∀ (A : Finset V) (o : V), ∑ v ∈ A, twoPoint G p o v ≤ C := by
  obtain ⟨N,a,ha,hdom⟩ := uniform_subcritical_domains G hl hq p hp
  refine ⟨N/(1-a),?_⟩
  intro A o
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  have hf (n : ℕ) : ∑ v ∈ A, (G.law p).real {ω | K n ∩ ω ∈ G.hitEvent o {v}} ≤
      N/(1-a) := by
    let := (K.finite n).fintype
    have hd : ∀ y : V, ∃ S : Set V, S.Finite ∧ y ∈ S ∧ S.ncard ≤ N ∧
        boundaryFlux (G.restrictEdges (K n)) (p : ℝ) y Sᶜ ≤ a := by
      intro y
      obtain ⟨S,hS,hy,hn,hphi⟩ := hdom y
      exact ⟨S,hS,hy,hn,(restricted_boundaryFlux_le_phi G hl p S hS y (K n) (K.finite n)).trans hphi⟩
    have hh := finite_contraction (G.restrictEdges (K n)) p.property N a ha hd A o
    simpa only [finite_probability_connection G p (K n) (K.finite n)] using hh
  have ht : Tendsto (fun n => ∑ v ∈ A, (G.law p).real
      {ω | K n ∩ ω ∈ G.hitEvent o {v}}) atTop (𝓝 (∑ v ∈ A, twoPoint G p o v)) := by
    apply tendsto_finsetSum
    intro v _
    simpa only [BondGraph.law,BernoulliProduct.law_const,twoPoint] using
      G.tendsto_real_hitEvent_exhaustion (fun _ : E => p) K o {v}
  exact le_of_tendsto ht (Eventually.of_forall hf)

theorem summable_subcritical_twoPoint [Countable V] [Countable E]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : p < G.criticalProbability) (o : V) :
    Summable (twoPoint G p o) := by
  let : Nonempty V := ⟨o⟩
  obtain ⟨C,hC⟩ := subcritical_susceptibility G hl hq p hp
  exact summable_of_sum_le (twoPoint_nonneg G p o) (fun A => hC A o)

end CriticalPercolation.Sharpness
end
end CurrentModule10

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_LayerExposure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma entrySeeds_subset_cluster (D : Set V) (o : V) (ω : Set E) :
    G.entrySeeds D o ω⊆G.cluster ω o :=
  fun _ h => G.cluster_mono Set.inter_subset_left o h.1

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_LayerExpectation
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma subcritical_seedExpectation_bound_bs_oai [Countable V] [Countable E]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (q : unitInterval) (hqc : q<G.criticalProbability) (o : V) :
    ∃ C : ℝ≥0∞, C≠∞ ∧ ∀ D : Set V, G.seedExpectation q D o≤C := by
  let C := ∑' x, ENNReal.ofReal (Sharpness.twoPoint G q o x)
  refine ⟨C,(Sharpness.summable_subcritical_twoPoint G hl hq q hqc o).tsum_ofReal_ne_top,?_⟩
  intro D
  apply ENNReal.tsum_le_tsum
  intro x
  have he : ENNReal.ofReal (Sharpness.twoPoint G q o x)=G.law q (G.hitEvent o {x}) := by
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [he]
  apply measure_mono
  intro ω hω
  rw [Sharpness.hit_singleton_eq]
  exact G.entrySeeds_subset_cluster D o ω hω

end BondGraph
end CriticalPercolation
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.subcritical_seedExpectation_bound_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.subcritical_seedExpectation_bound_bs_oai.{u_1, u_2}
