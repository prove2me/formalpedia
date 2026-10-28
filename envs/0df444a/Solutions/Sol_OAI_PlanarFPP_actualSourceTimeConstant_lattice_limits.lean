-- Prove2me | solution 1 for OAI.PlanarFPP.actualSourceTimeConstant_lattice_limits
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:41:47.605015+00:00
-- url     : https://prove2.me/submissions/f164009c-ed40-4922-9add-ef50bc1d53ea

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002

section
-- module Solutions.OAIS_PlanarFPP.Compat
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
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
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
/-- Mathlib's newer `SimpleGraph.Walk.length_le_bypass_length_iff` (ours has the two directions
separately). `_root_`, so `p.length_le_bypass_length_iff` resolves by dot notation. -/
theorem _root_.SimpleGraph.Walk.length_le_bypass_length_iff {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] {u v : V} (p : G.Walk u v) : p.length ≤ p.bypass.length ↔ p.bypass = p :=
  ⟨p.bypass_eq_self_of_length_le_length_bypass, fun h => by rw [h]⟩
end OAICompat434

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CompanionModel
attribute [-instance] _root_.OAI.CompanionFPP.countable_lattice_walk _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set

lemma steps_companion_walk (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    ∃ walk : CompanionFPP.lattice.Walk p (p+displacement ds),
      CompanionFPP.pathCost (companionWeights w) walk = pathCost w p ds := by
  induction ds generalizing p with
  | nil =>
    refine ⟨(SimpleGraph.Walk.nil : CompanionFPP.lattice.Walk p p).copy rfl (by simp),?_⟩
    rw [companion_pathCost_copy]
    rfl
  | cons d ds ih =>
    obtain ⟨walk,hw⟩ := ih (p+d.delta)
    have he : (p+d.delta)+displacement ds = p+displacement (d::ds) := by
      simp [add_assoc]
    refine ⟨(SimpleGraph.Walk.cons (companion_adj_step p d) walk).copy rfl he,?_⟩
    simp only [companion_pathCost_copy, CompanionFPP.pathCost_cons, CompanionFPP.edgeCost, pathCost, hw]
    rw [← companionEdge_step,companionWeights_edge]

lemma companion_walk_steps (w : Edge → ℝ) {p q : Vertex}
    (walk : CompanionFPP.lattice.Walk p q) :
    ∃ ds : List Step, p+displacement ds=q ∧ pathCost w p ds =
      CompanionFPP.pathCost (companionWeights w) walk := by
  induction walk with
  | nil => exact ⟨[],by simp,rfl⟩
  | @cons p u q hadj walk ih =>
    obtain ⟨d,rfl⟩ := (companion_adj_iff p u).mp hadj
    obtain ⟨ds,he,hc⟩ := ih
    refine ⟨d::ds,by simpa [add_assoc] using he,?_⟩
    simp only [pathCost,CompanionFPP.pathCost_cons,CompanionFPP.edgeCost,hc]
    rw [← companionEdge_step,companionWeights_edge]

theorem companion_passageTime_eq (w : Edge → ℝ) (p q : Vertex) :
    CompanionFPP.passageTime (companionWeights w) p q = passageTime w p q := by
  unfold CompanionFPP.passageTime passageTime
  congr 1
  ext t
  constructor
  · rintro ⟨walk,rfl⟩
    obtain ⟨ds,he,hc⟩ := companion_walk_steps w walk
    exact ⟨ds,he,hc⟩
  · rintro ⟨ds,he,rfl⟩
    obtain ⟨walk,hw⟩ := steps_companion_walk w p ds
    subst q
    exact ⟨walk,hw⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ExponentialEnvironment.companionLaw (h : ExponentialEnvironment P τ) :
    Measure.map (fun ω => companionWeights (fun e => τ e ω)) P =
      CompanionFPP.environmentLaw := by
  have hi := h.independent.precomp companionEdgeEquiv.symm.injective
  unfold companionWeights
  rw [hi.map_fun_eq_infinitePi_map (fun _ => h.measurable _)]
  simp only [h.marginal,CompanionFPP.environmentLaw]

lemma measurable_companionWeights (hτ : ∀ e, Measurable (τ e)) :
    Measurable (fun ω => companionWeights (fun e => τ e ω)) :=
  Measurable.of_eval (fun _ => hτ _)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_GeodesicSimple
attribute [-instance] _root_.OAI.CompanionFPP.countable_lattice_walk _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP

private lemma sublist_length_of_cost {α : Type*} (f : α → ℝ)
    {l₁ l₂ : List α} (h : l₁.Sublist l₂) (hpos : ∀ a ∈ l₂, 0 < f a)
    (hcost : (l₂.map f).sum ≤ (l₁.map f).sum) : l₂.length ≤ l₁.length := by
  induction h with
  | slnil => simp
  | @cons l₁ l₂ a h ih =>
    have hnonneg : ∀ b ∈ l₂, 0 ≤ f b := fun b hb => (hpos b (by simp [hb])).le
    have hle := (h.map f).sum_le_sum (by
      intro b hb
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
      exact hnonneg c hc)
    have ha := hpos a (by simp)
    simp only [List.map_cons, List.sum_cons] at hcost
    linarith
  | @cons_cons l₁ l₂ a h ih =>
    have ht : ∀ b ∈ l₂, 0 < f b := fun b hb => hpos b (by simp [hb])
    have hs : (l₂.map f).sum ≤ (l₁.map f).sum := by
      simpa only [List.map_cons, List.sum_cons, add_le_add_iff_left] using hcost
    simpa using ih ht hs

theorem minimizing_walk_isPath (ω : Environment) (hω : ∀ e, 0 < ω e)
    {x y : Vertex} (p : lattice.Walk x y)
    (hp : pathCost ω p = passageTime ω x y) : p.IsPath := by
  classical
  have hcost : pathCost ω p ≤ pathCost ω p.bypass := by
    rw [hp]
    exact passageTime_le_pathCost ω (fun e => (hω e).le) p.bypass
  rw [pathCost_eq_darts_sum, pathCost_eq_darts_sum] at hcost
  have hl := sublist_length_of_cost (fun d : lattice.Dart => edgeCost ω d.adj)
    p.darts_bypass_sublist_darts (by intro d _; exact hω _) hcost
  have he := p.length_le_bypass_length_iff.mp (by simpa using hl)
  rw [← he]
  exact p.bypass_isPath

theorem all_minimizing_walks_simple : ∀ᵐ ω ∂environmentLaw, ∀ x y : Vertex,
    ∀ p : lattice.Walk x y, pathCost ω p = passageTime ω x y → p.IsPath := by
  filter_upwards [all_edge_weights_positive] with ω hω
  exact fun _ _ p hp => minimizing_walk_isPath ω hω p hp

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_PositiveMoment
attribute [-instance] _root_.OAI.CompanionFPP.countable_lattice_walk _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

theorem costly_edge_set_probability (s : Finset Edge) (t : ℝ) :
    environmentLaw {ω : Environment | t ≤ ∑ e ∈ s, ω e} ≤
      2 ^ s.card / ENNReal.ofReal (exp (t / 2)) := by
  have hm := meas_ge_le_lintegral_div (μ := environmentLaw)
    (f := fun ω : Environment => ENNReal.ofReal (exp ((∑ e ∈ s, ω e) / 2)))
    (by fun_prop) (ε := ENNReal.ofReal (exp (t / 2)))
    (by positivity) ENNReal.ofReal_ne_top
  have hs : {ω : Environment | ENNReal.ofReal (exp (t / 2)) ≤
      ENNReal.ofReal (exp ((∑ e ∈ s, ω e) / 2))} =
      {ω : Environment | t ≤ ∑ e ∈ s, ω e} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ENNReal.ofReal_le_ofReal_iff (exp_pos _).le,
      exp_le_exp]
    constructor <;> intro h <;> linarith
  rw [hs] at hm
  simp_rw [positive_exp_sum] at hm
  rw [edge_set_positive_moment] at hm
  exact hm

theorem costly_trail_probability {x y : Vertex} (p : lattice.Walk x y)
    (hp : p.IsTrail) (t : ℝ) :
    environmentLaw.real {ω : Environment | t ≤ pathCost ω p} ≤
      (2 : ℝ)^p.length * exp (-t / 2) := by
  classical
  have hn := pathEdges_nodup hp
  have hc : (pathEdges p).toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hn, pathEdges_length]
  have he : ∀ ω : Environment, (∑ e ∈ (pathEdges p).toFinset, ω e) = pathCost ω p := by
    intro ω
    rw [pathCost_eq_edgeList_sum]
    exact List.sum_toFinset _ hn
  have h := costly_edge_set_probability (pathEdges p).toFinset t
  simp only [he, hc] at h
  have hr := ENNReal.toReal_mono (show (2 : ℝ≥0∞)^p.length /
      ENNReal.ofReal (exp (t/2)) ≠ ⊤ from
      ENNReal.div_ne_top (by simp) (by positivity)) h
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (exp_pos _).le, ENNReal.toReal_ofNat] at hr
  change environmentLaw.real _ ≤ _ at hr
  rw [show -t / 2 = -(t / 2) by ring, exp_neg]
  simpa only [div_eq_mul_inv] using hr

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_GeodesicTail
attribute [-instance] _root_.OAI.CompanionFPP.countable_lattice_walk _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real

theorem geodesic_tail_split (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (t : ℝ) (ht : 0 ≤ t) :
    environmentLaw.real {ω : Environment | ∃ p : lattice.Walk x y,
      p.IsPath ∧ pathCost ω p = passageTime ω x y ∧ R ≤ p.length} ≤
    (2 : ℝ)^(latticeDistance x y) * exp (-t/2) +
      (8/3 : ℝ) * exp (5*t) * (1/2 : ℝ)^R := by
  classical
  obtain ⟨q,hq,hlen⟩ := coordinate_path x y
  let A := {ω : Environment | t ≤ pathCost ω q}
  let B := {ω : Environment | ∃ a ∈ ({x} : Finset Vertex), ∃ b,
    ∃ p : lattice.Walk a b, p.IsPath ∧ R ≤ p.length ∧ pathCost ω p ≤ t}
  have hsub : environmentLaw {ω : Environment | ∃ p : lattice.Walk x y,
      p.IsPath ∧ pathCost ω p = passageTime ω x y ∧ R ≤ p.length} ≤
      environmentLaw (A ∪ B) := by
    apply measure_mono_ae
    filter_upwards [all_edge_weights_positive] with ω hω
    rintro ⟨p,hp,hcost,hl⟩
    by_cases ha : t ≤ pathCost ω q
    · exact Or.inl ha
    · right
      refine ⟨x, Finset.mem_singleton_self x, y, p, hp, hl, ?_⟩
      rw [hcost]
      exact (passageTime_le_pathCost ω (fun e => (hω e).le) q).trans
        (le_of_lt (lt_of_not_ge ha))
  have hsub' := ENNReal.toReal_mono (measure_ne_top _ _) hsub
  change environmentLaw.real _ ≤ environmentLaw.real (A ∪ B) at hsub'
  have ha : environmentLaw.real A ≤ (2 : ℝ)^latticeDistance x y * exp (-t/2) := by
    apply (costly_trail_probability q hq.isTrail t).trans
    gcongr
    norm_num
  have hb : environmentLaw.real B ≤ (8/3 : ℝ) * exp (5*t) * (1/2 : ℝ)^R := by
    simpa only [Finset.card_singleton, Nat.cast_one, mul_one] using
      no_long_cheap_paths {x} R hR t ht
  exact hsub'.trans ((measureReal_union_le A B).trans (add_le_add ha hb))

private lemma tail_numerics (l R : ℕ) (hl : 40*l ≤ R) :
    (2 : ℝ)^l * exp (-((log 2)*R/10)/2) +
      (8/3 : ℝ) * exp (5*((log 2)*R/10)) * (1/2 : ℝ)^R ≤
      (11/3 : ℝ) * exp (-(log 2 / 40) * R) := by
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hl' : 40*(l : ℝ) ≤ R := by exact_mod_cast hl
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
  have hp (n : ℕ) : (2 : ℝ)^n = exp ((n : ℝ)*log 2) := by
    rw [exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
  have hm (n : ℕ) : (1/2 : ℝ)^n = exp (-((n : ℝ)*log 2)) := by
    rw [exp_neg, ← hp]
    simp [one_div]
  rw [hp, hm]
  have h₁ : exp ((l : ℝ)*log 2) * exp (-((log 2)*R/10)/2) ≤
      exp (-(log 2/40)*R) := by
    rw [← exp_add, exp_le_exp]
    nlinarith
  have h₂ : exp (5*((log 2)*R/10)) * exp (-((R : ℝ)*log 2)) ≤
      exp (-(log 2/40)*R) := by
    rw [← exp_add, exp_le_exp]
    nlinarith
  nlinarith

theorem simple_geodesic_length_tail (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) :
    environmentLaw.real {ω : Environment | ∃ p : lattice.Walk x y,
      p.IsPath ∧ pathCost ω p = passageTime ω x y ∧ R ≤ p.length} ≤
      (11/3 : ℝ) * exp (-(log 2 / 40) * R) := by
  exact (geodesic_tail_split x y R hR ((log 2)*R/10) (by positivity)).trans
    (tail_numerics (latticeDistance x y) R hscale)

theorem geodesic_length_tail (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) :
    environmentLaw.real {ω : Environment | ∃ p : lattice.Walk x y,
      pathCost ω p = passageTime ω x y ∧ R ≤ p.length} ≤
      (11/3 : ℝ) * exp (-(log 2 / 40) * R) := by
  have hsub : environmentLaw {ω : Environment | ∃ p : lattice.Walk x y,
      pathCost ω p = passageTime ω x y ∧ R ≤ p.length} ≤
      environmentLaw {ω : Environment | ∃ p : lattice.Walk x y,
        p.IsPath ∧ pathCost ω p = passageTime ω x y ∧ R ≤ p.length} := by
    apply measure_mono_ae
    filter_upwards [all_minimizing_walks_simple] with ω hω
    rintro ⟨p,hp,hl⟩
    exact ⟨p,hω x y p hp,hp,hl⟩
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans
    (simple_geodesic_length_tail x y R hR hscale)

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_PassageRegularity
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

theorem passageTime_upper_tail (x y : Vertex) (t : ℝ) :
    environmentLaw.real {ω : Environment | t ≤ passageTime ω x y} ≤
      (2 : ℝ)^latticeDistance x y * exp (-t/2) := by
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  have hsub : environmentLaw {ω : Environment | t ≤ passageTime ω x y} ≤
      environmentLaw {ω : Environment | t ≤ pathCost ω p} := by
    apply measure_mono_ae
    filter_upwards [all_edge_weights_positive] with ω hω
    intro ht
    exact ht.trans (passageTime_le_pathCost ω (fun e => (hω e).le) p)
  apply (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans
  apply (costly_trail_probability p hp.isTrail t).trans
  gcongr
  norm_num

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_LocalPassage
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Finset Real

lemma mem_localCandidates {x y : Vertex} {R : ℕ} (p : lattice.Walk x y)
    (hp : p.IsPath) (hl : p.length < R) :
    (⟨y,p⟩ : Σ y : Vertex, lattice.Walk x y) ∈ localCandidates x R := by
  classical
  apply mem_filter.mpr
  exact ⟨mem_biUnion.mpr ⟨p.length, mem_range.mpr hl, trail_mem_starting p hp.isTrail⟩,
    hp, hl⟩

lemma pathCost_eq_of_agree (ω ω' : Environment) {x y : Vertex} (p : lattice.Walk x y)
    (h : ∀ e ∈ pathEdges p, ω e = ω' e) : pathCost ω p = pathCost ω' p := by
  rw [pathCost_eq_edgeList_sum, pathCost_eq_edgeList_sum]
  congr 1
  exact List.map_congr_left h

lemma local_pathCost_eq (ω ω' : Environment) {x y : Vertex} {R : ℕ}
    (h : ∀ e ∈ localEdges x R, ω e = ω' e)
    (p : lattice.Walk x y) (hp : p.IsPath) (hl : p.length < R) :
    pathCost ω p = pathCost ω' p := by
  classical
  apply pathCost_eq_of_agree
  intro e he
  apply h e
  exact mem_biUnion.mpr ⟨⟨y,p⟩, mem_localCandidates p hp hl, List.mem_toFinset.mpr he⟩

lemma local_costs_finite (ω : Environment) (x y : Vertex) (R : ℕ) :
    {c : ℝ | ∃ p : lattice.Walk x y, p.IsPath ∧ p.length < R ∧ c = pathCost ω p}.Finite := by
  classical
  apply ((localCandidates x R).image (fun q => pathCost ω q.2)).finite_toSet.subset
  rintro c ⟨p,hp,hl,rfl⟩
  exact mem_image.mpr ⟨⟨y,p⟩, mem_localCandidates p hp hl, rfl⟩

theorem localPassageTime_eq_of_agree (ω ω' : Environment) (x y : Vertex) (R : ℕ)
    (h : ∀ e ∈ localEdges x R, ω e = ω' e) :
    localPassageTime ω x y R = localPassageTime ω' x y R := by
  unfold localPassageTime
  congr 1
  ext c
  constructor <;> rintro ⟨p,hp,hl,rfl⟩
  · exact ⟨p,hp,hl,local_pathCost_eq ω ω' h p hp hl⟩
  · exact ⟨p,hp,hl,(local_pathCost_eq ω ω' h p hp hl).symm⟩

theorem local_geodesic_exists (ω : Environment) (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) :
    ∃ p : lattice.Walk x y, p.IsPath ∧ p.length < R ∧
      pathCost ω p = localPassageTime ω x y R := by
  let C := {c : ℝ | ∃ p : lattice.Walk x y, p.IsPath ∧ p.length < R ∧ c = pathCost ω p}
  have hC : C.Finite := local_costs_finite ω x y R
  obtain ⟨q,hq,hl⟩ := coordinate_path x y
  have hne : C.Nonempty := ⟨pathCost ω q,q,hq,hl.trans_lt hR,rfl⟩
  obtain ⟨c,hc,hm⟩ := Set.exists_min_image C id hC hne
  obtain ⟨p,hp,hl,rfl⟩ := hc
  refine ⟨p,hp,hl,le_antisymm ?_ ?_⟩
  · exact le_csInf hne (fun c hc => hm c hc)
  · exact csInf_le hC.bddBelow ⟨p,hp,hl,rfl⟩

theorem localPassageTime_eq_of_short_geodesic (ω : Environment) (hω : ∀ e, 0 ≤ ω e)
    {x y : Vertex} {R : ℕ} (p : lattice.Walk x y) (hp : p.IsPath)
    (hl : p.length < R) (hc : pathCost ω p = passageTime ω x y) :
    localPassageTime ω x y R = passageTime ω x y := by
  apply le_antisymm
  · rw [← hc]
    exact csInf_le (local_costs_finite ω x y R).bddBelow ⟨p,hp,hl,rfl⟩
  · apply le_csInf (s := {c : ℝ | ∃ q : lattice.Walk x y,
        q.IsPath ∧ q.length < R ∧ c = pathCost ω q}) ⟨pathCost ω p,p,hp,hl,rfl⟩
    rintro c ⟨q,_,_,rfl⟩
    exact passageTime_le_pathCost ω hω q

theorem localPassageTime_failure_probability (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) :
    environmentLaw.real {ω : Environment | localPassageTime ω x y R ≠ passageTime ω x y} ≤
      (11/3 : ℝ) * exp (-(log 2/40)*R) := by
  have hsub : environmentLaw {ω : Environment | localPassageTime ω x y R ≠ passageTime ω x y} ≤
      environmentLaw {ω : Environment | ∃ p : lattice.Walk x y,
        pathCost ω p = passageTime ω x y ∧ R ≤ p.length} := by
    apply measure_mono_ae
    filter_upwards [all_edge_weights_positive, geodesics_exist] with ω hω hg
    intro hne
    obtain ⟨p,hp,hc⟩ := hg x y
    refine ⟨p,hc, ?_⟩
    by_contra hl
    exact hne (localPassageTime_eq_of_short_geodesic ω (fun e => (hω e).le)
      p hp (lt_of_not_ge hl) hc)
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans
    (geodesic_length_tail x y R hR hscale)

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_LocalizationMean
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real

lemma integrable_trail_exp {x y : Vertex} (p : lattice.Walk x y) (hp : p.IsTrail) :
    Integrable (fun ω : Environment => exp (pathCost ω p / 2)) environmentLaw := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (by filter_upwards [] with ω; positivity)).mp
  rw [trail_positive_moment p hp]
  finiteness

lemma integral_trail_exp {x y : Vertex} (p : lattice.Walk x y) (hp : p.IsTrail) :
    (∫ ω : Environment, exp (pathCost ω p / 2) ∂environmentLaw) = (2 : ℝ)^p.length := by
  rw [integral_eq_lintegral_of_nonneg_ae (by filter_upwards [] with ω; positivity)
    (by fun_prop), trail_positive_moment p hp]
  simp

lemma integrable_trail_cost {x y : Vertex} (p : lattice.Walk x y) (hp : p.IsTrail) :
    Integrable (fun ω : Environment => pathCost ω p) environmentLaw := by
  apply ((integrable_trail_exp p hp).const_mul 2).mono' (by fun_prop)
  filter_upwards [all_edge_weights_positive] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (pathCost_nonneg ω (fun e => (hω e).le) p)]
  have he := add_one_le_exp (pathCost ω p / 2)
  linarith

lemma localPassageTime_le_pathCost (ω : Environment) {x y : Vertex} {R : ℕ}
    (p : lattice.Walk x y) (hp : p.IsPath) (hl : p.length < R) :
    localPassageTime ω x y R ≤ pathCost ω p :=
  csInf_le (local_costs_finite ω x y R).bddBelow ⟨p,hp,hl,rfl⟩

lemma passageTime_le_localPassageTime (ω : Environment) (hω : ∀ e, 0 ≤ ω e)
    (x y : Vertex) (R : ℕ) (hR : latticeDistance x y < R) :
    passageTime ω x y ≤ localPassageTime ω x y R := by
  obtain ⟨p,_,_,hp⟩ := local_geodesic_exists ω x y R hR
  rw [← hp]
  exact passageTime_le_pathCost ω hω p

theorem integrable_localPassageTime (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) :
    Integrable (fun ω : Environment => localPassageTime ω x y R) environmentLaw := by
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  apply (integrable_trail_cost p hp.isTrail).mono' (by fun_prop)
  filter_upwards [all_edge_weights_positive] with ω hω
  have ht := passageTime_nonneg ω (fun e => (hω e).le) (lattice_walk x y)
  have hn := passageTime_le_localPassageTime ω (fun e => (hω e).le) x y R hR
  rw [Real.norm_eq_abs, abs_of_nonneg (ht.trans hn)]
  exact localPassageTime_le_pathCost ω p hp (hl.trans_lt hR)

private lemma rare_cost_pointwise (S u : ℝ) (hu : 0 ≤ u) (P : Prop) [Decidable P] :
    (if P then S else 0) ≤ (if P then u else 0) + 4*exp (-u/4)*exp (S/2) := by
  by_cases hP : P
  · simp only [ite_eq_left hP]
    by_cases hs : S ≤ u
    · have : 0 ≤ 4*exp (-u/4)*exp (S/2) := by positivity
      linarith
    · have he := add_one_le_exp (S/4)
      have he' : exp (S/4) ≤ exp (-u/4 + S/2) := by
        rw [exp_le_exp]
        linarith
      rw [mul_assoc, ← exp_add]
      linarith
  · simp only [ite_eq_right hP, zero_add]
    positivity

theorem rare_cost_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Integrable S μ)
    (he : Integrable (fun ω => exp (S ω / 2)) μ) (F : Set Ω) (hF : MeasurableSet F)
    (u : ℝ) (hu : 0 ≤ u) :
    (∫ ω, F.indicator S ω ∂μ) ≤
      u * μ.real F + 4*exp (-u/4) * (∫ ω, exp (S ω/2) ∂μ) := by
  classical
  have hbound := integral_mono_ae (hS.indicator hF)
    (((integrable_const u).indicator hF).add (he.const_mul (4*exp (-u/4))))
    (Filter.Eventually.of_forall (fun ω => rare_cost_pointwise (S ω) u hu (ω ∈ F)))
  simp only [Pi.add_apply] at hbound
  rw [integral_add ((integrable_const u).indicator hF) (he.const_mul (4*exp (-u/4))),
    integral_const_mul, integral_indicator_const u hF] at hbound
  simpa [smul_eq_mul, mul_comm] using hbound

theorem localPassageTime_mean_error (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) :
    (∫ ω : Environment, localPassageTime ω x y R - passageTime ω x y ∂environmentLaw) ≤
      (R : ℝ) * ((11/3 : ℝ)*exp (-(log 2/40)*R)) +
        4*exp (-(R : ℝ)/4)*(2 : ℝ)^latticeDistance x y := by
  classical
  have hd : latticeDistance x y < R := by omega
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  let F := {ω : Environment | localPassageTime ω x y R ≠ passageTime ω x y}
  have hF : MeasurableSet F := (measurableSet_eq_fun (measurable_localPassageTime x y R)
    (measurable_passageTime x y)).compl
  have hcost := integrable_trail_cost p hp.isTrail
  have hb : (∫ ω : Environment, localPassageTime ω x y R - passageTime ω x y ∂environmentLaw) ≤
      ∫ ω, F.indicator (fun ω => pathCost ω p) ω ∂environmentLaw := by
    apply integral_mono_ae ((integrable_localPassageTime x y R hd).sub (integrable_passageTime x y))
      (hcost.indicator hF)
    filter_upwards [all_edge_weights_positive] with ω hω
    simp only [Pi.sub_apply]
    by_cases hf : ω ∈ F
    · rw [Set.indicator_of_mem hf]
      have h₁ := localPassageTime_le_pathCost ω p hp (hl.trans_lt hd)
      have h₂ := passageTime_nonneg ω (fun e => (hω e).le) (lattice_walk x y)
      linarith
    · rw [Set.indicator_of_notMem hf]
      have heq : localPassageTime ω x y R = passageTime ω x y := not_not.mp hf
      rw [heq, sub_self]
  apply hb.trans
  have hm := rare_cost_integral environmentLaw (fun ω => pathCost ω p) hcost
    (integrable_trail_exp p hp.isTrail) F hF (R : ℝ) (by positivity)
  rw [integral_trail_exp p hp.isTrail] at hm
  apply hm.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (localPassageTime_failure_probability x y R hR hscale)
      (Nat.cast_nonneg _)
  · gcongr
    norm_num

theorem localPassageTime_mean_error_exponential (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) :
    (∫ ω : Environment, localPassageTime ω x y R - passageTime ω x y ∂environmentLaw) ≤
      ((11/3 : ℝ)*R + 4) * exp (-(log 2/40)*R) := by
  apply (localPassageTime_mean_error x y R hR hscale).trans
  have hn : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
  have hl : 40*(latticeDistance x y : ℝ) ≤ R := by exact_mod_cast hscale
  have hlog : log (2 : ℝ) ≤ 1 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hpow : (2 : ℝ)^latticeDistance x y =
      exp ((latticeDistance x y : ℝ)*log 2) := by
    rw [exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
  have hb : exp (-(R : ℝ)/4) * (2 : ℝ)^latticeDistance x y ≤
      exp (-(log 2/40)*R) := by
    rw [hpow, ← exp_add, exp_le_exp]
    have hd : 0 ≤ (latticeDistance x y : ℝ) := Nat.cast_nonneg _
    nlinarith
  nlinarith

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_ExponentialIncrement
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

lemma exponential_weighted_density (a x : ℝ) (ha : a < 1) :
    exponentialPDF 1 x * ENNReal.ofReal (exp (a*x)) =
      ENNReal.ofReal (1/(1-a)) * exponentialPDF (1-a) x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [one_mul]
    rw [← exp_add]
    have he : -x + a*x = -((1-a)*x) := by ring
    rw [he]
    field_simp [show 1-a ≠ 0 by linarith]
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),
      exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_lmoment (a : ℝ) (ha : a < 1) :
    (∫⁻ x, ENNReal.ofReal (exp (a*x)) ∂expMeasure 1) = ENNReal.ofReal (1/(1-a)) := by
  change (∫⁻ x, ENNReal.ofReal (exp (a*x)) ∂volume.withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (by unfold exponentialPDF; fun_prop)
    (by fun_prop)]
  simp only [Pi.mul_apply, exponential_weighted_density a _ ha]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop),
    lintegral_exponentialPDF_eq_one (by linarith : 0 < 1-a), mul_one]

lemma integrable_exponential (a : ℝ) (ha : a < 1) :
    Integrable (fun x => exp (a*x)) (expMeasure 1) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (by filter_upwards [] with x; positivity)).mp
  rw [exponential_lmoment a ha]
  exact ENNReal.ofReal_ne_top

theorem integral_exponential (a : ℝ) (ha : a < 1) :
    (∫ x, exp (a*x) ∂expMeasure 1) = 1/(1-a) := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (by filter_upwards [] with x; positivity) (by fun_prop), exponential_lmoment a ha,
    ENNReal.toReal_ofReal (by positivity)]

lemma exponential_increment_square (a u : ℝ) :
    (exp (a*u)-1)^2 = exp ((2*a)*u)-2*exp (a*u)+1 := by
  rw [show (2*a)*u = a*u+a*u by ring, exp_add]
  ring

lemma integrable_exponential_increment_square (a : ℝ) (ha : 2*a < 1) :
    Integrable (fun u => (exp (a*u)-1)^2) (expMeasure 1) := by
  simp_rw [exponential_increment_square]
  exact ((integrable_exponential (2*a) ha).sub
    ((integrable_exponential a (by linarith)).const_mul 2)).add (integrable_const 1)

theorem integral_exponential_increment_square (a : ℝ) (ha : 2*a < 1) :
    (∫ u, (exp (a*u)-1)^2 ∂expMeasure 1) =
      2*a^2/((1-2*a)*(1-a)) := by
  simp_rw [exponential_increment_square]
  rw [integral_add (f := fun u => exp ((2*a)*u)-2*exp (a*u)) (g := fun _ => (1 : ℝ)) ((integrable_exponential (2*a) ha).sub
      ((integrable_exponential a (by linarith)).const_mul 2)) (integrable_const 1),
    integral_sub (f := fun u => exp ((2*a)*u)) (g := fun u => 2*exp (a*u)) (integrable_exponential (2*a) ha)
      ((integrable_exponential a (by linarith)).const_mul 2), integral_const_mul,
    integral_exponential (2*a) ha, integral_exponential a (by linarith)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  field_simp [show 1-a ≠ 0 by linarith, show 1-2*a ≠ 0 by linarith]
  ring

theorem exponential_half_increment_square_le (a : ℝ) (ha : |a| ≤ 1/2) :
    (∫⁻ u, ENNReal.ofReal ((exp (a*u/2)-1)^2) ∂expMeasure 1) ≤
      ENNReal.ofReal (2*a^2) := by
  have hb := abs_le.mp ha
  have hp : 2*(a/2) < 1 := by linarith
  have he (u : ℝ) : a*u/2 = (a/2)*u := by ring
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exponential_increment_square (a/2) hp)
    (by filter_upwards [] with u; positivity), integral_exponential_increment_square (a/2) hp]
  apply ENNReal.ofReal_le_ofReal
  have hd : 0 < (1-2*(a/2))*(1-a/2) := mul_pos (by linarith) (by linarith)
  apply (div_le_iff₀ hd).mpr
  have hden : (3/8 : ℝ) ≤ (1-2*(a/2))*(1-a/2) := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hden)]

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_EdgeInfluence
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open Finset

lemma trailCost_eq_sum (ω : Environment) {x y : Vertex} (p : lattice.Walk x y)
    (hp : p.IsTrail) : pathCost ω p = ∑ e ∈ (pathEdges p).toFinset, ω e := by
  classical
  rw [pathCost_eq_edgeList_sum]
  exact (List.sum_toFinset _ (pathEdges_nodup hp)).symm

theorem trailCost_one_edge_change (ω ω' : Environment) (e : Edge)
    (h : ∀ f, f ≠ e → ω' f = ω f) {x y : Vertex}
    (p : lattice.Walk x y) (hp : p.IsTrail) :
    pathCost ω' p - pathCost ω p =
      if e ∈ pathEdges p then ω' e - ω e else 0 := by
  classical
  rw [trailCost_eq_sum ω' p hp, trailCost_eq_sum ω p hp, ← sum_sub_distrib]
  by_cases he : e ∈ pathEdges p
  · rw [ite_eq_left he]
    apply sum_eq_single_of_mem e (List.mem_toFinset.mpr he)
    intro f _ hfe
    rw [h f hfe, sub_self]
  · rw [ite_eq_right he]
    apply sum_eq_zero
    intro f hf
    have hfe : f ≠ e := by
      intro hfe
      exact he (hfe ▸ List.mem_toFinset.mp hf)
    rw [h f hfe, sub_self]

theorem localPassageTime_one_edge_upper (ω ω' : Environment) (e : Edge)
    (h : ∀ f, f ≠ e → ω' f = ω f) {x y : Vertex} {R : ℕ}
    (p : lattice.Walk x y) (hp : p.IsPath) (hl : p.length < R)
    (hm : pathCost ω p = localPassageTime ω x y R) :
    localPassageTime ω' x y R - localPassageTime ω x y R ≤
      if e ∈ pathEdges p then ω' e - ω e else 0 := by
  classical
  have hc : localPassageTime ω' x y R ≤ pathCost ω' p :=
    csInf_le (local_costs_finite ω' x y R).bddBelow ⟨p,hp,hl,rfl⟩
  rw [← trailCost_one_edge_change ω ω' e h p hp.isTrail, ← hm]
  linarith

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_FiniteProduct
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset

@[fun_prop] lemma measurable_extendLocalCoordinates (x : Vertex) (R : ℕ) :
    Measurable (extendLocalCoordinates x R) := by
  classical
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ localEdges x R
  · simpa [extendLocalCoordinates, he] using (measurable_pi_apply (⟨e,he⟩ : ↥(localEdges x R)))
  · simp [extendLocalCoordinates, he]

@[fun_prop] lemma measurable_finitePassageTime (x y : Vertex) (R : ℕ) :
    Measurable (finitePassageTime x y R) :=
  (measurable_localPassageTime x y R).comp (measurable_extendLocalCoordinates x R)

theorem finitePassageTime_restrict (x y : Vertex) (R : ℕ) (ω : Environment) :
    finitePassageTime x y R ((localEdges x R).restrict ω) = localPassageTime ω x y R := by
  apply localPassageTime_eq_of_agree
  intro e he
  exact extendLocalCoordinates_apply x R _ ⟨e,he⟩

theorem finitePassageTime_law (x y : Vertex) (R : ℕ) :
    Measure.map (localPassageTime · x y R) environmentLaw =
      Measure.map (finitePassageTime x y R)
        (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) := by
  rw [← Measure.infinitePi_map_restrict (fun _ : Edge => expMeasure 1),
    Measure.map_map (measurable_finitePassageTime x y R) (measurable_restrict _)]
  congr 1
  funext ω
  exact (finitePassageTime_restrict x y R ω).symm

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_ResamplingMoment
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma upwardResampling_le (ω : Environment) (hω : ∀ e, 0 ≤ ω e)
    {x y : Vertex} {R : ℕ} (p : lattice.Walk x y) (hp : p.IsPath)
    (hl : p.length < R) (hm : pathCost ω p = localPassageTime ω x y R)
    (e : Edge) (u : ℝ) (hu : 0 ≤ u) :
    upwardResampling ω x y R e u ≤ if e ∈ pathEdges p then u else 0 := by
  classical
  have h := localPassageTime_one_edge_upper ω (Function.update ω e u) e
    (fun f hf => Function.update_of_ne hf _ _) p hp hl hm
  simp only [Function.update_self] at h
  unfold upwardResampling
  apply max_le
  · split_ifs at h ⊢ with he
    · linarith [hω e]
    · exact h
  · split_ifs <;> positivity

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_ProductVariance
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma square_integral_le_integral_square {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  simp only [Pi.pow_apply] at h
  linarith

lemma bounded_memLp_two {f : α → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (.of_forall (by simpa only [Real.norm_eq_abs] using hC))

lemma abs_integral_le_bound {f : α → ℝ} (C : ℝ) (hC : ∀ x, |f x| ≤ C) (_h0 : 0 ≤ C) :
    |∫ x, f x ∂μ| ≤ C := by
  simpa using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f) (.of_forall (by simpa only [Real.norm_eq_abs] using hC))

theorem product_variance_decomposition {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |f z| ≤ C) :
    variance f (μ.prod ν) =
      (∫ x, variance (fun y => f (x,y)) ν ∂μ) +
        variance (fun x => ∫ y, f (x,y) ∂ν) μ := by
  let g := fun x => ∫ y, f (x,y) ∂ν
  have hfm := bounded_memLp_two (μ := μ.prod ν) hf C hC
  have hsm : ∀ x, MemLp (fun y => f (x,y)) 2 ν := fun x =>
    bounded_memLp_two (hf.comp (measurable_const.prodMk measurable_id)) C (fun y => hC (x,y))
  have hgm : Measurable g := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hgb : ∀ x, |g x| ≤ C := fun x => abs_integral_le_bound C (fun y => hC (x,y)) hC0
  have hg := bounded_memLp_two (μ := μ) hgm C hgb
  have hv : (fun x => variance (fun y => f (x,y)) ν) =
      fun x => (∫ y, (f (x,y))^2 ∂ν) - (g x)^2 := by
    funext x
    exact variance_eq_sub (hsm x)
  rw [hv, integral_sub hfm.integrable_sq.integral_prod_left hg.integrable_sq,
    variance_eq_sub hfm, variance_eq_sub hg]
  have hi := integral_prod f (hfm.integrable (by norm_num))
  have hi2 := integral_prod (fun z => (f z)^2) hfm.integrable_sq
  change _ = _ - _ + (_ - _)
  simp only [Pi.pow_apply]
  rw [hi, hi2]
  dsimp [g]
  ring

theorem variance_integral_le_integral_variance {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |f z| ≤ C) :
    variance (fun x => ∫ y, f (x,y) ∂ν) μ ≤
      ∫ y, variance (fun x => f (x,y)) μ ∂ν := by
  let g := fun x => ∫ y, f (x,y) ∂ν
  let h := fun y => ∫ x, f (x,y) ∂μ
  have hfm := bounded_memLp_two (μ := μ.prod ν) hf C hC
  have hgm : Measurable g := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hhm : Measurable h := hf.stronglyMeasurable.integral_prod_left'.measurable
  have hgb : ∀ x, |g x| ≤ C := fun x => abs_integral_le_bound C (fun y => hC (x,y)) hC0
  have hhb : ∀ y, |h y| ≤ C := fun y => abs_integral_le_bound C (fun x => hC (x,y)) hC0
  have hg := bounded_memLp_two (μ := μ) hgm C hgb
  have hh := bounded_memLp_two (μ := ν) hhm C hhb
  let D := fun z : α × β => f z - h z.2
  have hDm : Measurable D := hf.sub (hhm.comp measurable_snd)
  have hDb : ∀ z, |D z| ≤ 2*C := by
    intro z
    exact (abs_sub _ _).trans (by linarith [hC z, hhb z.2])
  have hD := bounded_memLp_two (μ := μ.prod ν) hDm (2*C) hDb
  have hmean : (∫ y, h y ∂ν) = ∫ x, g x ∂μ :=
    (integral_integral_swap (f := fun x y => f (x,y)) (hfm.integrable (by norm_num))).symm
  have he : ∀ x, (∫ y, D (x,y) ∂ν) = g x - ∫ z, g z ∂μ := by
    intro x
    dsimp [D]
    rw [integral_sub (f := fun y => f (x,y)) (g := h) ((bounded_memLp_two (hf.comp (measurable_const.prodMk measurable_id))
      C (fun y => hC (x,y))).integrable (by norm_num)) (hh.integrable (by norm_num)), hmean]
  have hp : ∀ x, (g x - ∫ z, g z ∂μ)^2 ≤ ∫ y, (D (x,y))^2 ∂ν := by
    intro x
    rw [← he x]
    exact square_integral_le_integral_square
      (bounded_memLp_two (hDm.comp (measurable_const.prodMk measurable_id)) (2*C)
        (fun y => hDb (x,y)))
  rw [variance_eq_integral hgm.aemeasurable]
  apply (integral_mono (hg.sub (memLp_const _)).integrable_sq
    hD.integrable_sq.integral_prod_left hp).trans_eq
  rw [integral_integral_swap (f := fun x y => (D (x,y))^2) hD.integrable_sq]
  apply integral_congr_ae
  exact .of_forall (fun y => (variance_eq_integral
    (hf.comp (measurable_id.prodMk measurable_const)).aemeasurable).symm)

theorem product_variance_le {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |f z| ≤ C) :
    variance f (μ.prod ν) ≤
      (∫ x, variance (fun y => f (x,y)) ν ∂μ) +
      (∫ y, variance (fun x => f (x,y)) μ ∂ν) := by
  rw [product_variance_decomposition (μ := μ) (ν := ν) hf hC0 hC]
  exact add_le_add le_rfl (variance_integral_le_integral_variance (μ := μ) (ν := ν) hf hC0 hC)

lemma measurable_section_variance {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ z, |f z| ≤ C) :
    Measurable (fun x => variance (fun y => f (x,y)) ν) := by
  have he : (fun x => variance (fun y => f (x,y)) ν) =
      fun x => (∫ y, (f (x,y))^2 ∂ν) - (∫ y, f (x,y) ∂ν)^2 := by
    funext x
    exact variance_eq_sub (bounded_memLp_two
      (hf.comp (measurable_const.prodMk measurable_id)) C (fun y => hC (x,y)))
  rw [he]
  exact (hf.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable.sub
    (hf.stronglyMeasurable.integral_prod_right'.measurable.pow_const 2)

lemma variance_le_bound_square {f : α → ℝ} (hf : Measurable f)
    {C : ℝ} (_hC0 : 0 ≤ C) (hC : ∀ x, |f x| ≤ C) : variance f μ ≤ C^2 := by
  have hm := bounded_memLp_two (μ := μ) hf C hC
  apply (variance_le_expectation_sq hf.aestronglyMeasurable).trans
  have h := integral_mono hm.integrable_sq (integrable_const (C^2))
    (fun x => show (f x)^2 ≤ C^2 by nlinarith [hC x, abs_le.mp (hC x)])
  simpa using h

lemma integrable_section_variance {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |f z| ≤ C) :
    Integrable (fun x => variance (fun y => f (x,y)) ν) μ := by
  apply (bounded_memLp_two (measurable_section_variance hf hC) (C^2) ?_).integrable
    (by norm_num)
  intro x
  rw [abs_of_nonneg (variance_nonneg _ _)]
  exact variance_le_bound_square (hf.comp (measurable_const.prodMk measurable_id))
    hC0 (fun y => hC (x,y))

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_FiniteVariance
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Finset

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

lemma measurable_finCons (n : ℕ) :
    Measurable (fun z : α × (Fin n → α) => (Fin.cons z.1 z.2 : Fin (n+1) → α)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (measurable_fst : Measurable (Prod.fst : α × (Fin n → α) → α))
  · simpa only [Function.comp_def, Fin.cons_succ] using (measurable_pi_apply j).comp (measurable_snd :
      Measurable (Prod.snd : α × (Fin n → α) → (Fin n → α)))

lemma finCons_preserving (n : ℕ) :
    MeasurePreserving (fun z : α × (Fin n → α) => Fin.cons z.1 z.2)
      (μ.prod (Measure.pi (fun _ : Fin n => μ)))
      (Measure.pi (fun _ : Fin (n+1) => μ)) := by
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm

lemma integral_finCons {n : ℕ} {f : (Fin (n+1) → α) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ v, |f v| ≤ C) :
    (∫ v, f v ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ a, ∫ w, f (Fin.cons a w) ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
  have he := integral_map (finCons_preserving μ n).aemeasurable hf.aestronglyMeasurable
  rw [(finCons_preserving μ n).map_eq] at he
  rw [he]
  exact integral_prod _ ((bounded_memLp_two (hf.comp (measurable_finCons n))
    C (fun z => hC (Fin.cons z.1 z.2))).integrable (by norm_num))

lemma measurable_coordinateVariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → α) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ v, |f v| ≤ C) (i : ι) :
    Measurable (coordinateVariance μ f i) := by
  apply measurable_section_variance (C := C) (f := fun z => f (Function.update z.1 i z.2))
  · exact hf.comp (by fun_prop)
  · exact fun z => hC _

lemma coordinateVariance_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → α) → ℝ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, |f v| ≤ C) (i : ι) (v : ι → α) :
    |coordinateVariance μ f i v| ≤ C^2 := by
  rw [coordinateVariance, abs_of_nonneg (variance_nonneg _ _)]
  exact variance_le_bound_square (hf.comp (by fun_prop)) hC0 (fun _ => hC _)

lemma integrable_coordinateVariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → α) → ℝ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, |f v| ≤ C) (i : ι) :
    Integrable (coordinateVariance μ f i) (Measure.pi (fun _ : ι => μ)) :=
  (bounded_memLp_two (measurable_coordinateVariance μ hf hC i) (C^2)
    (coordinateVariance_bound μ hf hC0 hC i)).integrable (by norm_num)

omit [IsProbabilityMeasure μ] in
lemma coordinateVariance_cons_zero {n : ℕ} (f : (Fin (n+1) → α) → ℝ)
    (a : α) (w : Fin n → α) :
    coordinateVariance μ f 0 (Fin.cons a w) = variance (fun u => f (Fin.cons u w)) μ := by
  simp only [coordinateVariance, Fin.update_cons_zero]

omit [IsProbabilityMeasure μ] in
lemma coordinateVariance_cons_succ {n : ℕ} (f : (Fin (n+1) → α) → ℝ)
    (i : Fin n) (a : α) (w : Fin n → α) :
    coordinateVariance μ f i.succ (Fin.cons a w) =
      coordinateVariance μ (fun v => f (Fin.cons a v)) i w := by
  simp only [coordinateVariance, ← Fin.cons_update]

lemma integral_coordinateVariance_zero {n : ℕ} {f : (Fin (n+1) → α) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    (∫ v, coordinateVariance μ f 0 v ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ w, variance (fun u => f (Fin.cons u w)) μ ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_finCons μ (measurable_coordinateVariance μ hf hC 0)
    (coordinateVariance_bound μ hf hC0 hC 0)]
  simp [coordinateVariance_cons_zero]

lemma integral_coordinateVariance_succ {n : ℕ} {f : (Fin (n+1) → α) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) (i : Fin n) :
    (∫ v, coordinateVariance μ f i.succ v ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ a, ∫ w, coordinateVariance μ (fun v => f (Fin.cons a v)) i w
        ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
  rw [integral_finCons μ (measurable_coordinateVariance μ hf hC i.succ)
    (coordinateVariance_bound μ hf hC0 hC i.succ)]
  simp only [coordinateVariance_cons_succ]

theorem variance_fin_le_sum_coordinateVariance (n : ℕ)
    {f : (Fin n → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    variance f (Measure.pi (fun _ : Fin n => μ)) ≤
      ∑ i : Fin n, ∫ v, coordinateVariance μ f i v ∂Measure.pi (fun _ : Fin n => μ) := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext v
      congr 1
      funext i
      exact Fin.elim0 i
    rw [he]
    simp [variance_eq_integral measurable_const.aemeasurable]
  | succ n ih =>
    let F := fun z : α × (Fin n → α) => f (Fin.cons z.1 z.2)
    have hFm : Measurable F := hf.comp (measurable_finCons n)
    have hFb : ∀ z, |F z| ≤ C := fun z => hC _
    have he : variance f (Measure.pi (fun _ : Fin (n+1) => μ)) =
        variance F (μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
      rw [← (finCons_preserving μ n).map_eq,
        variance_map hf.aemeasurable (finCons_preserving μ n).aemeasurable]
      rfl
    rw [he]
    have hv := product_variance_le (μ := μ) (ν := Measure.pi (fun _ : Fin n => μ))
      hFm hC0 hFb
    apply hv.trans
    have hI : ∀ i : Fin n, Integrable (fun a => ∫ w,
        coordinateVariance μ (fun v => f (Fin.cons a v)) i w
        ∂Measure.pi (fun _ : Fin n => μ)) μ := by
      intro i
      have hm := (measurable_coordinateVariance μ hf hC i.succ).comp (measurable_finCons n)
      have hb := fun z : α × (Fin n → α) =>
        coordinateVariance_bound μ hf hC0 hC i.succ (Fin.cons z.1 z.2)
      have hi := (bounded_memLp_two (μ := μ.prod (Measure.pi (fun _ : Fin n => μ)))
        hm (C^2) hb).integrable (by norm_num)
      simpa only [Function.comp_def, coordinateVariance_cons_succ] using hi.integral_prod_left
    have hstep := integral_mono (integrable_section_variance hFm hC0 hFb)
      (integrable_finsetSum Finset.univ (fun i _ => hI i)) (fun a =>
        ih (hf.comp ((measurable_finCons n).comp (measurable_const.prodMk measurable_id)))
          (fun v => hC (Fin.cons a v)))
    rw [integral_finsetSum _ (fun i _ => hI i)] at hstep
    rw [Fin.sum_univ_succ, integral_coordinateVariance_zero μ hf hC0 hC]
    simp_rw [integral_coordinateVariance_succ μ hf hC0 hC]
    dsimp [F] at hstep ⊢
    linarith

lemma reindex_preserving {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι) :
    MeasurePreserving (fun v : κ → α => fun i => v (e.symm i))
      (Measure.pi (fun _ : κ => μ)) (Measure.pi (fun _ : ι => μ)) := by
  convert measurePreserving_piCongrLeft (fun _ : ι => μ) e using 1
  funext v i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

omit [IsProbabilityMeasure μ] in
lemma coordinateVariance_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : κ ≃ ι) (f : (ι → α) → ℝ) (j : κ) (v : κ → α) :
    coordinateVariance μ (fun w => f (fun i => w (e.symm i))) j v =
      coordinateVariance μ f (e j) (fun i => v (e.symm i)) := by
  unfold coordinateVariance
  congr 1
  funext u
  dsimp only
  congr 1
  funext i
  by_cases hi : i = e j
  · subst i
    simp
  · have hj : e.symm i ≠ j := by
      intro h
      apply hi
      simpa using congrArg e h
    simp [Function.update_of_ne hi, Function.update_of_ne hj]

theorem variance_pi_le_sum_coordinateVariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    variance f (Measure.pi (fun _ : ι => μ)) ≤
      ∑ i : ι, ∫ v, coordinateVariance μ f i v ∂Measure.pi (fun _ : ι => μ) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hmp := reindex_preserving μ e
  have hg := hf.comp hmp.measurable
  have ht := variance_fin_le_sum_coordinateVariance μ (Fintype.card ι) hg hC0
    (fun w => hC (fun i => w (e.symm i)))
  simp only [Function.comp_def] at ht
  rw [hmp.variance_fun_comp hf.aemeasurable] at ht
  simp only [coordinateVariance_reindex] at ht
  have he : ∀ j : Fin (Fintype.card ι),
      (∫ w, coordinateVariance μ f (e j) (fun i => w (e.symm i))
        ∂Measure.pi (fun _ : Fin (Fintype.card ι) => μ)) =
      ∫ v, coordinateVariance μ f (e j) v ∂Measure.pi (fun _ : ι => μ) := by
    intro j
    have h := integral_map hmp.aemeasurable
      (measurable_coordinateVariance μ hf hC (e j)).aestronglyMeasurable
    rw [hmp.map_eq] at h
    exact h.symm
  simp_rw [he] at ht
  rwa [e.sum_comp (fun i => ∫ v, coordinateVariance μ f i v ∂Measure.pi (fun _ : ι => μ))] at ht

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_ResamplingSymmetry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

lemma exchangeCoordinate_preserving (i : ι) :
    MeasurePreserving (exchangeCoordinate i)
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)))
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) := by
  have hA := measurePreserving_arrowProdEquivProdArrow α α ι (fun _ : ι => μ) (fun _ : ι => μ)
  let s := fun j : ι => if j = i then (Prod.swap : α × α → α × α) else id
  have hs : ∀ j, MeasurePreserving (s j) (μ.prod μ) (μ.prod μ) := by
    intro j
    by_cases hj : j = i
    · simpa [s, hj] using (Measure.measurePreserving_swap (μ := μ) (ν := μ))
    · simpa [s, hj] using (MeasurePreserving.id (μ.prod μ))
  have hp := measurePreserving_pi (fun _ : ι => μ.prod μ) (fun _ : ι => μ.prod μ) hs
  have h := hA.comp (hp.comp hA.symm)
  convert h using 1
  funext z
  apply Prod.ext <;> funext j <;>
    by_cases hj : j = i <;>
    simp [exchangeCoordinate, Function.comp_def, s, hj,
      MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]

omit [Fintype ι] [MeasurableSpace α] in
lemma exchangeCoordinate_first (i : ι) (z : (ι → α) × (ι → α)) :
    (exchangeCoordinate i z).1 = Function.update z.1 i (z.2 i) := rfl

omit [Fintype ι] [MeasurableSpace α] in
lemma exchangeCoordinate_resample (i : ι) (z : (ι → α) × (ι → α)) :
    Function.update (exchangeCoordinate i z).1 i ((exchangeCoordinate i z).2 i) = z.1 := by
  simp [exchangeCoordinate]

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_FiniteResampling
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma extendLocalCoordinates_update (x : Vertex) (R : ℕ)
    (v : LocalCoordinates x R) (e : ↥(localEdges x R)) (u : ℝ) :
    extendLocalCoordinates x R (Function.update v e u) =
      Function.update (extendLocalCoordinates x R v) e.val u := by
  classical
  funext f
  by_cases hf : f = e.val
  · subst f
    simp [extendLocalCoordinates, e.property]
  · by_cases hm : f ∈ localEdges x R
    · have hne : (⟨f,hm⟩ : ↥(localEdges x R)) ≠ e := by
        intro h
        exact hf (congrArg Subtype.val h)
      simp [extendLocalCoordinates, hm, Function.update_of_ne hf, Function.update_of_ne hne]
    · simp [extendLocalCoordinates, hm, Function.update_of_ne hf]

lemma finite_coordinates_nonnegative (x : Vertex) (R : ℕ) :
    ∀ᵐ v ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1), ∀ e, 0 ≤ v e := by
  rw [ae_all_iff]
  intro e
  exact ((measurePreserving_eval (fun _ : ↥(localEdges x R) => expMeasure 1) e).quasiMeasurePreserving.ae
    exponential_positive).mono (fun _ h => h.le)

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_ResamplingTransform
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

theorem sum_upwardResampling_transform (ω : Environment) (hω : ∀ e, 0 ≤ ω e)
    (x y : Vertex) (R : ℕ) (hR : latticeDistance x y < R)
    (φ : ℝ → ℝ≥0∞) (hφ : MonotoneOn φ (Set.Ici 0)) (hzero : φ 0 = 0) :
    (∑ e ∈ localEdges x R, ∫⁻ u, φ (upwardResampling ω x y R e u) ∂expMeasure 1) ≤
      (∫⁻ u, φ u ∂expMeasure 1) * R := by
  classical
  obtain ⟨p,hp,hl,hm⟩ := local_geodesic_exists ω x y R hR
  have hsub : (pathEdges p).toFinset ⊆ localEdges x R := by
    intro e he
    exact mem_biUnion.mpr ⟨⟨y,p⟩, mem_localCandidates p hp hl, he⟩
  have he : ∀ e, (∫⁻ u, φ (upwardResampling ω x y R e u) ∂expMeasure 1) ≤
      if e ∈ pathEdges p then ∫⁻ u, φ u ∂expMeasure 1 else 0 := by
    intro e
    by_cases he : e ∈ pathEdges p
    · rw [ite_eq_left he]
      apply lintegral_mono_ae
      filter_upwards [exponential_positive] with u hu
      apply hφ (by change 0 ≤ upwardResampling ω x y R e u; unfold upwardResampling; positivity) hu.le
      simpa only [ite_eq_left he] using upwardResampling_le ω hω p hp hl hm e u hu.le
    · rw [ite_eq_right he, ← lintegral_zero (μ := expMeasure 1)]
      apply lintegral_mono_ae
      filter_upwards [exponential_positive] with u hu
      have hb := upwardResampling_le ω hω p hp hl hm e u hu.le
      simp only [ite_eq_right he] at hb
      have hn : 0 ≤ upwardResampling ω x y R e u := by unfold upwardResampling; positivity
      rw [le_antisymm hb hn, hzero]
  calc
    _ ≤ ∑ e ∈ localEdges x R, if e ∈ pathEdges p then ∫⁻ u, φ u ∂expMeasure 1 else 0 :=
      sum_le_sum (fun e _ => he e)
    _ = ∑ e ∈ (pathEdges p).toFinset, ∫⁻ u, φ u ∂expMeasure 1 := by
      rw [← sum_filter]
      congr 1
      ext e
      simp only [mem_filter, List.mem_toFinset]
      exact and_iff_right_of_imp (fun he => hsub (List.mem_toFinset.mpr he))
    _ = (p.length : ℝ≥0∞) * ∫⁻ u, φ u ∂expMeasure 1 := by
      rw [sum_const, nsmul_eq_mul, List.toFinset_card_of_nodup (pathEdges_nodup hp.isTrail),
        pathEdges_length]
    _ ≤ (∫⁻ u, φ u ∂expMeasure 1)*R := by
      rw [mul_comm]
      gcongr

lemma exponential_increment_monotone (a : ℝ) :
    MonotoneOn (fun u => ENNReal.ofReal ((exp (a*u/2)-1)^2)) (Set.Ici 0) := by
  intro u hu v hv huv
  change 0 ≤ u at hu
  change 0 ≤ v at hv
  apply ENNReal.ofReal_le_ofReal
  rcases le_total 0 a with ha | ha
  · have he : exp (a*u/2) ≤ exp (a*v/2) := exp_le_exp.mpr (by nlinarith)
    have h1 : 1 ≤ exp (a*u/2) := one_le_exp_iff.mpr (by nlinarith)
    nlinarith
  · have he : exp (a*v/2) ≤ exp (a*u/2) := exp_le_exp.mpr (by nlinarith)
    have h1 : exp (a*u/2) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
    nlinarith

theorem sum_upwardResampling_exponential (ω : Environment) (hω : ∀ e, 0 ≤ ω e)
    (x y : Vertex) (R : ℕ) (hR : latticeDistance x y < R)
    (a : ℝ) (ha : |a| ≤ 1/2) :
    (∑ e ∈ localEdges x R, ∫⁻ u, ENNReal.ofReal
      ((exp (a * upwardResampling ω x y R e u / 2)-1)^2) ∂expMeasure 1) ≤
      ENNReal.ofReal (2*a^2) * R := by
  apply (sum_upwardResampling_transform ω hω x y R hR _ (exponential_increment_monotone a)
    (by simp)).trans
  gcongr
  exact exponential_half_increment_square_le a ha

theorem finite_upward_exponential_sum (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (v : LocalCoordinates x R) (hv : ∀ e, 0 ≤ v e)
    (a : ℝ) (ha : |a| ≤ 1/2) :
    (∑ e : ↥(localEdges x R), ∫⁻ u, ENNReal.ofReal
      ((exp (a * max (finitePassageTime x y R (Function.update v e u) -
        finitePassageTime x y R v) 0 / 2)-1)^2) ∂expMeasure 1) ≤
      ENNReal.ofReal (2*a^2) * R := by
  classical
  have hn : ∀ e, 0 ≤ extendLocalCoordinates x R v e := by
    intro e
    unfold extendLocalCoordinates
    split_ifs with he
    · exact hv ⟨e,he⟩
    · exact le_rfl
  have h := sum_upwardResampling_exponential (extendLocalCoordinates x R v) hn x y R hR a ha
  rw [← sum_attach (localEdges x R)] at h
  simpa only [attach_eq_univ, finitePassageTime, extendLocalCoordinates_update, upwardResampling]
    using h

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_ExponentialEnergy
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma exponential_square_difference (a b t : ℝ) :
    (exp (t*b/2)-exp (t*a/2))^2 = exp (t*a)*(exp (t*(b-a)/2)-1)^2 := by
  have h₁ : exp (t*b/2) = exp (t*a/2)*exp (t*(b-a)/2) := by
    rw [← exp_add]
    congr 1
    ring
  have h₂ : exp (t*a) = exp (t*a/2)^2 := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  rw [h₁, h₂]
  ring

lemma exponential_square_difference_split (a b t : ℝ) :
    (exp (t*b/2)-exp (t*a/2))^2 =
      exp (t*a)*(exp (t*max (b-a) 0/2)-1)^2 +
      exp (t*b)*(exp (t*max (a-b) 0/2)-1)^2 := by
  rcases le_total a b with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    simp only [mul_zero, zero_div, exp_zero, sub_self, zero_pow (by omega : 2 ≠ 0),
      mul_zero, add_zero]
    exact exponential_square_difference a b t
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    simp only [mul_zero, zero_div, exp_zero, sub_self, zero_pow (by omega : 2 ≠ 0),
      mul_zero, zero_add]
    rw [sub_sq_comm]
    exact exponential_square_difference b a t

theorem exponential_resampling_energy_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : (ι → ℝ) → ℝ) (hf : Measurable f)
    (i : ι) (a : ℝ) :
    (∫⁻ z : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
      ((exp (a*f (Function.update z.1 i (z.2 i))/2)-exp (a*f z.1/2))^2)
      ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) =
    2 * (∫⁻ z : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
      (exp (a*f z.1)*(exp (a*max (f (Function.update z.1 i (z.2 i))-f z.1) 0/2)-1)^2)
      ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) := by
  let P := (Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))
  let H := fun z : (ι → ℝ) × (ι → ℝ) => ENNReal.ofReal
    (exp (a*f z.1)*(exp (a*max (f (Function.update z.1 i (z.2 i))-f z.1) 0/2)-1)^2)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hswap := lintegral_map (μ := P) hH (exchangeCoordinate_preserving μ i).measurable
  rw [(exchangeCoordinate_preserving μ i).map_eq] at hswap
  have he (x y : ℝ) : ENNReal.ofReal ((exp (a*y/2)-exp (a*x/2))^2) =
      ENNReal.ofReal (exp (a*x)*(exp (a*max (y-x) 0/2)-1)^2) +
      ENNReal.ofReal (exp (a*y)*(exp (a*max (x-y) 0/2)-1)^2) := by
    rw [exponential_square_difference_split, ENNReal.ofReal_add (by positivity) (by positivity)]
  simp_rw [he]
  rw [lintegral_add_left (by fun_prop)]
  have hb : (∫⁻ z, ENNReal.ofReal
      (exp (a*f (Function.update z.1 i (z.2 i)))*
        (exp (a*max (f z.1-f (Function.update z.1 i (z.2 i))) 0/2)-1)^2) ∂P) =
      ∫⁻ z, H z ∂P := by
    rw [hswap]
    apply lintegral_congr
    intro z
    dsimp [H]
    rw [exchangeCoordinate_resample, exchangeCoordinate_first]
  change (∫⁻ z, H z ∂P) + _ = 2*(∫⁻ z, H z ∂P)
  rw [hb, two_mul]

theorem finite_exponential_forward_energy (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : |a| ≤ 1/2) :
    (∑ e : ↥(localEdges x R), ∫⁻ z : LocalCoordinates x R × LocalCoordinates x R,
      ENNReal.ofReal (exp (a*finitePassageTime x y R z.1) *
        (exp (a*max (finitePassageTime x y R (Function.update z.1 e (z.2 e))-
          finitePassageTime x y R z.1) 0/2)-1)^2)
      ∂(Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)).prod
        (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))) ≤
    (ENNReal.ofReal (2*a^2)*R) *
      ∫⁻ v, ENNReal.ofReal (exp (a*finitePassageTime x y R v))
        ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1) := by
  classical
  let P := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)
  let F := finitePassageTime x y R
  let K := fun v e u => ENNReal.ofReal ((exp (a*max (F (Function.update v e u)-F v) 0/2)-1)^2)
  have he : ∀ e : ↥(localEdges x R),
      (∫⁻ z : LocalCoordinates x R × LocalCoordinates x R,
        ENNReal.ofReal (exp (a*F z.1))*K z.1 e (z.2 e) ∂P.prod P) =
      ∫⁻ v, ENNReal.ofReal (exp (a*F v))*(∫⁻ u, K v e u ∂expMeasure 1) ∂P := by
    intro e
    rw [lintegral_prod _ (by dsimp [K,F]; fun_prop)]
    apply lintegral_congr
    intro v
    dsimp only
    rw [lintegral_const_mul _ (show Measurable (fun w : LocalCoordinates x R => K v e (w e)) from by dsimp [K,F]; fun_prop)]
    congr 1
    have h := lintegral_map (μ := P) (show Measurable (K v e) from by dsimp [K,F]; fun_prop)
      (measurable_pi_apply e)
    rw [(measurePreserving_eval (fun _ : ↥(localEdges x R) => expMeasure 1) e).map_eq] at h
    exact h.symm
  simp_rw [ENNReal.ofReal_mul (exp_pos _).le]
  change (∑ e, ∫⁻ z : LocalCoordinates x R × LocalCoordinates x R,
    ENNReal.ofReal (exp (a*F z.1))*K z.1 e (z.2 e) ∂P.prod P) ≤ _
  simp_rw [he]
  rw [← lintegral_finsetSum _ (fun e _ => by dsimp [K,F]; fun_prop)]
  simp_rw [← mul_sum]
  calc
    _ ≤ ∫⁻ v, ENNReal.ofReal (exp (a*F v))*(ENNReal.ofReal (2*a^2)*R) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [finite_coordinates_nonnegative x R] with v hv
      gcongr
      exact finite_upward_exponential_sum x y R hR v hv a ha
    _ = _ := by
      simp_rw [mul_comm _ (ENNReal.ofReal (2*a^2)*R)]
      exact lintegral_const_mul _ (by dsimp [F]; fun_prop)

theorem finite_exponential_resampling_energy (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : |a| ≤ 1/2) :
    (∑ e : ↥(localEdges x R), ∫⁻ z : LocalCoordinates x R × LocalCoordinates x R,
      ENNReal.ofReal ((exp (a*finitePassageTime x y R (Function.update z.1 e (z.2 e))/2) -
        exp (a*finitePassageTime x y R z.1/2))^2)
      ∂(Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)).prod
        (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))) ≤
    (ENNReal.ofReal (4*a^2)*R) *
      ∫⁻ v, ENNReal.ofReal (exp (a*finitePassageTime x y R v))
        ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1) := by
  classical
  simp_rw [exponential_resampling_energy_split (expMeasure 1) (finitePassageTime x y R)
    (measurable_finitePassageTime x y R), ← mul_sum]
  have h := finite_exponential_forward_energy x y R hR a ha
  calc
    _ ≤ 2*((ENNReal.ofReal (2*a^2)*R)*
      ∫⁻ v, ENNReal.ofReal (exp (a*finitePassageTime x y R v))
        ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) := by
      gcongr
    _ = _ := by
      have he : (2 : ℝ≥0∞)*ENNReal.ofReal (2*a^2) = ENNReal.ofReal (4*a^2) := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      simp only [← mul_assoc, he]

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_BoundedEfronStein
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

lemma variance_le_integral_square_sub {f : α → ℝ} (hf : Measurable f) (c : ℝ) :
    variance f μ ≤ ∫ u, (f u-c)^2 ∂μ := by
  have h := variance_le_expectation_sq (μ := μ) (hf.sub_const c).aestronglyMeasurable
  rw [variance_sub_const hf.aestronglyMeasurable c] at h
  exact h

theorem bounded_efron_stein {f : (ι → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    variance f (Measure.pi (fun _ : ι => μ)) ≤
      ∑ i : ι, ∫ z : (ι → α) × (ι → α),
        (f (Function.update z.1 i (z.2 i)) - f z.1)^2
        ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)) := by
  apply (variance_pi_le_sum_coordinateVariance μ hf hC0 hC).trans
  apply sum_le_sum
  intro i _
  let G := fun z : (ι → α) × (ι → α) => (f (Function.update z.1 i (z.2 i))-f z.1)^2
  have hGm : Measurable G := by dsimp [G]; fun_prop
  have hGb : ∀ z, |G z| ≤ (2*C)^2 := by
    intro z
    have hb : |f (Function.update z.1 i (z.2 i))-f z.1| ≤ 2*C :=
      (abs_sub _ _).trans (by linarith [hC (Function.update z.1 i (z.2 i)), hC z.1])
    dsimp [G]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_le.mp hb]
  have hGi := (bounded_memLp_two (μ := (Measure.pi (fun _ : ι => μ)).prod
      (Measure.pi (fun _ : ι => μ))) hGm ((2*C)^2) hGb).integrable (by norm_num)
  rw [integral_prod _ hGi]
  apply integral_mono (integrable_coordinateVariance μ hf hC0 hC i) hGi.integral_prod_left
  intro v
  have he : (∫ w : ι → α, G (v,w) ∂Measure.pi (fun _ : ι => μ)) =
      ∫ u, (f (Function.update v i u)-f v)^2 ∂μ := by
    exact integral_comp_eval (μ := fun _ : ι => μ) (i := i)
      (f := fun u => (f (Function.update v i u)-f v)^2)
      (show Measurable (fun u => (f (Function.update v i u)-f v)^2) from by fun_prop).aestronglyMeasurable
  change coordinateVariance μ f i v ≤ ∫ w, G (v,w) ∂Measure.pi (fun _ : ι => μ)
  rw [he]
  exact variance_le_integral_square_sub μ (hf.comp (by fun_prop)) (f v)

theorem bounded_centered_square_lintegral {f : (ι → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    (∫⁻ v : ι → α, ENNReal.ofReal ((f v - ∫ w, f w ∂Measure.pi (fun _ : ι => μ))^2)
      ∂Measure.pi (fun _ : ι => μ)) ≤
      ∑ i : ι, ∫⁻ z : (ι → α) × (ι → α),
        ENNReal.ofReal ((f (Function.update z.1 i (z.2 i))-f z.1)^2)
        ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)) := by
  have hv := ENNReal.ofReal_le_ofReal (bounded_efron_stein μ hf hC0 hC)
  rw [variance_eq_integral hf.aemeasurable] at hv
  have hm := bounded_memLp_two (μ := Measure.pi (fun _ : ι => μ)) hf C hC
  rw [ofReal_integral_eq_lintegral_ofReal (f := fun v => (f v - ∫ w, f w ∂Measure.pi (fun _ : ι => μ))^2) (hm.sub (memLp_const _)).integrable_sq
    (by filter_upwards [] with v; positivity)] at hv
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg (fun z => sq_nonneg _))] at hv
  apply hv.trans
  apply sum_le_sum
  intro i _
  have hm : MemLp (fun z : (ι → α) × (ι → α) =>
      f (Function.update z.1 i (z.2 i))-f z.1) 2
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) := by
    apply bounded_memLp_two (by fun_prop) (2*C)
    intro z
    exact (abs_sub _ _).trans (by linarith [hC (Function.update z.1 i (z.2 i)), hC z.1])
  rw [ofReal_integral_eq_lintegral_ofReal hm.integrable_sq
    (by filter_upwards [] with z; positivity)]

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_EfronStein
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal

lemma clipReal_bound (n : ℕ) (a : ℝ) : |clipReal n a| ≤ n := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (min_le_right _ _)

lemma clipReal_lipschitz (n : ℕ) (a b : ℝ) : |clipReal n a-clipReal n b| ≤ |a-b| := by
  have h₁ := abs_max_sub_max_le_max (-(n : ℝ)) (min a n) (-(n : ℝ)) (min b n)
  have h₂ := abs_min_sub_min_le_max a (n : ℝ) b n
  simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (min a (n : ℝ)-min b n))] at h₁
  simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (a-b))] at h₂
  exact h₁.trans h₂

lemma clipReal_abs_le (n : ℕ) (a : ℝ) : |clipReal n a| ≤ |a| := by
  have h := clipReal_lipschitz n a 0
  have he : clipReal n 0 = 0 := by simp [clipReal]
  simpa only [he, sub_zero] using h

lemma clipReal_tendsto (a : ℝ) : Tendsto (fun n => clipReal n a) atTop (𝓝 a) := by
  obtain ⟨N,hN⟩ := exists_nat_ge |a|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hna : |a| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have ha := abs_le.mp hna
  simp [clipReal, min_eq_left ha.2, max_eq_right ha.1]

theorem centered_square_lintegral_le_resampling {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : (ι → α) → ℝ} (hf : Measurable f)
    (hfi : Integrable f (Measure.pi (fun _ : ι => μ))) :
    (∫⁻ v : ι → α, ENNReal.ofReal ((f v - ∫ w, f w ∂Measure.pi (fun _ : ι => μ))^2)
      ∂Measure.pi (fun _ : ι => μ)) ≤
      ∑ i : ι, ∫⁻ z : (ι → α) × (ι → α),
        ENNReal.ofReal ((f (Function.update z.1 i (z.2 i))-f z.1)^2)
        ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)) := by
  let P := Measure.pi (fun _ : ι => μ)
  let F := fun n v => clipReal n (f v)
  have hFm : ∀ n, Measurable (F n) := fun n => (measurable_clipReal n).comp hf
  have hmean : Tendsto (fun n => ∫ v, F n v ∂P) atTop (𝓝 (∫ v, f v ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun v => |f v|)
      (fun n => (hFm n).aestronglyMeasurable) hfi.abs
    · intro n
      exact .of_forall (fun v => by simpa only [Real.norm_eq_abs] using clipReal_abs_le n (f v))
    · exact .of_forall (fun v => clipReal_tendsto (f v))
  let H := fun n v => ENNReal.ofReal ((F n v - ∫ w, F n w ∂P)^2)
  have hHm : ∀ n, Measurable (H n) := by intro n; dsimp [H]; fun_prop
  have hlim : ∀ v, Tendsto (fun n => H n v) atTop
      (𝓝 (ENNReal.ofReal ((f v - ∫ w, f w ∂P)^2))) := by
    intro v
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((clipReal_tendsto (f v)).sub hmean).pow 2)
  let E := ∑ i : ι, ∫⁻ z : (ι → α) × (ι → α),
    ENNReal.ofReal ((f (Function.update z.1 i (z.2 i))-f z.1)^2) ∂P.prod P
  have hbound : ∀ n, (∫⁻ v, H n v ∂P) ≤ E := by
    intro n
    apply (bounded_centered_square_lintegral μ (hFm n) (Nat.cast_nonneg n)
      (fun v => clipReal_bound n (f v))).trans
    apply sum_le_sum
    intro i _
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    have h := clipReal_lipschitz n (f (Function.update z.1 i (z.2 i))) (f z.1)
    have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
    simpa only [sq_abs] using hs
  change (∫⁻ v, ENNReal.ofReal ((f v - ∫ w, f w ∂P)^2) ∂P) ≤ E
  calc
    _ = ∫⁻ v, liminf (fun n => H n v) atTop ∂P :=
      lintegral_congr (fun v => (hlim v).liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ v, H n v ∂P) atTop := lintegral_liminf_le hHm
    _ ≤ E := by
      apply (liminf_le_liminf (.of_forall hbound)).trans_eq
      simp

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_PassageVariance
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma finitePassageTime_mean (x y : Vertex) (R : ℕ) :
    (∫ v, finitePassageTime x y R v
      ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) =
    ∫ ω, localPassageTime ω x y R ∂environmentLaw := by
  have h₁ := integral_map (μ := environmentLaw)
    (measurable_localPassageTime x y R).aemeasurable (f := (id : ℝ → ℝ)) aestronglyMeasurable_id
  have h₂ := integral_map (μ := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))
    (measurable_finitePassageTime x y R).aemeasurable (f := (id : ℝ → ℝ)) aestronglyMeasurable_id
  rw [finitePassageTime_law] at h₁
  exact h₂.symm.trans h₁

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_PassageMGF
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma integrable_localPassageTime_exp (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : a ≤ 1/2) :
    Integrable (fun ω => exp (a*localPassageTime ω x y R)) environmentLaw := by
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  apply (integrable_trail_exp p hp.isTrail).mono' (by fun_prop)
  filter_upwards [all_edge_weights_positive] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply exp_le_exp.mpr
  have hn := (passageTime_nonneg ω (fun e => (hω e).le) (lattice_walk x y)).trans
    (passageTime_le_localPassageTime ω (fun e => (hω e).le) x y R hR)
  have hb := localPassageTime_le_pathCost ω p hp (hl.trans_lt hR)
  nlinarith

lemma integrable_finitePassageTime_exp (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : a ≤ 1/2) :
    Integrable (fun v => exp (a*finitePassageTime x y R v))
      (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) := by
  have hg : AEStronglyMeasurable (fun u : ℝ => exp (a*u))
      (Measure.map (localPassageTime · x y R) environmentLaw) := by fun_prop
  have h₁ := integrable_map_measure (μ := environmentLaw) hg
    (measurable_localPassageTime x y R).aemeasurable
  rw [finitePassageTime_law] at h₁
  have h₂ := integrable_map_measure
    (μ := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))
    (g := fun u : ℝ => exp (a*u)) (by fun_prop)
    (measurable_finitePassageTime x y R).aemeasurable
  exact h₂.mp (h₁.mpr (integrable_localPassageTime_exp x y R hR a ha))

theorem finitePassageTime_mgf_recursion (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : |a| ≤ 1/2) :
    mgf (finitePassageTime x y R) (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) a ≤
      (mgf (finitePassageTime x y R) (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) (a/2))^2 +
      (4*a^2*R) * mgf (finitePassageTime x y R)
        (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) a := by
  classical
  let P := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)
  let F := finitePassageTime x y R
  let H := fun v => exp (a*F v/2)
  have hHmeas : Measurable H := by dsimp [H,F]; fun_prop
  have hExp : Integrable (fun v => exp (a*F v)) P :=
    integrable_finitePassageTime_exp x y R hR a (le_trans (le_abs_self a) ha)
  have hs : (fun v => (H v)^2) = fun v => exp (a*F v) := by
    funext v
    dsimp [H]
    rw [pow_two, ← exp_add]
    congr 1
    ring
  have hH : MemLp H 2 P := by
    apply (memLp_two_iff_integrable_sq hHmeas.aestronglyMeasurable).mpr
    rw [hs]
    exact hExp
  have henergy := finite_exponential_resampling_energy x y R hR a ha
  have hv : ENNReal.ofReal (variance H P) ≤ ENNReal.ofReal
      ((4*a^2*R)*(∫ v, exp (a*F v) ∂P)) := by
    rw [variance_eq_integral hHmeas.aemeasurable,
      ofReal_integral_eq_lintegral_ofReal
        (f := fun v => (H v - ∫ w, H w ∂P)^2)
        (hH.sub (memLp_const _)).integrable_sq (by filter_upwards [] with v; positivity)]
    apply (centered_square_lintegral_le_resampling (expMeasure 1) hHmeas
      (hH.integrable (by norm_num))).trans
    apply henergy.trans_eq
    rw [← ofReal_integral_eq_lintegral_ofReal hExp (by filter_upwards [] with v; positivity)]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4*a^2*R),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 4*a^2), ENNReal.ofReal_natCast]
  have hM : 0 ≤ ∫ v, exp (a*F v) ∂P := integral_nonneg (fun _ => (exp_pos _).le)
  have hv' := (ENNReal.ofReal_le_ofReal_iff (by positivity :
    0 ≤ (4*a^2*R)*(∫ v, exp (a*F v) ∂P))).mp hv
  rw [variance_eq_sub hH] at hv'
  simp only [Pi.pow_apply] at hv'
  rw [hs] at hv'
  have he : (∫ v, H v ∂P) = mgf F P (a/2) := by
    unfold mgf
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro v
    dsimp [H]
    congr 1
    ring
  rw [he] at hv'
  change mgf F P a ≤ (mgf F P (a/2))^2 + (4*a^2*R)*mgf F P a
  change mgf F P a - (mgf F P (a/2))^2 ≤ (4*a^2*R)*mgf F P a at hv'
  linarith

lemma neg_log_one_sub_le (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1/2) :
    -log (1-q) ≤ 2*q := by
  have hp : 0 < 1-q := by linarith
  have h := log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [log_inv] at h
  have hb : (1-q)⁻¹ - 1 ≤ 2*q := by
    rw [inv_eq_one_div]
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hp).mpr
    nlinarith
  exact h.trans hb

theorem finitePassageTime_cgf_recursion (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : |a| ≤ 1/2)
    (hq : 4*a^2*R ≤ 1/2) :
    cgf (finitePassageTime x y R) (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) a ≤
      2*cgf (finitePassageTime x y R) (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) (a/2)
        + 8*a^2*R := by
  let P := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)
  let F := finitePassageTime x y R
  have hM : 0 < mgf F P a := mgf_pos (integrable_finitePassageTime_exp x y R hR a
    ((le_abs_self a).trans ha))
  have hM2 : 0 < mgf F P (a/2) := mgf_pos (integrable_finitePassageTime_exp x y R hR (a/2)
    (by have := (le_abs_self a).trans ha; linarith))
  have hrec := finitePassageTime_mgf_recursion x y R hR a ha
  have hden : 0 < 1-4*a^2*R := by linarith
  have hr : mgf F P a ≤ (mgf F P (a/2))^2/(1-4*a^2*R) := by
    apply (le_div_iff₀ hden).mpr
    change mgf F P a ≤ (mgf F P (a/2))^2 + (4*a^2*R)*mgf F P a at hrec
    nlinarith
  have hl := log_le_log hM hr
  rw [log_div (pow_ne_zero _ hM2.ne') hden.ne', log_pow] at hl
  have hlog := neg_log_one_sub_le (4*a^2*R) (by positivity) hq
  change log (mgf F P a) ≤ 2*log (mgf F P (a/2)) + 8*a^2*R
  norm_num only [Nat.cast_ofNat] at hl
  linarith

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_DyadicMGF
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Filter Topology

theorem dyadic_derivative_bound (G : ℝ → ℝ) (a m K : ℝ) (hK : 0 ≤ K)
    (hzero : G 0 = 0) (hd : HasDerivAt G m 0)
    (hrec : ∀ n : ℕ, G (a*(1/2 : ℝ)^n) ≤
      2*G (a*(1/2 : ℝ)^(n+1)) + K*((1/2 : ℝ)^n)^2) :
    G a ≤ a*m+2*K := by
  have hi : ∀ n : ℕ, G a ≤ G (a*(1/2 : ℝ)^n)/(1/2 : ℝ)^n +
      2*K*(1-(1/2 : ℝ)^n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : 0 < (1/2 : ℝ)^n := pow_pos (by norm_num) n
      have hdiv := div_le_div_of_nonneg_right (hrec n) hn.le
      calc
        _ ≤ G (a*(1/2 : ℝ)^n)/(1/2 : ℝ)^n + 2*K*(1-(1/2 : ℝ)^n) := ih
        _ ≤ (2*G (a*(1/2 : ℝ)^(n+1))+K*((1/2 : ℝ)^n)^2)/(1/2 : ℝ)^n +
            2*K*(1-(1/2 : ℝ)^n) := add_le_add hdiv le_rfl
        _ = _ := by
          rw [pow_succ]
          field_simp
          ring
  by_cases ha : a = 0
  · subst a
    simp only [hzero, zero_mul, zero_add]
    positivity
  have hp : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb : Tendsto (fun n : ℕ => a*(1/2 : ℝ)^n) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using hp.const_mul a
    · exact .of_forall (fun n => by simp [ha])
  have hsl := (hd.tendsto_slope.comp hb).const_mul a
  have hmain : Tendsto (fun n : ℕ => G (a*(1/2 : ℝ)^n)/(1/2 : ℝ)^n)
      atTop (𝓝 (a*m)) := by
    convert hsl using 1
    funext n
    simp only [Function.comp_def, slope, sub_zero, hzero, smul_eq_mul, vsub_eq_sub, sub_zero]
    field_simp [ha]
  have hc : Tendsto (fun n : ℕ => 2*K*(1-(1/2 : ℝ)^n)) atTop (𝓝 (2*K)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).const_mul (2*K)
  exact ge_of_tendsto (hmain.add hc) (.of_forall hi)

theorem finitePassageTime_cgf_centered (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : |a| ≤ 1/2)
    (hq : 4*a^2*R ≤ 1/2) :
    cgf (finitePassageTime x y R) (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) a ≤
      a*(∫ v, finitePassageTime x y R v
        ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) + 16*a^2*R := by
  let P := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)
  let F := finitePassageTime x y R
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet F P) := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
    intro t ht
    exact integrable_finitePassageTime_exp x y R hR t ht.le
  have hd : HasDerivAt (cgf F P) (∫ v, F v ∂P) 0 := by
    have h := (analyticAt_cgf h0).differentiableAt.hasDerivAt
    rw [deriv_cgf_zero h0] at h
    simpa using h
  have hb := dyadic_derivative_bound (cgf F P) a (∫ v, F v ∂P) (8*a^2*R)
    (by positivity) (cgf_zero (X := F) (μ := P)) hd (fun n => ?_)
  · convert hb using 1; ring
  have hn0 : 0 ≤ (1/2 : ℝ)^n := by positivity
  have hn1 : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have han : |a*(1/2 : ℝ)^n| ≤ 1/2 := by
    rw [abs_mul, abs_of_nonneg hn0]
    calc
      _ ≤ |a| * 1 := mul_le_mul_of_nonneg_left hn1 (abs_nonneg a)
      _ ≤ _ := by simpa using ha
  have hqn : 4*(a*(1/2 : ℝ)^n)^2*R ≤ 1/2 := by
    have hs : ((1/2 : ℝ)^n)^2 ≤ 1 := by nlinarith
    calc
      _ = (4*a^2*R)*((1/2 : ℝ)^n)^2 := by ring
      _ ≤ (4*a^2*R)*1 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ _ := by simpa using hq
  have hr := finitePassageTime_cgf_recursion x y R hR (a*(1/2 : ℝ)^n) han hqn
  have he : a*(1/2 : ℝ)^n/2 = a*(1/2 : ℝ)^(n+1) := by rw [pow_succ]; ring
  rw [he] at hr
  convert hr using 1; ring

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_CenteredConcentration
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

theorem finitePassageTime_centered_exponential (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (t : ℝ) :
    (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))
      {v | t*sqrt R ≤ |finitePassageTime x y R v - ∫ w, finitePassageTime x y R w
        ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)|} ≤
      2*ENNReal.ofReal (exp (1-t/4)) := by
  let P := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)
  let F := finitePassageTime x y R
  let M := ∫ v, F v ∂P
  let a : ℝ := 1/(4*sqrt R)
  have hpos : 0 < R := lt_of_le_of_lt (Nat.zero_le _) hR
  have hs : 0 < sqrt R := sqrt_pos.mpr (by exact_mod_cast hpos)
  have hs1 : 1 ≤ sqrt R := by
    have hr : (1 : ℝ) ≤ R := by exact_mod_cast hpos
    nlinarith [sq_sqrt (Nat.cast_nonneg R), sqrt_nonneg (R : ℝ)]
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1/2 := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : 0 < 4*sqrt R)).mpr
    linarith
  have has : a*sqrt R = 1/4 := by dsimp [a]; field_simp
  have ha2 : a^2*R = 1/16 := by
    calc
      _ = (a*sqrt R)^2 := by rw [mul_pow, sq_sqrt (Nat.cast_nonneg R)]
      _ = _ := by rw [has]; norm_num
  have hc := finitePassageTime_cgf_centered x y R hR a
    (by rwa [abs_of_pos ha]) (by nlinarith [ha2])
  have hcn := finitePassageTime_cgf_centered x y R hR (-a)
    (by simpa only [abs_neg, abs_of_pos ha] using ha1) (by nlinarith [ha2])
  have hu : P.real {v | M+t*sqrt R ≤ F v} ≤ exp (1-t/4) := by
    apply (measure_ge_le_exp_cgf (μ := P) (X := F) (M+t*sqrt R) ha.le
      (integrable_finitePassageTime_exp x y R hR a ha1)).trans
    apply exp_le_exp.mpr
    change cgf F P a ≤ a*M+16*a^2*R at hc
    calc
      _ ≤ -a*(M+t*sqrt R)+(a*M+16*a^2*R) := add_le_add le_rfl hc
      _ = _ := by
        rw [show -a*(M+t*sqrt R)+(a*M+16*a^2*R) = 16*(a^2*R)-t*(a*sqrt R) by ring,
          ha2, has]
        ring
  have hl : P.real {v | F v ≤ M-t*sqrt R} ≤ exp (1-t/4) := by
    apply (measure_le_le_exp_cgf (μ := P) (X := F) (M-t*sqrt R) (neg_nonpos.mpr ha.le)
      (integrable_finitePassageTime_exp x y R hR (-a) (by linarith))).trans
    apply exp_le_exp.mpr
    change cgf F P (-a) ≤ (-a)*M+16*(-a)^2*R at hcn
    calc
      _ ≤ -(-a)*(M-t*sqrt R)+((-a)*M+16*(-a)^2*R) := add_le_add le_rfl hcn
      _ = _ := by
        rw [show -(-a)*(M-t*sqrt R)+((-a)*M+16*(-a)^2*R) =
          16*(a^2*R)-t*(a*sqrt R) by ring, ha2, has]
        ring
  have hu' : P {v | M+t*sqrt R ≤ F v} ≤ ENNReal.ofReal (exp (1-t/4)) := by
    have h := ENNReal.ofReal_le_ofReal hu
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
  have hl' : P {v | F v ≤ M-t*sqrt R} ≤ ENNReal.ofReal (exp (1-t/4)) := by
    have h := ENNReal.ofReal_le_ofReal hl
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
  have hsub : {v | t*sqrt R ≤ |F v-M|} ⊆
      {v | M+t*sqrt R ≤ F v} ∪ {v | F v ≤ M-t*sqrt R} := by
    intro v hv
    change t*sqrt R ≤ |F v-M| at hv
    rcases le_total M (F v) with h | h
    · left
      change M+t*sqrt R ≤ F v
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hv
      linarith
    · right
      change F v ≤ M-t*sqrt R
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hv
      linarith
  change P {v | t*sqrt R ≤ |F v-M|} ≤ _
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  simpa only [two_mul] using add_le_add hu' hl'

theorem localPassageTime_centered_exponential (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (t : ℝ) :
    environmentLaw {ω | t*sqrt R ≤ |localPassageTime ω x y R -
      ∫ η, localPassageTime η x y R ∂environmentLaw|} ≤ 2*ENNReal.ofReal (exp (1-t/4)) := by
  let S := {u : ℝ | t*sqrt R ≤ |u - ∫ η, localPassageTime η x y R ∂environmentLaw|}
  have hsub : Measurable (fun u : ℝ =>
      u - ∫ η, localPassageTime η x y R ∂environmentLaw) :=
    measurable_id.sub measurable_const
  have hS : MeasurableSet S := by
    exact measurableSet_le measurable_const (by
      simpa only [Real.norm_eq_abs] using hsub.norm)
  have h₁ := Measure.map_apply (μ := environmentLaw) (measurable_localPassageTime x y R) hS
  have h₂ := Measure.map_apply (μ := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) (measurable_finitePassageTime x y R) hS
  rw [finitePassageTime_law] at h₁
  have he := h₁.symm.trans h₂
  change environmentLaw ((localPassageTime · x y R) ⁻¹' S) ≤ _
  rw [he]
  dsimp [S]
  rw [← finitePassageTime_mean]
  exact finitePassageTime_centered_exponential x y R hR t

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_CenteredLocalization
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real

theorem passageTime_centered_large (x y : Vertex) (hd : 1 ≤ latticeDistance x y)
    (u : ℝ) (hu : 4*(latticeDistance x y : ℝ) ≤ u) :
    environmentLaw.real {ω : Environment |
      u ≤ |passageTime ω x y - ∫ η : Environment, passageTime η x y ∂environmentLaw|} ≤
      exp (-u/4) := by
  have hm := mean_passageTime_le_distance x y
  have hm0 := mean_passageTime_nonneg x y
  have hd' : (1 : ℝ) ≤ latticeDistance x y := by exact_mod_cast hd
  have hsub : environmentLaw {ω : Environment |
      u ≤ |passageTime ω x y - ∫ η : Environment, passageTime η x y ∂environmentLaw|} ≤
      environmentLaw {ω : Environment | u ≤ passageTime ω x y} := by
    apply measure_mono_ae
    filter_upwards [passageTime_properties] with ω hω
    intro he
    have hn := hω.1 x y
    change u ≤ passageTime ω x y
    rcases le_abs.mp he with he | he <;> linarith
  apply (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans
  apply (passageTime_upper_tail x y u).trans
  rw [show (2 : ℝ)^latticeDistance x y = exp ((latticeDistance x y : ℝ)*log 2) by
    rw [exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)], ← exp_add, exp_le_exp]
  have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  nlinarith

theorem passageTime_centered_large_sqrt (x y : Vertex) (hd : 1 ≤ latticeDistance x y)
    (t : ℝ) (ht : 4*sqrt (latticeDistance x y) ≤ t) :
    environmentLaw.real {ω : Environment |
      t*sqrt (latticeDistance x y) ≤
        |passageTime ω x y - ∫ η : Environment, passageTime η x y ∂environmentLaw|} ≤
      exp (-t/4) := by
  have hd' : (1 : ℝ) ≤ latticeDistance x y := by exact_mod_cast hd
  have hs := sqrt_nonneg (latticeDistance x y : ℝ)
  have hsq := sq_sqrt (show 0 ≤ (latticeDistance x y : ℝ) by positivity)
  have hs1 : 1 ≤ sqrt (latticeDistance x y : ℝ) := by nlinarith
  have ht0 : 0 ≤ t := by linarith
  apply (passageTime_centered_large x y hd (t*sqrt (latticeDistance x y))
    (by nlinarith)).trans
  rw [exp_le_exp]
  nlinarith

theorem localPassageTime_center_shift (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) :
    |(∫ ω : Environment, localPassageTime ω x y R ∂environmentLaw) -
      (∫ ω : Environment, passageTime ω x y ∂environmentLaw)| ≤
        ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) := by
  have hd : latticeDistance x y < R := by omega
  have hn : 0 ≤ (∫ ω : Environment, localPassageTime ω x y R ∂environmentLaw) -
      (∫ ω : Environment, passageTime ω x y ∂environmentLaw) := by
    apply sub_nonneg.mpr
    apply integral_mono_ae (integrable_passageTime x y) (integrable_localPassageTime x y R hd)
    filter_upwards [all_edge_weights_positive] with ω hω
    exact passageTime_le_localPassageTime ω (fun e => (hω e).le) x y R hd
  rw [abs_of_nonneg hn, ← integral_sub (integrable_localPassageTime x y R hd)
    (integrable_passageTime x y)]
  exact localPassageTime_mean_error_exponential x y R hR hscale

theorem passageTime_centered_localization (x y : Vertex) (R : ℕ) (hR : 1 ≤ R)
    (hscale : 40*latticeDistance x y ≤ R) (u : ℝ) :
    environmentLaw.real {ω : Environment |
      u ≤ |passageTime ω x y - ∫ η : Environment, passageTime η x y ∂environmentLaw|} ≤
      (11/3 : ℝ)*exp (-(log 2/40)*R) +
      environmentLaw.real {ω : Environment |
        u - ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) ≤
          |localPassageTime ω x y R -
            ∫ η : Environment, localPassageTime η x y R ∂environmentLaw|} := by
  let F := {ω : Environment | localPassageTime ω x y R ≠ passageTime ω x y}
  let G := {ω : Environment |
    u - ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) ≤
      |localPassageTime ω x y R -
        ∫ η : Environment, localPassageTime η x y R ∂environmentLaw|}
  have hs : {ω : Environment |
      u ≤ |passageTime ω x y - ∫ η : Environment, passageTime η x y ∂environmentLaw|} ⊆
      F ∪ G := by
    intro ω hω
    by_cases hf : ω ∈ F
    · exact Or.inl hf
    · right
      have he : localPassageTime ω x y R = passageTime ω x y := not_not.mp hf
      have hb := abs_add_le (localPassageTime ω x y R -
        ∫ η : Environment, localPassageTime η x y R ∂environmentLaw)
        ((∫ η : Environment, localPassageTime η x y R ∂environmentLaw) -
        ∫ η : Environment, passageTime η x y ∂environmentLaw)
      rw [sub_add_sub_cancel, he] at hb
      have hc := localPassageTime_center_shift x y R hR hscale
      change u ≤ |passageTime ω x y - ∫ η : Environment, passageTime η x y ∂environmentLaw| at hω
      change u - ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) ≤
        |localPassageTime ω x y R - ∫ η : Environment, localPassageTime η x y R ∂environmentLaw|
      rw [he]
      linarith
  apply (measureReal_mono hs).trans
  apply (measureReal_union_le F G).trans
  exact add_le_add (localPassageTime_failure_probability x y R hR hscale) le_rfl

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_MetricConcentration
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real

lemma localization_shift_uniform (R : ℕ) :
    ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) ≤ 300 := by
  have hlog := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hlog
  have hc : 1/80 ≤ log 2/40 := by linarith
  have hn : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
  have he : exp (-(log 2/40)*R) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hb : (R : ℝ)/80 ≤ exp ((log 2/40)*R) := by
    have hp := mul_le_mul_of_nonneg_right hc hn
    linarith [add_one_le_exp ((log 2/40)*R)]
  have hm := mul_le_mul_of_nonneg_right hb (exp_pos (-(log 2/40)*R)).le
  have hid : exp ((log 2/40)*R)*exp (-(log 2/40)*R) = 1 := by
    rw [← exp_add]
    convert exp_zero using 2; ring
  rw [hid] at hm
  nlinarith

lemma sqrt_sixtyfour_mul (d : ℕ) : sqrt ((64*d : ℕ) : ℝ) = 8*sqrt d := by
  rw [Nat.cast_mul, Nat.cast_ofNat, sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)]
  have he : sqrt (64 : ℝ) = 8 := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 64), sqrt_nonneg (64 : ℝ)]
  rw [he]

theorem passageTime_centered_intermediate (x y : Vertex) (hd : 1 ≤ latticeDistance x y)
    (t : ℝ) (ht : 600 ≤ t) (ht' : t ≤ 4*sqrt (latticeDistance x y)) :
    environmentLaw.real {ω | t*sqrt (latticeDistance x y) ≤
      |passageTime ω x y - ∫ η, passageTime η x y ∂environmentLaw|} ≤
      (2*exp 1+4)*exp (-t/64) := by
  let d := latticeDistance x y
  let R := 64*d
  have hR : 1 ≤ R := by dsimp [R,d]; omega
  have hscale : 40*latticeDistance x y ≤ R := by dsimp [R,d]; omega
  have hRd : latticeDistance x y < R := by dsimp [R,d]; omega
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ sqrt d := sqrt_nonneg _
  have hs1 : 1 ≤ sqrt d := by nlinarith [sq_sqrt (Nat.cast_nonneg d)]
  have hsd : sqrt d ≤ d := by nlinarith [sq_sqrt (Nat.cast_nonneg d)]
  have ht0 : 0 ≤ t := by linarith
  have hmean := localization_shift_uniform R
  have hthreshold : (t/16)*sqrt R ≤
      t*sqrt d - ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) := by
    rw [show R = 64*d from rfl, sqrt_sixtyfour_mul]
    have hprod := mul_le_mul_of_nonneg_left hs1 ht0
    nlinarith
  have hlocal := localPassageTime_centered_exponential x y R hRd (t/16)
  have hlocal' := ENNReal.toReal_mono (by finiteness) hlocal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (exp_pos _).le] at hlocal'
  have hlog := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hlog
  have hdecay : exp (-(log 2/40)*R) ≤ exp (-t/64) := by
    apply exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg d)
    dsimp [R]
    push_cast
    change t ≤ 4*sqrt d at ht'
    nlinarith
  apply (passageTime_centered_localization x y R hR hscale (t*sqrt d)).trans
  have hsub : environmentLaw.real {ω |
      t*sqrt d - ((11/3 : ℝ)*R+4)*exp (-(log 2/40)*R) ≤
        |localPassageTime ω x y R - ∫ η, localPassageTime η x y R ∂environmentLaw|} ≤
      environmentLaw.real {ω | (t/16)*sqrt R ≤
        |localPassageTime ω x y R - ∫ η, localPassageTime η x y R ∂environmentLaw|} :=
    measureReal_mono (fun _ h => hthreshold.trans h)
  calc
    _ ≤ (11/3 : ℝ)*exp (-t/64) + 2*exp (1-t/16/4) :=
      add_le_add (mul_le_mul_of_nonneg_left hdecay (by norm_num)) (hsub.trans hlocal')
    _ ≤ (2*exp 1+4)*exp (-t/64) := by
      rw [show 1-t/16/4 = 1+(-t/64) by ring, exp_add]
      nlinarith [exp_pos (-t/64)]

theorem passageTime_centered_concentration (x y : Vertex) (hd : 1 ≤ latticeDistance x y)
    (t : ℝ) (_ht : 0 ≤ t) :
    environmentLaw.real {ω | t*sqrt (latticeDistance x y) ≤
      |passageTime ω x y - ∫ η, passageTime η x y ∂environmentLaw|} ≤
      ((2*exp 1+4)*exp 10)*exp (-t/64) := by
  have hC : 1 ≤ 2*exp 1+4 := by linarith [exp_pos 1]
  have h10 : 1 ≤ exp (10 : ℝ) := one_le_exp_iff.mpr (by norm_num)
  by_cases hs : t ≤ 600
  · have hp : environmentLaw.real {ω | t*sqrt (latticeDistance x y) ≤
        |passageTime ω x y - ∫ η, passageTime η x y ∂environmentLaw|} ≤ 1 := by
      simp
    apply hp.trans
    rw [mul_assoc, ← exp_add]
    have he : 1 ≤ exp (10+-t/64) := one_le_exp_iff.mpr (by linarith)
    nlinarith
  · by_cases hl : 4*sqrt (latticeDistance x y) ≤ t
    · apply (passageTime_centered_large_sqrt x y hd t hl).trans
      have he : exp (-t/4) ≤ exp (-t/64) := exp_le_exp.mpr (by linarith)
      apply he.trans
      have hprod : (1 : ℝ) ≤ (2*exp 1+4)*exp 10 :=
        by simpa only [one_mul] using (mul_le_mul hC h10 (by norm_num) (by linarith))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod (exp_pos (-t/64)).le
    · apply (passageTime_centered_intermediate x y hd t (by linarith) (by linarith)).trans
      have hnon : 0 ≤ (2*exp 1+4)*exp (-t/64) := by positivity
      have hprod := mul_le_mul_of_nonneg_left h10 hnon
      nlinarith [hprod]

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_DirectionalConvergence
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Filter Topology

lemma exp_neg_sqrt_le (a m : ℝ) (ha : 0 < a) (hm : 0 < m) :
    exp (-(a*sqrt m)) ≤ (24/a^4)/m^2 := by
  have h := Real.pow_div_factorial_le_exp (a*sqrt m) (by positivity) 4
  have hs := sq_sqrt hm.le
  have he : (a*sqrt m)^4 = a^4*m^2 := by
    rw [mul_pow, show sqrt m^4 = (sqrt m^2)^2 by ring, hs]
  rw [he] at h
  norm_num at h
  rw [exp_neg, ← one_div, div_div]
  apply (div_le_div_iff₀ (exp_pos _) (by positivity)).mpr
  nlinarith

lemma summable_exp_neg_sqrt (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => exp (-(a*sqrt (n+1)))) := by
  have h := ((summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).comp_injective
    (show Function.Injective (fun n : ℕ => n+1) from fun _ _ h => Nat.add_right_cancel h)).mul_left (24/a^4)
  apply h.of_nonneg_of_le (fun n => (exp_pos _).le)
  intro n
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_one_div] using exp_neg_sqrt_le a (n+1) ha (by positivity)

lemma directional_centered_tail (x : Vertex) (hx : x ≠ 0) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    environmentLaw.real {ω | ε*(n+1) ≤
      |passageTime ω 0 (scaleVertex (n+1) x)-meanPassageSequence x (n+1)|} ≤
      ((2*exp 1+4)*exp 10)*exp (-((ε/(64*sqrt (latticeDistance 0 x)))*sqrt (n+1))) := by
  have hd : 0 < latticeDistance 0 x := by
    by_contra h
    have hz : latticeDistance 0 x = 0 := by omega
    apply hx
    ext <;> simp_all [latticeDistance]
  have hd' : (0 : ℝ) < latticeDistance 0 x := by exact_mod_cast hd
  have hm : 1 ≤ latticeDistance 0 (scaleVertex (n+1) x) := by
    rw [latticeDistance_scaleVertex]
    nlinarith
  have ht := passageTime_centered_concentration 0 (scaleVertex (n+1) x) hm
    ((ε/sqrt (latticeDistance 0 x))*sqrt (n+1)) (by positivity)
  rw [latticeDistance_scaleVertex, Nat.cast_mul, Nat.cast_add, Nat.cast_one, sqrt_mul (by positivity)] at ht
  have he : ε/sqrt (latticeDistance 0 x)*sqrt (n+1)*
      (sqrt (n+1)*sqrt (latticeDistance 0 x)) = ε*(n+1) := by
    have hs : sqrt (latticeDistance 0 x) ≠ 0 := (sqrt_pos.mpr hd').ne'
    have hn := sq_sqrt (show (0 : ℝ) ≤ n+1 by positivity)
    field_simp
    nlinarith
  rw [he] at ht
  convert ht using 1 <;> try rfl
  congr 2
  ring

lemma ae_directional_centered_small (x : Vertex) (hx : x ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂environmentLaw, ∀ᶠ n : ℕ in atTop,
      |passageTime ω 0 (scaleVertex (n+1) x)-meanPassageSequence x (n+1)| < ε*(n+1) := by
  have hd : (0 : ℝ) < latticeDistance 0 x := by
    have h : 0 < latticeDistance 0 x := by
      by_contra h
      have hz : latticeDistance 0 x = 0 := by omega
      apply hx
      ext <;> simp_all [latticeDistance]
    exact_mod_cast h
  have hs := (summable_exp_neg_sqrt (ε/(64*sqrt (latticeDistance 0 x))) (by positivity)).mul_left
    ((2*exp 1+4)*exp 10)
  have hsum : Summable (fun n : ℕ => environmentLaw.real {ω |
      ε*(n+1) ≤ |passageTime ω 0 (scaleVertex (n+1) x)-meanPassageSequence x (n+1)|}) :=
    hs.of_nonneg_of_le (fun _ => measureReal_nonneg) (directional_centered_tail x hx ε hε)
  have hsum' : (∑' n : ℕ, environmentLaw {ω |
      ε*(n+1) ≤ |passageTime ω 0 (scaleVertex (n+1) x)-meanPassageSequence x (n+1)|}) ≠ ⊤ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hsum.tsum_ofReal_ne_top
  simpa only [Set.mem_ofPred_eq, not_le] using ae_eventually_notMem hsum'

theorem passageTime_directional_tendsto (x : Vertex) :
    ∀ᵐ ω ∂environmentLaw,
      Tendsto (fun n : ℕ => passageTime ω 0 (scaleVertex n x)/(n : ℝ)) atTop
        (𝓝 (directionalMeanConstant x)) := by
  by_cases hx : x = 0
  · subst x
    have hm : directionalMeanConstant 0 = 0 := by
      apply le_antisymm _ (directionalMeanConstant_nonneg 0)
      apply (directionalMeanConstant_le_mean 0).trans_eq
      apply integral_eq_zero_of_ae
      filter_upwards [passageTime_properties] with ω hω
      exact hω.2.1 0
    filter_upwards [passageTime_properties] with ω hω
    have hz : ∀ n, scaleVertex n (0 : Vertex) = 0 := by intro n; ext <;> simp [scaleVertex]
    simp_rw [hz, hω.2.1 0, zero_div, hm]
    exact tendsto_const_nhds
  · have hall : ∀ᵐ ω ∂environmentLaw, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
        |passageTime ω 0 (scaleVertex (n+1) x)-meanPassageSequence x (n+1)| <
          (1/(k+1 : ℝ))*(n+1) :=
      ae_all_iff.mpr (fun k => ae_directional_centered_small x hx (1/(k+1)) (by positivity))
    filter_upwards [hall] with ω hω
    have hz : Tendsto (fun n : ℕ =>
        (passageTime ω 0 (scaleVertex (n+1) x)-meanPassageSequence x (n+1))/(n+1 : ℝ))
        atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
      filter_upwards [hω k] with n hn
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (by positivity : (0 : ℝ) < n+1)]
      exact ((div_lt_iff₀ (by positivity : (0 : ℝ) < n+1)).mpr hn).trans hk
    have hm := (meanPassageSequence_tendsto x).comp (tendsto_add_atTop_nat 1)
    have ht := hz.add hm
    have hs : Tendsto (fun n : ℕ => passageTime ω 0 (scaleVertex (n+1) x)/(n+1 : ℝ))
        atTop (𝓝 (directionalMeanConstant x)) := by
      simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, sub_div, sub_add_cancel, zero_add] using ht
    exact (tendsto_add_atTop_iff_nat 1).mp (by simpa only [Nat.cast_add, Nat.cast_one] using hs)

theorem passageTime_all_directions_tendsto :
    ∀ᵐ ω ∂environmentLaw, ∀ x : Vertex,
      Tendsto (fun n : ℕ => passageTime ω 0 (scaleVertex n x)/(n : ℝ)) atTop
        (𝓝 (directionalMeanConstant x)) :=
  ae_all_iff.mpr passageTime_directional_tendsto

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_TimeConstantNorm
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Filter Topology Set
open scoped NNReal

theorem actualTimeNorm_hasTimeConstant : HasTimeConstant actualTimeNorm := by
  filter_upwards [passageTime_all_directions_tendsto] with ω hω
  intro x
  change Tendsto (fun n : ℕ => passageTime ω (0 : Vertex) (scaleVertex n x)/(n : ℝ))
    atTop (𝓝 (timeSeminorm (embed x)))
  rw [timeSeminorm_embed]
  exact hω x

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ActualTimeConstant
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actualSourceTimeConstant_lattice_limits_oai (h : ExponentialEnvironment P τ) :
    ∀ᵐ ω ∂P, ∀ z : Vertex,
      Tendsto (fun n : ℕ => passageTime (fun e => τ e ω) 0 (n • z)/n) atTop
        (𝓝 (actualSourceTimeConstant (latticeEmbed z))) := by
  have hm : MeasurePreserving (fun ω => companionWeights (fun e => τ e ω)) P
      CompanionFPP.environmentLaw := ⟨measurable_companionWeights h.measurable,h.companionLaw⟩
  filter_upwards [hm.quasiMeasurePreserving.ae CompanionFPP.actualTimeNorm_hasTimeConstant] with ω hω
  intro z
  have hz := hω z
  simp only [companion_passageTime_eq] at hz
  have he (n : ℕ) : CompanionFPP.scaleVertex n z = n • z := by
    ext <;> simp [CompanionFPP.scaleVertex,nsmul_eq_mul]
  simp only [he] at hz
  exact hz

end PlanarFPP

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PlanarFPP.actualSourceTimeConstant_lattice_limits_oai.{u_1} := @OAI.PlanarFPP.actualSourceTimeConstant_lattice_limits_oai.{u_1}
