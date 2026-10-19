-- Prove2me | solution 1 for OAI.HyperedgeComparison.exact_cluster_independent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:36:17.220048+00:00
-- url     : https://prove2.me/submissions/9a07c0b1-7866-4c72-96e8-cffbba4b1e66

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
theorem hc_indep_disjoint_bits {E : Type*} [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (f g : (E → Bool) → ℝ)
    (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hg : ∀ ω ω', (∀ e ∉ J, ω' e = ω e) → g ω' = g ω) :
    IndepFun f g (law p) := by
  have hI : iIndepFun (fun (e : E) (ω : E → Bool) => ω e) (law p) := by
    unfold law
    exact iIndepFun_pi (X := fun _ (b : Bool) => b) (fun _ => measurable_id.aemeasurable)
  have h2 := hI.indepFun_finset J Jᶜ disjoint_compl_right (fun e => measurable_pi_apply e)
  let F : (J → Bool) → ℝ := fun ξ => f (fun e => if h : e ∈ J then ξ ⟨e, h⟩ else false)
  let G : ((Jᶜ : Finset E) → Bool) → ℝ :=
    fun ξ => g (fun e => if h : e ∈ Jᶜ then ξ ⟨e, h⟩ else false)
  have hF : f = F ∘ (fun ω (i : J) => ω i) := by
    funext ω
    exact (hf _ _ (fun e he => by simp [he])).symm
  have hG : g = G ∘ (fun ω (i : (Jᶜ : Finset E)) => ω i) := by
    funext ω
    refine (hg _ _ (fun e he => ?_)).symm
    have : e ∈ Jᶜ := Finset.mem_compl.mpr he
    simp [this]
  rw [hF, hG]
  exact h2.comp (Measurable.of_discrete) (Measurable.of_discrete)

theorem hc_clusters_eq_of_agree {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E} {ω ω' : E → Bool}
    {D S : Set V}
    (hagree : ∀ e, ¬ Disjoint (H e) (OAI.HyperedgeComparison.clusters H ω D S) → ω' e = ω e) :
    OAI.HyperedgeComparison.clusters H ω' D S = OAI.HyperedgeComparison.clusters H ω D S := by
  open OAI.HyperedgeComparison in
  have key : ∀ s ∈ S, ∀ y, (Connected H ω' D s y ↔ Connected H ω D s y) := by
    intro s hs y
    constructor
    · intro h
      induction h with
      | refl => exact .refl
      | @tail z w hsz hab ih =>
        obtain ⟨e, h1, h2, h3, h4⟩ := hab
        have hzC : z ∈ clusters H ω D S := ⟨s, hs, ih⟩
        have : ω' e = ω e := hagree e (Set.not_disjoint_iff.mpr ⟨z, h3, hzC⟩)
        exact Relation.ReflTransGen.tail ih ⟨e, this ▸ h1, h2, h3, h4⟩
    · intro h
      induction h with
      | refl => exact .refl
      | @tail z w hsz hab ih =>
        obtain ⟨e, h1, h2, h3, h4⟩ := hab
        have hzC : z ∈ clusters H ω D S := ⟨s, hs, hsz⟩
        have : ω' e = ω e := hagree e (Set.not_disjoint_iff.mpr ⟨z, h3, hzC⟩)
        exact Relation.ReflTransGen.tail ih ⟨e, this.trans h1, h2, h3, h4⟩
  ext y
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (key s hs y).mp h⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (key s hs y).mpr h⟩

theorem solution (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S W : Set V) (g : (E → Bool) → ℝ)
    (hg : ∀ ω ω', (∀ e, Disjoint (H e) W → ω' e = ω e) → g ω' = g ω) :
    IndepFun (fun ω => if clusters H ω D S = W then (1 : ℝ) else 0) g (law p) := by
  refine hc_indep_disjoint_bits p (Finset.univ.filter (fun e => ¬ Disjoint (H e) W)) _ g ?_ ?_
  · intro ω ω' hag
    by_cases h : clusters H ω D S = W
    · have : clusters H ω' D S = W := by
        rw [hc_clusters_eq_of_agree (fun e he => hag e (by simp [h ▸ he])), h]
      simp [h, this]
    · have : clusters H ω' D S ≠ W := by
        intro h'
        apply h
        rw [← h']
        exact hc_clusters_eq_of_agree (fun e he => (hag e (by simpa [h'] using he)).symm)
      simp [h, this]
  · intro ω ω' hag
    exact hg ω ω' (fun e he => hag e (by simpa using he))

