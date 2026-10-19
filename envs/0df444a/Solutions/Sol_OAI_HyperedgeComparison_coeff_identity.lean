-- Prove2me | solution 1 for OAI.HyperedgeComparison.coeff_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:46:11.907271+00:00
-- url     : https://prove2.me/submissions/af09a882-33dc-4ebd-9e0a-e61a30f3ac27

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

theorem hc_exact_indep {V E : Type*} [Fintype E] (H : Hypergraph V E)
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

theorem hc_exact_mul {V E : Type*} [Fintype E] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S W : Set V) (g : (E → Bool) → ℝ)
    (hg : ∀ ω ω', (∀ e, Disjoint (H e) W → ω' e = ω e) → g ω' = g ω) :
    (∫ ω, (if clusters H ω D S = W then g ω else 0) ∂law p) =
      clusterMass H p D S W * ∫ ω, g ω ∂law p := by
  have := (hc_exact_indep H p D S W g hg).integral_fun_mul_eq_mul_integral
    Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable
  rw [clusterMass, ← this]
  congr 1; funext ω; split_ifs <;> simp

theorem hc_decomp {V E : Type*} [Fintype E] [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S : Set V) (h : (E → Bool) → ℝ) :
    (∫ ω, h ω ∂law p) =
      ∑ W : Set V, ∫ ω, (if clusters H ω D S = W then h ω else 0) ∂law p := by
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  congr 1; funext ω
  rw [Finset.sum_ite_eq]; simp

theorem hc_cluster_delete {V E : Type*} {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {x : V} (hx : x ∉ clusters H ω D S) :
    cluster H ω (D ∪ clusters H ω D S) x = cluster H ω D x := by
  -- key: any vertex connected (avoiding D) to x is not in the clusters, and its hyperedges avoid them
  have hnot : ∀ y, Connected H ω D x y → ∀ s ∈ S, ¬ Connected H ω D s y := by
    intro y hy s hs hsy
    exact hx ⟨s, hs, hc_conn_trans hsy (hc_conn_symm hy)⟩
  ext y
  constructor
  · intro hy
    show Connected H ω D x y
    induction hy with
    | refl => exact .refl
    | tail _ hab ih =>
      obtain ⟨e, h1, h2, h3, h4⟩ := hab
      exact Relation.ReflTransGen.tail ih ⟨e, h1, h2.mono_right Set.subset_union_left, h3, h4⟩
  · intro hy
    show Connected H ω (D ∪ clusters H ω D S) x y
    change Connected H ω D x y at hy
    induction hy with
    | refl => exact .refl
    | @tail z w hxz hab ih =>
      obtain ⟨e, h1, h2, h3, h4⟩ := hab
      refine Relation.ReflTransGen.tail ih ⟨e, h1, ?_, h3, h4⟩
      rw [Set.disjoint_union_right]
      refine ⟨h2, Set.disjoint_left.mpr ?_⟩
      rintro u hu ⟨s, hs, hsu⟩
      exact hnot z hxz s hs (hc_conn_trans hsu (Relation.ReflTransGen.single ⟨e, h1, h2, hu, h3⟩))

theorem hc_cluster_agree {V E : Type*} {H : Hypergraph V E} {ω ω' : E → Bool}
    {D W : Set V} (hWD : W ⊆ D) (hag : ∀ e, Disjoint (H e) W → ω' e = ω e) (s : V) :
    cluster H ω' D s = cluster H ω D s := by
  ext y
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hab ih =>
      obtain ⟨e, h1, h2, h3, h4⟩ := hab
      exact Relation.ReflTransGen.tail ih ⟨e, (hag e (h2.mono_right hWD)) ▸ h1, h2, h3, h4⟩
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hab ih =>
      obtain ⟨e, h1, h2, h3, h4⟩ := hab
      exact Relation.ReflTransGen.tail ih ⟨e, (hag e (h2.mono_right hWD)).trans h1, h2, h3, h4⟩

theorem hc_cluster_cond {V E : Type*} [Fintype E] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (D S W : Set V) (F : Set V → ℝ)
    (hs : s ∉ W) :
    (∫ ω, if clusters H ω D S = W then F (cluster H ω D s) else 0 ∂law p) =
      clusterMass H p D S W * meanAfterDelete H p s (D ∪ W) F := by
  have e1 : (∫ ω, (if clusters H ω D S = W then F (cluster H ω D s) else 0) ∂law p) =
      ∫ ω, (if clusters H ω D S = W then F (cluster H ω (D ∪ W) s) else 0) ∂law p := by
    congr 1; funext ω
    split_ifs with h
    · rw [← h, hc_cluster_delete (h ▸ hs)]
    · rfl
  rw [e1, hc_exact_mul H p D S W _ (fun ω ω' h => by
    rw [hc_cluster_agree Set.subset_union_right h])]
  rfl

theorem hc_exact_weight {V E : Type*} [Fintype E] [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S : Set V) (f : Set V → ℝ)
    (g : (E → Bool) → Set V → ℝ)
    (hg : ∀ U ω ω', (∀ e, Disjoint (H e) U → ω' e = ω e) → g ω' U = g ω U) :
    (∫ ω, f (clusters H ω D S) * g ω (clusters H ω D S) ∂law p) =
      ∫ ω, f (clusters H ω D S) * (∫ ω', g ω' (clusters H ω D S) ∂law p) ∂law p := by
  rw [hc_decomp H p D S, hc_decomp H p D S]
  refine Finset.sum_congr rfl (fun W _ => ?_)
  have e1 : (∫ ω, (if clusters H ω D S = W then f (clusters H ω D S) * g ω (clusters H ω D S) else 0) ∂law p)
      = ∫ ω, (if clusters H ω D S = W then f W * g ω W else 0) ∂law p := by
    congr 1; funext ω; split_ifs with h <;> simp [h]
  have e2 : (∫ ω, (if clusters H ω D S = W then f (clusters H ω D S) * (∫ ω', g ω' (clusters H ω D S) ∂law p) else 0) ∂law p)
      = ∫ ω, (if clusters H ω D S = W then f W * (∫ ω', g ω' W ∂law p) else 0) ∂law p := by
    congr 1; funext ω; split_ifs with h <;> simp [h]
  rw [e1, e2, hc_exact_mul H p D S W _ (fun ω ω' h => by rw [hg W ω ω' h]),
    hc_exact_mul H p D S W _ (fun _ _ _ => rfl), integral_const_mul]
  simp
theorem hc_rm_eq {V E : Type*} [Fintype E] [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S U : Set V) (F : Set V → ℝ) :
    residualMean H p s S U F = ∫ ω, residualSample H ω s S U F ∂law p := by
  have key := hc_exact_weight H p U S (fun W => if s ∈ W then (0:ℝ) else 1)
    (fun (ω' : E → Bool) W => F (cluster H ω' W s) - F (cluster H ω' (W ∪ U) s))
    (fun W ω ω' h => by
      rw [hc_cluster_agree (le_refl W) h, hc_cluster_agree Set.subset_union_left h])
  have hR : (∫ ω, residualSample H ω s S U F ∂law p) = ∫ ω, (if s ∈ clusters H ω U S then (0:ℝ) else 1) *
      (F (cluster H ω (clusters H ω U S) s) - F (cluster H ω (clusters H ω U S ∪ U) s)) ∂law p := by
    unfold residualSample
    congr 1; funext ω
    by_cases h : s ∈ clusters H ω U S <;> simp [h]
  rw [hR, key]
  unfold residualMean meanAfterDelete
  congr 1; funext ω
  by_cases h : s ∈ clusters H ω U S
  · simp [h]
  · simp only [h, if_false, one_mul]
    rw [integral_sub Integrable.of_finite Integrable.of_finite]

theorem hc_rm_alt {V E : Type*} [Fintype E] [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S U : Set V) (F : Set V → ℝ) :
    residualMean H p s S U F =
      ∫ ω, if s ∈ clusters H ω U S then 0 else
        meanAfterDelete H p s (clusters H ω U S) F - F (cluster H ω U s) ∂law p := by
  have key := hc_exact_weight H p U S (fun W => if s ∈ W then (0:ℝ) else 1)
    (fun (ω' : E → Bool) W => meanAfterDelete H p s W F - F (cluster H ω' (W ∪ U) s))
    (fun W ω ω' h => by
      rw [hc_cluster_agree Set.subset_union_left h])
  have h1 : (∫ ω, (if s ∈ clusters H ω U S then (0:ℝ) else
        meanAfterDelete H p s (clusters H ω U S) F - F (cluster H ω U s)) ∂law p) =
      ∫ ω, (if s ∈ clusters H ω U S then (0:ℝ) else 1) *
      (meanAfterDelete H p s (clusters H ω U S) F - F (cluster H ω (clusters H ω U S ∪ U) s)) ∂law p := by
    congr 1; funext ω
    by_cases h : s ∈ clusters H ω U S
    · simp [h]
    · simp only [h, if_false, one_mul]
      rw [Set.union_comm, hc_cluster_delete h]
  rw [h1, key]
  unfold residualMean
  congr 1; funext ω
  by_cases h : s ∈ clusters H ω U S
  · simp [h]
  · simp only [h, if_false, one_mul]
    rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const]
    simp [meanAfterDelete]

theorem hc_cluster_eq_clusters {V E : Type*} (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (z : V) :
    cluster H ω D z = clusters H ω D {z} := by
  ext y; simp [clusters]

theorem hc_col_cond {V E : Type*} [Fintype E] [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n)
    (g : (E → Bool) → Set V → ℝ)
    (hg : ∀ U ω ω', (∀ e, Disjoint (H e) U → ω' e = ω e) → g ω' U = g ω U) :
    (∫ ω, (if firstRoot H x ω ∅ k i then g ω (cluster H ω ∅ (x k)) else 0) ∂law p) =
      column H p x k (fun U => ∫ ω, g ω U ∂law p) i := by
  have key := hc_exact_weight H p ∅ {x k}
    (fun U => if Disjoint U (earlier x k) ∧ x i ∈ U then (1:ℝ) else 0) g hg
  have h1 : (∫ ω, (if firstRoot H x ω ∅ k i then g ω (cluster H ω ∅ (x k)) else 0) ∂law p) =
      ∫ ω, (if Disjoint (clusters H ω ∅ {x k}) (earlier x k) ∧ x i ∈ clusters H ω ∅ {x k} then (1:ℝ) else 0) *
        g ω (clusters H ω ∅ {x k}) ∂law p := by
    congr 1; funext ω
    rw [← hc_cluster_eq_clusters]
    by_cases h : firstRoot H x ω ∅ k i
    · have h' : Disjoint (cluster H ω ∅ (x k)) (earlier x k) ∧ x i ∈ cluster H ω ∅ (x k) := h
      simp [h, h']
    · have h' : ¬ (Disjoint (cluster H ω ∅ (x k)) (earlier x k) ∧ x i ∈ cluster H ω ∅ (x k)) := h
      simp [h, h']
  rw [h1, key]
  unfold column
  congr 1; funext ω
  rw [← hc_cluster_eq_clusters]
  by_cases h : firstRoot H x ω ∅ k i
  · have h' : Disjoint (cluster H ω ∅ (x k)) (earlier x k) ∧ x i ∈ cluster H ω ∅ (x k) := h
    simp [h, h']
  · have h' : ¬ (Disjoint (cluster H ω ∅ (x k)) (earlier x k) ∧ x i ∈ cluster H ω ∅ (x k)) := h
    simp [h, h']

theorem hc_clusters_agree {V E : Type*} {H : Hypergraph V E} {ω ω' : E → Bool}
    {D W : Set V} (hWD : W ⊆ D) (hag : ∀ e, Disjoint (H e) W → ω' e = ω e) (S : Set V) :
    clusters H ω' D S = clusters H ω D S := by
  ext y; simp only [clusters, Set.mem_setOf_eq, hc_cluster_agree hWD hag]

theorem hc_cluster_outside {V E : Type*} {H : Hypergraph V E} {ω : E → Bool} {z y : V}
    (hy : y ∉ cluster H ω ∅ z) :
    cluster H ω (cluster H ω ∅ z) y = cluster H ω ∅ y := by
  rw [hc_cluster_eq_clusters H ω ∅ z] at hy ⊢
  have := hc_cluster_delete (D := ∅) hy
  rwa [Set.empty_union] at this

theorem hc_col_res {V E : Type*} [Fintype E] [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k j i : Fin n)
    (hkj : k < j) (F : Set V → ℝ) :
    column H p x j (residualMean H p (x k) (earlier x k) · F) i =
      ∫ ω, if firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k) then
        meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F -
          F (cluster H ω ∅ (x k)) else 0 ∂law p := by
  let g : (E → Bool) → Set V → ℝ := fun ω U =>
    if x k ∈ clusters H ω U (earlier x k) then 0 else
      meanAfterDelete H p (x k) (clusters H ω U (earlier x k)) F - F (cluster H ω U (x k))
  have hg : ∀ U ω ω', (∀ e, Disjoint (H e) U → ω' e = ω e) → g ω' U = g ω U := by
    intro U ω ω' h
    simp only [g, hc_clusters_agree (le_refl U) h, hc_cluster_agree (le_refl U) h]
  have e1 : (residualMean H p (x k) (earlier x k) · F) = fun U => ∫ ω, g ω U ∂law p := by
    funext U; rw [hc_rm_alt]
  rw [e1, ← hc_col_cond H p x j i g hg]
  congr 1; funext ω
  by_cases hf : firstRoot H x ω ∅ j i
  · have hout : ∀ y ∈ earlier x j, y ∉ cluster H ω ∅ (x j) := fun y hy hy' =>
      Set.disjoint_left.mp hf.1 hy' hy
    have hxk : x k ∉ cluster H ω ∅ (x j) := hout _ ⟨k, hkj, rfl⟩
    have hS : clusters H ω (cluster H ω ∅ (x j)) (earlier x k) = clusters H ω ∅ (earlier x k) := by
      ext y
      simp only [clusters, Set.mem_setOf_eq]
      constructor
      · rintro ⟨z, hz, hy⟩
        obtain ⟨m, hm, rfl⟩ := hz
        refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
        rwa [hc_cluster_outside (hout _ ⟨m, hm.trans hkj, rfl⟩)] at hy
      · rintro ⟨z, hz, hy⟩
        obtain ⟨m, hm, rfl⟩ := hz
        refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
        rwa [hc_cluster_outside (hout _ ⟨m, hm.trans hkj, rfl⟩)]
    simp only [g, hS, hc_cluster_outside hxk]
    by_cases h2 : x k ∈ clusters H ω ∅ (earlier x k) <;> simp [hf, h2]
  · simp [hf]

theorem hc_cond_weight {V E : Type*} [Fintype E] [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (D S : Set V)
    (w : Set V → ℝ) (F : Set V → ℝ) (hw : ∀ U, s ∈ U → w U = 0) :
    (∫ ω, w (clusters H ω D S) * F (cluster H ω D s) ∂law p) =
      ∫ ω, w (clusters H ω D S) *
        meanAfterDelete H p s (D ∪ clusters H ω D S) F ∂law p := by
  rw [hc_decomp H p D S, hc_decomp H p D S]
  refine Finset.sum_congr rfl (fun W _ => ?_)
  have e1 : (∫ ω, (if clusters H ω D S = W then w (clusters H ω D S) * F (cluster H ω D s) else 0) ∂law p)
      = w W * ∫ ω, (if clusters H ω D S = W then F (cluster H ω D s) else 0) ∂law p := by
    rw [← integral_const_mul]; congr 1; funext ω; split_ifs with h <;> simp [h]
  have e2 : (∫ ω, (if clusters H ω D S = W then w (clusters H ω D S) * meanAfterDelete H p s (D ∪ clusters H ω D S) F else 0) ∂law p)
      = ∫ ω, (if clusters H ω D S = W then w W * meanAfterDelete H p s (D ∪ W) F else 0) ∂law p := by
    congr 1; funext ω; split_ifs with h <;> simp [h]
  rw [e1, e2, hc_exact_mul H p D S W (fun _ => w W * meanAfterDelete H p s (D ∪ W) F) (fun _ _ _ => rfl)]
  by_cases hsW : s ∈ W
  · simp [hw W hsW]
  · rw [hc_cluster_cond H p s D S W F hsW]
    simp; ring

theorem hc_root_unique {V E : Type*} {n : ℕ} (H : Hypergraph V E) (x : Fin n → V)
    (ω : E → Bool) (D : Set V) (i : Fin n) : ∃! k, firstRoot H x ω D k i := by
  classical
  have hne : ∃ j, Connected H ω D (x j) (x i) := ⟨i, .refl⟩
  let k := Nat.find (p := fun m => ∃ h : m < n, Connected H ω D (x ⟨m, h⟩) (x i))
    ⟨i.1, i.2, .refl⟩
  have hk : ∃ h : k < n, Connected H ω D (x ⟨k, h⟩) (x i) := Nat.find_spec (p := fun m => ∃ h : m < n, Connected H ω D (x ⟨m, h⟩) (x i)) ⟨i.1, i.2, .refl⟩
  have hmin : ∀ j : Fin n, Connected H ω D (x j) (x i) → k ≤ j.1 := fun j hj =>
    Nat.find_min' (p := fun m => ∃ h : m < n, Connected H ω D (x ⟨m, h⟩) (x i)) _ ⟨j.2, hj⟩
  obtain ⟨hkn, hkc⟩ := hk
  refine ⟨⟨k, hkn⟩, ⟨?_, hkc⟩, ?_⟩
  · rw [Set.disjoint_left]
    rintro y hy ⟨j, hj, rfl⟩
    have := hmin j (hc_conn_trans (hc_conn_symm hy) hkc)
    have : j.1 < k := hj
    omega
  · rintro k' ⟨hd, hc⟩
    have h1 := hmin k' hc
    by_contra hne'
    have hlt : (⟨k, hkn⟩ : Fin n) < k' := by
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exact absurd (Fin.ext h.symm) hne'
    exact Set.disjoint_left.mp hd (hc_conn_trans hc (hc_conn_symm hkc) : _) ⟨_, hlt, rfl⟩

theorem hc_col_resample {V E : Type*} [Fintype E] [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n) (F : Set V → ℝ) :
    column H p x k (resample H p (x k) (earlier x k) F) i =
      ∫ ω, (if firstRoot H x ω ∅ k i then
        meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F else 0) ∂law p := by
  let g : (E → Bool) → Set V → ℝ := fun ω U =>
    meanAfterDelete H p (x k) (clusters H ω U (earlier x k)) F
  have hg : ∀ U ω ω', (∀ e, Disjoint (H e) U → ω' e = ω e) → g ω' U = g ω U := by
    intro U ω ω' h
    simp only [g, hc_clusters_agree (le_refl U) h]
  have e1 : resample H p (x k) (earlier x k) F = fun U => ∫ ω, g ω U ∂law p := rfl
  rw [e1, ← hc_col_cond H p x k i g hg]
  congr 1; funext ω
  by_cases hf : firstRoot H x ω ∅ k i
  · have hout : ∀ y ∈ earlier x k, y ∉ cluster H ω ∅ (x k) := fun y hy hy' =>
      Set.disjoint_left.mp hf.1 hy' hy
    have hS : clusters H ω (cluster H ω ∅ (x k)) (earlier x k) = clusters H ω ∅ (earlier x k) := by
      ext y
      simp only [clusters, Set.mem_setOf_eq]
      constructor
      · rintro ⟨z, hz, hy⟩
        exact ⟨z, hz, by rwa [hc_cluster_outside (hout _ hz)] at hy⟩
      · rintro ⟨z, hz, hy⟩
        exact ⟨z, hz, by rwa [hc_cluster_outside (hout _ hz)]⟩
    simp only [g, hS, hf, if_true]
  · simp [hf]

theorem hc_coeff_pt {V E : Type*} {n : ℕ} (H : Hypergraph V E) (x : Fin n → V) (k i : Fin n)
    (ω : E → Bool) (a b : ℝ) :
    (if firstRoot H x ω ∅ k i then a else 0) =
      (if firstRoot H x ω ∅ k i then b else 0) +
      ∑ j, (if k < j then (if firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
        then b - a else 0) else 0) +
      (if x k ∉ clusters H ω ∅ (earlier x k) ∧ x i ∉ clusters H ω ∅ (earlier x k) then (1:ℝ) else 0)
        * (a - b) := by
  obtain ⟨r, hr, huniq⟩ := hc_root_unique H x ω ∅ i
  have hnot : ∀ j, j ≠ r → ¬ firstRoot H x ω ∅ j i := fun j hj h => hj (huniq j h)
  rcases lt_trichotomy r k with hrk | rfl | hkr
  · -- root earlier: x i ∈ C
    have hxi : x i ∈ clusters H ω ∅ (earlier x k) := ⟨x r, ⟨r, hrk, rfl⟩, hr.2⟩
    have hk : ¬ firstRoot H x ω ∅ k i := hnot k (ne_of_gt hrk)
    have hsum : ∑ j, (if k < j then (if firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
        then b - a else 0) else (0:ℝ)) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      by_cases hkj : k < j
      · have : ¬ firstRoot H x ω ∅ j i := hnot j (by rintro rfl; exact absurd (hrk.trans hkj) (lt_irrefl _))
        simp [hkj, this]
      · simp [hkj]
    rw [hsum]; simp [hk, hxi]
  · have hs : x r ∉ clusters H ω ∅ (earlier x r) := by
      rintro ⟨y, ⟨m, hm, rfl⟩, hy⟩
      exact Set.disjoint_left.mp hr.1 (hc_conn_symm hy : _) ⟨m, hm, rfl⟩
    have hxi : x i ∉ clusters H ω ∅ (earlier x r) := by
      rintro ⟨y, ⟨m, hm, rfl⟩, hy⟩
      exact Set.disjoint_left.mp hr.1 (hc_conn_trans hr.2 (hc_conn_symm hy) : _) ⟨m, hm, rfl⟩
    have hsum : ∑ j, (if r < j then (if firstRoot H x ω ∅ j i ∧ x r ∉ clusters H ω ∅ (earlier x r)
        then b - a else 0) else (0:ℝ)) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      by_cases hkj : r < j
      · have : ¬ firstRoot H x ω ∅ j i := hnot j (ne_of_gt hkj)
        simp [hkj, this]
      · simp [hkj]
    rw [hsum]; simp [hr, hs, hxi]
  · have hk : ¬ firstRoot H x ω ∅ k i := hnot k (ne_of_lt hkr)
    have hxi : x i ∉ clusters H ω ∅ (earlier x k) := by
      rintro ⟨y, ⟨m, hm, rfl⟩, hy⟩
      exact Set.disjoint_left.mp hr.1 (hc_conn_trans hr.2 (hc_conn_symm hy) : _) ⟨m, hm.trans hkr, rfl⟩
    have hsum : ∑ j, (if k < j then (if firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
        then b - a else 0) else (0:ℝ)) =
        if x k ∉ clusters H ω ∅ (earlier x k) then b - a else 0 := by
      rw [Finset.sum_eq_single r]
      · simp [hkr, hr]
      · intro j _ hj; simp [hnot j hj]
      · simp
    rw [hsum]
    by_cases hs : x k ∈ clusters H ω ∅ (earlier x k)
    · simp [hk, hs]
    · simp [hk, hs, hxi]

theorem hc_column_identity {V E : Type*} [Fintype E] [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) :
    column H p x k F = column H p x k (resample H p (x k) (earlier x k) F) +
      ∑ j, if k < j then column H p x j (residualMean H p (x k) (earlier x k) · F) else 0 := by
  funext i
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [hc_col_resample]
  have hres : ∀ j, (if k < j then column H p x j (residualMean H p (x k) (earlier x k) · F) else 0) i
      = ∫ ω, (if k < j then (if firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k) then
        meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F -
          F (cluster H ω ∅ (x k)) else 0) else 0) ∂law p := by
    intro j
    by_cases hkj : k < j
    · simp only [hkj, if_true]; exact hc_col_res H p x k j i hkj F
    · simp [hkj]
  simp only [hres]
  have hw := hc_cond_weight H p (x k) ∅ (earlier x k)
    (fun U => if x k ∉ U ∧ x i ∉ U then (1:ℝ) else 0) F (fun U hU => by simp [hU])
  simp only [Set.empty_union] at hw
  have hz : (∫ ω, (if x k ∉ clusters H ω ∅ (earlier x k) ∧ x i ∉ clusters H ω ∅ (earlier x k) then (1:ℝ) else 0)
      * (F (cluster H ω ∅ (x k)) - meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F) ∂law p) = 0 := by
    simp only [mul_sub]
    rw [integral_sub Integrable.of_finite Integrable.of_finite, hw, sub_self]
  unfold column
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite),
    ← integral_add Integrable.of_finite Integrable.of_finite, ← sub_eq_zero,
    ← integral_sub Integrable.of_finite Integrable.of_finite]
  refine Eq.trans ?_ hz
  congr 1; funext ω
  rw [hc_coeff_pt H x k i ω (F (cluster H ω ∅ (x k)))
    (meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F)]
  ring

theorem solution [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) :
    coeff H p x k F = coeff H p x k (resample H p (x k) (earlier x k) F) +
      ∑ j, if k < j then coeff H p x j (residualMean H p (x k) (earlier x k) · F) else 0 := by
  unfold coeff
  rw [hc_column_identity H p x k F, Matrix.mulVec_add]
  congr 1
  rw [← Matrix.mulVecLin_apply, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rfl
  · simp

