-- Prove2me | solution 1 for OAI.Percolation.critical_encounter_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T00:59:45.992736+00:00
-- url     : https://prove2.me/submissions/37f8b7b4-4aed-4752-8a71-2334ddf5f828

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Graph_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed bond graphs, connectivity, percolation laws, kernels and countability. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}



section Deterministic
variable (G : BondGraph V E) (ω : Set E)

theorem cluster_eq_of_conn {x y : V} (h : Conn G ω x y) :
    cluster G ω x = cluster G ω y := by
  ext z
  exact ⟨fun hxz => conn_trans G ω (conn_symm G ω h) hxz,
    fun hyz => conn_trans G ω h hyz⟩

end Deterministic

section Countability


theorem exists_mem_reachBall {G : BondGraph V E} {x y : V}
    (h : Relation.ReflTransGen (Adj G) x y) : ∃ n, y ∈ reachBall G x n := by
  induction h with
  | refl => exact ⟨0, Set.mem_singleton _⟩
  | @tail y z _ hyz ih =>
    rcases ih with ⟨n, hn⟩
    refine ⟨n + 1, Or.inr ?_⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨y, hn, hyz⟩

end Countability

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel domination, monotone couplings and endpoint bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Coupling

theorem measurable_threshold (p : unitInterval) :
    Measurable (fun t : unitInterval => t ≤ p) :=
  measurableSet_setOfPred.mp measurableSet_Iic

 
theorem map_threshold (p : unitInterval) :
    (volume : Measure unitInterval).map (fun t => t ≤ p) =
      unitInterval.toNNReal p • Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False := by
  apply Measure.ext_of_singleton
  intro b
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [Measure.map_apply (measurable_threshold p), Set.preimage]
    change volume (Set.Iic p) = _
    rw [unitInterval.volume_Iic, ← unitInterval.coe_toNNReal p,
      ENNReal.ofReal_coe_nnreal]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [Measure.map_apply (measurable_threshold p), Set.preimage]
    change volume (Set.Ioi p) = _
    rw [unitInterval.volume_Ioi, ← unitInterval.coe_symm_eq,
      ← unitInterval.coe_toNNReal (unitInterval.symm p), ENNReal.ofReal_coe_nnreal]

 
theorem map_openEdges (p : unitInterval) :
    (labelLaw : Measure (E → unitInterval)).map (fun labels => openEdges labels p) =
      law p := by
  unfold law
  rw [setBernoulli_eq_map]
  have hmeas : Measurable (fun labels : E → unitInterval => fun e => labels e ≤ p) :=
    Measurable.of_eval (fun e => (measurable_threshold p).comp (measurable_pi_apply e))
  have he : (fun labels : E → unitInterval => openEdges labels p) =
      (fun f : E → Prop => {e | f e}) ∘ (fun labels e => labels e ≤ p) := rfl
  rw [he, ← Measure.map_map measurable_setOfPred hmeas]
  unfold labelLaw
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_threshold p)]
  simp only [map_threshold, Set.mem_univ, bernoulliMeasure_def]

end Coupling

section CouplingOrder
variable [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable E] in
theorem measurable_openEdges (p : unitInterval) :
    Measurable (fun labels : E → unitInterval => openEdges labels p) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_threshold p).comp (measurable_pi_apply e)))

omit [Countable E] in
theorem openEdges_mono (labels : E → unitInterval) : Monotone (openEdges labels) := by
  intro p q hpq e he
  exact he.trans hpq

end CouplingOrder

section CouplingLimits
open Filter Topology

theorem conn_iUnion_iff (G : BondGraph V E) (ω : ℕ → Set E) (hω : Monotone ω)
    (x y : V) : Conn G (⋃ n, ω n) x y ↔ ∃ n, Conn G (ω n) x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, conn_refl G _ _⟩
    | @tail y z _ hyz ih =>
      obtain ⟨m, hm⟩ := ih
      obtain ⟨e, he, heq⟩ := hyz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp he
      exact ⟨max m n, (conn_mono G (hω (le_max_left _ _)) hm).tail
        ⟨e, hω (le_max_right _ _) hn, heq⟩⟩
  · rintro ⟨n, hn⟩
    exact conn_mono G (Set.subset_iUnion ω n) hn

 
theorem ae_labels_ne [Countable E] (q : unitInterval) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), ∀ e, labels e ≠ q := by
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  simp only [not_not]
  change labelLaw ((fun labels : E → unitInterval => labels e) ⁻¹' {q}) = 0
  rw [← Measure.map_apply (measurable_pi_apply e) (measurableSet_singleton q)]
  change (Measure.infinitePi (fun _ : E => (volume : Measure unitInterval))).map
    (fun labels => labels e) {q} = 0
  rw [Measure.infinitePi_map_eval]
  simp

theorem openEdges_eq_iUnion_of_tendsto (labels : E → unitInterval)
    (q : unitInterval) (hneq : ∀ e, labels e ≠ q) (p : ℕ → unitInterval)
    (hle : ∀ n, p n ≤ q) (hlim : Tendsto p atTop (𝓝 q)) :
    openEdges labels q = ⋃ n, openEdges labels (p n) := by
  ext e
  constructor
  · intro he
    have hlt : labels e < q := lt_of_le_of_ne he (hneq e)
    obtain ⟨n, hn⟩ := ((tendsto_order.mp hlim).1 _ hlt).exists
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩
  · intro he
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp he
    exact hn.trans (hle n)



end CouplingLimits

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_ProductMeasure_Association
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Association, disjoint witnesses and the BK inequality. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Restriction

theorem measurable_set_restrict (s : Set E) :
    Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_pi_apply e.val).comp MeasurableEquiv.setOfPred.symm.measurable))


end Restriction

section WitnessAssociation
attribute [local instance] Classical.propDecidable
open Filter Topology


private theorem subset_edgeExhaustion [Encodable E] (s : Finset E) :
    ∃ n, s ⊆ edgeExhaustion n := by
  refine ⟨s.sup Encodable.encode + 1, ?_⟩
  intro e he
  simp only [edgeExhaustion, Finset.mem_preimage, Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.le_sup he)

 theorem witness_eq_union [Encodable E] (A : Set (Set E))
    (hA : IsUpperSet A) (hf : FiniteWitness A) :
    A = ⋃ n, {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ A} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · intro hω
    obtain ⟨s, hs, hsa⟩ := hf ω hω
    obtain ⟨n, hn⟩ := subset_edgeExhaustion s
    exact ⟨n, hA (fun _ he => ⟨hs he, hn he⟩) hsa⟩
  · rintro ⟨n, hn⟩
    exact hA Set.inter_subset_left hn



end WitnessAssociation

section ClusterEvents
attribute [local instance] Classical.propDecidable
open Filter Topology

 
theorem measurableSet_finiteWitness [Countable E] (A : Set (Set E))
    (hA : IsUpperSet A) (hfA : FiniteWitness A) : MeasurableSet A := by
  let := Encodable.ofCountable E
  rw [witness_eq_union A hA hfA]
  apply MeasurableSet.iUnion
  intro n
  let s := edgeExhaustion (E := E) n
  have he : {ω : Set E | ω ∩ (s : Set E) ∈ A} =
      (fun ω => (Subtype.val ⁻¹' ω : Set (s : Set E))) ⁻¹'
        {η | Subtype.val '' η ∈ A} := by
    ext ω
    change ω ∩ (s : Set E) ∈ A ↔ Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) ∈ A
    have hi : Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) = ω ∩ (s : Set E) := by
      ext e
      simp [and_comm]
    rw [hi]
  change MeasurableSet {ω : Set E | ω ∩ (s : Set E) ∈ A}
  rw [he]
  exact MeasurableSet.preimage .of_discrete (measurable_set_restrict _)

theorem finiteWitness_conn (G : BondGraph V E) (x y : V) :
    FiniteWitness {ω | Conn G ω x y} := by
  intro ω h
  induction h with
  | refl => exact ⟨∅, by simp, by simp⟩
  | @tail b c hab hbc ih =>
    obtain ⟨s, hs, hconn⟩ := ih
    obtain ⟨e, he, hGe⟩ := hbc
    refine ⟨insert e s, ?_, ?_⟩
    · simpa only [Finset.coe_insert] using Set.insert_subset he hs
    · exact (conn_mono G (by simp) hconn).tail ⟨e, by simp, hGe⟩

theorem finiteWitness_conn_finset (G : BondGraph V E) (x : V) (t : Finset V) :
    FiniteWitness {ω | ∀ y ∈ t, Conn G ω x y} := by
  intro ω h
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert a t ha ih =>
    obtain ⟨s, hs, hsa⟩ := finiteWitness_conn G x a ω (h a (by simp))
    obtain ⟨r, hr, hrt⟩ := ih (fun y hy => h y (by simp [hy]))
    refine ⟨s ∪ r, ?_, ?_⟩
    · simpa only [Finset.coe_union] using Set.union_subset hs hr
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact conn_mono G (by simp) hsa
      · exact conn_mono G (by simp) (hrt y hy)


theorem clusterLarge_upper (G : BondGraph V E) (x : V) (n : ℕ) :
    IsUpperSet (clusterLarge G x n) := by
  rintro ω η h ⟨t, ht, hc⟩
  exact ⟨t, ht, fun y hy => conn_mono G h (hc y hy)⟩

theorem finiteWitness_clusterLarge (G : BondGraph V E) (x : V) (n : ℕ) :
    FiniteWitness (clusterLarge G x n) := by
  rintro ω ⟨t, ht, hc⟩
  obtain ⟨s, hs, hsc⟩ := finiteWitness_conn_finset G x t ω hc
  exact ⟨s, hs, t, ht, hsc⟩

theorem measurableSet_clusterLarge [Countable E] (G : BondGraph V E) (x : V) (n : ℕ) :
    MeasurableSet (clusterLarge G x n) :=
  measurableSet_finiteWitness _ (clusterLarge_upper G x n) (finiteWitness_clusterLarge G x n)

theorem infinite_cluster_eq_iInter (G : BondGraph V E) (x : V) :
    {ω | (cluster G ω x).Infinite} = ⋂ n, clusterLarge G x n := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h n
    obtain ⟨t, ht, hcard⟩ := h.exists_subset_card_eq n
    exact ⟨t, hcard.ge, ht⟩
  · intro h hfin
    obtain ⟨t, ht, hc⟩ := h (hfin.toFinset.card + 1)
    have hsub : t ⊆ hfin.toFinset := fun y hy => hfin.mem_toFinset.mpr (hc y hy)
    have := Finset.card_le_card hsub
    omega

theorem measurableSet_infinite_cluster [Countable E] (G : BondGraph V E) (x : V) :
    MeasurableSet {ω | (cluster G ω x).Infinite} := by
  rw [infinite_cluster_eq_iInter]
  exact MeasurableSet.iInter (measurableSet_clusterLarge G x)


end ClusterEvents

section ORLift
attribute [local instance] Classical.propDecidable

instance bitLaw_isProbabilityMeasure (q : unitInterval) : IsProbabilityMeasure (bitLaw q) := by
  rw [bitLaw, ← map_threshold q]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)


end ORLift

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_Uniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cluster events, invariant covers and uniqueness thresholds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section CoverInvariance
attribute [local instance] Classical.propDecidable

 
theorem labelLaw_map_precomp (b : E ≃ E) :
    (labelLaw : Measure (E → unitInterval)).map (fun labels => labels ∘ b) = labelLaw := by
  have he : (fun labels : E → unitInterval => labels ∘ b) =
      MeasurableEquiv.piCongrLeft (fun _ : E => unitInterval) b.symm := by
    funext labels e
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : E => unitInterval)
      b.symm labels (b e)
    simpa only [Equiv.symm_apply_apply, Function.comp_apply] using h.symm
  unfold labelLaw
  rw [he]
  exact Measure.infinitePi_map_piCongrLeft (fun _ : E => (volume : Measure unitInterval)) b.symm

end CoverInvariance

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Sharpness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Russo formulae, exterior exposure and subcritical sharpness. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SharpnessBridge
attribute [local instance] Classical.propDecidable Classical.decEq
open Filter Topology

theorem pc_le_of_infinite_cluster_probability_pos (G : BondGraph V E)
    (x : V) (p : unitInterval) (hp : 0 < (law p).real {ω | (cluster G ω x).Infinite}) :
    pc G ≤ p := by
  apply sInf_le
  have hh : 0 < law p {ω | (cluster G ω x).Infinite} := (ENNReal.toReal_pos_iff.mp hp).1
  apply hh.trans_le
  apply measure_mono
  intro ω hω
  exact ⟨cluster G ω x,hω,x,rfl⟩


end SharpnessBridge

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Exploration_Goodness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pruning, finite and infinite goodness events and uniform bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section GoodnessLaw
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurableSet_finite_restriction (Q : Finset E) (A : Set (Set E)) :
    MeasurableSet {ω : Set E | ω ∩ (Q : Set E) ∈ A} := by
  have hm : MeasurableSet {η : Set (Q : Set E) | (Subtype.val '' η : Set E) ∈ A} := .of_discrete
  convert hm.preimage (measurable_set_restrict (Q : Set E)) using 1
  all_goals try with_reducible_and_instances rfl
  ext ω
  have he : (Subtype.val '' (Subtype.val ⁻¹' ω : Set (Q : Set E)) : Set E) = ω ∩ (Q : Set E) := by
    ext e
    simp [and_comm]
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,he]

end GoodnessLaw

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Transport_TrajectoryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trajectory Mass for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectoryTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

 

theorem RootTransport.real (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (m : V → V → ℝ)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y)
    (hr : ∀ x, Summable (m x)) (hc : ∀ y, Summable (fun x => m x y)) :
    (∑ i, weight i * ∑' y, m (root i) y) =
      (∑ i, weight i * ∑' x, m x (root i)) := by
  have ht := htr (fun x y => (m x y:ℂ))
    (fun a ha x y => congrArg Complex.ofReal (hi a ha x y))
    (fun x => Complex.summable_ofReal.mpr (hr x))
    (fun y => Complex.summable_ofReal.mpr (hc y))
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_tsum] using ht



end TrajectoryTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NonnegativeTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

theorem transportCut_mono (G : BondGraph V E) {n m : ℕ} (h : n ≤ m)
    {x y : V} (hxy : transportCut G n x y) : transportCut G m x y :=
  ⟨reachBall_mono G x h hxy.1, reachBall_mono G y h hxy.2⟩

theorem transportCut_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (ha : IsAut G a b) (n : ℕ) (x y : V) :
    transportCut G n (a x) (a y) ↔ transportCut G n x y := by
  simp only [transportCut,mem_reachBall_aut_iff G ha]

theorem exists_transportCut (G : BondGraph V E) (hconn : Connected G)
    (y : V) (Z : Finset V) : ∃ n, ∀ x ∈ Z, transportCut G n x y := by
  induction Z using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x Z _ ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨r,hr⟩ := exists_mem_reachBall (hconn x y)
    obtain ⟨s,hs⟩ := exists_mem_reachBall (hconn y x)
    refine ⟨max n (max r s), ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨reachBall_mono G z (le_trans (le_max_left r s) (le_max_right n _)) hr,
        reachBall_mono G y (le_trans (le_max_right r s) (le_max_right n _)) hs⟩
    · exact transportCut_mono G (le_max_left n _) (hn z hz)



end NonnegativeTransport

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_Connections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connections for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterWindowLaw
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterWindow_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (lo hi : ℕ) (ω : Set E) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
    ClusterWindow G x lo hi ω ↔ ClusterWindow G x lo hi (ω ∩ (Q : Set E)) := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  change ClusterWindow G x lo hi ω ↔ ClusterWindow G x lo hi (ω ∩ (Q : Set E))
  constructor
  · rintro ⟨hf,hl,hh⟩
    have hs : cluster G ω x ⊆ (finite_reachBall hloc x hi).toFinset := by
      simpa only [Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hf hi hh.le
    have he := cluster_restrict_incident_of_full G hloc _ ω x hs
    change cluster G (ω ∩ (Q : Set E)) x = cluster G ω x at he
    exact ⟨he.symm ▸ hf,he.symm ▸ hl,he.symm ▸ hh⟩
  · rintro ⟨hf,hl,hh⟩
    have he := cluster_restrict_of_cap G hloc Q ω x hi (Finset.Subset.refl _) hf hh.le
    exact ⟨he ▸ hf,he ▸ hl,he ▸ hh⟩

theorem measurableSet_clusterWindow (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (lo hi : ℕ) : MeasurableSet {ω | ClusterWindow G x lo hi ω} := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  have he : {ω | ClusterWindow G x lo hi ω} =
      {ω | ω ∩ (Q : Set E) ∈ {η | ClusterWindow G x lo hi η}} := by
    ext ω
    exact clusterWindow_local G hloc x lo hi ω
  rw [he]
  exact measurableSet_finite_restriction Q _

end ClusterWindowLaw
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Kernel_ScaleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale Budget for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterSizeMomentIntegrable
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_cluster_ncard (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Measurable (fun ω : Set E => (cluster G ω x).ncard) := by
  have hm (k : ℕ) (hk : k ≠ 0) : MeasurableSet {ω : Set E | (cluster G ω x).ncard = k} := by
    have he : {ω : Set E | (cluster G ω x).ncard = k} = {ω | ClusterWindow G x k (k+1) ω} := by
      ext ω
      constructor
      · intro h
        have hf := Set.finite_of_ncard_ne_zero (by rw [h]; exact hk)
        exact ⟨hf,by rw [h],by rw [h]; omega⟩
      · rintro ⟨hf,hl,hu⟩
        exact le_antisymm (by omega) hl
    rw [he]
    exact measurableSet_clusterWindow G hloc x k (k+1)
  have hm0 : MeasurableSet {ω : Set E | (cluster G ω x).ncard = 0} := by
    have he : {ω : Set E | (cluster G ω x).ncard = 0} =
        (⋃ k : ℕ, {ω : Set E | (cluster G ω x).ncard = k+1})ᶜ := by
      ext ω
      simp only [Set.mem_compl_iff,Set.mem_iUnion,Set.mem_ofPred_eq,not_exists]
      constructor
      · intro h k
        omega
      · intro h
        by_contra hz
        obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
        exact h k hk
    rw [he]
    exact (MeasurableSet.iUnion (fun k => hm (k+1) (by omega))).compl
  apply measurable_to_countable
  intro ω
  change MeasurableSet {ω' | (cluster G ω' x).ncard = (cluster G ω x).ncard}
  by_cases h : (cluster G ω x).ncard = 0
  · simpa only [h] using hm0
  · exact hm _ h



end ClusterSizeMomentIntegrable

end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_KernelMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterMassMoments
attribute [local instance] Classical.propDecidable Classical.decEq


theorem clusterMass_eq_ncard (G : BondGraph V E) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : clusterMass G ω x = (cluster G ω x).ncard := by
  change (∑' y, if y ∈ cluster G ω x then (1:ℝ≥0∞) else 0) = _
  rw [tsum_eq_sum (s := hf.toFinset) (fun y hy => by
    simp only [Set.Finite.mem_toFinset] at hy
    simp only [ite_eq_right hy])]
  have he : (∑ y ∈ hf.toFinset, if y ∈ cluster G ω x then (1:ℝ≥0∞) else 0) = ∑ _y ∈ hf.toFinset, (1:ℝ≥0∞) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact ite_eq_left (hf.mem_toFinset.mp hy)
  rw [he]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,←Set.ncard_eq_toFinset_card _ hf]

end ClusterMassMoments
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section SubcriticalMoments
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem subcritical_cluster_finite_ae (G : BondGraph V E)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    ∀ᵐ ω ∂law p, (cluster G ω x).Finite := by
  have hz : (law p).real {ω | (cluster G ω x).Infinite} = 0 := by
    apply le_antisymm _ measureReal_nonneg
    by_contra! h
    exact (not_le_of_gt hp) (pc_le_of_infinite_cluster_probability_pos G x p h)
  apply ae_iff.mpr
  change law p {ω | (cluster G ω x).Infinite} = 0
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top _ _)

end SubcriticalMoments
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_ExteriorMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteLocalIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurableSet_cluster_eq [Countable V] [Countable E]
    (G : BondGraph V E) (x : V) (W : Set V) : MeasurableSet {ω : Set E | cluster G ω x = W} := by
  have he : {ω : Set E | cluster G ω x = W} = ⋂ y, {ω : Set E | Conn G ω x y ↔ y ∈ W} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,Set.ext_iff,cluster]
  rw [he]
  apply MeasurableSet.iInter
  intro y
  by_cases hy : y ∈ W
  · simpa only [hy,iff_true] using measurableSet_conn G x y
  · simpa only [hy,iff_false,Set.compl_ofPred] using (measurableSet_conn G x y).compl



end FiniteLocalIndependence

end Percolation


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DistinctClusterMoments
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_ncard_covariant (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    (cluster G (b ⁻¹' ω) x).ncard = (cluster G ω (a x)).ncard := by
  rw [←cluster_aut G hab,Set.ncard_image_of_injective _ a.injective]

end DistinctClusterMoments
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Criticality_Susceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Susceptibility for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section SubcriticalSusceptibilityContinuity
attribute [local instance] Classical.propDecidable Classical.decEq

theorem label_cluster_finite_ae_subcritical [Countable E]
    (G : BondGraph V E) (p : unitInterval) (hp : p < pc G) (x : V) :
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)), (cluster G (openEdges labels p) x).Finite := by
  apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
    (p := fun ω : Set E => (cluster G ω x).Finite) (measurable_openEdges p).aemeasurable
  rw [map_openEdges]
  exact subcritical_cluster_finite_ae G p hp x

end SubcriticalSusceptibilityContinuity
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Clusters_LargeContacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Large Contacts for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ExtendedTransport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem enn_sum_iSup_nat {α : Type*} (s : Finset α) (f : ℕ → α → ℝ≥0∞)
    (hm : ∀ a, Monotone (fun n => f n a)) :
    (∑ a ∈ s, ⨆ n, f n a) = ⨆ n, ∑ a ∈ s, f n a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha,ih]
    exact ENNReal.iSup_add_iSup_of_monotone (hm a) (fun n m h =>
      Finset.sum_le_sum fun a _ => hm a h)

theorem enn_tsum_iSup_nat {α : Type*} (f : ℕ → α → ℝ≥0∞)
    (hm : ∀ a, Monotone (fun n => f n a)) :
    (∑' a, ⨆ n, f n a) = ⨆ n, ∑' a, f n a := by
  simp_rw [ENNReal.tsum_eq_iSup_sum,enn_sum_iSup_nat _ f hm]
  exact iSup_comm

 

theorem RootTransport.ennreal (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (m : V → V → ℝ≥0∞)
    (hi : ∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y) :
    (∑ i, ENNReal.ofReal (weight i) * ∑' y, m (root i) y) =
      (∑ i, ENNReal.ofReal (weight i) * ∑' x, m x (root i)) := by
  let cut (n : ℕ) (x y : V) : ℝ≥0∞ :=
    if transportCut G n x y then min (m x y) n else 0
  have hc0 (n : ℕ) (x y : V) : cut n x y ≠ ⊤ := by
    dsimp [cut]
    split_ifs
    · exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)
    · exact ENNReal.zero_ne_top
  have hcm (x y : V) : Monotone (fun n => cut n x y) := by
    intro n k hnk
    dsimp [cut]
    split_ifs with hn hk
    · exact min_le_min_left _ (by exact_mod_cast hnk)
    · exact False.elim (hk (transportCut_mono G hnk hn))
    · exact zero_le
    · exact le_refl _
  have hcs (x y : V) : (⨆ n, cut n x y) = m x y := by
    apply le_antisymm
    · refine iSup_le fun n => ?_
      dsimp [cut]
      split_ifs
      · exact min_le_left _ _
      · exact zero_le
    · obtain ⟨N,hN⟩ := exists_transportCut G hconn y {x}
      have hxy := hN x (Finset.mem_singleton_self x)
      have he : (⨆ k : ℕ, min (m x y) (k:ℝ≥0∞)) = m x y := by
        rw [←inf_iSup_eq,ENNReal.iSup_natCast,inf_top_eq]
      rw [←he]
      refine iSup_le fun k => le_iSup_of_le (max N k) ?_
      dsimp [cut]
      rw [ite_eq_left (transportCut_mono G (le_max_left N k) hxy)]
      exact min_le_min_left _ (by exact_mod_cast le_max_right N k)
  have hrow (n : ℕ) (x : V) : Summable (fun y => (cut n x y).toReal) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x n).toFinset)
    intro y hy
    have hh : ¬transportCut G n x y := fun h => hy ((Set.Finite.mem_toFinset _).mpr h.1)
    simp only [cut,ite_eq_right hh,ENNReal.toReal_zero]
  have hcol (n : ℕ) (y : V) : Summable (fun x => (cut n x y).toReal) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y n).toFinset)
    intro x hx
    have hh : ¬transportCut G n x y := fun h => hx ((Set.Finite.mem_toFinset _).mpr h.2)
    simp only [cut,ite_eq_right hh,ENNReal.toReal_zero]
  have he (n : ℕ) :
      (∑ i, ENNReal.ofReal (weight i) * ∑' y, cut n (root i) y) =
        (∑ i, ENNReal.ofReal (weight i) * ∑' x, cut n x (root i)) := by
    have ht := htr.real root weight Γ (fun x y => (cut n x y).toReal)
      (fun a ha x y => by
        obtain ⟨b,hb⟩ := hΓ ha
        simp only [cut,transportCut_aut G hb,hi a ha]) (hrow n) (hcol n)
    apply_fun ENNReal.ofReal at ht
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i)
      (tsum_nonneg fun _ => ENNReal.toReal_nonneg)),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i)
      (tsum_nonneg fun _ => ENNReal.toReal_nonneg))] at ht
    simp_rw [ENNReal.ofReal_mul (hw _),
      ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg) (hrow n _),
      ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg) (hcol n _),
      ENNReal.ofReal_toReal (hc0 n _ _)] at ht
    exact ht
  have hlim (f : ι → V → ℝ≥0∞) (g : ℕ → ι → V → ℝ≥0∞)
      (hmono : ∀ i y, Monotone (fun n => g n i y)) (hs : ∀ i y, (⨆ n, g n i y) = f i y) :
      (∑ i, ENNReal.ofReal (weight i) * ∑' y, f i y) =
        ⨆ n, ∑ i, ENNReal.ofReal (weight i) * ∑' y, g n i y := by
    simp_rw [←hs,enn_tsum_iSup_nat _ (hmono _),ENNReal.mul_iSup]
    exact enn_sum_iSup_nat _ _ (fun i n k h => mul_le_mul_right (ENNReal.tsum_le_tsum
      (fun y => hmono i y h)) _)
  rw [hlim (fun i y => m (root i) y) (fun n i y => cut n (root i) y)
    (fun i y => hcm (root i) y) (fun i y => hcs (root i) y),
    hlim (fun i x => m x (root i)) (fun n i x => cut n x (root i))
    (fun i x => hcm x (root i)) (fun i x => hcs x (root i))]
  exact iSup_congr he

end ExtendedTransport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterAveraging
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_clusterAveragingKernel [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x y : V) :
    Measurable (fun ω => clusterAveragingKernel G ω x y) := by
  exact (((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
    (measurable_cluster_ncard G hloc x)).inv).ite (measurableSet_conn G x y) measurable_const

theorem clusterAveragingKernel_symm (G : BondGraph V E) (ω : Set E) (x y : V) :
    clusterAveragingKernel G ω x y = clusterAveragingKernel G ω y x := by
  by_cases h : Conn G ω x y
  · simp only [clusterAveragingKernel,ite_eq_left h,ite_eq_left (conn_symm G ω h),cluster_eq_of_conn G ω h]
  · have h' : ¬Conn G ω y x := fun hh => h (conn_symm G ω hh)
    simp only [clusterAveragingKernel,ite_eq_right h,ite_eq_right h']

theorem cluster_ncard_pos (G : BondGraph V E) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : 0 < (cluster G ω x).ncard :=
  (Set.ncard_pos hf).mpr ⟨x,mem_cluster_self G ω x⟩

theorem clusterAveragingKernel_row (G : BondGraph V E) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) : (∑' y, clusterAveragingKernel G ω x y) = 1 := by
  have he : (fun y => clusterAveragingKernel G ω x y) =
      (fun y => (if Conn G ω x y then (1:ℝ≥0∞) else 0)*((cluster G ω x).ncard:ℝ≥0∞)⁻¹) := by
    funext y
    unfold clusterAveragingKernel
    split_ifs <;> simp
  rw [he,ENNReal.tsum_mul_right]
  change clusterMass G ω x * ((cluster G ω x).ncard:ℝ≥0∞)⁻¹ = 1
  rw [clusterMass_eq_ncard G ω x hf]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast (cluster_ncard_pos G ω x hf).ne') (ENNReal.natCast_ne_top _)

theorem clusterAveragingKernel_column (G : BondGraph V E) (ω : Set E) (y : V)
    (hf : (cluster G ω y).Finite) : (∑' x, clusterAveragingKernel G ω x y) = 1 := by
  simp_rw [clusterAveragingKernel_symm G ω]
  exact clusterAveragingKernel_row G ω y hf

theorem clusterAveragingKernel_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x y : V) :
    clusterAveragingKernel G (b ⁻¹' ω) x y = clusterAveragingKernel G ω (a x) (a y) := by
  simp only [clusterAveragingKernel,conn_aut_iff G hab,cluster_ncard_covariant G hab]



end ClusterAveraging
end Percolation


end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cut vertices and connected branches. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open SimpleGraph
universe u w
variable {V : Type u} {W : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem walk_reachable_cut (H : SimpleGraph V) (T : SimpleGraph W)
    (f : W → V) (hf : ∀ {a b}, T.Adj a b → H.Adj (f a) (f b))
    (x : V) {a b : W} (p : T.Walk a b)
    (hp : ∀ z ∈ p.support, f z ≠ x) :
    (cutVertex H x).Reachable (f a) (f b) := by
  induction p with
  | nil => exact .refl _
  | @cons a b c hab p ih =>
      apply Reachable.trans (Adj.reachable (G := cutVertex H x) ?_) (ih ?_)
      · exact ⟨hf hab,hp a (by simp),hp b (by simp [p.start_mem_support])⟩
      · intro z hz
        exact hp z (by simp [hz])

theorem branchCount_le_degree [Fintype W] (H : SimpleGraph V) (T : SimpleGraph W)
    (f : W ↪ V) (hf : ∀ {a b}, T.Adj a b → H.Adj (f a) (f b))
    (hT : T.Connected) (S : Finset V) (hS : ∀ z ∈ S, ∃ y, f y = z) (x : W) :
    branchCount H S (f x) ≤ T.degree x := by
  classical
  let g : W → (cutVertex H (f x)).ConnectedComponent :=
    fun y => (cutVertex H (f x)).connectedComponentMk (f y)
  have hsub : (S.erase (f x)).image (cutVertex H (f x)).connectedComponentMk ⊆
      (T.neighborFinset x).image g := by
    intro c hc
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hyx,hzS⟩ := Finset.mem_erase.mp hz
    obtain ⟨y,rfl⟩ := hS z hzS
    obtain ⟨p,hp⟩ := hT.exists_isPath x y
    cases p with
    | nil => exact False.elim (hyx rfl)
    | @cons x a y hab p =>
        refine Finset.mem_image.mpr ⟨a,(T.mem_neighborFinset x a).mpr hab,?_⟩
        apply ConnectedComponent.sound
        apply walk_reachable_cut H T f hf (f x) p
        intro z hz he
        have hzx := f.injective he
        subst z
        exact (List.nodup_cons.mp hp.support_nodup).1 hz
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by simp))

theorem connected_erase_leaf (H : SimpleGraph V) (D : Finset V)
    (T : SimpleGraph (D:Set V)) (hTH : T ≤ H.induce (D:Set V))
    (hT : T.Connected) (z : (D:Set V)) (hz : T.degree z = 1) :
    (H.induce ((D.erase z.val):Set V)).Connected := by
  let f : ({z}ᶜ : Set (D:Set V)) → ((D.erase z.val):Set V) :=
    fun y => ⟨y.val.val,Finset.mem_erase.mpr ⟨by
      intro h
      apply y.property
      exact Subtype.ext h,y.val.property⟩⟩
  have hf : Function.Surjective f := by
    intro y
    refine ⟨⟨⟨y.val,(Finset.mem_erase.mp y.property).2⟩,?_⟩,rfl⟩
    intro h
    exact (Finset.mem_erase.mp y.property).1 (congrArg Subtype.val h)
  apply (hT.induce_compl_singleton_of_degree_eq_one hz).map (f := ⟨f,?_⟩) hf
  intro a b hab
  exact hTH hab

theorem exists_pruned_connector (H : SimpleGraph V) (S D : Finset V)
    (hS : S.Nonempty) (hSD : S ⊆ D) (hD : (H.induce (D:Set V)).Connected) :
    ∃ D' : Finset V, D' ⊆ D ∧ S ⊆ D' ∧
      ∃ T : SimpleGraph (D':Set V), T ≤ H.induce (D':Set V) ∧ T.IsTree ∧
        ∀ z : (D':Set V), z.val ∉ S → 2 ≤ T.degree z := by
  classical
  induction hn : D.card using Nat.strong_induction_on generalizing D with
  | h n ih =>
      obtain ⟨T,hTH,hT⟩ := hD.exists_isTree_le
      by_cases hp : ∀ z : (D:Set V), z.val ∉ S → 2 ≤ T.degree z
      · exact ⟨D,Finset.Subset.refl _,hSD,T,hTH,hT,hp⟩
      push Not at hp
      obtain ⟨z,hzS,hzdeg⟩ := hp
      obtain ⟨s,hs⟩ := hS
      have hsz : s ≠ z.val := fun h => hzS (h ▸ hs)
      have hnon : Nontrivial (D:Set V) := ⟨⟨⟨s,hSD hs⟩,z,fun he => hsz (congrArg Subtype.val he)⟩⟩
      let := hnon
      have hdeg : T.degree z = 1 := by
        have hh := hT.connected.preconnected.minDegree_pos_of_nontrivial
        have hl := T.minDegree_le_degree z
        omega
      have hDel := connected_erase_leaf H D T hTH hT.connected z hdeg
      have hSD' : S ⊆ D.erase z.val := by
        intro a ha
        exact Finset.mem_erase.mpr ⟨fun he => hzS (he ▸ ha),hSD ha⟩
      obtain ⟨D',hD'D,hSD',T',hT'H,hT',hpr⟩ :=
        ih (D.erase z.val).card (by rw [←hn]; exact Finset.card_erase_lt_of_mem z.property)
          (D.erase z.val) hSD' hDel rfl
      exact ⟨D',hD'D.trans (Finset.erase_subset _ _),hSD',T',hT'H,hT',hpr⟩

theorem sum_branchCount_le (H : SimpleGraph V) (S D : Finset V)
    (hS : S.Nonempty) (hSD : S ⊆ D) (hD : (H.induce (D:Set V)).Connected) :
    (∑ x ∈ S, branchCount H S x) + 2 ≤ 2*S.card := by
  classical
  obtain ⟨D',_,hSD',T,hTH,hT,hpr⟩ := exists_pruned_connector H S D hS hSD hD
  let f : (D':Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hb (z : (D':Set V)) : branchCount H S z.val ≤ T.degree z :=
    branchCount_le_degree H T f (fun h => hTH h) hT.connected S
      (fun y hy => ⟨⟨y,hSD' hy⟩,rfl⟩) z
  have hsum : (∑ z : (D':Set V), if z.val ∈ S then branchCount H S z.val else 2) ≤
      ∑ z : (D':Set V), T.degree z := by
    apply Finset.sum_le_sum
    intro z _
    split_ifs with hz
    · exact hb z
    · exact hpr z hz
  have hsplit : (∑ z : (D':Set V), if z.val ∈ S then branchCount H S z.val else 2) =
      (∑ z ∈ S, branchCount H S z) + 2*(D'.card-S.card) := by
    rw [Finset.sum_finset_coe (fun z => if z ∈ S then branchCount H S z else 2) D']
    rw [Finset.sum_ite]
    simp only [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hSD',
      ←Finset.sdiff_eq_filter]
    simp only [Finset.sum_const,smul_eq_mul,Finset.card_sdiff_of_subset hSD',mul_comm]
  rw [hsplit,T.sum_degrees_eq_twice_card_edges] at hsum
  have hcard := hT.card_edgeFinset
  have hDcard : Fintype.card (D':Set V) = D'.card := by simp
  rw [hDcard] at hcard
  have hle := Finset.card_le_card hSD'
  omega

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_IntrinsicDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic distance and closest vertices in percolation clusters. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem Along.exists_open_walk_length_le {G : BondGraph V E} {ω : Set E}
    {x y : V} {l : List E} (h : Along G x l y) (ho : ∀ e ∈ l, e ∈ ω) :
    ∃ w : (openSimpleGraph G ω).Walk x y, w.length ≤ l.length := by
  induction h with
  | nil => exact ⟨.nil,le_rfl⟩
  | @cons x z y l e he ht ih =>
      obtain ⟨w,hw⟩ := ih (fun a ha => ho a (by simp [ha]))
      by_cases hxz : x = z
      · subst z
        exact ⟨w,hw.trans (by simp)⟩
      · exact ⟨.cons ⟨hxz,e,ho e (by simp),he⟩ w,by change w.length + 1 ≤ l.length + 1; omega⟩

theorem mem_intrinsicBall_iff (G : BondGraph V E) (ω : Set E) (x y : V) (n : ℕ) :
    y ∈ intrinsicBall G ω x n ↔ Conn G ω x y ∧ (openSimpleGraph G ω).dist x y ≤ n := by
  constructor
  · rintro ⟨l,hl,hlen,ho⟩
    obtain ⟨w,hw⟩ := hl.exists_open_walk_length_le ho
    exact ⟨hl.conn ho,(SimpleGraph.dist_le w).trans (hw.trans hlen)⟩
  · rintro ⟨h,hn⟩
    obtain ⟨w,hw⟩ := ((conn_iff_reachable G ω x y).mp h).exists_walk_length_eq_dist
    obtain ⟨l,hl,hm,ho⟩ := walk_lift_bonds G ω w
    refine ⟨l,hl,?_,ho⟩
    have he := congrArg List.length hm
    have hh : l.length = (openSimpleGraph G ω).dist x y := by
      simpa only [List.length_map,Walk.length_edges,hw] using he
    exact hh ▸ hn

theorem measurableSet_mem_intrinsicBall [Countable E] (G : BondGraph V E)
    (x y : V) (n : ℕ) : MeasurableSet {ω | y ∈ intrinsicBall G ω x n} := by
  have he : {ω | y ∈ intrinsicBall G ω x n} =
      ⋃ (l : List E), {ω | Along G x l y ∧ l.length ≤ n ∧ ∀ e ∈ l, e ∈ ω} := by
    ext ω; simp [intrinsicBall]
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  by_cases hl : Along G x l y ∧ l.length ≤ n
  · have hm : MeasurableSet {ω : Set E | ∀ e ∈ l, e ∈ ω} := by
      simpa only [Set.ofPred_forall] using MeasurableSet.iInter (fun e =>
        MeasurableSet.iInter (fun _ : e ∈ l => (measurableSet_setOfPred.mpr (measurable_set_mem e))))
    simpa [hl.1,hl.2] using hm
  · have he : {ω : Set E | Along G x l y ∧ l.length ≤ n ∧ ∀ e ∈ l, e ∈ ω} = ∅ := by
      ext ω; simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      intro h; exact hl ⟨h.1,h.2.1⟩
    rw [he]; exact MeasurableSet.empty

theorem closest_finite (G : BondGraph V E) (hloc : LocallyFinite G) (ω : Set E)
    (A : Set V) (x : V) : (closest (openSimpleGraph G ω) A x).Finite := by
  by_cases he : (closest (openSimpleGraph G ω) A x).Nonempty
  · obtain ⟨y,hy⟩ := he
    apply (finite_reachBall hloc x ((openSimpleGraph G ω).dist x y)).subset
    intro z hz
    apply intrinsicBall_subset_reachBall G ω x _
    exact (mem_intrinsicBall_iff G ω x z _).mpr
      ⟨(conn_iff_reachable G ω x z).mpr hz.2.1,hz.2.2 y hy.1 hy.2.1⟩
  · exact (Set.not_nonempty_iff_eq_empty.mp he) ▸ Set.finite_empty

theorem mem_closest_iff_balls (G : BondGraph V E) (ω : Set E) (A : Set V) (x y : V) :
    y ∈ closest (openSimpleGraph G ω) A x ↔ y ∈ A ∧ Conn G ω x y ∧
      ∀ n z, z ∈ A → z ∈ intrinsicBall G ω x n → y ∈ intrinsicBall G ω x n := by
  constructor
  · rintro ⟨hy,hr,hmin⟩
    refine ⟨hy,(conn_iff_reachable G ω x y).mpr hr,?_⟩
    intro n z hz hzb
    obtain ⟨hzc,hzd⟩ := (mem_intrinsicBall_iff G ω x z n).mp hzb
    exact (mem_intrinsicBall_iff G ω x y n).mpr
      ⟨(conn_iff_reachable G ω x y).mpr hr,
        (hmin z hz ((conn_iff_reachable G ω x z).mp hzc)).trans hzd⟩
  · rintro ⟨hy,hc,hmin⟩
    refine ⟨hy,(conn_iff_reachable G ω x y).mp hc,?_⟩
    intro z hz hzr
    have hzb := (mem_intrinsicBall_iff G ω x z ((openSimpleGraph G ω).dist x z)).mpr
      ⟨(conn_iff_reachable G ω x z).mpr hzr,le_rfl⟩
    exact ((mem_intrinsicBall_iff G ω x y _).mp (hmin _ z hz hzb)).2

theorem measurableSet_mem_closest [Countable V] [Countable E]
    (G : BondGraph V E) (A : Set E → Set V)
    (hA : ∀ y, MeasurableSet {ω | y ∈ A ω}) (x y : V) :
    MeasurableSet {ω | y ∈ closest (openSimpleGraph G ω) (A ω) x} := by
  simp only [mem_closest_iff_balls,Set.ofPred_and,Set.ofPred_forall]
  apply (hA y).inter
  apply (measurableSet_conn G x y).inter
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro z
  have he : {ω | z ∈ A ω → z ∈ intrinsicBall G ω x n → y ∈ intrinsicBall G ω x n} =
      {ω | z ∈ A ω}ᶜ ∪ {ω | z ∈ intrinsicBall G ω x n}ᶜ ∪
        {ω | y ∈ intrinsicBall G ω x n} := by ext ω; simp; tauto
  rw [he]
  exact ((hA z).compl.union (measurableSet_mem_intrinsicBall G x z n).compl).union
    (measurableSet_mem_intrinsicBall G x y n)

theorem iso_dist {W : Type*} {H : SimpleGraph V} {K : SimpleGraph W}
    (f : H ≃g K) (x y : V) : K.dist (f x) (f y) = H.dist x y := by
  by_cases hr : H.Reachable x y
  · obtain ⟨w,hw⟩ := hr.exists_walk_length_eq_dist
    have hr' := hr.map f.toHom
    obtain ⟨w',hw'⟩ := hr'.exists_walk_length_eq_dist
    apply le_antisymm
    · have hh := SimpleGraph.dist_le (w.map f.toHom)
      rw [Walk.length_map,hw] at hh
      exact hh
    · have hh := SimpleGraph.dist_le (w'.map f.symm.toHom)
      rw [Walk.length_map,hw'] at hh
      simpa using hh
  · have hr' : ¬K.Reachable (f x) (f y) := fun hh => hr (Iso.reachable_iff.mp hh)
    simp [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mpr (Or.inr hr),
      SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mpr (Or.inr hr')]

theorem closest_iso {W : Type*} {H : SimpleGraph V} {K : SimpleGraph W}
    (f : H ≃g K) (A : Set W) (x y : V) :
    y ∈ closest H (f ⁻¹' A) x ↔ f y ∈ closest K A (f x) := by
  constructor
  · rintro ⟨hy,hr,hmin⟩
    refine ⟨hy,hr.map f.toHom,?_⟩
    intro z hz hzr
    obtain ⟨z,rfl⟩ := f.surjective z
    simpa only [iso_dist] using hmin z hz (Iso.reachable_iff.mp hzr)
  · rintro ⟨hy,hr,hmin⟩
    refine ⟨hy,Iso.reachable_iff.mp hr,?_⟩
    intro z hz hzr
    simpa only [iso_dist] using hmin (f z) hz (hzr.map f.toHom)

theorem dist_lt_of_cut_separates (H : SimpleGraph V) {x y z : V}
    (hyr : H.Reachable y z) (hcut : ¬ (cutVertex H x).Reachable y z)
    (hxz : x ≠ z) : H.dist y x < H.dist y z := by
  obtain ⟨w,hw⟩ := hyr.exists_walk_length_eq_dist
  have hmem : x ∈ w.support := by
    by_contra hnot
    apply hcut
    exact walk_reachable_cut H H id (fun h => h) x w
      (fun a ha he => hnot (he ▸ ha))
  exact (SimpleGraph.dist_le (w.takeUntil x hmem)).trans_lt
    (hw ▸ w.length_takeUntil_lt_length hmem hxz)

theorem closest_eq_singleton_of_branch (H : SimpleGraph V) (A : Set V)
    {x y : V} (hx : x ∈ A) (hy : H.Reachable y x)
    (hbranch : ∀ z ∈ A, z ≠ x → ¬ (cutVertex H x).Reachable y z) :
    closest H A y = {x} := by
  have hstrict (z : V) (hz : z ∈ A) (hne : z ≠ x) (hr : H.Reachable y z) :
      H.dist y x < H.dist y z :=
    dist_lt_of_cut_separates H hr (hbranch z hz hne) hne.symm
  ext z
  constructor
  · intro hz
    have he : z = x := by
      by_contra hn
      exact (not_le_of_gt (hstrict z hz.1 hn hz.2.1)) (hz.2.2 x hx hy)
    exact he
  · intro hz
    have he : z = x := hz
    subst z
    refine ⟨hx,hy,?_⟩
    intro a ha hr
    by_cases he : a = x
    · subst a; exact le_rfl
    · exact (hstrict a ha he hr).le

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_NearestMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nearest-vertex transport and its finite incoming mass. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_nearestMass [Countable V] [Countable E]
    (G : BondGraph V E) (A : Set E → Set V)
    (hA : ∀ y, MeasurableSet {ω | y ∈ A ω}) (x y : V) :
    Measurable (fun ω => nearestMass G A ω x y) := by
  have hm : Measurable (fun ω => closest (openSimpleGraph G ω) (A ω) x) := by
    apply measurable_setOfPred.comp
    apply Measurable.of_eval
    intro z
    exact measurableSet_setOfPred.mp (measurableSet_mem_closest G A hA x z)
  exact Measurable.ite (measurableSet_mem_closest G A hA x y)
    (((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (measurable_ncard.comp hm)).inv) measurable_const

theorem nearestMass_row_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Set E → Set V) (ω : Set E) (x : V) :
    ∑' y, nearestMass G A ω x y ≤ 1 := by
  let S := closest (openSimpleGraph G ω) (A ω) x
  have hf := closest_finite G hloc ω (A ω) x
  rw [tsum_eq_sum (s := hf.toFinset) (fun y hy => by
    simp only [nearestMass,ite_eq_right (fun hh => hy (hf.mem_toFinset.mpr hh))])]
  simp only [nearestMass]
  have he : (∑ y ∈ hf.toFinset, if y ∈ S then (S.ncard : ℝ≥0∞)⁻¹ else 0) =
      (S.ncard : ℝ≥0∞) * (S.ncard : ℝ≥0∞)⁻¹ := by
    calc
      _ = ∑ _y ∈ hf.toFinset, (S.ncard : ℝ≥0∞)⁻¹ := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [ite_eq_left (hf.mem_toFinset.mp hy)]
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,←Set.ncard_eq_toFinset_card _ hf,S]
  change (∑ y ∈ hf.toFinset, if y ∈ S then (S.ncard : ℝ≥0∞)⁻¹ else 0) ≤ 1
  rw [he]
  exact ENNReal.mul_inv_le_one _

theorem nearestMass_aut (G : BondGraph V E) (A : Set E → Set V)
    (hA : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b → ∀ ω x,
      x ∈ A (b ⁻¹' ω) ↔ a x ∈ A ω)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (ω : Set E) (x y : V) :
    nearestMass G A (b ⁻¹' ω) x y = nearestMass G A ω (a x) (a y) := by
  have heA : A (b ⁻¹' ω) = a ⁻¹' A ω := by ext z; exact hA a b hab ω z
  have heS : closest (openSimpleGraph G (b ⁻¹' ω)) (A (b ⁻¹' ω)) x =
      a ⁻¹' closest (openSimpleGraph G ω) (A ω) (a x) := by
    rw [heA]
    ext z
    exact closest_iso (openAutIso G a b hab ω) (A ω) x z
  simp only [nearestMass,heS,Set.mem_preimage]
  rw [Set.ncard_preimage_of_injective_subset_range a.injective (by simp)]

theorem nearestMass_eq_one (G : BondGraph V E) (A : Set E → Set V)
    (ω : Set E) (x y : V)
    (h : closest (openSimpleGraph G ω) (A ω) x = {y}) :
    nearestMass G A ω x y = 1 := by simp [nearestMass,h]

theorem incoming_top_of_infinite (m : V → ℝ≥0∞) (B : Set V)
    (hB : B.Infinite) (hm : ∀ x ∈ B, m x = 1) : ∑' x, m x = ⊤ := by
  let : Infinite B := hB.to_subtype
  apply top_unique
  calc
    ⊤ = ∑' x : B, (1:ℝ≥0∞) := (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ = ∑' x : B, m x.val := tsum_congr (fun x => (hm x.val x.property).symm)
    _ = ∑' x, B.indicator m x := tsum_subtype B m
    _ ≤ ∑' x, m x := ENNReal.tsum_le_tsum (fun x => by
      by_cases hx : x ∈ B <;> simp [Set.indicator,hx])

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expected mass transport and cluster averaging. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

variable [Countable V] [Countable E] [Fintype ι]

omit [Countable V] [Countable E] [Fintype ι] in
theorem expected_mass_transport [Countable V] [Countable E] [Fintype ι]
    (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 ≤ weight i)
    (p : unitInterval) (m : Set E → V → V → ℝ≥0∞)
    (hm : ∀ x y, Measurable (fun ω => m ω x y))
    (hinv : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b → ∀ ω x y,
      m (b ⁻¹' ω) x y = m ω (a x) (a y)) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' y, m ω (root i) y ∂law p) =
      (∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' x, m ω x (root i) ∂law p) := by
  have hInv (a : V ≃ V) (ha : a ∈ vertexAut G) (x y : V) :
      (∫⁻ ω, m ω (a x) (a y) ∂law p) = ∫⁻ ω, m ω x y ∂law p := by
    obtain ⟨b,hb⟩ := ha
    calc
      _ = ∫⁻ ω, m (b ⁻¹' ω) x y ∂law p := lintegral_congr (fun ω => (hinv a b hb ω x y).symm)
      _ = ∫⁻ ω, m ω x y ∂(law p).map (fun ω => b ⁻¹' ω) :=
        (lintegral_map (hm x y) (measurable_set_preimage b)).symm
      _ = _ := by rw [law_map_preimage_equiv]
  have ht := htr.ennreal G hconn hloc root weight (vertexAut G) (Set.Subset.refl _) hw
    (fun x y => ∫⁻ ω, m ω x y ∂law p) hInv
  have hr (x : V) : (∫⁻ ω, ∑' y, m ω x y ∂law p) = ∑' y, ∫⁻ ω, m ω x y ∂law p :=
    lintegral_tsum (fun y => (hm x y).aemeasurable)
  have hc (y : V) : (∫⁻ ω, ∑' x, m ω x y ∂law p) = ∑' x, ∫⁻ ω, m ω x y ∂law p :=
    lintegral_tsum (fun x => (hm x y).aemeasurable)
  simp_rw [hr,hc]
  exact ht

theorem incoming_finite_ae (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1) (p : unitInterval) (m : Set E → V → V → ℝ≥0∞)
    (hm : ∀ x y, Measurable (fun ω => m ω x y))
    (hinv : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b → ∀ ω x y,
      m (b ⁻¹' ω) x y = m ω (a x) (a y))
    (hrow : ∀ ω x, ∑' y, m ω x y ≤ 1) (i : ι) :
    ∀ᵐ ω ∂law p, ∑' x, m ω x (root i) < ⊤ := by
  have ht := expected_mass_transport G hconn hloc root weight htr (fun i => (hw i).le)
    p m hm hinv
  have hupper : (∑ j, ENNReal.ofReal (weight j) * ∫⁻ ω, ∑' x, m ω x (root j) ∂law p) ≤ 1 := by
    rw [←ht]
    calc
      _ ≤ ∑ j, ENNReal.ofReal (weight j) * 1 := by
        apply Finset.sum_le_sum
        intro j _
        gcongr
        calc
          _ ≤ ∫⁻ ω : Set E, (1:ℝ≥0∞) ∂law p := lintegral_mono (fun ω => hrow ω (root j))
          _ = 1 := by simp
      _ = 1 := by
        simp only [mul_one,←ENNReal.ofReal_sum_of_nonneg (fun j _ => (hw j).le),hw1,ENNReal.ofReal_one]
  have hterm := (Finset.single_le_sum (fun j _ => (show (0:ℝ≥0∞) ≤ ENNReal.ofReal (weight j) * ∫⁻ ω, ∑' x, m ω x (root j) ∂law p from zero_le))
      (Finset.mem_univ i)).trans hupper
  have hfinite : (∫⁻ ω, ∑' x, m ω x (root i) ∂law p) ≠ ⊤ := by
    intro he
    rw [he,ENNReal.mul_top ((ENNReal.ofReal_pos.mpr (hw i)).ne')] at hterm
    exact (not_le_of_gt ENNReal.one_lt_top) hterm
  exact ae_lt_top (Measurable.tsum (fun x => hm x (root i))) hfinite

omit [Countable V] [Countable E] [Fintype ι] in
theorem expected_label_mass_transport [Countable V] [Countable E] [Fintype ι]
    (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 ≤ weight i)
    (m : (E → unitInterval) → V → V → ℝ≥0∞)
    (hm : ∀ x y, Measurable (fun l => m l x y))
    (hinv : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b → ∀ l x y,
      m (l ∘ b) x y = m l (a x) (a y)) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l, ∑' y, m l (root i) y ∂labelLaw) =
      (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l, ∑' x, m l x (root i) ∂labelLaw) := by
  have hInv (a : V ≃ V) (ha : a ∈ vertexAut G) (x y : V) :
      (∫⁻ l, m l (a x) (a y) ∂labelLaw) = ∫⁻ l, m l x y ∂labelLaw := by
    obtain ⟨b,hb⟩ := ha
    calc
      _ = ∫⁻ l, m (l ∘ b) x y ∂labelLaw := lintegral_congr (fun l => (hinv a b hb l x y).symm)
      _ = ∫⁻ l, m l x y ∂labelLaw.map (fun l => l ∘ b) :=
        (lintegral_map (hm x y) (by fun_prop)).symm
      _ = _ := by rw [labelLaw_map_precomp]
  have ht := htr.ennreal G hconn hloc root weight (vertexAut G) (Set.Subset.refl _) hw
    (fun x y => ∫⁻ l, m l x y ∂labelLaw) hInv
  have hr x : (∫⁻ l, ∑' y, m l x y ∂labelLaw) = ∑' y, ∫⁻ l, m l x y ∂labelLaw :=
    lintegral_tsum (fun y => (hm x y).aemeasurable)
  have hc y : (∫⁻ l, ∑' x, m l x y ∂labelLaw) = ∑' x, ∫⁻ l, m l x y ∂labelLaw :=
    lintegral_tsum (fun x => (hm x y).aemeasurable)
  simp_rw [hr,hc]
  exact ht

theorem label_root_cluster_average (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 ≤ weight i)
    (q : unitInterval) (hfin : ∀ x, ∀ᵐ ω ∂law q, (cluster G ω x).Finite)
    (f : (E → unitInterval) → V → ℝ≥0∞) (hf : ∀ x, Measurable (fun l => f l x))
    (hi : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b → ∀ l x,
      f (l ∘ b) x = f l (a x)) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l, ∑' y,
      clusterAveragingKernel G (openEdges l q) (root i) y * f l y ∂labelLaw) =
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l, f l (root i) ∂labelLaw) := by
  have hm x y : Measurable (fun l => clusterAveragingKernel G (openEdges l q) x y * f l y) :=
    ((measurable_clusterAveragingKernel G hloc x y).comp (measurable_openEdges q)).mul (hf y)
  have ht := expected_label_mass_transport G hconn hloc root weight htr hw
    (fun l x y => clusterAveragingKernel G (openEdges l q) x y * f l y) hm
    (fun a b hab l x y => by
      rw [hi a b hab]
      exact congrArg (fun t => t * f l (a y)) (clusterAveragingKernel_aut G hab (openEdges l q) x y))
  rw [ht]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply lintegral_congr_ae
  have hfl : ∀ᵐ l ∂labelLaw, (cluster G (openEdges l q) (root i)).Finite := by
    apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
      (p := fun ω : Set E => (cluster G ω (root i)).Finite) (measurable_openEdges q).aemeasurable
    rw [map_openEdges]
    exact hfin (root i)
  filter_upwards [hfl] with l hl
  rw [ENNReal.tsum_mul_right,clusterAveragingKernel_column G (openEdges l q) (root i) hl,one_mul]

theorem incoming_finite_ae_all (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1)
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x)
    (p : unitInterval) (m : Set E → V → V → ℝ≥0∞)
    (hm : ∀ x y, Measurable (fun ω => m ω x y))
    (hinv : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b → ∀ ω x y,
      m (b ⁻¹' ω) x y = m ω (a x) (a y))
    (hrow : ∀ ω x, ∑' y, m ω x y ≤ 1) :
    ∀ᵐ ω ∂law p, ∀ y, ∑' x, m ω x y < ⊤ := by
  apply ae_all_iff.mpr
  intro y
  obtain ⟨i,a,⟨b,hab⟩,rfl⟩ := hcov y
  have hi := incoming_finite_ae G hconn hloc root weight htr hw hw1 p m hm hinv hrow i
  have hi' : ∀ᵐ ω ∂law p, ∑' x, m (b ⁻¹' ω) x (root i) < ⊤ := by
    apply ae_of_ae_map (μ := law p)
      (p := fun ω : Set E => ∑' x, m ω x (root i) < ⊤)
      (measurable_set_preimage b).aemeasurable
    rw [law_map_preimage_equiv]
    exact hi
  filter_upwards [hi'] with ω hω
  simpa only [hinv a b hab,a.tsum_eq (fun x => m ω x (a (root i)))] using hω

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_Vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Encounter vertices and infinite open branches. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_cutConfig (G : BondGraph V E) (x : V) :
    Measurable (fun ω => cutConfig G ω x) := by
  apply measurable_setOfPred.comp (Measurable.of_eval ?_)
  intro e
  exact (measurable_set_mem e).and measurable_const

theorem cutVertex_open (G : BondGraph V E) (ω : Set E) (x : V) :
    cutVertex (openSimpleGraph G ω) x = openSimpleGraph G (cutConfig G ω x) := by
  ext a b
  change ((a ≠ b ∧ ∃ e ∈ ω, G e = s(a,b)) ∧ a ≠ x ∧ b ≠ x) ↔
    (a ≠ b ∧ ∃ e, (e ∈ ω ∧ x ∉ G e) ∧ G e = s(a,b))
  constructor
  · rintro ⟨⟨hab,e,he,hGe⟩,hax,hbx⟩
    exact ⟨hab,e,⟨he,by rw [hGe]; simpa [Sym2.mem_iff,eq_comm] using And.intro hax hbx⟩,hGe⟩
  · rintro ⟨hab,e,⟨he,hx⟩,hGe⟩
    rw [hGe] at hx
    have hh : a ≠ x ∧ b ≠ x := by simpa [Sym2.mem_iff,eq_comm] using hx
    exact ⟨⟨hab,e,he,hGe⟩,hh⟩

theorem cutConfig_aut (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E)
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    cutConfig G (b ⁻¹' ω) x = b ⁻¹' cutConfig G ω (a x) := by
  ext e
  simp only [cutConfig,Set.mem_ofPred_eq,Set.mem_preimage,hab e]
  rw [Sym2.mem_map]
  simp only [a.injective.eq_iff,exists_eq_right]

theorem measurableSet_isEncounter [Countable V] [Countable E]
    (G : BondGraph V E) (x : V) : MeasurableSet {ω | IsEncounter G ω x} := by
  simp only [IsEncounter,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro b
  apply MeasurableSet.iUnion
  intro c
  exact (measurableSet_conn G x a).inter ((measurableSet_conn G x b).inter
    ((measurableSet_conn G x c).inter
      (((measurableSet_infinite_cluster G a).preimage (measurable_cutConfig G x)).inter
      (((measurableSet_infinite_cluster G b).preimage (measurable_cutConfig G x)).inter
      (((measurableSet_infinite_cluster G c).preimage (measurable_cutConfig G x)).inter
      (((measurableSet_conn G a b).preimage (measurable_cutConfig G x)).compl.inter
      (((measurableSet_conn G a c).preimage (measurable_cutConfig G x)).compl.inter
      ((measurableSet_conn G b c).preimage (measurable_cutConfig G x)).compl)))))))

theorem isEncounter_aut_iff (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E)
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    IsEncounter G (b ⁻¹' ω) x ↔ IsEncounter G ω (a x) := by
  have hc y z : Conn G (cutConfig G (b ⁻¹' ω) x) y z ↔
      Conn G (cutConfig G ω (a x)) (a y) (a z) := by
    rw [cutConfig_aut G a b hab]
    exact conn_aut_iff G hab _ y z
  have hi y : (cluster G (cutConfig G (b ⁻¹' ω) x) y).Infinite ↔
      (cluster G (cutConfig G ω (a x)) (a y)).Infinite := by
    rw [cutConfig_aut G a b hab,←cluster_aut G hab]
    exact (Set.infinite_image_iff a.injective.injOn).symm
  constructor
  · rintro ⟨u,v,w,hxu,hxv,hxw,hu,hv,hw,huv,huw,hvw⟩
    exact ⟨a u,a v,a w,(conn_aut_iff G hab ω x u).mp hxu,
      (conn_aut_iff G hab ω x v).mp hxv,(conn_aut_iff G hab ω x w).mp hxw,
      (hi u).mp hu,(hi v).mp hv,(hi w).mp hw,
      fun h => huv ((hc u v).mpr h),fun h => huw ((hc u w).mpr h),fun h => hvw ((hc v w).mpr h)⟩
  · rintro ⟨u,v,w,hxu,hxv,hxw,hu,hv,hw,huv,huw,hvw⟩
    refine ⟨a.symm u,a.symm v,a.symm w,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (conn_aut_iff G hab ω x _).mpr (by simpa using hxu)
    · exact (conn_aut_iff G hab ω x _).mpr (by simpa using hxv)
    · exact (conn_aut_iff G hab ω x _).mpr (by simpa using hxw)
    · exact (hi _).mpr (by simpa using hu)
    · exact (hi _).mpr (by simpa using hv)
    · exact (hi _).mpr (by simpa using hw)
    · intro h; exact huv (by simpa using (hc _ _).mp h)
    · intro h; exact huw (by simpa using (hc _ _).mp h)
    · intro h; exact hvw (by simpa using (hc _ _).mp h)

theorem encounter_branch_contains_of_finite_incoming (G : BondGraph V E)
    (ω : Set E) (x a : V) (hx : IsEncounter G ω x) (hxa : Conn G ω x a)
    (hInf : (cluster G (cutConfig G ω x) a).Infinite)
    (hin : ∑' y, nearestMass G (encounters G) ω y x < ⊤) :
    ∃ z ∈ cluster G (cutConfig G ω x) a, z ≠ x ∧ IsEncounter G ω z := by
  by_contra hno
  have hm (y : V) (hy : y ∈ cluster G (cutConfig G ω x) a) :
      nearestMass G (encounters G) ω y x = 1 := by
    apply nearestMass_eq_one
    apply closest_eq_singleton_of_branch (openSimpleGraph G ω) (encounters G ω) hx
    · apply (conn_iff_reachable G ω y x).mp
      exact conn_symm G ω (conn_trans G ω hxa (conn_mono G (fun e he => he.1) hy))
    · intro z hz hzx hcut
      apply hno
      refine ⟨z,?_,hzx,hz⟩
      rw [cutVertex_open] at hcut
      exact conn_trans G _ hy ((conn_iff_reachable G _ y z).mpr hcut)
  have he := incoming_top_of_infinite (fun y => nearestMass G (encounters G) ω y x)
    (cluster G (cutConfig G ω x) a) hInf hm
  rw [he] at hin
  exact lt_irrefl _ hin

theorem encounter_branches_ae [Countable V] [Countable E] [Fintype ι]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1)
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x) (p : unitInterval) :
    ∀ᵐ ω ∂law p, ∀ x, IsEncounter G ω x → ∀ a, Conn G ω x a →
      (cluster G (cutConfig G ω x) a).Infinite →
      ∃ z ∈ cluster G (cutConfig G ω x) a, z ≠ x ∧ IsEncounter G ω z := by
  have hin := incoming_finite_ae_all G hconn hloc root weight htr hw hw1 hcov p
    (nearestMass G (encounters G))
    (measurable_nearestMass G (encounters G) (measurableSet_isEncounter G))
    (nearestMass_aut G (encounters G) (isEncounter_aut_iff G))
    (nearestMass_row_le G hloc (encounters G))
  filter_upwards [hin] with ω hω
  intro x hx a hxa hi
  exact encounter_branch_contains_of_finite_incoming G ω x a hx hxa hi (hω x)

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_Measurability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of branches and finite clusters. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem card_image_eq_minima [Encodable V] {W : Type*} (S : Finset V) (f : V → W) :
    (S.image f).card =
      (S.filter (fun y => ∀ z ∈ S, f z = f y → Encodable.encode y ≤ Encodable.encode z)).card := by
  let R := S.filter (fun y => ∀ z ∈ S, f z = f y → Encodable.encode y ≤ Encodable.encode z)
  have hRS : R ⊆ S := Finset.filter_subset _ _
  have hinj : Set.InjOn f (R:Set V) := by
    intro y hy z hz he
    apply Encodable.encode_injective
    exact le_antisymm ((Finset.mem_filter.mp hy).2 z (hRS hz) he.symm)
      ((Finset.mem_filter.mp hz).2 y (hRS hy) he)
  have he : R.image f = S.image f := by
    apply Finset.Subset.antisymm (Finset.image_subset_image hRS)
    intro c hc
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨z,hz,hmin⟩ := (S.filter (fun z => f z = f y)).exists_min_image
      Encodable.encode ⟨y,Finset.mem_filter.mpr ⟨hy,rfl⟩⟩
    refine Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,?_⟩,
      (Finset.mem_filter.mp hz).2⟩
    intro w hw hwe
    exact hmin w (Finset.mem_filter.mpr ⟨hw,hwe.trans (Finset.mem_filter.mp hz).2⟩)
  rw [←he]
  exact Finset.card_image_iff.mpr hinj

theorem measurable_branchCount [Countable V] [Countable E]
    (G : BondGraph V E) (S : Finset V) (x : V) :
    Measurable (fun ω => branchCount (openSimpleGraph G ω) S x) := by
  let : Encodable V := Encodable.ofCountable V
  have he (ω : Set E) : branchCount (openSimpleGraph G ω) S x =
      ∑ y ∈ S.erase x, if (∀ z ∈ S.erase x, Conn G (cutConfig G ω x) z y →
        Encodable.encode y ≤ Encodable.encode z) then 1 else 0 := by
    rw [branchCount,card_image_eq_minima,Finset.card_filter]
    apply Finset.sum_congr rfl
    intro y _
    simp only [ConnectedComponent.eq,cutVertex_open,←conn_iff_reachable]
  simp_rw [he]
  apply Finset.measurable_sum
  intro y hy
  apply Measurable.ite _ measurable_const measurable_const
  have he' : {ω : Set E | ∀ z ∈ S.erase x, Conn G (cutConfig G ω x) z y →
      Encodable.encode y ≤ Encodable.encode z} =
      ⋂ z ∈ S.erase x, ({ω | Conn G (cutConfig G ω x) z y}ᶜ ∪
        {ω : Set E | Encodable.encode y ≤ Encodable.encode z}) := by ext ω; simp [imp_iff_not_or]
  rw [he']
  apply MeasurableSet.iInter
  intro z
  apply MeasurableSet.iInter
  intro _
  exact ((measurableSet_conn G z y).preimage (measurable_cutConfig G x)).compl.union
    (by by_cases hh : Encodable.encode y ≤ Encodable.encode z <;> simp [hh])

theorem clusterFinset_coe (G : BondGraph V E) (ω : Set E) (x : V)
    (h : (cluster G ω x).Finite) : (clusterFinset G ω x : Set V) = cluster G ω x := by
  simp [clusterFinset,h]

theorem measurable_clusterFinset [Countable V] [Countable E]
    (G : BondGraph V E) (x : V) : Measurable (fun ω => clusterFinset G ω x) := by
  apply measurable_to_countable
  intro ω₀
  let S := clusterFinset G ω₀ x
  have he : {ω | clusterFinset G ω x = S} =
      {ω | cluster G ω x = (S:Set V)} ∪
        ({ω | (cluster G ω x).Infinite} ∩ {ω : Set E | S = ∅}) := by
    ext ω
    by_cases h : (cluster G ω x).Finite
    · simp only [Set.mem_ofPred,Set.mem_union,Set.mem_inter_iff,clusterFinset,dite_eq_left h]
      simp only [Set.Infinite,h,not_true_eq_false,false_and,or_false]
      constructor
      · intro he; rw [←he,h.coe_toFinset]
      · intro he; exact Finset.coe_injective (h.coe_toFinset.trans he)
    · simp only [Set.mem_ofPred,Set.mem_union,Set.mem_inter_iff,clusterFinset,dite_eq_right h]
      have hn : cluster G ω x ≠ (S:Set V) := fun he => h (he ▸ S.finite_toSet)
      simp [hn,Set.Infinite,h,eq_comm]
  change MeasurableSet {ω | clusterFinset G ω x = S}
  rw [he]
  exact (measurableSet_cluster_eq G x (S:Set V)).union
    ((measurableSet_infinite_cluster G x).inter (by by_cases hs : S = ∅ <;> simp [hs]))

theorem measurable_filter_finset {Ω : Type*} [MeasurableSpace Ω] [Countable V]
    (S : Ω → Finset V) (hS : Measurable S) (P : Ω → V → Prop)
    (hP : ∀ x, MeasurableSet {ω | P ω x}) :
    Measurable (fun ω => (S ω).filter (P ω)) := by
  have hf (D : Finset V) : Measurable (fun ω => D.filter (P ω)) := by
    apply measurable_to_countable
    intro ω₀
    have he : {ω | D.filter (P ω) = D.filter (P ω₀)} =
        ⋂ y, {ω | (y ∈ D ∧ P ω y) ↔ y ∈ D.filter (P ω₀)} := by
      ext ω; simp only [Set.mem_ofPred_eq,Set.mem_iInter,Finset.ext_iff,Finset.mem_filter]
    change MeasurableSet {ω | D.filter (P ω) = D.filter (P ω₀)}
    rw [he]
    apply MeasurableSet.iInter
    intro y
    by_cases hy : y ∈ D
    · by_cases hp : P ω₀ y <;> simp only [hy,hp,Finset.mem_filter,true_and,iff_true,iff_false]
      · exact hP y
      · exact (hP y).compl
    · simp [hy]
  have hm : Measurable (fun z : Ω × Finset V => z.2.filter (P z.1)) :=
    measurable_from_prod_countable_left hf
  exact hm.comp (measurable_id.prodMk hS)

end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_Counts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting encounter vertices by mass transport. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
open scoped ENNReal
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem branchCount_iso {W : Type*} {H : SimpleGraph V} {K : SimpleGraph W}
    (f : H ≃g K) (S : Finset V) (x : V) :
    branchCount K (S.image f) (f x) = branchCount H S x := by
  unfold branchCount
  rw [←Finset.image_erase f.injective,Finset.image_image]
  let e := (cutIso f x).connectedComponentEquiv
  have he : ((S.erase x).image (fun a => (cutVertex K (f x)).connectedComponentMk (f a))) =
      (((S.erase x).image (cutVertex H x).connectedComponentMk).image e) := by
    rw [Finset.image_image]
    rfl
  change ((S.erase x).image (fun a => (cutVertex K (f x)).connectedComponentMk (f a))).card = _
  rw [he]
  exact Finset.card_image_iff.mpr e.injective.injOn

theorem clusterFinset_aut (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E)
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    (clusterFinset G (b ⁻¹' ω) x).image a = clusterFinset G ω (a x) := by
  have hi : (cluster G (b ⁻¹' ω) x).Infinite ↔ (cluster G ω (a x)).Infinite := by
    rw [←cluster_aut G hab]
    exact (Set.infinite_image_iff a.injective.injOn).symm
  by_cases hf : (cluster G (b ⁻¹' ω) x).Finite
  · have hf' : (cluster G ω (a x)).Finite := by
      rw [←cluster_aut G hab]
      exact hf.image a
    apply Finset.coe_injective
    simp only [Finset.coe_image,clusterFinset_coe G _ _ hf,clusterFinset_coe G _ _ hf']
    exact cluster_aut G hab ω x
  · have hf' : ¬(cluster G ω (a x)).Finite := hi.mp hf
    simp only [clusterFinset,dite_eq_right hf,dite_eq_right hf',Finset.image_empty]

theorem measurable_branchCount_pair [Countable V] [Countable E]
    (G : BondGraph V E) (x : V) :
    Measurable (fun z : Set E × Finset V => branchCount (openSimpleGraph G z.1) z.2 x) :=
  measurable_from_prod_countable_left (fun S => measurable_branchCount G S x)

theorem markedCluster_aut (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E)
    (hab : IsAut G a b) (ω η : Set E) (x : V) :
    (markedCluster G (b ⁻¹' ω) (b ⁻¹' η) x).image a = markedCluster G ω η (a x) := by
  unfold markedCluster
  rw [←clusterFinset_aut G a b hab η x,Finset.filter_image]
  simp only [isEncounter_aut_iff G a b hab]

theorem encounterCount_aut (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E)
    (hab : IsAut G a b) (ω η : Set E) (x : V) :
    encounterCount G (b ⁻¹' ω) (b ⁻¹' η) x = encounterCount G ω η (a x) := by
  simp only [encounterCount,isEncounter_aut_iff G a b hab]
  congr 1
  rw [←markedCluster_aut G a b hab]
  exact (branchCount_iso (openAutIso G a b hab ω) _ x).symm

theorem measurable_markedCluster [Countable V] [Countable E]
    (G : BondGraph V E) (p q : unitInterval) (x : V) :
    Measurable (fun l : E → unitInterval => markedCluster G (openEdges l p) (openEdges l q) x) :=
  measurable_filter_finset _ ((measurable_clusterFinset G x).comp (measurable_openEdges q)) _
    (fun y => (measurableSet_isEncounter G y).preimage (measurable_openEdges p))

theorem measurable_encounterCount [Countable V] [Countable E]
    (G : BondGraph V E) (p q : unitInterval) (x : V) :
    Measurable (fun l : E → unitInterval => encounterCount G (openEdges l p) (openEdges l q) x) := by
  apply Measurable.ite ((measurableSet_isEncounter G x).preimage (measurable_openEdges p)) _ measurable_const
  exact (measurable_branchCount_pair G x).comp
    ((measurable_openEdges p).prodMk (measurable_markedCluster G p q x))

theorem cluster_induce_connected (G : BondGraph V E) (ω η : Set E) (hsub : η ⊆ ω) (x : V) :
    ((openSimpleGraph G ω).induce (cluster G η x)).Connected := by
  let H := openSimpleGraph G η
  have he : cluster G η x = (H.connectedComponentMk x).supp := by
    ext y
    simp only [cluster,Set.mem_ofPred_eq,ConnectedComponent.mem_supp_iff,ConnectedComponent.eq]
    exact (conn_iff_reachable G η x y).trans SimpleGraph.reachable_comm
  rw [he]
  apply SimpleGraph.Connected.mono (G := H.induce (H.connectedComponentMk x).supp)
  · intro a b hab
    exact ⟨hab.1,by obtain ⟨e,he,hGe⟩ := hab.2; exact ⟨e,hsub he,hGe⟩⟩
  · exact (H.connectedComponentMk x).connected_toSimpleGraph

theorem markedCluster_eq_of_conn (G : BondGraph V E) (ω η : Set E) {x y : V}
    (hxy : Conn G η x y) : markedCluster G ω η x = markedCluster G ω η y := by
  unfold markedCluster clusterFinset
  simp only [cluster_eq_of_conn G η hxy]

theorem sum_encounterCount_le (G : BondGraph V E) (ω η : Set E) (hsub : η ⊆ ω) (x : V)
    (hf : (cluster G η x).Finite) :
    (∑ y ∈ clusterFinset G η x, encounterCount G ω η y) ≤
      2*(markedCluster G ω η x).card := by
  let D := clusterFinset G η x
  let S := markedCluster G ω η x
  have hSD : S ⊆ D := Finset.filter_subset _ _
  have hDeq : (D:Set V) = cluster G η x := clusterFinset_coe G η x hf
  have hDconn : ((openSimpleGraph G ω).induce (D:Set V)).Connected :=
    hDeq ▸ cluster_induce_connected G ω η hsub x
  have he : (∑ y ∈ D, encounterCount G ω η y) =
      ∑ y ∈ S, branchCount (openSimpleGraph G ω) S y := by
    calc
      _ = ∑ y ∈ D, if IsEncounter G ω y then branchCount (openSimpleGraph G ω) S y else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        have hxy : Conn G η x y := by
          change y ∈ cluster G η x
          rw [←hDeq]
          exact hy
        rw [encounterCount,←markedCluster_eq_of_conn G ω η hxy]
      _ = _ := (Finset.sum_filter _ _).symm
  rw [he]
  by_cases hs : S.Nonempty
  · exact (Nat.le_add_right _ 2).trans (sum_branchCount_le (openSimpleGraph G ω) S D hs hSD hDconn)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

end Percolation

namespace Percolation
open MeasureTheory SimpleGraph
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_average_eq_sum (G : BondGraph V E) (η : Set E) (x : V)
    (hf : (cluster G η x).Finite) (f : V → ℝ≥0∞) :
    (∑' y, clusterAveragingKernel G η x y * f y) =
      ((cluster G η x).ncard : ℝ≥0∞)⁻¹ * ∑ y ∈ clusterFinset G η x, f y := by
  rw [tsum_eq_sum (s := clusterFinset G η x)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    have hc : Conn G η x y := by
      change y ∈ cluster G η x
      rw [←clusterFinset_coe G η x hf]
      exact hy
    simp only [clusterAveragingKernel,ite_eq_left hc]
  · intro y hy
    have hc : ¬Conn G η x y := by
      intro h
      apply hy
      have hm : y ∈ cluster G η x := h
      rwa [←clusterFinset_coe G η x hf] at hm
    simp only [clusterAveragingKernel,ite_eq_right hc,zero_mul]

theorem average_encounterCount_le (G : BondGraph V E) (ω η : Set E) (hsub : η ⊆ ω)
    (x : V) (hf : (cluster G η x).Finite) :
    (∑' y, clusterAveragingKernel G η x y * (encounterCount G ω η y : ℝ≥0∞)) ≤
      2 * ∑' y, clusterAveragingKernel G η x y * (if IsEncounter G ω y then 1 else 0) := by
  rw [cluster_average_eq_sum G η x hf,cluster_average_eq_sum G η x hf]
  have hc : (∑ y ∈ clusterFinset G η x, (encounterCount G ω η y : ℝ≥0∞)) ≤
      2 * (markedCluster G ω η x).card := by
    exact_mod_cast sum_encounterCount_le G ω η hsub x hf
  have he : (∑ y ∈ clusterFinset G η x, (if IsEncounter G ω y then (1:ℝ≥0∞) else 0)) =
      (markedCluster G ω η x).card := by
    rw [←Finset.sum_filter]
    simp only [markedCluster,Finset.sum_const,nsmul_one]
  rw [he,←mul_assoc, mul_comm (2:ℝ≥0∞),mul_assoc]
  exact mul_le_mul_right hc _

theorem expected_encounterCount_le [Countable V] [Countable E] [Fintype ι]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 ≤ weight i)
    (p q : unitInterval) (hqp : q ≤ p)
    (hfin : ∀ x, ∀ᵐ ω ∂law q, (cluster G ω x).Finite) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l,
      (encounterCount G (openEdges l p) (openEdges l q) (root i) : ℝ≥0∞) ∂labelLaw) ≤
    2 * (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l,
      (if IsEncounter G (openEdges l p) (root i) then 1 else 0) ∂labelLaw) := by
  have ha := label_root_cluster_average G hconn hloc root weight htr hw q hfin
    (fun l x => (encounterCount G (openEdges l p) (openEdges l q) x : ℝ≥0∞))
    (fun x => (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp (measurable_encounterCount G p q x))
    (fun a b hab l x => by exact_mod_cast encounterCount_aut G a b hab (openEdges l p) (openEdges l q) x)
  have hb := label_root_cluster_average G hconn hloc root weight htr hw q hfin
    (fun l x => if IsEncounter G (openEdges l p) x then (1:ℝ≥0∞) else 0)
    (fun x => Measurable.ite ((measurableSet_isEncounter G x).preimage (measurable_openEdges p))
      measurable_const measurable_const)
    (fun a b hab l x => by simp only [show openEdges (l ∘ b) p = b ⁻¹' openEdges l p from rfl,
      isEncounter_aut_iff G a b hab])
  rw [←ha,←hb,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [←mul_assoc,mul_comm (2:ℝ≥0∞),mul_assoc]
  apply mul_le_mul_right
  rw [←lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
  apply lintegral_mono_ae
  have hfl : ∀ᵐ l ∂labelLaw, (cluster G (openEdges l q) (root i)).Finite := by
    apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
      (p := fun ω : Set E => (cluster G ω (root i)).Finite) (measurable_openEdges q).aemeasurable
    rw [map_openEdges]
    exact hfin (root i)
  filter_upwards [hfl] with l hl
  exact average_encounterCount_le G _ _ (openEdges_mono l hqp) (root i) hl
end Percolation

end OAI
end

section
-- module Solutions.OAIQ040_CM.UnimodularPercolation_Encounter_ZeroIntensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical limits and zero encounter intensity. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph Filter Topology
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem branchCount_three (H : SimpleGraph V) (S : Finset V) (x a b c : V)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x)
    (hab : ¬(cutVertex H x).Reachable a b)
    (hac : ¬(cutVertex H x).Reachable a c)
    (hbc : ¬(cutVertex H x).Reachable b c) : 3 ≤ branchCount H S x := by
  let f := (cutVertex H x).connectedComponentMk
  have hab' : f a ≠ f b := fun h => hab (ConnectedComponent.exact h)
  have hac' : f a ≠ f c := fun h => hac (ConnectedComponent.exact h)
  have hbc' : f b ≠ f c := fun h => hbc (ConnectedComponent.exact h)
  have hs : ({f a,f b,f c}:Finset _) ⊆ (S.erase x).image f := by
    intro y hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨a,Finset.mem_erase.mpr ⟨hax,ha⟩,rfl⟩
    · exact Finset.mem_image.mpr ⟨b,Finset.mem_erase.mpr ⟨hbx,hb⟩,rfl⟩
    · exact Finset.mem_image.mpr ⟨c,Finset.mem_erase.mpr ⟨hcx,hc⟩,rfl⟩
  have hh := Finset.card_le_card hs
  have hcard : ({f a,f b,f c}:Finset _).card = 3 := by simp [hab',hac',hbc']
  rw [hcard] at hh
  exact hh

theorem eventually_conn_of_limit (G : BondGraph V E) (l : E → unitInterval)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hq : ∀ n, q n ≤ p) (hlim : Tendsto q atTop (𝓝 p)) (hne : ∀ e, l e ≠ p)
    {x y : V} (hxy : Conn G (openEdges l p) x y) :
    ∀ᶠ n in atTop, Conn G (openEdges l (q n)) x y := by
  rw [openEdges_eq_iUnion_of_tendsto l p hne q hq hlim,conn_iUnion_iff G _
    (fun m n hmn => openEdges_mono l (hmono hmn))] at hxy
  obtain ⟨n,hn⟩ := hxy
  exact eventually_atTop.mpr ⟨n,fun m hm => conn_mono G (openEdges_mono l (hmono hm)) hn⟩

theorem eventually_encounterCount_three (G : BondGraph V E) (l : E → unitInterval)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hq : ∀ n, q n ≤ p) (hlim : Tendsto q atTop (𝓝 p)) (hne : ∀ e, l e ≠ p)
    (hfin : ∀ n x, (cluster G (openEdges l (q n)) x).Finite)
    (hbranch : ∀ x, IsEncounter G (openEdges l p) x → ∀ a,
      Conn G (openEdges l p) x a → (cluster G (cutConfig G (openEdges l p) x) a).Infinite →
      ∃ z ∈ cluster G (cutConfig G (openEdges l p) x) a, z ≠ x ∧ IsEncounter G (openEdges l p) z)
    (x : V) (hx : IsEncounter G (openEdges l p) x) :
    ∀ᶠ n in atTop, 3 ≤ encounterCount G (openEdges l p) (openEdges l (q n)) x := by
  obtain ⟨a,b,c,hxa,hxb,hxc,ha,hb,hc,hab,hac,hbc⟩ := hx
  obtain ⟨a',haa',hax,ha'⟩ := hbranch x ⟨a,b,c,hxa,hxb,hxc,ha,hb,hc,hab,hac,hbc⟩ a hxa ha
  obtain ⟨b',hbb',hbx,hb'⟩ := hbranch x ⟨a,b,c,hxa,hxb,hxc,ha,hb,hc,hab,hac,hbc⟩ b hxb hb
  obtain ⟨c',hcc',hcx,hc'⟩ := hbranch x ⟨a,b,c,hxa,hxb,hxc,ha,hb,hc,hab,hac,hbc⟩ c hxc hc
  have hx' : IsEncounter G (openEdges l p) x := ⟨a,b,c,hxa,hxb,hxc,ha,hb,hc,hab,hac,hbc⟩
  have hac' : Conn G (openEdges l p) x a' := conn_trans G _ hxa (conn_mono G (fun _ h => h.1) haa')
  have hbc' : Conn G (openEdges l p) x b' := conn_trans G _ hxb (conn_mono G (fun _ h => h.1) hbb')
  have hxc' : Conn G (openEdges l p) x c' := conn_trans G _ hxc (conn_mono G (fun _ h => h.1) hcc')
  filter_upwards [eventually_conn_of_limit G l p q hmono hq hlim hne hac',
    eventually_conn_of_limit G l p q hmono hq hlim hne hbc',
    eventually_conn_of_limit G l p q hmono hq hlim hne hxc'] with n han hbn hcn
  rw [encounterCount,ite_eq_left hx']
  have hm (z : V) (hz : Conn G (openEdges l (q n)) x z) (he : IsEncounter G (openEdges l p) z) :
      z ∈ markedCluster G (openEdges l p) (openEdges l (q n)) x := by
    apply Finset.mem_filter.mpr
    refine ⟨?_,he⟩
    have ht : z ∈ cluster G (openEdges l (q n)) x := hz
    rwa [←clusterFinset_coe G _ x (hfin n x)] at ht
  apply branchCount_three _ _ x a' b' c' (hm _ han ha') (hm _ hbn hb') (hm _ hcn hc') hax hbx hcx
  · intro ht
    rw [cutVertex_open] at ht
    exact hab (conn_trans G _ haa' (conn_trans G _ ((conn_iff_reachable G _ a' b').mpr ht) (conn_symm G _ hbb')))
  · intro ht
    rw [cutVertex_open] at ht
    exact hac (conn_trans G _ haa' (conn_trans G _ ((conn_iff_reachable G _ a' c').mpr ht) (conn_symm G _ hcc')))
  · intro ht
    rw [cutVertex_open] at ht
    exact hbc (conn_trans G _ hbb' (conn_trans G _ ((conn_iff_reachable G _ b' c').mpr ht) (conn_symm G _ hcc')))

end Percolation

namespace Percolation
open MeasureTheory SimpleGraph Filter Topology
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Fintype ι]

theorem critical_encounter_density_zero
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hp : 0 < pc G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1)
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l,
      (if IsEncounter G (openEdges l (pc G)) (root i) then 1 else 0) ∂labelLaw) = 0 := by
  obtain ⟨q,hmono,hq,hlim⟩ := exists_seq_strictMono_tendsto' hp
  let d (l : E → unitInterval) : ℝ≥0∞ := ∑ i, ENNReal.ofReal (weight i) *
    if IsEncounter G (openEdges l (pc G)) (root i) then 1 else 0
  let f (n : ℕ) (l : E → unitInterval) : ℝ≥0∞ := ∑ i, ENNReal.ofReal (weight i) *
    (encounterCount G (openEdges l (pc G)) (openEdges l (q n)) (root i) : ℝ≥0∞)
  have hd : Measurable d := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (Measurable.ite ((measurableSet_isEncounter G (root i)).preimage
      (measurable_openEdges (pc G))) measurable_const measurable_const)
  have hf n : Measurable (f n) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
      (measurable_encounterCount G (pc G) (q n) (root i)))
  have hdint : (∫⁻ l, d l ∂labelLaw) = ∑ i, ENNReal.ofReal (weight i) * ∫⁻ l,
      (if IsEncounter G (openEdges l (pc G)) (root i) then 1 else 0) ∂labelLaw := by
    rw [show d = _ from rfl,lintegral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    · intro i _
      exact measurable_const.mul (Measurable.ite ((measurableSet_isEncounter G (root i)).preimage
        (measurable_openEdges (pc G))) measurable_const measurable_const)
  have hbound n : (∫⁻ l, f n l ∂labelLaw) ≤ 2 * ∫⁻ l, d l ∂labelLaw := by
    rw [hdint,show f n = _ from rfl,lintegral_finsetSum]
    · simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact expected_encounterCount_le G hconn hloc root weight htr (fun i => (hw i).le)
        (pc G) (q n) (hq n).2.le (fun x => subcritical_cluster_finite_ae G (q n) (hq n).2 x)
    · intro i _
      exact measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
        (measurable_encounterCount G (pc G) (q n) (root i)))
  have hfl : ∀ᵐ l ∂labelLaw, ∀ n x, (cluster G (openEdges l (q n)) x).Finite :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun x => label_cluster_finite_ae_subcritical G (q n) (hq n).2 x
  have hbl : ∀ᵐ l ∂labelLaw, ∀ x, IsEncounter G (openEdges l (pc G)) x → ∀ a,
      Conn G (openEdges l (pc G)) x a → (cluster G (cutConfig G (openEdges l (pc G)) x) a).Infinite →
      ∃ z ∈ cluster G (cutConfig G (openEdges l (pc G)) x) a, z ≠ x ∧ IsEncounter G (openEdges l (pc G)) z := by
    apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
      (p := fun ω : Set E => ∀ x, IsEncounter G ω x → ∀ a,
        Conn G ω x a → (cluster G (cutConfig G ω x) a).Infinite →
        ∃ z ∈ cluster G (cutConfig G ω x) a, z ≠ x ∧ IsEncounter G ω z)
      (measurable_openEdges (pc G)).aemeasurable
    rw [map_openEdges]
    exact encounter_branches_ae G hconn hloc root weight htr hw hw1 hcov (pc G)
  have hlow : ∀ᵐ l ∂labelLaw, 3 * d l ≤ liminf (fun n => f n l) atTop := by
    filter_upwards [hfl,hbl,ae_labels_ne (E := E) (pc G)] with l hl hb hn
    refine le_liminf_of_le (by isBoundedDefault) ?_
    have he (i : ι) : ∀ᶠ n in atTop,
        (3:ℝ≥0∞) * (if IsEncounter G (openEdges l (pc G)) (root i) then 1 else 0) ≤
        (encounterCount G (openEdges l (pc G)) (openEdges l (q n)) (root i) : ℝ≥0∞) := by
      by_cases hi : IsEncounter G (openEdges l (pc G)) (root i)
      · filter_upwards [eventually_encounterCount_three G l (pc G) q hmono.monotone
          (fun n => (hq n).2.le) hlim hn hl hb (root i) hi] with n hnc
        simpa only [ite_eq_left hi,mul_one] using (show (3:ℝ≥0∞) ≤ (encounterCount G (openEdges l (pc G)) (openEdges l (q n)) (root i):ℝ≥0∞) from by exact_mod_cast hnc)
      · filter_upwards [] with n
        simp only [ite_eq_right hi,mul_zero,zero_le]
    filter_upwards [(eventually_all_finset (Finset.univ : Finset ι)).mpr (fun i _ => he i)] with n hnn
    dsimp [d,f]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [←mul_assoc,mul_comm (3:ℝ≥0∞),mul_assoc]
    exact mul_le_mul_right (hnn i hi) _
  have hineq : 3 * (∫⁻ l, d l ∂labelLaw) ≤ 2 * ∫⁻ l, d l ∂labelLaw := by
    calc
      _ = ∫⁻ l, 3 * d l ∂labelLaw := (lintegral_const_mul' _ _ ENNReal.ofNat_ne_top).symm
      _ ≤ ∫⁻ l, liminf (fun n => f n l) atTop ∂labelLaw := lintegral_mono_ae hlow
      _ ≤ liminf (fun n => ∫⁻ l, f n l ∂labelLaw) atTop := lintegral_liminf_le hf
      _ ≤ _ := by
        refine liminf_le_of_le (by isBoundedDefault) ?_
        intro b hb
        obtain ⟨n,hn⟩ := hb.exists
        exact hn.trans (hbound n)
  have hdle (l : E → unitInterval) : d l ≤ 1 := by
    calc
      _ ≤ ∑ i, ENNReal.ofReal (weight i) * 1 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_right
        split_ifs <;> simp
      _ = 1 := by
        simp only [mul_one,←ENNReal.ofReal_sum_of_nonneg (fun i _ => (hw i).le),hw1,ENNReal.ofReal_one]
  have hdf : (∫⁻ l, d l ∂labelLaw) ≠ ⊤ := by
    have he : (∫⁻ l, d l ∂labelLaw) ≤ 1 := (lintegral_mono hdle).trans_eq (by simp)
    exact ne_of_lt (he.trans_lt ENNReal.one_lt_top)
  rw [←hdint]
  by_contra hne
  exact (not_lt_of_ge hineq) (ENNReal.mul_lt_mul_left hne hdf (by norm_num))

theorem critical_encounter_root_zero
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hp : 0 < pc G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1)
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x) (i : ι) :
    law (pc G) {ω | IsEncounter G ω (root i)} = 0 := by
  have hd := critical_encounter_density_zero G hconn hloc hp root weight htr hw hw1 hcov
  have hi : ENNReal.ofReal (weight i) * ∫⁻ l,
      (if IsEncounter G (openEdges l (pc G)) (root i) then (1:ℝ≥0∞) else 0) ∂labelLaw = 0 := by
    exact (Finset.sum_eq_zero_iff.mp hd) i (Finset.mem_univ i)
  have hz : (∫⁻ l, (if IsEncounter G (openEdges l (pc G)) (root i) then (1:ℝ≥0∞) else 0) ∂labelLaw) = 0 :=
    (mul_eq_zero.mp hi).resolve_left ((ENNReal.ofReal_pos.mpr (hw i)).ne')
  rw [←map_openEdges (pc G),Measure.map_apply (measurable_openEdges (pc G))
    (measurableSet_isEncounter G (root i))]
  have he : (fun l : E → unitInterval => if IsEncounter G (openEdges l (pc G)) (root i) then (1:ℝ≥0∞) else 0) =
      ((fun l : E → unitInterval => openEdges l (pc G)) ⁻¹' {ω | IsEncounter G ω (root i)}).indicator (fun _ => 1) := rfl
  rw [he,lintegral_indicator ((measurableSet_isEncounter G (root i)).preimage (measurable_openEdges (pc G)))] at hz
  simpa only [lintegral_const,Measure.restrict_apply_univ,one_mul] using hz

theorem critical_encounter_zero_oai
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hp : 0 < pc G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1)
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x) (x : V) :
    law (pc G) {ω | IsEncounter G ω x} = 0 := by
  obtain ⟨i,a,⟨b,hab⟩,rfl⟩ := hcov x
  have he : {ω | IsEncounter G ω (a (root i))} =
      (fun ω : Set E => b ⁻¹' ω) ⁻¹' {ω | IsEncounter G ω (root i)} := by
    ext ω
    exact (isEncounter_aut_iff G a b hab ω (root i)).symm
  rw [he,←Measure.map_apply (measurable_set_preimage b) (measurableSet_isEncounter G (root i)),
    law_map_preimage_equiv]
  exact critical_encounter_root_zero G hconn hloc hp root weight htr hw hw1 hcov i

end Percolation

end OAI
end

theorem solution.{u, v, w} : type_of% @OAI.Percolation.critical_encounter_zero_oai.{u, v, w} := @OAI.Percolation.critical_encounter_zero_oai.{u, v, w}
