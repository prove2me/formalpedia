-- Prove2me | solution 1 for OAI.Percolation.BenjaminiSchramm.critical_finite_general_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:04:29.597836+00:00
-- url     : https://prove2.me/submissions/a1a56b08-453d-40d2-8dce-6d4ba6afa074

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_main_failure_topological_classification_counterexample_bs
import Theorems.Thm_OAI_CriticalPercolation_CompactQuotient_virtuallyNilpotent_of_sparse_word_growth_bs
import Theorems.Thm_OAI_CriticalPercolation_RelativeGrowth_virtually_indicable_bs

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Graph_Basic
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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

theorem conn_univ_of_connected (h : Connected G) (x y : V) : Conn G Set.univ x y := by
  apply Relation.ReflTransGen.mono (r := Adj G) ?_ x y (h x y)
  rintro a b ⟨e, he⟩
  exact ⟨e, Set.mem_univ _, he⟩

end Deterministic

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PhaseInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem criticalModel_openGraph (G : BondGraph V E) (ω : Set E) :
    (criticalModel G).openGraph ω = openSimpleGraph G ω := by
  ext x y
  simp only [CriticalPercolation.BondGraph.openGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_image, openSimpleGraph, criticalModel]
  tauto

theorem criticalModel_cluster (G : BondGraph V E) (ω : Set E) (x : V) :
    (criticalModel G).cluster ω x = cluster G ω x := by
  ext y
  simp only [CriticalPercolation.BondGraph.cluster, criticalModel_openGraph,
    Set.mem_ofPred_eq, cluster]
  exact (conn_iff_reachable G ω x y).symm

theorem criticalModel_connected [Nonempty V] (G : BondGraph V E) (hconn : Connected G) :
    (criticalModel G).fullGraph.Connected := by
  rw [CriticalPercolation.BondGraph.fullGraph, criticalModel_openGraph]
  exact ⟨fun x y => (conn_iff_reachable G Set.univ x y).mp (conn_univ_of_connected G hconn x y)⟩

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_CriticalFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem criticalModel_percolates (G : BondGraph V E) :
    (criticalModel G).percolates = {ω | (infiniteClusters G ω).Nonempty} := by
  ext ω
  simp only [CriticalPercolation.BondGraph.percolates, Set.mem_ofPred_eq,
    criticalModel_cluster, Set.Nonempty, infiniteClusters]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨cluster G ω x,hx,x,rfl⟩
  · rintro ⟨C,hC,x,hx⟩
    exact ⟨x,hx ▸ hC⟩

theorem criticalModel_pc (G : BondGraph V E) :
    (criticalModel G).criticalProbability = pc G := by
  simp only [CriticalPercolation.BondGraph.criticalProbability, criticalModel_percolates,
    CriticalPercolation.BondGraph.law, pc, law]

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_GraphAutomorphismTopology
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X]

lemma continuous_variable_eval : Continuous (fun p : (X → X) × X => p.1 p.2) :=
  continuous_prod_of_discrete_right.mpr fun x => continuous_apply x

variable (Γ : SimpleGraph X)

attribute [local instance] OAI.CriticalPercolation.GraphTopology.instTopologicalSpaceIso_solutions
omit [DiscreteTopology X] in
lemma coordinates_embedding : IsEmbedding (coordinates Γ) where
  eq_induced := rfl
  injective := by
    intro g h he
    apply RelIso.ext
    intro x
    exact congrFun (congrArg Prod.fst he) x

omit [DiscreteTopology X] in
lemma continuous_eval (x : X) : Continuous (fun g : Γ ≃g Γ => g x) :=
  (continuous_apply x).comp (continuous_fst.comp (coordinates_embedding Γ).continuous)

omit [DiscreteTopology X] in
lemma continuous_inv_eval (x : X) : Continuous (fun g : Γ ≃g Γ => g.symm x) :=
  (continuous_apply x).comp (continuous_snd.comp (coordinates_embedding Γ).continuous)

omit [TopologicalSpace X] [DiscreteTopology X] in
lemma coordinates_range : Set.range (coordinates Γ) =
    {p : (X → X) × (X → X) |
      (∀ x, p.2 (p.1 x)=x) ∧ (∀ x, p.1 (p.2 x)=x) ∧
      (∀ x y, Γ.Adj (p.1 x) (p.1 y) ↔ Γ.Adj x y)} := by
  ext p
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g.symm_apply_apply,g.apply_symm_apply,fun _ _ => g.map_adj_iff⟩
  · rintro ⟨hleft,hright,hadj⟩
    refine ⟨{toEquiv := ⟨p.1,p.2,hleft,hright⟩,map_rel_iff' := fun {x y} => hadj x y},?_⟩
    exact Prod.eta p

lemma coordinates_closed : IsClosed (Set.range (coordinates Γ)) := by
  rw [coordinates_range]
  simp only [Set.ofPred_and,Set.ofPred_forall]
  refine (isClosed_iInter fun x => ?_).inter ((isClosed_iInter fun x => ?_).inter
    (isClosed_iInter fun x => isClosed_iInter fun y => ?_))
  · change IsClosed {p : (X → X) × (X → X) | p.2 (p.1 x)=x}
    exact isClosed_eq ((continuous_variable_eval (X := X)).comp (continuous_snd.prodMk
      ((continuous_apply x).comp continuous_fst))) continuous_const
  · change IsClosed {p : (X → X) × (X → X) | p.1 (p.2 x)=x}
    exact isClosed_eq ((continuous_variable_eval (X := X)).comp (continuous_fst.prodMk
      ((continuous_apply x).comp continuous_snd))) continuous_const
  · change IsClosed {p : (X → X) × (X → X) | Γ.Adj (p.1 x) (p.1 y) ↔ Γ.Adj x y}
    exact (isClosed_discrete {p : X × X | Γ.Adj p.1 p.2 ↔ Γ.Adj x y}).preimage
      (show Continuous (fun p : (X → X) × (X → X) => (p.1 x,p.1 y)) from
        ((continuous_apply x).comp continuous_fst).prodMk
          ((continuous_apply y).comp continuous_fst))

lemma coordinates_closedEmbedding : IsClosedEmbedding (coordinates Γ) :=
  ⟨coordinates_embedding Γ,coordinates_closed Γ⟩

instance aut_t2 : T2Space (Γ ≃g Γ) := (coordinates_embedding Γ).t2Space

instance aut_topologicalGroup : IsTopologicalGroup (Γ ≃g Γ) where
  continuous_mul := by
    apply (coordinates_embedding Γ).continuous_iff.mpr
    apply Continuous.prodMk
    · apply continuous_pi
      intro x
      exact continuous_variable_eval.comp
        (((continuous_fst.comp (coordinates_embedding Γ).continuous).comp continuous_fst).prodMk
          ((continuous_eval Γ x).comp continuous_snd))
    · apply continuous_pi
      intro x
      exact continuous_variable_eval.comp
        (((continuous_snd.comp (coordinates_embedding Γ).continuous).comp continuous_snd).prodMk
          ((continuous_inv_eval Γ x).comp continuous_fst))
  continuous_inv := by
    apply (coordinates_embedding Γ).continuous_iff.mpr
    exact (continuous_snd.comp (coordinates_embedding Γ).continuous).prodMk
      (continuous_fst.comp (coordinates_embedding Γ).continuous)

lemma compact_coordinate_bounds (F : X → Set X) (hF : ∀ x, (F x).Finite) :
    IsCompact {g : Γ ≃g Γ | (∀ x, g x∈F x) ∧ (∀ x, g.symm x∈F x)} := by
  have hK : IsCompact {f : X → X | ∀ x, f x∈F x} :=
    isCompact_pi_infinite fun x => (hF x).isCompact
  exact (coordinates_closedEmbedding Γ).isCompact_preimage (hK.prod hK)

lemma isClosed_eval_mem (x : X) (S : Set X) :
    IsClosed {g : Γ ≃g Γ | g x∈S} :=
  (isClosed_discrete S).preimage (continuous_eval Γ x)

lemma isOpen_eval_mem (x : X) (S : Set X) :
    IsOpen {g : Γ ≃g Γ | g x∈S} :=
  (isOpen_discrete S).preimage (continuous_eval Γ x)

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_GraphNeighborhoodCompact
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma reachBall_self (o : X) (r : ℕ) : o∈reachBall Γ o r :=
  ⟨SimpleGraph.Walk.nil,Nat.zero_le _⟩

lemma reachBall_symm {o x : X} {r : ℕ} (h : x∈reachBall Γ o r) :
    o∈reachBall Γ x r := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.reverse,by simpa using hp⟩

lemma inverse_displacement {o : X} {r : ℕ} (g : Γ ≃g Γ)
    (h : g o∈reachBall Γ o r) : g.symm o∈reachBall Γ o r := by
  have hh := reachBall_symm Γ (iso_reachBall Γ g.symm h)
  simpa using hh

variable [TopologicalSpace X] [DiscreteTopology X]

attribute [local instance] OAI.CriticalPercolation.GraphTopology.instTopologicalSpaceIso_solutions_1
lemma compact_displacement (hc : Γ.Connected)
    (hl : ∀ x, (Γ.neighborSet x).Finite) (o : X) (r : ℕ) :
    IsCompact {g : Γ ≃g Γ | g o∈reachBall Γ o r} := by
  have hp : ∀ x, ∃ p : Γ.Walk o x, True := fun x => by
    obtain ⟨p⟩ := hc o x
    exact ⟨p,trivial⟩
  choose p _ using hp
  let F : X → Set X := fun x => reachBall Γ o (r+(p x).length)
  have hfb : ∀ (g : Γ ≃g Γ), g o∈reachBall Γ o r → ∀ x, g x∈F x := by
    intro g hg x
    exact reachBall_add Γ hg (iso_reachBall Γ g ⟨p x,le_rfl⟩)
  apply (compact_coordinate_bounds Γ F (fun x => reachBall_finite Γ hl o _)).of_isClosed_subset
    (isClosed_eval_mem Γ o _)
  intro g hg
  exact ⟨hfb g hg,hfb g.symm (inverse_displacement Γ g hg)⟩

lemma compact_stabilizer (hc : Γ.Connected)
    (hl : ∀ x, (Γ.neighborSet x).Finite) (o : X) :
    IsCompact {g : Γ ≃g Γ | g o=o} := by
  apply (compact_displacement Γ hc hl o 0).of_isClosed_subset
    (isClosed_eq (continuous_eval Γ o) continuous_const)
  intro g hg
  change g o∈reachBall Γ o 0
  rw [hg]
  exact reachBall_self Γ o 0

lemma open_stabilizer (o : X) : IsOpen {g : Γ ≃g Γ | g o=o} :=
  isOpen_eval_mem Γ o {o}

instance aut_totallyDisconnected : TotallyDisconnectedSpace (Γ ≃g Γ) :=
  (coordinates_embedding Γ).isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_GraphApproximateNeighborhoods
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma one_mem_displacement (o : X) (r : ℕ) : 1∈displacement Γ o r :=
  reachBall_self Γ o r

lemma displacement_inv {o : X} {r : ℕ} {g : Γ ≃g Γ} :
    g⁻¹∈displacement Γ o r ↔ g∈displacement Γ o r := by
  constructor
  · intro h
    change g o∈reachBall Γ o r
    simpa using inverse_displacement Γ g.symm h
  · exact inverse_displacement Γ g

lemma displacement_mul_subset (o : X) (r s : ℕ) :
    displacement Γ o r * displacement Γ o s ⊆ displacement Γ o (r+s) := by
  rintro g ⟨a,ha,b,hb,rfl⟩
  exact reachBall_add Γ ha (iso_reachBall Γ a hb)

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_GraphGeneratingNeighborhood
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma displacement_eq_pow (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v)
    (o : X) (n : ℕ) : displacement Γ o (n+1)=displacement Γ o 1^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply Set.Subset.antisymm
    · intro g hg
      obtain ⟨p,hp⟩ := hg
      rw [pow_succ']
      generalize hx : g o=x at p
      cases p with
      | nil =>
        have hg1 : g∈displacement Γ o 1 := by
          change g o∈reachBall Γ o 1
          rw [hx]
          exact reachBall_self Γ o 1
        refine Set.mem_mul.mpr ⟨g,hg1,1,?_,mul_one g⟩
        rw [←ih]
        exact one_mem_displacement Γ o _
      | @cons a b c hab p =>
        obtain ⟨f,hf⟩ := ht o b
        have hfmem : f∈displacement Γ o 1 := by
          change f o∈reachBall Γ o 1
          rw [hf]
          exact ⟨SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil,by simp⟩
        have hrem : f⁻¹*g∈displacement Γ o (n+1) := by
          have hwalk : g o∈reachBall Γ b (n+1) := by
            rw [hx]
            exact ⟨p,by simpa using hp⟩
          have hh := iso_reachBall Γ f.symm hwalk
          rw [←hf] at hh
          change f.symm (g o)∈reachBall Γ o (n+1)
          simpa using hh
        refine Set.mem_mul.mpr ⟨f,hfmem,f⁻¹*g,?_,by simp⟩
        rw [←ih]
        exact hrem
    · rw [pow_succ',←ih]
      simpa only [show 1+(n+1)=n+1+1 by omega] using
        displacement_mul_subset Γ o 1 (n+1)

lemma displacement_powers_cover (hc : Γ.Connected)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (g : Γ ≃g Γ) :
    ∃ n : ℕ, g∈displacement Γ o 1^(n+1) := by
  obtain ⟨p⟩ := hc o (g o)
  refine ⟨p.length,?_⟩
  rw [←displacement_eq_pow Γ ht]
  exact ⟨p,Nat.le_succ _⟩

lemma displacement_generates (hc : Γ.Connected)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) :
    Subgroup.closure (displacement Γ o 1)=⊤ := by
  apply top_unique
  intro g _
  obtain ⟨n,hn⟩ := displacement_powers_cover Γ hc ht o g
  have hpow : ∀ k : ℕ, displacement Γ o 1^k ⊆
      (Subgroup.closure (displacement Γ o 1) : Set (Γ ≃g Γ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      rintro a ⟨b,hb,c,hc,rfl⟩
      exact (Subgroup.closure _).mul_mem (ih hb) (Subgroup.subset_closure hc)
  exact hpow (n+1) hn

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetBallIndex
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Pointwise

namespace CriticalPercolation.CosetGrowth
variable {A : Type*} [Group A]

lemma ball_zero (S : Set A) (L : Subgroup A) : ball S L 0={QuotientGroup.mk (1 : A)} := by
  simp [ball]

lemma ball_step (S : Set A) (L : Subgroup A) (n : ℕ) :
    ball S L (n+1)=⋃ s∈S, (fun q : A ⧸ L => s • q) '' ball S L n := by
  ext q
  simp only [ball,pow_succ',Set.mem_image,Set.mem_mul,Set.mem_iUnion]
  constructor
  · rintro ⟨_,⟨s,hs,a,ha,rfl⟩,rfl⟩
    exact ⟨s,hs,QuotientGroup.mk a,⟨a,ha,rfl⟩,rfl⟩
  · rintro ⟨s,hs,_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨s*a,⟨s,hs,a,ha,rfl⟩,rfl⟩

lemma ball_mono (S : Set A) (L : Subgroup A) (h1 : (1 : A)∈S) :
    Monotone (ball S L) := fun _ _ h => Set.image_mono (Set.pow_subset_pow_right h1 h)

lemma ball_one_mem (S : Set A) (L : Subgroup A) (h1 : (1 : A)∈S) (n : ℕ) :
    QuotientGroup.mk (1 : A)∈ball S L n := by
  apply ball_mono S L h1 (Nat.zero_le n)
  rw [ball_zero]
  exact Set.mem_singleton _

lemma ball_eq_univ_of_stationary (S : Set A) (L : Subgroup A)
    (h1 : (1 : A)∈S) (hinv : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (n : ℕ) (hstop : ball S L (n+1)=ball S L n) : ball S L n=Set.univ := by
  have hstable : ∀ s∈S, ∀ q∈ball S L n, s • q∈ball S L n := by
    intro s hs q hq
    rw [←hstop,ball_step]
    exact Set.mem_iUnion.mpr ⟨s,Set.mem_iUnion.mpr ⟨hs,⟨q,hq,rfl⟩⟩⟩
  have hS : S⊆MulAction.stabilizer A (ball S L n) := by
    intro s hs
    change (fun q : A ⧸ L => s • q) '' ball S L n=ball S L n
    apply Set.Subset.antisymm
    · rintro _ ⟨q,hq,rfl⟩
      exact hstable s hs q hq
    · intro q hq
      have hi : s⁻¹∈S := by rw [←hinv]; simpa only [Set.mem_inv,inv_inv] using hs
      exact ⟨s⁻¹ • q,hstable _ hi _ hq,smul_inv_smul s q⟩
  have hall : ∀ g : A, g • ball S L n=ball S L n := by
    have hh := (Subgroup.closure_le (MulAction.stabilizer A (ball S L n))).mpr hS
    rw [hgen] at hh
    exact fun g => hh (Subgroup.mem_top g)
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective q
  have hh : g • (QuotientGroup.mk (1 : A) : A ⧸ L)∈ball S L n := by
    rw [←hall g]
    exact ⟨_,ball_one_mem S L h1 n,rfl⟩
  simpa only [MulAction.Quotient.smul_mk,smul_eq_mul,mul_one] using hh

lemma finiteIndex_of_small_ball (S : Set A) (L : Subgroup A)
    (h1 : (1 : A)∈S) (hinv : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (n : ℕ) (hfin : (ball S L n).Finite) (hsmall : (ball S L n).ncard≤n) :
    L.FiniteIndex := by
  have hmon := ball_mono S L h1
  have hfi : ∀ i≤n, (ball S L i).Finite := fun i hi => hfin.subset (hmon hi)
  have hs : ∃ i<n, ball S L (i+1)=ball S L i := by
    by_contra! h
    have hg : ∀ i≤n, i+1≤(ball S L i).ncard := by
      intro i hi
      induction i with
      | zero => simp [ball_zero]
      | succ i ih =>
        have hle := ih (by omega)
        have hlt : (ball S L i).ncard<(ball S L (i+1)).ncard := by
          apply Set.ncard_lt_ncard
          · exact Set.ssubset_iff_subset_ne.mpr ⟨hmon (Nat.le_succ i),Ne.symm (h i (by omega))⟩
          · exact hfi _ hi
        omega
    have := hg n le_rfl
    omega
  obtain ⟨i,hi,he⟩ := hs
  have heq := ball_eq_univ_of_stationary S L h1 hinv hgen i he
  have hf : (Set.univ : Set (A ⧸ L)).Finite := heq ▸ hfi i (by omega)
  let _ : Finite (A ⧸ L) := Set.finite_univ_iff.mp hf
  exact Subgroup.finiteIndex_of_finite_quotient

end CriticalPercolation.CosetGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_GraphQuotientGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma image_displacement_ncard_le {B : Type*} [Group B]
    (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X)
    (f : (Γ ≃g Γ) →* B)
    (hB : (f '' {g : Γ ≃g Γ | g o=o}).Finite) (r : ℕ) :
    (f '' displacement Γ o r).ncard ≤
      (reachBall Γ o r).ncard * (f '' {g : Γ ≃g Γ | g o=o}).ncard := by
  let a : X → (Γ ≃g Γ) := fun x => (ht o x).choose
  have ha : ∀ x, a x o=x := fun x => (ht o x).choose_spec
  let U := reachBall Γ o r ×ˢ (f '' {g : Γ ≃g Γ | g o=o})
  let m : X × B → B := fun z => f (a z.1)*z.2
  have hU : U.Finite := (reachBall_finite Γ hl o r).prod hB
  have hs : f '' displacement Γ o r ⊆ m '' U := by
    rintro b ⟨g,hg,rfl⟩
    refine ⟨(g o,f ((a (g o))⁻¹*g)),⟨hg,?_⟩,?_⟩
    · refine ⟨(a (g o))⁻¹*g,?_,rfl⟩
      change (a (g o)).symm (g o)=o
      calc
        (a (g o)).symm (g o) = (a (g o)).symm ((a (g o)) o) :=
          congrArg (a (g o)).symm (ha (g o)).symm
        _ = o := (a (g o)).symm_apply_apply o
    · dsimp only [m]
      rw [←map_mul,mul_inv_cancel_left]
  calc
    (f '' displacement Γ o r).ncard ≤ (m '' U).ncard :=
      Set.ncard_le_ncard hs (hU.image m)
    _ ≤ U.ncard := Set.ncard_image_le hU
    _ = (reachBall Γ o r).ncard * (f '' {g : Γ ≃g Γ | g o=o}).ncard :=
      Set.ncard_prod

theorem quotient_powers_ncard_le
    [TopologicalSpace X] [DiscreteTopology X]
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X)
    (H : Subgroup (Γ ≃g Γ)) [H.Normal]
    (ho : @IsOpen (Γ ≃g Γ) (autTopology Γ) (H : Set (Γ ≃g Γ))) :
    let T := (QuotientGroup.mk' H) '' displacement Γ o 1
    ∃ M : ℕ, 1≤M ∧ T.Finite ∧ (1 : (Γ ≃g Γ) ⧸ H)∈T ∧ T⁻¹=T ∧
      Subgroup.closure T=⊤ ∧ ∀ n : ℕ, 1≤n →
        (T^n).ncard ≤ (reachBall Γ o n).ncard*M := by
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  let _ : DiscreteTopology ((Γ ≃g Γ) ⧸ H) := QuotientGroup.discreteTopology ho
  let f := QuotientGroup.mk' H
  let B := f '' {g : Γ ≃g Γ | g o=o}
  have hB : B.Finite := isCompact_iff_finite.mp
    ((compact_stabilizer Γ hc hl o).image QuotientGroup.continuous_mk)
  have hB1 : (1 : (Γ ≃g Γ) ⧸ H)∈B := ⟨1,rfl,map_one f⟩
  have hM : 1≤B.ncard := (Set.ncard_pos hB).mpr ⟨1,hB1⟩
  dsimp only
  refine ⟨B.ncard,hM,?_,⟨1,one_mem_displacement Γ o 1,map_one f⟩,?_,?_,?_⟩
  · exact isCompact_iff_finite.mp
      ((compact_displacement Γ hc hl o 1).image QuotientGroup.continuous_mk)
  · rw [←Set.image_inv]
    congr 1
    ext g
    exact displacement_inv Γ
  · rw [←MonoidHom.map_closure,displacement_generates Γ hc ht o]
    exact Subgroup.map_top_of_surjective _ QuotientGroup.mk_surjective
  · intro n hn
    rw [←Set.image_pow,←show displacement Γ o n=displacement Γ o 1^n by
      simpa only [Nat.sub_add_cancel hn] using displacement_eq_pow Γ ht o (n-1)]
    exact image_displacement_ncard_le Γ hl ht o f hB n

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_GraphQuotientPolynomial
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation
namespace GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

theorem quotient_sparse_polynomial_word_growth
    [TopologicalSpace X] [DiscreteTopology X]
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d)
    (H : Subgroup (Γ ≃g Γ)) [H.Normal]
    (ho : @IsOpen (Γ ≃g Γ) (autTopology Γ) (H : Set (Γ ≃g Γ))) :
    CompactQuotient.HasSparsePolynomialWordGrowth ((Γ ≃g Γ) ⧸ H) := by
  obtain ⟨M,_,hT,h1,hinv,hgen,hncard⟩ :=
    quotient_powers_ncard_le Γ hc hl ht o H ho
  refine ⟨(QuotientGroup.mk' H) '' displacement Γ o 1,hT,h1,hinv,hgen,d+1,?_⟩
  intro R
  obtain ⟨n,hn,hp⟩ := hpoly (max R (max M 1))
  have hnR : R≤n := (le_max_left _ _).trans hn
  have hnM : M≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn1 : 1≤n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  refine ⟨n,hnR,?_⟩
  calc
    (((QuotientGroup.mk' H) '' displacement Γ o 1)^n).ncard ≤
        (reachBall Γ o n).ncard*M := hncard n hn1
    _ ≤ n^d*M := Nat.mul_le_mul_right M hp
    _ ≤ n^d*n := Nat.mul_le_mul_left _ hnM
    _ = n^(d+1) := (pow_succ n d).symm

end GraphTopology
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_NormalClosureGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter Topology
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma eventually_exponential_dominates (C k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, C*n^k < 2^n := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k
    (by norm_num : (1:ℝ)<2)).const_mul (C:ℝ)
  have he : ∀ᶠ n : ℕ in atTop, (C:ℝ)*((n:ℝ)^k / 2^n) < 1 :=
    ht.eventually (Iio_mem_nhds (by simp : (C:ℝ)*0 < 1))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun n hn => ?_⟩
  have hx := hN n hn
  rw [← mul_div_assoc] at hx
  have hx' := (div_lt_one (pow_pos (by norm_num : (0:ℝ)<2) n)).mp hx
  exact_mod_cast hx'

lemma binaryProducts_mem (K : ℕ → Subgroup A) (hK : Monotone K)
    (g : ℕ → A) (hg : ∀ n, g n∈K (n+1)) :
    ∀ n, ∀ x ∈ binaryProducts g n, x∈K n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    have he : x=1 := by simpa [binaryProducts] using hx
    exact he ▸ (K 0).one_mem
  | succ n ih =>
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hK (Nat.le_succ n) (ih x hx)
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (K (n+1)).mul_mem (hg n) (hK (Nat.le_succ n) (ih y hy))

lemma binaryProducts_card (K : ℕ → Subgroup A) (hK : Monotone K)
    (g : ℕ → A) (hg : ∀ n, g n∈K (n+1)) (hout : ∀ n, g n∉K n) :
    ∀ n, (binaryProducts g n).card=2^n := by
  intro n
  induction n with
  | zero => simp [binaryProducts]
  | succ n ih =>
    have hd : Disjoint (binaryProducts g n)
        ((binaryProducts g n).image (fun x => g n*x)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hy
      have hxK := binaryProducts_mem K hK g hg n x hx
      have hyK := binaryProducts_mem K hK g hg n y hy
      apply hout n
      rw [←he] at hxK
      simpa only [mul_assoc,mul_inv_cancel,mul_one] using
        (K n).mul_mem hxK ((K n).inv_mem hyK)
    rw [binaryProducts,Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (mul_right_injective (g n)),ih,pow_succ]
    omega

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetSparseGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Filter Topology
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma ball_mono (K : Subgroup A) (S : Set A) (h1 : (1:A)∈S) :
    Monotone (ball K S) := fun _ _ h => Set.image_mono (Set.pow_subset_pow_right h1 h)

lemma not_quadratic_exponential_lower (K : Subgroup A) (S : Set A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree K S d) (L : ℕ) (hL : 0<L)
    (hlo : ∀ n : ℕ, 2^n ≤ (ball K S (L*n^2)).ncard) : False := by
  obtain ⟨hfin,C,hC⟩ := hg
  obtain ⟨N,hN⟩ := SparseGrowth.eventually_exponential_dominates (C*(4*L)^d) (2*d)
  obtain ⟨r,hr,hbound⟩ := hC (L*(max N 1)^2)
  let n := Nat.sqrt (r/L)
  have hn : max N 1 ≤ n := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le hL).mpr (by
    simpa only [Nat.mul_comm] using hr))
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnr : L*n^2 ≤ r := by
    calc
      _ ≤ L*(r/L) := Nat.mul_le_mul_left L (Nat.sqrt_le' (r/L))
      _ ≤ r := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self r L
  have hrn : r ≤ (4*L)*n^2 := by
    have ht := Nat.lt_mul_div_succ r hL
    have hs : r/L+1 ≤ (n+1)^2 := Nat.succ_le_of_lt (Nat.lt_succ_sqrt' (r/L))
    have hs' : (n+1)^2 ≤ 4*n^2 := by nlinarith
    have hj := (Nat.mul_le_mul_left L hs).trans (Nat.mul_le_mul_left L hs')
    nlinarith
  have hu : 2^n ≤ (C*(4*L)^d)*n^(2*d) := by
    calc
      _ ≤ (ball K S (L*n^2)).ncard := hlo n
      _ ≤ (ball K S r).ncard := Set.ncard_le_ncard (ball_mono K S h1 hnr) (hfin r)
      _ ≤ C*r^d := hbound
      _ ≤ C*((4*L)*n^2)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
      _ = (C*(4*L)^d)*n^(2*d) := by rw [mul_pow,pow_mul]; ring
  exact (not_le_of_gt (hN n ((le_max_left N 1).trans hn))) hu

lemma binaryProducts_coset_inj (K : Subgroup A) (H : ℕ → Subgroup A) (hH : Monotone H)
    (hK : K≤H 0) (g : ℕ → A) (hg : ∀ n, g n∈H (n+1)) (hout : ∀ n, g n∉H n) :
    ∀ n, Set.InjOn (QuotientGroup.mk : A → A ⧸ K) (SparseGrowth.binaryProducts g n : Set A) := by
  intro n
  induction n with
  | zero => simp [SparseGrowth.binaryProducts,Set.InjOn]
  | succ n ih =>
    intro x hx y hy he
    have hKn : K≤H n := hK.trans (hH (Nat.zero_le n))
    have hmem := SparseGrowth.binaryProducts_mem H hH g hg n
    have hbad (x y : A) (hx : x∈SparseGrowth.binaryProducts g n)
        (hy : y∈SparseGrowth.binaryProducts g n)
        (he : (QuotientGroup.mk x : A ⧸ K)=QuotientGroup.mk (g n*y)) : False := by
      have hxy : x⁻¹*(g n*y)∈H n := hKn (QuotientGroup.eq.mp he)
      have hz := (H n).mul_mem ((H n).mul_mem (hmem x hx) hxy) ((H n).inv_mem (hmem y hy))
      apply hout n
      simpa only [mul_inv_cancel_left,mul_assoc,mul_inv_cancel,mul_one] using hz
    rcases Finset.mem_union.mp hx with hx|hx <;> rcases Finset.mem_union.mp hy with hy|hy
    · exact ih hx hy he
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
      exact False.elim (hbad x z hx hz he)
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      exact False.elim (hbad y z hy hz he.symm)
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      apply congrArg (fun t => g n*t)
      apply ih ha hb
      apply QuotientGroup.eq.mpr
      have hh := QuotientGroup.eq.mp he
      simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel_left] using hh

lemma binaryProducts_subset_pow (S : Set A) (h1 : (1:A)∈S)
    (g : ℕ → A) (L : ℕ) (hg : ∀ n, g n∈S^(L*(n+1))) :
    ∀ n, (SparseGrowth.binaryProducts g n : Set A) ⊆ S^(L*n^2) := by
  intro n
  induction n with
  | zero => simp [SparseGrowth.binaryProducts]
  | succ n ih =>
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Set.pow_subset_pow_right h1 (Nat.mul_le_mul_left L (Nat.pow_le_pow_left (Nat.le_succ n) 2)) (ih hx)
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      have hlen : L*(n+1)+L*n^2 ≤ L*(n+1)^2 := by
        calc
          _ = L*(n+1+n^2) := by ring
          _ ≤ L*(n+1)^2 := Nat.mul_le_mul_left L (by nlinarith)
      apply Set.pow_subset_pow_right h1 hlen
      rw [pow_add]
      exact Set.mul_mem_mul (hg n) (ih hy)

lemma no_linear_strict_chain (K : Subgroup A) (S : Set A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree K S d) (H : ℕ → Subgroup A) (hH : Monotone H) (hK : K≤H 0)
    (g : ℕ → A) (hgin : ∀ n, g n∈H (n+1)) (hgout : ∀ n, g n∉H n)
    (L : ℕ) (hL : 0<L) (hword : ∀ n, g n∈S^(L*(n+1))) : False := by
  apply not_quadratic_exponential_lower K S h1 d hg L hL
  intro n
  have hin := binaryProducts_coset_inj K H hH hK g hgin hgout n
  rw [←SparseGrowth.binaryProducts_card H hH g hgin hgout n]
  have heq := hin.ncard_image
  rw [Set.ncard_coe_finset] at heq
  rw [←heq]
  exact Set.ncard_le_ncard (Set.image_mono (binaryProducts_subset_pow S h1 g L hword n)) (hg.1 _)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetBounded
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma bounded_singleton (S : Set A) (h1 : (1:A)∈S) (hi : S⁻¹=S)
    (hg : Subgroup.closure S=⊤) (a : A) : Bounded S {a} := by
  have ha : a∈Subgroup.closure S := hg.symm ▸ Subgroup.mem_top a
  suffices ∃ n, a∈S^n by simpa [Bounded] using this
  induction ha using Subgroup.closure_induction with
  | mem a ha => exact ⟨1,by simpa using ha⟩
  | one => exact ⟨1,by simpa using h1⟩
  | mul a b _ _ ha hb =>
    obtain ⟨n,hn⟩ := ha; obtain ⟨m,hm⟩ := hb
    exact ⟨n+m,by rw [pow_add]; exact Set.mul_mem_mul hn hm⟩
  | inv a _ ha =>
    obtain ⟨n,hn⟩ := ha
    refine ⟨n,?_⟩
    rw [←hi,inv_pow]
    exact Set.inv_mem_inv.mpr hn
lemma bounded_finite (S : Set A) (h1 : (1:A)∈S) (hi : S⁻¹=S)
    (hg : Subgroup.closure S=⊤) {F : Set A} (hf : F.Finite) : Bounded S F := by
  have hh : ∀ f∈F, ∃ n, f∈S^n := by
    intro f hf
    obtain ⟨n,hn⟩ := bounded_singleton S h1 hi hg f
    exact ⟨n,hn (Set.mem_singleton _)⟩
  choose n hn using hh
  let L := hf.toFinset.sup (fun a => if ha : a∈F then n a ha else 0)
  refine ⟨L,?_⟩
  intro a ha
  apply Set.pow_subset_pow_right h1 (show n a ha≤L from ?_) (hn a ha)
  have hh := Finset.le_sup (f:=fun a => if ha : a∈F then n a ha else 0) (hf.mem_toFinset.mpr ha)
  simpa only [dite_eq_left ha] using hh
lemma Bounded.mono {S T U : Set A} (h : Bounded S T) (hUT : U⊆T) : Bounded S U :=
  ⟨h.choose,hUT.trans h.choose_spec⟩
lemma Bounded.mul {S T U : Set A} (hT : Bounded S T) (hU : Bounded S U) : Bounded S (T*U) := by
  obtain ⟨n,hn⟩ := hT; obtain ⟨m,hm⟩ := hU
  exact ⟨n+m,by rw [pow_add]; exact Set.mul_subset_mul hn hm⟩
lemma Bounded.inv {S T : Set A} (hi : S⁻¹=S) (hT : Bounded S T) : Bounded S T⁻¹ := by
  obtain ⟨n,hn⟩ := hT
  refine ⟨n,?_⟩
  rw [←hi,inv_pow]
  exact Set.inv_subset_inv.mpr hn
lemma Bounded.union {S T U : Set A} (h1 : (1:A)∈S)
    (hT : Bounded S T) (hU : Bounded S U) : Bounded S (T∪U) := by
  obtain ⟨n,hn⟩ := hT; obtain ⟨m,hm⟩ := hU
  exact ⟨max n m,Set.union_subset (hn.trans (Set.pow_subset_pow_right h1 (le_max_left _ _)))
    (hm.trans (Set.pow_subset_pow_right h1 (le_max_right _ _)))⟩

lemma finite_coset_image_iff_cover (K : Subgroup A) (T : Set A) :
    ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite ↔
      ∃ F : Set A, F.Finite ∧ T⊆F*(K:Set A) := by
  constructor
  · intro hf
    let Q := (QuotientGroup.mk : A → A ⧸ K) '' T
    have hh : ∀ q∈Q, ∃ a∈T, (QuotientGroup.mk a : A ⧸ K)=q := fun q hq => hq
    choose a ha he using hh
    let F := Set.range (fun q : Q => a q.val q.property)
    let : Finite Q := hf.to_subtype
    refine ⟨F,Set.finite_range _,?_⟩
    intro t ht
    let q : Q := ⟨QuotientGroup.mk t,⟨t,ht,rfl⟩⟩
    refine ⟨a q.val q.property,⟨q,rfl⟩,(a q.val q.property)⁻¹*t,?_,by simp⟩
    exact QuotientGroup.eq.mp (he q.val q.property)
  · rintro ⟨F,hF,hcov⟩
    apply (hF.image (QuotientGroup.mk : A → A ⧸ K)).subset
    rintro _ ⟨t,ht,rfl⟩
    obtain ⟨f,hf,k,hk,rfl⟩ := hcov ht
    exact ⟨f,hf,QuotientGroup.eq.mpr (by simpa using hk)⟩

lemma bounded_of_finite_coset_image (S : Set A) (K : Subgroup A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hg : Subgroup.closure S=⊤) (hK : Bounded S (K:Set A))
    (T : Set A) (hf : ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite) : Bounded S T := by
  obtain ⟨F,hF,hcov⟩ := (finite_coset_image_iff_cover K T).mp hf
  exact ((bounded_finite S h1 hi hg hF).mul hK).mono hcov
lemma finite_coset_image_of_bounded (K : Subgroup A) (S T : Set A)
    (hf : ∀ n, (ball K S n).Finite) (hT : Bounded S T) :
    ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite := by
  obtain ⟨n,hn⟩ := hT
  exact (hf n).subset (Set.image_mono hn)

lemma HasDegree.bounded_generators {K : Subgroup A} {S T : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hg : HasDegree K S d) (hT : Bounded S T) : HasDegree K T d := by
  obtain ⟨L,hL⟩ := hT
  have hin (n : ℕ) : T^n⊆S^((L+1)*n) := by
    rw [pow_mul]
    exact Set.pow_subset_pow_left (hL.trans (Set.pow_subset_pow_right h1 (Nat.le_succ L)))
  refine ⟨fun n => (hg.1 _).subset (Set.image_mono (hin n)),?_⟩
  obtain ⟨C,hC⟩ := hg.2
  refine ⟨C*(2*(L+1))^d,?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hn : max R 1≤n := (Nat.le_div_iff_mul_le (by omega : 0<L+1)).mpr (by simpa [Nat.mul_comm] using hr)
  have hnr : (L+1)*n ≤ r := by simpa only [n,Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hrn : r≤(2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r (by omega : 0<L+1)
    change r<(L+1)*(n+1) at hlt
    have hh : 1≤n := (le_max_right R 1).trans hn
    nlinarith
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  calc
    _ ≤ (ball K S r).ncard := Set.ncard_le_ncard
      (Set.image_mono ((hin n).trans (Set.pow_subset_pow_right h1 hnr))) (hg.1 r)
    _ ≤ C*r^d := hbound
    _ ≤ C*((2*(L+1))*n)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
    _ = _ := by rw [mul_pow]; ring

lemma HasDegree.zero_finiteIndex {K : Subgroup A} {S : Set A}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hg : HasDegree K S 0) : K.FiniteIndex := by
  obtain ⟨C,hC⟩ := hg.2
  obtain ⟨n,hn,hb⟩ := hC C
  apply CosetGrowth.finiteIndex_of_small_ball S K h1 hi hgen n (hg.1 n)
  exact (by simpa using hb : (ball K S n).ncard≤C).trans hn

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetNormalClosure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma mem_boundedConjugates (S F : Set A) (n : ℕ) {x : A} :
    x∈boundedConjugates S F n ↔ ∃ g∈S^n, ∃ f∈F, g*f*g⁻¹=x := by
  rfl

lemma boundedConjugates_mono (S F : Set A) (h1 : (1:A)∈S) :
    Monotone (boundedConjugates S F) := by
  intro m n h x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F m).mp hx
  exact (mem_boundedConjugates S F n).mpr
    ⟨g,Set.pow_subset_pow_right h1 h hg,f,hf,rfl⟩

lemma conjugateStage_mono (S F : Set A) (h1 : (1:A)∈S) :
    Monotone (conjugateStage S F) := by
  intro m n h
  exact Subgroup.closure_mono (boundedConjugates_mono S F h1 h)

lemma boundedConjugates_subset_pow (S F : Set A) (hsym : S⁻¹=S)
    (L : ℕ) (hF : F⊆S^L) (n : ℕ) :
    boundedConjugates S F n ⊆ S^(2*n+L) := by
  intro x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hx
  have hgi : g⁻¹∈S^n := by
    rw [←hsym,inv_pow]
    exact Set.inv_mem_inv.mpr hg
  have he : 2*n+L=n+L+n := by omega
  rw [he,pow_add,pow_add]
  exact Set.mul_mem_mul (Set.mul_mem_mul hg (hF hf)) hgi

lemma conjugateStage_le_normalClosure (S F : Set A) (n : ℕ) :
    conjugateStage S F n ≤ Subgroup.normalClosure (F : Set A) := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hx
  exact Subgroup.normalClosure_normal.conj_mem f (Subgroup.subset_normalClosure hf) g

lemma conjugateStage_conj_generator (S F : Set A) (n : ℕ)
    (s : A) (hs : s∈S) {x : A} (hx : x∈conjugateStage S F n) :
    s*x*s⁻¹∈conjugateStage S F (n+1) := by
  change x∈Subgroup.closure _ at hx
  have hmap : conjugateStage S F n ≤
      (conjugateStage S F (n+1)).comap (MulAut.conj s) := by
    apply (Subgroup.closure_le _).mpr
    intro y hy
    obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hy
    apply Subgroup.subset_closure
    apply (mem_boundedConjugates S F (n+1)).mpr
    refine ⟨s*g,?_,f,hf,?_⟩
    · rw [pow_succ']
      exact Set.mul_mem_mul hs hg
    · simp [MulAut.conj_apply,mul_assoc]
  exact hmap hx

lemma conjugateStage_normal_of_stationary (S F : Set A) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure (S : Set A)=⊤) (n : ℕ)
    (he : conjugateStage S F (n+1)=conjugateStage S F n) :
    (conjugateStage S F n).Normal := by
  rw [←Subgroup.normalizer_eq_top_iff]
  apply top_unique
  rw [←hgen]
  apply (Subgroup.closure_le _).mpr
  intro s hs
  change ∀ x, x∈conjugateStage S F n ↔ s*x*s⁻¹∈conjugateStage S F n
  intro x
  constructor
  · intro hx
    rw [←he]
    exact conjugateStage_conj_generator S F n s hs hx
  · intro hx
    have hsi : s⁻¹∈S := by rw [←hsym]; exact Set.inv_mem_inv.mpr hs
    have hy := conjugateStage_conj_generator S F n s⁻¹ hsi hx
    rw [he] at hy
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hy

lemma normalClosure_eq_conjugateStage_of_stationary (S F : Set A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (hgen : Subgroup.closure (S : Set A)=⊤)
    (n : ℕ) (he : conjugateStage S F (n+1)=conjugateStage S F n) :
    Subgroup.normalClosure (F : Set A)=conjugateStage S F n := by
  let _ := conjugateStage_normal_of_stationary S F hsym hgen n he
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro f hf
    apply Subgroup.subset_closure
    exact (mem_boundedConjugates S F n).mpr
      ⟨1,Set.one_mem_pow h1,f,hf,by simp⟩
  · exact conjugateStage_le_normalClosure S F n

theorem exists_conjugateStage_stationary (S F : Set A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (K : Subgroup A) (hK : K≤Subgroup.closure F) (d : ℕ) (hg : HasDegree K S d)
    (L : ℕ) (hF : F⊆S^L) :
    ∃ n : ℕ, conjugateStage S F (n+1)=conjugateStage S F n := by
  by_contra! hn
  have hw : ∀ n : ℕ, ∃ x∈boundedConjugates S F (n+1), x∉conjugateStage S F n := by
    intro n
    by_contra! h
    apply hn n
    apply le_antisymm ((Subgroup.closure_le _).mpr h)
    exact conjugateStage_mono S F h1 (Nat.le_succ n)
  choose g hgin hgout using hw
  have hbase : K ≤ conjugateStage S F 0 := hK.trans (Subgroup.closure_mono (by
    intro f hf
    exact ⟨1,by simp,f,hf,by simp⟩))
  apply no_linear_strict_chain K S h1 d hg (conjugateStage S F)
    (conjugateStage_mono S F h1) hbase g (fun n => Subgroup.subset_closure (hgin n))
    hgout (L+2) (by omega)
  intro n
  apply Set.pow_subset_pow_right h1 (show 2*(n+1)+L≤(L+2)*(n+1) by nlinarith)
  exact boundedConjugates_subset_pow S F hsym L hF (n+1) (hgin n)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BoundedNormalJoins
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma conjugate_map_map (N : Subgroup A) (a b : A) :
    (N.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom=N.map (MulAut.conj (a*b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

lemma Bounded.conj {S : Set A} (h1 : (1:A)∈S) (hi : S⁻¹=S)
    (hg : Subgroup.closure S=⊤) {N : Subgroup A} (hN : Bounded S (N:Set A)) (g : A) :
    Bounded S (N.map (MulAut.conj g).toMonoidHom : Set A) := by
  have hh := ((bounded_singleton S h1 hi hg g).mul hN).mul (bounded_singleton S h1 hi hg g⁻¹)
  apply hh.mono
  rintro y ⟨x,hx,rfl⟩
  exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mem_singleton g) hx) (Set.mem_singleton g⁻¹)

lemma normalized_conjugate (L N : Subgroup A) [L.Normal] (hN : L≤(Subgroup.normalizer (N:Set A))) (g : A) :
    L≤(Subgroup.normalizer ((N.map (MulAut.conj g).toMonoidHom):Set A)) := by
  have hh := (Subgroup.map_mono hN (f:=(MulAut.conj g).toMonoidHom)).trans (N.le_normalizer_map (MulAut.conj g).toMonoidHom)
  have he : L.map (MulAut.conj g).toMonoidHom=L := Subgroup.Normal.map_conj_eq L g
  rwa [he] at hh

lemma finite_normalized_join_bounded (S : Set A) (h1 : (1:A)∈S)
    (L : Subgroup A) (F : Set (Subgroup A)) (hf : F.Finite)
    (hle : ∀ N∈F, N≤L) (hnorm : ∀ N∈F, L≤(Subgroup.normalizer (N:Set A)))
    (hb : ∀ N∈F, Bounded S (N:Set A)) :
    Bounded S ((⨆ N∈F, N : Subgroup A) : Set A) := by
  induction F, hf using Set.Finite.induction_on with
  | empty => exact ⟨1,by simpa using h1⟩
  | @insert N F hN hF ih =>
    have hbF := ih (fun M hM => hle M (Set.mem_insert_of_mem _ hM))
      (fun M hM => hnorm M (Set.mem_insert_of_mem _ hM))
      (fun M hM => hb M (Set.mem_insert_of_mem _ hM))
    have hleF : (⨆ M∈F, M : Subgroup A)≤L := iSup_le (fun M => iSup_le (fun hM => hle M (Set.mem_insert_of_mem _ hM)))
    have hn : (⨆ M∈F, M : Subgroup A)≤(Subgroup.normalizer (N:Set A)) := hleF.trans (hnorm N (Set.mem_insert N F))
    rw [iSup_insert,Subgroup.coe_mul_of_right_le_normalizer_left N _ hn]
    exact (hb N (Set.mem_insert N F)).mul hbF

lemma conjugateStage_eq_join (S : Set A) (N : Subgroup A) (n : ℕ) :
    conjugateStage S (N:Set A) n=⨆ M∈((fun g => N.map (MulAut.conj g).toMonoidHom) '' S^n), M := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨g,hg,y,hy,rfl⟩
    have hh : N.map (MulAut.conj g).toMonoidHom ≤ ⨆ M∈((fun g => N.map (MulAut.conj g).toMonoidHom) '' S^n), M :=
      le_iSup_of_le _ (le_iSup_of_le ⟨g,hg,rfl⟩ le_rfl)
    exact hh (Subgroup.mem_map.mpr ⟨y,hy,rfl⟩)
  · apply iSup_le
    intro M
    apply iSup_le
    rintro ⟨g,hg,rfl⟩ x ⟨y,hy,rfl⟩
    exact Subgroup.subset_closure ⟨g,hg,y,hy,rfl⟩

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetTransfer
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma subgroupCosetEmbedding_range (K H : Subgroup A) :
    Set.range (subgroupCosetEmbedding K H)=(QuotientGroup.mk : A → A ⧸ K) '' (H:Set A) := by
  ext q
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨h,rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨h,h.property,rfl⟩
  · rintro ⟨h,hh,rfl⟩
    exact ⟨QuotientGroup.mk (⟨h,hh⟩ : H),rfl⟩
lemma finite_coset_image_subgroup_iff (K H : Subgroup A) :
    ((QuotientGroup.mk : A → A ⧸ K) '' (H:Set A)).Finite ↔ K.relIndex H≠0 := by
  rw [←subgroupCosetEmbedding_range]
  rw [Set.finite_range_iff (subgroupCosetEmbedding K H).injective]
  change Finite (H ⧸ K.subgroupOf H) ↔ Nat.card (H ⧸ K.subgroupOf H)≠0
  exact ⟨fun h => by let := h; exact Nat.card_pos.ne',
    fun h => (Nat.finite_of_card_ne_zero h)⟩

lemma bounded_subgroup_iff (K H : Subgroup A) (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (hf : ∀ n, (ball K S n).Finite) :
    Bounded S (H:Set A) ↔ K.relIndex H≠0 := by
  rw [←finite_coset_image_subgroup_iff]
  exact ⟨finite_coset_image_of_bounded K S (H:Set A) hf,
    bounded_of_finite_coset_image S K h1 hi hgen hK (H:Set A)⟩

lemma subgroup_ball_image (K H : Subgroup A) (T : Set H) (n : ℕ) :
    (subgroupCosetEmbedding K H) '' ball (K.subgroupOf H) T n=
      ball K (H.subtype '' T) n := by
  rw [ball,Set.image_image,ball,←Set.image_pow]
  rw [Set.image_image]
  rfl
lemma HasDegree.subgroup_bounded {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hg : HasDegree K S d) (H : Subgroup A) (T : Set H)
    (hT : Bounded S (H.subtype '' T)) : HasDegree (K.subgroupOf H) T d := by
  have ht := hg.bounded_generators h1 hT
  have hf (n : ℕ) : (ball (K.subgroupOf H) T n).Finite := by
    apply Set.Finite.of_finite_image (f:=subgroupCosetEmbedding K H)
    rw [subgroup_ball_image]
    exact ht.1 n
    exact (subgroupCosetEmbedding K H).injective.injOn
  refine ⟨hf,?_⟩
  obtain ⟨C,hC⟩ := ht.2
  refine ⟨C,?_⟩
  intro R
  obtain ⟨n,hn,hb⟩ := hC R
  refine ⟨n,hn,?_⟩
  rw [←subgroup_ball_image,Set.ncard_image_of_injective _ (subgroupCosetEmbedding K H).injective] at hb
  exact hb

lemma finite_image_of_finite_coset_image {B : Type*} [Group B]
    (K : Subgroup A) (f : A →* B) (hK : (f '' (K:Set A)).Finite)
    (T : Set A) (hT : ((QuotientGroup.mk : A → A ⧸ K) '' T).Finite) :
    (f '' T).Finite := by
  obtain ⟨F,hF,hcov⟩ := (finite_coset_image_iff_cover K T).mp hT
  apply ((hF.image f).mul hK).subset
  rintro _ ⟨t,ht,rfl⟩
  obtain ⟨a,ha,k,hk,rfl⟩ := hcov ht
  rw [map_mul]
  exact Set.mul_mem_mul ⟨a,ha,rfl⟩ ⟨k,hk,rfl⟩

lemma finiteIndex_bounded_generators (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (H : Subgroup A) [H.FiniteIndex] :
    ∃ T : Set H, (1:H)∈T ∧ T⁻¹=T ∧ Subgroup.closure T=⊤ ∧ Bounded S (H.subtype '' T) := by
  let := H.fintypeQuotientOfFiniteIndex
  obtain ⟨R,hR,hR1⟩ := H.exists_isComplement_right 1
  have hRf : R.Finite := by
    let : Fintype R := Fintype.ofEquiv _ hR.rightQuotientEquiv
    exact Set.toFinite R
  let U : Set H := (R*S).image (fun g => ⟨g*(hR.toRightFun g:A)⁻¹,hR.mul_inv_toRightFun_mem g⟩)
  have hUgen : Subgroup.closure U=⊤ := Subgroup.closure_mul_image_eq_top hR hR1 hgen
  have hUb : Bounded S (H.subtype '' U) := by
    have hRb := bounded_finite S h1 hi hgen hRf
    have hSb : Bounded S S := ⟨1,by simp⟩
    exact ((hRb.mul hSb).mul (hRb.inv hi)).mono (by
      rintro _ ⟨_,⟨g,hg,rfl⟩,rfl⟩
      exact Set.mul_mem_mul hg (Set.inv_mem_inv.mpr (hR.toRightFun g).property))
  let T := {1}∪(U∪U⁻¹)
  refine ⟨T,by simp [T],?_,?_,?_⟩
  · simp [T,Set.union_inv,Set.union_comm]
  · apply top_unique
    rw [←hUgen]
    exact Subgroup.closure_mono (by intro u hu; exact Or.inr (Or.inl hu))
  · have he : H.subtype '' T={1}∪((H.subtype '' U)∪(H.subtype '' U)⁻¹) := by
      simp only [T,Set.image_union,Set.image_singleton,map_one,Set.image_inv]
    rw [he]
    exact (bounded_singleton S h1 hi hgen 1).union h1 (hUb.union h1 (hUb.inv hi))

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetFiniteCore
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma conjugate_map_one (N : Subgroup A) : N.map (MulAut.conj (1:A)).toMonoidHom=N :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.normalizer (N:Set A)).one_mem
lemma conjugate_eq_of_normalizer (N : Subgroup A) (g r : A) (h : r⁻¹*g∈(Subgroup.normalizer (N:Set A))) :
    N.map (MulAut.conj g).toMonoidHom=N.map (MulAut.conj r).toMonoidHom := by
  have he : N.map (MulAut.conj (r⁻¹*g)).toMonoidHom=N := Subgroup.mem_normalizer_iff_map_conj_eq.mp h
  have hh := congrArg (fun P : Subgroup A => P.map (MulAut.conj r).toMonoidHom) he
  rw [conjugate_map_map,mul_inv_cancel_left] at hh
  exact hh

lemma conjugate_stabilizer_relIndex (K : Subgroup A) (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (hf : ∀ n, (ball K S n).Finite) (g : A) :
    (K.map (MulAut.conj g).toMonoidHom).relIndex K≠0 := by
  have hk := (bounded_subgroup_iff K (K.map (MulAut.conj g⁻¹).toMonoidHom) S h1 hi hgen hK hf).mp (hK.conj h1 hi hgen g⁻¹)
  have he := Subgroup.relIndex_map_map_of_injective K (K.map (MulAut.conj g⁻¹).toMonoidHom) (f:=(MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [conjugate_map_map,mul_inv_cancel,conjugate_map_one] at he
  rwa [he]

lemma conjugate_commensurable_index (K N : Subgroup A) (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (hf : ∀ n, (ball K S n).Finite)
    (hN : N.relIndex K≠0) (g : A) :
    (N.map (MulAut.conj g).toMonoidHom).relIndex K≠0 := by
  apply Subgroup.relIndex_ne_zero_trans (K:=K.map (MulAut.conj g).toMonoidHom)
  · rwa [Subgroup.relIndex_map_map_of_injective N K (MulAut.conj g).injective]
  · exact conjugate_stabilizer_relIndex K S h1 hi hgen hK hf g

lemma finite_conjugate_family_of_finiteIndex_normalizer (H N : Subgroup A)
    [H.FiniteIndex] (hHN : H≤(Subgroup.normalizer (N:Set A))) :
    (Set.range (fun g : A => N.map (MulAut.conj g).toMonoidHom)).Finite := by
  let := H.fintypeQuotientOfFiniteIndex
  obtain ⟨R,hR,hR1⟩ := H.exists_isComplement_left 1
  have hRf : R.Finite := by
    let : Fintype R := Fintype.ofEquiv _ hR.leftQuotientEquiv
    exact Set.toFinite R
  apply (hRf.image (fun g => N.map (MulAut.conj g).toMonoidHom)).subset
  rintro _ ⟨g,rfl⟩
  refine ⟨hR.toLeftFun g,(hR.toLeftFun g).property,?_⟩
  exact (conjugate_eq_of_normalizer N g (hR.toLeftFun g) (hHN (hR.inv_toLeftFun_mul_mem g))).symm

lemma HasDegree.finiteIndex_normal_core {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (hg : HasDegree K S d)
    (H N : Subgroup A) [H.FiniteIndex] (hHN : H≤(Subgroup.normalizer (N:Set A)))
    (hNb : Bounded S (N:Set A)) (hNi : N.relIndex K≠0) :
    ∃ M : Subgroup A, M.Normal ∧ Bounded S (M:Set A) ∧ M.relIndex K≠0 := by
  refine ⟨N.normalCore,inferInstance,hNb.mono N.normalCore_le,?_⟩
  let F := Set.range (fun g : A => N.map (MulAut.conj g).toMonoidHom)
  let : Finite F := (finite_conjugate_family_of_finiteIndex_normalizer H N hHN).to_subtype
  have he : N.normalCore=⨅ P : F, P.val := by
    rw [Subgroup.normalCore_eq_iInf_map_conj]
    apply le_antisymm
    · apply le_iInf
      rintro ⟨P,⟨g,rfl⟩⟩
      exact iInf_le _ g
    · apply le_iInf
      intro g
      exact iInf_le (fun P : F => P.val) (⟨N.map (MulAut.conj g).toMonoidHom,⟨g,rfl⟩⟩ : F)
  rw [he]
  apply Subgroup.relIndex_iInf_ne_zero
  rintro ⟨P,⟨g,rfl⟩⟩
  exact conjugate_commensurable_index K N S h1 hi hgen hK hg.1 hNi g

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetIntegerKernel
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma integer_kernel_normalClosure (S : Set A)
    (hgen : Subgroup.closure S=⊤)
    (f : A →* Multiplicative ℤ) (a : A) (ha : f a=Multiplicative.ofAdd 1) :
    f.ker=Subgroup.normalClosure ((fun s => s*a^(-Multiplicative.toAdd (f s))) '' S) := by
  let F := (fun s => s*a^(-Multiplicative.toAdd (f s))) '' S
  let N := Subgroup.normalClosure F
  have hN : N≤f.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro y ⟨s,hs,rfl⟩
    change f (s*a^(-Multiplicative.toAdd (f s)))=1
    rw [map_mul,map_zpow,ha]
    apply Multiplicative.toAdd.injective
    simp
  let q := QuotientGroup.mk' N
  have hqa : ∀ x : A, q x=(q a)^Multiplicative.toAdd (f x) := by
    intro x
    have hx : x∈Subgroup.closure S := hgen.symm ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      have hm : x*a^(-Multiplicative.toAdd (f x))∈N := Subgroup.subset_normalClosure ⟨x,hx,rfl⟩
      have he := (QuotientGroup.eq_one_iff _).mpr hm
      change q (x*a^(-Multiplicative.toAdd (f x)))=1 at he
      rw [map_mul,map_zpow,zpow_neg] at he
      exact mul_inv_eq_one.mp he
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul,hx,hy,←zpow_add,map_mul,toAdd_mul]
    | inv x _ hx => rw [map_inv,hx,map_inv,toAdd_inv,zpow_neg]
  apply le_antisymm _ hN
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mp
  change q x=1
  rw [hqa,MonoidHom.mem_ker.mp hx]
  simp

lemma HasDegree.integer_kernel_bounded_generators {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤) (hg : HasDegree K S d)
    (hKS : (K:Set A)⊆S) (f : A →* Multiplicative ℤ) (hf : Surjective f) (hKf : K≤f.ker) :
    ∃ T : Set f.ker, (1:f.ker)∈T ∧ T⁻¹=T ∧ Subgroup.closure T=⊤ ∧
      Bounded S (f.ker.subtype '' T) ∧ (K.subgroupOf f.ker : Set f.ker)⊆T := by
  obtain ⟨a,ha⟩ := hf (Multiplicative.ofAdd 1)
  let F := (fun s => s*a^(-Multiplicative.toAdd (f s))) '' S
  have hFker : F⊆f.ker := by
    rintro y ⟨s,hs,rfl⟩
    change f (s*a^(-Multiplicative.toAdd (f s)))=1
    rw [map_mul,map_zpow,ha]
    apply Multiplicative.toAdd.injective
    simp
  have hKF : (K:Set A)⊆F := by
    intro k hk
    refine ⟨k,hKS hk,?_⟩
    dsimp only
    rw [MonoidHom.mem_ker.mp (hKf hk)]
    simp
  have hfi : (f '' (K:Set A)).Finite := by
    apply (Set.finite_singleton (1:Multiplicative ℤ)).subset
    rintro _ ⟨k,hk,rfl⟩
    exact MonoidHom.mem_ker.mp (hKf hk)
  have hfs : (f '' S).Finite := finite_image_of_finite_coset_image K f hfi S (by simpa only [ball,pow_one] using hg.1 1)
  have hFb : Bounded S F := by
    have hp := bounded_finite S h1 hi hgen (hfs.image (fun z => a^(-Multiplicative.toAdd z)))
    exact (Bounded.mul (show Bounded S S from ⟨1,by simp⟩) hp).mono (by
      rintro y ⟨s,hs,rfl⟩
      exact Set.mul_mem_mul hs ⟨f s,⟨s,hs,rfl⟩,rfl⟩)
  obtain ⟨L,hL⟩ := hFb
  obtain ⟨n,hn⟩ := exists_conjugateStage_stationary S F h1 hi K
    (fun k hk => Subgroup.subset_closure (hKF hk)) d hg L hL
  have hncl : f.ker=conjugateStage S F n :=
    (integer_kernel_normalClosure S hgen f a ha).trans (normalClosure_eq_conjugateStage_of_stationary S F h1 hi hgen n hn)
  let U := boundedConjugates S F n
  have hUk : U⊆f.ker := by
    intro u hu
    rw [hncl]
    exact Subgroup.subset_closure hu
  let T0 : Set f.ker := f.ker.subtype ⁻¹' U
  have hT0image : f.ker.subtype '' T0=U := by
    ext u
    exact ⟨fun ⟨x,hx,he⟩ => he ▸ hx,fun hu => ⟨⟨u,hUk hu⟩,hu,rfl⟩⟩
  have hT0gen : Subgroup.closure T0=⊤ := by
    apply Subgroup.map_injective f.ker.subtype_injective
    rw [MonoidHom.map_closure,hT0image,←MonoidHom.range_eq_map,Subgroup.range_subtype]
    exact hncl.symm
  have hT0b : Bounded S (f.ker.subtype '' T0) := by
    rw [hT0image]
    exact ⟨2*n+L,boundedConjugates_subset_pow S F hi L hL n⟩
  let T := {1}∪(T0∪T0⁻¹)
  refine ⟨T,by simp [T],?_,?_,?_,?_⟩
  · simp [T,Set.union_inv,Set.union_comm]
  · apply top_unique
    rw [←hT0gen]
    exact Subgroup.closure_mono (fun t ht => Or.inr (Or.inl ht))
  · have he : f.ker.subtype '' T={1}∪((f.ker.subtype '' T0)∪(f.ker.subtype '' T0)⁻¹) := by
      simp only [T,Set.image_union,Set.image_singleton,map_one,Set.image_inv]
    rw [he]
    exact (bounded_singleton S h1 hi hgen 1).union h1 (hT0b.union h1 (hT0b.inv hi))
  · intro k hk
    apply Or.inr ∘ Or.inl
    exact ⟨1,Set.one_mem_pow h1,k.val,hKF hk,by simp⟩

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetKernelDescent
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma integer_kernel_coset_packing (K : Subgroup A) (S : Set A) (h1 : (1:A)∈S)
    (f : A →* Multiplicative ℤ) (hKf : K≤f.ker) (a : A) (ha : f a=Multiplicative.ofAdd 1)
    (T : Set f.ker) (L M : ℕ) (hT : f.ker.subtype '' T⊆S^L) (haS : a∈S^M)
    (n : ℕ) (hfin : (ball K S ((L+M+1)*n)).Finite) :
    n*(ball (K.subgroupOf f.ker) T n).ncard≤(ball K S ((L+M+1)*n)).ncard := by
  let Q := ball (K.subgroupOf f.ker) T n
  have hh : ∀ q∈Q, ∃ b : f.ker, b∈T^n ∧ (QuotientGroup.mk b : f.ker ⧸ K.subgroupOf f.ker)=q := fun q hq => hq
  choose b hb he using hh
  let phi : Fin n × Q → A ⧸ K := fun p => QuotientGroup.mk (a^p.1.val*(b p.2.val p.2.property).val)
  have hin (p : Fin n × Q) : phi p∈ball K S ((L+M+1)*n) := by
    refine ⟨a^p.1.val*(b p.2.val p.2.property).val,?_,rfl⟩
    have ha' : a^p.1.val∈S^(M*p.1.val) := by
      rw [pow_mul]
      exact Set.pow_mem_pow haS
    have hb' : (b p.2.val p.2.property).val∈S^(L*n) := by
      rw [pow_mul]
      apply Set.pow_subset_pow_left hT
      rw [←Set.image_pow]
      exact ⟨b p.2.val p.2.property,hb p.2.val p.2.property,rfl⟩
    apply Set.pow_subset_pow_right h1 (show M*p.1.val+L*n≤(L+M+1)*n by nlinarith [p.1.isLt])
    rw [pow_add]
    exact Set.mul_mem_mul ha' hb'
  have hphi : Injective phi := by
    rintro ⟨i,q⟩ ⟨j,r⟩ hij
    have hm := QuotientGroup.eq.mp hij
    have hf' := MonoidHom.mem_ker.mp (hKf hm)
    simp only [map_mul,map_inv,map_pow,ha,MonoidHom.mem_ker.mp (b q.val q.property).property,
      MonoidHom.mem_ker.mp (b r.val r.property).property,mul_one] at hf'
    have hi : i=j := by
      apply Fin.ext
      have hz := congrArg Multiplicative.toAdd hf'
      simp at hz
      omega
    subst j
    apply congrArg (fun s : Q => (i,s))
    apply Subtype.ext
    rw [←he q.val q.property,←he r.val r.property]
    apply QuotientGroup.eq.mpr
    change ((b q.val q.property).val)⁻¹*(b r.val r.property).val∈K
    simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel_left] using hm
  let e : Fin n × Q ↪ ball K S ((L+M+1)*n) := ⟨fun p => ⟨phi p,hin p⟩,fun p q h => hphi (congrArg Subtype.val h)⟩
  let : Finite (ball K S ((L+M+1)*n)) := hfin.to_subtype
  have hc := Nat.card_le_card_of_injective e e.injective
  simpa only [Nat.card_prod,Nat.card_fin,Nat.card_coe_set_eq,Q] using hc

lemma HasDegree.integer_kernel_descent {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hg : HasDegree K S (d+1)) (f : A →* Multiplicative ℤ) (hf : Surjective f) (hKf : K≤f.ker)
    (T : Set f.ker) (hT : Bounded S (f.ker.subtype '' T)) :
    HasDegree (K.subgroupOf f.ker) T d := by
  have hTf := (hg.subgroup_bounded h1 f.ker T hT).1
  obtain ⟨L,hL⟩ := hT
  obtain ⟨a,ha⟩ := hf (Multiplicative.ofAdd 1)
  obtain ⟨M,hM⟩ := bounded_singleton S h1 hi hgen a
  have haS := hM (Set.mem_singleton a)
  obtain ⟨C,hC⟩ := hg.2
  let D := L+M+1
  have hD : 0<D := by dsimp [D]; omega
  refine ⟨hTf,C*(2*D)^(d+1),?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC (D*max R 1)
  let n := r/D
  have hnr : D*n ≤ r := by simpa only [n,Nat.mul_comm] using Nat.div_mul_le_self r D
  have hn : max R 1≤n := (Nat.le_div_iff_mul_le hD).mpr (by simpa [Nat.mul_comm] using hr)
  have hn1 : 1≤n := (le_max_right R 1).trans hn
  have hrn : r≤(2*D)*n := by
    have hlt := Nat.lt_mul_div_succ r hD
    change r<D*(n+1) at hlt
    nlinarith
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  have hb : n*(ball (K.subgroupOf f.ker) T n).ncard≤n*(C*(2*D)^(d+1)*n^d) := by
    calc
      _ ≤ (ball K S (D*n)).ncard := integer_kernel_coset_packing K S h1 f hKf a ha T L M hL haS n (hg.1 _)
      _ ≤ (ball K S r).ncard := Set.ncard_le_ncard (ball_mono K S h1 hnr) (hg.1 _)
      _ ≤ C*r^(d+1) := hbound
      _ ≤ C*((2*D)*n)^(d+1) := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn (d+1))
      _ = _ := by rw [mul_pow,pow_succ n]; ring
  exact Nat.le_of_mul_le_mul_left hb (by omega : 0<n)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetFiniteIndex
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma ball_smaller_stabilizer_bound (K L : Subgroup A) (hLK : L≤K)
    [Finite (K ⧸ L.subgroupOf K)] (S : Set A) (n : ℕ)
    (hf : (ball K S n).Finite) :
    (ball L S n).Finite ∧ (ball L S n).ncard≤(ball K S n).ncard*Nat.card (K ⧸ L.subgroupOf K) := by
  let e := Subgroup.quotientEquivProdOfLE hLK
  have hsub : e '' ball L S n ⊆ ball K S n ×ˢ (Set.univ : Set (K ⧸ L.subgroupOf K)) := by
    rintro _ ⟨_,⟨g,hg,rfl⟩,rfl⟩
    exact ⟨⟨g,hg,rfl⟩,Set.mem_univ _⟩
  have hprod := hf.prod (Set.finite_univ : (Set.univ : Set (K ⧸ L.subgroupOf K)).Finite)
  have hfin : (ball L S n).Finite := (hprod.subset hsub).of_finite_image e.injective.injOn
  refine ⟨hfin,?_⟩
  have hc := Set.ncard_le_ncard hsub hprod
  rw [Set.ncard_image_of_injective _ e.injective,Set.ncard_prod,Set.ncard_univ] at hc
  exact hc

lemma HasDegree.smaller_stabilizer {K L : Subgroup A} (hLK : L≤K)
    [Finite (K ⧸ L.subgroupOf K)] {S : Set A} {d : ℕ} (hg : HasDegree K S d) :
    HasDegree L S d := by
  obtain ⟨hf,C,hC⟩ := hg
  refine ⟨fun n => (ball_smaller_stabilizer_bound K L hLK S n (hf n)).1,
    C*Nat.card (K ⧸ L.subgroupOf K),?_⟩
  intro R
  obtain ⟨n,hn,hbound⟩ := hC R
  refine ⟨n,hn,?_⟩
  have hh := (ball_smaller_stabilizer_bound K L hLK S n (hf n)).2
  calc
    _ ≤ (ball K S n).ncard*Nat.card (K ⧸ L.subgroupOf K) := hh
    _ ≤ (C*n^d)*Nat.card (K ⧸ L.subgroupOf K) := Nat.mul_le_mul_right _ hbound
    _ = _ := by ring

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetNormalPromotion
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma conjugate_eq_of_integer_value (f : A →* Multiplicative ℤ)
    (a : A) (ha : f a=Multiplicative.ofAdd 1) (N : Subgroup A)
    (hN : f.ker≤(Subgroup.normalizer (N:Set A))) (g : A) :
    N.map (MulAut.conj g).toMonoidHom=N.map (MulAut.conj (a^Multiplicative.toAdd (f g))).toMonoidHom := by
  let z := Multiplicative.toAdd (f g)
  have hl : (a^z)⁻¹*g∈f.ker := by
    change f ((a^z)⁻¹*g)=1
    rw [map_mul,map_inv,map_zpow,ha]
    apply Multiplicative.toAdd.injective
    simp [z]
  have he : N.map (MulAut.conj ((a^z)⁻¹*g)).toMonoidHom=N :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN hl)
  have hg : g=a^z*((a^z)⁻¹*g) := by simp
  conv_lhs => rw [hg]
  rw [←conjugate_map_map,he]

lemma finite_bounded_conjugate_family (K : Subgroup A) (S : Set A)
    (hf : ∀ n, (ball K S n).Finite) (f : A →* Multiplicative ℤ) (hK : K≤f.ker)
    (a : A) (ha : f a=Multiplicative.ofAdd 1) (N : Subgroup A)
    (hN : f.ker≤(Subgroup.normalizer (N:Set A))) (n : ℕ) :
    ((fun g => N.map (MulAut.conj g).toMonoidHom) '' S^n).Finite := by
  have hKi : (f '' (K:Set A)).Finite := by
    apply (Set.finite_singleton (1:Multiplicative ℤ)).subset
    rintro _ ⟨k,hk,rfl⟩
    exact MonoidHom.mem_ker.mp (hK hk)
  have hfi := finite_image_of_finite_coset_image K f hKi (S^n) (hf n)
  apply (hfi.image (fun z => N.map (MulAut.conj (a^Multiplicative.toAdd z)).toMonoidHom)).subset
  rintro _ ⟨g,hg,rfl⟩
  exact ⟨f g,⟨g,hg,rfl⟩,(conjugate_eq_of_integer_value f a ha N hN g).symm⟩

lemma HasDegree.promote_integer_normal {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤) (hg : HasDegree K S d)
    (f : A →* Multiplicative ℤ) (hf : Surjective f) (hK : K≤f.ker)
    (N : Subgroup A) (hNL : N≤f.ker) (hLN : f.ker≤(Subgroup.normalizer (N:Set A)))
    (hNb : Bounded S (N:Set A)) (hNi : N.relIndex K≠0) :
    ∃ M : Subgroup A, M.Normal ∧ Bounded S (M:Set A) ∧ M.relIndex K≠0 := by
  let J := K⊓N
  have hJi : J.relIndex K≠0 := by simpa only [J,Subgroup.inf_relIndex_left] using hNi
  let : Finite (K ⧸ J.subgroupOf K) := Nat.finite_of_card_ne_zero hJi
  have hgJ := hg.smaller_stabilizer (show J≤K from inf_le_left)
  obtain ⟨L,hL⟩ := hNb
  obtain ⟨n,hn⟩ := exists_conjugateStage_stationary S (N:Set A) h1 hi J
    (by simpa only [Subgroup.closure_eq] using (show J≤N from inf_le_right)) d hgJ L hL
  let M := Subgroup.normalClosure (N:Set A)
  have hM : M=conjugateStage S (N:Set A) n := normalClosure_eq_conjugateStage_of_stationary S (N:Set A) h1 hi hgen n hn
  obtain ⟨a,ha⟩ := hf (Multiplicative.ofAdd 1)
  refine ⟨M,inferInstance,?_,?_⟩
  · rw [hM,conjugateStage_eq_join]
    apply finite_normalized_join_bounded S h1 f.ker _
      (finite_bounded_conjugate_family K S hg.1 f hK a ha N hLN n)
    · rintro Q ⟨g,hg,rfl⟩
      have hh := Subgroup.map_mono hNL (f:=(MulAut.conj g).toMonoidHom)
      have he : f.ker.map (MulAut.conj g).toMonoidHom=f.ker := Subgroup.Normal.map_conj_eq f.ker g
      rwa [he] at hh
    · rintro Q ⟨g,hg,rfl⟩
      exact normalized_conjugate f.ker N hLN g
    · rintro Q ⟨g,hg,rfl⟩
      exact (show Bounded S (N:Set A) from ⟨L,hL⟩).conj h1 hi hgen g
  · exact fun he => hNi (Subgroup.relIndex_eq_zero_of_le_left (fun x hx => Subgroup.subset_normalClosure hx) he)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_CosetSubgroupGenerators
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A B : Type*} [Group A] [Group B]

lemma Bounded.image_trans {S : Set B} {T U : Set A} (f : A →* B)
    (hT : Bounded S (f '' T)) (hU : Bounded T U) : Bounded S (f '' U) := by
  obtain ⟨L,hL⟩ := hT
  obtain ⟨n,hn⟩ := hU
  refine ⟨L*n,?_⟩
  rw [pow_mul]
  apply Set.Subset.trans (Set.image_mono hn)
  rw [Set.image_pow]
  exact Set.pow_subset_pow_left hL

lemma finiteIndex_generators_containing_stabilizer (K : Subgroup A) (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (H : Subgroup A) [H.FiniteIndex] :
    ∃ T : Set H, (1:H)∈T ∧ T⁻¹=T ∧ Subgroup.closure T=⊤ ∧
      Bounded S (H.subtype '' T) ∧ (K.subgroupOf H:Set H)⊆T := by
  obtain ⟨U,hU1,hUi,hUgen,hUb⟩ := finiteIndex_bounded_generators S h1 hi hgen H
  let T := (K.subgroupOf H:Set H)∪U
  refine ⟨T,Or.inr hU1,?_,?_,?_,Set.subset_union_left⟩
  · simp only [T,Set.union_inv,inv_coe_set,hUi]
  · apply top_unique
    rw [←hUgen]
    exact Subgroup.closure_mono Set.subset_union_right
  · rw [Set.image_union]
    exact (hK.mono (by rintro _ ⟨k,hk,rfl⟩; exact hk)).union h1 hUb

lemma normalizer_of_normal_subgroup (H : Subgroup A) (N : Subgroup H) [N.Normal] :
    H≤Subgroup.normalizer ((N.map H.subtype):Set A) := by
  have hh := N.le_normalizer_map H.subtype
  rwa [Subgroup.normalizer_eq_top,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hh

lemma relIndex_map_subgroupOf_nonzero (K H : Subgroup A) [H.FiniteIndex]
    (N : Subgroup H) (hN : N.relIndex (K.subgroupOf H)≠0) :
    (N.map H.subtype).relIndex K≠0 := by
  have he : (K.subgroupOf H).map H.subtype=K⊓H := by
    rw [Subgroup.subgroupOf,Subgroup.map_comap_eq,Subgroup.range_subtype,inf_comm]
  have hfirst : (N.map H.subtype).relIndex (K⊓H)≠0 := by
    rw [←he,Subgroup.relIndex_map_map_of_injective N (K.subgroupOf H) H.subtype_injective]
    exact hN
  apply Subgroup.relIndex_ne_zero_trans hfirst
  rw [Subgroup.inf_relIndex_left]
  exact fun h => (inferInstance : H.FiniteIndex).index_ne_zero (Subgroup.index_eq_zero_of_relIndex_eq_zero h)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Classification_RelativeClassification
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma bounded_top_of_finiteIndex (K : Subgroup A) (S : Set A)
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) [K.FiniteIndex] : Bounded S (⊤:Subgroup A) := by
  let := K.fintypeQuotientOfFiniteIndex
  apply bounded_of_finite_coset_image S K h1 hi hgen hK
  exact Set.toFinite _

lemma relIndex_map_subgroupOf_of_le (K L : Subgroup A) (hKL : K≤L)
    (N : Subgroup L) (hN : N.relIndex (K.subgroupOf L)≠0) :
    (N.map L.subtype).relIndex K≠0 := by
  have he : (K.subgroupOf L).map L.subtype=K := by
    rw [Subgroup.subgroupOf,Subgroup.map_comap_eq,Subgroup.range_subtype,inf_eq_right.mpr hKL]
  rw [←he,Subgroup.relIndex_map_map_of_injective N (K.subgroupOf L) L.subtype_injective]
  exact hN

universe u

theorem bounded_normal_commensurable (d : ℕ) :
    ∀ (A : Type u) [Group A] (K : Subgroup A) (S : Set A),
      (1:A)∈S → S⁻¹=S → Subgroup.closure S=⊤ → Bounded S (K:Set A) → HasDegree K S d →
      ∃ N : Subgroup A, N.Normal ∧ Bounded S (N:Set A) ∧ N.relIndex K≠0 := by
  induction d with
  | zero =>
    intro A _ K S h1 hi hgen hK hg
    let := hg.zero_finiteIndex h1 hi hgen
    exact ⟨⊤,inferInstance,bounded_top_of_finiteIndex K S h1 hi hgen hK,by simp⟩
  | succ d ih =>
    intro A _ K S h1 hi hgen hK hg
    rcases finite_or_infinite (A ⧸ K) with hfin | hinf
    · let : K.FiniteIndex := ⟨by let := hfin; exact Nat.card_pos.ne'⟩
      exact ⟨⊤,inferInstance,bounded_top_of_finiteIndex K S h1 hi hgen hK,by simp⟩
    let := hinf
    obtain ⟨H,hHi,f,hf,hKf⟩ := virtually_indicable_bs h1 hi hgen hK hg
    let := hHi
    let J := K.subgroupOf H
    obtain ⟨T,hT1,hTi,hTgen,hTb,hKT⟩ :=
      finiteIndex_generators_containing_stabilizer K S h1 hi hgen hK H
    have hgT : HasDegree J T (d+1) := hg.subgroup_bounded h1 H T hTb
    obtain ⟨U,hU1,hUi,hUgen,hUb,hKU⟩ :=
      hgT.integer_kernel_bounded_generators hT1 hTi hTgen hKT f hf hKf
    have hgU : HasDegree (J.subgroupOf f.ker) U d :=
      hgT.integer_kernel_descent hT1 hTi hTgen f hf hKf U hUb
    obtain ⟨N,hNn,hNb,hNi⟩ := ih f.ker (J.subgroupOf f.ker) U hU1 hUi hUgen
      ⟨1,by simpa only [pow_one] using hKU⟩ hgU
    let := hNn
    let P := N.map f.ker.subtype
    have hPL : P≤f.ker := by rintro _ ⟨n,hn,rfl⟩; exact n.property
    have hPN : f.ker≤Subgroup.normalizer (P:Set H) := normalizer_of_normal_subgroup f.ker N
    have hPb : Bounded T (P:Set H) := Bounded.image_trans f.ker.subtype hUb hNb
    have hPi : P.relIndex J≠0 := relIndex_map_subgroupOf_of_le J f.ker hKf N hNi
    obtain ⟨M,hMn,hMb,hMi⟩ := hgT.promote_integer_normal hT1 hTi hTgen f hf hKf P hPL hPN hPb hPi
    let := hMn
    let Q := M.map H.subtype
    have hQn : H≤Subgroup.normalizer (Q:Set A) := normalizer_of_normal_subgroup H M
    have hQb : Bounded S (Q:Set A) := Bounded.image_trans H.subtype hTb hMb
    have hQi : Q.relIndex K≠0 := relIndex_map_subgroupOf_nonzero K H M hMi
    exact hg.finiteIndex_normal_core h1 hi hgen hK H Q hQn hQb hQi

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphTopology_CommensurableClosure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]

lemma isOpen_of_isClosed_relIndex (K H : Subgroup A) (hK : IsOpen (K:Set A))
    (hH : IsClosed (H:Set A)) (hi : H.relIndex K≠0) : IsOpen (H:Set A) := by
  let J := H.subgroupOf K
  let : J.FiniteIndex := ⟨hi⟩
  have hJ : IsOpen (J:Set K) := J.isOpen_of_isClosed_of_finiteIndex
    (hH.preimage continuous_subtype_val)
  have hI : IsOpen ((J.map K.subtype):Set A) := hK.isOpenMap_subtype_val _ hJ
  exact Subgroup.isOpen_mono (by rintro _ ⟨k,hk,rfl⟩; exact hk) hI

lemma topologicalClosure_open_of_relIndex (K N : Subgroup A) (hK : IsOpen (K:Set A))
    (hi : N.relIndex K≠0) : IsOpen (N.topologicalClosure:Set A) := by
  apply isOpen_of_isClosed_relIndex K N.topologicalClosure hK N.isClosed_topologicalClosure
  exact fun h => hi (Subgroup.relIndex_eq_zero_of_le_left N.le_topologicalClosure h)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_GraphRelativeGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma displacement_pow_subset (o : X) (n : ℕ) :
    displacement Γ o 1^n⊆displacement Γ o n := by
  induction n with
  | zero =>
    intro g hg
    have he : g=1 := by simpa only [pow_zero,Set.mem_one] using hg
    subst g
    exact one_mem_displacement Γ o 0
  | succ n ih =>
    rw [pow_succ]
    exact (Set.mul_subset_mul_right ih).trans (displacement_mul_subset Γ o n 1)

lemma stabilizer_coset_ball_image_subset (o : X) (n : ℕ) :
    stabilizerCosetEmbedding Γ o '' RelativeGrowth.ball (vertexStabilizer Γ o) (displacement Γ o 1) n
      ⊆reachBall Γ o n := by
  rintro _ ⟨_,⟨g,hg,rfl⟩,rfl⟩
  exact displacement_pow_subset Γ o n hg

lemma displacement_relativeDegree (hl : ∀ x, (Γ.neighborSet x).Finite) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    RelativeGrowth.HasDegree (vertexStabilizer Γ o) (displacement Γ o 1) d := by
  have hf (n : ℕ) : (RelativeGrowth.ball (vertexStabilizer Γ o) (displacement Γ o 1) n).Finite := by
    apply Set.Finite.of_finite_image (f:=stabilizerCosetEmbedding Γ o)
    · exact (reachBall_finite Γ hl o n).subset (stabilizer_coset_ball_image_subset Γ o n)
    · exact (stabilizerCosetEmbedding Γ o).injective.injOn
  refine ⟨hf,1,?_⟩
  intro R
  obtain ⟨n,hn,hb⟩ := hpoly R
  refine ⟨n,hn,?_⟩
  rw [one_mul]
  apply le_trans _ hb
  rw [←Set.ncard_image_of_injective _ (stabilizerCosetEmbedding Γ o).injective]
  exact Set.ncard_le_ncard (stabilizer_coset_ball_image_subset Γ o n) (reachBall_finite Γ hl o n)

lemma vertexStabilizer_bounded (o : X) :
    RelativeGrowth.Bounded (displacement Γ o 1) (vertexStabilizer Γ o:Set (Γ ≃g Γ)) := by
  refine ⟨1,?_⟩
  rw [pow_one]
  intro g hg
  change g o∈reachBall Γ o 1
  rw [(mem_vertexStabilizer Γ o g).mp hg]
  exact reachBall_self Γ o 1

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Classification_GraphCompactNormalClassification
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

theorem compact_open_normal_of_sparse_polynomial
    [TopologicalSpace X] [DiscreteTopology X]
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
    ∃ H : Subgroup (Γ ≃g Γ), H.Normal ∧ IsCompact (H:Set (Γ ≃g Γ)) ∧ IsOpen (H:Set (Γ ≃g Γ)) := by
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  let K := vertexStabilizer Γ o
  let S := displacement Γ o 1
  have h1 : (1:Γ ≃g Γ)∈S := one_mem_displacement Γ o 1
  have hi : S⁻¹=S := by ext g; exact displacement_inv Γ
  have hgen : Subgroup.closure S=⊤ := displacement_generates Γ hc ht o
  obtain ⟨N,hNn,hNb,hNi⟩ := RelativeGrowth.bounded_normal_commensurable d
    (Γ ≃g Γ) K S h1 hi hgen (vertexStabilizer_bounded Γ o) (displacement_relativeDegree Γ hl o d hpoly)
  let := hNn
  let H := N.topologicalClosure
  have hHn : H.Normal := Subgroup.is_normal_topologicalClosure N
  have hcH : IsCompact (H:Set (Γ ≃g Γ)) := by
    obtain ⟨n,hn⟩ := hNb
    have hNs : (N:Set (Γ ≃g Γ))⊆displacement Γ o n := hn.trans (displacement_pow_subset Γ o n)
    apply (compact_displacement Γ hc hl o n).of_isClosed_subset N.isClosed_topologicalClosure
    exact closure_minimal hNs (isClosed_eval_mem Γ o _)
  have hoH : IsOpen (H:Set (Γ ≃g Γ)) :=
    RelativeGrowth.topologicalClosure_open_of_relIndex K N (open_stabilizer Γ o) hNi
  exact ⟨H,hHn,hcH,hoH⟩

theorem compact_open_virtually_nilpotent_quotient_of_sparse_polynomial
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    HasCompactOpenVirtuallyNilpotentQuotient Γ := by
  let _ : TopologicalSpace X := ⊥
  let _ : DiscreteTopology X := ⟨rfl⟩
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  obtain ⟨H,hHn,hcH,hoH⟩ := compact_open_normal_of_sparse_polynomial Γ hc hl ht o d hpoly
  let := hHn
  have hg := quotient_sparse_polynomial_word_growth Γ hc hl ht o d hpoly H hoH
  obtain ⟨N,hNn,hNi⟩ := CompactQuotient.virtuallyNilpotent_of_sparse_word_growth_bs hg
  exact ⟨H,hHn,hcH,hoH,N,hNn,hNi.index_ne_zero⟩

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Main
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem no_percolation_at_criticality [Infinite V]
    (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive)
    (hpc : G.criticalProbability < 1) :
    G.law G.criticalProbability G.percolates = 0 := by
  by_contra hper
  obtain ⟨o⟩ := hconnected.nonempty
  obtain ⟨d,hd,C,hconn,hinf,hloc,htrans,hscales,happrox,hnot⟩ :=
    G.main_failure_topological_classification_counterexample_bs
      hconnected hlocal hquasi hpc hper o
  let u : MulAction.orbit G.Aut o := ⟨o,MulAction.mem_orbit_self o⟩
  apply hnot
  exact GraphTopology.compact_open_virtually_nilpotent_quotient_of_sparse_polynomial
    (G.orbitPower o (2*C+1)) hconn hloc htrans u (d+1) (fun R => by
      obtain ⟨n,hn,hp⟩ := hscales R
      exact ⟨n,hn,hp u⟩)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GeneralCriticalFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem critical_finite_general_bs_oai [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hpc : pc G < 1) (x : V) :
    ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
  have hz := (criticalModel G).no_percolation_at_criticality
    (criticalModel_connected G hconn) hloc (criticalModel_quasiTransitive G hqt)
    (by simpa only [criticalModel_pc] using hpc)
  rw [criticalModel_pc,criticalModel_percolates] at hz
  change law (pc G) {ω | (infiniteClusters G ω).Nonempty} = 0 at hz
  rw [ae_iff]
  apply measure_mono_null _ hz
  intro ω hω
  exact ⟨cluster G ω x,hω,x,rfl⟩

end Percolation.BenjaminiSchramm

end OAI
end

theorem solution.{u, v} : type_of% @OAI.Percolation.BenjaminiSchramm.critical_finite_general_bs_oai.{u, v} := @OAI.Percolation.BenjaminiSchramm.critical_finite_general_bs_oai.{u, v}
