-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:23:10.132198+00:00
-- url     : https://prove2.me/submissions/d615bdd4-2538-4035-8170-5af51e8eef3c

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Definitions.Def_OAIQ228B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_critical_null_of_compact_open_orbital_quotient
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_main_failure_sparse_polynomial
import Theorems.Thm_OAI_CriticalPercolation_RelativeGrowth_virtually_indicable
import Theorems.Thm_OAI_CriticalPercolation_SparseGrowth_HasPolynomialDegree_linear_virtually_indicable

section
-- module Solutions.Q228_CP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_GraphAutomorphismTopology
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_GraphNeighborhoodCompact
attribute [-simp] _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.mem_around
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

lemma open_displacement (o : X) (r : ℕ) :
    IsOpen {g : Γ ≃g Γ | g o∈reachBall Γ o r} := isOpen_eval_mem Γ o _

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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_GraphBalls
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbit_density_radius (hconnected : G.fullGraph.Connected)
    (hquasi : G.QuasiTransitive) (u : V) :
    ∃ C : ℕ, ∀ v, ∃ φ : G.Aut, φ.vertex u ∈ G.vertexBall v C := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  have hpath : ∀ z : S, ∃ n, u ∈ G.vertexBall z.val n :=
    fun z => G.reachable_mem_vertexBall (hconnected z u)
  choose n hn using hpath
  let := hS.fintype
  let C := ∑ z : S, n z
  refine ⟨C,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  refine ⟨φ,(Aut.vertexBall_mem G φ z u C).mpr ?_⟩
  exact G.vertexBall_mono z (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨z,hz⟩ : S))) (hn ⟨z,hz⟩)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FiniteIndexAction
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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
variable {V E Λ Q : Type*} (G : BondGraph V E)
  [Group Λ] [Group Q] [MulAction Λ V] [MulAction Λ E]

lemma subgroup_preservesEnds (ha : G.PreservesEnds (Λ := Λ)) (L : Subgroup Λ) :
    G.PreservesEnds (Λ := L) := fun g e => ha g.val e

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OrbitQuotientTransfer
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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
variable {V E Λ Q Y : Type*} (G : BondGraph V E)
  [Group Λ] [Group Q] [MulAction Λ V] [MulAction Λ E]

lemma finite_kernel_orbits_from_one_vertex
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := Λ)) (ρ : Λ →* Q) (o : V)
    (ho : (MulAction.orbit ρ.ker o).Finite) :
    ∀ v : V, (MulAction.orbit ρ.ker v).Finite := by
  intro v
  obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc o v)
  have hfin := ho.biUnion (fun w _ => G.vertexBall_finite hl w n)
  apply hfin.subset
  rintro w ⟨g,rfl⟩
  refine Set.mem_iUnion₂.mpr ⟨g.val • o,⟨g,rfl⟩,?_⟩
  exact (Aut.vertexBall_mem G (G.smulAut ha g.val) o v n).mpr hn

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OrbitalPower
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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

lemma powerOn_reachable_of_close {O : Set V} {L : ℕ} (u v : O)
    (h : v.val∈G.vertexBall u.val L) : (G.powerOn O L).Reachable u v := by
  by_cases huv : u=v
  · rw [huv]
  · exact SimpleGraph.Adj.reachable (⟨huv,h⟩ : (G.powerOn O L).Adj u v)

lemma powerOn_reachable_lift {O : Set V} {C : ℕ}
    (hdense : ∀ x : V, ∃ u : O, u.val∈G.vertexBall x C)
    {x y : V} (p : G.fullGraph.Walk x y) (u v : O)
    (hu : u.val∈G.vertexBall x C) (hv : v.val∈G.vertexBall y C) :
    (G.powerOn O (2*C+1)).Reachable u v := by
  induction p generalizing u with
  | nil =>
    apply G.powerOn_reachable_of_close
    exact G.vertexBall_mono u.val (by omega)
      (G.vertexBall_add (G.vertexBall_comm.mp hu) C hv)
  | @cons x z y hxz p ih =>
    obtain ⟨w,hw⟩ := hdense z
    apply SimpleGraph.Reachable.trans (v := w)
    · apply G.powerOn_reachable_of_close
      have hz := G.vertexBall_step (G.vertexBall_comm.mp hu) hxz
      have hvw := G.vertexBall_add hz C hw
      simpa only [show C+1+C=2*C+1 by omega] using hvw
    · exact ih w hw hv

lemma powerOn_connected (hc : G.fullGraph.Connected) {O : Set V} {C : ℕ}
    (hdense : ∀ x : V, ∃ u : O, u.val∈G.vertexBall x C) :
    (G.powerOn O (2*C+1)).Connected := by
  let _ := hc.nonempty
  obtain ⟨o⟩ := ‹Nonempty V›
  obtain ⟨u,_⟩ := hdense o
  let _ : Nonempty O := ⟨u⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨p⟩ := hc x.val y.val
  exact G.powerOn_reachable_lift hdense p x y
    (G.mem_vertexBall_self x.val C) (G.mem_vertexBall_self y.val C)

lemma powerOn_finite_neighbors (hl : G.LocallyFinite) (O : Set V) (L : ℕ) (u : O) :
    ((G.powerOn O L).neighborSet u).Finite := by
  apply (Set.Finite.preimage Subtype.val_injective.injOn (G.vertexBall_finite hl u.val L)).subset
  exact fun _ h => h.2

lemma powerOn_walk_bound {O : Set V} {L : ℕ} {u v : O}
    (p : (G.powerOn O L).Walk u v) :
    v.val∈G.vertexBall u.val (L*p.length) := by
  induction p with
  | nil => exact G.mem_vertexBall_self _ _
  | @cons u w v huw p ih =>
    simpa only [SimpleGraph.Walk.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm]
      using G.vertexBall_add huw.2 (L*p.length) ih

lemma powerOn_ball_bound {O : Set V} {L n : ℕ} (u : O) :
    {v : O | ∃ p : (G.powerOn O L).Walk u v, p.length≤n} ⊆
      Subtype.val ⁻¹' G.vertexBall u.val (L*n) := by
  rintro v ⟨p,hp⟩
  exact G.vertexBall_mono u.val (Nat.mul_le_mul_left _ hp) (G.powerOn_walk_bound p)

lemma powerOn_ball_card_le (hl : G.LocallyFinite) {O : Set V} {L n C R : ℕ}
    (x : V) (u : O) (hu : u.val∈G.vertexBall x C) (hR : C+L*n≤R) :
    {v : O | ∃ p : (G.powerOn O L).Walk u v, p.length≤n}.ncard ≤
      (G.vertexBall x R).ncard := by
  have hh : {v : O | ∃ p : (G.powerOn O L).Walk u v, p.length≤n} ⊆
      Subtype.val ⁻¹' G.vertexBall x R := by
    intro v hv
    exact G.vertexBall_mono x hR (G.vertexBall_add hu (L*n) (G.powerOn_ball_bound u hv))
  calc
    _ = (Subtype.val '' {v : O | ∃ p : (G.powerOn O L).Walk u v, p.length≤n}).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (G.vertexBall x R).ncard := Set.ncard_le_ncard (Set.image_subset_iff.mpr hh)
      (G.vertexBall_finite hl x R)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OrbitalAction
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

lemma orbitPower_connected (hc : G.fullGraph.Connected) (hq : G.QuasiTransitive)
    (o : V) : ∃ C : ℕ, (G.orbitPower o (2*C+1)).Connected ∧
      (∀ v, ∃ u : MulAction.orbit G.Aut o, u.val∈G.vertexBall v C) := by
  obtain ⟨C,hC⟩ := G.orbit_density_radius hc hq o
  have hd : ∀ v, ∃ u : MulAction.orbit G.Aut o, u.val∈G.vertexBall v C := by
    intro v
    obtain ⟨φ,hφ⟩ := hC v
    exact ⟨⟨φ.vertex o,⟨φ,rfl⟩⟩,hφ⟩
  exact ⟨C,G.powerOn_connected hc hd,hd⟩

lemma orbitPower_ball_ncard (o : V) (L n : ℕ) (u v : MulAction.orbit G.Aut o) :
    {w | ∃ p : (G.orbitPower o L).Walk u w, p.length≤n}.ncard =
    {w | ∃ p : (G.orbitPower o L).Walk v w, p.length≤n}.ncard := by
  obtain ⟨φ,hφ⟩ := MulAction.exists_smul_eq G.Aut u v
  subst v
  let f := G.orbitPowerHom o L φ
  have he : f '' {w | ∃ p : (G.orbitPower o L).Walk u w, p.length≤n} =
      {w | ∃ p : (G.orbitPower o L).Walk (φ • u) w, p.length≤n} := by
    ext w
    constructor
    · rintro ⟨z,⟨p,hp⟩,rfl⟩
      exact ⟨p.map f.toHom,(SimpleGraph.Walk.length_map f.toHom p).le.trans hp⟩
    · rintro ⟨p,hp⟩
      refine ⟨f.symm w,?_,f.apply_symm_apply w⟩
      have hp' : ∃ q : (G.orbitPower o L).Walk (f.symm (f u)) (f.symm w), q.length≤n :=
        ⟨p.map f.symm.toHom,(SimpleGraph.Walk.length_map f.symm.toHom p).le.trans hp⟩
      rw [show f.symm (f u)=u from f.symm_apply_apply u] at hp'
      exact hp'
  rw [← he,Set.ncard_image_of_injective _ f.injective]

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OrbitalScales
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma dense_set_infinite [Infinite V] (hl : G.LocallyFinite) {O : Set V} {C : ℕ}
    (hdense : ∀ x : V, ∃ u : O, u.val∈G.vertexBall x C) : O.Infinite := by
  intro hO
  have hh : (⋃ u∈O, G.vertexBall u C).Finite :=
    hO.biUnion (fun u _ => G.vertexBall_finite hl u C)
  apply Set.infinite_univ.not_finite (hh.subset ?_)
  intro v _
  obtain ⟨u,hu⟩ := hdense v
  exact Set.mem_iUnion₂.mpr ⟨u.val,u.property,G.vertexBall_comm.mp hu⟩

lemma polynomial_scale_arithmetic (C L d N R : ℕ) (hL : 0<L)
    (hR : C+L*(max N ((C+2*L)^d)+1)≤R) :
    let n := (R-C)/L
    N≤n ∧ C+L*n≤R ∧ R^d≤n^(d+1) := by
  dsimp
  let n := (R-C)/L
  change N≤n ∧ C+L*n≤R ∧ R^d≤n^(d+1)
  have hC : C≤R := by omega
  have hsub : R-C+C=R := Nat.sub_add_cancel hC
  have hN : max N ((C+2*L)^d)+1≤n := by
    apply (Nat.le_div_iff_mul_le hL).mpr
    nlinarith
  have hn : 1≤n := by omega
  have hmul : L*n≤R-C := by
    dsimp [n]
    exact Nat.mul_div_le (R-C) L
  have hmod : R-C<L*n+L := by
    have he := Nat.div_add_mod (R-C) L
    have ht := Nat.mod_lt (R-C) hL
    dsimp [n]
    nlinarith
  have hcn : C+L≤(C+L)*n := by nlinarith [Nat.mul_le_mul_left (C+L) hn]
  have hupper : R≤(C+2*L)*n := by nlinarith
  refine ⟨by omega,by omega,?_⟩
  calc
    R^d ≤ ((C+2*L)*n)^d := Nat.pow_le_pow_left hupper d
    _ = (C+2*L)^d*n^d := Nat.mul_pow _ _ _
    _ ≤ n*n^d := Nat.mul_le_mul_right _ (by omega)
    _ = n^(d+1) := by rw [pow_succ,Nat.mul_comm]

theorem orbital_power_polynomial_scales (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) :
    ∃ C : ℕ, (G.orbitPower o (2*C+1)).Connected ∧
      (∀ x, ∃ u : MulAction.orbit G.Aut o, u.val∈G.vertexBall x C) ∧
      (∀ N : ℕ, ∃ n≥N, ∀ u : MulAction.orbit G.Aut o,
        {v | ∃ p : (G.orbitPower o (2*C+1)).Walk u v, p.length≤n}.ncard≤n^(d+1)) := by
  obtain ⟨C,hC,hdense⟩ := G.orbitPower_connected hc hq o
  refine ⟨C,hC,hdense,?_⟩
  intro N
  let L := 2*C+1
  obtain ⟨R,hR,x,hx⟩ := hpoly (C+L*(max N ((C+2*L)^d)+1))
  obtain ⟨u,hu⟩ := hdense x
  have hh := polynomial_scale_arithmetic C L d N R (by dsimp [L]; omega) hR
  dsimp only at hh
  refine ⟨(R-C)/L,hh.1,?_⟩
  intro v
  rw [G.orbitPower_ball_ncard o L ((R-C)/L) v u]
  exact (G.powerOn_ball_card_le hl x u hu hh.2.1).trans (hx.trans hh.2.2)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_SparseDoubling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

lemma sparse_polynomial_doubling_scales (f : ℕ → ℕ) (hf : Monotone f)
    (hpos : ∀ n, 1≤f n) (d : ℕ) (hpoly : ∀ R, ∃ n≥R, f n≤n^d) :
    ∀ R : ℕ, ∃ n≥R, f (5*n)≤5^(d+1)*f n := by
  intro R
  by_contra! hbad
  let A := max R 1
  have hA : 0<A := by dsimp [A]; omega
  have hRA : R≤A := le_max_left _ _
  have hgrow : ∀ k : ℕ, (5^(d+1))^k≤f (5^k*A) := by
    intro k
    induction k with
    | zero => simpa using hpos A
    | succ k ih =>
      have hbase : R≤5^k*A := hRA.trans (by
        have : 1≤5^k := Nat.one_le_pow k 5 (by omega)
        nlinarith)
      have hh := (hbad (5^k*A) hbase).le
      calc
        (5^(d+1))^(k+1) = 5^(d+1)*(5^(d+1))^k := by rw [pow_succ]; ring
        _ ≤ 5^(d+1)*f (5^k*A) := Nat.mul_le_mul_left _ ih
        _ ≤ f (5*(5^k*A)) := hh
        _ = f (5^(k+1)*A) := by congr 1; rw [pow_succ]; ring
  obtain ⟨n,hn,hnpoly⟩ := hpoly (5*A*((5*A)^d+1))
  have hnA : 5*((5*A)^d+1)≤n/A := by
    apply (Nat.le_div_iff_mul_le hA).mpr
    nlinarith
  have hnApos : n/A≠0 := by omega
  let k := Nat.log 5 (n/A)
  let P := 5^k
  have hP : P≤n/A := Nat.pow_log_le_self 5 hnApos
  have hP' : n/A<5*P := by
    have hh := Nat.lt_pow_of_log_lt (b := 5) (x := k+1) (y := n/A) (by omega)
      (show Nat.log 5 (n/A)<k+1 by omega)
    simpa only [pow_succ,Nat.mul_comm] using hh
  have hPL : (5*A)^d<P := by nlinarith
  have hPA : P*A≤n := (Nat.le_div_iff_mul_le hA).mp hP
  have hnupper : n<(5*P)*A := (Nat.div_lt_iff_lt_mul hA).mp hP'
  have hPP : 5^((d+1)*k)≤f n := by
    rw [pow_mul]
    exact (hgrow k).trans (hf hPA)
  have hform : 5^((d+1)*k)=P^d*P := by
    dsimp [P]
    rw [←pow_mul,←pow_add]
    congr 1
    ring
  rw [hform] at hPP
  have hupper : n^d≤P^d*(5*A)^d := by
    have hh := Nat.pow_le_pow_left hnupper.le d
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hPpos : 0<P^d := pow_pos (by dsimp [P] <;> positivity) d
  have hlt : P^d*(5*A)^d<P^d*P := Nat.mul_lt_mul_of_pos_left hPL hPpos
  exact (not_lt_of_ge (hPP.trans (hnpoly.trans hupper))) hlt

end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_OrbitalNeighborhoods
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical Pointwise

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbitBall_finite (hl : G.LocallyFinite) (o : V) (r : ℕ) :
    (G.orbitBall o r).Finite := (G.vertexBall_finite hl o r).subset Set.inter_subset_right

lemma Aut.orbitBall_mem (φ : G.Aut) (o v : V) (r : ℕ) :
    φ • v ∈ G.orbitBall (φ • o) r ↔ v ∈ G.orbitBall o r := by
  change (φ • v ∈ MulAction.orbit G.Aut (φ • o) ∧
    φ.vertex v ∈ G.vertexBall (φ.vertex o) r) ↔ _
  rw [Aut.vertexBall_mem]
  refine and_congr ?_ Iff.rfl
  rw [MulAction.orbit_smul]
  constructor
  · rintro ⟨ψ,hψ⟩
    refine ⟨φ⁻¹*ψ,?_⟩
    change (φ⁻¹*ψ) • o=v
    change ψ • o=φ • v at hψ
    rw [mul_smul,hψ,inv_smul_smul]
  · rintro ⟨ψ,rfl⟩
    exact ⟨φ*ψ,mul_smul _ _ _⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OrbitalFiniteGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbitPower_propagate_subgroup_orbit (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (hgen : ∀ v∈G.orbitBall o L, v∈MulAction.orbit Λ o)
    {u v : MulAction.orbit G.Aut o} (huv : (G.orbitPower o L).Adj u v)
    (hu : u.val∈MulAction.orbit Λ o) : v.val∈MulAction.orbit Λ o := by
  obtain ⟨φ,hφ⟩ := hu
  change φ.val • o=u.val at hφ
  have hv : v.val∈G.orbitBall (φ.val • o) L := by
    refine ⟨?_,?_⟩
    · simpa only [MulAction.orbit_smul] using v.property
    · rw [hφ]
      exact huv.2
  have hback : φ.val⁻¹ • v.val∈G.orbitBall o L := by
    have hh := (Aut.orbitBall_mem G φ.val o (φ.val⁻¹ • v.val) L)
    rw [smul_inv_smul] at hh
    exact hh.mp hv
  obtain ⟨ψ,hψ⟩ := hgen _ hback
  refine ⟨φ*ψ,?_⟩
  change (φ*ψ) • o=v.val
  change ψ • o=φ.val⁻¹ • v.val at hψ
  rw [mul_smul,hψ]
  change φ.val • (φ.val⁻¹ • v.val)=v.val
  exact smul_inv_smul _ _

lemma orbitPower_subgroup_transitive (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (hc : (G.orbitPower o L).Connected)
    (hgen : ∀ v∈G.orbitBall o L, v∈MulAction.orbit Λ o) :
    MulAction.orbit Λ o=MulAction.orbit G.Aut o := by
  apply Set.Subset.antisymm
  · rintro v ⟨φ,hφ⟩
    exact ⟨φ.val,hφ⟩
  · intro v hv
    let o' : MulAction.orbit G.Aut o := ⟨o,MulAction.mem_orbit_self o⟩
    let v' : MulAction.orbit G.Aut o := ⟨v,hv⟩
    obtain ⟨p⟩ := hc o' v'
    have hwalk : ∀ {u w : MulAction.orbit G.Aut o} (p : (G.orbitPower o L).Walk u w),
        u.val∈MulAction.orbit Λ o → w.val∈MulAction.orbit Λ o := by
      intro u w p
      induction p with
      | nil => exact id
      | cons huw p ih =>
        exact fun hu => ih (G.orbitPower_propagate_subgroup_orbit o L Λ hgen huw hu)
    exact hwalk p (MulAction.mem_orbit_self o)

lemma dense_orbit_subgroup_representatives (o : V)
    (C : ℕ) (hdense : ∀ v, ∃ u : MulAction.orbit G.Aut o, u.val∈G.vertexBall v C)
    (Λ : Subgroup G.Aut) (horbit : MulAction.orbit Λ o=MulAction.orbit G.Aut o) :
    ∀ v, ∃ s∈G.vertexBall o C, v∈MulAction.orbit Λ s := by
  intro v
  obtain ⟨u,hu⟩ := hdense v
  have hu' : u.val∈MulAction.orbit Λ o := by rw [horbit]; exact u.property
  obtain ⟨φ,hφ⟩ := hu'
  change φ.val • o=u.val at hφ
  refine ⟨φ.val⁻¹ • v,?_,φ,?_⟩
  · apply (Aut.vertexBall_mem G φ.val o (φ.val⁻¹ • v) C).mp
    change φ.val • (φ.val⁻¹ • v)∈G.vertexBall (φ.val • o) C
    rw [smul_inv_smul,hφ]
    exact G.vertexBall_comm.mp hu
  · change φ.val • (φ.val⁻¹ • v)=v
    exact smul_inv_smul _ _

theorem finitelyGenerated_quasiTransitive_subgroup (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) :
    ∃ Λ : Subgroup G.Aut, Group.FG Λ ∧
      MulAction.orbit Λ o=MulAction.orbit G.Aut o ∧
      ∃ S : Set V, S.Finite ∧ ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s := by
  obtain ⟨C,hC,hdense⟩ := G.orbitPower_connected hc hq o
  let B := G.orbitBall o (2*C+1)
  have hB : B.Finite := G.orbitBall_finite hl o _
  let _ := hB.fintype
  have hφ : ∀ v : B, ∃ φ : G.Aut, φ • o=v.val := fun v => v.property.1
  choose φ hφ using hφ
  let F := Finset.univ.image φ
  let Λ := Subgroup.closure (F : Set G.Aut)
  have hgen : ∀ v∈G.orbitBall o (2*C+1), v∈MulAction.orbit Λ o := by
    intro v hv
    have hf : φ ⟨v,hv⟩∈Λ := Subgroup.subset_closure
      (Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩)
    exact ⟨⟨φ ⟨v,hv⟩,hf⟩,hφ ⟨v,hv⟩⟩
  have horbit := G.orbitPower_subgroup_transitive o (2*C+1) Λ hC hgen
  refine ⟨Λ,inferInstance,horbit,G.vertexBall o C,G.vertexBall_finite hl o C,?_⟩
  exact G.dense_orbit_subgroup_representatives o C hdense Λ horbit

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularLevelGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

attribute [local instance] OAI.CriticalPercolation.BondGraph.instMulActionAut_1
lemma aut_preservesEnds : G.PreservesEnds (Λ := G.Aut) := fun φ => φ.preserves

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Classification_FaithfulOrbitalModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbitalActionMap_kernel_fixes (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (φ : (G.orbitalActionMap o L Λ).ker) : φ • o=o := by
  have hh := congrArg Subtype.val φ.property
  change (G.orbitPowerHom o L φ.val.val) = 1 at hh
  let o' : MulAction.orbit G.Aut o := ⟨o,MulAction.mem_orbit_self o⟩
  have ho := congrArg (fun f : G.orbitPower o L ≃g G.orbitPower o L => (f o').val) hh
  exact ho

lemma orbitalActionMap_finite_kernel_orbits (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (o : V) (L : ℕ) (Λ : Subgroup G.Aut) :
    ∀ v : V, (MulAction.orbit (G.orbitalActionMap o L Λ).ker v).Finite := by
  let _ : MulAction G.Aut E := G.autEdgeAction
  apply G.finite_kernel_orbits_from_one_vertex hc hl
    (G.subgroup_preservesEnds G.aut_preservesEnds Λ) (G.orbitalActionMap o L Λ) o
  apply (Set.finite_singleton o).subset
  rintro v ⟨φ,rfl⟩
  exact G.orbitalActionMap_kernel_fixes o L Λ φ

lemma orbitalActionGroup_transitive (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (horbit : MulAction.orbit Λ o=MulAction.orbit G.Aut o)
    (u v : MulAction.orbit G.Aut o) :
    ∃ φ : G.orbitalActionGroup o L Λ, φ.val u=v := by
  have hu : u.val∈MulAction.orbit Λ o := by rw [horbit]; exact u.property
  have hv : v.val∈MulAction.orbit Λ o := by rw [horbit]; exact v.property
  obtain ⟨a,ha⟩ := hu
  obtain ⟨b,hb⟩ := hv
  refine ⟨G.orbitalActionMap o L Λ (b*a⁻¹),?_⟩
  apply Subtype.ext
  change (b*a⁻¹) • u.val=v.val
  change a • o=u.val at ha
  change b • o=v.val at hb
  rw [←ha,mul_smul,inv_smul_smul,hb]

theorem sparse_polynomial_faithful_orbital_model [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (o : V) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) :
    ∃ C : ℕ, ∃ Λ : Subgroup G.Aut, Group.FG Λ ∧
      (G.orbitPower o (2*C+1)).Connected ∧
      (MulAction.orbit G.Aut o).Infinite ∧
      (∀ u, ((G.orbitPower o (2*C+1)).neighborSet u).Finite) ∧
      (∀ u v, ∃ φ : G.orbitalActionGroup o (2*C+1) Λ, φ.val u=v) ∧
      (∀ v : V, (MulAction.orbit (G.orbitalActionMap o (2*C+1) Λ).ker v).Finite) ∧
      (∃ S : Set V, S.Finite ∧ ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) ∧
      (∀ R : ℕ, ∃ n≥R, ∀ u : MulAction.orbit G.Aut o,
        {v | ∃ p : (G.orbitPower o (2*C+1)).Walk u v, p.length≤n}.ncard≤n^(d+1)) := by
  obtain ⟨C,hC,hdense,hscales⟩ := G.orbital_power_polynomial_scales hc hl hq o d hpoly
  obtain ⟨Λ,hΛ,horbit,hreps⟩ := G.finitelyGenerated_quasiTransitive_subgroup hc hl hq o
  refine ⟨C,Λ,hΛ,hC,G.dense_set_infinite hl hdense,?_,?_,?_,hreps,hscales⟩
  · exact G.powerOn_finite_neighbors hl _ _
  · exact G.orbitalActionGroup_transitive o (2*C+1) Λ horbit
  · exact G.orbitalActionMap_finite_kernel_orbits hc hl o (2*C+1) Λ

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_CentralCommutatorGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G : Type*} [Group G]

private lemma central_conjugation {z : G} (hz : z∈Subgroup.center G) (a : G) :
    a*z*a⁻¹=z := by
  rw [Subgroup.mem_center_iff.mp hz a,mul_assoc,mul_inv_cancel,mul_one]

private lemma central_comm_inv_left {a b : G} (h : ⁅a,b⁆∈Subgroup.center G) :
    ⁅a⁻¹,b⁆=⁅a,b⁆⁻¹ := by
  rw [commutatorElement_inv_left,←commutatorElement_inv]
  simpa using central_conjugation ((Subgroup.center G).inv_mem h) a⁻¹

private lemma central_comm_inv_right {a b : G} (h : ⁅a,b⁆∈Subgroup.center G) :
    ⁅a,b⁻¹⁆=⁅a,b⁆⁻¹ := by
  rw [commutatorElement_inv_right,←commutatorElement_inv]
  simpa using central_conjugation ((Subgroup.center G).inv_mem h) b⁻¹

theorem central_commutator_generated (S T : Set G)
    (hc : ⁅Subgroup.closure S,Subgroup.closure T⁆≤Subgroup.center G) :
    ⁅Subgroup.closure S,Subgroup.closure T⁆=
      Subgroup.closure (Set.image2 (fun a b : G => ⁅a,b⁆) S T) := by
  let K := Subgroup.closure (Set.image2 (fun a b : G => ⁅a,b⁆) S T)
  have hz {a b : G} (ha : a∈Subgroup.closure S) (hb : b∈Subgroup.closure T) :
      ⁅a,b⁆∈Subgroup.center G := hc (Subgroup.commutator_mem_commutator ha hb)
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      intro b hb
      induction hb using Subgroup.closure_induction with
      | mem b hb => exact Subgroup.subset_closure (Set.mem_image2.mpr ⟨a,ha,b,hb,rfl⟩)
      | one => simp
      | mul b c hb hc' ihb ihc =>
        rw [commutatorElement_mul_right_eq_mul_conj]
        have he : ⁅a,b⁆*b*⁅a,c⁆*b⁻¹=⁅a,b⁆*(b*⁅a,c⁆*b⁻¹) := by group
        rw [he,central_conjugation (hz (Subgroup.subset_closure ha) hc') b]
        exact K.mul_mem ihb ihc
      | inv b hb ih =>
        rw [central_comm_inv_right (hz (Subgroup.subset_closure ha) hb)]
        exact K.inv_mem ih
    | one => intro b _; simp
    | mul a c ha hc' iha ihc =>
      intro b hb
      rw [commutatorElement_mul_left_eq_conj_mul,
        central_conjugation (hz hc' hb) a]
      exact K.mul_mem (ihc b hb) (iha b hb)
    | inv a ha ih =>
      intro b hb
      rw [central_comm_inv_left (hz ha hb)]
      exact K.inv_mem (ih b hb)
  · apply (Subgroup.closure_le _).mpr
    rintro z ⟨a,ha,b,hb,rfl⟩
    exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure ha)
      (Subgroup.subset_closure hb)

theorem central_commutator_fg (H J : Subgroup G) (hH : H.FG) (hJ : J.FG)
    (hc : ⁅H,J⁆≤Subgroup.center G) : ⁅H,J⁆.FG := by
  obtain ⟨S,hS,hfinS⟩ := Subgroup.fg_iff H |>.mp hH
  obtain ⟨T,hT,hfinT⟩ := Subgroup.fg_iff J |>.mp hJ
  apply (Subgroup.fg_iff _).mpr
  refine ⟨Set.image2 (fun a b : G => ⁅a,b⁆) S T,?_,hfinS.image2 _ hfinT⟩
  rw [←central_commutator_generated S T (by rwa [hS,hT]),hS,hT]

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_CentralCommutatorQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable {G Q : Type*} [Group G] [Group Q]

lemma finite_generating_lifts [Group.FG Q] {H : Type*} [Group H]
    (f : H →* Q) (hf : Surjective f) :
    ∃ S : Set H, S.Finite ∧ (Subgroup.closure S).map f=⊤ := by
  obtain ⟨T,hT,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG Q)
  choose s hs using hf
  refine ⟨s '' T,hfin.image s,?_⟩
  rw [MonoidHom.map_closure,Set.image_image]
  have he : (fun x => f (s x))=id := funext hs
  rw [he,Set.image_id,hT]

theorem central_commutator_fg_of_quotient [Group.FG G] [Group.FG Q]
    (H : Subgroup G) (f : H →* Q) (hf : Surjective f)
    (hker : f.ker.map H.subtype≤Subgroup.center G)
    (hcentral : ⁅(⊤ : Subgroup G),H⁆≤Subgroup.center G) :
    ⁅(⊤ : Subgroup G),H⁆.FG := by
  obtain ⟨S,hS,himage⟩ := finite_generating_lifts f hf
  let L := Subgroup.closure S
  let M := L.map H.subtype
  have hM : M.FG := by
    apply (Subgroup.fg_iff M).mpr
    refine ⟨H.subtype '' S,?_,hS.image H.subtype⟩
    exact (MonoidHom.map_closure H.subtype S).symm
  have hMH : M≤H := by
    rintro x ⟨y,_,rfl⟩
    exact y.property
  suffices he : ⁅(⊤ : Subgroup G),H⁆=⁅(⊤ : Subgroup G),M⁆ by
    rw [he]
    exact central_commutator_fg ⊤ M (Group.fg_def.mp inferInstance) hM
      ((Subgroup.commutator_mono le_rfl hMH).trans hcentral)
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro g _ h hh
    have him : f ⟨h,hh⟩∈L.map f := by rw [himage]; trivial
    obtain ⟨l,hl,he⟩ := him
    let z : H := l⁻¹*⟨h,hh⟩
    have hzker : z∈f.ker := by
      change f (l⁻¹*⟨h,hh⟩)=1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hz : (z:G)∈Subgroup.center G := hker ⟨z,hzker,rfl⟩
    have hgz : ⁅g,(z:G)⁆=1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz g)
    have hdecomp : h=(l:G)*(z:G) := by simp [z]
    rw [hdecomp,commutatorElement_mul_right_eq_mul_conj,hgz]
    simpa using (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G))
      (H₂ := M) (by trivial) (show (l:G)∈M from ⟨l,hl,rfl⟩) : ⁅g,(l:G)⁆∈⁅⊤,M⁆)
  · exact Subgroup.commutator_mono le_rfl hMH

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_LowerCentralFG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation
variable (G : Type*) [Group G]

lemma lowerFactor_central (n : ℕ) : lowerFactor G n≤
    Subgroup.center (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (n+1)) := by
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
  let f := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1))
  have hf : (⊤ : Subgroup G).map f=⊤ :=
    Subgroup.map_top_of_surjective f QuotientGroup.mk_surjective
  change ⁅((⊤ : Subgroup G).lowerCentralSeries n).map f,⊤⁆=⊥
  rw [←hf,←Subgroup.map_commutator,←Subgroup.lowerCentralSeries_succ]
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']

theorem lowerFactor_fg [Group.FG G] (n : ℕ) : Group.FG (lowerFactor G n) := by
  induction n with
  | zero =>
    unfold lowerFactor
    rw [Subgroup.lowerCentralSeries_zero,←MonoidHom.range_eq_map]
    infer_instance
  | succ n ih =>
    let N := (⊤ : Subgroup G).lowerCentralSeries (n+1)
    let M := (⊤ : Subgroup G).lowerCentralSeries (n+2)
    let π := QuotientGroup.mk' M
    let σ := QuotientGroup.mk' N
    have hMN : M≤N := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
    let q : (G ⧸ M) →* (G ⧸ N) := QuotientGroup.lift M σ (by
      rw [QuotientGroup.ker_mk']; exact hMN)
    have hq (g : G) : q (π g)=σ g := rfl
    let H := ((⊤ : Subgroup G).lowerCentralSeries n).map π
    let f : H →* lowerFactor G n := {
      toFun := fun h => ⟨q h.val,by
        obtain ⟨g,hg,he⟩ := h.property
        exact ⟨g,hg,by change σ g=q h.val; rw [←he,hq]⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hf : Surjective f := by
      rintro ⟨x,g,hg,rfl⟩
      exact ⟨⟨π g,⟨g,hg,rfl⟩⟩,rfl⟩
    have hker : f.ker.map H.subtype≤Subgroup.center (G ⧸ M) := by
      rintro x ⟨h,hh,rfl⟩
      obtain ⟨g,hg,he⟩ := h.property
      apply lowerFactor_central G (n+1)
      refine ⟨g,?_,he⟩
      have heq : σ g=1 := by
        rw [←hq,he]
        exact congrArg Subtype.val hh
      change g∈N
      rw [←QuotientGroup.ker_mk' N]
      exact heq
    have hcomm : ⁅(⊤ : Subgroup (G ⧸ M)),H⁆=lowerFactor G (n+1) := by
      have hπ : (⊤ : Subgroup G).map π=⊤ :=
        Subgroup.map_top_of_surjective π QuotientGroup.mk_surjective
      change ⁅⊤,((⊤ : Subgroup G).lowerCentralSeries n).map π⁆=
        ((⊤ : Subgroup G).lowerCentralSeries (n+1)).map π
      rw [←hπ,←Subgroup.map_commutator,Subgroup.commutator_comm,
        ←Subgroup.lowerCentralSeries_succ]
    let _ := ih
    have hfg := central_commutator_fg_of_quotient H f hf hker
      (hcomm ▸ lowerFactor_central G (n+1))
    apply (Group.fg_iff_subgroup_fg _).mpr
    rwa [hcomm] at hfg

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_FGExtensions
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

namespace CriticalPercolation

theorem fg_of_kernel_quotient {G Q : Type*} [Group G] [Group Q] [Group.FG Q]
    (f : G →* Q) (hf : Surjective f) [Group.FG f.ker] : Group.FG G := by
  obtain ⟨S,hS,himage⟩ := finite_generating_lifts f hf
  obtain ⟨T,hT,hfinT⟩ := Group.fg_iff.mp (inferInstance : Group.FG f.ker)
  let U := S ∪ f.ker.subtype '' T
  let L := Subgroup.closure U
  have hSle : Subgroup.closure S≤L := Subgroup.closure_mono Set.subset_union_left
  have hker : f.ker≤L := by
    have he : (Subgroup.closure T).map f.ker.subtype=f.ker := by
      rw [hT,←MonoidHom.range_eq_map,Subgroup.subtype_range]
    rw [←he,MonoidHom.map_closure]
    exact Subgroup.closure_mono Set.subset_union_right
  have htop : L=⊤ := by
    apply top_unique
    intro g _
    have hg : f g∈(Subgroup.closure S).map f := by rw [himage]; trivial
    obtain ⟨a,ha,he⟩ := hg
    have hz : a⁻¹*g∈f.ker := by
      change f (a⁻¹*g)=1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    simpa using L.mul_mem (hSle ha) (hker hz)
  exact Group.fg_iff.mpr ⟨U,htop,hS.union (hfinT.image _)⟩

theorem abelian_subgroup_fg {A : Type*} [CommGroup A] [Group.FG A]
    (H : Subgroup A) : Group.FG H := by
  let K := H.toAddSubgroup.toIntSubmodule
  let _ : Module.Finite ℤ (Additive A) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let _ : AddGroup.FG K := Module.Finite.iff_addGroup_fg.mp inferInstance
  let e : Multiplicative K ≃* H := {
    toFun := fun a => ⟨a.toAdd.val.toMul,a.toAdd.property⟩
    invFun := fun h => Multiplicative.ofAdd ⟨Additive.ofMul h.val,h.property⟩
    left_inv := by intro a; rfl
    right_inv := by intro h; rfl
    map_mul' := by intros; rfl }
  exact Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_NilpotentSubgroupFG
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

namespace CriticalPercolation

theorem nilpotent_subgroup_fg (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] (J : Subgroup G) : Group.FG J := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => J ⊓ (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hn : Group.FG (L (n+1))) : Group.FG (L n) := by
    let F := lowerFactor G n
    let _ : CommGroup F := {
      (inferInstance : Group F) with
      mul_comm := fun a b => Subtype.ext
        (Subgroup.mem_center_iff.mp (lowerFactor_central G n b.property) a.val) }
    let _ : Group.FG F := lowerFactor_fg G n
    let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property.2,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    let _ : Group.FG f.range := abelian_subgroup_fg f.range
    let _ : Group.FG (L (n+1)) := hn
    have hemem (x : L n) : x∈f.ker ↔ x.val∈(⊤ : Subgroup G).lowerCentralSeries (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃* f.ker := {
      toFun := fun x => ⟨⟨x.val,⟨x.property.1,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property.2⟩⟩,
        (hemem _).mpr x.property.2⟩
      invFun := fun x => ⟨x.val.val,⟨x.val.property.1,(hemem _).mp x.property⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_mul' := by intros; rfl }
    let _ : Group.FG f.ker := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
    have he : f.rangeRestrict.ker=f.ker := by
      ext x
      change f.rangeRestrict x=1 ↔ f x=1
      exact Subtype.ext_iff
    let _ : Group.FG f.rangeRestrict.ker := he.symm ▸ (inferInstance : Group.FG f.ker)
    exact fg_of_kernel_quotient f.rangeRestrict f.rangeRestrict_surjective
  have base : Group.FG (L c) := by
    have he : L c=⊥ := by simp [L,hc]
    rw [he]
    infer_instance
  have hall : ∀ k, Group.FG (L (c-k)) := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      by_cases hk : k < c
      · have he : c-k=(c-(k+1))+1 := by omega
        rw [he] at ih
        exact step _ ih
      · simpa [Nat.sub_eq_zero_of_le (by omega : c≤k),
          Nat.sub_eq_zero_of_le (by omega : c≤k+1)] using ih
  have h := hall c
  simpa [L] using h

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_GraphApproximateNeighborhoods
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
attribute [-simp] _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.mem_around
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

lemma iso_reachBall_image (g : Γ ≃g Γ) (o : X) (r : ℕ) :
    g '' reachBall Γ o r=reachBall Γ (g o) r := by
  apply Set.Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact iso_reachBall Γ g hy
  · intro x hx
    refine ⟨g.symm x,?_,g.apply_symm_apply x⟩
    simpa using iso_reachBall Γ g.symm hx

lemma reachBall_ncard_eq (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o x : X) (r : ℕ) :
    (reachBall Γ x r).ncard=(reachBall Γ o r).ncard := by
  obtain ⟨g,rfl⟩ := ht o x
  rw [←iso_reachBall_image Γ g o r,Set.ncard_image_of_injective _ g.injective]

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

lemma reachBall_packing (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (r K : ℕ)
    (hd : (reachBall Γ o (5*r)).ncard≤K*(reachBall Γ o r).ncard) :
    ∃ F : Finset X, (↑F : Set X)⊆reachBall Γ o (4*r) ∧ F.card≤K ∧
      ∀ u∈reachBall Γ o (4*r), ∃ v∈F, u∈reachBall Γ v (2*r) := by
  let A := (reachBall_finite Γ hl o (4*r)).toFinset
  let C : Finset (Finset X) := A.powerset.filter
    (fun F => (F : Set X).PairwiseDisjoint (fun v => reachBall Γ v r))
  obtain ⟨F,hFmax⟩ := C.exists_maximal <| Finset.filter_nonempty_iff.mpr
    ⟨∅,Finset.empty_mem_powerset _,by simp⟩
  simp only [C,Finset.mem_filter,Finset.mem_powerset] at hFmax
  obtain ⟨hFA,hF⟩ := hFmax.1
  have hFo : (F : Set X)⊆reachBall Γ o (4*r) := by
    intro u hu
    exact (reachBall_finite Γ hl o (4*r)).mem_toFinset.mp (hFA hu)
  have hsub : (⋃ u∈(F : Set X), reachBall Γ u r) ⊆ reachBall Γ o (5*r) := by
    intro v hv
    obtain ⟨u,hu,hv⟩ := Set.mem_iUnion₂.mp hv
    simpa only [show 4*r+r=5*r by omega] using reachBall_add Γ (hFo hu) hv
  have hcount : F.card*(reachBall Γ o r).ncard≤(reachBall Γ o (5*r)).ncard := by
    calc
      F.card*(reachBall Γ o r).ncard = ∑ u∈F, (reachBall Γ u r).ncard := by
        symm
        apply Finset.sum_const_nat
        intro u _
        exact reachBall_ncard_eq Γ ht o u r
      _ = (⋃ u∈(F : Set X), reachBall Γ u r).ncard := by
        rw [(F.finite_toSet).ncard_biUnion (fun u _ => reachBall_finite Γ hl u r) hF,
          finsum_mem_coe_finset]
      _ ≤ (reachBall Γ o (5*r)).ncard := Set.ncard_le_ncard hsub (reachBall_finite Γ hl o _)
  have hpos : 0<(reachBall Γ o r).ncard :=
    (Set.ncard_pos (reachBall_finite Γ hl o r)).mpr ⟨o,reachBall_self Γ o r⟩
  refine ⟨F,hFo,le_of_mul_le_mul_right (hcount.trans hd) hpos,?_⟩
  intro u hu
  by_cases huF : u∈F
  · exact ⟨u,huF,reachBall_self Γ u _⟩
  by_cases! H : ∀ v∈F, Disjoint (reachBall Γ u r) (reachBall Γ v r)
  · refine False.elim (hFmax.not_gt ?_ (Finset.ssubset_insert huF))
    rw [Finset.insert_subset_iff,Finset.coe_insert]
    exact ⟨⟨(reachBall_finite Γ hl o (4*r)).mem_toFinset.mpr hu,hFA⟩,
      hF.insert (fun v hv _ => H v hv)⟩
  · simp_rw [Set.not_disjoint_iff] at H
    obtain ⟨v,hv,w,hwu,hwv⟩ := H
    refine ⟨v,hv,?_⟩
    simpa only [show r+r=2*r by omega] using
      reachBall_add Γ hwv (reachBall_symm Γ hwu)

lemma displacement_cover_of_doubling (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (r K : ℕ)
    (hd : (reachBall Γ o (5*r)).ncard≤K*(reachBall Γ o r).ncard) :
    CovBySMul (Γ ≃g Γ) (K : ℝ) (displacement Γ o (4*r)) (displacement Γ o (2*r)) := by
  obtain ⟨F,hFo,hFK,hcover⟩ := reachBall_packing Γ hl ht o r K hd
  have hex : ∀ v : F, ∃ φ : Γ ≃g Γ, φ o=v.val := fun v => ht o v.val
  choose φ hφ using hex
  let H := Finset.univ.image φ
  have hH : H.card≤K := (Finset.card_image_le).trans (by simpa using hFK)
  refine ⟨H,by exact_mod_cast hH,?_⟩
  intro ψ hψ
  obtain ⟨v,hv,huv⟩ := hcover (ψ o) hψ
  let c := φ ⟨v,hv⟩
  have hc : c∈H := Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩
  have hco : c o=v := hφ ⟨v,hv⟩
  have hrem : c⁻¹*ψ∈displacement Γ o (2*r) := by
    have hh := iso_reachBall Γ c.symm huv
    rw [←hco] at hh
    change c.symm (ψ o)∈reachBall Γ o (2*r)
    simpa using hh
  change ψ∈(H : Set (Γ ≃g Γ))*displacement Γ o (2*r)
  exact Set.mem_mul.mpr ⟨c,hc,c⁻¹*ψ,hrem,by simp⟩

lemma displacement_approximate_of_doubling (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (r K : ℕ)
    (hd : (reachBall Γ o (5*r)).ncard≤K*(reachBall Γ o r).ncard) :
    IsApproximateSubgroup (K : ℝ) (displacement Γ o (2*r)) where
  one_mem := one_mem_displacement Γ o _
  inv_eq_self := by
    ext φ
    change φ⁻¹∈displacement Γ o (2*r) ↔ φ∈displacement Γ o (2*r)
    exact displacement_inv Γ
  sq_covBySMul := by
    apply (displacement_cover_of_doubling Γ hl ht o r K hd).subset_left
    rw [pow_two]
    simpa only [show 2*r+2*r=4*r by omega] using displacement_mul_subset Γ o (2*r) (2*r)

theorem compact_open_approximate_scales
    [TopologicalSpace X] [DiscreteTopology X]
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
    ∀ R : ℕ, ∃ n≥R, IsCompact (displacement Γ o (2*n)) ∧
      IsOpen (displacement Γ o (2*n)) ∧
      IsApproximateSubgroup (5^(d+1) : ℝ) (displacement Γ o (2*n)) := by
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  dsimp only
  intro R
  obtain ⟨n,hn,hd⟩ := sparse_polynomial_doubling_scales
    (fun n => (reachBall Γ o n).ncard)
    (fun r s hrs => Set.ncard_le_ncard (reachBall_mono Γ o hrs) (reachBall_finite Γ hl o s))
    (fun n => (Set.ncard_pos (reachBall_finite Γ hl o n)).mpr ⟨o,reachBall_self Γ o n⟩)
    d hpoly R
  refine ⟨n,hn,compact_displacement Γ hc hl o _,open_displacement Γ o _,?_⟩
  exact_mod_cast displacement_approximate_of_doubling Γ hl ht o n (5^(d+1)) hd

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_GraphGeneratingNeighborhood
attribute [-simp] _root_.OAI.CriticalPercolation.HomogeneousAnalysis.Geometry.mem_around
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

theorem compact_open_generating_approximate_powers
    [TopologicalSpace X] [DiscreteTopology X]
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
    let S := displacement Γ o 1
    IsCompact S ∧ IsOpen S ∧ (1 : Γ ≃g Γ)∈S ∧ S⁻¹=S ∧
      Subgroup.closure S=⊤ ∧
      ∀ R : ℕ, ∃ n≥R, IsCompact (S^n) ∧ IsOpen (S^n) ∧
        IsApproximateSubgroup (5^(d+1) : ℝ) (S^n) := by
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  dsimp only
  refine ⟨compact_displacement Γ hc hl o 1,open_displacement Γ o 1,
    one_mem_displacement Γ o 1,?_,displacement_generates Γ hc ht o,?_⟩
  · ext g
    change g⁻¹∈displacement Γ o 1 ↔ g∈displacement Γ o 1
    exact displacement_inv Γ
  · intro R
    obtain ⟨n,hn,hcomp,hopen,happrox⟩ :=
      compact_open_approximate_scales Γ hc hl ht o d hpoly (max R 1)
    have he : displacement Γ o (2*n)=displacement Γ o 1^(2*n) := by
      have hpos : 0<2*n := by omega
      simpa only [Nat.sub_add_cancel (show 1≤2*n by omega)] using
        displacement_eq_pow Γ ht o (2*n-1)
    refine ⟨2*n,by omega,?_,?_,?_⟩ <;> rwa [←he]

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_TopologicalClassificationBoundary
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function MeasureTheory Topology
open scoped Classical ENNReal Pointwise

namespace CriticalPercolation
namespace GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

lemma uniform_compact_approximate_powers_of_sparse_polynomial
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    HasUniformCompactApproximatePowers Γ (5^(d+1)) := by
  let _ : TopologicalSpace X := ⊥
  let _ : DiscreteTopology X := ⟨rfl⟩
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  exact ⟨displacement Γ o 1,
    compact_open_generating_approximate_powers Γ hc hl ht o d hpoly⟩

end GraphTopology
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem main_failure_topological_classification_counterexample [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1)
    (hper : G.law G.criticalProbability G.percolates≠0) (o : V) :
    ∃ d : ℕ, 2≤d ∧ ∃ C : ℕ,
      (G.orbitPower o (2*C+1)).Connected ∧
      (MulAction.orbit G.Aut o).Infinite ∧
      (∀ u, ((G.orbitPower o (2*C+1)).neighborSet u).Finite) ∧
      (∀ u v, ∃ g : G.orbitPower o (2*C+1) ≃g G.orbitPower o (2*C+1), g u=v) ∧
      (∀ R : ℕ, ∃ n≥R, ∀ u : MulAction.orbit G.Aut o,
        (GraphTopology.reachBall (G.orbitPower o (2*C+1)) u n).ncard≤n^(d+1)) ∧
      GraphTopology.HasUniformCompactApproximatePowers
        (G.orbitPower o (2*C+1)) (5^(d+2)) ∧
      ¬GraphTopology.HasCompactOpenVirtuallyNilpotentQuotient
        (G.orbitPower o (2*C+1)) := by
  obtain ⟨hg,_,d,hd,hpoly⟩ := G.main_failure_sparse_polynomial hc hl hq hpc hper
  obtain ⟨C,Λ,hfg,hconn,hinf,hloc,htrans,hker,hreps,hscales⟩ :=
    G.sparse_polynomial_faithful_orbital_model hc hl hq o d hpoly
  let _ : Group.FG Λ := hfg
  have ht : ∀ u v, ∃ g : G.orbitPower o (2*C+1) ≃g G.orbitPower o (2*C+1), g u=v := by
    intro u v
    obtain ⟨g,hg⟩ := htrans u v
    exact ⟨g.val,hg⟩
  have hpow : GraphTopology.HasUniformCompactApproximatePowers
      (G.orbitPower o (2*C+1)) (5^(d+2)) := by
    apply GraphTopology.uniform_compact_approximate_powers_of_sparse_polynomial
      _ hconn hloc ht (⟨o,MulAction.mem_orbit_self o⟩ : MulAction.orbit G.Aut o) (d+1)
    intro R
    obtain ⟨n,hn,hh⟩ := hscales R
    exact ⟨n,hn,hh _⟩
  refine ⟨d,hd,C,hconn,hinf,hloc,ht,hscales,hpow,?_⟩
  rintro ⟨H,hn,hcomp,hopen,N,hnil,hN⟩
  let _ := hn
  let _ := hnil
  obtain ⟨S,hS,hcover⟩ := hreps
  exact hper (G.critical_null_of_compact_open_orbital_quotient hc hl hg o (2*C+1)
    hconn Λ S hS hcover H N hN ⟨hcomp,hopen⟩ hpc)

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetBallIndex
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
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_FiniteKernelNilpotent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function

namespace CriticalPercolation.CompactQuotient
variable {A B : Type*} [Group A] [Group B]

theorem virtuallyNilpotent_of_finite_kernel (f : A →* B)
    (hfin : (f.ker : Set A).Finite) (hB : Group.IsVirtuallyNilpotent B) :
    Group.IsVirtuallyNilpotent A := by
  let _ : Finite f.ker := hfin.to_subtype
  obtain ⟨N,hN,hNi⟩ := hB
  let _ := hN
  let _ := hNi
  let c : A →* MulAut f.ker := MulAut.conjNormal
  let P := N.comap f ⊓ c.ker
  let _ : c.ker.FiniteIndex := inferInstance
  let _ : (N.comap f).FiniteIndex := by
    constructor
    rw [N.index_comap]
    exact (inferInstance : (N.subgroupOf f.range).FiniteIndex).index_ne_zero
  let _ : P.FiniteIndex := inferInstance
  let j : P →* N :=
    { toFun := fun a => ⟨f a.val,a.property.1⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a.val b.val) }
  have hker : j.ker≤Subgroup.center P := by
    intro a ha
    have haf : (a : A)∈f.ker := by
      exact congrArg Subtype.val ha
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    have hb : c b.val=1 := b.property.2
    have he := congrArg (fun e : MulAut f.ker => (e ⟨a.val,haf⟩).val) hb
    change b.val*a.val*b.val⁻¹=a.val at he
    exact (mul_inv_eq_iff_eq_mul).mp he
  exact ⟨P,Subgroup.isNilpotent_of_ker_le_center j hker,inferInstance⟩

end CriticalPercolation.CompactQuotient
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_GraphQuotientGrowth
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_GraphQuotientPolynomial
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
-- module Solutions.Q228_CP.CriticalPercolation_Growth_PolynomialGrowthDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

lemma cyclic_inter_lower_bound (S : Finset A) (h1 : (1 : A) ∈ S)
    (H : Subgroup A) (a : A) (ha : a ∈ H) (ha0 : orderOf a = 0)
    (L : ℕ) (haL : a ∈ S ^ L) (n : ℕ) :
    n + 1 ≤ ((S ^ (L*n)).filter (fun x => x ∈ H)).card := by
  have hinj : Injective (fun i : ℕ => a^i) := fun _ _ h =>
    (pow_inj_iff_of_orderOf_eq_zero ha0).mp h
  calc
    n+1 = ((Finset.range (n+1)).image (fun i => a^i)).card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    _ ≤ ((S ^ (L*n)).filter (fun x => x ∈ H)).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      refine Finset.mem_filter.mpr ⟨?_,H.pow_mem ha i⟩
      apply Finset.pow_subset_pow_right h1 (Nat.mul_le_mul_left L hi')
      simpa only [pow_mul] using Finset.pow_mem_pow (n := i) haL

lemma quotient_linear_packing (S : Finset A) (h1 : (1 : A) ∈ S)
    (H : Subgroup A) [H.Normal] (a : A) (ha : a ∈ H) (ha0 : orderOf a = 0)
    (L : ℕ) (haL : a ∈ S ^ L) (n : ℕ) :
    ((S.image (QuotientGroup.mk' H)) ^ n).card * (n+1) ≤
      (S ^ ((L+1)*n)).card := by
  calc
    _ ≤ ((S^n).image (QuotientGroup.mk' H)).card *
        ((S ^ (L*n)).filter (fun x => x ∈ H)).card := by
      rw [Finset.image_pow]
      exact Nat.mul_le_mul_left _ (cyclic_inter_lower_bound S h1 H a ha ha0 L haL n)
    _ ≤ (S ^ (n + L*n)).card := Finset.card_pow_quotient_mul_pow_inter_subgroup_le
    _ = (S ^ ((L+1)*n)).card := by congr 2; ring

theorem quotient_degree_descent (S : Finset A) (h1 : (1 : A) ∈ S)
    (H : Subgroup A) [H.Normal] (a : A) (ha : a ∈ H) (ha0 : orderOf a = 0)
    (L : ℕ) (haL : a ∈ S ^ L) (d : ℕ) (hg : HasDegree S (d+1)) :
    HasDegree (S.image (QuotientGroup.mk' H)) d := by
  obtain ⟨C,hC⟩ := hg
  refine ⟨C * (2*(L+1))^(d+1),?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hL : 0 < L+1 := by omega
  have hnr : (L+1)*n ≤ r := by
    simpa only [n, Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hn : max R 1 ≤ n := (Nat.le_div_iff_mul_le hL).mpr (by simpa [Nat.mul_comm] using hr)
  have hn1 : 1 ≤ n := (le_max_right R 1).trans hn
  have hrn : r ≤ (2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r hL
    change r < (L+1)*(n+1) at hlt
    have hh : (L+1)*(n+1) ≤ (2*(L+1))*n := by nlinarith
    exact hlt.le.trans hh
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  have hb : ((S.image (QuotientGroup.mk' H))^n).card * n ≤
      (C*(2*(L+1))^(d+1)*n^d)*n := by
    calc
      _ ≤ ((S.image (QuotientGroup.mk' H))^n).card * (n+1) :=
        Nat.mul_le_mul_left _ (Nat.le_succ n)
      _ ≤ (S ^ ((L+1)*n)).card := quotient_linear_packing S h1 H a ha ha0 L haL n
      _ ≤ (S ^ r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 hnr)
      _ ≤ C*r^(d+1) := hbound
      _ ≤ C*((2*(L+1))*n)^(d+1) := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn (d+1))
      _ = (C*(2*(L+1))^(d+1)*n^d)*n := by rw [mul_pow,pow_succ n]; ac_rfl
  exact Nat.le_of_mul_le_mul_right hb (by omega : 0<n)

theorem finite_of_degree_zero (S : Finset A) (h1 : (1 : A) ∈ S)
    (hgen : Subgroup.closure (S : Set A) = ⊤) (hg : HasDegree S 0) : Finite A := by
  rcases finite_or_infinite A with hA | hA
  · exact hA
  let _ := hA
  obtain ⟨C,hC⟩ := hg
  obtain ⟨n,hn,hbound⟩ := hC C
  have hinf : (Subgroup.closure (S : Set A) : Set A).Infinite := by
    simpa only [hgen, Subgroup.coe_top] using (Set.infinite_univ : (Set.univ : Set A).Infinite)
  have hlow := Finset.add_one_le_card_pow h1 hinf n
  simp only [pow_zero,mul_one] at hbound
  omega

omit [DecidableEq A] [DecidableEq B] in

theorem virtuallyNilpotent_of_central_kernel (f : A →* B)
    (hc : f.ker ≤ Subgroup.center A) (hB : Group.IsVirtuallyNilpotent B) :
    Group.IsVirtuallyNilpotent A := by
  obtain ⟨N,hN,hNi⟩ := hB
  let _ := hN
  let _ := hNi
  let P := N.comap f
  let _ : P.FiniteIndex := by
    constructor
    rw [N.index_comap]
    exact (inferInstance : (N.subgroupOf f.range).FiniteIndex).index_ne_zero
  let j : P →* N :=
    { toFun := fun a => ⟨f a.val,a.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a.val b.val) }
  have hker : j.ker ≤ Subgroup.center P := by
    intro a ha
    have haf : (a : A) ∈ f.ker := congrArg Subtype.val ha
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hc haf)) b.val)
  exact ⟨P,Subgroup.isNilpotent_of_ker_le_center j hker,inferInstance⟩

omit [DecidableEq A] in

theorem virtuallyNilpotent_of_finiteIndex (H : Subgroup A) [H.FiniteIndex]
    (hH : Group.IsVirtuallyNilpotent H) : Group.IsVirtuallyNilpotent A := by
  obtain ⟨N,hN,hNi⟩ := hH
  let _ := hN
  refine ⟨N.map H.subtype,Group.nilpotent_of_surjective
    (H.subtype.subgroupMap N) (H.subtype.subgroupMap_surjective N),?_⟩
  constructor
  rw [Subgroup.index_map_subtype]
  exact mul_ne_zero hNi.index_ne_zero (inferInstance : H.FiniteIndex).index_ne_zero

lemma finite_subset_word_ball (S : Finset A) (h1 : (1 : A) ∈ S) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure (S : Set A)=⊤) (T : Finset A) :
    ∃ L : ℕ, T ⊆ S^L := by
  have hword : ∀ a : A, ∃ n : ℕ, a ∈ S^n := fun a =>
    exists_mem_pow S hsym (by rw [hgen]; trivial)
  choose l hl using hword
  refine ⟨T.sup l,fun a ha => ?_⟩
  exact Finset.pow_subset_pow_right h1 (Finset.le_sup ha) (hl a)

theorem degree_of_injective (S : Finset A) (h1 : (1 : A) ∈ S) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure (S : Set A)=⊤) (f : B →* A) (hf : Injective f)
    (T : Finset B) (d : ℕ) (hg : HasDegree S d) : HasDegree T d := by
  obtain ⟨L,hL⟩ := finite_subset_word_ball S h1 hsym hgen (T.image f)
  obtain ⟨C,hC⟩ := hg
  refine ⟨C*(2*(L+1))^d,?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hLpos : 0 < L+1 := by omega
  have hnr : (L+1)*n ≤ r := by
    simpa only [n,Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hn : max R 1 ≤ n := (Nat.le_div_iff_mul_le hLpos).mpr (by simpa [Nat.mul_comm] using hr)
  have hn1 : 1 ≤ n := (le_max_right R 1).trans hn
  have hrn : r ≤ (2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r hLpos
    change r < (L+1)*(n+1) at hlt
    have hh : (L+1)*(n+1) ≤ (2*(L+1))*n := by nlinarith
    exact hlt.le.trans hh
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  calc
    (T^n).card = ((T^n).image f).card := (Finset.card_image_of_injective _ hf).symm
    _ = ((T.image f)^n).card := by rw [Finset.image_pow]
    _ ≤ ((S^L)^n).card := Finset.card_le_card (Finset.pow_subset_pow_left hL)
    _ = (S^(L*n)).card := by rw [pow_mul]
    _ ≤ (S^r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 (by nlinarith))
    _ ≤ C*r^d := hbound
    _ ≤ C*((2*(L+1))*n)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
    _ = C*(2*(L+1))^d*n^d := by rw [mul_pow,mul_assoc]

lemma hasPolynomialDegree_iff (d : ℕ) : HasPolynomialDegree A d ↔
    ∃ S : Finset A, (1 : A)∈S ∧ S⁻¹=S ∧
      Subgroup.closure (S : Set A)=⊤ ∧ HasDegree S d := by
  constructor
  · rintro ⟨S,hSf,h1,hsym,hgen,C,hC⟩
    refine ⟨hSf.toFinset,by simpa using h1,?_,by simpa using hgen,C,?_⟩
    · apply Finset.coe_injective
      simpa only [Finset.coe_inv,Set.Finite.coe_toFinset] using hsym
    · intro R
      obtain ⟨n,hn,hb⟩ := hC R
      refine ⟨n,hn,?_⟩
      have hb' : ((hSf.toFinset : Set A)^n).ncard ≤ C*n^d := by
        simpa only [Set.Finite.coe_toFinset] using hb
      simpa only [← Finset.coe_pow,Set.ncard_coe_finset] using hb'
  · rintro ⟨S,h1,hsym,hgen,C,hC⟩
    refine ⟨S,S.finite_toSet,h1,?_,hgen,C,?_⟩
    · simpa only [Finset.coe_inv] using congrArg (fun T : Finset A => (T : Set A)) hsym
    · intro R
      obtain ⟨n,hn,hb⟩ := hC R
      exact ⟨n,hn,by simpa only [← Finset.coe_pow,Set.ncard_coe_finset] using hb⟩

omit [DecidableEq A] in
lemma HasPolynomialDegree.fg {d : ℕ} (h : HasPolynomialDegree A d) : Group.FG A := by
  obtain ⟨S,hS,_,_,hgen,_⟩ := h
  exact Group.fg_iff.mpr ⟨S,hgen,hS⟩

lemma exists_symmetric_generators [Group.FG A] :
    ∃ S : Finset A, (1 : A)∈S ∧ S⁻¹=S ∧ Subgroup.closure (S : Set A)=⊤ := by
  obtain ⟨F,hF⟩ := Group.FG.out (G := A)
  let S := insert 1 (F ∪ F⁻¹)
  refine ⟨S,by simp [S],?_,?_⟩
  · ext a
    simp only [S,Finset.mem_inv',Finset.mem_insert,Finset.mem_union,inv_eq_one,inv_inv]
    tauto
  · apply top_unique
    rw [← hF]
    apply Subgroup.closure_mono
    intro a ha
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ ha)

theorem HasPolynomialDegree.of_injective {d : ℕ} (h : HasPolynomialDegree A d)
    (f : B →* A) (hf : Injective f) [Group.FG B] : HasPolynomialDegree B d := by
  obtain ⟨S,h1,hs,hgen,hg⟩ := (hasPolynomialDegree_iff d).mp h
  obtain ⟨T,hT1,hTs,hTgen⟩ := exists_symmetric_generators (A := B)
  exact (hasPolynomialDegree_iff d).mpr ⟨T,hT1,hTs,hTgen,
    degree_of_injective S h1 hs hgen f hf T d hg⟩

theorem HasPolynomialDegree.finiteIndex_subgroup {d : ℕ} (h : HasPolynomialDegree A d)
    (H : Subgroup A) [H.FiniteIndex] : HasPolynomialDegree H d := by
  let _ := h.fg
  exact h.of_injective H.subtype H.subtype_injective

theorem HasPolynomialDegree.finite (h : HasPolynomialDegree A 0) : Finite A := by
  obtain ⟨S,h1,_,hgen,hg⟩ := (hasPolynomialDegree_iff 0).mp h
  exact finite_of_degree_zero S h1 hgen hg

theorem HasPolynomialDegree.quotient_descent {d : ℕ} (h : HasPolynomialDegree A (d+1))
    (H : Subgroup A) [H.Normal] (a : A) (ha : a ∈ H) (ha0 : orderOf a=0) :
    HasPolynomialDegree (A ⧸ H) d := by
  obtain ⟨S,h1,hs,hgen,hg⟩ := (hasPolynomialDegree_iff (d+1)).mp h
  obtain ⟨L,haL⟩ := exists_mem_pow S hs (a := a) (by rw [hgen]; trivial)
  apply (hasPolynomialDegree_iff d).mpr
  refine ⟨S.image (QuotientGroup.mk' H),?_,?_,?_,
    quotient_degree_descent S h1 H a ha ha0 L haL d hg⟩
  · exact Finset.mem_image.mpr ⟨1,h1,map_one _⟩
  · rw [← Finset.image_inv,hs]
  · rw [Finset.coe_image,← MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective _ QuotientGroup.mk_surjective

omit [DecidableEq A] in
lemma virtuallyNilpotent_of_finite [Finite A] : Group.IsVirtuallyNilpotent A :=
  ⟨⊥,inferInstance,inferInstance⟩

universe u

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_NormalClosureGrowth
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

lemma not_quadratic_exponential_lower (S : Finset A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree S d) (L : ℕ) (hL : 0<L)
    (hlo : ∀ n : ℕ, 2^n ≤ (S^(L*n^2)).card) : False := by
  obtain ⟨C,hC⟩ := hg
  obtain ⟨N,hN⟩ := eventually_exponential_dominates (C*(4*L)^d) (2*d)
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
      _ ≤ (S^(L*n^2)).card := hlo n
      _ ≤ (S^r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 hnr)
      _ ≤ C*r^d := hbound
      _ ≤ C*((4*L)*n^2)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
      _ = (C*(4*L)^d)*n^(2*d) := by rw [mul_pow,pow_mul]; ring
  exact (not_le_of_gt (hN n ((le_max_left N 1).trans hn))) hu

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

lemma binaryProducts_subset_pow (S : Finset A) (h1 : (1:A)∈S)
    (g : ℕ → A) (L : ℕ) (hg : ∀ n, g n∈S^(L*(n+1))) :
    ∀ n, binaryProducts g n ⊆ S^(L*n^2) := by
  intro n
  induction n with
  | zero => simp [binaryProducts]
  | succ n ih =>
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.pow_subset_pow_right h1 (Nat.mul_le_mul_left L (Nat.pow_le_pow_left (Nat.le_succ n) 2)) (ih hx)
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      have hlen : L*(n+1)+L*n^2 ≤ L*(n+1)^2 := by
        calc
          _ = L*(n+1+n^2) := by ring
          _ ≤ L*(n+1)^2 := Nat.mul_le_mul_left L (by nlinarith)
      apply Finset.pow_subset_pow_right h1 hlen
      rw [pow_add]
      exact Finset.mul_mem_mul (hg n) (ih hy)

theorem no_linear_word_strict_chain (S : Finset A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree S d) (K : ℕ → Subgroup A) (hK : Monotone K)
    (g : ℕ → A) (hgin : ∀ n, g n∈K (n+1)) (hgout : ∀ n, g n∉K n)
    (L : ℕ) (hL : 0<L) (hword : ∀ n, g n∈S^(L*(n+1))) : False := by
  apply not_quadratic_exponential_lower S h1 d hg L hL
  intro n
  rw [←binaryProducts_card K hK g hgin hgout n]
  exact Finset.card_le_card (binaryProducts_subset_pow S h1 g L hword n)

lemma mem_boundedConjugates (S F : Finset A) (n : ℕ) {x : A} :
    x∈boundedConjugates S F n ↔ ∃ g∈S^n, ∃ f∈F, g*f*g⁻¹=x := by
  simp [boundedConjugates, MulAut.conj_apply]

lemma boundedConjugates_mono (S F : Finset A) (h1 : (1:A)∈S) :
    Monotone (boundedConjugates S F) := by
  intro m n h x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F m).mp hx
  exact (mem_boundedConjugates S F n).mpr
    ⟨g,Finset.pow_subset_pow_right h1 h hg,f,hf,rfl⟩

lemma conjugateStage_mono (S F : Finset A) (h1 : (1:A)∈S) :
    Monotone (conjugateStage S F) := by
  intro m n h
  exact Subgroup.closure_mono (boundedConjugates_mono S F h1 h)

lemma boundedConjugates_subset_pow (S F : Finset A) (hsym : S⁻¹=S)
    (L : ℕ) (hF : F⊆S^L) (n : ℕ) :
    boundedConjugates S F n ⊆ S^(2*n+L) := by
  intro x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hx
  have hgi : g⁻¹∈S^n := by
    rw [←hsym,inv_pow]
    exact Finset.inv_mem_inv hg
  have he : 2*n+L=n+L+n := by omega
  rw [he,pow_add,pow_add]
  exact Finset.mul_mem_mul (Finset.mul_mem_mul hg (hF hf)) hgi

lemma conjugateStage_le_normalClosure (S F : Finset A) (n : ℕ) :
    conjugateStage S F n ≤ Subgroup.normalClosure (F : Set A) := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hx
  exact Subgroup.normalClosure_normal.conj_mem f (Subgroup.subset_normalClosure hf) g

lemma conjugateStage_conj_generator (S F : Finset A) (n : ℕ)
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
      exact Finset.mul_mem_mul hs hg
    · simp [MulAut.conj_apply,mul_assoc]
  exact hmap hx

lemma conjugateStage_normal_of_stationary (S F : Finset A) (hsym : S⁻¹=S)
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
    have hsi : s⁻¹∈S := by rw [←hsym]; exact Finset.inv_mem_inv hs
    have hy := conjugateStage_conj_generator S F n s⁻¹ hsi hx
    rw [he] at hy
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hy

lemma normalClosure_eq_conjugateStage_of_stationary (S F : Finset A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (hgen : Subgroup.closure (S : Set A)=⊤)
    (n : ℕ) (he : conjugateStage S F (n+1)=conjugateStage S F n) :
    Subgroup.normalClosure (F : Set A)=conjugateStage S F n := by
  let _ := conjugateStage_normal_of_stationary S F hsym hgen n he
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro f hf
    apply Subgroup.subset_closure
    exact (mem_boundedConjugates S F n).mpr
      ⟨1,Finset.one_mem_pow h1,f,hf,by simp⟩
  · exact conjugateStage_le_normalClosure S F n

theorem exists_conjugateStage_stationary (S F : Finset A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (d : ℕ) (hg : HasDegree S d)
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
  apply no_linear_word_strict_chain S h1 d hg (conjugateStage S F)
    (conjugateStage_mono S F h1) g (fun n => Subgroup.subset_closure (hgin n))
    hgout (L+2) (by omega)
  intro n
  apply Finset.pow_subset_pow_right h1 (show 2*(n+1)+L≤(L+2)*(n+1) by nlinarith)
  exact boundedConjugates_subset_pow S F hsym L hF (n+1) (hgin n)

theorem normalClosure_fg_of_sparse_growth (S F : Finset A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (hgen : Subgroup.closure (S : Set A)=⊤)
    (d : ℕ) (hg : HasDegree S d) : (Subgroup.normalClosure (F : Set A)).FG := by
  obtain ⟨L,hF⟩ := finite_subset_word_ball S h1 hsym hgen F
  obtain ⟨n,hn⟩ := exists_conjugateStage_stationary S F h1 hsym d hg L hF
  rw [normalClosure_eq_conjugateStage_of_stationary S F h1 hsym hgen n hn]
  exact (Subgroup.fg_iff _).mpr ⟨(boundedConjugates S F n : Set A),rfl,Finset.finite_toSet _⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_IntegerKernelGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma integer_kernel_normalClosure (S : Finset A)
    (hgen : Subgroup.closure (S : Set A)=⊤)
    (f : A →* Multiplicative ℤ) (a : A) (ha : f a=Multiplicative.ofAdd 1) :
    f.ker=Subgroup.normalClosure
      ((S.image (fun s => s*a^(-Multiplicative.toAdd (f s)))) : Set A) := by
  let F := S.image (fun s => s*a^(-Multiplicative.toAdd (f s)))
  let N := Subgroup.normalClosure (F : Set A)
  have hN : N≤f.ker := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hy
    change f (s*a^(-Multiplicative.toAdd (f s)))=1
    rw [map_mul,map_zpow,ha]
    apply Multiplicative.toAdd.injective
    simp
  let q := QuotientGroup.mk' N
  have hqa : ∀ x : A, q x=(q a)^Multiplicative.toAdd (f x) := by
    intro x
    have hx : x∈Subgroup.closure (S : Set A) := hgen.symm ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      have hm : x*a^(-Multiplicative.toAdd (f x))∈N :=
        Subgroup.subset_normalClosure (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
      have he := (QuotientGroup.eq_one_iff _).mpr hm
      change q (x*a^(-Multiplicative.toAdd (f x)))=1 at he
      rw [map_mul,map_zpow,zpow_neg] at he
      exact mul_inv_eq_one.mp he
    | one => simp
    | mul x y _ _ hx hy =>
      rw [map_mul,hx,hy,←zpow_add,map_mul,toAdd_mul]
    | inv x _ hx =>
      rw [map_inv,hx,map_inv,toAdd_inv,zpow_neg]
  apply le_antisymm _ hN
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mp
  change q x=1
  rw [hqa,MonoidHom.mem_ker.mp hx]
  simp

theorem HasPolynomialDegree.integer_kernel_fg {d : ℕ}
    (hg : HasPolynomialDegree A d) (f : A →* Multiplicative ℤ) (hf : Surjective f) :
    Group.FG f.ker := by
  obtain ⟨S,h1,hs,hgen,hS⟩ := (hasPolynomialDegree_iff d).mp hg
  obtain ⟨a,ha⟩ := hf (Multiplicative.ofAdd 1)
  rw [integer_kernel_normalClosure S hgen f a ha]
  exact (Group.fg_iff_subgroup_fg _).mpr
    (normalClosure_fg_of_sparse_growth S _ h1 hs hgen d hS)

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_KernelGrowthDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma quotient_word_lower (S : Finset A) (h1 : (1:A)∈S)
    (hgen : Subgroup.closure (S : Set A)=⊤)
    (H : Subgroup A) [H.Normal] [Infinite (A ⧸ H)] (n : ℕ) :
    n+1 ≤ ((S^n).image (QuotientGroup.mk' H)).card := by
  let q := QuotientGroup.mk' H
  have hq1 : (1:A ⧸ H)∈S.image q := Finset.mem_image.mpr ⟨1,h1,map_one q⟩
  have hqgen : Subgroup.closure (S.image q : Set (A ⧸ H))=⊤ := by
    rw [Finset.coe_image,←MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective H)
  have hinf : (Subgroup.closure (S.image q : Set (A ⧸ H)) : Set (A ⧸ H)).Infinite := by
    rw [hqgen,Subgroup.coe_top]
    exact Set.infinite_univ
  rw [Finset.image_pow]
  exact Finset.add_one_le_card_pow hq1 hinf n

lemma subgroup_linear_packing (S : Finset A) (h1 : (1:A)∈S)
    (hgen : Subgroup.closure (S : Set A)=⊤)
    (H : Subgroup A) [H.Normal] [Infinite (A ⧸ H)]
    (T : Finset H) (L : ℕ) (hT : T.image H.subtype ⊆ S^L) (n : ℕ) :
    (T^n).card*(n+1) ≤ (S^((L+1)*n)).card := by
  have hTin : (T^n).image H.subtype ⊆ (S^(L*n)).filter (fun a => a∈H) := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_filter.mpr ⟨?_,b.property⟩
    have he : (b : A)∈(T.image H.subtype)^n := by
      rw [←Finset.image_pow]
      exact Finset.mem_image.mpr ⟨b,hb,rfl⟩
    rw [pow_mul]
    exact Finset.pow_subset_pow_left hT he
  calc
    _ = (n+1)*((T^n).image H.subtype).card := by
      rw [Finset.card_image_of_injective _ H.subtype_injective,Nat.mul_comm]
    _ ≤ ((S^n).image (QuotientGroup.mk' H)).card *
        ((S^(L*n)).filter (fun a => a∈H)).card :=
      Nat.mul_le_mul (quotient_word_lower S h1 hgen H n) (Finset.card_le_card hTin)
    _ ≤ (S^(n+L*n)).card := Finset.card_pow_quotient_mul_pow_inter_subgroup_le
    _ = (S^((L+1)*n)).card := by congr 2; ring

theorem subgroup_degree_descent (S : Finset A) (h1 : (1:A)∈S)
    (hgen : Subgroup.closure (S : Set A)=⊤)
    (H : Subgroup A) [H.Normal] [Infinite (A ⧸ H)]
    (T : Finset H) (L : ℕ) (hT : T.image H.subtype ⊆ S^L)
    (d : ℕ) (hg : HasDegree S (d+1)) : HasDegree T d := by
  obtain ⟨C,hC⟩ := hg
  refine ⟨C*(2*(L+1))^(d+1),?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hL : 0<L+1 := by omega
  have hnr : (L+1)*n ≤ r := by
    simpa only [n,Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hn : max R 1≤n := (Nat.le_div_iff_mul_le hL).mpr (by simpa [Nat.mul_comm] using hr)
  have hn1 : 1≤n := (le_max_right R 1).trans hn
  have hrn : r≤(2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r hL
    change r<(L+1)*(n+1) at hlt
    have hh : (L+1)*(n+1)≤(2*(L+1))*n := by nlinarith
    exact hlt.le.trans hh
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  have hb : (T^n).card*n ≤ (C*(2*(L+1))^(d+1)*n^d)*n := by
    calc
      _ ≤ (T^n).card*(n+1) := Nat.mul_le_mul_left _ (Nat.le_succ n)
      _ ≤ (S^((L+1)*n)).card := subgroup_linear_packing S h1 hgen H T L hT n
      _ ≤ (S^r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 hnr)
      _ ≤ C*r^(d+1) := hbound
      _ ≤ C*((2*(L+1))*n)^(d+1) := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn (d+1))
      _ = (C*(2*(L+1))^(d+1)*n^d)*n := by rw [mul_pow,pow_succ n]; ac_rfl
  exact Nat.le_of_mul_le_mul_right hb (by omega : 0<n)

theorem HasPolynomialDegree.normal_subgroup_descent {d : ℕ}
    (h : HasPolynomialDegree A (d+1)) (H : Subgroup A) [H.Normal]
    [Infinite (A ⧸ H)] [Group.FG H] : HasPolynomialDegree H d := by
  obtain ⟨S,h1,hs,hgen,hg⟩ := (hasPolynomialDegree_iff (d+1)).mp h
  obtain ⟨T,hT1,hTs,hTgen⟩ := exists_symmetric_generators (A := H)
  obtain ⟨L,hL⟩ := finite_subset_word_ball S h1 hs hgen (T.image H.subtype)
  exact (hasPolynomialDegree_iff d).mpr ⟨T,hT1,hTs,hTgen,
    subgroup_degree_descent S h1 hgen H T L hL d hg⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_ExpandingCharacterGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

lemma binaryProducts_map (f : B →* A) (g : ℕ → B) (n : ℕ) :
    (binaryProducts g n).image f = binaryProducts (fun i => f (g i)) n := by
  induction n with
  | zero => simp [binaryProducts]
  | succ n ih =>
    simp only [binaryProducts, Finset.image_union]
    rw [←ih]
    congr 1
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact map_mul f (g n) x

lemma binaryProducts_card_norm_bound
    (φ : A →* Multiplicative ℂ) (g : ℕ → A) (b q : ℝ)
    (hb : 0 < b) (hq : 3 ≤ q)
    (he : ∀ n, ‖Multiplicative.toAdd (φ (g n))‖ = b*q^n) :
    ∀ n, (binaryProducts g n).card=2^n ∧
      ∀ a∈binaryProducts g n,
        2*‖Multiplicative.toAdd (φ a)‖ ≤ b*(q^n-1) := by
  intro n
  induction n with
  | zero =>
    constructor
    · simp [binaryProducts]
    · intro a ha
      have ha1 : a=1 := by simpa [binaryProducts] using ha
      simp [ha1]
  | succ n ih =>
    have hdis : Disjoint (binaryProducts g n)
        ((binaryProducts g n).image (fun x => g n*x)) := by
      apply Finset.disjoint_left.mpr
      intro a ha ha'
      obtain ⟨c,hc,hca⟩ := Finset.mem_image.mp ha'
      have heq : Multiplicative.toAdd (φ (g n)) =
          Multiplicative.toAdd (φ a)-Multiplicative.toAdd (φ c) := by
        rw [←hca,map_mul]
        change Multiplicative.toAdd (φ (g n)) =
          (Multiplicative.toAdd (φ (g n))+Multiplicative.toAdd (φ c))-
            Multiplicative.toAdd (φ c)
        abel
      have hn := norm_sub_le (Multiplicative.toAdd (φ a)) (Multiplicative.toAdd (φ c))
      rw [←heq,he n] at hn
      have haB := ih.2 a ha
      have hcB := ih.2 c hc
      nlinarith
    constructor
    · simp only [binaryProducts,Finset.card_union_of_disjoint hdis,
        Finset.card_image_of_injective _ (mul_right_injective (g n)),ih.1,pow_succ]
      omega
    · intro a ha
      obtain ha|ha := Finset.mem_union.mp ha
      · have haB := ih.2 a ha
        have hpow : q^n ≤ q^(n+1) := by
          rw [pow_succ]
          nlinarith [pow_nonneg (by linarith : 0≤q) n]
        exact haB.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hpow 1) hb.le)
      · obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp ha
        have hn := norm_add_le (Multiplicative.toAdd (φ (g n))) (Multiplicative.toAdd (φ c))
        have hcB := ih.2 c hc
        rw [he n] at hn
        rw [map_mul]
        change 2*‖Multiplicative.toAdd (φ (g n))+Multiplicative.toAdd (φ c)‖≤_
        rw [pow_succ]
        have hqn : 0≤q^n := pow_nonneg (by linarith) n
        have hprod : 3*(b*q^n) ≤ (b*q^n)*q := by
          calc
            3*(b*q^n) = (b*q^n)*3 := mul_comm _ _
            _ ≤ (b*q^n)*q := mul_le_mul_of_nonneg_left hq (mul_nonneg hb.le hqn)
        nlinarith

theorem no_expanding_short_character (S : Finset A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree S d) (f : B →* A) (hf : Injective f)
    (φ : B →* Multiplicative ℂ) (g : ℕ → B) (b q : ℝ)
    (hb : 0<b) (hq : 3≤q)
    (he : ∀ n, ‖Multiplicative.toAdd (φ (g n))‖=b*q^n)
    (L : ℕ) (hL : 0<L) (hw : ∀ n, f (g n)∈S^(L*(n+1))) : False := by
  apply not_quadratic_exponential_lower S h1 d hg L hL
  intro n
  have hc := (binaryProducts_card_norm_bound φ g b q hb hq he n).1
  calc
    2^n = ((binaryProducts g n).image f).card := by
      rw [Finset.card_image_of_injective _ hf,hc]
    _ = (binaryProducts (fun i => f (g i)) n).card := by rw [binaryProducts_map]
    _ ≤ (S^(L*n^2)).card :=
      Finset.card_le_card (binaryProducts_subset_pow S h1 (fun i => f (g i)) L hw n)

theorem HasPolynomialDegree.norm_conj_eigencharacter_le_one {d : ℕ}
    (hg : HasPolynomialDegree A d) (H : Subgroup A) [H.Normal]
    (a : A) (φ : H →* Multiplicative ℂ) (ζ : ℂ)
    (heigen : ∀ x : H, Multiplicative.toAdd (φ ((MulAut.conjNormal a) x)) =
      ζ * Multiplicative.toAdd (φ x))
    (b : H) (hb : Multiplicative.toAdd (φ b) ≠ 0) : ‖ζ‖≤1 := by
  by_contra! hl
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (3:ℝ) hl
  obtain ⟨S,h1,hs,hgen,hgrowth⟩ := (hasPolynomialDegree_iff d).mp hg
  obtain ⟨L,hL⟩ := finite_subset_word_ball S h1 hs hgen {a,a⁻¹,(b:A)}
  have haL : a∈S^L := hL (by simp)
  have haiL : a⁻¹∈S^L := hL (by simp)
  have hbL : (b:A)∈S^L := hL (by simp)
  have hepow : ∀ m : ℕ, ∀ x : H,
      Multiplicative.toAdd (φ ((MulAut.conjNormal (a^m)) x)) =
        ζ^m * Multiplicative.toAdd (φ x) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ',map_mul,MulAut.mul_apply,heigen,ih,pow_succ']
      ring
  let g : ℕ → H := fun n => (MulAut.conjNormal (a^(k*n))) b
  apply no_expanding_short_character S h1 d hgrowth H.subtype H.subtype_injective
    φ g ‖Multiplicative.toAdd (φ b)‖ (‖ζ‖^k) (norm_pos_iff.mpr hb) hk.le
    (fun n => ?_) (2*L*k+L+1) (by omega) (fun n => ?_)
  · dsimp only [g]
    rw [hepow,norm_mul,norm_pow,pow_mul,mul_comm]
  · change ((MulAut.conjNormal (a^(k*n))) b : A)∈_
    rw [MulAut.conjNormal_apply]
    have haP : a^(k*n)∈S^(L*(k*n)) := by
      rw [pow_mul]
      exact Finset.pow_mem_pow haL
    have haiP : (a^(k*n))⁻¹∈S^(L*(k*n)) := by
      rw [←inv_pow,pow_mul]
      exact Finset.pow_mem_pow haiL
    apply Finset.pow_subset_pow_right h1
      (show L*(k*n)+L+L*(k*n)≤(2*L*k+L+1)*(n+1) by nlinarith)
    rw [pow_add,pow_add]
    exact Finset.mul_mem_mul (Finset.mul_mem_mul haP hbL) haiP

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_ConjugationMatrixGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Matrix

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma latticeCharacter_mulVec (w : ι → ℂ) (M : Matrix ι ι ℤ) (v : ι → ℤ) :
    Multiplicative.toAdd (latticeCharacter w (Multiplicative.ofAdd (M.mulVec v))) =
      (Matrix.vecMul w (M.map (Int.castRingHom ℂ))) ⬝ᵥ (fun i => (v i : ℂ)) := by
  change (w ⬝ᵥ fun i => ((M.mulVec v i : ℤ) : ℂ)) = _
  have he : (fun i => ((M.mulVec v i : ℤ) : ℂ)) =
      (M.map (Int.castRingHom ℂ)).mulVec (fun i => (v i : ℂ)) := by
    funext i
    exact (Int.castRingHom ℂ).map_mulVec M v i
  rw [he,Matrix.dotProduct_mulVec]

lemma latticeCharacter_single (w : ι → ℂ) (i : ι) :
    Multiplicative.toAdd (latticeCharacter w (Multiplicative.ofAdd (Pi.single i 1)))=w i := by
  change (w ⬝ᵥ fun j => (((Pi.single i (1:ℤ) : ι → ℤ) j : ℤ) : ℂ))=w i
  have he : (fun j => (((Pi.single i (1:ℤ) : ι → ℤ) j : ℤ) : ℂ)) = Pi.single i (1:ℂ) := by
    funext j
    by_cases h : i=j
    · subst j; simp
    · simp [Ne.symm h]
  rw [he,dotProduct_single,mul_one]

theorem HasPolynomialDegree.conjugationMatrix_roots_norm_le_one {d : ℕ}
    (hg : HasPolynomialDegree A d) (H : Subgroup A) [H.Normal] (a : A)
    (p : H →* Multiplicative (ι → ℤ)) (hp : Surjective p)
    (M : Matrix ι ι ℤ)
    (hM : ∀ x : H, Multiplicative.toAdd (p ((MulAut.conjNormal a) x)) =
      M.mulVec (Multiplicative.toAdd (p x))) :
    ∀ z∈(M.map (Int.castRingHom ℂ)).charpoly.roots, ‖z‖≤1 := by
  intro z hz
  let C := M.map (Int.castRingHom ℂ)
  have hroot : (C.transpose.mulVecLin.charpoly).IsRoot z := by
    rw [Matrix.charpoly_mulVecLin,Matrix.charpoly_transpose]
    exact (Polynomial.mem_roots (Matrix.charpoly_monic C).ne_zero).mp hz
  have heig := (Module.End.hasEigenvalue_iff_isRoot_charpoly C.transpose.mulVecLin z).mpr hroot
  obtain ⟨w,hw⟩ := heig.exists_hasUnifEigenvector
  have hweq : Matrix.vecMul w C = z • w := by
    simpa only [Matrix.mulVecLin_apply,Matrix.mulVec_transpose] using hw.apply_eq_smul
  have hwn := hw.2
  have hex : ∃ i, w i ≠ 0 := by
    by_contra! h
    exact hwn (funext h)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨b,hb⟩ := hp (Multiplicative.ofAdd (Pi.single i 1))
  let φ := (latticeCharacter w).comp p
  have hφ : ∀ x : H, Multiplicative.toAdd (φ ((MulAut.conjNormal a) x)) =
      z * Multiplicative.toAdd (φ x) := by
    intro x
    change Multiplicative.toAdd (latticeCharacter w (p ((MulAut.conjNormal a) x))) =
      z * Multiplicative.toAdd (latticeCharacter w (p x))
    have hpx : p ((MulAut.conjNormal a) x) =
      Multiplicative.ofAdd (M.mulVec (Multiplicative.toAdd (p x))) := by
      exact congrArg Multiplicative.ofAdd (hM x)
    rw [hpx,latticeCharacter_mulVec]
    change (Matrix.vecMul w C) ⬝ᵥ (fun i => ((Multiplicative.toAdd (p x) i : ℤ) : ℂ)) = _
    rw [hweq,smul_dotProduct]
    rfl
  have hφb : Multiplicative.toAdd (φ b) ≠ 0 := by
    change Multiplicative.toAdd (latticeCharacter w (p b)) ≠ 0
    rw [hb,latticeCharacter_single]
    exact hi
  exact hg.norm_conj_eigencharacter_le_one H a φ z hφ b hφb

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_MatrixPeriodicDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Matrix

namespace CriticalPercolation.SparseGrowth
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma intMatrix_mahlerMeasure_eq_one (M : Matrix ι ι ℤ)
    (hroots : ∀ z∈(M.map (Int.castRingHom ℂ)).charpoly.roots, ‖z‖≤1) :
    (M.charpoly.map (Int.castRingHom ℂ)).mahlerMeasure=1 := by
  rw [←Matrix.charpoly_map,Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    (Matrix.charpoly_monic _).leadingCoeff,norm_one,one_mul]
  apply Multiset.prod_eq_one
  intro x hx
  obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hx
  exact max_eq_left (hroots z hz)

lemma intMatrix_root_is_rootOfUnity (M : Matrix ι ι ℤ)
    (hroots : ∀ z∈(M.map (Int.castRingHom ℂ)).charpoly.roots, ‖z‖≤1)
    (z : ℂ) (hz : z∈(M.map (Int.castRingHom ℂ)).charpoly.roots) (hz0 : z≠0) :
    ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  apply Polynomial.pow_eq_one_of_mahlerMeasure_eq_one
    (intMatrix_mahlerMeasure_eq_one M hroots) hz0
  have he : Int.castRingHom ℂ = algebraMap ℤ ℂ := by ext; simp
  simpa only [Polynomial.aroots_def,Matrix.charpoly_map,he] using hz

theorem intMatrix_exists_periodic_vector [Nonempty ι] (M : Matrix ι ι ℤ)
    (hunit : IsUnit M)
    (hroots : ∀ z∈(M.map (Int.castRingHom ℂ)).charpoly.roots, ‖z‖≤1) :
    ∃ m : ℕ, 0 < m ∧ ∃ v : ι → ℤ, v≠0 ∧ (M^m).mulVec v=v := by
  let C := M.map (Int.castRingHom ℂ)
  have hcunit : IsUnit C := hunit.map (Int.castRingHom ℂ).mapMatrix
  have hdeg : C.charpoly.degree ≠ 0 := by
    apply ne_of_gt
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [Matrix.charpoly_natDegree_eq_dim]
    exact Fintype.card_pos
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_root C.charpoly hdeg
  have heig : Module.End.HasEigenvalue C.mulVecLin z := by
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    rwa [Matrix.charpoly_mulVecLin]
  have hz0 : z≠0 := by
    intro hz0
    obtain ⟨w,hw⟩ := heig.exists_hasEigenvector
    apply hw.2
    apply Matrix.mulVec_injective_iff_isUnit.mpr hcunit
    have he := hw.apply_eq_smul
    simpa [hz0] using he
  have hzmem := (Polynomial.mem_roots (Matrix.charpoly_monic C).ne_zero).mpr hz
  obtain ⟨m,hm,hmz⟩ := intMatrix_root_is_rootOfUnity M hroots z hzmem hz0
  have heigpow := heig.pow m
  rw [hmz] at heigpow
  have hroot : (C^m).charpoly.IsRoot 1 := by
    have he : (C^m).mulVecLin = C.mulVecLin^m := Matrix.toLin'_pow C m
    rw [←Matrix.charpoly_mulVecLin,he]
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp heigpow
  have hrootZ : (M^m).charpoly.IsRoot 1 := by
    apply Polynomial.IsRoot.of_map (f := Int.castRingHom ℂ) ?_ (Int.castRingHom ℂ).injective_int
    simpa only [map_one,←Matrix.charpoly_map,Matrix.map_pow] using hroot
  have heigZ : Module.End.HasEigenvalue (M^m).mulVecLin 1 := by
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    rwa [Matrix.charpoly_mulVecLin]
  obtain ⟨v,hv⟩ := heigZ.exists_hasEigenvector
  refine ⟨m,hm,v,hv.2,?_⟩
  simpa only [Matrix.mulVecLin_apply,one_smul] using hv.apply_eq_smul

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_AbelianConjugationGrowth
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Matrix IsMulCommutative

namespace CriticalPercolation.SparseGrowth

variable {B : Type*} [CommGroup B]

lemma periodic_lift_of_torsion_coset (f : B ≃* B) (x : B)
    (hx : ¬IsOfFinOrder x) (hfix : f x * x⁻¹ ∈ CommGroup.torsion B) :
    ∃ y : B, ¬IsOfFinOrder y ∧ f y=y := by
  obtain ⟨k,hk,he⟩ := (CommGroup.mem_torsion _).mp hfix |>.exists_pow_eq_one
  refine ⟨x^k,fun hy => hx (hy.of_pow (Nat.ne_of_gt hk)),?_⟩
  rw [map_pow]
  rw [mul_pow,inv_pow,mul_inv_eq_one] at he
  exact he

lemma infinite_fg_commgroup_quotient_torsion_nontrivial [Group.FG B] [Infinite B] :
    Nontrivial (B ⧸ CommGroup.torsion B) := by
  by_contra h
  have hs : Subsingleton (B ⧸ CommGroup.torsion B) := not_nontrivial_iff_subsingleton.mp h
  have ht : IsMulTorsion B := by
    intro x
    exact (QuotientGroup.eq_one_iff (N := CommGroup.torsion B) x).mp (Subsingleton.elim _ _)
  let _ := CommGroup.finite_of_fg_isMulTorsion B ht
  exact not_finite B

variable {A : Type*} [Group A] [DecidableEq A]

theorem HasPolynomialDegree.abelian_normal_periodic_direction {d : ℕ}
    (hg : HasPolynomialDegree A d) (H : Subgroup A) [H.Normal]
    [IsMulCommutative H] [Group.FG H] [Infinite H] (a : A) :
    ∃ m : ℕ, 0 < m ∧ ∃ x : H, ¬IsOfFinOrder x ∧ (MulAut.conjNormal (a^m)) x=x := by
  let T := CommGroup.torsion H
  let Q := H ⧸ T
  let _ : Nontrivial Q := infinite_fg_commgroup_quotient_torsion_nontrivial
  let V := Additive Q
  let _ : Module.Finite ℤ V := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let _ : Module.Free ℤ V := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex ℤ V
  let b := Module.Free.chooseBasis ℤ V
  let _ : Fintype ι := Module.Free.ChooseBasisIndex.fintype ℤ V
  let _ : Nonempty ι := b.index_nonempty
  let e := b.equivFun
  let c : Q ≃* Multiplicative (ι → ℤ) :=
    { toFun := fun q => Multiplicative.ofAdd (e (Additive.ofMul q))
      invFun := fun v => Additive.toMul (e.symm (Multiplicative.toAdd v))
      left_inv := by intro q; exact congrArg Additive.toMul (e.symm_apply_apply _)
      right_inv := by intro v; exact congrArg Multiplicative.ofAdd (e.apply_symm_apply _)
      map_mul' := by intro x y; exact congrArg Multiplicative.ofAdd (e.map_add _ _) }
  let f := MulAut.conjNormal a (H := H)
  let fQ := QuotientGroup.congr T T f f.map_torsion
  let fV : V ≃ₗ[ℤ] V := fQ.toAdditive.toIntLinearEquiv
  let M := LinearMap.toMatrix b b fV.toLinearMap
  have hfunit : IsUnit fV.toLinearMap := by
    refine ⟨⟨fV.toLinearMap,fV.symm.toLinearMap,?_,?_⟩,rfl⟩ <;> ext x <;> simp
  have hMunit : IsUnit M := hfunit.map (LinearMap.toMatrixAlgEquiv b)
  let p := c.toMonoidHom.comp (QuotientGroup.mk' T)
  have hp : Surjective p := c.surjective.comp (QuotientGroup.mk'_surjective T)
  have hM : ∀ x : H, Multiplicative.toAdd (p (f x))=M.mulVec (Multiplicative.toAdd (p x)) := by
    intro x
    change e (Additive.ofMul ((QuotientGroup.mk' T) (f x))) =
      M.mulVec (e (Additive.ofMul ((QuotientGroup.mk' T) x)))
    have he := (LinearMap.toMatrix_mulVec_repr b b fV.toLinearMap
      (Additive.ofMul ((QuotientGroup.mk' T) x))).symm
    simpa [←Module.Basis.equivFun_apply, fV, fQ, e, M, MulEquiv.toAdditive] using he
  have hroots := hg.conjugationMatrix_roots_norm_le_one H a p hp M hM
  obtain ⟨m,hm,v,hv,hMv⟩ := intMatrix_exists_periodic_vector M hMunit hroots
  let q := c.symm (Multiplicative.ofAdd v)
  obtain ⟨x,hxq⟩ := QuotientGroup.mk'_surjective T q
  have hqne : q≠1 := by
    intro h
    apply hv
    have hh := congrArg c h
    simpa [q] using hh
  have hx : ¬IsOfFinOrder x := by
    intro hx
    have hqfin : IsOfFinOrder q := hxq ▸ (QuotientGroup.mk' T).isOfFinOrder hx
    exact isMulTorsionFree_iff_not_isOfFinOrder.mp (inferInstance : IsMulTorsionFree Q) hqne hqfin
  have hMp (n : ℕ) (y : H) :
      Multiplicative.toAdd (p ((MulAut.conjNormal (a^n)) y))=
        (M^n).mulVec (Multiplicative.toAdd (p y)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',map_mul,MulAut.mul_apply,hM,ih,Matrix.mulVec_mulVec,←pow_succ']
  have hpx : Multiplicative.toAdd (p x)=v := by
    change Multiplicative.toAdd (c ((QuotientGroup.mk' T) x))=v
    rw [hxq]
    exact congrArg Multiplicative.toAdd (c.apply_symm_apply _)
  have hT : (MulAut.conjNormal (a^m)) x*x⁻¹ ∈ T := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' T) (_*_)=1
    rw [map_mul,map_inv,mul_inv_eq_one]
    apply c.injective
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (p ((MulAut.conjNormal (a^m)) x))=
      Multiplicative.toAdd (p x)
    rw [hMp,hpx,hMv]
  obtain ⟨y,hy,hyfix⟩ := periodic_lift_of_torsion_coset (MulAut.conjNormal (a^m)) x hx hT
  exact ⟨m,hm,y,hy,hyfix⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_SolvableGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise IsMulCommutative commutatorElement

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A]

omit [DecidableEq A] in
lemma isMulCommutative_of_generators (S : Set A) (hgen : Subgroup.closure S=⊤)
    (hcomm : ∀ x∈S, ∀ y∈S, x*y=y*x) : IsMulCommutative A := by
  have hc := Subgroup.isMulCommutative_closure
    (fun left hleft right hright => hcomm left hleft right hright)
  rw [hgen] at hc
  let _ := hc
  exact ⟨⟨fun x y => congrArg Subtype.val
    (mul_comm' (⟨x,Subgroup.mem_top x⟩ : (⊤ : Subgroup A))
      (⟨y,Subgroup.mem_top y⟩ : (⊤ : Subgroup A)))⟩⟩

lemma commutator_eq_normalClosure_generators (S : Finset A)
    (hgen : Subgroup.closure (S : Set A)=⊤) :
    commutator A = Subgroup.normalClosure
      (((S.product S).image (fun p : A×A => ⁅p.1,p.2⁆)) : Set A) := by
  let F := (S.product S).image (fun p : A×A => ⁅p.1,p.2⁆)
  let N := Subgroup.normalClosure (F : Set A)
  change commutator A=N
  apply le_antisymm
  · apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    let q := QuotientGroup.mk' N
    apply isMulCommutative_of_generators (q '' (S : Set A))
    · rw [←MonoidHom.map_closure,hgen,←MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
    · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [←map_commutatorElement]
      apply (QuotientGroup.eq_one_iff ⁅x,y⁆).mpr
      apply Subgroup.subset_normalClosure
      exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    obtain ⟨⟨u,v⟩,huv,rfl⟩ := Finset.mem_image.mp hx
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)

theorem HasPolynomialDegree.commutator_fg {d : ℕ} (h : HasPolynomialDegree A d) :
    (commutator A).FG := by
  obtain ⟨S,h1,hsym,hgen,hg⟩ := (hasPolynomialDegree_iff d).mp h
  rw [commutator_eq_normalClosure_generators S hgen]
  exact normalClosure_fg_of_sparse_growth S _ h1 hsym hgen d hg

omit [DecidableEq A] in
lemma finite_of_fg_torsion_finite_commutator [Group.FG A]
    (ht : IsMulTorsion A) [Finite (commutator A)] : Finite A := by
  let N := commutator A
  let _ : IsMulCommutative (A ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  let _ : Finite (A ⧸ N) := CommGroup.finite_of_fg_isMulTorsion _
    (IsMulTorsion.of_surjective (QuotientGroup.mk'_surjective N) ht)
  exact Finite.of_subgroup_quotient N

omit [DecidableEq A] in
lemma map_derivedSeries_commutator (n : ℕ) :
    (derivedSeries (commutator A) n).map (commutator A).subtype =
      derivedSeries A (n+1) := by
  induction n with
  | zero =>
    change (⊤ : Subgroup (commutator A)).map (commutator A).subtype=commutator A
    rw [←MonoidHom.range_eq_map,Subgroup.range_subtype]
  | succ n ih =>
    change (⁅derivedSeries (commutator A) n,derivedSeries (commutator A) n⁆).map _=_
    rw [Subgroup.map_commutator,ih]
    rfl

theorem finite_of_torsion_derivedSeries_eq_bot (n : ℕ) :
    ∀ (A : Type*) [Group A] [DecidableEq A], ∀ d : ℕ,
      HasPolynomialDegree A d → IsMulTorsion A → derivedSeries A n=⊥ → Finite A := by
  induction n with
  | zero =>
    intro A _ _ d hg ht hz
    have hsub : Subsingleton A := by
      constructor
      intro x y
      have hx : x=1 := by
        have hm : x∈derivedSeries A 0 := Subgroup.mem_top x
        simpa only [hz,Subgroup.mem_bot] using hm
      have hy : y=1 := by
        have hm : y∈derivedSeries A 0 := Subgroup.mem_top y
        simpa only [hz,Subgroup.mem_bot] using hm
      exact hx.trans hy.symm
    exact Finite.of_subsingleton
  | succ n ih =>
    intro A _ _ d hg ht hz
    let _ := hg.fg
    let H := commutator A
    let _ : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hg.commutator_fg
    have hH : HasPolynomialDegree H d := hg.of_injective H.subtype Subtype.val_injective
    have htH := ht.subgroup H
    have hzH : derivedSeries H n=⊥ := by
      apply Subgroup.map_injective (f := H.subtype) Subtype.val_injective
      rw [Subgroup.map_bot,map_derivedSeries_commutator,hz]
    let _ : Finite H := ih H d hH htH hzH
    exact finite_of_fg_torsion_finite_commutator ht

omit [DecidableEq A] in
theorem finite_of_torsion_solvable_sparse_growth {d : ℕ} (hg : HasPolynomialDegree A d)
    (ht : IsMulTorsion A) [Group.IsSolvable A] : Finite A := by
  classical
  obtain ⟨n,hn⟩ := Group.IsSolvable.solvable (G := A)
  exact finite_of_torsion_derivedSeries_eq_bot n A d hg ht hn

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_CharacteristicNilpotentCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise IsMulCommutative

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

lemma HasPolynomialDegree.of_surjective {d : ℕ} (hg : HasPolynomialDegree A d)
    (f : A →* B) (hf : Surjective f) : HasPolynomialDegree B d := by
  obtain ⟨S,h1,hs,hgen,C,hC⟩ := (hasPolynomialDegree_iff d).mp hg
  apply (hasPolynomialDegree_iff d).mpr
  refine ⟨S.image f,Finset.mem_image.mpr ⟨1,h1,map_one f⟩,?_,?_,C,?_⟩
  · rw [←Finset.image_inv,hs]
  · rw [Finset.coe_image,←MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective f hf
  · intro R
    obtain ⟨n,hn,hb⟩ := hC R
    refine ⟨n,hn,le_trans ?_ hb⟩
    rw [←Finset.image_pow]
    exact Finset.card_image_le

omit [DecidableEq A] [DecidableEq B] in
lemma powerSubgroup_le_finiteIndex (L : Subgroup A) [L.Normal] [L.FiniteIndex] :
    powerSubgroup A (Nat.card (A ⧸ L)) ≤ L := by
  apply (Subgroup.closure_le L).mpr
  rintro _ ⟨x,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' L) (x^_)=1
  rw [map_pow]
  let _ := Fintype.ofFinite (A ⧸ L)
  simpa only [Nat.card_eq_fintype_card] using
    (pow_card_eq_one (x := (QuotientGroup.mk' L) x))

omit [DecidableEq A] [DecidableEq B] in
lemma characteristic_map_normal (N : Subgroup A) [N.Normal]
    (P : Subgroup N) [P.Characteristic] : (P.map N.subtype).Normal := by
  constructor
  rintro _ ⟨x,hx,rfl⟩ a
  refine ⟨(MulAut.conjNormal a) x,?_,rfl⟩
  exact Subgroup.characteristic_iff_le_comap.mp inferInstance (MulAut.conjNormal a) hx

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_FiniteCyclicExtensionIndex
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A]

lemma finiteIndex_of_finite_kernel_int (f : A →* Multiplicative ℤ)
    [Finite f.ker] (a : A) (ha : f a=Multiplicative.ofAdd 1)
    (H : Subgroup A) (m : ℕ) (hm : 0 < m) (haH : a^m ∈ H) : H.FiniteIndex := by
  let F : f.ker × Fin m → A ⧸ H := fun p => QuotientGroup.mk (p.1.val*a^p.2.val)
  have hF : Surjective F := by
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective q
    let n : ℤ := (f x).toAdd
    let k : A := x*a^(-n)
    have hk : k∈f.ker := by
      change f k=1
      apply Multiplicative.toAdd.injective
      simp [k,map_zpow,ha,n]
    let r : Fin m := ⟨(n % (m:ℤ)).toNat,by
      have hr0 := Int.emod_nonneg n (by omega : (m:ℤ)≠0)
      have hr := Int.emod_lt_of_pos n (by omega : 0<(m:ℤ))
      omega⟩
    refine ⟨(⟨k,hk⟩,r),?_⟩
    apply QuotientGroup.eq.mpr
    change (k*a^r.val)⁻¹*x∈H
    have hr : (r.val:ℤ)=n%(m:ℤ) := Int.toNat_of_nonneg
      (Int.emod_nonneg n (by omega : (m:ℤ)≠0))
    have he : (k*a^r.val)⁻¹*x=(a^m)^(n/(m:ℤ)) := by
      calc
        (k*a^r.val)⁻¹*x = a^(-(r.val:ℤ))*a^n := by simp only [k,mul_inv_rev,zpow_neg,←zpow_natCast]; group
        _ = a^((m:ℤ)*(n/(m:ℤ))) := by
          rw [←zpow_add,hr]
          congr 1
          have hh := Int.emod_add_mul_ediv n (m:ℤ)
          omega
        _ = (a^m)^(n/(m:ℤ)) := by rw [zpow_mul,zpow_natCast]
    rw [he]
    exact H.zpow_mem haH _
  let _ : Finite (A ⧸ H) := Finite.of_surjective F hF
  exact Subgroup.finiteIndex_of_finite_quotient

lemma finite_lift_kernel (f : A →* Multiplicative ℤ) (L : Subgroup A) [L.Normal]
    (hL : L ≤ f.ker) [(L.subgroupOf f.ker).FiniteIndex] :
    Finite (QuotientGroup.lift L f hL).ker := by
  let q := QuotientGroup.mk' L
  let p := q.comp f.ker.subtype
  have hpker : p.ker=L.subgroupOf f.ker := by
    ext x
    exact QuotientGroup.eq_one_iff (N := L) x.val
  let _ : p.ker.FiniteIndex := hpker.symm ▸ (inferInstance : (L.subgroupOf f.ker).FiniteIndex)
  let _ : Finite p.range := Finite.of_equiv (f.ker ⧸ p.ker)
    (QuotientGroup.quotientKerEquivRange p).toEquiv
  have he : p.range=(QuotientGroup.lift L f hL).ker := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact y.property
    · intro hx
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective L x
      exact ⟨⟨y,hx⟩,rfl⟩
  exact he ▸ (inferInstance : Finite p.range)

lemma finiteIndex_of_normal_kernel_subgroup (f : A →* Multiplicative ℤ)
    (L : Subgroup A) [L.Normal] (hL : L ≤ f.ker) [(L.subgroupOf f.ker).FiniteIndex]
    (a : A) (ha : f a=Multiplicative.ofAdd 1)
    (H : Subgroup A) (hLH : L ≤ H) (m : ℕ) (hm : 0 < m) (haH : a^m ∈ H) :
    H.FiniteIndex := by
  let q := QuotientGroup.mk' L
  let g := QuotientGroup.lift L f hL
  let _ : Finite g.ker := finite_lift_kernel f L hL
  have hi : (H.map q).FiniteIndex := finiteIndex_of_finite_kernel_int g (q a) ha
    (H.map q) m hm (by rw [←map_pow]; exact ⟨a^m,haH,rfl⟩)
  constructor
  rw [←Subgroup.index_map_eq H (QuotientGroup.mk'_surjective L)
    (by simpa only [QuotientGroup.ker_mk'] using hLH)]
  exact hi.index_ne_zero

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_NilpotentInfiniteCenter
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical commutatorElement

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A]

lemma finite_upperCentralSeriesStep [Group.FG A] [Finite (Subgroup.center A)]
    (N : Subgroup A) [N.Normal] [Finite N] :
    Finite (Subgroup.upperCentralSeriesStep N) := by
  obtain ⟨S,hS⟩ := Group.fg_def.mp (inferInstance : Group.FG A)
  let U := Subgroup.upperCentralSeriesStep N
  let f : U → (S → N) := fun u s => ⟨⁅u.val,s.val⁆,u.property s.val⟩
  have hdiff (u v : U) (h : f u=f v) : v.val⁻¹*u.val ∈ Subgroup.center A := by
    rw [←Subgroup.centralizer_univ,←Subgroup.coe_top,←hS,Subgroup.centralizer_closure]
    intro s hs
    have he := congrArg (fun g : S → N => (g ⟨s,hs⟩).val) h
    change ⁅u.val,s⁆=⁅v.val,s⁆ at he
    simp only [commutatorElement_def] at he
    calc
      s*(v.val⁻¹*u.val) = v.val⁻¹*(v.val*s*v.val⁻¹*s⁻¹)*s*u.val := by group
      _ = v.val⁻¹*(u.val*s*u.val⁻¹*s⁻¹)*s*u.val := by rw [he]
      _ = v.val⁻¹*u.val*s := by group
  have hf (b : S → N) : Finite {u : U // f u=b} := by
    by_cases hb : Nonempty {u : U // f u=b}
    · obtain ⟨v,hv⟩ := hb
      let e : {u : U // f u=b} → Subgroup.center A := fun u =>
        ⟨v.val⁻¹*u.val.val,hdiff u.val v (u.property.trans hv.symm)⟩
      apply Finite.of_injective e
      intro u w he
      apply Subtype.ext
      apply Subtype.ext
      have he' := congrArg Subtype.val he
      exact mul_left_cancel he'
    · let _ : IsEmpty {u : U // f u=b} := not_nonempty_iff.mp hb
      infer_instance
  let _ : ∀ b : S → N, Finite {u : U // f u=b} := hf
  apply Finite.of_injective (fun u : U => (⟨f u,⟨u,rfl⟩⟩ : Σ b : S → N, {u : U // f u=b}))
  intro u v h
  exact congrArg (fun x : Σ b : S → N, {u : U // f u=b} => x.2.val) h

theorem finite_of_finite_center [Group.FG A] [Group.IsNilpotent A]
    [Finite (Subgroup.center A)] : Finite A := by
  have hf (n : ℕ) : Finite (Subgroup.upperCentralSeries A n) := by
    induction n with
    | zero => simpa only [Subgroup.upperCentralSeries_zero] using
        (inferInstance : Finite (⊥ : Subgroup A))
    | succ n ih =>
      let _ := ih
      exact finite_upperCentralSeriesStep (Subgroup.upperCentralSeries A n)
  obtain ⟨n,hn⟩ := Group.IsNilpotent.nilpotent A
  let _ : Finite (⊤ : Subgroup A) := hn ▸ hf n
  exact Finite.of_surjective (⊤ : Subgroup A).subtype (by intro x; exact ⟨⟨x,Subgroup.mem_top x⟩,rfl⟩)

theorem infinite_center_of_nilpotent [Group.FG A] [Group.IsNilpotent A]
    [Infinite A] : Infinite (Subgroup.center A) := by
  rcases finite_or_infinite (Subgroup.center A) with hf | hi
  · let _ := hf
    let _ : Finite A := finite_of_finite_center
    exact False.elim (_root_.not_finite A)
  · exact hi

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_GeneralPeriodicCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma HasPolynomialDegree.periodic_center_of_fg_nilpotent_kernel {d : ℕ}
    (hg : HasPolynomialDegree A d)
    (f : A →* Multiplicative ℤ) (hf : Surjective f)
    (L : Subgroup A) [L.Normal] [Group.IsNilpotent L] [Group.FG L] [Infinite L]
    (hLK : L ≤ f.ker) [(L.subgroupOf f.ker).FiniteIndex] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ x : H,
      x∈Subgroup.center H ∧ ¬IsOfFinOrder x := by
  let Z := Subgroup.center L
  let _ : Infinite Z := infinite_center_of_nilpotent
  let C := Z.map L.subtype
  let e : Z ≃* C := Z.equivMapOfInjective L.subtype Subtype.val_injective
  let _ : C.Normal := characteristic_map_normal L Z
  let _ : IsMulCommutative C := ⟨⟨fun x y => e.symm.injective (by
    simp only [map_mul]; exact mul_comm _ _)⟩⟩
  let _ : Infinite C := Infinite.of_injective e e.injective
  let _ : Group.FG Z := nilpotent_subgroup_fg L Z
  let _ : Group.FG C := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  obtain ⟨a,ha⟩ := hf (Multiplicative.ofAdd 1)
  obtain ⟨m,hm,x,hx,hfix⟩ := hg.abelian_normal_periodic_direction C a
  let H := Subgroup.centralizer ({x.val} : Set A)
  have hLH : L≤H := by
    intro l hl
    obtain ⟨z,hz,hzx⟩ := x.property
    rw [Subgroup.mem_centralizer_singleton_iff,←hzx]
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨l,hl⟩)
  have haH : a^m∈H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have he := congrArg Subtype.val hfix
    change a^m*x.val*(a^m)⁻¹=x.val at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hHi : H.FiniteIndex := finiteIndex_of_normal_kernel_subgroup f L hLK a ha H hLH m hm haH
  let y : H := ⟨x.val,by rw [Subgroup.mem_centralizer_singleton_iff]⟩
  refine ⟨H,hHi,y,?_,?_⟩
  · rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp w.property
  · intro hy
    obtain ⟨k,hk,he⟩ := hy.exists_pow_eq_one
    apply hx
    apply isOfFinOrder_iff_pow_eq_one.mpr
    exact ⟨k,hk,Subtype.ext (congrArg (fun z : H => z.val) he)⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Nilpotent_GeneralNilpotentCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

omit [DecidableEq A] [DecidableEq B] in
lemma virtuallyNilpotent_of_surjective (f : A →* B) (hf : Surjective f)
    (hv : Group.IsVirtuallyNilpotent A) : Group.IsVirtuallyNilpotent B := by
  obtain ⟨N,hN,hNi⟩ := hv
  let _ := hN
  let _ := hNi
  refine ⟨N.map f,?_,⟨fun he => hNi.index_ne_zero (by have hh := N.index_map_dvd hf; simpa [he] using hh)⟩⟩
  let g : N →* N.map f := {
    toFun := fun x => ⟨f x,⟨x,x.property,rfl⟩⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' := fun x y => Subtype.ext (map_mul f x.val y.val) }
  apply Group.nilpotent_of_surjective g
  rintro ⟨y,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

omit [DecidableEq B] in
lemma finite_of_torsion_virtuallyNilpotent_growth {d : ℕ}
    (hg : HasPolynomialDegree A d) (ht : IsMulTorsion A)
    (hv : Group.IsVirtuallyNilpotent A) : Finite A := by
  obtain ⟨N,hN,hNi⟩ := hv
  let _ := hN
  let _ := hNi
  let _ : Finite N := finite_of_torsion_solvable_sparse_growth
    (hg.finiteIndex_subgroup N) (ht.subgroup N)
  exact N.finite_iff_finite_and_finiteIndex.mpr ⟨inferInstance,hNi⟩

omit [DecidableEq B] in
lemma HasPolynomialDegree.powerSubgroup_finiteIndex {d : ℕ}
    (hg : HasPolynomialDegree A d) (hv : Group.IsVirtuallyNilpotent A)
    (k : ℕ) (hk : 0<k) : (powerSubgroup A k).FiniteIndex := by
  let P := powerSubgroup A k
  have ht : IsMulTorsion (A ⧸ P) := by
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective P q
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨k,hk,?_⟩
    rw [←map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_closure ⟨x,rfl⟩
  have hq := hg.of_surjective (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
  have hvq := virtuallyNilpotent_of_surjective (QuotientGroup.mk' P)
    (QuotientGroup.mk'_surjective P) hv
  let _ : Finite (A ⧸ P) := finite_of_torsion_virtuallyNilpotent_growth hq ht hvq
  exact Subgroup.finiteIndex_of_finite_quotient

omit [DecidableEq B] in
lemma HasPolynomialDegree.characteristic_nilpotent_core_general {d : ℕ}
    (hg : HasPolynomialDegree A d) (hv : Group.IsVirtuallyNilpotent A) :
    ∃ P : Subgroup A, P.Characteristic ∧ P.FiniteIndex ∧ Group.IsNilpotent P := by
  obtain ⟨L,hL,hLi⟩ := hv
  let _ := hL
  let _ := hLi
  let N := L.normalCore
  let k := Nat.card (A ⧸ N)
  have hk : 0 < k := Nat.card_pos
  let P := powerSubgroup A k
  have hPL : P≤L := (powerSubgroup_le_finiteIndex N).trans L.normalCore_le
  refine ⟨P,inferInstance,hg.powerSubgroup_finiteIndex ⟨L,hL,hLi⟩ k hk,?_⟩
  let f : P →* L := Subgroup.inclusion hPL
  apply Subgroup.isNilpotent_of_ker_le_center f
  rw [(MonoidHom.ker_eq_bot_iff f).mpr (Subgroup.inclusion_injective hPL)]
  exact bot_le

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_IndicableDegreeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical IsMulCommutative

namespace CriticalPercolation.SparseGrowth
universe u

theorem virtuallyNilpotent_of_indicability_degree_step
    (d : ℕ)
    (ih : ∀ (B : Type u) [Group B] [DecidableEq B],
      HasPolynomialDegree B d → Group.IsVirtuallyNilpotent B)
    (A : Type u) [Group A] [DecidableEq A]
    (hg : HasPolynomialDegree A (d+1))
    (hind : ∃ H : Subgroup A, H.FiniteIndex ∧
      ∃ f : H →* Multiplicative ℤ, Surjective f) :
    Group.IsVirtuallyNilpotent A := by
    rcases finite_or_infinite A with hfin | hinf
    · let _ := hfin
      exact virtuallyNilpotent_of_finite
    let _ := hinf
    obtain ⟨H,hHi,f,hf⟩ := hind
    let _ := hHi
    apply virtuallyNilpotent_of_finiteIndex H
    have hgH := hg.finiteIndex_subgroup H
    let _ : Group.FG H := hgH.fg
    let K := f.ker
    let _ : Group.FG K := hgH.integer_kernel_fg f hf
    let _ : Infinite (H ⧸ K) :=
      (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv.infinite_iff.mpr inferInstance
    have hgK := hgH.normal_subgroup_descent K
    have hvK := ih K hgK
    obtain ⟨P,hP,hPi,hPn⟩ := hgK.characteristic_nilpotent_core_general hvK
    let _ := hP
    let _ := hPi
    let _ := hPn
    let L := P.map K.subtype
    let e : P ≃* L := P.equivMapOfInjective K.subtype Subtype.val_injective
    let _ : L.Normal := characteristic_map_normal K P
    let _ : Group.IsNilpotent L := Group.nilpotent_of_surjective e.toMonoidHom e.surjective
    have hLK : L≤K := Subgroup.map_subtype_le P
    have he : L.subgroupOf K=P := by
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective P
    let _ : (L.subgroupOf K).FiniteIndex := he.symm ▸ hPi
    rcases finite_or_infinite L with hLf | hLi
    · let _ := hLf
      let _ : Finite P := Finite.of_equiv L e.symm.toEquiv
      let _ : Finite K := P.finite_iff_finite_and_finiteIndex.mpr ⟨inferInstance,hPi⟩
      exact CompactQuotient.virtuallyNilpotent_of_finite_kernel f (Set.toFinite _)
        (Group.IsNilpotent.isVirtuallyNilpotent inferInstance)
    · let _ := hLi
      let _ : Group.FG P := inferInstance
      let _ : Group.FG L := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
      obtain ⟨J,hJi,x,hx,hxinf⟩ := hgH.periodic_center_of_fg_nilpotent_kernel f hf L hLK
      let _ := hJi
      apply virtuallyNilpotent_of_finiteIndex J
      have hgJ := hgH.finiteIndex_subgroup J
      have hgQ := hgJ.quotient_descent (Subgroup.center J) x hx (orderOf_eq_zero hxinf)
      have hvQ := ih (J ⧸ Subgroup.center J) hgQ
      exact virtuallyNilpotent_of_central_kernel (QuotientGroup.mk' (Subgroup.center J))
        (by rw [QuotientGroup.ker_mk']) hvQ

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Harmonic_WeakGromovHarmonic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.SparseGrowth

universe u

theorem sparse_polynomial_virtuallyNilpotent (d : ℕ) :
    ∀ (A : Type u) [Group A] [DecidableEq A],
      HasPolynomialDegree A d → Group.IsVirtuallyNilpotent A := by
  induction d with
  | zero =>
    intro A _ _ hg
    let : Finite A := hg.finite
    exact virtuallyNilpotent_of_finite
  | succ d ih =>
    intro A _ _ hg
    rcases finite_or_infinite A with hf | hi
    · let := hf
      exact virtuallyNilpotent_of_finite
    let := hi
    exact virtuallyNilpotent_of_indicability_degree_step d ih A hg hg.linear_virtually_indicable

end CriticalPercolation.SparseGrowth
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Classification_DiscreteWeakGromovBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.CompactQuotient
lemma virtuallyNilpotent_of_sparse_word_growth {A : Type*} [Group A]
    (hg : HasSparsePolynomialWordGrowth A) : Group.IsVirtuallyNilpotent A := by
  obtain ⟨S,hSf,h1,hi,hgen,d,hg⟩ := hg
  exact SparseGrowth.sparse_polynomial_virtuallyNilpotent d A
    ⟨S,hSf,h1,hi,hgen,1,by simpa only [one_mul] using hg⟩
end CriticalPercolation.CompactQuotient

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetSparseGrowth
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
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetBounded
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
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetNormalClosure
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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_BoundedNormalJoins
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
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetTransfer
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetFiniteCore
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
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetIntegerKernel
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
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetKernelDescent
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
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetFiniteIndex
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
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetNormalPromotion
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
-- module Solutions.Q228_CP.CriticalPercolation_Growth_CosetSubgroupGenerators
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
-- module Solutions.Q228_CP.CriticalPercolation_Classification_RelativeClassification
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
    obtain ⟨H,hHi,f,hf,hKf⟩ := virtually_indicable h1 hi hgen hK hg
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphTopology_CommensurableClosure
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
-- module Solutions.Q228_CP.CriticalPercolation_Growth_GraphRelativeGrowth
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
-- module Solutions.Q228_CP.CriticalPercolation_Classification_GraphCompactNormalClassification
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
  obtain ⟨N,hNn,hNi⟩ := CompactQuotient.virtuallyNilpotent_of_sparse_word_growth hg
  exact ⟨H,hHn,hcH,hoH,N,hNn,hNi.index_ne_zero⟩

end CriticalPercolation.GraphTopology
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OrbitalStructureTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

instance orbitalActionGroup_action (o : V) (L : ℕ) (Λ : Subgroup G.Aut) :
    MulAction (G.orbitalActionGroup o L Λ) (MulAction.orbit G.Aut o) where
  smul g u := g.val u
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Main
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

theorem no_percolation_at_criticality_oai [Infinite V]
    (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive)
    (hpc : G.criticalProbability < 1) :
    G.law G.criticalProbability G.percolates = 0 := by
  by_contra hper
  obtain ⟨o⟩ := hconnected.nonempty
  obtain ⟨d,hd,C,hconn,hinf,hloc,htrans,hscales,happrox,hnot⟩ :=
    G.main_failure_topological_classification_counterexample
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

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_oai.{u_1, u_2}
