-- Prove2me | solution 1 for OAI.TorsionFreeZeroDivisors.SplitModel.has_model
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:09:38.095757+00:00
-- url     : https://prove2.me/submissions/d1993de4-2222-4a41-81c3-72bfef4fe93e

import Mathlib
import Definitions.Def_TorsionFreeZeroDivisors
import Definitions.Def_TorsionFreeZeroDivisorsConstruction
import Definitions.Def_TFZDCellModule
import Definitions.Def_TFZDTopologyA
import Definitions.Def_TFZDTopologyB
universe u v w z

section
section
namespace OAI



namespace TorsionFreeZeroDivisors


end TorsionFreeZeroDivisors



end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace GroupRingTopology

instance (Vertex : Type*) [Fintype Vertex] : CompactSpace (simplexSet ℝ Vertex) := by
  apply isCompact_iff_compactSpace.mp
  have hsub : simplexSet ℝ Vertex ⊆ Set.Icc 0 1 := fun x hx =>
    ⟨fun v => hx.1 v, fun v => by
      have := Finset.single_le_sum (fun w _ => hx.1 w) (Finset.mem_univ v)
      simpa [hx.2] using this⟩
  refine (isCompact_Icc (a := (0 : Vertex → ℝ)) (b := 1)).of_isClosed_subset ?_ hsub
  have h : simplexSet ℝ Vertex = (⋂ v, {x : Vertex → ℝ | 0 ≤ x v}) ∩ {x | ∑ v, x v = 1} := by
    ext x; simp [simplexSet]
  rw [h]
  exact (isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)).inter
    (isClosed_eq (continuous_finset_sum _ fun v _ => continuous_apply v) continuous_const)

end GroupRingTopology

open Set Metric Topology BigOperators
namespace GroupRingTopology.SimplexDisk

end GroupRingTopology.SimplexDisk
open Set Metric Topology BigOperators
namespace GroupRingTopology.Simplicial

section
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

instance : TopologicalSpace (Space K) := TopologicalSpace.coinduced (quotient K) inferInstance

instance : T2Space (Space K) :=
  T2Space.of_injective_continuous (f := fun x : Space K => (x.1 : V → ℝ))
    (fun _ _ h => Subtype.ext (Finsupp.ext fun v => congrFun h v))
    (continuous_pi fun v => continuous_eval K v)

end

open Set Metric Topology BigOperators
open scoped Classical
variable {V : Type u} {W : Type v} {T : Type w}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

end GroupRingTopology.Simplicial

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators

namespace GroupRingTopology.Simplicial

section
open Set Metric Topology BigOperators
open scoped Classical unitInterval
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

variable (f g : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (hg : ∀ s : Face K, s.1.image g ∈ L)
variable (hfg : ∀ s : Face K, s.1.image f ∪ s.1.image g ∈ L)
end
open Set Metric Topology BigOperators
open scoped Classical
variable {V : Type u} (K L : PreAbstractSimplicialComplex V) (hKL : ∀ s ∈ K, s ∈ L)
end GroupRingTopology.Simplicial
namespace GroupRingTopology.Milnor
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical unitInterval
local instance (priority := 2000) (α : Type*) : DecidableEq α := Classical.decEq α
variable (G : Type u)

variable {G} {H : Type v}

end GroupRingTopology.Milnor

namespace GroupRingTopology.Simplicial
open Set Metric Topology BigOperators
variable {V : Type u} (K : PreAbstractSimplicialComplex V)
end GroupRingTopology.Simplicial
open Set Metric Topology

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Cellular
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

end GroupRingTopology.Cellular

namespace GroupRingTopology.Simplicial
open Set Metric Topology BigOperators
open scoped Classical
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

end GroupRingTopology.Simplicial

open Set Metric Topology
namespace GroupRingTopology.SphereTopology

variable {Y : Type*} [TopologicalSpace Y] {n : ℕ}

end GroupRingTopology.SphereTopology

/-! Classical cellular lifting and its geometric foundations.
No classifying-space existence or Hurewicz theorem is assumed. -/
open Set Metric Topology

namespace GroupRingTopology.Cellular

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

variable {E : Type v} [TopologicalSpace E] {n : ℕ}

end GroupRingTopology.Cellular

end

end OAI

end
end

section
section
namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
namespace GroupRingTopology.Cellular
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

namespace PartialLift
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
variable {p : C(E,B)} {f : C(X,B)} {n : ℕ}

end PartialLift

section Lift
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B] [Nonempty E]
variable {p : C(E,B)} (hp : DiskRLP p) (f : C(X,B))

end Lift

noncomputable section

variable {Y : Type u} [TopologicalSpace Y]

section CylinderMap
variable {n : ℕ} (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))

variable (h : ∀ x, pathEndpoint (a x) = b (boundary n x))

end CylinderMap

end
end GroupRingTopology.Cellular

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Milnor

section
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical unitInterval
variable {G : Type u}
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

end

section
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical
variable {G : Type u} [_root_.Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

end
section
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical
variable {G : Type u} {H : Type v} [_root_.Group G] [_root_.Group H]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
end
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical unitInterval
variable {G : Type u} {H : Type v} [_root_.Group G] [_root_.Group H]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

variable (φ : G →* H) (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ)
variable (hα : Function.Injective α) (hβ : Function.Injective β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
end GroupRingTopology.Milnor

/-! Functoriality and product additivity on actual higher homotopy groups.
This is geometric support for the literal finite idempotent diagrams. -/
namespace GroupRingTopology.HomotopyFunctor
open scoped Topology Topology.Homotopy
variable {N : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}

variable {Z : Type*} [TopologicalSpace Z] {z : Z}
end GroupRingTopology.HomotopyFunctor

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.HomotopyFunctor
open scoped Topology Topology.Homotopy
variable {N : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}
end GroupRingTopology.HomotopyFunctor
namespace GroupRingTopology.Milnor

section
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical Topology.Homotopy
variable (G : Type u) [_root_.Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

variable (N : Type v) [DecidableEq N] [Nonempty N]

instance : DirectedSystem (fun S : Shapes G => HomotopyGroup N (Simplicial.Space (stage G S)) (stagePoint G S))
    (fun S T h => stageHom G N S T h) where
  map_self _ a := by
    exact HomotopyFunctor.map_id a
  map_map _ _ _ h₁ h₂ a := by
    exact HomotopyFunctor.map_comp _ _ _ _ a

end

section
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical unitInterval
variable {G : Type u} [_root_.Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

instance : MulAction G (Space G) where
  smul g x := map (g * ·) id Function.injective_id x
  one_smul x := by
    change map (1 * ·) id Function.injective_id x = x
    apply Subtype.ext
    change x.1.mapDomain (fun v => (v.1,1*v.2)) = x.1
    rw [show (fun v : ℕ × G => (v.1,1*v.2)) = id from funext (fun v => Prod.ext rfl (one_mul v.2))]
    exact Finsupp.mapDomain_id
  mul_smul g h x := by
    change map ((g*h) * ·) id Function.injective_id x = map (g * ·) id Function.injective_id (map (h * ·) id Function.injective_id x)
    rw [map_comp]
    have he : (fun a => (g*h)*a) = ((g * ·) ∘ (h * ·)) := funext (mul_assoc g h)
    rw [he]
    rfl

instance : ContinuousConstSMul G (Space G) where
  continuous_const_smul g := (map (g * ·) id Function.injective_id).continuous

end
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical
variable (G : Type u) [_root_.Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

variable {X : Type v} [TopologicalSpace X] [MulAction G X]
end GroupRingTopology.Milnor
open Set Metric Topology
namespace GroupRingTopology.Attachment

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}
variable (a : ι → C(Sphere n,X))

instance : TopologicalSpace (Space a) := TopologicalSpace.coinduced (quotient a) inferInstance

variable [Nonempty X]

end GroupRingTopology.Attachment
open Set Metric Topology

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Cellular
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
variable {C : Set X} [CWComplex C] {f : X → Y} (hf : IsClosedEmbedding f)

variable [T2Space X]

end GroupRingTopology.Cellular
open Set Metric Topology
namespace GroupRingTopology.Attachment

section
open Set Metric Topology
variable {X : Type z} [TopologicalSpace X] [T2Space X] [Nonempty X]
variable [CWComplex (Set.univ : Set X)] {ι : Type z} {n : ℕ}
variable (a : ι → C(Sphere n,X))

end

section
open Set Metric Topology
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}
variable (a : ι → C(Sphere n,X))
variable {G : Type w} [_root_.Group G] [MulAction G X] [MulAction G ι]

variable (ha : ∀ (g : G) i x, a (g • i) x = g • a i x)
include ha

end

open Set Metric Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}
variable (a : ι → C(Sphere n,X))

variable {G : Type w} [_root_.Group G] [MulAction G X] [MulAction G ι]
variable (ha : ∀ (g : G) i x, a (g • i) x = g • a i x)
include ha

end GroupRingTopology.Attachment

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Attachment

section
open Set Metric Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι : Type w} {κ : Type z} {n : ℕ}
variable (a : ι → C(Sphere n,X)) (b : κ → C(Sphere n,Y))

end

open Set Metric Topology

instance {G : Type u} [_root_.Group G] {ι : Type v} : MulAction G (FreeIndex G ι) where
  smul g p := (g * p.1,p.2)
  one_smul p := by change ((1:G)*p.1,p.2)=p; simp only [one_mul]; rfl
  mul_smul g h p := by change ((g*h)*p.1,p.2)=(g*(h*p.1),p.2); rw [mul_assoc]

instance {G : Type u} [_root_.Group G] {ι : Type v} : IsCancelSMul G (FreeIndex G ι) where
  right_cancel' _ _ _ he := mul_right_cancel (congrArg (fun p : FreeIndex G ι => p.1) he)

variable {G : Type u} [_root_.Group G]
variable {E : Type v} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]
variable {X : Type w} [TopologicalSpace X] {ι : Type z} {n : ℕ}
variable (a : ι → C(Sphere n,E))

variable (p : C(E,X)) (hp : IsQuotientCoveringMap p G)
variable (b : ι → C(Sphere n,X)) (h : ∀ i x, p (a i x) = b i x)

end GroupRingTopology.Attachment

namespace GroupRingTopology.Cayley
open Set Metric Topology Attachment

instance : Finite (Sphere 1) := by
  have he : {r : ℝ | r = -1 ∨ r = 1} = {-1,1} := by ext r; simp
  have hS : Set.Finite {r : ℝ | r = -1 ∨ r = 1} := he.symm ▸ ((Set.finite_singleton (1 : ℝ)).insert (-1))
  let : Finite {r : ℝ // r = -1 ∨ r = 1} := hS.to_subtype
  apply Finite.of_injective (fun x : Sphere 1 => (⟨x.1 0,sphere_one_cases x⟩ :
    {r : ℝ // r = -1 ∨ r = 1}))
  intro x y h
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa only [hi] using congrArg Subtype.val h

instance : DiscreteTopology (Sphere 1) := inferInstance

variable {G : Type u} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)

instance : Nonempty (Graph s) := ⟨base _ 1⟩

instance : T2Space (Graph s) :=
  t2Space _ ((realSeparated_of_tychonoff (Y := G)))

end GroupRingTopology.Cayley

namespace GroupRingTopology.PathSquares
open Set
open scoped unitInterval
variable {X : Type*} [TopologicalSpace X] {x a b : X}
end GroupRingTopology.PathSquares
namespace GroupRingTopology.Cayley
open Set Metric Topology Attachment
open scoped unitInterval

variable {G : Type u} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)

variable {Y : Type v} [TopologicalSpace Y] (f : C(Graph s,Y)) (y : Y)
variable (p : ∀ g, Path y (f (vertex s g)))
variable (hp : ∀ g i, ((p g).trans ((edge s g i).map f.continuous)).Homotopic (p (g*s i)))
end GroupRingTopology.Cayley
open Set Metric Topology

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Cellular
open Set Metric Topology
variable {Y : Type*} [TopologicalSpace Y]

end GroupRingTopology.Cellular
namespace GroupRingTopology.LoopSphere
open Set Metric Topology Cellular
open scoped unitInterval
variable {X : Type u} [TopologicalSpace X] {x : X}

variable {Y : Type v} [TopologicalSpace Y]
end GroupRingTopology.LoopSphere

/-! The path-class extension of an acting group. This is geometric support for
the finite presentation Cayley cover, not an assumption of simple connectivity. -/

namespace GroupRingTopology.PathExtension

section
open Path.Homotopic
variable {X : Type u} [TopologicalSpace X]

namespace Q
variable {x y z : X}

namespace Equal
end Equal

end Q

variable {G : Type v} [_root_.Group G] [MulAction G X] [ContinuousConstSMul G X]

variable (G) (x₀ : X)
variable {G x₀}

instance : One (Extension G x₀) :=
  ⟨⟨1,(Path.Homotopic.Quotient.refl x₀).cast rfl (one_smul G x₀)⟩⟩
instance : Mul (Extension G x₀) :=
  ⟨fun a b => ⟨a.1*b.1,(a.2.trans (b.2.map (smulMap a.1))).cast rfl (mul_smul ..)⟩⟩
instance : Inv (Extension G x₀) :=
  ⟨fun a => ⟨a.1⁻¹,((a.2.map (smulMap a.1⁻¹)).symm).cast (inv_smul_smul a.1 x₀).symm rfl⟩⟩

instance : Group (Extension G x₀) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := inv_mul_cancel

end
open Path.Homotopic
variable {G : Type u} [_root_.Group G]
variable {X : Type v} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable {Y : Type w} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable (f : C(X,Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

variable (x₀ : X)
end GroupRingTopology.PathExtension
namespace GroupRingTopology.Cayley
open Set Metric Topology Attachment PathExtension
open scoped unitInterval
variable {G : Type u} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)

variable (rels : Set (FreeGroup S)) (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
end GroupRingTopology.Cayley

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Cayley

section
open Set Metric Topology Attachment PathExtension
open scoped unitInterval
variable {G : Type u} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)
variable {Y : Type v} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable (f : C(Graph s,Y)) (hf : ∀ (g : G) x, f (g • x) = g • f x)

variable (τ : G →* PathExtension.Extension G (f (vertex s 1)))
variable (hτ : ∀ g, (τ g).1 = g)

variable (hgen : ∀ i, Q.Equal (τ (s i)).2 (Path.Homotopic.Quotient.mk ((edge s 1 i).map f.continuous)))
end
open PathExtension Attachment
variable {G : Type u} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G) (rels : Set (FreeGroup S))
variable (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
variable (hs : Function.Surjective (FreeGroup.lift s))
variable (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels)
end GroupRingTopology.Cayley
namespace GroupRingTopology.Attachment
open Set Metric Topology
variable {G : Type u} [_root_.Group G]
variable {X : Type v} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable {Y : Type w} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable {ι : Type z} {n : ℕ} (a : ι → C(Sphere n,X))
end GroupRingTopology.Attachment

namespace GroupRingTopology.Milnor
open Set Metric Topology Attachment
variable {G : Type u} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {A : Type u} (s : A → G)

variable (rels : Set (FreeGroup A)) (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
end GroupRingTopology.Milnor

namespace GroupRingTopology.Attachment
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X))

end GroupRingTopology.Attachment

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Attachment
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X))

end GroupRingTopology.Attachment

open Set Topology
namespace GroupRingTopology.Cellular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

end GroupRingTopology.Cellular
open Set Metric Topology
open scoped NNReal
namespace GroupRingTopology.GeneralPosition

section
variable {K : Type*} [MetricSpace K] [CompactSpace K]

end

section
open Set Metric Topology
open scoped NNReal ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K]

end

open Set Metric Topology
open scoped NNReal ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K]

end GroupRingTopology.GeneralPosition

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal

namespace GroupRingTopology.Cellular

section
open Set Metric Topology
open scoped ENNReal NNReal
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {n : ℕ}

variable {K : Type*} [MetricSpace K]

end

section
open Set Metric Topology
open scoped ENNReal NNReal
variable {Y : Type*} [TopologicalSpace Y] {n : ℕ}
variable {K : Type*} [MetricSpace K]

end

open Set Metric Topology
open scoped ENNReal NNReal
section
variable {Y : Type*} [TopologicalSpace Y] {K : Type*} [TopologicalSpace K]

end
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {n : ℕ}
variable {K : Type*} [MetricSpace K] [CompactSpace K] {ι : Type*}
variable (e : ι → C(ChartDisk n,Y)) (he : ∀ i, IsOpenEmbedding (e i))
variable (hd : Pairwise (fun i j => Disjoint (Set.range (e i)) (Set.range (e j))))

end GroupRingTopology.Cellular

namespace GroupRingTopology.Attachment
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X)) [T2Space (Space a)]
variable {K : Type*} [MetricSpace K] [CompactSpace K]

end GroupRingTopology.Attachment
open Set Metric Topology
open scoped NNReal ENNReal
namespace GroupRingTopology.GeneralPosition

end GroupRingTopology.GeneralPosition

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal

namespace GroupRingTopology.Attachment

section
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X)) [T2Space (Space a)]

end
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
variable {ι : Type*} {n : ℕ} (a : ι → C(Sphere n,X)) [Nonempty (Sphere n)]
end GroupRingTopology.Attachment

namespace GroupRingTopology.Cayley
open Set Metric Topology Attachment
variable {G : Type u} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G) (rels : Set (FreeGroup S))
variable (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
variable (hs : Function.Surjective (FreeGroup.lift s))
variable (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels)
end GroupRingTopology.Cayley

namespace GroupRingTopology
variable {G : Type u} [_root_.Group G] {A : Type v} [MulAction G A]

variable (hfree : ∀ (g : G) (a : A), g • a = a → g = 1)

end GroupRingTopology

open Set Metric Topology
namespace GroupRingTopology.Cellular
variable {G : Type u} [_root_.Group G] {X : Type u} [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X]
variable [CWComplex (univ : Set X)] {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)

variable
  (ho : ∀ n (g : G) (i : ι n),
    (fun x : X => g • x) '' RelCWComplex.openCell n (σ n (1,i)) = RelCWComplex.openCell n (σ n (g,i)))
  (hc : ∀ n (g : G) (i : ι n),
    (fun x : X => g • x) '' RelCWComplex.closedCell n (σ n (1,i)) = RelCWComplex.closedCell n (σ n (g,i)))

variable [T2Space X]
end GroupRingTopology.Cellular

namespace GroupRingTopology.Milnor
open Set Metric Topology GroupRingTopology.Simplicial
variable (G : Type u) [_root_.Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

end GroupRingTopology.Milnor

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology

namespace GroupRingTopology.Cellular

section
open Set Metric Topology
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]
end

section
open Set Metric Topology
variable {G : Type u} [_root_.Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)

variable {E : Type u} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]
end

section
open Set Metric Topology
variable {G : Type u} [_root_.Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G B]
end

open Set Metric Topology
variable {G : Type u} [_root_.Group G] {X : Type u} [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
variable {ι : ℕ → Type u}
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)
variable (hσ : ∀ n (g h : G) (i : ι n) (x : Fin n → ℝ),
  RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x)

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G B]

variable {Y : Type u} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
end GroupRingTopology.Cellular

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology

namespace GroupRingTopology.Cellular
open Set Metric Topology
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]
variable {K : Type v} [MetricSpace K] [CompactSpace K]
end GroupRingTopology.Cellular
namespace GroupRingTopology.SphereTopology
open Set Metric Topology
variable {Y : Type u} [TopologicalSpace Y]
end GroupRingTopology.SphereTopology
namespace GroupRingTopology.Cellular
open Set Metric Topology
variable {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

namespace PartialHomotopy
variable {f g : C(X,Y)} {n : ℕ}

end PartialHomotopy
end GroupRingTopology.Cellular

namespace TorsionFreeZeroDivisors.FiniteDimensionalCW
open Set Metric Topology GroupRingTopology GroupRingTopology.Cellular
variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]
end TorsionFreeZeroDivisors.FiniteDimensionalCW

namespace TorsionFreeZeroDivisors.PresentationTopology
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
variable {G S : Type} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (s : S → G)

variable (rels : Set (FreeGroup S)) (hrel : ∀ r ∈ rels, FreeGroup.lift s r=1)

variable (hs : Function.Surjective (FreeGroup.lift s))
  (hker : (FreeGroup.lift s).ker=Subgroup.normalClosure rels)

end TorsionFreeZeroDivisors.PresentationTopology

end

end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.GraphConeCW
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
open GroupRingTopology.Cellular hiding Disk Sphere boundary
open scoped unitInterval Classical
noncomputable section
lemma cons_tail_time {n : ℕ} (d : Disk (n+1)) : diskCons (diskTail d) (diskTime d)=d := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [diskCons,diskTime,Fin.cons_zero]
    ring
  · rfl
lemma cylinder_side {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (a : C(Sphere n,C(I,Y))) (b : C(Disk n,Y×Y))
    (h : ∀x,pathEndpoint (a x)=b (boundary n x)) (x : Sphere n) (t : I) :
    cylinderBoundaryMap a b h ⟨_,cons_mem_sphere_of_boundary x t⟩=a x t := by
  let z : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
  have hz : z∈cylinderFace n none := by
    change (diskTail (diskCons (boundary n x) t)).1∈sphere 0 1
    rw [diskTail_cons]
    exact x.2
  rw [cylinderBoundaryMap_face a b h none ⟨z,hz⟩]
  change a (faceSphere ⟨z,hz⟩) (diskTime (diskCons (boundary n x) t))=a x t
  rw [diskTime_cons]
  congr 1
lemma cylinder_bottom {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (a : C(Sphere n,C(I,Y))) (b : C(Disk n,Y×Y))
    (h : ∀x,pathEndpoint (a x)=b (boundary n x)) (d : Disk n) :
    cylinderBoundaryMap a b h ⟨_,cons_zero_mem_sphere d⟩=(b d).1 := by
  let z : Sphere (n+1) := ⟨_,cons_zero_mem_sphere d⟩
  have hz : z∈cylinderFace n (some false) := by norm_num [z,cylinderFace,diskCons]
  rw [cylinderBoundaryMap_face a b h (some false) ⟨z,hz⟩]
  change (b (diskTail (diskCons d 0))).1=_
  rw [diskTail_cons]
lemma cylinder_top {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (a : C(Sphere n,C(I,Y))) (b : C(Disk n,Y×Y))
    (h : ∀x,pathEndpoint (a x)=b (boundary n x)) (d : Disk n) :
    cylinderBoundaryMap a b h ⟨_,cons_one_mem_sphere d⟩=(b d).2 := by
  let z : Sphere (n+1) := ⟨_,cons_one_mem_sphere d⟩
  have hz : z∈cylinderFace n (some true) := by norm_num [z,cylinderFace,diskCons]
  rw [cylinderBoundaryMap_face a b h (some true) ⟨z,hz⟩]
  change (b (diskTail (diskCons d 1))).2=_
  rw [diskTail_cons]
variable {V E : Type*} (src dst : E→V)
local instance : TopologicalSpace (Option V) := ⊥
local instance : DiscreteTopology (Option V) := ⟨rfl⟩
def endpoint : V⊕E → Bool → Option V
  | .inl v,false => some v
  | .inl _,true => none
  | .inr e,false => some (src e)
  | .inr e,true => some (dst e)
def oneBoundary (i : V⊕E) : C(Sphere 1,Option V) :=
  ⟨fun x=>endpoint src dst i (if x=Cayley.minus then false else true),continuous_of_discreteTopology⟩
abbrev One := Space (oneBoundary src dst)
def vertex (v : Option V) : One src dst := base _ v
lemma minus_ne_plus : Cayley.minus≠Cayley.plus := by
  intro he
  have := congrArg (fun x : Sphere 1=>x.1 0) he
  norm_num [Cayley.minus,Cayley.plus] at this
@[simp] lemma oneBoundary_minus (i : V⊕E) : oneBoundary src dst i Cayley.minus=endpoint src dst i false := by
  simp [oneBoundary]
@[simp] lemma oneBoundary_plus (i : V⊕E) : oneBoundary src dst i Cayley.plus=endpoint src dst i true := by
  simp [oneBoundary,Ne.symm minus_ne_plus]
def radial (v : V) : C(I,One src dst) := (cell _ (.inl v)).comp ⟨Cayley.edgeParam,Cayley.continuous_edgeParam⟩
def outer (e : E) : C(Disk 1,One src dst) := cell _ (.inr e)
@[simp] lemma radial_zero (v : V) : radial src dst v 0=vertex src dst (some v) := by
  change cell _ _ (Cayley.edgeParam 0)=_
  rw [Cayley.edgeParam_zero,cell_boundary,oneBoundary_minus]
  rfl
@[simp] lemma radial_one (v : V) : radial src dst v 1=vertex src dst none := by
  change cell _ _ (Cayley.edgeParam 1)=_
  rw [Cayley.edgeParam_one,cell_boundary,oneBoundary_plus]
  rfl
@[simp] lemma outer_minus (e : E) : outer src dst e (boundary 1 Cayley.minus)=vertex src dst (some (src e)) := by
  change cell _ _ (boundary 1 Cayley.minus)=_
  rw [cell_boundary,oneBoundary_minus]
  rfl
@[simp] lemma outer_plus (e : E) : outer src dst e (boundary 1 Cayley.plus)=vertex src dst (some (dst e)) := by
  change cell _ _ (boundary 1 Cayley.plus)=_
  rw [cell_boundary,oneBoundary_plus]
  rfl
def sides (e : E) : C(Sphere 1,C(I,One src dst)) :=
  ⟨fun x=>radial src dst (if x=Cayley.minus then src e else dst e),continuous_of_discreteTopology⟩
def ends (e : E) : C(Disk 1,One src dst × One src dst) :=
  ⟨fun d=>(outer src dst e d,vertex src dst none),(outer src dst e).continuous.prodMk continuous_const⟩
lemma compatible (e : E) (x : Sphere 1) : pathEndpoint (sides src dst e x)=ends src dst e (boundary 1 x) := by
  rcases Cayley.sphere_one_eq x with rfl|rfl <;>
    simp [pathEndpoint,sides,ends,Ne.symm minus_ne_plus]
def twoBoundary (e : E) : C(Sphere 2,One src dst) := cylinderBoundaryMap (sides src dst e) (ends src dst e) (compatible src dst e)
abbrev Cone := Space (twoBoundary src dst)
def inclusion : C(One src dst,Cone src dst) := ⟨base _,continuous_base _⟩
def apex : Cone src dst := inclusion src dst (vertex src dst none)
def square (e : E) : C(Disk 2,Cone src dst) := cell _ e
lemma square_side (e : E) (x : Sphere 1) (t : I) :
    square src dst e (diskCons (boundary 1 x) t)=inclusion src dst (sides src dst e x t) := by
  change cell _ e (boundary 2 ⟨_,cons_mem_sphere_of_boundary x t⟩)=_
  rw [cell_boundary]
  exact congrArg (inclusion src dst) (cylinder_side _ _ _ x t)
lemma square_bottom (e : E) (d : Disk 1) :
    square src dst e (diskCons d 0)=inclusion src dst (outer src dst e d) := by
  change cell _ e (boundary 2 ⟨_,cons_zero_mem_sphere d⟩)=_
  rw [cell_boundary]
  exact congrArg (inclusion src dst) (cylinder_bottom _ _ _ d)
lemma square_top (e : E) (d : Disk 1) : square src dst e (diskCons d 1)=apex src dst := by
  change cell _ e (boundary 2 ⟨_,cons_one_mem_sphere d⟩)=_
  rw [cell_boundary]
  exact congrArg (inclusion src dst) (cylinder_top _ _ _ d)
def joinTime (r t : I) : I := ⟨r.1+(1-r.1)*t.1,by
  constructor
  · nlinarith [r.2.1,r.2.2,t.2.1,t.2.2]
  · nlinarith [r.2.1,r.2.2,t.2.1,t.2.2]⟩
lemma continuous_joinTime : Continuous (fun p : I×I=>joinTime p.1 p.2) := by
  unfold joinTime
  fun_prop
@[simp] lemma joinTime_zero (r : I) : joinTime r 0=r := by ext; simp [joinTime]
@[simp] lemma joinTime_one (r : I) : joinTime r 1=1 := by ext; simp [joinTime]
@[simp] lemma zero_joinTime (t : I) : joinTime 0 t=t := by ext; simp [joinTime]
@[simp] lemma one_joinTime (t : I) : joinTime 1 t=1 := by ext; simp [joinTime]
def vertexPaths : C(Option V,C(I,Cone src dst)) :=
  ⟨fun v=>match v with
    | none => .const _ (apex src dst)
    | some v => (inclusion src dst).comp (radial src dst v),continuous_of_discreteTopology⟩
def radialPaths (v : V) : C(Disk 1,C(I,Cone src dst)) :=
  (⟨fun p : Disk 1×I=>inclusion src dst (radial src dst v (joinTime (Cayley.edgeTime p.1) p.2)),
    (inclusion src dst).continuous.comp ((radial src dst v).continuous.comp
      (continuous_joinTime.comp ((Cayley.continuous_edgeTime.comp continuous_fst).prodMk continuous_snd)))⟩ :
    C(Disk 1×I,Cone src dst)).curry
def outerPaths (e : E) : C(Disk 1,C(I,Cone src dst)) :=
  ((square src dst e).comp ⟨fun p : Disk 1×I=>diskCons p.1 p.2,continuous_diskCons⟩).curry
def edgePaths : V⊕E → C(Disk 1,C(I,Cone src dst)) := Sum.elim (radialPaths src dst) (outerPaths src dst)
lemma edgePaths_boundary (i : V⊕E) (x : Sphere 1) :
    edgePaths src dst i (boundary 1 x)=vertexPaths src dst (oneBoundary src dst i x) := by
  ext t
  cases i with
  | inl v =>
    rcases Cayley.sphere_one_eq x with rfl|rfl
    · change inclusion src dst (radial src dst v (joinTime (Cayley.edgeTime (boundary 1 Cayley.minus)) t))=_
      simp [Cayley.edgeTime_minus,vertexPaths,endpoint]
    · change inclusion src dst (radial src dst v (joinTime (Cayley.edgeTime (boundary 1 Cayley.plus)) t))=_
      simp [Cayley.edgeTime_plus,vertexPaths,endpoint,apex]
  | inr e =>
    change square src dst e (diskCons (boundary 1 x) t)=_
    rw [square_side]
    rcases Cayley.sphere_one_eq x with rfl|rfl <;>
      simp [sides,vertexPaths,endpoint,Ne.symm minus_ne_plus]
def onePaths : C(One src dst,C(I,Cone src dst)) :=
  lift _ (vertexPaths src dst) (edgePaths src dst) (edgePaths_boundary src dst)
@[simp] lemma onePaths_vertex (v : Option V) : onePaths src dst (vertex src dst v)=vertexPaths src dst v := rfl
@[simp] lemma onePaths_outer (e : E) (d : Disk 1) (t : I) :
    onePaths src dst (outer src dst e d) t=square src dst e (diskCons d t) := by
  change onePaths src dst (cell (oneBoundary src dst) (.inr e) d) t=_
  simp only [onePaths,lift_cell]
  rfl
@[simp] lemma onePaths_radial (v : V) (r t : I) :
    onePaths src dst (radial src dst v r) t=inclusion src dst (radial src dst v (joinTime r t)) := by
  change onePaths src dst (cell (oneBoundary src dst) (.inl v) (Cayley.edgeParam r)) t=_
  simp only [onePaths,lift_cell]
  change inclusion src dst (radial src dst v (joinTime (Cayley.edgeTime (Cayley.edgeParam r)) t))=_
  rw [Cayley.edgeTime_param]
def squarePaths (e : E) : C(Disk 2,C(I,Cone src dst)) :=
  (⟨fun p : Disk 2×I=>square src dst e (diskCons (diskTail p.1) (joinTime (diskTime p.1) p.2)),
    (square src dst e).continuous.comp (continuous_diskCons.comp
      ((continuous_diskTail.comp continuous_fst).prodMk (continuous_joinTime.comp
      ((continuous_diskTime.comp continuous_fst).prodMk continuous_snd))))⟩ : C(Disk 2×I,Cone src dst)).curry
lemma squarePaths_boundary (e : E) (x : Sphere 2) :
    squarePaths src dst e (boundary 2 x)=onePaths src dst (twoBoundary src dst e x) := by
  ext t
  change square src dst e (diskCons (diskTail (boundary 2 x)) (joinTime (diskTime (boundary 2 x)) t))=_
  rcases sphere_split x with hz|ho|hs
  · have ht : diskTime (boundary 2 x)=0 := faceTime_eq_zero x hz
    rw [ht,zero_joinTime]
    have hx : twoBoundary src dst e x=outer src dst e (diskTail (boundary 2 x)) := by
      exact cylinderBoundaryMap_face _ _ _ (some false) ⟨x,hz⟩
    rw [hx,onePaths_outer]
  · have ht : diskTime (boundary 2 x)=1 := faceTime_eq_one x ho
    rw [ht,one_joinTime,square_top]
    have hx : twoBoundary src dst e x=vertex src dst none := by
      exact cylinderBoundaryMap_face _ _ _ (some true) ⟨x,ho⟩
    rw [hx,onePaths_vertex]
    rfl
  · let z : Sphere 1 := ⟨(diskTail (boundary 2 x)).1,hs⟩
    have hx : twoBoundary src dst e x=sides src dst e z (diskTime (boundary 2 x)) :=
      cylinderBoundaryMap_face _ _ _ none ⟨x,hs⟩
    rw [hx]
    change square src dst e (diskCons (boundary 1 z) (joinTime (diskTime (boundary 2 x)) t))=_
    rw [square_side]
    change inclusion src dst (radial src dst (if z=Cayley.minus then src e else dst e) _)=
      onePaths src dst (radial src dst (if z=Cayley.minus then src e else dst e) _) _
    rw [onePaths_radial]
def contractionPaths : C(Cone src dst,C(I,Cone src dst)) :=
  lift _ (onePaths src dst) (squarePaths src dst) (squarePaths_boundary src dst)
lemma onePaths_zero (z : One src dst) : onePaths src dst z 0=inclusion src dst z := by
  obtain ⟨q,rfl⟩ := quotient_surjective (oneBoundary src dst) z
  cases q with
  | inl v =>
    change vertexPaths src dst v 0=inclusion src dst (vertex src dst v)
    cases v <;> simp [vertexPaths,apex]
  | inr p =>
    change onePaths src dst (cell (oneBoundary src dst) p.1 p.2) 0=_
    simp only [onePaths,lift_cell]
    rcases p with ⟨v|e,d⟩
    · change inclusion src dst (radial src dst v (joinTime (Cayley.edgeTime d) 0))=_
      rw [joinTime_zero]
      change inclusion src dst (cell _ (.inl v) (Cayley.edgeParam (Cayley.edgeTime d)))=_
      rw [Cayley.edgeParam_time]
      rfl
    · exact square_bottom src dst e d
lemma onePaths_one (z : One src dst) : onePaths src dst z 1=apex src dst := by
  obtain ⟨q,rfl⟩ := quotient_surjective (oneBoundary src dst) z
  cases q with
  | inl v =>
    change vertexPaths src dst v 1=apex src dst
    cases v <;> simp [vertexPaths,apex]
  | inr p =>
    change onePaths src dst (cell (oneBoundary src dst) p.1 p.2) 1=_
    simp only [onePaths,lift_cell]
    rcases p with ⟨v|e,d⟩
    · change inclusion src dst (radial src dst v (joinTime (Cayley.edgeTime d) 1))=_
      rw [joinTime_one,radial_one]
      rfl
    · exact square_top src dst e d
def contraction : (ContinuousMap.id (Cone src dst)).Homotopy (.const _ (apex src dst)) where
  toFun p := contractionPaths src dst p.2 p.1
  continuous_toFun := (contractionPaths src dst).uncurry.continuous.comp continuous_swap
  map_zero_left z := by
    obtain ⟨q,rfl⟩ := quotient_surjective (twoBoundary src dst) z
    cases q with
    | inl v => exact onePaths_zero src dst v
    | inr p =>
      change contractionPaths src dst (cell (twoBoundary src dst) p.1 p.2) 0=_
      simp only [contractionPaths,lift_cell]
      change square src dst p.1 (diskCons (diskTail p.2) (joinTime (diskTime p.2) 0))=_
      rw [joinTime_zero,cons_tail_time]
      rfl
  map_one_left z := by
    obtain ⟨q,rfl⟩ := quotient_surjective (twoBoundary src dst) z
    cases q with
    | inl v => exact onePaths_one src dst v
    | inr p =>
      change contractionPaths src dst (cell (twoBoundary src dst) p.1 p.2) 1=_
      simp only [contractionPaths,lift_cell]
      change square src dst p.1 (diskCons (diskTail p.2) (joinTime (diskTime p.2) 1))=_
      rw [joinTime_one,square_top]
      rfl
instance contractible : ContractibleSpace (Cone src dst) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨apex src dst,⟨contraction src dst⟩⟩
end
end TorsionFreeZeroDivisors.GraphConeCW


end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GraphConeCW
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
open scoped unitInterval Classical
variable {V E : Type} (src dst : E→V)
local instance optionVertexTopology : TopologicalSpace (Option V) := ⊥
local instance optionVertexDiscreteTopology : DiscreteTopology (Option V) := ⟨rfl⟩
instance oneNonempty : Nonempty (One src dst) := ⟨vertex src dst none⟩
lemma zero_dimension (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set (Option V)) n) : n<1 := by
  cases n with
  | zero => omega
  | succ n => exact i.elim
instance oneCW : CWComplex (Set.univ : Set (One src dst)) := layerCW _ zero_dimension
instance oneT2 : T2Space (One src dst) := t2Space _ realSeparated_of_tychonoff
lemma one_dimension (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set (One src dst)) n) : n<2 :=
  layerCW_dimensions _ zero_dimension n i
instance coneCW : CWComplex (Set.univ : Set (Cone src dst)) := layerCW _ (one_dimension src dst)
instance coneT2 : T2Space (Cone src dst) := t2Space _ (realSeparated _ realSeparated_of_tychonoff)
variable {Y : Type*} [TopologicalSpace Y]
variable (v : C(Option V,Y)) (ed : V⊕E→C(Disk 1,Y))
    (hed : ∀i x,ed i (boundary 1 x)=v (oneBoundary src dst i x))
def mapOne : C(One src dst,Y) := lift _ v ed hed
@[simp] lemma mapOne_vertex (x : Option V) : mapOne src dst v ed hed (vertex src dst x)=v x := rfl
@[simp] lemma mapOne_edge (i : V⊕E) (d : Disk 1) : mapOne src dst v ed hed (cell (oneBoundary src dst) i d)=ed i d :=
  lift_cell _ _ _ _ i d
variable (sq : E→C(Disk 2,Y)) (hsq : ∀e x,sq e (boundary 2 x)=mapOne src dst v ed hed (twoBoundary src dst e x))
def mapCone : C(Cone src dst,Y) := lift _ (mapOne src dst v ed hed) sq hsq
@[simp] lemma mapCone_one (x : One src dst) : mapCone src dst v ed hed sq hsq (inclusion src dst x)=mapOne src dst v ed hed x := rfl
@[simp] lemma mapCone_square (e : E) (d : Disk 2) : mapCone src dst v ed hed sq hsq (square src dst e d)=sq e d :=
  lift_cell _ _ _ _ e d
end TorsionFreeZeroDivisors.GraphConeCW

namespace TorsionFreeZeroDivisors.CellPresentation
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment GroupRingTopology.PathExtension
open scoped unitInterval
variable {G S Q : Type} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (s : S→G) (a : Q→C(Sphere 2,Cayley.Graph s))
abbrev Cover := Space (equivariantFamily (G:=G) a)
def inclusion : C(Cayley.Graph s,Cover s a) := ⟨base _,continuous_base _⟩
lemma inclusion_smul (g : G) (x : Cayley.Graph s) : inclusion s a (g • x)=g • inclusion s a x := rfl
def wordLift : FreeGroup S →* Extension G (inclusion s a (Cayley.vertex s 1)) :=
  (PathExtension.map (inclusion s a) (inclusion_smul s a) (Cayley.vertex s 1)).comp (Cayley.wordLift s)
variable (rel : Q→FreeGroup S) (ha : ∀q,wordLift s a (rel q)=1)
variable (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker=Subgroup.normalClosure (Set.range rel))
include ha hker in
lemma wordLift_ker : (FreeGroup.lift s).ker≤(wordLift s a).ker := by
  rw [hker]
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨q,rfl⟩
  exact ha q
def sectionMap : G →* Extension G (inclusion s a (Cayley.vertex s 1)) :=
  (FreeGroup.lift s).liftOfSurjective hs ⟨wordLift s a,wordLift_ker s a rel ha hker⟩
lemma sectionMap_lift (w : FreeGroup S) :
    sectionMap s a rel ha hs hker (FreeGroup.lift s w)=wordLift s a w :=
  MonoidHom.liftOfRightInverse_comp_apply ..
lemma sectionMap_fst (g : G) : (sectionMap s a rel ha hs hker g).1=g := by
  obtain ⟨w,rfl⟩ := hs g
  rw [sectionMap_lift]
  exact Cayley.wordLift_fst s w
lemma sectionMap_generator (i : S) : PathExtension.Q.Equal
    (sectionMap s a rel ha hs hker (s i)).2
    (Path.Homotopic.Quotient.mk ((Cayley.edge s 1 i).map (inclusion s a).continuous)) := by
  have hh : sectionMap s a rel ha hs hker (s i)=
      PathExtension.map (inclusion s a) (inclusion_smul s a) (Cayley.vertex s 1)
        (Cayley.pathGenerator s i) := by
    simpa only [FreeGroup.lift_apply_of,wordLift,MonoidHom.comp_apply,Cayley.wordLift]
      using sectionMap_lift s a rel ha hs hker (FreeGroup.of i)
  rw [hh]
  exact (PathExtension.mapFun_equal (inclusion s a) (inclusion_smul s a)
    (Cayley.vertex s 1) (Cayley.pathGenerator s i)).trans
      ((Cayley.pathGenerator_equal s i).map (inclusion s a))
def graphNullhomotopy : (inclusion s a).Homotopy
    (.const _ (inclusion s a (Cayley.vertex s 1))) :=
  Cayley.nullhomotopyOfSection s (inclusion s a) (inclusion_smul s a)
    (sectionMap s a rel ha hs hker) (sectionMap_fst s a rel ha hs hker)
    (sectionMap_generator s a rel ha hs hker)
instance coverT2 : T2Space (Cover s a) :=
  t2Space _ (realSeparated _ (realSeparated_of_tychonoff (Y:=G)))
instance coverCW : CWComplex (Set.univ : Set (Cover s a)) :=
  layerCW _ (Cayley.graph_dimension s)
include hs in
lemma cover_pathConnected : PathConnectedSpace (Cover s a) := by
  have hgen : Subgroup.closure (Set.range s)=⊤ := by
    rw [←FreeGroup.range_lift_eq_closure,MonoidHom.range_eq_top]
    exact hs
  let := Cayley.graph_pathConnected s hgen
  let := SphereTopology.sphere_nonempty 1
  exact Attachment.pathConnectedSpace _
include ha hs hker in
lemma cover_circleFill (b : C(Sphere 2,Cover s a)) : SphereTopology.Extends b := by
  let := SphereTopology.sphere_nonempty 1
  have hdim : dimH (Set.univ : Set (Sphere 2))<2 :=
    (GeneralPosition.dimH_cube_boundary_subtype_le 1).trans_lt (by norm_num)
  obtain ⟨g,H,_⟩ := exists_deformation_into_base _ b hdim
  apply SphereTopology.extends_of_homotopy H
  exact SphereTopology.extends_of_nullhomotopic
    (((graphNullhomotopy s a rel ha hs hker).compContinuousMap g).symm)
include ha hs hker in
lemma cover_simplyConnected : SimplyConnectedSpace (Cover s a) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨cover_pathConnected s a hs,?_⟩
  intro x p
  obtain ⟨F,hF⟩ := cover_circleFill s a rel ha hs hker (LoopSphere.map p)
  apply LoopSphere.homotopic_of_fill p F
  intro z
  exact ContinuousMap.congr_fun hF z

def diskAttaching : Q→C(Sphere 2,PresentationTopology.Rose s) := fun q=>
  (PresentationTopology.graphProjection s).comp (a q)
abbrev Base := Space (diskAttaching s a)
def projection : C(Cover s a,Base s a) :=
  coverMap a (PresentationTopology.graphProjection s)
    (PresentationTopology.graphProjection_quotient s) (diskAttaching s a) (fun _ _=>rfl)
lemma projection_quotient : IsQuotientCoveringMap (projection s a) G :=
  coverMap_isQuotientCovering _ _ _ _ _
instance baseT2 : T2Space (Base s a) := t2Space _ (realSeparated _ realSeparated_of_tychonoff)
instance baseCW : CWComplex (Set.univ : Set (Base s a)) :=
  layerCW _ (PresentationTopology.rose_dimension s)
lemma base_dimension (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set (Base s a)) m) : m < 3 :=
  layerCW_dimensions _ (PresentationTopology.rose_dimension s) m i
lemma base_no_higher (m : ℕ) (hm : 2 < m) : IsEmpty (RelCWComplex.cell (Set.univ : Set (Base s a)) m) :=
  ⟨fun i=>by have := base_dimension s a m i; omega⟩
lemma base_finite [Finite S] [Finite Q] : CWComplex.Finite (Set.univ : Set (Base s a)) where
  eventually_isEmpty_cell := Filter.eventually_atTop.mpr ⟨3,fun m hm=>base_no_higher s a m (by omega)⟩
  finite_cell m := layerCW_finite_cells _ (PresentationTopology.rose_finite s) (PresentationTopology.rose_dimension s) m
lemma base_two_cell [Nonempty Q] : Nonempty (RelCWComplex.cell (Set.univ : Set (Base s a)) 2) :=
  ⟨Sum.inr ⟨⟨⟨rfl⟩,Classical.choice inferInstance⟩⟩⟩
instance basePathConnected : PathConnectedSpace (Base s a) := by
  let := SphereTopology.sphere_nonempty 1
  exact Attachment.pathConnectedSpace _
def coverPoint : Cover s a := inclusion s a (Cayley.vertex s 1)
def basePoint : Base s a := projection s a (coverPoint s a)
def fundamentalEquiv : G ≃* FundamentalGroup (Base s a) (basePoint s a) := by
  let := cover_simplyConnected s a rel ha hs hker
  exact (MulEquiv.inv' G).trans
    ((projection_quotient s a).fundamentalGroupEquiv ⟨coverPoint s a,rfl⟩).symm
end TorsionFreeZeroDivisors.CellPresentation
namespace TorsionFreeZeroDivisors.ConeCells
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment GroupRingTopology.PathExtension
open scoped unitInterval Classical
variable {G S V E : Type} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (s : S→G)
def wordClass (w : FreeGroup S) : Path.Homotopic.Quotient (Cayley.vertex s 1) (Cayley.vertex s (FreeGroup.lift s w)) :=
  (Cayley.wordLift s w).2.cast rfl (by rw [Cayley.wordLift_fst,Cayley.smul_vertex,_root_.mul_one])
def wordPath (w : FreeGroup S) : Path (Cayley.vertex s 1) (Cayley.vertex s (FreeGroup.lift s w)) :=
  (Path.Homotopic.Quotient.mk_surjective (wordClass s w)).choose
variable (src dst : E→V) (z : V→FreeGroup S) (lab : E→FreeGroup S)
variable (he : ∀e,FreeGroup.lift s (z (src e))*FreeGroup.lift s (lab e)=FreeGroup.lift s (z (dst e)))
def outerPath (e : E) : Path (Cayley.vertex s (FreeGroup.lift s (z (src e)))) (Cayley.vertex s (FreeGroup.lift s (z (dst e)))) :=
  ((wordPath s (lab e)).map (smulMap (FreeGroup.lift s (z (src e)))).continuous).cast
    (by simp [smulMap,Cayley.smul_vertex]) (by simpa only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex] using congrArg (Cayley.vertex s) (he e).symm)
local instance optionVertexTopology : TopologicalSpace (Option V) := ⊥
local instance optionVertexDiscreteTopology : DiscreteTopology (Option V) := ⟨rfl⟩
def vertexMap : C(Option V,Cayley.Graph s) :=
  ⟨fun v=>Cayley.vertex s (match v with | none=>1 | some v=>FreeGroup.lift s (z v)),continuous_of_discreteTopology⟩
def edgeMap : V⊕E→C(Disk 1,Cayley.Graph s)
  | .inl v => (wordPath s (z v)).symm.toContinuousMap.comp ⟨Cayley.edgeTime,Cayley.continuous_edgeTime⟩
  | .inr e => (outerPath s src dst z lab he e).toContinuousMap.comp ⟨Cayley.edgeTime,Cayley.continuous_edgeTime⟩
lemma edgeMap_boundary (i : V⊕E) (x : Sphere 1) :
    edgeMap s src dst z lab he i (boundary 1 x)=vertexMap s z (GraphConeCW.oneBoundary src dst i x) := by
  cases i with
  | inl v =>
    rcases Cayley.sphere_one_eq x with rfl|rfl <;>
      simp [edgeMap,Cayley.edgeTime_minus,Cayley.edgeTime_plus,GraphConeCW.endpoint,vertexMap]
  | inr e =>
    rcases Cayley.sphere_one_eq x with rfl|rfl <;>
      simp [edgeMap,Cayley.edgeTime_minus,Cayley.edgeTime_plus,GraphConeCW.endpoint,vertexMap]
def oneMap : C(GraphConeCW.One src dst,Cayley.Graph s) :=
  GraphConeCW.mapOne src dst (vertexMap s z) (edgeMap s src dst z lab he) (edgeMap_boundary s src dst z lab he)
def attaching (e : E) : C(Sphere 2,Cayley.Graph s) :=
  (oneMap s src dst z lab he).comp (GraphConeCW.twoBoundary src dst e)
abbrev Cover := CellPresentation.Cover s (attaching s src dst z lab he)
def coneMap : C(GraphConeCW.Cone src dst,Cover s src dst z lab he) :=
  lift _ ((CellPresentation.inclusion s (attaching s src dst z lab he)).comp (oneMap s src dst z lab he))
    (fun e=>cell _ (show FreeIndex G E from ((1:G),e))) (by
      intro e x
      rw [cell_boundary]
      simp only [equivariantFamily,ContinuousMap.coe_mk,one_smul]
      rfl)
@[simp] lemma coneMap_one (x : GraphConeCW.One src dst) :
    coneMap s src dst z lab he (GraphConeCW.inclusion src dst x)=
      CellPresentation.inclusion s (attaching s src dst z lab he) (oneMap s src dst z lab he x) := rfl
@[simp] lemma coneMap_square (e : E) (d : Disk 2) :
    coneMap s src dst z lab he (GraphConeCW.square src dst e d)=cell _ (show FreeIndex G E from ((1:G),e)) d := lift_cell _ _ _ _ e d
def coneRadial (v : V) : Path
    (GraphConeCW.inclusion src dst (GraphConeCW.vertex src dst (some v))) (GraphConeCW.apex src dst) where
  toFun t := GraphConeCW.inclusion src dst (GraphConeCW.radial src dst v t)
  continuous_toFun := (GraphConeCW.inclusion src dst).continuous.comp (GraphConeCW.radial src dst v).continuous
  source' := by rw [GraphConeCW.radial_zero]
  target' := by rw [GraphConeCW.radial_one]; rfl
@[simp] lemma coneRadial_apply (v : V) (t : I) : coneRadial src dst v t =
    GraphConeCW.inclusion src dst (GraphConeCW.radial src dst v t) := rfl
end TorsionFreeZeroDivisors.ConeCells

end

end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.DiskTracks
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
open GroupRingTopology.Cellular hiding Disk Sphere boundary
open scoped unitInterval
noncomputable section
variable {Y : Type} [TopologicalSpace Y] {y : Y} {p : Path y y}
def square (c : Path p (Path.refl y)) : C(Disk 2,Y) :=
  ⟨fun d=>c (diskTime d) (Cayley.edgeTime (diskTail d)),
   (Path.continuous_uncurry_iff.mpr c.continuous).comp
     (continuous_diskTime.prodMk (Cayley.continuous_edgeTime.comp continuous_diskTail))⟩
lemma square_boundary (c : Path p (Path.refl y)) (z : Sphere 2) :
    square c (boundary 2 z)=LoopSphere.map p z := by
  have hz : z∈⋃i,cylinderFace 1 i := by rw [cylinderFace_cover];trivial
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
  change _=cylinderBoundaryMap _ _ _ z
  rw [cylinderBoundaryMap_face _ _ _ i ⟨z,hi⟩]
  cases i with
  | none =>
    have he : diskTail (boundary 2 z)=boundary 1 (faceSphere ⟨z,hi⟩) := rfl
    change c (diskTime (boundary 2 z)) (Cayley.edgeTime (diskTail (boundary 2 z)))=y
    rw [he]
    obtain hh|hh := Cayley.sphere_one_eq (faceSphere ⟨z,hi⟩)
    · rw [hh,Cayley.edgeTime_minus,Path.source]
    · rw [hh,Cayley.edgeTime_plus,Path.target]
  | some b =>
    cases b
    · have ht : diskTime (boundary 2 z)=0 := by
        apply Subtype.ext
        change (z.1 0+1)/2=0
        change z.1 0= -1 at hi
        rw [hi];norm_num
      change c (diskTime (boundary 2 z)) (Cayley.edgeTime (diskTail (boundary 2 z)))=p _
      rw [ht,c.source];rfl
    · have ht : diskTime (boundary 2 z)=1 := by
        apply Subtype.ext
        change (z.1 0+1)/2=1
        change z.1 0=1 at hi
        rw [hi];norm_num
      change c (diskTime (boundary 2 z)) (Cayley.edgeTime (diskTail (boundary 2 z)))=y
      rw [ht,c.target];rfl
variable (F : C(Disk 2,Y)) (hF : ∀z,F (boundary 2 z)=LoopSphere.map p z)
def physical : Path p (Path.refl y) where
  toFun t := {
    toFun s := F (diskCons (Cayley.edgeParam s) t)
    continuous_toFun := F.continuous.comp (continuous_diskCons.comp
      (Cayley.continuous_edgeParam.prodMk continuous_const))
    source' := by
      rw [Cayley.edgeParam_zero]
      erw [hF ⟨_,cons_mem_sphere_of_boundary Cayley.minus t⟩]
      exact GraphConeCW.cylinder_side _ _ _ _ _
    target' := by
      rw [Cayley.edgeParam_one]
      erw [hF ⟨_,cons_mem_sphere_of_boundary Cayley.plus t⟩]
      exact GraphConeCW.cylinder_side _ _ _ _ _ }
  continuous_toFun := Path.continuous_uncurry_iff.mp (F.continuous.comp
    (continuous_diskCons.comp ((Cayley.continuous_edgeParam.comp continuous_snd).prodMk continuous_fst)))
  source' := by
    ext s
    change F (diskCons (Cayley.edgeParam s) 0)=p s
    erw [hF ⟨_,cons_zero_mem_sphere (Cayley.edgeParam s)⟩]
    unfold LoopSphere.map
    erw [GraphConeCW.cylinder_bottom]
    change p (Cayley.edgeTime (Cayley.edgeParam s))=p s
    rw [Cayley.edgeTime_param]
  target' := by
    ext s
    change F (diskCons (Cayley.edgeParam s) 1)=y
    erw [hF ⟨_,cons_one_mem_sphere (Cayley.edgeParam s)⟩]
    exact GraphConeCW.cylinder_top _ _ _ _
lemma square_physical : square (physical F hF)=F := by
  ext d
  change F (diskCons (Cayley.edgeParam (Cayley.edgeTime (diskTail d))) (diskTime d))=F d
  rw [Cayley.edgeParam_time,GraphConeCW.cons_tail_time]

def shift (t s : unitInterval) : unitInterval :=
  ⟨t+(1-t)*s,by constructor <;> nlinarith [t.2.1,t.2.2,s.2.1,s.2.2]⟩
lemma continuous_shift : Continuous (fun q : unitInterval×unitInterval=>shift q.1 q.2) := by
  apply Continuous.subtype_mk
  fun_prop
@[simp] lemma shift_zero (s : unitInterval) : shift 0 s=s := by ext;simp [shift]
@[simp] lemma shift_one (s : unitInterval) : shift 1 s=1 := by ext;simp [shift]
@[simp] lemma shift_zero_right (t : unitInterval) : shift t 0=t := by ext;simp [shift]
@[simp] lemma shift_one_right (t : unitInterval) : shift t 1=1 := by ext;simp [shift]
def tail (c : Path p (Path.refl y)) (t : unitInterval) : Path (c t) (Path.refl y) where
  toFun s:=c (shift t s)
  continuous_toFun:=c.continuous.comp (continuous_shift.comp (continuous_const.prodMk continuous_id))
  source':=by rw [shift_zero_right]
  target':=by rw [shift_one_right,c.target]
def contract (c : Path p (Path.refl y)) : (square c).Homotopy (.const _ y) where
  toFun z:=square (tail c z.1) z.2
  continuous_toFun := (Path.continuous_uncurry_iff.mpr c.continuous).comp
    ((continuous_shift.comp (continuous_fst.prodMk (continuous_diskTime.comp continuous_snd))).prodMk
      (Cayley.continuous_edgeTime.comp (continuous_diskTail.comp continuous_snd)))
  map_zero_left d := by change c (shift 0 (diskTime d)) _=c _ _;rw [shift_zero]
  map_one_left d := by change c (shift 1 (diskTime d)) _=y;rw [shift_one,c.target];rfl
lemma contract_boundary (c : Path p (Path.refl y)) (t : unitInterval) (z : Sphere 2) :
    contract c (t,boundary 2 z)=LoopSphere.map (c t) z := square_boundary (tail c t) z
end
end TorsionFreeZeroDivisors.DiskTracks

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.LoopTracks
open scoped Topology unitInterval
noncomputable section
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x y : X}

def piOneHomeo (e : X≃ₜY) (x : X) : FundamentalGroup X x≃*FundamentalGroup Y (e x) where
  toFun := Quotient.map (fun p : Path x x => p.map e.continuous)
    (fun _ _ h => h.map ⟨e,e.continuous⟩)
  invFun := Quotient.map (fun p : Path (e x) (e x) => (p.map e.symm.continuous).cast
    (e.symm_apply_apply x).symm (e.symm_apply_apply x).symm) (fun _ _ h => h.map ⟨e.symm,e.symm.continuous⟩)
  left_inv a := by
    induction a using Quotient.inductionOn with | h p =>
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.symm_apply_apply (p t)
  right_inv a := by
    induction a using Quotient.inductionOn with | h p =>
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.apply_symm_apply (p t)
  map_mul' a b := by
    induction a using Quotient.inductionOn with | h p =>
    induction b using Quotient.inductionOn with | h q =>
    exact congrArg Path.Homotopic.Quotient.mk (q.map_trans p e.continuous)

def uniqueLoopHomeo (N : Type*) [Unique N] (x : X) : GenLoop N X x≃ₜPath x x where
  toEquiv := genLoopEquivOfUnique N
  continuous_toFun := Path.continuous_uncurry_iff.mp (by
    change Continuous (fun z : GenLoop N X x × unitInterval => z.1 (fun _ => z.2))
    fun_prop)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : Path x x × (N→unitInterval) => z.1 (z.2 default))
    fun_prop

/-- The loop-space fundamental group is genuinely commutative (Eckmann-Hilton).
This is the coefficient group of two-cell homotopy-extension obstructions. -/
lemma loopGroup_comm (x : X) : ∀a b : FundamentalGroup (Path x x) (Path.refl x), a*b=b*a := by
  let N := {j : Bool // j≠true}
  let _ : Unique N := ⟨⟨false,by decide⟩,by intro a;rcases a with ⟨a,ha⟩;cases a <;> simp_all⟩
  let e : HomotopyGroup Bool X x≃* FundamentalGroup (GenLoop N X x) GenLoop.const :=
    { toEquiv := homotopyGroupEquivFundamentalGroup true
      map_mul' := by
        intro a b
        have h := HomotopyGroup.auxGroup_indep (X:=X) (x:=x) (Classical.arbitrary Bool) true
        apply Eq.trans (congrArg (fun i : Group (HomotopyGroup Bool X x) =>
          (homotopyGroupEquivFundamentalGroup true) (@Mul.mul _ i.toMul a b)) h)
        exact (homotopyGroupEquivFundamentalGroup true).apply_symm_apply _ }
  let f := piOneHomeo (uniqueLoopHomeo N x) GenLoop.const
  have hf : uniqueLoopHomeo N x GenLoop.const=Path.refl x := by ext t;rfl
  rw [←hf]
  intro a b
  obtain ⟨a,rfl⟩ := (e.trans f).surjective a
  obtain ⟨b,rfl⟩ := (e.trans f).surjective b
  rw [←map_mul,←map_mul,mul_comm]
end
end TorsionFreeZeroDivisors.LoopTracks

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.LoopTranspose
open scoped Topology unitInterval
noncomputable section
variable {X : Type u} [TopologicalSpace X] (x : X)
abbrev Other (b : Bool) := {j : Bool // j≠b}
instance (b : Bool) : Unique (Other b) where
  default := ⟨!b,by cases b <;> decide⟩
  uniq a := by rcases a with ⟨a,ha⟩;cases a <;> cases b <;> simp_all

def groupEquiv (b : Bool) : HomotopyGroup Bool X x≃*
    FundamentalGroup (GenLoop (Other b) X x) GenLoop.const where
  toEquiv := homotopyGroupEquivFundamentalGroup b
  map_mul' a c := by
    have h := HomotopyGroup.auxGroup_indep (X:=X) (x:=x) (Classical.arbitrary Bool) b
    apply Eq.trans (congrArg (fun i : Group (HomotopyGroup Bool X x) =>
      (homotopyGroupEquivFundamentalGroup b) (@Mul.mul _ i.toMul a c)) h)
    exact (homotopyGroupEquivFundamentalGroup b).apply_symm_apply _
def equiv (b : Bool) : HomotopyGroup Bool X x≃*FundamentalGroup (Path x x) (Path.refl x) := by
  let e := (groupEquiv x b).trans (LoopTracks.piOneHomeo (LoopTracks.uniqueLoopHomeo (Other b) x) GenLoop.const)
  have he : LoopTracks.uniqueLoopHomeo (Other b) x GenLoop.const=Path.refl x := by ext t;rfl
  rw [he] at e
  exact e

def turnPath (p : Path (Path.refl x) (Path.refl x)) : Path (Path.refl x) (Path.refl x) where
  toFun t := {
    toFun s := p s t
    continuous_toFun := (Path.continuous_uncurry_iff.mpr p.continuous).comp (continuous_id.prodMk continuous_const)
    source' := by rw [p.source];rfl
    target' := by rw [p.target];rfl }
  continuous_toFun := Path.continuous_uncurry_iff.mp
    ((Path.continuous_uncurry_iff.mpr p.continuous).comp continuous_swap)
  source' := by ext s;exact (p s).source
  target' := by ext s;exact (p s).target

def turn : FundamentalGroup (Path x x) (Path.refl x)≃*FundamentalGroup (Path x x) (Path.refl x) :=
  (equiv x true).symm.trans (equiv x false)

lemma equiv_mk (b : Bool) (p : GenLoop Bool X x) :
    equiv x b (Quotient.mk' p)=Path.Homotopic.Quotient.mk
      (((GenLoop.toLoop b p).map (LoopTracks.uniqueLoopHomeo (Other b) x).continuous).cast
        (by ext t;rfl) (by ext t;rfl)) := by
  rfl
lemma turn_equiv_mk (p : GenLoop Bool X x) :
    turn x (equiv x true (Quotient.mk' p))=equiv x false (Quotient.mk' p) := by
  change equiv x false ((equiv x true).symm ((equiv x true) (Quotient.mk' p)))=_
  exact (equiv x false).congr_arg ((equiv x true).symm_apply_apply _)
lemma turns_representative (p : GenLoop Bool X x) :
    turnPath x (((GenLoop.toLoop true p).map (LoopTracks.uniqueLoopHomeo (Other true) x).continuous).cast
        (by ext t;rfl) (by ext t;rfl))=
      (((GenLoop.toLoop false p).map (LoopTracks.uniqueLoopHomeo (Other false) x).continuous).cast
        (by ext t;rfl) (by ext t;rfl)) := by
  ext s t
  change p (Cube.insertAt true (t,fun _=>s))=p (Cube.insertAt false (s,fun _=>t))
  apply congrArg p
  funext b
  cases b <;> simp [Cube.insertAt]

lemma turn_mk (p : Path (Path.refl x) (Path.refl x)) :
    turn x (Path.Homotopic.Quotient.mk p)=Path.Homotopic.Quotient.mk (turnPath x p) := by
  obtain ⟨q,hq⟩ := (equiv x true).surjective (Path.Homotopic.Quotient.mk p)
  induction q using Quotient.inductionOn with | h q=>
  change equiv x true (Quotient.mk' q)=Path.Homotopic.Quotient.mk p at hq
  rw [←hq,turn_equiv_mk,equiv_mk]
  rw [equiv_mk] at hq
  have h := Path.Homotopic.Quotient.eq.mp hq
  have ht : (turnPath x (((GenLoop.toLoop true q).map (LoopTracks.uniqueLoopHomeo (Other true) x).continuous).cast
      (by ext t;rfl) (by ext t;rfl))).Homotopic (turnPath x p) := by
    obtain ⟨H⟩ := h
    refine ⟨{
      toFun := fun z=>{
        toFun t:=H (z.1,t) z.2
        continuous_toFun:=?_
        source':=?_
        target':=?_ }
      continuous_toFun:=?_
      map_zero_left:=?_
      map_one_left:=?_
      prop':=?_ }⟩
    · exact (Path.continuous_uncurry_iff.mpr H.continuous).comp
        ((continuous_const.prodMk continuous_id).prodMk continuous_const)
    · rw [H.eq_fst z.1 (show (0:unitInterval)∈{0,1} from Or.inl rfl)]
      simp only [Path.coe_toContinuousMap,Path.source,Path.refl_apply]
    · rw [H.eq_fst z.1 (show (1:unitInterval)∈{0,1} from Or.inr rfl)]
      simp only [Path.coe_toContinuousMap,Path.target,Path.refl_apply]
    · apply Path.continuous_uncurry_iff.mp
      exact (Path.continuous_uncurry_iff.mpr H.continuous).comp
        (((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
          (continuous_snd.comp continuous_fst))
    · intro s;ext t;exact congrArg (fun r : Path x x=>r s) (H.apply_zero t)
    · intro s;ext t;exact congrArg (fun r : Path x x=>r s) (H.apply_one t)
    · intro s t ht;ext z
      rcases ht with rfl|rfl
      · change (H (s,z)) 0=_
        simp only [Path.coe_toContinuousMap,Path.source,Path.refl_apply]
      · change (H (s,z)) 1=_
        simp only [Path.coe_toContinuousMap,Path.target,Path.refl_apply]
  rw [turns_representative] at ht
  exact Path.Homotopic.Quotient.eq.mpr ht
end
end TorsionFreeZeroDivisors.LoopTranspose

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.HomotopyTracks
open scoped unitInterval
noncomputable section
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y} {f : C(X,Y)} (hx : f x=y)
def mapped (p : Path x x) : Path y y := (p.map f.continuous).cast hx.symm hx.symm
variable (H : f.Homotopy (.const _ y)) (hH : ∀t,H (t,x)=y)
def track (p : Path x x) : Path (mapped hx p) (Path.refl y) where
  toFun t := {
    toFun s := H (t,p s)
    continuous_toFun := H.continuous.comp (continuous_const.prodMk p.continuous)
    source' := by rw [p.source];exact hH t
    target' := by rw [p.target];exact hH t }
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (H.continuous.comp (continuous_fst.prodMk (p.continuous.comp continuous_snd)))
  source' := by ext s;exact H.apply_zero (p s)
  target' := by ext s;exact H.apply_one (p s)
variable (D : C(X,Path y y)) (hD : D x=Path.refl y)
def run : (ContinuousMap.const X y).Homotopy (.const _ y) where
  toFun z := D z.2 z.1
  continuous_toFun := (Path.continuous_uncurry_iff.mpr D.continuous).comp continuous_swap
  map_zero_left _z := Path.source _
  map_one_left _z := Path.target _
include hD in
lemma run_base (t : unitInterval) : run D (t,x)=y := by
  change D x t=y
  rw [hD];rfl
include hH hD in
lemma trans_base (t : unitInterval) : (H.trans (run D)) (t,x)=y := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hH _
  · exact run_base D hD _
lemma track_trans (p : Path x x) :
    track hx (H.trans (run D)) (trans_base H hH D hD) p=
      (track hx H hH p).trans (LoopTranspose.turnPath y ((p.map D.continuous).cast hD.symm hD.symm)) := by
  ext t s
  change (H.trans (run D)) (t,p s)=((track hx H hH p).trans
    (LoopTranspose.turnPath y ((p.map D.continuous).cast hD.symm hD.symm))) t s
  rw [ContinuousMap.Homotopy.trans_apply,Path.trans_apply]
  split_ifs <;> rfl
end
end TorsionFreeZeroDivisors.HomotopyTracks

end



end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.DiskTracks
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
open GroupRingTopology.Cellular hiding Disk Sphere boundary
open scoped unitInterval
variable {Y : Type} [TopologicalSpace Y] {y : Y} {p : Path y y}
  {c h : Path p (Path.refl y)}
def squareHomotopy (H : c.Homotopy h) : (square c).Homotopy (square h) where
  toFun z := square (H.eval z.1) z.2
  continuous_toFun := (Path.continuous_uncurry_iff.mpr H.continuous).comp
    ((continuous_fst.prodMk (continuous_diskTime.comp continuous_snd)).prodMk
      (Cayley.continuous_edgeTime.comp (continuous_diskTail.comp continuous_snd)))
  map_zero_left d := by
    change H (0,diskTime d) _=c _ _
    rw [H.apply_zero];rfl
  map_one_left d := by
    change H (1,diskTime d) _=h _ _
    rw [H.apply_one];rfl
lemma squareHomotopy_boundary (H : c.Homotopy h) (t : unitInterval) (z : Sphere 2) :
    squareHomotopy H (t,boundary 2 z)=LoopSphere.map p z := square_boundary (H.eval t) z

def extension (F : C(Disk 2,Y)) (hF : ∀z,F (boundary 2 z)=LoopSphere.map p z)
    (h : Path p (Path.refl y)) (H : (physical F hF).Homotopy h) : F.Homotopy (.const _ y) := by
  have e := (squareHomotopy H).trans (contract h)
  exact { e with
    map_zero_left := fun d=>(e.apply_zero d).trans (ContinuousMap.congr_fun (square_physical F hF) d) }
lemma extension_boundary (F : C(Disk 2,Y)) (hF : ∀z,F (boundary 2 z)=LoopSphere.map p z)
    (h : Path p (Path.refl y)) (H : (physical F hF).Homotopy h)
    (t : unitInterval) (z : Sphere 2) :
    extension F hF h H (t,boundary 2 z)=
      if ht : (t:ℝ)≤1/2 then LoopSphere.map p z
      else LoopSphere.map (h ⟨2*t-1,unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le,t.2.2⟩⟩) z := by
  change ((squareHomotopy H).trans (contract h)) (t,boundary 2 z)=_
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact squareHomotopy_boundary H _ z
  · exact contract_boundary h _ z
end TorsionFreeZeroDivisors.DiskTracks
namespace TorsionFreeZeroDivisors.HomotopyTracks
open GroupRingTopology GroupRingTopology.Attachment
open scoped unitInterval
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y} {f : C(X,Y)} (hx : f x=y)
lemma natural_cast (p : Path x x) : LoopSphere.map (mapped hx p)=f.comp (LoopSphere.map p) := by
  subst y
  exact LoopSphere.natural p f
variable (H : f.Homotopy (.const _ y)) (hH : ∀t,H (t,x)=y)
lemma track_boundary (p : Path x x) (t : unitInterval) (z : Sphere 2) :
    LoopSphere.map ((track hx H hH p) t) z=H (t,LoopSphere.map p z) := by
  let k : C(X,Y) := ⟨fun u=>H (t,u),H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  exact ContinuousMap.congr_fun (natural_cast (f:=k) (hH t) p) z
end TorsionFreeZeroDivisors.HomotopyTracks

end

end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.IndexedCells
open Set Topology GroupRingTopology GroupRingTopology.Attachment GroupRingTopology.PathExtension
noncomputable section
variable {G S Q : Type} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
  (s : S→G) (w : Q→FreeGroup S) (hw : ∀i,FreeGroup.lift s (w i)=1)
include hw in
omit [TopologicalSpace G] [DiscreteTopology G] in
lemma in_range (r : FreeGroup S) (hr : r∈Set.range w) : FreeGroup.lift s r=1 := by
  rcases hr with ⟨i,rfl⟩;exact hw i
def loop (i : Q) : Path (Cayley.vertex s 1) (Cayley.vertex s 1) :=
  Cayley.relatorLoop s (Set.range w) (in_range s w hw) ⟨w i,⟨i,rfl⟩⟩
lemma loop_equal (i : Q) : PathExtension.Q.Equal (Path.Homotopic.Quotient.mk (loop s w hw i)) (Cayley.wordLift s (w i)).2 :=
  Cayley.relatorLoop_equal s (Set.range w) (in_range s w hw) ⟨w i,⟨i,rfl⟩⟩
def attaching (i : Q) : C(Sphere 2,Cayley.Graph s) := LoopSphere.map (loop s w hw i)
abbrev Cover := CellPresentation.Cover s (attaching s w hw)
abbrev Base := CellPresentation.Base s (attaching s w hw)
def inclusion : C(Cayley.Graph s,Cover s w hw) := CellPresentation.inclusion s (attaching s w hw)
lemma mapped_loop (i : Q) : ((loop s w hw i).map (inclusion s w hw).continuous).Homotopic
    (Path.refl (inclusion s w hw (Cayley.vertex s 1))) := by
  apply LoopSphere.homotopic_map_of_fill _ _ (cell _ ((1:G),i))
  intro z
  change cell (equivariantFamily (G:=G) (attaching s w hw)) ((1:G),i) (boundary 2 z)=_
  erw [cell_boundary]
  simp only [equivariantFamily,ContinuousMap.coe_mk,one_smul]
  rfl
lemma wordLift_rel (i : Q) : CellPresentation.wordLift s (attaching s w hw) (w i)=1 := by
  apply PathExtension.ext (a:=CellPresentation.wordLift s (attaching s w hw) (w i)) (b:=1)
    ((Cayley.wordLift_fst s (w i)).trans (hw i))
  apply PathExtension.Q.Equal.path
  apply (PathExtension.mapFun_equal (inclusion s w hw) (CellPresentation.inclusion_smul s (attaching s w hw))
    (Cayley.vertex s 1) (Cayley.wordLift s (w i))).trans
  apply ((loop_equal s w hw i).map (inclusion s w hw)).symm.trans
  apply (PathExtension.Q.Equal.ofEq (Quotient.sound (mapped_loop s w hw i))).trans
  exact PathExtension.one_path_equal.symm
variable (hs : Function.Surjective (FreeGroup.lift s))
  (hker : (FreeGroup.lift s).ker=Subgroup.normalClosure (Set.range w))
include hs hker in
lemma cover_simplyConnected : SimplyConnectedSpace (Cover s w hw) :=
  CellPresentation.cover_simplyConnected s (attaching s w hw) w (wordLift_rel s w hw) hs hker

def translated (g : G) (i : Q) : Path (Cayley.vertex s g) (Cayley.vertex s g) :=
  ((loop s w hw i).map (smulMap g).continuous).cast
    (by simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,_root_.mul_one])
    (by simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,_root_.mul_one])
lemma translated_equal (g : G) (i : Q) : PathExtension.Q.Equal
    (Path.Homotopic.Quotient.mk (translated s w hw g i)) ((Cayley.wordLift s (w i)).2.map (smulMap g)) :=
  (PathExtension.Q.cast_equal _ _ _).trans ((loop_equal s w hw i).map _)
lemma attaching_translated (g : G) (i : Q) (z : Sphere 2) :
    equivariantFamily (G:=G) (attaching s w hw) (g,i) z=LoopSphere.map (translated s w hw g i) z := by
  exact (ContinuousMap.congr_fun (HomotopyTracks.natural_cast
    (f:=smulMap g) (by simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,_root_.mul_one])
    (loop s w hw i)) z).symm
end
end TorsionFreeZeroDivisors.IndexedCells

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.FixedGraph
open GroupRingTopology GroupRingTopology.Attachment
open scoped unitInterval
noncomputable section
variable {G S Y : Type} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace Y] [SimplyConnectedSpace Y]
  (s : S→G) (f : C(Cayley.Graph s,Y)) (y : Y) (hv : ∀g,f (Cayley.vertex s g)=y)
def vertices (g : G) : Path y (f (Cayley.vertex s g)) := (Path.refl y).cast rfl (hv g)
lemma compatible (g : G) (a : S) :
    ((vertices s f y hv g).trans ((Cayley.edge s g a).map f.continuous)).Homotopic
      (vertices s f y hv (g*s a)) := by
  apply Path.Homotopic.Quotient.eq.mp
  exact Subsingleton.elim _ _
def homotopy : f.Homotopy (.const _ y) :=
  Cayley.graphNullhomotopy s f y (vertices s f y hv) (compatible s f y hv)
lemma homotopy_vertex (t : unitInterval) (g : G) : homotopy s f y hv (t,Cayley.vertex s g)=y := by
  change ((Path.refl (f (Cayley.vertex s g))).trans (vertices s f y hv g).symm) t=y
  rw [Path.trans_apply]
  split_ifs <;> simp [vertices,hv]
end
end TorsionFreeZeroDivisors.FixedGraph

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.CellModule
open scoped Classical BigOperators
noncomputable section
variable {G I : Type} [_root_.Group G]
variable (q : FreeGroup I→*G)
end
end TorsionFreeZeroDivisors.CellModule

end


end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.WordResponse
open GroupRingTopology GroupRingTopology.PathExtension
open Path.Homotopic
noncomputable section
variable {X : Type u} [TopologicalSpace X] {x : X}
def basedClass {a b : X} (p : Path.Homotopic.Quotient a b) {Y : Type*} [TopologicalSpace Y]
    (f : C(X,Y)) (y : Y) (ha : f a=y) (hb : f b=y) : FundamentalGroup Y y :=
  (p.map f).cast ha.symm hb.symm
lemma basedClass_equal {a b c d : X} {p : Path.Homotopic.Quotient a b}
    {q : Path.Homotopic.Quotient c d} (h : Q.Equal p q) {Y : Type*} [TopologicalSpace Y]
    (f : C(X,Y)) (y : Y) (ha : f a=y) (hb : f b=y) (hc : f c=y) (hd : f d=y) :
    basedClass p f y ha hb=basedClass q f y hc hd := by
  rcases h with ⟨h1,h2,h3⟩
  subst c;subst d;cases eq_of_heq h3;rfl
lemma basedClass_trans {a b c : X} (p : Path.Homotopic.Quotient a b)
    (q : Path.Homotopic.Quotient b c) {Y : Type*} [TopologicalSpace Y]
    (f : C(X,Y)) (y : Y) (ha : f a=y) (hb : f b=y) (hc : f c=y) :
    basedClass (p.trans q) f y ha hc=basedClass q f y hb hc * basedClass p f y ha hb := by
  unfold basedClass
  rw [Q.map_trans,←Q.trans_cast _ _ ha.symm hb.symm hc.symm]
  rfl
variable {G S Y : Type} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace Y] (s : S→G) (f : C(Cayley.Graph s,Y)) (y : Y)
  (hv : ∀g,f (Cayley.vertex s g)=y)
include hv in
lemma source_eq (g : G) : f (g • Cayley.vertex s 1)=y := by rw [Cayley.smul_vertex,_root_.mul_one,hv]
include hv in
lemma target_eq (g : G) (w : FreeGroup S) : f (g • ((Cayley.wordLift s w).1 • Cayley.vertex s 1))=y := by
  rw [Cayley.smul_vertex,Cayley.smul_vertex,_root_.mul_one,hv]
def response (g : G) (w : FreeGroup S) : Additive (FundamentalGroup Y y) :=
  Additive.ofMul (basedClass ((Cayley.wordLift s w).2.map (smulMap g)) f y
    (source_eq s f y hv g) (target_eq s f y hv g w))
variable [IsMulCommutative (FundamentalGroup Y y)]
local instance : CommGroup (FundamentalGroup Y y) :=
  { (inferInstance : Group (FundamentalGroup Y y)) with mul_comm:=isMulCommutative_iff.mp inferInstance }
lemma response_mul (g : G) (w v : FreeGroup S) :
    response s f y hv g (w*v)=response s f y hv g w+
      response s f y hv (g*FreeGroup.lift s w) v := by
  let a:=Cayley.wordLift s w
  let b:=Cayley.wordLift s v
  have h := ((mul_path_equal a b).map (smulMap g)).trans
    (Q.Equal.ofEq (Q.map_trans a.2 (b.2.map (smulMap a.1)) (smulMap g)))
  have h2 := map_mul_equal b.2 g a.1
  have he : Q.Equal ((Cayley.wordLift s (w*v)).2.map (smulMap g)) ((a*b).2.map (smulMap g)) := by
    rw [show Cayley.wordLift s (w*v)=a*b from map_mul _ _ _]
    exact .refl _
  change basedClass ((Cayley.wordLift s (w*v)).2.map (smulMap g)) f y
    (source_eq s f y hv g) (target_eq s f y hv g (w*v))= _ * _
  rw [basedClass_equal (he.trans h) f y (source_eq s f y hv g)
    (target_eq s f y hv g (w*v)) (source_eq s f y hv g) (by
      change f (g • (a.1 • (b.1 • Cayley.vertex s 1)))=y
      simp only [Cayley.smul_vertex,hv])]
  erw [basedClass_trans _ _ f y (source_eq s f y hv g) (by
    change f (g • (a.1 • Cayley.vertex s 1))=y
    simp only [Cayley.smul_vertex,hv]) (by
      change f (g • (a.1 • (b.1 • Cayley.vertex s 1)))=y
      simp only [Cayley.smul_vertex,hv])]
  rw [mul_comm]
  congr 1
  have hh:= basedClass_equal h2 f y (by
    simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,hv]) (by
    simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,hv])
    (by simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,hv]) (by
      simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,hv])
  refine hh.trans ?_
  change (response s f y hv (g*a.1) v).toMul=(response s f y hv (g*FreeGroup.lift s w) v).toMul
  exact congrArg (fun h : G=>(response s f y hv (g*h) v).toMul) (Cayley.wordLift_fst s w)
lemma response_one (g : G) : response s f y hv g 1=0 := by
  have h:=response_mul s f y hv g 1 1
  simpa only [_root_.one_mul,map_one,_root_.mul_one] using (add_eq_left.mp h.symm)
lemma response_inv (g : G) (w : FreeGroup S) :
    response s f y hv g w⁻¹= -response s f y hv (g*(FreeGroup.lift s w)⁻¹) w := by
  have h:=response_mul s f y hv g w⁻¹ w
  rw [_root_.inv_mul_cancel,response_one s f y hv,map_inv] at h
  exact eq_neg_of_add_eq_zero_left h.symm

def edges : CellModule.Module G S→+ Additive (FundamentalGroup Y y) :=
  Finsupp.liftAddHom (fun z : G×S=>zmultiplesHom _ (response s f y hv z.1 (FreeGroup.of z.2)))
lemma edges_fox (g : G) (w : FreeGroup S) :
    edges s f y hv (CellModule.translate g (CellModule.fox (FreeGroup.lift s) w))=response s f y hv g w := by
  induction w using FreeGroup.induction_on generalizing g with
  | C1=>rw [CellModule.fox_one,map_zero,map_zero,response_one s f y hv]
  | of a=>simp [CellModule.fox_of,CellModule.translate_single,edges]
  | inv_of a ih=>
    rw [CellModule.fox_inv,map_neg,map_neg,←CellModule.translate_mul,ih,response_inv s f y hv]
  | mul w v hw hv'=>
    rw [CellModule.fox_mul,map_add,map_add,←CellModule.translate_mul,hw,hv',response_mul s f y hv]
end
end TorsionFreeZeroDivisors.WordResponse

end


end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.GraphLabels
open GroupRingTopology GroupRingTopology.Attachment GroupRingTopology.PathExtension
open scoped unitInterval
noncomputable section
variable {G S Y : Type} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace Y] (s : S→G) (y : Y) (k : G×S→FundamentalGroup Y y)
def representative (e : G×S) : Path y y :=
  (Path.Homotopic.Quotient.mk_surjective (k e)).choose
omit [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G] in
lemma representative_class (e : G×S) : Path.Homotopic.Quotient.mk (representative y k e)=k e :=
  (Path.Homotopic.Quotient.mk_surjective (k e)).choose_spec
def edgeMap (e : G×S) : C(Disk 1,Y) :=
  (representative y k e).toContinuousMap.comp ⟨Cayley.edgeTime,Cayley.continuous_edgeTime⟩
omit [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G] in
lemma edgeMap_boundary (e : G×S) (z : Sphere 1) : edgeMap y k e (boundary 1 z)=y := by
  obtain rfl|rfl:=Cayley.sphere_one_eq z
  · change representative y k e (Cayley.edgeTime (boundary 1 Cayley.minus))=y
    rw [Cayley.edgeTime_minus,Path.source]
  · change representative y k e (Cayley.edgeTime (boundary 1 Cayley.plus))=y
    rw [Cayley.edgeTime_plus,Path.target]
def map : C(Cayley.Graph s,Y) :=
  lift (equivariantFamily (G:=G) (Cayley.attaching s)) (.const _ y) (edgeMap y k)
    (fun e z=>edgeMap_boundary y k e z)
lemma map_vertex (g : G) : map s y k (Cayley.vertex s g)=y := rfl
lemma map_edge (g : G) (a : S) (t : unitInterval) :
    map s y k (Cayley.edge s g a t)=representative y k (g,a) t := by
  change map s y k (cell _ (g,a) (Cayley.edgeParam t))=_
  unfold map
  erw [lift_cell]
  change representative y k (g,a) (Cayley.edgeTime (Cayley.edgeParam t))=_
  rw [Cayley.edgeTime_param]

lemma edge_translate (g : G) (a : S) : Q.Equal
    ((Path.Homotopic.Quotient.mk (Cayley.edge s 1 a)).map (smulMap g))
    (Path.Homotopic.Quotient.mk (Cayley.edge s g a)) := by
  refine ⟨?_,?_,Path.Homotopic.hpath_hext ?_⟩
  · change g • Cayley.vertex s 1=Cayley.vertex s g
    rw [Cayley.smul_vertex,_root_.mul_one]
  · change g • Cayley.vertex s (1*s a)=Cayley.vertex s (g*s a)
    rw [Cayley.smul_vertex,_root_.one_mul]
  · intro t
    change g • cell (equivariantFamily (G:=G) (Cayley.attaching s)) ((1:G),a) (Cayley.edgeParam t)=cell (equivariantFamily (G:=G) (Cayley.attaching s)) (g,a) (Cayley.edgeParam t)
    erw [smul_cell _ (equivariantFamily_smul (Cayley.attaching s))]
    change cell (equivariantFamily (G:=G) (Cayley.attaching s)) (g*1,a) (Cayley.edgeParam t)=_
    rw [_root_.mul_one]
lemma response_generator (g : G) (a : S) :
    WordResponse.response s (map s y k) y (map_vertex s y k) g (FreeGroup.of a)=Additive.ofMul (k (g,a)) := by
  have hh : Q.Equal (((Cayley.wordLift s (FreeGroup.of a)).2).map (smulMap g))
      (Path.Homotopic.Quotient.mk (Cayley.edge s g a)) :=
    by
      rw [show Cayley.wordLift s (FreeGroup.of a)=Cayley.pathGenerator s a from FreeGroup.lift_apply_of]
      exact ((Cayley.pathGenerator_equal s a).map (smulMap g)).trans (edge_translate s g a)
  change WordResponse.basedClass (((Cayley.wordLift s (FreeGroup.of a)).2).map (smulMap g)) (map s y k) y
    (WordResponse.source_eq s (map s y k) y (map_vertex s y k) g)
    (WordResponse.target_eq s (map s y k) y (map_vertex s y k) g (FreeGroup.of a))=k (g,a)
  erw [WordResponse.basedClass_equal hh (map s y k) y _ _ (map_vertex s y k g) (map_vertex s y k (g*s a))]
  change Path.Homotopic.Quotient.mk (((Cayley.edge s g a).map (map s y k).continuous).cast _ _)=k (g,a)
  rw [show (((Cayley.edge s g a).map (map s y k).continuous).cast (map_vertex s y k g).symm
    (map_vertex s y k (g*s a)).symm)=representative y k (g,a) from by
      ext t;exact map_edge s y k g a t]
  exact representative_class y k (g,a)
variable [IsMulCommutative (FundamentalGroup Y y)]
local instance : CommGroup (FundamentalGroup Y y) :=
  { (inferInstance : Group (FundamentalGroup Y y)) with mul_comm:=isMulCommutative_iff.mp inferInstance }
lemma realizes (c : CellModule.Module G S→+Additive (FundamentalGroup Y y)) (g : G) (w : FreeGroup S) :
    WordResponse.response s (map s y (fun e=>(c (Finsupp.single e 1)).toMul)) y
      (map_vertex s y _) g w=c (CellModule.translate g (CellModule.fox (FreeGroup.lift s) w)) := by
  rw [←WordResponse.edges_fox]
  have he : WordResponse.edges s (map s y (fun e=>(c (Finsupp.single e 1)).toMul)) y
      (map_vertex s y _)=c := by
    apply Finsupp.addHom_ext
    intro e z
    simp only [WordResponse.edges,Finsupp.liftAddHom_apply_single,zmultiplesHom_apply,response_generator]
    change z • c (Finsupp.single e 1)=c (Finsupp.single e z)
    rw [←map_zsmul]
    congr 1
    simp
  rw [he]
end
end TorsionFreeZeroDivisors.GraphLabels

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.AbsorbTracks
open Set GroupRingTopology GroupRingTopology.Attachment GroupRingTopology.PathExtension
open scoped unitInterval
noncomputable section
variable {G S Q Y : Type} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace Y] [SimplyConnectedSpace Y]
  (s : S→G) (w : Q→FreeGroup S) (hw : ∀i,FreeGroup.lift s (w i)=1)
  (L : CellModule.Module G S→+CellModule.Module G Q)
  (hL : ∀g i,L (CellModule.translate g (CellModule.fox (FreeGroup.lift s) (w i)))=Finsupp.single (g,i) 1)
  (f : C(IndexedCells.Cover s w hw,Y)) (y : Y)
  (hv : ∀g,f (IndexedCells.inclusion s w hw (Cayley.vertex s g))=y)
def graph : C(Cayley.Graph s,Y) := f.comp (IndexedCells.inclusion s w hw)
def initial : (graph s w hw f).Homotopy (.const _ y) := FixedGraph.homotopy s (graph s w hw f) y hv
lemma initial_vertex (t : unitInterval) (g : G) : initial s w hw f y hv (t,Cayley.vertex s g)=y :=
  FixedGraph.homotopy_vertex s (graph s w hw f) y hv t g
def boundaryLoop (g : G) (i : Q) : Path y y := HomotopyTracks.mapped (f:=graph s w hw f) (hv g) (IndexedCells.translated s w hw g i)
def initialTrack (g : G) (i : Q) : Path (boundaryLoop s w hw f y hv g i) (Path.refl y) :=
  HomotopyTracks.track (f:=graph s w hw f) (hv g) (initial s w hw f y hv) (fun t=>initial_vertex s w hw f y hv t g)
    (IndexedCells.translated s w hw g i)
def cellMap (g : G) (i : Q) : C(Disk 2,Y) := f.comp (cell (equivariantFamily (G:=G) (IndexedCells.attaching s w hw)) (g,i))
include hv in
omit [SimplyConnectedSpace Y] in
lemma cellMap_boundary (g : G) (i : Q) (z : Sphere 2) :
    cellMap s w hw f g i (boundary 2 z)=LoopSphere.map (boundaryLoop s w hw f y hv g i) z := by
  change f (cell _ (g,i) (boundary 2 z))=_
  erw [cell_boundary]
  rw [IndexedCells.attaching_translated]
  exact (ContinuousMap.congr_fun (HomotopyTracks.natural_cast (f:=graph s w hw f) (hv g) (IndexedCells.translated s w hw g i)) z).symm
def physical (g : G) (i : Q) : Path (boundaryLoop s w hw f y hv g i) (Path.refl y) :=
  DiskTracks.physical (cellMap s w hw f g i) (cellMap_boundary s w hw f y hv g i)
local instance : CommGroup (FundamentalGroup (Path y y) (Path.refl y)) :=
  { (inferInstance : Group (FundamentalGroup (Path y y) (Path.refl y))) with
    mul_comm:=LoopTracks.loopGroup_comm y }
abbrev Coef := Additive (FundamentalGroup (Path y y) (Path.refl y))
def obstruction (g : G) (i : Q) : Coef y := Additive.ofMul
  (Path.Homotopic.Quotient.mk ((initialTrack s w hw f y hv g i).symm.trans (physical s w hw f y hv g i)))
def obstructionMap : CellModule.Module G Q→+Coef y :=
  Finsupp.liftAddHom (fun e=>zmultiplesHom _ (obstruction s w hw f y hv e.1 e.2))
lemma obstructionMap_single (g : G) (i : Q) : obstructionMap s w hw f y hv (Finsupp.single (g,i) 1)=obstruction s w hw f y hv g i := by
  simp [obstructionMap]
def turnBack : Coef y→+Coef y where
  toFun a := Additive.ofMul ((LoopTranspose.turn y).symm a.toMul)
  map_zero' := (LoopTranspose.turn y).symm.map_one
  map_add' a b := (LoopTranspose.turn y).symm.map_mul a.toMul b.toMul
def correction : CellModule.Module G S→+Coef y := (turnBack y).comp ((obstructionMap s w hw f y hv).comp L)
def labels : C(Cayley.Graph s,Path y y) :=
  GraphLabels.map s (Path.refl y) (fun e=>(correction s w hw L f y hv (Finsupp.single e 1)).toMul)
lemma labels_vertex (g : G) : labels s w hw L f y hv (Cayley.vertex s g)=Path.refl y :=
  GraphLabels.map_vertex _ _ _ g

def final : (graph s w hw f).Homotopy (.const _ y) :=
  (initial s w hw f y hv).trans (HomotopyTracks.run (labels s w hw L f y hv))
lemma final_vertex (t : unitInterval) (g : G) : final s w hw L f y hv (t,Cayley.vertex s g)=y :=
  HomotopyTracks.trans_base (initial s w hw f y hv) (fun t=>initial_vertex s w hw f y hv t g)
    (labels s w hw L f y hv) (labels_vertex s w hw L f y hv g) t

def finalTrack (g : G) (i : Q) : Path (boundaryLoop s w hw f y hv g i) (Path.refl y) :=
  HomotopyTracks.track (f:=graph s w hw f) (hv g) (final s w hw L f y hv) (fun t=>final_vertex s w hw L f y hv t g)
    (IndexedCells.translated s w hw g i)
include hL in
lemma response (g : G) (i : Q) :
    Path.Homotopic.Quotient.mk (LoopTranspose.turnPath y
      (((IndexedCells.translated s w hw g i).map (labels s w hw L f y hv).continuous).cast
        (labels_vertex s w hw L f y hv g).symm (labels_vertex s w hw L f y hv g).symm))=
      (obstruction s w hw f y hv g i).toMul := by
  rw [←LoopTranspose.turn_mk]
  have he := WordResponse.basedClass_equal (IndexedCells.translated_equal s w hw g i)
    (labels s w hw L f y hv) (Path.refl y) (labels_vertex s w hw L f y hv g)
    (labels_vertex s w hw L f y hv g)
    (WordResponse.source_eq s (labels s w hw L f y hv) (Path.refl y) (labels_vertex s w hw L f y hv) g)
    (WordResponse.target_eq s (labels s w hw L f y hv) (Path.refl y) (labels_vertex s w hw L f y hv) g (w i))
  change Path.Homotopic.Quotient.mk (((IndexedCells.translated s w hw g i).map (labels s w hw L f y hv).continuous).cast _ _)=
    (WordResponse.response s (labels s w hw L f y hv) (Path.refl y) (labels_vertex s w hw L f y hv) g (w i)).toMul at he
  rw [he]
  have hr:=GraphLabels.realizes s (Path.refl y) (correction s w hw L f y hv) g (w i)
  change WordResponse.response s (labels s w hw L f y hv) (Path.refl y) (labels_vertex s w hw L f y hv) g (w i)=_ at hr
  rw [hr]
  change LoopTranspose.turn y ((LoopTranspose.turn y).symm
    ((obstructionMap s w hw f y hv) (L (CellModule.translate g (CellModule.fox (FreeGroup.lift s) (w i))))).toMul)=_
  rw [hL,obstructionMap_single]
  exact (LoopTranspose.turn y).apply_symm_apply _
include hL in
lemma homotopic (g : G) (i : Q) : (physical s w hw f y hv g i).Homotopic (finalTrack s w hw L f y hv g i) := by
  apply Path.Homotopic.Quotient.eq.mp
  change Path.Homotopic.Quotient.mk (physical s w hw f y hv g i)=Path.Homotopic.Quotient.mk
    (HomotopyTracks.track (f:=graph s w hw f) (hv g) ((initial s w hw f y hv).trans (HomotopyTracks.run (labels s w hw L f y hv))) _ _)
  erw [HomotopyTracks.track_trans (f:=graph s w hw f) (hv g) (initial s w hw f y hv)
    (fun t=>initial_vertex s w hw f y hv t g) (labels s w hw L f y hv)
    (labels_vertex s w hw L f y hv g) (IndexedCells.translated s w hw g i)]
  erw [Path.Homotopic.Quotient.mk_trans]
  erw [response s w hw L hL f y hv g i]
  change Path.Homotopic.Quotient.mk (physical s w hw f y hv g i)=
    (Path.Homotopic.Quotient.mk (initialTrack s w hw f y hv g i)).trans
      ((Path.Homotopic.Quotient.mk (initialTrack s w hw f y hv g i)).symm.trans
        (Path.Homotopic.Quotient.mk (physical s w hw f y hv g i)))
  rw [←Path.Homotopic.Quotient.trans_assoc,Path.Homotopic.Quotient.trans_symm,Path.Homotopic.Quotient.refl_trans]
end
end TorsionFreeZeroDivisors.AbsorbTracks

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.AbsorbCells
open Set GroupRingTopology GroupRingTopology.Attachment
open scoped unitInterval
noncomputable section
variable {G S Q Y : Type} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace Y] [SimplyConnectedSpace Y]
  (s : S→G) (w : Q→FreeGroup S) (hw : ∀i,FreeGroup.lift s (w i)=1)
  (L : CellModule.Module G S→+CellModule.Module G Q)
  (hL : ∀g i,L (CellModule.translate g (CellModule.fox (FreeGroup.lift s) (w i)))=Finsupp.single (g,i) 1)
  (f : C(IndexedCells.Cover s w hw,Y)) (y : Y)
  (hv : ∀g,f (IndexedCells.inclusion s w hw (Cayley.vertex s g))=y)
def graphHomotopy : (AbsorbTracks.graph s w hw f).Homotopy (.const _ y) :=
  (ContinuousMap.Homotopy.refl _).trans (AbsorbTracks.final s w hw L f y hv)
def diskHomotopy (e : G×Q) : (AbsorbTracks.cellMap s w hw f e.1 e.2).Homotopy (.const _ y) :=
  DiskTracks.extension (AbsorbTracks.cellMap s w hw f e.1 e.2)
    (AbsorbTracks.cellMap_boundary s w hw f y hv e.1 e.2)
    (AbsorbTracks.finalTrack s w hw L f y hv e.1 e.2)
    (AbsorbTracks.homotopic s w hw L hL f y hv e.1 e.2).some
lemma diskHomotopy_boundary (e : G×Q) (t : unitInterval) (z : Sphere 2) :
    diskHomotopy s w hw L hL f y hv e (t,boundary 2 z)=
      graphHomotopy s w hw L f y hv (t,equivariantFamily (G:=G) (IndexedCells.attaching s w hw) e z) := by
  change DiskTracks.extension _ _ _ _ (t,boundary 2 z)=_
  erw [DiskTracks.extension_boundary]
  change _=((ContinuousMap.Homotopy.refl _).trans (AbsorbTracks.final s w hw L f y hv)) _
  rw [ContinuousMap.Homotopy.trans_apply,IndexedCells.attaching_translated]
  split_ifs
  · exact ContinuousMap.congr_fun (HomotopyTracks.natural_cast (f:=AbsorbTracks.graph s w hw f) (hv e.1) (IndexedCells.translated s w hw e.1 e.2)) z
  · exact HomotopyTracks.track_boundary (f:=AbsorbTracks.graph s w hw f) (hv e.1) (AbsorbTracks.final s w hw L f y hv)
      (fun t=>AbsorbTracks.final_vertex s w hw L f y hv t e.1) (IndexedCells.translated s w hw e.1 e.2) _ z

def graphPaths : C(Cayley.Graph s,C(unitInterval,Y)) :=
  ((graphHomotopy s w hw L f y hv).toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩).curry
def cellPaths (e : G×Q) : C(Disk 2,C(unitInterval,Y)) :=
  ((diskHomotopy s w hw L hL f y hv e).toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩).curry
lemma paths_boundary (e : G×Q) (z : Sphere 2) : cellPaths s w hw L hL f y hv e (boundary 2 z)=
    graphPaths s w hw L f y hv (equivariantFamily (G:=G) (IndexedCells.attaching s w hw) e z) := by
  ext t
  exact diskHomotopy_boundary s w hw L hL f y hv e t z
def paths : C(IndexedCells.Cover s w hw,C(unitInterval,Y)) :=
  lift (equivariantFamily (G:=G) (IndexedCells.attaching s w hw))
    (graphPaths s w hw L f y hv) (cellPaths s w hw L hL f y hv) (paths_boundary s w hw L hL f y hv)
lemma paths_zero (z : IndexedCells.Cover s w hw) : paths s w hw L hL f y hv z 0=f z := by
  cases z with
  | inl z => exact (graphHomotopy s w hw L f y hv).apply_zero z
  | inr z =>
    change diskHomotopy s w hw L hL f y hv z.1 (0,interior 2 z.2)=_
    rw [ContinuousMap.Homotopy.apply_zero]
    change f (cell _ z.1 (interior 2 z.2))=f (Sum.inr z)
    rw [cell_interior]
lemma paths_one (z : IndexedCells.Cover s w hw) : paths s w hw L hL f y hv z 1=y := by
  cases z with
  | inl z=>exact (graphHomotopy s w hw L f y hv).apply_one z
  | inr z=>exact (diskHomotopy s w hw L hL f y hv z.1).apply_one (interior 2 z.2)
def homotopy : f.Homotopy (.const _ y) where
  toFun z:=paths s w hw L hL f y hv z.2 z.1
  continuous_toFun:=(paths s w hw L hL f y hv).uncurry.continuous.comp continuous_swap
  map_zero_left:=paths_zero s w hw L hL f y hv
  map_one_left:=paths_one s w hw L hL f y hv
end
end TorsionFreeZeroDivisors.AbsorbCells

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.CellHEP
open Set Metric Topology GroupRingTopology GroupRingTopology.Cellular
open scoped unitInterval
noncomputable section
variable {n : ℕ}
abbrev Cylinder (n : ℕ) := unitInterval × Disk n
def denom (q : Cylinder n) : ℝ := max (2-q.1.1) (2*‖q.2.1‖)
lemma denom_pos (q : Cylinder n) : 0<denom q :=
  lt_of_lt_of_le (by linarith [q.1.2.2] : 0<2-q.1.1) (le_max_left _ _)
lemma denom_le_two (q : Cylinder n) : denom q ≤ 2 := by
  have h := mem_closedBall_zero_iff.mp q.2.2
  exact max_le (by linarith [q.1.2.1]) (by linarith)
def scale (q : Cylinder n) : ℝ := 2/denom q
lemma scale_nonneg (q : Cylinder n) : 0 ≤ scale q := div_nonneg (by norm_num) (denom_pos q).le
lemma scale_ge_one (q : Cylinder n) : 1 ≤ scale q := by
  rw [scale,le_div_iff₀ (denom_pos q)]
  simpa using denom_le_two q
lemma scale_time (q : Cylinder n) : scale q*(2-q.1.1) ≤ 2 := by
  dsimp [scale]
  rw [div_mul_eq_mul_div,div_le_iff₀ (denom_pos q)]
  have h : 2-q.1.1 ≤ denom q := le_max_left _ _
  nlinarith
lemma scale_norm (q : Cylinder n) : scale q*‖q.2.1‖ ≤ 1 := by
  dsimp [scale]
  rw [div_mul_eq_mul_div,div_le_iff₀ (denom_pos q)]
  simpa only [one_mul,denom] using le_max_right (2-q.1.1) (2*‖q.2.1‖)
def retract (q : Cylinder n) : Cylinder n :=
  (⟨2-scale q*(2-q.1.1),by
      constructor
      · linarith [scale_time q]
      · have h := mul_le_mul_of_nonneg_right (scale_ge_one q) (by linarith [q.1.2.2] : 0 ≤ 2-q.1.1)
        linarith [q.1.2.2]⟩,
   ⟨scale q • q.2.1,by
      rw [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_nonneg (scale_nonneg q)]
      exact scale_norm q⟩)
lemma continuous_retract : Continuous (@retract n) := by
  have hd : Continuous (@denom n) := by unfold denom;fun_prop
  have hs : Continuous (@scale n) := continuous_const.div hd (fun q=>(denom_pos q).ne')
  exact (Continuous.subtype_mk ((continuous_const.sub (hs.mul
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst))))) _).prodMk
    (Continuous.subtype_mk (hs.smul (continuous_subtype_val.comp continuous_snd)) _)
def Rim (n : ℕ) : Set (Cylinder n) := {q | q.1=0 ∨ q.2.1 ∈ sphere 0 1}
lemma retract_mem (q : Cylinder n) : retract q∈Rim n := by
  rcases le_total (2*‖q.2.1‖) (2-q.1.1) with h|h
  · left
    apply Subtype.ext
    change 2-scale q*(2-q.1.1)=0
    have he : denom q=2-q.1.1 := max_eq_left h
    rw [scale,←he,div_mul_cancel₀ _ (denom_pos q).ne']
    ring
  · right
    rw [mem_sphere_zero_iff_norm]
    change ‖scale q • q.2.1‖=1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (scale_nonneg q)]
    have he : denom q=2*‖q.2.1‖ := max_eq_right h
    rw [scale,div_mul_eq_mul_div]
    change (2*‖q.2.1‖)/denom q=1
    rw [←he,div_self (denom_pos q).ne']
lemma retract_eq (q : Cylinder n) (h : q∈Rim n) : retract q=q := by
  have hm : denom q=2 := by
    apply le_antisymm (denom_le_two q)
    rcases h with h|h
    · have ht : q.1.1=0 := congrArg Subtype.val h
      simp [denom,ht]
    · have hn : ‖q.2.1‖=1 := mem_sphere_zero_iff_norm.mp h
      simp [denom,hn]
  have hs : scale q=1 := by simp [scale,hm]
  apply Prod.ext
  · apply Subtype.ext
    change 2-scale q*(2-q.1.1)=q.1.1
    rw [hs];ring
  · apply Subtype.ext
    change scale q • q.2.1=q.2.1
    rw [hs,one_smul]

def retraction : C(Cylinder n,Rim n) := ⟨fun q=>⟨retract q,retract_mem q⟩,
  continuous_retract.subtype_mk _⟩
variable {Y : Type*} [TopologicalSpace Y]
def face (n : ℕ) : Bool → Set (Rim n)
  | false => {z | z.1.1=0}
  | true => {z | z.1.2.1∈sphere 0 1}
lemma face_closed (b : Bool) : IsClosed (face n b) := by
  cases b
  · exact isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  · exact isClosed_sphere.preimage (continuous_subtype_val.comp
      (continuous_snd.comp continuous_subtype_val))
lemma face_cover : ⋃b,face n b=univ := by
  apply eq_univ_of_forall
  rintro ⟨q,hq⟩
  rcases hq with hq|hq
  · exact mem_iUnion.mpr ⟨false,hq⟩
  · exact mem_iUnion.mpr ⟨true,hq⟩
variable (f : C(Disk n,Y)) (H : C(unitInterval × Sphere n,Y))
  (h : ∀x,H (0,x)=f (boundary n x))
def faceMap : ∀ b : Bool,C(face n b,Y)
  | false => ⟨fun z=>f z.1.1.2,
      f.continuous.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))⟩
  | true => ⟨fun z=>H (z.1.1.1,⟨z.1.1.2.1,z.2⟩),H.continuous.comp
      ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
        ((continuous_subtype_val.comp (continuous_snd.comp
          (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _))⟩
include h in
lemma faceMap_compat (b c : Bool) (z : Rim n) (hb : z∈face n b) (hc : z∈face n c) :
    faceMap f H b ⟨z,hb⟩=faceMap f H c ⟨z,hc⟩ := by
  have cross (hb : z∈face n false) (hc : z∈face n true) :
      faceMap f H false ⟨z,hb⟩=faceMap f H true ⟨z,hc⟩ := by
    change f z.1.2=H (z.1.1,⟨z.1.2.1,hc⟩)
    change z.1.1=0 at hb
    rw [hb,h]
    rfl
  cases b <;> cases c
  · rfl
  · exact cross hb hc
  · exact (cross hc hb).symm
  · rfl
def rimMap : C(Rim n,Y) := ⟨Set.liftCover (face n) (fun b=>faceMap f H b)
  (faceMap_compat f H h) face_cover,
  continuous_liftCover _ _ _ _ face_closed⟩
lemma rimMap_face (b : Bool) (z : face n b) :
    rimMap f H h z.1=faceMap f H b z := by
  apply Set.liftCover_coe (S:=face n) (f:=fun b=>faceMap f H b)
    (hf:=faceMap_compat f H h) (hS:=face_cover)
/-- Literal homotopy extension for a cell, with no fibrancy premise. -/
def extension : C(Cylinder n,Y) := (rimMap f H h).comp retraction
lemma extension_zero (x : Disk n) : extension f H h (0,x)=f x := by
  have hr : retract (0,x)=(0,x) := retract_eq _ (Or.inl rfl)
  change rimMap f H h ⟨retract (0,x),retract_mem (0,x)⟩=f x
  simp only [hr]
  exact rimMap_face f H h false ⟨⟨(0,x),Or.inl rfl⟩,rfl⟩
lemma extension_boundary (t : unitInterval) (x : Sphere n) :
    extension f H h (t,boundary n x)=H (t,x) := by
  have hr : retract (t,boundary n x)=(t,boundary n x) := retract_eq _ (Or.inr x.2)
  change rimMap f H h ⟨retract (t,boundary n x),retract_mem (t,boundary n x)⟩=H (t,x)
  simp only [hr]
  exact rimMap_face f H h true ⟨⟨(t,boundary n x),Or.inr x.2⟩,x.2⟩

end
end TorsionFreeZeroDivisors.CellHEP


end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.AttachmentHEP
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
open scoped unitInterval
noncomputable section
variable {X : Type u} {Y : Type v} {J : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable {n : ℕ} (a : J→C(Sphere n,X)) (f : C(Space a,Y))
  (H : C(unitInterval × X,Y)) (h : ∀x,H (0,x)=f (base a x))
def eval (t : unitInterval) : C(C(unitInterval,Y),Y) := ⟨fun p=>p t,continuous_eval_const t⟩
def basePaths : C(X,C(unitInterval,Y)) := H.comp ⟨Prod.swap,continuous_swap⟩ |>.curry
def cellPaths (i : J) : C(Disk n,C(unitInterval,Y)) :=
  ((CellHEP.extension (f.comp (cell a i))
    (H.comp ⟨fun z : unitInterval × Sphere n=>(z.1,a i z.2),
      continuous_fst.prodMk ((a i).continuous.comp continuous_snd)⟩)
    (fun x=>by change H (0,a i x)=f (cell a i (boundary n x));rw [h,cell_boundary])).comp
      ⟨Prod.swap,continuous_swap⟩).curry
lemma cellPaths_boundary (i : J) (x : Sphere n) :
    cellPaths a f H h i (boundary n x)=basePaths H (a i x) := by
  apply ContinuousMap.ext
  intro t
  dsimp only [cellPaths,basePaths,ContinuousMap.curry_apply,ContinuousMap.comp_apply,ContinuousMap.coe_mk,Prod.swap]
  change CellHEP.extension _ _ _ (t,Cellular.boundary n x)=_
  rw [CellHEP.extension_boundary]
  rfl
lemma cellPaths_zero (i : J) (d : Disk n) : cellPaths a f H h i d 0=f (cell a i d) := by
  dsimp only [cellPaths,ContinuousMap.curry_apply,ContinuousMap.comp_apply,ContinuousMap.coe_mk,Prod.swap]
  rw [CellHEP.extension_zero]
  rfl
def paths : C(Space a,C(unitInterval,Y)) :=
  lift a (basePaths H) (cellPaths a f H h) (cellPaths_boundary a f H h)
lemma paths_zero (x : Space a) : paths a f H h x 0=f x := by
  have he : (eval 0).comp (paths a f H h)=f := by
    apply lift_unique a
    · intro x
      exact h x
    · intro i d
      change paths a f H h (cell a i d) 0=f (cell a i d)
      rw [paths,lift_cell]
      exact cellPaths_zero a f H h i d
  exact ContinuousMap.congr_fun he x
/-- Homotopy extension for a genuine disk attachment with arbitrarily many
cells. Currying into the compact-open path space respects the weak topology. -/
def extend : C(unitInterval × Space a,Y) := (paths a f H h).uncurry.comp ⟨Prod.swap,continuous_swap⟩
lemma extend_zero (x : Space a) : extend a f H h (0,x)=f x := paths_zero a f H h x
def endpoint : C(Space a,Y) := (eval 1).comp (paths a f H h)
def homotopy : f.Homotopy (endpoint a f H h) where
  toContinuousMap := extend a f H h
  map_zero_left := extend_zero a f H h
  map_one_left _ := rfl
end
end TorsionFreeZeroDivisors.AttachmentHEP

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.VertexCollapse
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
open scoped unitInterval
noncomputable section
variable {G S Q Y : Type} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace Y] [PathConnectedSpace Y]
variable (s : S→G) (a : Q→C(Sphere 2,Cayley.Graph s)) (f : C(CellPresentation.Cover s a,Y)) (y : Y)
def vertexPath (g : G) : Path (f (CellPresentation.inclusion s a (Cayley.vertex s g))) y :=
  PathConnectedSpace.somePath _ _
def vertices : C(unitInterval × G,Y) :=
  ((⟨fun g=>(vertexPath s a f y g).toContinuousMap,continuous_of_discreteTopology⟩ :
    C(G,C(unitInterval,Y))).uncurry).comp ⟨Prod.swap,continuous_swap⟩
lemma vertices_zero (g : G) : vertices s a f y (0,g)=f (CellPresentation.inclusion s a (Cayley.vertex s g)) :=
  Path.source _
lemma vertices_one (g : G) : vertices s a f y (1,g)=y := Path.target _
def graph : C(unitInterval × Cayley.Graph s,Y) :=
  AttachmentHEP.extend (equivariantFamily (G:=G) (Cayley.attaching s))
    (f.comp (CellPresentation.inclusion s a)) (vertices s a f y) (vertices_zero s a f y)
lemma graph_zero (z : Cayley.Graph s) : graph s a f y (0,z)=f (CellPresentation.inclusion s a z) :=
  AttachmentHEP.extend_zero _ _ _ _ z
/-- Homotope an actual map on the whole presentation complex so that EVERY
vertex goes to one basepoint. Both cell layers are extended, not collapsed by
an unproved quotient/homotopy-equivalence assertion. -/
def map : C(CellPresentation.Cover s a,Y) :=
  AttachmentHEP.endpoint (equivariantFamily (G:=G) a) f (graph s a f y) (graph_zero s a f y)
def homotopy : f.Homotopy (map s a f y) :=
  AttachmentHEP.homotopy (equivariantFamily (G:=G) a) f (graph s a f y) (graph_zero s a f y)
lemma map_vertex (g : G) : map s a f y (CellPresentation.inclusion s a (Cayley.vertex s g))=y :=
  vertices_one s a f y g
end
end TorsionFreeZeroDivisors.VertexCollapse


end



end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.BlockGrid

end TorsionFreeZeroDivisors.BlockGrid

/-! Exact half-integer alignment, including the reflection endpoint conventions.
Uniform deficit bounds converge to zero relative to s
when |a/s-ν| does; no rounding of the prescribed real grid s is needed. -/
namespace TorsionFreeZeroDivisors.BlockAlignment

section
open scoped Classical

def block (s : ℝ) (k : ℤ) : Finset ℤ := positions ((k : ℝ)*s) (((k : ℝ)+1)*s)

end

open scoped Classical BigOperators

def blockCount (s : ℝ) (ell : ℕ) : ℕ := ⌊(ell : ℝ)/s⌋₊

end TorsionFreeZeroDivisors.BlockAlignment

/-! Extraction of the actual partial matching of block occurrences from the
original comparison pairing. Comparison sides are retained,
so a block cannot join itself by aggregating several short comparisons. -/

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.EntropyStages
end TorsionFreeZeroDivisors.EntropyStages

namespace TorsionFreeZeroDivisors.OccurrenceMatching
open scoped Classical
open EntropyStages
variable {Ω B E : Type*}

namespace Data

open scoped BigOperators
variable [Fintype Ω] [Fintype B]

end Data
end TorsionFreeZeroDivisors.OccurrenceMatching

/-! The actual common-grid block matching of an affine comparison system.
Positions are the literal half-integer edge indices within each traversal. -/
namespace TorsionFreeZeroDivisors.ComparedBlocks
open scoped Classical BigOperators
open BlockAlignment EntropyStages
variable {T E : Type*}
abbrev Block (s : ℝ) (len : T → ℕ) := (t : T) × Fin (blockCount s (len t))

variable (s : ℝ) (hs : 0 < s) (len : T → ℕ)

namespace Comparisons
variable (C : Comparisons (E := E) len) (err : ℕ)

variable [Fintype T] [Fintype E]

end Comparisons
end TorsionFreeZeroDivisors.ComparedBlocks

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.BlockPropagation

open scoped BigOperators

namespace Skeleton

variable {I T : Type*} (h : I → ℕ) (known : (i : I) → Finset (Fin (h i)))

variable [Fintype I] [Fintype T] [DecidableEq I]

end Skeleton
end TorsionFreeZeroDivisors.BlockPropagation

/-! Label projection along connected substring links.
A link determines a specified subset of one block from positions in its
partner word, via a letter equivalence such as identity or inversion.
No embedding of inactive graph vertices is requested or assumed. -/
namespace TorsionFreeZeroDivisors.StageLabels

section
open scoped Classical BigOperators
open BlockPropagation

variable {I T : Type*} [Fintype I] [Fintype T] [Nonempty T]

namespace Links
variable {h : I → ℕ}

end Links

variable {C : Type*} [Fintype C] (color : I → C) (h : I → ℕ)

end

open scoped Classical BigOperators
variable {I T : Type*} [Fintype I] [Fintype T] [Nonempty T]
variable {h : I → ℕ}

namespace Links

end Links
end TorsionFreeZeroDivisors.StageLabels

/-! The link constraints are now extracted from the actual occurrence
matching, rather than supplied as an unexplained propagation hypothesis. -/

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MatchedLabels
open scoped Classical
open OccurrenceMatching StageLabels
variable {Ω B E I A : Type*}
variable (color : B → I)
variable (h : I → ℕ)
variable (symbol : E → (A ≃ A))

namespace Witness
variable {D color} {i j : I}

end Witness

end TorsionFreeZeroDivisors.MatchedLabels

namespace TorsionFreeZeroDivisors.BlockConstraints

open scoped BigOperators

namespace ParentMap

variable {h : ℕ} {T : Type*}

end ParentMap

namespace Translation

variable {h : ℕ}

end Translation

end TorsionFreeZeroDivisors.BlockConstraints

namespace TorsionFreeZeroDivisors.IntervalSelfLinks
open scoped Classical
open BlockConstraints

/-- The literal increasing coordinate on a contiguous block of integer edge
indices (the manuscript's half-integer centers shifted by 1/2). -/
def coordinate (lo hi : ℤ) : (Finset.Ico lo hi) ≃ Fin (hi-lo).toNat where
  toFun q := ⟨(q.val-lo).toNat,by
    have hq := Finset.mem_Ico.mp q.property
    omega⟩
  invFun k := ⟨lo+k.val,by
    apply Finset.mem_Ico.mpr
    have hk := k.isLt
    omega⟩
  left_inv q := by
    apply Subtype.ext
    have hq := Finset.mem_Ico.mp q.property
    dsimp
    omega
  right_inv k := by
    apply Fin.ext
    dsimp
    omega

theorem coordinate_val {lo hi : ℤ} (q : Finset.Ico lo hi) :
    ((coordinate lo hi q).val : ℤ) = q.val-lo := by
  have hq := Finset.mem_Ico.mp q.property
  dsimp [coordinate]
  omega

variable (lo hi a : ℤ) (D : Finset ℤ)
variable (ha : 0 < a) (hD : ∀ q ∈ D, q ∈ Finset.Ico lo hi ∧ q+a ∈ Finset.Ico lo hi)

end TorsionFreeZeroDivisors.IntervalSelfLinks

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.IntervalSelfLinks
open scoped Classical

end TorsionFreeZeroDivisors.IntervalSelfLinks

/-!
Finite combinatorial and numerical bounds: occurrence pairings,
layer-cake stage counts and selection of one small stage. None of the graph
existence, matching estimates or topological assertions is an assumption here.
-/

namespace TorsionFreeZeroDivisors.EntropyStages

open scoped BigOperators

namespace Pairing

variable {O C : Type*} [Fintype O] [DecidableEq O] [DecidableEq C] (P : Pairing O)

end Pairing

end TorsionFreeZeroDivisors.EntropyStages

namespace TorsionFreeZeroDivisors
open scoped BigOperators

end TorsionFreeZeroDivisors

namespace TorsionFreeZeroDivisors.StageFusion

section
open scoped BigOperators
open EntropyStages

section Components
variable {C : Type*} [Fintype C] {I : C → Type*} [∀ c, Fintype (I c)]

end Components

end

open scoped Classical BigOperators

section FiniteProbability
variable {Ω P : Type*} [Fintype P] (sample : Finset Ω) (hsample : sample.Nonempty)

end FiniteProbability

end TorsionFreeZeroDivisors.StageFusion

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.LinkComponents
open scoped Classical BigOperators
open EntropyStages
variable {I : Type*} [Fintype I] (m : I → ℕ)
abbrev Occurrence := (i : I) × Fin (m i)
variable (P : Pairing (Occurrence m))

end TorsionFreeZeroDivisors.LinkComponents

namespace TorsionFreeZeroDivisors.OccurrenceMatching.Data
open scoped Classical
variable {Ω B B' E : Type*}

end TorsionFreeZeroDivisors.OccurrenceMatching.Data

namespace TorsionFreeZeroDivisors.RepeatedBlocks
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {C E : Type*} (s : ℝ) (hs : 0 < s) (len m : C → ℕ)
abbrev traversalLength : Traversal m → ℕ := fun t => len t.1
abbrev Underlying := ComparedBlocks.Block s len
abbrev Occurrence := ComparedBlocks.Block s (traversalLength len m)
abbrev multiplicity (i : Underlying s len) : ℕ := m i.1

/-- The occurrence index is retained separately from the common chain grid. -/
def occurrenceEquiv : Occurrence s len m ≃ LinkComponents.Occurrence (multiplicity s len m) where
  toFun b := ⟨⟨b.1.1,b.2⟩,b.1.2⟩
  invFun b := ⟨⟨b.1.1,b.2⟩,b.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def color (b : Occurrence s len m) : Underlying s len := (occurrenceEquiv s len m b).1

def height (i : Underlying s len) : ℕ := (block s i.2.val).card

def lower (i : Underlying s len) : ℤ := ⌈(i.2.val : ℝ)*s-1/2⌉
def upper (i : Underlying s len) : ℤ := ⌈((i.2.val : ℝ)+1)*s-1/2⌉

theorem block_interval (i : Underlying s len) : block s i.2.val = Finset.Ico (lower s len i) (upper s len i) := by
  simp only [block,positions,lower,upper,Int.cast_natCast]

/-- Literal increasing edge coordinates shared by every repetition. -/
def wordCoordinate (i : Underlying s len) : block s i.2.val ≃ Fin (height s len i) :=
  (Equiv.setCongr (congrArg (fun positions : Finset ℤ => (positions : Set ℤ)) (block_interval s len i))).trans
    ((IntervalSelfLinks.coordinate (lower s len i) (upper s len i)).trans
      (finCongr (by rw [height,block_interval,Int.card_Ico])))

theorem wordCoordinate_val (i : Underlying s len) (q : block s i.2.val) :
    ((wordCoordinate s len i q).val : ℤ) = q.val-lower s len i := by
  exact IntervalSelfLinks.coordinate_val ⟨q.val,by rw [← block_interval]; exact q.property⟩

variable (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

variable {A : Type*} (symbol : E → (A ≃ A))

end TorsionFreeZeroDivisors.RepeatedBlocks

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors
namespace WordEstimate

open scoped BigOperators

def inverse (t : Letter) : Letter := (t.1, !t.2)

def IsExtra (t : Letter) : Prop := ∃ i : Fin 3, t = (Sum.inl i, true)

instance (t : Letter) : Decidable (IsExtra t) := inferInstanceAs (Decidable (∃ _, _))

@[simp] theorem isExtra_inl (i : Fin 3) (b : Bool) :
    IsExtra (Sum.inl i, b) ↔ b = true := by simp [IsExtra, Prod.mk.injEq]

@[simp] theorem not_isExtra_inr (i : Fin 8255) (b : Bool) :
    ¬IsExtra (Sum.inr i, b) := by simp [IsExtra]

@[simp] theorem inverse_inverse (t : Letter) : inverse (inverse t) = t := by
  simp [inverse]

/-! Binning the weights: entropy.tex, equation (entropy-bins). -/

end WordEstimate
end TorsionFreeZeroDivisors

namespace TorsionFreeZeroDivisors.WordEstimate
open scoped BigOperators

end TorsionFreeZeroDivisors.WordEstimate

/-! Source entropy.tex 300--458, with all local root counts evaluated rather
than assumed. A translation self-link saves the root; a component without one
uses its selected bin-minimizing root. Reflection self-links are ruled out by
`BlockConstraints.reflection_impossible` before this count is applied. -/

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageBlocks
open scoped BigOperators Classical
open StageLabels WordEstimate
variable {I : Type*} [Fintype I] {h : I → ℕ}
variable (d : I → ℤ)

end TorsionFreeZeroDivisors.StageBlocks

namespace TorsionFreeZeroDivisors.ActualStageLabels

open scoped Classical BigOperators
section
end
open scoped Classical BigOperators
open ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ)
variable (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

variable (d : Underlying s len → ℤ)

end TorsionFreeZeroDivisors.ActualStageLabels

namespace TorsionFreeZeroDivisors.ChainStageLabels
open scoped Classical BigOperators
section
end
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ) (j : ℕ)

abbrev ActiveChain := {c : C // j < m c}

variable (cmp : Comparisons (E := E) (traversalLength len m)) (d : Underlying s len → ℤ)

end TorsionFreeZeroDivisors.ChainStageLabels

end

end OAI

end
end

section
section
namespace OAI



section

/-!
The uniform maximum-degree exclusion bound for finite graph balls.
This treats labelled port graphs too: `neighbors` forgets multiplicities;
loops and multiple edges only decrease the number of distinct vertices.
-/

namespace TorsionFreeZeroDivisors.BallCount

open scoped BigOperators
noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Endpoints of walks of exactly k steps. -/
def ends (neighbors : V → Finset V) (x : V) : ℕ → Finset V
  | 0 => {x}
  | k + 1 => (ends neighbors x k).biUnion neighbors

/-- Finite closed combinatorial ball. -/
def ball (neighbors : V → Finset V) (x : V) (r : ℕ) : Finset V :=
  (Finset.range (r + 1)).biUnion (ends neighbors x)

@[simp] theorem mem_ball_iff (neighbors : V → Finset V) (x y : V) (r : ℕ) :
    y ∈ ball neighbors x r ↔ ∃ k ≤ r, y ∈ ends neighbors x k := by
  simp [ball]

/-- The ordinary finite neighbor set, with its classical finiteness data fixed. -/
def graphNeighbors [Fintype V] (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact G.neighborFinset v

omit [DecidableEq V] in
@[simp] theorem mem_graphNeighbors [Fintype V] (G : SimpleGraph V) (a b : V) :
    b ∈ graphNeighbors G a ↔ G.Adj a b := by
  classical
  simp [graphNeighbors]

section Matchings
variable {X Y : Type*} [Fintype X] [DecidableEq X]

end Matchings
end
end TorsionFreeZeroDivisors.BallCount


/-!
A faithful simple-graph encoding of the manuscript's labelled multigraphs.
An original edge has two opposite ports, and its threefold subdivision is
original vertex -- port -- opposite port -- original vertex. Loops become
triangles and parallel edges remain distinct, so neither is silently discarded.
-/

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PortSubdivision

namespace PortGraph
variable {V D : Type*} (Γ : PortGraph V D)

@[simp] theorem adj_original (v w : V) : ¬ Γ.subdivision.Adj (.inl v) (.inl w) := id
@[simp] theorem adj_original_port (v : V) (d : D) :
    Γ.subdivision.Adj (.inl v) (.inr d) ↔ Γ.origin d = v := Iff.rfl
@[simp] theorem adj_port_original (v : V) (d : D) :
    Γ.subdivision.Adj (.inr d) (.inl v) ↔ Γ.origin d = v := Iff.rfl
@[simp] theorem adj_ports (d e : D) :
    Γ.subdivision.Adj (.inr d) (.inr e) ↔ Γ.reverse d = e := Iff.rfl

/-- Conjugating the reversal while keeping port origins fixed is a
matching switch, not a relabeling of the original graph. -/
def moveMatches (σ : Equiv.Perm D) : PortGraph V D where
  origin := Γ.origin
  reverse d := σ (Γ.reverse (σ.symm d))
  reverse_reverse d := by simp
  reverse_ne d := by
    intro h
    have h' := congrArg σ.symm h
    simp only [Equiv.symm_apply_apply] at h'
    exact Γ.reverse_ne (σ.symm d) h'

section Switching
variable [DecidableEq D]

/-- Transpose two equally oriented ports. Their reverse ports are not moved. -/
def switch (d e : D) : PortGraph V D := Γ.moveMatches (Equiv.swap d e)

@[simp] theorem switch_origin (d e f : D) : (Γ.switch d e).origin f = Γ.origin f := rfl

/-- Transposing two occurrences of the same label preserves every port label. -/
theorem label_swap {T : Type*} (label : D → T) (d e : D) (h : label d = label e)
    (f : D) : label ((Equiv.swap d e) f) = label f := by
  by_cases hfd : f = d
  · subst f; simpa using h.symm
  · by_cases hfe : f = e
    · subst f; simpa using h
    · rw [Equiv.swap_apply_of_ne_of_ne hfd hfe]

end Switching

/-- Multigraph walks remember the traversed port, not just endpoint vertices. -/
inductive Walk : V → V → Type _
  | nil (v : V) : Walk v v
  | cons {v w : V} (d : D) (hd : Γ.origin d = v)
      (p : Walk (Γ.origin (Γ.reverse d)) w) : Walk v w

namespace Walk
variable {Γ} {a b c : V}

def length {a b : V} : Γ.Walk a b → ℕ
  | .nil _ => 0
  | .cons _ _ p => p.length + 1

def darts {a b : V} : Γ.Walk a b → List D
  | .nil _ => []
  | .cons d _ p => d :: p.darts

def append {a b c : V} : Γ.Walk a b → Γ.Walk b c → Γ.Walk a c
  | .nil _,q => q
  | .cons d hd p,q => .cons d hd (p.append q)

@[simp] theorem length_darts (p : Γ.Walk a b) : p.darts.length = p.length := by
  induction p <;> simp_all [darts,length]

@[simp] theorem length_append (p : Γ.Walk a b) (q : Γ.Walk b c) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp [append,length]
  | cons d hd p ih => simp only [append,length,ih]; omega

/-- No changes to endpoints or to the original multigraph are made by subdividing. -/
def toSubdivision {a b : V} : Γ.Walk a b → Γ.subdivision.Walk (.inl a) (.inl b)
  | .nil a => .nil
  | .cons d hd p =>
    .cons (show Γ.subdivision.Adj (.inl a) (.inr d) from hd)
      (.cons (show Γ.subdivision.Adj (.inr d) (.inr (Γ.reverse d)) from rfl)
        (.cons (show Γ.subdivision.Adj (.inr (Γ.reverse d)) (.inl (Γ.origin (Γ.reverse d))) from rfl) p.toSubdivision))

@[simp] theorem length_toSubdivision (p : Γ.Walk a b) :
    p.toSubdivision.length = 3 * p.length := by
  induction p with
  | nil => rfl
  | cons d hd p ih => simp only [toSubdivision,SimpleGraph.Walk.length_cons,length,ih]; omega

@[simp] theorem toSubdivision_append (p : Γ.Walk a b) (q : Γ.Walk b c) :
    (p.append q).toSubdivision = p.toSubdivision.append q.toSubdivision := by
  induction p with
  | nil => rfl
  | cons d hd p ih => simp only [append,toSubdivision,SimpleGraph.Walk.cons_append,ih]

end Walk
end PortGraph
end TorsionFreeZeroDivisors.PortSubdivision

/-!
Quantitative edge switching for the girth conditioning in types.tex 116–147.
The simple-graph lemmas are also applicable to the canonical threefold
subdivision of a port multigraph (loops become triangles). No random-graph
existence or cone-topology conclusion is assumed in these lemmas.
-/

namespace TorsionFreeZeroDivisors.GirthSwitch

open SimpleGraph
open scoped ENNReal

variable {V : Type*} {G H : SimpleGraph V} {a b x y : V}

/-- Adjoining one new edge. -/
def addEdge (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  G ⊔ SimpleGraph.fromEdgeSet {s(x,y)}

@[simp] theorem addEdge_adj (u v : V) :
    (addEdge G x y).Adj u v ↔ G.Adj u v ∨ (s(u,v) = s(x,y) ∧ u ≠ v) := by
  simp [addEdge, SimpleGraph.fromEdgeSet_adj]

end TorsionFreeZeroDivisors.GirthSwitch

/-! ### Typed matching families have nonempty large-girth spaces. -/

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MatchingGraphs
open PortSubdivision BallCount GirthSwitch
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.ConditionedMatchings
open PortSubdivision BallCount GirthSwitch MatchingGraphs
variable {V D T : Type*}

namespace Matching
variable {label : D → T} {bar : T → T}
instance : CoeFun (Matching label bar) (fun _ => D → D) := ⟨fun r => r.val⟩
instance [Fintype D] : Fintype (Matching label bar) := by
  classical
  unfold Matching
  infer_instance
instance : DecidableEq (Matching label bar) := Classical.decEq _
theorem label_reverse (r : Matching label bar) (x : D) :
    label (r x) = bar (label x) := r.property.2.2 x

@[ext] theorem ext {r s : Matching label bar} (h : ∀ x, r x = s x) : r = s :=
  Subtype.ext (Equiv.ext h)

variable [DecidableEq D]

/-- Conjugating by the transposition of equally labelled ports. -/
def switch (r : Matching label bar) (x e : D) (he : label x = label e) : Matching label bar :=
  ⟨(Equiv.swap x e).trans (r.val.trans (Equiv.swap x e)),by
    constructor
    · intro f; simp
    constructor
    · intro f h
      have h' := congrArg (Equiv.swap x e) h
      simp only [Equiv.trans_apply,Equiv.swap_apply_self] at h'
      exact r.property.2.1 ((Equiv.swap x e) f) h'
    · intro f
      change label ((Equiv.swap x e) (r ((Equiv.swap x e) f))) = bar (label f)
      rw [PortGraph.label_swap label x e he, r.label_reverse,PortGraph.label_swap label x e he]⟩

@[simp] theorem switch_apply (r : Matching label bar) (x e : D) (he : label x = label e) (f : D) :
    r.switch x e he f = (Equiv.swap x e) (r ((Equiv.swap x e) f)) := rfl

@[simp] theorem switch_switch (r : Matching label bar) (x e : D) (he : label x = label e) :
    (r.switch x e he).switch x e he = r := by
  ext f
  simp

variable [Fintype V] [Fintype D]

end Matching
end TorsionFreeZeroDivisors.ConditionedMatchings

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternCount
open scoped Classical
open ConditionedMatchings
variable {V D T F E A : Type*} [Fintype V] [Fintype D] [Fintype F] [Fintype E]
variable (label : D → T) (bar : T → T)

end TorsionFreeZeroDivisors.PatternCount

namespace TorsionFreeZeroDivisors.PatternEmbeddings
open scoped BigOperators Classical
open PortSubdivision ConditionedMatchings
variable {PV PD TV T : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]

variable (Γ : PortGraph PV PD) (plabel : PD → T) (outgoing : TV → Finset T)
  (allowed : PV → Finset TV)
  (hallowed : ∀ v x, x ∈ allowed v → ∀ d, Γ.origin d = v → plabel d ∈ outgoing x)

end TorsionFreeZeroDivisors.PatternEmbeddings

/-!
Exact finite geometry and type system over the field with 128 elements.
-/

namespace TorsionFreeZeroDivisors
namespace Types

open scoped LinearAlgebra.Projectivization
open Configuration

instance : Fintype Field128 := Fintype.ofFinite _
instance : DecidableEq Field128 := Classical.decEq _

instance : Fintype Point := Fintype.ofFinite _
instance : DecidableEq Point := Classical.decEq _

instance (p : Point) (l : Line) : Decidable (p ∈ l) := Classical.propDecidable _

def linesOn (p : Point) : Finset Line := Finset.univ.filter (p ∈ ·)

@[simp] theorem mem_pointsOn {p : Point} {l : Line} : p ∈ pointsOn l ↔ p ∈ l := by
  simp [pointsOn]

@[simp] theorem mem_linesOn {p : Point} {l : Line} : l ∈ linesOn p ↔ p ∈ l := by
  simp [linesOn]

/-! The empirical type slots. Each line has exactly 33026 slots on each
side, before the admissible replication parameter is applied. -/

/-! ### The fixed inverse pairing and the actual space of graph matchings -/

@[simp] theorem inverse_signed (g : Generator) (b : Bool) :
    inverse (signedLetter (g,b)) = signedLetter (g,!b) := by simp [inverse]

@[simp] theorem inverse_inverse (t : Letter) : inverse (inverse t) = t := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  simp

variable {V : Type*} (outgoing : V → Finset Letter)

/-- Each inverse pair receives a bijection between its two carrier sets. -/
def MatchingTuple := (g : Generator) →
  {x : V // signedLetter (g,true) ∈ outgoing x} ≃
    {x : V // signedLetter (g,false) ∈ outgoing x}

/-- The direction of a step is given by the signed letter. Non-carrier
values are immaterial and are defined to fix the vertex. -/
def nextSigned (M : MatchingTuple outgoing) (x : V) : Signed → V
  | (g,true) => if hx : signedLetter (g,true) ∈ outgoing x then (M g ⟨x,hx⟩).val else x
  | (g,false) => if hx : signedLetter (g,false) ∈ outgoing x then ((M g).symm ⟨x,hx⟩).val else x

def next (M : MatchingTuple outgoing) (x : V) (t : Letter) : V :=
  nextSigned outgoing M x (signedLetter.symm t)

@[simp] theorem next_signed (M : MatchingTuple outgoing) (x : V) (g : Generator) (b : Bool) :
    next outgoing M x (signedLetter (g,b)) = nextSigned outgoing M x (g,b) := by
  simp [next]

/-! Joint type incidences for internal-chain vertex counts.
These derive the turn weights from the actual prescribed types. -/

end Types
end TorsionFreeZeroDivisors

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypeWeights
open TorsionFreeZeroDivisors.Types

end TorsionFreeZeroDivisors.TypeWeights

namespace TorsionFreeZeroDivisors.StageRealization
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {PV PD TV T : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]

section Typed
open TorsionFreeZeroDivisors.Types
variable (rep : ℕ) (Γ : PortGraph PV PD) (plabel : PD → Letter)
  (himm : Function.Injective (fun d => (Γ.origin d,plabel d)))
  (J : Finset PV) (a b : PV → PD)
  (ha : ∀ v ∈ J, Γ.origin (a v) = v) (hb : ∀ v ∈ J, Γ.origin (b v) = v)
  (hab : ∀ v ∈ J, a v ≠ b v)

include himm ha hb hab

end Typed

end TorsionFreeZeroDivisors.StageRealization

namespace TorsionFreeZeroDivisors.ChainSubdivision
open scoped Classical BigOperators
variable {C V : Type*} (len : C → ℕ) (first last : C → V)
abbrev Interior := (c : C) × Fin (len c-1)
abbrev Vertex := V ⊕ Interior len
abbrev Edge := (c : C) × Fin (len c)
abbrev Dart := Edge len × Bool

def point (c : C) (k : Fin (len c+1)) : Vertex len (V := V) :=
  if h0 : k.val=0 then .inl (first c) else if h1 : k.val=len c then .inl (last c)
  else .inr ⟨c,⟨k.val-1,by omega⟩⟩

def graph : PortSubdivision.PortGraph (Vertex len (V := V)) (Dart len) where
  origin d := point len first last d.1.1 ⟨d.1.2.val+(if d.2 then 1 else 0),by
    cases d.2 <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega⟩
  reverse d := (d.1,!d.2)
  reverse_reverse d := by simp
  reverse_ne d := by
    intro h
    have hh := congrArg Prod.snd h
    cases hb : d.2 <;> simp [hb] at hh

@[simp] theorem reverse (d : Dart len) : (graph len first last).reverse d = (d.1,!d.2) := rfl
@[simp] theorem origin_forward (e : Edge len) :
    (graph len first last).origin (e,false) = point len first last e.1 ⟨e.2.val,by omega⟩ := rfl
@[simp] theorem origin_backward (e : Edge len) :
    (graph len first last).origin (e,true) = point len first last e.1 ⟨e.2.val+1,by omega⟩ := rfl

@[simp] theorem at_zero (c : C) : point len first last c ⟨0,by omega⟩ = .inl (first c) := by
  simp [point]

@[simp] theorem at_interior (c : C) (k : Fin (len c-1)) :
    point len first last c ⟨k.val+1,by omega⟩ = .inr ⟨c,k⟩ := by
  have hk : k.val+1 ≠ len c := by omega
  simp [point,hk]

/-- Outgoing darts at an internal vertex: the preceding edge backwards and
following edge forwards, with no arbitrary choices. -/
def back (v : Interior len) : Dart len := (⟨v.1,⟨v.2.val,by omega⟩⟩,true)
def front (v : Interior len) : Dart len := (⟨v.1,⟨v.2.val+1,by omega⟩⟩,false)

@[simp] theorem back_origin (v : Interior len) :
    (graph len first last).origin (back len v) = .inr v := by
  simpa only [back,origin_backward] using at_interior len first last v.1 v.2
@[simp] theorem front_origin (v : Interior len) :
    (graph len first last).origin (front len v) = .inr v := by
  simpa only [front,origin_forward] using at_interior len first last v.1 v.2

theorem back_ne_front (v : Interior len) : back len v ≠ front len v := by
  intro h
  have hh := congrArg Prod.snd h
  cases hh

variable [Fintype C] [Fintype V]

@[simp] theorem card_edges : Fintype.card (Edge len) = ∑ c, len c := by
  simp [Edge,Fintype.card_sigma]

@[simp] theorem card_darts : Fintype.card (Dart len) = 2*∑ c, len c := by
  simp [Dart,Fintype.card_prod,Nat.mul_comm]

@[simp] theorem card_interiors : Fintype.card (Interior len) = ∑ c, (len c-1) := by
  simp [Interior,Fintype.card_sigma]

/-- The complete set of unmarked internal vertices. -/
def internal : Finset (Vertex len (V := V)) := Finset.univ.image Sum.inr


omit [Fintype V] in
@[simp] theorem mem_internal (v : Vertex len (V := V)) :
    v ∈ internal len (V := V) ↔ ∃ x, v = Sum.inr x := by
  simp [internal,eq_comm]


omit [Fintype V] in
@[simp] theorem card_internal : (internal len (V := V)).card = ∑ c, (len c-1) := by
  rw [internal,Finset.card_image_of_injective _ Sum.inr_injective,Finset.card_univ,card_interiors]

/-- Constant traversal multiplicity on each original marked chain. -/
def multiplicity (m : C → ℕ) (d : Dart len) := m d.1.1
omit [Fintype C] [Fintype V] in
@[simp] theorem multiplicity_reverse (m : C → ℕ) (d : Dart len) :
    multiplicity len m ((graph len first last).reverse d) = multiplicity len m d := rfl

end TorsionFreeZeroDivisors.ChainSubdivision

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageRealization
open scoped Classical
open PortSubdivision
end TorsionFreeZeroDivisors.StageRealization

namespace TorsionFreeZeroDivisors.ChainRealization
open scoped Classical BigOperators
open ChainSubdivision TorsionFreeZeroDivisors.Types
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C V : Type*} [Fintype C] [Fintype V]
variable (len : C → ℕ) (first last : C → V)

def label (w : C → ℤ → WordEstimate.Letter) (d : Dart len) : Types.Letter :=
  if d.2 then Types.inverse (signedLetter (w d.1.1 d.1.2.val))
  else signedLetter (w d.1.1 d.1.2.val)

omit [Fintype C] [Fintype V] in
@[simp] theorem label_reverse (w : C → ℤ → WordEstimate.Letter) (d : Dart len) :
    label len w ((graph len first last).reverse d) = Types.inverse (label len w d) := by
  rcases d with ⟨e,b⟩
  cases b <;> simp [label,Types.inverse_inverse]

omit [Fintype C] [Fintype V] in
@[simp] theorem label_back (w : C → ℤ → WordEstimate.Letter) (v : Interior len) :
    label len w (back len v) = Types.inverse (signedLetter (w v.1 v.2.val)) := rfl
omit [Fintype C] [Fintype V] in
@[simp] theorem label_front (w : C → ℤ → WordEstimate.Letter) (v : Interior len) :
    label len w (front len v) = signedLetter (w v.1 ((v.2.val : ℤ)+1)) := by
  simp [label,front,Nat.cast_add]

/-- Marked vertices carry the optional prescribed root. Internal vertices
never gain spurious pins. -/
def pin {TV : Type*} (p : V → Option TV) : Vertex len (V := V) → Option TV
  | .inl v => p v
  | .inr _ => none

omit [Fintype C] [Fintype V] in
@[simp] theorem pin_internal {TV : Type*} (p : V → Option TV) (v : Interior len) :
    pin len p (.inr v) = none := rfl

end TorsionFreeZeroDivisors.ChainRealization

namespace TorsionFreeZeroDivisors.ChainWeights
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len : C → ℕ)

def firstCoordinate (i : Underlying s len) (k : Fin (height s len i-1)) : block s i.2.val :=
  (wordCoordinate s len i).symm ⟨k.val,by omega⟩
def nextCoordinate (i : Underlying s len) (k : Fin (height s len i-1)) : block s i.2.val :=
  (wordCoordinate s len i).symm ⟨k.val+1,by omega⟩

omit [Fintype C] in
@[simp] theorem firstCoordinate_val (i : Underlying s len) (k : Fin (height s len i-1)) :
    (firstCoordinate s len i k).val = (k.val : ℤ)+lower s len i := by
  have h := wordCoordinate_val s len i (firstCoordinate s len i k)
  simp only [firstCoordinate,Equiv.apply_symm_apply] at h
  dsimp only [firstCoordinate]
  omega
omit [Fintype C] in
@[simp] theorem nextCoordinate_val (i : Underlying s len) (k : Fin (height s len i-1)) :
    (nextCoordinate s len i k).val = (k.val : ℤ)+lower s len i+1 := by
  have h := wordCoordinate_val s len i (nextCoordinate s len i k)
  simp only [nextCoordinate,Equiv.apply_symm_apply,Nat.cast_add,Nat.cast_one] at h
  dsimp only [nextCoordinate]
  omega

end TorsionFreeZeroDivisors.ChainWeights

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageExpectation
open scoped Classical BigOperators
open ChainSubdivision BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
section
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C V TV : Type*} [Fintype C] [Fintype V] [Fintype TV]
variable (s : ℝ) (hs : 0 < s) (len : C → ℕ) (first last : C → V)

/-- Finite letters on a chain, extended only to make the integer indexing
convenient. The fallback is never used at an edge of the pattern. -/
def readWord (F : ComparedBlocks.Position len → Letter) (c : C) (q : ℤ) : Letter :=
  if h : q ∈ positions 0 (len c) then F ⟨c,⟨q,h⟩⟩ else default

omit [Fintype C] in
@[simp] theorem readWord_on (F : ComparedBlocks.Position len → Letter) (c : C)
    (q : positions 0 (len c)) : readWord len F c q.val = F ⟨c,q⟩ := by
  simp [readWord,q.property]

end

section Active
open ChainStageLabels
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ) (j : ℕ)

abbrev activeLen : ActiveChain m j → ℕ := fun c => len c.val

end Active
variable {C V TV : Type*} [Fintype C] [Fintype V] [Fintype TV]
variable (s : ℝ) (hs : 0 < s) (len : C → ℕ) (first last : C → V)
local instance : DecidableEq Types.Letter := Classical.decEq _

end TorsionFreeZeroDivisors.StageExpectation

/-! Finite Fubini for the product of the separately girth-conditioned sides.
The label set here is global: it is not replaced by the product of its two
projections. This is the independence actually used in entropy.tex 396–435. -/
namespace TorsionFreeZeroDivisors.TwoSideMean
open scoped BigOperators Classical

variable {A B W : Type*}

end TorsionFreeZeroDivisors.TwoSideMean

namespace TorsionFreeZeroDivisors.TwoSideStage
open scoped Classical BigOperators
open ChainSubdivision PatternEmbeddings ConditionedMatchings BlockAlignment ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _

/-- A stage on one prescribed side. Its marked vertices do not include any
isolated vertices of inactive chains. The source number of available vertices
is n on EACH side, not the cardinality 2n of their disjoint union. -/
structure Side where
  C : Type
  V : Type
  TV : Type
  fC : Fintype C
  fV : Fintype V
  fTV : Fintype TV
  len : C → ℕ
  first : C → V
  last : C → V
  outgoing : TV → Finset Types.Letter
  pin : V → Option TV

variable (s : ℝ) (hs : 0 < s)

variable {W : Type*}

end TorsionFreeZeroDivisors.TwoSideStage

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TwoSideFullStage
open scoped Classical BigOperators
open RepeatedBlocks BlockAlignment ComparedBlocks ChainStageLabels WordEstimate
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {A B E VA VB TA TB : Type} [Fintype A] [Fintype B] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : A ⊕ B → ℕ) (j : ℕ)

abbrev CA := {a : A // j < m (.inl a)}
abbrev CB := {b : B // j < m (.inr b)}
abbrev lenA : CA m j → ℕ := fun a => len (.inl a.val)
abbrev lenB : CB m j → ℕ := fun b => len (.inr b.val)

variable (firstA lastA : CA m j → VA) (firstB lastB : CB m j → VB)
  (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter)
  (pinA : VA → Option TA) (pinB : VB → Option TB)

def sideA : TwoSideStage.Side where
  C := CA m j; V := VA; TV := TA
  fC := inferInstance; fV := inferInstance; fTV := inferInstance
  len := lenA len m j
  first := firstA; last := lastA; outgoing := outA; pin := pinA

def sideB : TwoSideStage.Side where
  C := CB m j; V := VB; TV := TB
  fC := inferInstance; fV := inferInstance; fTV := inferInstance
  len := lenB len m j
  first := firstB; last := lastB; outgoing := outB; pin := pinB

local notation "SA" => sideA len m j firstA lastA outA pinA
local notation "SB" => sideB len m j firstB lastB outB pinB

end TorsionFreeZeroDivisors.TwoSideFullStage

namespace TorsionFreeZeroDivisors.MatchingGraphs
open PortSubdivision BallCount GirthSwitch
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.TypedGraphs
open TorsionFreeZeroDivisors.Types PortSubdivision ConditionedMatchings MatchingGraphs
variable {V : Type*} (outgoing : V → Finset Letter)

end TorsionFreeZeroDivisors.TypedGraphs

namespace TorsionFreeZeroDivisors.GirthAsymptotics
open Filter
open scoped Topology

end TorsionFreeZeroDivisors.GirthAsymptotics

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedGraphs
open Filter GirthAsymptotics TorsionFreeZeroDivisors.Types ConditionedMatchings PortSubdivision
open scoped Topology

end TorsionFreeZeroDivisors.TypedGraphs

namespace TorsionFreeZeroDivisors.TypedStage
open scoped Classical BigOperators Topology
open TorsionFreeZeroDivisors.Types TwoSideStage GirthAsymptotics Filter
local instance : DecidableEq Types.Letter := Classical.decEq _

variable {C V : Type} [Fintype C] [Fintype V]
variable (rep : ℕ) (len : C → ℕ) (first last : C → V)

end TorsionFreeZeroDivisors.TypedStage

namespace TorsionFreeZeroDivisors.StageCost
open scoped BigOperators

end TorsionFreeZeroDivisors.StageCost

namespace TorsionFreeZeroDivisors.StageDenominator

section
open scoped Topology
open Filter GirthAsymptotics TypedGraphs

end

open scoped BigOperators Topology
open Filter GirthAsymptotics TypedGraphs TwoSideStage

variable {C V : Type} [Fintype C] [Fintype V]

end TorsionFreeZeroDivisors.StageDenominator

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageEntropy

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks ChainStageLabels WordEstimate
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0<s) (len m : C → ℕ)
    (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)
    (d : Underlying s len → ℤ)

end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks ChainStageLabels WordEstimate TwoSideFullStage
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {A B E VA VB TA TB : Type} [Fintype A] [Fintype B] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : A ⊕ B → ℕ) (j : ℕ)
variable (firstA lastA : CA m j → VA) (firstB lastB : CB m j → VB)
  (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter)
  (pinA : VA → Option TA) (pinB : VB → Option TB)
local notation "SA" => sideA len m j firstA lastA outA pinA
local notation "SB" => sideB len m j firstB lastB outB pinB

end TorsionFreeZeroDivisors.StageEntropy

namespace TorsionFreeZeroDivisors.OccurrenceMatching.Data
open scoped Classical
variable {Ω B B' E : Type*}

variable [Fintype B]
end TorsionFreeZeroDivisors.OccurrenceMatching.Data

namespace TorsionFreeZeroDivisors.StageMass

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0<s) (len m : C → ℕ)
  (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

variable [Fintype E]

end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
variable {C E : Type*} [Fintype C] [Fintype E]
  (s : ℝ) (hs : 0<s) (len m : C → ℕ)
  (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

end TorsionFreeZeroDivisors.StageMass

namespace TorsionFreeZeroDivisors.BinProfiles
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate

variable {C : Type*} [Fintype C]
end TorsionFreeZeroDivisors.BinProfiles

namespace TorsionFreeZeroDivisors.GridAsymptotics
open Filter Topology
open scoped Classical

end TorsionFreeZeroDivisors.GridAsymptotics

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GridUniform
open scoped Topology BigOperators
open Filter GridAsymptotics

end TorsionFreeZeroDivisors.GridUniform
namespace TorsionFreeZeroDivisors.StageUniform
open scoped Classical BigOperators Topology
open BlockAlignment ComparedBlocks RepeatedBlocks GridAsymptotics Filter

variable {C E : Type*} [Fintype C] [Fintype E]

open GirthAsymptotics TypedGraphs

end TorsionFreeZeroDivisors.StageUniform
namespace TorsionFreeZeroDivisors.GridUniform
open scoped Topology BigOperators
open Filter GridAsymptotics

end TorsionFreeZeroDivisors.GridUniform
namespace TorsionFreeZeroDivisors.BinProfiles
open scoped Classical
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] [Fintype E]

end TorsionFreeZeroDivisors.BinProfiles

namespace TorsionFreeZeroDivisors.RealizationTransport
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {PV PD TV T : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]

variable {Γ : PortGraph PV PD} {plabel : PD → T} {outgoing : TV → Finset T}
    {pin : PV → Option TV} {bar : T → T} {r : Matching (label outgoing) bar}
    (e : Embedding Γ plabel outgoing pin bar r)

variable {PV' PD' : Type*} [Fintype PV'] [Fintype PD']

end TorsionFreeZeroDivisors.RealizationTransport

namespace TorsionFreeZeroDivisors.TwoSideStage
open scoped Classical BigOperators
variable {W : Type*}

end TorsionFreeZeroDivisors.TwoSideStage

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedCycles
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- Expanded length, attached to undirected edges. -/
def weight (w : Sym2 V → ℝ) (p : G.Walk u v) : ℝ := (p.edges.map w).sum

@[simp] theorem weight_nil (w : Sym2 V → ℝ) (u : V) : weight w (G := G) (Walk.nil : G.Walk u u) = 0 := rfl
@[simp] theorem weight_cons (w : Sym2 V → ℝ) {a b c : V} (h : G.Adj a b)
    (p : G.Walk b c) : weight w (Walk.cons h p) = w s(a,b) + weight w p := rfl
@[simp] theorem weight_append (w : Sym2 V → ℝ) {a b c : V}
    (p : G.Walk a b) (q : G.Walk b c) : weight w (p.append q) = weight w p + weight w q := by
  simp [weight]
@[simp] theorem weight_reverse (w : Sym2 V → ℝ) (p : G.Walk u v) :
    weight w p.reverse = weight w p := by simp [weight]

end TorsionFreeZeroDivisors.WeightedCycles
namespace TorsionFreeZeroDivisors.WeightedMoore
open scoped BigOperators

instance {D : Type*} [Fintype D] (k : ℕ) : Fintype (Chain D k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype D)
  | succ k ih => exact inferInstanceAs (Fintype (D × Chain D k))

def head {D : Type*} : {k : ℕ} → Chain D k → D
  | 0, p => p
  | _+1, p => p.1

def last {D : Type*} : {k : ℕ} → Chain D k → D
  | 0, p => p
  | _+1, p => last p.2

variable {D : Type*} [Fintype D] (T : D → D → ℝ)

variable {T}

namespace PortWalk

variable {V : Type*} (origin : D → V) (rev : D → D)
    (hinv : Function.Involutive rev)

open scoped Classical

include hinv

end PortWalk

end TorsionFreeZeroDivisors.WeightedMoore

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedPortMoore
open SimpleGraph WeightedMoore PortSubdivision WeightedCycles
variable {V D : Type*} (Γ : PortGraph V D)

/-- Validity as a chain of actual nonbacktracking directed edges. -/
def Good : {k : ℕ} → Chain D k → Prop
  | 0, _ => True
  | _+1, p => PortWalk.step Γ.origin Γ.reverse p.1 (head p.2) ∧ Good p.2

/-- The physical port walk, starting and ending at the first/last ports.
It has one middle edge per macro-edge, and two spokes between them. -/
def draw : {k : ℕ} → (p : Chain D k) → Good Γ p →
    Γ.subdivision.Walk (.inr (head p)) (.inr (Γ.reverse (last p)))
  | 0, d, _ => Walk.cons (show Γ.subdivision.Adj (.inr d) (.inr (Γ.reverse d)) from rfl) Walk.nil
  | _+1, p, h =>
    Walk.cons (show Γ.subdivision.Adj (.inr p.1) (.inr (Γ.reverse p.1)) from rfl)
      (Walk.cons (show Γ.subdivision.Adj (.inr (Γ.reverse p.1)) (.inl (Γ.origin (Γ.reverse p.1))) from rfl)
        (Walk.cons (show Γ.subdivision.Adj (.inl (Γ.origin (Γ.reverse p.1))) (.inr (head p.2)) from h.1.1.symm)
          (draw p.2 h.2)))

@[simp] theorem draw_head_edge {k : ℕ} (p : Chain D k) (hp : Good Γ p) :
    (draw Γ p hp).edges.head? = some s(Sum.inr (head p),Sum.inr (Γ.reverse (head p))) := by
  cases k <;> rfl

/-- Nonnegative symmetric length on the subdivision; spokes cost zero. -/
def edgeWeight (len : D → ℝ) : Sym2 (V ⊕ D) → ℝ :=
  Sym2.lift ⟨fun a b => match a,b with
    | .inr d,.inr e => (len d+len e)/2
    | _,_ => 0, by intro a b; cases a <;> cases b <;> simp [add_comm]⟩

@[simp] theorem edgeWeight_spoke (len : D → ℝ) (v : V) (d : D) :
    edgeWeight len s(Sum.inl v,Sum.inr d) = 0 := rfl

@[simp] theorem edgeWeight_middle (len : D → ℝ) (hsym : ∀ d, len (Γ.reverse d) = len d) (d : D) :
    edgeWeight (V := V) len s(Sum.inr d,Sum.inr (Γ.reverse d)) = len d := by
  change (len d+len (Γ.reverse d))/2 = len d
  rw [hsym]; ring

end TorsionFreeZeroDivisors.WeightedPortMoore

namespace TorsionFreeZeroDivisors.ChainSuppression
open Function
open scoped Classical

variable {D : Type*} (σ τ : D → D)
    (hσ : Involutive σ) (hτ : Involutive τ)

include hσ hτ

include hσ hτ
variable [Finite D]

/-- Each directed edge can be traversed at most once among all oriented
maximal chains. This is the exact disjoint-interior count, not a bound supplied
as an extra hypothesis. -/
lemma chain_dart_injective :
    Injective (fun p : (x : {x : D // τ x=x}) × Fin (length σ τ hσ hτ x.val x.property) =>
      (next σ τ)^[p.2.val] p.1.val) := by
  intro ⟨x,i⟩ ⟨y,j⟩ he
  have hone (x y : {x : D // τ x=x})
      (i : Fin (length σ τ hσ hτ x.val x.property))
      (j : Fin (length σ τ hσ hτ y.val y.property))
      (hij : i.val ≤ j.val)
      (he : (next σ τ)^[i.val] x.val=(next σ τ)^[j.val] y.val) :
      x=y ∧ i.val=j.val := by
    have hji : j.val=i.val+(j.val-i.val) := by omega
    rw [hji,iterate_add_apply] at he
    have hr := ((next_injective σ τ hσ hτ).iterate i.val) he
    have hzero : j.val-i.val=0 := by
      by_contra hz
      have hf : τ ((next σ τ)^[j.val-i.val] y.val)=(next σ τ)^[j.val-i.val] y.val := by
        rw [← hr]; exact x.property
      exact no_internal_mark σ τ hσ hτ y.val y.property (Nat.pos_of_ne_zero hz)
        (by omega) hf
    have hexy : x=y := by
      apply Subtype.ext
      simpa only [hzero,iterate_zero,id_eq] using hr
    exact ⟨hexy,by omega⟩
  have hxy : x=y ∧ i.val=j.val := by
    rcases le_total i.val j.val with hij | hji
    · exact hone x y i j hij he
    · obtain ⟨hexy,hij⟩ := hone y x j i hji he.symm
      exact ⟨hexy.symm,hij.symm⟩
  obtain ⟨rfl,hij⟩ := hxy
  congr 1
  exact Fin.ext hij

end TorsionFreeZeroDivisors.ChainSuppression

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.DegreeTwoSuppression
open Function
open scoped Classical
open TorsionFreeZeroDivisors ChainSuppression PortSubdivision
variable {V D : Type*} [Fintype D]

variable (o : D → V) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out o v).card=2)

lemma turn_origin (d : D) : o (turn o mark h2 d)=o d := by
  by_cases hd : mark (o d)
  · rw [turn_of_mark o mark h2 d hd]
  · exact (turn_of_unmarked o mark h2 d hd).1

lemma turn_fixed_iff (d : D) : turn o mark h2 d=d ↔ mark (o d) := by
  constructor
  · intro he
    by_contra hd
    exact (turn_of_unmarked o mark h2 d hd).2 he
  · exact turn_of_mark o mark h2 d

lemma chainLength_pos (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (d : {d : D // turn Γ.origin mark h2 d=d}) : 0 < chainLength Γ mark h2 d :=
  length_pos _ _ _ _ _ _

lemma chainLength_reverse (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (d : {d : D // turn Γ.origin mark h2 d=d}) :
    chainLength Γ mark h2 ((suppressed Γ mark h2).reverse d)=chainLength Γ mark h2 d :=
  length_endpoint _ _ _ _ _

end TorsionFreeZeroDivisors.DegreeTwoSuppression

namespace TorsionFreeZeroDivisors.SuppressedMoore
open Function SimpleGraph
open scoped Classical
open TorsionFreeZeroDivisors PortSubdivision WeightedMoore WeightedPortMoore
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)

local notation "τ" => DegreeTwoSuppression.turn Γ.origin mark h2
local notation "hτ" => DegreeTwoSuppression.turn_involutive Γ.origin mark h2
local notation "F" => ChainSuppression.next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "Γ'" => DegreeTwoSuppression.suppressed Γ mark h2
local notation "len" => DegreeTwoSuppression.chainLength Γ mark h2

omit [Fintype D] in
@[simp] lemma head_iterChain (f : D → D) (n : ℕ) (x : D) : head (iterChain f n x)=x := by
  cases n <;> rfl

omit [Fintype D] in
@[simp] lemma last_iterChain (f : D → D) (n : ℕ) (x : D) :
    last (iterChain f n x)=f^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change last (iterChain f n (f x))=f^[n+1] x
    rw [ih,iterate_succ_apply]

lemma chain_last (d : B) : Γ.reverse (last (iterChain F (len d-1) d.val)) = ((Γ').reverse d).val := by
  rw [last_iterChain]
  have hf := ((Γ').reverse d).property
  change τ (F^[len d] d.val)=F^[len d] d.val at hf
  have hk : len d=(len d-1)+1 := by
    have hp := DegreeTwoSuppression.chainLength_pos Γ mark h2 d
    omega
  conv_lhs at hf => rw [hk,iterate_succ_apply']
  change τ (τ (Γ.reverse (F^[len d-1] d.val)))=F^[len d] d.val at hf
  rw [hτ] at hf
  exact hf

end TorsionFreeZeroDivisors.SuppressedMoore

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.CoreStripping
open PortSubdivision
open scoped Classical
variable {V D : Type*} (Γ : PortGraph V D)

variable [Fintype V]

end TorsionFreeZeroDivisors.CoreStripping

namespace TorsionFreeZeroDivisors.ImageComplexity
open PortSubdivision WeightedPortMoore WeightedCycles CoreStripping
open scoped BigOperators Classical
variable {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)

end TorsionFreeZeroDivisors.ImageComplexity

namespace TorsionFreeZeroDivisors.SystemLeaves
open SimpleGraph PortSubdivision
open scoped Classical
variable {W : Type*} {G : SimpleGraph W}

variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)

variable [Fintype V]

end TorsionFreeZeroDivisors.SystemLeaves

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainCoverage
open Function ChainSuppression
open scoped Classical
variable {D : Type*} [Finite D] (σ τ : D → D)
    (hσ : Involutive σ) (hτ : Involutive τ)

end TorsionFreeZeroDivisors.ChainCoverage

namespace TorsionFreeZeroDivisors.ActualMarkedChains
open Function PortSubdivision ChainSuppression DegreeTwoSuppression ChainCoverage
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)

end TorsionFreeZeroDivisors.ActualMarkedChains

namespace TorsionFreeZeroDivisors.MarkedChainBound
open PortSubdivision DegreeTwoSuppression CoreStripping ImageComplexity
open scoped Classical BigOperators
variable {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)

end TorsionFreeZeroDivisors.MarkedChainBound

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore WeightedPortMoore SuppressedMoore ActualMarkedChains
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "len" => chainLength Γ mark h2

omit [Fintype D] in
/-- Enumerating a chain lists precisely the forward iterates before its first mark. -/
lemma outWord_iterChain (f : D → D) (n : ℕ) (x : D) :
    outWord (iterChain f n x) = (List.range (n+1)).map (fun i => f^[i] x) := by
  induction n generalizing x with
  | zero => simp [iterChain,outWord]
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [iterChain,outWord,ih,List.map_cons,List.map_map,iterate_zero,id_eq]
    congr 1

lemma word_eq_range (d : B) :
    word Γ mark h2 d = (List.range (len d)).map (fun i => F^[i] d.val) := by
  rw [word,outWord_iterChain]
  have h := chainLength_pos Γ mark h2 d
  congr 2
  omega

lemma mem_word_iff (d : B) (x : D) :
    x∈word Γ mark h2 d ↔ ∃ i : Fin (len d), F^[i.val] d.val=x := by
  rw [word_eq_range,List.mem_map]
  constructor
  · rintro ⟨i,hi,hx⟩
    exact ⟨⟨i,List.mem_range.mp hi⟩,hx⟩
  · rintro ⟨i,hx⟩
    exact ⟨i.val,List.mem_range.mpr i.isLt,hx⟩

lemma words_disjoint {d e : B} (hne : d≠e) :
    List.Disjoint (word Γ mark h2 d) (word Γ mark h2 e) := by
  intro x hx hy
  obtain ⟨i,hi⟩ := (mem_word_iff Γ mark h2 d x).mp hx
  obtain ⟨j,hj⟩ := (mem_word_iff Γ mark h2 e x).mp hy
  have h := chain_dart_injective Γ.reverse τ Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2) (a₁ := ⟨d,i⟩) (a₂ := ⟨e,j⟩) (hi.trans hj.symm)
  exact hne (congrArg Sigma.fst h)

end TorsionFreeZeroDivisors.ChainPaths

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MultiplicityBound
open SimpleGraph WeightedCycles
variable {V : Type*} {G : SimpleGraph V}

end TorsionFreeZeroDivisors.MultiplicityBound

namespace TorsionFreeZeroDivisors.PathMultiplicity
open SimpleGraph WeightedCycles WeightedMoore WeightedPortMoore
open PortSubdivision SuppressedMoore
open scoped Classical
variable {V D : Type*} (Γ : PortGraph V D)
local instance : BEq (V ⊕ D) := instBEqOfDecidableEq

/-- Convert a literal nonempty dart path to the dependent chain encoding. -/
def pathChain (x : D) : (xs : List D) → Chain D xs.length
  | [] => x
  | y::ys => (x,pathChain y ys)

@[simp] lemma pathChain_head (x : D) (xs : List D) : head (pathChain x xs)=x := by
  cases xs <;> rfl

@[simp] lemma pathChain_word (x : D) (xs : List D) : outWord (pathChain x xs)=x::xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih => exact congrArg (List.cons x) (ih y)

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore WeightedPortMoore SuppressedMoore ActualMarkedChains
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "len" => chainLength Γ mark h2

lemma reverse_mem_word (d : B) (x : D) (hx : x∈word Γ mark h2 d) :
    Γ.reverse x∈word Γ mark h2 ((suppressed Γ mark h2).reverse d) := by
  obtain ⟨i,rfl⟩ := (mem_word_iff Γ mark h2 d x).mp hx
  let e := (suppressed Γ mark h2).reverse d
  let k := len d
  have hj : k-i.val-1 < len e := by
    rw [chainLength_reverse]
    have hi := i.isLt
    change i.val < k at hi
    omega
  rw [mem_word_iff]
  refine ⟨⟨k-i.val-1,hj⟩,?_⟩
  have hf := endpoint_reverse Γ.reverse τ Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2) (x:=d) (i:=k-i.val) (by change k-i.val ≤ k; omega)
  have he : k-(k-i.val)=i.val := by omega
  have hs : k-i.val=(k-i.val-1)+1 := by have hi := i.isLt; change i.val < k at hi; omega
  change F^[k-i.val] e.val = τ (F^[k-(k-i.val)] d.val) at hf
  rw [he,hs,iterate_succ_apply'] at hf
  have h := congrArg τ hf
  change τ (τ (Γ.reverse (F^[k-i.val-1] e.val))) = τ (τ (F^[i.val] d.val)) at h
  rw [turn_involutive Γ.origin mark h2,turn_involutive Γ.origin mark h2] at h
  have hh := congrArg Γ.reverse h
  rwa [Γ.reverse_reverse] at hh

end TorsionFreeZeroDivisors.ChainPaths

namespace TorsionFreeZeroDivisors.PathMultiplicity
open PortSubdivision WeightedCycles WeightedPortMoore
open scoped BigOperators Classical
variable {V D I : Type*} (Γ : PortGraph V D) [Fintype I]

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore WeightedPortMoore SuppressedMoore ActualMarkedChains WeightedCycles
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "B" => {d : D // τ d=d}

end TorsionFreeZeroDivisors.ChainPaths

namespace TorsionFreeZeroDivisors.IncidenceStages
open scoped Classical BigOperators
open EntropyStages
variable {O D V : Type*} [Fintype O] [Fintype D] [Fintype V]

/-- An incidence remembers its occurrence and which (oriented) half-edge it
uses. Passages pair incidences at a vertex; path endpoints are fixed points. -/
structure Passages (origin : D → V) (port : O → D) extends Pairing O where
  location : ∀ o, origin (port (partner o)) = origin (port o)
  reduced : ∀ o, partner o ≠ o → port (partner o) ≠ port o

namespace Passages
variable {origin : D → V} {port : O → D} (P : Passages origin port)

def multiplicity (d : D) : ℕ := Fintype.card {o : O // port o = d}

end Passages
end TorsionFreeZeroDivisors.IncidenceStages

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PathIncidences

section
open scoped Classical BigOperators
open EntropyStages IncidenceStages

namespace Opened
variable {O : Type*} (P : EntropyStages.Pairing O)

end Opened

variable {E D V : Type*} (origin : D → V) (reverse : D → D)
  (edge : E → D)
  (succ : Equiv.Perm E) (cut : Option E)

/-- Initial and terminal half-edge of an occurrence, respectively. -/
def port (x : E × Bool) : D := if x.2 then reverse (edge x.1) else edge x.1

end

open scoped Classical BigOperators
open EntropyStages IncidenceStages

variable {I D V : Type*} [Fintype I] [Fintype D] [Fintype V] {E : I → Type*}
  [∀ i, Fintype (E i)] (origin : D → V) (reverse : D → D)
  (edge : ∀ i, E i → D) (succ : ∀ i, Equiv.Perm (E i)) (cut : ∀ i, Option (E i))
  (hvertex : ∀ i e, cut i ≠ some (succ i e) →
    origin (edge i (succ i e)) = origin (reverse (edge i e)))
  (hreduced : ∀ i e, cut i ≠ some (succ i e) →
    edge i (succ i e) ≠ reverse (edge i e))

def familyPort (x : Σ i, E i × Bool) : D := port reverse (edge x.1) x.2

end TorsionFreeZeroDivisors.PathIncidences

namespace TorsionFreeZeroDivisors.StageSubgraphs
open scoped Classical BigOperators
open PortSubdivision
variable {V D : Type*} [Fintype V] [Fintype D] (Γ : PortGraph V D)

abbrev ActiveV (m : D → ℕ) (j : ℕ) := {v : V // ∃ d, Γ.origin d = v ∧ j < m d}

variable {I : Type*} [Fintype I] {E : I → Type*} [∀ i, Fintype (E i)]
  (edge : ∀ i, E i → D)

def multiplicity (d : D) : ℕ := IncidenceStages.Passages.multiplicity
  (port := PathIncidences.familyPort Γ.reverse edge) d

omit [Fintype V] [Fintype D] in
/-- Source traversal multiplicity agrees on the two orientations. -/
theorem multiplicity_reverse (d : D) :
    multiplicity Γ edge (Γ.reverse d) = multiplicity Γ edge d := by
  let flip : (Σ i, E i × Bool) ≃ (Σ i, E i × Bool) :=
    { toFun := fun x => ⟨x.1,x.2.1,!x.2.2⟩
      invFun := fun x => ⟨x.1,x.2.1,!x.2.2⟩
      left_inv := by rintro ⟨i,e,b⟩; cases b <;> rfl
      right_inv := by rintro ⟨i,e,b⟩; cases b <;> rfl }
  have hf (x : Σ i, E i × Bool) :
      PathIncidences.familyPort Γ.reverse edge (flip x) =
        Γ.reverse (PathIncidences.familyPort Γ.reverse edge x) := by
    rcases x with ⟨i,e,b⟩
    cases b
    · rfl
    · exact (Γ.reverse_reverse (edge i e)).symm
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv flip (fun o => by
    rw [hf]
    constructor
    · intro h
      rw [h,Γ.reverse_reverse]
    · intro h
      exact Γ.reverse_reverse.injective ((Γ.reverse_reverse d).symm ▸ h))

variable (succ : ∀ i, Equiv.Perm (E i)) (cut : ∀ i, Option (E i))
  (hvertex : ∀ i e, cut i ≠ some (succ i e) →
    Γ.origin (edge i (succ i e)) = Γ.origin (Γ.reverse (edge i e)))
  (hreduced : ∀ i e, cut i ≠ some (succ i e) →
    edge i (succ i e) ≠ Γ.reverse (edge i e))

end TorsionFreeZeroDivisors.StageSubgraphs

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ListPassages
open scoped Classical BigOperators

variable {D : Type*} (p : List D) (hp : p ≠ [])

end TorsionFreeZeroDivisors.ListPassages
namespace TorsionFreeZeroDivisors.ChainPathTransport
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open WeightedMoore
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "w" => word Γ mark h2

end TorsionFreeZeroDivisors.ChainPathTransport
namespace TorsionFreeZeroDivisors.ListStageExponents
open scoped Classical BigOperators
open PortSubdivision WeightedMoore StageSubgraphs
variable {V D I : Type*} [Fintype V] [Fintype D] [Fintype I]
    (Γ : PortGraph V D) (p : I → List D) (hp : ∀ i,p i ≠ [])
    (cyclic : I → Bool)
    (hc : ∀ i,(p i).IsChain (PortWalk.step Γ.origin Γ.reverse))
    (hclose : ∀ i,cyclic i=true → ∀ᵉ (x∈(p i).getLast?) (y∈(p i).head?),
      PortWalk.step Γ.origin Γ.reverse x y)

abbrev edge (i : I) : Fin (p i).length → D := (p i).get
abbrev mult : D → ℕ := multiplicity Γ (edge p)

end TorsionFreeZeroDivisors.ListStageExponents

/-! A choice of one direction for each unoriented edge of a finite port graph.
The reversal has no fixed points. No graph is assumed bipartite or loop-free. -/
namespace TorsionFreeZeroDivisors.InvolutionOrientation
open scoped Classical BigOperators
variable {D : Type*} [Fintype D] (σ : D → D)

variable (hσ : Function.Involutive σ) (hne : ∀d,σ d≠d)

include hσ hne

include hσ hne
@[simp] lemma equiv_false (c : Representative σ) : equiv σ hσ hne (c,false) = c.val := rfl
@[simp] lemma equiv_true (c : Representative σ) : equiv σ hσ hne (c,true) = σ c.val := rfl

end TorsionFreeZeroDivisors.InvolutionOrientation
namespace TorsionFreeZeroDivisors.ChainIsomorphism
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => InvolutionOrientation.Representative (PortGraph.reverse (suppressed Γ mark h2))
local notation "len" => chainLength Γ mark h2
abbrev repLength (c : R) := len c.val

def first (c : R) : Mark mark :=
  ⟨Γ.origin c.val.val,(turn_fixed_iff Γ.origin mark h2 _).mp c.val.property⟩
def last (c : R) : Mark mark :=
  ⟨Γ.origin ((S).reverse c.val).val,(turn_fixed_iff Γ.origin mark h2 _).mp ((S).reverse c.val).property⟩

local notation "P" => ChainSubdivision.graph (repLength Γ mark h2) (first Γ mark h2) (last Γ mark h2)

def dartMap (d : ChainSubdivision.Dart (repLength Γ mark h2)) : D :=
  if d.2 then Γ.reverse (F^[d.1.2.val] d.1.1.val.val) else F^[d.1.2.val] d.1.1.val.val

lemma forward_mem (c : R) (i : Fin (len c.val)) :
    F^[i.val] c.val.val ∈ ChainPaths.word Γ mark h2 c.val :=
  (ChainPaths.mem_word_iff Γ mark h2 _ _).mpr ⟨i,rfl⟩

lemma dart_mem (d : ChainSubdivision.Dart (repLength Γ mark h2)) :
    dartMap Γ mark h2 d ∈ ChainPaths.word Γ mark h2
      (InvolutionOrientation.orient (S).reverse (d.1.1,d.2)) := by
  cases hb : d.2
  · simpa only [dartMap,InvolutionOrientation.orient,hb,Bool.false_eq_true,ite_false] using
      forward_mem Γ mark h2 d.1.1 d.1.2
  · simpa only [dartMap,InvolutionOrientation.orient,hb,ite_true] using
      ChainPaths.reverse_mem_word Γ mark h2 _ _ (forward_mem Γ mark h2 d.1.1 d.1.2)

lemma same_word {a b : B} {x : D} (ha : x∈ChainPaths.word Γ mark h2 a)
    (hb : x∈ChainPaths.word Γ mark h2 b) : a=b := by
  by_contra h
  exact ChainPaths.words_disjoint Γ mark h2 h ha hb

lemma dartMap_injective : Injective (dartMap Γ mark h2) := by
  rintro ⟨⟨a,i⟩,u⟩ ⟨⟨b,j⟩,v⟩ he
  have hw := same_word Γ mark h2 (dart_mem Γ mark h2 ((⟨a,i⟩),u))
    (he.symm ▸ dart_mem Γ mark h2 ((⟨b,j⟩),v))
  have hab := InvolutionOrientation.orient_injective (S).reverse (S).reverse_reverse (S).reverse_ne hw
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj hab
  have hi : F^[i.val] a.val.val=F^[j.val] a.val.val := by
    cases u
    · exact he
    · exact Γ.reverse_reverse.injective he
  have hij := chain_dart_injective Γ.reverse τ Γ.reverse_reverse (turn_involutive Γ.origin mark h2)
    (a₁ := ⟨a.val,i⟩) (a₂ := ⟨a.val,j⟩) hi
  have hij' : i=j := Fin.ext (congrArg (fun z => z.2.val) hij)
  cases hij'
  rfl

lemma dartMap_surjective (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) : Surjective (dartMap Γ mark h2) := by
  intro x
  rcases hcovered x with ⟨b,i,hi⟩
  rcases InvolutionOrientation.chosen_or_reverse (S).reverse
    (S).reverse_reverse (S).reverse_ne b with hb|hb
  · exact ⟨(⟨⟨b,hb⟩,i⟩,false),hi⟩
  · have hx : x∈ChainPaths.word Γ mark h2 b :=
      (ChainPaths.mem_word_iff Γ mark h2 _ _).mpr ⟨i,hi⟩
    have hr := ChainPaths.reverse_mem_word Γ mark h2 b x hx
    rcases (ChainPaths.mem_word_iff Γ mark h2 _ _).mp hr with ⟨j,hj⟩
    refine ⟨(⟨⟨(S).reverse b,hb⟩,j⟩,true),?_⟩
    exact (congrArg Γ.reverse hj).trans (Γ.reverse_reverse x)

def dartEquiv (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) : ChainSubdivision.Dart (repLength Γ mark h2) ≃ D :=
  Equiv.ofBijective (dartMap Γ mark h2)
    ⟨dartMap_injective Γ mark h2,dartMap_surjective Γ mark h2 hcovered⟩

lemma dartMap_reverse (d : ChainSubdivision.Dart (repLength Γ mark h2)) :
    dartMap Γ mark h2 ((P).reverse d)=Γ.reverse (dartMap Γ mark h2 d) := by
  cases hb : d.2 <;> simp only [ChainSubdivision.reverse,dartMap,hb,Bool.not_false,Bool.not_true,
    Bool.false_eq_true,ite_false,ite_true]
  exact (Γ.reverse_reverse _).symm

def vertexMap : ChainSubdivision.Vertex (repLength Γ mark h2) (V := Mark mark) → V
  | .inl v => v.val
  | .inr ⟨c,i⟩ => Γ.origin (F^[i.val+1] c.val.val)

lemma internal_unmarked (v : ChainSubdivision.Interior (repLength Γ mark h2)) :
    ¬mark (vertexMap Γ mark h2 (.inr v)) := by
  intro hh
  have hf := (turn_fixed_iff Γ.origin mark h2 _).mpr hh
  have hi : v.2.val+1 < len v.1.val := by have h:=v.2.isLt; dsimp only [repLength] at h; omega
  exact no_internal_mark Γ.reverse τ Γ.reverse_reverse (turn_involutive Γ.origin mark h2)
    v.1.val.val v.1.val.property (by omega : 0<v.2.val+1) hi hf

lemma origin_map (d : ChainSubdivision.Dart (repLength Γ mark h2)) :
    vertexMap Γ mark h2 ((P).origin d) = Γ.origin (dartMap Γ mark h2 d) := by
  rcases d with ⟨⟨c,i⟩,b⟩
  cases b
  · rw [ChainSubdivision.origin_forward]
    by_cases hz : i.val=0
    · simp only [ChainSubdivision.point,Fin.val_mk,hz,dif_pos,vertexMap,first,dartMap,
        Bool.false_eq_true,ite_false]
      rfl
    · have hl : i.val≠repLength Γ mark h2 c := Nat.ne_of_lt i.isLt
      simp only [ChainSubdivision.point,hz,hl,vertexMap,dartMap,
        Bool.false_eq_true,ite_false]
      change Γ.origin (F^[i.val-1+1] c.val.val) = Γ.origin (F^[i.val] c.val.val)
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hz)]
  · rw [ChainSubdivision.origin_backward]
    have hz : i.val+1≠0 := by omega
    by_cases hl : i.val+1=repLength Γ mark h2 c
    · have hp : repLength Γ mark h2 c≠0 := Nat.ne_of_gt (chainLength_pos Γ mark h2 c.val)
      simp only [ChainSubdivision.point,Fin.val_mk,hl,hp,dif_pos,vertexMap,last,
        dartMap,ite_true]
      have hi : i.val=len c.val-1 := by change i.val+1=len c.val at hl; omega
      have he := chain_last Γ mark h2 c.val
      rw [last_iterChain] at he
      change Γ.origin ((S).reverse c.val).val = Γ.origin (Γ.reverse (F^[i.val] c.val.val))
      rw [hi,he]
    · simp only [ChainSubdivision.point,hz,hl,vertexMap,dartMap,ite_true]
      change Γ.origin (F^[i.val+1-1+1] c.val.val) = Γ.origin (Γ.reverse (F^[i.val] c.val.val))
      rw [Nat.add_sub_cancel,iterate_succ_apply']
      exact turn_origin Γ.origin mark h2 _

lemma original_two_ports (v : ChainSubdivision.Interior (repLength Γ mark h2))
    (d : D) (hd : Γ.origin d=vertexMap Γ mark h2 (.inr v)) :
    d=dartMap Γ mark h2 (ChainSubdivision.front (repLength Γ mark h2) v) ∨
    d=dartMap Γ mark h2 (ChainSubdivision.back (repLength Γ mark h2) v) := by
  let a := ChainSubdivision.front (repLength Γ mark h2) v
  let b := ChainSubdivision.back (repLength Γ mark h2) v
  have ha : Γ.origin (dartMap Γ mark h2 a)=vertexMap Γ mark h2 (.inr v) := by
    rw [←origin_map,ChainSubdivision.front_origin]
  have hb : Γ.origin (dartMap Γ mark h2 b)=vertexMap Γ mark h2 (.inr v) := by
    rw [←origin_map,ChainSubdivision.back_origin]
  by_cases hda : d=dartMap Γ mark h2 a
  · exact Or.inl hda
  · right
    have hba : dartMap Γ mark h2 b≠dartMap Γ mark h2 a := by
      intro hh
      exact ChainSubdivision.back_ne_front _ v (dartMap_injective Γ mark h2 hh)
    exact ((unique_other Γ.origin (dartMap Γ mark h2 a)
      (h2 _ (ha ▸ internal_unmarked Γ mark h2 v))).unique
        ⟨hd.trans ha.symm,hda⟩ ⟨hb.trans ha.symm,hba⟩)

lemma vertexMap_injective : Injective (vertexMap Γ mark h2) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext he)
    | inr b => exact (internal_unmarked Γ mark h2 b (he ▸ a.property)).elim
  | inr a =>
    cases b with
    | inl b => exact (internal_unmarked Γ mark h2 a (he.symm ▸ b.property)).elim
    | inr b =>
      have hb : Γ.origin (dartMap Γ mark h2 (ChainSubdivision.front (repLength Γ mark h2) b)) =
          vertexMap Γ mark h2 (.inr a) := by
        rw [←origin_map,ChainSubdivision.front_origin,he]
      rcases original_two_ports Γ mark h2 a _ hb with h|h
      · have hh := dartMap_injective Γ mark h2 h
        have h' := congrArg (fun d => (P).origin d) hh
        simpa only [ChainSubdivision.front_origin] using h'.symm
      · have hh := dartMap_injective Γ mark h2 h
        have h' := congrArg Prod.snd hh
        cases h'

lemma vertexMap_surjective (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) : Surjective (vertexMap Γ mark h2) := by
  intro v
  by_cases hv : mark v
  · exact ⟨.inl ⟨v,hv⟩,rfl⟩
  · have hp : (out Γ.origin v).Nonempty := Finset.card_pos.mp (by rw [h2 v hv]; decide)
    obtain ⟨d,hd⟩ := hp
    obtain ⟨a,ha⟩ := dartMap_surjective Γ mark h2 hcovered d
    refine ⟨(P).origin a,?_⟩
    rw [origin_map,ha]
    exact (mem_out Γ.origin v d).mp hd

def vertexEquiv (hcovered : ∀ d : D, ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) : ChainSubdivision.Vertex (repLength Γ mark h2) (V := Mark mark) ≃ V :=
  Equiv.ofBijective (vertexMap Γ mark h2)
    ⟨vertexMap_injective Γ mark h2,vertexMap_surjective Γ mark h2 hcovered⟩

variable [Fintype V]

end TorsionFreeZeroDivisors.ChainIsomorphism

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.AffineIntervals
open scoped Classical
open BlockAlignment

end TorsionFreeZeroDivisors.AffineIntervals
namespace TorsionFreeZeroDivisors.ChunkComparisons
open scoped Classical
open BlockAlignment ComparedBlocks AffineIntervals EntropyStages

variable {P T E : Type*} {lp : P → ℕ} {lt : T → ℕ}

namespace Chunking
variable (C : Comparisons (E := E) lp)

variable (lo hi : E → ℤ)

variable (hlo : ∀ e, C.lo e=(lo e : ℝ)) (hhi : ∀ e, C.hi e=(hi e : ℝ))

end Chunking
end TorsionFreeZeroDivisors.ChunkComparisons

namespace TorsionFreeZeroDivisors.FiniteChunking
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks AffineIntervals ChunkComparisons

variable {n : ℕ}

variable {P : Type*} [Fintype P] (chunks : P → ℕ)
  (len : (p : P) → Fin (chunks p) → ℕ) (rev : (p : P) → Fin (chunks p) → Bool)

end TorsionFreeZeroDivisors.FiniteChunking

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChunkComparisons
open scoped Classical
open ComparedBlocks
variable {P T U C : Type*} {lp : P → ℕ} {lt : T → ℕ}

namespace Chunking
end Chunking

variable [Fintype T] (color : T → C)

end TorsionFreeZeroDivisors.ChunkComparisons

namespace TorsionFreeZeroDivisors.ListChunkCoordinates
open scoped Classical BigOperators
open FiniteChunking
variable {A D : Type*} (ds : List A) (word : A → List D)

end TorsionFreeZeroDivisors.ListChunkCoordinates

namespace TorsionFreeZeroDivisors.ChainChunkTransport
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChunkComparisons FiniteChunking ComparedBlocks
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "len" => chainLength Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "w" => word Γ mark h2
def reversed (b : B) : Bool := ((orientation Γ mark h2).symm b).2

lemma oriented (b : B) : b=if reversed Γ mark h2 b then (S).reverse (representative Γ mark h2 b).val
    else (representative Γ mark h2 b).val := (orientation Γ mark h2).apply_symm_apply b |>.symm

variable {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})

variable {E : Type*}
    (cmp : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (lo hi : E → ℤ) (hlo : ∀ e,cmp.lo e=(lo e:ℝ)) (hhi : ∀ e,cmp.hi e=(hi e:ℝ))

end TorsionFreeZeroDivisors.ChainChunkTransport

namespace TorsionFreeZeroDivisors.ChainMultiplicity
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2

lemma representative_val (c : R) : representative Γ mark h2 c.val=c := by
  change ((orientation Γ mark h2).symm ((orientation Γ mark h2) (c,false))).1=c
  rw [Equiv.symm_apply_apply]

lemma reverse_oriented (b : B) :
    (S).reverse b=(orientation Γ mark h2) (representative Γ mark h2 b,!(reversed Γ mark h2 b)) := by
  have h := oriented Γ mark h2 b
  cases hr : reversed Γ mark h2 b
  · simp only [hr,Bool.false_eq_true,ite_false] at h
    change (S).reverse b=(S).reverse (representative Γ mark h2 b).val
    exact congrArg (S).reverse h
  · simp only [hr,ite_true] at h
    change (S).reverse b=(representative Γ mark h2 b).val
    calc
      _ = (S).reverse ((S).reverse (representative Γ mark h2 b).val) := congrArg (S).reverse h
      _ = _ := (S).reverse_reverse _

lemma representative_reverse (b : B) : representative Γ mark h2 ((S).reverse b)=representative Γ mark h2 b := by
  rw [reverse_oriented]
  change ((orientation Γ mark h2).symm ((orientation Γ mark h2) _)).1=_
  rw [Equiv.symm_apply_apply]

lemma unsigned (b : B) :
    (if reversed Γ mark h2 b then (S).reverse b else b)=(representative Γ mark h2 b).val := by
  have h := oriented Γ mark h2 b
  cases hr : reversed Γ mark h2 b
  · simpa only [hr,Bool.false_eq_true,ite_false] using h
  · simp only [hr,ite_true] at h ⊢
    calc
      _ = (S).reverse ((S).reverse (representative Γ mark h2 b).val) := congrArg (S).reverse h
      _ = _ := (S).reverse_reverse _

lemma signed_representative (b : B) (r : Bool) :
    representative Γ mark h2 (if r then (S).reverse b else b)=representative Γ mark h2 b := by
  cases r <;> simp only [Bool.false_eq_true,ite_false,ite_true,representative_reverse]

lemma sign_injective (b : B) : Function.Injective (fun r : Bool => if r then (S).reverse b else b) := by
  intro r t h
  cases r <;> cases t <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h ⊢
  · exact ((S).reverse_ne b h.symm).elim
  · exact ((S).reverse_ne b h).elim

variable {P : Type*} [Fintype P]
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d})

local notation "col" => color Γ mark h2 paths
local notation "tp" => Traversal (chunks Γ mark h2 paths)
local notation "e" => ListStageExponents.edge paths

/-- The incidence fibre used in the Euler-exponent proof is the exact colour
fibre used in the chain/block first moment. Both chain orientations count once. -/
def incidenceEquiv (c : R) :
    {o : (p : P) × (Fin (paths p).length × Bool) // PathIncidences.familyPort (S).reverse e o=c.val} ≃
      {t : tp // col t=c} where
  toFun o := ⟨⟨o.val.1,o.val.2.1⟩,by
    have h := congrArg (representative Γ mark h2) o.property
    change representative Γ mark h2 (if o.val.2.2 then (S).reverse ((paths o.val.1).get o.val.2.1)
      else (paths o.val.1).get o.val.2.1)=representative Γ mark h2 c.val at h
    rw [signed_representative,representative_val] at h
    exact h⟩
  invFun t := ⟨⟨t.val.1,t.val.2,reversed Γ mark h2 ((paths t.val.1).get t.val.2)⟩,by
    change (if reversed Γ mark h2 ((paths t.val.1).get t.val.2) then
      (S).reverse ((paths t.val.1).get t.val.2) else (paths t.val.1).get t.val.2)=c.val
    rw [unsigned]
    exact congrArg Subtype.val t.property⟩
  left_inv := by
    rintro ⟨⟨p,i,r⟩,ho⟩
    apply Subtype.ext
    change (⟨p,i,reversed Γ mark h2 ((paths p).get i)⟩ : (p : P) × (Fin (paths p).length × Bool))=⟨p,i,r⟩
    have hr : reversed Γ mark h2 ((paths p).get i)=r := by
      apply sign_injective Γ mark h2 ((paths p).get i)
      dsimp only
      rw [unsigned]
      have h := congrArg (representative Γ mark h2) ho
      change representative Γ mark h2 (if r then (S).reverse ((paths p).get i)
        else (paths p).get i)=representative Γ mark h2 c.val at h
      rw [signed_representative,representative_val] at h
      rw [h]
      exact ho.symm
    rw [hr]
  right_inv _ := rfl

lemma multiplicity_eq (c : R) :
    StageSubgraphs.multiplicity (S) e c.val=ChunkComparisons.multiplicity col c := by
  classical
  unfold StageSubgraphs.multiplicity IncidenceStages.Passages.multiplicity ChunkComparisons.multiplicity
  simp only [Fintype.card_eq_nat_card]
  exact Nat.card_congr (incidenceEquiv Γ mark h2 paths c)

end TorsionFreeZeroDivisors.ChainMultiplicity

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainActiveStages
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open StageSubgraphs
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "col" => color Γ mark h2 paths
local notation "e" => ListStageExponents.edge paths
local notation "m" => StageSubgraphs.multiplicity (S) e
abbrev ActiveChain (j : ℕ) := {c : R // j < ChunkComparisons.multiplicity col c}
local notation "A" => ActiveChain Γ mark h2 paths

variable [Fintype V]

def first (j : ℕ) (c : A j) : ActiveV (S) m j :=
  ⟨ChainIsomorphism.first Γ mark h2 c.val,c.val.val,rfl,by
    rw [multiplicity_eq Γ mark h2 paths]; exact c.property⟩

def last (j : ℕ) (c : A j) : ActiveV (S) m j :=
  ⟨ChainIsomorphism.last Γ mark h2 c.val,(S).reverse c.val.val,rfl,by
    rw [multiplicity_reverse,multiplicity_eq Γ mark h2 paths]; exact c.property⟩

end TorsionFreeZeroDivisors.ChainActiveStages

namespace TorsionFreeZeroDivisors.SubdivisionRestriction
open scoped Classical
open ChainSubdivision
variable {C V : Type*} (len : C → ℕ) (first last : C → V)
    (active : C → Prop) (incident : V → Prop)
    (hf : ∀ c,active c → incident (first c))
    (hl : ∀ c,active c → incident (last c))

abbrev length : {c // active c} → ℕ := fun c => len c.val
def firstPoint (c : {c // active c}) : {v // incident v} := ⟨first c.val,hf _ c.property⟩
def lastPoint (c : {c // active c}) : {v // incident v} := ⟨last c.val,hl _ c.property⟩

local notation "P" => graph len first last
local notation "Q" => graph (length len active) (firstPoint first active incident hf) (lastPoint last active incident hl)

end TorsionFreeZeroDivisors.SubdivisionRestriction

namespace TorsionFreeZeroDivisors.ChainStageEmbedding
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open StageSubgraphs
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "col" => color Γ mark h2 paths
local notation "e" => ListStageExponents.edge paths
local notation "m" => StageSubgraphs.multiplicity (S) e
local notation "A" => ChainActiveStages.ActiveChain Γ mark h2 paths j
local notation "W" => ActiveV (S) m j

abbrev length : A → ℕ := fun c => repLength Γ mark h2 c.val
abbrev graph := ChainSubdivision.graph (length Γ mark h2 paths j)
  (ChainActiveStages.first Γ mark h2 paths j) (ChainActiveStages.last Γ mark h2 paths j)
local notation "Q" => graph Γ mark h2 paths j

end TorsionFreeZeroDivisors.ChainStageEmbedding

namespace TorsionFreeZeroDivisors.RootPins
open scoped Classical BigOperators
variable {V T : Type*} [Fintype V]

end TorsionFreeZeroDivisors.RootPins

namespace TorsionFreeZeroDivisors.ActiveRoot
open scoped Classical
open PortSubdivision StageSubgraphs
variable {V D P : Type*} [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (paths : P → List D) (hp : ∀ p,paths p≠[])

omit [Fintype D] in
lemma occurrence_positive (p : P) (i : Fin (paths p).length) :
    0<ListStageExponents.mult Γ paths ((paths p).get i) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨p,i,false⟩,rfl⟩⟩

/-- The actual initial vertex belongs to the first active stage. -/
def vertex (p : P) : ActiveV Γ (ListStageExponents.mult Γ paths) 0 :=
  let i : Fin (paths p).length := ⟨0,List.length_pos_iff.mpr (hp p)⟩
  ⟨Γ.origin ((paths p).get i),(paths p).get i,rfl,occurrence_positive Γ paths p i⟩

omit [Fintype D] in
@[simp] lemma vertex_val (p : P) :
    (vertex Γ paths hp p).val=Γ.origin ((paths p).head (hp p)) := by
  simp [vertex,List.head_eq_getElem]

end TorsionFreeZeroDivisors.ActiveRoot

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.RealizationTransport
open scoped Classical
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {PV PD TV T QV QD : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]
    [Fintype QV] [Fintype QD]
variable {Γ : PortGraph PV PD} {plabel : PD → T} {outgoing : TV → Finset T}
    {pin : PV → Option TV} {bar : T → T} {r : Matching (label outgoing) bar}
    (e : Embedding Γ plabel outgoing pin bar r)

end TorsionFreeZeroDivisors.RealizationTransport

namespace TorsionFreeZeroDivisors.ActualStageRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open StageSubgraphs
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "S" => suppressed Γ mark h2
local notation "len" => ChainStageEmbedding.length Γ mark h2 paths j
local notation "Q" => ChainStageEmbedding.graph Γ mark h2 paths j
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)

variable [Fintype V] {TV : Type} [Fintype TV]
    {outgoing : TV → Finset Types.Letter} {pin : V → Option TV}
    {r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) Types.inverse}

end TorsionFreeZeroDivisors.ActualStageRealization

namespace TorsionFreeZeroDivisors.ActualStageFeasibility
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate

variable {C : Type*} [Fintype C] (s : ℝ) (len : C → ℕ)

variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "lenR" => repLength Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (ChainChunkTransport.color Γ mark h2 paths)

variable {E : Type*}
    (cmp : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (lo hi : E → ℤ) (hlo : ∀ e,cmp.lo e=(lo e:ℝ)) (hhi : ∀ e,cmp.hi e=(hi e:ℝ))

end TorsionFreeZeroDivisors.ActualStageFeasibility

namespace TorsionFreeZeroDivisors.StagePartition
open scoped Classical BigOperators
open RepeatedBlocks BlockAlignment ComparedBlocks ChainStageLabels WordEstimate
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)

abbrev CA := {a : C // j < m a ∧ side a=true}
abbrev CB := {b : C // j < m b ∧ side b=false}
abbrev lenA : CA m side j → ℕ := fun a => len a.val
abbrev lenB : CB m side j → ℕ := fun b => len b.val

variable (firstA lastA : CA m side j → VA) (firstB lastB : CB m side j → VB)
  (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter)
  (pinA : VA → Option TA) (pinB : VB → Option TB)

def sideA : TwoSideStage.Side where
  C := CA m side j; V := VA; TV := TA
  fC := inferInstance; fV := inferInstance; fTV := inferInstance
  len := lenA len m side j
  first := firstA; last := lastA; outgoing := outA; pin := pinA

def sideB : TwoSideStage.Side where
  C := CB m side j; V := VB; TV := TB
  fC := inferInstance; fV := inferInstance; fTV := inferInstance
  len := lenB len m side j
  first := firstB; last := lastB; outgoing := outB; pin := pinB

local notation "SA" => sideA len m side j firstA lastA outA pinA
local notation "SB" => sideB len m side j firstB lastB outB pinB

end TorsionFreeZeroDivisors.StagePartition

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PartitionEntropy
open scoped Classical BigOperators
open StageEntropy BlockAlignment ComparedBlocks RepeatedBlocks ChainStageLabels WordEstimate StagePartition
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)
variable (firstA lastA : CA m side j → VA) (firstB lastB : CB m side j → VB)
  (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter)
  (pinA : VA → Option TA) (pinB : VB → Option TB)
local notation "SA" => sideA len m side j firstA lastA outA pinA
local notation "SB" => sideB len m side j firstB lastB outB pinB

end TorsionFreeZeroDivisors.PartitionEntropy

namespace TorsionFreeZeroDivisors.SideRestriction
open scoped Classical
open PortSubdivision
variable {V D : Type*} (Γ : PortGraph V D) (side : V → Bool)
    (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d)) (b : Bool)

variable {QV QD : Type*} (Q : PortGraph QV QD) (fv : QV ↪ V) (fd : QD ↪ D)
    (ho : ∀ d,fv (Q.origin d)=Γ.origin (fd d))
    (hr : ∀ d,fd (Q.reverse d)=Γ.reverse (fd d))
    (hf : ∀ v,side (fv v)=b)

variable [Fintype V] [Fintype D] [Fintype QV] [Fintype QD]
    {TV T : Type*} [Fintype TV] [Fintype T]
    (label : D → T) (outgoing : TV → Finset T) (pin : Vertex side b → Option TV)
    (bar : T → T) (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) bar)

end TorsionFreeZeroDivisors.SideRestriction

namespace TorsionFreeZeroDivisors.StageSideEmbedding
open scoped Classical BigOperators
open ChainSubdivision
variable {C V : Type*} (len m : C → ℕ) (j : ℕ) (side : C → Bool) (vside : V → Bool)
    (first last : {c // j < m c} → V)
    (hf : ∀ c,vside (first c)=side c.val) (hl : ∀ c,vside (last c)=side c.val) (b : Bool)

abbrev Chain := {c : C // j < m c ∧ side c=b}
abbrev Vertex := {v : V // vside v=b}
abbrev length : Chain m j side b → ℕ := fun c => len c.val

def firstPoint (c : Chain m j side b) : Vertex vside b :=
  ⟨first ⟨c.val,c.property.1⟩,(hf _).trans c.property.2⟩
def lastPoint (c : Chain m j side b) : Vertex vside b :=
  ⟨last ⟨c.val,c.property.1⟩,(hl _).trans c.property.2⟩
abbrev graph := ChainSubdivision.graph (length len m j side b)
  (firstPoint m j side vside first hf b) (lastPoint m j side vside last hl b)
local notation "Q" => graph len m j side vside first last hf hl b
local notation "P" => ChainSubdivision.graph (StageExpectation.activeLen len m j) first last

variable [Fintype C] [Fintype V]

end TorsionFreeZeroDivisors.StageSideEmbedding

namespace TorsionFreeZeroDivisors.ChainSide
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2

def chain (c : R) : Bool := side (Γ.origin c.val.val)

include hs in
lemma next_side (d : D) : side (Γ.origin (F d))=side (Γ.origin d) := by
  change side (Γ.origin (turn Γ.origin mark h2 (Γ.reverse d)))=side (Γ.origin d)
  rw [turn_origin Γ.origin mark h2]
  exact hs d

include hs in
lemma iterate_side (d : D) (i : ℕ) : side (Γ.origin (F^[i] d))=side (Γ.origin d) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [iterate_succ_apply',next_side Γ mark h2 side hs,ih]

include hs in
lemma suppressed_side (d : {d : D // turn Γ.origin mark h2 d=d}) :
    side ((S).origin ((S).reverse d))=side ((S).origin d) := by
  change side (Γ.origin ((S).reverse d).val)=side (Γ.origin d.val)
  have he := chain_last Γ mark h2 d
  rw [last_iterChain] at he
  rw [←he,hs]
  exact iterate_side Γ mark h2 side hs d.val _

include hs in
lemma last_side (c : R) : side (ChainIsomorphism.last Γ mark h2 c).val=chain Γ mark h2 side c :=
  suppressed_side Γ mark h2 side hs c.val

variable {P : Type*} [Fintype P]
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "W" => StageSubgraphs.ActiveV (S) (ListStageExponents.mult (S) paths) j
local notation "A" => ChainActiveStages.ActiveChain Γ mark h2 paths j

def vertex (w : W) : Bool := side w.val

lemma active_first (c : A) : vertex Γ mark h2 side paths j (ChainActiveStages.first Γ mark h2 paths j c)=
    chain Γ mark h2 side c.val := rfl
include hs in
lemma active_last (c : A) : vertex Γ mark h2 side paths j (ChainActiveStages.last Γ mark h2 paths j c)=
    chain Γ mark h2 side c.val := last_side Γ mark h2 side hs c.val

end TorsionFreeZeroDivisors.ChainSide

namespace TorsionFreeZeroDivisors.ActualSideRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons StageSubgraphs
variable {V D : Type} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    {P : Type} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ) (b : Bool)
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "cs" => ChainSide.chain Γ mark h2 side
local notation "vs" => ChainSide.vertex Γ mark h2 side paths j
local notation "first" => ChainActiveStages.first Γ mark h2 paths j
local notation "last" => ChainActiveStages.last Γ mark h2 paths j
local notation "hf" => ChainSide.active_first Γ mark h2 side paths j
local notation "hl" => ChainSide.active_last Γ mark h2 side hs paths j
local notation "W" => ActiveV (S) (ListStageExponents.mult (S) paths) j

abbrev length := StageSideEmbedding.length len m j cs b
abbrev graph := StageSideEmbedding.graph len m j cs vs first last hf hl b
local notation "Q" => graph Γ mark h2 side hs paths j b
local notation "l" => length Γ mark h2 side paths j b

variable [Fintype V] {TV : Type} [Fintype TV]
    (label : D → Types.Letter) (outgoing : TV → Finset Types.Letter)
    (pin : SideRestriction.Vertex side b → Option TV)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) Types.inverse)

end TorsionFreeZeroDivisors.ActualSideRealization

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SidePins
open scoped Classical BigOperators
variable {V TA TB : Type*} [Fintype V] (side : V → Bool)

end TorsionFreeZeroDivisors.SidePins

namespace TorsionFreeZeroDivisors.StageRoot
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking StageSubgraphs
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
local notation "S" => suppressed Γ mark h2
local notation "mult" => ListStageExponents.mult (S) paths
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)

/-- Only the first stage fixes the marked initial vertex. -/
def vertex (root : Option P) (j : ℕ) : Option (ActiveV (S) mult j) :=
  if h : j=0 then by
    subst j
    exact root.map (ActiveRoot.vertex (S) paths hp)
  else none

end TorsionFreeZeroDivisors.StageRoot

namespace TorsionFreeZeroDivisors.RootPins
open scoped Classical
variable {V T : Type*}
end TorsionFreeZeroDivisors.RootPins

namespace TorsionFreeZeroDivisors.SidePins
open scoped Classical
variable {V : Type*} (side : V → Bool)
end TorsionFreeZeroDivisors.SidePins

namespace TorsionFreeZeroDivisors.StageRoot
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking StageSubgraphs
variable {V D P : Type} [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
local notation "S" => suppressed Γ mark h2
local notation "mult" => ListStageExponents.mult (S) paths

variable (side : V → Bool)

end TorsionFreeZeroDivisors.StageRoot

namespace TorsionFreeZeroDivisors.ActualStagePair
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs StageSideEmbedding
open ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "cs" => ChainSide.chain Γ mark h2 side
local notation "vs" => ChainSide.vertex Γ mark h2 side paths
local notation "first" => ChainActiveStages.first Γ mark h2 paths
local notation "last" => ChainActiveStages.last Γ mark h2 paths
local notation "hf" => ChainSide.active_first Γ mark h2 side paths
local notation "hl" => ChainSide.active_last Γ mark h2 side hsid paths

abbrev pinA (j : ℕ) := RootPins.pin (SidePins.root (vs j) (StageRoot.vertex Γ mark h2 paths hp root j) true) a
abbrev pinB (j : ℕ) := RootPins.pin (SidePins.root (vs j) (StageRoot.vertex Γ mark h2 paths hp root j) false) b

abbrev A (j : ℕ) : TwoSideStage.Side :=
  StagePartition.sideA len m cs j
    (firstPoint m j cs (vs j) (first j) (hf j) true)
    (lastPoint m j cs (vs j) (last j) (hl j) true)
    (@Types.outgoingA rep) (pinA Γ mark h2 side paths hp root rep a j)

abbrev B (j : ℕ) : TwoSideStage.Side :=
  StagePartition.sideB len m cs j
    (firstPoint m j cs (vs j) (first j) (hf j) false)
    (lastPoint m j cs (vs j) (last j) (hl j) false)
    (@Types.outgoingB rep) (pinB Γ mark h2 side paths hp root rep b j)
local notation "SA" => A Γ mark h2 side hsid paths hp root rep a
local notation "SB" => B Γ mark h2 side hsid paths hp root rep b

variable {E : Type}

end TorsionFreeZeroDivisors.ActualStagePair

namespace TorsionFreeZeroDivisors.ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs StageSideEmbedding
open ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _

variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "vs" => ChainSide.vertex Γ mark h2 side paths
local notation "SA" => ActualStagePair.A Γ mark h2 side hsid paths hp root rep a
local notation "SB" => ActualStagePair.B Γ mark h2 side hsid paths hp root rep b

variable [Fintype E]

end TorsionFreeZeroDivisors.ActualPatternEvent

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternUniform
open scoped Classical Topology BigOperators
open Filter GridAsymptotics GirthAsymptotics TypedGraphs

variable {C E : Type*} [Fintype C] [Fintype E]

end TorsionFreeZeroDivisors.PatternUniform

namespace TorsionFreeZeroDivisors.ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs StageSideEmbedding
open ComparedBlocks RepeatedBlocks GridAsymptotics GirthAsymptotics TypedGraphs
variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2

variable [Fintype E]

end TorsionFreeZeroDivisors.ActualPatternEvent

namespace TorsionFreeZeroDivisors.OriginalPattern
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs StageSideEmbedding
open ComparedBlocks RepeatedBlocks GridAsymptotics GirthAsymptotics TypedGraphs ActualPatternEvent
variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "pl" => pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)

variable [Fintype E]

end TorsionFreeZeroDivisors.OriginalPattern

namespace TorsionFreeZeroDivisors.ComparisonGeometry
open scoped Classical
open BlockAlignment ComparedBlocks ChunkComparisons
variable {P P' E E' : Type*} {len : P → ℕ} {len' : P' → ℕ}

namespace Iso
variable {C : Comparisons (E:=E) len} {C' : Comparisons (E:=E') len'}

end Iso
end TorsionFreeZeroDivisors.ComparisonGeometry

namespace TorsionFreeZeroDivisors.PortSubdivision
structure Iso {V D V' D' : Type*} (Γ : PortGraph V D) (Γ' : PortGraph V' D') where
  vertex : V ≃ V'
  dart : D ≃ D'
  origin_eq : ∀ d,vertex (Γ.origin d)=Γ'.origin (dart d)
  reverse_eq : ∀ d,dart (Γ.reverse d)=Γ'.reverse (dart d)

namespace Iso
variable {V D V' D' V'' D'' : Type*} {Γ : PortGraph V D} {Γ' : PortGraph V' D'} {Γ'' : PortGraph V'' D''}
def symm (f : Iso Γ Γ') : Iso Γ' Γ where
  vertex := f.vertex.symm
  dart := f.dart.symm
  origin_eq d := by
    apply f.vertex.injective
    simp only [Equiv.apply_symm_apply,f.origin_eq]
  reverse_eq d := by
    apply f.dart.injective
    simp only [Equiv.apply_symm_apply,f.reverse_eq]

def trans (f : Iso Γ Γ') (g : Iso Γ' Γ'') : Iso Γ Γ'' where
  vertex := f.vertex.trans g.vertex
  dart := f.dart.trans g.dart
  origin_eq d := by simp only [Equiv.trans_apply,f.origin_eq,g.origin_eq]
  reverse_eq d := by simp only [Equiv.trans_apply,f.reverse_eq,g.reverse_eq]
end Iso
end TorsionFreeZeroDivisors.PortSubdivision

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PortSubdivision.Iso
open scoped Classical
variable {V D V' D' T TV : Type*} [Fintype V] [Fintype D] [Fintype V'] [Fintype D']
    [Fintype T] [Fintype TV] {Γ : PortGraph V D} {Γ' : PortGraph V' D'}
    (f : Iso Γ Γ') (side : V → Bool) (side' : V' → Bool)
    (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (hs' : ∀ d,side' (Γ'.origin (Γ'.reverse d))=side' (Γ'.origin d))
    (hside : ∀ v,side v=side' (f.vertex v)) (b : Bool)
    (root : Option V) (root' : Option V') (hroot : root.map f.vertex=root')
    (label : D' → T) (outgoing : TV → Finset T) (target : TV) (bar : T → T)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) bar)

end TorsionFreeZeroDivisors.PortSubdivision.Iso

namespace TorsionFreeZeroDivisors.OriginalPatternIso
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks ActualPatternEvent
variable {V D P E V' D' P' E' : Type} [Fintype V] [Fintype D] [Fintype P]
    [Fintype V'] [Fintype D'] [Fintype P']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (paths' : P' → List {x : D' // turn Γ'.origin mark' h2' x=x}) (hp' : ∀ p,paths' p≠[])
local notation "pl" => pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)
local notation "pl'" => pathLength (chunks Γ' mark' h2' paths') (chunkLength Γ' mark' h2' paths')
variable (f : Iso Γ Γ') (eP : P ≃ P')
    (hwords : ∀ p,((paths p).flatMap (word Γ mark h2)).map f.dart =
      (paths' (eP p)).flatMap (word Γ' mark' h2'))

variable (side : V → Bool) (side' : V' → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d)) (hs' : ∀ d,side' (Γ'.origin (Γ'.reverse d))=side' (Γ'.origin d)) (hside : ∀ v,side v=side' (f.vertex v)) (root : Option P) (root' : Option P') (hroot : (StageRoot.source Γ mark h2 paths hp root).map f.vertex=
      StageRoot.source Γ' mark' h2' paths' hp' root') (C : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths))) (C' : Comparisons (E:=E') (pathLength (chunks Γ' mark' h2' paths') (chunkLength Γ' mark' h2' paths'))) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)

end TorsionFreeZeroDivisors.OriginalPatternIso

/-!
Finite names for the actual-image patterns in entropy.tex 126–138.  The bounds
R,K,T,I are fixed before H grows.  No vertex names or letters are stored.  Raw
codes include invalid multigraphs as an overcount; all validity conditions must
still be checked when a code is used in a realization event.
-/
namespace TorsionFreeZeroDivisors.PatternCoding

section
open scoped BigOperators Classical

/-- Thus all the actual comparison endpoints with a ≤H bound fit literally. -/
def endName (H : ℕ) (i : ℕ) (hi : i ≤ H) : Fin (H+1) := ⟨i,by omega⟩

@[simp] lemma endName_val (H i : ℕ) (hi : i ≤ H) : (endName H i hi).val = i := rfl

end

open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]

variable {D V P J D' V' P' J' : Type*}
  [Fintype D] [Fintype V] [Fintype P] [Fintype J]
  [Fintype D'] [Fintype V'] [Fintype P'] [Fintype J']

variable (R K T I H : ℕ) (hR : 0<R)
  (hD : Fintype.card D ≤ R) (hV : Fintype.card V ≤ R)
  (hP : Fintype.card P ≤ K) (hJ : Fintype.card J ≤ I)

variable (hD' : Fintype.card D' ≤ R) (hV' : Fintype.card V' ≤ R)
  (hP' : Fintype.card P' ≤ K) (hJ' : Fintype.card J' ≤ I)

end TorsionFreeZeroDivisors.PatternCoding

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ComparisonCoding
open scoped Classical
open PatternCoding

variable {P E P' E' : Type*} [Fintype P] [Fintype E] [Fintype P'] [Fintype E']
    (K I H : ℕ) (hK : 0<K) (hI : 0<I)
    (hP : Fintype.card P≤K) (hE : Fintype.card E≤I)

variable (hP' : Fintype.card P'≤K) (hE' : Fintype.card E'≤I)

end TorsionFreeZeroDivisors.ComparisonCoding

namespace TorsionFreeZeroDivisors.SubdivisionIso
open scoped Classical
open ChainSubdivision PortSubdivision
variable {C V C' V' : Type*} (len : C → ℕ) (len' : C' → ℕ)
    (first last : C → V) (first' last' : C' → V')
    (eC : C ≃ C') (eV : V ≃ V') (hl : ∀ c,len c=len' (eC c))

def edge : Edge len ≃ Edge len' := Equiv.sigmaCongr eC (fun c => finCongr (hl c))
def interior : Interior len ≃ Interior len' := Equiv.sigmaCongr eC (fun c => finCongr (congrArg (fun n => n-1) (hl c)))
def vertex : Vertex len (V:=V) ≃ Vertex len' (V:=V') := Equiv.sumCongr eV (interior len len' eC hl)
def dart : Dart len ≃ Dart len' := Equiv.prodCongr (edge len len' eC hl) (Equiv.refl Bool)

variable (hf : ∀ c,eV (first c)=first' (eC c)) (ht : ∀ c,eV (last c)=last' (eC c))

include hf ht in
lemma point_eq (c : C) (k : Fin (len c+1)) :
    vertex len len' eC eV hl (point len first last c k)=
      point len' first' last' (eC c) ⟨k.val,by rw [←hl c]; exact k.isLt⟩ := by
  by_cases hz : k.val=0
  · simp [point,hz,vertex,hf]
  · by_cases ht' : k.val=len c
    · have hn : k.val=len' (eC c) := ht'.trans (hl c)
      simp only [point,dif_neg hz,dif_pos ht',dif_pos hn]
      exact congrArg Sum.inl (ht c)
    · have hn : k.val≠len' (eC c) := by rwa [←hl c]
      simp only [point,dif_neg hz,dif_neg ht',dif_neg hn]
      rfl

include hf ht in
lemma origin_eq (d : Dart len) :
    vertex len len' eC eV hl ((graph len first last).origin d)=
      (graph len' first' last').origin (dart len len' eC hl d) := by
  exact point_eq len len' first last first' last' eC eV hl hf ht d.1.1 _

omit eV in
lemma reverse_eq (d : Dart len) :
    dart len len' eC hl ((graph len first last).reverse d)=
      (graph len' first' last').reverse (dart len len' eC hl d) := rfl

end TorsionFreeZeroDivisors.SubdivisionIso

namespace TorsionFreeZeroDivisors.RankedSuppressionIso

section
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D V' D' : Type*} [Fintype D] [Fintype D']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
def skeleton : PortGraph (Mark mark) {d : D // turn Γ.origin mark h2 d=d} where
  origin d := ⟨Γ.origin d.val,(turn_fixed_iff Γ.origin mark h2 _).mp d.property⟩
  reverse := (suppressed Γ mark h2).reverse
  reverse_reverse := (suppressed Γ mark h2).reverse_reverse
  reverse_ne := (suppressed Γ mark h2).reverse_ne

local notation "S" => skeleton Γ mark h2
local notation "S'" => skeleton Γ' mark' h2'
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "B'" => {d : D' // turn Γ'.origin mark' h2' d=d}
local notation "R" => Rep Γ mark h2
local notation "R'" => Rep Γ' mark' h2'

lemma chosen_iff (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val) (d : B) : InvolutionOrientation.Chosen (S).reverse d ↔
    InvolutionOrientation.Chosen (S').reverse (f.dart d) := by
  unfold InvolutionOrientation.Chosen InvolutionOrientation.rank
  change (Fintype.equivFin B d).val < (Fintype.equivFin B ((S).reverse d)).val ↔
    (Fintype.equivFin B' (f.dart d)).val < (Fintype.equivFin B' ((S').reverse (f.dart d))).val
  rw [←f.reverse_eq,hrank,hrank]

def rep (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val) : R ≃ R' :=
  f.dart.subtypeEquiv (chosen_iff Γ mark h2 Γ' mark' h2' f hrank)

lemma rep_length (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,chainLength Γ mark h2 d=chainLength Γ' mark' h2' (f.dart d)) (c : R) : repLength Γ mark h2 c=
    repLength Γ' mark' h2' (rep Γ mark h2 Γ' mark' h2' f hrank c) := hlen c.val

lemma first_eq (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val) (c : R) : f.vertex (first Γ mark h2 c)=
    first Γ' mark' h2' (rep Γ mark h2 Γ' mark' h2' f hrank c) := f.origin_eq c.val

lemma last_eq (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val) (c : R) : f.vertex (last Γ mark h2 c)=
    last Γ' mark' h2' (rep Γ mark h2 Γ' mark' h2' f hrank c) := by
  change f.vertex ((S).origin ((S).reverse c.val))=(S').origin ((S').reverse (f.dart c.val))
  rw [f.origin_eq,f.reverse_eq]

/-- Exact canonical-rank suppression isomorphisms lift to actual subdivisions. -/
def subdivided (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,chainLength Γ mark h2 d=chainLength Γ' mark' h2' (f.dart d)) :
    Iso (ChainSubdivision.graph (repLength Γ mark h2) (first Γ mark h2) (last Γ mark h2))
      (ChainSubdivision.graph (repLength Γ' mark' h2') (first Γ' mark' h2') (last Γ' mark' h2')) where
  vertex := SubdivisionIso.vertex _ _ (rep Γ mark h2 Γ' mark' h2' f hrank) f.vertex
    (rep_length Γ mark h2 Γ' mark' h2' f hrank hlen)
  dart := SubdivisionIso.dart _ _ (rep Γ mark h2 Γ' mark' h2' f hrank)
    (rep_length Γ mark h2 Γ' mark' h2' f hrank hlen)
  origin_eq := SubdivisionIso.origin_eq _ _ _ _ _ _ _ _ _
    (first_eq Γ mark h2 Γ' mark' h2' f hrank) (last_eq Γ mark h2 Γ' mark' h2' f hrank)
  reverse_eq := SubdivisionIso.reverse_eq _ _ _ _ _ _ _ _

variable (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
    Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d)
  (hcovered' : ∀ d,ChainCoverage.Covered Γ'.reverse (turn Γ'.origin mark' h2')
    Γ'.reverse_reverse (turn_involutive Γ'.origin mark' h2') d)

def actual (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
    Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d) :
    Iso (ChainSubdivision.graph (repLength Γ mark h2) (first Γ mark h2) (last Γ mark h2)) Γ where
  vertex := vertexEquiv Γ mark h2 hcovered
  dart := dartEquiv Γ mark h2 hcovered
  origin_eq := origin_map Γ mark h2
  reverse_eq := dartMap_reverse Γ mark h2

include hcovered hcovered' in
/-- No vertex or dart names survive, but all actual graph incidence does. -/
def full (f : Iso S S')
    (hrank : ∀ d,(Fintype.equivFin B' (f.dart d)).val=(Fintype.equivFin B d).val)
    (hlen : ∀ d,chainLength Γ mark h2 d=chainLength Γ' mark' h2' (f.dart d)) : Iso Γ Γ' :=
  ((actual Γ mark h2 hcovered).symm.trans (subdivided Γ mark h2 Γ' mark' h2' f hrank hlen)).trans
    (actual Γ' mark' h2' hcovered')

end

section
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D V' D' : Type*} [Fintype D] [Fintype D']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
    (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
      Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d)
    (hcovered' : ∀ d,ChainCoverage.Covered Γ'.reverse (turn Γ'.origin mark' h2')
      Γ'.reverse_reverse (turn_involutive Γ'.origin mark' h2') d)
local notation "S" => skeleton Γ mark h2
local notation "S'" => skeleton Γ' mark' h2'
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "B'" => {d : D' // turn Γ'.origin mark' h2' d=d}
local notation "R" => Rep Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "F'" => next Γ'.reverse (turn Γ'.origin mark' h2')
local notation "len" => chainLength Γ mark h2
local notation "len'" => chainLength Γ' mark' h2'

end

open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D V' D' : Type} [Fintype D] [Fintype D']
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (Γ' : PortGraph V' D') (mark' : V' → Prop) (h2' : ∀ v,¬mark' v → (out Γ'.origin v).card=2)
    (hcovered : ∀ d,ChainCoverage.Covered Γ.reverse (turn Γ.origin mark h2)
      Γ.reverse_reverse (turn_involutive Γ.origin mark h2) d)
    (hcovered' : ∀ d,ChainCoverage.Covered Γ'.reverse (turn Γ'.origin mark' h2')
      Γ'.reverse_reverse (turn_involutive Γ'.origin mark' h2') d)
local notation "S" => skeleton Γ mark h2
local notation "S'" => skeleton Γ' mark' h2'
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "B'" => {d : D' // turn Γ'.origin mark' h2' d=d}
local notation "len" => chainLength Γ mark h2
local notation "len'" => chainLength Γ' mark' h2'
variable (f : Iso (skeleton Γ mark h2) (skeleton Γ' mark' h2'))
    (hrank : ∀ d,(Fintype.equivFin {d : D' // turn Γ'.origin mark' h2' d=d} (f.dart d)).val=
      (Fintype.equivFin {d : D // turn Γ.origin mark h2 d=d} d).val)
    (hlen : ∀ d,chainLength Γ mark h2 d=chainLength Γ' mark' h2' (f.dart d))
local notation "F" => full Γ mark h2 Γ' mark' h2' hcovered hcovered' f hrank hlen

variable (side : V → Bool) (side' : V' → Bool)
    (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (hs' : ∀ d,side' (Γ'.origin (Γ'.reverse d))=side' (Γ'.origin d))
    (hside : ∀ v : Mark mark,side v.val=side' (f.vertex v).val)

variable {P P' : Type} (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
    (paths' : P' → List {d : D' // turn Γ'.origin mark' h2' d=d})
    (eP : P ≃ P') (hp : ∀ p,(paths p).map f.dart=paths' (eP p))

variable (hne : ∀ p,paths p≠[]) (hne' : ∀ p,paths' p≠[])
    (root : Option P) (root' : Option P') (hroot : root.map eP=root')

end TorsionFreeZeroDivisors.RankedSuppressionIso

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternTotalCoding
open scoped Classical
open PatternCoding

variable {D V P E D' V' P' E' : Type*}
    [Fintype D] [Fintype V] [Fintype P] [Fintype E]
    [Fintype D'] [Fintype V'] [Fintype P'] [Fintype E']
    (R K T I H : ℕ) (hR : 0<R) (hK : 0<K) (hI : 0<I)
    (hD : Fintype.card D≤R) (hV : Fintype.card V≤R)
    (hP : Fintype.card P≤K) (hE : Fintype.card E≤I)

variable (hD' : Fintype.card D'≤R) (hV' : Fintype.card V'≤R)
    (hP' : Fintype.card P'≤K) (hE' : Fintype.card E'≤I)

end TorsionFreeZeroDivisors.PatternTotalCoding

namespace TorsionFreeZeroDivisors.BoundedPattern
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks RankedSuppressionIso

namespace Data
variable {R K T I H : ℕ} (a : Data R K T I H)

end Data
end TorsionFreeZeroDivisors.BoundedPattern

namespace TorsionFreeZeroDivisors.PatternFiniteUnion
open scoped Classical

end TorsionFreeZeroDivisors.PatternFiniteUnion

namespace TorsionFreeZeroDivisors.BoundedPattern.Data

section
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks RankedSuppressionIso
variable {R K T I H : ℕ} (a b : Data R K T I H)

end

open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks ActualPatternEvent
open GridAsymptotics GirthAsymptotics TypedGraphs
variable {R K T I H : ℕ} (a : Data R K T I H)

end TorsionFreeZeroDivisors.BoundedPattern.Data

namespace TorsionFreeZeroDivisors.BoundedPattern
open scoped Classical
open ActualPatternEvent GirthAsymptotics TypedGraphs

end TorsionFreeZeroDivisors.BoundedPattern

namespace TorsionFreeZeroDivisors.ActualComplexity
open scoped Classical BigOperators
open PortSubdivision DegreeTwoSuppression CoreStripping ImageComplexity
open ChainSuppression SuppressedMoore ChainPaths ChainIsomorphism ChainChunkTransport
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P] (Γ : PortGraph V D)

variable (paths : P → List D) (hp : ∀ p,paths p≠[])

end TorsionFreeZeroDivisors.ActualComplexity

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainUsage
open scoped Classical BigOperators
open PortSubdivision DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity
variable {V D P : Type} [Fintype D] [Fintype P] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2
local notation "w" => word Γ mark h2
variable (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "col" => color Γ mark h2 paths
local notation "m" => ChunkComparisons.multiplicity col

end TorsionFreeZeroDivisors.ChainUsage

namespace TorsionFreeZeroDivisors.SourcePattern
open scoped Classical BigOperators
open PortSubdivision MarkedChainBound DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open ActualComplexity CoreStripping ImageComplexity GirthAsymptotics TypedGraphs

namespace Data
variable {B K I rep : ℕ}

end Data
end TorsionFreeZeroDivisors.SourcePattern

namespace TorsionFreeZeroDivisors.BoundedPattern
open scoped Classical Topology
open Filter GirthAsymptotics TypedGraphs ActualPatternEvent

end TorsionFreeZeroDivisors.BoundedPattern

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.RawDecomposition
open scoped Classical BigOperators
open PortSubdivision MarkedChainBound DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open ActualComplexity CoreStripping ImageComplexity GirthAsymptotics TypedGraphs
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (raw : P → List D) (hp : ∀ p,raw p≠[])
    (hc : ∀ p,(raw p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))

end TorsionFreeZeroDivisors.RawDecomposition

namespace TorsionFreeZeroDivisors.ComparisonGeometry

section
open scoped Classical
open ComparedBlocks ChunkComparisons
variable {P E : Type} {l l' : P → ℕ}

variable [Fintype P]
end
open scoped Classical
open ComparedBlocks ChunkComparisons
variable {P E : Type} {l l' : P → ℕ}
end TorsionFreeZeroDivisors.ComparisonGeometry

namespace TorsionFreeZeroDivisors.RawSourcePattern

section
open scoped Classical BigOperators
open PortSubdivision MarkedChainBound DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open ActualComplexity CoreStripping ImageComplexity GirthAsymptotics TypedGraphs ActualPatternEvent

namespace Data
variable {B K I rep : ℕ}

end Data
end
open scoped Classical
open GirthAsymptotics TypedGraphs ActualPatternEvent Filter

end TorsionFreeZeroDivisors.RawSourcePattern
namespace TorsionFreeZeroDivisors.DiameterCounting
open scoped BigOperators Classical
open ConditionedMatchings
variable {V D T : Type*} [Fintype V] [Fintype D]
variable (origin : D → V)

def ports (S : Finset V) : Finset D := Finset.univ.filter (fun e => origin e ∈ S)


omit [Fintype V] in
@[simp] lemma mem_ports (S : Finset V) (e : D) : e ∈ ports origin S ↔ origin e ∈ S := by
  simp [ports]

variable {label : D → T} {bar : T → T}

end TorsionFreeZeroDivisors.DiameterCounting

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ExpansionDiameter
open scoped Classical BigOperators
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def ball (v : V) (r : ℕ) : Finset V :=
  Finset.univ.filter fun w => G.edist v w  ≤  r

@[simp] lemma mem_ball (v w : V) (r : ℕ) : w∈ball G v r ↔ G.edist v w  ≤  r := by
  simp [ball]

end TorsionFreeZeroDivisors.ExpansionDiameter

/-! Quantitative probability estimates for dense witnesses in conditioned
matchings. -/
namespace TorsionFreeZeroDivisors.DiameterProbability
open scoped BigOperators Topology Classical
open Filter

end TorsionFreeZeroDivisors.DiameterProbability

namespace TorsionFreeZeroDivisors.MatchingDiameter
open scoped Classical BigOperators
open ConditionedMatchings DiameterCounting
variable {V D T : Type*} [Fintype V] [Fintype D]
variable (origin : D → V) {label : D → T} {bar : T → T}

end TorsionFreeZeroDivisors.MatchingDiameter

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedDiameter
open Filter ConditionedMatchings MatchingDiameter DiameterProbability
open GirthAsymptotics TypedGraphs TorsionFreeZeroDivisors.Types
open scoped Topology Classical BigOperators

end TorsionFreeZeroDivisors.TypedDiameter
namespace TorsionFreeZeroDivisors.FiniteJointAvoidance
open scoped Classical
end TorsionFreeZeroDivisors.FiniteJointAvoidance

namespace TorsionFreeZeroDivisors.MatchingAlias
open scoped Classical
end TorsionFreeZeroDivisors.MatchingAlias

namespace TorsionFreeZeroDivisors.GraphSample
open scoped Classical
open GirthAsymptotics TypedGraphs ActualPatternEvent Filter

end TorsionFreeZeroDivisors.GraphSample

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SupportedImage
open scoped Classical BigOperators
open PortSubdivision WeightedPortMoore WeightedCycles CoreStripping
variable {V D : Type} (Γ : PortGraph V D) (Q : Finset D)

variable {P : Type} (paths : P → List D) (hpaths : ∀ p d,d∈paths p → d∈Q)

end TorsionFreeZeroDivisors.SupportedImage

namespace TorsionFreeZeroDivisors.RootPins
open scoped Classical
end TorsionFreeZeroDivisors.RootPins

namespace TorsionFreeZeroDivisors.SupportedImage
open scoped Classical
open PortSubdivision
variable {V D : Type} (Γ : PortGraph V D) (Q : Finset D) (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d)) (b : Bool)

variable [Fintype V] [Fintype D] {T TV : Type} [Fintype T] [Fintype TV] (label : D → T) (outgoing : TV → Finset T) (bar : T → T) (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) bar) (target : TV)
end TorsionFreeZeroDivisors.SupportedImage
namespace TorsionFreeZeroDivisors.AmbientPattern
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ComparisonGeometry GirthAsymptotics TypedGraphs ActualPatternEvent

namespace Data
variable {B K I rep : ℕ}

end Data

end TorsionFreeZeroDivisors.AmbientPattern

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedGirth
open scoped Classical BigOperators
open PortSubdivision WeightedPortMoore WeightedCycles
variable {V D : Type} (Γ : PortGraph V D)

end TorsionFreeZeroDivisors.WeightedGirth
namespace TorsionFreeZeroDivisors.SumGirth
open SimpleGraph
variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
end TorsionFreeZeroDivisors.SumGirth
namespace TorsionFreeZeroDivisors.SumPort

section
open PortSubdivision SimpleGraph
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
end
open PortSubdivision
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
end TorsionFreeZeroDivisors.SumPort
namespace TorsionFreeZeroDivisors.SampleGraph

section
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings ActualPatternEvent TypedGraphs GirthAsymptotics
variable (rep : ℕ) (r : Match rep)
end
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ComparisonGeometry GirthAsymptotics TypedGraphs ActualPatternEvent
attribute [instance] BoundedSystem.fP BoundedSystem.fE

end TorsionFreeZeroDivisors.SampleGraph

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ComparisonGeometry GirthAsymptotics TypedGraphs ActualPatternEvent
attribute [instance] BoundedSystem.fP BoundedSystem.fE

namespace BoundedSystem
variable {Bnd K I rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : BoundedSystem Bnd K I rep r x y)
end BoundedSystem
end TorsionFreeZeroDivisors.SampleGraph
namespace TorsionFreeZeroDivisors.ShortClosure

section
open scoped Classical BigOperators
open PortSubdivision WeightedMoore
variable {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)
    (allowed : D → Prop) (z : V)

end
open scoped Classical BigOperators
open PortSubdivision WeightedMoore
variable {V D : Type} (Γ : PortGraph V D)

namespace ReducedPath
variable {Γ} {a b c : V} {p q : List D}
end ReducedPath

variable [Fintype V] [Fintype D]

end TorsionFreeZeroDivisors.ShortClosure

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ShortClosure
open scoped Classical
open PortSubdivision WeightedMoore
variable {V D : Type} (Γ : PortGraph V D)

variable [Fintype V] [Fintype D]

end TorsionFreeZeroDivisors.ShortClosure
namespace TorsionFreeZeroDivisors.SumPort
open PortSubdivision
open scoped Classical BigOperators
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
variable [Fintype DA] [Fintype DB]
end TorsionFreeZeroDivisors.SumPort
namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings ActualPatternEvent TypedGraphs GirthAsymptotics
variable (rep : ℕ) (r : Match rep)
end TorsionFreeZeroDivisors.SampleGraph

namespace TorsionFreeZeroDivisors.RestrictComparisons
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T E : Type} {len : T → ℕ} (C : Comparisons (E:=E) len) (keep : T → Prop)

variable [Fintype T]
end TorsionFreeZeroDivisors.RestrictComparisons

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.FiniteClusters
open scoped Classical BigOperators
variable {V : Type} [Fintype V] (G : SimpleGraph V)
local instance : Fintype G.ConnectedComponent := Fintype.ofFinite _

end TorsionFreeZeroDivisors.FiniteClusters

namespace TorsionFreeZeroDivisors.PairingClusters
open scoped Classical BigOperators
variable {O T : Type} [Fintype O] [Fintype T]
    (f : O → T) (α : O → O) (hα : Function.Involutive α) (keep : T → Prop)
abbrev Vertex := {t // keep t}
include hα in
omit [Fintype O] [Fintype T] in
lemma rel_symm {p q : T} (h : Rel f α p q) : Rel f α q p := by
  obtain ⟨o,ho,hp⟩ := h
  exact ⟨α o,hp,by simpa only [hα o] using ho⟩
def graph : SimpleGraph (Vertex keep) where
  Adj p q := p≠q ∧ Rel f α p.val q.val
  symm := ⟨by
    intro p q h
    exact ⟨Ne.symm h.1,rel_symm f α hα h.2⟩⟩
  loopless := ⟨by intro p h; exact h.1 rfl⟩
local instance : Fintype (graph f α hα keep).ConnectedComponent := Fintype.ofFinite _
end TorsionFreeZeroDivisors.PairingClusters

/-! Arithmetic localization of finite-cluster mass and comparison bounds. -/
namespace TorsionFreeZeroDivisors.PlanarLocalization
open scoped Classical BigOperators

end TorsionFreeZeroDivisors.PlanarLocalization

namespace TorsionFreeZeroDivisors.ClusterLocalization
open scoped Classical BigOperators
open ComparedBlocks
variable {T E : Type} [Fintype T] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop)

abbrev graph := PairingClusters.graph (fun x : Position len => x.1)
  C.pairing.partner C.pairing.involutive keep
abbrev Cluster := (graph C keep).ConnectedComponent
local instance : Fintype (Cluster C keep) := Fintype.ofFinite _
end TorsionFreeZeroDivisors.ClusterLocalization

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ClusterLocalization

section
open scoped Classical BigOperators
open ComparedBlocks
variable {T E : Type} [Fintype T] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop)
local instance clusterFintype : Fintype (Cluster C keep) := Fintype.ofFinite _

end

open scoped Classical BigOperators
open ComparedBlocks
variable {T E : Type} [Fintype T] [Fintype E] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop)
local instance selectedClusterFintype : Fintype (Cluster C keep) := Fintype.ofFinite _

end TorsionFreeZeroDivisors.ClusterLocalization
namespace TorsionFreeZeroDivisors.RestrictComparisons
open scoped Classical
variable {T : Type} (root : Option T) (keep : T → Prop)
end TorsionFreeZeroDivisors.RestrictComparisons

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ComparisonGeometry GirthAsymptotics TypedGraphs ActualPatternEvent
attribute [instance] PathSystem.fP PathSystem.fE
namespace PathSystem
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (keep : s.P → Prop)
end PathSystem
end TorsionFreeZeroDivisors.SampleGraph
namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open ComparedBlocks ClusterLocalization GirthAsymptotics TypedGraphs ActualPatternEvent
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (keep : s.P → Prop)
local instance : Fintype (Cluster s.comparisons keep) := Fintype.ofFinite _

end TorsionFreeZeroDivisors.SampleGraph.PathSystem

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.BalancedPieces
open scoped Classical BigOperators

end TorsionFreeZeroDivisors.BalancedPieces
namespace TorsionFreeZeroDivisors.ConsecutivePieces
open scoped Classical BigOperators
variable {A : Type*} {m : ℕ} (l : List A) (n : Fin m → ℕ) (hs : (∑ i,n i)=l.length)

end TorsionFreeZeroDivisors.ConsecutivePieces
namespace TorsionFreeZeroDivisors.BalancedWords
open scoped Classical BigOperators
variable {T A : Type} (w : T → List A) (cap : ℕ) (hc : 0<cap)

variable [Fintype T]
end TorsionFreeZeroDivisors.BalancedWords
namespace TorsionFreeZeroDivisors.ShortClosure
open PortSubdivision WeightedMoore.PortWalk
variable {V D : Type} (Γ : PortGraph V D)
end TorsionFreeZeroDivisors.ShortClosure
namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap)
    (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap)
    (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords
namespace TorsionFreeZeroDivisors.SingleException
open scoped Classical BigOperators
variable {T : Type} [Fintype T] (root : Option T) (f : T → ℕ) (L : ℕ)
end TorsionFreeZeroDivisors.SingleException
namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (U : ℕ) (hU : 3≤U)
    (hL : 1≤L (size rep)) (hcap : 6≤U*L (size rep))
    (hd : GraphSample.Diameters rep r) (hr : r∈samples rep)
    (hordinary : ∃t,s.root≠some t)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

/-! Finite rotation systems. The Euler inequality here
is explicitly an input from a planar realization; no PL realization or planar
separator theorem is asserted by this file. The face cycles and bad-gap count,
however, are computed from the actual boundary and pairing permutations. -/
namespace TorsionFreeZeroDivisors.PermutationCycles
open scoped Classical BigOperators
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
instance : Fintype (Cycle f) := Fintype.ofFinite _
def cycle (x : O) : Cycle f := Quotient.mk _ x
def members (c : Cycle f) : Finset O := Finset.univ.filter (fun x => cycle f x=c)
@[simp] lemma mem_members {c : Cycle f} {x : O} : x∈members f c ↔ cycle f x=c := by simp [members]
omit [Fintype O] in
lemma cycle_eq {x y : O} : cycle f x=cycle f y ↔ f.SameCycle x y := Quotient.eq
omit [Fintype O] in
@[simp] lemma cycle_apply (x : O) : cycle f (f x)=cycle f x := by
  apply (cycle_eq f).mpr
  simpa only [Equiv.Perm.sameCycle_apply_left] using Equiv.Perm.SameCycle.refl f x

end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.PlanarRotation
open scoped Classical BigOperators
open PermutationCycles

variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.PlanarRotation
namespace TorsionFreeZeroDivisors.PlanarRuns
open scoped Classical BigOperators
open PlanarRotation
variable {O : Type}

namespace CutSystem
variable {σ : Equiv.Perm O} (S : CutSystem σ)
def distance (x : O) : ℕ := Nat.find (S.hits x)
def finish (x : O) : O := (σ^(S.distance x)) x
lemma finish_mem (x : O) : S.finish x∈S.cut := Nat.find_spec (S.hits x)
lemma distance_zero {x : O} (hx : x∈S.cut) : S.distance x=0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.find_min' (S.hits x) (by simpa using hx)
lemma finish_cut {x : O} (hx : x∈S.cut) : S.finish x=x := by
  simp only [finish,S.distance_zero hx,pow_zero,Equiv.Perm.one_apply]
lemma zero_iff (x : O) : S.distance x=0 ↔ x∈S.cut := by
  constructor
  · intro h
    simpa only [finish,h,pow_zero,Equiv.Perm.one_apply] using S.finish_mem x
  · exact S.distance_zero
lemma distance_next {x : O} (hx : x∉S.cut) : S.distance x=S.distance (σ x)+1 := by
  have hp : 0<S.distance x := Nat.pos_of_ne_zero (fun h => hx ((S.zero_iff x).mp h))
  apply Nat.le_antisymm
  · apply Nat.find_min'
    simpa only [finish,pow_succ,Equiv.Perm.mul_apply] using S.finish_mem (σ x)
  · have hm := Nat.find_min' (S.hits (σ x)) (show (σ^(S.distance x-1)) (σ x)∈S.cut from by
      rw [← Equiv.Perm.mul_apply,← pow_succ,Nat.sub_add_cancel hp]
      exact S.finish_mem x)
    change S.distance (σ x)≤S.distance x-1 at hm
    omega
lemma finish_next {x : O} (hx : x∉S.cut) : S.finish (σ x)=S.finish x := by
  simp only [finish,S.distance_next hx,pow_succ,Equiv.Perm.mul_apply]

namespace Paired
variable {S}
variable {α : Equiv.Perm O} (P : S.Paired α)
include P
lemma opposite_next {x : O} (hx : x∉S.cut) : σ (α (σ x))=α x := by
  have h := congrArg α (P.good x hx).1
  change α (α (σ (α (σ x))))=α x at h
  rw [P.involutive] at h
  exact h
lemma opposite_uncut {x : O} (hx : x∉S.cut) : α (σ x)∉S.cut := by
  exact fun h => hx ((P.stable x (P.good x hx)).mpr h)
lemma finish_opposite {x : O} (hx : x∉S.cut) : S.finish (α (σ x))=S.finish (α x) := by
  have h := S.finish_next (P.opposite_uncut hx)
  rw [P.opposite_next hx] at h
  exact h.symm
lemma finish_pair (x : O) : S.finish (α (S.finish x))=S.finish (α x) := by
  generalize hn : S.distance x=n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hx : x∈S.cut
    · rw [S.finish_cut hx]
    · have hd := S.distance_next hx
      have he := ih (S.distance (σ x)) (by omega) (σ x) rfl
      rw [S.finish_next hx] at he
      exact he.trans (P.finish_opposite hx)

def pair (_P : S.Paired α) (c : {x // x∈S.cut}) : {x // x∈S.cut} := ⟨S.finish (α c.val),S.finish_mem _⟩
lemma pair_involutive : Function.Involutive (P.pair) := by
  intro c
  apply Subtype.ext
  change S.finish (α (S.finish (α c.val)))=c.val
  rw [P.finish_pair,P.involutive,S.finish_cut c.property]

end Paired
namespace PairOrbit
variable {A : Type} (r : A→A) (hr : Function.Involutive r)
def relation : Setoid A where
  r x y := x=y ∨ r x=y
  iseqv := ⟨fun _ => Or.inl rfl,fun {x y} h => by
    rcases h with h|h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [←h,hr]),fun {x y z} h k => by
    rcases h with rfl|h
    · exact k
    · rcases k with rfl|k
      · exact Or.inr h
      · exact Or.inl (by rw [←k,←h,hr])⟩
abbrev Orbit := Quotient (relation r hr)
variable [Fintype A]
instance : Fintype (Orbit r hr) := Fintype.ofFinite _
end PairOrbit

namespace Paired
variable {S} {α : Equiv.Perm O} (P : S.Paired α)
abbrev IntervalPair := PairOrbit.Orbit P.pair P.pair_involutive
instance : Fintype P.IntervalPair := PairOrbit.instFintypeOrbit _ _
end Paired

end CutSystem
end TorsionFreeZeroDivisors.PlanarRuns

namespace TorsionFreeZeroDivisors.PlanarIntervals
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks PlanarRuns PlanarRuns.CutSystem
variable {T : Type} {len : T→ℕ} {σ α : Equiv.Perm (Position len)}
    (S : CutSystem σ) (P : S.Paired α)
    (hstep : ∀ x,x∉S.cut → (σ x).1=x.1 ∧ (σ x).2.val=x.2.val+1)

include hstep
end TorsionFreeZeroDivisors.PlanarIntervals
namespace TorsionFreeZeroDivisors.ExtendComparisons
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T E : Type} {len more : T → ℕ} (C : Comparisons (E:=E) len)
    (hle : ∀ t,len t ≤ more t)

variable (hupper : ∀ e,C.hi e≤len (C.source e))

variable [Fintype T]
end TorsionFreeZeroDivisors.ExtendComparisons
namespace TorsionFreeZeroDivisors.WordPositions

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T : Type} (len : T → ℕ)
variable {A : Type} (w : T → List A)

variable (cap : ℕ) (hc : 0<cap)
end
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T : Type} [Fintype T] (len : T → ℕ)
variable {A : Type} (w v : T → List A)
variable {E : Type} (C : Comparisons (E:=E) (fun t=>(w t).length))
end TorsionFreeZeroDivisors.WordPositions

namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore BlockAlignment ComparedBlocks
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap) (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r) {E : Type} [Fintype E] (lo hi : E → ℕ) (hle : ∀ e,lo e≤hi e)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

namespace TorsionFreeZeroDivisors.BoundaryRotation

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T : Type} (len : T → ℕ)
variable [Fintype T]
end

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T A : Type} [Fintype T] (len : T → ℕ) (root : Option T) (label : Position len → A) (bar : A → A) (α : Equiv.Perm (Position len)) (hr : Function.Involutive α) (hcomp : ∀ x,label (α x)=bar (label x))
end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions
variable {T : Type} (len : T → ℕ)
variable {A : Type} (w : T → List A) (R : A → A → Prop)
end TorsionFreeZeroDivisors.BoundaryRotation

namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions BoundaryRotation WeightedMoore ActualPatternEvent GirthAsymptotics
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} (s : PathSystem rep r x y)
end TorsionFreeZeroDivisors.SampleGraph.PathSystem

namespace TorsionFreeZeroDivisors.PermutationTransport
variable {A B : Type} (e : A ≃ B) (f : Equiv.Perm A)
end TorsionFreeZeroDivisors.PermutationTransport

namespace TorsionFreeZeroDivisors.BalancedRotation
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T A : Type} [Fintype T] (w : T → List A) (cap : ℕ) (hc : 0<cap)
end TorsionFreeZeroDivisors.BalancedRotation

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
namespace FullPairing
variable {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap)
end FullPairing
end TorsionFreeZeroDivisors.SampleGraph

namespace TorsionFreeZeroDivisors.PermutationTransport
open PermutationCycles
variable {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (f : Equiv.Perm A)
end TorsionFreeZeroDivisors.PermutationTransport

namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent PermutationCycles PlanarRotation
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap)
end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap) (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.FullPairing

/-! Recursive separation. This is the actual deletion-set
construction and sharp charging estimate. The one-step Lipton–Tarjan theorem
is kept as an explicit dependency, not asserted from an unspecified planar
predicate.  No claim of a completed planar realization is made here. -/
namespace TorsionFreeZeroDivisors.RecursiveSeparator
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] (R : V → V → Prop)

namespace Split
variable {R} {S : Finset V} (P : Split R S)
end Split

namespace Split
variable {R} {S : Finset V} (P : Split R S) (D : Finset V → Finset V)
end Split

end TorsionFreeZeroDivisors.RecursiveSeparator

namespace TorsionFreeZeroDivisors.PlanarParameters
open scoped Classical
open RecursiveSeparator
variable (ε : ℝ) (D : ℕ)
end TorsionFreeZeroDivisors.PlanarParameters

namespace TorsionFreeZeroDivisors.LocalizationCounts
open scoped Classical BigOperators
open ComparedBlocks BlockAlignment
variable {T E : Type} [Fintype T] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop) (old : T → ℕ)
    (hprefix : ∀ p : Position len,C.pairing.partner p≠p → p.2.val∈positions 0 (old p.1))

end TorsionFreeZeroDivisors.LocalizationCounts

namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs ComparedBlocks ClusterLocalization
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y)
local instance : Fintype s.P := s.fP
local instance : Fintype s.E := s.fE

end TorsionFreeZeroDivisors.SampleGraph.PathSystem

namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (hL : 2≤L (size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.FullPairing

namespace TorsionFreeZeroDivisors.PermutationCycles
variable {O B : Type} [Fintype O] (f : Equiv.Perm O)
omit [Fintype O] in
lemma invariant_pow (q : O → B) (hq : ∀x,q (f x)=q x) (n : ℕ) (x : O) :
    q ((f^n) x)=q x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,hq,ih]
def lift (q : O → B) (hq : ∀x,q (f x)=q x) : Cycle f → B :=
  Quotient.lift q (by
    intro x y h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    rw [←hn]
    exact (invariant_pow f q hq n x).symm)
@[simp] lemma lift_cycle (q : O → B) (hq : ∀x,q (f x)=q x) (x : O) :
    lift f q hq (cycle f x)=q x := rfl
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.InsertedRotation
open scoped Classical
open PermutationCycles
variable {O : Type} (σ α : Equiv.Perm O) (p : O)

def rotation : Equiv.Perm (O⊕Bool) :=
  Equiv.sumCongr σ (Equiv.refl _) * Equiv.swap (.inl p) (.inr true) *
    Equiv.swap (.inl p) (.inr false)
def pairing : Equiv.Perm (O⊕Bool) := Equiv.sumCongr α Equiv.boolNot
def face : Equiv.Perm (O⊕Bool) := pairing α * rotation σ p
@[simp] lemma rotation_p : rotation σ p (.inl p)=.inr false := by
  simp [rotation,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
@[simp] lemma rotation_false : rotation σ p (.inr false)=.inr true := by
  simp [rotation,Equiv.Perm.mul_apply]
@[simp] lemma rotation_true : rotation σ p (.inr true)=.inl (σ p) := by
  simp [rotation,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
@[simp] lemma face_p : face σ α p (.inl p)=.inr true := by
  simp [face,Equiv.Perm.mul_apply,pairing]
@[simp] lemma face_false : face σ α p (.inr false)=.inr false := by
  simp [face,Equiv.Perm.mul_apply,pairing]
@[simp] lemma face_true : face σ α p (.inr true)=.inl ((α*σ) p) := by
  simp [face,Equiv.Perm.mul_apply,pairing]

variable [Fintype O]

end TorsionFreeZeroDivisors.InsertedRotation

namespace TorsionFreeZeroDivisors.SwapCycles

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)
abbrev Away := {c : Cycle f // c≠cycle f p ∧ c≠cycle f q}
def classify (x : O) : Option (Away f p q) :=
  if h : cycle f x≠cycle f p ∧ cycle f x≠cycle f q then some ⟨cycle f x,h⟩ else none
@[simp] lemma classify_p : classify f p q p=none := by simp [classify]
@[simp] lemma classify_q : classify f p q q=none := by simp [classify]
variable [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)

variable [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O)
end

open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (f : Equiv.Perm O) (p q : O)
end TorsionFreeZeroDivisors.SwapCycles

namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles SwapCycles
variable {O : Type} [Fintype O]

def merge (f : Equiv.Perm O) (p q : O) : Equiv.Perm O :=
  if cycle f p=cycle f q then f else Equiv.swap p q*f

def forest (σ : Equiv.Perm O) : List (O×O) → Equiv.Perm O
  | []=>σ
  | e::l=>merge (forest σ l) e.1 e.2
end TorsionFreeZeroDivisors.ComponentEuler

namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O]
def component (σ α : Equiv.Perm O) (x : O) : Component σ α := Quotient.mk _ x
variable (σ α : Equiv.Perm O) (l : List (O×O))
    (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
    (he : ∀e∈l,α e.1=e.2)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles SwapCycles
variable {O : Type} [Fintype O]
end TorsionFreeZeroDivisors.ComponentEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler PairingFactors
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.DeleteCycle

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
variable [Fintype O]
end
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
variable [Fintype O]
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
variable {O B : Type} (σ α : Equiv.Perm O)
def lift (q : O→B) (hσ : ∀x,q (σ x)=q x) (hα : ∀x,q (α x)=q x) : Component σ α →B :=
  Quotient.lift q (by
    intro x y h
    induction h with
    | rel x y h=>
      rcases h with h|h
      · exact (hσ x).symm.trans (congrArg q h)
      · exact (hα x).symm.trans (congrArg q h)
    | refl=>rfl
    | symm _ _ _ ih=>exact ih.symm
    | trans _ _ _ _ _ ih ih'=>exact ih.trans ih')
@[simp] lemma lift_component (q : O→B) (hσ : ∀x,q (σ x)=q x) (hα : ∀x,q (α x)=q x) (x : O) :
    lift σ α q hσ hα (component σ α x)=q x := rfl
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.MapDeletion

section
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p) (hs : σ p≠p)
end
open scoped Classical
open DeleteCycle MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open PermutationCycles DeleteCycle
variable {O A : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)

variable (hs : σ p≠p)
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
end TorsionFreeZeroDivisors.BandEuler

/-! Actual finite noncrossing word matchings, the cancellation part of the
cone-picture construction. An ear is inserted at two adjacent positions.
This file asserts no sphere realization or asphericity theorem. -/
namespace TorsionFreeZeroDivisors.WordPairing

section
variable {A : Type*} {n : ℕ}

namespace Ear
variable (k : ℕ)
def raise (i : Fin n) : Fin (n+2) := ⟨if i.val<k then i.val else i.val+2,by
  split_ifs with h <;> omega⟩
lemma raise_injective : Function.Injective (raise (n:=n) k) := by
  intro i j he
  apply Fin.ext
  have hh := congrArg Fin.val he
  simp only [raise] at hh
  split_ifs at hh <;> omega
lemma raise_avoid (i : Fin n) : (raise k i).val≠k ∧ (raise k i).val≠k+1 := by
  simp only [raise]
  split_ifs <;> omega

def insert (hk : k≤n) : Fin n⊕Bool → Fin (n+2)
  | .inl i => raise k i
  | .inr false => ⟨k,by omega⟩
  | .inr true => ⟨k+1,by omega⟩
lemma insert_injective (hk : k≤n) : Function.Injective (insert k hk) := by
  intro x y he
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (raise_injective k he)
    | inr b =>
      have hh := congrArg Fin.val he
      have ha := raise_avoid k i
      cases b <;> simp only [insert] at hh <;> omega
  | inr b =>
    cases y with
    | inl i =>
      have hh := congrArg Fin.val he
      have ha := raise_avoid k i
      cases b <;> simp only [insert] at hh <;> omega
    | inr c =>
      have hh := congrArg Fin.val he
      cases b <;> cases c <;> simp only [insert] at hh <;> first | rfl | omega
lemma insert_surjective (hk : k≤n) : Function.Surjective (insert k hk) := by
  intro y
  by_cases h : y.val<k
  · refine ⟨.inl ⟨y.val,by omega⟩,?_⟩
    apply Fin.ext
    simp only [insert,raise,if_pos h]
  · by_cases he : y.val=k
    · exact ⟨.inr false,Fin.ext he.symm⟩
    · by_cases he' : y.val=k+1
      · exact ⟨.inr true,Fin.ext he'.symm⟩
      · refine ⟨.inl ⟨y.val-2,by omega⟩,?_⟩
        apply Fin.ext
        have hh : ¬y.val-2<k := by omega
        simp only [insert,raise,if_neg hh]
        omega

def equiv (hk : k≤n) : Fin n⊕Bool ≃ Fin (n+2) :=
  Equiv.ofBijective (insert k hk) ⟨insert_injective k hk,insert_surjective k hk⟩
@[simp] lemma equiv_left (hk : k≤n) (i : Fin n) : equiv k hk (.inl i)=raise k i := rfl
@[simp] lemma equiv_false (hk : k≤n) : (equiv k hk (.inr false)).val=k := rfl
@[simp] lemma equiv_true (hk : k≤n) : (equiv k hk (.inr true)).val=k+1 := rfl

variable {inv : A → A} {label : Fin n → A}
end Ear
end

section
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Data
end Data

namespace Ear
variable (k : ℕ) (hk : k≤n) (a : A)
def labels (i : Fin (n+2)) : A :=
  Sum.elim label (fun b=>if b then inv a else a) ((equiv k hk).symm i)
@[simp] lemma labels_left (i : Fin n) :
    labels (label:=label) (inv:=inv) k hk a (equiv k hk (.inl i))=label i := by
  simp only [labels,Equiv.symm_apply_apply,Sum.elim_inl]
@[simp] lemma labels_false :
    labels (label:=label) (inv:=inv) k hk a (equiv k hk (.inr false))=a := by
  simp only [labels,Equiv.symm_apply_apply,Sum.elim_inr,Bool.false_eq_true,ite_false]
@[simp] lemma labels_true :
    labels (label:=label) (inv:=inv) k hk a (equiv k hk (.inr true))=inv a := by
  simp only [labels,Equiv.symm_apply_apply,Sum.elim_inr,ite_true]

end Ear

namespace ListInsert
variable (u v : List A) (a b : A)
end ListInsert

end
variable {A : Type*}
namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
end ListInsert

end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.Ear
open PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
variable (k : ℕ) (hk : k≤n) (hn : 0<n)

end TorsionFreeZeroDivisors.WordPairing.Ear

namespace TorsionFreeZeroDivisors.PermutationCycles
variable (O : Type) [Fintype O]
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.WordPairing

section
open PermutationCycles
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Ear
variable (k : ℕ) (hk : k≤n)
end Ear

namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
end ListInsert

end
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.EraseEar
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin (n+2)→A} (k : ℕ) (hk : k≤n)
end TorsionFreeZeroDivisors.WordPairing.EraseEar
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
variable {A : Type*} {inv : A → A}
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.MapEuler
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
open MapEuler PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin n→A}
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.DeleteCycle
open scoped Classical
variable {O : Type} (σ : Equiv.Perm O) (p : O)
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.IsolatedDeletion
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} (σ α : Equiv.Perm O) (p : O) (hs : σ p=p) (ha : α p=p)
variable [Fintype O]
end TorsionFreeZeroDivisors.IsolatedDeletion
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion

namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.BoundarySurgery
open scoped Classical
open DeleteCycle BandEuler
variable {O V : Type} [Fintype O] (σ : Equiv.Perm O) (before after : O→V)
variable (p q : O) (hpq : p≠q)
end TorsionFreeZeroDivisors.BoundarySurgery

namespace TorsionFreeZeroDivisors.VertexSplit
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O)
  (l : List (O×O)) (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
  (he : ∀e∈l,α e.1=e.2)
  (hc : cycle σ p=cycle σ q)
local notation "σ'" => Equiv.swap p q*σ
local notation "L'" => (α p,α q)::l
local notation "f'" => forest σ' L'
end TorsionFreeZeroDivisors.VertexSplit
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.MapConjugation
open scoped Classical
open MapEuler PermutationCycles
variable {A B : Type} (e : A ≃ B) (σ α : Equiv.Perm A)
local notation "σ'" => e.permCongr σ
local notation "α'" => e.permCongr α
variable [Fintype A] [Fintype B]
end TorsionFreeZeroDivisors.MapConjugation

/-! The finite matching operation for the same-lifted-edge band surgery.
Deleting two inverse occurrences splices their partners unless they were already
paired. Labels, involutivity and the absence of fixed points are proved from the
actual matching. This file does not assert a surface realization or essentiality.
-/
namespace TorsionFreeZeroDivisors.MatchingSurgery
open scoped Classical
variable {O A : Type*} (α : Equiv.Perm O) (hi : Function.Involutive α)
  (hf : ∀x,α x≠x) (p q : O) (hpq : p≠q)

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))

end TorsionFreeZeroDivisors.MatchingSurgery
namespace TorsionFreeZeroDivisors.Smoothing
open scoped Classical
open DeleteCycle
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (hf : ∀x,α x≠x)
  (p q : O) (hpq : p≠q) (hsp : σ p=q) (hsq : σ q=p)

variable [Fintype O]

end TorsionFreeZeroDivisors.Smoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
open PermutationCycles
variable {O V : Type} (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)

variable [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (hf : ∀x,α x≠x)

variable (before after : O→V)
end TorsionFreeZeroDivisors.Tightening

/-! The finite matching operation for the same-lifted-edge band surgery.
Deleting two inverse occurrences splices their partners unless they were already
paired. Labels, involutivity and the absence of fixed points are proved from the
actual matching. This file does not assert a surface realization or essentiality.
-/
namespace TorsionFreeZeroDivisors.PartialMatchingSurgery
open scoped Classical
variable {O A : Type*} (α : Equiv.Perm O) (hi : Function.Involutive α)
  (p q : O) (hpq : p≠q) (hfp : α p≠p) (hfq : α q≠q)

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))

end TorsionFreeZeroDivisors.PartialMatchingSurgery
namespace TorsionFreeZeroDivisors.PartialSmoothing
open scoped Classical
open DeleteCycle
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α)
  (p q : O) (hpq : p≠q) (hfp : α p≠p) (hfq : α q≠q) (hsp : σ p=q) (hsq : σ q=p)

variable [Fintype O]

end TorsionFreeZeroDivisors.PartialSmoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
variable {O : Type} [Fintype O] (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)
  (α : Equiv.Perm O) (hi : Function.Involutive α) (hfp : α p≠p) (hfq : α q≠q)
end TorsionFreeZeroDivisors.Tightening
namespace TorsionFreeZeroDivisors.FinitePicture
open scoped Classical
open PortSubdivision
variable {V D A O : Type} (Γ : PortGraph V D) (label : D→A) (inv : A→A) (x y : V) [Fintype O]
namespace Data
variable {Γ label inv x y}

variable {O' : Type} [Fintype O']

variable (p q : O) (hpq : p≠q)
end Data
end TorsionFreeZeroDivisors.FinitePicture

namespace TorsionFreeZeroDivisors.PermutationCycles
open scoped Classical BigOperators
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
end TorsionFreeZeroDivisors.PermutationCycles
namespace TorsionFreeZeroDivisors.FinitePicture.Data
open scoped Classical
open DeleteCycle MapEuler PermutationCycles
variable {V D A O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D} {label : D→A} {inv : A→A} {x y : V}
variable (hxy : x≠y)

variable (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
  (himm : ∀d e,Γ.origin d=Γ.origin e → label d=label e → d=e)
end TorsionFreeZeroDivisors.FinitePicture.Data

/-! Exact finite permutation cycles, including singleton cycles, as nonempty
lists with their literal successor. This is the coordinate bridge from marked
picture surgery to boundary words; it asserts no geometric realization. -/

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ContiguousSplit
open scoped Classical
open PermutationCycles
variable (n m : ℕ)

end TorsionFreeZeroDivisors.ContiguousSplit
namespace TorsionFreeZeroDivisors.BoundaryRefinement
open scoped Classical
open PermutationCycles
variable {O : Type}
variable [Fintype O]
variable {P : Type} [Fintype P]

end TorsionFreeZeroDivisors.BoundaryRefinement
namespace TorsionFreeZeroDivisors.BlockBoundary
open scoped Classical
open BoundaryRefinement
/-- Each original block has its own actual finite cyclic boundary. Empty
blocks contribute no occurrences, rather than an artificial marked vertex. -/
def Occ : List ℕ→Type
  | []=>Empty
  | n::ns=>Fin n⊕Occ ns
instance (ns : List ℕ) : Fintype (Occ ns) := by
  induction ns with
  | nil=>exact inferInstanceAs (Fintype Empty)
  | cons n ns ih=>
    let : Fintype (Occ ns) := ih
    exact inferInstanceAs (Fintype (Fin n⊕Occ ns))

variable {A : Type*} {ns : List ℕ} {inv : A→A} {label : Fin ns.sum→A}

end TorsionFreeZeroDivisors.BlockBoundary
/-! Algebraic disk-picture certificates. The relator words are retained literally,
not replaced by their reduced representatives. Connector words may be arbitrary.
No planar-surface realization or minimal-band theorem is assumed here. -/
namespace TorsionFreeZeroDivisors.AlgebraicPictures
open FreeGroup
variable {A I : Type*} (rel : I → List (A×Bool))

structure Term where
  index : I
  positive : Bool
  connector : List (A×Bool)
namespace Term
variable (t : Term (A:=A) (I:=I))
def core : List (A×Bool) := if t.positive then rel t.index else invRev (rel t.index)
def word : List (A×Bool) := t.connector++t.core rel++invRev t.connector
def flip : Term (A:=A) (I:=I) := ⟨t.index,!t.positive,t.connector⟩
lemma core_flip : t.flip.core rel=invRev (t.core rel) := by
  cases t with
  | mk i b c => cases b <;> simp [flip,core]
lemma word_flip : t.flip.word rel=invRev (t.word rel) := by
  change t.connector++t.flip.core rel++invRev t.connector=_
  rw [core_flip]
  simp only [word,invRev_append,invRev_invRev,List.append_assoc]
end Term

def word (ts : List (Term (A:=A) (I:=I))) : List (A×Bool) := ts.flatMap (Term.word rel)
def relations : Set (FreeGroup A) := Set.range (fun i=>mk (rel i))
lemma word_append (s t : List (Term (A:=A) (I:=I))) :
    word rel (s++t)=word rel s++word rel t := List.flatMap_append
lemma word_reverse_flip (s : List (Term (A:=A) (I:=I))) :
    word rel (s.reverse.map Term.flip)=invRev (word rel s) := by
  induction s with
  | nil => rfl
  | cons t s ih =>
    simp only [List.reverse_cons,List.map_append,List.map_singleton,
      word,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] at *
    rw [ih,Term.word_flip,invRev_append]

/-- Literal normal-closure expansion, with each actual relator and its sign. -/
theorem expansion {g : FreeGroup A} (h : g∈Subgroup.normalClosure (relations rel)) :
    ∃ ts : List (Term (A:=A) (I:=I)),mk (word rel ts)=g := by
  classical
  induction h using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨r,⟨i,rfl⟩,hc⟩ := Group.mem_conjugatesOfSet_iff.mp hg
    obtain ⟨c,rfl⟩ := isConj_iff.mp hc
    refine ⟨[⟨i,true,c.toWord⟩],?_⟩
    simp only [word,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      Term.word,Term.core,ite_true,←mul_mk,←inv_mk,mk_toWord]
  | one => exact ⟨[],rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s,hs⟩ := hx
    obtain ⟨t,ht⟩ := hy
    exact ⟨s++t,by rw [word_append,←mul_mk,hs,ht]⟩
  | inv x _ hx =>
    obtain ⟨s,hs⟩ := hx
    exact ⟨s.reverse.map Term.flip,by rw [word_reverse_flip,←inv_mk,hs]⟩

variable (outer : List (A×Bool))

end TorsionFreeZeroDivisors.AlgebraicPictures

end

end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.RelationArea
open scoped Classical BigOperators
open AlgebraicPictures CellModule
noncomputable section
variable {A I : Type} (rel : I→List (A×Bool))
abbrev G := PresentedGroup (relations rel)
abbrev N := Subgroup.normalClosure (relations rel)
abbrev q : FreeGroup A→*G rel := PresentedGroup.mk (relations rel)
def term (t : Term (A:=A) (I:=I)) : CellModule.Module (G rel) I :=
  if t.positive then Finsupp.single (q rel (FreeGroup.mk t.connector),t.index) 1
  else -Finsupp.single (q rel (FreeGroup.mk t.connector),t.index) 1
def total (ts : List (Term (A:=A) (I:=I))) : CellModule.Module (G rel) I := (ts.map (term rel)).sum
variable (hz : ∀ts : List (Term (A:=A) (I:=I)),FreeGroup.mk (word rel ts)=1→total rel ts=0)

def area (x : N rel) : CellModule.Module (G rel) I := total rel (Classical.choose (expansion rel x.property))

def d₂ : CellModule.Module (G rel) I→+CellModule.Module (G rel) A :=
  Finsupp.liftAddHom (fun p=>zmultiplesHom _ (translate p.1 (fox (q rel) (FreeGroup.mk (rel p.2)))))
@[simp] lemma d₂_single (p : G rel×I) (z : ℤ) :
    d₂ rel (Finsupp.single p z)=z • translate p.1 (fox (q rel) (FreeGroup.mk (rel p.2))) := by
  simp [d₂]
end
end TorsionFreeZeroDivisors.RelationArea


end


end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.RelationSplit
open scoped Classical BigOperators
open AlgebraicPictures CellModule RelationArea
noncomputable section
variable {A I : Type} (rel : I→List (A×Bool))
variable (hz : ∀ts : List (Term (A:=A) (I:=I)),FreeGroup.mk (word rel ts)=1→total rel ts=0)
def sectionWord (g : G rel) : FreeGroup A := Classical.choose (PresentedGroup.mk_surjective (relations rel) g)
lemma sectionWord_q (g : G rel) : q rel (sectionWord rel g)=g :=
  Classical.choose_spec (PresentedGroup.mk_surjective (relations rel) g)
def loop (g : G rel) (w : FreeGroup A) : N rel :=
  ⟨sectionWord rel g*w*(sectionWord rel (g*q rel w))⁻¹,PresentedGroup.mk_eq_one_iff.mp (by
    simp only [map_mul,map_inv,sectionWord_q,mul_inv_cancel])⟩

def retract : CellModule.Module (G rel) A→+CellModule.Module (G rel) I :=
  Finsupp.liftAddHom (fun p=>zmultiplesHom _ (area rel (loop rel p.1 (FreeGroup.of p.2))))
@[simp] lemma retract_single (p : G rel×A) (z : ℤ) :
    retract rel (Finsupp.single p z)=z • area rel (loop rel p.1 (FreeGroup.of p.2)) := by
  simp [retract]
end
end TorsionFreeZeroDivisors.RelationSplit

end


end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SplitModel
open Set Topology GroupRingTopology GroupRingTopology.Attachment
variable {G S Q : Type} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
  (s : S→G) (w : Q→FreeGroup S) (hw : ∀i,FreeGroup.lift s (w i)=1)
  (hs : Function.Surjective (FreeGroup.lift s))
  (hker : (FreeGroup.lift s).ker=Subgroup.normalClosure (Set.range w))
  (L : CellModule.Module G S→+CellModule.Module G Q)
  (hL : ∀g i,L (CellModule.translate g (CellModule.fox (FreeGroup.lift s) (w i)))=Finsupp.single (g,i) 1)
include hs hker hL in
theorem contractible : ContractibleSpace (IndexedCells.Cover s w hw) := by
  let := IndexedCells.cover_simplyConnected s w hw hs hker
  let a := IndexedCells.attaching s w hw
  let f : C(IndexedCells.Cover s w hw,IndexedCells.Cover s w hw) := .id _
  let y := IndexedCells.inclusion s w hw (Cayley.vertex s 1)
  let f' := VertexCollapse.map s a f y
  have hv : ∀g,f' (IndexedCells.inclusion s w hw (Cayley.vertex s g))=y :=
    VertexCollapse.map_vertex s a f y
  apply (contractible_iff_id_nullhomotopic _).mpr
  exact ⟨y,⟨(VertexCollapse.homotopy s a f y).trans (AbsorbCells.homotopy s w hw L hL f' y hv)⟩⟩
include hw hs hker hL in
theorem has_model_oai [Finite S] [Finite Q] [Nonempty Q] : HasFiniteTwoDimensionalClassifyingSpace G := by
  let a := IndexedCells.attaching s w hw
  refine ⟨IndexedCells.Base s w hw,inferInstance,inferInstance,inferInstance,inferInstance,
    CellPresentation.base_finite s a,CellPresentation.base_no_higher s a,
    CellPresentation.base_two_cell s a,CellPresentation.basePoint s a,
    ⟨CellPresentation.fundamentalEquiv s a w (IndexedCells.wordLift_rel s w hw) hs hker⟩,
    IndexedCells.Cover s w hw,inferInstance,contractible s w hw hs hker L hL,
    CellPresentation.projection s a,?_,?_⟩
  · exact (CellPresentation.projection_quotient s a).isCoveringMap
  · exact (CellPresentation.projection_quotient s a).surjective
end TorsionFreeZeroDivisors.SplitModel

namespace TorsionFreeZeroDivisors.RelationModel
open AlgebraicPictures RelationArea
variable {A I : Type} (rel : I→List (A×Bool))
  (hz : ∀ts : List (Term (A:=A) (I:=I)),FreeGroup.mk (word rel ts)=1→total rel ts=0)
local instance : TopologicalSpace (G rel) := ⊥
local instance : DiscreteTopology (G rel) := ⟨rfl⟩
end TorsionFreeZeroDivisors.RelationModel

end

end OAI

end
end


open OAI.TorsionFreeZeroDivisors in
theorem solution {G S Q : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (s : S → G) (w : Q → FreeGroup S) (hw : ∀ i, FreeGroup.lift s (w i) = 1)
    (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure (Set.range w))
    (L : CellModule.Module G S →+ CellModule.Module G Q)
    (hL : ∀ g i, L (CellModule.translate g (CellModule.fox (FreeGroup.lift s) (w i))) =
      Finsupp.single (g, i) 1)
    [Finite S] [Finite Q] [Nonempty Q] :
    HasFiniteTwoDimensionalClassifyingSpace G :=
  OAI.TorsionFreeZeroDivisors.SplitModel.has_model_oai s w hw hs hker L hL
