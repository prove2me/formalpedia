-- Prove2me | solution 1 for OAI.TorsionFreeZeroDivisors.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:28:22.473127+00:00
-- url     : https://prove2.me/submissions/8ab52946-549b-4204-9180-4c87e59cda79

import Mathlib
import Definitions.Def_TorsionFreeZeroDivisors
import Definitions.Def_TorsionFreeZeroDivisorsConstruction
import Definitions.Def_TFZDCellModule
import Definitions.Def_TFZDTopologyA
import Definitions.Def_TFZDTopologyB
import Theorems.Thm_OAI_TorsionFreeZeroDivisors_SampleGraph_exists_avoiding
import Theorems.Thm_OAI_TorsionFreeZeroDivisors_SampleGraph_SpherePicture_excluded
import Theorems.Thm_OAI_TorsionFreeZeroDivisors_ConeTorsion_graph_torsion_free
import Theorems.Thm_OAI_TorsionFreeZeroDivisors_ConcreteFactors_both_nonzero
import Theorems.Thm_OAI_TorsionFreeZeroDivisors_SplitModel_has_model

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
instance coverT2 : T2Space (Cover s a) :=
  t2Space _ (realSeparated _ (realSeparated_of_tychonoff (Y:=G)))
instance coverCW : CWComplex (Set.univ : Set (Cover s a)) :=
  layerCW _ (Cayley.graph_dimension s)

def diskAttaching : Q→C(Sphere 2,PresentationTopology.Rose s) := fun q=>
  (PresentationTopology.graphProjection s).comp (a q)
abbrev Base := Space (diskAttaching s a)
instance baseT2 : T2Space (Base s a) := t2Space _ (realSeparated _ realSeparated_of_tychonoff)
instance baseCW : CWComplex (Set.univ : Set (Base s a)) :=
  layerCW _ (PresentationTopology.rose_dimension s)
instance basePathConnected : PathConnectedSpace (Base s a) := by
  let := SphereTopology.sphere_nonempty 1
  exact Attachment.pathConnectedSpace _
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
variable (F : C(Disk 2,Y)) (hF : ∀z,F (boundary 2 z)=LoopSphere.map p z)

def shift (t s : unitInterval) : unitInterval :=
  ⟨t+(1-t)*s,by constructor <;> nlinarith [t.2.1,t.2.2,s.2.1,s.2.2]⟩
@[simp] lemma shift_zero (s : unitInterval) : shift 0 s=s := by ext;simp [shift]
@[simp] lemma shift_one (s : unitInterval) : shift 1 s=1 := by ext;simp [shift]
@[simp] lemma shift_zero_right (t : unitInterval) : shift t 0=t := by ext;simp [shift]
@[simp] lemma shift_one_right (t : unitInterval) : shift t 1=1 := by ext;simp [shift]
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
variable (H : f.Homotopy (.const _ y)) (hH : ∀t,H (t,x)=y)
variable (D : C(X,Path y y)) (hD : D x=Path.refl y)
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
end TorsionFreeZeroDivisors.DiskTracks
namespace TorsionFreeZeroDivisors.HomotopyTracks
open GroupRingTopology GroupRingTopology.Attachment
open scoped unitInterval
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y} {f : C(X,Y)} (hx : f x=y)
variable (H : f.Homotopy (.const _ y)) (hH : ∀t,H (t,x)=y)
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
def attaching (i : Q) : C(Sphere 2,Cayley.Graph s) := LoopSphere.map (loop s w hw i)
abbrev Cover := CellPresentation.Cover s (attaching s w hw)
def inclusion : C(Cayley.Graph s,Cover s w hw) := CellPresentation.inclusion s (attaching s w hw)
variable (hs : Function.Surjective (FreeGroup.lift s))
  (hker : (FreeGroup.lift s).ker=Subgroup.normalClosure (Set.range w))
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
variable {G S Y : Type} [_root_.Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace Y] (s : S→G) (f : C(Cayley.Graph s,Y)) (y : Y)
  (hv : ∀g,f (Cayley.vertex s g)=y)
variable [IsMulCommutative (FundamentalGroup Y y)]
local instance : CommGroup (FundamentalGroup Y y) :=
  { (inferInstance : Group (FundamentalGroup Y y)) with mul_comm:=isMulCommutative_iff.mp inferInstance }
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
variable [IsMulCommutative (FundamentalGroup Y y)]
local instance : CommGroup (FundamentalGroup Y y) :=
  { (inferInstance : Group (FundamentalGroup Y y)) with mul_comm:=isMulCommutative_iff.mp inferInstance }
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
local instance : CommGroup (FundamentalGroup (Path y y) (Path.refl y)) :=
  { (inferInstance : Group (FundamentalGroup (Path y y) (Path.refl y))) with
    mul_comm:=LoopTracks.loopGroup_comm y }
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
variable {Y : Type*} [TopologicalSpace Y]
variable (f : C(Disk n,Y)) (H : C(unitInterval × Sphere n,Y))
  (h : ∀x,H (0,x)=f (boundary n x))

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

theorem order_eq : ProjectivePlane.order Point Line = 128 := by
  have h := ProjectivePlane.card_points Point Line
  rw [point_card] at h
  have hi : (16513 : ℤ) = (ProjectivePlane.order Point Line : ℤ) ^ 2 +
      (ProjectivePlane.order Point Line : ℤ) + 1 := by exact_mod_cast h
  have hf : ((ProjectivePlane.order Point Line : ℤ) - 128) *
      ((ProjectivePlane.order Point Line : ℤ) + 129) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h1 | h1 <;> omega

def linesOn (p : Point) : Finset Line := Finset.univ.filter (p ∈ ·)

@[simp] theorem mem_pointsOn {p : Point} {l : Line} : p ∈ pointsOn l ↔ p ∈ l := by
  simp [pointsOn]

@[simp] theorem mem_linesOn {p : Point} {l : Line} : l ∈ linesOn p ↔ p ∈ l := by
  simp [linesOn]

theorem pointsOn_card (l : Line) : (pointsOn l).card = 129 := by
  have h := ProjectivePlane.pointCount_eq Point l
  rw [order_eq] at h
  simpa [pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype, pointsOn] using h

theorem pointsOn_inter_card {l m : Line} (hlm : l ≠ m) :
    (pointsOn l ∩ pointsOn m).card = 1 := by
  obtain ⟨p, hp, hu⟩ := HasPoints.existsUnique_point Point Line l m hlm
  have heq : pointsOn l ∩ pointsOn m = {p} := by
    ext q
    simp only [Finset.mem_inter, mem_pointsOn, Finset.mem_singleton]
    exact ⟨fun hq => hu q hq, fun hq => hq ▸ hp⟩
  rw [heq, Finset.card_singleton]

/-! The empirical type slots. Each line has exactly 33026 slots on each
side, before the admissible replication parameter is applied. -/

theorem disjSum_inter {P E : Type*} [DecidableEq P] [DecidableEq E]
    (a b : Finset P) (c d : Finset E) :
    a.disjSum c ∩ b.disjSum d = (a ∩ b).disjSum (c ∩ d) := by
  ext x
  cases x <;> simp

theorem ordinary_inter_odd (l m : Line) : Odd ((pointsOn l ∩ pointsOn m).card) := by
  by_cases h : l = m
  · subst m
    simp only [Finset.inter_self,pointsOn_card]
    decide
  · rw [pointsOn_inter_card h]
    decide

theorem extras_inter_even (a : SlotA) (b : SlotB) :
    Even ((extrasA a ∩ extrasB b).card) := by
  rcases a with ⟨i,j⟩ | k <;> cases b <;>
    simp [extrasA, extrasB, Finset.card_erase_of_mem]

/-- The parity condition holds on every admissible size, independently of
all edge matchings, exactly as in equation odd-intersections. -/
theorem odd_cross_intersections {N : ℕ} (x : VertexA N) (y : VertexB N) :
    Odd ((outgoingA x ∩ outgoingB y).card) := by
  rw [outgoingA, outgoingB, disjSum_inter, Finset.card_disjSum]
  exact (ordinary_inter_odd x.1 y.1).add_even (extras_inter_even x.2.1 y.2.1)

theorem degreeA_bounds {N : ℕ} (x : VertexA N) :
    129 ≤ (outgoingA x).card ∧ (outgoingA x).card ≤ 132 := by
  rw [outgoingA, Finset.card_disjSum, pointsOn_card]
  rcases x.2.1 with ⟨i,j⟩ | k <;> simp [extrasA, Finset.card_erase_of_mem]

/-! ### The fixed inverse pairing and the actual space of graph matchings -/

@[simp] theorem inverse_signed (g : Generator) (b : Bool) :
    inverse (signedLetter (g,b)) = signedLetter (g,!b) := by simp [inverse]

@[simp] theorem inverse_inverse (t : Letter) : inverse (inverse t) = t := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  simp

theorem inverse_ne (t : Letter) : inverse t ≠ t := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  intro he
  cases b <;> simp only [inverse_signed, Bool.not_true, Bool.not_false] at he <;>
    cases signedLetter.injective he

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

theorem L_tendsto : Tendsto L atTop atTop := by
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ) / 100) atTop atTop := by
    simpa only [div_eq_mul_inv, Function.comp_apply] using
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_mul_const
        (by norm_num : (0 : ℝ) < (100 : ℝ)⁻¹)
  exact tendsto_nat_floor_atTop.comp hl

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

theorem size_tendsto : Tendsto size atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => n) _ tendsto_id
  intro n
  dsimp [size]
  omega

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
lemma label_reverse (d : DA rep⊕DB rep) : label rep ((graph rep r).reverse d)=Types.inverse (label rep d) := by
  cases d with
  | inl d => exact r.1.label_reverse d
  | inr d => exact r.2.label_reverse d
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
omit [Fintype O] in
lemma cycle_surjective : Function.Surjective (cycle f) := Quotient.mk_surjective

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
lemma apply_fin (t : T) (i : Fin (len t)) :
    perm len ((fin len).symm ⟨t,i⟩)=(fin len).symm ⟨t,finRotate (len t) i⟩ := by
  simp only [perm,Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply,
    Equiv.sigmaCongrRight_apply]
lemma pow_fin (t : T) (i : Fin (len t)) (n : ℕ) :
    (perm len^n) ((fin len).symm ⟨t,i⟩)=(fin len).symm ⟨t,(finRotate (len t)^n) i⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,ih,apply_fin,pow_succ',Equiv.Perm.mul_apply]
lemma first (x : Position len) : (perm len x).1=x.1 := by
  rw [←(fin len).symm_apply_apply x]
  exact rfl
lemma finRotate_same {n : ℕ} (i j : Fin n) : (finRotate n).SameCycle i j := by
  by_cases hn : 2≤n
  · apply Equiv.Perm.IsCycle.sameCycle (isCycle_finRotate_of_le hn)
    · have hm : i∈(finRotate n).support := by rw [support_finRotate_of_le hn]; exact Finset.mem_univ _
      exact Equiv.Perm.mem_support.mp hm
    · have hm : j∈(finRotate n).support := by rw [support_finRotate_of_le hn]; exact Finset.mem_univ _
      exact Equiv.Perm.mem_support.mp hm
  · have he : i=j := by apply Fin.ext; omega
    exact he.sameCycle _
lemma same_first {x y : Position len} (h : x.1=y.1) : (perm len).SameCycle x y := by
  rcases x with ⟨a',i'⟩
  rcases y with ⟨b',j'⟩
  dsimp at h
  subst b'
  let u : Fin (len a') := ⟨i'.val.toNat,by have hb:=bounds i'; omega⟩
  let v : Fin (len a') := ⟨j'.val.toNat,by have hb:=bounds j'; omega⟩
  obtain ⟨n,hn⟩ := (finRotate_same u v).exists_nat_pow_eq
  refine ⟨(n:ℤ),?_⟩
  rw [zpow_natCast]
  have hh := pow_fin len a' u n
  rw [hn] at hh
  change (perm len^n) ((fin len).symm (fin len ⟨a',i'⟩))=(fin len).symm (fin len ⟨a',j'⟩) at hh
  simpa only [Equiv.symm_apply_apply] using hh
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
lemma pow_apply (x : A) (n : ℕ) : (e.permCongr f^n) (e x)=e ((f^n) x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Equiv.Perm.mul_apply,ih,Equiv.permCongr_apply,Equiv.symm_apply_apply]
lemma sameCycle [Finite A] {x y : A} (h : f.SameCycle x y) : (e.permCongr f).SameCycle (e x) (e y) := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  exact ⟨(n:ℤ),by rw [zpow_natCast,pow_apply,hn]⟩
lemma involutive (h : Function.Involutive f) : Function.Involutive (e.permCongr f) := by
  intro x
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  rw [h,Equiv.apply_symm_apply]
lemma fixed_free (h : ∀x,f x≠x) (x : B) : e.permCongr f x≠x := by
  intro he
  apply h (e.symm x)
  simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using congrArg e.symm he
lemma mul (g : Equiv.Perm A) : e.permCongr (f*g)=e.permCongr f*e.permCongr g := by
  ext x
  simp only [Equiv.Perm.mul_apply,Equiv.permCongr_apply,Equiv.symm_apply_apply]
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
lemma sameCycle_iff (x y : A) : f.SameCycle x y ↔ (e.permCongr f).SameCycle (e x) (e y) := by
  refine ⟨sameCycle e f,?_⟩
  intro h
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  refine ⟨(n:ℤ),?_⟩
  rw [zpow_natCast]
  apply e.injective
  rwa [pow_apply] at hn
def cycles : Cycle f ≃ Cycle (e.permCongr f) := Quotient.congr e (sameCycle_iff e f)
lemma card_cycles : Fintype.card (Cycle (e.permCongr f))=Fintype.card (Cycle f) :=
  (Fintype.card_congr (cycles e f)).symm
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
lemma U_ge : 3≤U ε D := le_max_left _ _
lemma U_pos : 0<U ε D := lt_of_lt_of_le (by norm_num) (U_ge ε D)
lemma K_pos : 0<K ε D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
lemma C_pos : 0<C ε D := Nat.mul_pos (K_pos ε D) (Nat.add_pos_left (U_pos ε D) _)
lemma sides_pos : 0<sides ε D := by
  unfold sides C₂
  exact Nat.mul_pos (by norm_num) (C_pos ε D)

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
lemma lift_surjective (q : O → B) (hq : ∀x,q (f x)=q x) (hs : Function.Surjective q) :
    Function.Surjective (lift f q hq) := by
  intro b
  obtain ⟨x,rfl⟩ := hs b
  exact ⟨cycle f x,rfl⟩
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
lemma rotation_left (i : O) (hi : i≠p) : rotation σ p (.inl i)=.inl (σ i) := by
  simp [rotation,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne,hi]
@[simp] lemma rotation_p : rotation σ p (.inl p)=.inr false := by
  simp [rotation,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
@[simp] lemma rotation_false : rotation σ p (.inr false)=.inr true := by
  simp [rotation,Equiv.Perm.mul_apply]
@[simp] lemma rotation_true : rotation σ p (.inr true)=.inl (σ p) := by
  simp [rotation,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
lemma face_left (i : O) (hi : i≠p) : face σ α p (.inl i)=.inl ((α*σ) i) := by
  simp only [face,Equiv.Perm.mul_apply,rotation_left σ p i hi,pairing,Equiv.sumCongr_apply,Sum.map_inl]
@[simp] lemma face_p : face σ α p (.inl p)=.inr true := by
  simp [face,Equiv.Perm.mul_apply,pairing]
@[simp] lemma face_false : face σ α p (.inr false)=.inr false := by
  simp [face,Equiv.Perm.mul_apply,pairing]
@[simp] lemma face_true : face σ α p (.inr true)=.inl ((α*σ) p) := by
  simp [face,Equiv.Perm.mul_apply,pairing]

def classify : O⊕Bool → Option (Cycle (α*σ))
  | .inl i => some (cycle _ i)
  | .inr false => none
  | .inr true => some (cycle _ p)
lemma classify_invariant (i : O⊕Bool) : classify σ α p (face σ α p i)=classify σ α p i := by
  cases i with
  | inl i =>
    by_cases he : i=p
    · subst i; rw [face_p]; rfl
    · rw [face_left σ α p i he]
      simp only [classify,cycle_apply]
  | inr b => cases b <;> simp only [face_false,face_true,classify,cycle_apply]
lemma classify_surjective : Function.Surjective (classify σ α p) := by
  intro b
  cases b with
  | none => exact ⟨.inr false,rfl⟩
  | some c =>
    obtain ⟨i,rfl⟩ := cycle_surjective (α*σ) c
    exact ⟨.inl i,rfl⟩
variable [Fintype O]
/-- Inserting an ear creates a new face and retains all old face cycles. -/
theorem face_count : Fintype.card (Cycle (α*σ))+1≤Fintype.card (Cycle (face σ α p)) := by
  have h := Fintype.card_le_of_surjective _ (lift_surjective (face σ α p)
    (classify σ α p) (classify_invariant σ α p) (classify_surjective σ α p))
  simpa only [Fintype.card_option] using h

end TorsionFreeZeroDivisors.InsertedRotation

namespace TorsionFreeZeroDivisors.SwapCycles

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)
abbrev Away := {c : Cycle f // c≠cycle f p ∧ c≠cycle f q}
def classify (x : O) : Option (Away f p q) :=
  if h : cycle f x≠cycle f p ∧ cycle f x≠cycle f q then some ⟨cycle f x,h⟩ else none
lemma classify_apply (x : O) : classify f p q (f x)=classify f p q x := by
  simp only [classify,cycle_apply]
@[simp] lemma classify_p : classify f p q p=none := by simp [classify]
@[simp] lemma classify_q : classify f p q q=none := by simp [classify]
lemma classify_swap (x : O) : classify f p q (Equiv.swap p q x)=classify f p q x := by
  by_cases hp : x=p
  · subst x; simp
  · by_cases hq : x=q
    · subst x; simp
    · rw [Equiv.swap_apply_of_ne_of_ne hp hq]
lemma invariant (x : O) : classify f p q ((Equiv.swap p q*f) x)=classify f p q x := by
  rw [Equiv.Perm.mul_apply,classify_swap,classify_apply]
lemma surjective : Function.Surjective (classify f p q) := by
  intro b
  cases b with
  | none => exact ⟨p,classify_p f p q⟩
  | some c =>
    obtain ⟨x,hx⟩ := cycle_surjective f c.val
    refine ⟨x,?_⟩
    have h : cycle f x≠cycle f p ∧ cycle f x≠cycle f q := hx ▸ c.property
    rw [classify,dif_pos h]
    exact congrArg some (Subtype.ext hx)
variable [Fintype O]
lemma lower : Fintype.card (Away f p q)+1≤Fintype.card (Cycle (Equiv.swap p q*f)) := by
  have h := Fintype.card_le_of_surjective _ (lift_surjective (Equiv.swap p q*f)
    (classify f p q) (invariant f p q) (surjective f p q))
  simpa only [Fintype.card_option] using h
lemma away_count : Fintype.card (Cycle f)≤Fintype.card (Away f p q)+2 := by
  let rest : Finset (Cycle f) := Finset.univ.filter (fun c=>c≠cycle f p ∧ c≠cycle f q)
  have hs : (Finset.univ : Finset (Cycle f))⊆rest∪{cycle f p,cycle f q} := by
    intro c _
    by_cases h : c≠cycle f p ∧ c≠cycle f q
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    · apply Finset.mem_union_right
      simp only [Finset.mem_insert,Finset.mem_singleton]
      tauto
  have h := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hr : rest.card=Fintype.card (Away f p q) := by
    simp [rest,Fintype.card_subtype]
  rw [Finset.card_univ,hr] at h
  exact h.trans (Nat.add_le_add_left (Finset.card_insert_le _ _) _)
/-- A two-endpoint switch loses at most one permutation cycle. -/
theorem count_le : Fintype.card (Cycle f)≤Fintype.card (Cycle (Equiv.swap p q*f))+1 := by
  have h₁ := lower f p q
  have h₂ := away_count f p q
  omega

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)
lemma cycle_swap (h : cycle f p=cycle f q) (x : O) :
    cycle f (Equiv.swap p q x)=cycle f x := by
  by_cases hp : x=p
  · subst x; simpa using h.symm
  · by_cases hq : x=q
    · subst x; simpa using h
    · rw [Equiv.swap_apply_of_ne_of_ne hp hq]

def adjacentClass (x : O) : Option (Cycle f) := if x=p then none else some (cycle f x)
lemma adjacent_fixed : (Equiv.swap p (f p)*f) p=p := by simp
lemma adjacentClass_invariant (x : O) :
    adjacentClass f p ((Equiv.swap p (f p)*f) x)=adjacentClass f p x := by
  by_cases hx : x=p
  · subst x; rw [adjacent_fixed]
  · have hg : (Equiv.swap p (f p)*f) x≠p := by
      intro h
      exact hx ((Equiv.swap p (f p)*f).injective (h.trans (adjacent_fixed f p).symm))
    rw [adjacentClass,if_neg hg,adjacentClass,if_neg hx]
    apply congrArg some
    rw [Equiv.Perm.mul_apply,cycle_swap f p (f p) (cycle_apply f p).symm,cycle_apply]
lemma adjacentClass_surjective (hp : f p≠p) : Function.Surjective (adjacentClass f p) := by
  intro c
  cases c with
  | none => exact ⟨p,by simp [adjacentClass]⟩
  | some c =>
    obtain ⟨x,rfl⟩ := cycle_surjective f c
    by_cases hx : x=p
    · subst x
      exact ⟨f p,by simp [adjacentClass,hp]⟩
    · exact ⟨x,by simp [adjacentClass,hx]⟩

variable [Fintype O]
lemma count_reverse : Fintype.card (Cycle (Equiv.swap p q*f))≤Fintype.card (Cycle f)+1 := by
  simpa only [←mul_assoc,Equiv.swap_mul_self,one_mul] using count_le (Equiv.swap p q*f) p q
/-- Switching the two arrows adjacent to a nonfixed point splits off that point
as one new actual cycle. -/
lemma adjacent_count (hp : f p≠p) :
    Fintype.card (Cycle (Equiv.swap p (f p)*f))=Fintype.card (Cycle f)+1 := by
  have h := Fintype.card_le_of_surjective _ (lift_surjective (Equiv.swap p (f p)*f)
    (adjacentClass f p) (adjacentClass_invariant f p) (adjacentClass_surjective f p hp))
  simp only [Fintype.card_option] at h
  exact Nat.le_antisymm (count_reverse f p (f p)) h
lemma adjacent_support (hp : f p≠p) :
    (Equiv.swap p (f p)*f).support.card<f.support.card := by
  have hs : (Equiv.swap p (f p)*f).support⊆f.support.erase p := by
    intro x hx
    simp only [Finset.mem_erase,Equiv.Perm.mem_support] at *
    refine ⟨?_,?_⟩
    · intro he; subst x; exact hx (adjacent_fixed f p)
    · intro he
      have hxp : x≠p := by intro h; subst x; exact hp he
      have hxf : x≠f p := by
        intro h
        have he' : f x=f p := he.trans h
        exact hxp (f.injective he')
      exact hx (by simp [Equiv.Perm.mul_apply,he,Equiv.swap_apply_of_ne_of_ne hxp hxf])
  exact (Finset.card_le_card hs).trans_lt (Finset.card_erase_lt_of_mem (Equiv.Perm.mem_support.mpr hp))

lemma away_same (h : cycle f p=cycle f q) :
    Fintype.card (Cycle f)≤Fintype.card (Away f p q)+1 := by
  let rest : Finset (Cycle f) := Finset.univ.filter (fun c=>c≠cycle f p ∧ c≠cycle f q)
  have hs : (Finset.univ : Finset (Cycle f))⊆rest∪{cycle f p} := by
    intro c _
    by_cases hc : c=cycle f p
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hc)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,by rwa [←h]⟩)
  have hh := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hr : rest.card=Fintype.card (Away f p q) := by simp [rest,Fintype.card_subtype]
  simpa [hr] using hh
lemma same_monotone (h : cycle f p=cycle f q) :
    Fintype.card (Cycle f)≤Fintype.card (Cycle (Equiv.swap p q*f)) :=
  (away_same f p q h).trans (lower f p q)

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]
lemma identity_count : Fintype.card (Cycle (1 : Equiv.Perm O))=Fintype.card O := by
  apply (Fintype.card_of_bijective (f:=cycle (1 : Equiv.Perm O)) ?_).symm
  refine ⟨?_,cycle_surjective _⟩
  intro x y h
  exact ((cycle_eq _).mp h).eq_of_left rfl
/-- The ordinary permutation sign in terms of all cycles, including fixed points. -/
lemma sign_formula (f : Equiv.Perm O) :
    Equiv.Perm.sign f=(-1 : ℤˣ)^(Fintype.card O+Fintype.card (Cycle f)) := by
  have aux : ∀m,∀g : Equiv.Perm O,g.support.card=m →
      Equiv.Perm.sign g=(-1 : ℤˣ)^(Fintype.card O+Fintype.card (Cycle g)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro g hg
      by_cases he : g=1
      · subst g
        rw [Equiv.Perm.sign_one,identity_count,←two_mul,pow_mul]
        norm_num
      · obtain ⟨p,hp⟩ : ∃p,g p≠p := by
          by_contra! h
          exact he (Equiv.ext h)
        have hsmall := adjacent_support g p hp
        have hh := ih (Equiv.swap p (g p)*g).support.card (hg ▸ hsmall)
          (Equiv.swap p (g p)*g) rfl
        rw [Equiv.Perm.sign_mul,Equiv.Perm.sign_swap hp.symm,adjacent_count g p hp,
          ←Nat.add_assoc,pow_succ,mul_comm] at hh
        exact mul_right_cancel hh
  exact aux f.support.card f rfl

/-- A switch between distinct positions of one cycle splits it in two. -/
theorem split_count (f : Equiv.Perm O) (p q : O) (hpq : p≠q)
    (h : cycle f p=cycle f q) :
    Fintype.card (Cycle (Equiv.swap p q*f))=Fintype.card (Cycle f)+1 := by
  have hlo := same_monotone f p q h
  have hhi := count_reverse f p q
  have hne : Fintype.card (Cycle (Equiv.swap p q*f))≠Fintype.card (Cycle f) := by
    intro he
    have hs : Equiv.Perm.sign (Equiv.swap p q*f)=Equiv.Perm.sign f := by
      rw [sign_formula,sign_formula,he]
    rw [Equiv.Perm.sign_mul,Equiv.Perm.sign_swap hpq] at hs
    have hn : (-1 : ℤˣ)=1 := mul_right_cancel (hs.trans (one_mul _).symm)
    norm_num at hn
  omega

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O)
end

open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (f : Equiv.Perm O) (p q : O)
/-- Switching two distinct cycles joins the two selected positions in one
actual new cycle. The witness follows the old cycle up to its first return. -/
lemma merge_same (h : cycle f p≠cycle f q) :
    (Equiv.swap p q*f).SameCycle p q := by
  have hp : ∃n : ℕ,0<n ∧ (f^n) p=p :=
    ⟨orderOf f,orderOf_pos f,by rw [pow_orderOf_eq_one];rfl⟩
  let n := Nat.find hp
  have hn : 0<n ∧ (f^n) p=p := Nat.find_spec hp
  have hmin : ∀k,0<k → k<n → (f^k) p≠p := by
    intro k hk hkn he
    have hh := Nat.find_min' hp ⟨hk,he⟩
    omega
  have no_q (k : ℕ) : (f^k) p≠q := by
    intro he
    exact h ((cycle_eq f).mpr ⟨(k:ℤ),by simpa only [zpow_natCast] using he⟩)
  have heq : ∀k,k<n → ((Equiv.swap p q*f)^k) p=(f^k) p := by
    intro k
    induction k with
    | zero => intro _;rfl
    | succ k ih =>
      intro hk
      rw [pow_succ',Equiv.Perm.mul_apply,ih (by omega),Equiv.Perm.mul_apply]
      have hf : f ((f^k) p)=(f^(k+1)) p := by rw [pow_succ',Equiv.Perm.mul_apply]
      rw [hf,Equiv.swap_apply_of_ne_of_ne (hmin _ (by omega) hk) (no_q _)]
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  refine ⟨(n:ℤ),?_⟩
  rw [zpow_natCast,hm,pow_succ',Equiv.Perm.mul_apply,heq m (by omega),Equiv.Perm.mul_apply]
  have he : f ((f^m) p)=p := by
    rw [←Equiv.Perm.mul_apply,←pow_succ']
    simpa only [hm, Nat.succ_eq_add_one] using hn.2
  rw [he,Equiv.swap_apply_left]

lemma merge_count (h : cycle f p≠cycle f q) :
    Fintype.card (Cycle (Equiv.swap p q*f))+1=Fintype.card (Cycle f) := by
  have hpq : p≠q := by intro he;exact h (he ▸ rfl)
  have hh := split_count (Equiv.swap p q*f) p q hpq ((cycle_eq _).mpr (merge_same f p q h))
  simpa only [←mul_assoc,Equiv.swap_mul_self,one_mul] using hh.symm
end TorsionFreeZeroDivisors.SwapCycles

namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles SwapCycles
variable {O : Type} [Fintype O]

def Refines (f g : Equiv.Perm O) : Prop := ∀x y,cycle f x=cycle f y → cycle g x=cycle g y
lemma refines_of_invariant (f g : Equiv.Perm O) (h : ∀x,cycle g (f x)=cycle g x) : Refines f g := by
  intro x y hxy
  exact congrArg (lift f (cycle g) h) hxy

lemma merge_refines (f : Equiv.Perm O) (p q : O) (h : cycle f p≠cycle f q) :
    Refines f (Equiv.swap p q*f) := by
  apply refines_of_invariant
  intro x
  have hs : cycle (Equiv.swap p q*f) p=cycle (Equiv.swap p q*f) q :=
    (cycle_eq _).mpr (merge_same f p q h)
  calc
    cycle (Equiv.swap p q*f) (f x)=cycle (Equiv.swap p q*f) (Equiv.swap p q ((Equiv.swap p q*f) x)) := by simp
    _ = cycle (Equiv.swap p q*f) ((Equiv.swap p q*f) x) := cycle_swap _ p q hs _
    _ = cycle (Equiv.swap p q*f) x := cycle_apply _ _

def merge (f : Equiv.Perm O) (p q : O) : Equiv.Perm O :=
  if cycle f p=cycle f q then f else Equiv.swap p q*f
lemma merge_refines' (f : Equiv.Perm O) (p q : O) : Refines f (merge f p q) := by
  by_cases h : cycle f p=cycle f q
  · simp only [merge,if_pos h];exact fun _ _ h=>h
  · simp only [merge,if_neg h];exact merge_refines f p q h
lemma merge_pair (f : Equiv.Perm O) (p q : O) : cycle (merge f p q) p=cycle (merge f p q) q := by
  by_cases h : cycle f p=cycle f q
  · rw [merge,if_pos h]; exact h
  · rw [merge,if_neg h]; exact (cycle_eq _).mpr (merge_same f p q h)

def forest (σ : Equiv.Perm O) : List (O×O) → Equiv.Perm O
  | []=>σ
  | e::l=>merge (forest σ l) e.1 e.2
def face (σ : Equiv.Perm O) : List (O×O) → Equiv.Perm O
  | []=>σ
  | e::l=>Equiv.swap e.1 e.2*face σ l
lemma face_invariant (σ : Equiv.Perm O) (l : List (O×O)) (x : O) :
    cycle (forest σ l) (face σ l x)=cycle (forest σ l) x := by
  induction l with
  | nil=>exact cycle_apply σ x
  | cons e l ih=>
    change cycle (merge (forest σ l) e.1 e.2) (Equiv.swap e.1 e.2 (face σ l x))=_
    rw [cycle_swap _ _ _ (merge_pair _ _ _)]
    exact merge_refines' _ _ _ _ _ ih
lemma face_refines (σ : Equiv.Perm O) (l : List (O×O)) : Refines (face σ l) (forest σ l) :=
  refines_of_invariant _ _ (face_invariant σ l)

/-- Euler's upper bound for the actual component partition formed by gluing
listed bands. The forest permutation is a computed partition, not a planar input. -/
theorem upper (σ : Equiv.Perm O) (l : List (O×O)) :
    Nat.card (Cycle σ)+Nat.card (Cycle (face σ l))≤
      l.length+2*Nat.card (Cycle (forest σ l)) := by
  induction l with
  | nil=>simp only [face,forest,List.length_nil];omega
  | cons e l ih=>
    by_cases h : cycle (forest σ l) e.1=cycle (forest σ l) e.2
    · have hf := count_reverse (face σ l) e.1 e.2
      simp only [face,forest,merge,if_pos h,List.length_cons]
      simp only [←Nat.card_eq_fintype_card] at *
      omega
    · have hc := merge_count (forest σ l) e.1 e.2 h
      have hn : cycle (face σ l) e.1≠cycle (face σ l) e.2 := fun hh=>h (face_refines σ l _ _ hh)
      have hf := merge_count (face σ l) e.1 e.2 hn
      simp only [face,forest,merge,if_neg h,List.length_cons]
      simp only [←Nat.card_eq_fintype_card] at *
      omega
lemma forest_refines (σ : Equiv.Perm O) (l : List (O×O)) : Refines σ (forest σ l) := by
  induction l with
  | nil=>exact fun _ _ h=>h
  | cons e l ih=>exact fun x y h=>merge_refines' (forest σ l) e.1 e.2 x y (ih x y h)
lemma forest_pair (σ : Equiv.Perm O) (l : List (O×O)) (e : O×O) (he : e∈l) :
    cycle (forest σ l) e.1=cycle (forest σ l) e.2 := by
  induction l with
  | nil=>simp at he
  | cons a l ih=>
    rcases List.mem_cons.mp he with rfl|he
    · exact merge_pair _ _ _
    · exact merge_refines' _ _ _ _ _ (ih he)

omit [Fintype O] in
lemma invariant_forest {B : Type} (σ : Equiv.Perm O) (l : List (O×O)) (q : O→B)
    (hσ : ∀x,q (σ x)=q x) (hl : ∀e∈l,q e.1=q e.2) : ∀x,q (forest σ l x)=q x := by
  induction l with
  | nil=>exact hσ
  | cons e l ih=>
    have he := hl e (List.mem_cons_self)
    have hi := ih (fun a ha=>hl a (List.mem_cons_of_mem _ ha))
    intro x
    change q (merge (forest σ l) e.1 e.2 x)=q x
    dsimp only [merge]
    split
    · exact hi x
    · change q (Equiv.swap e.1 e.2 (forest σ l x))=q x
      have hs : ∀z,q (Equiv.swap e.1 e.2 z)=q z := by
        intro z
        by_cases hz : z=e.1
        · subst z;rw [Equiv.swap_apply_left];exact he.symm
        · by_cases hz' : z=e.2
          · subst z;rw [Equiv.swap_apply_right];exact he
          · rw [Equiv.swap_apply_of_ne_of_ne hz hz']
      rw [hs,hi]
end TorsionFreeZeroDivisors.ComponentEuler

namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
def strip : Equiv.Perm O := Equiv.swap p (α p)*α
omit [Fintype O] in
lemma strip_p : strip α p p=p := by simp [strip]
omit [Fintype O] in
include hi in
lemma strip_q : strip α p (α p)=α p := by simp only [strip,Equiv.Perm.mul_apply,hi p,Equiv.swap_apply_left]
omit [Fintype O] in
include hi in
lemma strip_away (x : O) (hp : x≠p) (hq : x≠α p) : strip α p x=α x := by
  have hxp : α x≠p := by intro h;exact hq ((hi x).symm.trans (congrArg α h))
  have hxq : α x≠α p := α.injective.ne hp
  exact Equiv.swap_apply_of_ne_of_ne hxp hxq
omit [Fintype O] in
include hi in
lemma strip_involutive : Function.Involutive (strip α p) := by
  intro x
  by_cases hp : x=p
  · subst x;rw [strip_p,strip_p]
  · by_cases hq : x=α p
    · subst x;rw [strip_q α hi p,strip_q α hi p]
    · rw [strip_away α hi p x hp hq,strip_away α hi p (α x)]
      · exact hi x
      · intro h;exact hq ((hi x).symm.trans (congrArg α h))
      · exact α.injective.ne hp
include hi in
lemma strip_support : (strip α p).support=α.support\{p,α p} := by
  ext x
  simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,not_or,Equiv.Perm.mem_support]
  constructor
  · intro h
    have hp : x≠p := by intro he;subst x;exact h (strip_p α p)
    have hq : x≠α p := by intro he;subst x;exact h (strip_q α hi p)
    exact ⟨by rwa [strip_away α hi p x hp hq] at h,hp,hq⟩
  · rintro ⟨h,hp,hq⟩
    rwa [strip_away α hi p x hp hq]
include hi in
lemma strip_card (hp : α p≠p) : (strip α p).support.card+2=α.support.card := by
  rw [strip_support α hi p,Finset.card_sdiff_of_subset]
  · have hc : ({p,α p} : Finset O).card=2 := by simp [Ne.symm hp]
    have hs : {p,α p}⊆α.support := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact Equiv.Perm.mem_support.mpr hp
      · exact Equiv.Perm.mem_support.mpr (by rw [hi];exact Ne.symm hp)
    have hh := Finset.card_le_card hs
    rw [hc] at *
    omega
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact Equiv.Perm.mem_support.mpr hp
    · exact Equiv.Perm.mem_support.mpr (by rw [hi];exact Ne.symm hp)

include hi in
/-- Every finite involution is literally a product of its own nontrivial
paired-edge swaps, with exactly one factor for each pair. -/
theorem factorization : ∃l : List (O×O),
    (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α ∧
      2*l.length=α.support.card ∧ ∀e∈l,e.1≠e.2 ∧ α e.1=e.2 := by
  generalize hn : α.support.card=n
  induction n using Nat.strong_induction_on generalizing α with
  | h n ih=>
    by_cases hn0 : n=0
    · have hs : α.support=∅ := Finset.card_eq_zero.mp (hn.trans hn0)
      have ha : α=1 := Equiv.Perm.support_eq_empty_iff.mp hs
      refine ⟨[],?_,by simp [←hn,hs],by simp⟩
      simpa using ha.symm
    · obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<α.support.card)
      have hp' := Equiv.Perm.mem_support.mp hp
      have hc := strip_card α hi p hp'
      obtain ⟨l,hl,hL,hedge⟩ := ih (strip α p).support.card (by omega)
        (strip α p) (strip_involutive α hi p) rfl
      refine ⟨(p,α p)::l,?_,?_,?_⟩
      · simp only [List.map_cons,List.prod_cons,hl,strip]
        rw [←mul_assoc,Equiv.swap_mul_self,one_mul]
      · simp only [List.length_cons]
        omega
      · intro e he
        rcases List.mem_cons.mp he with rfl|he
        · exact ⟨Ne.symm hp',rfl⟩
        · obtain ⟨hne,heq⟩ := hedge e he
          have hep : e.1≠p := by
            intro hh
            have hy : e.2=p := (heq.symm.trans (congrArg (strip α p) hh)).trans (strip_p α p)
            exact hne (hh.trans hy.symm)
          have heq' : e.1≠α p := by
            intro hh
            have hy : e.2=α p := (heq.symm.trans (congrArg (strip α p) hh)).trans (strip_q α hi p)
            exact hne (hh.trans hy.symm)
          exact ⟨hne,(strip_away α hi p e.1 hep heq').symm.trans heq⟩
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O]
omit [Fintype O] in
lemma product_invariant {B : Type} (l : List (O×O)) (q : O→B)
    (hl : ∀e∈l,q e.1=q e.2) (x : O) :
    q ((l.map (fun e=>Equiv.swap e.1 e.2)).prod x)=q x := by
  induction l with
  | nil=>rfl
  | cons e l ih=>
    have he := hl e List.mem_cons_self
    have hi := ih (fun a ha=>hl a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
    have hs : ∀z,q (Equiv.swap e.1 e.2 z)=q z := by
      intro z
      by_cases hz : z=e.1
      · subst z;rw [Equiv.swap_apply_left];exact he.symm
      · by_cases hz' : z=e.2
        · subst z;rw [Equiv.swap_apply_right];exact he
        · rw [Equiv.swap_apply_of_ne_of_ne hz hz']
    rw [hs,hi]
omit [Fintype O] in
lemma face_product (σ : Equiv.Perm O) (l : List (O×O)) :
    face σ l=(l.map (fun e=>Equiv.swap e.1 e.2)).prod*σ := by
  induction l with
  | nil=>simp [face]
  | cons e l ih=>simp only [face,List.map_cons,List.prod_cons,ih,mul_assoc]
def component (σ α : Equiv.Perm O) (x : O) : Component σ α := Quotient.mk _ x
variable (σ α : Equiv.Perm O) (l : List (O×O))
    (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
    (he : ∀e∈l,α e.1=e.2)
omit [Fintype O] in
include he in
lemma component_forest (x : O) : component σ α (forest σ l x)=component σ α x := by
  apply invariant_forest σ l
  · intro y
    exact Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl)))
  · intro e h
    exact Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr (he e h)))
include hl in
lemma forest_alpha (x : O) : cycle (forest σ l) (α x)=cycle (forest σ l) x := by
  rw [←hl]
  exact product_invariant l (cycle (forest σ l)) (forest_pair σ l) x
include hl in
lemma forest_component {x y : O} (h : component σ α x=component σ α y) :
    cycle (forest σ l) x=cycle (forest σ l) y := by
  have hxy : Relation.EqvGen (Edge σ α) x y := Quotient.exact h
  clear h
  induction hxy with
  | rel x y h=>
    rcases h with h|h
    · exact forest_refines σ l x y (by rw [←h,cycle_apply])
    · rw [←h,forest_alpha σ α l hl]
  | refl=>rfl
  | symm _ _ _ ih=>exact ih.symm
  | trans _ _ _ _ _ ih ih'=>exact ih.trans ih'

def componentEquiv : Cycle (forest σ l) ≃ Component σ α :=
  Equiv.ofBijective (lift (forest σ l) (component σ α) (component_forest σ α l he)) ⟨by
    intro a b hh
    obtain ⟨x,rfl⟩ := cycle_surjective (forest σ l) a
    obtain ⟨y,rfl⟩ := cycle_surjective (forest σ l) b
    exact forest_component σ α l hl hh,
    lift_surjective _ _ _ Quotient.mk_surjective⟩
include hl he in
lemma upper_factors : Nat.card (Cycle σ)+Nat.card (Cycle (α*σ))≤l.length+2*Nat.card (Component σ α) := by
  have hh := upper σ l
  rw [face_product,hl,Nat.card_congr (componentEquiv σ α l hl he)] at hh
  exact hh

/-- Every finite orientable permutation map obeys the Euler upper bound. This
uses only its actual involution and actual connected-component equivalence;
no topological realization or Euler inequality is assumed. -/
theorem upper (hi : Function.Involutive α) :
    2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))≤α.support.card+4*Nat.card (Component σ α) := by
  obtain ⟨l,hl,hL,he⟩ := PairingFactors.factorization α hi
  have hh := upper_factors σ α l hl (fun e h=>(he e h).2)
  omega
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles SwapCycles
variable {O : Type} [Fintype O]
/-- A handle is precisely an edge whose endpoints are already in one component
but which merges two distinct face cycles when glued. -/
def handles (σ : Equiv.Perm O) : List (O×O) → ℕ
  | []=>0
  | e::l=>handles σ l+if cycle (forest σ l) e.1=cycle (forest σ l) e.2 ∧
      cycle (face σ l) e.1≠cycle (face σ l) e.2 then 1 else 0
omit [Fintype O] in
lemma handles_tail (σ : Equiv.Perm O) (e : O×O) (l : List (O×O)) : handles σ l≤handles σ (e::l) := by
  simp only [handles];omega
lemma handles_exact (σ : Equiv.Perm O) (l : List (O×O)) (hd : ∀e∈l,e.1≠e.2) :
    Nat.card (Cycle σ)+Nat.card (Cycle (face σ l))+2*handles σ l=
      l.length+2*Nat.card (Cycle (forest σ l)) := by
  induction l with
  | nil=>simp only [face,forest,handles,List.length_nil];omega
  | cons e l ih=>
    have he := hd e List.mem_cons_self
    have hh := ih (fun a ha=>hd a (List.mem_cons_of_mem _ ha))
    by_cases hc : cycle (forest σ l) e.1=cycle (forest σ l) e.2
    · by_cases hf : cycle (face σ l) e.1=cycle (face σ l) e.2
      · have hg := split_count (face σ l) e.1 e.2 he hf
        simp only [←Nat.card_eq_fintype_card] at hg
        have hn : ¬(cycle (forest σ l) e.1=cycle (forest σ l) e.2 ∧
            cycle (face σ l) e.1≠cycle (face σ l) e.2) := fun h=>h.2 hf
        simp only [face,forest,merge,if_pos hc,handles,if_neg hn,List.length_cons]
        omega
      · have hg := merge_count (face σ l) e.1 e.2 hf
        simp only [←Nat.card_eq_fintype_card] at hg
        simp only [face,forest,merge,if_pos hc,handles,if_pos (And.intro hc hf),List.length_cons]
        omega
    · have hn : cycle (face σ l) e.1≠cycle (face σ l) e.2 := fun hh=>hc (face_refines σ l _ _ hh)
      have hg := merge_count (face σ l) e.1 e.2 hn
      have hj := merge_count (forest σ l) e.1 e.2 hc
      simp only [←Nat.card_eq_fintype_card] at hg hj
      have hn' : ¬(cycle (forest σ l) e.1=cycle (forest σ l) e.2 ∧
          cycle (face σ l) e.1≠cycle (face σ l) e.2) := fun h=>hc h.1
      simp only [face,forest,merge,if_neg hc,handles,if_neg hn',List.length_cons]
      omega
end TorsionFreeZeroDivisors.ComponentEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
lemma genusZero_of_lower (hi : Function.Involutive α)
    (h : α.support.card+4*Nat.card (Component σ α)≤2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))) :
    GenusZero σ α := Nat.le_antisymm h (upper σ α hi) |>.symm
lemma genusZero_iff_handles (l : List (O×O))
    (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
    (hd : ∀e∈l,e.1≠e.2 ∧ α e.1=e.2) (hL : 2*l.length=α.support.card) :
    GenusZero σ α ↔ handles σ l=0 := by
  have hh := handles_exact σ l (fun e he=>(hd e he).1)
  rw [face_product,hl,Nat.card_congr (componentEquiv σ α l hl (fun e he=>(hd e he).2))] at hh
  dsimp only [GenusZero]
  omega
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
include hi in
lemma strip_edge {x y : O} (hne : x≠y) (he : strip α p x=y) : α x=y := by
  have hxp : x≠p := by
    intro hx
    have hy : y=p := (he.symm.trans (congrArg (strip α p) hx)).trans (strip_p α p)
    exact hne (hx.trans hy.symm)
  have hxq : x≠α p := by
    intro hx
    have hy : y=α p := (he.symm.trans (congrArg (strip α p) hx)).trans (strip_q α hi p)
    exact hne (hx.trans hy.symm)
  exact (strip_away α hi p x hxp hxq).symm.trans he
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler PairingFactors
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
include hi in
/-- Deleting an actual paired edge cannot create a handle in any component. -/
lemma genusZero_strip (hz : GenusZero σ α) (p : O) (hp : α p≠p) : GenusZero σ (strip α p) := by
  obtain ⟨l,hl,hL,he⟩ := factorization (strip α p) (strip_involutive α hi p)
  have he' : ∀e∈(p,α p)::l,e.1≠e.2 ∧ α e.1=e.2 := by
    intro e hm
    rcases List.mem_cons.mp hm with rfl|hm
    · exact ⟨Ne.symm hp,rfl⟩
    · exact ⟨(he e hm).1,strip_edge α hi p (he e hm).1 (he e hm).2⟩
  have hl' : (((p,α p)::l).map (fun e=>Equiv.swap e.1 e.2)).prod=α := by
    simp only [List.map_cons,List.prod_cons,hl,strip]
    rw [←mul_assoc,Equiv.swap_mul_self,one_mul]
  have hL' : 2*((p,α p)::l).length=α.support.card := by
    have hc := strip_card α hi p hp
    simp only [List.length_cons]
    omega
  have hh := (genusZero_iff_handles σ α ((p,α p)::l) hl' he' hL').mp hz
  have ht : handles σ l=0 := Nat.eq_zero_of_le_zero ((handles_tail σ (p,α p) l).trans_eq hh)
  exact (genusZero_iff_handles σ (strip α p) l hl he hL).mpr ht
omit [Fintype O] in
include hi in
lemma dual_rel {x y : O} (h : Relation.EqvGen (Edge σ α) x y) :
    Relation.EqvGen (Edge (α*σ) α) x y := by
  induction h with
  | rel x y h=>
    rcases h with hs|ha
    · exact Relation.EqvGen.trans x ((α*σ) x) y
        (Relation.EqvGen.rel _ _ (Or.inl rfl))
        (Relation.EqvGen.rel _ _ (Or.inr (by rw [Equiv.Perm.mul_apply,hi];exact hs)))
    · exact Relation.EqvGen.rel _ _ (Or.inr ha)
  | refl=>exact Relation.EqvGen.refl _
  | symm _ _ _ ih=>exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ih'=>exact Relation.EqvGen.trans _ _ _ ih ih'
omit [Fintype O] in
include hi in
lemma dual_twice : α*(α*σ)=σ := by
  ext x
  exact hi (σ x)
def dualEquiv : Component σ α ≃ Component (α*σ) α := Quotient.congrRight (fun x y=>⟨
  dual_rel σ α hi,fun h=>by
    have hh := dual_rel (α*σ) α hi h
    rwa [dual_twice σ α hi] at hh⟩)
include hi in
lemma genusZero_dual : GenusZero σ α ↔ GenusZero (α*σ) α := by
  have hc := Nat.card_congr (dualEquiv σ α hi)
  simp only [GenusZero,dual_twice σ α hi]
  omega
include hi in
/-- The actual band splice preserves componentwise combinatorial genus zero,
prior to bypassing its two now-unpaired occurrences. Both the merge and the
split vertex cases are covered by dual edge deletion. -/
theorem genusZero_band (hz : GenusZero σ α) (p : O) (hp : α p≠p) :
    GenusZero (Equiv.swap p (α p)*σ) (strip α p) := by
  have hd := (genusZero_dual σ α hi).mp hz
  have hs := genusZero_strip (α*σ) α hi hd p hp
  have hh := (genusZero_dual (α*σ) (strip α p) (strip_involutive α hi p)).mp hs
  have he : strip α p*(α*σ)=Equiv.swap p (α p)*σ := by
    rw [strip,mul_assoc,dual_twice σ α hi]
  rwa [he] at hh
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.DeleteCycle

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
abbrev Rest := {x : O // x ≠ p}
lemma invariant (h : f p=p) (x : O) : f x ≠ p ↔ x ≠ p := by
  constructor
  · intro hx he; exact hx (he ▸ h)
  · intro hx he; exact hx (f.injective (he.trans h.symm))
def restrict (h : f p=p) : Equiv.Perm (Rest p) := f.subtypePerm (invariant f p h)
lemma restrict_pow (h : f p=p) (x : Rest p) (k : ℕ) :
    ((restrict f p h ^ k) x).val=(f^k) x := by
  simp only [restrict,Equiv.Perm.subtypePerm_pow,Equiv.Perm.subtypePerm_apply]
variable [Fintype O]
lemma restrict_same (h : f p=p) (x y : Rest p) :
    (restrict f p h).SameCycle x y ↔ f.SameCycle x y := by
  constructor
  · intro hs
    obtain ⟨k,hk⟩ := hs.exists_nat_pow_eq
    refine ⟨(k:ℤ),?_⟩
    rw [zpow_natCast]
    exact (restrict_pow f p h x k).symm.trans (congrArg Subtype.val hk)
  · intro hs
    obtain ⟨k,hk⟩ := hs.exists_nat_pow_eq
    refine ⟨(k:ℤ),?_⟩
    rw [zpow_natCast]
    apply Subtype.ext
    exact (restrict_pow f p h x k).trans hk

def classify (h : f p=p) (x : O) : Option (Cycle (restrict f p h)) :=
  if hx : x=p then none else some (cycle (restrict f p h) ⟨x,hx⟩)
omit [Fintype O] in
lemma classify_apply (h : f p=p) (x : O) : classify f p h (f x)=classify f p h x := by
  by_cases hx : x=p
  · subst x; rw [h]
  · have hfx := (invariant f p h x).mpr hx
    rw [classify,dif_neg hfx,classify,dif_neg hx]
    apply congrArg some
    exact cycle_apply (restrict f p h) ⟨x,hx⟩
omit [Fintype O] in
lemma classify_surjective (h : f p=p) : Function.Surjective (classify f p h) := by
  intro c
  cases c with
  | none => exact ⟨p,by simp [classify]⟩
  | some c =>
    obtain ⟨x,rfl⟩ := cycle_surjective (restrict f p h) c
    exact ⟨x,by simp [classify,x.property]⟩
lemma classify_eq (h : f p=p) {x y : O} (he : classify f p h x=classify f p h y) : f.SameCycle x y := by
  by_cases hx : x=p
  · subst x
    have hy : y=p := by
      by_contra hy
      simp [classify,hy] at he
    subst y
    exact Equiv.Perm.SameCycle.refl _ _
  · by_cases hy : y=p
    · subst y; simp [classify,hx] at he
    · simp only [classify,dif_neg hx,dif_neg hy,Option.some.injEq] at he
      exact (restrict_same f p h ⟨x,hx⟩ ⟨y,hy⟩).mp ((cycle_eq _).mp he)
def cycleEquiv (h : f p=p) : Cycle f ≃ Option (Cycle (restrict f p h)) :=
  Equiv.ofBijective (lift f (classify f p h) (classify_apply f p h)) ⟨by
    intro c d he
    obtain ⟨x,rfl⟩ := cycle_surjective f c
    obtain ⟨y,rfl⟩ := cycle_surjective f d
    exact (cycle_eq f).mpr (classify_eq f p h he),
    lift_surjective f _ _ (classify_surjective f p h)⟩
lemma fixed_count (h : f p=p) :
    Fintype.card (Cycle f)=Fintype.card (Cycle (restrict f p h))+1 := by
  simpa only [Fintype.card_option] using Fintype.card_congr (cycleEquiv f p h)

/-- Delete an occurrence by bypassing it in its boundary cycle. -/
def bypass : Equiv.Perm (Rest p) := restrict (Equiv.swap p (f p)*f) p (SwapCycles.adjacent_fixed f p)
lemma bypass_count (h : f p≠p) : Fintype.card (Cycle (bypass f p))=Fintype.card (Cycle f) := by
  have h₁ := fixed_count (Equiv.swap p (f p)*f) p (SwapCycles.adjacent_fixed f p)
  have h₂ := SwapCycles.adjacent_count f p h
  change _=Fintype.card (Cycle (bypass f p))+1 at h₁
  omega
end
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
lemma bypass_apply [Fintype O] (x : Rest p) :
    (bypass f p x).val=Equiv.swap p (f p) (f x) := rfl
/-- Bypassing a point commutes with a left permutation fixing that point. -/
lemma bypass_mul [Fintype O] (a : Equiv.Perm O) (ha : a p=p) :
    bypass (a*f) p=restrict a p ha*bypass f p := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change Equiv.swap p (a (f p)) (a (f x))=a (Equiv.swap p (f p) (f x))
  simpa only [ha] using (a.injective.swap_apply p (f p) (f x))
variable [Fintype O]
lemma card_rest : Fintype.card (Rest p)+1=Fintype.card O := by
  have h := Fintype.card_subtype_compl (fun x : O=>x=p)
  have he : Fintype.card {x : O // x=p}=1 := Fintype.card_unique
  change Fintype.card (Rest p)=_ at h
  rw [he] at h
  have hn : 0<Fintype.card O := Fintype.card_pos_iff.mpr ⟨p⟩
  omega
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
variable {O B : Type} (σ α : Equiv.Perm O)
lemma component_rotation (x : O) : component σ α (σ x)=component σ α x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl)))
lemma component_partner (x : O) : component σ α (α x)=component σ α x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl)))
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
lemma swap_invariant (q : O→B) (p r : O) (h : q p=q r) (x : O) : q (Equiv.swap p r x)=q x := by
  by_cases hp : x=p
  · subst x;rw [Equiv.swap_apply_left];exact h.symm
  · by_cases hr : x=r
    · subst x;rw [Equiv.swap_apply_right];exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hp hr]
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.MapDeletion

section
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p) (hs : σ p≠p)
abbrev rotation := bypass σ p
abbrev partner := restrict α p ha
def push (x : O) : Rest p := if hx : x=p then ⟨σ p,hs⟩ else ⟨x,hx⟩
omit [Fintype O] in
lemma push_p : push σ p hs p=⟨σ p,hs⟩ := by simp [push]
omit [Fintype O] in
lemma push_val (x : Rest p) : push σ p hs x=x := by simp [push,x.property]
lemma push_rotation (x : Rest p) : push σ p hs (σ x)=rotation σ p x := by
  apply Subtype.ext
  rw [bypass_apply]
  by_cases h : σ x=p
  · simp only [push,h,dif_pos trivial,Equiv.swap_apply_left]
  · have hn : σ x≠σ p := σ.injective.ne x.property
    simp only [push,dif_neg h,Equiv.swap_apply_of_ne_of_ne h hn]
def projectRaw (x : O) : MapEuler.Component (rotation σ p) (partner α p ha) :=
  component (rotation σ p) (partner α p ha) (push σ p hs x)
lemma project_rotation (x : O) : projectRaw σ α p ha hs (σ x)=projectRaw σ α p ha hs x := by
  by_cases hx : x=p
  · subst x
    change component _ _ (push σ p hs (σ p))=component _ _ (push σ p hs p)
    rw [push_p]
    simp only [push,dif_neg hs]
  · change component _ _ (push σ p hs (σ (⟨x,hx⟩ : Rest p)))=_
    rw [push_rotation]
    change component _ _ (rotation σ p ⟨x,hx⟩)=component _ _ (push σ p hs (⟨x,hx⟩ : Rest p))
    rw [push_val,component_rotation]
omit [Fintype O] in
lemma project_partner (x : O) : projectRaw σ α p ha hs (α x)=projectRaw σ α p ha hs x := by
  by_cases hx : x=p
  · subst x;rw [ha]
  · have hn : α x≠p := (DeleteCycle.invariant α p ha x).mpr hx
    change component _ _ (push σ p hs (α x))=component _ _ (push σ p hs x)
    simp only [push,dif_neg hx,dif_neg hn]
    exact component_partner (rotation σ p) (partner α p ha) ⟨x,hx⟩
def project : MapEuler.Component σ α → MapEuler.Component (rotation σ p) (partner α p ha) :=
  MapEuler.lift σ α (projectRaw σ α p ha hs) (project_rotation σ α p ha hs) (project_partner σ α p ha hs)
lemma include_rotation (x : Rest p) : component σ α (rotation σ p x)=component σ α x := by
  rw [bypass_apply,MapEuler.swap_invariant (component σ α) p (σ p) (component_rotation σ α p).symm]
  exact component_rotation σ α x
omit [Fintype O] in
lemma include_partner (x : Rest p) : component σ α (partner α p ha x)=component σ α x :=
  component_partner σ α x
def inclusion : MapEuler.Component (rotation σ p) (partner α p ha) → MapEuler.Component σ α :=
  MapEuler.lift _ _ (fun x : Rest p=>component σ α x) (include_rotation σ α p) (include_partner σ α p ha)
omit [Fintype O] in
lemma component_push (x : O) : component σ α (push σ p hs x)=component σ α x := by
  by_cases hx : x=p
  · subst x;rw [push_p];exact component_rotation σ α p
  · simp only [push,dif_neg hx]
lemma left_inverse : Function.LeftInverse (inclusion σ α p ha) (project σ α p ha hs) := by
  intro c
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
  exact component_push σ α p hs x
lemma project_surjective : Function.Surjective (project σ α p ha hs) := by
  intro c
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
  refine ⟨component σ α x,?_⟩
  change component _ _ (push σ p hs x)=component _ _ x
  rw [push_val]
def componentEquiv : MapEuler.Component σ α ≃ MapEuler.Component (rotation σ p) (partner α p ha) :=
  Equiv.ofBijective (project σ α p ha hs) ⟨(left_inverse σ α p ha hs).injective,project_surjective σ α p ha hs⟩
end
open scoped Classical
open DeleteCycle MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
def support_equiv : ↥(partner α p ha).support ≃ ↥α.support where
  toFun x := ⟨x.val.val,by
    have h := Equiv.Perm.mem_support.mp x.property
    exact Equiv.Perm.mem_support.mpr (fun he=>h (Subtype.ext he))⟩
  invFun x := ⟨⟨x.val,by
    intro he
    have hn := Equiv.Perm.mem_support.mp x.property
    exact hn (he ▸ ha)⟩,by
      apply Equiv.Perm.mem_support.mpr
      intro he
      exact Equiv.Perm.mem_support.mp x.property (congrArg Subtype.val he)⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
lemma support_count : (partner α p ha).support.card=α.support.card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (support_equiv α p ha)
omit [Fintype O] in
include ha in
lemma face_nonfixed (hs : σ p≠p) : (α*σ) p≠p := by
  intro he
  exact hs (α.injective ((show α (σ p)=p from he).trans ha.symm))
/-- Removing a dart fixed by the partner involution preserves all actual map
components and the Euler equality when its vertex is not a singleton. -/
theorem genusZero_delete (hs : σ p≠p) (hz : GenusZero σ α) :
    GenusZero (rotation σ p) (partner α p ha) := by
  have hv := bypass_count σ p hs
  have hf := bypass_count (α*σ) p (face_nonfixed σ α p ha hs)
  rw [bypass_mul σ p α ha] at hf
  have hc := Nat.card_congr (componentEquiv σ α p ha hs)
  have he := support_count α p ha
  simp only [←Nat.card_eq_fintype_card] at hv hf
  dsimp only [GenusZero] at hz ⊢
  change Nat.card (Cycle (rotation σ p))=Nat.card (Cycle σ) at hv
  change Nat.card (Cycle (partner α p ha*rotation σ p))=Nat.card (Cycle (α*σ)) at hf
  rw [hv,hf,←hc]
  have hsup : ∀ (i j : Fintype (Rest p)) (d e : DecidableEq (Rest p)),
      @Equiv.Perm.support (Rest p) d i (partner α p ha) =
      @Equiv.Perm.support (Rest p) e j (partner α p ha) := by
    intro i j d e
    cases Subsingleton.elim i j
    cases Subsingleton.elim d e
    rfl
  convert hz using 1
  rw [←he]
  congr 1
  exact congrArg Finset.card (hsup _ _ _ _)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open PermutationCycles DeleteCycle
variable {O A : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
abbrev q' : Rest p := ⟨q,hpq.symm⟩
abbrev Residual := Rest (q' p q hpq)
def adjusted := α*Equiv.swap p q
omit [Fintype O] in
include hi hpair in
lemma adjusted_p : adjusted α p q p=p := by
  rw [adjusted,Equiv.Perm.mul_apply,Equiv.swap_apply_left]
  exact (congrArg α hpair).symm.trans (hi p)
omit [Fintype O] in
include hpair in
lemma adjusted_q : adjusted α p q q=q := by
  rw [adjusted,Equiv.Perm.mul_apply,Equiv.swap_apply_right,hpair]
def α₁ : Equiv.Perm (Rest p) := restrict (adjusted α p q) p (adjusted_p α hi p q hpair)
omit [Fintype O] in
lemma α₁_q : α₁ α hi p q hpair (q' p q hpq)=q' p q hpq := by
  apply Subtype.ext
  exact adjusted_q α p q hpair

def partner : Equiv.Perm (Residual p q hpq) :=
  restrict (α₁ α hi p q hpair) (q' p q hpq) (α₁_q α hi p q hpq hpair)
def switched : Equiv.Perm O := Equiv.swap p q*σ
def rotation : Equiv.Perm (Residual p q hpq) := bypass (bypass (switched σ p q) p) (q' p q hpq)
def face : Equiv.Perm O := α*σ

def val (x : Residual p q hpq) : O := x.val.val
omit [Fintype O] in
lemma val_ne_p (x : Residual p q hpq) : val p q hpq x≠p := x.val.property
omit [Fintype O] in
lemma val_ne_q (x : Residual p q hpq) : val p q hpq x≠q := by
  intro h
  exact x.property (Subtype.ext h)
omit [Fintype O] in
lemma val_injective : Function.Injective (val p q hpq) := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)
omit [Fintype O] in
lemma partner_val (x : Residual p q hpq) :
    val p q hpq (partner α hi p q hpq hpair x)=α (val p q hpq x) := by
  change α (Equiv.swap p q (val p q hpq x))=_
  rw [Equiv.swap_apply_of_ne_of_ne (val_ne_p p q hpq x) (val_ne_q p q hpq x)]
omit [Fintype O] in
lemma partner_involutive : Function.Involutive (partner α hi p q hpq hpair) := by
  intro x
  apply val_injective p q hpq
  rw [partner_val,partner_val,hi]

variable (hs : σ p≠p) (hfp : face σ α p≠p) (hfq : face σ α q≠q)
lemma two_fewer : Fintype.card (Residual p q hpq)+2=Fintype.card O := by
  have h₁ := card_rest (p:=p)
  have h₂ := card_rest (p:=q' p q hpq)
  simp only [←Nat.card_eq_fintype_card] at h₁ h₂ ⊢
  change Nat.card (Residual p q hpq)+1=Nat.card (Rest p) at h₂
  omega
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
lemma genusZero_fintype {O : Type} (i j : Fintype O) (σ α : Equiv.Perm O) :
    @GenusZero O i σ α ↔ @GenusZero O j σ α := by
  cases Subsingleton.elim i j
  rfl
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
omit [Fintype O] in
include hi hpair in
lemma adjusted_strip : adjusted α p q=PairingFactors.strip α p := by
  rw [←hpair]
  ext x
  change α (Equiv.swap p (α p) x)=Equiv.swap p (α p) (α x)
  rw [←α.injective.swap_apply,hi p,Equiv.swap_comm (α p) p]
include hi hpq hpair in
lemma switched_genusZero (hz : GenusZero σ α) :
    GenusZero (switched σ p q) (adjusted α p q) := by
  rw [adjusted_strip α hi p q hpair]
  have hp : α p≠p := by rw [hpair];exact hpq.symm
  have hh := genusZero_band σ α hi hz p hp
  simpa only [switched,hpair] using hh
end TorsionFreeZeroDivisors.BandEuler

/-! Actual finite noncrossing word matchings, the cancellation part of the
cone-picture construction. An ear is inserted at two adjacent positions.
This file asserts no sphere realization or asphericity theorem. -/
namespace TorsionFreeZeroDivisors.WordPairing

section
variable {A : Type*} {n : ℕ}

structure Data (inv : A → A) (label : Fin n → A) where
  partner : Equiv.Perm (Fin n)
  involutive : Function.Involutive partner
  distinct : ∀ i,partner i≠i
  compatible : ∀ i,label (partner i)=inv (label i)
  noncrossing : ∀ i j,i<j → j<partner i → partner i<partner j → False

namespace Ear
variable (k : ℕ)
def raise (i : Fin n) : Fin (n+2) := ⟨if i.val<k then i.val else i.val+2,by
  split_ifs with h <;> omega⟩
lemma raise_lt (i j : Fin n) : raise k i<raise k j ↔ i<j := by
  simp only [raise,Fin.lt_def]
  split_ifs <;> omega
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

variable {inv : A → A} {label : Fin n → A} (d : Data inv label)
def sumPartner : Equiv.Perm (Fin n⊕Bool) := Equiv.sumCongr d.partner Equiv.boolNot

def partner (hk : k≤n) : Equiv.Perm (Fin (n+2)) :=
  (equiv k hk).permCongr (sumPartner d)
lemma partner_apply (hk : k≤n) (i : Fin n⊕Bool) :
    partner k d hk (equiv k hk i)=equiv k hk (sumPartner d i) := by
  simp only [partner,Equiv.permCongr_apply,Equiv.symm_apply_apply]

lemma involutive (hk : k≤n) : Function.Involutive (partner k d hk) := by
  intro i
  obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
  rw [partner_apply,partner_apply]
  congr 1
  cases i with
  | inl i => exact congrArg Sum.inl (d.involutive i)
  | inr b => cases b <;> rfl
lemma distinct (hk : k≤n) (i : Fin (n+2)) : partner k d hk i≠i := by
  obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
  rw [partner_apply]
  intro he
  have hh := (equiv k hk).injective he
  cases i with
  | inl i => exact d.distinct i (Sum.inl.inj hh)
  | inr b => cases b <;> cases hh

lemma noncrossing (hk : k≤n) : ∀ i j : Fin (n+2),
    i<j → j<partner k d hk i → partner k d hk i<partner k d hk j → False := by
  intro i j hij hjp hpp
  obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
  obtain ⟨j,rfl⟩ := (equiv k hk).surjective j
  rw [partner_apply] at hjp hpp
  rw [partner_apply] at hpp
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact d.noncrossing i j ((raise_lt k _ _).mp hij)
        ((raise_lt k _ _).mp hjp) ((raise_lt k _ _).mp hpp)
    | inr b =>
      cases b with
      | false =>
        change k < (raise k (d.partner i)).val at hjp
        change (raise k (d.partner i)).val < k+1 at hpp
        omega
      | true =>
        change k+1 < (raise k (d.partner i)).val at hjp
        change (raise k (d.partner i)).val < k at hpp
        omega
  | inr b =>
    cases b with
    | false =>
      change k < (equiv k hk j).val at hij
      change (equiv k hk j).val < k+1 at hjp
      omega
    | true =>
      change k+1 < (equiv k hk j).val at hij
      change (equiv k hk j).val < k at hjp
      omega
end Ear
end

section
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Data
variable (d : Data inv label)
lemma reindex_apply (e : Fin n ≃o Fin m) (i : Fin n) :
    e.toEquiv.permCongr d.partner (e i)=e (d.partner i) := by
  change e (d.partner (e.symm (e i)))=e (d.partner i)
  rw [e.symm_apply_apply]
def reindex (e : Fin n ≃o Fin m) (label' : Fin m → A)
    (hl : ∀ i,label' (e i)=label i) : Data inv label' where
  partner := e.toEquiv.permCongr d.partner
  involutive := by
    intro i
    obtain ⟨i,rfl⟩ := e.surjective i
    rw [d.reindex_apply,d.reindex_apply,d.involutive]
  distinct := by
    intro i
    obtain ⟨i,rfl⟩ := e.surjective i
    rw [d.reindex_apply]
    exact fun he=>d.distinct i (e.injective he)
  compatible := by
    intro i
    obtain ⟨i,rfl⟩ := e.surjective i
    rw [d.reindex_apply,hl,hl]
    exact d.compatible i
  noncrossing := by
    intro i j hij hjp hpp
    obtain ⟨i,rfl⟩ := e.surjective i
    obtain ⟨j,rfl⟩ := e.surjective j
    rw [d.reindex_apply] at hjp
    rw [d.reindex_apply,d.reindex_apply] at hpp
    exact d.noncrossing i j ((e.lt_iff_lt).mp hij)
      ((e.lt_iff_lt).mp hjp) ((e.lt_iff_lt).mp hpp)
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

def data (d : Data inv label) (ha : inv (inv a)=a) :
    Data inv (labels (label:=label) (inv:=inv) k hk a) where
  partner := partner k d hk
  involutive := involutive k d hk
  distinct := distinct k d hk
  compatible := by
    intro i
    obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
    rw [partner_apply]
    cases i with
    | inl i =>
      change labels k hk a (equiv k hk (.inl (d.partner i)))=_
      rw [labels_left,labels_left]
      exact d.compatible i
    | inr b =>
      cases b with
      | false => exact (labels_true k hk a).trans (congrArg inv (labels_false k hk a).symm)
      | true =>
        change labels k hk a (equiv k hk (.inr false))=inv (labels k hk a (equiv k hk (.inr true)))
        rw [labels_false,labels_true,ha]
  noncrossing := noncrossing k d hk
end Ear

namespace ListInsert
variable (u v : List A) (a b : A)
lemma get_old (i : ℕ) (hi : i<(u++v).length) :
    (u++a::b::v)[if i<u.length then i else i+2]'(by split_ifs <;> simp only [List.length_append,List.length_cons] at * <;> omega)=
      (u++v)[i] := by
  by_cases h : i<u.length
  · simp only [if_pos h,List.getElem_append_left h]
  · have hh : ¬i+2<u.length := by omega
    have he : i+2-u.length=(i-u.length)+2 := by omega
    simp only [if_neg h,List.getElem_append,dif_neg h,dif_neg hh,he,List.getElem_cons_succ]
lemma get_first :
    (u++a::b::v)[u.length]'(by simp only [List.length_append,List.length_cons];omega)=a := by
  simp only [List.getElem_append,dif_neg (Nat.lt_irrefl _),Nat.sub_self,List.getElem_cons_zero]
lemma get_second :
    (u++a::b::v)[u.length+1]'(by simp only [List.length_append,List.length_cons];omega)=b := by
  have hh : ¬u.length+1<u.length := by omega
  simp only [List.getElem_append,dif_neg hh,Nat.add_sub_cancel_left,List.getElem_cons_succ,List.getElem_cons_zero]
end ListInsert

end
variable {A : Type*}
namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
lemma length_eq : (u++v).length+2=(u++a::inv a::v).length := by
  simp only [List.length_append,List.length_cons]
  omega

def orderIso : Fin ((u++v).length+2) ≃o Fin (u++a::inv a::v).length :=
  Fin.castOrderIso (length_eq u v inv a)

lemma labels_eq (i : Fin ((u++v).length+2)) :
    (u++a::inv a::v).get (orderIso u v inv a i)=
      Ear.labels (label:=(u++v).get) (inv:=inv) u.length
        (by simp only [List.length_append];omega) a i := by
  obtain ⟨i,rfl⟩ := (Ear.equiv u.length (show u.length≤(u++v).length by
    simp only [List.length_append];omega)).surjective i
  cases i with
  | inl i =>
    rw [Ear.labels_left]
    change (u++a::inv a::v)[if i.val<u.length then i.val else i.val+2]'(by
      have hi := i.isLt
      split_ifs <;> simp only [List.length_append,List.length_cons] at * <;> omega)=
      (u++v)[i.val]
    exact get_old u v a (inv a) i.val i.isLt
  | inr b =>
    cases b with
    | false =>
      rw [Ear.labels_false]
      exact get_first u v a (inv a)
    | true =>
      rw [Ear.labels_true]
      exact get_second u v a (inv a)

def data (d : Data inv (u++v).get) (ha : inv (inv a)=a) :
    Data inv (u++a::inv a::v).get :=
  (Ear.data u.length (by simp only [List.length_append];omega) a d ha).reindex
    (orderIso u v inv a) _ (labels_eq u v inv a)
end ListInsert
lemma inverseLetter_involutive : Function.Involutive (inverseLetter (A:=A)) := by
  intro p
  cases p with
  | mk a b => cases b <;> rfl

def emptyData : Data (inverseLetter (A:=A)) ([] : List (A×Bool)).get where
  partner := Equiv.refl _
  involutive := fun _=>rfl
  distinct i := Fin.elim0 i
  compatible i := Fin.elim0 i
  noncrossing i := Fin.elim0 i

end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.Ear
open PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
lemma rotate_val (i : Fin n) : (finRotate n i).val=if i.val+1<n then i.val+1 else 0 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [coe_finRotate]
    simp only [Fin.ext_iff,Fin.val_last]
    split_ifs <;> have := i.isLt <;> omega

def previous (k : ℕ) (hk : k≤n) (hn : 0<n) : Fin n :=
  ⟨if k=0 then n-1 else k-1,by split_ifs <;> omega⟩
variable (k : ℕ) (hk : k≤n) (hn : 0<n)
lemma previous_rotate : finRotate (n+2) (raise k (previous k hk hn))=equiv k hk (.inr false) := by
  apply Fin.ext
  change (finRotate (n+2) (raise k (previous k hk hn))).val=k
  rw [rotate_val]
  simp only [raise,previous]
  split_ifs <;> omega
lemma rotate_old (i : Fin n) (hi : i≠previous k hk hn) :
    finRotate (n+2) (raise k i)=raise k (finRotate n i) := by
  apply Fin.ext
  have hi' : i.val≠(previous k hk hn).val := fun h=>hi (Fin.ext h)
  rw [rotate_val]
  simp only [raise,rotate_val,previous] at *
  have hb := i.isLt
  split_ifs at * <;> omega
lemma rotate_false : finRotate (n+2) (equiv k hk (.inr false))=equiv k hk (.inr true) := by
  apply Fin.ext
  rw [rotate_val]
  change (if k+1<n+2 then k+1 else 0)=k+1
  rw [if_pos (by omega)]
lemma rotate_true : finRotate (n+2) (equiv k hk (.inr true))=
    raise k (finRotate n (previous k hk hn)) := by
  apply Fin.ext
  rw [rotate_val]
  change (if k+1+1<n+2 then k+1+1 else 0)=_
  simp only [raise,rotate_val,previous]
  split_ifs <;> omega

lemma rotation_transport (i : Fin n⊕Bool) :
    finRotate (n+2) (equiv k hk i)=equiv k hk
      (InsertedRotation.rotation (finRotate n) (previous k hk hn) i) := by
  cases i with
  | inl i =>
    by_cases hi : i=previous k hk hn
    · subst i
      rw [InsertedRotation.rotation_p,equiv_left]
      exact previous_rotate k hk hn
    · rw [InsertedRotation.rotation_left _ _ i hi,equiv_left,equiv_left]
      exact rotate_old k hk hn i hi
  | inr b =>
    cases b with
    | false => rw [InsertedRotation.rotation_false]; exact rotate_false k hk
    | true => rw [InsertedRotation.rotation_true,equiv_left]; exact rotate_true k hk hn

lemma rotation_eq : (equiv k hk).permCongr
    (InsertedRotation.rotation (finRotate n) (previous k hk hn))=finRotate (n+2) := by
  apply Equiv.ext
  intro i
  obtain ⟨i,rfl⟩ := (equiv k hk).surjective i
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  exact (rotation_transport k hk hn i).symm

variable (d : Data inv label)
lemma face_eq : (equiv k hk).permCongr
    (InsertedRotation.face (finRotate n) d.partner (previous k hk hn))=
    partner k d hk *finRotate (n+2) := by
  rw [InsertedRotation.face,PermutationTransport.mul,rotation_eq k hk hn]
  rfl

include hn in
theorem face_count :
    Fintype.card (Cycle (d.partner*finRotate n))+1≤
      Fintype.card (Cycle (partner k d hk*finRotate (n+2))) := by
  rw [←face_eq k hk hn d,PermutationTransport.card_cycles]
  exact InsertedRotation.face_count _ _ _

end TorsionFreeZeroDivisors.WordPairing.Ear

namespace TorsionFreeZeroDivisors.PermutationCycles
variable (O : Type) [Fintype O]
lemma card_identity : Fintype.card (Cycle (1 : Equiv.Perm O))=Fintype.card O := by
  apply (Fintype.card_of_bijective (f:=cycle (1 : Equiv.Perm O)) ?_).symm
  refine ⟨?_,cycle_surjective _⟩
  intro x y h
  exact ((cycle_eq _).mp h).eq_of_left rfl
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.WordPairing

section
open PermutationCycles
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

/-- The disk Euler estimate for the actual circle rotation and word matching.
The empty word is distinguished, since it has no boundary occurrences. -/
def DiskEuler (d : Data inv label) : Prop :=
  n=0 ∨ n+2≤2*Fintype.card (Cycle (d.partner*finRotate n))

namespace Ear
variable (k : ℕ) (hk : k≤n) (d : Data inv label)
lemma empty_rotation (hn : n=0) : partner k d hk=finRotate (n+2) := by
  subst n
  have he : k=0 := by omega
  subst k
  apply Equiv.ext
  intro i
  obtain ⟨i,rfl⟩ := (equiv 0 hk).surjective i
  rw [partner_apply]
  cases i with
  | inl i => exact i.elim0
  | inr b => cases b <;> rfl

lemma euler (hd : DiskEuler d) :
    n+2+2≤2*Fintype.card (Cycle (partner k d hk*finRotate (n+2))) := by
  by_cases he : n=0
  · have hrot := empty_rotation k hk d he
    have hf : partner k d hk*finRotate (n+2)=1 := by
      apply Equiv.ext
      intro i
      rw [Equiv.Perm.mul_apply,←hrot]
      exact involutive k d hk i
    rw [hf,card_identity,Fintype.card_fin,he]
  · have hn : 0<n := Nat.pos_of_ne_zero he
    have hc := face_count k hk hn d
    rcases hd with hh|hh
    · exact (he hh).elim
    · omega
end Ear

namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
end ListInsert

end
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
/-- Every nonempty finite noncrossing perfect matching has a literal adjacent
ear, obtained by minimizing the positive distance between matched positions. -/
theorem adjacent_ear (d : Data inv label) (hn : 0 < n) :
    ∃i : Fin n,(d.partner i).val=i.val+1 := by
  let s : Finset (Fin n) := Finset.univ.filter (fun i=> i < d.partner i)
  have hs : s.Nonempty := by
    let z : Fin n := ⟨0,hn⟩
    refine ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    have he := d.distinct z
    have hv : (d.partner z).val ≠ 0 := by intro h;exact he (Fin.ext h)
    change 0 < (d.partner z).val
    omega
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image s (fun i=> (d.partner i).val-i.val) hs
  have hip : i < d.partner i := (Finset.mem_filter.mp hi).2
  refine ⟨i,?_⟩
  by_contra he
  have hgap : i.val+1 < (d.partner i).val := by change i.val < (d.partner i).val at hip;omega
  let j : Fin n := ⟨i.val+1,lt_trans hgap (d.partner i).isLt⟩
  have hij : i < j := by change i.val < i.val+1;omega
  have hjp : j < d.partner i := hgap
  have hpj : j < d.partner j := by
    by_contra h
    have hpj : d.partner j < j := lt_of_le_of_ne (le_of_not_gt h) (d.distinct j)
    have hai : d.partner j ≠ i := by
      intro h
      have h' : j=d.partner i := (d.involutive j).symm.trans (congrArg d.partner h)
      exact (ne_of_lt hjp) h'
    have hapi : d.partner j < i := by
      have haival : (d.partner j).val ≠ i.val := by intro hh;exact hai (Fin.ext hh)
      change (d.partner j).val < i.val
      change (d.partner j).val < i.val+1 at hpj
      omega
    apply d.noncrossing (d.partner j) i hapi
    · simpa only [d.involutive j] using hij
    · simpa only [d.involutive j] using hjp
  have upper : d.partner j < d.partner i := by
    have hnlt : ¬d.partner i < d.partner j := fun h=> d.noncrossing i j hij hjp h
    have hne : d.partner j ≠ d.partner i := fun hh=> ne_of_gt hij (d.partner.injective hh)
    exact lt_of_le_of_ne (le_of_not_gt hnlt) hne
  have hmem : j∈s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpj⟩
  have hm := hmin j hmem
  change (d.partner i).val-i.val ≤ (d.partner j).val-(i.val+1) at hm
  change (d.partner j).val < (d.partner i).val at upper
  omega
end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.EraseEar
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin (n+2)→A}
  (d : Data inv label) (k : ℕ) (hk : k≤n)
  (hpair : d.partner (Ear.equiv k hk (.inr false))=Ear.equiv k hk (.inr true))
include hpair in
lemma back : d.partner (Ear.equiv k hk (.inr true))=Ear.equiv k hk (.inr false) :=
  (congrArg d.partner hpair).symm.trans (d.involutive _)
include hpair in
lemma remains (i : Fin n) : ∃j : Fin n,Ear.raise k j=d.partner (Ear.raise k i) := by
  obtain ⟨a,ha⟩ := (Ear.equiv k hk).surjective (d.partner (Ear.raise k i))
  cases a with
  | inl j => exact ⟨j,ha⟩
  | inr b =>
    cases b with
    | false =>
      have he := hpair.symm.trans ((congrArg d.partner ha).trans (d.involutive _))
      change Ear.equiv k hk (.inr true)=Ear.equiv k hk (.inl i) at he
      cases (Ear.equiv k hk).injective he
    | true =>
      have he := (back d k hk hpair).symm.trans ((congrArg d.partner ha).trans (d.involutive _))
      change Ear.equiv k hk (.inr false)=Ear.equiv k hk (.inl i) at he
      cases (Ear.equiv k hk).injective he

def lower (i : Fin n) : Fin n := Classical.choose (remains d k hk hpair i)
lemma lower_spec (i : Fin n) : Ear.raise k (lower d k hk hpair i)=d.partner (Ear.raise k i) :=
  Classical.choose_spec (remains d k hk hpair i)
lemma lower_involutive : Function.Involutive (lower d k hk hpair) := by
  intro i
  apply Ear.raise_injective k
  rw [lower_spec,lower_spec,d.involutive]

def data : Data inv (fun i=>label (Ear.raise (n:=n) k i)) where
  partner := ⟨lower d k hk hpair,lower d k hk hpair,
    lower_involutive d k hk hpair,lower_involutive d k hk hpair⟩
  involutive := lower_involutive d k hk hpair
  distinct i := by
    intro he
    have hh := congrArg (Ear.raise k) he
    change Ear.raise k (lower d k hk hpair i)=Ear.raise k i at hh
    rw [lower_spec] at hh
    exact d.distinct _ hh
  compatible i := by
    change label (Ear.raise k (lower d k hk hpair i))=inv (label (Ear.raise k i))
    rw [lower_spec,d.compatible]
  noncrossing i j hij hji hpp := by
    apply d.noncrossing (Ear.raise k i) (Ear.raise k j) ((Ear.raise_lt k i j).mpr hij)
    · rw [←lower_spec d k hk hpair i]
      exact (Ear.raise_lt k _ _).mpr hji
    · rw [←lower_spec d k hk hpair i,←lower_spec d k hk hpair j]
      exact (Ear.raise_lt k _ _).mpr hpp

lemma recover : Ear.partner k (data d k hk hpair) hk=d.partner := by
  apply Equiv.ext
  intro i
  obtain ⟨a,rfl⟩ := (Ear.equiv k hk).surjective i
  rw [Ear.partner_apply]
  cases a with
  | inl i => exact lower_spec d k hk hpair i
  | inr b =>
    cases b with
    | false => exact hpair.symm
    | true => exact (back d k hk hpair).symm

lemma euler (hd : DiskEuler (data d k hk hpair)) : DiskEuler d := by
  apply Or.inr
  rw [←recover d k hk hpair]
  exact Ear.euler k hk (data d k hk hpair) hd
end TorsionFreeZeroDivisors.WordPairing.EraseEar
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
variable {A : Type*} {inv : A → A}
/-- Every literal finite noncrossing inverse-letter matching has the disk Euler
estimate, independently of its choice as a free cancellation witness. -/
theorem Data.diskEuler {n : ℕ} {label : Fin n → A} (d : Data inv label) : DiskEuler d := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact Or.inl rfl
    | succ n =>
      cases n with
      | zero => exact False.elim (d.distinct 0 (Fin.ext (by have h := (d.partner 0).isLt; omega)))
      | succ n =>
        obtain ⟨i,hi⟩ := adjacent_ear d (by omega)
        have hk : i.val ≤ n := by have hb := (d.partner i).isLt;omega
        have hp : d.partner (Ear.equiv i.val hk (.inr false))=
            Ear.equiv i.val hk (.inr true) := by
          have he : Ear.equiv i.val hk (.inr false)=i := Fin.ext rfl
          rw [he]
          exact Fin.ext hi
        apply EraseEar.euler d i.val hk hp
        exact ih n (by omega) (EraseEar.data d i.val hk hp)
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.MapEuler
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
lemma component_sameCycle {x y : O} (h : σ.SameCycle x y) :
    component σ α x=component σ α y := by
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  have hh := PermutationCycles.invariant_pow σ (component σ α) (component_rotation σ α) k x
  rw [hk] at hh
  exact hh.symm
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
open MapEuler PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin n→A} (d : Data inv label)
lemma rotate_sameCycle (hn : 2≤n) (x y : Fin n) : (finRotate n).SameCycle x y := by
  apply (isCycle_finRotate_of_le hn).sameCycle
  · exact Equiv.Perm.mem_support.mp (by rw [support_finRotate_of_le hn];exact Finset.mem_univ _)
  · exact Equiv.Perm.mem_support.mp (by rw [support_finRotate_of_le hn];exact Finset.mem_univ _)
/-- The noncrossing cancellation matching has actual combinatorial genus zero,
not just a scalar disk face estimate. Nonempty words (necessarily of length at
least two) have a single map component; the empty case is separate. -/
theorem Data.genusZero : GenusZero (finRotate n) d.partner := by
  by_cases hn : n=0
  · subst n
    have hi : IsEmpty (Fin 0) := inferInstance
    have hV : IsEmpty (Cycle (finRotate 0)) := inferInstance
    have hF : IsEmpty (Cycle (d.partner*finRotate 0)) := inferInstance
    have hC : IsEmpty (Component (finRotate 0) d.partner) := inferInstance
    simp only [GenusZero,Nat.card_of_isEmpty,mul_zero,add_zero]
    simp only [Equiv.Perm.support,Finset.univ_eq_empty,Finset.filter_empty,Finset.card_empty]
  have hn2 : 2≤n := by
    by_contra hh
    have he : n=1 := by omega
    subst n
    exact d.distinct 0 (Subsingleton.elim _ _)
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let : Subsingleton (Cycle (finRotate n)) := ⟨by
    intro x y
    obtain ⟨a,rfl⟩ := cycle_surjective _ x
    obtain ⟨b,rfl⟩ := cycle_surjective _ y
    exact (cycle_eq _).mpr (rotate_sameCycle hn2 a b)⟩
  let : Subsingleton (Component (finRotate n) d.partner) := ⟨by
    intro x y
    obtain ⟨a,rfl⟩ := Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Quotient.mk_surjective y
    exact component_sameCycle _ _ (rotate_sameCycle hn2 a b)⟩
  let : Nonempty (Cycle (finRotate n)) := ⟨cycle _ ⟨0,by omega⟩⟩
  let : Nonempty (Component (finRotate n) d.partner) := ⟨component _ _ ⟨0,by omega⟩⟩
  have hV : Nat.card (Cycle (finRotate n))=1 := Nat.card_unique
  have hC : Nat.card (Component (finRotate n) d.partner)=1 := Nat.card_unique
  have hd := (d.diskEuler).resolve_left hn
  simp only [←Nat.card_eq_fintype_card] at hd
  apply genusZero_of_lower (finRotate n) d.partner d.involutive
  rw [hV,hC]
  have he := d.distinct
  simp only [Equiv.Perm.support,he,ne_eq,not_false_eq_true,Finset.filter_true,Finset.card_univ,Fintype.card_fin]
  omega
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.DeleteCycle
open scoped Classical
variable {O : Type} (σ : Equiv.Perm O) (p : O)
lemma bypass_fixed (h : σ p=p) : bypass σ p=restrict σ p h := by
  ext x
  change Equiv.swap p (σ p) (σ x)=σ x
  rw [h,Equiv.swap_self]
  rfl
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.IsolatedDeletion
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} (σ α : Equiv.Perm O) (p : O) (hs : σ p=p) (ha : α p=p)
def classify (x : O) : Option (Component (restrict σ p hs) (restrict α p ha)) :=
  if hx : x=p then none else some (component _ _ ⟨x,hx⟩)
lemma classify_rotation (x : O) : classify σ α p hs ha (σ x)=classify σ α p hs ha x := by
  by_cases hx : x=p
  · subst x;rw [hs]
  · rw [classify,dif_neg ((invariant σ p hs x).mpr hx),classify,dif_neg hx]
    exact congrArg some (component_rotation (restrict σ p hs) (restrict α p ha) ⟨x,hx⟩)
lemma classify_partner (x : O) : classify σ α p hs ha (α x)=classify σ α p hs ha x := by
  by_cases hx : x=p
  · subst x;rw [ha]
  · rw [classify,dif_neg ((invariant α p ha x).mpr hx),classify,dif_neg hx]
    exact congrArg some (component_partner (restrict σ p hs) (restrict α p ha) ⟨x,hx⟩)
def project : Component σ α → Option (Component (restrict σ p hs) (restrict α p ha)) :=
  MapEuler.lift σ α (classify σ α p hs ha) (classify_rotation σ α p hs ha) (classify_partner σ α p hs ha)
def inclusion : Component (restrict σ p hs) (restrict α p ha) → Component σ α :=
  MapEuler.lift _ _ (fun x : Rest p=>component σ α x)
    (fun x=>component_rotation σ α x) (fun x=>component_partner σ α x)
lemma project_injective : Function.Injective (project σ α p hs ha) := by
  intro c d he
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
  obtain ⟨y,rfl⟩ := Quotient.mk_surjective d
  change classify σ α p hs ha x=classify σ α p hs ha y at he
  by_cases hx : x=p
  · subst x
    have hy : y=p := by
      by_contra hy
      simp [classify,hy] at he
    subst y;rfl
  · by_cases hy : y=p
    · subst y;simp [classify,hx] at he
    · simp only [classify,dif_neg hx,dif_neg hy,Option.some.injEq] at he
      exact congrArg (inclusion σ α p hs ha) he
lemma project_surjective : Function.Surjective (project σ α p hs ha) := by
  intro c
  cases c with
  | none=>exact ⟨component σ α p,by simp [project,MapEuler.lift,classify,component]⟩
  | some c=>
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    refine ⟨component σ α x,?_⟩
    change classify σ α p hs ha x=some (component _ _ x)
    simp only [classify,dif_neg x.property]
def componentEquiv : Component σ α ≃ Option (Component (restrict σ p hs) (restrict α p ha)) :=
  Equiv.ofBijective (project σ α p hs ha) ⟨project_injective σ α p hs ha,project_surjective σ α p hs ha⟩
variable [Fintype O]
lemma component_count : Nat.card (Component σ α)=Nat.card (Component (restrict σ p hs) (restrict α p ha))+1 := by
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option] using Nat.card_congr (componentEquiv σ α p hs ha)
include hs in
/-- Deleting an isolated unpaired occurrence removes one vertex, one face and
one actual connected component; genus zero is preserved also in the empty case. -/
theorem genusZero (hz : GenusZero σ α) :
    GenusZero (bypass σ p) (restrict α p ha) := by
  rw [bypass_fixed σ p hs]
  have hv := fixed_count σ p hs
  have hf := fixed_count (α*σ) p (show (α*σ) p=p by change α (σ p)=p;rw [hs,ha])
  have hc := component_count σ α p hs ha
  have he := MapDeletion.support_count α p ha
  simp only [←Nat.card_eq_fintype_card] at hv hf
  have hface : restrict (α*σ) p (show (α*σ) p=p by change α (σ p)=p;rw [hs,ha])=
      restrict α p ha*restrict σ p hs := by ext x;rfl
  rw [hface] at hf
  dsimp only [GenusZero] at hz ⊢
  have hsup : (restrict α p ha).support.card=α.support.card := by
    convert he using 1
  have hh : 2*Nat.card (PermutationCycles.Cycle (restrict σ p hs))+
      2*Nat.card (PermutationCycles.Cycle (restrict α p ha*restrict σ p hs))=
      (restrict α p ha).support.card+4*Nat.card (Component (restrict σ p hs) (restrict α p ha)) := by omega
  have hinst : ∀ (i j : Fintype (Rest p)) (d e : DecidableEq (Rest p)),
      @Equiv.Perm.support (Rest p) d i (restrict α p ha)=
      @Equiv.Perm.support (Rest p) e j (restrict α p ha) := by
    intro i j d e
    cases Subsingleton.elim i j
    cases Subsingleton.elim d e
    rfl
  convert hh using 1
  congr 1
  exact congrArg Finset.card (hinst _ _ _ _)
end TorsionFreeZeroDivisors.IsolatedDeletion
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
/-- Unconditional deletion of an unpaired occurrence, including isolated
vertices/components. -/
theorem genusZero_delete_all (hz : GenusZero σ α) : GenusZero (bypass σ p) (restrict α p ha) := by
  by_cases hs : σ p=p
  · exact IsolatedDeletion.genusZero σ α p hs ha hz
  · exact genusZero_delete σ α p ha hs hz
end TorsionFreeZeroDivisors.MapDeletion

namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open DeleteCycle MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
include hi hpair in
/-- Paired-band deletion preserves genus zero without any degree or face
nondegeneracy assumptions. Empty residual maps, isolated disks, monogons, digons,
and split components are all included. This is purely a permutation-map result,
not an assertion that an essential sphere survives the surgery. -/
theorem genusZero_all (hz : GenusZero σ α) :
    GenusZero (rotation σ p q hpq) (partner α hi p q hpq hpair) := by
  have h₀ := switched_genusZero σ α hi p q hpq hpair hz
  have h₁ := MapDeletion.genusZero_delete_all (switched σ p q) (adjusted α p q) p
    (adjusted_p α hi p q hpair) h₀
  have h₂ := MapDeletion.genusZero_delete_all (bypass (switched σ p q) p) (α₁ α hi p q hpair)
    (q' p q hpq) (α₁_q α hi p q hpq hpair) h₁
  exact (genusZero_fintype _ _ _ _).mp h₂
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
/-- Consecutive edge endpoint agreement. A marked exterior break can be encoded
by one extra formal item with distinct prescribed before/after endpoints. -/
def Consistent : Prop := ∀ x,after x=before (σ x)
include σ in
lemma bypass_consistent (h : Consistent σ before after) (p : O) (hp : after p=before p) :
    Consistent (bypass σ p) (fun x : Rest p=>before x) (fun x : Rest p=>after x) := by
  intro x
  change after (x : O)=before ((bypass σ p x : Rest p) : O)
  rw [bypass_apply,MapEuler.swap_invariant before p (σ p) (hp.symm.trans (h p))]
  exact h x
variable (p q : O) (hpq : p≠q)
def swappedBefore (x : O) : V := before (Equiv.swap p q x)
omit [Fintype O] in
lemma switched_consistent (h : Consistent σ before after) :
    Consistent (switched σ p q) (swappedBefore before p q) after := by
  intro x
  change after x=before (Equiv.swap p q (Equiv.swap p q (σ x)))
  rw [Equiv.swap_apply_self]
  exact h x
/-- The literal band-spliced boundary preserves the graph endpoint equations.
The two crossed endpoints are exactly those forced by an edge and its reverse.
No statement about homotopy or essentiality is hidden in this combinatorial
lemma, and neither distinct-boundary nor same-boundary cases are excluded. -/
theorem consistent (h : Consistent σ before after)
    (hp : after p=before q) (hq : after q=before p) :
    Consistent (rotation σ p q hpq) (fun x=>before (val p q hpq x))
      (fun x=>after (val p q hpq x)) := by
  have hp' : after p=swappedBefore before p q p := by rw [swappedBefore,Equiv.swap_apply_left];exact hp
  have hq' : after q=swappedBefore before p q q := by rw [swappedBefore,Equiv.swap_apply_right];exact hq
  have h₁ := bypass_consistent (switched σ p q) (swappedBefore before p q) after
    (switched_consistent σ before after p q h) p hp'
  have h₂ := bypass_consistent (bypass (switched σ p q) p)
    (fun x : Rest p=>swappedBefore before p q x) (fun x : Rest p=>after x) h₁
    (q' p q hpq) hq'
  intro x
  have hh := h₂ x
  change after (val p q hpq x)=swappedBefore before p q (val p q hpq (rotation σ p q hpq x)) at hh
  rw [swappedBefore,Equiv.swap_apply_of_ne_of_ne (val_ne_p p q hpq _) (val_ne_q p q hpq _)] at hh
  exact hh
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
include hl in
lemma forest_partner (x : O) : cycle f' (α x)=cycle f' x := by
  have h := MapEuler.product_invariant l (cycle f')
    (fun e h=>forest_pair σ' L' e (List.mem_cons_of_mem _ h)) x
  simpa only [hl] using h
include hl in
lemma forest_join : cycle f' p=cycle f' q := by
  have h := forest_pair σ' L' (α p,α q) List.mem_cons_self
  dsimp only at h
  rw [forest_partner σ α p q l hl,forest_partner σ α p q l hl] at h
  exact h
include hl in
lemma forest_rotation (x : O) : cycle f' (σ x)=cycle f' x := by
  have hh := forest_refines σ' L' (σ' x) x (cycle_apply σ' x)
  change cycle f' (Equiv.swap p q (σ x))=cycle f' x at hh
  rw [SwapCycles.cycle_swap f' p q (forest_join σ α p q l hl) (σ x)] at hh
  exact hh
include he hc in
lemma original_invariant (x : O) : MapEuler.component σ α (f' x)=MapEuler.component σ α x := by
  have hpq : MapEuler.component σ α p=MapEuler.component σ α q :=
    MapEuler.component_sameCycle σ α ((cycle_eq σ).mp hc)
  apply invariant_forest σ' L' (MapEuler.component σ α)
  · intro y
    change MapEuler.component σ α (Equiv.swap p q (σ y))=MapEuler.component σ α y
    rw [MapEuler.swap_invariant (MapEuler.component σ α) p q hpq]
    exact MapEuler.component_rotation σ α y
  · intro e h
    rcases List.mem_cons.mp h with rfl|h
    · dsimp only
      rw [MapEuler.component_partner,MapEuler.component_partner]
      exact hpq
    · rw [←he e h]
      exact (MapEuler.component_partner σ α e.1).symm

def toOriginal : Cycle f' → MapEuler.Component σ α :=
  PermutationCycles.lift f' (MapEuler.component σ α) (original_invariant σ α p q l he hc)
def toForest : MapEuler.Component σ α → Cycle f' :=
  MapEuler.lift σ α (cycle f') (forest_rotation σ α p q l hl) (forest_partner σ α p q l hl)
def componentEquiv : Cycle f' ≃ MapEuler.Component σ α :=
  Equiv.ofBijective (toOriginal σ α p q l he hc) ⟨by
    intro c d h
    obtain ⟨x,rfl⟩ := cycle_surjective f' c
    obtain ⟨y,rfl⟩ := cycle_surjective f' d
    exact congrArg (toForest σ α p q l hl) h,
    PermutationCycles.lift_surjective _ _ _ Quotient.mk_surjective⟩
omit [Fintype O] in
include hl in
lemma face_eq : face σ' L'=α*σ := by
  rw [MapEuler.face_product,List.map_cons,List.prod_cons,hl]
  have hs : Equiv.swap (α p) (α q)*α=α*Equiv.swap p q := by
    ext x
    exact α.injective.swap_apply p q x
  rw [hs,mul_assoc,←mul_assoc (Equiv.swap p q),Equiv.swap_mul_self,one_mul]
end TorsionFreeZeroDivisors.VertexSplit
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles ComponentEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
include hi in
/-- Splitting a vertex along two gaps preserves combinatorial genus zero.
This permits empty/isolated components and needs no topological embedding
assumption. The two gaps must be on the same actual vertex cycle. -/
theorem genusZero_vertexSplit (hz : GenusZero σ α) (p q : O) (hpq : p≠q)
    (hc : cycle σ p=cycle σ q) : GenusZero (Equiv.swap p q*σ) α := by
  obtain ⟨l,hl,hL,he⟩ := PairingFactors.factorization α hi
  let σ' := Equiv.swap p q*σ
  let L' := (α p,α q)::l
  have hC := Nat.card_congr (VertexSplit.componentEquiv σ α p q l hl (fun e h=>(he e h).2) hc)
  have hV := SwapCycles.split_count σ p q hpq hc
  simp only [←Nat.card_eq_fintype_card] at hV
  have hF := VertexSplit.face_eq σ α p q l hl
  have hD : ∀e∈L',e.1≠e.2 := by
    intro e h
    rcases List.mem_cons.mp h with rfl|h
    · exact fun h=>hpq (α.injective h)
    · exact (he e h).1
  have hh := handles_exact σ' L' hD
  change Nat.card (Cycle σ')+Nat.card (Cycle (face σ' L'))+2*handles σ' L'=
    L'.length+2*Nat.card (Cycle (forest σ' L')) at hh
  change face σ' L'=α*σ at hF
  rw [hF,hC] at hh
  have hh₀ : handles σ' L'=0 := by
    dsimp only [L',List.length_cons] at hh
    dsimp only [GenusZero] at hz
    change Nat.card (Cycle σ')=Nat.card (Cycle σ)+1 at hV
    change handles σ' ((α p,α q)::l)=0
    omega
  have ht : handles σ' l=0 := Nat.eq_zero_of_le_zero
    ((handles_tail σ' (α p,α q) l).trans_eq hh₀)
  exact (genusZero_iff_handles σ' α l hl he hL).mpr ht
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.MapConjugation
open scoped Classical
open MapEuler PermutationCycles
variable {A B : Type} (e : A ≃ B) (σ α : Equiv.Perm A)
local notation "σ'" => e.permCongr σ
local notation "α'" => e.permCongr α
def forward : Component σ α → Component σ' α' :=
  MapEuler.lift σ α (fun x=>component σ' α' (e x))
    (fun x=>by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using component_rotation σ' α' (e x))
    (fun x=>by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using component_partner σ' α' (e x))
def backward : Component σ' α' → Component σ α :=
  MapEuler.lift σ' α' (fun x=>component σ α (e.symm x))
    (fun x=>by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using component_rotation σ α (e.symm x))
    (fun x=>by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using component_partner σ α (e.symm x))
def components : Component σ α ≃ Component σ' α' where
  toFun := forward e σ α
  invFun := backward e σ α
  left_inv c := by
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    change component σ α (e.symm (e x))=component σ α x
    rw [e.symm_apply_apply]
  right_inv c := by
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    change component σ' α' (e (e.symm x))=component σ' α' x
    rw [e.apply_symm_apply]
variable [Fintype A] [Fintype B]
def supports : ↥α.support ≃ ↥(α').support where
  toFun x := ⟨e x,by
    apply Equiv.Perm.mem_support.mpr
    intro h
    have hn := Equiv.Perm.mem_support.mp x.property
    exact hn (e.injective (by simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using h))⟩
  invFun x := ⟨e.symm x,by
    apply Equiv.Perm.mem_support.mpr
    intro h
    have hn := Equiv.Perm.mem_support.mp x.property
    apply hn
    change e (α (e.symm x))=x
    rw [h,e.apply_symm_apply]⟩
  left_inv x := by ext;simp
  right_inv x := by ext;simp
lemma support_count : (α').support.card=α.support.card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (supports e α)).symm
/-- Changing the actual finite occurrence coordinates does not change genus. -/
theorem genusZero (h : GenusZero σ α) : GenusZero σ' α' := by
  have hC := Nat.card_congr (components e σ α)
  have hV := Nat.card_congr (PermutationTransport.cycles e σ)
  have hF := Nat.card_congr (PermutationTransport.cycles e (α*σ))
  rw [PermutationTransport.mul] at hF
  have hE := support_count e α
  dsimp only [GenusZero] at h ⊢
  rw [←hC,←hV,←hF,hE]
  exact h
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

abbrev Remaining := {x : O // x≠p ∧ x≠q}
def splice (x : O) : O := if α x=p then α q else if α x=q then α p else α x

include hi hf in
lemma splice_avoids (x : Remaining p q) : splice α p q x≠p ∧ splice α p q x≠q := by
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    have hqp : α q≠p := by
      intro h
      have h' : q=α p := (hi _).symm.trans (congrArg α h)
      exact x.property.2 (hx ▸ h'.symm)
    rw [splice,if_pos h1]
    exact ⟨hqp,hf q⟩
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      have hpq' : α p≠q := by
        intro h
        have h' : p=α q := (hi _).symm.trans (congrArg α h)
        exact x.property.1 (hx ▸ h'.symm)
      rw [splice,if_neg h1,if_pos h2]
      exact ⟨hf p,hpq'⟩
    · rw [splice,if_neg h1,if_neg h2]
      exact ⟨h1,h2⟩

def apply (x : Remaining p q) : Remaining p q := ⟨splice α p q x,splice_avoids α hi hf p q x⟩

include hpq in
lemma involutive : Function.Involutive (apply α hi hf p q) := by
  intro x
  apply Subtype.ext
  change splice α p q (splice α p q x)=x
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    have hs : splice α p q x=α q := by rw [splice,if_pos h1]
    rw [hs,splice,hi q,if_neg hpq.symm,if_pos rfl]
    exact hx
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      have hs : splice α p q x=α p := by rw [splice,if_neg h1,if_pos h2]
      rw [hs,splice,hi p,if_pos rfl]
      exact hx
    · have hs : splice α p q x=α x := by rw [splice,if_neg h1,if_neg h2]
      rw [hs,splice,hi x,if_neg x.property.1,if_neg x.property.2]

include hpq in
lemma distinct (x : Remaining p q) : apply α hi hf p q x≠x := by
  intro he
  have he := congrArg Subtype.val he
  change splice α p q x=x at he
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    rw [splice,if_pos h1] at he
    exact hpq (α.injective (hx.trans he.symm))
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      rw [splice,if_neg h1,if_pos h2] at he
      exact hpq (α.injective (he.trans hx.symm))
    · exact hf x (by simpa [splice,h1,h2] using he)

def partner : Equiv.Perm (Remaining p q) := ⟨apply α hi hf p q,apply α hi hf p q,involutive α hi hf p q hpq,involutive α hi hf p q hpq⟩

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))
include hinv hl hlabel in
lemma compatible (x : Remaining p q) :
    label (partner α hi hf p q hpq x)=inv (label x) := by
  change label (splice α p q x)=_
  by_cases h1 : α x=p
  · rw [splice,if_pos h1,hl,hlabel,hinv]
    exact (congrArg label h1).symm.trans (hl x)
  · by_cases h2 : α x=q
    · rw [splice,if_neg h1,if_pos h2,hl,←hlabel]
      exact (congrArg label h2).symm.trans (hl x)
    · rw [splice,if_neg h1,if_neg h2,hl]

end TorsionFreeZeroDivisors.MatchingSurgery
namespace TorsionFreeZeroDivisors.Smoothing
open scoped Classical
open DeleteCycle
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (hf : ∀x,α x≠x)
  (p q : O) (hpq : p≠q) (hsp : σ p=q) (hsq : σ q=p)

include hsp hsq in
lemma rotation_invariant (x : O) : (σ x≠p ∧ σ x≠q) ↔ (x≠p ∧ x≠q) := by
  constructor
  · rintro ⟨hp,hq⟩
    exact ⟨fun h=>hq (h ▸ hsp),fun h=>hp (h ▸ hsq)⟩
  · rintro ⟨hp,hq⟩
    exact ⟨fun h=>hq (σ.injective (h.trans hsq.symm)),fun h=>hp (σ.injective (h.trans hsp.symm))⟩
def rotation : Equiv.Perm (MatchingSurgery.Remaining p q) :=
  σ.subtypePerm (rotation_invariant σ p q hsp hsq)

abbrev r := α p
include hf in
lemma pr : p≠r α p := (hf p).symm
include hf hpq in
lemma rename_invariant (x : O) :
    (Equiv.swap q (r α p) x≠p ∧ Equiv.swap q (r α p) x≠q) ↔ (x≠p ∧ x≠r α p) := by
  have hp : Equiv.swap q (r α p) p=p := Equiv.swap_apply_of_ne_of_ne hpq (pr α hf p)
  have hr : Equiv.swap q (r α p) (r α p)=q := Equiv.swap_apply_right _ _
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨fun h=>h1 (h ▸ hp),fun h=>h2 (h ▸ hr)⟩
  · rintro ⟨h1,h2⟩
    exact ⟨fun h=>h1 ((Equiv.swap q (r α p)).injective (h.trans hp.symm)),
      fun h=>h2 ((Equiv.swap q (r α p)).injective (h.trans hr.symm))⟩
def flatten : BandEuler.Residual p (r α p) (pr α hf p) ≃ MatchingSurgery.Remaining p (r α p) where
  toFun x := ⟨BandEuler.val p (r α p) (pr α hf p) x,
    BandEuler.val_ne_p p (r α p) (pr α hf p) x,BandEuler.val_ne_q p (r α p) (pr α hf p) x⟩
  invFun x := ⟨⟨x,x.property.1⟩,fun he=>x.property.2 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl
def rename : MatchingSurgery.Remaining p (r α p) ≃ MatchingSurgery.Remaining p q :=
  (Equiv.swap q (r α p)).subtypeEquiv (fun x=>(rename_invariant α hf p q hpq x).symm)
def coordinates : BandEuler.Residual p (r α p) (pr α hf p) ≃ MatchingSurgery.Remaining p q :=
  (flatten α hf p).trans (rename α hf p q hpq)
lemma coordinates_val (x : BandEuler.Residual p (r α p) (pr α hf p)) :
    (coordinates α hf p q hpq x).val=Equiv.swap q (r α p) (BandEuler.val p (r α p) (pr α hf p) x) := rfl

lemma partner_commutes (x : BandEuler.Residual p (r α p) (pr α hf p)) :
    coordinates α hf p q hpq (BandEuler.partner α hi p (r α p) (pr α hf p) rfl x)=
      MatchingSurgery.partner α hi hf p q hpq (coordinates α hf p q hpq x) := by
  apply Subtype.ext
  rw [coordinates_val,BandEuler.partner_val]
  change Equiv.swap q (α p) (α (BandEuler.val p (α p) (pr α hf p) x))=
    MatchingSurgery.splice α p q (Equiv.swap q (α p) (BandEuler.val p (α p) (pr α hf p) x))
  let v := BandEuler.val p (α p) (pr α hf p) x
  change Equiv.swap q (α p) (α v)=MatchingSurgery.splice α p q (Equiv.swap q (α p) v)
  have hvp : v≠p := BandEuler.val_ne_p _ _ _ x
  have hvr : v≠α p := BandEuler.val_ne_q _ _ _ x
  have havp : α v≠p := fun h=>hvr ((hi _).symm.trans (congrArg α h))
  have havr : α v≠α p := α.injective.ne hvp
  by_cases hvq : v=q
  · rw [hvq,Equiv.swap_apply_left,MatchingSurgery.splice,hi p,if_pos rfl]
    have hαq : α q≠q := hf q
    have hαqr : α q≠α p := α.injective.ne hpq.symm
    exact Equiv.swap_apply_of_ne_of_ne hαq hαqr
  · rw [Equiv.swap_apply_of_ne_of_ne hvq hvr,MatchingSurgery.splice,if_neg havp]
    by_cases havq : α v=q
    · rw [if_pos havq,havq,Equiv.swap_apply_left]
    · rw [if_neg havq,Equiv.swap_apply_of_ne_of_ne havq havr]

lemma bypass_value (f : Equiv.Perm O) (a : O) (x : Rest a) :
    (bypass f a x).val=if f x=a then f a else f x := by
  change Equiv.swap a (f a) (f x)=_
  by_cases h : f x=a
  · rw [if_pos h,h,Equiv.swap_apply_left]
  · rw [if_neg h,Equiv.swap_apply_of_ne_of_ne h (f.injective.ne x.property)]
lemma rotation_value (a b : O) (hab : a≠b) (x : BandEuler.Residual a b hab) :
    BandEuler.val a b hab (BandEuler.rotation σ a b hab x)=
      let f := BandEuler.switched σ a b
      let g := fun y=>if f y=a then f a else f y
      if g (BandEuler.val a b hab x)=b then g b else g (BandEuler.val a b hab x) := by
  let f := BandEuler.switched σ a b
  let g := fun y=>if f y=a then f a else f y
  change ((bypass (bypass f a) (BandEuler.q' a b hab) x).val).val=
    if g x.val.val=b then g b else g x.val.val
  have he : bypass f a x.val=BandEuler.q' a b hab ↔ g x.val.val=b := by
    rw [Subtype.ext_iff,bypass_value]
  by_cases hc : g x.val.val=b
  · rw [if_pos hc]
    have hv := bypass_value (bypass f a) (BandEuler.q' a b hab) x
    rw [if_pos (he.mpr hc)] at hv
    exact (congrArg Subtype.val hv).trans (bypass_value f a (BandEuler.q' a b hab))
  · rw [if_neg hc]
    have hv := bypass_value (bypass f a) (BandEuler.q' a b hab) x
    rw [if_neg (fun h=>hc (he.mp h))] at hv
    exact (congrArg Subtype.val hv).trans (bypass_value f a x.val)

include hsp hsq hpq in
lemma smoothing_value (r v : O) (hpr : p≠r) (hvp : v≠p) (hvr : v≠r) :
    let f := Equiv.swap p r*σ
    let g := fun y=>if f y=p then f p else f y
    Equiv.swap q r (if g v=r then g r else g v)=σ (Equiv.swap q r v) := by
  let f := Equiv.swap p r*σ
  let g := fun y=>if f y=p then f p else f y
  change Equiv.swap q r (if g v=r then g r else g v)=_
  by_cases hqr : q=r
  · subst r
    have hsvp : σ v≠p := fun h=>hvr (σ.injective (h.trans hsq.symm))
    have hsvq : σ v≠q := fun h=>hvp (σ.injective (h.trans hsp.symm))
    have hfv : f v=σ v := Equiv.swap_apply_of_ne_of_ne hsvp hsvq
    have hg : g v=σ v := by
      change (if f v=p then f p else f v)=σ v
      simp only [hfv,if_neg hsvp]
    rw [hg,if_neg hsvq,Equiv.swap_self]
    rfl
  · have hfp : f p=q := by
      dsimp only [f,Equiv.Perm.mul_apply]
      rw [hsp,Equiv.swap_apply_of_ne_of_ne hpq.symm hqr]
    have hG (y : O) (hyp : y≠p) (hyq : y≠q) : Equiv.swap q r (g y)=σ y := by
      have hsyp : σ y≠p := fun h=>hyq (σ.injective (h.trans hsq.symm))
      have hsyq : σ y≠q := fun h=>hyp (σ.injective (h.trans hsp.symm))
      by_cases hsyr : σ y=r
      · have hfy : f y=p := by simp only [f,Equiv.Perm.mul_apply,hsyr,Equiv.swap_apply_right]
        change Equiv.swap q r (if f y=p then f p else f y)=σ y
        rw [if_pos hfy,hfp,Equiv.swap_apply_left,hsyr]
      · have hfy : f y=σ y := by
          exact Equiv.swap_apply_of_ne_of_ne hsyp hsyr
        change Equiv.swap q r (if f y=p then f p else f y)=σ y
        simp only [hfy,if_neg hsyp,Equiv.swap_apply_of_ne_of_ne hsyq hsyr]
    by_cases hvq : v=q
    · have hfq : f q=r := by simp only [f,Equiv.Perm.mul_apply,hsq,Equiv.swap_apply_left]
      have hgq : g q=r := by
        change (if f q=p then f p else f q)=r
        simp only [hfq,if_neg hpr.symm]
      rw [hvq,hgq,if_pos rfl,Equiv.swap_apply_left]
      exact hG r hpr.symm (Ne.symm hqr)
    · have hgv : g v≠r := by
        intro he
        have hh := hG v hvp hvq
        rw [he,Equiv.swap_apply_right] at hh
        exact hvp (σ.injective (hh.symm.trans hsp.symm))
      rw [if_neg hgv,Equiv.swap_apply_of_ne_of_ne hvq hvr]
      exact hG v hvp hvq

lemma rotation_commutes (x : BandEuler.Residual p (r α p) (pr α hf p)) :
    coordinates α hf p q hpq (BandEuler.rotation σ p (r α p) (pr α hf p) x)=
      rotation σ p q hsp hsq (coordinates α hf p q hpq x) := by
  apply Subtype.ext
  rw [coordinates_val,rotation_value]
  exact smoothing_value σ p q hpq hsp hsq (r α p)
    (BandEuler.val p (r α p) (pr α hf p) x) (pr α hf p)
    (BandEuler.val_ne_p _ _ _ x) (BandEuler.val_ne_q _ _ _ x)

variable [Fintype O]
/-- Suppressing an actual two-occurrence boundary splices its matching partners,
including the already-paired case, and preserves combinatorial genus zero. -/
theorem genusZero (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero (rotation σ p q hsp hsq)
      (MatchingSurgery.partner α hi hf p q hpq) := by
  let e := coordinates α hf p q hpq
  let σ₀ := BandEuler.rotation σ p (r α p) (pr α hf p)
  let α₀ := BandEuler.partner α hi p (r α p) (pr α hf p) rfl
  have hz₀ : MapEuler.GenusZero σ₀ α₀ := BandEuler.genusZero_all σ α hi p
    (r α p) (pr α hf p) rfl hz
  have h := MapConjugation.genusZero e σ₀ α₀ hz₀
  have hσ : e.permCongr σ₀=rotation σ p q hsp hsq := by
    apply Equiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [Equiv.permCongr_apply,e.symm_apply_apply]
    exact rotation_commutes σ α hf p q hpq hsp hsq x
  have hα : e.permCongr α₀=MatchingSurgery.partner α hi hf p q hpq := by
    apply Equiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [Equiv.permCongr_apply,e.symm_apply_apply]
    exact partner_commutes α hi hf p q hpq x
  rwa [hσ,hα] at h

end TorsionFreeZeroDivisors.Smoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
open PermutationCycles
variable {O V : Type} (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)
def isolate : Equiv.Perm O := Equiv.swap p (σ q)*σ
include hpq hsp in
lemma q_ne_next : q≠σ q := fun h=>hpq (σ.injective (hsp.trans h))
include hpq hsp in
lemma isolate_p : isolate σ p q p=q := by
  change Equiv.swap p (σ q) (σ p)=q
  rw [hsp,Equiv.swap_apply_of_ne_of_ne hpq.symm (q_ne_next σ p q hpq hsp)]
lemma isolate_q : isolate σ p q q=p := Equiv.swap_apply_right _ _
def rotation : Equiv.Perm (MatchingSurgery.Remaining p q) :=
  Smoothing.rotation (isolate σ p q) p q (isolate_p σ p q hpq hsp) (isolate_q σ p q)

variable [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (hf : ∀x,α x≠x)
include hsp hi in
lemma isolate_genusZero (hz : MapEuler.GenusZero σ α) : MapEuler.GenusZero (isolate σ p q) α := by
  by_cases he : p=σ q
  · have hs : isolate σ p q=σ := by rw [isolate,←he,Equiv.swap_self];rfl
    rwa [hs]
  · apply MapEuler.genusZero_vertexSplit σ α hi hz p (σ q) he
    rw [cycle_apply,←hsp,cycle_apply]
/-- Deleting an actual adjacent backtracking pair from its boundary, with the
forced partner splice, preserves genus zero even if the two occurrences were
not paired. This supplies the finite-map part of cyclic tightening. -/
theorem genusZero (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero (rotation σ p q hpq hsp) (MatchingSurgery.partner α hi hf p q hpq) :=
  Smoothing.genusZero (isolate σ p q) α hi hf p q hpq
    (isolate_p σ p q hpq hsp) (isolate_q σ p q) (isolate_genusZero σ p q hsp α hi hz)

variable (before after : O→V)
omit [Fintype O] in
/-- The graph endpoint conditions, not just the rose labels, survive the
backtracking deletion. The second occurrence really returns to the first
occurrence's starting vertex. -/
theorem consistent (h : BoundarySurgery.Consistent σ before after) (hq : after q=before p) :
    BoundarySurgery.Consistent (rotation σ p q hpq hsp)
      (fun x=>before x) (fun x=>after x) := by
  have he : before p=before (σ q) := hq.symm.trans (h q)
  intro x
  change after (x : O)=before (Equiv.swap p (σ q) (σ x))
  rw [MapEuler.swap_invariant before p (σ q) he]
  exact h x
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

abbrev Remaining := {x : O // x≠p ∧ x≠q}
def splice (x : O) : O := if α x=p then α q else if α x=q then α p else α x

include hi hfp hfq in
lemma splice_avoids (x : Remaining p q) : splice α p q x≠p ∧ splice α p q x≠q := by
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    have hqp : α q≠p := by
      intro h
      have h' : q=α p := (hi _).symm.trans (congrArg α h)
      exact x.property.2 (hx ▸ h'.symm)
    rw [splice,if_pos h1]
    exact ⟨hqp,hfq⟩
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      have hpq' : α p≠q := by
        intro h
        have h' : p=α q := (hi _).symm.trans (congrArg α h)
        exact x.property.1 (hx ▸ h'.symm)
      rw [splice,if_neg h1,if_pos h2]
      exact ⟨hfp,hpq'⟩
    · rw [splice,if_neg h1,if_neg h2]
      exact ⟨h1,h2⟩

def apply (x : Remaining p q) : Remaining p q := ⟨splice α p q x,splice_avoids α hi p q hfp hfq x⟩

include hpq in
lemma involutive : Function.Involutive (apply α hi p q hfp hfq) := by
  intro x
  apply Subtype.ext
  change splice α p q (splice α p q x)=x
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    have hs : splice α p q x=α q := by rw [splice,if_pos h1]
    rw [hs,splice,hi q,if_neg hpq.symm,if_pos rfl]
    exact hx
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      have hs : splice α p q x=α p := by rw [splice,if_neg h1,if_pos h2]
      rw [hs,splice,hi p,if_pos rfl]
      exact hx
    · have hs : splice α p q x=α x := by rw [splice,if_neg h1,if_neg h2]
      rw [hs,splice,hi x,if_neg x.property.1,if_neg x.property.2]

include hpq in
lemma distinct (x : Remaining p q) (hfx : α x≠x) : apply α hi p q hfp hfq x≠x := by
  intro he
  have he := congrArg Subtype.val he
  change splice α p q x=x at he
  by_cases h1 : α x=p
  · have hx : α p=x := (congrArg α h1).symm.trans (hi x)
    rw [splice,if_pos h1] at he
    exact hpq (α.injective (hx.trans he.symm))
  · by_cases h2 : α x=q
    · have hx : α q=x := (congrArg α h2).symm.trans (hi x)
      rw [splice,if_neg h1,if_pos h2] at he
      exact hpq (α.injective (he.trans hx.symm))
    · exact hfx (by simpa [splice,h1,h2] using he)

def partner : Equiv.Perm (Remaining p q) := ⟨apply α hi p q hfp hfq,apply α hi p q hfp hfq,involutive α hi p q hpq hfp hfq,involutive α hi p q hpq hfp hfq⟩

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))
include hinv hl hlabel in
lemma compatible (x : Remaining p q) :
    label (partner α hi p q hpq hfp hfq x)=inv (label x) := by
  change label (splice α p q x)=_
  by_cases h1 : α x=p
  · rw [splice,if_pos h1,hl,hlabel,hinv]
    exact (congrArg label h1).symm.trans (hl x)
  · by_cases h2 : α x=q
    · rw [splice,if_neg h1,if_pos h2,hl,←hlabel]
      exact (congrArg label h2).symm.trans (hl x)
    · rw [splice,if_neg h1,if_neg h2,hl]

end TorsionFreeZeroDivisors.PartialMatchingSurgery
namespace TorsionFreeZeroDivisors.PartialSmoothing
open scoped Classical
open DeleteCycle
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α)
  (p q : O) (hpq : p≠q) (hfp : α p≠p) (hfq : α q≠q) (hsp : σ p=q) (hsq : σ q=p)

include hsp hsq in
lemma rotation_invariant (x : O) : (σ x≠p ∧ σ x≠q) ↔ (x≠p ∧ x≠q) := by
  constructor
  · rintro ⟨hp,hq⟩
    exact ⟨fun h=>hq (h ▸ hsp),fun h=>hp (h ▸ hsq)⟩
  · rintro ⟨hp,hq⟩
    exact ⟨fun h=>hq (σ.injective (h.trans hsq.symm)),fun h=>hp (σ.injective (h.trans hsp.symm))⟩
def rotation : Equiv.Perm (PartialMatchingSurgery.Remaining p q) :=
  σ.subtypePerm (rotation_invariant σ p q hsp hsq)

abbrev r := α p
include hfp in
lemma pr : p≠r α p := (hfp).symm
include hfp hpq in
lemma rename_invariant (x : O) :
    (Equiv.swap q (r α p) x≠p ∧ Equiv.swap q (r α p) x≠q) ↔ (x≠p ∧ x≠r α p) := by
  have hp : Equiv.swap q (r α p) p=p := Equiv.swap_apply_of_ne_of_ne hpq (pr α p hfp)
  have hr : Equiv.swap q (r α p) (r α p)=q := Equiv.swap_apply_right _ _
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨fun h=>h1 (h ▸ hp),fun h=>h2 (h ▸ hr)⟩
  · rintro ⟨h1,h2⟩
    exact ⟨fun h=>h1 ((Equiv.swap q (r α p)).injective (h.trans hp.symm)),
      fun h=>h2 ((Equiv.swap q (r α p)).injective (h.trans hr.symm))⟩
def flatten : BandEuler.Residual p (r α p) (pr α p hfp) ≃ PartialMatchingSurgery.Remaining p (r α p) where
  toFun x := ⟨BandEuler.val p (r α p) (pr α p hfp) x,
    BandEuler.val_ne_p p (r α p) (pr α p hfp) x,BandEuler.val_ne_q p (r α p) (pr α p hfp) x⟩
  invFun x := ⟨⟨x,x.property.1⟩,fun he=>x.property.2 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl
def rename : PartialMatchingSurgery.Remaining p (r α p) ≃ PartialMatchingSurgery.Remaining p q :=
  (Equiv.swap q (r α p)).subtypeEquiv (fun x=>(rename_invariant α p q hpq hfp x).symm)
def coordinates : BandEuler.Residual p (r α p) (pr α p hfp) ≃ PartialMatchingSurgery.Remaining p q :=
  (flatten α p hfp).trans (rename α p q hpq hfp)
lemma coordinates_val (x : BandEuler.Residual p (r α p) (pr α p hfp)) :
    (coordinates α p q hpq hfp x).val=Equiv.swap q (r α p) (BandEuler.val p (r α p) (pr α p hfp) x) := rfl

lemma partner_commutes (x : BandEuler.Residual p (r α p) (pr α p hfp)) :
    coordinates α p q hpq hfp (BandEuler.partner α hi p (r α p) (pr α p hfp) rfl x)=
      PartialMatchingSurgery.partner α hi p q hpq hfp hfq (coordinates α p q hpq hfp x) := by
  apply Subtype.ext
  rw [coordinates_val,BandEuler.partner_val]
  change Equiv.swap q (α p) (α (BandEuler.val p (α p) (pr α p hfp) x))=
    PartialMatchingSurgery.splice α p q (Equiv.swap q (α p) (BandEuler.val p (α p) (pr α p hfp) x))
  let v := BandEuler.val p (α p) (pr α p hfp) x
  change Equiv.swap q (α p) (α v)=PartialMatchingSurgery.splice α p q (Equiv.swap q (α p) v)
  have hvp : v≠p := BandEuler.val_ne_p _ _ _ x
  have hvr : v≠α p := BandEuler.val_ne_q _ _ _ x
  have havp : α v≠p := fun h=>hvr ((hi _).symm.trans (congrArg α h))
  have havr : α v≠α p := α.injective.ne hvp
  by_cases hvq : v=q
  · rw [hvq,Equiv.swap_apply_left,PartialMatchingSurgery.splice,hi p,if_pos rfl]
    have hαq : α q≠q := hfq
    have hαqr : α q≠α p := α.injective.ne hpq.symm
    exact Equiv.swap_apply_of_ne_of_ne hαq hαqr
  · rw [Equiv.swap_apply_of_ne_of_ne hvq hvr,PartialMatchingSurgery.splice,if_neg havp]
    by_cases havq : α v=q
    · rw [if_pos havq,havq,Equiv.swap_apply_left]
    · rw [if_neg havq,Equiv.swap_apply_of_ne_of_ne havq havr]

lemma bypass_value (f : Equiv.Perm O) (a : O) (x : Rest a) :
    (bypass f a x).val=if f x=a then f a else f x := by
  change Equiv.swap a (f a) (f x)=_
  by_cases h : f x=a
  · rw [if_pos h,h,Equiv.swap_apply_left]
  · rw [if_neg h,Equiv.swap_apply_of_ne_of_ne h (f.injective.ne x.property)]
lemma rotation_value (a b : O) (hab : a≠b) (x : BandEuler.Residual a b hab) :
    BandEuler.val a b hab (BandEuler.rotation σ a b hab x)=
      let f := BandEuler.switched σ a b
      let g := fun y=>if f y=a then f a else f y
      if g (BandEuler.val a b hab x)=b then g b else g (BandEuler.val a b hab x) := by
  let f := BandEuler.switched σ a b
  let g := fun y=>if f y=a then f a else f y
  change ((bypass (bypass f a) (BandEuler.q' a b hab) x).val).val=
    if g x.val.val=b then g b else g x.val.val
  have he : bypass f a x.val=BandEuler.q' a b hab ↔ g x.val.val=b := by
    rw [Subtype.ext_iff,bypass_value]
  by_cases hc : g x.val.val=b
  · rw [if_pos hc]
    have hv := bypass_value (bypass f a) (BandEuler.q' a b hab) x
    rw [if_pos (he.mpr hc)] at hv
    exact (congrArg Subtype.val hv).trans (bypass_value f a (BandEuler.q' a b hab))
  · rw [if_neg hc]
    have hv := bypass_value (bypass f a) (BandEuler.q' a b hab) x
    rw [if_neg (fun h=>hc (he.mp h))] at hv
    exact (congrArg Subtype.val hv).trans (bypass_value f a x.val)

include hsp hsq hpq in
lemma smoothing_value (r v : O) (hpr : p≠r) (hvp : v≠p) (hvr : v≠r) :
    let f := Equiv.swap p r*σ
    let g := fun y=>if f y=p then f p else f y
    Equiv.swap q r (if g v=r then g r else g v)=σ (Equiv.swap q r v) := by
  let f := Equiv.swap p r*σ
  let g := fun y=>if f y=p then f p else f y
  change Equiv.swap q r (if g v=r then g r else g v)=_
  by_cases hqr : q=r
  · subst r
    have hsvp : σ v≠p := fun h=>hvr (σ.injective (h.trans hsq.symm))
    have hsvq : σ v≠q := fun h=>hvp (σ.injective (h.trans hsp.symm))
    have hfv : f v=σ v := Equiv.swap_apply_of_ne_of_ne hsvp hsvq
    have hg : g v=σ v := by
      change (if f v=p then f p else f v)=σ v
      simp only [hfv,if_neg hsvp]
    rw [hg,if_neg hsvq,Equiv.swap_self]
    rfl
  · have hfp : f p=q := by
      dsimp only [f,Equiv.Perm.mul_apply]
      rw [hsp,Equiv.swap_apply_of_ne_of_ne hpq.symm hqr]
    have hG (y : O) (hyp : y≠p) (hyq : y≠q) : Equiv.swap q r (g y)=σ y := by
      have hsyp : σ y≠p := fun h=>hyq (σ.injective (h.trans hsq.symm))
      have hsyq : σ y≠q := fun h=>hyp (σ.injective (h.trans hsp.symm))
      by_cases hsyr : σ y=r
      · have hfy : f y=p := by simp only [f,Equiv.Perm.mul_apply,hsyr,Equiv.swap_apply_right]
        change Equiv.swap q r (if f y=p then f p else f y)=σ y
        rw [if_pos hfy,hfp,Equiv.swap_apply_left,hsyr]
      · have hfy : f y=σ y := by
          exact Equiv.swap_apply_of_ne_of_ne hsyp hsyr
        change Equiv.swap q r (if f y=p then f p else f y)=σ y
        simp only [hfy,if_neg hsyp,Equiv.swap_apply_of_ne_of_ne hsyq hsyr]
    by_cases hvq : v=q
    · have hfq : f q=r := by simp only [f,Equiv.Perm.mul_apply,hsq,Equiv.swap_apply_left]
      have hgq : g q=r := by
        change (if f q=p then f p else f q)=r
        simp only [hfq,if_neg hpr.symm]
      rw [hvq,hgq,if_pos rfl,Equiv.swap_apply_left]
      exact hG r hpr.symm (Ne.symm hqr)
    · have hgv : g v≠r := by
        intro he
        have hh := hG v hvp hvq
        rw [he,Equiv.swap_apply_right] at hh
        exact hvp (σ.injective (hh.symm.trans hsp.symm))
      rw [if_neg hgv,Equiv.swap_apply_of_ne_of_ne hvq hvr]
      exact hG v hvp hvq

lemma rotation_commutes (x : BandEuler.Residual p (r α p) (pr α p hfp)) :
    coordinates α p q hpq hfp (BandEuler.rotation σ p (r α p) (pr α p hfp) x)=
      rotation σ p q hsp hsq (coordinates α p q hpq hfp x) := by
  apply Subtype.ext
  rw [coordinates_val,rotation_value]
  exact smoothing_value σ p q hpq hsp hsq (r α p)
    (BandEuler.val p (r α p) (pr α p hfp) x) (pr α p hfp)
    (BandEuler.val_ne_p _ _ _ x) (BandEuler.val_ne_q _ _ _ x)

variable [Fintype O]
/-- Suppressing an actual two-occurrence boundary splices its matching partners,
including the already-paired case, and preserves combinatorial genus zero. -/
theorem genusZero (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero (rotation σ p q hsp hsq)
      (PartialMatchingSurgery.partner α hi p q hpq hfp hfq) := by
  let e := coordinates α p q hpq hfp
  let σ₀ := BandEuler.rotation σ p (r α p) (pr α p hfp)
  let α₀ := BandEuler.partner α hi p (r α p) (pr α p hfp) rfl
  have hz₀ : MapEuler.GenusZero σ₀ α₀ := BandEuler.genusZero_all σ α hi p
    (r α p) (pr α p hfp) rfl hz
  have h := MapConjugation.genusZero e σ₀ α₀ hz₀
  have hσ : e.permCongr σ₀=rotation σ p q hsp hsq := by
    apply Equiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [Equiv.permCongr_apply,e.symm_apply_apply]
    exact rotation_commutes σ α p q hpq hfp hsp hsq x
  have hα : e.permCongr α₀=PartialMatchingSurgery.partner α hi p q hpq hfp hfq := by
    apply Equiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [Equiv.permCongr_apply,e.symm_apply_apply]
    exact partner_commutes α hi p q hpq hfp hfq x
  rwa [hσ,hα] at h

end TorsionFreeZeroDivisors.PartialSmoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
variable {O : Type} [Fintype O] (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)
  (α : Equiv.Perm O) (hi : Function.Involutive α) (hfp : α p≠p) (hfq : α q≠q)
/-- The tightening operation also allows unrelated unpaired markers. Only the
actual two deleted letter occurrences are required to be nonfixed. -/
theorem partial_genusZero (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero (rotation σ p q hpq hsp)
      (PartialMatchingSurgery.partner α hi p q hpq hfp hfq) :=
  PartialSmoothing.genusZero (isolate σ p q) α hi p q hpq hfp hfq
    (isolate_p σ p q hpq hsp) (isolate_q σ p q) (isolate_genusZero σ p q hsp α hi hz)
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
lemma rotate_val {n : ℕ} (i : Fin n) :
    (finRotate n i).val=if i.val+1=n then 0 else i.val+1 := by
  cases n with
  | zero=>exact i.elim0
  | succ n=>
    rw [coe_finRotate]
    have hh : i=Fin.last n ↔ i.val+1=n+1 := by
      constructor
      · rintro rfl;rfl
      · intro successor_eq
        exact Fin.ext (Nat.add_right_cancel successor_eq)
    simp only [hh]
variable (n m : ℕ)
abbrev O := Fin (n+1)⊕Fin (m+1)
def split : Equiv.Perm (O n m) := Equiv.sumCongr (finRotate (n+1)) (finRotate (m+1))
def joined : Equiv.Perm (O n m) := Equiv.swap (.inl 0) (.inr 0)*split n m
lemma joined_commutes (x : O n m) :
    finSumFinEquiv (joined n m x)=finRotate ((n+1)+(m+1)) (finSumFinEquiv x) := by
  cases x with
  | inl i=>
    by_cases hi : i=Fin.last n
    · subst i
      simp only [joined,split,Equiv.Perm.mul_apply,Equiv.sumCongr_apply,Sum.map_inl,
        finRotate_last,Equiv.swap_apply_left,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right]
      apply Fin.ext
      rw [rotate_val]
      simp only [Fin.val_natAdd,Fin.val_zero,add_zero,Fin.val_castAdd,Fin.val_last]
      rw [if_neg (by omega)]
    · have hn : finRotate (n+1) i≠0 := by
        intro hh
        have h : finRotate (n+1) i=finRotate (n+1) (Fin.last n) := hh.trans (finRotate_last (n:=n)).symm
        exact hi ((finRotate _).injective h)
      simp only [joined,split,Equiv.Perm.mul_apply,Equiv.sumCongr_apply,Sum.map_inl]
      rw [Equiv.swap_apply_of_ne_of_ne (by simpa using hn) (by simp)]
      simp only [finSumFinEquiv_apply_left]
      apply Fin.ext
      rw [Fin.val_castAdd,rotate_val,rotate_val]
      have hit : i.val < n := (Fin.lt_last_iff_ne_last).mpr hi
      simp only [Fin.val_castAdd]
      rw [if_neg (by omega),if_neg (by omega)]
  | inr i=>
    by_cases hi : i=Fin.last m
    · subst i
      simp only [joined,split,Equiv.Perm.mul_apply,Equiv.sumCongr_apply,Sum.map_inr,
        finRotate_last,Equiv.swap_apply_right,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right]
      apply Fin.ext
      rw [rotate_val]
      simp only [Fin.val_castAdd,Fin.val_zero,Fin.val_natAdd,Fin.val_last]
      rw [if_pos (by omega)]
    · have hn : finRotate (m+1) i≠0 := by
        intro hh
        have h : finRotate (m+1) i=finRotate (m+1) (Fin.last m) := hh.trans (finRotate_last (n:=m)).symm
        exact hi ((finRotate _).injective h)
      simp only [joined,split,Equiv.Perm.mul_apply,Equiv.sumCongr_apply,Sum.map_inr]
      rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hn)]
      simp only [finSumFinEquiv_apply_right]
      apply Fin.ext
      rw [Fin.val_natAdd,rotate_val,rotate_val]
      have hit : i.val < m := (Fin.lt_last_iff_ne_last).mpr hi
      simp only [Fin.val_natAdd]
      rw [if_neg (by omega),if_neg (by omega)]
      omega
lemma joined_conjugate : joined n m=finSumFinEquiv.symm.permCongr (finRotate ((n+1)+(m+1))) := by
  apply Equiv.ext
  intro x
  apply finSumFinEquiv.injective
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply,joined_commutes]
lemma joined_sameCycle (x y : O n m) : (joined n m).SameCycle x y := by
  rw [joined_conjugate]
  have hh := WordPairing.rotate_sameCycle (show 2≤(n+1)+(m+1) by omega)
    (finSumFinEquiv x) (finSumFinEquiv y)
  have ht := PermutationTransport.sameCycle finSumFinEquiv.symm (finRotate ((n+1)+(m+1))) hh
  simpa only [Equiv.symm_apply_apply] using ht

end TorsionFreeZeroDivisors.ContiguousSplit
namespace TorsionFreeZeroDivisors.BoundaryRefinement
open scoped Classical
open PermutationCycles
variable {O : Type}
/-- Finite sequences of actual vertex cuts. This retains the whole matching;
only cyclic boundary order changes. Cuts must occur on the same current cycle. -/
inductive Cuts : Equiv.Perm O → Equiv.Perm O → Prop
  | refl (σ) : Cuts σ σ
  | step (σ) (p q : O) (hne : p≠q) (hcycle : σ.SameCycle p q) :
      Cuts σ (Equiv.swap p q*σ)
  | trans {σ τ υ} : Cuts σ τ → Cuts τ υ → Cuts σ υ
variable [Fintype O]
lemma preserves {σ τ : Equiv.Perm O} (h : Cuts σ τ) (α : Equiv.Perm O)
    (hi : Function.Involutive α) (hz : MapEuler.GenusZero σ α) :
    MapEuler.GenusZero τ α := by
  induction h with
  | refl=>exact hz
  | step σ p q hn hc=>
    have hh := MapEuler.genusZero_vertexSplit σ α hi hz p q hn ((cycle_eq σ).mpr hc)
    convert hh using 1
  | trans h h' ih ih'=>exact ih' (ih hz)
lemma mapped_sameCycle {P : Type} (f : O→P) (σ : Equiv.Perm O) (τ : Equiv.Perm P)
    (hc : ∀x,τ (f x)=f (σ x)) {x y : O} (h : σ.SameCycle x y) :
    τ.SameCycle (f x) (f y) := by
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  have he : ∀k x,(τ^k) (f x)=f ((σ^k) x) := by
    intro k
    induction k with
    | zero=>intro x;rfl
    | succ k ih=>intro x;simp only [pow_succ',Equiv.Perm.mul_apply,ih,hc]
  exact ⟨(k:ℤ),by rw [zpow_natCast,he,hk]⟩
variable {P : Type} [Fintype P]
omit [Fintype P] in
lemma conjugate {σ τ : Equiv.Perm O} (h : Cuts σ τ) (e : O≃P) :
    Cuts (e.permCongr σ) (e.permCongr τ) := by
  induction h with
  | refl=>exact .refl _
  | step σ p q hn hc=>
    have hex : e.permCongr (Equiv.swap p q*σ)=Equiv.swap (e p) (e q)*e.permCongr σ := by
      apply Equiv.ext
      intro x
      simp only [Equiv.permCongr_apply,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
      have he₂ : σ (e.symm x)=p ↔ e (σ (e.symm x))=e p := e.injective.eq_iff.symm
      have he₃ : σ (e.symm x)=q ↔ e (σ (e.symm x))=e q := e.injective.eq_iff.symm
      split_ifs <;> first | rfl | simp_all
    rw [hex]
    exact .step _ _ _ (fun h=>hn (e.injective h)) (PermutationTransport.sameCycle e σ hc)
  | trans h h' ih ih'=>exact ih.trans ih'
omit [Fintype P] in
lemma left {σ τ : Equiv.Perm O} (h : Cuts σ τ) (ρ : Equiv.Perm P) :
    Cuts (Equiv.sumCongr σ ρ) (Equiv.sumCongr τ ρ) := by
  let : DecidableEq (O⊕P) := fun _ _=>Classical.propDecidable _
  induction h with
  | refl=>exact .refl _
  | step σ p q hn hc=>
    have hex : Equiv.sumCongr (Equiv.swap p q*σ) ρ=
        Equiv.swap (Sum.inl p) (Sum.inl q)*Equiv.sumCongr σ ρ := by
      apply Equiv.ext
      intro x
      cases x with
      | inl x=>simp [Equiv.Perm.mul_apply,Equiv.swap_apply_def];split_ifs <;> simp_all
      | inr x=>simp [Equiv.Perm.mul_apply,Equiv.swap_apply_def]
    rw [hex]
    exact .step _ _ _ (fun h=>hn (Sum.inl.inj h))
      (mapped_sameCycle Sum.inl σ (Equiv.sumCongr σ ρ) (fun _=>rfl) hc)
  | trans h h' ih ih'=>exact ih.trans ih'
lemma right {σ τ : Equiv.Perm P} (h : Cuts σ τ) (ρ : Equiv.Perm O) :
    Cuts (Equiv.sumCongr ρ σ) (Equiv.sumCongr ρ τ) := by
  have hh := conjugate (left h ρ) (Equiv.sumComm P O)
  convert hh using 1 <;> apply Equiv.ext <;> intro x <;> cases x <;> rfl

end TorsionFreeZeroDivisors.BoundaryRefinement
namespace TorsionFreeZeroDivisors.BlockBoundary
open scoped Classical
open BoundaryRefinement
lemma fin_cut (n m : ℕ) : Cuts
    (finSumFinEquiv.symm.permCongr (finRotate (n+m)))
    (Equiv.sumCongr (finRotate n) (finRotate m)) := by
  cases n with
  | zero=>
    have he : finSumFinEquiv.symm.permCongr (finRotate (0+m))=
        Equiv.sumCongr (finRotate 0) (finRotate m) := by
      apply Equiv.ext
      intro x
      cases x with
      | inl x=>exact x.elim0
      | inr x=>
        apply finSumFinEquiv.injective
        simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply,
          Equiv.sumCongr_apply,Sum.map_inr,finSumFinEquiv_apply_right]
        simp
        apply Fin.ext
        simp [Fin.val_add]
    rw [he];exact .refl _
  | succ n=>
    cases m with
    | zero=>
      have he : finSumFinEquiv.symm.permCongr (finRotate ((n+1)+0))=
          Equiv.sumCongr (finRotate (n+1)) (finRotate 0) := by
        apply Equiv.ext
        intro x
        cases x with
        | inr x=>exact x.elim0
        | inl x=>
          apply finSumFinEquiv.injective
          simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply,
            Equiv.sumCongr_apply,Sum.map_inl,finSumFinEquiv_apply_left]
          congr 1
      rw [he];exact .refl _
    | succ m=>
      rw [←ContiguousSplit.joined_conjugate n m]
      have hh := Cuts.step (ContiguousSplit.joined n m)
        (Sum.inl (0 : Fin (n+1))) (Sum.inr (0 : Fin (m+1)))
        (by simp) (ContiguousSplit.joined_sameCycle n m _ _)
      have he : Equiv.swap (Sum.inl (0 : Fin (n+1))) (Sum.inr (0 : Fin (m+1))) *
          ContiguousSplit.joined n m=ContiguousSplit.split n m := by
        apply Equiv.ext
        intro x
        simp only [ContiguousSplit.joined,Equiv.Perm.mul_apply]
        convert Equiv.swap_apply_self (Sum.inl (0 : Fin (n+1)))
          (Sum.inr (0 : Fin (m+1))) (ContiguousSplit.split n m x) using 1
      have hh' : Cuts (ContiguousSplit.joined n m)
          (Equiv.swap (Sum.inl (0 : Fin (n+1))) (Sum.inr (0 : Fin (m+1))) *
          ContiguousSplit.joined n m) := by
        convert hh using 1
        apply Equiv.ext
        intro x
        simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_def]
        split_ifs <;> rfl
      rw [he] at hh'
      exact hh'
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

def coordinates : (ns : List ℕ)→Occ ns≃Fin ns.sum
  | []=>@Equiv.equivOfIsEmpty Empty (Fin 0) inferInstance inferInstance
  | _n::ns=>(Equiv.sumCongr (Equiv.refl _) (coordinates ns)).trans finSumFinEquiv

def rotation : (ns : List ℕ)→Equiv.Perm (Occ ns)
  | []=>1
  | n::ns=>Equiv.sumCongr (finRotate n) (rotation ns)
def full (ns : List ℕ) : Equiv.Perm (Occ ns) :=
  (coordinates ns).symm.permCongr (finRotate ns.sum)
/-- Split the flattened boundary at every literal word boundary. The
matching is retained in full, including pairs joining different blocks. -/
theorem refinement (ns : List ℕ) : Cuts (full ns) (rotation ns) := by
  induction ns with
  | nil=>
    have he : full []=rotation [] := by
      apply Equiv.ext
      intro x
      exact Empty.elim x
    rw [he];exact .refl _
  | cons n ns ih=>
    let e : Fin n⊕Fin ns.sum≃Occ (n::ns) :=
      Equiv.sumCongr (Equiv.refl _) (coordinates ns).symm
    have hh := conjugate (fin_cut n ns.sum) e
    have he₁ : e.permCongr (finSumFinEquiv.symm.permCongr (finRotate (n+ns.sum)))=
        full (n::ns) := by
      rfl
    have he₂ : e.permCongr (Equiv.sumCongr (finRotate n) (finRotate ns.sum))=
        Equiv.sumCongr (finRotate n) (full ns) := by
      apply Equiv.ext
      intro x
      cases x <;> rfl
    rw [he₁,he₂] at hh
    exact hh.trans (right ih (finRotate n))
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
lemma total_append (s t : List (Term (A:=A) (I:=I))) : total rel (s++t)=total rel s+total rel t := by
  simp only [total,List.map_append,List.sum_append]
lemma total_reverse_flip (s : List (Term (A:=A) (I:=I))) : total rel (s.reverse.map Term.flip)= -total rel s := by
  have hf (t : Term (A:=A) (I:=I)) : term rel t.flip= -term rel t := by
    obtain ⟨i,b,c⟩ := t
    cases b <;> simp [term,Term.flip]
  simp only [total,List.map_map,Function.comp_def,hf,List.map_reverse,List.sum_reverse,List.sum_neg]
variable (hz : ∀ts : List (Term (A:=A) (I:=I)),FreeGroup.mk (word rel ts)=1→total rel ts=0)
include hz in
lemma total_eq {s t : List (Term (A:=A) (I:=I))}
    (hst : FreeGroup.mk (word rel s)=FreeGroup.mk (word rel t)) : total rel s=total rel t := by
  have hword : FreeGroup.mk (word rel (s++t.reverse.map Term.flip))=1 := by
    rw [word_append,word_reverse_flip,←FreeGroup.mul_mk,←FreeGroup.inv_mk,hst,mul_inv_cancel]
  have h := hz _ hword
  rw [total_append,total_reverse_flip] at h
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)

def area (x : N rel) : CellModule.Module (G rel) I := total rel (Classical.choose (expansion rel x.property))
include hz in
lemma area_eq (x : N rel) (ts : List (Term (A:=A) (I:=I)))
    (hts : FreeGroup.mk (word rel ts)=x.val) : area rel x=total rel ts := by
  exact total_eq rel hz ((Classical.choose_spec (expansion rel x.property)).trans hts.symm)
include hz in
lemma area_mul (x y : N rel) : area rel (x*y)=area rel x+area rel y := by
  obtain ⟨s,hs⟩ := expansion rel x.property
  obtain ⟨t,ht⟩ := expansion rel y.property
  rw [area_eq rel hz x s hs,area_eq rel hz y t ht,area_eq rel hz (x*y) (s++t) (by
    rw [word_append,←FreeGroup.mul_mk,hs,ht];rfl),total_append]
include hz in
lemma area_one : area rel 1=0 := by
  exact (area_eq rel hz 1 [] rfl).trans rfl

def conjugate (w : FreeGroup A) (x : N rel) : N rel :=
  ⟨w*x.val*w⁻¹,(Subgroup.normalClosure_normal (s:=relations rel)).conj_mem _ x.property w⟩
def move (w : FreeGroup A) (t : Term (A:=A) (I:=I)) : Term (A:=A) (I:=I) :=
  ⟨t.index,t.positive,w.toWord++t.connector⟩
lemma move_mk (w : FreeGroup A) (t : Term (A:=A) (I:=I)) :
    FreeGroup.mk ((move w t).word rel)=w*FreeGroup.mk (t.word rel)*w⁻¹ := by
  simp only [move,Term.word,Term.core,←FreeGroup.mul_mk,←FreeGroup.inv_mk,FreeGroup.mk_toWord,mul_inv_rev]
  group
  rfl
lemma move_word (w : FreeGroup A) (ts : List (Term (A:=A) (I:=I))) :
    FreeGroup.mk (word rel (ts.map (move w)))=w*FreeGroup.mk (word rel ts)*w⁻¹ := by
  induction ts with
  | nil=>change (1 : FreeGroup A)=w*1*w⁻¹; simp
  | cons t ts ih=>
    change FreeGroup.mk ((move w t).word rel++word rel (ts.map (move w)))=
      w*FreeGroup.mk (t.word rel++word rel ts)*w⁻¹
    rw [←FreeGroup.mul_mk,move_mk,ih,←FreeGroup.mul_mk]
    group
lemma move_term (w : FreeGroup A) (t : Term (A:=A) (I:=I)) :
    term rel (move w t)=translate (q rel w) (term rel t) := by
  simp only [term,move,←FreeGroup.mul_mk,FreeGroup.mk_toWord,map_mul]
  split <;> simp only [translate_single,map_neg]
lemma move_total (w : FreeGroup A) (ts : List (Term (A:=A) (I:=I))) :
    total rel (ts.map (move w))=translate (q rel w) (total rel ts) := by
  simp only [total,List.map_map,Function.comp_def,move_term,map_list_sum]
include hz in
lemma area_conjugate (w : FreeGroup A) (x : N rel) :
    area rel (conjugate rel w x)=translate (q rel w) (area rel x) := by
  obtain ⟨s,hs⟩ := expansion rel x.property
  rw [area_eq rel hz x s hs,area_eq rel hz (conjugate rel w x) (s.map (move w)) (by
    rw [move_word,hs];rfl),move_total]

def d₂ : CellModule.Module (G rel) I→+CellModule.Module (G rel) A :=
  Finsupp.liftAddHom (fun p=>zmultiplesHom _ (translate p.1 (fox (q rel) (FreeGroup.mk (rel p.2)))))
@[simp] lemma d₂_single (p : G rel×I) (z : ℤ) :
    d₂ rel (Finsupp.single p z)=z • translate p.1 (fox (q rel) (FreeGroup.mk (rel p.2))) := by
  simp [d₂]
lemma q_rel (i : I) : q rel (FreeGroup.mk (rel i))=1 := PresentedGroup.one_of_mem ⟨i,rfl⟩
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
lemma loop_one (g : G rel) : loop rel g 1=1 := by
  apply Subtype.ext
  simp [loop]
lemma loop_mul (g : G rel) (w u : FreeGroup A) :
    loop rel g (w*u)=loop rel g w*loop rel (g*q rel w) u := by
  apply Subtype.ext
  simp only [loop,Subgroup.coe_mul,map_mul,mul_assoc]
  group
include hz in
lemma area_loop_mul (g : G rel) (w u : FreeGroup A) :
    area rel (loop rel g (w*u))=area rel (loop rel g w)+area rel (loop rel (g*q rel w) u) := by
  rw [loop_mul,area_mul rel hz]
include hz in
lemma area_loop_inv (g : G rel) (w : FreeGroup A) :
    area rel (loop rel g w⁻¹)= -area rel (loop rel (g*(q rel w)⁻¹) w) := by
  have h := area_loop_mul rel hz g w⁻¹ w
  rw [inv_mul_cancel,loop_one,area_one rel hz,map_inv] at h
  exact eq_neg_of_add_eq_zero_left h.symm

def retract : CellModule.Module (G rel) A→+CellModule.Module (G rel) I :=
  Finsupp.liftAddHom (fun p=>zmultiplesHom _ (area rel (loop rel p.1 (FreeGroup.of p.2))))
@[simp] lemma retract_single (p : G rel×A) (z : ℤ) :
    retract rel (Finsupp.single p z)=z • area rel (loop rel p.1 (FreeGroup.of p.2)) := by
  simp [retract]
include hz in
lemma retract_fox (w : FreeGroup A) (g : G rel) :
    retract rel (translate g (fox (q rel) w))=area rel (loop rel g w) := by
  induction w using FreeGroup.induction_on generalizing g with
  | C1=>rw [fox_one,map_zero,map_zero,loop_one,area_one rel hz]
  | of a=>simp only [fox_of,translate_single,mul_one,retract_single,one_zsmul]
  | inv_of a ih=>
    rw [fox_inv,map_neg,map_neg,←translate_mul,ih,area_loop_inv rel hz]
  | mul w u hw hu=>
    rw [fox_mul,map_add,map_add,←translate_mul,hw,hu,area_loop_mul rel hz]
include hz in
lemma area_rel (i : I) : area rel ⟨FreeGroup.mk (rel i),Subgroup.subset_normalClosure ⟨i,rfl⟩⟩=
    Finsupp.single (1,i) 1 := by
  let t : Term (A:=A) (I:=I) := ⟨i,true,[]⟩
  have ht : FreeGroup.mk (word rel [t])=FreeGroup.mk (rel i) := by
    simp [word,Term.word,Term.core,t]
  rw [area_eq rel hz _ [t] ht]
  simp [total,term,t,←FreeGroup.one_eq_mk]
include hz in
lemma retract_d₂_single (g : G rel) (i : I) :
    retract rel (d₂ rel (Finsupp.single (g,i) 1))=Finsupp.single (g,i) 1 := by
  rw [d₂_single,one_zsmul,retract_fox rel hz]
  have he : loop rel g (FreeGroup.mk (rel i))=
      conjugate rel (sectionWord rel g) ⟨FreeGroup.mk (rel i),Subgroup.subset_normalClosure ⟨i,rfl⟩⟩ := by
    apply Subtype.ext
    simp only [loop,conjugate,q_rel,mul_one]
  rw [he,area_conjugate rel hz,area_rel rel hz,sectionWord_q,translate_single,mul_one]
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
end TorsionFreeZeroDivisors.SplitModel

namespace TorsionFreeZeroDivisors.RelationModel
open AlgebraicPictures RelationArea
variable {A I : Type} (rel : I→List (A×Bool))
  (hz : ∀ts : List (Term (A:=A) (I:=I)),FreeGroup.mk (word rel ts)=1→total rel ts=0)
local instance : TopologicalSpace (G rel) := ⊥
local instance : DiscreteTopology (G rel) := ⟨rfl⟩
def generators : A→G rel := PresentedGroup.of
lemma lift_generators : FreeGroup.lift (generators rel)=q rel := by ext a;rfl
include hz in
theorem has_model [Finite A] [Finite I] [Nonempty I] : HasFiniteTwoDimensionalClassifyingSpace (G rel) := by
  apply SplitModel.has_model (generators rel) (fun i=>FreeGroup.mk (rel i))
    (fun i=>by rw [lift_generators];exact q_rel rel i)
    (by rw [lift_generators];exact PresentedGroup.mk_surjective _)
    (by rw [lift_generators];exact QuotientGroup.ker_mk' _)
    (RelationSplit.retract rel)
  intro g i
  rw [lift_generators]
  have h:=RelationSplit.retract_d₂_single rel hz g i
  simpa only [RelationArea.d₂_single,one_zsmul] using h
end TorsionFreeZeroDivisors.RelationModel

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.CycleLists
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
variable (rep : Cycle f→O) (hrep : ∀c,cycle f (rep c)=c)
end TorsionFreeZeroDivisors.CycleLists

namespace TorsionFreeZeroDivisors.FinitePicture.Data
open scoped Classical
open PermutationCycles CycleLists
variable {V D A O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D} {label : D→A} {inv : A→A} {x y : V} (hxy : x≠y)

end TorsionFreeZeroDivisors.FinitePicture.Data

namespace TorsionFreeZeroDivisors.ComparedBlocks.Comparisons
open scoped Classical
open BlockAlignment
end TorsionFreeZeroDivisors.ComparedBlocks.Comparisons
namespace TorsionFreeZeroDivisors.SampleGraph.Picture
open scoped Classical
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep} {z w : VA rep⊕VB rep} {O : Type} [Fintype O] (hzw : z≠w) (hz : z=Sum.inl x ∨ z=Sum.inr y)

end TorsionFreeZeroDivisors.SampleGraph.Picture

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
open BlockBoundary
variable {A : Type*}
abbrev lengths (ws : List (List A)) : List ℕ := ws.map List.length
abbrev Occ (ws : List (List A)) := BlockBoundary.Occ (lengths ws)
lemma total_length (ws : List (List A)) : (lengths ws).sum=ws.flatten.length := by
  induction ws with
  | nil=>rfl
  | cons w ws ih=>simpa only [lengths,List.map_cons,List.sum_cons,List.flatten_cons,List.length_append] using congrArg (w.length+·) ih
def coordinates (ws : List (List A)) : Occ ws≃Fin ws.flatten.length :=
  (BlockBoundary.coordinates (lengths ws)).trans (finCongr (total_length ws))
def letter : (ws : List (List A))→Occ ws→A
  | [],x=>Empty.elim x
  | w::ws,x=>Sum.elim w.get (letter ws) x
lemma coordinates_inl (w : List A) (ws : List (List A)) (x : Fin w.length) :
    (coordinates (w::ws) (.inl x)).val=x.val := rfl
lemma letter_eq (ws : List (List A)) (x : Occ ws) :
    letter ws x=ws.flatten.get (coordinates ws x) := by
  induction ws with
  | nil=>exact Empty.elim x
  | cons w ws ih=>
    cases x with
    | inl x=>
      change w[x.val]=((w++ws.flatten).get _)
      simp only [List.get_eq_getElem,coordinates_inl]
      rw [List.getElem_append_left x.isLt]
    | inr x=>
      rw [show letter (w::ws) (.inr x)=letter ws x from rfl,ih]
      change ws.flatten[(coordinates ws x).val]=
        (w++ws.flatten)[w.length+(coordinates ws x).val]'(by
          simpa only [List.length_append] using Nat.add_lt_add_left (coordinates ws x).isLt w.length)
      simpa only [Nat.add_comm] using List.getElem_append_right' w (coordinates ws x).isLt
lemma finRotate_congr {n m : ℕ} (h : n=m) :
    (finCongr h).symm.permCongr (finRotate m)=finRotate n := by subst m;rfl
lemma full_eq (ws : List (List A)) :
    (coordinates ws).symm.permCongr (finRotate ws.flatten.length)=
      BlockBoundary.full (lengths ws) := by
  change (BlockBoundary.coordinates (lengths ws)).symm.permCongr
    ((finCongr (total_length ws)).symm.permCongr (finRotate ws.flatten.length))=_
  rw [finRotate_congr]
  rfl
/-- A full inverse-letter matching on the separate literal word boundaries,
with actual combinatorial genus zero. This is not a PL-picture assertion. -/
structure Matching (inv : A→A) (ws : List (List A)) where
  partner : Equiv.Perm (Occ ws)
  involutive : Function.Involutive partner
  fixed_free : ∀x,partner x≠x
  compatible : ∀x,letter ws (partner x)=inv (letter ws x)
  genusZero : MapEuler.GenusZero (BlockBoundary.rotation (lengths ws)) partner

def ofDisk {inv : A→A} (ws : List (List A))
    (d : WordPairing.Data inv ws.flatten.get) : Matching inv ws where
  partner := (coordinates ws).symm.permCongr d.partner
  involutive := PermutationTransport.involutive _ _ d.involutive
  fixed_free := PermutationTransport.fixed_free _ _ d.distinct
  compatible x := by
    simp only [letter_eq,Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
    exact d.compatible _
  genusZero := by
    have hh := MapConjugation.genusZero (coordinates ws).symm _ _ d.genusZero
    rw [full_eq] at hh
    exact BoundaryRefinement.preserves (BlockBoundary.refinement (lengths ws)) _
      (PermutationTransport.involutive _ _ d.involutive) hh

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.AlgebraicPictures
open FreeGroup
variable {A I : Type*} (rel : I→List (A×Bool)) (outer : List (A×Bool))

end TorsionFreeZeroDivisors.AlgebraicPictures

namespace TorsionFreeZeroDivisors.CyclicCaps
open scoped Classical
variable {R : Type} (n : ℕ)
abbrev O := Fin (n+2)⊕R
abbrev p : O (R:=R) n := .inl (Fin.last (n+1))
abbrev q : O (R:=R) n := .inl 0
lemma distinct : p (R:=R) n≠q n := by
  intro h
  have he := congrArg (fun x : Fin (n+2)=>x.val) (Sum.inl.inj h)
  simp only [Fin.val_last,Fin.val_zero] at he
  omega
def raise (i : Fin n) : Fin (n+2) := ⟨i.val+1,by omega⟩
def embed : Fin n⊕R→MatchingSurgery.Remaining (p (R:=R) n) (q n)
  | .inl i=>⟨.inl (raise n i),by
      constructor <;> intro h
      · have hh := congrArg Fin.val (Sum.inl.inj h)
        simp only [raise,Fin.val_last] at hh
        omega
      · have hh := congrArg Fin.val (Sum.inl.inj h)
        simp only [raise,Fin.val_zero] at hh
        omega⟩
  | .inr r=>⟨.inr r,by simp [p,q]⟩
lemma embed_injective : Function.Injective (embed (R:=R) n) := by
  intro x y he
  have hh := congrArg Subtype.val he
  cases x <;> cases y
  · apply congrArg Sum.inl
    apply Fin.ext
    have hh := congrArg Fin.val (Sum.inl.inj hh)
    simpa only [raise,embed,Nat.add_right_cancel_iff] using hh
  · cases hh
  · cases hh
  · exact congrArg Sum.inr (Sum.inr.inj hh)
lemma embed_surjective : Function.Surjective (embed (R:=R) n) := by
  rintro ⟨x,hp,hq⟩
  cases x with
  | inl i=>
    have hi0 : i.val≠0 := fun h=>hq (congrArg Sum.inl (Fin.ext h))
    have hilast : i.val≠n+1 := fun h=>hp (congrArg Sum.inl (Fin.ext h))
    let j : Fin n := ⟨i.val-1,by omega⟩
    refine ⟨.inl j,?_⟩
    apply Subtype.ext
    apply congrArg Sum.inl
    apply Fin.ext
    change (i.val-1)+1=i.val
    omega
  | inr r=>exact ⟨.inr r,rfl⟩
def coordinates : (Fin n⊕R)≃MatchingSurgery.Remaining (p (R:=R) n) (q n) :=
  Equiv.ofBijective (embed n) ⟨embed_injective n,embed_surjective n⟩
variable (ρ : Equiv.Perm R)
def rotation : Equiv.Perm (O (R:=R) n) := Equiv.sumCongr (finRotate (n+2)) ρ
lemma next : rotation n ρ (p n)=q n := by simp [rotation,p,q]
lemma rotation_commutes (x : Fin n⊕R) :
    Tightening.rotation (rotation n ρ) (p n) (q n) (distinct n) (next n ρ) (coordinates n x)=
      coordinates n (Equiv.sumCongr (finRotate n) ρ x) := by
  let : DecidableEq (O (R:=R) n) := fun _ _=>Classical.propDecidable _
  apply Subtype.ext
  change Equiv.swap (p n) (rotation n ρ (q n))
    (rotation n ρ (embed n x))=(embed n (Equiv.sumCongr (finRotate n) ρ x)).val
  cases x with
  | inr r=>simp [rotation,embed,p,q,Equiv.swap_apply_def]
  | inl i=>
    have hr : (finRotate (n+2) (raise n i)).val=i.val+2 := by
      rw [ContiguousSplit.rotate_val]
      split_ifs with h
      all_goals dsimp only [raise] at *
      all_goals omega
    have hz : (finRotate (n+2) (0 : Fin (n+2))).val=1 := by
      rw [ContiguousSplit.rotate_val,if_neg (by simp only [Fin.val_zero];omega)]
      rfl
    by_cases hi : i.val+1=n
    · have hp : rotation n ρ (embed (R:=R) n (.inl i)).val=p n := by
        apply congrArg Sum.inl
        apply Fin.ext
        exact hr.trans (by simp only [Fin.val_last];omega)
      rw [hp,Equiv.swap_apply_left]
      apply congrArg Sum.inl
      apply Fin.ext
      change (finRotate (n+2) (0 : Fin (n+2))).val=(finRotate n i).val+1
      rw [hz,ContiguousSplit.rotate_val,if_pos hi]
    · have hp : rotation n ρ (embed (R:=R) n (.inl i)).val≠p n := by
        intro hh
        have hh := congrArg Fin.val (Sum.inl.inj hh)
        change (finRotate (n+2) (raise n i)).val=n+1 at hh
        rw [hr] at hh
        omega
      have hq : rotation n ρ (embed (R:=R) n (.inl i)).val≠rotation n ρ (q n) := by
        intro hh
        have hh := (rotation n ρ).injective hh
        exact (embed (R:=R) n (.inl i)).property.2 hh
      rw [Equiv.swap_apply_of_ne_of_ne hp hq]
      apply congrArg Sum.inl
      apply Fin.ext
      change (finRotate (n+2) (raise n i)).val=(finRotate n i).val+1
      rw [hr,ContiguousSplit.rotate_val,if_neg hi]
lemma rotation_conjugate :
    Tightening.rotation (rotation n ρ) (p n) (q n) (distinct n) (next n ρ)=
      (coordinates n).permCongr (Equiv.sumCongr (finRotate n) ρ) := by
  apply Equiv.ext
  intro x
  obtain ⟨x,rfl⟩ := (coordinates n).surjective x
  rw [rotation_commutes]
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
variable [Fintype R]
variable (α : Equiv.Perm (O (R:=R) n)) (hi : Function.Involutive α) (hf : ∀x,α x≠x)
def partner : Equiv.Perm (Fin n⊕R) :=
  (coordinates n).symm.permCongr (MatchingSurgery.partner α hi hf (p n) (q n) (distinct n))
omit [Fintype R] in
lemma involutive : Function.Involutive (partner n α hi hf) :=
  PermutationTransport.involutive _ _ (MatchingSurgery.involutive α hi hf (p n) (q n) (distinct n))
omit [Fintype R] in
lemma fixed_free (x : Fin n⊕R) : partner n α hi hf x≠x :=
  PermutationTransport.fixed_free _ _ (MatchingSurgery.distinct α hi hf (p n) (q n) (distinct n)) x
/-- Removing the two literal end letters of a cyclic block preserves genus
zero with the forced matching splice. The enclosed block may be empty. -/
theorem genusZero (hz : MapEuler.GenusZero (rotation n ρ) α) :
    MapEuler.GenusZero (Equiv.sumCongr (finRotate n) ρ) (partner n α hi hf) := by
  let : DecidableEq (O (R:=R) n) := fun _ _=>Classical.propDecidable _
  have hh := Tightening.genusZero (rotation n ρ) (p n) (q n) (distinct n) (next n ρ) α hi hf hz
  rw [rotation_conjugate] at hh
  have ht := MapConjugation.genusZero (coordinates n).symm _ _ hh
  have he : (coordinates n).symm.permCongr
      ((coordinates n).permCongr (Equiv.sumCongr (finRotate n) ρ))=
      Equiv.sumCongr (finRotate n) ρ := by
    apply Equiv.ext
    intro x
    simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.symm_apply_apply]
  rw [he] at ht
  exact ht
variable {A : Type*} (inv : A→A) (hinv : Function.Involutive inv) (label : O (R:=R) n→A)
  (hc : ∀x,label (α x)=inv (label x)) (hl : label (q n)=inv (label (p n)))
include hinv hc hl in
omit [Fintype R] in
lemma compatible (x : Fin n⊕R) :
    label (embed n (partner n α hi hf x))=inv (label (embed n x)) := by
  have hh := MatchingSurgery.compatible α hi hf (p n) (q n) (distinct n) inv hinv label hc hl (coordinates n x)
  convert hh using 1
  change label ((coordinates n) ((coordinates n).symm ((MatchingSurgery.partner α hi hf (p n) (q n) (distinct n))
    (coordinates n x))))=_
  rw [Equiv.apply_symm_apply]
  all_goals rfl

end TorsionFreeZeroDivisors.CyclicCaps
namespace TorsionFreeZeroDivisors.WordBlocks

section
open scoped Classical
variable {A : Type*} {inv : A→A} {ws vs : List (List A)}
def Matching.rename (d : Matching inv ws) (e : Occ ws≃Occ vs)
    (hl : ∀x,letter vs (e x)=letter ws x)
    (hr : ∀x,e (BlockBoundary.rotation (lengths ws) x)=BlockBoundary.rotation (lengths vs) (e x)) :
    Matching inv vs where
  partner := e.permCongr d.partner
  involutive := PermutationTransport.involutive _ _ d.involutive
  fixed_free := PermutationTransport.fixed_free _ _ d.fixed_free
  compatible x := by
    obtain ⟨x,rfl⟩ := e.surjective x
    simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply,hl]
    exact d.compatible x
  genusZero := by
    have hh := MapConjugation.genusZero e _ _ d.genusZero
    have he : e.permCongr (BlockBoundary.rotation (lengths ws))=BlockBoundary.rotation (lengths vs) := by
      apply Equiv.ext
      intro x
      obtain ⟨x,rfl⟩ := e.surjective x
      simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using hr x
    rwa [he] at hh

def exchange {X Y Z : Type} : (X⊕(Y⊕Z))≃(Y⊕(X⊕Z)) where
  toFun
    | .inl x=>.inr (.inl x)
    | .inr (.inl y)=>.inl y
    | .inr (.inr z)=>.inr (.inr z)
  invFun
    | .inl y=>.inr (.inl y)
    | .inr (.inl x)=>.inl x
    | .inr (.inr z)=>.inr (.inr z)
  left_inv x := by rcases x with x|y|z <;> rfl
  right_inv x := by rcases x with x|y|z <;> rfl
lemma exchange_rotation {X Y Z : Type} (f : Equiv.Perm X) (g : Equiv.Perm Y) (h : Equiv.Perm Z)
    (x : X⊕(Y⊕Z)) :
    exchange (Equiv.sumCongr f (Equiv.sumCongr g h) x)=
      Equiv.sumCongr g (Equiv.sumCongr f h) (exchange x) := by
  rcases x with x|y|z <;> rfl
lemma exchange_letter {X Y Z : Type} (f : X→A) (g : Y→A) (h : Z→A) (x : X⊕(Y⊕Z)) :
    Sum.elim g (Sum.elim f h) (exchange x)=Sum.elim f (Sum.elim g h) x := by
  rcases x with x|y|z <;> rfl
variable {w : List A}

end
open scoped Classical
variable {A : Type*} {inv : A→A} (hinv : Function.Involutive inv)
variable (a : A) (w : List A) (ws : List (List A))
def capCoordinates : Occ ((a::(w++[inv a]))::ws)≃CyclicCaps.O (R:=Occ ws) w.length :=
  Equiv.sumCongr (finCongr (by simp)) (Equiv.refl _)
lemma capRotation : (capCoordinates (inv:=inv) a w ws).permCongr
    (BlockBoundary.rotation (lengths ((a::(w++[inv a]))::ws)))=
      CyclicCaps.rotation w.length (BlockBoundary.rotation (lengths ws)) := by
  apply Equiv.ext
  intro x
  cases x with
  | inl i=>
    apply congrArg Sum.inl
    have h : (a::(w++[inv a])).length=w.length+2 := by simp
    exact Equiv.congr_fun (finRotate_congr h.symm) i
  | inr i=>rfl
abbrev capLabel := fun x:CyclicCaps.O (R:=Occ ws) w.length=>
  letter ((a::(w++[inv a]))::ws) ((capCoordinates (inv:=inv) a w ws).symm x)
lemma capLabel_q : capLabel (inv:=inv) a w ws (CyclicCaps.q w.length)=a := by rfl
lemma capLabel_p : capLabel (inv:=inv) a w ws (CyclicCaps.p w.length)=inv a := by
  change (a::(w++[inv a]))[w.length+1]=inv a
  simp
lemma capLabel_embed (x : Occ (w::ws)) :
    capLabel (inv:=inv) a w ws (CyclicCaps.embed w.length x)=letter (w::ws) x := by
  cases x with
  | inl i=>
    change (a::(w++[inv a]))[i.val+1]=w[i.val]
    simp only [List.getElem_cons_succ,List.getElem_append_left i.isLt]
  | inr i=>rfl
/-- Tighten inverse end caps of one literal word boundary. The matching is
spliced, and its genuine genus zero remains valid even for an empty interior. -/
def Matching.removeCaps (d : Matching inv ((a::(w++[inv a]))::ws)) : Matching inv (w::ws) := by
  let e := capCoordinates (inv:=inv) a w ws
  let α := e.permCongr d.partner
  have hi : Function.Involutive α := PermutationTransport.involutive e d.partner d.involutive
  have hf : ∀x,α x≠x := PermutationTransport.fixed_free e d.partner d.fixed_free
  have hz : MapEuler.GenusZero (CyclicCaps.rotation w.length (BlockBoundary.rotation (lengths ws))) α := by
    have ht := MapConjugation.genusZero e _ _ d.genusZero
    rwa [show e.permCongr (BlockBoundary.rotation (lengths ((a::(w++[inv a]))::ws)))=
      CyclicCaps.rotation w.length (BlockBoundary.rotation (lengths ws)) from capRotation a w ws] at ht
  have hc : ∀x,capLabel (inv:=inv) a w ws (α x)=inv (capLabel (inv:=inv) a w ws x) := by
    intro x
    simpa only [capLabel,α,e,Equiv.permCongr_apply,Equiv.symm_apply_apply] using d.compatible (e.symm x)
  refine ⟨CyclicCaps.partner w.length α hi hf,
    CyclicCaps.involutive w.length α hi hf,
    CyclicCaps.fixed_free w.length α hi hf,?_,CyclicCaps.genusZero w.length _ α hi hf hz⟩
  intro x
  have hh := CyclicCaps.compatible w.length α hi hf inv hinv (capLabel (inv:=inv) a w ws) hc
    (by rw [capLabel_q,capLabel_p,hinv]) x
  rw [capLabel_embed a w ws (CyclicCaps.partner w.length α hi hf x),capLabel_embed a w ws x] at hh
  exact hh

end TorsionFreeZeroDivisors.WordBlocks

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
variable {A : Type*}
open FreeGroup

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.AlgebraicPictures
open FreeGroup
variable {A I : Type*} (rel : I→List (A×Bool))

end TorsionFreeZeroDivisors.AlgebraicPictures

namespace TorsionFreeZeroDivisors.GraphPresentation
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)
namespace Path
variable {Γ} {a b c : V}
def reverse : Path Γ a b→Path Γ b a := by
  intro p
  induction p with
  | nil v => exact .nil v
  | cons d p ih =>
    exact (ih.append (single (Γ:=Γ) (Γ.reverse d))).cast rfl
      (congrArg Γ.origin (PortGraph.reverse_reverse_apply Γ d))
@[simp] lemma eval_nil {G : Type*} [_root_.Group G] (label : D→G) (v : V) :
    (Path.nil (Γ:=Γ) v).eval label=1 := rfl
@[simp] lemma eval_cons {G : Type*} [_root_.Group G] (label : D→G) (d : D)
    (p : Path Γ (Γ.origin (Γ.reverse d)) b) :
    (Path.cons d p).eval label=label d*p.eval label := rfl
@[simp] lemma eval_append {G : Type*} [_root_.Group G] (label : D→G)
    (p : Path Γ a b) (q : Path Γ b c) :
    (p.append q).eval label=p.eval label*q.eval label := by
  induction p with
  | nil v => simp [append]
  | cons d p ih => simp only [append,eval_cons,ih,mul_assoc]
@[simp] lemma eval_single {G : Type*} [_root_.Group G] (label : D→G) (d : D) :
    (single (Γ:=Γ) d).eval label=label d := by simp [single]
@[simp] lemma eval_cast {G : Type*} [_root_.Group G] (label : D→G)
    {a b a' b' : V} (ha : a=a') (hb : b=b') (p : Path Γ a b) :
    (p.cast ha hb).eval label=p.eval label := by
  subst a'; subst b'; rfl
lemma eval_reverse {G : Type*} [_root_.Group G] (label : D→G)
    (hl : ∀ d,label (Γ.reverse d)=(label d)⁻¹) (p : Path Γ a b) :
    p.reverse.eval label=(p.eval label)⁻¹ := by
  induction p with
  | nil v => simp [reverse]
  | cons d p ih =>
    simp only [reverse] at ih
    simp only [reverse, eval_cast, eval_append,eval_single,ih,hl,eval_cons,mul_inv_rev]

lemma eval_map {G H : Type*} [_root_.Group G] [_root_.Group H] (f : G→*H)
    (label : D→G) (p : Path Γ a b) :
    p.eval (fun d => f (label d))=f (p.eval label) := by
  induction p with
  | nil v => simp
  | cons d p ih => simp only [eval_cons,ih,map_mul]

end Path
end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.GraphPresentation.Path
open PortSubdivision
variable {V D : Type} {Γ : PortGraph V D} {a b c : V}
def darts : {a b : V}→Path Γ a b→List D
  | _,_,.nil _=>[]
  | _,_,.cons d p=>d::darts p
@[simp] lemma darts_nil (v : V) : darts (Path.nil (Γ:=Γ) v)=[] := rfl
@[simp] lemma darts_cons (d : D) (p : Path Γ (Γ.origin (Γ.reverse d)) b) :
    darts (.cons d p)=d::darts p := rfl
@[simp] lemma darts_cast {a b a' b' : V} (ha : a=a') (hb : b=b') (p : Path Γ a b) :
    darts (p.cast ha hb)=p.darts := by subst a';subst b';rfl
lemma darts_append (p : Path Γ a b) (q : Path Γ b c) :
    (p.append q).darts=p.darts++q.darts := by
  induction p with
  | nil=>rfl
  | cons d p ih=>simp only [append,darts_cons,ih,List.cons_append]
lemma darts_reverse (p : Path Γ a b) : p.reverse.darts=p.darts.reverse.map Γ.reverse := by
  induction p with
  | nil=>rfl
  | cons d p ih=>
    simp only [reverse] at ih
    simp only [reverse,darts_cast,darts_append,single,darts_cons,darts_nil,
      List.reverse_cons,List.map_append,List.map_cons,List.map_nil]
    exact congrArg (fun l=>l++[Γ.reverse d]) ih
lemma empty_ends (p : Path Γ a b) (he : p.darts=[]) : a=b := by
  cases p with
  | nil=>rfl
  | cons d p=>simp only [darts_cons,List.cons_ne_nil] at he
lemma first_origin (p : Path Γ a b) (hn : p.darts≠[]) : Γ.origin (p.darts.head hn)=a := by
  cases p with
  | nil=>exact False.elim (hn rfl)
  | cons d p=>rfl
lemma last_origin (p : Path Γ a b) (hn : p.darts≠[]) :
    Γ.origin (Γ.reverse (p.darts.getLast hn))=b := by
  induction p with
  | nil=>exact False.elim (hn rfl)
  | cons d p ih=>
    by_cases he : p.darts=[]
    · simpa only [darts_cons,he,List.getLast_singleton] using p.empty_ends he
    · simpa only [darts_cons,List.getLast_cons he] using ih he
lemma chain (p : Path Γ a b) : p.darts.IsChain (fun d e=>Γ.origin (Γ.reverse d)=Γ.origin e) := by
  induction p with
  | nil=>exact List.IsChain.nil
  | cons d p ih=>
    rw [darts_cons,List.isChain_cons]
    refine ⟨?_,ih⟩
    intro e he
    have hn : p.darts≠[] := by intro h;simp [h] at he
    have hh : e=p.darts.head hn := by
      exact (by simpa only [List.head?_eq_some_head hn,Option.mem_def,Option.some.injEq] using he : p.darts.head hn=e).symm
    rw [hh]
    exact (p.first_origin hn).symm
variable {A : Type*} (label : D→A×Bool)
def letters (p : Path Γ a b) : List (A×Bool) := p.darts.map label
lemma letters_mk (p : Path Γ a b) :
    FreeGroup.mk (p.letters label)=p.eval (fun d=>FreeGroup.mk [label d]) := by
  induction p with
  | nil=>rfl
  | cons d p ih=>
    change FreeGroup.mk (label d::p.letters label)=_
    rw [show label d::p.letters label=[label d]++p.letters label from rfl,←FreeGroup.mul_mk,ih]
    rfl
lemma letters_reverse (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
    (p : Path Γ a b) : p.reverse.letters label=FreeGroup.invRev (p.letters label) := by
  simp only [letters,darts_reverse,List.map_map,FreeGroup.invRev,List.map_reverse]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro d _
  exact hl d

end TorsionFreeZeroDivisors.GraphPresentation.Path
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
variable {D A : Type*} (label : D→A)
lemma rotate_cast {n m : ℕ} (h : n=m) (i : Fin n) :
    finCongr h (finRotate n i)=finRotate m (finCongr h i) := by subst m;rfl

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open DeleteCycle MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.MarkerInsertion
open scoped Classical
open DeleteCycle
variable {O : Type} (σ α : Equiv.Perm O) (p : O)
/-- Insert an unpaired marker immediately before p. -/
def rotation : Equiv.Perm (Option O) := Equiv.swap none (some p)*Equiv.optionCongr σ
def partner : Equiv.Perm (Option O) := Equiv.optionCongr α
@[simp] lemma rotation_none : rotation σ p none=some p := by simp [rotation,Equiv.Perm.mul_apply]
@[simp] lemma partner_none : partner α none=none := rfl
variable [Fintype O]

end TorsionFreeZeroDivisors.MarkerInsertion
namespace TorsionFreeZeroDivisors.FinitePicture
open scoped Classical
open PortSubdivision
variable {V D A O : Type} [Fintype O] (Γ : PortGraph V D) (label : D→A) (inv : A→A) (x y : V)
  (σ α : Equiv.Perm O) (hi : Function.Involutive α) (hf : ∀i,α i≠i)
  (edge : O→D) (p : O)
  (hc : ∀i,label (edge (α i))=inv (label (edge i)))
  (hj : ∀i,σ i≠p → Γ.origin (Γ.reverse (edge i))=Γ.origin (edge (σ i)))
  (hp : Γ.origin (edge p)=x)
  (he : ∀i,σ i=p → Γ.origin (Γ.reverse (edge i))=y)
  (hz : MapEuler.GenusZero σ α)

end TorsionFreeZeroDivisors.FinitePicture

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GraphPresentation.Path
open PortSubdivision
variable {V D : Type} {Γ : PortGraph V D} {a b : V}
lemma join_rotation (p : Path Γ a b) (i : Fin p.darts.length)
    (hn : (finRotate p.darts.length i).val≠0) :
    Γ.origin (Γ.reverse (p.darts.get i))=Γ.origin (p.darts.get (finRotate p.darts.length i)) := by
  have hi : i.val+1≠p.darts.length := by
    intro he
    apply hn
    rw [ContiguousSplit.rotate_val,if_pos he]
  have hin : i.val+1<p.darts.length := by omega
  have hj := (List.isChain_iff_getElem.mp p.chain) i.val hin
  simpa only [List.get_eq_getElem,ContiguousSplit.rotate_val,if_neg hi] using hj
lemma end_rotation (p : Path Γ a b) (i : Fin p.darts.length)
    (hz : (finRotate p.darts.length i).val=0) :
    Γ.origin (Γ.reverse (p.darts.get i))=b := by
  have hi : i.val+1=p.darts.length := by
    rw [ContiguousSplit.rotate_val] at hz
    split_ifs at hz with h
    exact h
  have hn : p.darts≠[] := List.length_pos_iff.mp (by omega)
  have he : i.val=p.darts.length-1 := by omega
  simpa only [List.getLast_eq_getElem,List.get_eq_getElem,he] using p.last_origin hn
lemma first_get (p : Path Γ a b) (hn : 0<p.darts.length) : Γ.origin (p.darts.get ⟨0,hn⟩)=a := by
  simpa only [List.head_eq_getElem,List.get_eq_getElem] using p.first_origin (List.length_pos_iff.mp hn)
lemma closed_rotation (p : Path Γ a a) (i : Fin p.darts.length) :
    Γ.origin (Γ.reverse (p.darts.get i))=Γ.origin (p.darts.get (finRotate p.darts.length i)) := by
  by_cases hi : (finRotate p.darts.length i).val=0
  · rw [p.end_rotation i hi]
    have he : finRotate p.darts.length i=⟨0,by omega⟩ := Fin.ext hi
    rw [he]
    exact (p.first_get _).symm
  · exact p.join_rotation i hi

end TorsionFreeZeroDivisors.GraphPresentation.Path
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
open PortSubdivision GraphPresentation
variable {V D A : Type} (Γ : PortGraph V D) (label : D→A) (inv : A→A)
def AllClosed (ws : List (List D)) : Prop := ∀w∈ws,∃v,∃p : Path Γ v v,p.darts=w
lemma closed_consistent (ws : List (List D)) (hc : AllClosed Γ ws) (i : Occ ws) :
    Γ.origin (Γ.reverse (letter ws i))=Γ.origin (letter ws (BlockBoundary.rotation (lengths ws) i)) := by
  induction ws with
  | nil=>exact Empty.elim i
  | cons w ws ih=>
    cases i with
    | inl i=>
      obtain ⟨v,p,rfl⟩ := hc w (List.mem_cons_self)
      exact p.closed_rotation i
    | inr i=>exact ih (fun w hw=>hc w (List.mem_cons_of_mem _ hw)) i
variable {x y : V} (p : Path Γ x y) (hxy : x≠y) (ws : List (List D))

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.AlgebraicPictures
variable {A I : Type*} (rel : I→List (A×Bool))
open FreeGroup
end TorsionFreeZeroDivisors.AlgebraicPictures
namespace TorsionFreeZeroDivisors.InitialPicture
open scoped Classical
open PortSubdivision GraphPresentation AlgebraicPictures
variable {V D A I : Type} (Γ : PortGraph V D) (label : D→A×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
abbrev Loop := Σv,Path Γ v v
variable (rel : I→Loop Γ)
def relWords (i : I) : List (A×Bool) := (rel i).2.letters label
def signedLoop (t : Term (A:=A) (I:=I)) : Loop Γ :=
  if t.positive then rel t.index else ⟨(rel t.index).1,(rel t.index).2.reverse⟩
include hl in
lemma signedLoop_letters (t : Term (A:=A) (I:=I)) :
    (signedLoop Γ rel t).2.letters label=t.core (relWords Γ label rel) := by
  rcases t with ⟨i,b,c⟩
  cases b
  · exact Path.letters_reverse label hl _
  · rfl
variable {x y : V} (p : Path Γ x y)

end TorsionFreeZeroDivisors.InitialPicture

namespace TorsionFreeZeroDivisors.GraphPresentation

section
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)

variable {S : Type*} (letters : D→FreeGroup S) (R : Routes Γ)
def letter (d : D) : Group Γ letters R := PresentedGroup.mk _ (letters d)
lemma edge (d : D) : value Γ letters R (Γ.origin (Γ.reverse d))=
    value Γ letters R (Γ.origin d)*letter Γ letters R d := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (show relator Γ letters R d∈relations Γ letters R from ⟨d,rfl⟩)
  simpa only [value,letter,map_mul] using h.symm

/-- Every literal path has the source's path-order value, independently of
which route was chosen to define the finite fundamental-cycle presentation. -/
lemma path_value {a b : V} (p : Path Γ a b) :
    p.eval (letter Γ letters R)=(value Γ letters R a)⁻¹*value Γ letters R b := by
  induction p with
  | nil v => simp
  | cons d p ih =>
    rw [Path.eval_cons,ih,edge]
    group
lemma closed_value (a : V) (p : Path Γ a a) : p.eval (letter Γ letters R)=1 := by
  rw [path_value]
  simp

instance [Finite S] [Finite D] : _root_.Group.IsFinitelyPresented (Group Γ letters R) := by
  have : Finite (relations Γ letters R) := Set.finite_range (relator Γ letters R) |>.to_subtype
  infer_instance

end

open scoped Classical
open PortSubdivision
variable {V D A : Type} (Γ : PortGraph V D) (label : D→A×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d)) (R : Routes Γ)

end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.FinitePicture.Data
open scoped Classical
variable {V D A B O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D} {label : D→A} {inv : A→A} {x y : V} (f : A→B) (label' : D→B) (inv' : B→B) (hl : ∀d,label' d=f (label d)) (hf : ∀t,f (inv t)=inv' (f t))

end TorsionFreeZeroDivisors.FinitePicture.Data
namespace TorsionFreeZeroDivisors.GraphPresentation
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)
namespace Path
variable {Γ}
end Path

end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.ConcreteGroup

section
open scoped Classical BigOperators
open PortSubdivision TypedGraphs ConditionedMatchings SampleGraph
lemma freeLetter_inverse (t : Types.Letter) :
    freeLetter (Types.inverse t)=(freeLetter t)⁻¹ := by
  obtain ⟨⟨g,b⟩,rfl⟩ := Types.signedLetter.surjective t
  cases b <;> simp [freeLetter]
variable (rep : ℕ) (r : ActualPatternEvent.Match rep)
lemma labels_reverse (d : DA rep⊕DB rep) : labels rep ((Γ rep r).reverse d)=(labels rep d)⁻¹ := by
  simp only [labels,Function.comp_apply,SampleGraph.label_reverse,freeLetter_inverse]
def letter (t : Types.Letter) : G rep r := PresentedGroup.mk _ (freeLetter t)
instance : Group.IsFinitelyPresented (G rep r) := inferInstance
lemma edge (d : DA rep⊕DB rep) : value rep r ((Γ rep r).origin ((Γ rep r).reverse d))=
    value rep r ((Γ rep r).origin d)*letter rep r (SampleGraph.label rep d) :=
  GraphPresentation.edge _ _ _ d
end

open scoped Classical
open SampleGraph
variable {rep : ℕ} (r : ActualPatternEvent.Match rep)

end TorsionFreeZeroDivisors.ConcreteGroup

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ConcreteGroup
open scoped Classical
open SampleGraph
variable {rep : ℕ} (r : ActualPatternEvent.Match rep)

end TorsionFreeZeroDivisors.ConcreteGroup
namespace TorsionFreeZeroDivisors.SampleGraph.Picture
open scoped Classical
open BlockAlignment ComparedBlocks
variable {rep : ℕ} (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep)
  (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)

end TorsionFreeZeroDivisors.SampleGraph.Picture

namespace TorsionFreeZeroDivisors.BoundaryRefinement

section
open scoped Classical
variable {I : Type} {O : I→Type} [∀i,Fintype (O i)]
variable [Fintype I]

end

open scoped Classical BigOperators
end TorsionFreeZeroDivisors.BoundaryRefinement
namespace TorsionFreeZeroDivisors.BalancedGenus
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions BoundaryRefinement
variable {T A : Type} [Fintype T] (w : T→List A) (cap : ℕ) (hc : 0<cap)

end TorsionFreeZeroDivisors.BalancedGenus
namespace TorsionFreeZeroDivisors.ExtendComparisons
open scoped Classical
open BlockAlignment ComparedBlocks
variable {T E : Type} {len more : T→ℕ} (C : Comparisons (E:=E) len)
  (hle : ∀t,len t ≤ more t)

end TorsionFreeZeroDivisors.ExtendComparisons
namespace TorsionFreeZeroDivisors.RecursiveSeparator.Split
open scoped Classical
variable {V : Type} [DecidableEq V] {R Q : V→V→Prop} {S : Finset V}

end TorsionFreeZeroDivisors.RecursiveSeparator.Split
namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing
open scoped Classical
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap) (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)

end TorsionFreeZeroDivisors.SampleGraph.FullPairing

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing
open scoped Classical
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap) (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)

end TorsionFreeZeroDivisors.SampleGraph.FullPairing
namespace TorsionFreeZeroDivisors.SampleGraph.Picture
open scoped Classical
open BlockAlignment ComparedBlocks
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep} {z w : VA rep⊕VB rep} {O : Type} [Fintype O] (hzw : z≠w) (hz : z=Sum.inl x ∨ z=Sum.inr y) (cap : ℕ) (hc : 0<cap)

end TorsionFreeZeroDivisors.SampleGraph.Picture
namespace TorsionFreeZeroDivisors.MapEuler

section
open scoped Classical
open PermutationCycles PairingFactors
variable {O : Type} [Fintype O]

/-- Any submatching of a literal genus-zero map is still genus zero; dangling
half-edges are retained as fixed points. No embedding predicate is assumed. -/
theorem genusZero_subpairing (σ α β : Equiv.Perm O)
    (ha : Function.Involutive α) (_hb : Function.Involutive β)
    (hsub : ∀ x, β x = x ∨ β x = α x) (hz : GenusZero σ α) :
    GenusZero σ β := by
  classical
  generalize hn : α.support.card = n at *
  induction n using Nat.strong_induction_on generalizing α with
  | h n ih =>
    by_cases he : α = β
    · simpa only [he] using hz
    · obtain ⟨p,hp⟩ : ∃ p, α p ≠ β p := by
        by_contra h
        push Not at h
        exact he (Equiv.ext h)
      have hbp : β p = p := (hsub p).resolve_right (Ne.symm hp)
      have hap : α p ≠ p := by simpa only [hbp] using hp
      have hbq : β (α p) = α p := by
        rcases hsub (α p) with hh|hh
        · exact hh
        · rw [ha] at hh
          exact (hap (β.injective (hh.trans hbp.symm))).elim
      have hs : ∀ x, β x = x ∨ β x = strip α p x := by
        intro x
        by_cases hxp : x = p
        · exact Or.inl (hxp ▸ hbp)
        by_cases hxq : x = α p
        · exact Or.inl (hxq ▸ hbq)
        rcases hsub x with hh|hh
        · exact Or.inl hh
        · exact Or.inr (hh.trans (strip_away α ha p x hxp hxq).symm)
      have hc := strip_card α ha p hap
      exact ih (strip α p).support.card (by omega) (strip α p)
        (strip_involutive α ha p) hs (genusZero_strip σ α ha hz p hap) rfl

/-- Keep a pair precisely when both its actual endpoint darts satisfy P. -/
def inducedPairFun (α : Equiv.Perm O) (P : O → Prop) (x : O) : O :=
  if P x ∧ P (α x) then α x else x

omit [Fintype O] in
lemma inducedPairFun_involutive (α : Equiv.Perm O) (ha : Function.Involutive α)
    (P : O → Prop) : Function.Involutive (inducedPairFun α P) := by
  intro x
  by_cases h : P x ∧ P (α x)
  · have h' : P (α x) ∧ P (α (α x)) := ⟨h.2,by rw [ha x]; exact h.1⟩
    simp only [inducedPairFun, if_pos h, if_pos h']
    exact ha x
  · simp only [inducedPairFun, if_neg h]

def inducedPair (α : Equiv.Perm O) (ha : Function.Involutive α) (P : O → Prop) :
    Equiv.Perm O where
  toFun := inducedPairFun α P
  invFun := inducedPairFun α P
  left_inv := inducedPairFun_involutive α ha P
  right_inv := inducedPairFun_involutive α ha P

omit [Fintype O] in
lemma inducedPair_apply (α : Equiv.Perm O) (ha : Function.Involutive α)
    (P : O → Prop) (x : O) :
    inducedPair α ha P x = if P x ∧ P (α x) then α x else x := rfl

/-- The rotation of every vertex is unchanged; only crossing/outside pairs
are removed. This handles loops, parallel edges, and disconnected graphs. -/
theorem genusZero_inducedPair (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (P : O → Prop) (hz : GenusZero σ α) : GenusZero σ (inducedPair α ha P) := by
  apply genusZero_subpairing σ α _ ha (inducedPairFun_involutive α ha P) _ hz
  intro x
  rw [inducedPair_apply]
  split_ifs <;> simp

/-- The underlying simple graph of the actual permutation map. Ignoring loops
and parallel copies does not discard any adjacency between distinct vertices. -/
def graph (σ α : Equiv.Perm O) (ha : Function.Involutive α) : SimpleGraph (Cycle σ) where
  Adj v w := v ≠ w ∧ ∃ x, cycle σ x = v ∧ cycle σ (α x) = w
  symm := ⟨by
    intro v w ⟨hne,x,hx,hy⟩
    exact ⟨hne.symm,α x,hy,by rw [ha x]; exact hx⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} (σ α : Equiv.Perm O) (ha : Function.Involutive α)

lemma component_rot (x : O) : component σ α (σ x)=component σ α x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl)))
lemma component_pair (x : O) : component σ α (α x)=component σ α x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl)))

include ha in
lemma reachable_pair (x : O) :
    (graph σ α ha).Reachable (cycle σ x) (cycle σ (α x)) := by
  by_cases h : cycle σ x=cycle σ (α x)
  · rw [h]
  · exact SimpleGraph.Adj.reachable ⟨h,x,rfl,rfl⟩

include ha in
lemma reachable_of_component {x y : O}
    (h : component σ α x=component σ α y) :
    (graph σ α ha).Reachable (cycle σ x) (cycle σ y) := by
  have hh : Relation.EqvGen (Edge σ α) x y := Quotient.exact h
  clear h
  induction hh with
  | rel x y h =>
    rcases h with h|h
    · rw [←h,cycle_apply]
    · rw [←h]
      exact reachable_pair σ α ha x
  | refl => exact SimpleGraph.Reachable.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

variable [Fintype O]
def vertexComponent : Cycle σ → Component σ α :=
  PermutationCycles.lift σ (component σ α) (component_rot σ α)

@[simp] lemma vertexComponent_cycle (x : O) :
    vertexComponent σ α (cycle σ x)=component σ α x := rfl

lemma vertexComponent_adj {v w : Cycle σ} (h : (graph σ α ha).Adj v w) :
    vertexComponent σ α v=vertexComponent σ α w := by
  obtain ⟨_,x,rfl,rfl⟩ := h
  exact (component_pair σ α x).symm

include ha in
lemma vertexComponent_reachable {v w : Cycle σ} (h : (graph σ α ha).Reachable v w) :
    vertexComponent σ α v=vertexComponent σ α w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact (vertexComponent_adj σ α ha h).trans ih

/-- The map and the underlying simple graph have literally the same components. -/
def graphComponentEquiv : Component σ α ≃ (graph σ α ha).ConnectedComponent where
  toFun := Quotient.lift (fun x=>(graph σ α ha).connectedComponentMk (cycle σ x))
    (fun x y h=>SimpleGraph.ConnectedComponent.sound
      (reachable_of_component σ α ha (Quotient.sound h)))
  invFun := Quot.lift (vertexComponent σ α) (fun _ _ h=>vertexComponent_reachable σ α ha h)
  left_inv := by
    intro c
    induction c using Quotient.inductionOn with | h x => rfl
  right_inv := by
    intro c
    induction c using Quot.inductionOn with
    | h v =>
      obtain ⟨x,rfl⟩ := cycle_surjective σ v
      rfl

lemma graphComponent_card : Nat.card (Component σ α)=Nat.card (graph σ α ha).ConnectedComponent :=
  Nat.card_congr (graphComponentEquiv σ α ha)

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)

/-- Pick an actual occurrence realizing each directed edge; this is injective
because both endpoint vertices of an occurrence are fixed. -/
def realizeDart (d : (graph σ α ha).Dart) : O := d.adj.2.choose
omit [Fintype O] in
lemma realizeDart_fst (d : (graph σ α ha).Dart) :
    cycle σ (realizeDart σ α ha d)=d.fst := d.adj.2.choose_spec.1
omit [Fintype O] in
lemma realizeDart_snd (d : (graph σ α ha).Dart) :
    cycle σ (α (realizeDart σ α ha d))=d.snd := d.adj.2.choose_spec.2
lemma realizeDart_mem (d : (graph σ α ha).Dart) : realizeDart σ α ha d∈α.support := by
  apply Equiv.Perm.mem_support.mpr
  intro he
  apply d.fst_ne_snd
  rw [←realizeDart_fst σ α ha d,←realizeDart_snd σ α ha d,he]
omit [Fintype O] in
lemma realizeDart_injective : Function.Injective (realizeDart σ α ha) := by
  intro d e h
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rw [←realizeDart_fst σ α ha d,←realizeDart_fst σ α ha e,h]
  · rw [←realizeDart_snd σ α ha d,←realizeDart_snd σ α ha e,h]

/-- Removing loops and parallel copies lowers the true paired-edge count. -/
theorem twice_graph_edges_le_support :
    2*Nat.card (graph σ α ha).edgeSet≤α.support.card := by
  let f : (graph σ α ha).Dart → {x // x∈α.support} :=
    fun d=>⟨realizeDart σ α ha d,realizeDart_mem σ α ha d⟩
  have hi : Function.Injective f := fun _ _ h=>
    realizeDart_injective σ α ha (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hi
  rw [Fintype.card_coe,SimpleGraph.dart_card_eq_twice_card_edges,
    SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card] at hc
  exact hc

/-- A connected map with the minimal possible true edge count is a tree,
even though the ambient definition permits loops and parallel edges. -/
theorem graph_isTree_of_support (hc : (graph σ α ha).Connected)
    (he : α.support.card+2=2*Nat.card (Cycle σ)) : (graph σ α ha).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hc,?_⟩
  have h₁ := twice_graph_edges_le_support σ α ha
  have h₂ := hc.card_vert_le_card_edgeSet_add_one
  omega

end

open scoped Classical BigOperators
open PermutationCycles
variable {O : Type} (σ α : Equiv.Perm O) (ha : Function.Involutive α)

lemma edge_has_realizer (e : (graph σ α ha).edgeSet) :
    ∃ x : O, α x≠x ∧ s(cycle σ x,cycle σ (α x))=e.val := by
  obtain ⟨e,he⟩ := e
  induction e using Sym2.inductionOn with
  | _ v w =>
    obtain ⟨hne,x,hx,hy⟩ := he
    refine ⟨x,?_,?_⟩
    rotate_left
    · change s(cycle σ x,cycle σ (α x))=s(v,w)
      rw [hx,hy]
    intro h
    exact hne (hx.symm.trans ((congrArg (cycle σ) h).symm.trans hy))

def edgeRep (e : (graph σ α ha).edgeSet) : O := (edge_has_realizer σ α ha e).choose
lemma edgeRep_ne (e : (graph σ α ha).edgeSet) : α (edgeRep σ α ha e)≠edgeRep σ α ha e :=
  (edge_has_realizer σ α ha e).choose_spec.1
lemma edgeRep_edge (e : (graph σ α ha).edgeSet) :
    s(cycle σ (edgeRep σ α ha e),cycle σ (α (edgeRep σ α ha e)))=e.val :=
  (edge_has_realizer σ α ha e).choose_spec.2

variable (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha)
def edgeOfSubgraph (e : T.edgeSet) : (graph σ α ha).edgeSet :=
  ⟨e.val,SimpleGraph.edgeSet_mono hT e.property⟩
def pairFinset (e : T.edgeSet) : Finset O :=
  {edgeRep σ α ha (edgeOfSubgraph σ α ha T hT e),
    α (edgeRep σ α ha (edgeOfSubgraph σ α ha T hT e))}

lemma pairFinset_card (e : T.edgeSet) : (pairFinset σ α ha T hT e).card=2 := by
  simp [pairFinset,Ne.symm (edgeRep_ne σ α ha _)]
lemma pairFinset_nonfixed (e : T.edgeSet) {x : O} (hx : x∈pairFinset σ α ha T hT e) : α x≠x := by
  simp only [pairFinset,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl
  · exact edgeRep_ne σ α ha _
  · rw [ha]
    exact Ne.symm (edgeRep_ne σ α ha _)
lemma pairFinset_pair (e : T.edgeSet) {x : O} (hx : x∈pairFinset σ α ha T hT e) :
    α x∈pairFinset σ α ha T hT e := by
  simp only [pairFinset,Finset.mem_insert,Finset.mem_singleton] at hx ⊢
  rcases hx with rfl|rfl
  · exact Or.inr rfl
  · exact Or.inl (ha _)
lemma pairFinset_edge (e : T.edgeSet) {x : O} (hx : x∈pairFinset σ α ha T hT e) :
    s(cycle σ x,cycle σ (α x))=e.val := by
  simp only [pairFinset,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl
  · exact edgeRep_edge σ α ha _
  · rw [ha,Sym2.eq_swap]
    exact edgeRep_edge σ α ha _

lemma pairFinset_disjoint {e f : T.edgeSet} (hef : e≠f) :
    Disjoint (pairFinset σ α ha T hT e) (pairFinset σ α ha T hT f) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hef (Subtype.ext ((pairFinset_edge σ α ha T hT e hx).symm.trans
    (pairFinset_edge σ α ha T hT f hy)))

variable [Fintype O]
def pickedDarts : Finset O := Finset.univ.biUnion (pairFinset σ α ha T hT)
lemma mem_pickedDarts (x : O) :
    x∈pickedDarts σ α ha T hT ↔ ∃ e : T.edgeSet,x∈pairFinset σ α ha T hT e := by
  simp only [pickedDarts,Finset.mem_biUnion,Finset.mem_univ,true_and]
lemma pickedDarts_nonfixed {x : O} (hx : x∈pickedDarts σ α ha T hT) : α x≠x := by
  obtain ⟨e,he⟩ := (mem_pickedDarts σ α ha T hT x).mp hx
  exact pairFinset_nonfixed σ α ha T hT e he
lemma pickedDarts_pair {x : O} (hx : x∈pickedDarts σ α ha T hT) : α x∈pickedDarts σ α ha T hT := by
  obtain ⟨e,he⟩ := (mem_pickedDarts σ α ha T hT x).mp hx
  exact (mem_pickedDarts σ α ha T hT (α x)).mpr ⟨e,pairFinset_pair σ α ha T hT e he⟩
lemma pickedDarts_card : (pickedDarts σ α ha T hT).card=2*Nat.card T.edgeSet := by
  rw [pickedDarts,Finset.card_biUnion]
  · simp only [pairFinset_card,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
    omega
  · intro e _ f _ hef
    exact pairFinset_disjoint σ α ha T hT hef

/-- A chosen simple subgraph is realized by exactly one original paired edge
per simple edge, with the original vertex rotations unchanged. -/
def subgraphPair : Equiv.Perm O := inducedPair α ha (fun x=>x∈pickedDarts σ α ha T hT)
lemma subgraphPair_involutive : Function.Involutive (subgraphPair σ α ha T hT) :=
  inducedPairFun_involutive α ha _
lemma subgraphPair_apply (x : O) : subgraphPair σ α ha T hT x=
    if x∈pickedDarts σ α ha T hT then α x else x := by
  rw [subgraphPair,inducedPair_apply]
  by_cases hx : x∈pickedDarts σ α ha T hT
  · rw [if_pos hx,if_pos ⟨hx,pickedDarts_pair σ α ha T hT hx⟩]
  · rw [if_neg hx,if_neg (fun h=>hx h.1)]
lemma subgraphPair_support : (subgraphPair σ α ha T hT).support=pickedDarts σ α ha T hT := by
  ext x
  rw [Equiv.Perm.mem_support,subgraphPair_apply]
  by_cases hx : x∈pickedDarts σ α ha T hT
  · rw [if_pos hx]
    exact iff_of_true (pickedDarts_nonfixed σ α ha T hT hx) hx
  · rw [if_neg hx]
    simp only [ne_eq,not_true_eq_false,false_iff]
    exact hx
lemma subgraphPair_support_card : (subgraphPair σ α ha T hT).support.card=2*Nat.card T.edgeSet := by
  rw [subgraphPair_support,pickedDarts_card]

lemma subgraphPair_graph :
    graph σ (subgraphPair σ α ha T hT) (subgraphPair_involutive σ α ha T hT)=T := by
  ext v w
  constructor
  · rintro ⟨hne,x,hx,hy⟩
    rw [subgraphPair_apply] at hy
    by_cases hp : x∈pickedDarts σ α ha T hT
    · rw [if_pos hp] at hy
      obtain ⟨e,he⟩ := (mem_pickedDarts σ α ha T hT x).mp hp
      have hedge := pairFinset_edge σ α ha T hT e he
      rw [hx,hy] at hedge
      exact (T.mem_edgeSet).mp (hedge.symm ▸ e.property)
    · rw [if_neg hp] at hy
      exact (hne (hx.symm.trans hy)).elim
  · intro h
    let e : T.edgeSet := ⟨s(v,w),h⟩
    let p := edgeRep σ α ha (edgeOfSubgraph σ α ha T hT e)
    have hmem : p∈pickedDarts σ α ha T hT :=
      (mem_pickedDarts σ α ha T hT p).mpr ⟨e,Finset.mem_insert_self _ _⟩
    have he : s(cycle σ p,cycle σ (α p))=s(v,w) := edgeRep_edge σ α ha _
    rcases Sym2.eq_iff.mp he with ⟨hv,hw⟩|⟨hw,hv⟩
    · refine ⟨h.ne,p,hv,?_⟩
      rw [subgraphPair_apply,if_pos hmem]
      exact hw
    · refine ⟨h.ne,α p,hv,?_⟩
      rw [subgraphPair_apply,if_pos (pickedDarts_pair σ α ha T hT hmem),ha]
      exact hw

lemma genusZero_subgraphPair (hz : GenusZero σ α) :
    GenusZero σ (subgraphPair σ α ha T hT) := genusZero_inducedPair σ α ha _ hz

end TorsionFreeZeroDivisors.MapEuler

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MapEuler

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)

lemma component_card_one_of_connected (hc : (graph σ α ha).Connected) :
    Nat.card (Component σ α)=1 := by
  rw [graphComponent_card σ α ha]
  have : Nonempty (Cycle σ) := hc.nonempty
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨hc.preconnected.subsingleton_connectedComponent,inferInstance⟩

omit [Fintype O] in
lemma connected_of_component_card_one (hc : Nat.card (Component σ α)=1) :
    (graph σ α ha).Connected := by
  obtain ⟨hs,hn⟩ := Nat.card_eq_one_iff_unique.mp hc
  have : Subsingleton (Component σ α) := hs
  obtain ⟨c⟩ := hn
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
  have : Nonempty (Cycle σ) := ⟨cycle σ x⟩
  refine ⟨?_⟩
  intro v w
  obtain ⟨y,rfl⟩ := cycle_surjective σ v
  obtain ⟨z,rfl⟩ := cycle_surjective σ w
  exact reachable_of_component σ α ha (Subsingleton.elim _ _)

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} (σ α β : Equiv.Perm O)
    (ha : Function.Involutive α) (hb : Function.Involutive β)
    (hsub : ∀ x,β x=x ∨ β x=α x)

include ha hb hsub in
lemma subpairing_commute : Commute α β := by
  show α*β=β*α
  ext x
  change α (β x)=β (α x)
  rcases hsub x with hx|hx
  · rcases hsub (α x) with hy|hy
    · rw [hx,hy]
    · rw [ha x] at hy
      have he : α x=x := β.injective (hy.trans hx.symm)
      rw [hx,he,hx]
  · have hy : β (α x)=x := by rw [←hx,hb x]
    rw [hx,ha x,hy]

include ha hb hsub in
lemma complement_involutive : Function.Involutive (α*β) := by
  have he : ∀ x, β (α x)=α (β x) := fun x=>
    (congrArg (fun f : Equiv.Perm O => f x) (subpairing_commute α β ha hb hsub).eq).symm
  intro x
  change α (β (α (β x)))=x
  rw [he,hb x,ha x]

include ha hsub in
lemma complement_subpairing : ∀ x,(α*β) x=x ∨ (α*β) x=α x := by
  intro x
  change α (β x)=x ∨ α (β x)=α x
  rcases hsub x with hx|hx
  · exact Or.inr (congrArg α hx)
  · exact Or.inl ((congrArg α hx).trans (ha x))

include ha hb hsub in
lemma complement_face : (α*β)*(α*σ)=β*σ := by
  ext x
  change α (β (α (σ x)))=β (σ x)
  have he : β (α (σ x))=α (β (σ x)) :=
    (congrArg (fun f : Equiv.Perm O => f (σ x)) (subpairing_commute α β ha hb hsub).eq).symm
  rw [he,ha]

variable [Fintype O]
include hsub in
lemma subpairing_support_subset : β.support⊆α.support := by
  intro x hx
  rw [Equiv.Perm.mem_support] at hx ⊢
  rcases hsub x with hh|hh
  · exact (hx hh).elim
  · rwa [←hh]

include ha hsub in
lemma complement_support : (α*β).support=α.support\β.support := by
  ext x
  simp only [Equiv.Perm.mem_support,Finset.mem_sdiff]
  change α (β x)≠x ↔ α x≠x ∧ ¬β x≠x
  rcases hsub x with hh|hh
  · simp only [hh,ne_eq,not_true_eq_false,not_false_eq_true,and_true]
  · simp only [hh,ha x,ne_eq,not_true_eq_false,not_not,false_iff]
    exact fun h=>h.1 h.2

include ha hsub in
lemma complement_support_card : (α*β).support.card+β.support.card=α.support.card := by
  rw [complement_support α β ha hsub,Finset.card_sdiff_of_subset (subpairing_support_subset α β hsub)]
  exact Nat.sub_add_cancel (Finset.card_le_card (subpairing_support_subset α β hsub))

include ha hb hsub in
/-- Deleting a chosen set of primal edges is actual complementary-pair deletion
in the dual map, not an assumed planar-minor interface. -/
theorem genusZero_complement_dual (hz : GenusZero σ α) : GenusZero (α*σ) (α*β) :=
  genusZero_subpairing (α*σ) α (α*β) ha (complement_involutive α β ha hb hsub)
    (complement_subpairing α β ha hsub) ((genusZero_dual σ α ha).mp hz)

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha)

lemma subgraphPair_subpairing : ∀ x,subgraphPair σ α ha T hT x=x ∨
    subgraphPair σ α ha T hT x=α x := by
  intro x
  rw [subgraphPair_apply]
  split_ifs <;> simp only [true_or,or_true]

lemma subgraphPair_support_tree (ht : T.IsTree) :
    (subgraphPair σ α ha T hT).support.card+2=2*Nat.card (Cycle σ) := by
  rw [subgraphPair_support_card]
  have hc := (SimpleGraph.isTree_iff_connected_and_card.mp ht).2
  omega

/-- The literal contour permutation of a chosen spanning tree has one cycle. -/
theorem tree_contour_card (hz : GenusZero σ α) (ht : T.IsTree) :
    Nat.card (Cycle (subgraphPair σ α ha T hT*σ))=1 := by
  have hc : (graph σ (subgraphPair σ α ha T hT) (subgraphPair_involutive σ α ha T hT)).Connected := by
    rw [subgraphPair_graph]
    exact ht.connected
  have hcomp := component_card_one_of_connected σ _ (subgraphPair_involutive σ α ha T hT) hc
  have hgen := genusZero_subgraphPair σ α ha T hT hz
  change 2*Nat.card (Cycle σ)+2*Nat.card (Cycle (subgraphPair σ α ha T hT*σ))=
    (subgraphPair σ α ha T hT).support.card+4*Nat.card (Component σ (subgraphPair σ α ha T hT)) at hgen
  have hsup := subgraphPair_support_tree σ α ha T hT ht
  omega

/-- The complementary edge matching in the original dual rotation has exactly
one fewer edge than dual vertices. -/
lemma cotree_support (hz : GenusZero σ α) (ht : T.IsTree) :
    (α*subgraphPair σ α ha T hT).support.card+2=2*Nat.card (Cycle (α*σ)) := by
  have hconn : (graph σ α ha).Connected := ht.connected.mono hT
  have hc := component_card_one_of_connected σ α ha hconn
  have hp := subgraphPair_support_tree σ α ha T hT ht
  have hs := complement_support_card α _ ha (subgraphPair_subpairing σ α ha T hT)
  change 2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))=α.support.card+4*Nat.card (Component σ α) at hz
  omega

/-- Tree--cotree duality proved from actual permutations and Euler equality.
Loops and parallel edges in the original map are allowed. No embedding or
planar-duality axiom is used. -/
theorem spanning_cotree_isTree (hz : GenusZero σ α) (ht : T.IsTree) :
    (graph (α*σ) (α*subgraphPair σ α ha T hT)
      (complement_involutive α _ ha (subgraphPair_involutive σ α ha T hT)
        (subgraphPair_subpairing σ α ha T hT))).IsTree := by
  let β := subgraphPair σ α ha T hT
  have hb := subgraphPair_involutive σ α ha T hT
  have hsub := subgraphPair_subpairing σ α ha T hT
  have hface := complement_face σ α β ha hb hsub
  have hgen := genusZero_complement_dual σ α β ha hb hsub hz
  have htface := tree_contour_card σ α ha T hT hz ht
  have hs := cotree_support σ α ha T hT hz ht
  change 2*Nat.card (Cycle (α*σ))+2*Nat.card (Cycle ((α*β)*(α*σ)))=
    (α*β).support.card+4*Nat.card (Component (α*σ) (α*β)) at hgen
  rw [hface] at hgen
  have hcomp : Nat.card (Component (α*σ) (α*β))=1 := by
    dsimp only [β] at hgen ⊢
    omega
  exact graph_isTree_of_support (α*σ) (α*β) (complement_involutive α β ha hb hsub)
    (connected_of_component_card_one _ _ _ hcomp) hs

end

section
open scoped Classical
open PermutationCycles
variable {O V : Type} [Fintype O]

end

open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha)

end TorsionFreeZeroDivisors.MapEuler

/-! The weighted centroid needed by planar dual-tree separator constructions.
This is an actual theorem for finite Mathlib trees, not a separator assumption. -/
namespace TorsionFreeZeroDivisors.TreeCentroid
open scoped Classical BigOperators
open SimpleGraph
variable {V : Type} {G : SimpleGraph V} (h : G.IsTree)

variable [Fintype V]

end TorsionFreeZeroDivisors.TreeCentroid

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TreeCentroid
open scoped Classical
open SimpleGraph
variable {V : Type} [Fintype V] {G : SimpleGraph V} (h : G.IsTree)

end TorsionFreeZeroDivisors.TreeCentroid

namespace TorsionFreeZeroDivisors.MapEuler

section
open scoped Classical
open PermutationCycles
variable {O : Type} (σ φ γ : Equiv.Perm O) (hγ : Function.Involutive γ)

variable [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha) (ht : T.IsTree)

end

open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)

end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.TreeCentroid
open scoped Classical
open SimpleGraph
variable {V : Type} [Fintype V] {T : SimpleGraph V} (ht : T.IsTree)
    (H : SimpleGraph V) (hH : H≤T) (c n : V) (hn : ¬H.Adj c n)

end TorsionFreeZeroDivisors.TreeCentroid

namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

variable (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha)
    (hz : GenusZero σ α) (ht : T.IsTree)
local notation "β" => subgraphPair σ α ha T hT
local notation "γ" => α*β
local notation "φ" => α*σ
local notation "hγ" => complement_involutive α β ha (subgraphPair_involutive σ α ha T hT)
  (subgraphPair_subpairing σ α ha T hT)
local notation "D" => graph φ γ hγ
local notation "htD" => spanning_cotree_isTree σ α ha T hT hz ht

end TorsionFreeZeroDivisors.MapEuler

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical BigOperators
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha)
    (hz : GenusZero σ α) (ht : T.IsTree)
local notation "β" => subgraphPair σ α ha T hT
local notation "γ" => α*β
local notation "φ" => α*σ
local notation "hγ" => complement_involutive α β ha (subgraphPair_involutive σ α ha T hT)
  (subgraphPair_subpairing σ α ha T hT)
local notation "D" => graph φ γ hγ
local notation "htD" => spanning_cotree_isTree σ α ha T hT hz ht

omit [Fintype O] in
lemma home_cycle (v : Cycle σ) : cycle σ (Quotient.out v)=v := Quotient.out_eq v

end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.ConedMap

section
open scoped Classical BigOperators
open PermutationCycles MapEuler
variable {O : Type} (σ α : Equiv.Perm O)

/-- Original darts plus one radial pair for each face corner. Radial true is
at the new face center, radial false at the original vertex. -/
abbrev Dart (O : Type) := O ⊕ (O × Bool)
def old (x : O) : Dart O := .inl x
def radial (x : O) : Dart O := .inr (x,false)
def center (x : O) : Dart O := .inr (x,true)

def rotation : Equiv.Perm (Dart O) where
  toFun
    | .inl x => radial x
    | .inr (x,false) => old (σ x)
    | .inr (x,true) => center ((α*σ).symm x)
  invFun
    | .inl x => radial (σ.symm x)
    | .inr (x,false) => old x
    | .inr (x,true) => center ((α*σ) x)
  left_inv := by
    rintro (x|⟨x,b⟩)
    · rfl
    · cases b
      · exact congrArg radial (σ.symm_apply_apply x)
      · exact congrArg center ((α*σ).apply_symm_apply x)
  right_inv := by
    rintro (x|⟨x,b⟩)
    · exact congrArg old (σ.apply_symm_apply x)
    · cases b
      · rfl
      · exact congrArg center ((α*σ).symm_apply_apply x)

def pairing : Equiv.Perm (Dart O) := Equiv.sumCongr α (Equiv.prodCongr (Equiv.refl O) Equiv.boolNot)

@[simp] lemma rotation_old (x : O) : rotation σ α (old x)=radial x := rfl
@[simp] lemma rotation_radial (x : O) : rotation σ α (radial x)=old (σ x) := rfl
@[simp] lemma rotation_center (x : O) : rotation σ α (center x)=center ((α*σ).symm x) := rfl
@[simp] lemma pairing_old (x : O) : pairing α (old x)=old (α x) := rfl
@[simp] lemma pairing_radial (x : O) : pairing α (radial x)=center x := rfl
@[simp] lemma pairing_center (x : O) : pairing α (center x)=radial x := rfl

lemma pairing_involutive (ha : Function.Involutive α) : Function.Involutive (pairing α) := by
  rintro (x|⟨x,b⟩)
  · change old (α (α x))=old x
    rw [ha]
  · cases b <;> rfl

local notation "ρ" => rotation σ α
local notation "π" => pairing α
local notation "φ" => α*σ
local notation "ψ" => π*ρ

@[simp] lemma face_old (x : O) : ψ (old x)=center x := rfl
@[simp] lemma face_center (x : O) : ψ (center x)=radial ((α*σ).symm x) := rfl
@[simp] lemma face_radial (x : O) : ψ (radial x)=old (φ x) := rfl

lemma vertex_radial (x : O) : cycle ρ (radial x)=cycle ρ (old x) := cycle_apply ρ (old x)
lemma vertex_old_apply (x : O) : cycle ρ (old (σ x))=cycle ρ (old x) :=
  (cycle_apply ρ (radial x)).trans (vertex_radial σ α x)
lemma vertex_center_apply (x : O) : cycle ρ (center (φ x))=cycle ρ (center x) := by
  have h := cycle_apply ρ (center (φ x))
  simpa only [rotation_center,Equiv.symm_apply_apply] using h.symm

/-- Literal vertex classification: original vertices and the inserted face centers. -/
def vertexRaw : Dart O → Cycle σ ⊕ Cycle φ
  | .inl x => .inl (cycle σ x)
  | .inr (x,false) => .inl (cycle σ x)
  | .inr (x,true) => .inr (cycle φ x)
lemma vertexRaw_invariant (x : Dart O) : vertexRaw σ α (ρ x)=vertexRaw σ α x := by
  rcases x with x|⟨x,b⟩
  · rfl
  · cases b
    · exact congrArg Sum.inl (cycle_apply σ x)
    · change Sum.inr (cycle φ ((α*σ).symm x))=Sum.inr (cycle φ x)
      rw [←cycle_apply φ ((α*σ).symm x),(α*σ).apply_symm_apply]

variable [Fintype O]

def vertices : Cycle ρ → Cycle σ ⊕ Cycle φ :=
  PermutationCycles.lift ρ (vertexRaw σ α) (vertexRaw_invariant σ α)
def vertexInverse : Cycle σ ⊕ Cycle φ → Cycle ρ
  | .inl v=>PermutationCycles.lift σ (fun x=>cycle ρ (old x)) (vertex_old_apply σ α) v
  | .inr f=>PermutationCycles.lift φ (fun x=>cycle ρ (center x)) (vertex_center_apply σ α) f
lemma vertices_right_inverse : Function.RightInverse (vertexInverse σ α) (vertices σ α) := by
  rintro (v|f)
  · obtain ⟨x,rfl⟩ := cycle_surjective σ v
    rfl
  · obtain ⟨x,rfl⟩ := cycle_surjective φ f
    rfl
lemma vertices_left_inverse : Function.LeftInverse (vertexInverse σ α) (vertices σ α) := by
  intro v
  obtain ⟨x,rfl⟩ := cycle_surjective ρ v
  rcases x with x|⟨x,b⟩
  · rfl
  · cases b
    · exact (vertex_radial σ α x).symm
    · rfl

def vertexEquiv : Cycle ρ≃Cycle σ ⊕ Cycle φ :=
  ⟨vertices σ α,vertexInverse σ α,vertices_left_inverse σ α,vertices_right_inverse σ α⟩

@[simp] lemma vertexEquiv_old (x : O) : vertexEquiv σ α (cycle ρ (old x))=.inl (cycle σ x) := rfl
@[simp] lemma vertexEquiv_radial (x : O) : vertexEquiv σ α (cycle ρ (radial x))=.inl (cycle σ x) := rfl
@[simp] lemma vertexEquiv_center (x : O) : vertexEquiv σ α (cycle ρ (center x))=.inr (cycle φ x) := rfl

end

open scoped Classical
open PermutationCycles MapEuler
variable {O : Type} (σ α : Equiv.Perm O)
local notation "ρ" => rotation σ α
local notation "π" => pairing α
local notation "φ" => α*σ

variable [Fintype O]

omit [Fintype O] in
lemma support_card_nat {X : Type} [Fintype X] [DecidableEq X] (p : Equiv.Perm X) :
    p.support.card=Nat.card {x : X // p x≠x} := by
  rw [←Fintype.card_coe,←Nat.card_eq_fintype_card]
  exact Nat.card_congr
    ⟨fun x=>⟨x.val,Equiv.Perm.mem_support.mp x.property⟩,
     fun x=>⟨x.val,Equiv.Perm.mem_support.mpr x.property⟩,
     fun _=>rfl,fun _=>rfl⟩

end TorsionFreeZeroDivisors.ConedMap

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ConedMap
open scoped Classical
open PermutationCycles MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)
local notation "ρ" => rotation σ α
local notation "π" => pairing α
local notation "G" => graph σ α ha
local notation "G'" => graph ρ π (pairing_involutive α ha)

def oldVertex (v : Cycle σ) : Cycle ρ := (vertexEquiv σ α).symm (.inl v)
def centerVertex (f : Cycle (α*σ)) : Cycle ρ := (vertexEquiv σ α).symm (.inr f)

@[simp] lemma oldVertex_cycle (x : O) : oldVertex σ α (cycle σ x)=cycle ρ (old x) := rfl
@[simp] lemma centerVertex_cycle (x : O) : centerVertex σ α (cycle (α*σ) x)=cycle ρ (center x) := rfl

end TorsionFreeZeroDivisors.ConedMap

/-! A literal breadth-first spanning tree, with its distances and radius
preserved. This is the rooted tree used in the sharp planar separator. -/
namespace TorsionFreeZeroDivisors.BFSTree
open scoped Classical
open SimpleGraph
variable {V : Type} (G : SimpleGraph V) (hc : G.Connected) (root : V)

variable [Fintype V]

end TorsionFreeZeroDivisors.BFSTree

namespace TorsionFreeZeroDivisors.TreeCentroid
open scoped Classical
open SimpleGraph
variable {V : Type} [Fintype V] {T : SimpleGraph V} (ht : T.IsTree)

end TorsionFreeZeroDivisors.TreeCentroid

namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.MapRestrict
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (f : Equiv.Perm O) (P : O→Prop) (hf : ∀ x,P (f x)↔P x)

def perm : Equiv.Perm {x // P x} := f.subtypeEquiv (fun x=>(hf x).symm)
omit [Fintype O] in
@[simp] lemma perm_val (x : {x // P x}) : (perm f P hf x).val=f x := rfl
omit [Fintype O] in
include hf in
lemma not_invariant (x : O) : (¬P (f x))↔¬P x := not_congr (hf x)
local notation "fP" => perm f P hf
local notation "fN" => perm f (fun x=>¬P x) (not_invariant f P hf)

def cycleInclude : Cycle fP→Cycle f :=
  PermutationCycles.lift fP (fun x=>cycle f x.val) (fun x=>cycle_apply f x.val)
@[simp] lemma cycleInclude_cycle (x : {x // P x}) : cycleInclude f P hf (cycle fP x)=cycle f x.val := rfl

def cycleRaw (x : O) : Cycle fP ⊕ Cycle fN :=
  if h:P x then .inl (cycle fP ⟨x,h⟩) else .inr (cycle fN ⟨x,h⟩)
omit [Fintype O] in
lemma cycleRaw_apply (x : O) : cycleRaw f P hf (f x)=cycleRaw f P hf x := by
  by_cases hx : P x
  · rw [cycleRaw,dif_pos ((hf x).mpr hx),cycleRaw,dif_pos hx]
    exact congrArg Sum.inl (cycle_apply fP ⟨x,hx⟩)
  · rw [cycleRaw,dif_neg (fun h=>hx ((hf x).mp h)),cycleRaw,dif_neg hx]
    exact congrArg Sum.inr (cycle_apply fN ⟨x,hx⟩)

def cycleEquiv : Cycle f≃Cycle fP ⊕ Cycle fN where
  toFun := PermutationCycles.lift f (cycleRaw f P hf) (cycleRaw_apply f P hf)
  invFun := Sum.elim (cycleInclude f P hf) (cycleInclude f (fun x=>¬P x) (not_invariant f P hf))
  left_inv := by
    intro c
    obtain ⟨x,rfl⟩ := cycle_surjective f c
    change (Sum.elim _ _) (cycleRaw f P hf x)=cycle f x
    unfold cycleRaw
    split_ifs <;> rfl
  right_inv := by
    intro c
    rcases c with c|c
    · obtain ⟨x,rfl⟩ := cycle_surjective fP c
      change cycleRaw f P hf x.val=Sum.inl (cycle fP x)
      rw [cycleRaw,dif_pos x.property]
    · obtain ⟨x,rfl⟩ := cycle_surjective fN c
      change cycleRaw f P hf x.val=Sum.inr (cycle fN x)
      rw [cycleRaw,dif_neg x.property]

lemma cycle_card : Nat.card (Cycle f)=Nat.card (Cycle fP)+Nat.card (Cycle fN) := by
  rw [Nat.card_congr (cycleEquiv f P hf),Nat.card_sum]
omit [Fintype O] in
lemma perm_involutive (hi : Function.Involutive f) : Function.Involutive fP :=
  fun x=>Subtype.ext (hi x.val)

def supportEquiv : {x : O // f x≠x} ≃
    {x : Subtype P // fP x≠x} ⊕ {x : {x // ¬P x} // fN x≠x} where
  toFun x := if h:P x.val then .inl ⟨⟨x.val,h⟩,fun he=>x.property (congrArg Subtype.val he)⟩
    else .inr ⟨⟨x.val,h⟩,fun he=>x.property (congrArg Subtype.val he)⟩
  invFun := Sum.elim (fun x=>⟨x.val.val,fun he=>x.property (Subtype.ext he)⟩)
    (fun x=>⟨x.val.val,fun he=>x.property (Subtype.ext he)⟩)
  left_inv := by intro x;dsimp;split_ifs <;> rfl
  right_inv := by
    intro x
    rcases x with x|x
    · dsimp
      rw [dif_pos x.val.property]
    · dsimp
      rw [dif_neg x.val.property]

lemma support_card : f.support.card=(fP).support.card+(fN).support.card := by
  simp only [ConedMap.support_card_nat]
  rw [Nat.card_congr (supportEquiv f P hf),Nat.card_sum]

end TorsionFreeZeroDivisors.MapRestrict

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MapRestrict

section
open scoped Classical
open PermutationCycles MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (P : O→Prop)
    (hs : ∀ x,P (σ x)↔P x) (ha : ∀ x,P (α x)↔P x)
local notation "σP" => perm σ P hs
local notation "αP" => perm α P ha
local notation "σN" => perm σ (fun x=>¬P x) (not_invariant σ P hs)
local notation "αN" => perm α (fun x=>¬P x) (not_invariant α P ha)

def componentInclude : Component σP αP→ Component σ α :=
  MapEuler.lift σP αP (fun x=>component σ α x.val)
    (fun x=>component_rotation σ α x.val) (fun x=>component_partner σ α x.val)
omit [Fintype O] in
@[simp] lemma componentInclude_component (x : Subtype P) :
    componentInclude σ α P hs ha (component σP αP x)=component σ α x.val := rfl

def componentRaw (x : O) : Component σP αP ⊕ Component σN αN :=
  if h:P x then .inl (component σP αP ⟨x,h⟩) else .inr (component σN αN ⟨x,h⟩)
omit [Fintype O] in
lemma componentRaw_rotation (x : O) : componentRaw σ α P hs ha (σ x)=componentRaw σ α P hs ha x := by
  by_cases hx : P x
  · rw [componentRaw,dif_pos ((hs x).mpr hx),componentRaw,dif_pos hx]
    exact congrArg Sum.inl (component_rotation σP αP ⟨x,hx⟩)
  · rw [componentRaw,dif_neg (fun h=>hx ((hs x).mp h)),componentRaw,dif_neg hx]
    exact congrArg Sum.inr (component_rotation σN αN ⟨x,hx⟩)
omit [Fintype O] in
lemma componentRaw_partner (x : O) : componentRaw σ α P hs ha (α x)=componentRaw σ α P hs ha x := by
  by_cases hx : P x
  · rw [componentRaw,dif_pos ((ha x).mpr hx),componentRaw,dif_pos hx]
    exact congrArg Sum.inl (component_partner σP αP ⟨x,hx⟩)
  · rw [componentRaw,dif_neg (fun h=>hx ((ha x).mp h)),componentRaw,dif_neg hx]
    exact congrArg Sum.inr (component_partner σN αN ⟨x,hx⟩)

def componentEquiv : Component σ α≃Component σP αP ⊕ Component σN αN where
  toFun := MapEuler.lift σ α (componentRaw σ α P hs ha)
    (componentRaw_rotation σ α P hs ha) (componentRaw_partner σ α P hs ha)
  invFun := Sum.elim (componentInclude σ α P hs ha)
    (componentInclude σ α (fun x=>¬P x) (not_invariant σ P hs) (not_invariant α P ha))
  left_inv := by
    intro c
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    change (Sum.elim _ _) (componentRaw σ α P hs ha x)=component σ α x
    unfold componentRaw
    split_ifs <;> rfl
  right_inv := by
    intro c
    rcases c with c|c
    · obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
      change componentRaw σ α P hs ha x.val=Sum.inl (component σP αP x)
      rw [componentRaw,dif_pos x.property]
    · obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
      change componentRaw σ α P hs ha x.val=Sum.inr (component σN αN x)
      rw [componentRaw,dif_neg x.property]

lemma component_card : Nat.card (Component σ α)=Nat.card (Component σP αP)+Nat.card (Component σN αN) := by
  rw [Nat.card_congr (componentEquiv σ α P hs ha),Nat.card_sum]

omit [Fintype O] in
include hs ha in
lemma mul_invariant (x : O) : P ((α*σ) x)↔P x := (ha (σ x)).trans (hs x)
omit [Fintype O] in
lemma perm_mul : perm (α*σ) P (mul_invariant σ α P hs ha)=αP*σP := rfl

/-- Restriction to any invariant union of map components preserves actual
Euler genus zero. The proof uses decomposition and the universal Euler upper
bound on BOTH complementary pieces. -/
theorem genusZero (hi : Function.Involutive α) (hz : GenusZero σ α) : GenusZero σP αP := by
  have hs' := cycle_card σ P hs
  have hf' := cycle_card (α*σ) P (mul_invariant σ α P hs ha)
  have ha' := support_card α P ha
  have hc' := component_card σ α P hs ha
  have hP := MapEuler.upper σP αP (perm_involutive α P ha hi)
  have hN := MapEuler.upper σN αN (perm_involutive α (fun x=>¬P x) (not_invariant α P ha) hi)
  have heN : perm (α*σ) (fun x=>¬P x) (not_invariant (α*σ) P (mul_invariant σ α P hs ha))=αN*σN := rfl
  rw [perm_mul σ α P hs ha,heN] at hf'
  unfold GenusZero at hz ⊢
  simp only [ConedMap.support_card_nat] at ha' hP hN hz ⊢
  omega

end

open scoped Classical
open PermutationCycles MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
    (S : Set (Cycle σ))

lemma cycleInclude_injective (f : Equiv.Perm O) (P : O→Prop) (hf : ∀ x,P (f x)↔P x) :
    Function.Injective (cycleInclude f P hf) := (cycleEquiv f P hf).symm.injective.comp Sum.inl_injective

def internalPair : Equiv.Perm O := inducedPair α hi (fun x=>cycle σ x∈S)
omit [Fintype O] in
lemma internalPair_involutive : Function.Involutive (internalPair σ α hi S) :=
  inducedPairFun_involutive α hi _
omit [Fintype O] in
lemma rotation_invariant (x : O) : (cycle σ (σ x)∈S)↔cycle σ x∈S := by rw [cycle_apply]
omit [Fintype O] in
lemma pairing_invariant (x : O) : (cycle σ (internalPair σ α hi S x)∈S)↔cycle σ x∈S := by
  change (cycle σ (if cycle σ x∈S ∧ cycle σ (α x)∈S then α x else x)∈S)↔cycle σ x∈S
  split_ifs with h
  · exact iff_of_true h.2 h.1
  · rfl

def rotation := perm σ (fun x=>cycle σ x∈S) (rotation_invariant σ S)
def pairing := perm (internalPair σ α hi S) (fun x=>cycle σ x∈S) (pairing_invariant σ α hi S)
omit [Fintype O] in
lemma pairing_involutive : Function.Involutive (pairing σ α hi S) :=
  perm_involutive _ _ _ (internalPair_involutive σ α hi S)

def vertexEquiv : Cycle (rotation σ S)≃S where
  toFun c := ⟨cycleInclude σ (fun x=>cycle σ x∈S) (rotation_invariant σ S) c,by
    obtain ⟨x,rfl⟩ := cycle_surjective (rotation σ S) c
    exact x.property⟩
  invFun v := cycle (rotation σ S) ⟨Quotient.out v.val,by rw [MapEuler.home_cycle];exact v.property⟩
  left_inv := by
    intro c
    apply cycleInclude_injective
    exact Quotient.out_eq _
  right_inv := by intro v;exact Subtype.ext (Quotient.out_eq v.val)
@[simp] lemma vertexEquiv_cycle (x : {x : O // cycle σ x∈S}) :
    vertexEquiv σ S (cycle (rotation σ S) x)=⟨cycle σ x.val,x.property⟩ := rfl

theorem induced_genusZero (hz : GenusZero σ α) : GenusZero (rotation σ S) (pairing σ α hi S) :=
  genusZero σ (internalPair σ α hi S) (fun x=>cycle σ x∈S) (rotation_invariant σ S)
    (pairing_invariant σ α hi S) (internalPair_involutive σ α hi S)
    (genusZero_inducedPair σ α hi _ hz)

end TorsionFreeZeroDivisors.MapRestrict

namespace TorsionFreeZeroDivisors.MapContract
open scoped Classical
open PermutationCycles MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
    (B : Set (Cycle σ))
local notation "P" => fun x : O=>cycle σ x∈B
local notation "s" => MapRestrict.rotation σ B
local notation "a" => MapRestrict.pairing σ α hi B
local notation "hai" => MapRestrict.pairing_involutive σ α hi B
variable (T : SimpleGraph (Cycle (MapRestrict.rotation σ B)))
  (hT : T≤graph (MapRestrict.rotation σ B) (MapRestrict.pairing σ α hi B) (MapRestrict.pairing_involutive σ α hi B))
local notation "b" => subgraphPair s a hai T hT

def treePair : Equiv.Perm O := Equiv.Perm.ofSubtype (p:=fun x : O=>cycle σ x∈B)
  (subgraphPair (MapRestrict.rotation σ B) (MapRestrict.pairing σ α hi B)
    (MapRestrict.pairing_involutive σ α hi B) T hT)
local notation "β" => treePair σ α hi B T hT
lemma treePair_inside (x : {x : O // P x}) : β x=(b x).val := Equiv.Perm.ofSubtype_apply_coe b x
lemma treePair_outside (x : O) (hx : ¬P x) : β x=x := Equiv.Perm.ofSubtype_apply_of_not_mem b hx
lemma treePair_invariant (x : O) : P (β x)↔P x := Equiv.Perm.ofSubtype_apply_mem_iff_mem b x

def rotation : Equiv.Perm O := β*σ
def pairing : Equiv.Perm O := α*β
local notation "ρ" => rotation σ α hi B T hT
local notation "γ" => pairing σ α hi B T hT

lemma rotation_invariant (x : O) : P (ρ x)↔P x := by
  change P (β (σ x))↔P x
  simpa only [cycle_apply] using treePair_invariant σ α hi B T hT (σ x)
lemma rotation_inside : MapRestrict.perm ρ P (rotation_invariant σ α hi B T hT)=b*s := by
  ext x
  exact treePair_inside σ α hi B T hT (s x)

variable (hz : GenusZero σ α) (ht : T.IsTree)
include hz ht in
lemma inside_cycle_eq {x y : O} (hx : P x) (hy : P y) : cycle ρ x=cycle ρ y := by
  have hn := tree_contour_card s a hai T hT (MapRestrict.induced_genusZero σ α hi B hz) ht
  have hs : Subsingleton (Cycle (b*s)) := (Nat.card_eq_one_iff_unique.mp hn).1
  have h := Subsingleton.elim (cycle (b*s) ⟨x,hx⟩) (cycle (b*s) ⟨y,hy⟩)
  rw [←rotation_inside σ α hi B T hT] at h
  exact congrArg (MapRestrict.cycleInclude ρ P (rotation_invariant σ α hi B T hT)) h

include hz ht in
lemma quotient_invariant (x : O) : cycle ρ (σ x)=cycle ρ x := by
  by_cases hx : P x
  · exact inside_cycle_eq σ α hi B T hT hz ht (by simpa only [cycle_apply] using hx) hx
  · have h : ρ x=σ x := treePair_outside σ α hi B T hT (σ x) (by simpa only [cycle_apply] using hx)
    rw [←h,cycle_apply]

def quotient : Cycle σ→Cycle ρ :=
  PermutationCycles.lift σ (fun x=>cycle ρ x) (quotient_invariant σ α hi B T hT hz ht)
local notation "q" => quotient σ α hi B T hT hz ht
@[simp] lemma quotient_cycle (x : O) : q (cycle σ x)=cycle ρ x := rfl

end TorsionFreeZeroDivisors.MapContract

namespace TorsionFreeZeroDivisors.GraphBall
open scoped Classical
open SimpleGraph
variable {V : Type} (G : SimpleGraph V) (hc : G.Connected) (root : V) (N : ℕ)

include hc

end TorsionFreeZeroDivisors.GraphBall

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GraphQuotient
open SimpleGraph
variable {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (q : V→W)
    (hq : ∀ v w,G.Adj v w→q v=q w ∨ H.Adj (q v) (q w))
end TorsionFreeZeroDivisors.GraphQuotient

namespace TorsionFreeZeroDivisors.PlanarMap

section
open scoped Classical
open PermutationCycles MapEuler
variable {V : Type} (G : SimpleGraph V)
variable {G}

end

open scoped Classical
open PermutationCycles MapEuler
variable {V : Type} (G : SimpleGraph V) (B : Set V)
variable {G B}

end TorsionFreeZeroDivisors.PlanarMap

namespace TorsionFreeZeroDivisors.CutTransfer
open scoped Classical
variable {V W : Type} [Fintype V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    (A : Finset V) (f : V→W)

end TorsionFreeZeroDivisors.CutTransfer

namespace TorsionFreeZeroDivisors.PlanarMap
open scoped Classical
open SimpleGraph
variable {V : Type} [Fintype V] {G : SimpleGraph V}

end TorsionFreeZeroDivisors.PlanarMap

/-!
Sharp level-selection arithmetic for the planar-separator dependency.  The
profile is the actual number of vertices on each integer BFS level.  No planar
separator is assumed or concluded here: the bounded-radius geometric step is
separate.
-/
namespace TorsionFreeZeroDivisors.SeparatorLevels
open scoped BigOperators

end TorsionFreeZeroDivisors.SeparatorLevels

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SeparatorLevels

section
open scoped BigOperators
variable {V : Type*} [Fintype V]

end

variable {V : Type*} (G : SimpleGraph V) (root : V)

end TorsionFreeZeroDivisors.SeparatorLevels

namespace TorsionFreeZeroDivisors.RecursiveSeparator
open scoped Classical
variable {V I : Type} [DecidableEq V] [Fintype I] [DecidableEq I]
    (R : V→V→Prop) (S remove : Finset V) (label : V→I)

end TorsionFreeZeroDivisors.RecursiveSeparator

namespace TorsionFreeZeroDivisors.PlanarMap
open scoped Classical
open SeparatorLevels
variable {V : Type} [Fintype V] {G : SimpleGraph V}

end TorsionFreeZeroDivisors.PlanarMap

namespace TorsionFreeZeroDivisors.RecursiveSeparator.Split
open scoped Classical
variable {V W : Type} [DecidableEq V] [DecidableEq W]
    {R : V→V→Prop} {Q : W→W→Prop} {S : Finset V}

end TorsionFreeZeroDivisors.RecursiveSeparator.Split

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PlanarMap

section
open scoped Classical
open SimpleGraph RecursiveSeparator
variable {V : Type} [Fintype V] {G : SimpleGraph V}

end

open scoped Classical
open RecursiveSeparator
variable {V : Type} [Fintype V] {G : SimpleGraph V}
end TorsionFreeZeroDivisors.PlanarMap

namespace TorsionFreeZeroDivisors.BoundaryRotation
open scoped Classical
open BlockAlignment ComparedBlocks PermutationCycles
variable {T : Type} [Fintype T] (len : T→ℕ) (hpos : ∀t,0<len t)
/-- Actual boundary cycles are exactly the nonempty boundary words. -/
def cyclesEquiv : Cycle (perm len) ≃ T :=
  Equiv.ofBijective (PermutationCycles.lift (perm len) (fun p=>p.1) (first len)) ⟨by
    intro a b he
    obtain ⟨x,rfl⟩ := cycle_surjective (perm len) a
    obtain ⟨y,rfl⟩ := cycle_surjective (perm len) b
    exact (cycle_eq (perm len)).mpr (same_first len he),by
    intro t
    exact ⟨cycle (perm len) ((WordPositions.fin len).symm ⟨t,⟨0,hpos t⟩⟩),rfl⟩⟩
@[simp] lemma cyclesEquiv_cycle (p : Position len) :
    cyclesEquiv len hpos (cycle (perm len) p)=p.1 := rfl

end TorsionFreeZeroDivisors.BoundaryRotation

namespace TorsionFreeZeroDivisors.SampleGraph.Picture
open scoped Classical
open BlockAlignment ComparedBlocks
variable {rep : ℕ} (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep)
  (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.Picture

/-! The parity argument in source sections/factors.tex. We count reversible
flags, retaining parallel edges instead of identifying them in a simple graph. -/
namespace TorsionFreeZeroDivisors.Factors
open scoped BigOperators Classical

lemma odd_nsmul {R : Type*} [AddCommMonoid R] (h2 : ∀ x : R,x+x=0) {n : ℕ}
    (hn : Odd n) (x : R) : n • x=x := by
  obtain ⟨k,rfl⟩ := hn
  simp only [add_nsmul,mul_nsmul,two_nsmul,one_nsmul]
  rw [h2,nsmul_zero,zero_add]

/-- Odd fibres allow an invariant sum over vertices to be computed over flags.
The fixed-point-free involution of flags then cancels it in characteristic two. -/
theorem odd_fibre_cancellation {P F R : Type*} [Fintype P] [Fintype F]
    [AddCommMonoid R] (h2 : ∀ x : R,x+x=0) (proj : F → P) (rev : F → F)
    (hr : Function.Involutive rev) (hne : ∀ e,rev e≠e)
    (hodd : ∀ p,Odd (Finset.univ.filter (fun e => proj e=p)).card)
    (f : P → R) (hf : ∀ e,f (proj (rev e))=f (proj e)) :
    ∑ p,f p=0 := by
  have hs : ∑ e : F,f (proj e)=∑ p : P,f p := by
    rw [← Finset.sum_fiberwise_of_maps_to' (fun e (_ : e∈(Finset.univ : Finset F)) =>
      Finset.mem_univ (proj e)) f]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_const]
    exact odd_nsmul h2 (hodd p) (f p)
  rw [← hs]
  exact Finset.sum_ninvolution rev
    (fun e => by rw [hf]; exact h2 _)
    (fun e _ => hne e) (fun _ => Finset.mem_univ _) hr

variable {A B T G : Type*} [Fintype A] [Fintype B] [Fintype T] [_root_.Group G]
variable (outA : A → Finset T) (outB : B → Finset T)
abbrev DartA := {p : A×T // p.2∈outA p.1}
abbrev DartB := {p : B×T // p.2∈outB p.1}
abbrev Flag := {p : DartA outA×DartB outB // p.1.val.2=p.2.val.2}
def base (e : Flag outA outB) : A×B := (e.val.1.val.1,e.val.2.val.1)

/-- The entire common outgoing set, not a quotient of its parallel steps. -/
def fibreEquiv (p : A×B) : {e : Flag outA outB // base outA outB e=p} ≃
    {t : T // t∈outA p.1∩outB p.2} where
  toFun e := ⟨e.val.val.1.val.2,by
    have ha := e.val.val.1.property
    have hb := e.val.val.2.property
    have h1 := congrArg Prod.fst e.property
    have h2 := congrArg Prod.snd e.property
    change e.val.val.1.val.1=p.1 at h1
    change e.val.val.2.val.1=p.2 at h2
    exact Finset.mem_inter.mpr ⟨by simpa only [h1] using ha,
      by simpa only [h2,← e.val.property] using hb⟩⟩
  invFun t := ⟨⟨(⟨(p.1,t.val),(Finset.mem_inter.mp t.property).1⟩,
      ⟨(p.2,t.val),(Finset.mem_inter.mp t.property).2⟩),rfl⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (congrArg Prod.fst e.property).symm rfl
    · apply Subtype.ext
      exact Prod.ext (congrArg Prod.snd e.property).symm e.val.property
  right_inv _ := rfl

lemma fibre_card (p : A×B) :
    (Finset.univ.filter (fun e : Flag outA outB => base outA outB e=p)).card=
      (outA p.1∩outB p.2).card := by
  have h := Fintype.card_congr (fibreEquiv outA outB p)
  simpa only [Fintype.card_subtype,Finset.filter_mem_eq_inter,Finset.univ_inter] using h

variable (bar : T→T) (rA : DartA outA→DartA outA) (rB : DartB outB→DartB outB)
  (hA : ∀ d,(rA d).val.2=bar d.val.2) (hB : ∀ d,(rB d).val.2=bar d.val.2)
def reverse (e : Flag outA outB) : Flag outA outB :=
  ⟨(rA e.val.1,rB e.val.2),by rw [hA,hB,e.property]⟩
omit [Fintype A] [Fintype B] [Fintype T] in
lemma reverse_involutive (hrA : Function.Involutive rA) (hrB : Function.Involutive rB) :
    Function.Involutive (reverse outA outB bar rA rB hA hB) := by
  intro e
  apply Subtype.ext
  exact Prod.ext (hrA e.val.1) (hrB e.val.2)
omit [Fintype A] [Fintype B] [Fintype T] in
lemma reverse_ne (hbar : ∀ t,bar t≠t) (e : Flag outA outB) :
    reverse outA outB bar rA rB hA hB e≠e := by
  intro he
  have h := congrArg (fun z : Flag outA outB => z.val.1.val.2) he
  exact hbar e.val.1.val.2 ((hA e.val.1).symm.trans h)

include hA hB in
/-- The source factors on full components; compatibility is the literal
path-order rule along every outgoing edge. -/
theorem product_zero
    (hrA : Function.Involutive rA) (hrB : Function.Involutive rB)
    (hbar : ∀ t,bar t≠t) (hodd : ∀ a b,Odd (outA a∩outB b).card)
    (letter : T→G) (g : A→G) (h : B→G)
    (hg : ∀ d : DartA outA,g (rA d).val.1=g d.val.1*letter d.val.2)
    (hh : ∀ d : DartB outB,h (rB d).val.1=h d.val.1*letter d.val.2) :
    (∑ a,MonoidAlgebra.single (g a) (1 : ZMod 2)) *
      (∑ b,MonoidAlgebra.single ((h b)⁻¹) (1 : ZMod 2))=0 := by
  have h2 (x : MonoidAlgebra (ZMod 2) G) : x+x=0 := by
    ext z
    exact CharTwo.add_self_eq_zero (x.coeff z)
  have hz := odd_fibre_cancellation h2 (base outA outB)
    (reverse outA outB bar rA rB hA hB)
    (reverse_involutive outA outB bar rA rB hA hB hrA hrB)
    (reverse_ne outA outB bar rA rB hA hB hbar)
    (fun p => by
      convert hodd p.1 p.2 using 1
      convert fibre_card outA outB p using 1
      congr 1
      ext e
      simp)
    (fun p : A×B => MonoidAlgebra.single (g p.1*(h p.2)⁻¹) (1 : ZMod 2)) (by
      intro e
      change MonoidAlgebra.single (g (rA e.val.1).val.1*(h (rB e.val.2).val.1)⁻¹) _ = _
      rw [hg,hh,e.property]
      congr 1
      dsimp only [base]
      group)
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum,MonoidAlgebra.single_mul_single,one_mul]
  simpa only [Fintype.sum_prod_type] using hz

end TorsionFreeZeroDivisors.Factors

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedComponent
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings TypedGraphs
variable {V : Type} (outgoing : V→Finset Types.Letter)
    (r : Matching (label outgoing) Types.inverse) (root : V)
def out (v : Vertex outgoing r root) : Finset Types.Letter := outgoing v.val
abbrev Dart := Factors.DartA (out outgoing r root)
def lift (d : Dart outgoing r root) : TypedGraphs.Dart outgoing :=
  ⟨(d.val.1.val,d.val.2),d.property⟩
lemma lift_injective : Function.Injective (lift outgoing r root) := by
  intro d e h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z : TypedGraphs.Dart outgoing => z.val.1) h
  · exact congrArg (fun z : TypedGraphs.Dart outgoing => z.val.2) h

def reverse (d : Dart outgoing r root) : Dart outgoing r root :=
  ⟨(⟨(r (lift outgoing r root d)).val.1,
    d.val.1.property.trans (ShortClosure.dart_reachable (graph outgoing r) (lift outgoing r root d))⟩,
    (r (lift outgoing r root d)).val.2),(r (lift outgoing r root d)).property⟩
lemma lift_reverse (d : Dart outgoing r root) :
    lift outgoing r root (reverse outgoing r root d)=r (lift outgoing r root d) := rfl
lemma reverse_reverse : Function.Involutive (reverse outgoing r root) := by
  intro d
  apply lift_injective outgoing r root
  rw [lift_reverse,lift_reverse,r.reverse_reverse]
lemma label_reverse (d : Dart outgoing r root) :
    (reverse outgoing r root d).val.2=Types.inverse d.val.2 :=
  r.label_reverse (lift outgoing r root d)
def base : Vertex outgoing r root := ⟨root,.refl _⟩
end TorsionFreeZeroDivisors.TypedComponent

namespace TorsionFreeZeroDivisors.ComponentFactors
open scoped Classical BigOperators
open ConditionedMatchings TypedGraphs TypedComponent SampleGraph
variable {G : Type} [_root_.Group G] (rep : ℕ) (r : ActualPatternEvent.Match rep)
  (x : SampleGraph.VA rep) (y : SampleGraph.VB rep)
/-- Actual full components in the chosen sample, with every outgoing edge
retained. Parallel simultaneous steps cancel as distinct signed flags. -/
theorem product_zero (letter : Types.Letter→G) (g : CA rep r x→G) (h : CB rep r y→G)
    (hg : ∀ d : TypedComponent.Dart (@Types.outgoingA rep) r.1 x,
      g (TypedComponent.reverse _ r.1 x d).val.1=g d.val.1*letter d.val.2)
    (hh : ∀ d : TypedComponent.Dart (@Types.outgoingB rep) r.2 y,
      h (TypedComponent.reverse _ r.2 y d).val.1=h d.val.1*letter d.val.2) :
    (∑ a,MonoidAlgebra.single (g a) (1 : ZMod 2)) *
      (∑ b,MonoidAlgebra.single ((h b)⁻¹) (1 : ZMod 2))=0 := by
  exact Factors.product_zero (TypedComponent.out _ r.1 x) (TypedComponent.out _ r.2 y)
    Types.inverse (TypedComponent.reverse _ r.1 x) (TypedComponent.reverse _ r.2 y)
    (TypedComponent.label_reverse _ r.1 x) (TypedComponent.label_reverse _ r.2 y)
    (TypedComponent.reverse_reverse _ r.1 x) (TypedComponent.reverse_reverse _ r.2 y)
    Types.inverse_ne (fun leftVertex rightVertex => by
      convert Types.odd_cross_intersections leftVertex.val rightVertex.val using 1
      congr 1
      ext letterType
      simp [TypedComponent.out]) letter g h hg hh

end TorsionFreeZeroDivisors.ComponentFactors

namespace TorsionFreeZeroDivisors.ConcreteFactors
open scoped Classical BigOperators
open TypedGraphs ConditionedMatchings SampleGraph ConcreteGroup TypedComponent
variable (rep : ℕ) (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep)
lemma left_edge (d : TypedComponent.Dart (@Types.outgoingA rep) r.1 x) :
    leftValue rep r x (TypedComponent.reverse _ r.1 x d).val.1=
      leftValue rep r x d.val.1*letter rep r d.val.2 := by
  have h := ConcreteGroup.edge rep r (Sum.inl (TypedComponent.lift _ r.1 x d))
  change value rep r (Sum.inl (r.1 (TypedComponent.lift _ r.1 x d)).val.1)=
    value rep r (Sum.inl d.val.1.val)*letter rep r d.val.2 at h
  change (value rep r (Sum.inl x))⁻¹*value rep r (Sum.inl (r.1 (TypedComponent.lift _ r.1 x d)).val.1)=_
  rw [h]
  exact (mul_assoc _ _ _).symm
lemma right_edge (d : TypedComponent.Dart (@Types.outgoingB rep) r.2 y) :
    rightValue rep r y (TypedComponent.reverse _ r.2 y d).val.1=
      rightValue rep r y d.val.1*letter rep r d.val.2 := by
  have h := ConcreteGroup.edge rep r (Sum.inr (TypedComponent.lift _ r.2 y d))
  change value rep r (Sum.inr (r.2 (TypedComponent.lift _ r.2 y d)).val.1)=
    value rep r (Sum.inr d.val.1.val)*letter rep r d.val.2 at h
  change (value rep r (Sum.inr y))⁻¹*value rep r (Sum.inr (r.2 (TypedComponent.lift _ r.2 y d)).val.1)=_
  rw [h]
  exact (mul_assoc _ _ _).symm
@[simp] lemma left_root : leftValue rep r x (TypedComponent.base _ r.1 x)=1 := by
  simp [leftValue,TypedComponent.base]
@[simp] lemma right_root : rightValue rep r y (TypedComponent.base _ r.2 y)=1 := by
  simp [rightValue,TypedComponent.base]
/-- The author's factors multiply to zero in the exact finite graph presentation,
for every matching sample. Nonvanishing is a separate geometric obligation. -/
theorem product_zero : alpha rep r x*beta rep r y=0 :=
  ComponentFactors.product_zero rep r x y (letter rep r) (leftValue rep r x) (rightValue rep r y)
    (left_edge rep r x) (right_edge rep r y)
end TorsionFreeZeroDivisors.ConcreteFactors

namespace TorsionFreeZeroDivisors.SumPort
open scoped Classical
open PortSubdivision
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
end TorsionFreeZeroDivisors.SumPort
namespace TorsionFreeZeroDivisors.ConcreteFactors

section
open scoped Classical
open SampleGraph ConcreteGroup
variable {rep : ℕ} (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep) (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r) (hsample : r∈ActualPatternEvent.samples rep) (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
    (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y))

end
open scoped Classical
open SampleGraph
variable {rep : ℕ} (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep)
  (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
  (hsample : r∈ActualPatternEvent.samples rep)
  (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
    (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y))
include hL hd hsample havoid
end TorsionFreeZeroDivisors.ConcreteFactors

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical
open Filter GirthAsymptotics TypedGraphs
/-- An actual sample with both nonzero factors in its exact finitely presented
group. Torsion-freeness and the topological classifying-space clause are NOT
asserted here; they remain obligations for the main theorem. -/
theorem exists_nonzero_factors :
    ∃ (rep : ℕ) (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep),
      r∈ActualPatternEvent.samples rep ∧ 2≤L (size rep) ∧
      GraphSample.Diameters rep r ∧
      IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
        (PlanarParameters.K PathSystem.ε ClosedWords.D)
        (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y) ∧
      ConcreteFactors.alpha rep r x≠0 ∧ ConcreteFactors.beta rep r y≠0 ∧
      ConcreteFactors.alpha rep r x*ConcreteFactors.beta rep r y=0 := by
  have he := exists_avoiding (PlanarParameters.C PathSystem.ε ClosedWords.D)
    (PlanarParameters.K PathSystem.ε ClosedWords.D)
    (PlanarParameters.sides PathSystem.ε ClosedWords.D)
    (PlanarParameters.K_pos _ _) (PlanarParameters.sides_pos _ _)
  have hL := (L_tendsto.comp size_tendsto).eventually (eventually_ge_atTop 2)
  obtain ⟨rep,hrep,hL,hpos⟩ := (he.and (hL.and (eventually_ge_atTop 1))).exists
  let : NeZero rep := ⟨by omega⟩
  let x : VA rep := Classical.choice inferInstance
  let y : VB rep := Classical.choice inferInstance
  obtain ⟨r,hr,hd,ha⟩ := hrep x y
  obtain ⟨hx,hy⟩ := ConcreteFactors.both_nonzero r x y hL hd hr ha
  exact ⟨rep,r,x,y,hr,hL,hd,ha,hx,hy,ConcreteFactors.product_zero rep r x y⟩
end TorsionFreeZeroDivisors.SampleGraph

namespace TorsionFreeZeroDivisors
end TorsionFreeZeroDivisors

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WordCursor

section
open scoped Classical
variable {A G : Type*} [_root_.Group G] (v : A→G)
def value (w : List A) : G := (w.map v).prod
def cursor (w : List A) (n : ℕ) : G := value v (w.take n)
@[simp] lemma value_nil : value v []=1 := rfl
@[simp] lemma value_cons (a : A) (w : List A) : value v (a::w)=v a*value v w := rfl
@[simp] lemma value_append (x y : List A) : value v (x++y)=value v x*value v y := by simp [value]
@[simp] lemma cursor_zero (w : List A) : cursor v w 0=1 := rfl
@[simp] lemma cursor_length (w : List A) : cursor v w w.length=value v w := by simp [cursor]
lemma cursor_succ (w : List A) (i : Fin w.length) :
    cursor v w (i.val+1)=cursor v w i.val*v (w.get i) := by
  rw [cursor,List.take_succ_eq_append_getElem i.isLt,value_append]
  simp only [value_cons,value_nil,mul_one]
  rfl
lemma cursor_append_left (x y : List A) (n : ℕ) (hn : n≤x.length) :
    cursor v (x++y) n=cursor v x n := by
  rw [cursor,List.take_append_of_le_length hn]
  rfl
lemma cursor_append_right (x y : List A) (n : ℕ) :
    cursor v (x++y) (x.length+n)=value v x*cursor v y n := by
  simp only [cursor,List.take_append,List.take_of_length_le (by omega : x.length≤x.length+n),
    Nat.add_sub_cancel_left,value_append]
lemma cursor_cons_succ (a : A) (w : List A) (n : ℕ) :
    cursor v (a::w) (n+1)=v a*cursor v w n := rfl
lemma insert_old (u w : List A) (a b : A) (hb : v a*v b=1) (i : ℕ) :
    cursor v (u++a::b::w) (if i<u.length then i else i+2)=cursor v (u++w) i := by
  by_cases hi : i<u.length
  · rw [if_pos hi,cursor_append_left v u (a::b::w) i hi.le,cursor_append_left v u w i hi.le]
  · rw [if_neg hi]
    have hs : i=u.length+(i-u.length) := by omega
    rw [hs,show u.length+(i-u.length)+2=u.length+((i-u.length)+2) by omega,
      cursor_append_right,cursor_append_right]
    rw [show (i-u.length)+2=((i-u.length)+1)+1 by omega,cursor_cons_succ,cursor_cons_succ]
    calc
      _=value v u*((v a*v b)*cursor v w (i-u.length)) := by simp only [mul_assoc]
      _=_ := by rw [hb,one_mul]
lemma insert_first (u w : List A) (a b : A) : cursor v (u++a::b::w) u.length=value v u := by
  rw [cursor_append_left v u _ _ le_rfl,cursor_length]
lemma insert_second (u w : List A) (a b : A) : cursor v (u++a::b::w) (u.length+1)=value v u*v a := by
  rw [cursor_append_right,cursor_cons_succ,cursor_zero,mul_one]
variable (inv : A→A) (hv : ∀a,v (inv a)=(v a)⁻¹)
def Paired {w : List A} (d : WordPairing.Data inv w.get) : Prop :=
  ∀i,cursor v w (d.partner i).val=cursor v w i.val*v (w.get i)
include hv in
lemma inserted (u w : List A) (a : A) (d : WordPairing.Data inv (u++w).get)
    (ha : inv (inv a)=a) (hd : Paired v inv d) :
    Paired v inv (WordPairing.ListInsert.data u w inv a d ha) := by
  intro i
  let hk : u.length≤(u++w).length := by simp only [List.length_append];omega
  let e := WordPairing.Ear.equiv u.length hk
  obtain ⟨i,rfl⟩ := (WordPairing.ListInsert.orderIso u w inv a).surjective i
  obtain ⟨i,rfl⟩ := e.surjective i
  change cursor v (u++a::inv a::w)
    (((WordPairing.ListInsert.orderIso u w inv a).toEquiv.permCongr
      (WordPairing.Ear.partner u.length d hk)) ((WordPairing.ListInsert.orderIso u w inv a) (e i))).val=_
  simp only [Equiv.permCongr_apply]
  change cursor v (u++a::inv a::w) (WordPairing.Ear.partner u.length d hk (e i)).val=_
  rw [WordPairing.Ear.partner_apply]
  cases i with
  | inl i =>
    change cursor v (u++a::inv a::w) (if (d.partner i).val<u.length then (d.partner i).val else (d.partner i).val+2)=
      cursor v (u++a::inv a::w) (if i.val<u.length then i.val else i.val+2)*
      v ((u++a::inv a::w).get ((WordPairing.ListInsert.orderIso u w inv a) (e (.inl i))))
    rw [insert_old v u w a (inv a) (by rw [hv,mul_inv_cancel]),
      insert_old v u w a (inv a) (by rw [hv,mul_inv_cancel])]
    rw [WordPairing.ListInsert.labels_eq,WordPairing.Ear.labels_left]
    exact hd i
  | inr b =>
    cases b
    · change cursor v (u++a::inv a::w) (u.length+1)=cursor v (u++a::inv a::w) u.length*
        v ((u++a::inv a::w).get ((WordPairing.ListInsert.orderIso u w inv a) (e (.inr false))))
      rw [insert_first,insert_second,WordPairing.ListInsert.labels_eq,WordPairing.Ear.labels_false]
    · change cursor v (u++a::inv a::w) u.length=cursor v (u++a::inv a::w) (u.length+1)*
        v ((u++a::inv a::w).get ((WordPairing.ListInsert.orderIso u w inv a) (e (.inr true))))
      rw [insert_first,insert_second,WordPairing.ListInsert.labels_eq,WordPairing.Ear.labels_true,hv,
        mul_inv_cancel_right]
end
open scoped Classical
variable {A G : Type*} [_root_.Group G] (v : A×Bool→G)
  (hv : ∀a,v (WordPairing.inverseLetter a)=(v a)⁻¹)
include hv in
lemma of_reduction {w : List (A×Bool)} (h : FreeGroup.Red w []) :
    ∃d : WordPairing.Data WordPairing.inverseLetter w.get,Paired v _ d := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨WordPairing.emptyData,fun i=>Fin.elim0 i⟩
  | @head x y hxy hy ih =>
    cases hxy with
    | @not u w a b =>
      obtain ⟨d,hd⟩ := ih
      exact ⟨WordPairing.ListInsert.data u w WordPairing.inverseLetter (a,b) d
        (WordPairing.inverseLetter_involutive _),inserted v _ hv u w (a,b) d
        (WordPairing.inverseLetter_involutive _) hd⟩
include hv in
lemma of_identity {w : List (A×Bool)} (h : FreeGroup.mk w=1) :
    ∃d : WordPairing.Data WordPairing.inverseLetter w.get,Paired v _ d := by
  apply of_reduction v hv
  have hh : FreeGroup.reduce w=[] := FreeGroup.reduce.sound h
  rw [←hh]
  exact FreeGroup.reduce.red
end TorsionFreeZeroDivisors.WordCursor

end

end OAI

end
end

section
section
namespace OAI

section

namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
noncomputable section
variable {A G : Type*} [_root_.Group G] (v : A→G) {inv : A→A} {ws : List (List A)}
structure Lift (d : Matching inv ws) where
  position : Occ ws→G
  next : ∀i,position (BlockBoundary.rotation (lengths ws) i)=position i*v (letter ws i)
  pair : ∀i,position (d.partner i)=position i*v (letter ws i)
variable {v}
lemma cursor_rotation (w : List A) (hw : WordCursor.value v w=1) (i : Fin w.length) :
    WordCursor.cursor v w (finRotate w.length i).val=WordCursor.cursor v w i.val*v (w.get i) := by
  by_cases hi : i.val+1<w.length
  · have hh : (finRotate w.length i).val=i.val+1 := by
      obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w.length≠0)
      have aux : ∀j : Fin w.length,j.val+1<w.length→(finRotate w.length j).val=j.val+1 := by
        rw [hn]
        rintro ⟨j,hj⟩ hjj
        change j+1<n+1 at hjj
        exact congrArg Fin.val (finRotate_of_lt (by omega : j<n))
      exact aux i hi
    rw [hh]
    exact WordCursor.cursor_succ v w i
  · have he : i.val+1=w.length := by omega
    have h := WordCursor.cursor_succ v w i
    rw [he,WordCursor.cursor_length,hw] at h
    have hh : (finRotate w.length i).val=0 := by
      obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w.length≠0)
      have aux : ∀j : Fin w.length,j.val+1=w.length→(finRotate w.length j).val=0 := by
        rw [hn]
        intro j hj
        have hjj : j=Fin.last n := by apply Fin.ext; simp only [Fin.val_last];omega
        rw [hjj,finRotate_last]
        rfl
      exact aux i he
    rw [hh]
    exact h
lemma flat_rotation (ws : List (List A)) (h : ∀w∈ws,WordCursor.value v w=1) (i : Occ ws) :
    WordCursor.cursor v ws.flatten (coordinates ws (BlockBoundary.rotation (lengths ws) i)).val=
      WordCursor.cursor v ws.flatten (coordinates ws i).val*v (letter ws i) := by
  induction ws with
  | nil=>exact Empty.elim i
  | cons w ws ih=>
    cases i with
    | inl i=>
      change WordCursor.cursor v (w++ws.flatten) (finRotate w.length i).val=
        WordCursor.cursor v (w++ws.flatten) i.val*v (w.get i)
      rw [WordCursor.cursor_append_left v _ _ _ (finRotate _ i).isLt.le,
        WordCursor.cursor_append_left v _ _ _ i.isLt.le]
      exact cursor_rotation w (h w (List.mem_cons_self)) i
    | inr i=>
      change WordCursor.cursor v (w++ws.flatten) (w.length+(coordinates ws (BlockBoundary.rotation (lengths ws) i)).val)=
        WordCursor.cursor v (w++ws.flatten) (w.length+(coordinates ws i).val)*v (letter ws i)
      rw [WordCursor.cursor_append_right,WordCursor.cursor_append_right,
        ih (fun w hw=>h w (List.mem_cons_of_mem _ hw)),mul_assoc]
def liftOfDisk (d : WordPairing.Data inv ws.flatten.get) (hd : WordCursor.Paired v inv d)
    (h : ∀w∈ws,WordCursor.value v w=1) : Lift v (ofDisk ws d) where
  position i := WordCursor.cursor v ws.flatten (coordinates ws i).val
  next := flat_rotation ws h
  pair i := by
    change WordCursor.cursor v ws.flatten (coordinates ws ((coordinates ws).symm.permCongr d.partner i)).val=_
    simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply,letter_eq]
    exact hd _
end
end TorsionFreeZeroDivisors.WordBlocks

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
noncomputable section
variable {A G : Type} [_root_.Group G] {v : A→G} {inv : A→A} {ws vs : List (List A)}
def Lift.rename {d : Matching inv ws} (l : Lift v d) (e : Occ ws≃Occ vs)
    (hl : ∀x,letter vs (e x)=letter ws x)
    (hr : ∀x,e (BlockBoundary.rotation (lengths ws) x)=BlockBoundary.rotation (lengths vs) (e x)) :
    Lift v (d.rename e hl hr) where
  position i := l.position (e.symm i)
  next i := by
    obtain ⟨i,rfl⟩ := e.surjective i
    rw [←hr,Equiv.symm_apply_apply,Equiv.symm_apply_apply,hl]
    exact l.next i
  pair i := by
    obtain ⟨i,rfl⟩ := e.surjective i
    change l.position (e.symm (e.permCongr d.partner (e i)))=_
    simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply,hl]
    exact l.pair i
variable (hv : ∀a,v (inv a)=(v a)⁻¹) (hinv : Function.Involutive inv)
variable (a : A) (w : List A) (ws : List (List A))
def capEmbedding (x : Occ (w::ws)) : Occ ((a::(w++[inv a]))::ws) :=
  (capCoordinates (inv:=inv) a w ws).symm (CyclicCaps.embed w.length x)
variable {a w ws}
def Lift.removeCaps {d : Matching inv ((a::(w++[inv a]))::ws)} (l : Lift v d) :
    Lift v (d.removeCaps hinv a w ws) := by
  let e := capCoordinates (inv:=inv) a w ws
  let α := e.permCongr d.partner
  let σ := CyclicCaps.rotation w.length (BlockBoundary.rotation (lengths ws))
  let pos := fun x=>l.position (e.symm x)
  let lab := capLabel (inv:=inv) a w ws
  have hi : Function.Involutive α := PermutationTransport.involutive e d.partner d.involutive
  have hf : ∀x,α x≠x := PermutationTransport.fixed_free e d.partner d.fixed_free
  have hpos : ∀x,pos (σ x)=pos x*v (lab x) := by
    intro x
    have hs := capRotation (inv:=inv) a w ws
    change e.permCongr (BlockBoundary.rotation (lengths ((a::(w++[inv a]))::ws)))=σ at hs
    rw [←hs]
    change l.position (e.symm (e.permCongr _ x))=_
    simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
    exact l.next _
  have hpair : ∀x,pos (α x)=pos x*v (lab x) := by
    intro x
    change l.position (e.symm (e.permCongr d.partner x))=_
    simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
    exact l.pair _
  have hp : pos (CyclicCaps.q w.length)=pos (CyclicCaps.p w.length)*v (lab (CyclicCaps.p w.length)) := by
    rw [←CyclicCaps.next w.length (BlockBoundary.rotation (lengths ws))]
    exact hpos _
  have hq : pos (CyclicCaps.q w.length)*v (lab (CyclicCaps.q w.length))=pos (CyclicCaps.p w.length) := by
    rw [hp]
    dsimp only [lab]
    rw [capLabel_p,capLabel_q,hv,inv_mul_cancel_right]
  refine ⟨fun i=>l.position (capEmbedding a w ws i),?_,?_⟩
  · intro i
    have hh := Tightening.consistent σ (CyclicCaps.p w.length) (CyclicCaps.q w.length)
      (CyclicCaps.distinct w.length) (CyclicCaps.next _ _) pos (fun x=>pos x*v (lab x))
      (fun x=>(hpos x).symm) hq (CyclicCaps.coordinates w.length i)
    change pos (CyclicCaps.coordinates w.length i)*v (lab (CyclicCaps.coordinates w.length i))=
      pos (Tightening.rotation σ _ _ _ _ (CyclicCaps.coordinates w.length i)) at hh
    have rot := congrArg (fun x : MatchingSurgery.Remaining (CyclicCaps.p (R:=Occ ws) w.length)
      (CyclicCaps.q w.length)=>pos x)
      (CyclicCaps.rotation_commutes w.length (BlockBoundary.rotation (lengths ws)) i)
    have hh := rot.symm.trans hh.symm
    exact hh.trans (congrArg (pos (CyclicCaps.coordinates w.length i)*·)
      (congrArg v (capLabel_embed a w ws i)))
  · intro i
    change pos (CyclicCaps.coordinates w.length (CyclicCaps.partner w.length α hi hf i))=_
    change pos ((CyclicCaps.coordinates w.length) ((CyclicCaps.coordinates w.length).symm
      ((MatchingSurgery.partner α hi hf (CyclicCaps.p w.length) (CyclicCaps.q w.length)
        (CyclicCaps.distinct w.length)) (CyclicCaps.coordinates w.length i))))=_
    rw [Equiv.apply_symm_apply]
    change pos (PartialMatchingSurgery.splice α (CyclicCaps.p w.length) (CyclicCaps.q w.length)
      (CyclicCaps.coordinates w.length i))=_
    let x := CyclicCaps.coordinates w.length i
    have hh : pos (PartialMatchingSurgery.splice α (CyclicCaps.p w.length) (CyclicCaps.q w.length) x)=pos x*v (lab x) := by
      by_cases h1 : α x=CyclicCaps.p w.length
      · rw [PartialMatchingSurgery.splice,if_pos h1,hpair,hq]
        exact (congrArg pos h1).symm.trans (hpair x)
      · by_cases h2 : α x=CyclicCaps.q w.length
        · rw [PartialMatchingSurgery.splice,if_neg h1,if_pos h2,hpair,←hp]
          exact (congrArg pos h2).symm.trans (hpair x)
        · rw [PartialMatchingSurgery.splice,if_neg h1,if_neg h2,hpair]
    exact hh.trans (congrArg (pos x*·) (congrArg v (capLabel_embed a w ws i)))
end
end TorsionFreeZeroDivisors.WordBlocks

end


end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.WordFrames
open scoped Classical
open WordBlocks WordCursor
noncomputable section
variable {A G : Type} [_root_.Group G] (v : A→G) (inv : A→A)
abbrev words (bs : List (G×List A)) : List (List A) := bs.map Prod.snd
def position : (bs : List (G×List A))→Occ (words bs)→G
  | [],i=>Empty.elim i
  | (g,w)::_bs,.inl i=>g*cursor v w i.val
  | (_g,_w)::bs,.inr i=>position bs i
structure Data (bs : List (G×List A)) where
  matching : Matching inv (words bs)
  lifted : Lift v matching
  framed : ∀i,lifted.position i=position v bs i
variable {v inv}
def Data.rename {bs cs : List (G×List A)} (d : Data v inv bs)
    (e : Occ (words bs)≃Occ (words cs))
    (hl : ∀i,letter (words cs) (e i)=letter (words bs) i)
    (hr : ∀i,e (BlockBoundary.rotation (lengths (words bs)) i)=BlockBoundary.rotation (lengths (words cs)) (e i))
    (hp : ∀i,position v cs (e i)=position v bs i) : Data v inv cs where
  matching := d.matching.rename e hl hr
  lifted := d.lifted.rename e hl hr
  framed i := by
    change d.lifted.position (e.symm i)=_
    rw [d.framed,←hp,Equiv.apply_symm_apply]
variable (hv : ∀a,v (inv a)=(v a)⁻¹) (hi : Function.Involutive inv)
def Data.removeCaps (g : G) (a : A) (w : List A) (bs : List (G×List A))
    (d : Data v inv ((g,a::(w++[inv a]))::bs)) : Data v inv ((g*v a,w)::bs) where
  matching := d.matching.removeCaps hi a w (words bs)
  lifted := d.lifted.removeCaps hv hi
  framed i := by
    change d.lifted.position (capEmbedding a w (words bs) i)=_
    rw [d.framed]
    cases i with
    | inl i=>
      change g*cursor v (a::(w++[inv a])) (i.val+1)=(g*v a)*cursor v w i.val
      rw [cursor_cons_succ,cursor_append_left v w [inv a] i.val i.isLt.le,mul_assoc]
    | inr i=>rfl
def focus : (pre : List (G×List A))→(g : G)→(w : List A)→(post : List (G×List A))→
    Occ (words (pre++(g,w)::post))≃Occ (words ((g,w)::(pre++post)))
  | [],_,_,_=>Equiv.refl _
  | t::pre,g,w,post=>(Equiv.sumCongr (Equiv.refl (Fin t.2.length)) (focus pre g w post)).trans exchange
omit [_root_.Group G] in
lemma focus_letter (pre : List (G×List A)) (g : G) (w : List A) (post : List (G×List A))
    (i : Occ (words (pre++(g,w)::post))) :
    letter (words ((g,w)::(pre++post))) (focus pre g w post i)=letter (words (pre++(g,w)::post)) i := by
  induction pre with
  | nil=>rfl
  | cons t pre ih=>
    cases i with
    | inl i=>rfl
    | inr i=>
      change Sum.elim w.get (Sum.elim t.2.get (letter (words (pre++post))))
        (exchange (.inr (focus pre g w post i)))=letter (words (pre++(g,w)::post)) i
      rw [exchange_letter]
      exact ih i
omit [_root_.Group G] in
lemma focus_rotation (pre : List (G×List A)) (g : G) (w : List A) (post : List (G×List A))
    (i : Occ (words (pre++(g,w)::post))) :
    focus pre g w post (BlockBoundary.rotation (lengths (words (pre++(g,w)::post))) i)=
      BlockBoundary.rotation (lengths (words ((g,w)::(pre++post)))) (focus pre g w post i) := by
  induction pre with
  | nil=>rfl
  | cons t pre ih=>
    cases i with
    | inl i=>rfl
    | inr i=>
      change exchange (.inr (focus pre g w post (BlockBoundary.rotation (lengths (words (pre++(g,w)::post))) i)))=
        Equiv.sumCongr (finRotate w.length)
          (Equiv.sumCongr (finRotate t.2.length) (BlockBoundary.rotation (lengths (words (pre++post)))))
          (exchange (.inr (focus pre g w post i)))
      rw [ih]
      exact exchange_rotation (finRotate t.2.length) (finRotate w.length) (BlockBoundary.rotation (lengths (words (pre++post)))) (.inr (focus pre g w post i))
lemma focus_position (pre : List (G×List A)) (g : G) (w : List A) (post : List (G×List A))
    (i : Occ (words (pre++(g,w)::post))) :
    position v ((g,w)::(pre++post)) (WordFrames.focus pre g w post i)=position v (pre++(g,w)::post) i := by
  induction pre with
  | nil=>rfl
  | cons t pre ih=>
    cases t with
    | mk g' w'=>
      cases i with
      | inl i=>rfl
      | inr i=>
        have hh := ih i
        change position v ((g,w)::(g',w')::(pre++post))
          (exchange (.inr (WordFrames.focus pre g w post i)))=position v (pre++(g,w)::post) i
        cases he : WordFrames.focus pre g w post i with
        | inl j=>rw [he] at hh; exact hh
        | inr j=>rw [he] at hh; exact hh
variable (v)
def Data.focus (pre : List (G×List A)) (g : G) (w : List A) (post : List (G×List A))
    (d : Data v inv (pre++(g,w)::post)) : Data v inv ((g,w)::(pre++post)) :=
  d.rename (WordFrames.focus pre g w post)
    (WordFrames.focus_letter _ _ _ _) (WordFrames.focus_rotation _ _ _ _) (focus_position pre g w post)
def Data.unfocus (pre : List (G×List A)) (g : G) (w : List A) (post : List (G×List A))
    (d : Data v inv ((g,w)::(pre++post))) : Data v inv (pre++(g,w)::post) :=
  d.rename (WordFrames.focus pre g w post).symm
    (fun x=>by simpa using (WordFrames.focus_letter pre g w post ((WordFrames.focus pre g w post).symm x)).symm)
    (fun x=>by
      apply (WordFrames.focus pre g w post).injective
      simpa only [Equiv.apply_symm_apply] using (WordFrames.focus_rotation pre g w post ((WordFrames.focus pre g w post).symm x)).symm)
    (fun x=>by simpa only [Equiv.apply_symm_apply] using
      (focus_position (v:=v) pre g w post ((WordFrames.focus pre g w post).symm x)).symm)
end
end TorsionFreeZeroDivisors.WordFrames

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.WordFrames
open scoped Classical
open WordBlocks WordCursor FreeGroup AlgebraicPictures
noncomputable section
variable {A G : Type} [_root_.Group G] (v : A×Bool→G)
  (hv : ∀a,v (WordPairing.inverseLetter a)=(v a)⁻¹)
def Data.removeConjugator (g : G) (c w : List (A×Bool)) (bs : List (G×List (A×Bool)))
    (d : Data v WordPairing.inverseLetter ((g,c++w++invRev c)::bs)) :
    Data v WordPairing.inverseLetter ((g*value v c,w)::bs) := by
  induction c generalizing g with
  | nil=>simpa only [List.nil_append,invRev_empty,List.append_nil,value_nil,mul_one] using d
  | cons a c ih=>
    have he : (a::c)++w++invRev (a::c)=a::((c++w++invRev c)++[WordPairing.inverseLetter a]) := by
      simp only [List.cons_append,invRev,WordPairing.inverseLetter,
        List.reverse_cons,List.map_cons,List.append_assoc]
    rw [he] at d
    have dd := d.removeCaps hv WordPairing.inverseLetter_involutive g a (c++w++invRev c) bs
    have ee := ih (g*v a) dd
    simpa only [value_cons,mul_assoc] using ee
def Data.removeConjugatorAt (g : G) (c w : List (A×Bool)) (pre post : List (G×List (A×Bool)))
    (d : Data v WordPairing.inverseLetter (pre++(g,c++w++invRev c)::post)) :
    Data v WordPairing.inverseLetter (pre++(g*value v c,w)::post) :=
  ((d.focus v pre g (c++w++invRev c) post).removeConjugator v hv g c w (pre++post)).unfocus v pre (g*value v c) w post
variable {I : Type} (rel : I→List (A×Bool))
def framedCores (ts : List (Term (A:=A) (I:=I))) : List (G×List (A×Bool)) :=
  ts.map (fun t=>(value v t.connector,t.core rel))
def framedWords (ts : List (Term (A:=A) (I:=I))) : List (G×List (A×Bool)) :=
  ts.map (fun t=>(1,t.word rel))
def Data.strip (ts : List (Term (A:=A) (I:=I))) (pre : List (G×List (A×Bool)))
    (d : Data v WordPairing.inverseLetter (pre++framedWords (G:=G) rel ts)) :
    Data v WordPairing.inverseLetter (pre++framedCores v rel ts) := by
  induction ts generalizing pre with
  | nil=>exact d
  | cons t ts ih=>
    change Data v WordPairing.inverseLetter
      (pre++(1,t.connector++t.core rel++invRev t.connector)::framedWords (G:=G) rel ts) at d
    have d' := d.removeConjugatorAt v hv 1 t.connector (t.core rel) pre (framedWords (G:=G) rel ts)
    rw [one_mul] at d'
    have d'' := ih (pre++[(value v t.connector,t.core rel)])
      (by simpa only [List.append_assoc,List.singleton_append] using d')
    simpa only [framedCores,List.map_cons,List.append_assoc,List.singleton_append] using d''
lemma flat_position (bs : List (G×List (A×Bool))) (h : ∀b∈bs,value v b.2=1) (hg : ∀b∈bs,b.1=1)
    (i : Occ (words bs)) :
    cursor v (words bs).flatten (coordinates (words bs) i).val=position v bs i := by
  induction bs with
  | nil=>exact Empty.elim i
  | cons b bs ih=>
    cases b with
    | mk g w=>
      have hg' := hg (g,w) (List.mem_cons_self)
      have hw := h (g,w) (List.mem_cons_self)
      change g=1 at hg'
      change value v w=1 at hw
      cases i with
      | inl i=>
        change cursor v (w++(words bs).flatten) i.val=g*cursor v w i.val
        rw [cursor_append_left v _ _ _ i.isLt.le,hg',one_mul]
      | inr i=>
        change cursor v (w++(words bs).flatten) (w.length+(coordinates (words bs) i).val)=position v bs i
        rw [cursor_append_right,hw,one_mul]
        exact ih (fun b hb=>h b (List.mem_cons_of_mem _ hb)) (fun b hb=>hg b (List.mem_cons_of_mem _ hb)) i
include hv in
lemma of_identity (bs : List (G×List (A×Bool)))
    (he : FreeGroup.mk (words bs).flatten=1) (h : ∀b∈bs,value v b.2=1) (hg : ∀b∈bs,b.1=1) :
    Nonempty (Data v WordPairing.inverseLetter bs) := by
  obtain ⟨d,hd⟩ := WordCursor.of_identity v hv he
  have hh : ∀w∈words bs,value v w=1 := by
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
    exact h b hb
  refine ⟨⟨WordBlocks.ofDisk (words bs) d,WordBlocks.liftOfDisk d hd hh,?_⟩⟩
  exact flat_position v bs h hg
include hv in
/-- Every literal free identity among the conjugated relators gives a genuine
planar matching on the signed CORE words, retaining the actual conjugating
group coordinate at EVERY occurrence. No expected relator-area identity is
used as an assumption. -/
theorem identity_framed_cores (ts : List (Term (A:=A) (I:=I)))
    (he : FreeGroup.mk (AlgebraicPictures.word rel ts)=1)
    (ht : ∀t∈ts,value v (t.word rel)=1) :
    Nonempty (Data v WordPairing.inverseLetter (framedCores v rel ts)) := by
  have hw : words (framedWords (G:=G) rel ts)=ts.map (Term.word rel) := by
    simp only [words,framedWords,List.map_map]
    rfl
  obtain ⟨d⟩ := of_identity v hv (framedWords (G:=G) rel ts) (by
    rw [hw]
    simpa only [List.flatMap_def,AlgebraicPictures.word] using he) (by
      rintro b hb
      obtain ⟨t,ht',rfl⟩ := List.mem_map.mp hb
      exact ht t ht') (by
      rintro b hb
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp hb
      rfl)
  exact ⟨d.strip v hv rel ts []⟩
end
end TorsionFreeZeroDivisors.WordFrames

end



end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SphericalPicture
open scoped Classical
open PortSubdivision PermutationCycles CycleLists
variable {V D A O : Type} [Fintype O] (Γ : PortGraph V D) (label : D→A) (inv : A→A)
namespace Data
variable {Γ label inv} (a : Data (O:=O) Γ label inv)

variable {O' : Type} [Fintype O']

variable (p q : O) (hpq : p≠q)
def band (hpair : a.partner p=q) (he : a.dart q=Γ.reverse (a.dart p)) :
    Data (O:=BandEuler.Residual p q hpq) Γ label inv where
  rotation := BandEuler.rotation a.rotation p q hpq
  partner := BandEuler.partner a.partner a.involutive p q hpq hpair
  involutive := BandEuler.partner_involutive a.partner a.involutive p q hpq hpair
  fixed_free i hi := by
    apply a.fixed_free (BandEuler.val p q hpq i)
    have hh := congrArg (BandEuler.val p q hpq) hi
    rwa [BandEuler.partner_val] at hh
  dart i := a.dart (BandEuler.val p q hpq i)
  consistent := BoundarySurgery.consistent a.rotation (Γ.origin ∘ a.dart)
    (Γ.origin ∘ Γ.reverse ∘ a.dart) p q hpq a.consistent
    (by dsimp;rw [he]) (by dsimp;rw [he,Γ.reverse_reverse])
  compatible i := by rw [BandEuler.partner_val];exact a.compatible _
  genusZero := BandEuler.genusZero_all a.rotation a.partner a.involutive p q hpq hpair a.genusZero

def tighten (hinv : Function.Involutive inv) (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
    (hsp : a.rotation p=q) (he : a.dart q=Γ.reverse (a.dart p)) :
    Data (O:=PartialMatchingSurgery.Remaining p q) Γ label inv where
  rotation := Tightening.rotation a.rotation p q hpq hsp
  partner := PartialMatchingSurgery.partner a.partner a.involutive p q hpq (a.fixed_free p) (a.fixed_free q)
  involutive := PartialMatchingSurgery.involutive a.partner a.involutive p q hpq (a.fixed_free p) (a.fixed_free q)
  fixed_free i := PartialMatchingSurgery.distinct a.partner a.involutive p q hpq (a.fixed_free p)
    (a.fixed_free q) i (a.fixed_free i)
  dart i := a.dart i
  consistent := Tightening.consistent a.rotation p q hpq hsp (Γ.origin ∘ a.dart)
    (Γ.origin ∘ Γ.reverse ∘ a.dart) a.consistent (by dsimp;rw [he,Γ.reverse_reverse])
  compatible i := PartialMatchingSurgery.compatible a.partner a.involutive p q hpq (a.fixed_free p)
    (a.fixed_free q) inv hinv (label ∘ a.dart) a.compatible (by dsimp;rw [he,hlabel]) i
  genusZero := Tightening.partial_genusZero a.rotation p q hpq hsp a.partner a.involutive
    (a.fixed_free p) (a.fixed_free q) a.genusZero

lemma unequal_backtrack (he : a.dart q=Γ.reverse (a.dart p)) : p≠q := by
  intro h
  subst q
  exact Γ.reverse_ne (a.dart p) he.symm

variable (hr : a.Reduced)
end Data
end TorsionFreeZeroDivisors.SphericalPicture

namespace TorsionFreeZeroDivisors.SampleGraph.SpherePicture
open scoped Classical
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep}
  {O : Type} [Fintype O]
  (a : SphericalPicture.Data (O:=O) (graph rep r) (label rep) Types.inverse) (hr : a.Reduced)

end TorsionFreeZeroDivisors.SampleGraph.SpherePicture

namespace TorsionFreeZeroDivisors.SphericalPicture
open scoped Classical
variable {V D A : Type} (Γ : PortSubdivision.PortGraph V D) (label : D→A) (inv : A→A)
/-- Literal finite surgery trace, including the empty terminal picture.  This
records no geometric realization or implicit essentiality hypothesis. -/
inductive ReducesToEmpty : {O : Type} → [Fintype O] → Data (O:=O) Γ label inv → Prop
  | empty {O : Type} [Fintype O] (a : Data (O:=O) Γ label inv) (h : IsEmpty O) :
      ReducesToEmpty a
  | band {O : Type} [Fintype O] (a : Data (O:=O) Γ label inv) (p q : O) (hpq : p≠q)
      (hpair : a.partner p=q) (he : a.dart q=Γ.reverse (a.dart p))
      (next : ReducesToEmpty (a.band p q hpq hpair he)) : ReducesToEmpty a
  | tighten {O : Type} [Fintype O] (a : Data (O:=O) Γ label inv) (p q : O) (hpq : p≠q)
      (hinv : Function.Involutive inv) (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
      (hsp : a.rotation p=q) (he : a.dart q=Γ.reverse (a.dart p))
      (next : ReducesToEmpty (a.tighten p q hpq hinv hlabel hsp he)) : ReducesToEmpty a
variable {Γ label inv}
namespace Data
variable {O : Type} [Fintype O] (p q : O) (hpq : p≠q)
def deletionCoordinates : BandEuler.Residual p q hpq ≃ PartialMatchingSurgery.Remaining p q where
  toFun z := ⟨BandEuler.val p q hpq z,BandEuler.val_ne_p p q hpq z,BandEuler.val_ne_q p q hpq z⟩
  invFun z := ⟨⟨z,z.property.1⟩,fun he=>z.property.2 (congrArg Subtype.val he)⟩
  left_inv _ := rfl
  right_inv _ := rfl
include hpq in
lemma remaining_two_fewer : Fintype.card (PartialMatchingSurgery.Remaining p q)+2=Fintype.card O := by
  rw [←Fintype.card_congr (deletionCoordinates p q hpq)]
  exact BandEuler.two_fewer p q hpq
end Data
/-- Strong induction on the actual number of boundary occurrences: each
nonterminal step deletes two occurrences. -/
theorem reduces_of_no_reduced (hinv : Function.Involutive inv)
    (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
    (hex : ∀{O : Type}[Fintype O][Nonempty O](a : Data (O:=O) Γ label inv),¬a.Reduced)
    {O : Type} [Fintype O] (a : Data (O:=O) Γ label inv) : ReducesToEmpty Γ label inv a := by
  generalize he : Fintype.card O=n
  induction n using Nat.strong_induction_on generalizing O with
  | h n ih =>
    by_cases hzero : IsEmpty O
    · exact .empty a hzero
    let : Nonempty O := not_isEmpty_iff.mp hzero
    have hn := hex a
    simp only [Data.Reduced,not_and_or,not_forall,Classical.not_not] at hn
    rcases hn with ⟨p,hp⟩ | ⟨p,hp⟩
    · let q := a.partner p
      have hpq : p≠q := (a.fixed_free p).symm
      refine .band a p q hpq rfl hp (ih (Fintype.card (BandEuler.Residual p q hpq)) ?_ _ rfl)
      have hc := BandEuler.two_fewer p q hpq
      omega
    · let q := a.rotation p
      have hpq : p≠q := a.unequal_backtrack p q hp
      refine .tighten a p q hpq hinv hlabel rfl hp
        (ih (Fintype.card (PartialMatchingSurgery.Remaining p q)) ?_ _ rfl)
      have hc := Data.remaining_two_fewer p q hpq
      omega
end TorsionFreeZeroDivisors.SphericalPicture
namespace TorsionFreeZeroDivisors.SampleGraph.SpherePicture
open scoped Classical
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep}
end TorsionFreeZeroDivisors.SampleGraph.SpherePicture

namespace TorsionFreeZeroDivisors.ConePicture
open PortSubdivision GraphPresentation SphericalPicture
open scoped Classical
variable {V D A : Type} (Γ : PortGraph V D) (R : Routes Γ)
abbrev Radial := {v : V // v≠R.base v}
abbrev Dart := D ⊕ (Radial Γ R × Bool)
def reverse : Dart Γ R→Dart Γ R
  | .inl d => .inl (Γ.reverse d)
  | .inr (v,b) => .inr (v,!b)
def origin : Dart Γ R→V
  | .inl d => Γ.origin d
  | .inr (v,b) => if b then R.base v else v
/-- The one-skeleton in an abstract graph cone after its root radial edge
is collapsed. Physical graph edges and all other radial edges are retained. -/
def graph : PortGraph V (Dart Γ R) where
  origin := origin Γ R
  reverse := reverse Γ R
  reverse_reverse d := by
    rcases d with d|⟨v,b⟩
    · exact congrArg Sum.inl (Γ.reverse_reverse d)
    · cases b <;> rfl
  reverse_ne d := by
    rcases d with d|⟨v,b⟩
    · intro he; exact Γ.reverse_ne d (Sum.inl.inj he)
    · cases b <;> simp [reverse]
variable (label : D→A) (inv : A→A)
def labels : Dart Γ R→ A ⊕ (Radial Γ R × Bool)
  | .inl d => .inl (label d)
  | .inr p => .inr p
def inverse : A ⊕ (Radial Γ R × Bool) → A ⊕ (Radial Γ R × Bool)
  | .inl a => .inl (inv a)
  | .inr (v,b) => .inr (v,!b)
lemma label_reverse (hl : ∀d,label (Γ.reverse d)=inv (label d)) (d : Dart Γ R) :
    labels Γ R label ((graph Γ R).reverse d)=inverse Γ R inv (labels Γ R label d) := by
  rcases d with d|⟨v,b⟩
  · exact congrArg Sum.inl (hl d)
  · rfl
variable {Γ R label inv} {O : Type} [Fintype O]
  (a : Data (O:=O) (graph Γ R) (labels Γ R label) (inverse Γ R inv))
lemma reduced_old (hr : a.Reduced) (i : O) : ∃d,a.dart i=Sum.inl d := by
  cases he : a.dart i with
  | inl d => exact ⟨d,rfl⟩
  | inr p =>
    exfalso
    have hc := a.compatible i
    rw [he] at hc
    have hp : a.dart (a.partner i)=Sum.inr (p.1,!p.2) := by
      cases hq : a.dart (a.partner i) with
      | inl d => simp [hq,labels,inverse] at hc
      | inr q =>
        have heq : q=(p.1,!p.2) := Sum.inr.inj (by simpa only [hq,labels,inverse] using hc)
        rw [heq]
    exact hr.1 i (by rw [he,hp];rfl)
/-- Removing the ghost radial alphabet from a reduced picture changes
NEITHER its permutation genus nor its boundary representatives. -/
def oldData (hr : a.Reduced) : Data (O:=O) Γ label inv where
  rotation := a.rotation
  partner := a.partner
  involutive := a.involutive
  fixed_free := a.fixed_free
  dart i := (reduced_old a hr i).choose
  consistent i := by
    have h := a.consistent i
    rw [(reduced_old a hr i).choose_spec,(reduced_old a hr (a.rotation i)).choose_spec] at h
    exact h
  compatible i := by
    have h := a.compatible i
    rw [(reduced_old a hr i).choose_spec,(reduced_old a hr (a.partner i)).choose_spec] at h
    exact Sum.inl.inj h
  genusZero := a.genusZero
lemma oldData_reduced (hr : a.Reduced) : (oldData a hr).Reduced := by
  constructor
  · intro i hi
    apply hr.1 i
    rw [(reduced_old a hr i).choose_spec,(reduced_old a hr (a.partner i)).choose_spec]
    exact congrArg Sum.inl hi
  · intro i hi
    apply hr.2 i
    rw [(reduced_old a hr i).choose_spec,(reduced_old a hr (a.rotation i)).choose_spec]
    exact congrArg Sum.inl hi
variable (hi : Function.Involutive inv) (hl : ∀d,label (Γ.reverse d)=inv (label d))
end TorsionFreeZeroDivisors.ConePicture

end

end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.PictureChains
open scoped Classical BigOperators
open SphericalPicture PortSubdivision
noncomputable section
variable {V D A G M : Type} [_root_.Group G] [AddCommGroup M]
  (Γ : PortGraph V D) (label : D→A) (inv : A→A) (eval : A→G)
  (heval : ∀a,eval (inv a)=(eval a)⁻¹)
  (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
variable {O : Type} [Fintype O] (a : Data (O:=O) Γ label inv)
/-- The actual group-coordinate lift of every boundary occurrence. Rotation
and paired sides share the prescribed endpoint in the Cayley one-skeleton. -/
structure Lift where
  position : O→G
  next : ∀i,position (a.rotation i)=position i*eval (label (a.dart i))
  pair : ∀i,position (a.partner i)=position i*eval (label (a.dart i))
variable {Γ label inv eval} (l : Lift Γ label inv eval a)
include heval hlabel in
lemma reverse_value (d : D) : eval (label (Γ.reverse d))=(eval (label d))⁻¹ := by
  rw [hlabel,heval]
include heval hlabel in
lemma inverse_segment {p q : O} (hpos : l.position q=l.position p*eval (label (a.dart p)))
    (he : a.dart q=Γ.reverse (a.dart p)) :
    l.position q*eval (label (a.dart q))=l.position p := by
  rw [hpos,he,reverse_value heval hlabel,mul_inv_cancel_right]
variable (p q : O) (hpq : p≠q)
def band (hpair : a.partner p=q) (he : a.dart q=Γ.reverse (a.dart p)) :
    Lift Γ label inv eval (a.band p q hpq hpair he) where
  position i := l.position (BandEuler.val p q hpq i)
  next i := (BoundarySurgery.consistent a.rotation l.position
    (fun j=>l.position j*eval (label (a.dart j))) p q hpq
    (fun i=>(l.next i).symm)
    (by rw [←l.pair,hpair])
    (inverse_segment heval hlabel a l (by rw [←hpair,l.pair]) he) i).symm
  pair i := by
    change l.position (BandEuler.val p q hpq (BandEuler.partner a.partner a.involutive p q hpq hpair i))=_
    rw [BandEuler.partner_val]
    exact l.pair _
def tighten (hinv : Function.Involutive inv) (hsp : a.rotation p=q)
    (he : a.dart q=Γ.reverse (a.dart p)) :
    Lift Γ label inv eval (a.tighten p q hpq hinv hlabel hsp he) where
  position i := l.position i
  next i := (Tightening.consistent a.rotation p q hpq hsp l.position
    (fun j=>l.position j*eval (label (a.dart j))) (fun i=>(l.next i).symm)
    (inverse_segment heval hlabel a l (by rw [←hsp,l.next]) he) i).symm
  pair i := by
    change l.position (PartialMatchingSurgery.splice a.partner p q i)=_
    by_cases h1 : a.partner i=p
    · rw [PartialMatchingSurgery.splice,if_pos h1,l.pair]
      exact (inverse_segment heval hlabel a l (by rw [←hsp,l.next]) he).trans
        ((congrArg l.position h1).symm.trans (l.pair i))
    · by_cases h2 : a.partner i=q
      · rw [PartialMatchingSurgery.splice,if_neg h1,if_pos h2,l.pair]
        exact (l.next p).symm.trans ((congrArg l.position hsp).trans
          ((congrArg l.position h2).symm.trans (l.pair i)))
      · rw [PartialMatchingSurgery.splice,if_neg h1,if_neg h2]
        exact l.pair i

variable (c : G→D→M)
  (hc : ∀g d,c (g*eval (label d)) (Γ.reverse d)=-c g d)
def chain : M := ∑i,c (l.position i) (a.dart i)
include hc in
lemma cancel_pair {p q : O} (hpos : l.position q=l.position p*eval (label (a.dart p)))
    (he : a.dart q=Γ.reverse (a.dart p)) :
    c (l.position p) (a.dart p)+c (l.position q) (a.dart q)=0 := by
  rw [hpos,he,hc,add_neg_cancel]

lemma sum_remaining {B : Type*} [AddCommGroup B] {O : Type*} [Fintype O]
    (p q : O) (hpq : p≠q) (f : O→B) (hf : f p+f q=0) :
    (∑i : PartialMatchingSurgery.Remaining p q,f i)=∑i,f i := by
  classical
  have hs : (∑i∈Finset.univ.erase p |>.erase q,f i)+f q+f p=∑i,f i := by
    rw [Finset.sum_erase_add _ _ (by simp [hpq.symm]),Finset.sum_erase_add _ _ (Finset.mem_univ _)]
  have hsum : (∑i : PartialMatchingSurgery.Remaining p q,f i)=
      ∑i∈Finset.univ.erase p |>.erase q,f i := by
    apply Finset.sum_bij (fun i _=>i.1)
    · intro i _;simp only [Finset.mem_erase,Finset.mem_univ,and_true];exact ⟨i.2.2,i.2.1⟩
    · intro i _ j _ hij;exact Subtype.ext hij
    · intro j hj
      simp only [Finset.mem_erase,Finset.mem_univ,and_true] at hj
      exact ⟨⟨j,hj.2,hj.1⟩,Finset.mem_univ _,rfl⟩
    · intro i _;rfl
  rw [hsum]
  have hh : f q+f p=0 := by rwa [add_comm] at hf
  simpa only [add_assoc,hh,add_zero] using hs

include hc in
lemma band_chain (hpair : a.partner p=q) (he : a.dart q=Γ.reverse (a.dart p)) :
    chain (a.band p q hpq hpair he) (band heval hlabel a l p q hpq hpair he) c=chain a l c := by
  change (∑i : BandEuler.Residual p q hpq,c (l.position (BandEuler.val p q hpq i)) (a.dart (BandEuler.val p q hpq i)))=_
  exact ((Data.deletionCoordinates p q hpq).sum_comp
    (fun i : PartialMatchingSurgery.Remaining p q=>c (l.position i) (a.dart i))).trans
    (sum_remaining p q hpq (fun i=>c (l.position i) (a.dart i))
      (cancel_pair a l c hc (by rw [←hpair,l.pair]) he))
include hc in
lemma tighten_chain (hinv : Function.Involutive inv) (hsp : a.rotation p=q)
    (he : a.dart q=Γ.reverse (a.dart p)) :
    chain (a.tighten p q hpq hinv hlabel hsp he) (tighten heval hlabel a l p q hpq hinv hsp he) c=chain a l c := by
  change (∑i : PartialMatchingSurgery.Remaining p q,c (l.position i) (a.dart i))=_
  exact sum_remaining p q hpq (fun i=>c (l.position i) (a.dart i))
    (cancel_pair a l c hc (by rw [←hsp,l.next]) he)

include heval hlabel hc in
/-- Every actual lifted genus-zero spherical boundary picture which reduces as
proved by the sharp arrangement exclusion has ZERO integral cell-chain charge.
Only an antisymmetric physical cone-edge contribution is needed. -/
theorem chain_eq_zero (h : ReducesToEmpty Γ label inv a) : chain a l c=0 := by
  induction h with
  | empty a h =>
    let := h
    simp only [chain, Finset.univ_eq_empty, Finset.sum_empty]
  | band a p q hpq hpair he next ih =>
    rw [←band_chain heval hlabel a l p q hpq c hc hpair he]
    exact ih (band heval hlabel a l p q hpq hpair he)
  | tighten a p q hpq hinv hl hsp he next ih =>
    rw [←tighten_chain heval hl a l p q hpq c hc hinv hsp he]
    exact ih (tighten heval hl a l p q hpq hinv hsp he)
end
end TorsionFreeZeroDivisors.PictureChains

end


end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.WordFrames
open scoped Classical BigOperators
open WordBlocks WordCursor PortSubdivision
noncomputable section
variable {V D A G : Type} [_root_.Group G] (Γ : PortGraph V D) (lab : D→A) (v : A→G) (inv : A→A)
def mapLabels (bs : List (G×List D)) : List (G×List A) := bs.map (fun b=>(b.1,b.2.map lab))
def labelCoordinates : (bs : List (G×List D))→Occ (words bs)≃Occ (words (mapLabels lab bs))
  | []=>Equiv.refl _
  | b::bs=>Equiv.sumCongr (finCongr (List.length_map (f:=lab) (as:=b.2)).symm) (labelCoordinates bs)
omit [_root_.Group G] in
lemma labelCoordinates_letter (bs : List (G×List D)) (i : Occ (words bs)) :
    letter (words (mapLabels lab bs)) (labelCoordinates lab bs i)=lab (letter (words bs) i) := by
  induction bs with
  | nil=>exact Empty.elim i
  | cons b bs ih=>
    cases i with
    | inl i=>exact List.getElem_map _
    | inr i=>exact ih i
omit [_root_.Group G] in
lemma labelCoordinates_rotation (bs : List (G×List D)) (i : Occ (words bs)) :
    labelCoordinates lab bs (BlockBoundary.rotation (lengths (words bs)) i)=
      BlockBoundary.rotation (lengths (words (mapLabels lab bs))) (labelCoordinates lab bs i) := by
  induction bs with
  | nil=>exact Empty.elim i
  | cons b bs ih=>
    cases i with
    | inl i=>exact congrArg Sum.inl (rotate_cast (List.length_map (f:=lab) (as:=b.2)).symm i)
    | inr i=>exact congrArg Sum.inr (ih i)
lemma cursor_map (w : List D) (n : ℕ) : cursor v (w.map lab) n=cursor (v∘lab) w n := by
  simp only [cursor,value,←List.map_take,List.map_map]
lemma labelCoordinates_position (bs : List (G×List D)) (i : Occ (words bs)) :
    position v (mapLabels lab bs) (labelCoordinates lab bs i)=position (v∘lab) bs i := by
  induction bs with
  | nil=>exact Empty.elim i
  | cons b bs ih=>
    cases b with
    | mk g w=>
      cases i with
      | inl i=>exact congrArg (g*·) (cursor_map lab v w i.val)
      | inr i=>exact ih i
variable {v inv lab} {bs : List (G×List D)}
  (d : Data v inv (mapLabels lab bs)) (hc : AllClosed Γ (words bs))
def spherical : SphericalPicture.Data (O:=Occ (words bs)) Γ lab inv where
  rotation := BlockBoundary.rotation (lengths (words bs))
  partner := (labelCoordinates lab bs).symm.permCongr d.matching.partner
  involutive := PermutationTransport.involutive _ _ d.matching.involutive
  fixed_free := PermutationTransport.fixed_free _ _ d.matching.fixed_free
  dart := letter (words bs)
  consistent := closed_consistent Γ (words bs) hc
  compatible i := by
    rw [←labelCoordinates_letter lab bs,←labelCoordinates_letter lab bs]
    simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
    exact d.matching.compatible (labelCoordinates lab bs i)
  genusZero := by
    have hh := MapConjugation.genusZero (labelCoordinates lab bs).symm _ _ d.matching.genusZero
    have he : (labelCoordinates lab bs).symm.permCongr
        (BlockBoundary.rotation (lengths (words (mapLabels lab bs))))=BlockBoundary.rotation (lengths (words bs)) := by
      apply Equiv.ext
      intro i
      apply (labelCoordinates lab bs).injective
      simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
      exact (labelCoordinates_rotation lab bs i).symm
    rwa [he] at hh
def sphericalLift : PictureChains.Lift Γ lab inv v (spherical Γ d hc) where
  position i := d.lifted.position (labelCoordinates lab bs i)
  next i := by
    change d.lifted.position (labelCoordinates lab bs (BlockBoundary.rotation (lengths (words bs)) i))=_
    rw [labelCoordinates_rotation,d.lifted.next,labelCoordinates_letter]
    rfl
  pair i := by
    change d.lifted.position (labelCoordinates lab bs (((labelCoordinates lab bs).symm.permCongr d.matching.partner) i))=_
    simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
    rw [d.lifted.pair,labelCoordinates_letter]
    rfl
lemma sphericalLift_position (i : Occ (words bs)) :
    (sphericalLift Γ d hc).position i=position (v∘lab) bs i := by
  change d.lifted.position (labelCoordinates lab bs i)=_
  rw [d.framed,labelCoordinates_position]
variable {M : Type} [AddCommGroup M]
  (hv : ∀a,v (inv a)=(v a)⁻¹) (hl : ∀b,lab (Γ.reverse b)=inv (lab b))
  (c : G→D→M) (hcharge : ∀g b,c (g*v (lab b)) (Γ.reverse b)=-c g b)
include hv hl hcharge in
/-- Relator frames retain their ACTUAL conjugating coordinates when the
matching is interpreted as a spherical graph picture. -/
theorem charge_zero (hred : SphericalPicture.ReducesToEmpty Γ lab inv (spherical Γ d hc)) :
    (∑i : Occ (words bs),c (position (v∘lab) bs i) (letter (words bs) i))=0 := by
  have hh := PictureChains.chain_eq_zero hv hl (spherical Γ d hc) (sphericalLift Γ d hc) c hcharge hred
  simpa only [PictureChains.chain,sphericalLift_position,spherical] using hh
end
end TorsionFreeZeroDivisors.WordFrames

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.PathCharges
open scoped Classical BigOperators
open WordCursor WordFrames WordBlocks
noncomputable section
variable {D G M : Type} [_root_.Group G] [AddCommGroup M] (v : D→G) (c : G→D→M)
def charge (g : G) : List D→M
  | []=>0
  | d::w=>c g d+charge (g*v d) w
@[simp] lemma charge_nil (g : G) : charge v c g []=0 := rfl
@[simp] lemma charge_cons (g : G) (d : D) (w : List D) :
    charge v c g (d::w)=c g d+charge v c (g*v d) w := rfl
lemma charge_append (g : G) (w u : List D) :
    charge v c g (w++u)=charge v c g w+charge v c (g*value v w) u := by
  induction w generalizing g with
  | nil=>simp
  | cons d w ih=>
    rw [List.cons_append,charge_cons,ih,charge_cons,value_cons,mul_assoc,add_assoc]
lemma charge_sum (g : G) (w : List D) :
    (∑i : Fin w.length,c (g*cursor v w i.val) (w.get i))=charge v c g w := by
  induction w generalizing g with
  | nil=>simp
  | cons d w ih=>
    change (∑i : Fin (w.length+1),c (g*cursor v (d::w) i.val) ((d::w).get i))=_
    rw [Fin.sum_univ_succ,charge_cons]
    change c (g*1) d+(∑i : Fin w.length,c (g*(v d*cursor v w i.val)) (w.get i))=_
    simp only [mul_one,←mul_assoc]
    rw [ih]
lemma frames_sum (bs : List (G×List D)) :
    (∑i : Occ (words bs),c (WordFrames.position v bs i) (letter (words bs) i))=
    (bs.map (fun b=>charge v c b.1 b.2)).sum := by
  induction bs with
  | nil=>
    change (∑i : Empty,c (WordFrames.position v [] i) (letter (words []) i))=0
    simp only [Finset.univ_eq_empty,Finset.sum_empty]
  | cons b bs ih=>
    change (∑i : Fin b.2.length⊕Occ (words bs),c (WordFrames.position v (b::bs) i) (letter (words (b::bs)) i))=_
    rw [Fintype.sum_sum_type]
    cases b with
    | mk g w=>
      change (∑i : Fin w.length,c (g*cursor v w i.val) (w.get i))+
        (∑i : Occ (words bs),c (WordFrames.position v bs i) (letter (words bs) i))=_
      rw [charge_sum,ih]
      rfl
variable (rev : D→D) (hv : ∀d,v (rev d)=(v d)⁻¹)
  (hc : ∀g d,c (g*v d) (rev d)=-c g d)
include hv in
lemma value_reverse (w : List D) : value v (w.reverse.map rev)=(value v w)⁻¹ := by
  induction w with
  | nil=>simp
  | cons d w ih=>simp only [List.reverse_cons,List.map_append,List.map_singleton,
      value_append,value_cons,value_nil,mul_one,ih,hv,mul_inv_rev]
include hv hc in
lemma charge_reverse (g : G) (w : List D) :
    charge v c (g*value v w) (w.reverse.map rev)=-charge v c g w := by
  induction w generalizing g with
  | nil=>simp
  | cons d w ih=>
    rw [List.reverse_cons,List.map_append,List.map_singleton,value_cons,←mul_assoc,charge_append,ih]
    rw [value_reverse v rev hv]
    simp only [charge_cons,charge_nil,add_zero,mul_inv_cancel_right]
    rw [hc,neg_add]
    exact add_comm _ _
end
end TorsionFreeZeroDivisors.PathCharges

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.FramedLoopIdentities
open scoped Classical BigOperators
open PortSubdivision GraphPresentation AlgebraicPictures InitialPicture WordFrames WordCursor
noncomputable section
variable {V D A I G M : Type} [_root_.Group G] [AddCommGroup M]
  (Γ : PortGraph V D) (label : D→A×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
  (rel : I→Loop Γ) (v : A×Bool→G)
  (hv : ∀a,v (WordPairing.inverseLetter a)=(v a)⁻¹)
  (c : G→D→M) (hc : ∀g d,c (g*v (label d)) (Γ.reverse d)=-c g d)
  (ts : List (Term (A:=A) (I:=I)))
def frames : List (G×List D) := ts.map (fun t=>(value v t.connector,(signedLoop Γ rel t).2.darts))
include hl in
lemma frames_labels : mapLabels label (frames Γ rel v ts)=framedCores v (relWords Γ label rel) ts := by
  simp only [mapLabels,frames,framedCores,List.map_map]
  apply List.map_congr_left
  intro t _
  apply Prod.ext
  · rfl
  · exact signedLoop_letters Γ label hl rel t
lemma frames_closed : WordBlocks.AllClosed Γ (words (frames Γ rel v ts)) := by
  intro w hw
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hb
  exact ⟨(signedLoop Γ rel t).1,(signedLoop Γ rel t).2,rfl⟩
def area (t : Term (A:=A) (I:=I)) : M :=
  PathCharges.charge (v∘label) c (value v t.connector) (signedLoop Γ rel t).2.darts
include hl hv hc in
/-- A free identity among conjugated closed relators has exactly zero lifted
edge area whenever sharp arrangement exclusion reduces all its actual spherical
pictures. The frames are not erased or existentially replaced. -/
theorem identity_area_zero
    (he : FreeGroup.mk (AlgebraicPictures.word (relWords Γ label rel) ts)=1)
    (ht : ∀t∈ts,value v (t.word (relWords Γ label rel))=1)
    (hred : ∀{O : Type}[Fintype O](a : SphericalPicture.Data (O:=O) Γ label WordPairing.inverseLetter),
      SphericalPicture.ReducesToEmpty Γ label WordPairing.inverseLetter a) :
    (ts.map (area Γ label rel v c)).sum=0 := by
  obtain ⟨d⟩ := identity_framed_cores v hv (relWords Γ label rel) ts he ht
  rw [←frames_labels Γ label hl rel v ts] at d
  have hh := WordFrames.charge_zero Γ d (frames_closed Γ rel v ts) hv hl c hc (hred _)
  rw [PathCharges.frames_sum] at hh
  simp only [frames,List.map_map] at hh
  exact hh
end
end TorsionFreeZeroDivisors.FramedLoopIdentities

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.GraphConePresentation
open PortSubdivision GraphPresentation
open scoped Classical
noncomputable section
variable {V D S : Type} (Γ : PortGraph V D)
/-- Physical unoriented edges, retaining loops and parallel edges. -/
def edgeSetoid : Setoid D where
  r d e := d=e ∨ d=Γ.reverse e
  iseqv := ⟨fun _=>Or.inl rfl, by
    intro d e h
    rcases h with rfl|h
    · exact Or.inl rfl
    · exact Or.inr (by rw [h,Γ.reverse_reverse_apply]), by
    intro d e f h k
    rcases h with rfl|h
    · exact k
    · rcases k with rfl|k
      · exact Or.inr h
      · exact Or.inl (by rw [h,k,Γ.reverse_reverse_apply])⟩
abbrev Edge := Quotient (edgeSetoid Γ)
def edge (d : D) : Edge Γ := Quotient.mk _ d
def representative (e : Edge Γ) : D := e.out
lemma representative_cases (d : D) :
    d=representative Γ (edge Γ d) ∨ d=Γ.reverse (representative Γ (edge Γ d)) :=
  Quotient.exact (Quotient.out_eq (edge Γ d)).symm

variable (letters : D→FreeGroup S) (R : Routes Γ)
/-- Radial edges except for the one edge collapsed at the root of each component. -/
abbrev Generator := S ⊕ {v : V // v≠R.base v}
def old : FreeGroup S →* FreeGroup (Generator (S:=S) Γ R) := FreeGroup.map Sum.inl
def radial (v : V) : FreeGroup (Generator (S:=S) Γ R) :=
  if h : v=R.base v then 1 else FreeGroup.of (Sum.inr ⟨v,h⟩)
def triangle (d : D) : FreeGroup (Generator (S:=S) Γ R) :=
  radial Γ R (Γ.origin d)*old Γ R (letters d)*(radial Γ R (Γ.origin (Γ.reverse d)))⁻¹
/-- There is one two-cell per physical edge, NOT one per directed dart. -/
def attachment (e : Edge Γ) : FreeGroup (Generator (S:=S) Γ R) := triangle Γ letters R (representative Γ e)
def relations : Set (FreeGroup (Generator (S:=S) Γ R)) := Set.range (attachment Γ letters R)
abbrev Group := PresentedGroup (relations Γ letters R)
def radialValue (v : V) : Group Γ letters R := PresentedGroup.mk _ (radial Γ R v)
def oldMap : FreeGroup S →* Group Γ letters R := (PresentedGroup.mk _).comp (old Γ R)
lemma triangle_reverse (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹) (d : D) :
    triangle Γ letters R (Γ.reverse d)=(triangle Γ letters R d)⁻¹ := by
  simp only [triangle,Γ.reverse_reverse_apply,hl,map_inv,mul_inv_rev,inv_inv]
  group
lemma triangle_trivial (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹) (d : D) :
    PresentedGroup.mk (relations Γ letters R) (triangle Γ letters R d)=1 := by
  have h := PresentedGroup.one_of_mem (show attachment Γ letters R (edge Γ d)∈relations Γ letters R from ⟨_,rfl⟩)
  change PresentedGroup.mk _ (triangle Γ letters R (representative Γ (edge Γ d)))=1 at h
  rcases representative_cases Γ d with hd|hd
  · rw [hd]; exact h
  · rw [hd,triangle_reverse Γ letters R hl,map_inv,h,inv_one]
lemma edge_value (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹) (d : D) :
    radialValue Γ letters R (Γ.origin (Γ.reverse d))=
      radialValue Γ letters R (Γ.origin d)*oldMap Γ letters R (letters d) := by
  have h := triangle_trivial Γ letters R hl d
  simp only [triangle,map_mul,map_inv] at h
  exact (mul_inv_eq_one.mp h).symm
lemma path_value (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹)
    {a b : V} (p : Path Γ a b) :
    p.eval (fun d=>oldMap Γ letters R (letters d))=
      (radialValue Γ letters R a)⁻¹*radialValue Γ letters R b := by
  induction p with
  | nil v => simp
  | cons d p ih =>
    rw [Path.eval_cons,ih,edge_value Γ letters R hl]
    group
lemma radial_base (hbase : ∀v,R.base (R.base v)=R.base v) (v : V) :
    radial (S:=S) Γ R (R.base v)=1 := by simp [radial,hbase]
lemma old_word (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹)
    (hbase : ∀v,R.base (R.base v)=R.base v) (v : V) :
    oldMap Γ letters R (word Γ letters R v)=radialValue Γ letters R v := by
  rw [word,←Path.eval_map,path_value Γ letters R hl]
  simp [radialValue,radial_base Γ R hbase]

/-- The original graph-loop group maps to the nonredundant cone group. -/
def fromGraph (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹)
    (hbase : ∀v,R.base (R.base v)=R.base v) :
    GraphPresentation.Group Γ letters R →* Group Γ letters R :=
  PresentedGroup.toGroup (f:=fun s=>oldMap Γ letters R (FreeGroup.of s)) (by
    have hf : FreeGroup.lift (fun s=>oldMap Γ letters R (FreeGroup.of s))=oldMap Γ letters R := by
      ext s; simp
    rintro w ⟨d,rfl⟩
    rw [hf,relator,map_mul,map_mul,map_inv,old_word Γ letters R hl hbase,
      old_word Γ letters R hl hbase,←edge_value Γ letters R hl]
    simp)

lemma graph_value_base (hbase : ∀v,R.base (R.base v)=R.base v) (v : V) :
    value Γ letters R (R.base v)=1 := by
  have h := closed_value Γ letters R (R.base v)
    ((R.path (R.base v)).cast (hbase v) rfl)
  rw [Path.eval_cast] at h
  change (R.path (R.base v)).eval (fun d=>PresentedGroup.mk _ (letters d))=1 at h
  rw [Path.eval_map] at h
  exact h

def toGraphGenerator : Generator (S:=S) Γ R → GraphPresentation.Group Γ letters R
  | .inl s => PresentedGroup.of s
  | .inr v => value Γ letters R v
lemma lift_old : (FreeGroup.lift (toGraphGenerator Γ letters R)).comp (old Γ R)=
    PresentedGroup.mk (GraphPresentation.relations Γ letters R) := by
  ext s
  simp [old,toGraphGenerator,PresentedGroup.of]
lemma lift_radial (hbase : ∀v,R.base (R.base v)=R.base v) (v : V) :
    FreeGroup.lift (toGraphGenerator Γ letters R) (radial Γ R v)=value Γ letters R v := by
  by_cases h : v=R.base v
  · simp only [radial,dif_pos h,map_one]
    rw [h,graph_value_base Γ letters R hbase]
  · simp [radial,h,toGraphGenerator]
/-- The precise reverse Tietze map, keeping each new radial generator's value. -/
def toGraph (hbase : ∀v,R.base (R.base v)=R.base v) :
    Group Γ letters R →* GraphPresentation.Group Γ letters R :=
  PresentedGroup.toGroup (f:=toGraphGenerator Γ letters R) (by
    rintro _ ⟨e,rfl⟩
    simp only [attachment,triangle,map_mul,map_inv,lift_radial Γ letters R hbase]
    rw [←MonoidHom.comp_apply,lift_old]
    change value Γ letters R _*letter Γ letters R _*(value Γ letters R _)⁻¹=1
    rw [←GraphPresentation.edge]
    simp)
lemma fromGraph_mk (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹)
    (hbase : ∀v,R.base (R.base v)=R.base v) (w : FreeGroup S) :
    fromGraph Γ letters R hl hbase (PresentedGroup.mk _ w)=oldMap Γ letters R w := by
  have h : (fromGraph Γ letters R hl hbase).comp (PresentedGroup.mk _)=oldMap Γ letters R := by
    ext s
    change fromGraph Γ letters R hl hbase (PresentedGroup.of s)=_
    simp [fromGraph]
  exact DFunLike.congr_fun h w
lemma fromGraph_value (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹)
    (hbase : ∀v,R.base (R.base v)=R.base v) (v : V) :
    fromGraph Γ letters R hl hbase (value Γ letters R v)=radialValue Γ letters R v := by
  rw [value,fromGraph_mk,old_word Γ letters R hl hbase]

def equivalence (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹)
    (hbase : ∀v,R.base (R.base v)=R.base v) :
    GraphPresentation.Group Γ letters R ≃* Group Γ letters R :=
  MonoidHom.toMulEquiv (fromGraph Γ letters R hl hbase) (toGraph Γ letters R hbase) (by
    apply PresentedGroup.ext
    intro s
    change toGraph Γ letters R hbase (oldMap Γ letters R (FreeGroup.of s))=PresentedGroup.of s
    change toGraph Γ letters R hbase (PresentedGroup.of (Sum.inl s))=_
    simp [toGraph,toGraphGenerator]) (by
    apply PresentedGroup.ext
    intro s
    cases s with
    | inl s =>
      simp only [MonoidHom.comp_apply,MonoidHom.id_apply,toGraph,PresentedGroup.toGroup.of,toGraphGenerator]
      change fromGraph Γ letters R hl hbase (PresentedGroup.of s)=PresentedGroup.of (Sum.inl s)
      rw [PresentedGroup.of,fromGraph_mk]
      rfl
    | inr v =>
      simp only [MonoidHom.comp_apply,MonoidHom.id_apply,toGraph,PresentedGroup.toGroup.of,toGraphGenerator]
      change fromGraph Γ letters R hl hbase (value Γ letters R v)=PresentedGroup.of (Sum.inr v)
      rw [fromGraph_value]
      simp [radialValue,radial,v.property,PresentedGroup.of])

lemma canonical_base (v : V) : (routes Γ).base ((routes Γ).base v)=(routes Γ).base v := by
  exact congrArg (fun q : Quot (ShortClosure.simpleGraph Γ).Reachable=>q.out)
    ((ShortClosure.simpleGraph Γ).connectedComponentMk v).out_eq

instance [Finite S] [Finite V] [Finite D] : _root_.Group.IsFinitelyPresented (Group Γ letters R) := by
  have : Finite (relations Γ letters R) := Set.finite_range (attachment Γ letters R) |>.to_subtype
  infer_instance
end
end TorsionFreeZeroDivisors.GraphConePresentation

end


end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ConePicture
open PortSubdivision GraphPresentation
open scoped Classical
variable {V D S : Type} (Γ : PortGraph V D) (R : Routes Γ)
  (letters : D→FreeGroup S)
def wordLabel : Dart Γ R→FreeGroup (GraphConePresentation.Generator (S:=S) Γ R)
  | .inl d => GraphConePresentation.old Γ R (letters d)
  | .inr (v,b) => if b then FreeGroup.of (Sum.inr v) else (FreeGroup.of (Sum.inr v))⁻¹
lemma wordLabel_reverse (hl : ∀d,letters (Γ.reverse d)=(letters d)⁻¹) (d : Dart Γ R) :
    wordLabel Γ R letters ((graph Γ R).reverse d)=(wordLabel Γ R letters d)⁻¹ := by
  rcases d with d|⟨v,b⟩
  · exact (congrArg (GraphConePresentation.old Γ R) (hl d)).trans (map_inv _ _)
  · cases b <;> simp [wordLabel,graph,reverse]
def rootPath (v : V) : Path (graph Γ R) (R.base v) v :=
  if h : v=R.base v then (Path.nil (Γ:=graph Γ R) (R.base v)).cast rfl h.symm
  else (Path.single (Γ:=graph Γ R) (Sum.inr (⟨v,h⟩,true))).cast
    (show (graph Γ R).origin (Sum.inr (⟨v,h⟩,true))=R.base v from rfl)
    (show (graph Γ R).origin ((graph Γ R).reverse (Sum.inr (⟨v,h⟩,true)))=v from rfl)
lemma rootPath_eval (v : V) :
    (rootPath Γ R v).eval (wordLabel Γ R letters)=GraphConePresentation.radial Γ R v := by
  by_cases hv : v=R.base v
  · simp only [rootPath,dif_pos hv,Path.eval_cast,Path.eval_nil,GraphConePresentation.radial]
  · simp only [rootPath,dif_neg hv,Path.eval_cast,Path.eval_single,wordLabel,ite_true,
      GraphConePresentation.radial]
/-- The actual triangular closed boundary, with a root radial omitted exactly
when it is collapsed in the finite CW model. No directed-edge duplication. -/
def trianglePath (d : D) : Path (graph Γ R) (R.base (Γ.origin d)) (R.base (Γ.origin d)) :=
  ((rootPath Γ R (Γ.origin d)).append
    (((Path.single (Γ:=graph Γ R) (Sum.inl d)).cast
      (show (graph Γ R).origin (Sum.inl d)=Γ.origin d from rfl)
      (show (graph Γ R).origin ((graph Γ R).reverse (Sum.inl d))=Γ.origin (Γ.reverse d) from rfl)).append ((rootPath Γ R (Γ.origin (Γ.reverse d))).reverse))).cast
      rfl (R.same d).symm
lemma trianglePath_eval (hl : ∀d,letters (Γ.reverse d)=(letters d)⁻¹) (d : D) :
    (trianglePath Γ R d).eval (wordLabel Γ R letters)=GraphConePresentation.triangle Γ letters R d := by
  rw [trianglePath,Path.eval_cast,Path.eval_append (Γ:=graph Γ R),
    Path.eval_append (Γ:=graph Γ R),Path.eval_cast,Path.eval_single (Γ:=graph Γ R),
    Path.eval_reverse _ (wordLabel_reverse Γ R letters hl),rootPath_eval,rootPath_eval]
  exact (mul_assoc _ _ _).symm
end TorsionFreeZeroDivisors.ConePicture
namespace TorsionFreeZeroDivisors.SampleGraph.ConeSpherePicture
open scoped Classical
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep}
end TorsionFreeZeroDivisors.SampleGraph.ConeSpherePicture

end

end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.ConeChains
open PortSubdivision GraphPresentation GraphConePresentation
open scoped Classical BigOperators
noncomputable section
variable {V D A S : Type} (Γ : PortGraph V D) (R : Routes Γ)
  (label : D→A) (inv : A→A) (letters : A→FreeGroup S)
  (hi : Function.Involutive inv) (hl : ∀d,label (Γ.reverse d)=inv (label d))
  (hw : ∀a,letters (inv a)=(letters a)⁻¹)
local notation "G" => GraphConePresentation.Group Γ (letters ∘ label) R
abbrev Cells := G × Edge Γ
abbrev TwoChain := Cells Γ R label letters →₀ ℤ
lemma edge_reverse (d : D) : edge Γ (Γ.reverse d)=edge Γ d :=
  Quotient.sound (Or.inr rfl)
lemma representative_edge (e : Edge Γ) : edge Γ (representative Γ e)=e := Quotient.out_eq e
include hl hw in
lemma letters_reverse (d : D) : (letters ∘ label) (Γ.reverse d)=((letters ∘ label) d)⁻¹ := by
  simp only [Function.comp_apply,hl,hw]
def eval : A ⊕ (ConePicture.Radial Γ R × Bool)→G
  | .inl a => oldMap Γ (letters ∘ label) R (letters a)
  | .inr (v,b) => if b then radialValue Γ (letters ∘ label) R v else (radialValue Γ (letters ∘ label) R v)⁻¹
/-- Actual oriented physical two-cell with its group translate. The translation
is measured from the common cone apex, not from the endpoint of the edge. -/
def cell (g : G) (d : D) : Cells Γ R label letters :=
  (g*(radialValue Γ (letters ∘ label) R (Γ.origin d))⁻¹,edge Γ d)
include hl hw in
lemma cell_reverse (g : G) (d : D) :
    cell Γ R label letters (g*oldMap Γ (letters ∘ label) R (letters (label d))) (Γ.reverse d)=
      cell Γ R label letters g d := by
  apply Prod.ext
  · dsimp [cell]
    rw [edge_value Γ (letters ∘ label) R (letters_reverse Γ label inv letters hl hw)]
    dsimp only [Function.comp_apply]
    group
  · exact edge_reverse Γ d

def charge (g : G) (d : D) : TwoChain Γ R label letters :=
  if d=representative Γ (edge Γ d) then Finsupp.single (cell Γ R label letters g d) 1
  else -Finsupp.single (cell Γ R label letters g d) 1
include hl hw in
lemma charge_reverse (g : G) (d : D) :
    charge Γ R label letters (g*oldMap Γ (letters ∘ label) R (letters (label d))) (Γ.reverse d)=
      -charge Γ R label letters g d := by
  rw [charge,cell_reverse Γ R label inv letters hl hw,edge_reverse]
  by_cases hd : d=representative Γ (edge Γ d)
  · have hr : Γ.reverse d≠representative Γ (edge Γ d) := by
      rw [←hd];exact Γ.reverse_ne d
    rw [if_neg hr,charge,if_pos hd]
  · have hr : Γ.reverse d=representative Γ (edge Γ d) := by
      rcases representative_cases Γ d with hh|hh
      · exact (hd hh).elim
      · exact (congrArg Γ.reverse hh).trans (Γ.reverse_reverse_apply _)
    rw [if_pos hr,charge,if_neg hd,neg_neg]
def coneCharge (g : G) : ConePicture.Dart Γ R→TwoChain Γ R label letters
  | .inl d => charge Γ R label letters g d
  | .inr _ => 0
include hl hw in
lemma coneCharge_reverse (g : G) (d : ConePicture.Dart Γ R) :
    coneCharge Γ R label letters
      (g*eval Γ R label letters (ConePicture.labels Γ R label d)) ((ConePicture.graph Γ R).reverse d)=
    -coneCharge Γ R label letters g d := by
  rcases d with d|p
  · exact charge_reverse Γ R label inv letters hl hw g d
  · exact (neg_zero).symm

variable {O : Type} [Fintype O]
  (a : SphericalPicture.Data (O:=O) (ConePicture.graph Γ R)
    (ConePicture.labels Γ R label) (ConePicture.inverse Γ R inv))
  (l : PictureChains.Lift _ _ _ (eval Γ R label letters) a)
end
end TorsionFreeZeroDivisors.ConeChains

end


end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.ConeSigned
open scoped Classical
open PortSubdivision GraphPresentation GraphConePresentation
noncomputable section
variable {V D S : Type} (Γ : PortGraph V D) (R : Routes Γ) (label : D→S×Bool)
def pack : (S×Bool) ⊕ (ConePicture.Radial Γ R × Bool) ≃ (Generator (S:=S) Γ R × Bool) where
  toFun | .inl (s,b)=>(.inl s,b) | .inr (v,b)=>(.inr v,b)
  invFun | (.inl s,b)=>.inl (s,b) | (.inr v,b)=>.inr (v,b)
  left_inv x := by rcases x with ⟨s,b⟩|⟨v,b⟩ <;> rfl
  right_inv x := by rcases x with ⟨s|v,b⟩ <;> rfl
lemma pack_inverse (a : (S×Bool) ⊕ (ConePicture.Radial Γ R × Bool)) :
    pack (S:=S) Γ R (ConePicture.inverse Γ R WordPairing.inverseLetter a)=
      WordPairing.inverseLetter (pack Γ R a) := by
  rcases a with ⟨s,b⟩|⟨v,b⟩ <;> rfl
def labels : ConePicture.Dart Γ R→Generator (S:=S) Γ R × Bool := pack Γ R ∘ ConePicture.labels Γ R label
lemma labels_reverse (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
    (d : ConePicture.Dart Γ R) :
    labels Γ R label ((ConePicture.graph Γ R).reverse d)=WordPairing.inverseLetter (labels Γ R label d) := by
  dsimp only [labels,Function.comp_apply]
  rw [ConePicture.label_reverse Γ R label WordPairing.inverseLetter hl,pack_inverse]
def unpack {O : Type}[Fintype O]
    (a : SphericalPicture.Data (O:=O) (ConePicture.graph Γ R) (labels Γ R label) WordPairing.inverseLetter) :
    SphericalPicture.Data (O:=O) (ConePicture.graph Γ R) (ConePicture.labels Γ R label)
      (ConePicture.inverse Γ R WordPairing.inverseLetter) where
  rotation := a.rotation
  partner := a.partner
  involutive := a.involutive
  fixed_free := a.fixed_free
  dart := a.dart
  consistent := a.consistent
  compatible i := by
    apply (pack Γ R).injective
    rw [pack_inverse]
    exact a.compatible i
  genusZero := a.genusZero
lemma reduces_to_empty (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
    (hex : ∀{P : Type}[Fintype P][Nonempty P]
      (a : SphericalPicture.Data (O:=P) Γ label WordPairing.inverseLetter),¬a.Reduced)
    {O : Type}[Fintype O]
    (a : SphericalPicture.Data (O:=O) (ConePicture.graph Γ R) (labels Γ R label) WordPairing.inverseLetter) :
    SphericalPicture.ReducesToEmpty _ _ _ a := by
  apply SphericalPicture.reduces_of_no_reduced WordPairing.inverseLetter_involutive (labels_reverse Γ R label hl)
  intro P _ _ b hb
  exact hex (ConePicture.oldData (unpack Γ R label b) hb)
    (ConePicture.oldData_reduced _ hb)
lemma freeLetter_inverse {A : Type} (a : A×Bool) :
    freeLetter (WordPairing.inverseLetter a)=(freeLetter a)⁻¹ := by
  change FreeGroup.mk [WordPairing.inverseLetter a]=(FreeGroup.mk [a])⁻¹
  rw [FreeGroup.inv_mk]
  rfl
lemma freeLetter_map {A B : Type} (f : A→B) (a : A×Bool) :
    FreeGroup.map f (freeLetter a)=freeLetter (f a.1,a.2) := by
  simp only [freeLetter,FreeGroup.map.mk,List.map_singleton]
local notation "letters" => freeLetter ∘ label
local notation "G" => GraphConePresentation.Group Γ letters R
def eval (a : Generator (S:=S) Γ R × Bool) : G := PresentedGroup.mk _ (freeLetter a)
lemma eval_inverse (a : Generator (S:=S) Γ R × Bool) :
    eval Γ R label (WordPairing.inverseLetter a)=(eval Γ R label a)⁻¹ := by
  simp only [eval,freeLetter_inverse,map_inv]
lemma eval_pack (a : (S×Bool) ⊕ (ConePicture.Radial Γ R × Bool)) :
    eval Γ R label (pack Γ R a)=ConeChains.eval Γ R label freeLetter a := by
  rcases a with ⟨s,b⟩|⟨v,b⟩
  · change PresentedGroup.mk _ (freeLetter (Sum.inl s,b))=
      oldMap Γ letters R (freeLetter (s,b))
    rw [oldMap,MonoidHom.comp_apply,old,freeLetter_map]
  · cases b
    · change PresentedGroup.mk _ (FreeGroup.of (Sum.inr v))⁻¹=
        (radialValue Γ letters R v)⁻¹
      rw [map_inv,radialValue,radial,dif_neg v.property]
    · change PresentedGroup.mk _ (FreeGroup.of (Sum.inr v))=radialValue Γ letters R v
      rw [radialValue,radial,dif_neg v.property]
lemma wordLabel_eq (d : ConePicture.Dart Γ R) :
    freeLetter (labels Γ R label d)=ConePicture.wordLabel Γ R letters d := by
  rcases d with d|⟨v,b⟩
  · change freeLetter (Sum.inl (label d).1,(label d).2)=FreeGroup.map Sum.inl (freeLetter (label d))
    exact (freeLetter_map _ _).symm
  · cases b <;> rfl
lemma value_mk {A H : Type} [_root_.Group H] (q : FreeGroup A→*H) (w : List (A×Bool)) :
    WordCursor.value (fun a=>q (freeLetter a)) w=q (FreeGroup.mk w) := by
  induction w with
  | nil=>exact (map_one q).symm
  | cons a w ih=>rw [WordCursor.value_cons,ih,show a::w=[a]++w from rfl,←FreeGroup.mul_mk,map_mul];rfl
lemma eval_value (w : List (Generator (S:=S) Γ R × Bool)) :
    WordCursor.value (eval Γ R label) w=PresentedGroup.mk _ (FreeGroup.mk w) :=
  value_mk _ w

end
end TorsionFreeZeroDivisors.ConeSigned

end


end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.ConeArea
open scoped Classical BigOperators
open PortSubdivision GraphPresentation GraphConePresentation ConeSigned WordCursor
noncomputable section
variable {V D S : Type} (Γ : PortGraph V D) (R : Routes Γ) (label : D→S×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
local notation "letters" => freeLetter ∘ label
local notation "G" => GraphConePresentation.Group Γ letters R
local notation "v" => ConeSigned.eval Γ R label ∘ ConeSigned.labels Γ R label
local notation "c" => ConeChains.coneCharge Γ R label freeLetter
include hl in
lemma letters_reverse (d : D) : letters (Γ.reverse d)=(letters d)⁻¹ := by
  simp only [Function.comp_apply,hl,freeLetter_inverse]
lemma path_value {a b : V} (p : Path (ConePicture.graph Γ R) a b) :
    value v p.darts=PresentedGroup.mk _ (p.eval (ConePicture.wordLabel Γ R letters)) := by
  induction p with
  | nil=>simp [Path.darts_nil]
  | cons d p ih=>
    rw [Path.darts_cons,value_cons,ih,Path.eval_cons,map_mul]
    congr 1
    exact congrArg (PresentedGroup.mk _) (wordLabel_eq Γ R label d)
lemma root_value (a : V) : value v (ConePicture.rootPath Γ R a).darts=radialValue Γ letters R a := by
  rw [path_value,ConePicture.rootPath_eval]
  rfl
lemma root_charge (g : G) (a : V) :
    PathCharges.charge v c g (ConePicture.rootPath Γ R a).darts=0 := by
  by_cases ha : a=R.base a
  · simp only [ConePicture.rootPath,dif_pos ha,Path.darts_cast,Path.darts_nil,PathCharges.charge_nil]
  · simp only [ConePicture.rootPath,dif_neg ha,Path.darts_cast,Path.single,Path.darts_cons,
      Path.darts_nil,PathCharges.charge_cons,PathCharges.charge_nil,ConeChains.coneCharge,add_zero]
include hl in
lemma eval_reverse (d : ConePicture.Dart Γ R) :
    v ((ConePicture.graph Γ R).reverse d)=(v d)⁻¹ := by
  dsimp only [Function.comp_apply]
  rw [ConeSigned.labels_reverse Γ R label hl,ConeSigned.eval_inverse]
include hl in
lemma charge_reverse (g : G) (d : ConePicture.Dart Γ R) :
    c (g*v d) ((ConePicture.graph Γ R).reverse d)=-c g d := by
  change c (g*ConeSigned.eval Γ R label (pack Γ R (ConePicture.labels Γ R label d))) _=_
  rw [eval_pack]
  exact ConeChains.coneCharge_reverse Γ R label WordPairing.inverseLetter freeLetter hl freeLetter_inverse g d
include hl in
lemma reverse_root_charge (g : G) (a : V) :
    PathCharges.charge v c g (ConePicture.rootPath Γ R a).reverse.darts=0 := by
  let w := (ConePicture.rootPath Γ R a).darts
  have h := PathCharges.charge_reverse v c (ConePicture.graph Γ R).reverse
    (eval_reverse Γ R label hl) (charge_reverse Γ R label hl) (g*(value v w)⁻¹) w
  rw [inv_mul_cancel_right,root_charge,neg_zero] at h
  simpa only [Path.darts_reverse] using h
include hl in
lemma triangle_charge (g : G) (d : D) :
    PathCharges.charge v c g (ConePicture.trianglePath Γ R d).darts=
      ConeChains.charge Γ R label freeLetter (g*radialValue Γ letters R (Γ.origin d)) d := by
  simp only [ConePicture.trianglePath,Path.darts_cast,Path.darts_append,PathCharges.charge_append]
  rw [root_charge,zero_add,root_value]
  rw [reverse_root_charge Γ R label hl,add_zero]
  simp only [Path.single,Path.darts_cons,Path.darts_nil,PathCharges.charge_cons,
    PathCharges.charge_nil,add_zero,ConeChains.coneCharge]
def loops (e : Edge Γ) : InitialPicture.Loop (ConePicture.graph Γ R) :=
  ⟨R.base (Γ.origin (representative Γ e)),ConePicture.trianglePath Γ R (representative Γ e)⟩
def words : Edge Γ→List (Generator (S:=S) Γ R × Bool) :=
  InitialPicture.relWords (ConePicture.graph Γ R) (ConeSigned.labels Γ R label) (loops Γ R)
include hl in
lemma words_mk (e : Edge Γ) : FreeGroup.mk (words Γ R label e)=attachment Γ letters R e := by
  rw [words,InitialPicture.relWords,Path.letters_mk]
  have hh : (fun d=>FreeGroup.mk [ConeSigned.labels Γ R label d])=ConePicture.wordLabel Γ R letters := by
    funext d;exact wordLabel_eq Γ R label d
  rw [hh]
  exact ConePicture.trianglePath_eval Γ R letters (letters_reverse Γ label hl) (representative Γ e)
include hl in
lemma loop_value (e : Edge Γ) : value v (loops Γ R e).2.darts=1 := by
  rw [path_value]
  change PresentedGroup.mk _ ((ConePicture.trianglePath Γ R (representative Γ e)).eval _)=1
  rw [ConePicture.trianglePath_eval Γ R letters (letters_reverse Γ label hl)]
  exact triangle_trivial Γ letters R (letters_reverse Γ label hl) _
include hl in
lemma loop_charge (g : G) (e : Edge Γ) :
    PathCharges.charge v c g (loops Γ R e).2.darts=Finsupp.single (g,e) (1:ℤ) := by
  rw [loops,triangle_charge Γ R label hl,ConeChains.charge]
  have he : edge Γ (representative Γ e)=e := ConeChains.representative_edge Γ e
  rw [he,if_pos rfl]
  congr 1
  apply Prod.ext
  · exact mul_inv_cancel_right _ _
  · exact he
include hl in
lemma signed_charge (g : G) (t : AlgebraicPictures.Term (A:=Generator (S:=S) Γ R) (I:=Edge Γ)) :
    PathCharges.charge v c g (InitialPicture.signedLoop (ConePicture.graph Γ R) (loops Γ R) t).2.darts=
      if t.positive then Finsupp.single (g,t.index) (1:ℤ) else -Finsupp.single (g,t.index) (1:ℤ) := by
  obtain ⟨i,b,co⟩ := t
  cases b
  · change PathCharges.charge v c g (loops Γ R i).2.reverse.darts= -Finsupp.single (g,i) (1:ℤ)
    rw [Path.darts_reverse]
    have h := PathCharges.charge_reverse v c (ConePicture.graph Γ R).reverse
      (eval_reverse Γ R label hl) (charge_reverse Γ R label hl) g (loops Γ R i).2.darts
    rw [loop_value Γ R label hl,mul_one,loop_charge Γ R label hl] at h
    exact h
  · exact loop_charge Γ R label hl g i
include hl in
lemma term_value (t : AlgebraicPictures.Term (A:=Generator (S:=S) Γ R) (I:=Edge Γ)) :
    value (ConeSigned.eval Γ R label) (t.word (words Γ R label))=1 := by
  rw [AlgebraicPictures.Term.word,value_append,value_append]
  have hr : value (ConeSigned.eval Γ R label) (words Γ R label t.index)=1 := by
    rw [eval_value,words_mk Γ R label hl]
    exact PresentedGroup.one_of_mem ⟨_,rfl⟩
  have hi (w) := PathCharges.value_reverse (ConeSigned.eval Γ R label)
    WordPairing.inverseLetter (ConeSigned.eval_inverse Γ R label) w
  have hh (w : List (Generator (S:=S) Γ R × Bool)) : FreeGroup.invRev w=w.reverse.map WordPairing.inverseLetter := by
    simp only [FreeGroup.invRev,List.map_reverse]
    congr 1
  rw [hh,hi]
  cases hb : t.positive <;>
    simp only [AlgebraicPictures.Term.core,hb,Bool.false_eq_true,ite_false,ite_true,hh,hi,hr,inv_one,mul_one,mul_inv_cancel]
def termArea (t : AlgebraicPictures.Term (A:=Generator (S:=S) Γ R) (I:=Edge Γ)) :
    ConeChains.TwoChain Γ R label freeLetter :=
  if t.positive then Finsupp.single (PresentedGroup.mk _ (FreeGroup.mk t.connector),t.index) 1
  else -Finsupp.single (PresentedGroup.mk _ (FreeGroup.mk t.connector),t.index) 1
include hl in
lemma termArea_eq (t : AlgebraicPictures.Term (A:=Generator (S:=S) Γ R) (I:=Edge Γ)) :
    termArea Γ R label t=FramedLoopIdentities.area (ConePicture.graph Γ R)
      (ConeSigned.labels Γ R label) (loops Γ R) (ConeSigned.eval Γ R label) c t := by
  rw [FramedLoopIdentities.area,signed_charge Γ R label hl,eval_value]
  rfl
include hl in
/-- Every actual free identity of the physical triangular presentation has zero
integral translated physical-cell area. No cellular realization is presumed. -/
theorem identity_zero
    (hex : ∀{P : Type}[Fintype P][Nonempty P]
      (a : SphericalPicture.Data (O:=P) Γ label WordPairing.inverseLetter),¬a.Reduced)
    (ts : List (AlgebraicPictures.Term (A:=Generator (S:=S) Γ R) (I:=Edge Γ)))
    (he : FreeGroup.mk (AlgebraicPictures.word (words Γ R label) ts)=1) :
    (ts.map (termArea Γ R label)).sum=0 := by
  have hh := FramedLoopIdentities.identity_area_zero (ConePicture.graph Γ R)
    (ConeSigned.labels Γ R label) (ConeSigned.labels_reverse Γ R label hl) (loops Γ R)
    (ConeSigned.eval Γ R label) (ConeSigned.eval_inverse Γ R label) c
    (charge_reverse Γ R label hl) ts he (fun t _=>term_value Γ R label hl t)
    (fun a=>ConeSigned.reduces_to_empty Γ R label hl hex a)
  have heq : termArea Γ R label=FramedLoopIdentities.area (ConePicture.graph Γ R)
      (ConeSigned.labels Γ R label) (loops Γ R) (ConeSigned.eval Γ R label) c := by
    funext t;exact termArea_eq Γ R label hl t
  rw [heq];exact hh
end
end TorsionFreeZeroDivisors.ConeArea

end

end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.FreeActionNorm
open scoped Classical BigOperators
open CategoryTheory
noncomputable section
variable {H X : Type} [CommGroup H] [MulAction H X] [IsCancelSMul H X]
abbrev Orbit := Quotient (MulAction.orbitRel H X)
def orbitMap (p : Orbit (H:=H) (X:=X) × H) : X := p.2 • p.1.out
omit [IsCancelSMul H X] in
lemma orbit_class (h : H) (x : X) : (Quotient.mk'' (h • x) : Orbit (H:=H))=Quotient.mk'' x := by
  apply Quotient.sound
  exact MulAction.mem_orbit_iff.mpr ⟨h,rfl⟩
lemma orbitMap_bijective : Function.Bijective (orbitMap (H:=H) (X:=X)) := by
  constructor
  · rintro ⟨j,h⟩ ⟨k,g⟩ he
    have hjk : j=k := by
      have := congrArg (fun x=>(Quotient.mk'' x : Orbit (H:=H))) he
      simpa only [orbitMap,orbit_class,Quotient.out_eq'] using this
    subst k
    exact Prod.ext rfl (IsCancelSMul.right_cancel h g j.out he)
  · intro x
    have hx : x∈MulAction.orbit H (Quotient.mk'' x : Orbit (H:=H)).out := by
      exact (MulAction.orbitRel_apply).mp (Quotient.exact (Quotient.out_eq' (Quotient.mk'' x : Orbit (H:=H))).symm)
    obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp hx
    exact ⟨⟨Quotient.mk'' x,h⟩,hh⟩
def orbitEquiv : Orbit (H:=H) (X:=X) × H ≃ X := Equiv.ofBijective orbitMap orbitMap_bijective
@[simp] lemma orbitEquiv_apply (j : Orbit (H:=H) (X:=X)) (h : H) : orbitEquiv (j,h)=h • j.out := rfl

def act (h : H) : (X→₀ℤ)≃+(X→₀ℤ) := Finsupp.domCongr (MulAction.toPerm h)
omit [IsCancelSMul H X] in
@[simp] lemma act_apply (h : H) (x : X→₀ℤ) (a : X) : act h x a=x (h⁻¹ • a) := rfl

def coords : (X→₀ℤ)≃+(Orbit (H:=H) (X:=X)→₀MonoidAlgebra ℤ H) :=
  ((Finsupp.domCongr orbitEquiv.symm).trans Finsupp.curryAddEquiv).trans
    (Finsupp.mapRange.addEquiv (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toAddEquiv)
@[simp] lemma coords_coeff (x : X→₀ℤ) (j : Orbit (H:=H) (X:=X)) (h : H) :
    ((coords x) j).coeff h=x (h • j.out) := rfl
variable [Fintype H]
end
end TorsionFreeZeroDivisors.FreeActionNorm


end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.CellNorm
open scoped Classical BigOperators
open CellModule
noncomputable section
variable {H G I : Type} [CommGroup H] [_root_.Group G] [Fintype H]
  (φ : H→*G) (hφ : Function.Injective φ)
@[instance_reducible] def moduleAction : MulAction H (G×I) where
  smul h p := (φ h*p.1,p.2)
  one_smul p := by change (φ 1*p.1,p.2)=p; simp
  mul_smul h k p := by change (φ (h*k)*p.1,p.2)=(φ h*(φ k*p.1),p.2); rw [map_mul,mul_assoc]

def augmentation : CellModule.Module G I→+ℤ := Finsupp.liftAddHom (fun _=>AddMonoidHom.id ℤ)
omit [_root_.Group G] in
@[simp] lemma augmentation_single (p : G×I) (z : ℤ) : augmentation (Finsupp.single p z)=z := by simp [augmentation]
end
end TorsionFreeZeroDivisors.CellNorm

end



end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.RelationTorsion
open scoped Classical BigOperators
open AlgebraicPictures CellModule RelationArea
noncomputable section
variable {A I : Type} (rel : I→List (A×Bool))
local instance zpowersCommGroup (g : G rel) : CommGroup (Subgroup.zpowers g) := IsCyclic.commGroup
end
end TorsionFreeZeroDivisors.RelationTorsion

end


end OAI

end
end

section
section
namespace OAI



section
namespace TorsionFreeZeroDivisors.ConeTorsion
open scoped Classical
open PortSubdivision GraphPresentation GraphConePresentation
noncomputable section
variable {V D S : Type} (Γ : PortGraph V D) (R : Routes Γ) (label : D→S×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
local notation "letters" => ConeSigned.freeLetter ∘ label
include hl in
lemma relations_eq : AlgebraicPictures.relations (ConeArea.words Γ R label)=
    GraphConePresentation.relations Γ letters R := by
  change Set.range (fun e=>FreeGroup.mk (ConeArea.words Γ R label e))=Set.range _
  congr 1
  funext e
  exact ConeArea.words_mk Γ R label hl e
include hl in
lemma total_zero
    (hex : ∀{P : Type}[Fintype P][Nonempty P]
      (a : SphericalPicture.Data (O:=P) Γ label WordPairing.inverseLetter),¬a.Reduced)
    (ts : List (AlgebraicPictures.Term (A:=Generator (S:=S) Γ R) (I:=Edge Γ)))
    (he : FreeGroup.mk (AlgebraicPictures.word (ConeArea.words Γ R label) ts)=1) :
    RelationArea.total (ConeArea.words Γ R label) ts=0 := by
  have h := ConeArea.identity_zero Γ R label hl hex ts he
  unfold RelationArea.total RelationArea.term RelationArea.q RelationArea.G
  rw [relations_eq Γ R label hl]
  exact h
end
end TorsionFreeZeroDivisors.ConeTorsion

end



end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ConcreteTorsion
open scoped Classical
open SampleGraph
variable (rep : ℕ) (r : ActualPatternEvent.Match rep)
def signedLabels : DA rep⊕DB rep→Types.Generator×Bool :=
  Types.signedLetter.symm ∘ label rep
lemma signedLabels_reverse (d : DA rep⊕DB rep) :
    signedLabels rep ((graph rep r).reverse d)=WordPairing.inverseLetter (signedLabels rep d) := by
  simp only [signedLabels,Function.comp_apply,label_reverse,Types.inverse,Equiv.symm_apply_apply]
  rfl
lemma freeLetter_eq (t : Types.Letter) :
    ConeSigned.freeLetter (Types.signedLetter.symm t)=ConcreteGroup.freeLetter t := by
  obtain ⟨⟨g,b⟩,rfl⟩ := Types.signedLetter.surjective t
  cases b <;> simp only [ConeSigned.freeLetter,ConcreteGroup.freeLetter,Equiv.symm_apply_apply,Bool.false_eq_true,ite_false,ite_true] <;> rfl
lemma letters_eq : ConeSigned.freeLetter ∘ signedLabels rep=ConcreteGroup.labels rep := by
  funext d
  exact freeLetter_eq _
def unsigned {O : Type} [Fintype O]
    (a : SphericalPicture.Data (O:=O) (graph rep r) (signedLabels rep) WordPairing.inverseLetter) :
    SphericalPicture.Data (O:=O) (graph rep r) (label rep) Types.inverse where
  rotation := a.rotation
  partner := a.partner
  involutive := a.involutive
  fixed_free := a.fixed_free
  dart := a.dart
  consistent := a.consistent
  compatible i := by
    have h := congrArg Types.signedLetter (a.compatible i)
    simpa only [signedLabels,Function.comp_apply,Equiv.apply_symm_apply,WordPairing.inverseLetter,Types.inverse] using h
  genusZero := a.genusZero
variable (x : VA rep) (y : VB rep)
  (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
  (hsample : r∈ActualPatternEvent.samples rep)
  (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
    (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y))
include hL hd hsample havoid in
theorem torsion_free : ∀ (g : ConcreteGroup.G rep r) (n : ℕ), 0 < n → g ^ n = 1 → g = 1 := by
  have hex {O : Type} [Fintype O] [Nonempty O]
      (a : SphericalPicture.Data (O:=O) (graph rep r) (signedLabels rep) WordPairing.inverseLetter) : ¬a.Reduced := by
    intro ha
    exact SpherePicture.excluded (unsigned rep r a) ha hL hd hsample havoid
  have h := ConeTorsion.graph_torsion_free (graph rep r) (ConcreteGroup.routes rep r)
    (signedLabels rep) (signedLabels_reverse rep r) (GraphConePresentation.canonical_base _) hex
  rw [letters_eq] at h
  exact h
end TorsionFreeZeroDivisors.ConcreteTorsion

namespace TorsionFreeZeroDivisors
end TorsionFreeZeroDivisors

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors
lemma HasFiniteTwoDimensionalClassifyingSpace.of_equiv {G H : Type} [_root_.Group G] [_root_.Group H]
    (e : G ≃* H) (h : HasFiniteTwoDimensionalClassifyingSpace H) :
    HasFiniteTwoDimensionalClassifyingSpace G := by
  rcases h with ⟨X,topX,hT,hP,cw,hf,hh,h2,x,⟨k⟩,E,topE,hE,p,hp,hps⟩
  exact ⟨X,topX,hT,hP,cw,hf,hh,h2,x,⟨e.trans k⟩,E,topE,hE,p,hp,hps⟩
end TorsionFreeZeroDivisors
namespace TorsionFreeZeroDivisors.ConcreteModel
open scoped Classical
open SampleGraph
variable (rep : ℕ) (r : ActualPatternEvent.Match rep)
  (x : VA rep) (y : VB rep)
  (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
  (hsample : r∈ActualPatternEvent.samples rep)
  (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
    (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y))
include hL hd hsample havoid in
/-- The finite exact two-dimensional model of the actual sampled graph group.
The cover contraction is built by absorbing physical disk-track obstructions
through the proved integral cell-boundary splitting. -/
theorem has_model : HasFiniteTwoDimensionalClassifyingSpace (ConcreteGroup.G rep r) := by
  have hex {O : Type} [Fintype O] [Nonempty O]
      (a : SphericalPicture.Data (O:=O) (graph rep r) (ConcreteTorsion.signedLabels rep) WordPairing.inverseLetter) : ¬a.Reduced := by
    intro ha
    exact SpherePicture.excluded (ConcreteTorsion.unsigned rep r a) ha hL hd hsample havoid
  obtain ⟨t,ht⟩ := Finset.card_pos.mp (show 0<(Types.outgoingA x).card by
    have h := (Types.degreeA_bounds x).1
    omega)
  let : Nonempty (GraphConePresentation.Edge (graph rep r)) :=
    ⟨GraphConePresentation.edge (graph rep r) (Sum.inl ⟨(x,t),ht⟩)⟩
  have hm := RelationModel.has_model
    (ConeArea.words (graph rep r) (ConcreteGroup.routes rep r) (ConcreteTorsion.signedLabels rep))
    (ConeTorsion.total_zero (graph rep r) (ConcreteGroup.routes rep r) (ConcreteTorsion.signedLabels rep)
      (ConcreteTorsion.signedLabels_reverse rep r) hex)
  unfold RelationArea.G at hm
  rw [ConeTorsion.relations_eq _ _ _ (ConcreteTorsion.signedLabels_reverse rep r)] at hm
  rw [ConcreteTorsion.letters_eq] at hm
  exact HasFiniteTwoDimensionalClassifyingSpace.of_equiv
    (GraphConePresentation.equivalence (graph rep r) (ConcreteGroup.labels rep) (ConcreteGroup.routes rep r)
      (ConcreteGroup.labels_reverse rep r) (GraphConePresentation.canonical_base _)) hm
end TorsionFreeZeroDivisors.ConcreteModel

end

end OAI

end
end

section
section
namespace OAI

section

namespace TorsionFreeZeroDivisors
noncomputable section
/-- A torsion-free group with a finite 2-dimensional K(G,1) and zero divisors.
Both zero-divisor factors are nonzero, and torsion-freeness is ordinary
absence of all nontrivial finite-order elements. -/
theorem main_oai : MainTheorem := by
  obtain ⟨rep,r,x,y,hr,hL,hd,ha,hx,hy,hz⟩ := SampleGraph.exists_nonzero_factors
  exact ⟨ConcreteGroup.G rep r,inferInstance,inferInstance,
    ConcreteTorsion.torsion_free rep r x y hL hd hr ha,
    ConcreteModel.has_model rep r x y hL hd hr ha,
    ConcreteFactors.alpha rep r x,ConcreteFactors.beta rep r y,hx,hy,hz⟩
end
end TorsionFreeZeroDivisors

end

end OAI

end
end


theorem solution : OAI.TorsionFreeZeroDivisors.MainTheorem := OAI.TorsionFreeZeroDivisors.main_oai
