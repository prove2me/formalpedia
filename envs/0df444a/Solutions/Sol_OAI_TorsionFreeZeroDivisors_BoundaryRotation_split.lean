-- Prove2me | solution 1 for OAI.TorsionFreeZeroDivisors.BoundaryRotation.split
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T15:20:00.045107+00:00
-- url     : https://prove2.me/submissions/d6df1d4a-53eb-4917-9c3c-b1a45d18463b

import Mathlib
import Definitions.Def_TorsionFreeZeroDivisorsConstruction
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

section Switching
variable [DecidableEq D]

end Switching

namespace Walk
variable {Γ} {a b c : V}

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

end TorsionFreeZeroDivisors.GirthSwitch

/-! ### Typed matching families have nonempty large-girth spaces. -/

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedCycles
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {u v : V}

end TorsionFreeZeroDivisors.WeightedCycles
namespace TorsionFreeZeroDivisors.WeightedMoore
open scoped BigOperators

instance {D : Type*} [Fintype D] (k : ℕ) : Fintype (Chain D k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype D)
  | succ k ih => exact inferInstanceAs (Fintype (D × Chain D k))

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

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MultiplicityBound
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

end TorsionFreeZeroDivisors.MultiplicityBound

namespace TorsionFreeZeroDivisors.PathMultiplicity
open SimpleGraph WeightedMoore
open PortSubdivision SuppressedMoore
open scoped Classical
variable {V D : Type*} (Γ : PortGraph V D)
local instance : BEq (V ⊕ D) := instBEqOfDecidableEq

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore SuppressedMoore
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "len" => chainLength Γ mark h2

end TorsionFreeZeroDivisors.ChainPaths

namespace TorsionFreeZeroDivisors.PathMultiplicity
open PortSubdivision
open scoped BigOperators Classical
variable {V D I : Type*} (Γ : PortGraph V D) [Fintype I]

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore SuppressedMoore
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

namespace Passages
variable {origin : D → V} {port : O → D}

end Passages
end TorsionFreeZeroDivisors.IncidenceStages

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MatchingGraphs
open PortSubdivision
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.ConditionedMatchings
open PortSubdivision
variable {V D T : Type*}

namespace Matching
variable {label : D → T} {bar : T → T}
instance : CoeFun (Matching label bar) (fun _ => D → D) := ⟨fun r => r.val⟩
instance : DecidableEq (Matching label bar) := Classical.decEq _

@[ext] theorem ext {r s : Matching label bar} (h : ∀ x, r x = s x) : r = s :=
  Subtype.ext (Equiv.ext h)

variable [DecidableEq D]

variable [Fintype V] [Fintype D]

end Matching
end TorsionFreeZeroDivisors.ConditionedMatchings

end

end OAI
end

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

instance : DecidableEq Field128 := Classical.decEq _

@[simp] theorem mem_pointsOn {p : Point} {l : Line} : p ∈ pointsOn l ↔ p ∈ l := by
  simp [pointsOn]

/-! The empirical type slots. Each line has exactly 33026 slots on each
side, before the admissible replication parameter is applied. -/

/-! ### The fixed inverse pairing and the actual space of graph matchings -/

@[simp] theorem inverse_signed (g : Generator) (b : Bool) :
    inverse (signedLetter (g,b)) = signedLetter (g,!b) := by simp [inverse]

@[simp] theorem inverse_inverse (t : Letter) : inverse (inverse t) = t := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  simp

variable {V : Type*} (outgoing : V → Finset Letter)

/-! Joint type incidences for internal-chain vertex counts.
These derive the turn weights from the actual prescribed types. -/

end Types
end TorsionFreeZeroDivisors

end

end OAI
end

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
open PortSubdivision WeightedMoore
variable {V D I : Type*} [Fintype V] [Fintype D] [Fintype I]
    (Γ : PortGraph V D) (p : I → List D) (hp : ∀ i,p i ≠ [])
    (cyclic : I → Bool)
    (hc : ∀ i,(p i).IsChain (PortWalk.step Γ.origin Γ.reverse))
    (hclose : ∀ i,cyclic i=true → ∀ᵉ (x∈(p i).getLast?) (y∈(p i).head?),
      PortWalk.step Γ.origin Γ.reverse x y)

end TorsionFreeZeroDivisors.ListStageExponents

/-! A choice of one direction for each unoriented edge of a finite port graph.
The reversal has no fixed points. No graph is assumed bipartite or loop-free. -/
namespace TorsionFreeZeroDivisors.InvolutionOrientation
open scoped Classical BigOperators
variable {D : Type*} [Fintype D] (σ : D → D)

variable (hσ : Function.Involutive σ) (hne : ∀d,σ d≠d)

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

variable [Fintype V]

end TorsionFreeZeroDivisors.ChainIsomorphism

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageRealization
open scoped Classical
open PortSubdivision
end TorsionFreeZeroDivisors.StageRealization

namespace TorsionFreeZeroDivisors.ChainRealization
open scoped Classical BigOperators
open TorsionFreeZeroDivisors.Types
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C V : Type*} [Fintype C] [Fintype V]
variable (len : C → ℕ) (first last : C → V)

end TorsionFreeZeroDivisors.ChainRealization

namespace TorsionFreeZeroDivisors.ChainWeights
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len : C → ℕ)

end TorsionFreeZeroDivisors.ChainWeights

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageExpectation
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
section
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C V TV : Type*} [Fintype C] [Fintype V] [Fintype TV]
variable (s : ℝ) (hs : 0 < s) (len : C → ℕ) (first last : C → V)

end

section Active
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ) (j : ℕ)

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
open PatternEmbeddings ConditionedMatchings BlockAlignment ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _

variable (s : ℝ) (hs : 0 < s)

variable {W : Type*}

end TorsionFreeZeroDivisors.TwoSideStage

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TwoSideFullStage
open scoped Classical BigOperators
open RepeatedBlocks BlockAlignment ComparedBlocks WordEstimate
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {A B E VA VB TA TB : Type} [Fintype A] [Fintype B] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : A ⊕ B → ℕ) (j : ℕ)

variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

end TorsionFreeZeroDivisors.TwoSideFullStage

namespace TorsionFreeZeroDivisors.MatchingGraphs
open PortSubdivision
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.TypedGraphs
open TorsionFreeZeroDivisors.Types PortSubdivision ConditionedMatchings
variable {V : Type*} (outgoing : V → Finset Letter)

end TorsionFreeZeroDivisors.TypedGraphs

namespace TorsionFreeZeroDivisors.GirthAsymptotics
open Filter
open scoped Topology

end TorsionFreeZeroDivisors.GirthAsymptotics

end

end OAI
end

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

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageEntropy

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0<s) (len m : C → ℕ) (err : ℕ)

end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate TwoSideFullStage
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {A B E VA VB TA TB : Type} [Fintype A] [Fintype B] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : A ⊕ B → ℕ) (j : ℕ)
variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

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
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0<s) (len m : C → ℕ) (err : ℕ)

variable [Fintype E]

end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
variable {C E : Type*} [Fintype C] [Fintype E] (s : ℝ) (hs : 0<s) (len m : C → ℕ) (err : ℕ)

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
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "S" => suppressed Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)

variable [Fintype V] {TV : Type} [Fintype TV]
    {outgoing : TV → Finset Types.Letter} {pin : V → Option TV}
    {r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) Types.inverse}

end TorsionFreeZeroDivisors.ActualStageRealization

namespace TorsionFreeZeroDivisors.ActualStageFeasibility
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate

variable {C : Type*} [Fintype C] (s : ℝ) (len : C → ℕ)

variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "m" => ChunkComparisons.multiplicity (ChainChunkTransport.color Γ mark h2 paths)

variable {E : Type*}
    (cmp : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (lo hi : E → ℤ) (hlo : ∀ e,cmp.lo e=(lo e:ℝ)) (hhi : ∀ e,cmp.hi e=(hi e:ℝ))

end TorsionFreeZeroDivisors.ActualStageFeasibility

namespace TorsionFreeZeroDivisors.StagePartition
open scoped Classical BigOperators
open RepeatedBlocks BlockAlignment ComparedBlocks WordEstimate
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)

variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

end TorsionFreeZeroDivisors.StagePartition

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PartitionEntropy
open scoped Classical BigOperators
open StageEntropy BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate StagePartition
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)
variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

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
variable {C V : Type*} (len m : C → ℕ) (j : ℕ) (side : C → Bool) (vside : V → Bool)
    (first last : {c // j < m c} → V)
    (hf : ∀ c,vside (first c)=side c.val) (hl : ∀ c,vside (last c)=side c.val) (b : Bool)

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

variable {P : Type*} [Fintype P]
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)

end TorsionFreeZeroDivisors.ChainSide

namespace TorsionFreeZeroDivisors.ActualSideRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons
variable {V D : Type} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    {P : Type} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ) (b : Bool)
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)

variable [Fintype V] {TV : Type} [Fintype TV]
    (label : D → Types.Letter) (outgoing : TV → Finset Types.Letter)
    (pin : SideRestriction.Vertex side b → Option TV)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) Types.inverse)

end TorsionFreeZeroDivisors.ActualSideRealization

end

end OAI
end

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
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)

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
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D P : Type} [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
local notation "S" => suppressed Γ mark h2

variable (side : V → Bool)

end TorsionFreeZeroDivisors.StageRoot

namespace TorsionFreeZeroDivisors.ActualStagePair
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking
open ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2

variable {E : Type}

end TorsionFreeZeroDivisors.ActualStagePair

namespace TorsionFreeZeroDivisors.ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking
open ComparedBlocks RepeatedBlocks

variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2

variable [Fintype E]

end TorsionFreeZeroDivisors.ActualPatternEvent

end

end OAI
end

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

end TorsionFreeZeroDivisors.ClusterLocalization

end

end OAI
end

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
lemma members_nonempty (c : Cycle f) : (members f c).Nonempty := by
  obtain ⟨x,rfl⟩ := cycle_surjective f c
  exact ⟨x,(mem_members f).mpr rfl⟩

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

namespace Paired
variable {S}
variable {α : Equiv.Perm O} (P : S.Paired α)
include P

end Paired
namespace PairOrbit
variable {A : Type} (r : A→A) (hr : Function.Involutive r)
variable [Fintype A]
end PairOrbit

namespace Paired
variable {S} {α : Equiv.Perm O} (P : S.Paired α)
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
lemma subset {b : Finset V} (hb : b∈P.parts) : b⊆S\P.remove := by
  intro x hx
  rw [←P.cover]
  exact Finset.mem_biUnion.mpr ⟨b,hb,hx⟩
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
variable {T E : Type} [Fintype T] {len : T → ℕ} (C : Comparisons (E:=E) len) (keep : T → Prop) (old : T → ℕ)

end TorsionFreeZeroDivisors.LocalizationCounts

namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs ComparedBlocks
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
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.MapDeletion

section
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p) (hs : σ p≠p)
end
open scoped Classical
open MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open PermutationCycles
variable {O A : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)

variable (hs : σ p≠p)
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open MapEuler
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

variable {inv : A → A} {label : Fin n → A}
end Ear
end

section
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Data
end Data

namespace Ear
variable (k : ℕ) (hk : k≤n) (a : A)
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
open MapEuler
variable {O : Type} (σ α : Equiv.Perm O) (p : O) (hs : σ p=p) (ha : α p=p)
variable [Fintype O]
end TorsionFreeZeroDivisors.IsolatedDeletion
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion

namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open MapEuler
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
open MapEuler PermutationCycles
variable {V D A O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D} {label : D→A} {inv : A→A} {x y : V}
variable (hxy : x≠y)
end TorsionFreeZeroDivisors.FinitePicture.Data

/-! Exact finite permutation cycles, including singleton cycles, as nonempty
lists with their literal successor. This is the coordinate bridge from marked
picture surgery to boundary words; it asserts no geometric realization. -/

end

end OAI
end

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

end Path
end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.GraphPresentation.Path
open PortSubdivision
variable {V D : Type} {Γ : PortGraph V D} {a b c : V}
variable {A : Type*} (label : D→A×Bool)

end TorsionFreeZeroDivisors.GraphPresentation.Path
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
variable {D A : Type*} (label : D→A)

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.MarkerInsertion
open scoped Classical
variable {O : Type} (σ α : Equiv.Perm O) (p : O)
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

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GraphPresentation.Path
open PortSubdivision
variable {V D : Type} {Γ : PortGraph V D} {a b : V}

end TorsionFreeZeroDivisors.GraphPresentation.Path
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
open PortSubdivision GraphPresentation
variable {V D A : Type} (Γ : PortGraph V D) (label : D→A) (inv : A→A)
variable {x y : V} (p : Path Γ x y) (hxy : x≠y) (ws : List (List D))

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.AlgebraicPictures
variable {A I : Type*} (rel : I→List (A×Bool))
open FreeGroup
end TorsionFreeZeroDivisors.AlgebraicPictures
namespace TorsionFreeZeroDivisors.InitialPicture
open scoped Classical
open PortSubdivision GraphPresentation
variable {V D A I : Type} (Γ : PortGraph V D) (label : D→A×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
variable {x y : V} (p : Path Γ x y)

end TorsionFreeZeroDivisors.InitialPicture

namespace TorsionFreeZeroDivisors.GraphPresentation

section
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)

variable {S : Type*} (letters : D→FreeGroup S) (R : Routes Γ)

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
variable (rep : ℕ) (r : ActualPatternEvent.Match rep)
instance : Group.IsFinitelyPresented (G rep r) := inferInstance
end

open scoped Classical
open SampleGraph
variable {rep : ℕ} (r : ActualPatternEvent.Match rep)

end TorsionFreeZeroDivisors.ConcreteGroup

end

end OAI
end

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
open BlockAlignment ComparedBlocks WordPositions
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
/-- Loops have no effect on separator closure. -/
def of_off_diagonal (h : ∀p q,p≠q→(R p q↔Q p q)) (P : RecursiveSeparator.Split R S) :
    RecursiveSeparator.Split Q S where
  remove := P.remove
  parts := P.parts
  remove_subset := P.remove_subset
  cover := P.cover
  disjoint := P.disjoint
  closed := by
    intro b hb x hx y hy hq
    by_cases he : x=y
    · simpa only [←he] using hx
    · exact P.closed b hb x hx y hy ((h x y he).mpr hq)
  size := P.size
  cost := P.cost

end TorsionFreeZeroDivisors.RecursiveSeparator.Split
namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing
open scoped Classical
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap) (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)

end TorsionFreeZeroDivisors.SampleGraph.FullPairing

end

end OAI
end

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

omit [Fintype O] in
lemma sameCycle_of_card_one (θ : Equiv.Perm O) (hθ : Nat.card (Cycle θ)=1) (x y : O) :
    θ.SameCycle x y := by
  have : Subsingleton (Cycle θ) := (Nat.card_eq_one_iff_unique.mp hθ).1
  exact (cycle_eq θ).mp (Subsingleton.elim _ _)

/-- In a cyclic contour with at most one exit from S, the labels of all members
of S are connected using only steps internal to S. This finite orbit argument
replaces a geometric assertion that tree-subtree corners form an interval. -/
theorem contour_interval_reachable (θ : Equiv.Perm O)
    (hθ : ∀ x y,θ.SameCycle x y) (S : Set O) (p : O)
    (hout : ∀ x∈S,θ x∉S → x=p) (H : SimpleGraph V) (label : O → V)
    (hstep : ∀ x∈S,θ x∈S → H.Reachable (label x) (label (θ x)))
    (x : O) (hx : x∈S) : H.Reachable (label p) (label x) := by
  by_contra hn
  have invariant (y : O) (hy : y∈S) (hn : ¬H.Reachable (label p) (label y)) :
      θ y∈S ∧ ¬H.Reachable (label p) (label (θ y)) := by
    have hy' : θ y∈S := by
      by_contra h
      have he := hout y hy h
      subst y
      exact hn (SimpleGraph.Reachable.refl _)
    refine ⟨hy',fun h=>hn (h.trans (hstep y hy hy').symm)⟩
  have hp (n : ℕ) : (θ^n) x∈S ∧ ¬H.Reachable (label p) (label ((θ^n) x)) := by
    induction n with
    | zero => exact ⟨hx,hn⟩
    | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      exact invariant _ ih.1 ih.2
  obtain ⟨n,he⟩ := (hθ x p).exists_nat_pow_eq
  have hh := (hp n).2
  rw [he] at hh
  exact hh (SimpleGraph.Reachable.refl _)

end

open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha)

omit [Fintype O] in
lemma pairFinset_adj (e : T.edgeSet) {x : O} (hx : x∈pairFinset σ α ha T hT e) :
    T.Adj (cycle σ x) (cycle σ (α x)) := by
  change s(cycle σ x,cycle σ (α x))∈T.edgeSet
  rw [pairFinset_edge σ α ha T hT e hx]
  exact e.property

omit [Fintype O] in
lemma pairFinset_cycle_injective (e : T.edgeSet) {x y : O}
    (hx : x∈pairFinset σ α ha T hT e) (hy : y∈pairFinset σ α ha T hT e)
    (h : cycle σ x=cycle σ y) : x=y := by
  have hadj := pairFinset_adj σ α ha T hT e hx
  simp only [pairFinset,Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
  · rfl
  · exact (hadj.ne h).elim
  · rw [ha] at hadj
    exact (hadj.ne h).elim
  · rfl

lemma subgraphPair_nonfixed_mem {x : O} (hx : subgraphPair σ α ha T hT x≠x) :
    x∈pickedDarts σ α ha T hT := by
  have h := Equiv.Perm.mem_support.mpr hx
  rwa [subgraphPair_support] at h

lemma subgraphPair_nonfixed_apply {x : O} (hx : subgraphPair σ α ha T hT x≠x) :
    subgraphPair σ α ha T hT x=α x := by
  rw [subgraphPair_apply,if_pos (subgraphPair_nonfixed_mem σ α ha T hT hx)]

lemma subgraphPair_adj {x : O} (hx : subgraphPair σ α ha T hT x≠x) :
    T.Adj (cycle σ x) (cycle σ (subgraphPair σ α ha T hT x)) := by
  obtain ⟨e,he⟩ := (mem_pickedDarts σ α ha T hT x).mp
    (subgraphPair_nonfixed_mem σ α ha T hT hx)
  rw [subgraphPair_nonfixed_apply σ α ha T hT hx]
  exact pairFinset_adj σ α ha T hT e he

/-- A realized simple subgraph has exactly one dart per directed adjacency. -/
theorem subgraphPair_dart_unique {x y : O}
    (hx : subgraphPair σ α ha T hT x≠x) (hy : subgraphPair σ α ha T hT y≠y)
    (h₁ : cycle σ x=cycle σ y)
    (h₂ : cycle σ (subgraphPair σ α ha T hT x)=cycle σ (subgraphPair σ α ha T hT y)) : x=y := by
  obtain ⟨e,he⟩ := (mem_pickedDarts σ α ha T hT x).mp
    (subgraphPair_nonfixed_mem σ α ha T hT hx)
  obtain ⟨f,hf⟩ := (mem_pickedDarts σ α ha T hT y).mp
    (subgraphPair_nonfixed_mem σ α ha T hT hy)
  rw [subgraphPair_nonfixed_apply σ α ha T hT hx,
    subgraphPair_nonfixed_apply σ α ha T hT hy] at h₂
  have hef : e=f := Subtype.ext (by
    rw [←pairFinset_edge σ α ha T hT e he,←pairFinset_edge σ α ha T hT f hf,h₁,h₂])
  subst f
  exact pairFinset_cycle_injective σ α ha T hT e he hf h₁

end TorsionFreeZeroDivisors.MapEuler

/-! The weighted centroid needed by planar dual-tree separator constructions.
This is an actual theorem for finite Mathlib trees, not a separator assumption. -/
namespace TorsionFreeZeroDivisors.TreeCentroid
open scoped Classical BigOperators
open SimpleGraph
variable {V : Type} {G : SimpleGraph V} (h : G.IsTree)

def path (x y : V) : G.Walk x y := (h.connected.exists_path_of_dist x y).choose
lemma path_isPath (x y : V) : ((path h) x y).IsPath :=
  (h.connected.exists_path_of_dist x y).choose_spec.1
lemma path_length (x y : V) : ((path h) x y).length=G.dist x y :=
  (h.connected.exists_path_of_dist x y).choose_spec.2
lemma eq_path {x y : V} {p : G.Walk x y} (hp : p.IsPath) : p=(path h) x y :=
  Subtype.mk.inj (h.isAcyclic.subsingleton_path x y |>.elim ⟨p,hp⟩ ⟨_,(path_isPath h) x y⟩)
include h in
lemma path_dist {x y : V} {p : G.Walk x y} (hp : p.IsPath) : p.length=G.dist x y := by
  rw [(eq_path h) hp,(path_length h)]

def next (x y : V) : V := ((path h) x y).snd
lemma next_adj {x y : V} (hne : x≠y) : G.Adj x ((next h) x y) :=
  Walk.adj_snd (Walk.not_nil_of_ne hne)

lemma next_concat {c x y : V} {p : G.Walk c x} (hne : c≠x) (e : G.Adj x y) :
    (p.concat e).snd=p.snd := by
  cases p with
  | nil => exact (hne rfl).elim
  | cons _ _ => simp only [Walk.concat_eq_append,Walk.cons_append,Walk.snd_cons]

lemma next_adjacent {c x y : V} (hx : c≠x) (hy : c≠y) (e : G.Adj x y) :
    (next h) c x=(next h) c y := by
  by_cases hm : x∈((path h) c y).support
  · have hh := h.isAcyclic.path_concat ((path_isPath h) c x) ((path_isPath h) c y) e hm
    unfold next
    rw [hh,next_concat hx]
  · have hm' := h.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
      ((path_isPath h) c x) ((path_isPath h) c y) e hm
    have hh := h.isAcyclic.path_concat ((path_isPath h) c y) ((path_isPath h) c x) e.symm hm'
    unfold next
    rw [hh,next_concat hy]

lemma dist_next {c z : V} (hz : c≠z) : G.dist c z=G.dist ((next h) c z) z+1 := by
  have hl := (path_dist h) ((path_isPath h) c z).tail
  rw [Walk.length_tail,(path_length h)] at hl
  change G.dist c z-1=G.dist (next h c z) z at hl
  have hd : 0<G.dist c z := Nat.pos_of_ne_zero (fun he=>hz (h.connected.dist_eq_zero_iff.mp he))
  omega
lemma dist_not_next {c n z : V} (e : G.Adj c n) (hn : (next h) c z≠n) :
    G.dist n z=G.dist c z+1 := by
  have hmem : n∉((path h) c z).support := by
    intro hm
    exact hn (h.isAcyclic.eq_snd_of_adj_start ((path_isPath h) c z) e hm).symm
  have hp := ((path_isPath h) c z).cons (h := e.symm) hmem
  have hl := (path_dist h) hp
  simpa only [Walk.length_cons,(path_length h)] using hl.symm

variable [Fintype V]

def branch (c n : V) : Finset V := Finset.univ.filter (fun z=>z≠c ∧ (next h) c z=n)
lemma mem_branch {c n z : V} : z∈(branch h) c n ↔ z≠c ∧ (next h) c z=n := by
  simp only [branch,Finset.mem_filter,Finset.mem_univ,true_and]
lemma branch_adj {c n z : V} (hz : z∈(branch h) c n) : G.Adj c n := by
  obtain ⟨hz,hn⟩ := (mem_branch h).mp hz
  simpa only [hn] using (next_adj h) hz.symm
lemma branch_closed {c n x y : V} (hx : x∈(branch h) c n) (hy : y≠c) (e : G.Adj x y) :
    y∈(branch h) c n := by
  obtain ⟨hx,hn⟩ := (mem_branch h).mp hx
  exact (mem_branch h).mpr ⟨hy,((next_adjacent h) hx.symm hy.symm e).symm.trans hn⟩

lemma distance_step {c n z : V} (e : G.Adj c n) :
    G.dist n z + (if z∈(branch h) c n then 2 else 0)=G.dist c z+1 := by
  by_cases hb : z∈(branch h) c n
  · rw [if_pos hb]
    obtain ⟨hz,hn⟩ := (mem_branch h).mp hb
    have hd := (dist_next h) hz.symm
    rw [hn] at hd
    omega
  · rw [if_neg hb,Nat.add_zero]
    by_cases hz : z=c
    · subst z
      rw [SimpleGraph.dist_self,dist_eq_one_iff_adj.mpr e.symm]
    · apply (dist_not_next h) e
      intro hn
      exact hb ((mem_branch h).mpr ⟨hz,hn⟩)

def potential (w : V → ℕ) (c : V) : ℕ := ∑ z,w z*G.dist c z
lemma potential_step (w : V → ℕ) {c n : V} (e : G.Adj c n) :
    (potential (G:=G)) w n+2*(∑ z∈(branch h) c n,w z)=(potential (G:=G)) w c+∑ z,w z := by
  have hi (z : V) : w z*G.dist n z+(if z∈(branch h) c n then 2*w z else 0)=
      w z*G.dist c z+w z := by
    have hh := congrArg (fun t : ℕ=>w z*t) (distance_step h (z:=z) e)
    split_ifs at hh ⊢ <;> nlinarith only [hh]
  have hs := Finset.sum_congr (s₁:=Finset.univ) rfl (fun z _=>hi z)
  simp only [Finset.sum_add_distrib] at hs
  have hif : (∑ z,if z∈(branch h) c n then 2*w z else 0)=2*(∑ z∈(branch h) c n,w z) := by
    rw [←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.mul_sum]
  rw [hif] at hs
  exact hs

/-- A finite tree has a weighted centroid: every branch after its deletion
has at most half of the total nonnegative integral weight. Zero weights allowed. -/
theorem exists_centroid (w : V → ℕ) :
    ∃ c : V,∀ n : V,2*(∑ z∈(branch h) c n,w z)≤∑ z,w z := by
  have : Nonempty V := h.connected.nonempty
  obtain ⟨c,_,hc⟩ := Finset.univ.exists_min_image ((potential (G:=G)) w) Finset.univ_nonempty
  refine ⟨c,fun n=>?_⟩
  by_cases he : G.Adj c n
  · have hh := (potential_step h) w he
    have hm := hc n (Finset.mem_univ n)
    omega
  · have hempty : (branch h) c n=∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun z hz=>he ((branch_adj h) hz))
    simp only [hempty,Finset.sum_empty,Nat.mul_zero,Nat.zero_le]

end TorsionFreeZeroDivisors.TreeCentroid

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TreeCentroid
open scoped Classical
open SimpleGraph
variable {V : Type} [Fintype V] {G : SimpleGraph V} (h : G.IsTree)

omit [Fintype V] in
lemma next_of_adj {c n : V} (he : G.Adj c n) : next h c n=n := by
  exact (h.isAcyclic.eq_snd_of_adj_start (path_isPath h c n) he (path h c n).end_mem_support).symm

lemma branch_head {c n : V} (he : G.Adj c n) : n∈branch h c n :=
  (mem_branch h).mpr ⟨he.ne',next_of_adj h he⟩

/-- A tree branch has exactly one possible directed edge leaving it. -/
lemma branch_boundary {c n x y : V} (hx : x∈branch h c n) (hy : y∉branch h c n)
    (he : G.Adj x y) : x=n ∧ y=c := by
  have hyc : y=c := by
    by_contra hn
    exact hy (branch_closed h hx hn he)
  subst y
  have hn := (mem_branch h).mp hx
  have heq := next_of_adj h he.symm
  exact ⟨heq.symm.trans hn.2,rfl⟩

lemma branch_walk_boundary {c n x y : V} (hx : x∉branch h c n) (hy : y∈branch h c n)
    (p : G.Walk x y) : n∈p.support := by
  induction p with
  | nil => exact (hx hy).elim
  | @cons x z y e p ih =>
    by_cases hz : z∈branch h c n
    · have he := branch_boundary h hz hx e.symm
      simp only [Walk.support_cons,List.mem_cons]
      exact Or.inr (he.1 ▸ p.start_mem_support)
    · simp only [Walk.support_cons,List.mem_cons]
      exact Or.inr (ih hz hy)

/-- Descendants are defined by the actual branch beyond the parent edge. -/
def descendants (root v : V) : Finset V := branch h (next h v root) v

lemma root_not_descendants {root v : V} (hv : v≠root) : root∉descendants h root v := by
  intro hr
  obtain ⟨hr,hn⟩ := (mem_branch h).mp hr
  have hd := dist_next h hv
  have hd' := dist_next h hr.symm
  rw [hn] at hd'
  omega

lemma self_mem_descendants {root v : V} (hv : v≠root) : v∈descendants h root v :=
  branch_head h (next_adj h hv).symm

lemma descendant_mem_root_path {root v w : V} (hv : v≠root) (hw : w∈descendants h root v) :
    v∈(path h root w).support :=
  branch_walk_boundary h (root_not_descendants h hv) hw (path h root w)

def rootPath (root v : V) : Finset V := (path h root v).support.toFinset
omit [Fintype V] in
lemma root_mem_rootPath (root v : V) : root∈rootPath h root v :=
  List.mem_toFinset.mpr (path h root v).start_mem_support
omit [Fintype V] in
lemma self_mem_rootPath (root v : V) : v∈rootPath h root v :=
  List.mem_toFinset.mpr (path h root v).end_mem_support
omit [Fintype V] in
lemma rootPath_card (root v : V) : (rootPath h root v).card=G.dist root v+1 := by
  rw [rootPath,List.toFinset_card_of_nodup (path_isPath h root v).support_nodup,
    Walk.length_support,path_length]

end TorsionFreeZeroDivisors.TreeCentroid

namespace TorsionFreeZeroDivisors.MapEuler

section
open scoped Classical
open PermutationCycles
variable {O : Type} (σ φ γ : Equiv.Perm O) (hγ : Function.Involutive γ)

/-- Dual edges incident to a specified set of primal vertices. -/
def touchGraph (S : Set (Cycle σ)) : SimpleGraph (Cycle φ) where
  Adj f g := f≠g ∧ ∃ x,cycle φ x=f ∧ cycle φ (γ x)=g ∧
    (cycle σ x∈S ∨ cycle σ (γ x)∈S)
  symm := ⟨by
    rintro f g ⟨hne,x,hx,hy,hS⟩
    refine ⟨hne.symm,γ x,hy,?_,?_⟩
    · rwa [hγ]
    · rw [hγ]
      exact hS.symm⟩
  loopless := ⟨fun _ h=>h.1 rfl⟩

lemma touchGraph_le (S : Set (Cycle σ)) : touchGraph σ φ γ hγ S≤graph φ γ hγ := by
  rintro f g ⟨hne,x,hx,hy,_⟩
  exact ⟨hne,x,hx,hy⟩

lemma touchGraph_contour_step (θ : Equiv.Perm O) (hθ : γ*θ=φ)
    (S : Set (Cycle σ)) (x : O) (hx : cycle σ (θ x)∈S) :
    (touchGraph σ φ γ hγ S).Reachable (cycle φ x) (cycle φ (θ x)) := by
  by_cases he : cycle φ x=cycle φ (θ x)
  · rw [he]
  · have hp : γ (θ x)=φ x := congrArg (fun f : Equiv.Perm O=>f x) hθ
    apply SimpleGraph.Reachable.symm
    apply SimpleGraph.Adj.reachable
    exact ⟨Ne.symm he,θ x,rfl,by rw [hp,cycle_apply],Or.inl hx⟩

variable [Fintype O]
/-- A subtree interval in the primal contour gives actual connectivity through
only those dual edges incident to the subtree. -/
theorem touchGraph_connected_of_contour (θ : Equiv.Perm O) (hθ : γ*θ=φ)
    (hc : Nat.card (Cycle θ)=1) (S : Set (Cycle σ)) (p : O)
    (hout : ∀ x,cycle σ x∈S → cycle σ (θ x)∉S → x=p)
    {x y : O} (hx : cycle σ x∈S) (hy : cycle σ y∈S) :
    (touchGraph σ φ γ hγ S).Reachable (cycle φ x) (cycle φ y) := by
  have hh (z : O) (hz : cycle σ z∈S) := contour_interval_reachable θ
    (sameCycle_of_card_one θ hc) {x | cycle σ x∈S} p hout
    (touchGraph σ φ γ hγ S) (cycle φ)
    (fun x _ h=>touchGraph_contour_step σ φ γ hγ θ hθ S x h) z hz
  exact (hh x hx).symm.trans (hh y hy)

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha) (ht : T.IsTree)

/-- Every rooted tree branch has a unique possible exit in the actual contour. -/
theorem branch_contour_exit {c n : Cycle σ} (he : T.Adj n c) :
    ∃ p : O,∀ x,cycle σ x∈TreeCentroid.branch ht c n →
      cycle σ ((subgraphPair σ α ha T hT*σ) x)∉TreeCentroid.branch ht c n → x=p := by
  have he' : (graph σ (subgraphPair σ α ha T hT)
      (subgraphPair_involutive σ α ha T hT)).Adj n c := by
    rwa [subgraphPair_graph]
  obtain ⟨hne,p,hp,hq⟩ := he'
  have hpn : subgraphPair σ α ha T hT p≠p := fun h=>hne (hp.symm.trans (h ▸ hq))
  refine ⟨σ.symm p,fun x hx hy=>?_⟩
  have hx' : cycle σ (σ x)∈TreeCentroid.branch ht c n := by rwa [cycle_apply]
  have hxn : subgraphPair σ α ha T hT (σ x)≠σ x := by
    intro h
    exact hy (h.symm ▸ hx')
  have hb := TreeCentroid.branch_boundary ht hx' hy
    (subgraphPair_adj σ α ha T hT hxn)
  have heq := subgraphPair_dart_unique σ α ha T hT hxn hpn
    (hb.1.trans hp.symm) (hb.2.trans hq.symm)
  exact σ.injective (heq.trans (σ.apply_symm_apply p).symm)

/-- Literal face connectivity around a primal tree branch in a genus-zero
map, using only cotree edges touching that branch. -/
theorem branch_dual_touch_connected (hz : GenusZero σ α) {c n : Cycle σ}
    (he : T.Adj n c) {x y : O}
    (hx : cycle σ x∈TreeCentroid.branch ht c n)
    (hy : cycle σ y∈TreeCentroid.branch ht c n) :
    (touchGraph σ (α*σ) (α*subgraphPair σ α ha T hT)
      (complement_involutive α _ ha (subgraphPair_involutive σ α ha T hT)
        (subgraphPair_subpairing σ α ha T hT))
      (↑(TreeCentroid.branch ht c n) : Set (Cycle σ))).Reachable
      (cycle (α*σ) x) (cycle (α*σ) y) := by
  obtain ⟨p,hp⟩ := branch_contour_exit σ α ha T hT ht he
  apply touchGraph_connected_of_contour σ (α*σ) (α*subgraphPair σ α ha T hT) _
    (subgraphPair σ α ha T hT*σ) _ (tree_contour_card σ α ha T hT hz ht) _ p hp hx hy
  ext z
  change α (subgraphPair σ α ha T hT (subgraphPair σ α ha T hT (σ z)))=α (σ z)
  rw [subgraphPair_involutive σ α ha T hT]

end

open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)

def supportedRealize (d : (graph σ α ha).Dart) : {x // x∈α.support} :=
  ⟨realizeDart σ α ha d,realizeDart_mem σ α ha d⟩
lemma supportedRealize_injective : Function.Injective (supportedRealize σ α ha) :=
  fun _ _ h=>realizeDart_injective σ α ha (congrArg Subtype.val h)

lemma supportedRealize_surjective (he : 2*Nat.card (graph σ α ha).edgeSet=α.support.card) :
    Function.Surjective (supportedRealize σ α ha) := by
  apply ((Fintype.bijective_iff_injective_and_card (supportedRealize σ α ha)).mpr
    ⟨supportedRealize_injective σ α ha,?_⟩).surjective
  rw [Fintype.card_coe,SimpleGraph.dart_card_eq_twice_card_edges,
    SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card]
  exact he

lemma dart_unique_of_edge_count (he : 2*Nat.card (graph σ α ha).edgeSet=α.support.card)
    {x y : O} (hx : α x≠x) (hy : α y≠y)
    (h₁ : cycle σ x=cycle σ y) (h₂ : cycle σ (α x)=cycle σ (α y)) : x=y := by
  obtain ⟨d,hd⟩ := supportedRealize_surjective σ α ha he ⟨x,Equiv.Perm.mem_support.mpr hx⟩
  obtain ⟨e,he'⟩ := supportedRealize_surjective σ α ha he ⟨y,Equiv.Perm.mem_support.mpr hy⟩
  have hh : realizeDart σ α ha d=x := congrArg Subtype.val hd
  have hq : realizeDart σ α ha e=y := congrArg Subtype.val he'
  have hde : d=e := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · rw [←realizeDart_fst σ α ha d,←realizeDart_fst σ α ha e,hh,hq]
      exact h₁
    · rw [←realizeDart_snd σ α ha d,←realizeDart_snd σ α ha e,hh,hq]
      exact h₂
  exact hh.symm.trans ((congrArg (realizeDart σ α ha) hde).trans hq)

lemma edge_count_of_tree_support (ht : (graph σ α ha).IsTree)
    (hs : α.support.card+2=2*Nat.card (Cycle σ)) :
    2*Nat.card (graph σ α ha).edgeSet=α.support.card := by
  have he := (SimpleGraph.isTree_iff_connected_and_card.mp ht).2
  omega

end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.TreeCentroid
open scoped Classical
open SimpleGraph
variable {V : Type} [Fintype V] {T : SimpleGraph V} (ht : T.IsTree)
    (H : SimpleGraph V) (hH : H≤T) (c n : V) (hn : ¬H.Adj c n)

include hH hn in
lemma branch_mem_iff_adj_of_avoid {x y : V} (he : H.Adj x y) :
    x∈branch ht c n ↔ y∈branch ht c n := by
  constructor
  · intro hx
    by_contra hy
    obtain ⟨rfl,rfl⟩ := branch_boundary ht hx hy (hH he)
    exact hn he.symm
  · intro hy
    by_contra hx
    obtain ⟨rfl,rfl⟩ := branch_boundary ht hy hx (hH he.symm)
    exact hn he

include hH hn in
lemma branch_mem_iff_reachable_of_avoid {x y : V} (hr : H.Reachable x y) :
    x∈branch ht c n ↔ y∈branch ht c n := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons e p ih => exact (branch_mem_iff_adj_of_avoid ht H hH c n hn e).trans ih

end TorsionFreeZeroDivisors.TreeCentroid

namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

lemma touchGraph_avoids_edge (σ φ γ : Equiv.Perm O) (hγ : Function.Involutive γ)
    (he : 2*Nat.card (graph φ γ hγ).edgeSet=γ.support.card)
    (S : Set (Cycle σ)) (d : O)
    (hd : cycle σ d∉S) (hd' : cycle σ (γ d)∉S) :
    ¬(touchGraph σ φ γ hγ S).Adj (cycle φ d) (cycle φ (γ d)) := by
  rintro ⟨hne,x,hx,hy,hS⟩
  have hdn : γ d≠d := fun h=>hne (by rw [h])
  have hxn : γ x≠x := fun h=>hne (hx.symm.trans (by rwa [h] at hy))
  have hxd := dart_unique_of_edge_count φ γ hγ he hxn hdn hx hy
  subst x
  exact hS.elim hd hd'

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

def cotreeSide (d : O) : Finset (Cycle φ) :=
  TreeCentroid.branch htD (cycle φ d) (cycle φ (γ d))

def fundamentalVertices (root : Cycle σ) (d : O) : Finset (Cycle σ) :=
  TreeCentroid.rootPath ht root (cycle σ d) ∪ TreeCentroid.rootPath ht root (cycle σ (α d))

omit [Fintype O] in
lemma root_mem_fundamentalVertices (root : Cycle σ) (d : O) :
    root∈fundamentalVertices σ α T ht root d :=
  Finset.mem_union_left _ (TreeCentroid.root_mem_rootPath ht _ _)

lemma endpoints_not_descendants {root v : Cycle σ} {d : O}
    (hv : v∉fundamentalVertices σ α T ht root d) :
    cycle σ d∉TreeCentroid.descendants ht root v ∧
    cycle σ (γ d)∉TreeCentroid.descendants ht root v := by
  have hvr : v≠root := fun he=>hv (he ▸ root_mem_fundamentalVertices σ α T ht root d)
  have h₁ : cycle σ d∉TreeCentroid.descendants ht root v := by
    intro h
    apply hv
    apply Finset.mem_union_left
    simpa only [TreeCentroid.rootPath,List.mem_toFinset] using
      (TreeCentroid.descendant_mem_root_path ht hvr h)
  have h₂ : cycle σ (α d)∉TreeCentroid.descendants ht root v := by
    intro h
    apply hv
    apply Finset.mem_union_right
    simpa only [TreeCentroid.rootPath,List.mem_toFinset] using
      (TreeCentroid.descendant_mem_root_path ht hvr h)
  refine ⟨h₁,?_⟩
  rcases complement_subpairing α β ha (subgraphPair_subpairing σ α ha T hT) d with h|h
  · rwa [h]
  · rwa [h]

/-- Outside the two actual root paths, all incident faces of a primal vertex
lie on the same side of the deleted cotree edge. -/
theorem outside_fundamental_sameSide {root v : Cycle σ} {d x y : O}
    (hv : v∉fundamentalVertices σ α T ht root d)
    (hx : cycle σ x=v) (hy : cycle σ y=v) :
    cycle φ x∈cotreeSide σ α ha T hT hz ht d ↔
    cycle φ y∈cotreeSide σ α ha T hT hz ht d := by
  have hvr : v≠root := fun he=>hv (he ▸ root_mem_fundamentalVertices σ α T ht root d)
  let S : Set (Cycle σ) := ↑(TreeCentroid.descendants ht root v)
  have hs : v∈S := TreeCentroid.self_mem_descendants ht hvr
  have hh := branch_dual_touch_connected σ α ha T hT ht hz
    (TreeCentroid.next_adj ht hvr) (hx ▸ hs) (hy ▸ hs)
  have he := edge_count_of_tree_support φ γ hγ htD (cotree_support σ α ha T hT hz ht)
  obtain ⟨hd,hd'⟩ := endpoints_not_descendants σ α ha T hT ht hv
  exact TreeCentroid.branch_mem_iff_reachable_of_avoid htD
    (touchGraph σ φ γ hγ S) (touchGraph_le σ φ γ hγ S)
    (cycle φ d) (cycle φ (γ d))
    (touchGraph_avoids_edge σ φ γ hγ he S d hd hd') hh

omit [Fintype O] in
/-- Endpoints of a primal edge have incident occurrences on a common face. -/
lemma edge_common_face (x : O) : cycle φ (σ.symm x)=cycle φ (α x) := by
  have hf := cycle_apply φ (σ.symm x)
  simpa only [Equiv.Perm.mul_apply,Equiv.apply_symm_apply] using hf.symm

/-- The two-root-path vertex set really separates the corresponding dual sides,
including original loops, parallel edges, and tree edges. -/
theorem fundamental_no_crossing {root : Cycle σ} {d : O} {v w : Cycle σ}
    (hv : v∉fundamentalVertices σ α T ht root d)
    (hw : w∉fundamentalVertices σ α T ht root d)
    (he : (graph σ α ha).Adj v w) {x y : O}
    (hx : cycle σ x=v) (hy : cycle σ y=w) :
    cycle φ x∈cotreeSide σ α ha T hT hz ht d ↔
    cycle φ y∈cotreeSide σ α ha T hT hz ht d := by
  obtain ⟨_,z,hzv,hzw⟩ := he
  have hzv' : cycle σ (σ.symm z)=v := by
    rw [←cycle_apply σ (σ.symm z),σ.apply_symm_apply]
    exact hzv
  have h₁ := outside_fundamental_sameSide σ α ha T hT hz ht hv hx hzv'
  have h₂ := outside_fundamental_sameSide σ α ha T hT hz ht hw hzw hy
  rw [edge_common_face σ α z] at h₁
  exact h₁.trans h₂

end TorsionFreeZeroDivisors.MapEuler

end

end OAI
end

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

def homeFace (v : Cycle σ) : Cycle φ := cycle φ (Quotient.out v)

omit [Fintype O] in
lemma home_cycle (v : Cycle σ) : cycle σ (Quotient.out v)=v := Quotient.out_eq v

def vertexSide (active : Finset (Cycle σ)) (d : O) : Finset (Cycle σ) :=
  active.filter (fun v=>homeFace σ α v∈cotreeSide σ α ha T hT hz ht d)

def centralDeleted (active : Finset (Cycle σ)) (root : Cycle σ) (c : Cycle φ) (d : O) :
    Finset (Cycle σ) :=
  active.filter (fun v=>homeFace σ α v=c ∧ v∈fundamentalVertices σ α T ht root d)

def pressure (active : Finset (Cycle σ)) (root : Cycle σ) (c : Cycle φ) (d : O) :
    Finset (Cycle σ) :=
  vertexSide σ α ha T hT hz ht active d ∪ centralDeleted σ α T ht active root c d

lemma pressure_subset (active : Finset (Cycle σ)) (root : Cycle σ) (c : Cycle φ) (d : O) :
    pressure σ α ha T hT hz ht active root c d⊆active :=
  Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)

lemma pressure_cover (active : Finset (Cycle σ)) (root : Cycle σ) (c : Cycle φ) :
    active⊆(members φ c).biUnion (pressure σ α ha T hT hz ht active root c) := by
  intro v hv
  by_cases he : homeFace σ α v=c
  · refine Finset.mem_biUnion.mpr ⟨Quotient.out v,(mem_members φ).mpr he,?_⟩
    apply Finset.mem_union_right
    refine Finset.mem_filter.mpr ⟨hv,he,?_⟩
    apply Finset.mem_union_left
    rw [home_cycle]
    exact TreeCentroid.self_mem_rootPath ht root v
  · have hn := TreeCentroid.next_adj htD (Ne.symm he)
    obtain ⟨_,d,hd,hd'⟩ := hn
    refine Finset.mem_biUnion.mpr ⟨d,(mem_members φ).mpr hd,?_⟩
    apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨hv,?_⟩
    change homeFace σ α v∈TreeCentroid.branch htD (cycle φ d) (cycle φ (γ d))
    rw [hd,hd']
    exact (TreeCentroid.mem_branch htD).mpr ⟨he,rfl⟩

/-- A weighted centroid face and at most three boundary occurrences force one
fundamental separator to remove or put on its small side at least one third
of the active vertices. Active vertices have unit cost; all others have zero. -/
theorem triangular_dart (active : Finset (Cycle σ)) (root : Cycle σ)
    (htri : ∀ c : Cycle φ,(members φ c).card≤3) :
    ∃ c : Cycle φ,∃ d∈members φ c,
      2*(vertexSide σ α ha T hT hz ht active d).card≤active.card ∧
      active.card≤3*(pressure σ α ha T hT hz ht active root c d).card := by
  let weight : Cycle φ→ℕ := fun c=>(active.filter (fun v=>homeFace σ α v=c)).card
  have hsum : ∑ c,weight c=active.card := by
    simpa only [weight,Finset.mem_univ,Finset.filter_true] using
      (Finset.sum_card_fiberwise_eq_card_filter active Finset.univ (homeFace σ α))
  obtain ⟨c,hc⟩ := TreeCentroid.exists_centroid htD weight
  obtain ⟨d,hd,hm⟩ := (members φ c).exists_max_image
    (fun d=>(pressure σ α ha T hT hz ht active root c d).card) (members_nonempty φ c)
  refine ⟨c,d,hd,?_,?_⟩
  · have hh := hc (cycle φ (γ d))
    rw [hsum] at hh
    have hf := Finset.sum_card_fiberwise_eq_card_filter active
      (cotreeSide σ α ha T hT hz ht d) (homeFace σ α)
    have hdc := (mem_members φ).mp hd
    change ∑ f∈cotreeSide σ α ha T hT hz ht d,weight f=
      (vertexSide σ α ha T hT hz ht active d).card at hf
    unfold cotreeSide at hf
    rw [hdc] at hf
    rwa [←hf]
  · have hb := (Finset.card_le_card (pressure_cover σ α ha T hT hz ht active root c)).trans
      (Finset.card_biUnion_le)
    have hm' := Finset.sum_le_sum (fun x hx=>hm x hx)
    have ht' := htri c
    simp only [Finset.sum_const,smul_eq_mul] at hm'
    exact hb.trans (hm'.trans (Nat.mul_le_mul_right _ ht'))

/-- The opposite retained side of a fundamental cut is disjoint from its
pressure set. -/
lemma opposite_disjoint_pressure (active : Finset (Cycle σ)) (root : Cycle σ)
    (c : Cycle φ) (d : O) :
    Disjoint (active.filter (fun v=>v∉fundamentalVertices σ α T ht root d ∧
      homeFace σ α v∉cotreeSide σ α ha T hT hz ht d))
      (pressure σ α ha T hT hz ht active root c d) := by
  apply Finset.disjoint_left.mpr
  intro v hv hp
  obtain ⟨_,hvC,hvS⟩ := Finset.mem_filter.mp hv
  rcases Finset.mem_union.mp hp with hp|hp
  · exact hvS (Finset.mem_filter.mp hp).2
  · exact hvC (Finset.mem_filter.mp hp).2.2

/-- The literal two-root-path separator balances both retained sides in a
triangular genus-zero map. This is the sharp bounded-radius crux; no planar
embedding or separator theorem is imported. -/
theorem triangular_balanced_fundamental (active : Finset (Cycle σ)) (root : Cycle σ)
    (htri : ∀ c : Cycle φ,(members φ c).card≤3) :
    ∃ d : O,
      3*(active.filter (fun v=>v∉fundamentalVertices σ α T ht root d ∧
        homeFace σ α v∈cotreeSide σ α ha T hT hz ht d)).card≤2*active.card ∧
      3*(active.filter (fun v=>v∉fundamentalVertices σ α T ht root d ∧
        homeFace σ α v∉cotreeSide σ α ha T hT hz ht d)).card≤2*active.card := by
  obtain ⟨c,d,_,hsmall,hlarge⟩ := triangular_dart σ α ha T hT hz ht active root htri
  refine ⟨d,?_,?_⟩
  · have hsub : active.filter (fun v=>v∉fundamentalVertices σ α T ht root d ∧
        homeFace σ α v∈cotreeSide σ α ha T hT hz ht d)⊆
        vertexSide σ α ha T hT hz ht active d := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2.2⟩
    have hh := Finset.card_le_card hsub
    omega
  · have hsub : (active.filter (fun v=>v∉fundamentalVertices σ α T ht root d ∧
        homeFace σ α v∉cotreeSide σ α ha T hT hz ht d)) ∪
        pressure σ α ha T hT hz ht active root c d⊆active :=
      Finset.union_subset (Finset.filter_subset _ _)
        (pressure_subset σ α ha T hT hz ht active root c d)
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (opposite_disjoint_pressure σ α ha T hT hz ht active root c d)] at hh
    omega

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

/-- Each coned face is the actual three-cycle old--center--radial. -/
def faceRaw : Dart O → O
  | .inl x=>x
  | .inr (x,false)=>φ x
  | .inr (x,true)=>x
omit [Fintype O] in
lemma faceRaw_invariant (x : Dart O) : faceRaw σ α (ψ x)=faceRaw σ α x := by
  rcases x with x|⟨x,b⟩
  · rfl
  · cases b
    · rfl
    · exact (α*σ).apply_symm_apply x

def faces : Cycle ψ→O := PermutationCycles.lift ψ (faceRaw σ α) (faceRaw_invariant σ α)
omit [Fintype O] in
lemma face_cycle_center (x : O) : cycle ψ (center x)=cycle ψ (old x) := cycle_apply ψ (old x)
omit [Fintype O] in
lemma face_cycle_radial (x : O) : cycle ψ (radial x)=cycle ψ (old (φ x)) :=
  (cycle_apply ψ (radial x)).symm
lemma faces_left_inverse : Function.LeftInverse (fun x=>cycle ψ (old x)) (faces σ α) := by
  intro f
  obtain ⟨x,rfl⟩ := cycle_surjective ψ f
  rcases x with x|⟨x,b⟩
  · rfl
  · cases b
    · exact (face_cycle_radial σ α x).symm
    · exact (face_cycle_center σ α x).symm

def faceEquiv : Cycle ψ≃O :=
  ⟨faces σ α,fun x=>cycle ψ (old x),faces_left_inverse σ α,fun _=>rfl⟩

lemma face_members (x : O) : members ψ (cycle ψ (old x))={old x,center x,radial ((α*σ).symm x)} := by
  ext y
  rw [mem_members]
  constructor
  · intro hy
    have hh := congrArg (faceEquiv σ α) hy
    rcases y with y|⟨y,b⟩
    · change y=x at hh
      subst y
      exact Finset.mem_insert_self _ _
    · cases b
      · change φ y=x at hh
        have he : y=(α*σ).symm x := (α*σ).injective (hh.trans ((α*σ).apply_symm_apply x).symm)
        subst y
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      · change y=x at hh
        subst y
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · intro hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl|rfl|rfl
    · rfl
    · exact face_cycle_center σ α x
    · rw [face_cycle_radial,(α*σ).apply_symm_apply]

lemma triangular (f : Cycle ψ) : (members ψ f).card=3 := by
  obtain ⟨x,rfl⟩ := (faceEquiv σ α).symm.surjective f
  change (members ψ (cycle ψ (old x))).card=3
  rw [face_members]
  simp [old,center,radial]

lemma vertex_count : Nat.card (Cycle ρ)=Nat.card (Cycle σ)+Nat.card (Cycle φ) := by
  rw [Nat.card_congr (vertexEquiv σ α),Nat.card_sum]
lemma face_count : Nat.card (Cycle ψ)=Nat.card O := Nat.card_congr (faceEquiv σ α)

end

open scoped Classical
open PermutationCycles MapEuler
variable {O : Type} (σ α : Equiv.Perm O)
local notation "ρ" => rotation σ α
local notation "π" => pairing α
local notation "φ" => α*σ

lemma component_face (x : O) : component σ α ((α*σ) x)=component σ α x :=
  (component_partner σ α (σ x)).trans (component_rotation σ α x)

def componentRaw : Dart O → Component σ α
  | .inl x=>component σ α x
  | .inr (x,_)=>component σ α x
lemma componentRaw_rotation (x : Dart O) : componentRaw σ α (ρ x)=componentRaw σ α x := by
  rcases x with x|⟨x,b⟩
  · rfl
  · cases b
    · exact component_rotation σ α x
    · change component σ α ((α*σ).symm x)=component σ α x
      rw [←component_face σ α ((α*σ).symm x),(α*σ).apply_symm_apply]
lemma componentRaw_pairing (x : Dart O) : componentRaw σ α (π x)=componentRaw σ α x := by
  rcases x with x|⟨x,b⟩
  · exact component_partner σ α x
  · cases b <;> rfl

def componentForward : Component ρ π→ Component σ α :=
  MapEuler.lift ρ π (componentRaw σ α) (componentRaw_rotation σ α) (componentRaw_pairing σ α)
lemma component_radial (x : O) : component ρ π (radial x)=component ρ π (old x) :=
  component_rotation ρ π (old x)
lemma component_center (x : O) : component ρ π (center x)=component ρ π (old x) :=
  (component_partner ρ π (radial x)).trans (component_radial σ α x)
lemma component_old_rotation (x : O) : component ρ π (old (σ x))=component ρ π (old x) :=
  (component_rotation ρ π (radial x)).trans (component_radial σ α x)
lemma component_old_pairing (x : O) : component ρ π (old (α x))=component ρ π (old x) :=
  component_partner ρ π (old x)
def componentInverse : Component σ α→ Component ρ π :=
  MapEuler.lift σ α (fun x=>component ρ π (old x))
    (component_old_rotation σ α) (component_old_pairing σ α)

def componentEquiv : Component ρ π≃Component σ α where
  toFun := componentForward σ α
  invFun := componentInverse σ α
  left_inv := by
    intro c
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    rcases x with x|⟨x,b⟩
    · rfl
    · cases b
      · exact (component_radial σ α x).symm
      · exact (component_center σ α x).symm
  right_inv := by
    intro c
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    rfl

variable [Fintype O]

def supportEquiv : ↥(pairing α).support ≃ ↥α.support ⊕ (O×Bool) where
  toFun x := match x with
    | ⟨.inl y,hy⟩=>.inl ⟨y,by
        apply Equiv.Perm.mem_support.mpr
        intro he
        exact Equiv.Perm.mem_support.mp hy (congrArg old he)⟩
    | ⟨.inr y,_⟩=>.inr y
  invFun
    | .inl y=>⟨old y.val,by
        apply Equiv.Perm.mem_support.mpr
        intro he
        exact Equiv.Perm.mem_support.mp y.property (Sum.inl.inj he)⟩
    | .inr (x,b)=>⟨.inr (x,b),by
        apply Equiv.Perm.mem_support.mpr
        cases b <;> simp [pairing,Equiv.sumCongr_apply,Equiv.prodCongr_apply]⟩
  left_inv := by
    rintro ⟨x,hx⟩
    rcases x with x|⟨x,b⟩ <;> rfl
  right_inv := by
    rintro (x|⟨x,b⟩) <;> rfl

lemma support_count : (pairing α).support.card=α.support.card+2*Nat.card O := by
  have h := Fintype.card_congr (supportEquiv α)
  simp only [Fintype.card_coe,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool] at h
  rw [←Nat.card_eq_fintype_card] at h
  omega

omit [Fintype O] in
lemma support_card_nat {X : Type} [Fintype X] [DecidableEq X] (p : Equiv.Perm X) :
    p.support.card=Nat.card {x : X // p x≠x} := by
  rw [←Fintype.card_coe,←Nat.card_eq_fintype_card]
  exact Nat.card_congr
    ⟨fun x=>⟨x.val,Equiv.Perm.mem_support.mp x.property⟩,
     fun x=>⟨x.val,Equiv.Perm.mem_support.mpr x.property⟩,
     fun _=>rfl,fun _=>rfl⟩

/-- Coning all literal face cycles preserves Euler genus zero, with no
geometric embedding premise and without identifying or deleting any original vertex. -/
theorem genusZero (hz : GenusZero σ α) : GenusZero ρ π := by
  classical
  have hv := vertex_count σ α
  have hf := face_count σ α
  have hc := Nat.card_congr (componentEquiv σ α)
  have hs := support_count α
  unfold GenusZero at hz ⊢
  rw [hv,hf,hc]
  simp only [support_card_nat] at hz hs ⊢
  omega

end TorsionFreeZeroDivisors.ConedMap

end

end OAI
end

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
lemma oldVertex_injective : Function.Injective (oldVertex σ α) :=
  (vertexEquiv σ α).symm.injective.comp Sum.inl_injective
lemma old_ne_center (v : Cycle σ) (f : Cycle (α*σ)) : oldVertex σ α v≠centerVertex σ α f := by
  intro he
  have hh := (vertexEquiv σ α).symm.injective he
  exact Sum.inl_ne_inr hh

@[simp] lemma oldVertex_cycle (x : O) : oldVertex σ α (cycle σ x)=cycle ρ (old x) := rfl
@[simp] lemma centerVertex_cycle (x : O) : centerVertex σ α (cycle (α*σ) x)=cycle ρ (center x) := rfl

lemma old_adj {v w : Cycle σ} (he : (G).Adj v w) : (G').Adj (oldVertex σ α v) (oldVertex σ α w) := by
  obtain ⟨hne,x,hx,hy⟩ := he
  refine ⟨(oldVertex_injective σ α).ne hne,old x,?_,?_⟩
  · rw [←oldVertex_cycle,hx]
  · rw [pairing_old,←oldVertex_cycle,hy]

lemma radial_adj (x : O) : (G').Adj (oldVertex σ α (cycle σ x))
    (centerVertex σ α (cycle (α*σ) x)) := by
  refine ⟨old_ne_center σ α _ _,radial x,?_,?_⟩
  · rw [vertex_radial,oldVertex_cycle]
  · rw [pairing_radial,centerVertex_cycle]

def oldHom : G →g G' := ⟨oldVertex σ α,fun h=>old_adj σ α ha h⟩

theorem connected (hc : (G).Connected) : (G').Connected := by
  apply connected_of_component_card_one
  rw [Nat.card_congr (componentEquiv σ α)]
  exact component_card_one_of_connected σ α ha hc

lemma old_distance_le (hc : (G).Connected) (v w : Cycle σ) :
    (G').dist (oldVertex σ α v) (oldVertex σ α w)≤(G).dist v w := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist v w
  have hh := (G').dist_le (p.map (oldHom σ α ha))
  rwa [SimpleGraph.Walk.length_map,hp] at hh

lemma center_distance_le (hc : (G).Connected) (root : Cycle σ) (r : ℕ)
    (hr : ∀ v,(G).dist root v≤r) (f : Cycle (α*σ)) :
    (G').dist (oldVertex σ α root) (centerVertex σ α f)≤r+1 := by
  obtain ⟨x,rfl⟩ := cycle_surjective (α*σ) f
  have hh := (connected σ α ha hc).dist_triangle
    (u:=oldVertex σ α root) (v:=oldVertex σ α (cycle σ x))
    (w:=centerVertex σ α (cycle (α*σ) x))
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr (radial_adj σ α ha x)] at hh
  exact hh.trans (Nat.add_le_add_right ((old_distance_le σ α ha hc _ _).trans (hr _)) _)

def oldEmbedding : Cycle σ ↪ Cycle ρ := ⟨oldVertex σ α,oldVertex_injective σ α⟩
def liftSet (s : Finset (Cycle σ)) : Finset (Cycle ρ) := s.map (oldEmbedding σ α)
lemma liftSet_card (s : Finset (Cycle σ)) : (liftSet σ α s).card=s.card := Finset.card_map _
lemma old_mem_liftSet (s : Finset (Cycle σ)) (v : Cycle σ) :
    oldVertex σ α v∈liftSet σ α s ↔ v∈s := Finset.mem_map' (oldEmbedding σ α)
lemma center_not_liftSet (s : Finset (Cycle σ)) (f : Cycle (α*σ)) :
    centerVertex σ α f∉liftSet σ α s := by
  intro hf
  obtain ⟨v,_,hv⟩ := Finset.mem_map.mp hf
  exact old_ne_center σ α v f hv

/-- Distances to zero-cost auxiliary centers incur one extra step, but all
original vertices remain within the original radius. -/
theorem distance_cost (hc : (G).Connected) (root : Cycle σ) (r : ℕ)
    (hr : ∀ v,(G).dist root v≤r) (v : Cycle ρ) :
    (G').dist (oldVertex σ α root) v + (if v∈liftSet σ α Finset.univ then 1 else 0)≤r+1 := by
  obtain ⟨q,rfl⟩ := (vertexEquiv σ α).symm.surjective v
  rcases q with v|f
  · change (G').dist (oldVertex σ α root) (oldVertex σ α v)+
      (if oldVertex σ α v∈liftSet σ α Finset.univ then 1 else 0)≤r+1
    rw [if_pos ((old_mem_liftSet σ α Finset.univ v).mpr (Finset.mem_univ _))]
    exact Nat.add_le_add_right ((old_distance_le σ α ha hc root v).trans (hr v)) _
  · change (G').dist (oldVertex σ α root) (centerVertex σ α f)+
      (if centerVertex σ α f∈liftSet σ α Finset.univ then 1 else 0)≤r+1
    rw [if_neg (center_not_liftSet σ α Finset.univ f),Nat.add_zero]
    exact center_distance_le σ α ha hc root r hr f

end TorsionFreeZeroDivisors.ConedMap

/-! A literal breadth-first spanning tree, with its distances and radius
preserved. This is the rooted tree used in the sharp planar separator. -/
namespace TorsionFreeZeroDivisors.BFSTree
open scoped Classical
open SimpleGraph
variable {V : Type} (G : SimpleGraph V) (hc : G.Connected) (root : V)

include hc in
lemma exists_parent (v : V) (hv : v≠root) :
    ∃ u,G.Adj v u ∧ G.dist u root+1=G.dist v root := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist v root
  cases p with
  | nil => exact (hv rfl).elim
  | @cons v u root h p =>
    refine ⟨u,h,?_⟩
    have h₁ := G.dist_le p
    have h₂ := hc.dist_triangle (u:=v) (v:=u) (w:=root)
    rw [G.dist_eq_one_iff_adj.mpr h] at h₂
    simp only [Walk.length_cons] at hp
    omega

def parent (v : V) : V := if hv : v=root then root else (exists_parent G hc root v hv).choose
lemma parent_adj (v : V) (hv : v≠root) : G.Adj v (parent G hc root v) := by
  rw [parent,dif_neg hv]
  exact (exists_parent G hc root v hv).choose_spec.1
lemma parent_dist (v : V) (hv : v≠root) :
    G.dist (parent G hc root v) root+1=G.dist v root := by
  rw [parent,dif_neg hv]
  exact (exists_parent G hc root v hv).choose_spec.2
lemma parent_ne (v : V) (hv : v≠root) : parent G hc root v≠v := (parent_adj G hc root v hv).ne'

def tree : SimpleGraph V where
  Adj v w := (v≠root ∧ parent G hc root v=w) ∨ (w≠root ∧ parent G hc root w=v)
  symm := ⟨fun _ _ h=>h.elim Or.inr Or.inl⟩
  loopless := ⟨fun v h=>h.elim (fun h=>parent_ne G hc root v h.1 h.2)
    (fun h=>parent_ne G hc root v h.1 h.2)⟩

lemma tree_le : tree G hc root≤G := by
  intro v w h
  rcases h with ⟨hv,h⟩|⟨hw,h⟩
  · rw [←h]
    exact parent_adj G hc root v hv
  · rw [←h]
    exact (parent_adj G hc root w hw).symm

lemma exists_tree_walk (v : V) :
    ∃ p : (tree G hc root).Walk v root,p.length=G.dist v root := by
  generalize hn : G.dist v root=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v=root
    · subst v
      exact ⟨Walk.nil,by simp only [Walk.length_nil,dist_self] at hn ⊢; omega⟩
    · have hp := parent_dist G hc root v hv
      obtain ⟨p,hl⟩ := ih (G.dist (parent G hc root v) root) (by omega)
        (parent G hc root v) rfl
      have he : (tree G hc root).Adj v (parent G hc root v) := Or.inl ⟨hv,rfl⟩
      exact ⟨Walk.cons he p,by rw [Walk.length_cons,hl];omega⟩

lemma connected : (tree G hc root).Connected := by
  have : Nonempty V := ⟨root⟩
  refine ⟨fun v w=>?_⟩
  obtain ⟨p,_⟩ := exists_tree_walk G hc root v
  obtain ⟨q,_⟩ := exists_tree_walk G hc root w
  exact ⟨p.append q.reverse⟩

/-- All root distances are unchanged, not merely bounded by an abstract height. -/
theorem dist_root (v : V) : (tree G hc root).dist v root=G.dist v root := by
  apply Nat.le_antisymm
  · obtain ⟨p,hp⟩ := exists_tree_walk G hc root v
    rw [←hp]
    exact (tree G hc root).dist_le p
  · exact Reachable.dist_anti (tree_le G hc root) ((connected G hc root) v root)

def parentEdge (v : {v : V // v≠root}) : (tree G hc root).edgeSet :=
  ⟨s(v.val,parent G hc root v.val),Or.inl ⟨v.property,rfl⟩⟩
lemma parentEdge_surjective : Function.Surjective (parentEdge G hc root) := by
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ v w =>
    rcases he with ⟨hv,h⟩|⟨hw,h⟩
    · refine ⟨⟨v,hv⟩,Subtype.ext ?_⟩
      change s(v,parent G hc root v)=s(v,w)
      rw [h]
    · refine ⟨⟨w,hw⟩,Subtype.ext ?_⟩
      change s(w,parent G hc root w)=s(v,w)
      rw [h,Sym2.eq_swap]

variable [Fintype V]
/-- The parent edges form an actual spanning tree of the original graph. -/
theorem isTree : (tree G hc root).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨connected G hc root,?_⟩
  have hl := Fintype.card_le_of_surjective _ (parentEdge_surjective G hc root)
  have hr := (connected G hc root).card_vert_le_card_edgeSet_add_one
  have hcard : Fintype.card {v : V // v≠root}+1=Fintype.card V := by
    simpa only [Fintype.card_subtype_compl,Fintype.card_unique] using
      Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨root⟩)
  rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card] at hl hcard
  omega

end TorsionFreeZeroDivisors.BFSTree

namespace TorsionFreeZeroDivisors.TreeCentroid
open scoped Classical
open SimpleGraph
variable {V : Type} [Fintype V] {T : SimpleGraph V} (ht : T.IsTree)

omit [Fintype V] in
lemma rootPath_cost (budget : Finset V) (root v : V) (r : ℕ)
    (hr : T.dist root v+(if v∈budget then 1 else 0)≤r+1) :
    ((rootPath ht root v)∩budget).card≤r+1 := by
  by_cases hv : v∈budget
  · have hh := Finset.card_le_card (show rootPath ht root v∩budget⊆rootPath ht root v from Finset.inter_subset_left)
    rw [rootPath_card] at hh
    rw [if_pos hv] at hr
    omega
  · have hs : rootPath ht root v∩budget⊆(rootPath ht root v).erase v := by
      intro x hx
      obtain ⟨hx,hxb⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_erase.mpr ⟨fun he=>hv (he ▸ hxb),hx⟩
    have hh := Finset.card_le_card hs
    rw [Finset.card_erase_of_mem (self_mem_rootPath ht root v),rootPath_card] at hh
    rw [if_neg hv] at hr
    omega

omit [Fintype V] in
/-- Zero-cost face centers may be introduced for triangulation without losing
the sharp original-vertex bound. Only original vertices are charged. -/
theorem two_root_paths_cost (budget : Finset V) (root v w : V) (r : ℕ)
    (hroot : root∈budget)
    (hv : T.dist root v+(if v∈budget then 1 else 0)≤r+1)
    (hw : T.dist root w+(if w∈budget then 1 else 0)≤r+1) :
    ((rootPath ht root v∪rootPath ht root w)∩budget).card≤2*r+1 := by
  have h₁ := rootPath_cost ht budget root v r hv
  have h₂ := rootPath_cost ht budget root w r hw
  have hp : 0<((rootPath ht root v∩budget)∩(rootPath ht root w∩budget)).card :=
    Finset.card_pos.mpr ⟨root,Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨root_mem_rootPath ht root v,hroot⟩,
       Finset.mem_inter.mpr ⟨root_mem_rootPath ht root w,hroot⟩⟩⟩
  rw [Finset.union_inter_distrib_right]
  have hh := Finset.card_union_add_card_inter (rootPath ht root v∩budget) (rootPath ht root w∩budget)
  omega

end TorsionFreeZeroDivisors.TreeCentroid

namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

/-- The exact bounded-radius separator on a genus-zero rotation map.  The
partition balances any chosen set of unit-weight vertices.  In particular the
root is charged once, so deleting a contracted root saves one unit. -/
theorem radius_separator (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (hz : GenusZero σ α) (hc : (graph σ α ha).Connected)
    (root : Cycle σ) (r : ℕ) (hr : ∀ v,(graph σ α ha).dist root v≤r)
    (active : Finset (Cycle σ)) :
    ∃ cut side : Finset (Cycle σ), root∈cut ∧ cut.card≤2*r+1 ∧
      (cut.erase root).card≤2*r ∧
      3*(active.filter (fun v=>v∉cut ∧ v∈side)).card≤2*active.card ∧
      3*(active.filter (fun v=>v∉cut ∧ v∉side)).card≤2*active.card ∧
      ∀ v w,v∉cut→w∉cut→(graph σ α ha).Adj v w→(v∈side↔w∈side) := by
  classical
  let ρ := ConedMap.rotation σ α
  let π := ConedMap.pairing α
  have hπ := ConedMap.pairing_involutive α ha
  let g := graph ρ π hπ
  have hgc : g.Connected := ConedMap.connected σ α ha hc
  let e := ConedMap.oldEmbedding σ α
  let u := e root
  let T := BFSTree.tree g hgc u
  have hT : T≤g := BFSTree.tree_le g hgc u
  have ht : T.IsTree := BFSTree.isTree g hgc u
  have hz' : GenusZero ρ π := ConedMap.genusZero σ α hz
  have htri : ∀ c : Cycle (π*ρ),(members (π*ρ) c).card≤3 :=
    fun c=>(ConedMap.triangular σ α c).le
  let a := ConedMap.liftSet σ α active
  obtain ⟨d,h₁,h₂⟩ := triangular_balanced_fundamental ρ π hπ T hT hz' ht a u htri
  let F := fundamentalVertices ρ π T ht u d
  let D := cotreeSide ρ π hπ T hT hz' ht d
  let cut := Finset.univ.filter (fun v=>e v∈F)
  let side := Finset.univ.filter (fun v=>homeFace ρ π (e v)∈D)
  have hcut (v : Cycle σ) : v∈cut↔e v∈F := by simp only [cut,Finset.mem_filter,Finset.mem_univ,true_and]
  have hside (v : Cycle σ) : v∈side↔homeFace ρ π (e v)∈D := by
    simp only [side,Finset.mem_filter,Finset.mem_univ,true_and]
  have hroot : root∈cut := (hcut root).mpr (root_mem_fundamentalVertices ρ π T ht u d)
  let budget : Finset (Cycle ρ) := ConedMap.liftSet σ α Finset.univ
  have hcost (v : Cycle ρ) : T.dist u v+(if v∈budget then 1 else 0)≤r+1 := by
    rw [SimpleGraph.dist_comm,BFSTree.dist_root,SimpleGraph.dist_comm]
    exact ConedMap.distance_cost σ α ha hc root r hr v
  have hmap : cut.map e=F∩ConedMap.liftSet σ α Finset.univ := by
    ext v
    simp only [Finset.mem_map,Finset.mem_inter,ConedMap.liftSet,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨(hcut x).mp hx,⟨x,rfl⟩⟩
    · rintro ⟨hv,x,rfl⟩
      exact ⟨x,(hcut x).mpr hv,rfl⟩
  have hcard : cut.card≤2*r+1 := by
    rw [←Finset.card_map (f:=e),hmap]
    have hh := TreeCentroid.two_root_paths_cost ht budget
      u (cycle ρ d) (cycle ρ (π d)) r
      ((ConedMap.old_mem_liftSet σ α Finset.univ root).mpr (Finset.mem_univ _)) (by convert hcost (cycle ρ d) using 1; congr 2) (by convert hcost (cycle ρ (π d)) using 1; congr 2)
    convert hh using 1
    congr 1
    ext v
    simp only [F,budget,fundamentalVertices,Finset.mem_inter,Finset.mem_union,TreeCentroid.rootPath,List.mem_toFinset]
  have hfilter (p : Cycle ρ→Prop) [DecidablePred p] :
      (active.filter (fun v=>p (e v))).card=(a.filter p).card := by
    rw [←Finset.card_map (f:=e)]
    congr 1
    ext v
    simp only [Finset.mem_map,Finset.mem_filter]
    constructor
    · rintro ⟨x,⟨hx,hp⟩,rfl⟩
      exact ⟨Finset.mem_map.mpr ⟨x,hx,rfl⟩,hp⟩
    · rintro ⟨hv,hp⟩
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hv
      exact ⟨x,⟨hx,hp⟩,rfl⟩
  refine ⟨cut,side,hroot,hcard,?_,?_,?_,?_⟩
  · rw [Finset.card_erase_of_mem hroot]
    omega
  · have he : active.filter (fun v=>v∉cut ∧ v∈side)=
        active.filter (fun v=>e v∉F ∧ homeFace ρ π (e v)∈D) := by
      ext v
      simp only [Finset.mem_filter,hcut,hside]
    rw [he,hfilter (fun v=>v∉F ∧ homeFace ρ π v∈D),←ConedMap.liftSet_card σ α active]
    exact h₁
  · have he : active.filter (fun v=>v∉cut ∧ v∉side)=
        active.filter (fun v=>e v∉F ∧ homeFace ρ π (e v)∉D) := by
      ext v
      simp only [Finset.mem_filter,hcut,hside]
    rw [he,hfilter (fun v=>v∉F ∧ homeFace ρ π v∉D),←ConedMap.liftSet_card σ α active]
    exact h₂
  · intro v w hv hw he
    rw [hside,hside]
    exact fundamental_no_crossing ρ π hπ T hT hz' ht
      (fun h=>hv ((hcut v).mpr h)) (fun h=>hw ((hcut w).mpr h))
      (ConedMap.old_adj σ α ha he) (home_cycle ρ (e v)) (home_cycle ρ (e w))

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

/-- The restricted dart system realizes precisely the induced simple graph. -/
def graphIso : graph (rotation σ S) (pairing σ α hi S) (pairing_involutive σ α hi S) ≃g
    (graph σ α hi).induce S where
  toEquiv := vertexEquiv σ S
  map_rel_iff' := by
    intro v w
    constructor
    · intro he
      change (graph σ α hi).Adj (vertexEquiv σ S v).val (vertexEquiv σ S w).val at he
      obtain ⟨hne,x,hx,hy⟩ := he
      have hxS : cycle σ x∈S := hx ▸ (vertexEquiv σ S v).property
      have hyS : cycle σ (α x)∈S := hy ▸ (vertexEquiv σ S w).property
      refine ⟨fun h=>hne (congrArg (fun c=>(vertexEquiv σ S c).val) h),⟨x,hxS⟩,?_,?_⟩
      · apply (vertexEquiv σ S).injective
        exact Subtype.ext hx
      · apply (vertexEquiv σ S).injective
        apply Subtype.ext
        change cycle σ (internalPair σ α hi S x)=(vertexEquiv σ S w).val
        rw [internalPair,inducedPair_apply,if_pos ⟨hxS,hyS⟩]
        exact hy
    · rintro ⟨hne,x,hx,hy⟩
      change (graph σ α hi).Adj (vertexEquiv σ S v).val (vertexEquiv σ S w).val
      have hvw : (vertexEquiv σ S v).val≠(vertexEquiv σ S w).val :=
        fun h=>hne ((vertexEquiv σ S).injective (Subtype.ext h))
      have hx' := congrArg (fun c=>(vertexEquiv σ S c).val) hx
      have hy' := congrArg (fun c=>(vertexEquiv σ S c).val) hy
      change cycle σ x.val=(vertexEquiv σ S v).val at hx'
      change cycle σ (internalPair σ α hi S x.val)=(vertexEquiv σ S w).val at hy'
      have hh : cycle σ (α x.val)∈S := by
        by_contra hn
        rw [internalPair,inducedPair_apply,if_neg (fun h=>hn h.2)] at hy'
        exact hvw (hx'.symm.trans hy')
      rw [internalPair,inducedPair_apply,if_pos ⟨x.property,hh⟩] at hy'
      exact ⟨hvw,x.val,hx',hy'⟩

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
lemma treePair_involutive : Function.Involutive β := by
  intro x
  by_cases hx : P x
  · have h := congrArg Subtype.val (subgraphPair_involutive s a hai T hT ⟨x,hx⟩)
    change β (β (⟨x,hx⟩ : {x : O // P x}))=x
    rw [treePair_inside,treePair_inside]
    exact h
  · rw [treePair_outside σ α hi B T hT x hx,treePair_outside σ α hi B T hT x hx]
lemma treePair_subpairing (x : O) : β x=x ∨ β x=α x := by
  by_cases hx : P x
  · have he := subgraphPair_subpairing s a hai T hT ⟨x,hx⟩
    rcases he with he|he
    · exact Or.inl ((treePair_inside σ α hi B T hT ⟨x,hx⟩).trans (congrArg Subtype.val he))
    · have h := (treePair_inside σ α hi B T hT ⟨x,hx⟩).trans (congrArg Subtype.val he)
      change β x=MapRestrict.internalPair σ α hi B x at h
      rw [MapRestrict.internalPair,inducedPair_apply] at h
      split_ifs at h
      · exact Or.inr h
      · exact Or.inl h
  · exact Or.inl (treePair_outside σ α hi B T hT x hx)

def rotation : Equiv.Perm O := β*σ
def pairing : Equiv.Perm O := α*β
local notation "ρ" => rotation σ α hi B T hT
local notation "γ" => pairing σ α hi B T hT
lemma pairing_involutive : Function.Involutive γ :=
  complement_involutive α β hi (treePair_involutive σ α hi B T hT) (treePair_subpairing σ α hi B T hT)

theorem genusZero (hz : GenusZero σ α) : GenusZero ρ γ := by
  have h := (genusZero_dual (α*σ) γ (pairing_involutive σ α hi B T hT)).mp
    (genusZero_complement_dual σ α β hi (treePair_involutive σ α hi B T hT)
      (treePair_subpairing σ α hi B T hT) hz)
  rw [show γ*(α*σ)=ρ from complement_face σ α β hi (treePair_involutive σ α hi B T hT)
    (treePair_subpairing σ α hi B T hT)] at h
  exact h

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
lemma quotient_surjective : Function.Surjective q := by
  intro v
  obtain ⟨x,rfl⟩ := cycle_surjective ρ v
  exact ⟨cycle σ x,rfl⟩

def labelRaw (x : O) : Option (Cycle σ) := if P x then none else some (cycle σ x)
lemma labelRaw_invariant (x : O) : labelRaw σ B (ρ x)=labelRaw σ B x := by
  by_cases hx : P x
  · rw [labelRaw,if_pos ((rotation_invariant σ α hi B T hT x).mpr hx),labelRaw,if_pos hx]
  · have he : ρ x=σ x := treePair_outside σ α hi B T hT (σ x) (by simpa only [cycle_apply] using hx)
    simp only [he,labelRaw,cycle_apply]
def label : Cycle ρ→Option (Cycle σ) :=
  PermutationCycles.lift ρ (labelRaw σ B) (labelRaw_invariant σ α hi B T hT)
lemma label_quotient (v : Cycle σ) : label σ α hi B T hT (q v)=if v∈B then none else some v := by
  obtain ⟨x,rfl⟩ := cycle_surjective σ v
  rfl

lemma quotient_eq_iff (v w : Cycle σ) : q v=q w ↔ v=w ∨ (v∈B ∧ w∈B) := by
  constructor
  · intro h
    have he := congrArg (label σ α hi B T hT) h
    rw [label_quotient,label_quotient] at he
    by_cases hv : v∈B <;> by_cases hw : w∈B <;> simp only [hv,hw,ite_true,ite_false] at he
    · exact Or.inr ⟨hv,hw⟩
    · contradiction
    · contradiction
    · exact Or.inl (Option.some.inj he)
  · rintro (rfl|⟨hv,hw⟩)
    · rfl
    · obtain ⟨x,rfl⟩ := cycle_surjective σ v
      obtain ⟨y,rfl⟩ := cycle_surjective σ w
      exact inside_cycle_eq σ α hi B T hT hz ht hv hw

include hz ht in
lemma cycle_treePair (x : O) : cycle ρ (β x)=cycle ρ x := by
  by_cases hx : P x
  · exact inside_cycle_eq σ α hi B T hT hz ht ((treePair_invariant σ α hi B T hT x).mpr hx) hx
  · rw [treePair_outside σ α hi B T hT x hx]

/-- Every original edge either contracts to a vertex or is an actual edge. -/
lemma quotient_adj {v w : Cycle σ} (he : (graph σ α hi).Adj v w) :
    q v=q w ∨ (graph ρ γ (pairing_involutive σ α hi B T hT)).Adj (q v) (q w) := by
  by_cases h : q v=q w
  · exact Or.inl h
  · obtain ⟨_,x,rfl,rfl⟩ := he
    refine Or.inr ⟨h,β x,cycle_treePair σ α hi B T hT hz ht x,?_⟩
    change cycle ρ (α (β (β x)))=cycle ρ (α x)
    rw [treePair_involutive σ α hi B T hT x]

/-- No new nonloop adjacency is introduced by the literal contraction. -/
lemma adj_lift {v w : Cycle ρ} (he : (graph ρ γ (pairing_involutive σ α hi B T hT)).Adj v w) :
    ∃ x y,(graph σ α hi).Adj x y ∧ q x=v ∧ q y=w := by
  obtain ⟨hne,x,rfl,rfl⟩ := he
  have hb : β x=x := by
    rcases treePair_subpairing σ α hi B T hT x with h|h
    · exact h
    · have hf : γ x=x := (congrArg α h).trans (hi x)
      exact (hne (congrArg (cycle ρ) hf).symm).elim
  have he : γ x=α x := congrArg α hb
  refine ⟨cycle σ x,cycle σ (α x),⟨?_,x,rfl,rfl⟩,rfl,?_⟩
  · intro h
    exact hne ((congrArg q h).trans (congrArg (cycle ρ) he.symm))
  · exact congrArg (cycle ρ) he.symm

end TorsionFreeZeroDivisors.MapContract

namespace TorsionFreeZeroDivisors.GraphBall
open scoped Classical
open SimpleGraph
variable {V : Type} (G : SimpleGraph V) (hc : G.Connected) (root : V) (N : ℕ)
def vertices : Set V := {v | G.dist v root≤N}
def rootVertex : vertices G root N := ⟨root,by simp [vertices]⟩

include hc
lemma exists_walk (v : vertices G root N) :
    ∃ p : (G.induce (vertices G root N)).Walk v (rootVertex G root N), p.length=G.dist v.val root := by
  generalize hn : G.dist v.val root=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v.val=root
    · have he : v=rootVertex G root N := Subtype.ext hv
      subst v
      exact ⟨Walk.nil,by simpa only [Walk.length_nil,rootVertex,dist_self] using hn⟩
    · let u := BFSTree.parent G hc root v.val
      have hd : G.dist u root+1=G.dist v.val root := BFSTree.parent_dist G hc root v.val hv
      have hu : u∈vertices G root N := by have hh := v.property;change G.dist v.val root≤N at hh;exact by dsimp [vertices];omega
      obtain ⟨p,hp⟩ := ih (G.dist u root) (by omega) ⟨u,hu⟩ rfl
      have he : (G.induce (vertices G root N)).Adj v ⟨u,hu⟩ := BFSTree.parent_adj G hc root v.val hv
      refine ⟨p.cons he,?_⟩
      rw [Walk.length_cons,hp,hd,hn]

lemma connected : (G.induce (vertices G root N)).Connected := by
  apply (connected_iff_exists_forall_reachable (G.induce (vertices G root N))).mpr
  refine ⟨rootVertex G root N,fun v=>?_⟩
  obtain ⟨p,_⟩ := exists_walk G hc root N v
  exact p.reverse.reachable

lemma dist_root (v : vertices G root N) :
    (G.induce (vertices G root N)).dist v (rootVertex G root N)=G.dist v.val root := by
  apply Nat.le_antisymm
  · obtain ⟨p,hp⟩ := exists_walk G hc root N v
    rw [←hp]
    exact (G.induce (vertices G root N)).dist_le p
  · obtain ⟨p,hp⟩ := (connected G hc root N).exists_walk_length_eq_dist v (rootVertex G root N)
    let f : G.induce (vertices G root N) →g G := ⟨Subtype.val,fun h=>h⟩
    have h := G.dist_le (p.map f)
    change G.dist v.val root≤(p.map f).length at h
    simpa only [Walk.length_map,hp] using h

end TorsionFreeZeroDivisors.GraphBall

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GraphQuotient
open SimpleGraph
variable {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) (q : V→W)
    (hq : ∀ v w,G.Adj v w→q v=q w ∨ H.Adj (q v) (q w))
include hq in
lemma reachable {v w : V} (h : G.Reachable v w) : H.Reachable (q v) (q w) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.rfl
  | @cons v u w h p ih =>
    rcases hq v u h with h|h
    · exact h ▸ ih
    · exact h.reachable.trans ih

include hq in
lemma connected (hs : Function.Surjective q) (hc : G.Connected) : H.Connected := by
  have : Nonempty W := hc.nonempty.map q
  refine ⟨fun v w=>?_⟩
  obtain ⟨v,rfl⟩ := hs v
  obtain ⟨w,rfl⟩ := hs w
  exact reachable G H q hq (hc v w)

include hq in
lemma distance_sub (hc : G.Connected) (hcH : H.Connected) (root : V) (N : ℕ)
    (hb : ∀ v,G.dist v root≤N→q v=q root) (v : V) :
    H.dist (q v) (q root)≤G.dist v root-N := by
  generalize hn : G.dist v root=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : G.dist v root≤N
    · rw [hb v hv,dist_self]
      exact Nat.zero_le _
    · have hv' : v≠root := by rintro rfl;simp only [dist_self] at hv;omega
      obtain ⟨u,hu,hd⟩ := BFSTree.exists_parent G hc root v hv'
      have hi := ih (G.dist u root) (by omega) u rfl
      rcases hq v u hu with he|he
      · rw [he]
        omega
      · have hh := hcH.dist_triangle (u:=q v) (v:=q u) (w:=q root)
        rw [H.dist_eq_one_iff_adj.mpr he] at hh
        omega
end TorsionFreeZeroDivisors.GraphQuotient

namespace TorsionFreeZeroDivisors.PlanarMap

section
open scoped Classical
open PermutationCycles MapEuler
variable {V : Type} (G : SimpleGraph V)
/-- A concrete finite rotation map, with its exact Euler equality and an
isomorphism to the represented simple graph. Loops and parallel darts are
allowed; no abstract planar-minor or separator hypotheses are used. -/
structure Model where
  Dart : Type
  [finiteDart : Fintype Dart]
  rotation : Equiv.Perm Dart
  pairing : Equiv.Perm Dart
  involutive : Function.Involutive pairing
  genus : GenusZero rotation pairing
  iso : graph rotation pairing involutive ≃g G
attribute [instance] Model.finiteDart
variable {G}

def Model.induced (M : Model G) (S : Set V) : Model (G.induce S) where
  Dart := {x : M.Dart // M.iso (cycle M.rotation x)∈S}
  rotation := MapRestrict.rotation M.rotation {v | M.iso v∈S}
  pairing := MapRestrict.pairing M.rotation M.pairing M.involutive {v | M.iso v∈S}
  involutive := MapRestrict.pairing_involutive M.rotation M.pairing M.involutive {v | M.iso v∈S}
  genus := MapRestrict.induced_genusZero M.rotation M.pairing M.involutive {v | M.iso v∈S} M.genus
  iso := (MapRestrict.graphIso M.rotation M.pairing M.involutive {v | M.iso v∈S}).trans
    (M.iso.induce ⟨fun _ h=>h,M.iso.injective.injOn,fun v hv=>by
      refine ⟨M.iso.symm v,?_,M.iso.apply_symm_apply v⟩
      change M.iso (M.iso.symm v)∈S
      simpa only [M.iso.apply_symm_apply] using hv⟩)

/-- Sharp radius separation transported along the actual graph isomorphism. -/
theorem Model.radius_separator (M : Model G) (hc : G.Connected) (root : V) (r : ℕ)
    (hr : ∀ v,G.dist root v≤r) (active : Finset V) :
    ∃ cut side : Finset V,root∈cut ∧ cut.card≤2*r+1 ∧ (cut.erase root).card≤2*r ∧
      3*(active.filter (fun v=>v∉cut ∧ v∈side)).card≤2*active.card ∧
      3*(active.filter (fun v=>v∉cut ∧ v∉side)).card≤2*active.card ∧
      ∀ v w,v∉cut→w∉cut→G.Adj v w→(v∈side↔w∈side) := by
  let e := M.iso.toEquiv
  let A := active.map e.symm.toEmbedding
  obtain ⟨C,D,hrC,hC,hCe,h₁,h₂,hsep⟩ := MapEuler.radius_separator M.rotation M.pairing
    M.involutive M.genus (M.iso.connected_iff.mpr hc) (e.symm root) r (by
      intro v
      obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist root (e v)
      have hh := (graph M.rotation M.pairing M.involutive).dist_le (p.map M.iso.symm.toHom)
      change (graph M.rotation M.pairing M.involutive).dist (e.symm root) (e.symm (e v))≤(p.map M.iso.symm.toHom).length at hh
      rw [e.symm_apply_apply,SimpleGraph.Walk.length_map,hp] at hh
      exact hh.trans (hr (e v))) A
  let cut := C.map e.toEmbedding
  let side := D.map e.toEmbedding
  have hcut (v : V) : v∈cut↔e.symm v∈C := by simp only [cut,Finset.mem_map_equiv]
  have hside (v : V) : v∈side↔e.symm v∈D := by simp only [side,Finset.mem_map_equiv]
  have hroot : root∈cut := (hcut root).mpr hrC
  have hcard : cut.card=C.card := Finset.card_map _
  have hfilter (p : Cycle M.rotation→Prop) [DecidablePred p] :
      (active.filter (fun v=>p (e.symm v))).card=(A.filter p).card := by
    rw [←Finset.card_map (f:=e.symm.toEmbedding)]
    congr 1
    ext v
    simp only [Finset.mem_map,Finset.mem_filter]
    constructor
    · rintro ⟨x,⟨hx,hp⟩,rfl⟩
      exact ⟨Finset.mem_map.mpr ⟨x,hx,rfl⟩,hp⟩
    · rintro ⟨hv,hp⟩
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hv
      exact ⟨x,⟨hx,hp⟩,rfl⟩
  refine ⟨cut,side,hroot,by omega,?_,?_,?_,?_⟩
  · rw [Finset.card_erase_of_mem hroot,hcard,←Finset.card_erase_of_mem hrC]
    exact hCe
  · have he : active.filter (fun v=>v∉cut ∧ v∈side)=active.filter (fun v=>e.symm v∉C ∧ e.symm v∈D) := by
      ext v;simp only [Finset.mem_filter,hcut,hside]
    rw [he,hfilter (fun v=>v∉C ∧ v∈D)]
    simpa only [A,Finset.card_map] using h₁
  · have he : active.filter (fun v=>v∉cut ∧ v∉side)=active.filter (fun v=>e.symm v∉C ∧ e.symm v∉D) := by
      ext v;simp only [Finset.mem_filter,hcut,hside]
    rw [he,hfilter (fun v=>v∉C ∧ v∉D)]
    simpa only [A,Finset.card_map] using h₂
  · intro v w hv hw he
    rw [hside,hside]
    exact hsep (e.symm v) (e.symm w) (fun h=>hv ((hcut v).mpr h))
      (fun h=>hw ((hcut w).mpr h)) (M.iso.symm.toHom.map_adj he)

end

open scoped Classical
open PermutationCycles MapEuler
variable {V : Type} (G : SimpleGraph V) (B : Set V)
structure Contraction where
  Vertex : Type
  [finiteVertex : Fintype Vertex]
  graph : SimpleGraph Vertex
  model : Model graph
  quotient : V→Vertex
  surjective : Function.Surjective quotient
  eq_iff : ∀ v w,quotient v=quotient w↔v=w ∨ (v∈B ∧ w∈B)
  adj : ∀ v w,G.Adj v w→quotient v=quotient w ∨ graph.Adj (quotient v) (quotient w)
  lift_adj : ∀ v w,graph.Adj v w→∃ x y,G.Adj x y ∧ quotient x=v ∧ quotient y=w
attribute [instance] Contraction.finiteVertex
variable {G B}

/-- A connected induced set is contracted by choosing its literal spanning
submatching and replacing the rotations by the contour permutation. -/
def Model.contract (M : Model G) (hB : (G.induce B).Connected) : Contraction G B := by
  let S : Set (Cycle M.rotation) := {v | M.iso v∈B}
  let s := MapRestrict.rotation M.rotation S
  let a := MapRestrict.pairing M.rotation M.pairing M.involutive S
  let hi := MapRestrict.pairing_involutive M.rotation M.pairing M.involutive S
  have hc : (graph s a hi).Connected := ((M.induced B).iso.connected_iff).mpr hB
  let T := hc.exists_isTree_le.choose
  have hT : T≤graph s a hi := hc.exists_isTree_le.choose_spec.1
  have ht : T.IsTree := hc.exists_isTree_le.choose_spec.2
  let ρ := MapContract.rotation M.rotation M.pairing M.involutive S T hT
  let γ := MapContract.pairing M.rotation M.pairing M.involutive S T hT
  let hγ := MapContract.pairing_involutive M.rotation M.pairing M.involutive S T hT
  let q := MapContract.quotient M.rotation M.pairing M.involutive S T hT M.genus ht
  refine { Vertex := Cycle ρ
           graph := graph ρ γ hγ
           model := {
             Dart := M.Dart
             rotation := ρ
             pairing := γ
             involutive := hγ
             genus := MapContract.genusZero M.rotation M.pairing M.involutive S T hT M.genus
             iso := .refl }
           quotient := fun v=>q (M.iso.symm v)
           surjective := (MapContract.quotient_surjective M.rotation M.pairing M.involutive S T hT M.genus ht).comp M.iso.symm.surjective
           eq_iff := ?_
           adj := ?_
           lift_adj := ?_ }
  · intro v w
    rw [MapContract.quotient_eq_iff]
    simp only [S,Set.mem_ofPred_eq,M.iso.apply_symm_apply,M.iso.symm.injective.eq_iff]
  · intro v w h
    exact MapContract.quotient_adj M.rotation M.pairing M.involutive S T hT M.genus ht (M.iso.symm.toHom.map_adj h)
  · intro v w h
    obtain ⟨x,y,hxy,hx,hy⟩ := MapContract.adj_lift M.rotation M.pairing M.involutive S T hT M.genus ht h
    exact ⟨M.iso x,M.iso y,M.iso.toHom.map_adj hxy,by simpa only [M.iso.symm_apply_apply] using hx,by simpa only [M.iso.symm_apply_apply] using hy⟩

end TorsionFreeZeroDivisors.PlanarMap

namespace TorsionFreeZeroDivisors.CutTransfer
open scoped Classical
variable {V W : Type} [Fintype V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    (A : Finset V) (f : V→W)

theorem pullback (hinj : Set.InjOn f A)
    (hmap : ∀ v∈A,∀ w∈A,G.Adj v w→f v=f w ∨ H.Adj (f v) (f w))
    (C D budget : Finset W) (K : ℕ) (hcost : budget.card≤K)
    (hbudget : ∀ v∈A,f v∈C→f v∈budget)
    (h₁ : 3*((A.image f).filter (fun v=>v∉C ∧ v∈D)).card≤2*(A.image f).card)
    (h₂ : 3*((A.image f).filter (fun v=>v∉C ∧ v∉D)).card≤2*(A.image f).card)
    (hsep : ∀ v w,v∉C→w∉C→H.Adj v w→(v∈D↔w∈D)) :
    ∃ cut side : Finset V,cut⊆A ∧ cut.card≤K ∧
      3*(A.filter (fun v=>v∉cut ∧ v∈side)).card≤2*A.card ∧
      3*(A.filter (fun v=>v∉cut ∧ v∉side)).card≤2*A.card ∧
      ∀ v∈A,∀ w∈A,v∉cut→w∉cut→G.Adj v w→(v∈side↔w∈side) := by
  let cut := A.filter (fun v=>f v∈C)
  let side := Finset.univ.filter (fun v=>f v∈D)
  have hsub : cut⊆A := Finset.filter_subset _ _
  have hcut {v : V} (hv : v∈A) : v∈cut↔f v∈C := by simp only [cut,Finset.mem_filter,hv,true_and]
  have hside (v : V) : v∈side↔f v∈D := by simp only [side,Finset.mem_filter,Finset.mem_univ,true_and]
  have hcard : (A.image f).card=A.card := Finset.card_image_of_injOn hinj
  have hfilter (p : W→Prop) [DecidablePred p] :
      ((A.image f).filter p).card=(A.filter (fun v=>p (f v))).card := by
    rw [Finset.filter_image]
    exact Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))
  have hfirst : (A.image f).filter (fun v=>v∉C ∧ v∈D) =
      (A.filter (fun v=>v∉cut ∧ v∈side)).image f := by
    rw [Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro v hv
    simp only [hcut hv,hside]
  have hsecond : (A.image f).filter (fun v=>v∉C ∧ v∉D) =
      (A.filter (fun v=>v∉cut ∧ v∉side)).image f := by
    rw [Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro v hv
    simp only [hcut hv,hside]
  have himage : cut.image f⊆budget := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    exact hbudget x (hsub hx) ((hcut (hsub hx)).mp hx)
  refine ⟨cut,side,hsub,?_,?_,?_,?_⟩
  · have he : (cut.image f).card=cut.card := Finset.card_image_of_injOn (hinj.mono hsub)
    rw [←he]
    exact (Finset.card_le_card himage).trans hcost
  · rw [hfirst,Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _)),hcard] at h₁
    exact h₁
  · rw [hsecond,Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _)),hcard] at h₂
    exact h₂
  · intro v hv w hw hvC hwC he
    rw [hside,hside]
    rcases hmap v hv w hw he with h|h
    · rw [h]
    · exact hsep (f v) (f w) (fun h=>hvC ((hcut hv).mpr h)) (fun h=>hwC ((hcut hw).mpr h)) h
end TorsionFreeZeroDivisors.CutTransfer

namespace TorsionFreeZeroDivisors.PlanarMap
open scoped Classical
open SimpleGraph
variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- Root-saving radius separation after literal connected lower-ball
contraction. Only vertices of `active` are charged or retained. -/
theorem Model.annular_separator (M : Model G) (hc : G.Connected) (root : V)
    (lo hi : ℕ) (active : Finset V)
    (hA : ∀ v∈active,lo<G.dist v root ∧ G.dist v root≤hi) :
    ∃ cut side : Finset V,cut⊆active ∧ cut.card≤2*(hi-lo) ∧
      3*(active.filter (fun v=>v∉cut ∧ v∈side)).card≤2*active.card ∧
      3*(active.filter (fun v=>v∉cut ∧ v∉side)).card≤2*active.card ∧
      ∀ v∈active,∀ w∈active,v∉cut→w∉cut→G.Adj v w→(v∈side↔w∈side) := by
  let S := GraphBall.vertices G root hi
  let H := G.induce S
  let r : S := GraphBall.rootVertex G root hi
  have hH : H.Connected := GraphBall.connected G hc root hi
  let B := GraphBall.vertices H r lo
  let J := (M.induced S).contract (GraphBall.connected H hH r lo)
  let q := J.quotient
  have hJ : J.graph.Connected := GraphQuotient.connected H J.graph q J.adj J.surjective hH
  have hcollapse (v : S) (hv : H.dist v r≤lo) : q v=q r :=
    (J.eq_iff v r).mpr (Or.inr ⟨hv,by change H.dist r r≤lo;simp only [SimpleGraph.dist_self];omega⟩)
  have hdist (v : S) : J.graph.dist (q v) (q r)≤G.dist v.val root-lo := by
    have h := GraphQuotient.distance_sub H J.graph q J.adj hH hJ r lo hcollapse v
    have he : H.dist v r=G.dist v.val root := GraphBall.dist_root G hc root hi v
    rwa [he] at h
  have hr (w : J.Vertex) : J.graph.dist (q r) w≤hi-lo := by
    obtain ⟨v,rfl⟩ := J.surjective w
    rw [SimpleGraph.dist_comm]
    exact (hdist v).trans (Nat.sub_le_sub_right v.property lo)
  let f : V→J.Vertex := fun v=>if hv:v∈S then q ⟨v,hv⟩ else q r
  have hf (v : V) (hv : v∈S) : f v=q ⟨v,hv⟩ := dif_pos hv
  have hAS {v : V} (hv : v∈active) : v∈S := (hA v hv).2
  have hout (v : V) (hv : v∈active) : (⟨v,hAS hv⟩ : S)∉B := by
    change ¬H.dist ⟨v,hAS hv⟩ r≤lo
    rw [GraphBall.dist_root G hc root hi]
    exact Nat.not_le.mpr (hA v hv).1
  have hinj : Set.InjOn f active := by
    intro v hv w hw he
    rw [hf v (hAS hv),hf w (hAS hw)] at he
    rcases (J.eq_iff _ _).mp he with he|he
    · exact congrArg Subtype.val he
    · exact (hout v hv he.1).elim
  have hroot (v : V) (hv : v∈active) : f v≠q r := by
    intro he
    rw [hf v (hAS hv)] at he
    rcases (J.eq_iff _ _).mp he with he|he
    · have hd : H.dist (⟨v,hAS hv⟩ : S) r=0 := by rw [he,SimpleGraph.dist_self]
      have hh : (⟨v,hAS hv⟩ : S)∈B := by change H.dist _ r≤lo;omega
      exact hout v hv hh
    · exact hout v hv he.1
  have hmap : ∀ v∈active,∀ w∈active,G.Adj v w→f v=f w ∨ J.graph.Adj (f v) (f w) := by
    intro v hv w hw he
    rw [hf v (hAS hv),hf w (hAS hw)]
    exact J.adj ⟨v,hAS hv⟩ ⟨w,hAS hw⟩ he
  obtain ⟨C,D,_,_,hCe,h₁,h₂,hsep⟩ := J.model.radius_separator hJ (q r) (hi-lo) hr (active.image f)
  exact CutTransfer.pullback G J.graph active f hinj hmap C D (C.erase (q r)) (2*(hi-lo)) hCe
    (fun v hv h=>Finset.mem_erase.mpr ⟨hroot v hv,h⟩) h₁ h₂ hsep

/-- The uncontracted alternative, needed when the selected lower level is
negative. Its extra root vertex fits strictly within the level-gap budget. -/
theorem Model.ball_separator (M : Model G) (hc : G.Connected) (root : V)
    (hi : ℕ) (active : Finset V) (hA : ∀ v∈active,G.dist v root≤hi) :
    ∃ cut side : Finset V,cut⊆active ∧ cut.card≤2*hi+1 ∧
      3*(active.filter (fun v=>v∉cut ∧ v∈side)).card≤2*active.card ∧
      3*(active.filter (fun v=>v∉cut ∧ v∉side)).card≤2*active.card ∧
      ∀ v∈active,∀ w∈active,v∉cut→w∉cut→G.Adj v w→(v∈side↔w∈side) := by
  let S := GraphBall.vertices G root hi
  let : DecidableEq S := Classical.decEq S
  let H := G.induce S
  let r : S := GraphBall.rootVertex G root hi
  have hH : H.Connected := GraphBall.connected G hc root hi
  let f : V→S := fun v=>if hv:v∈S then ⟨v,hv⟩ else r
  have hf (v : V) (hv : v∈S) : f v=⟨v,hv⟩ := dif_pos hv
  have hinj : Set.InjOn f active := by
    intro v hv w hw he
    rw [hf v (hA v hv),hf w (hA w hw)] at he
    exact congrArg Subtype.val he
  have hmap : ∀ v∈active,∀ w∈active,G.Adj v w→f v=f w ∨ H.Adj (f v) (f w) := by
    intro v hv w hw he
    rw [hf v (hA v hv),hf w (hA w hw)]
    exact Or.inr he
  have hr (v : S) : H.dist r v≤hi := by
    rw [SimpleGraph.dist_comm,GraphBall.dist_root G hc root hi]
    exact v.property
  obtain ⟨C,D,_,hC,_,h₁,h₂,hsep⟩ := (M.induced S).radius_separator hH r hi hr (active.image f)
  exact CutTransfer.pullback G H active f hinj hmap C D C (2*hi+1) hC (fun _ _ h=>h) h₁ h₂ hsep

end TorsionFreeZeroDivisors.PlanarMap

/-!
Sharp level-selection arithmetic for the planar-separator dependency.  The
profile is the actual number of vertices on each integer BFS level.  No planar
separator is assumed or concluded here: the bounded-radius geometric step is
separate.
-/
namespace TorsionFreeZeroDivisors.SeparatorLevels
open scoped BigOperators

private theorem twice_sum_succ (h : ℕ) :
    (∑ k ∈ Finset.range h, 2*(k+1)) = h*(h+1) := by
  induction h with
  | zero => simp
  | succ h ih => rw [Finset.sum_range_succ,ih]; ring

/-- The exact discrete triangle under a minimum level cost. -/
theorem triangular_bound (m : ℕ) (c : ℕ → ℕ)
    (hc : ∀ k < m/2, m ≤ c k + 2*(k+1)) :
    m^2 ≤ 4*(∑ k ∈ Finset.range (m/2), c k) + 2*m := by
  have hs : (m/2)*m ≤ (∑ k ∈ Finset.range (m/2),c k)+(m/2)*(m/2+1) := by
    have hh := Finset.sum_le_sum (s:=Finset.range (m/2))
      (fun k hk => hc k (Finset.mem_range.mp hk))
    simpa only [Finset.sum_add_distrib,twice_sum_succ,Finset.sum_const,
      Finset.card_range,smul_eq_mul] using hh
  have hr := Nat.mod_add_div m 2
  have hr' := Nat.mod_lt m (by decide : 0<2)
  have : m%2=0 ∨ m%2=1 := by omega
  rcases this with he | he <;> rw [he] at hr <;> nlinarith

theorem exists_minimum (f : ℕ → ℕ) : ∃ k, ∀ j, f k ≤ f j := by
  obtain ⟨m,⟨k,hk⟩,hm⟩ := Nat.lt_wfRel.wf.has_min (Set.range f) ⟨f 0,0,rfl⟩
  refine ⟨k,fun j => ?_⟩
  have hh := hm (f j) ⟨j,rfl⟩
  change ¬ f j < m at hh
  rw [hk]
  omega

/-- A nonnegative integer profile with total mass at most `N` has two levels
whose combined width plus twice their separation is at most `sqrt(8*N)`.
The center level is counted only once in the mass estimate. -/
theorem select (a : ℤ → ℕ) (N : ℕ) (center : ℤ)
    (mass : ∀ s : Finset ℤ, ∑ z ∈ s,a z ≤ N) :
    ∃ kL kR : ℕ,
      (a (center-kL) + a (center+kR) + 2*(kL+kR) : ℝ) ≤
        2*Real.sqrt 2*Real.sqrt N := by
  classical
  obtain ⟨kL,hL⟩ := exists_minimum (fun k=>a (center-k)+2*k)
  obtain ⟨kR,hR⟩ := exists_minimum (fun k=>a (center+k)+2*k)
  let A := a (center-kL)+2*kL
  let B := a (center+kR)+2*kR
  have hA : A ≤ a center := by
    simpa only [sub_zero,Nat.cast_zero,mul_zero,add_zero] using hL 0
  have hB : B ≤ a center := by
    simpa only [add_zero,Nat.cast_zero,mul_zero] using hR 0
  have tA := triangular_bound A (fun k=>a (center-(k+1:ℕ)))
    (fun k _ => hL (k+1))
  have tB := triangular_bound B (fun k=>a (center+(k+1:ℕ)))
    (fun k _ => hR (k+1))
  let left := (Finset.range (A/2)).image (fun k:ℕ=>center-(k+1:ℕ))
  let right := (Finset.range (B/2)).image (fun k:ℕ=>center+(k+1:ℕ))
  have hl : ∀ z ∈ left,z<center := by
    intro z hz
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
    omega
  have hr : ∀ z ∈ right,center<z := by
    intro z hz
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
    omega
  have hlr : Disjoint left right := by
    apply Finset.disjoint_left.mpr
    intro z hzl hzr
    have := hl z hzl
    have := hr z hzr
    omega
  have hc : center ∉ left ∪ right := by
    intro hh
    rcases Finset.mem_union.mp hh with hh|hh
    · exact (lt_irrefl center) (hl center hh)
    · exact (lt_irrefl center) (hr center hh)
  have sal : ∑ z ∈ left,a z = ∑ k ∈ Finset.range (A/2),a (center-(k+1:ℕ)) := by
    apply Finset.sum_image
    intro x _ y _ he
    change center-(x+1:ℕ)=center-(y+1:ℕ) at he
    omega
  have sar : ∑ z ∈ right,a z = ∑ k ∈ Finset.range (B/2),a (center+(k+1:ℕ)) := by
    apply Finset.sum_image
    intro x _ y _ he
    change center+(x+1:ℕ)=center+(y+1:ℕ) at he
    omega
  have hmass := mass (insert center (left ∪ right))
  rw [Finset.sum_insert hc,Finset.sum_union hlr,sal,sar] at hmass
  have hs : A^2+B^2 ≤ 4*N := by nlinarith
  have hs' : (A:ℝ)^2+(B:ℝ)^2 ≤ 4*(N:ℝ) := by exact_mod_cast hs
  have hab : ((A:ℝ)+(B:ℝ))^2 ≤ 8*(N:ℝ) := by nlinarith [sq_nonneg ((A:ℝ)-B)]
  have sqn := Real.sq_sqrt (show (0:ℝ)≤N by positivity)
  have sq2 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hp : (2*Real.sqrt 2*Real.sqrt N)^2=8*(N:ℝ) := by
    calc
      _ = 4*(Real.sqrt 2)^2*(Real.sqrt N)^2 := by ring
      _ = _ := by rw [sqn,sq2]; ring
  have hfinal : (A:ℝ)+B ≤ 2*Real.sqrt 2*Real.sqrt N := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [hp]
    exact hab
  refine ⟨kL,kR,?_⟩
  convert hfinal using 1
  dsimp [A,B]
  push_cast
  ring

end TorsionFreeZeroDivisors.SeparatorLevels

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SeparatorLevels

section
open scoped BigOperators
variable {V : Type*} [Fintype V]

/-- Canonical finite vertex level profile; its mass is not an extra assumption. -/
def profile (level : V → ℤ) (z : ℤ) : ℕ :=
  (Finset.univ.filter (fun v=>level v=z)).card

theorem profile_mass (level : V → ℤ) (s : Finset ℤ) :
    ∑ z ∈ s,profile level z ≤ Fintype.card V := by
  classical
  unfold profile
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

theorem select_vertices (level : V → ℤ) (center : ℤ) :
    ∃ kL kR : ℕ,
      (profile level (center-kL) + profile level (center+kR) + 2*(kL+kR) : ℝ) ≤
        2*Real.sqrt 2*Real.sqrt (Fintype.card V) :=
  select (profile level) _ center (profile_mass level)

/-- A median genuine BFS level, including the empty graph and repeated levels. -/
theorem exists_median (level : V → ℕ) :
    ∃ center : ℕ,
      2*(Finset.univ.filter (fun v=>level v<center)).card ≤ Fintype.card V ∧
      2*(Finset.univ.filter (fun v=>center<level v)).card ≤ Fintype.card V := by
  classical
  let P := fun k => Fintype.card V ≤
    2*(Finset.univ.filter (fun v=>level v≤k)).card
  have hex : ∃ k,P k := by
    refine ⟨Finset.univ.sup level,?_⟩
    have hh : ∀ v,level v ≤ Finset.univ.sup level :=
      fun v=>Finset.le_sup (Finset.mem_univ v)
    simp only [P,Finset.filter_true_of_mem (fun v _ => hh v),Finset.card_univ]
    omega
  let center := Nat.find hex
  have hc : P center := Nat.find_spec hex
  refine ⟨center,?_,?_⟩
  · cases he : center with
    | zero => simp only [Nat.not_lt_zero,Finset.filter_false,Finset.card_empty,mul_zero]
              exact Nat.zero_le _
    | succ k =>
      have hk : k < Nat.find hex := by change k<center;omega
      have hp := Nat.find_min hex hk
      change ¬ P k at hp
      simp only [Nat.lt_succ_iff]
      dsimp [P] at hp
      omega
  · have hparts : (Finset.univ.filter (fun v=>level v≤center)).card+
        (Finset.univ.filter (fun v=>center<level v)).card=Fintype.card V := by
      have hh := Finset.card_filter_add_card_filter_not
        (s:=Finset.univ) (p:=fun v=>level v≤center)
      simpa only [not_le,Finset.card_univ] using hh
    dsimp [P] at hc
    omega

/-- The selected levels are literal finite graph levels, and both exterior
regions already satisfy the stronger half-size bound. -/
theorem selected_levels (level : V → ℕ) :
    ∃ center kL kR : ℕ,
      (profile (fun v=>(level v:ℤ)) ((center:ℤ)-kL) +
       profile (fun v=>(level v:ℤ)) ((center:ℤ)+kR) + 2*(kL+kR) : ℝ) ≤
        2*Real.sqrt 2*Real.sqrt (Fintype.card V) ∧
      2*(Finset.univ.filter (fun v=>(level v:ℤ)<(center:ℤ)-kL)).card ≤ Fintype.card V ∧
      2*(Finset.univ.filter (fun v=>(center:ℤ)+kR<(level v:ℤ))).card ≤ Fintype.card V := by
  classical
  obtain ⟨center,hcl,hcr⟩ := exists_median level
  obtain ⟨kL,kR,hk⟩ := select_vertices (fun v=>(level v:ℤ)) center
  refine ⟨center,kL,kR,hk,?_,?_⟩
  · have hs : (Finset.univ.filter (fun v=>(level v:ℤ)<(center:ℤ)-kL))⊆
        (Finset.univ.filter (fun v=>level v<center)) := by
      intro v hv
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
      omega
    have hh := Finset.card_le_card hs
    omega
  · have hs : (Finset.univ.filter (fun v=>(center:ℤ)+kR<(level v:ℤ)))⊆
        (Finset.univ.filter (fun v=>center<level v)) := by
      intro v hv
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
      omega
    have hh := Finset.card_le_card hs
    omega

end

variable {V : Type*} (G : SimpleGraph V) (root : V)

theorem bfs_step (hconn : G.Connected) {x y : V} (hxy : G.Adj x y) :
    (G.dist root y:ℤ) ≤ (G.dist root x:ℤ)+1 ∧
    (G.dist root x:ℤ) ≤ (G.dist root y:ℤ)+1 := by
  have h₁ := hconn.dist_triangle (u:=root) (v:=x) (w:=y)
  have h₂ := hconn.dist_triangle (u:=root) (v:=y) (w:=x)
  rw [G.dist_eq_one_iff_adj.mpr hxy] at h₁
  rw [G.dist_eq_one_iff_adj.mpr hxy.symm] at h₂
  exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩

end TorsionFreeZeroDivisors.SeparatorLevels

namespace TorsionFreeZeroDivisors.RecursiveSeparator
open scoped Classical
variable {V I : Type} [DecidableEq V] [Fintype I] [DecidableEq I]
    (R : V→V→Prop) (S remove : Finset V) (label : V→I)

def Split.of_fibers (hsub : remove⊆S)
    (hclosed : ∀ x∈S\remove,∀ y∈S\remove,R x y→label x=label y)
    (hsize : ∀ i,3*((S\remove).filter (fun x=>label x=i)).card≤2*S.card)
    (hcost : (remove.card:ℝ)≤2*Real.sqrt 2*Real.sqrt S.card) : Split R S where
  remove := remove
  parts := Finset.univ.image (fun i=>(S\remove).filter (fun x=>label x=i))
  remove_subset := hsub
  cover := by
    ext x
    simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and,id_eq]
    constructor
    · rintro ⟨b,⟨i,rfl⟩,hx⟩
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      exact ⟨(S\remove).filter (fun y=>label y=label x),⟨label x,rfl⟩,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩
  disjoint := by
    intro b hb c hc hbc
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hc
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hi := (Finset.mem_filter.mp hx).2
    have hj := (Finset.mem_filter.mp hy).2
    have he : i=j := hi.symm.trans hj
    exact hbc (by rw [he])
  closed := by
    intro b hb x hx y hy hxy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hx,hi⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hy,(hclosed x hx y hy hxy).symm.trans hi⟩
  size := by
    intro b hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    exact hsize i
  cost := hcost
end TorsionFreeZeroDivisors.RecursiveSeparator

namespace TorsionFreeZeroDivisors.PlanarMap
open scoped Classical
open SeparatorLevels
variable {V : Type} [Fintype V] {G : SimpleGraph V}

theorem Model.connected_split (M : Model G) (hc : G.Connected) :
    Nonempty (RecursiveSeparator.Split G.Adj Finset.univ) := by
  classical
  have : Nonempty V := hc.nonempty
  let root := Classical.ofNonempty (α:=V)
  let level : V→ℕ := fun v=>G.dist v root
  obtain ⟨center,kL,kR,hcost,hbelow,habove⟩ := selected_levels level
  let L : ℤ := (center:ℤ)-kL
  let U : ℤ := (center:ℤ)+kR
  have hLU : L≤U := by dsimp [L,U];omega
  let A := Finset.univ.filter (fun v=>L<(level v:ℤ) ∧ (level v:ℤ)<U)
  have hA (v : V) : v∈A↔L<(level v:ℤ) ∧ (level v:ℤ)<U := by simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
  have hex : ∃ cut side : Finset V,cut⊆A ∧ cut.card≤2*(kL+kR) ∧
      3*(A.filter (fun v=>v∉cut ∧ v∈side)).card≤2*A.card ∧
      3*(A.filter (fun v=>v∉cut ∧ v∉side)).card≤2*A.card ∧
      ∀ v∈A,∀ w∈A,v∉cut→w∉cut→G.Adj v w→(v∈side↔w∈side) := by
    by_cases hk : kL≤center
    · obtain ⟨C,D,hs,hcC,h₁,h₂,hsep⟩ := M.annular_separator hc root (center-kL) (center+kR) A (by
        intro v hv
        have hh := (hA v).mp hv
        change center-kL<level v ∧ level v≤center+kR
        dsimp [L,U] at hh
        omega)
      refine ⟨C,D,hs,?_,h₁,h₂,hsep⟩
      have he : center+kR-(center-kL)=kL+kR := by omega
      rwa [he] at hcC
    · obtain ⟨C,D,hs,hcC,h₁,h₂,hsep⟩ := M.ball_separator hc root (center+kR) A (by
        intro v hv
        have hh := (hA v).mp hv
        change level v≤center+kR
        dsimp [U] at hh
        omega)
      exact ⟨C,D,hs,by omega,h₁,h₂,hsep⟩
  obtain ⟨C,D,hCA,hC,h₁,h₂,hsep⟩ := hex
  let low := Finset.univ.filter (fun v=>(level v:ℤ)<L)
  let high := Finset.univ.filter (fun v=>U<(level v:ℤ))
  let eL := Finset.univ.filter (fun v=>(level v:ℤ)=L)
  let eU := Finset.univ.filter (fun v=>(level v:ℤ)=U)
  let remove := eL∪eU∪C
  have hremove (v : V) : v∈remove↔(level v:ℤ)=L ∨ (level v:ℤ)=U ∨ v∈C := by
    simp only [remove,eL,eU,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,or_assoc]
  have hnone {v : V} (hv : v∈Finset.univ\remove) : (level v:ℤ)≠L ∧ (level v:ℤ)≠U ∧ v∉C := by
    have hh := (Finset.mem_sdiff.mp hv).2
    simpa only [hremove,not_or] using hh
  let label : V→Fin 4 := fun v=>if (level v:ℤ)<L then 0 else if U<(level v:ℤ) then 1 else if v∈D then 2 else 3
  have hl0 {v : V} (hv : label v=0) : (level v:ℤ)<L := by
    dsimp [label] at hv
    split_ifs at hv with h₀ h₁ h₂ <;> simp_all
  have hl1 {v : V} (hv : label v=1) : U<(level v:ℤ) := by
    dsimp [label] at hv
    split_ifs at hv with h₀ h₁ h₂ <;> simp_all
  have hl2 {v : V} (hv : label v=2) : ¬(level v:ℤ)<L ∧ ¬U<(level v:ℤ) ∧ v∈D := by
    dsimp [label] at hv
    split_ifs at hv with h₀ h₁ h₂ <;> simp_all
  have hl3 {v : V} (hv : label v=3) : ¬(level v:ℤ)<L ∧ ¬U<(level v:ℤ) ∧ v∉D := by
    dsimp [label] at hv
    split_ifs at hv with h₀ h₁ h₂ <;> simp_all
  have hglobal : A.card≤Fintype.card V := Finset.card_le_univ _
  have hsize (i : Fin 4) : 3*((Finset.univ\remove).filter (fun v=>label v=i)).card≤2*(Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    fin_cases i
    · change 3*((Finset.univ\remove).filter (fun v=>label v=(0:Fin 4))).card≤2*Fintype.card V
      have hs : (Finset.univ\remove).filter (fun v=>label v=0)⊆low := by
        intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl0 (Finset.mem_filter.mp hv).2⟩
      have hh := Finset.card_le_card hs
      change 2*low.card≤Fintype.card V at hbelow
      omega
    · change 3*((Finset.univ\remove).filter (fun v=>label v=(1:Fin 4))).card≤2*Fintype.card V
      have hs : (Finset.univ\remove).filter (fun v=>label v=1)⊆high := by
        intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl1 (Finset.mem_filter.mp hv).2⟩
      have hh := Finset.card_le_card hs
      change 2*high.card≤Fintype.card V at habove
      omega
    · change 3*((Finset.univ\remove).filter (fun v=>label v=(2:Fin 4))).card≤2*Fintype.card V
      have hs : (Finset.univ\remove).filter (fun v=>label v=2)⊆A.filter (fun v=>v∉C ∧ v∈D) := by
        intro v hv
        obtain ⟨hr,he⟩ := Finset.mem_filter.mp hv
        have hn := hnone hr
        have hd := hl2 he
        exact Finset.mem_filter.mpr ⟨(hA v).mpr (by omega),hn.2.2,hd.2.2⟩
      have hh := Finset.card_le_card hs
      omega
    · change 3*((Finset.univ\remove).filter (fun v=>label v=(3:Fin 4))).card≤2*Fintype.card V
      have hs : (Finset.univ\remove).filter (fun v=>label v=3)⊆A.filter (fun v=>v∉C ∧ v∉D) := by
        intro v hv
        obtain ⟨hr,he⟩ := Finset.mem_filter.mp hv
        have hn := hnone hr
        have hd := hl3 he
        exact Finset.mem_filter.mpr ⟨(hA v).mpr (by omega),hn.2.2,hd.2.2⟩
      have hh := Finset.card_le_card hs
      omega
  have hclosed : ∀ v∈Finset.univ\remove,∀ w∈Finset.univ\remove,G.Adj v w→label v=label w := by
    intro v hv w hw he
    have hnV := hnone hv
    have hnW := hnone hw
    have hstep : (level w:ℤ)≤(level v:ℤ)+1 ∧ (level v:ℤ)≤(level w:ℤ)+1 := by
      have h := bfs_step G root hc he
      simpa only [SimpleGraph.dist_comm,level] using h
    by_cases hL : (level v:ℤ)<L
    · have hwL : (level w:ℤ)<L := by omega
      simp only [label,if_pos hL,if_pos hwL]
    · by_cases hU : U<(level v:ℤ)
      · have hwU : U<(level w:ℤ) := by omega
        have hwL : ¬(level w:ℤ)<L := by omega
        simp only [label,if_neg hL,if_neg hwL,if_pos hU,if_pos hwU]
      · have hvA : v∈A := (hA v).mpr (by omega)
        have hwA : w∈A := (hA w).mpr (by omega)
        have hwL : ¬(level w:ℤ)<L := by have := (hA w).mp hwA;omega
        have hwU : ¬U<(level w:ℤ) := by have := (hA w).mp hwA;omega
        have hd := hsep v hvA w hwA hnV.2.2 hnW.2.2 he
        simp only [label,if_neg hL,if_neg hU,if_neg hwL,if_neg hwU,hd]
  have hrCost : (remove.card:ℝ)≤2*Real.sqrt 2*Real.sqrt (Finset.univ : Finset V).card := by
    have hcn : remove.card≤eL.card+eU.card+C.card :=
      (Finset.card_union_le (eL∪eU) C).trans (Nat.add_le_add_right (Finset.card_union_le eL eU) _)
    have hbound : remove.card≤eL.card+eU.card+2*(kL+kR) := by omega
    have hre : (remove.card:ℝ)≤(eL.card:ℝ)+eU.card+2*(kL+kR) := by exact_mod_cast hbound
    rw [Finset.card_univ]
    exact hre.trans hcost
  exact ⟨RecursiveSeparator.Split.of_fibers G.Adj Finset.univ remove label
    (Finset.subset_univ _) hclosed hsize hrCost⟩

end TorsionFreeZeroDivisors.PlanarMap

namespace TorsionFreeZeroDivisors.RecursiveSeparator.Split
open scoped Classical
variable {V W : Type} [DecidableEq V] [DecidableEq W]
    {R : V→V→Prop} {Q : W→W→Prop} {S : Finset V}

def map (P : Split R S) (f : V ↪ W) (hR : ∀ v w,Q (f v) (f w)→R v w) :
    Split Q (S.map f) where
  remove := P.remove.map f
  parts := P.parts.image (fun b=>b.map f)
  remove_subset := Finset.map_subset_map.mpr P.remove_subset
  cover := by
    rw [←Finset.map_sdiff]
    ext x
    constructor
    · intro hx
      obtain ⟨b,hb,hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hb
      subst b
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
      refine Finset.mem_map.mpr ⟨v,?_,rfl⟩
      rw [←P.cover]
      exact Finset.mem_biUnion.mpr ⟨c,hc,hv⟩
    · intro hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
      rw [←P.cover] at hv
      obtain ⟨b,hb,hv⟩ := Finset.mem_biUnion.mp hv
      exact Finset.mem_biUnion.mpr ⟨b.map f,Finset.mem_image.mpr ⟨b,hb,rfl⟩,
        Finset.mem_map.mpr ⟨v,hv,rfl⟩⟩
  disjoint := by
    intro b hb c hc hbc
    obtain ⟨d,hd,he⟩ := Finset.mem_image.mp hb
    subst b
    obtain ⟨e,he,hf⟩ := Finset.mem_image.mp hc
    subst c
    exact (Finset.disjoint_map f).mpr (P.disjoint hd he (fun h=>hbc (congrArg (fun b=>b.map f) h)))
  closed := by
    intro b hb x hx y hy hxy
    obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hb
    subst b
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
    rw [←Finset.map_sdiff] at hy
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hy
    exact Finset.mem_map.mpr ⟨w,P.closed c hc v hv w hw (hR v w hxy),rfl⟩
  size := by
    intro b hb
    obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hb
    subst b
    simpa only [Finset.card_map] using P.size c hc
  cost := by simpa only [Finset.card_map] using P.cost
end TorsionFreeZeroDivisors.RecursiveSeparator.Split

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PlanarMap

section
open scoped Classical
open SimpleGraph RecursiveSeparator
variable {V : Type} [Fintype V] {G : SimpleGraph V}

def componentVertices (G : SimpleGraph V) (c : G.ConnectedComponent) : Finset V :=
  Finset.univ.filter (fun v=>G.connectedComponentMk v=c)
lemma mem_componentVertices (c : G.ConnectedComponent) (v : V) :
    v∈componentVertices G c↔G.connectedComponentMk v=c := by simp only [componentVertices,Finset.mem_filter,Finset.mem_univ,true_and]
lemma componentVertices_disjoint (c d : G.ConnectedComponent) (h : c≠d) :
    Disjoint (componentVertices G c) (componentVertices G d) := by
  apply Finset.disjoint_left.mpr
  intro v hv hd
  exact h (((mem_componentVertices c v).mp hv).symm.trans ((mem_componentVertices d v).mp hd))

/-- Add the untouched small components to a separator of the unique large
component. The original deletion set and hence its sharp cost are retained. -/
def extendComponent (c : G.ConnectedComponent)
    (P : Split G.Adj (componentVertices G c))
    (hsmall : ∀ d : G.ConnectedComponent,d≠c→3*(componentVertices G d).card≤2*Fintype.card V) :
    Split G.Adj Finset.univ := by
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let others := (Finset.univ.erase c).image (componentVertices G)
  have hother {b : Finset V} : b∈others↔∃d,d≠c ∧ b=componentVertices G d := by
    simp only [others,Finset.mem_image,Finset.mem_erase,Finset.mem_univ,and_true]
    constructor
    · rintro ⟨d,hd,rfl⟩;exact ⟨d,hd,rfl⟩
    · rintro ⟨d,hd,rfl⟩;exact ⟨d,hd,rfl⟩
  have hdisj {b : Finset V} (hb : b∈P.parts) {d : G.ConnectedComponent} (hd : d≠c) :
      Disjoint b (componentVertices G d) :=
    (componentVertices_disjoint c d hd.symm).mono_left ((P.subset hb).trans Finset.sdiff_subset)
  refine {
    remove := P.remove
    parts := P.parts∪others
    remove_subset := Finset.subset_univ _
    cover := ?_
    disjoint := ?_
    closed := ?_
    size := ?_
    cost := ?_ }
  · ext v
    constructor
    · intro hv
      obtain ⟨b,hb,hv⟩ := Finset.mem_biUnion.mp hv
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
      rcases Finset.mem_union.mp hb with hb|hb
      · exact (Finset.mem_sdiff.mp (P.subset hb hv)).2
      · obtain ⟨d,hd,rfl⟩ := hother.mp hb
        intro hr
        exact Finset.disjoint_left.mp (componentVertices_disjoint c d hd.symm) (P.remove_subset hr) hv
    · intro hv
      have hnr := (Finset.mem_sdiff.mp hv).2
      by_cases hc : G.connectedComponentMk v=c
      · have hc' := (mem_componentVertices c v).mpr hc
        have he := Finset.mem_sdiff.mpr ⟨hc',hnr⟩
        rw [←P.cover] at he
        obtain ⟨b,hb,hv⟩ := Finset.mem_biUnion.mp he
        exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_union_left _ hb,hv⟩
      · exact Finset.mem_biUnion.mpr ⟨componentVertices G (G.connectedComponentMk v),
          Finset.mem_union_right _ (hother.mpr ⟨_,hc,rfl⟩),(mem_componentVertices _ _).mpr rfl⟩
  · intro b hb d hd hbd
    rcases Finset.mem_union.mp hb with hb|hb <;> rcases Finset.mem_union.mp hd with hd|hd
    · exact P.disjoint hb hd hbd
    · obtain ⟨e,he,rfl⟩ := hother.mp hd
      exact hdisj hb he
    · obtain ⟨e,he,rfl⟩ := hother.mp hb
      exact (hdisj hd he).symm
    · obtain ⟨e,_,rfl⟩ := hother.mp hb
      obtain ⟨f,_,rfl⟩ := hother.mp hd
      exact componentVertices_disjoint e f (fun h=>hbd (congrArg (componentVertices G) h))
  · intro b hb v hv w hw he
    rcases Finset.mem_union.mp hb with hb|hb
    · have hvc := (mem_componentVertices c v).mp (Finset.sdiff_subset (P.subset hb hv))
      have hwc : w∈componentVertices G c := (mem_componentVertices c w).mpr
        ((ConnectedComponent.connectedComponentMk_eq_of_adj he).symm.trans hvc)
      exact P.closed b hb v hv w (Finset.mem_sdiff.mpr ⟨hwc,(Finset.mem_sdiff.mp hw).2⟩) he
    · obtain ⟨d,_,rfl⟩ := hother.mp hb
      exact (mem_componentVertices d w).mpr
        ((ConnectedComponent.connectedComponentMk_eq_of_adj he).symm.trans ((mem_componentVertices d v).mp hv))
  · intro b hb
    rw [Finset.card_univ]
    rcases Finset.mem_union.mp hb with hb|hb
    · exact (P.size b hb).trans (Nat.mul_le_mul_left 2 (Finset.card_le_univ _))
    · obtain ⟨d,hd,rfl⟩ := hother.mp hb
      exact hsmall d hd
  · rw [Finset.card_univ]
    exact P.cost.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast Finset.card_le_univ (componentVertices G c)))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))

/-- Sharp separator for any finite genus-zero rotation map, including empty
and disconnected graphs. -/
theorem Model.univ_split (M : Model G) : Nonempty (Split G.Adj Finset.univ) := by
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  by_cases hbig : ∃c : G.ConnectedComponent,2*Fintype.card V<3*(componentVertices G c).card
  · obtain ⟨c,hc⟩ := hbig
    let : DecidableEq c.supp := Classical.decEq _
    obtain ⟨P⟩ := (M.induced c.supp).connected_split c.connected_toSimpleGraph
    let f : c.supp ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    have he : (Finset.univ : Finset c.supp).map f=componentVertices G c := by
      ext v
      simp only [Finset.mem_map,Finset.mem_univ,true_and,mem_componentVertices]
      constructor
      · rintro ⟨x,rfl⟩;exact x.property
      · intro hv;exact ⟨⟨v,hv⟩,rfl⟩
    have PP : Nonempty (Split G.Adj (componentVertices G c)) := by
      rw [←he]
      exact ⟨P.map f (fun _ _ h=>h)⟩
    obtain ⟨P⟩ := PP
    refine ⟨extendComponent c P ?_⟩
    intro d hd
    have hadd : (componentVertices G c).card+(componentVertices G d).card≤Fintype.card V := by
      rw [←Finset.card_union_of_disjoint (componentVertices_disjoint c d hd.symm)]
      exact Finset.card_le_univ _
    omega
  · push Not at hbig
    refine ⟨Split.of_fibers G.Adj Finset.univ ∅ G.connectedComponentMk (Finset.empty_subset _)
      (fun _ _ _ _ h=>ConnectedComponent.connectedComponentMk_eq_of_adj h) ?_ ?_⟩
    · intro c
      simpa only [Finset.sdiff_empty,Finset.card_univ,componentVertices] using hbig c
    · simp only [Finset.card_empty,Nat.cast_zero]
      positivity

end

open scoped Classical
open RecursiveSeparator
variable {V : Type} [Fintype V] {G : SimpleGraph V}
omit [Fintype V] in
/-- The exact sharp separator on every induced vertex set. -/
theorem Model.split (M : Model G) (S : Finset V) : Nonempty (Split G.Adj S) := by
  let : DecidableEq S := Classical.decEq _
  obtain ⟨P⟩ := (M.induced (S : Set V)).univ_split
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have he : (Finset.univ : Finset S).map f=S := by
    ext v
    simp only [Finset.mem_map,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨x,rfl⟩;exact x.property
    · intro hv;exact ⟨⟨v,hv⟩,rfl⟩
  rw [←he]
  exact ⟨P.map f (fun _ _ h=>h)⟩
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

def interaction (α : Equiv.Perm (Position len)) (ha : Function.Involutive α) : SimpleGraph T where
  Adj p q := p≠q ∧ PairingClusters.Rel (fun x=>x.1) α p q
  symm := ⟨by
    rintro p q ⟨hpq,x,hx,hy⟩
    exact ⟨hpq.symm,α x,hy,by rw [ha x];exact hx⟩⟩
  loopless := ⟨fun _ h=>h.1 rfl⟩

def graphIso (α : Equiv.Perm (Position len)) (ha : Function.Involutive α) :
    MapEuler.graph (perm len) α ha ≃g interaction len α ha where
  toEquiv := cyclesEquiv len hpos
  map_rel_iff' := by
    intro a b
    change ((cyclesEquiv len hpos a≠cyclesEquiv len hpos b) ∧
      ∃x,x.1=cyclesEquiv len hpos a ∧ (α x).1=cyclesEquiv len hpos b) ↔
      (a≠b ∧ ∃x,cycle (perm len) x=a ∧ cycle (perm len) (α x)=b)
    constructor
    · rintro ⟨hn,x,hx,hy⟩
      exact ⟨fun h=>hn (congrArg (cyclesEquiv len hpos) h),x,
        (cyclesEquiv len hpos).injective hx,(cyclesEquiv len hpos).injective hy⟩
    · rintro ⟨hn,x,hx,hy⟩
      exact ⟨fun h=>hn ((cyclesEquiv len hpos).injective h),x,
        congrArg (cyclesEquiv len hpos) hx,congrArg (cyclesEquiv len hpos) hy⟩

def model (α : Equiv.Perm (Position len)) (ha : Function.Involutive α)
    (hz : MapEuler.GenusZero (perm len) α) : PlanarMap.Model (interaction len α ha) where
  Dart := Position len
  rotation := perm len
  pairing := α
  involutive := ha
  genus := hz
  iso := graphIso len hpos α ha

include hpos in
/-- The sharp separator for the literal interaction relation, retaining loops
as required by the existing recursive charging theorem. -/
theorem split_dev (α : Equiv.Perm (Position len)) (ha : Function.Involutive α)
    (hz : MapEuler.GenusZero (perm len) α) (S : Finset T) :
    Nonempty (RecursiveSeparator.Split (PairingClusters.Rel (fun x=>x.1) α) S) := by
  obtain ⟨P⟩ := (model len hpos α ha hz).split S
  exact ⟨RecursiveSeparator.Split.of_off_diagonal (fun p q hpq=>by
    change (p≠q ∧ _)↔_
    exact and_iff_right hpq) P⟩
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

variable {A B T G : Type*} [Fintype A] [Fintype B] [Fintype T] [_root_.Group G]
variable (outA : A → Finset T) (outB : B → Finset T)

variable (bar : T→T)

end TorsionFreeZeroDivisors.Factors

end

end OAI
end

section
namespace OAI



section
namespace TorsionFreeZeroDivisors.CellNorm
open scoped Classical BigOperators
noncomputable section
variable {H G I : Type} [CommGroup H] [_root_.Group G] [Fintype H]
  (φ : H→*G) (hφ : Function.Injective φ)
@[instance_reducible] def moduleAction : MulAction H (G×I) where
  smul h p := (φ h*p.1,p.2)
  one_smul p := by change (φ 1*p.1,p.2)=p; simp
  mul_smul h k p := by change (φ (h*k)*p.1,p.2)=(φ h*(φ k*p.1),p.2); rw [map_mul,mul_assoc]
end
end TorsionFreeZeroDivisors.CellNorm

end



end OAI
end

open scoped Classical in
open OAI.TorsionFreeZeroDivisors OAI.TorsionFreeZeroDivisors.BoundaryRotation ComparedBlocks in
theorem solution {T : Type} [Fintype T] (len : T→ℕ) (hpos : ∀t,0<len t)
    (α : Equiv.Perm (Position len)) (ha : Function.Involutive α)
    (hz : MapEuler.GenusZero (perm len) α) (S : Finset T) :
    Nonempty (RecursiveSeparator.Split (PairingClusters.Rel (fun x : Position len => x.1) α) S) :=
  OAI.TorsionFreeZeroDivisors.BoundaryRotation.split_dev len hpos α ha hz S
