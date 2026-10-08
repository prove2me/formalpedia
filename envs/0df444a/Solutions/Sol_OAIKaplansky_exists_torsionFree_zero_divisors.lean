-- Prove2me | solution 1 for OAIKaplansky.exists_torsionFree_zero_divisors
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T15:20:21.481126+00:00
-- url     : https://prove2.me/submissions/95b2c2a6-198a-438e-bc79-018bdbbda57d

import Mathlib
import Definitions.Def_TorsionFreeZeroDivisorsConstruction
import Theorems.Thm_OAI_TorsionFreeZeroDivisors_SampleGraph_exists_avoiding
import Theorems.Thm_OAI_TorsionFreeZeroDivisors_SampleGraph_SpherePicture_excluded
import Theorems.Thm_OAI_TorsionFreeZeroDivisors_ConeTorsion_graph_torsion_free
import Theorems.Thm_OAI_TorsionFreeZeroDivisors_ConcreteFactors_both_nonzero
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

theorem label_reverse (r : Matching label bar) (x : D) :
    label (r x) = bar (label x) := r.property.2.2 x

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

theorem order_eq : ProjectivePlane.order Point Line = 128 := by
  have h := ProjectivePlane.card_points Point Line
  rw [point_card] at h
  have hi : (16513 : ℤ) = (ProjectivePlane.order Point Line : ℤ) ^ 2 +
      (ProjectivePlane.order Point Line : ℤ) + 1 := by exact_mod_cast h
  have hf : ((ProjectivePlane.order Point Line : ℤ) - 128) *
      ((ProjectivePlane.order Point Line : ℤ) + 129) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h1 | h1 <;> omega

@[simp] theorem mem_pointsOn {p : Point} {l : Line} : p ∈ pointsOn l ↔ p ∈ l := by
  simp [pointsOn]

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

namespace TorsionFreeZeroDivisors.WeightedGirth
open scoped Classical BigOperators
open PortSubdivision
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
open PortSubdivision ComparedBlocks GirthAsymptotics TypedGraphs ActualPatternEvent
attribute [instance] BoundedSystem.fP BoundedSystem.fE

end TorsionFreeZeroDivisors.SampleGraph

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
open PermutationCycles
variable {O : Type} [Fintype O]

end TorsionFreeZeroDivisors.ComponentEuler

namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]
variable (σ α : Equiv.Perm O) (l : List (O×O))
    (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
    (he : ∀e∈l,α e.1=e.2)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]
end TorsionFreeZeroDivisors.ComponentEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
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
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O) (l : List (O×O)) (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α) (he : ∀e∈l,α e.1=e.2)
local notation "σ'" => Equiv.swap p q*σ
local notation "L'" => (α p,α q)::l
end TorsionFreeZeroDivisors.VertexSplit
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
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
def letter (d : D) : Group Γ letters R := PresentedGroup.mk _ (letters d)
lemma edge (d : D) : value Γ letters R (Γ.origin (Γ.reverse d))=
    value Γ letters R (Γ.origin d)*letter Γ letters R d := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (show relator Γ letters R d∈relations Γ letters R from ⟨d,rfl⟩)
  simpa only [value,letter,map_mul] using h.symm

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

section
namespace OAI



section
namespace TorsionFreeZeroDivisors.GraphConePresentation
open PortSubdivision GraphPresentation
open scoped Classical
noncomputable section
variable {V D S : Type} (Γ : PortGraph V D)

variable (letters : D→FreeGroup S) (R : Routes Γ)

lemma canonical_base (v : V) : (routes Γ).base ((routes Γ).base v)=(routes Γ).base v := by
  exact congrArg (fun q : Quot (ShortClosure.simpleGraph Γ).Reachable=>q.out)
    ((ShortClosure.simpleGraph Γ).connectedComponentMk v).out_eq

end
end TorsionFreeZeroDivisors.GraphConePresentation

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
include hsample havoid

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
/-- The exact group's ordinary torsion-freeness and both nonzero zero-divisor
factors, proved without assuming a resolution or topological asphericity. The
finite classifying-space clause remains separate and is not asserted here. -/
theorem torsion_free_finitely_presented_zero_divisors :
    ∃ (G : Type) (inst : Group G), letI : Group G := inst
      Group.IsFinitelyPresented G ∧
      (∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1) ∧
      ∃ α β : MonoidAlgebra (ZMod 2) G, α≠0 ∧ β≠0 ∧ α*β=0 := by
  obtain ⟨rep,r,x,y,hr,hL,hd,ha,hx,hy,hz⟩ := SampleGraph.exists_nonzero_factors
  exact ⟨ConcreteGroup.G rep r,inferInstance,inferInstance,
    ConcreteTorsion.torsion_free rep r x y hL hd hr ha,
    ConcreteFactors.alpha rep r x,ConcreteFactors.beta rep r y,hx,hy,hz⟩
end TorsionFreeZeroDivisors

end

end OAI
end

/-- Transfer of `OAI.TorsionFreeZeroDivisors.torsion_free_finitely_presented_zero_divisors` to the
published statement: torsion-freeness as `IsOfFinOrder g → g = 1`. -/
theorem solution :
    ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧
      (∀ g : G, IsOfFinOrder g → g = 1) ∧
      ∃ α β : MonoidAlgebra (ZMod 2) G, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0 := by
  obtain ⟨G, inst, hfp, htf, α, β, hα, hβ, hαβ⟩ :=
    OAI.TorsionFreeZeroDivisors.torsion_free_finitely_presented_zero_divisors
  letI : Group G := inst
  exact ⟨G, inst, hfp, fun g hg => htf g (orderOf g) hg.orderOf_pos (pow_orderOf_eq_one g),
    α, β, hα, hβ, hαβ⟩
