-- Prove2me | solution 1 for OAI.TorsionFreeZeroDivisors.SampleGraph.SpherePicture.excluded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T15:20:22.047106+00:00
-- url     : https://prove2.me/submissions/ded159fe-29ad-4195-8867-115fd5b27e90

import Mathlib
import Definitions.Def_TorsionFreeZeroDivisorsConstruction
import Theorems.Thm_OAI_TorsionFreeZeroDivisors_BoundaryRotation_split
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

lemma positions_card (n : ℕ) : (positions 0 n).card=n := by
  rw [nat_positions,Int.card_Ico,sub_zero,Int.toNat_natCast]

lemma position_card {T : Type*} [Fintype T] (len : T → ℕ) :
    Fintype.card (Position len)=∑ t,len t := by
  simp only [Position,Fintype.card_sigma,Fintype.card_coe,positions_card]

variable {P : Type*} [Fintype P] (chunks : P → ℕ)
  (len : (p : P) → Fin (chunks p) → ℕ) (rev : (p : P) → Fin (chunks p) → Bool)

end TorsionFreeZeroDivisors.FiniteChunking

end

end OAI
end

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

@[simp] theorem length_darts (p : Γ.Walk a b) : p.darts.length = p.length := by
  induction p <;> simp_all [darts,length]

/-- Source immersion is exactly nonbacktracking of consecutive ports. -/
def IsReduced (p : Γ.Walk a b) : Prop :=
  p.darts.IsChain (fun d e => e ≠ Γ.reverse d)

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

/-- Immersion of the original port path is preserved by the subdivision.
In particular the encoding does not spuriously remove a short circuit. -/
theorem reduced_toSubdivision (p : Γ.Walk a b) (hp : p.IsReduced) :
    p.toSubdivision.edges.IsChain (· ≠ ·) := by
  induction p with
  | nil => simp [toSubdivision]
  | @cons a b d hd p ih =>
    cases p with
    | nil =>
      simp [toSubdivision, SimpleGraph.Walk.edges_cons, List.isChain_cons_cons]
    | cons e he q =>
      have hp' : (Walk.cons e he q).IsReduced := by
        exact (List.isChain_cons.mp hp).2
      have hde : e ≠ Γ.reverse d := by
        exact (List.isChain_cons_cons.mp hp).1
      have hi := ih hp'
      simp only [toSubdivision, SimpleGraph.Walk.edges_cons] at hi ⊢
      simp only [List.isChain_cons_cons] at hi ⊢
      refine ⟨?_, ?_, ?_, hi⟩
      · simp
      · simp
      · simpa using Ne.symm hde

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

/-- Below the girth, a nonbacktracking walk cannot repeat a vertex.
This is the quantitative version of Mathlib's forest lemma. -/
theorem short_reduced_isPath (L : ℕ) (hG : L ≤ G.egirth)
    (p : G.Walk a b) (hlen : p.length < L)
    (h : p.edges.IsChain (· ≠ ·)) : p.IsPath := by
  classical
  induction p with
  | nil => simp
  | @cons u v w head tail ih =>
    have hcc := List.isChain_cons.mp (Walk.edges_cons _ _ ▸ h)
    have hi : tail.IsPath := ih (by simpa only [Walk.length_cons] using
      (show tail.length + 1 < L from hlen) |> fun h => by omega) hcc.2
    refine Walk.cons_isPath_iff head tail |>.mpr ⟨hi, ?_⟩
    rcases tail.length.eq_zero_or_pos with hz | hz
    · simp [Walk.nil_iff_support_eq.mp (Walk.length_eq_zero_iff.mp hz), head.ne]
    · by_contra hh
      have hc : (Walk.cons head (tail.takeUntil u hh)).IsCycle := by
        simp only [Walk.isCycle_def, Walk.isTrail_def, Walk.edges_cons, List.nodup_cons,
          ne_eq, reduceCtorEq, not_false_eq_true, Walk.support_cons, List.tail_cons, true_and]
        have ht : (Walk.cons head (tail.takeUntil u hh)).support.tail.Nodup :=
          tail.isPath_def.mp hi |>.sublist <| List.IsInfix.sublist
            ⟨[], (tail.dropUntil u hh).support.tail, by simp [← Walk.support_append]⟩
        refine ⟨⟨?_, Walk.edges_nodup_of_support_nodup ht⟩, ht⟩
        by_contra he
        refine hcc.1 s(u,v) ?_ rfl
        rw [← tail.cons_tail_eq (by simp [Walk.not_nil_iff_lt_length, hz])]
        have hh' := Walk.IsPath.mk' ht |>.eq_snd_of_mem_edges (Sym2.eq_swap ▸ he)
        simp [hh', Walk.snd_takeUntil head.ne]
      have hg := hc.egirth_le_length
      have ht := tail.length_takeUntil_le_length hh
      have hn : L ≤ (Walk.cons head (tail.takeUntil u hh)).length :=
        ENat.natCast_le_natCast.mp (hG.trans hg)
      simp only [Walk.length_cons] at hn hlen
      omega

/-- Every nonempty immersed circuit has at least the graph's girth. -/
theorem reduced_closed_length (L : ℕ) (hG : L ≤ G.egirth)
    (p : G.Walk a a) (hne : 0 < p.length)
    (h : p.edges.IsChain (· ≠ ·)) : L ≤ p.length := by
  by_contra hn
  have hp := short_reduced_isPath L hG p (by omega) h
  have he := (Walk.isPath_iff_nil.mp hp).eq_nil
  have hl : p.length = 0 := by rw [he]; rfl
  omega

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

theorem epsilon_pos {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) : 0 < epsilon δ a := by
  apply lt_min (by norm_num)
  exact div_pos hδ (by positivity)

end

open scoped Classical BigOperators

section FiniteProbability
variable {Ω P : Type*} [Fintype P] (sample : Finset Ω) (hsample : sample.Nonempty)

end FiniteProbability

end TorsionFreeZeroDivisors.StageFusion

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
open PortSubdivision GirthSwitch
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.ConditionedMatchings
open PortSubdivision GirthSwitch
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

/-! The empirical type slots. Each line has exactly 33026 slots on each
side, before the admissible replication parameter is applied. -/

theorem card_slotA : Fintype.card SlotA = 33026 := by
  simp [SlotA]

theorem card_slotB : Fintype.card SlotB = 33026 := by
  simp [SlotB]

theorem card_vertexA (N : ℕ) : Fintype.card (VertexA N) = 2 * 16513 ^ 2 * N := by
  simp only [Fintype.card_prod, card_slotA, Fintype.card_fin, point_card]
  ring

theorem card_vertexB (N : ℕ) : Fintype.card (VertexB N) = 2 * 16513 ^ 2 * N := by
  simp only [Fintype.card_prod, card_slotB, Fintype.card_fin, point_card]
  ring

theorem degreeA_bounds {N : ℕ} (x : VertexA N) :
    129 ≤ (outgoingA x).card ∧ (outgoingA x).card ≤ 132 := by
  rw [outgoingA, Finset.card_disjSum, pointsOn_card]
  rcases x.2.1 with ⟨i,j⟩ | k <;> simp [extrasA, Finset.card_erase_of_mem]

theorem degreeB_bounds {N : ℕ} (y : VertexB N) :
    129 ≤ (outgoingB y).card ∧ (outgoingB y).card ≤ 132 := by
  rw [outgoingB, Finset.card_disjSum, pointsOn_card]
  cases y.2.1 <;> simp [extrasB]

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
open PortSubdivision GirthSwitch
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.TypedGraphs
open TorsionFreeZeroDivisors.Types PortSubdivision ConditionedMatchings
variable {V : Type*} (outgoing : V → Finset Letter)

/-- An origin fibre is exactly the prescribed outgoing type. -/
def originFiber (v : V) : {e : Dart outgoing // origin outgoing e = v} ≃
    {t : Letter // t ∈ outgoing v} where
  toFun e := ⟨e.val.val.2,by
    have h := e.val.property
    simpa only [← e.property,origin,label] using h⟩
  invFun t := ⟨⟨(v,t.val),t.property⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext e.property.symm rfl
  right_inv _ := rfl

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

/-- The simple-graph girth says exactly what is required of the original
multigraph's immersed closed paths. Loops and parallel edges were not discarded. -/
theorem reduced_circuit_length {V D : Type*} (Γ : PortGraph V D) (L : ℕ)
    (hg : (3 * L : ℕ) ≤ Γ.subdivision.egirth) {v : V}
    (p : Γ.Walk v v) (hp : p.IsReduced) (hne : 0 < p.length) : L ≤ p.length := by
  have h := GirthSwitch.reduced_closed_length (3*L) hg p.toSubdivision
    (by rw [p.length_toSubdivision]; omega) (p.reduced_toSubdivision hp)
  rw [p.length_toSubdivision] at h
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

namespace TorsionFreeZeroDivisors.PatternUniform
open scoped Classical Topology BigOperators
open Filter GridAsymptotics GirthAsymptotics TypedGraphs

variable {C E : Type*} [Fintype C] [Fintype E]

end TorsionFreeZeroDivisors.PatternUniform

namespace TorsionFreeZeroDivisors.ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking
open ComparedBlocks RepeatedBlocks GridAsymptotics GirthAsymptotics TypedGraphs
variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2

variable [Fintype E]

end TorsionFreeZeroDivisors.ActualPatternEvent

namespace TorsionFreeZeroDivisors.OriginalPattern
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking
open ComparedBlocks RepeatedBlocks GridAsymptotics GirthAsymptotics TypedGraphs ActualPatternEvent
variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "pl" => pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)

variable [Fintype E]

end TorsionFreeZeroDivisors.OriginalPattern

namespace TorsionFreeZeroDivisors.ComparisonGeometry
open scoped Classical
open BlockAlignment ComparedBlocks ChunkComparisons
variable {P P' E E' : Type*} {len : P → ℕ} {len' : P' → ℕ}

def position (e : P ≃ P') (hl : ∀ p,len p=len' (e p)) : Position len ≃ Position len' :=
  Equiv.sigmaCongr e (fun p => Equiv.subtypeEquivRight (fun q => by rw [hl p]))

namespace Iso
variable {C : Comparisons (E:=E) len} {C' : Comparisons (E:=E') len'}

end Iso
end TorsionFreeZeroDivisors.ComparisonGeometry

namespace TorsionFreeZeroDivisors.PortSubdivision

namespace Iso
variable {V D V' D' V'' D'' : Type*} {Γ : PortGraph V D} {Γ' : PortGraph V' D'} {Γ'' : PortGraph V'' D''}
end Iso
end TorsionFreeZeroDivisors.PortSubdivision

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedDiameter
open Filter ConditionedMatchings MatchingDiameter
open GirthAsymptotics TypedGraphs TorsionFreeZeroDivisors.Types
open scoped Topology Classical BigOperators

theorem log_radius_bound (n : ℕ) (hL : 1 ≤ L n) :
    2*(Nat.log 2 n+1)+1 ≤ 803*L n := by
  have hlog : (Nat.log 2 n:ℝ)*Real.log 2 ≤ Real.log n := by
    have := Real.natLog_le_logb n 2
    rw [Real.logb] at this
    norm_num only [Nat.cast_ofNat] at this
    exact (le_div_iff₀ (by linarith [Real.log_two_gt_d9])).mp this
  have hg := mul_le_mul_of_nonneg_left
    (show (1/2:ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
    (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 n))
  have hl : Real.log n/100 < (L n:ℝ)+1 := Nat.lt_floor_add_one _
  have hL' : (1:ℝ) ≤ L n := by exact_mod_cast hL
  have hr : (Nat.log 2 n:ℝ) ≤ 400*L n := by nlinarith
  have hr' : Nat.log 2 n ≤ 400*L n := by exact_mod_cast hr
  omega

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
def inlWalk {a b : V} : (G⊕g H).Walk (.inl a) (.inl b) → G.Walk a b
  | .nil => .nil
  | .cons (v:=.inl c) h p => .cons h (inlWalk p)
  | .cons (v:=.inr _) h _ => by cases h
lemma map_inlWalk {a b : V} (p : (G⊕g H).Walk (.inl a) (.inl b)) :
    (inlWalk G H p).map Embedding.sumInl.toHom=p := by
  fun_induction inlWalk G H p
  · rfl
  · rename_i a b c h p ih
    change SimpleGraph.Walk.cons _ ((inlWalk G H p).map Embedding.sumInl.toHom) = _
    rw [ih]
    rfl
  · contradiction
lemma inlWalk_length {a b : V} (p : (G⊕g H).Walk (.inl a) (.inl b)) :
    (inlWalk G H p).length=p.length := by
  calc
    _ = ((inlWalk G H p).map Embedding.sumInl.toHom).length := (SimpleGraph.Walk.length_map _ _).symm
    _ = p.length := congrArg SimpleGraph.Walk.length (map_inlWalk G H p)
lemma inlWalk_cycle {a : V} (p : (G⊕g H).Walk (.inl a) (.inl a)) (hp : p.IsCycle) :
    (inlWalk G H p).IsCycle := by
  rw [←map_inlWalk G H p] at hp
  exact hp.of_map
lemma le_egirth (n : ℕ∞) (hG : n≤G.egirth) (hH : n≤H.egirth) :
    n≤(G⊕g H).egirth := by
  apply SimpleGraph.le_egirth.mpr
  intro a p hp
  cases a with
  | inl a =>
    have h := SimpleGraph.le_egirth.mp hG a (inlWalk G H p) (inlWalk_cycle G H p hp)
    simpa only [inlWalk_length] using h
  | inr b =>
    let q : (H⊕g G).Walk (.inl b) (.inl b) := p.map Iso.sumComm.toHom
    have hq : q.IsCycle := hp.map Iso.sumComm.injective
    have h := SimpleGraph.le_egirth.mp hH b (inlWalk H G q) (inlWalk_cycle H G q hq)
    have hl : (inlWalk H G q).length=p.length := (inlWalk_length H G q).trans (p.length_map Iso.sumComm.toHom)
    rw [hl] at h
    exact h
lemma walk_side {a b : V⊕W} (p : (G⊕g H).Walk a b) : a.isLeft=b.isLeft := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    have hs : a.isLeft=b.isLeft := by cases a <;> cases b <;> first | rfl | cases h
    exact hs.trans ih
lemma diameter (B : ℕ)
    (hG : ∀ a b,G.Reachable a b → G.dist a b≤B)
    (hH : ∀ a b,H.Reachable a b → H.dist a b≤B) :
    ∀ a b,(G⊕g H).Reachable a b → (G⊕g H).dist a b≤B := by
  intro a b ⟨p⟩
  have hs := walk_side G H p
  cases a with
  | inl a =>
    cases b with
    | inr b => cases hs
    | inl b =>
      have hab : G.Reachable a b := ⟨inlWalk G H p⟩
      obtain ⟨q,hq⟩ := hab.exists_walk_length_eq_dist
      exact (SimpleGraph.dist_le (q.map (Embedding.sumInl (H:=H)).toHom)).trans (by
        simpa only [SimpleGraph.Walk.length_map,hq] using hG a b hab)
  | inr a =>
    cases b with
    | inl b => cases hs
    | inr b =>
      let p' : (H⊕g G).Walk (.inl a) (.inl b) := p.map Iso.sumComm.toHom
      have hab : H.Reachable a b := ⟨inlWalk H G p'⟩
      obtain ⟨q,hq⟩ := hab.exists_walk_length_eq_dist
      exact (SimpleGraph.dist_le (q.map (Embedding.sumInr (G:=G)).toHom)).trans (by
        simpa only [SimpleGraph.Walk.length_map,hq] using hH a b hab)
end TorsionFreeZeroDivisors.SumGirth
namespace TorsionFreeZeroDivisors.SumPort

section
open PortSubdivision SimpleGraph
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
def subdivisionIso : (graph A B).subdivision ≃g A.subdivision⊕g B.subdivision where
  toEquiv := Equiv.sumSumSumComm VA VB DA DB
  map_rel_iff' := by
    intro a b
    rcases a with (a|a)|(a|a) <;> rcases b with (b|b)|(b|b) <;>
      simp [graph,PortGraph.subdivision,Equiv.sumSumSumComm]
lemma girth (n : ℕ∞) (hA : n≤A.subdivision.egirth) (hB : n≤B.subdivision.egirth) :
    n≤(graph A B).subdivision.egirth := by
  rw [(subdivisionIso A B).egirth_eq]
  exact SumGirth.le_egirth _ _ _ hA hB

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
lemma immersed (d e : DA rep⊕DB rep)
    (ho : (graph rep r).origin d=(graph rep r).origin e) (hl : label rep d=label rep e) : d=e := by
  cases d with
  | inl d =>
    cases e with
    | inl e => exact congrArg Sum.inl (Subtype.ext (Prod.ext (Sum.inl.inj ho) hl))
    | inr e => cases ho
  | inr d =>
    cases e with
    | inl e => cases ho
    | inr e => exact congrArg Sum.inr (Subtype.ext (Prod.ext (Sum.inr.inj ho) hl))
lemma girth (hr : r∈samples rep) : (3*L (size rep):ℕ)≤(graph rep r).subdivision.egirth := by
  have hm := Finset.mem_product.mp hr
  have hA := (Finset.mem_filter.mp hm.1).2.2
  have hB := (Finset.mem_filter.mp hm.2).2.2
  exact SumPort.girth _ _ _ hA hB
end
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ComparisonGeometry GirthAsymptotics TypedGraphs ActualPatternEvent
attribute [instance] BoundedSystem.fP BoundedSystem.fE

end TorsionFreeZeroDivisors.SampleGraph

end

end OAI
end

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

/-- Terminal vertex of a literal path, including the empty path at `z`. -/
def endpoint (l : List D) : V := ((l.getLast?).map (fun d => Γ.origin (Γ.reverse d))).getD z

omit [Fintype V] [Fintype D] in
lemma endpoint_append (l : List D) (d : D) : endpoint Γ z (l++[d])=Γ.origin (Γ.reverse d) := by
  simp [endpoint]

def choices (l : List D) : Finset D := Finset.univ.filter fun d =>
  allowed d ∧ Γ.origin d=endpoint Γ z l ∧ ∀ e∈l.getLast?,d≠Γ.reverse e

def walks : ℕ → Finset (List D)
  | 0 => {[]}
  | k+1 => (walks k).biUnion (fun l => (choices Γ allowed z l).image (fun d => l++[d]))

omit [Fintype V] in
lemma mem_walks_succ {k : ℕ} {l : List D} : l∈walks Γ allowed z (k+1) ↔
    ∃ p∈walks Γ allowed z k,∃ d∈choices Γ allowed z p,l=p++[d] := by
  simp only [walks,Finset.mem_biUnion,Finset.mem_image]
  aesop

omit [Fintype V] in
lemma length_mem {k : ℕ} {l : List D} (hl : l∈walks Γ allowed z k) : l.length=k := by
  induction k generalizing l with
  | zero => simpa only [List.length_nil] using congrArg List.length (Finset.mem_singleton.mp hl)
  | succ k ih =>
    obtain ⟨p,hp,d,_,rfl⟩ := (mem_walks_succ Γ allowed z).mp hl
    simp only [List.length_append,List.length_singleton,ih hp]

omit [Fintype V] in
lemma chain_mem {k : ℕ} {l : List D} (hl : l∈walks Γ allowed z k) :
    l.IsChain (PortWalk.step Γ.origin Γ.reverse) := by
  induction k generalizing l with
  | zero => have := Finset.mem_singleton.mp hl; subst l; simp
  | succ k ih =>
    obtain ⟨p,hp,d,hd,rfl⟩ := (mem_walks_succ Γ allowed z).mp hl
    have hd := (Finset.mem_filter.mp hd).2
    refine (ih hp).append (by simp) ?_
    intro e he f hf
    have hf : f=d := by simpa [eq_comm] using hf
    subst f
    refine ⟨?_,hd.2.2 e he⟩
    have he' : p.getLast?=some e := he
    simpa only [endpoint,he',Option.map_some,Option.getD_some] using hd.2.1.symm

omit [Fintype V] in
lemma allowed_mem {k : ℕ} {l : List D} (hl : l∈walks Γ allowed z k) :
    ∀ d∈l,allowed d := by
  induction k generalizing l with
  | zero => have := Finset.mem_singleton.mp hl; subst l; simp
  | succ k ih =>
    obtain ⟨p,hp,e,he,rfl⟩ := (mem_walks_succ Γ allowed z).mp hl
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact ih hp d hd
    · have hde : d=e := by simpa [eq_comm] using hd
      subst d
      exact (Finset.mem_filter.mp he).2.1

omit [Fintype V] in
lemma head_mem {k : ℕ} {l : List D} (hl : l∈walks Γ allowed z k) :
    ∀ d∈l.head?,Γ.origin d=z := by
  induction k generalizing l with
  | zero => have := Finset.mem_singleton.mp hl; subst l; simp
  | succ k ih =>
    obtain ⟨p,hp,e,he,rfl⟩ := (mem_walks_succ Γ allowed z).mp hl
    intro d hd
    cases p with
    | nil =>
      have hde : d=e := by simpa [eq_comm] using hd
      subst d
      exact (Finset.mem_filter.mp he).2.2.1
    | cons f p =>
      have hdf : d=f := by simpa [eq_comm] using hd
      subst d
      exact ih hp f (by simp)

omit [Fintype V] in
lemma choices_card (l : List D) (hdeg : ∀ v,3≤(Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=v)).card) :
    2≤(choices Γ allowed z l).card := by
  let s := Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=endpoint Γ z l)
  cases he : l.getLast? with
  | none =>
    have hh : choices Γ allowed z l=s := by ext d; simp [choices,s,he]
    rw [hh]
    exact (by omega : 2≤3).trans (hdeg _)
  | some e =>
    have hh : choices Γ allowed z l=s.erase (Γ.reverse e) := by
      ext d
      simp only [choices,s,Finset.mem_filter,Finset.mem_univ,true_and,he,
        Option.mem_some_iff,Finset.mem_erase]
      constructor
      · rintro ⟨ha,ho,hh⟩
        exact ⟨hh e rfl,ha,ho⟩
      · rintro ⟨hh,ha,ho⟩
        exact ⟨ha,ho,fun f hf => hf ▸ hh⟩
    rw [hh]
    have hc3 : s.card ≤ (s.erase (Γ.reverse e)).card+1 := by
      calc
        _ ≤ (insert (Γ.reverse e) (s.erase (Γ.reverse e))).card := Finset.card_le_card (by intro d hd; by_cases h : d=Γ.reverse e <;> simp_all)
        _ ≤ _ := Finset.card_insert_le _ _
    have hc' := hdeg (endpoint Γ z l)
    change 3 ≤ s.card at hc'
    omega

omit [Fintype V] in
lemma card_walks_succ (k : ℕ) (hdeg : ∀ v,3≤(Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=v)).card) :
    2*(walks Γ allowed z k).card≤(walks Γ allowed z (k+1)).card := by
  rw [walks,Finset.card_biUnion]
  · calc
      _ = ∑ _l∈walks Γ allowed z k,2 := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro l _
        rw [Finset.card_image_of_injective _ (by intro d e h; simpa using (List.append_cancel_left h))]
        exact choices_card Γ allowed z l hdeg
  · intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro l hl hl'
    obtain ⟨d,_,hd⟩ := Finset.mem_image.mp hl
    obtain ⟨e,_,he⟩ := Finset.mem_image.mp hl'
    have hh := List.append_inj (hd.trans he.symm) ((length_mem Γ allowed z hp).trans (length_mem Γ allowed z hq).symm)
    exact hpq hh.1

omit [Fintype V] in
lemma card_walks (k : ℕ) (hdeg : ∀ v,3≤(Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=v)).card) :
    2^k≤(walks Γ allowed z k).card := by
  induction k with
  | zero => simp [walks]
  | succ k ih =>
    calc
      _ = 2*2^k := by rw [pow_succ]; omega
      _ ≤ 2*(walks Γ allowed z k).card := Nat.mul_le_mul_left 2 ih
      _ ≤ _ := card_walks_succ Γ allowed z k hdeg
 
/-- Collision of equal-length nonbacktracking paths, before any cancellation. -/
def Collision (k : ℕ) : Prop :=
  ∃ p∈walks Γ allowed z k,∃ q∈walks Γ allowed z k,p≠q ∧ endpoint Γ z p=endpoint Γ z q

lemma collision_exists (k : ℕ) (hk : Fintype.card V<2^k)
    (hdeg : ∀ v,3≤(Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=v)).card) :
    Collision Γ allowed z k := by
  apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (t:=Finset.univ) (f:=endpoint Γ z)
  · simpa only [Finset.card_univ] using hk.trans_le (card_walks Γ allowed z k hdeg)
  · intro p _
    exact Finset.mem_univ _

omit [Fintype V] [Fintype D] in
lemma chain_reverse {l : List D} (hl : l.IsChain (PortWalk.step Γ.origin Γ.reverse)) :
    (l.reverse.map Γ.reverse).IsChain (PortWalk.step Γ.origin Γ.reverse) := by
  rw [List.isChain_map,List.isChain_reverse]
  apply hl.imp
  intro a b hab
  refine ⟨?_,?_⟩
  · simpa only [PortWalk.step,PortGraph.reverse_reverse_apply] using hab.1.symm
  · intro hh
    apply hab.2
    simpa only [PortGraph.reverse_reverse_apply] using hh.symm

/-- A based reduced loop with excluded darts never used. No cyclic reduction at
its base is asserted or needed. Least collision length avoids common suffixes. -/
theorem based_loop (k : ℕ) (hk : Fintype.card V<2^k)
    (hdeg : ∀ v,3≤(Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=v)).card)
    (hsymm : ∀ d,allowed d → allowed (Γ.reverse d)) :
    ∃ l : List D,l≠[] ∧ l.length≤2*k ∧
      l.IsChain (PortWalk.step Γ.origin Γ.reverse) ∧
      (∀ d∈l,allowed d) ∧ (∀ d∈l.head?,Γ.origin d=z) ∧ endpoint Γ z l=z := by
  have H : ∃ m,Collision Γ allowed z m := ⟨k,collision_exists Γ allowed z k hk hdeg⟩
  let m := Nat.find H
  have hmle : m≤k := Nat.find_min' H (collision_exists Γ allowed z k hk hdeg)
  obtain ⟨p,hp,q,hq,hpq,hep⟩ := Nat.find_spec H
  have hmpos : 0 < m := by
    by_contra hn
    have hm0 : m=0 := by omega
    change p∈walks Γ allowed z m at hp
    change q∈walks Γ allowed z m at hq
    rw [hm0] at hp hq
    exact hpq ((Finset.mem_singleton.mp hp).trans (Finset.mem_singleton.mp hq).symm)
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  change p∈walks Γ allowed z m at hp
  change q∈walks Γ allowed z m at hq
  rw [hj] at hp hq
  obtain ⟨p',hp',d,hd,hpd⟩ := (mem_walks_succ Γ allowed z).mp hp
  obtain ⟨q',hq',e,he,hqe⟩ := (mem_walks_succ Γ allowed z).mp hq
  have hde : d≠e := by
    intro hde
    have hc : Collision Γ allowed z j := by
      refine ⟨p',hp',q',hq',?_,?_⟩
      · intro heq
        apply hpq
        simp only [hpd,hqe,heq,hde]
      · exact (Finset.mem_filter.mp hd).2.2.1.symm.trans
          (hde ▸ (Finset.mem_filter.mp he).2.2.1)
    exact Nat.find_min H (by change j < m; omega) hc
  have hpne : p≠[] := by
    intro hh
    have hh' := length_mem Γ allowed z hp
    simp only [hh,List.length_nil] at hh'
    omega
  have hqne : q≠[] := by
    intro hh
    have hh' := length_mem Γ allowed z hq
    simp only [hh,List.length_nil] at hh'
    omega
  refine ⟨p++q.reverse.map Γ.reverse,?_,?_,?_,?_,?_,?_⟩
  · intro hh
    exact hpne (List.append_eq_nil_iff.mp hh).1
  · simp only [List.length_append,List.length_map,List.length_reverse,
      length_mem Γ allowed z hp,length_mem Γ allowed z hq]
    omega
  · apply (chain_mem Γ allowed z hp).append (chain_reverse Γ (chain_mem Γ allowed z hq))
    intro x hx y hy
    have hxd : x=d := by simpa only [hpd,List.getLast?_append,List.getLast?_singleton,
      Option.some_or,Option.some.injEq] using hx.symm
    have hye : y=Γ.reverse e := by
      simpa only [hqe,List.head?_map,List.head?_reverse,List.getLast?_append,
        List.getLast?_singleton,Option.some_or,Option.map_some,Option.some.injEq] using hy.symm
    subst x; subst y
    refine ⟨?_,fun h => hde (Γ.reverse_reverse.injective h).symm⟩
    simpa only [hpd,hqe,endpoint_append] using hep
  · intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact allowed_mem Γ allowed z hp x hx
    · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      exact hsymm y (allowed_mem Γ allowed z hq y (List.mem_reverse.mp hy))
  · intro x hx
    apply head_mem Γ allowed z hp x
    cases p with
    | nil => exact (hpne rfl).elim
    | cons a p => simpa using hx
  · cases hqq : q with
    | nil => exact (hqne hqq).elim
    | cons a q' =>
      simp only [List.reverse_cons,List.map_append,List.map_singleton,←List.append_assoc,endpoint_append,
        PortGraph.reverse_reverse_apply]
      exact head_mem Γ allowed z (hqq ▸ hq) a (by simp)

/-- A logarithmic loop bound, valid even before excluding loops and parallel edges. -/
theorem logarithmic_based_loop
    (hdeg : ∀ v,3≤(Finset.univ.filter (fun d => allowed d ∧ Γ.origin d=v)).card)
    (hsymm : ∀ d,allowed d → allowed (Γ.reverse d)) :
    ∃ l : List D,l≠[] ∧ l.length≤2*(Nat.log 2 (Fintype.card V)+1) ∧
      l.IsChain (PortWalk.step Γ.origin Γ.reverse) ∧
      (∀ d∈l,allowed d) ∧ (∀ d∈l.head?,Γ.origin d=z) ∧ endpoint Γ z l=z :=
  based_loop Γ allowed z _ (Nat.lt_pow_succ_log_self (by decide) _) hdeg hsymm

end
open scoped Classical BigOperators
open PortSubdivision WeightedMoore
variable {V D : Type} (Γ : PortGraph V D)

structure ReducedPath (a b : V) (l : List D) : Prop where
  chain : l.IsChain (PortWalk.step Γ.origin Γ.reverse)
  start : ∀ d∈l.head?,Γ.origin d=a
  finish : endpoint Γ a l=b

lemma endpoint_append_list (a : V) (p q : List D) :
    endpoint Γ a (p++q)=endpoint Γ (endpoint Γ a p) q := by
  simp only [endpoint,List.getLast?_append]
  cases p.getLast? <;> cases q.getLast? <;> rfl

namespace ReducedPath
variable {Γ} {a b c : V} {p q : List D}
lemma nil_iff (h : ReducedPath Γ a b []) : a=b := h.finish
lemma last (h : ReducedPath Γ a b p) {d : D} (hd : d∈p.getLast?) : Γ.origin (Γ.reverse d)=b := by
  have hd : p.getLast?=some d := hd
  simpa only [endpoint,hd,Option.map_some,Option.getD_some] using h.finish

lemma append (hp : ReducedPath Γ a b p) (hq : ReducedPath Γ b c q)
    (hb : ∀ᵉ (x∈p.getLast?) (y∈q.head?),y≠Γ.reverse x) :
    ReducedPath Γ a c (p++q) where
  chain := hp.chain.append hq.chain fun x hx y hy => ⟨(hp.last hx).trans (hq.start y hy).symm,hb x hx y hy⟩
  start := by
    cases p with
    | nil =>
      have hab : a=b := hp.nil_iff
      intro d hd
      simpa only [List.nil_append,hab] using hq.start d hd
    | cons d p =>
      intro e he
      exact hp.start e (by simpa using he)
  finish := by rw [endpoint_append_list,hp.finish]; exact hq.finish

lemma cyclic_join (hp : ReducedPath Γ a a p)
    (hb : ∀ᵉ (x∈p.getLast?) (y∈p.head?),y≠Γ.reverse x) :
    ∀ᵉ (x∈p.getLast?) (y∈p.head?),PortWalk.step Γ.origin Γ.reverse x y := by
  intro x hx y hy
  exact ⟨(hp.last hx).trans (hp.start y hy).symm,hb x hx y hy⟩
end ReducedPath

/-- Excluding an undirected edge means excluding both of its darts. -/
def forbidden (d e : D) : Finset D := {d,Γ.reverse d,e,Γ.reverse e}
def avoids (d e x : D) : Prop := x∉forbidden Γ d e
lemma avoids_symm (d e x : D) (hx : avoids Γ d e x) : avoids Γ d e (Γ.reverse x) := by
  simp only [avoids,forbidden,Finset.mem_insert,Finset.mem_singleton] at hx ⊢
  rcases not_or.mp hx with ⟨h₁,hx⟩
  rcases not_or.mp hx with ⟨h₂,hx⟩
  rcases not_or.mp hx with ⟨h₃,h₄⟩
  intro hx
  rcases hx with hx|hx|hx|hx
  · exact h₂ (by simpa using congrArg Γ.reverse hx)
  · exact h₁ (Γ.reverse_reverse.injective hx)
  · exact h₄ (by simpa using congrArg Γ.reverse hx)
  · exact h₃ (Γ.reverse_reverse.injective hx)
lemma avoids_left (d e x : D) (hx : avoids Γ d e x) : x≠d ∧ x≠Γ.reverse d := by
  have hx : x≠d ∧ x≠Γ.reverse d ∧ x≠e ∧ x≠Γ.reverse e := by
    simpa only [avoids,forbidden,Finset.mem_insert,Finset.mem_singleton,not_or] using hx
  exact ⟨hx.1,hx.2.1⟩
lemma avoids_right (d e x : D) (hx : avoids Γ d e x) : x≠e ∧ x≠Γ.reverse e := by
  have hx : x≠d ∧ x≠Γ.reverse d ∧ x≠e ∧ x≠Γ.reverse e := by
    simpa only [avoids,forbidden,Finset.mem_insert,Finset.mem_singleton,not_or] using hx
  exact hx.2.2

variable [Fintype V] [Fintype D]
omit [Fintype V] in
lemma avoiding_degree (d e : D)
    (hdeg : ∀ v,7≤(Finset.univ.filter (fun x : D => Γ.origin x=v)).card) :
    ∀ v,3≤(Finset.univ.filter (fun x => avoids Γ d e x ∧ Γ.origin x=v)).card := by
  intro v
  have hsub : Finset.univ.filter (fun x : D => Γ.origin x=v) ⊆
      Finset.univ.filter (fun x => avoids Γ d e x ∧ Γ.origin x=v) ∪ forbidden Γ d e := by
    intro x hx
    have hv := (Finset.mem_filter.mp hx).2
    by_cases hb : x∈forbidden Γ d e
    · exact Finset.mem_union_right _ hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb,hv⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hf : (forbidden Γ d e).card≤4 := by
    unfold forbidden
    calc
      _ ≤ ({Γ.reverse d,e,Γ.reverse e}:Finset D).card+1 := Finset.card_insert_le _ _
      _ ≤ ({e,Γ.reverse e}:Finset D).card+2 := by have := Finset.card_insert_le (Γ.reverse d) ({e,Γ.reverse e}:Finset D); omega
      _ ≤ ({Γ.reverse e}:Finset D).card+3 := by have := Finset.card_insert_le e ({Γ.reverse e}:Finset D); omega
      _ = 4 := by simp
  have hv := hdeg v
  omega

/-- Literal reduced based loops avoiding both prescribed unoriented edges. -/
lemma avoiding_loop (d e : D) (z : V)
    (hdeg : ∀ v,7≤(Finset.univ.filter (fun x : D => Γ.origin x=v)).card) :
    ∃ l : List D,l≠[] ∧ l.length≤2*(Nat.log 2 (Fintype.card V)+1) ∧
      ReducedPath Γ z z l ∧ ∀ x∈l,avoids Γ d e x := by
  obtain ⟨l,hn,hl,hc,ha,hs,he⟩ := logarithmic_based_loop Γ (avoids Γ d e) z
    (avoiding_degree Γ d e hdeg) (avoids_symm Γ d e)
  exact ⟨l,hn,hl,⟨hc,hs,he⟩,ha⟩

omit [Fintype D] in
lemma mem_head_eq {l : List D} (hn : l≠[]) {x : D} (hx : x∈l.head?) : x=l.head hn := by
  have h := List.head?_eq_some_head hn
  rw [h] at hx
  exact Option.some.inj hx.symm
omit [Fintype D] in
lemma mem_last_eq {l : List D} (hn : l≠[]) {x : D} (hx : x∈l.getLast?) : x=l.getLast hn := by
  have h := List.getLast?_eq_some_getLast hn
  rw [h] at hx
  exact Option.some.inj hx.symm

/-- Short closure, before the uniform logarithmic-to-L bound.
Only a reduced return path is used; its length need not be minimal. -/
theorem extend_of_return {a b : V} {p q : List D}
    (hp : ReducedPath Γ a b p) (hpn : p≠[]) (hq : ReducedPath Γ b a q)
    (hdeg : ∀ v,7≤(Finset.univ.filter (fun x : D => Γ.origin x=v)).card) :
    ∃ t : List D,t.length≤q.length+4*(Nat.log 2 (Fintype.card V)+1) ∧
      ReducedPath Γ a a (p++t) ∧
      ∀ᵉ (x∈(p++t).getLast?) (y∈(p++t).head?),PortWalk.step Γ.origin Γ.reverse x y := by
  by_cases hqn : q=[]
  · subst q
    have hba : b=a := hq.nil_iff
    subst b
    obtain ⟨j,hjn,hjl,hj,ha⟩ := avoiding_loop Γ (p.getLast hpn) (p.head hpn) a hdeg
    have hjp : ReducedPath Γ a a (p++j) := hp.append hj (by
      intro x hx y hy
      have hx := mem_last_eq hpn hx
      subst x
      exact (avoids_left Γ _ _ _ (ha y (List.mem_of_mem_head? hy))).2)
    refine ⟨j,?_,hjp,hjp.cyclic_join ?_⟩
    · simp only [List.length_nil,zero_add]
      omega
    · intro x hx y hy
      rw [List.getLast?_append_of_ne_nil _ hjn] at hx
      rw [List.head?_append_of_ne_nil _ hpn] at hy
      have hy := mem_head_eq hpn hy
      subst y
      intro he
      have hx' := (avoids_right Γ _ _ _ (ha x (List.mem_of_mem_getLast? hx))).2
      exact hx' (by simpa using (congrArg Γ.reverse he).symm)
  · obtain ⟨jb,hjbn,hjbl,hjb,hab⟩ := avoiding_loop Γ (p.getLast hpn) (q.head hqn) b hdeg
    obtain ⟨ja,hjan,hjal,hja,haa⟩ := avoiding_loop Γ (q.getLast hqn) (p.head hpn) a hdeg
    have hpjb : ReducedPath Γ a b (p++jb) := hp.append hjb (by
      intro x hx y hy
      have hx := mem_last_eq hpn hx
      subst x
      exact (avoids_left Γ _ _ _ (hab y (List.mem_of_mem_head? hy))).2)
    have hpjbq : ReducedPath Γ a a ((p++jb)++q) := hpjb.append hq (by
      intro x hx y hy
      rw [List.getLast?_append_of_ne_nil _ hjbn] at hx
      have hy := mem_head_eq hqn hy
      subst y
      intro he
      have hx' := (avoids_right Γ _ _ _ (hab x (List.mem_of_mem_getLast? hx))).2
      exact hx' (by simpa using (congrArg Γ.reverse he).symm))
    have hall : ReducedPath Γ a a (((p++jb)++q)++ja) := hpjbq.append hja (by
      intro x hx y hy
      rw [List.getLast?_append_of_ne_nil _ hqn] at hx
      have hx := mem_last_eq hqn hx
      subst x
      exact (avoids_left Γ _ _ _ (haa y (List.mem_of_mem_head? hy))).2)
    refine ⟨jb++q++ja,?_,?_,?_⟩
    · simp only [List.length_append]
      omega
    · simpa only [List.append_assoc] using hall
    · have hcy := hall.cyclic_join (by
        intro x hx y hy
        rw [List.getLast?_append_of_ne_nil _ hjan] at hx
        rw [List.append_assoc,List.append_assoc,List.head?_append_of_ne_nil _ hpn] at hy
        have hy := mem_head_eq hpn hy
        subst y
        intro he
        have hx' := (avoids_right Γ _ _ _ (haa x (List.mem_of_mem_getLast? hx))).2
        exact hx' (by simpa using (congrArg Γ.reverse he).symm))
      simpa only [List.append_assoc] using hcy

end TorsionFreeZeroDivisors.ShortClosure

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ShortClosure
open scoped Classical
open PortSubdivision WeightedMoore
variable {V D : Type} (Γ : PortGraph V D)

def liftWalk {a b : V} : (simpleGraph Γ).Walk a b → List D
  | .nil => []
  | .cons h p => edgeDart Γ h::liftWalk p

lemma liftWalk_length {a b : V} (p : (simpleGraph Γ).Walk a b) : (liftWalk Γ p).length=p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [liftWalk,List.length_cons,SimpleGraph.Walk.length_cons,ih]

lemma liftWalk_start {a b : V} (p : (simpleGraph Γ).Walk a b) :
    ∀ d∈(liftWalk Γ p).head?,Γ.origin d=a := by
  cases p with
  | nil => simp [liftWalk]
  | cons h p =>
    intro d hd
    have hd : d=edgeDart Γ h := by simpa only [liftWalk,List.head?_cons,Option.some.injEq] using hd.symm
    subst d
    exact edgeDart_start Γ h

lemma liftWalk_head_target {a b : V} (p : (simpleGraph Γ).Walk a b) :
    ∀ d∈(liftWalk Γ p).head?,Γ.origin (Γ.reverse d)∈p.support := by
  cases p with
  | nil => simp [liftWalk]
  | @cons a b c h p =>
    intro d hd
    have hd : d=edgeDart Γ h := by simpa only [liftWalk,List.head?_cons,Option.some.injEq] using hd.symm
    subst d
    rw [edgeDart_end]
    exact List.mem_cons_of_mem a (SimpleGraph.Walk.start_mem_support p)

lemma liftWalk_finish {a b : V} (p : (simpleGraph Γ).Walk a b) : endpoint Γ a (liftWalk Γ p)=b := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    change endpoint Γ _ ([edgeDart Γ h]++liftWalk Γ p)=_
    rw [endpoint_append_list]
    change endpoint Γ (Γ.origin (Γ.reverse (edgeDart Γ h))) (liftWalk Γ p)=_
    rw [edgeDart_end]
    exact ih

lemma liftWalk_reduced {a b : V} (p : (simpleGraph Γ).Walk a b) (hp : p.IsPath) :
    ReducedPath Γ a b (liftWalk Γ p) := by
  refine ⟨?_,liftWalk_start Γ p,liftWalk_finish Γ p⟩
  induction p with
  | nil => simp [liftWalk]
  | @cons a b c h p ih =>
    apply (ih hp.of_cons).cons
    intro y hy
    refine ⟨(edgeDart_end Γ h).trans (liftWalk_start Γ p y hy).symm,?_⟩
    intro he
    have hu : a∉p.support := (List.nodup_cons.mp hp.support_nodup).1
    apply hu
    have hm := liftWalk_head_target Γ p y hy
    simpa only [he,PortGraph.reverse_reverse_apply,edgeDart_start] using hm

/-- A literal reduced segment stays in one connected component, including when
loops or parallel darts were present in the original port graph. -/
lemma ReducedPath.reachable {a b : V} {l : List D} (hp : ReducedPath Γ a b l) :
    (simpleGraph Γ).Reachable a b := by
  induction l generalizing a with
  | nil => rw [←hp.finish]; exact .refl _
  | cons d l ih =>
    have hs : Γ.origin d=a := hp.start d (by simp)
    have ht : ReducedPath Γ (Γ.origin (Γ.reverse d)) b l := by
      refine ⟨hp.chain.tail,?_,?_⟩
      · intro e he
        exact (hp.chain.rel_head? he).1.symm
      · have he := hp.finish
        change endpoint Γ a ([d]++l)=b at he
        rw [endpoint_append_list] at he
        exact he
    rw [←hs]
    exact (dart_reachable Γ d).trans (ih ht)

/-- Geodesics of the simple shadow lift without backtracking to the actual
multigraph. Thus the previously proved component diameter is the needed one. -/
lemma reduced_return {a b : V} {p : List D} (hp : ReducedPath Γ a b p) :
    ∃ q : List D,ReducedPath Γ b a q ∧ q.length=(simpleGraph Γ).dist b a := by
  obtain ⟨w,hw⟩ := (hp.reachable Γ).symm.exists_walk_length_eq_dist
  exact ⟨liftWalk Γ w,liftWalk_reduced Γ w (w.isPath_of_length_eq_dist hw),(liftWalk_length Γ w).trans hw⟩

variable [Fintype V] [Fintype D]
/-- The entire deterministic closure lemma, with an explicit logarithmic
additive loss. No graph embedding theorem or cyclic cancellation is assumed. -/
theorem short_closure (B : ℕ)
    (hdiam : ∀ a b,(simpleGraph Γ).Reachable a b → (simpleGraph Γ).dist a b≤B)
    (hdeg : ∀ v,7≤(Finset.univ.filter (fun x : D => Γ.origin x=v)).card)
    {a b : V} {p : List D} (hp : ReducedPath Γ a b p) (hpn : p≠[]) :
    ∃ t : List D,t.length≤B+4*(Nat.log 2 (Fintype.card V)+1) ∧
      ReducedPath Γ a a (p++t) ∧
      ∀ᵉ (x∈(p++t).getLast?) (y∈(p++t).head?),PortWalk.step Γ.origin Γ.reverse x y := by
  obtain ⟨q,hq,hql⟩ := reduced_return Γ hp
  obtain ⟨t,ht,hp',hc⟩ := extend_of_return Γ hp hpn hq hdeg
  refine ⟨t,?_,hp',hc⟩
  have hb := hdiam b a (hp.reachable Γ).symm
  omega

end TorsionFreeZeroDivisors.ShortClosure
namespace TorsionFreeZeroDivisors.SumPort
open PortSubdivision
open scoped Classical BigOperators
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
lemma simple_eq : ShortClosure.simpleGraph (graph A B)=
    ShortClosure.simpleGraph A⊕g ShortClosure.simpleGraph B := by
  ext a b
  rcases a with a|a <;> rcases b with b|b <;>
    simp [ShortClosure.simpleGraph,graph,SimpleGraph.sum,Sum.exists]
variable [Fintype DA] [Fintype DB]
lemma degree_left (v : VA) :
    (Finset.univ.filter (fun d : DA⊕DB => (graph A B).origin d=Sum.inl v)).card=
      (Finset.univ.filter (fun d : DA => A.origin d=v)).card := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_sum_type]
  simp [graph, -Finset.sum_boole]
lemma degree_right (v : VB) :
    (Finset.univ.filter (fun d : DA⊕DB => (graph A B).origin d=Sum.inr v)).card=
      (Finset.univ.filter (fun d : DB => B.origin d=v)).card := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_sum_type]
  simp [graph, -Finset.sum_boole]
lemma typed_degree {V : Type} [Fintype V] (outgoing : V → Finset Types.Letter) (v : V) :
    (Finset.univ.filter (fun d : TypedGraphs.Dart outgoing => TypedGraphs.origin outgoing d=v)).card=(outgoing v).card := by
  have h := Fintype.card_congr (TypedGraphs.originFiber outgoing v)
  simpa [Fintype.card_subtype] using h
end TorsionFreeZeroDivisors.SumPort
namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings ActualPatternEvent TypedGraphs GirthAsymptotics
variable (rep : ℕ) (r : Match rep)
lemma simple_eq : ShortClosure.simpleGraph (graph rep r)=
    ShortClosure.simpleGraph (A rep r)⊕g ShortClosure.simpleGraph (B rep r) :=
  SumPort.simple_eq (A rep r) (B rep r)
lemma degreeA (v : VA rep) :
    (Finset.univ.filter (fun d : DA rep⊕DB rep => (graph rep r).origin d=Sum.inl v)).card=
      (Types.outgoingA v).card := by
  unfold graph
  have h := (SumPort.degree_left (A rep r) (B rep r) v).trans (SumPort.typed_degree (@Types.outgoingA rep) v)
  convert h using 1
  congr 1
  ext d
  simp
lemma degreeB (v : VB rep) :
    (Finset.univ.filter (fun d : DA rep⊕DB rep => (graph rep r).origin d=Sum.inr v)).card=
      (Types.outgoingB v).card := by
  unfold graph
  have h := (SumPort.degree_right (A rep r) (B rep r) v).trans (SumPort.typed_degree (@Types.outgoingB rep) v)
  convert h using 1
  congr 1
  ext d
  simp
lemma degree (v : VA rep⊕VB rep) :
    129≤(Finset.univ.filter (fun d : DA rep⊕DB rep => (graph rep r).origin d=v)).card := by
  cases v with
  | inl v => rw [degreeA]; exact (Types.degreeA_bounds v).1
  | inr v => rw [degreeB]; exact (Types.degreeB_bounds v).1
lemma diameter (hd : GraphSample.Diameters rep r) :
    ∀ a b,(ShortClosure.simpleGraph (graph rep r)).Reachable a b →
      (ShortClosure.simpleGraph (graph rep r)).dist a b≤TypedDiameter.D₀*L (size rep) := by
  rw [simple_eq]
  exact SumGirth.diameter _ _ _ hd.1 hd.2
lemma card_vertices : Fintype.card (VA rep⊕VB rep)=2*size rep := by
  rw [Fintype.card_sum,Types.card_vertexA,Types.card_vertexB]
  unfold size
  omega
lemma closure_log_bound (n : ℕ) (hL : 1≤L n) :
    4*(Nat.log 2 (2*n)+1)≤1608*L n := by
  have h := TypedDiameter.log_radius_bound n hL
  by_cases hn : n=0
  · subst n; simp only [Nat.mul_zero,Nat.log_zero_right,zero_add]; omega
  · rw [Nat.mul_comm 2 n,Nat.log_mul_base (by omega) hn]
    omega
/-- The short-closure conclusion on the actual sampled two-side graph,
with one uniform fixed constant independent of the segment and n. -/
theorem short_closure (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
    {a b : VA rep⊕VB rep} {p : List (DA rep⊕DB rep)}
    (hp : ShortClosure.ReducedPath (graph rep r) a b p) (hpn : p≠[]) :
    ∃ t : List (DA rep⊕DB rep),t.length≤(TypedDiameter.D₀+1608)*L (size rep) ∧
      ShortClosure.ReducedPath (graph rep r) a a (p++t) ∧
      ∀ᵉ (x∈(p++t).getLast?) (y∈(p++t).head?),
        WeightedMoore.PortWalk.step (graph rep r).origin (graph rep r).reverse x y := by
  obtain ⟨t,ht,hp',hc⟩ := ShortClosure.short_closure (graph rep r) (TypedDiameter.D₀*L (size rep))
    (diameter rep r hd) (fun v => (by norm_num : 7≤129).trans (degree rep r v)) hp hpn
  refine ⟨t,?_,hp',hc⟩
  rw [card_vertices] at ht
  have hb := closure_log_bound (size rep) hL
  nlinarith
end TorsionFreeZeroDivisors.SampleGraph

namespace TorsionFreeZeroDivisors.RestrictComparisons
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T E : Type} {len : T → ℕ} (C : Comparisons (E:=E) len) (keep : T → Prop)

abbrev Length : {t // keep t} → ℕ := fun t => len t.val

def embed (x : Position (Length keep (len:=len))) : Position len := ⟨x.1.val,x.2⟩
def liftPosition (x : Position len) (h : keep x.1) : Position (Length keep (len:=len)) := ⟨⟨x.1,h⟩,x.2⟩
lemma embed_local (x : Position len) (h : keep x.1) : embed keep (liftPosition keep x h)=x := by cases x; rfl
lemma embed_injective : Function.Injective (embed keep (len:=len)) := by
  rintro ⟨⟨t,ht⟩,q⟩ ⟨⟨u,hu⟩,r⟩ h
  cases h
  rfl

abbrev Active (e : E) : Prop := keep (C.source e) ∧ keep (C.source (C.flip e))
lemma active_flip (e : E) : Active C keep (C.flip e) ↔ Active C keep e := by
  simp only [Active,C.flip_inv e,and_comm]
def flip (e : {e // Active C keep e}) : {e // Active C keep e} :=
  ⟨C.flip e.val,(active_flip C keep e.val).mpr e.property⟩
lemma flip_inv : Function.Involutive (flip C keep) := by
  intro e
  apply Subtype.ext
  exact C.flip_inv e.val
lemma flip_ne (e : {e // Active C keep e}) : flip C keep e≠e := by
  intro h
  exact C.flip_ne e.val (congrArg Subtype.val h)

def partner (x : Position (Length keep (len:=len))) : Position (Length keep (len:=len)) :=
  if h : keep (C.pairing.partner (embed keep x)).1 then
    liftPosition keep (C.pairing.partner (embed keep x)) h else x
lemma partner_image_yes (x : Position (Length keep (len:=len)))
    (h : keep (C.pairing.partner (embed keep x)).1) :
    embed keep (partner C keep x)=C.pairing.partner (embed keep x) := by
  simp only [partner,dif_pos h,embed_local]
lemma partner_no (x : Position (Length keep (len:=len)))
    (h : ¬keep (C.pairing.partner (embed keep x)).1) : partner C keep x=x := by
  simp only [partner,dif_neg h]
lemma partner_inv : Function.Involutive (partner C keep) := by
  intro x
  by_cases h : keep (C.pairing.partner (embed keep x)).1
  · have hh : keep (C.pairing.partner (embed keep (partner C keep x))).1 := by
      rw [partner_image_yes C keep x h,C.pairing.involutive]
      exact x.1.property
    apply embed_injective keep
    rw [partner_image_yes C keep _ hh,partner_image_yes C keep x h,C.pairing.involutive]
  · rw [partner_no C keep x h,partner_no C keep x h]

/-- Drop comparisons exactly when either whole path has been deleted. -/
def side (x : Position (Length keep (len:=len))) : Option {e // Active C keep e} :=
  match C.side (embed keep x) with
  | none => none
  | some e => if h : Active C keep e then some ⟨e,h⟩ else none
lemma side_some (x : Position (Length keep (len:=len))) (e : {e // Active C keep e}) :
    side C keep x=some e ↔ C.side (embed keep x)=some e.val := by
  unfold side
  cases h : C.side (embed keep x) with
  | none => simp
  | some f =>
    by_cases hf : Active C keep f
    · simp only [dif_pos hf,Option.some.injEq,Subtype.ext_iff]
    · simp only [dif_neg hf,reduceCtorEq,false_iff,Option.some.injEq]
      intro he; subst f; exact hf e.property
lemma partner_image_of_side {x : Position (Length keep (len:=len))} {e : {e // Active C keep e}}
    (he : side C keep x=some e) : embed keep (partner C keep x)=C.pairing.partner (embed keep x) := by
  apply partner_image_yes
  rw [C.partner_source _ _ ((side_some C keep x e).mp he)]
  exact e.property.2
lemma side_none (x : Position (Length keep (len:=len))) : side C keep x=none ↔ partner C keep x=x := by
  constructor
  · intro hs
    by_cases hk : keep (C.pairing.partner (embed keep x)).1
    · apply embed_injective keep
      rw [partner_image_yes C keep x hk]
      apply (C.none_iff _).mp
      cases he : C.side (embed keep x) with
      | none => rfl
      | some e =>
        have ha : Active C keep e := by
          constructor
          · rw [←((C.side_iff _ _).mp he).1]; exact x.1.property
          · rwa [←C.partner_source _ _ he]
        have hh := (side_some C keep x ⟨e,ha⟩).mpr he
        rw [hs] at hh
        cases hh
    · exact partner_no C keep x hk
  · intro hp
    cases hs : side C keep x with
    | none => rfl
    | some e =>
      have hh := partner_image_of_side C keep hs
      rw [hp] at hh
      have hn := (C.none_iff _).mpr hh.symm
      have he := (side_some C keep x e).mp hs
      rw [hn] at he
      cases he

def comparisons : Comparisons (E:={e // Active C keep e}) (Length keep (len:=len)) where
  pairing := ⟨partner C keep,partner_inv C keep⟩
  side := side C keep
  flip := flip C keep
  flip_inv := flip_inv C keep
  flip_ne := flip_ne C keep
  side_partner := by
    intro x e he
    apply (side_some C keep _ _).mpr
    rw [partner_image_of_side C keep he]
    exact C.side_partner _ _ ((side_some C keep x e).mp he)
  none_iff := side_none C keep
  source e := ⟨C.source e.val,e.property.1⟩
  lo e := C.lo e.val
  hi e := C.hi e.val
  reverse e := C.reverse e.val
  offset e := C.offset e.val
  side_iff := by
    intro x e
    rw [side_some,C.side_iff]
    simp only [Subtype.ext_iff]
    rfl
  partner_source := by
    intro x e he
    apply Subtype.ext
    have hh := congrArg Sigma.fst (partner_image_of_side C keep he)
    exact hh.trans (C.partner_source _ _ ((side_some C keep x e).mp he))
  partner_coordinate := by
    intro x e he
    have hh := congrArg (fun x : Position len => x.2.val) (partner_image_of_side C keep he)
    exact hh.trans (C.partner_coordinate _ _ ((side_some C keep x e).mp he))
  target_range e := C.target_range e.val

/-- A new fixed position was either already fixed or points to a deleted path.
This is an exact dichotomy of literal occurrence indices. -/
lemma fixed_iff (x : Position (Length keep (len:=len))) :
    partner C keep x=x ↔ C.pairing.partner (embed keep x)=embed keep x ∨
      ¬keep (C.pairing.partner (embed keep x)).1 := by
  constructor
  · intro hx
    by_cases h : keep (C.pairing.partner (embed keep x)).1
    · left
      have hh := partner_image_yes C keep x h
      rw [hx] at hh
      exact hh.symm
    · exact Or.inr h
  · rintro (h|h)
    · apply embed_injective keep
      have hk : keep (C.pairing.partner (embed keep x)).1 := by rw [h]; exact x.1.property
      rw [partner_image_yes C keep x hk,h]
    · exact partner_no C keep x h

variable [Fintype T]
end TorsionFreeZeroDivisors.RestrictComparisons

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

def block (c : G.ConnectedComponent) : Finset V :=
  Finset.univ.filter (fun v => G.connectedComponentMk v=c)
lemma mem_block {c : G.ConnectedComponent} {v : V} :
    v∈block G c ↔ G.connectedComponentMk v=c := by simp [block]
lemma block_nonempty (c : G.ConnectedComponent) : (block G c).Nonempty := by
  exact ⟨c.out,(mem_block G).mpr c.out_eq⟩
omit [Fintype V] in
lemma same_of_adj {v w : V} (h : G.Adj v w) : G.connectedComponentMk v=G.connectedComponentMk w :=
  SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h

omit [Fintype V] in
lemma reachable_closed {B : Finset V}
    (hc : ∀ x∈B,∀ y,G.Adj x y → y∈B) {x y : V}
    (hp : G.Reachable x y) (hx : x∈B) : y∈B := by
  obtain ⟨p⟩ := hp
  induction p with
  | nil => exact hx
  | @cons u v w h p ih => exact ih (hc u hx v h)

lemma block_card {K : ℕ}
    (hs : ∀ x : V,∃ B : Finset V,x∈B ∧ B.card≤K ∧ ∀ y∈B,∀ z,G.Adj y z → z∈B)
    (c : G.ConnectedComponent) : (block G c).card≤K := by
  obtain ⟨x,hx⟩ := block_nonempty G c
  obtain ⟨B,hB,hBK,hclosed⟩ := hs x
  apply (Finset.card_le_card (show block G c⊆B from ?_)).trans hBK
  intro y hy
  apply reachable_closed G hclosed _ hB
  apply SimpleGraph.ConnectedComponent.exact
  exact (mem_block G).mp hx |>.trans ((mem_block G).mp hy).symm

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
abbrev Cluster := (graph f α hα keep).ConnectedComponent

def cluster (t : T) : Option (Cluster f α hα keep) :=
  if h : keep t then some ((graph f α hα keep).connectedComponentMk ⟨t,h⟩) else none
omit [Fintype O] [Fintype T] in
lemma cluster_some {t : T} (h : keep t) :
    cluster f α hα keep t=some ((graph f α hα keep).connectedComponentMk ⟨t,h⟩) := dif_pos h
omit [Fintype O] [Fintype T] in
lemma cluster_none {t : T} (h : ¬keep t) : cluster f α hα keep t=none := dif_neg h
omit [Fintype O] [Fintype T] in
lemma cluster_exists {t : T} : (∃ c,cluster f α hα keep t=some c) ↔ keep t := by
  by_cases h : keep t
  · simp only [cluster_some f α hα keep h,Option.some.injEq,exists_eq',h]
  · simp only [cluster_none f α hα keep h,reduceCtorEq,exists_false,false_iff]; exact h
omit [Fintype O] [Fintype T] in
lemma cluster_pair {o : O} (h : keep (f o)) (h' : keep (f (α o))) :
    cluster f α hα keep (f o)=cluster f α hα keep (f (α o)) := by
  rw [cluster_some f α hα keep h,cluster_some f α hα keep h']
  apply congrArg some
  by_cases he : (⟨f o,h⟩ : Vertex keep)=⟨f (α o),h'⟩
  · rw [he]
  · apply FiniteClusters.same_of_adj
    exact ⟨he,⟨o,rfl,rfl⟩⟩
omit [Fintype O] [Fintype T] in
lemma same_cluster_partner {o : O} {c : Cluster f α hα keep}
    (hc : cluster f α hα keep (f o)=some c) :
    (cluster f α hα keep (f (α o))=some c ↔ keep (f (α o))) := by
  constructor
  · intro h; exact (cluster_exists f α hα keep).mp ⟨c,h⟩
  · intro h
    rw [←cluster_pair f α hα keep ((cluster_exists f α hα keep).mp ⟨c,hc⟩) h,hc]

def bad (o : O) : Prop := keep (f o) ∧ (α o=o ∨ ¬keep (f (α o)))
def localBad (c : Cluster f α hα keep) (o : O) : Prop :=
  cluster f α hα keep (f o)=some c ∧
    (α o=o ∨ cluster f α hα keep (f (α o))≠some c)
omit [Fintype O] [Fintype T] in
lemma localBad_iff (c : Cluster f α hα keep) (o : O) :
    localBad f α hα keep c o ↔ bad f α keep o ∧ cluster f α hα keep (f o)=some c := by
  constructor
  · rintro ⟨hc,hb⟩
    refine ⟨⟨(cluster_exists f α hα keep).mp ⟨c,hc⟩,?_⟩,hc⟩
    exact hb.imp_right fun hn h => hn ((same_cluster_partner f α hα keep hc).mpr h)
  · rintro ⟨⟨_,hb⟩,hc⟩
    exact ⟨hc,hb.imp_right fun hn h => hn ((same_cluster_partner f α hα keep hc).mp h)⟩

lemma local_bad_sum :
    (∑ c : Cluster f α hα keep,(Finset.univ.filter (localBad f α hα keep c)).card)=
    (Finset.univ.filter (bad f α keep)).card := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  simp only [localBad_iff]
  by_cases hb : bad f α keep o
  · obtain ⟨c,hc⟩ := (cluster_exists f α hα keep).mpr hb.1
    simp [hb,hc]
  · simp [hb]

include hα in
omit [Fintype T] in
lemma total_bad_bound : (Finset.univ.filter (bad f α keep)).card≤
    (Finset.univ.filter (fun o => α o=o)).card+
    (Finset.univ.filter (fun o => ¬keep (f o) ∧ α o≠o)).card := by
  let old := Finset.univ.filter (fun o : O => keep (f o) ∧ α o=o)
  let cut := Finset.univ.filter (fun o : O => keep (f o) ∧ α o≠o ∧ ¬keep (f (α o)))
  have cover : Finset.univ.filter (bad f α keep)⊆old∪cut := by
    intro o ho
    have ho := (Finset.mem_filter.mp ho).2
    by_cases he : α o=o
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho.1,he⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho.1,he,ho.2.resolve_left he⟩)
  have hold : old.card≤(Finset.univ.filter (fun o => α o=o)).card := by
    apply Finset.card_le_card
    intro o ho
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ho).2.2⟩
  have hcut : cut.card≤(Finset.univ.filter (fun o => ¬keep (f o) ∧ α o≠o)).card := by
    apply Finset.card_le_card_of_injOn (f:=α)
    · intro o ho
      have ho := (Finset.mem_filter.mp ho).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho.2.2,by simpa only [hα o] using Ne.symm ho.2.1⟩
    · exact fun _ _ _ _ h => hα.injective h
  exact (Finset.card_le_card cover).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hold hcut))

lemma total_local_bad_bound :
    (∑ c : Cluster f α hα keep,(Finset.univ.filter (localBad f α hα keep c)).card)≤
    (Finset.univ.filter (fun o => α o=o)).card+
    (Finset.univ.filter (fun o => ¬keep (f o) ∧ α o≠o)).card := by
  rw [local_bad_sum]
  exact total_bad_bound f α hα keep
end TorsionFreeZeroDivisors.PairingClusters

/-! Arithmetic localization of finite-cluster mass and comparison bounds. -/
namespace TorsionFreeZeroDivisors.PlanarLocalization
open scoped Classical BigOperators

lemma bad_mass {Z : Type} [Fintype Z] (h b : Z → ℝ) (ε : ℝ)
    (hb : ∀ z,0 ≤ b z) :
    ε*(∑ z∈Finset.univ.filter (fun z => ε*h z < b z),h z) ≤ ∑ z,b z := by
  calc
    _ = ∑ z∈Finset.univ.filter (fun z => ε*h z < b z),ε*h z := by rw [Finset.mul_sum]
    _ ≤ ∑ z∈Finset.univ.filter (fun z => ε*h z < b z),b z :=
      Finset.sum_le_sum fun z hz => (Finset.mem_filter.mp hz).2.le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun z _ _ => hb z)

/-- Three exact exclusions leave a positive amount of source length. -/
theorem exists_good_cluster {Z : Type} [Fintype Z]
    (h b i : Z → ℝ) (H₀ L ε C C₂ : ℝ)
    (hH₀ : 0 < H₀) (hL : 0 < L) (hε : 0 < ε) (hC₂ : 0 < C₂)
    (hh : ∀ z,0 ≤ h z) (hb : ∀ z,0 ≤ b z) (hi : ∀ z,0 ≤ i z)
    (hupper : ∀ z,h z ≤ C*L)
    (hretained : 15/16*H₀ ≤ ∑ z,h z)
    (hunpaired : ∑ z,b z ≤ ε/16*H₀)
    (hcomparisons : ∑ z,i z ≤ C₂/(16*L)*H₀)
    (hshort : ∑ z∈Finset.univ.filter (fun z => h z < L),h z ≤ H₀/2) :
    ∃ z,L ≤ h z ∧ h z ≤ C*L ∧ b z ≤ ε*h z ∧ i z ≤ C₂*h z/L := by
  let badB := Finset.univ.filter (fun z => ε*h z < b z)
  let badI := Finset.univ.filter (fun z => (C₂/L)*h z < i z)
  let short := Finset.univ.filter (fun z => h z < L)
  have hB : ∑ z∈badB,h z ≤ H₀/16 := by
    have ht := (bad_mass h b ε hb).trans hunpaired
    change ε*(∑ z∈badB,h z) ≤ ε/16*H₀ at ht
    nlinarith
  have hI : ∑ z∈badI,h z ≤ H₀/16 := by
    have ht := (bad_mass h i (C₂/L) hi).trans hcomparisons
    change (C₂/L)*(∑ z∈badI,h z) ≤ C₂/(16*L)*H₀ at ht
    have he : C₂/(16*L)*H₀=(C₂/L)*(H₀/16) := by ring
    rw [he] at ht
    have hp := div_pos hC₂ hL
    nlinarith
  by_contra hn
  have hc : ∀ z,z∈badB ∨ z∈badI ∨ z∈short := by
    intro z
    by_cases hB : b z ≤ ε*h z
    · by_cases hI : i z ≤ C₂*h z/L
      · have hs : h z < L := by
          by_contra hl
          exact hn ⟨z,le_of_not_gt hl,hupper z,hB,hI⟩
        exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩))
      · right; left
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        simpa only [div_mul_eq_mul_div] using lt_of_not_ge hI
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_not_ge hB⟩)
  have hsum : (∑ z,h z) ≤ (∑ z∈badB,h z)+(∑ z∈badI,h z)+(∑ z∈short,h z) := by
    rw [Finset.sum_filter,Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib,
      ←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _
    have hc := hc z
    simp only [badB,badI,short,Finset.mem_filter,Finset.mem_univ,true_and] at hc
    rcases hc with hc|hc|hc
    · simp only [if_pos hc]
      have h1 : 0 ≤ if C₂/L*h z < i z then h z else 0 := by split <;> first | exact hh z | exact le_rfl
      have h2 : 0 ≤ if h z < L then h z else 0 := by split <;> first | exact hh z | exact le_rfl
      linarith
    · simp only [if_pos hc]
      have h1 : 0 ≤ if ε*h z < b z then h z else 0 := by split <;> first | exact hh z | exact le_rfl
      have h2 : 0 ≤ if h z < L then h z else 0 := by split <;> first | exact hh z | exact le_rfl
      linarith
    · simp only [if_pos hc]
      have h1 : 0 ≤ if ε*h z < b z then h z else 0 := by split <;> first | exact hh z | exact le_rfl
      have h2 : 0 ≤ if C₂/L*h z < i z then h z else 0 := by split <;> first | exact hh z | exact le_rfl
      linarith
  change (∑ z∈short,h z) ≤ H₀/2 at hshort
  linarith

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
def cluster := PairingClusters.cluster (fun x : Position len => x.1)
  C.pairing.partner C.pairing.involutive keep
abbrev belongs (c : Cluster C keep) (t : T) : Prop := cluster C keep t=some c
abbrev localC (c : Cluster C keep) := RestrictComparisons.comparisons C (belongs C keep c)
def mass (c : Cluster C keep) : ℕ := ∑ t∈Finset.univ.filter (belongs C keep c),len t
def bad (c : Cluster C keep) : ℕ :=
  (Finset.univ.filter (PairingClusters.localBad (fun x : Position len => x.1)
    C.pairing.partner C.pairing.involutive keep c)).card
def comparisons [Fintype E] (c : Cluster C keep) : ℕ :=
  Fintype.card {e // RestrictComparisons.Active C (belongs C keep c) e}
def paths (c : Cluster C keep) : Finset T := Finset.univ.filter (belongs C keep c)

omit [Fintype T] in
lemma cluster_exists {t : T} : (∃ c,belongs C keep c t) ↔ keep t :=
  PairingClusters.cluster_exists _ _ _ _

lemma mass_sum : (∑ c,mass C keep c)=∑ t∈Finset.univ.filter keep,len t := by
  simp only [mass,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : keep t
  · obtain ⟨c,hc⟩ := (cluster_exists C keep).mpr ht
    change cluster C keep t=some c at hc
    simp [belongs,hc,ht]
  · have hc : cluster C keep t=none := PairingClusters.cluster_none _ _ _ _ ht
    simp [belongs,hc,ht]

lemma bad_sum : (∑ c,bad C keep c)≤
    (Finset.univ.filter (fun x : Position len=>C.pairing.partner x=x)).card+
    (Finset.univ.filter (fun x : Position len=>¬keep x.1 ∧ C.pairing.partner x≠x)).card := by
  convert PairingClusters.total_local_bad_bound (fun x : Position len => x.1) C.pairing.partner C.pairing.involutive keep using 1
  · apply Finset.sum_congr (by ext c; simp)
    intro c _
    unfold bad
    congr 1
  · congr 1 <;> congr 1 <;> ext x <;> simp

lemma comparisons_sum [Fintype E] : (∑ c,comparisons C keep c)≤Fintype.card E := by
  simp only [comparisons,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _e : E,1 := by
      apply Finset.sum_le_sum
      intro e _
      by_cases hk : keep (C.source e)
      · obtain ⟨c,hc⟩ := (cluster_exists C keep).mpr hk
        change cluster C keep (C.source e)=some c at hc
        calc
          _ ≤ ∑ d : Cluster C keep, if belongs C keep d (C.source e) then 1 else 0 := by
            apply Finset.sum_le_sum
            intro d _
            by_cases h : belongs C keep d (C.source e)
            · simp only [if_pos h]; split_ifs <;> omega
            · simp only [RestrictComparisons.Active,h,false_and,ite_false,le_refl]
          _ = 1 := by simp [belongs,hc]
      · have hc : cluster C keep (C.source e)=none := PairingClusters.cluster_none _ _ _ _ hk
        simp [RestrictComparisons.Active,belongs,hc]
    _ = _ := by simp

/-- The fixed positions in the literal restricted comparison system are exactly
this cluster's old fixed or lost-partner occurrences. -/
def fixedEquiv (c : Cluster C keep) :
    {x : Position (RestrictComparisons.Length (belongs C keep c) (len:=len)) //
      (localC C keep c).pairing.partner x=x} ≃
    {x : Position len // PairingClusters.localBad (fun x : Position len => x.1)
      C.pairing.partner C.pairing.involutive keep c x} where
  toFun x := ⟨RestrictComparisons.embed _ x.val,x.val.1.property,
    (RestrictComparisons.fixed_iff C _ _).mp x.property⟩
  invFun x := by
    have hx : belongs C keep c x.val.1 ∧
        (C.pairing.partner x.val=x.val ∨ ¬belongs C keep c (C.pairing.partner x.val).1) := x.property
    refine ⟨RestrictComparisons.liftPosition _ x.val hx.1,?_⟩
    apply (RestrictComparisons.fixed_iff C _ _).mpr
    simpa only [RestrictComparisons.embed_local] using hx.2
  left_inv x := by rcases x with ⟨⟨⟨t,ht⟩,q⟩,hx⟩; rfl
  right_inv x := by rcases x with ⟨⟨t,q⟩,hx⟩; rfl
lemma fixed_card (c : Cluster C keep) :
    (Finset.univ.filter (fun x => (localC C keep c).pairing.partner x=x)).card=bad C keep c := by
  simpa only [bad,Fintype.card_subtype] using Fintype.card_congr (fixedEquiv C keep c)

lemma local_mass (c : Cluster C keep) :
    (∑ t : {t // belongs C keep c t},len t.val)=mass C keep c := by
  exact (Finset.sum_subtype (Finset.univ.filter (belongs C keep c)) (by intro t; simp) len).symm

lemma short_member {L : ℕ} (c : Cluster C keep) (hc : mass C keep c<L)
    {t : T} (ht : belongs C keep c t) : len t<L := by
  apply lt_of_le_of_lt _ hc
  exact Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩)

/-- With at most one short exceptional piece there is at most one short cluster.
The estimate counts actual retained path lengths, not abstract cluster masses. -/
lemma short_mass {L : ℕ} (root : Option T)
    (ho : ∀ t,root≠some t → L≤len t) :
    (∑ c∈Finset.univ.filter (fun c=>mass C keep c<L),mass C keep c)≤
      ∑ t∈Finset.univ.filter (fun t=>root=some t),len t := by
  simp only [Finset.sum_filter]
  have expand (c : Cluster C keep) :
      (if mass C keep c<L then mass C keep c else 0)=
      ∑ t,if mass C keep c<L then (if belongs C keep c t then len t else 0) else 0 := by
    by_cases h : mass C keep c<L
    · simp only [if_pos h]
      simp only [mass,Finset.sum_filter]
    · simp only [if_neg h,Finset.sum_const_zero]
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t _
  by_cases hr : root=some t
  · rw [if_pos hr]
    by_cases hk : keep t
    · obtain ⟨c,hc⟩ := (cluster_exists C keep).mpr hk
      change cluster C keep t=some c at hc
      simp only [belongs,hc,Option.some.injEq]
      calc
        _ ≤ ∑ d : Cluster C keep,if c=d then len t else 0 := by
          apply Finset.sum_le_sum
          intro d _
          split_ifs <;> omega
        _ = len t := by simp
    · have hc : cluster C keep t=none := PairingClusters.cluster_none _ _ _ _ hk
      simp [belongs,hc]
  · rw [if_neg hr]
    apply Nat.le_zero.mpr
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : mass C keep c<L
    · have hnt : ¬belongs C keep c t := fun h => (not_lt_of_ge (ho t hr)) (short_member C keep c hc h)
      simp only [if_pos hc,if_neg hnt]
    · simp only [if_neg hc]
end TorsionFreeZeroDivisors.ClusterLocalization

end

end OAI
end

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

def pathEquiv (c : Cluster C keep) : {t // belongs C keep c t} ≃
    {v : {t // keep t} // (graph C keep).connectedComponentMk v=c} where
  toFun t := by
    have hk : keep t.val := (cluster_exists C keep).mp ⟨c,t.property⟩
    refine ⟨⟨t.val,hk⟩,?_⟩
    have he := PairingClusters.cluster_some (fun x : Position len => x.1)
      C.pairing.partner C.pairing.involutive keep hk
    exact Option.some.inj (he.symm.trans t.property)
  invFun v := ⟨v.val.val,by
    change PairingClusters.cluster _ _ _ _ v.val.val=some c
    rw [PairingClusters.cluster_some _ _ _ _ v.val.property]
    exact congrArg some v.property⟩
  left_inv t := Subtype.ext rfl
  right_inv v := Subtype.ext (Subtype.ext rfl)

lemma paths_card (c : Cluster C keep) : (paths C keep c).card=(FiniteClusters.block (graph C keep) c).card := by
  simpa only [Fintype.card_subtype,paths,FiniteClusters.block] using Fintype.card_congr (pathEquiv C keep c)
lemma member_exists (c : Cluster C keep) : ∃ t,belongs C keep c t := by
  obtain ⟨v,hv⟩ := FiniteClusters.block_nonempty (graph C keep) c
  let t := (pathEquiv C keep c).symm ⟨v,(FiniteClusters.mem_block _).mp hv⟩
  exact ⟨t.val,t.property⟩

/-- A closed retained subset supplied by recursive separation bounds the
actual connected component, even when the pairing has loops or parallel arcs. -/
lemma paths_card_le {K : ℕ}
    (hs : ∀ t,keep t → ∃ B : Finset T,t∈B ∧ B.card≤K ∧
      ∀ x∈B,∀ y,keep y → PairingClusters.Rel (fun x : Position len=>x.1) C.pairing.partner x y → y∈B)
    (c : Cluster C keep) : (paths C keep c).card≤K := by
  rw [paths_card]
  apply FiniteClusters.block_card
  intro t
  obtain ⟨B,hB,hBK,hcl⟩ := hs t.val t.property
  refine ⟨B.subtype keep,?_,?_,?_⟩
  · simpa only [Finset.mem_subtype] using hB
  · exact (by rw [Finset.card_subtype]; exact Finset.card_filter_le _ _ : (B.subtype keep).card≤B.card).trans hBK
  · intro x hx y hxy
    have hx' : x.val∈B := by simpa only [Finset.mem_subtype] using hx
    have hy := hcl x.val hx' y.val y.property hxy.2
    simpa only [Finset.mem_subtype] using hy

lemma mass_upper {K cap : ℕ} (hK : ∀ c : Cluster C keep,(paths C keep c).card≤K)
    (hcap : ∀ t,len t≤cap) (c : Cluster C keep) : mass C keep c≤K*cap := by
  calc
    _ ≤ ∑ _t∈paths C keep c,cap := Finset.sum_le_sum fun t _=>hcap t
    _ = (paths C keep c).card*cap := by simp
    _ ≤ K*cap := Nat.mul_le_mul_right _ (hK c)

lemma mass_lower {L : ℕ} (hL : ∀ t,L≤len t) (c : Cluster C keep) : L ≤ mass C keep c := by
  obtain ⟨t,ht⟩ := member_exists C keep c
  apply (hL t).trans
  exact Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩)

lemma short_mass_refined {L : ℕ} (root : Option T)
    (ho : ∀ t,root≠some t → L≤len t) :
    (∑ c∈Finset.univ.filter (fun c=>mass C keep c<L),mass C keep c)≤
      ∑ t∈Finset.univ.filter (fun t=>root=some t ∧ len t<L),len t := by
  cases root with
  | none => simpa using short_mass C keep none ho
  | some r =>
    by_cases h : len r<L
    · have he : Finset.univ.filter (fun t=>some r=some t ∧ len t<L)=
          Finset.univ.filter (fun t=>some r=some t) := by
        ext t
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,Option.some.injEq]
        constructor
        · exact And.left
        · intro ht; exact ⟨ht,ht ▸ h⟩
      rw [he]
      exact short_mass C keep (some r) ho
    · have hall : ∀ t,L≤len t := by
        intro t
        by_cases ht : r=t
        · subst t; omega
        · exact ho t (fun he=>ht (Option.some.inj he))
      have hn : ∀ c : Cluster C keep,¬mass C keep c<L :=
        fun c=>not_lt_of_ge (mass_lower C keep hall c)
      simp only [Finset.filter_false_of_mem (fun c _=>hn c),Finset.sum_empty,Nat.zero_le]

lemma short_mass_half {L : ℕ} (root : Option T) (H₀ : ℝ) (hH₀ : 0≤H₀)
    (ho : ∀ t,root≠some t → L≤len t)
    (hr : ∀ t,root=some t → len t<L → (len t:ℝ)≤H₀/2) :
    ((∑ c∈Finset.univ.filter (fun c=>mass C keep c<L),mass C keep c):ℝ)≤H₀/2 := by
  have hh : ((∑ c∈Finset.univ.filter (fun c=>mass C keep c<L),mass C keep c):ℝ)≤
      ((∑ t∈Finset.univ.filter (fun t=>root=some t ∧ len t<L),len t):ℝ) := by
    exact_mod_cast short_mass_refined C keep root ho
  apply hh.trans
  cases root with
  | none => simp only [reduceCtorEq,false_and]; simp; positivity
  | some r =>
    by_cases h : len r<L
    · have he : (Finset.univ.filter (fun t=>some r=some t ∧ len t<L))={r} := by ext t; simp; aesop
      rw [he,Finset.sum_singleton]
      exact hr r rfl h
    · have he : (Finset.univ.filter (fun t=>some r=some t ∧ len t<L))=∅ := by ext t; simp; aesop
      rw [he,Finset.sum_empty]
      positivity
end

open scoped Classical BigOperators
open ComparedBlocks
variable {T E : Type} [Fintype T] [Fintype E] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop)
local instance selectedClusterFintype : Fintype (Cluster C keep) := Fintype.ofFinite _

omit [Fintype E] in
/-- Retained closures are nonnegative; only deleted original positions are
charged in the lower bound for retained mass. -/
lemma retained_original (old : T → ℕ) (ho : ∀ t,old t≤len t) :
    (∑t,old t)≤(∑c,mass C keep c)+∑t∈Finset.univ.filter (fun t=>¬keep t),old t := by
  rw [mass_sum]
  calc
    _ = (∑t∈Finset.univ.filter keep,old t)+∑t∈Finset.univ.filter (fun t=>¬keep t),old t :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ _ := Nat.add_le_add_right (Finset.sum_le_sum fun t _=>ho t) _

/-- An averaging argument on the actual connected components of the
retained pairing graph. E counts oriented interval sides, hence its factor 2. -/
theorem exists_selected (old : T → ℕ) (ho : ∀ t,old t≤len t)
    (root : Option T) (L K cap : ℕ) (H₀ ε C₂ : ℝ)
    (hH₀ : 0<H₀) (hL : 0<L) (hε : 0<ε) (hC₂ : 0<C₂)
    (hsize : ∀ c : Cluster C keep,(paths C keep c).card≤K)
    (hcap : ∀ t,len t≤cap*L)
    (hbase : H₀≤∑t,(old t:ℝ))
    (hdelete : (∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ))≤H₀/16)
    (hbad : ((Finset.univ.filter (fun x : Position len=>C.pairing.partner x=x)).card:ℝ)+
      ((Finset.univ.filter (fun x : Position len=>¬keep x.1 ∧ C.pairing.partner x≠x)).card:ℝ)≤ε/16*H₀)
    (hcompare : (Fintype.card E:ℝ)/2≤C₂/(16*L)*H₀)
    (hlong : ∀ t,root≠some t → L≤len t)
    (hroot : ∀ t,root=some t → len t<L → (len t:ℝ)≤H₀/2) :
    ∃ c : Cluster C keep,L ≤ mass C keep c ∧ mass C keep c≤K*cap*L ∧
      (bad C keep c:ℝ)≤ε*mass C keep c ∧
      (comparisons C keep c:ℝ)/2≤C₂*mass C keep c/L := by
  have hret : 15/16*H₀≤∑c,(mass C keep c:ℝ) := by
    have hh : (∑t,(old t:ℝ))≤(∑c,(mass C keep c:ℝ))+
        ∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ) := by
      exact_mod_cast retained_original C keep old ho
    linarith
  have hb : (∑c,(bad C keep c:ℝ))≤ε/16*H₀ := by
    have hh : (∑c,(bad C keep c:ℝ))≤
        ((Finset.univ.filter (fun x : Position len=>C.pairing.partner x=x)).card:ℝ)+
        ((Finset.univ.filter (fun x : Position len=>¬keep x.1 ∧ C.pairing.partner x≠x)).card:ℝ) := by
      exact_mod_cast bad_sum C keep
    exact hh.trans hbad
  have hi : (∑c,(comparisons C keep c:ℝ)/2)≤C₂/(16*L)*H₀ := by
    rw [←Finset.sum_div]
    apply le_trans _ hcompare
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact_mod_cast comparisons_sum C keep
  have hu : ∀ c : Cluster C keep,(mass C keep c:ℝ)≤(K*cap:ℝ)*L := by
    intro c
    have h := mass_upper C keep hsize hcap c
    rw [←Nat.mul_assoc] at h
    exact_mod_cast h
  have hs : (∑c∈Finset.univ.filter (fun c=>(mass C keep c:ℝ)<L),(mass C keep c:ℝ))≤H₀/2 := by
    have h := short_mass_half C keep root H₀ hH₀.le hlong hroot
    simpa only [Nat.cast_sum,Nat.cast_lt] using h
  obtain ⟨c,hcl,hcu,hcb,hci⟩ := PlanarLocalization.exists_good_cluster
    (fun c=>(mass C keep c:ℝ)) (fun c=>(bad C keep c:ℝ))
    (fun c=>(comparisons C keep c:ℝ)/2) H₀ L ε (K*cap) C₂ hH₀
    (by exact_mod_cast hL) hε hC₂ (fun _=>Nat.cast_nonneg _) (fun _=>Nat.cast_nonneg _)
    (fun _=>by positivity) hu hret hb hi hs
  refine ⟨c,?_,?_,hcb,hci⟩
  · exact_mod_cast hcl
  · exact_mod_cast hcu
end TorsionFreeZeroDivisors.ClusterLocalization
namespace TorsionFreeZeroDivisors.RestrictComparisons
open scoped Classical
variable {T : Type} (root : Option T) (keep : T → Prop)
def rootPath : Option {t // keep t} := root.bind fun t=>if h : keep t then some ⟨t,h⟩ else none
lemma rootPath_some (t : {t // keep t}) : rootPath root keep=some t ↔ root=some t.val := by
  cases root with
  | none => simp [rootPath]
  | some r =>
    by_cases hr : keep r
    · simp only [rootPath,Option.bind_some,dif_pos hr,Option.some.injEq,Subtype.ext_iff]
    · simp only [rootPath,Option.bind_some,dif_neg hr,reduceCtorEq,false_iff,Option.some.injEq]
      intro h; subst r; exact hr t.property
lemma rootPath_cyclic (t : {t // keep t}) : StageRoot.cyclic (rootPath root keep) t=StageRoot.cyclic root t.val := by
  simp only [StageRoot.cyclic,ne_eq,rootPath_some]
lemma rootPath_map {Z : Type} (f : T → Z) {z : Z}
    (h : (rootPath root keep).map (f ∘ Subtype.val)=some z) : root.map f=some z := by
  cases root with
  | none => simp [rootPath] at h
  | some r =>
    by_cases hr : keep r
    · simpa only [rootPath,Option.bind_some,dif_pos hr,Option.map_some,Function.comp_apply] using h
    · simp only [rootPath,Option.bind_some,dif_neg hr,Option.map_none,reduceCtorEq] at h
end TorsionFreeZeroDivisors.RestrictComparisons

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ComparisonGeometry GirthAsymptotics TypedGraphs ActualPatternEvent
attribute [instance] PathSystem.fP PathSystem.fE
namespace PathSystem
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (keep : s.P → Prop)

abbrev restrict : PathSystem rep r x y where
  P := {p // keep p}
  E := {e // RestrictComparisons.Active s.comparisons keep e}
  fP := inferInstance
  fE := inferInstance
  paths := fun p=>s.paths p.val
  nonempty := fun p=>s.nonempty p.val
  root := RestrictComparisons.rootPath s.root keep
  path_chain := fun p=>s.path_chain p.val
  cyclic_chain := by
    intro p hp
    exact s.cyclic_chain p.val ((RestrictComparisons.rootPath_cyclic s.root keep p) ▸ hp)
  comparisons := RestrictComparisons.comparisons s.comparisons keep
  lower := fun e=>s.lower e.val
  upper := fun e=>s.upper e.val
  lower_eq := fun e=>s.lower_eq e.val
  upper_eq := fun e=>s.upper_eq e.val
  lower_le := fun e=>s.lower_le e.val
  upper_le := fun e=>s.upper_le e.val
  reduced := by
    intro p e he
    have hh := s.reduced (RestrictComparisons.embed keep p) e.val
      ((RestrictComparisons.side_some s.comparisons keep p e).mp he)
    rw [←RestrictComparisons.partner_image_of_side s.comparisons keep he] at hh
    exact hh
  rootA := fun z hz=>s.rootA z (RestrictComparisons.rootPath_map s.root keep
    (fun p=>(graph rep r).origin ((s.paths p).head (s.nonempty p))) hz)
  rootB := fun z hz=>s.rootB z (RestrictComparisons.rootPath_map s.root keep
    (fun p=>(graph rep r).origin ((s.paths p).head (s.nonempty p))) hz)
  compatible := by
    intro p e he
    have hh := s.compatible (RestrictComparisons.embed keep p) e.val
      ((RestrictComparisons.side_some s.comparisons keep p e).mp he)
    rw [←RestrictComparisons.partner_image_of_side s.comparisons keep he] at hh
    exact hh

end PathSystem
end TorsionFreeZeroDivisors.SampleGraph
namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open ComparedBlocks ClusterLocalization GirthAsymptotics TypedGraphs ActualPatternEvent
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (keep : s.P → Prop)
local instance : Fintype (Cluster s.comparisons keep) := Fintype.ofFinite _

/-- Realizes the selected component by exactly its literal retained paths and
interval sides, with the same signs, noncoincident lifts, and prescribed root. -/
def selected_bounded {Bnd K I : ℕ} (c : Cluster s.comparisons keep)
    (hP : (ClusterLocalization.paths s.comparisons keep c).card≤K)
    (hE : ClusterLocalization.comparisons s.comparisons keep c≤I)
    (hlo : L (size rep) ≤ mass s.comparisons keep c)
    (hhi : mass s.comparisons keep c≤Bnd*L (size rep))
    (hbad : (bad s.comparisons keep c:ℝ)≤
      StageFusion.epsilon (1/600) 256*mass s.comparisons keep c) :
    BoundedSystem Bnd K I rep r x y := by
  let sc := s.restrict (belongs s.comparisons keep c)
  refine {
    P := {p // belongs s.comparisons keep c p}
    E := {e // RestrictComparisons.Active s.comparisons (belongs s.comparisons keep c) e}
    fP := inferInstance
    fE := inferInstance
    paths := fun p=>s.paths p.val
    nonempty := fun p=>s.nonempty p.val
    root := sc.root
    path_bound := ?_
    comparison_bound := hE
    path_chain := sc.path_chain
    cyclic_chain := sc.cyclic_chain
    length_le := ?_
    length_ge := ?_
    comparisons := localC s.comparisons keep c
    lower := sc.lower
    upper := sc.upper
    lower_eq := sc.lower_eq
    upper_eq := sc.upper_eq
    lower_le := sc.lower_le
    upper_le := sc.upper_le
    reduced := sc.reduced
    unpaired_le := ?_
    rootA := sc.rootA
    rootB := sc.rootB
    compatible := sc.compatible }
  · simpa only [Fintype.card_subtype,ClusterLocalization.paths] using hP
  · rw [local_mass]; exact hhi
  · rw [local_mass]; exact hlo
  · rw [←fixed_card s.comparisons keep c,←local_mass s.comparisons keep c] at hbad
    convert hbad using 2
    congr 1
    ext p
    simp

/-- The analytic union bound excludes the localized system using the sharp
mass and interval estimates. -/
theorem excluded_of_local_totals (K cap : ℕ) (C₂ H₀ : ℝ) (old : s.P → ℕ)
    (ho : ∀ t,old t≤(s.paths t).length)
    (hH₀ : 0<H₀) (hL : 0<L (size rep)) (hC₂ : 0<C₂)
    (hsize : ∀ c : Cluster s.comparisons keep,(ClusterLocalization.paths s.comparisons keep c).card≤K)
    (hcap : ∀ t,(s.paths t).length≤cap*L (size rep))
    (hbase : H₀≤∑t,(old t:ℝ))
    (hdelete : (∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ))≤H₀/16)
    (hbad : ((Finset.univ.filter (fun p=>s.comparisons.pairing.partner p=p)).card:ℝ)+
      ((Finset.univ.filter (fun p=>¬keep p.1 ∧ s.comparisons.pairing.partner p≠p)).card:ℝ)≤
        StageFusion.epsilon (1/600) 256/16*H₀)
    (hcompare : (Fintype.card s.E:ℝ)/2≤C₂/(16*L (size rep))*H₀)
    (hlong : ∀ t,s.root≠some t → L (size rep)≤(s.paths t).length)
    (hroot : ∀ t,s.root=some t → (s.paths t).length<L (size rep) → ((s.paths t).length:ℝ)≤H₀/2)
    (havoid : IsEmpty (BoundedSystem (K*cap) K ⌈2*C₂*(K*cap:ℝ)⌉₊ rep r x y)) : False := by
  have hε : 0<StageFusion.epsilon (1/600) 256 := StageFusion.epsilon_pos (by norm_num) (by norm_num)
  obtain ⟨c,hlo,hhi,hb,hi⟩ := exists_selected s.comparisons keep old ho s.root
    (L (size rep)) K cap H₀ (StageFusion.epsilon (1/600) 256) C₂ hH₀ hL hε hC₂
    hsize hcap hbase hdelete hbad hcompare hlong hroot
  have he : ClusterLocalization.comparisons s.comparisons keep c≤⌈2*C₂*(K*cap:ℝ)⌉₊ := by
    suffices (ClusterLocalization.comparisons s.comparisons keep c:ℝ)≤(⌈2*C₂*(K*cap:ℝ)⌉₊:ℝ) by exact_mod_cast this
    apply le_trans _ (Nat.le_ceil _)
    have hLr : (0:ℝ)<L (size rep) := by exact_mod_cast hL
    have hi' := (le_div_iff₀ hLr).mp hi
    have hh : (mass s.comparisons keep c:ℝ)≤(K*cap:ℝ)*L (size rep) := by exact_mod_cast hhi
    have hm := mul_le_mul_of_nonneg_left hh hC₂.le
    nlinarith
  exact havoid.false (s.selected_bounded keep c (hsize c) he hlo hhi hb)
end TorsionFreeZeroDivisors.SampleGraph.PathSystem

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.BalancedPieces
open scoped Classical BigOperators

def count (h cap : ℕ) : ℕ := (h+cap-1)/cap
def length (h m : ℕ) (i : Fin m) : ℕ := h/m + if i.val<h%m then 1 else 0
lemma sum_length (h m : ℕ) (hm : 0 < m) : (∑ i,length h m i)=h := by
  unfold length
  rw [Finset.sum_add_distrib]
  have hi : (∑ i : Fin m,if i.val<h%m then 1 else 0)=h%m := by
    rw [←Finset.sum_filter]
    have he : (Finset.univ.filter (fun i : Fin m => i.val<h%m))=Finset.Iio ⟨h%m,Nat.mod_lt _ hm⟩ := by
      ext i
      simp [Fin.lt_def]
    rw [he,Finset.sum_const,Fin.card_Iio,smul_eq_mul,mul_one]
  rw [hi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  exact Nat.div_add_mod h m
lemma length_pos (h m : ℕ) (hm : m≤h) (hm0 : 0 < m) (i : Fin m) : 0<length h m i := by
  have hh : 0<h/m := (Nat.div_pos_iff).mpr ⟨hm0,hm⟩
  unfold length
  omega
lemma count_bounds {h cap : ℕ} (hc : 0<cap) (hh : cap<h) :
    2≤count h cap ∧ h≤count h cap*cap ∧ (count h cap-1)*cap<h := by
  have h1 := Nat.div_mul_le_self (h+cap-1) cap
  have h2 := Nat.lt_div_mul_add (a:=h+cap-1) hc
  dsimp only [count]
  have h3 : 2≤(h+cap-1)/cap := by
    apply (Nat.le_div_iff_mul_le hc).mpr
    omega
  constructor
  · exact h3
  constructor
  · omega
  · rw [Nat.mul_sub_right_distrib]
    omega
lemma count_le {h cap : ℕ} (hc : 1≤cap) (hh : cap<h) : count h cap≤h := by
  have hb := count_bounds (by omega : 0<cap) hh
  have hm := Nat.mul_le_mul_left (count h cap-1) hc
  omega
lemma quotient_bounds {h cap : ℕ} (hc : 6≤cap) (hh : cap<h) :
    cap≤3*(h/count h cap) ∧ (h/count h cap)+(if h%count h cap=0 then 0 else 1)≤cap := by
  obtain ⟨hm,hup,hlo⟩ := count_bounds (by omega : 0<cap) hh
  have hdiv := Nat.div_add_mod h (count h cap)
  have hrem := Nat.mod_lt h (by omega : 0<count h cap)
  have hprod : (count h cap-1)*cap=count h cap*cap-cap := by simp only [Nat.mul_sub_right_distrib,one_mul]
  have hmcap : cap≤count h cap*cap := by nlinarith
  have hlow' : count h cap*cap-cap<h := by rwa [hprod] at hlo
  constructor
  · by_contra hn
    have hq : 3*(h/count h cap)<cap := by omega
    have h2 : 2*(h/count h cap+1)≤cap := by omega
    have h2m := Nat.mul_le_mul_left (count h cap) h2
    have hmc := Nat.mul_le_mul_right cap hm
    have hlow'' : count h cap*cap<h+cap := by omega
    nlinarith only [h2m,hmc,hlow'',hdiv,hrem]
  · split_ifs with hr
    · have hq := Nat.div_le_of_le_mul hup
      simpa using hq
    · have hrp : 0<h%count h cap := by omega
      by_contra hn
      have hq : cap≤h/count h cap := by omega
      nlinarith
lemma length_bounds {h cap : ℕ} (hc : 6≤cap) (hh : cap<h) (i : Fin (count h cap)) :
    cap≤3*length h (count h cap) i ∧ length h (count h cap) i≤cap := by
  obtain ⟨hl,hu⟩ := quotient_bounds hc hh
  unfold length
  constructor
  · split_ifs <;> omega
  · by_cases hr : h%count h cap=0
    · rw [if_pos hr] at hu
      simp only [hr,Nat.not_lt_zero,ite_false,add_zero]
      exact hu
    · rw [if_neg hr] at hu
      split_ifs <;> omega
lemma count_charge {h cap : ℕ} (hc : 6≤cap) (hh : cap<h) : count h cap*cap≤3*h := by
  have hs := sum_length h (count h cap) (by have hb := count_bounds (by omega : 0<cap) hh; omega)
  have hi : (∑ i : Fin (count h cap),cap)≤∑ i : Fin (count h cap),3*length h (count h cap) i :=
    Finset.sum_le_sum fun i _ => (length_bounds hc hh i).1
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,←Finset.mul_sum,hs] using hi

def number (h cap : ℕ) : ℕ := if h≤cap then 1 else count h cap
def sizes (h cap : ℕ) (i : Fin (number h cap)) : ℕ :=
  if h≤cap then h else length h (number h cap) i
lemma number_pos {h cap : ℕ} (hc : 0<cap) : 0<number h cap := by
  by_cases hh : h≤cap
  · simp only [number,if_pos hh]; omega
  · have hb := (count_bounds hc (show cap<h by omega)).1
    simp only [number,if_neg hh]
    omega
lemma sizes_sum {h cap : ℕ} (hc : 0<cap) : (∑ i,sizes h cap i)=h := by
  by_cases hh : h≤cap
  · have hn : number h cap=1 := if_pos hh
    simp only [sizes,if_pos hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,hn,one_smul]
  · simp only [sizes,if_neg hh]
    exact sum_length h (number h cap) (number_pos hc)
lemma sizes_pos {h cap : ℕ} (hc : 0<cap) (hh : 0<h) (i : Fin (number h cap)) : 0<sizes h cap i := by
  by_cases hle : h≤cap
  · simpa only [sizes,if_pos hle] using hh
  · simp only [sizes,if_neg hle]
    apply length_pos _ _ _ (number_pos hc)
    simp only [number,if_neg hle]
    exact count_le hc (by omega)
lemma sizes_upper {h cap : ℕ} (hc : 6≤cap) (i : Fin (number h cap)) : sizes h cap i≤cap := by
  by_cases hh : h≤cap
  · simpa only [sizes,if_pos hh] using hh
  · simp only [sizes,if_neg hh]
    have he : number h cap=count h cap := if_neg hh
    have hb := (length_bounds hc (show cap<h by omega) (Fin.cast he i)).2
    convert hb using 1
    unfold length
    simp only [Fin.val_cast,he]
lemma sizes_lower_long {h cap : ℕ} (hc : 6≤cap) (hh : cap<h) (i : Fin (number h cap)) :
    cap≤3*sizes h cap i := by
  have hn : ¬h≤cap := by omega
  simp only [sizes,if_neg hn]
  have hi : number h cap=count h cap := if_neg hn
  have hb := (length_bounds hc hh (Fin.cast hi i)).1
  convert hb using 1
  unfold length
  simp only [Fin.val_cast,hi]
lemma number_charge {h cap : ℕ} (hc : 6≤cap) :
    (if cap<h then number h cap else 0)*cap≤3*h := by
  by_cases hh : cap<h
  · simp only [if_pos hh,number,if_neg (show ¬h≤cap by omega)]
    exact count_charge hc hh
  · simp only [if_neg hh,Nat.zero_mul,Nat.zero_le]
end TorsionFreeZeroDivisors.BalancedPieces
namespace TorsionFreeZeroDivisors.ConsecutivePieces
open scoped Classical BigOperators
variable {A : Type*} {m : ℕ} (l : List A) (n : Fin m → ℕ) (hs : (∑ i,n i)=l.length)

def index : ((i : Fin m) × Fin (n i)) ≃ Fin l.length := finSigmaFinEquiv.trans (finCongr hs)
def offset (i : Fin m) : ℕ := ∑ j : Fin i.val,n (Fin.castLE i.isLt.le j)
lemma index_val (i : Fin m) (j : Fin (n i)) : (index l n hs ⟨i,j⟩).val=offset n i+j.val := by
  simp only [index,Equiv.trans_apply,finCongr_apply,Fin.val_cast,finSigmaFinEquiv_apply,offset]
def segment (i : Fin m) : List A := List.ofFn fun j : Fin (n i) => l[index l n hs ⟨i,j⟩]
lemma length_segment (i : Fin m) : (segment l n hs i).length=n i := List.length_ofFn
lemma successor_index (i : Fin m) (j : ℕ) (hj : j+1<n i) :
    (index l n hs ⟨i,⟨j+1,hj⟩⟩).val=(index l n hs ⟨i,⟨j,by omega⟩⟩).val+1 := by
  rw [index_val,index_val]
  change offset n i+(j+1)=offset n i+j+1
  omega
lemma segment_chain {R : A → A → Prop} (hp : l.IsChain R) (i : Fin m) :
    (segment l n hs i).IsChain R := by
  rw [List.isChain_iff_getElem]
  intro j hj
  have hj' : j+1<n i := by simpa only [length_segment] using hj
  have he := successor_index l n hs i j hj'
  have hb := (index l n hs ⟨i,⟨j+1,hj'⟩⟩).isLt
  have hp' := (List.isChain_iff_getElem.mp hp) (index l n hs ⟨i,⟨j,by omega⟩⟩).val (by omega)
  simp only [segment,List.getElem_ofFn]
  change R l[(index l n hs ⟨i,⟨j,by omega⟩⟩).val] l[(index l n hs ⟨i,⟨j+1,hj'⟩⟩).val]
  simpa only [←he] using hp'
end TorsionFreeZeroDivisors.ConsecutivePieces
namespace TorsionFreeZeroDivisors.BalancedWords
open scoped Classical BigOperators
variable {T A : Type} (w : T → List A) (cap : ℕ) (hc : 0<cap)
abbrev Piece := (t : T) × Fin (BalancedPieces.number (w t).length cap)
def old (p : Piece w cap) : ℕ := BalancedPieces.sizes (w p.1).length cap p.2
def segment (p : Piece w cap) : List A :=
  ConsecutivePieces.segment (w p.1) (BalancedPieces.sizes (w p.1).length cap)
    (BalancedPieces.sizes_sum (h:=(w p.1).length) hc) p.2
lemma segment_length (p : Piece w cap) : (segment w cap hc p).length=old w cap p :=
  ConsecutivePieces.length_segment _ _ _ _
include hc in
lemma old_pos (hpos : ∀ t,(w t)≠[]) (p : Piece w cap) : 0<old w cap p :=
  BalancedPieces.sizes_pos hc (List.length_pos_iff.mpr (hpos p.1)) p.2
lemma segment_nonempty (hpos : ∀ t,(w t)≠[]) (p : Piece w cap) : segment w cap hc p≠[] := by
  apply List.length_pos_iff.mp
  rw [segment_length]
  exact old_pos w cap hc hpos p
lemma segment_chain {R : A → A → Prop} (h : ∀ t,(w t).IsChain R) (p : Piece w cap) :
    (segment w cap hc p).IsChain R := ConsecutivePieces.segment_chain _ _ _ (h p.1) p.2
lemma old_le (hcap : 6≤cap) (p : Piece w cap) : old w cap p≤cap :=
  BalancedPieces.sizes_upper hcap p.2
lemma intact (p : Piece w cap) (hp : (w p.1).length≤cap) : segment w cap hc p=w p.1 := by
  have hi : p.2.val=0 := by
    have hh := p.2.isLt
    have hh' : p.2.val<1 := by simpa only [BalancedPieces.number,if_pos hp] using hh
    omega
  apply List.ext_getElem
  · rw [segment_length]
    simp only [old,BalancedPieces.sizes,if_pos hp]
  · intro j hj hk
    have hj' : j<BalancedPieces.sizes (w p.1).length cap p.2 := by simpa only [segment_length,old] using hj
    simp only [segment,ConsecutivePieces.segment,List.getElem_ofFn,Fin.getElem_fin]
    congr 1
    rw [ConsecutivePieces.index_val]
    have hz : ConsecutivePieces.offset (BalancedPieces.sizes (w p.1).length cap) p.2=0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hilt := i.isLt
      omega
    rw [hz,zero_add]

variable [Fintype T]
include hc in
lemma old_sum : (∑p : Piece w cap,old w cap p)=∑t,(w t).length := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  exact BalancedPieces.sizes_sum (h:=(w t).length) hc

/-- Quantitative closing, before identifying the added positions as fixed.
Only genuinely split words get closure terms. -/
lemma closure_charge (tail : Piece w cap → List A) (tailCap : ℕ) (hcap : 6≤cap)
    (hshort : ∀ p,(w p.1).length≤cap → tail p=[])
    (htail : ∀ p,(tail p).length≤tailCap) :
    cap*(∑p,(tail p).length)≤3*tailCap*(∑t,(w t).length) := by
  rw [Fintype.sum_sigma,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  by_cases hs : (w t).length≤cap
  · have he : ∀ i : Fin (BalancedPieces.number (w t).length cap),tail ⟨t,i⟩=[] := fun i=>hshort ⟨t,i⟩ hs
    simp only [he,List.length_nil,Finset.sum_const_zero,Nat.mul_zero,Nat.zero_le]
  · have hsum : (∑i : Fin (BalancedPieces.number (w t).length cap),(tail ⟨t,i⟩).length)≤
        BalancedPieces.number (w t).length cap*tailCap := by
      calc
        _ ≤ ∑_i : Fin (BalancedPieces.number (w t).length cap),tailCap := Finset.sum_le_sum fun i _=>htail ⟨t,i⟩
        _ = _ := by simp
    have hcount := BalancedPieces.number_charge (h:= (w t).length) hcap
    rw [if_pos (show cap<(w t).length by omega)] at hcount
    have ha := Nat.mul_le_mul_left cap hsum
    have hb := Nat.mul_le_mul_right tailCap hcount
    nlinarith
end TorsionFreeZeroDivisors.BalancedWords
namespace TorsionFreeZeroDivisors.ShortClosure
open PortSubdivision WeightedMoore.PortWalk
variable {V D : Type} (Γ : PortGraph V D)
lemma endpoint_cons' (a : V) (d : D) (p : List D) :
    endpoint Γ a (d::p)=endpoint Γ (Γ.origin (Γ.reverse d)) p := by
  cases p with
  | nil => rfl
  | cons e p => simp only [endpoint,List.getLast?_cons,Option.map_some,Option.getD_some]

lemma ReducedPath.exists_walk {a b : V} {p : List D} (hp : ReducedPath Γ a b p) :
    ∃ q : Γ.Walk a b,q.darts=p := by
  induction p generalizing a with
  | nil =>
    have he : a=b := hp.finish
    subst b
    exact ⟨.nil a,rfl⟩
  | cons d p ih =>
    have hc := List.isChain_cons.mp hp.chain
    have ht : ReducedPath Γ (Γ.origin (Γ.reverse d)) b p := {
      chain := hc.2
      start := fun e he=>(hc.1 e he).1.symm
      finish := by rw [←endpoint_cons' Γ a d p]; exact hp.finish }
    obtain ⟨q,hq⟩ := ih ht
    exact ⟨.cons d (hp.start d (by simp)) q,by simp only [PortGraph.Walk.darts,hq]⟩

lemma ReducedPath.length_ge {a : V} {p : List D} (hp : ReducedPath Γ a a p)
    (hn : p≠[]) (L : ℕ) (hg : (3*L:ℕ)≤Γ.subdivision.egirth) : L≤p.length := by
  obtain ⟨q,hq⟩ := hp.exists_walk Γ
  have hr : q.IsReduced := by
    rw [PortGraph.Walk.IsReduced,hq]
    exact hp.chain.imp (fun _ _ h=>h.2)
  have hn' : 0<q.length := by rw [←q.length_darts,hq]; exact List.length_pos_iff.mpr hn
  have hh := TypedGraphs.reduced_circuit_length Γ L hg q hr hn'
  simpa only [←q.length_darts,hq] using hh

lemma of_cyclic {p : List D} (hn : p≠[])
    (hch : p.IsChain (step Γ.origin Γ.reverse))
    (hc : ∀ᵉ (x∈p.getLast?) (y∈p.head?),step Γ.origin Γ.reverse x y) :
    ReducedPath Γ (Γ.origin (p.head hn)) (Γ.origin (p.head hn)) p where
  chain := hch
  start := by
    intro d hd
    rw [List.head?_eq_some_head hn] at hd
    exact congrArg Γ.origin (Option.some.inj hd.symm)
  finish := by
    have h := (hc (p.getLast hn) (List.getLast_mem_getLast? hn) (p.head hn) (List.head_mem_head? hn)).1
    simpa only [endpoint,List.getLast?_eq_some_getLast hn,Option.map_some,Option.getD_some] using h
end TorsionFreeZeroDivisors.ShortClosure
namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap)
    (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
abbrev Piece := BalancedWords.Piece s.paths cap
abbrev seg (p : Piece s cap) := BalancedWords.segment s.paths cap hc p
abbrev seg_ne (p : Piece s cap) : seg s cap hc p≠[] :=
  BalancedWords.segment_nonempty s.paths cap hc s.nonempty p
abbrev start (p : Piece s cap) := (graph rep r).origin ((seg s cap hc p).head (seg_ne s cap hc p))
lemma segment_path (p : Piece s cap) :
    ShortClosure.ReducedPath (graph rep r) (start s cap hc p)
      (ShortClosure.endpoint (graph rep r) (start s cap hc p) (seg s cap hc p)) (seg s cap hc p) where
  chain := BalancedWords.segment_chain s.paths cap hc s.path_chain p
  start := by
    intro d hd
    rw [List.head?_eq_some_head (seg_ne s cap hc p)] at hd
    exact congrArg (graph rep r).origin (Option.some.inj hd.symm)
  finish := rfl

def chosenTail (p : Piece s cap) : List (DA rep⊕DB rep) :=
  (SampleGraph.short_closure rep r hL hd (segment_path s cap hc p) (seg_ne s cap hc p)).choose
lemma chosenTail_spec (p : Piece s cap) :
    (chosenTail s cap hc hL hd p).length≤ D*L (size rep) ∧
      ShortClosure.ReducedPath (graph rep r) (start s cap hc p) (start s cap hc p)
        (seg s cap hc p++chosenTail s cap hc hL hd p) ∧
      ∀ᵉ (a∈(seg s cap hc p++chosenTail s cap hc hL hd p).getLast?)
          (b∈(seg s cap hc p++chosenTail s cap hc hL hd p).head?),
        PortWalk.step (graph rep r).origin (graph rep r).reverse a b :=
  (SampleGraph.short_closure rep r hL hd (segment_path s cap hc p) (seg_ne s cap hc p)).choose_spec

def tail (p : Piece s cap) : List (DA rep⊕DB rep) :=
  if (s.paths p.1).length≤cap then [] else chosenTail s cap hc hL hd p
def word (p : Piece s cap) : List (DA rep⊕DB rep) := seg s cap hc p++tail s cap hc hL hd p
lemma tail_short (p : Piece s cap) (hp : (s.paths p.1).length≤cap) : tail s cap hc hL hd p=[] := if_pos hp
lemma tail_bound (p : Piece s cap) : (tail s cap hc hL hd p).length≤D*L (size rep) := by
  unfold tail
  split_ifs
  · simp only [List.length_nil,Nat.zero_le]
  · exact (chosenTail_spec s cap hc hL hd p).1
lemma word_short (p : Piece s cap) (hp : (s.paths p.1).length≤cap) : word s cap hc hL hd p=s.paths p.1 := by
  rw [word,tail_short s cap hc hL hd p hp,List.append_nil]
  exact BalancedWords.intact s.paths cap hc p hp
lemma nonempty (p : Piece s cap) : word s cap hc hL hd p≠[] := by
  intro h
  exact seg_ne s cap hc p (List.append_eq_nil_iff.mp h).1
lemma chain (p : Piece s cap) :
    (word s cap hc hL hd p).IsChain (PortWalk.step (graph rep r).origin (graph rep r).reverse) := by
  by_cases hp : (s.paths p.1).length≤cap
  · rw [word_short s cap hc hL hd p hp]
    exact s.path_chain p.1
  · simpa only [word,tail,if_neg hp] using (chosenTail_spec s cap hc hL hd p).2.1.chain
lemma cyclic_of_long (p : Piece s cap) (hp : cap<(s.paths p.1).length) :
    ∀ᵉ (a∈(word s cap hc hL hd p).getLast?) (b∈(word s cap hc hL hd p).head?),
      PortWalk.step (graph rep r).origin (graph rep r).reverse a b := by
  simpa only [word,tail,if_neg (show ¬(s.paths p.1).length≤cap by omega)] using
    (chosenTail_spec s cap hc hL hd p).2.2

lemma original_girth (hr : r∈samples rep) (t : s.P) (ht : s.root≠some t) : L (size rep)≤(s.paths t).length := by
  have hc' := s.cyclic_chain t (by simp only [StageRoot.cyclic,decide_eq_true_eq]; exact ht)
  exact (ShortClosure.of_cyclic (graph rep r) (s.nonempty t) (s.path_chain t) hc').length_ge
    (graph rep r) (s.nonempty t) (L (size rep)) (girth rep r hr)

lemma old_le_word (p : Piece s cap) : BalancedWords.old s.paths cap p≤(word s cap hc hL hd p).length := by
  simp only [word,List.length_append,BalancedWords.segment_length]
  omega
lemma word_bound (hcap : 6≤cap) (p : Piece s cap) : (word s cap hc hL hd p).length≤cap+D*L (size rep) := by
  have ho := BalancedWords.old_le s.paths cap hcap p
  have ht := tail_bound s cap hc hL hd p
  simp only [word,List.length_append,BalancedWords.segment_length]
  omega
lemma total_added (hcap : 6≤cap) : cap*(∑p : Piece s cap,(tail s cap hc hL hd p).length)≤
    3*(D*L (size rep))*(∑t,(s.paths t).length) :=
  BalancedWords.closure_charge s.paths cap (tail s cap hc hL hd) (D*L (size rep)) hcap
    (tail_short s cap hc hL hd) (tail_bound s cap hc hL hd)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

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
def root : Option (Piece s cap) := s.root.bind fun t=>
  if (s.paths t).length≤cap then some ⟨t,⟨0,BalancedPieces.number_pos hc⟩⟩ else none
lemma piece_eq (p q : Piece s cap) (h : p.1=q.1) (hp : (s.paths p.1).length≤cap) : p=q := by
  rcases p with ⟨t,i⟩
  rcases q with ⟨u,j⟩
  dsimp only at h hp
  subst u
  have hij : i=j := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    simp only [BalancedPieces.number,if_pos hp] at hi hj
    omega
  cases hij
  rfl
lemma root_eq_some (p : Piece s cap) : root s cap hc=some p ↔ s.root=some p.1 ∧ (s.paths p.1).length≤cap := by
  cases hr : s.root with
  | none => simp [root,hr]
  | some t =>
    by_cases ht : (s.paths t).length≤cap
    · simp only [root,hr,Option.bind_some,if_pos ht,Option.some.injEq]
      constructor
      · intro h
        rw [←h]
        exact ⟨rfl,ht⟩
      · intro h
        exact piece_eq s cap _ p h.1 ht
    · simp only [root,hr,Option.bind_some,if_neg ht,Option.some.injEq]
      constructor
      · intro h; cases h
      · intro h; exact False.elim (ht (h.1 ▸ h.2))
lemma cyclic_iff {T : Type} (root : Option T) (t : T) :
    StageRoot.cyclic root t=true ↔ root≠some t := by
  simp only [StageRoot.cyclic,decide_eq_true_eq]
lemma cyclic (p : Piece s cap) (hp : StageRoot.cyclic (root s cap hc) p=true) :
    ∀ᵉ (a∈(word s cap hc hL hd p).getLast?) (b∈(word s cap hc hL hd p).head?),
      PortWalk.step (graph rep r).origin (graph rep r).reverse a b := by
  have hp' := (cyclic_iff (root s cap hc) p).mp hp
  by_cases hs : (s.paths p.1).length≤cap
  · rw [word_short s cap hc hL hd p hs]
    apply s.cyclic_chain
    apply (cyclic_iff _ _).mpr
    intro he
    exact hp' ((root_eq_some s cap hc p).mpr ⟨he,hs⟩)
  · exact cyclic_of_long s cap hc hL hd p (by omega)
lemma root_start (p : Piece s cap) (hp : root s cap hc=some p) :
    (word s cap hc hL hd p).head (nonempty s cap hc hL hd p)=(s.paths p.1).head (s.nonempty p.1) := by
  have hs := ((root_eq_some s cap hc p).mp hp).2
  simp only [word_short s cap hc hL hd p hs]
lemma rootA (z : VA rep) (hz : (root s cap hc).map (fun p=>(graph rep r).origin
      ((word s cap hc hL hd p).head (nonempty s cap hc hL hd p)))=some (.inl z)) : z=x := by
  obtain ⟨p,hp,he⟩ := Option.map_eq_some_iff.mp hz
  apply s.rootA z
  have hh := (root_eq_some s cap hc p).mp hp
  rw [hh.1,Option.map_some]
  rw [root_start s cap hc hL hd p hp] at he
  exact congrArg some he
lemma rootB (z : VB rep) (hz : (root s cap hc).map (fun p=>(graph rep r).origin
      ((word s cap hc hL hd p).head (nonempty s cap hc hL hd p)))=some (.inr z)) : z=y := by
  obtain ⟨p,hp,he⟩ := Option.map_eq_some_iff.mp hz
  apply s.rootB z
  have hh := (root_eq_some s cap hc p).mp hp
  rw [hh.1,Option.map_some]
  rw [root_start s cap hc hL hd p hp] at he
  exact congrArg some he
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords
namespace TorsionFreeZeroDivisors.SingleException
open scoped Classical BigOperators
variable {T : Type} [Fintype T] (root : Option T) (f : T → ℕ) (L : ℕ)
lemma cardinal_charge (h : ∀t,root≠some t → L≤f t) : Fintype.card T*L≤(∑t,f t)+L := by
  classical
  have hsum : (∑_t : T,L)≤∑t,(f t+if root=some t then L else 0) := by
    apply Finset.sum_le_sum
    intro t _
    by_cases ht : root=some t
    · simp only [if_pos ht]; omega
    · simpa only [if_neg ht,Nat.add_zero] using h t ht
  rw [Finset.sum_add_distrib] at hsum
  have he : (∑t : T,if root=some t then L else 0)≤L := by
    cases root with
    | none => simp
    | some t => simp
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hsum
  omega
lemma two_mass (a b : T) (hab : a≠b) : f a+f b≤∑t,f t := by
  classical
  have h := Finset.sum_le_sum_of_subset (s:={a,b}) (t:=Finset.univ) (f:=f) (by simp)
  simpa only [Finset.sum_pair hab] using h
lemma divide_cast {U L D A H : ℕ} (hU : 0<U) (hL : 0<L)
    (h : U*L*A≤3*(D*L)*H) : (A:ℝ)≤3*(D:ℝ)/U*(H:ℝ) := by
  have hh : (U:ℝ)*L*A≤3*((D:ℝ)*L)*H := by exact_mod_cast h
  have hu : (0:ℝ)<U := by exact_mod_cast hU
  have hl : (0:ℝ)<L := by exact_mod_cast hL
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hu).mpr
  nlinarith
end TorsionFreeZeroDivisors.SingleException
namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (U : ℕ) (hU : 3≤U)
    (hL : 1≤L (size rep)) (hcap : 6≤U*L (size rep))
    (hd : GraphSample.Diameters rep r) (hr : r∈samples rep)
    (hordinary : ∃t,s.root≠some t)
abbrev cap_pos : 0<U*L (size rep) := lt_of_lt_of_le (by norm_num : 0<6) hcap
abbrev H₀ : ℕ := ∑t,(s.paths t).length
include hr hordinary in
lemma H₀_ge : L (size rep)≤H₀ s := by
  obtain ⟨t,ht⟩ := hordinary
  exact (original_girth s hr t ht).trans (Finset.single_le_sum (f:=fun t=>(s.paths t).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ t))
include hU hr in
lemma old_lower (p : Piece s (U*L (size rep)))
    (hp : root s _ (cap_pos U hcap)≠some p) :
    L (size rep)≤BalancedWords.old s.paths (U*L (size rep)) p := by
  have hc := cap_pos U hcap
  by_cases hs : (s.paths p.1).length≤U*L (size rep)
  · have ht : s.root≠some p.1 := fun he=>hp ((root_eq_some s _ hc p).mpr ⟨he,hs⟩)
    simp only [BalancedWords.old,BalancedPieces.sizes,if_pos hs]
    exact original_girth s hr p.1 ht
  · have hh := BalancedPieces.sizes_lower_long hcap (by omega : U*L (size rep)<(s.paths p.1).length) p.2
    change L (size rep)≤BalancedPieces.sizes (s.paths p.1).length (U*L (size rep)) p.2
    nlinarith
include hU hcap hr hordinary in
lemma piece_charge : Fintype.card (Piece s (U*L (size rep)))*L (size rep)≤2*H₀ s := by
  have hh := SingleException.cardinal_charge (root s _ (cap_pos U hcap)) (BalancedWords.old s.paths _) (L (size rep))
    (old_lower s U hU hcap hr)
  rw [BalancedWords.old_sum s.paths _ (cap_pos U hcap)] at hh
  have hH := H₀_ge s hr hordinary
  change L (size rep)≤∑t,(s.paths t).length at hH
  change _≤2*(∑t,(s.paths t).length)
  omega
include hU hr in
lemma lower_word (p : Piece s (U*L (size rep)))
    (hp : root s _ (cap_pos U hcap)≠some p) :
    L (size rep)≤(word s _ (cap_pos U hcap) hL hd p).length :=
  (old_lower s U hU hcap hr p hp).trans (old_le_word s _ (cap_pos U hcap) hL hd p)
include hr hordinary in
lemma root_mass (p : Piece s (U*L (size rep)))
    (hp : root s _ (cap_pos U hcap)=some p)
    (hshort : (word s _ (cap_pos U hcap) hL hd p).length<L (size rep)) :
    2*(word s _ (cap_pos U hcap) hL hd p).length≤H₀ s := by
  obtain ⟨t,ht⟩ := hordinary
  have hs := (root_eq_some s _ (cap_pos U hcap) p).mp hp
  have hne : p.1≠t := by intro h; exact ht (h ▸ hs.1)
  have hg := original_girth s hr t ht
  have hsum := SingleException.two_mass (fun t=> (s.paths t).length) p.1 t hne
  rw [word_short s _ (cap_pos U hcap) hL hd p hs.2] at hshort ⊢
  change _≤∑t,(s.paths t).length
  omega
include hU in
lemma added_real : (∑p : Piece s (U*L (size rep)),((tail s _ (cap_pos U hcap) hL hd p).length:ℝ))≤
    3*(D:ℝ)/U*(H₀ s:ℝ) := by
  have h := total_added s _ (cap_pos U hcap) hL hd hcap
  have hh := SingleException.divide_cast (U:=U) (L:=L (size rep)) (D:=D)
    (A:=∑p : Piece s (U*L (size rep)),(tail s _ (cap_pos U hcap) hL hd p).length)
    (H:=H₀ s) (by omega) (by omega) h
  rw [Nat.cast_sum] at hh
  exact hh
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
lemma mem_of_mem {c : Cycle f} {x : O} (hx : x∈members f c) : f x∈members f c := by
  simpa only [mem_members,cycle_apply] using hx
lemma card_one_fixed {x : O} (h : (members f (cycle f x)).card=1) : f x=x := by
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h
  have hx : x∈members f (cycle f x) := (mem_members f).mpr rfl
  have hf := mem_of_mem f hx
  rw [ha,Finset.mem_singleton] at hx hf
  exact hf.trans hx.symm
lemma card_le_two_square {x : O} (h : (members f (cycle f x)).card≤2) : f (f x)=x := by
  by_contra hn
  have hfx : f x≠x := fun he => hn (by rw [he,he])
  have hff : f (f x)≠f x := fun he => hfx (f.injective he)
  have hx : x∈members f (cycle f x) := (mem_members f).mpr rfl
  have hs : {x,f x,f (f x)}⊆members f (cycle f x) := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl
    · exact hx
    · exact mem_of_mem f hx
    · exact mem_of_mem f (mem_of_mem f hx)
  have hc := (Finset.card_le_card hs).trans h
  have he : ({x,f x,f (f x)} : Finset O).card=3 := by
    simp [Ne.symm hfx,Ne.symm hn,Ne.symm hff]
  omega

def fixed : Finset O := Finset.univ.filter (fun x => f x=x)
lemma fixed_le_cycles : (fixed f).card≤Fintype.card (Cycle f) := by
  have hi : Function.Injective (fun x : {x // x∈fixed f} => cycle f x.val) := by
    intro x y he
    apply Subtype.ext
    exact ((cycle_eq f).mp he).eq_of_left ((Finset.mem_filter.mp x.property).2)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hi
lemma singleton_cycles_le_fixed :
    (Finset.univ.filter (fun c : Cycle f => (members f c).card=1)).card≤(fixed f).card := by
  let pick : {c : Cycle f // (members f c).card=1} → {x // x∈fixed f} := fun c =>
    ⟨Quotient.out c.val,by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      apply card_one_fixed f
      have he : cycle f (Quotient.out c.val)=c.val := Quotient.out_eq c.val
      simpa only [he] using c.property⟩
  have hi : Function.Injective pick := by
    intro c d he
    apply Subtype.ext
    have h := congrArg (fun x : {x // x∈fixed f} => cycle f x.val) he
    simpa only [pick,cycle,Quotient.out_eq] using h
  simpa only [Fintype.card_subtype,Finset.filter_mem_eq_inter,Finset.univ_inter] using Fintype.card_le_of_injective pick hi
lemma sum_card : (∑ c : Cycle f,(members f c).card)=Fintype.card O := by
  have h := Finset.card_eq_sum_card_fiberwise (f:=cycle f)
    (s:=Finset.univ) (t:=Finset.univ) (fun _ _ => Finset.mem_univ _)
  exact h.symm
lemma large_count :
    (∑ c∈Finset.univ.filter (fun c : Cycle f => 3≤(members f c).card),(members f c).card)=
     (Finset.univ.filter (fun x : O => 3≤(members f (cycle f x)).card)).card := by
  calc
    _ = (Finset.univ.filter (fun x : O => cycle f x∈Finset.univ.filter
      (fun c : Cycle f => 3≤(members f c).card))).card :=
      Finset.sum_card_fiberwise_eq_card_filter _ _ (cycle f)
    _ = _ := by congr 1; ext x; simp

end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.PlanarRotation
open scoped Classical BigOperators
open PermutationCycles
lemma excess_identity {C : Type} [Fintype C] (len : C→ℕ) (hp : ∀ c,0<len c) :
    (∑ c,(len c-2))+2*Fintype.card C=(∑ c,len c)+
      (Finset.univ.filter (fun c => len c=1)).card := by
  calc
    _ = ∑ c,(len c-2+2) := by simp [Finset.sum_add_distrib,Nat.mul_comm]
    _ = ∑ c,(len c+if len c=1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro c _
      have h := hp c
      split_ifs <;> omega
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_boole,Nat.cast_id]
lemma large_sum_le {C : Type} [Fintype C] (len : C→ℕ) :
    (∑ c∈Finset.univ.filter (fun c => 3≤len c),len c)≤3*∑ c,(len c-2) := by
  rw [Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  split_ifs <;> omega

variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
def bad : Finset O := Finset.univ.filter (fun x => ¬Good σ α x)
lemma bad_card_bound :
    (bad σ α).card≤(fixed (opposite σ α)).card+(fixed σ).card+
      (Finset.univ.filter (fun x => 3≤(members (opposite σ α) (cycle (opposite σ α) x)).card)).card := by
  let f := opposite σ α
  let large := Finset.univ.filter (fun x => 3≤(members f (cycle f x)).card)
  have hs : bad σ α⊆(fixed f∪fixed σ)∪large := by
    intro x hx
    have hx := (Finset.mem_filter.mp hx).2
    by_cases h1 : f x=x
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h1⟩))
    by_cases h2 : σ x=x
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h2⟩))
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    by_contra hn
    exact hx ⟨card_le_two_square f (by omega),h1,h2⟩
  exact (Finset.card_le_card hs).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))

/-- The exact `8N` estimate. The planar input is only its explicit Euler
inequality; no comparison-count estimate is assumed. -/
theorem bad_gaps_le
    (heuler : Fintype.card O+4≤2*Fintype.card (Cycle σ)+2*Fintype.card (Cycle (opposite σ α)))
    (hmono : (fixed (opposite σ α)).card≤1) :
    (bad σ α).card≤8*Fintype.card (Cycle σ) := by
  let f := opposite σ α
  let P := ∑ c : Cycle f,((members f c).card-2)
  let M := (Finset.univ.filter (fun c : Cycle f => (members f c).card=1)).card
  have hM : M≤1 := (singleton_cycles_le_fixed f).trans hmono
  change (fixed f).card≤1 at hmono
  have hP : P+2*Fintype.card (Cycle f)=Fintype.card O+M := by
    have h := excess_identity (fun c : Cycle f => (members f c).card)
      (fun c => Finset.card_pos.mpr (members_nonempty f c))
    rw [sum_card] at h
    exact h
  have hl := large_sum_le (fun c : Cycle f => (members f c).card)
  rw [large_count] at hl
  have hb := bad_card_bound σ α
  have hs := fixed_le_cycles σ
  change (bad σ α).card≤(fixed f).card+(fixed σ).card+
    (Finset.univ.filter (fun x => 3≤(members f (cycle f x)).card)).card at hb
  change (Finset.univ.filter (fun x => 3≤(members f (cycle f x)).card)).card≤3*P at hl
  change Fintype.card O+4≤2*Fintype.card (Cycle σ)+2*Fintype.card (Cycle f) at heuler
  omega

omit [Fintype O] in
lemma good_opposite (hr : Function.Involutive α) {x : O} (hx : Good σ α x) :
    Good σ α (opposite σ α x) := by
  have he : σ (opposite σ α x)=α x := by
    have h := congrArg α hx.1
    change α (α (σ (α (σ x))))=α x at h
    rw [hr] at h
    exact h
  refine ⟨congrArg (opposite σ α) hx.1,?_,?_⟩
  · intro h
    exact hx.2.1 (h.symm.trans hx.1)
  · intro h
    rw [he] at h
    exact hx.2.2 (α.injective h).symm

/-- Cut every bad gap and every prescribed marking together with its opposite. -/
def cuts (marks : Finset O) : Finset O := bad σ α∪marks∪marks.image (opposite σ α)
lemma cardinal_cuts (marks : Finset O) : (cuts σ α marks).card≤(bad σ α).card+2*marks.card := by
  have h := (Finset.card_union_le (bad σ α∪marks) (marks.image (opposite σ α))).trans
    (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_image_le))
  unfold cuts
  omega
lemma cut_stable (hr : Function.Involutive α) (marks : Finset O) {x : O} (hx : Good σ α x) :
    x∈cuts σ α marks ↔ opposite σ α x∈cuts σ α marks := by
  have hy := good_opposite σ α hr hx
  have image_iff {z : O} (hz : Good σ α z) :
      z∈marks.image (opposite σ α) ↔ opposite σ α z∈marks := by
    constructor
    · intro hm
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hm
      have hwz : w=opposite σ α z := (opposite σ α).injective (he.trans hz.1.symm)
      simpa only [hwz] using hw
    · intro h
      exact Finset.mem_image.mpr ⟨opposite σ α z,h,hz.1⟩
  simp only [cuts,Finset.mem_union,bad,Finset.mem_filter,Finset.mem_univ,true_and,
    not_true_eq_false, hx,hy,false_or,image_iff hx,image_iff hy,hx.1]
  exact or_comm

/-- The source's `J ≤ 12N'`, retaining the exact boundary and splitting count. -/
theorem cuts_le_twelve (marks : Finset O) (pieces : ℕ)
    (heuler : Fintype.card O+4≤2*Fintype.card (Cycle σ)+2*Fintype.card (Cycle (opposite σ α)))
    (hmono : (fixed (opposite σ α)).card≤1)
    (hpieces : Fintype.card (Cycle σ)≤pieces)
    (hmarks : marks.card≤Fintype.card (Cycle σ)+pieces) :
    (cuts σ α marks).card≤12*pieces := by
  have hb := bad_gaps_le σ α heuler hmono
  have hc := cardinal_cuts σ α marks
  omega
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
lemma before {x : O} {i : ℕ} (hi : i<S.distance x) : (σ^i) x∉S.cut :=
  Nat.find_min (S.hits x) hi
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

lemma distance_iterate (x : O) : ∀ i, i≤S.distance x →
    S.distance ((σ^i) x)=S.distance x-i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro hi
    have hp := S.before (x:=x) (i:=i) (by omega)
    have hn := S.distance_next hp
    have hh := ih (by omega)
    rw [pow_succ',Equiv.Perm.mul_apply]
    omega
lemma finish_iterate (x : O) : ∀ i, i≤S.distance x → S.finish ((σ^i) x)=S.finish x := by
  intro i hi
  unfold finish
  rw [S.distance_iterate x i hi,← Equiv.Perm.mul_apply,← pow_add,Nat.sub_add_cancel hi]

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

lemma reverse_steps (c : {x // x∈S.cut}) (hs : P.pair c=c) :
    ∀ i, i≤S.distance (α c.val) →
      α ((σ^i) (α c.val))=(σ^(S.distance (α c.val)-i)) (α c.val) := by
  intro i
  induction i with
  | zero =>
    intro _
    have h := congrArg Subtype.val hs
    change S.finish (α c.val)=c.val at h
    simp only [pow_zero,Equiv.Perm.one_apply,Nat.sub_zero]
    rw [P.involutive]
    exact h.symm
  | succ i ih =>
    intro hi
    have hj : i<S.distance (α c.val) := by omega
    have hcut := S.before hj
    have he := P.opposite_next hcut
    have hh := ih (by omega)
    apply σ.injective
    rw [pow_succ',Equiv.Perm.mul_apply,he,hh]
    have hd : S.distance (α c.val)-i=(S.distance (α c.val)-(i+1))+1 := by omega
    rw [hd,pow_succ',Equiv.Perm.mul_apply]
lemma pair_fixed_free (c : {x // x∈S.cut}) : P.pair c≠c := by
  intro hs
  let d := S.distance (α c.val)
  let k := d/2
  have hk : k≤d := Nat.div_le_self _ _
  have he := P.reverse_steps c hs k hk
  by_cases hp : d=2*k
  · have hdk : S.distance (α c.val)-k=k := by change d-k=k; omega
    rw [hdk] at he
    exact P.fixed_free _ he
  · have hd : d=2*k+1 := by dsimp [k]; omega
    have hdk : S.distance (α c.val)-k=k+1 := by change d-k=k+1; omega
    rw [hdk,pow_succ',Equiv.Perm.mul_apply] at he
    have hc : (σ^k) (α c.val)∉S.cut := S.before (by change k<d; omega)
    have hg := P.good _ hc
    apply hg.2.1
    change α (σ ((σ^k) (α c.val)))=(σ^k) (α c.val)
    rw [← he,P.involutive]

lemma predecessor_cut (c : {x // x∈S.cut}) : σ.symm (α c.val)∈S.cut := by
  by_contra hn
  have h := P.opposite_uncut hn
  rw [Equiv.apply_symm_apply,P.involutive] at h
  exact h c.property

/-- Each cut is the last occurrence of its run; the first occurrence is the
partner of the final occurrence of the opposite run. -/
def first (c : {x // x∈S.cut}) : O := α (P.pair c).val
lemma finish_first (c : {x // x∈S.cut}) : S.finish (P.first c)=c.val := by
  exact congrArg Subtype.val (P.pair_involutive c)
lemma before_first_cut (c : {x // x∈S.cut}) : σ.symm (P.first c)∈S.cut :=
  P.predecessor_cut (P.pair c)

lemma distance_le_first {c : {x // x∈S.cut}} {x : O} (hx : S.finish x=c.val) :
    S.distance x≤S.distance (P.first c) := by
  by_contra hn
  have hd : S.distance (P.first c)+1≤S.distance x := by omega
  have he : (σ^(S.distance x-S.distance (P.first c))) x=P.first c := by
    apply (σ^(S.distance (P.first c))).injective
    rw [← Equiv.Perm.mul_apply,← pow_add,Nat.add_sub_of_le (by omega)]
    exact hx.trans (P.finish_first c).symm
  have hg : (σ^(S.distance x-S.distance (P.first c)-1)) x=σ.symm (P.first c) := by
    apply σ.injective
    rw [Equiv.apply_symm_apply,← Equiv.Perm.mul_apply,← pow_succ']
    have heq : S.distance x-S.distance (P.first c)-1+1=S.distance x-S.distance (P.first c) := by omega
    rw [heq]
    exact he
  have hcut := P.before_first_cut c
  rw [← hg] at hcut
  exact S.before (by omega) hcut

lemma run_coordinates {c : {x // x∈S.cut}} {x : O} (hx : S.finish x=c.val) :
    (σ^(S.distance (P.first c)-S.distance x)) (P.first c)=x := by
  have hd := P.distance_le_first hx
  apply (σ^(S.distance x)).injective
  rw [← Equiv.Perm.mul_apply,← pow_add,Nat.add_sub_of_le hd]
  exact (P.finish_first c).trans hx.symm

def run (c : {x // x∈S.cut}) : List O :=
  (List.range (S.distance (P.first c)+1)).map (fun i => (σ^i) (P.first c))
lemma mem_run {c : {x // x∈S.cut}} {x : O} : x∈P.run c ↔ S.finish x=c.val := by
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    have hi' : i≤S.distance (P.first c) := by simpa only [List.mem_range,Nat.lt_succ_iff] using hi
    exact (S.finish_iterate _ _ hi').trans (P.finish_first c)
  · intro hx
    apply List.mem_map.mpr
    exact ⟨S.distance (P.first c)-S.distance x,
      List.mem_range.mpr (by omega),P.run_coordinates hx⟩
lemma belongs_opposite {c : {x // x∈S.cut}} {x : O} (hx : x∈P.run c) :
    α x∈P.run (P.pair c) := by
  apply P.mem_run.mpr
  have he := P.mem_run.mp hx
  have h := P.finish_pair x
  rw [he] at h
  exact h.symm

lemma first_pair (c : {x // x∈S.cut}) : P.first (P.pair c)=α c.val := by
  unfold first
  rw [P.pair_involutive]
lemma distance_reverse (c : {x // x∈S.cut}) : ∀ i,i≤S.distance (P.first c) →
    S.distance (α ((σ^i) (P.first c)))=i := by
  intro i
  induction i with
  | zero =>
    intro _
    simp only [pow_zero,Equiv.Perm.one_apply,first]
    rw [P.involutive]
    exact S.distance_zero (P.pair c).property
  | succ i ih =>
    intro hi
    have hc := S.before (x:=P.first c) (i:=i) (by omega)
    have hd := S.distance_next (P.opposite_uncut hc)
    rw [P.opposite_next hc,ih (by omega)] at hd
    simpa only [pow_succ',Equiv.Perm.mul_apply] using hd
lemma distance_first_pair (c : {x // x∈S.cut}) :
    S.distance (P.first (P.pair c))=S.distance (P.first c) := by
  have h := P.distance_reverse c (S.distance (P.first c)) le_rfl
  change S.distance (α (S.finish (P.first c)))=S.distance (P.first c) at h
  rw [P.finish_first] at h
  rw [P.first_pair]
  exact h
lemma reverse_coordinate (c : {x // x∈S.cut}) (i : ℕ) (hi : i≤S.distance (P.first c)) :
    α ((σ^i) (P.first c))=(σ^(S.distance (P.first c)-i)) (P.first (P.pair c)) := by
  have hmem : (σ^i) (P.first c)∈P.run c :=
    P.mem_run.mpr ((S.finish_iterate _ _ hi).trans (P.finish_first c))
  have he := P.run_coordinates (P.mem_run.mp (P.belongs_opposite hmem))
  rw [P.distance_first_pair,P.distance_reverse c i hi] at he
  exact he.symm

end Paired
namespace PairOrbit
variable {A : Type} (r : A→A) (hr : Function.Involutive r)
variable [Fintype A]
end PairOrbit

namespace Paired
variable {S} {α : Equiv.Perm O} (P : S.Paired α)
end Paired

/-- The literal source cut construction has at least one cut per boundary,
using one chosen indexing mark there. -/
def ofMarks [Fintype O] (α : Equiv.Perm O) (marks : Finset O)
    (hmark : ∀ x,∃ y∈marks,σ.SameCycle x y) : CutSystem σ where
  cut := PlanarRotation.cuts σ α marks
  hits x := by
    obtain ⟨y,hy,hxy⟩ := hmark x
    obtain ⟨n,hn⟩ := hxy.exists_nat_pow_eq
    refine ⟨n,?_⟩
    rw [hn]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hy)))
lemma ofMarks_paired [Fintype O] (α : Equiv.Perm O) (marks : Finset O)
    (hmark : ∀ x,∃ y∈marks,σ.SameCycle x y)
    (hr : Function.Involutive α) (hf : ∀ x,α x≠x) :
    (ofMarks α marks hmark).Paired α where
  involutive := hr
  fixed_free := hf
  good x hx := by
    by_contra hn
    exact hx (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)))))
  stable x hx := PlanarRotation.cut_stable σ α hr marks hx

end CutSystem
end TorsionFreeZeroDivisors.PlanarRuns

namespace TorsionFreeZeroDivisors.PlanarIntervals
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks PlanarRuns PlanarRuns.CutSystem
variable {T : Type} {len : T→ℕ} {σ α : Equiv.Perm (Position len)}
    (S : CutSystem σ) (P : S.Paired α)
    (hstep : ∀ x,x∉S.cut → (σ x).1=x.1 ∧ (σ x).2.val=x.2.val+1)

include hstep
lemma coordinate_iterate (x : Position len) (i : ℕ) (hi : i≤S.distance x) :
    ((σ^i) x).1=x.1 ∧ ((σ^i) x).2.val=x.2.val+i := by
  induction i with
  | zero =>
    change x.1=x.1 ∧ x.2.val=x.2.val+(0:ℤ)
    simp
  | succ i ih =>
    have hh := hstep ((σ^i) x) (S.before (by omega))
    have ih := ih (by omega)
    rw [pow_succ',Equiv.Perm.mul_apply]
    constructor
    · exact hh.1.trans ih.1
    · rw [hh.2,ih.2,Nat.cast_add,Nat.cast_one]; ring

def lower (c : {x // x∈S.cut}) : ℤ := (P.first c).2.val
def upper (c : {x // x∈S.cut}) : ℤ := c.val.2.val+1
lemma finish_coordinates (c : {x // x∈S.cut}) :
    c.val.1=(P.first c).1 ∧ upper S c=lower S P c+S.distance (P.first c)+1 := by
  have hh := coordinate_iterate S hstep (P.first c) (S.distance (P.first c)) le_rfl
  change (S.finish (P.first c)).1=_ ∧ (S.finish (P.first c)).2.val=_ at hh
  rw [P.finish_first] at hh
  exact ⟨hh.1,by dsimp only [upper,lower]; omega⟩
lemma bounds (c : {x // x∈S.cut}) :
    0≤lower S P c ∧ lower S P c<upper S c ∧ upper S c≤len (P.first c).1 := by
  have hf := (P.first c).2.property
  have hc := c.val.2.property
  rw [mem_positions] at hf hc
  have he := finish_coordinates S P hstep c
  have h0 : (0:ℝ)≤((P.first c).2.val:ℝ) := by
    have : (0:ℤ)≤(P.first c).2.val := by exact_mod_cast (show (-1:ℝ)<((P.first c).2.val:ℝ) by linarith [hf.1])
    exact_mod_cast this
  have h1 : c.val.2.val+1≤(len c.val.1:ℤ) := by
    have : (c.val.2.val:ℝ)<len c.val.1 := by linarith [hc.2]
    exact_mod_cast this
  have h1 := h1.trans_eq (congrArg (fun t => (len t : ℤ)) he.1)
  refine ⟨by exact_mod_cast h0,?_,h1⟩
  rw [he.2]
  omega

lemma finish_iff (x : Position len) (c : {x // x∈S.cut}) :
    S.finish x=c.val ↔ x.1=(P.first c).1 ∧ lower S P c≤x.2.val ∧ x.2.val<upper S c := by
  constructor
  · intro hx
    have hc := P.run_coordinates hx
    have hi : S.distance (P.first c)-S.distance x≤S.distance (P.first c) := Nat.sub_le _ _
    have hh := coordinate_iterate S hstep (P.first c) _ hi
    rw [hc] at hh
    have hd := P.distance_le_first hx
    have he := (finish_coordinates S P hstep c).2
    refine ⟨hh.1,?_,?_⟩ <;> dsimp only [lower] at * <;> omega
  · rintro ⟨hs,hl,hu⟩
    have he := (finish_coordinates S P hstep c).2
    let i := (x.2.val-lower S P c).toNat
    have hi : i≤S.distance (P.first c) := by dsimp only [i]; omega
    have hh := coordinate_iterate S hstep (P.first c) i hi
    have hp : (σ^i) (P.first c)=x := by
      apply position_ext
      · exact hh.1.trans hs.symm
      · rw [hh.2]
        dsimp only [i,lower] at *
        omega
    rw [←hp]
    exact (S.finish_iterate _ _ hi).trans (P.finish_first c)

lemma finish_real_iff (x : Position len) (c : {x // x∈S.cut}) :
    S.finish x=c.val ↔ x.1=(P.first c).1 ∧
      x.2.val∈positions (lower S P c) (upper S c) := by
  rw [finish_iff S P hstep,mem_positions]
  constructor
  · rintro ⟨hs,hl,hu⟩
    have hl' : (lower S P c:ℝ)≤x.2.val := by exact_mod_cast hl
    have hu' : (x.2.val:ℝ)+1≤upper S c := by exact_mod_cast hu
    exact ⟨hs,by linarith,by linarith⟩
  · rintro ⟨hs,hl,hu⟩
    have hl' : lower S P c≤x.2.val := by
      have : (lower S P c:ℝ)-1<x.2.val := by linarith
      have hh : lower S P c-1<x.2.val := by exact_mod_cast this
      omega
    have hu' : x.2.val<upper S c := by exact_mod_cast (show (x.2.val:ℝ)<upper S c by linarith)
    exact ⟨hs,hl',hu'⟩

lemma partner_coordinate {x : Position len} {c : {x // x∈S.cut}} (hx : S.finish x=c.val) :
    (α x).2.val=lower S P (P.pair c)+upper S c-1-x.2.val := by
  let i := S.distance (P.first c)-S.distance x
  have hi : i≤S.distance (P.first c) := Nat.sub_le _ _
  have hp := P.run_coordinates hx
  change (σ^i) (P.first c)=x at hp
  have hα := P.reverse_coordinate c i hi
  rw [hp] at hα
  have ht := coordinate_iterate S hstep (P.first (P.pair c)) (S.distance (P.first c)-i) (by
    rw [P.distance_first_pair]; omega)
  rw [←hα] at ht
  have hh := coordinate_iterate S hstep (P.first c) i hi
  rw [hp] at hh
  have he := (finish_coordinates S P hstep c).2
  dsimp only [lower] at *
  omega

/-- Every actual maximal run yields a literal integer comparison side. No
real-grid or arbitrary interval compatibility is postulated. -/
def comparisons : Comparisons (E:={x // x∈S.cut}) len where
  pairing := ⟨α,P.involutive⟩
  side x := some ⟨S.finish x,S.finish_mem x⟩
  flip := P.pair
  flip_inv := P.pair_involutive
  flip_ne := P.pair_fixed_free
  side_partner := by
    intro x c hc
    have he : S.finish x=c.val := congrArg Subtype.val (Option.some.inj hc)
    apply congrArg some
    apply Subtype.ext
    change S.finish (α x)=S.finish (α c.val)
    rw [←he,←P.finish_pair]
  none_iff x := by simp only [Option.some_ne_none,false_iff]; exact P.fixed_free x
  source c := (P.first c).1
  lo c := lower S P c
  hi c := upper S c
  reverse _ := true
  offset c := lower S P (P.pair c)+upper S c
  side_iff x c := by
    rw [Option.some.injEq,Subtype.ext_iff]
    exact finish_real_iff S P hstep x c
  partner_source := by
    intro x c hc
    have he : S.finish x=c.val := congrArg Subtype.val (Option.some.inj hc)
    have ht : S.finish (α x)=(P.pair c).val := by
      change S.finish (α x)=S.finish (α c.val)
      rw [←he,←P.finish_pair]
    exact ((finish_iff S P hstep _ _).mp ht).1
  partner_coordinate := by
    intro x c hc
    exact partner_coordinate S P hstep (congrArg Subtype.val (Option.some.inj hc))
  target_range := by
    intro c
    simp only [ite_true,Int.cast_add]
    have hb := bounds S P hstep (P.pair c)
    have h1 := (finish_coordinates S P hstep c).2
    have h2 := (finish_coordinates S P hstep (P.pair c)).2
    rw [P.distance_first_pair] at h2
    constructor
    · have hh : (0:ℝ)≤lower S P (P.pair c) := by exact_mod_cast hb.1
      linarith
    · have hh : lower S P (P.pair c)+upper S c-lower S P c≤(len (P.first (P.pair c)).1:ℤ) := by omega
      exact_mod_cast hh
end TorsionFreeZeroDivisors.PlanarIntervals
namespace TorsionFreeZeroDivisors.ExtendComparisons
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T E : Type} {len more : T → ℕ} (C : Comparisons (E:=E) len)
    (hle : ∀ t,len t ≤ more t)

lemma positions_mono {m n : ℕ} (h : m≤n) : positions 0 m⊆positions 0 n := by
  intro q hq
  rw [mem_positions] at hq ⊢
  exact ⟨hq.1,hq.2.trans_le (by exact_mod_cast h)⟩
def embed (x : Position len) : Position more :=
  ⟨x.1,⟨x.2.val,positions_mono (hle x.1) x.2.property⟩⟩
abbrev Old (x : Position more) : Prop := x.2.val∈positions 0 (len x.1)
def project (x : Position more) (h : Old (len:=len) x) : Position len := ⟨x.1,⟨x.2.val,h⟩⟩
lemma old_embed (x : Position len) : Old (len:=len) (embed hle x) := x.2.property
lemma project_embed (x : Position len) : project (embed hle x) (old_embed hle x)=x := by cases x; rfl
lemma embed_project (x : Position more) (h : Old (len:=len) x) : embed hle (project x h)=x := by cases x; rfl
lemma embed_injective : Function.Injective (embed hle) := by
  intro x y h
  apply PlanarIntervals.position_ext
  · exact congrArg (fun x : Position more => x.1) h
  · exact congrArg (fun x : Position more => x.2.val) h

def partner (x : Position more) : Position more :=
  if h : Old (len:=len) x then embed hle (C.pairing.partner (project x h)) else x
lemma partner_embed (x : Position len) : partner C hle (embed hle x)=embed hle (C.pairing.partner x) := by
  simp only [partner,dif_pos (old_embed hle x),project_embed]
lemma partner_new (x : Position more) (h : ¬Old (len:=len) x) : partner C hle x=x := by
  simp only [partner,dif_neg h]
lemma partner_inv : Function.Involutive (partner C hle) := by
  intro x
  by_cases h : Old (len:=len) x
  · rw [←embed_project hle x h,partner_embed,partner_embed,C.pairing.involutive]
  · rw [partner_new C hle x h,partner_new C hle x h]
def side (x : Position more) : Option E :=
  if h : Old (len:=len) x then C.side (project x h) else none
lemma side_embed (x : Position len) : side C (embed hle x)=C.side x := by
  simp only [side,dif_pos (old_embed hle x),project_embed]
lemma side_some_old {x : Position more} {e : E} (h : side C x=some e) : Old (len:=len) x := by
  by_contra hn
  simp only [side,dif_neg hn] at h
  cases h
lemma side_none (x : Position more) : side C x=none ↔ partner C hle x=x := by
  by_cases h : Old (len:=len) x
  · rw [←embed_project hle x h,side_embed,partner_embed]
    exact (C.none_iff _).trans (embed_injective hle).eq_iff.symm
  · simp only [side,dif_neg h,partner_new C hle x h]

variable (hupper : ∀ e,C.hi e≤len (C.source e))
include hupper in
lemma side_iff (x : Position more) (e : E) :
    side C x=some e ↔ x.1=C.source e ∧ x.2.val∈positions (C.lo e) (C.hi e) := by
  constructor
  · intro hx
    have ho := side_some_old C hx
    rw [side,dif_pos ho] at hx
    exact (C.side_iff _ _).mp hx
  · intro hx
    have ho : Old (len:=len) x := by
      apply mem_positions.mpr
      have h1 := (mem_positions.mp x.2.property).1
      have h2 := (mem_positions.mp hx.2).2
      have h3 : C.hi e≤len x.1 := by simpa only [hx.1] using hupper e
      exact ⟨h1,h2.trans_le h3⟩
    rw [side,dif_pos ho]
    exact (C.side_iff _ _).mpr hx

lemma partner_side {x : Position more} {e : E} (hx : side C x=some e) :
    side C (partner C hle x)=some (C.flip e) := by
  have ho := side_some_old C hx
  rw [←embed_project hle x ho,partner_embed,side_embed]
  apply C.side_partner
  rwa [←side_embed C hle,embed_project]
lemma partner_source {x : Position more} {e : E} (hx : side C x=some e) :
    (partner C hle x).1=C.source (C.flip e) := by
  have ho := side_some_old C hx
  rw [←embed_project hle x ho,partner_embed]
  exact C.partner_source _ _ (by rwa [←side_embed C hle,embed_project])
lemma partner_coordinate {x : Position more} {e : E} (hx : side C x=some e) :
    (partner C hle x).2.val=affine (C.reverse e) (C.offset e) x.2.val := by
  have ho := side_some_old C hx
  have hx' : C.side (project x ho)=some e := by
    simpa only [side,dif_pos ho] using hx
  have he : partner C hle x=embed hle (C.pairing.partner (project x ho)) := dif_pos ho
  rw [he]
  exact C.partner_coordinate (project x ho) e hx' 
include hle in
lemma target_range (e : E) : if C.reverse e then
    0≤(C.offset e:ℝ)-C.hi e ∧ (C.offset e:ℝ)-C.lo e ≤ more (C.source (C.flip e))
    else 0≤C.lo e+(C.offset e:ℝ) ∧ C.hi e+(C.offset e:ℝ) ≤ more (C.source (C.flip e)) := by
  have hh := C.target_range e
  have hn : (len (C.source (C.flip e)):ℝ) ≤ more (C.source (C.flip e)) := by exact_mod_cast hle _
  split_ifs at hh ⊢ <;> exact ⟨hh.1,hh.2.trans hn⟩

def comparisons : Comparisons (E:=E) more where
  pairing := ⟨partner C hle,partner_inv C hle⟩
  side := side C
  flip := C.flip
  flip_inv := C.flip_inv
  flip_ne := C.flip_ne
  side_partner _ _ := partner_side C hle
  none_iff := side_none C hle
  source := C.source
  lo := C.lo
  hi := C.hi
  reverse := C.reverse
  offset := C.offset
  side_iff := side_iff C hupper
  partner_source _ _ := partner_source C hle
  partner_coordinate _ _ := partner_coordinate C hle
  target_range := target_range C hle

variable [Fintype T]
include hle in
lemma old_card : (Finset.univ.filter (fun x : Position more => Old (len:=len) x)).card=
    Fintype.card (Position len) := by
  symm
  rw [←Finset.card_univ]
  apply Finset.card_bij (fun x _ => embed hle x)
  · intro x _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,old_embed hle x⟩
  · intro x _ y _ h
    exact embed_injective hle h
  · intro x hx
    have ho := (Finset.mem_filter.mp hx).2
    exact ⟨project x ho,Finset.mem_univ _,embed_project hle x ho⟩
lemma fixed_old_card : (Finset.univ.filter (fun x : Position more => Old (len:=len) x ∧ partner C hle x=x)).card=
    (Finset.univ.filter (fun x : Position len => C.pairing.partner x=x)).card := by
  symm
  apply Finset.card_bij (fun x _ => embed hle x)
  · intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,old_embed hle x,?_⟩
    rw [partner_embed,(Finset.mem_filter.mp hx).2]
  · intro x _ y _ h
    exact embed_injective hle h
  · intro x hx
    obtain ⟨ho,hf⟩ := (Finset.mem_filter.mp hx).2
    refine ⟨project x ho,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,embed_project hle x ho⟩
    apply embed_injective hle
    rw [←partner_embed,embed_project,hf]
lemma fixed_card : (Finset.univ.filter (fun x : Position more => partner C hle x=x)).card=
    (Finset.univ.filter (fun x : Position len => C.pairing.partner x=x)).card+
    (Finset.univ.filter (fun x : Position more => ¬Old (len:=len) x)).card := by
  have he : (Finset.univ.filter (fun x : Position more => partner C hle x=x))=
      (Finset.univ.filter (fun x : Position more => Old (len:=len) x ∧ partner C hle x=x))∪
      (Finset.univ.filter (fun x : Position more => ¬Old (len:=len) x)) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    by_cases h : Old (len:=len) x
    · simp only [h,true_and,not_true_eq_false,or_false]
    · simp only [h,false_and,not_false_eq_true,or_true,iff_true]
      exact partner_new C hle x h
  have hd : Disjoint (Finset.univ.filter (fun x : Position more => Old (len:=len) x ∧ partner C hle x=x))
      (Finset.univ.filter (fun x : Position more => ¬Old (len:=len) x)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx).2.1
  rw [he,Finset.card_union_of_disjoint hd,fixed_old_card]
end TorsionFreeZeroDivisors.ExtendComparisons
namespace TorsionFreeZeroDivisors.WordPositions

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T : Type} (len : T → ℕ)
variable {A : Type} (w : T → List A)
lemma dart_fin (x : (t : T) × Fin (w t).length) :
    RawDecomposition.dart w ((fin (fun t=>(w t).length)).symm x)=(w x.1).get x.2 := by
  change (w x.1).get ⟨(x.2.val:ℤ).toNat,_⟩=(w x.1).get x.2
  congr 1
lemma dart_prefix (v : T → List A) (x : Position (fun t=>(w t).length)) :
    RawDecomposition.dart (fun t=>w t++v t)
      (ExtendComparisons.embed (fun t=>by simp only [List.length_append]; omega) x)=
    RawDecomposition.dart w x := by
  dsimp only [RawDecomposition.dart,ExtendComparisons.embed]
  simpa only [List.get_eq_getElem] using List.getElem_append_left
    (show x.2.val.toNat<(w x.1).length from (fin _ x).2.isLt)

variable (cap : ℕ) (hc : 0<cap)
def joinFin : ((p : BalancedWords.Piece w cap) × Fin (BalancedWords.old w cap p)) ≃
      ((t : T) × Fin (w t).length) :=
  (Equiv.sigmaAssoc fun t i=>Fin (BalancedPieces.sizes (w t).length cap i)).trans
    (Equiv.sigmaCongrRight fun t=>ConsecutivePieces.index (w t)
      (BalancedPieces.sizes (w t).length cap) (BalancedPieces.sizes_sum hc))
def join : Position (BalancedWords.old w cap) ≃ Position (fun t=>(w t).length) :=
  (fin _).trans ((joinFin w cap hc).trans (fin _).symm)
lemma join_value (x : Position (BalancedWords.old w cap)) : (join w cap hc x).2.val=
    (ConsecutivePieces.offset (BalancedPieces.sizes (w x.1.1).length cap) x.1.2:ℤ)+x.2.val := by
  let q : Fin (BalancedPieces.sizes (w x.1.1).length cap x.1.2) :=
    ⟨x.2.val.toNat,by
      have hb := (fin _ x).2.isLt
      exact hb⟩
  change ((ConsecutivePieces.index (w x.1.1) (BalancedPieces.sizes (w x.1.1).length cap)
    (BalancedPieces.sizes_sum hc) ⟨x.1.2,q⟩).val:ℤ)=_
  rw [ConsecutivePieces.index_val,Nat.cast_add]
  congr 1
  exact Int.toNat_of_nonneg (bounds x.2).1

def segments : Position (fun p=>(BalancedWords.segment w cap hc p).length) ≃
    Position (fun t=>(w t).length) :=
  (ComparisonGeometry.position (Equiv.refl _) (BalancedWords.segment_length w cap hc)).trans (join w cap hc)
lemma segments_dart (x : Position (fun p=>(BalancedWords.segment w cap hc p).length)) :
    RawDecomposition.dart (BalancedWords.segment w cap hc) x=
      RawDecomposition.dart w (segments w cap hc x) := by
  unfold RawDecomposition.dart
  simp only [BalancedWords.segment,ConsecutivePieces.segment,List.get_eq_getElem,List.getElem_ofFn,
    Fin.getElem_fin]
  congr 1
end
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T : Type} [Fintype T] (len : T → ℕ)
lemma cardinal : Fintype.card (Position len)=∑t,len t := by
  rw [Fintype.card_congr (fin len),Fintype.card_sigma]
  simp only [Fintype.card_fin]
variable {A : Type} (w v : T → List A)
abbrev prefix_bound (t : T) : (w t).length≤(w t++v t).length := by
  simp only [List.length_append]
  omega
lemma new_card : (Finset.univ.filter (fun x : Position (fun t=>(w t++v t).length)=>
    ¬ExtendComparisons.Old (len:=fun t=>(w t).length) x)).card=∑t,(v t).length := by
  have hp := Finset.card_filter_add_card_filter_not
    (s:=Finset.univ (α:=Position (fun t=>(w t++v t).length)))
    (p:=fun x=>ExtendComparisons.Old (len:=fun t=>(w t).length) x)
  have ho := ExtendComparisons.old_card (prefix_bound w v)
  rw [ho,Finset.card_univ,cardinal,cardinal] at hp
  simp only [List.length_append,Finset.sum_add_distrib] at hp
  omega
variable {E : Type} (C : Comparisons (E:=E) (fun t=>(w t).length))
lemma fixed_card (hfull : ∀ x,C.pairing.partner x≠x) :
    (Finset.univ.filter (fun x=>ExtendComparisons.partner C (prefix_bound w v) x=x)).card=
      ∑t,(v t).length := by
  rw [ExtendComparisons.fixed_card,new_card]
  have he : (Finset.univ.filter (fun x=>C.pairing.partner x=x))=∅ := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
    exact hfull x
  rw [he,Finset.card_empty,Nat.zero_add]
omit [Fintype T] in
lemma nonfixed_old (p : Position (fun t=>(w t++v t).length))
    (hp : ExtendComparisons.partner C (prefix_bound w v) p≠p) :
    p.2.val∈positions 0 (w p.1).length := by
  by_contra hn
  exact hp (ExtendComparisons.partner_new C (prefix_bound w v) p hn)
end TorsionFreeZeroDivisors.WordPositions

namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore BlockAlignment ComparedBlocks
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap)
    (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
    {E : Type} [Fintype E]
    (C : Comparisons (E:=E) (fun p=>(seg s cap hc p).length))
    (lo hi : E → ℕ) (hlo : ∀ e,C.lo e=lo e) (hhi : ∀ e,C.hi e=hi e)
    (hle : ∀ e,lo e≤hi e) (hh : ∀ e,hi e≤(seg s cap hc (C.source e)).length)
    (hred : ∀ p e,C.side p=some e →
      RawDecomposition.dart (seg s cap hc) p≠RawDecomposition.dart (seg s cap hc) (C.pairing.partner p) ∧
      RawDecomposition.dart (seg s cap hc) p≠(graph rep r).reverse (RawDecomposition.dart (seg s cap hc) (C.pairing.partner p)))
    (hcomp : ∀ p e,C.side p=some e → label rep (RawDecomposition.dart (seg s cap hc) p)=
      if C.reverse e then Types.inverse (label rep (RawDecomposition.dart (seg s cap hc) (C.pairing.partner p)))
      else label rep (RawDecomposition.dart (seg s cap hc) (C.pairing.partner p)))
abbrev grow := WordPositions.prefix_bound (seg s cap hc) (tail s cap hc hL hd)
include hhi hh in
omit [Fintype E] in
lemma upper_real (e : E) : C.hi e≤((seg s cap hc (C.source e)).length:ℝ) := by
  rw [hhi]
  exact_mod_cast hh e

/-- Appending the actual short closures changes neither original comparison nor
its underlying graph lifts. Every newly added position is unpaired. -/
def system : PathSystem rep r x y where
  P := Piece s cap
  E := E
  fP := inferInstance
  fE := inferInstance
  paths := word s cap hc hL hd
  nonempty := nonempty s cap hc hL hd
  root := root s cap hc
  path_chain := chain s cap hc hL hd
  cyclic_chain := cyclic s cap hc hL hd
  comparisons := ExtendComparisons.comparisons C (grow s cap hc hL hd) (upper_real s cap hc C hi hhi hh)
  lower := lo
  upper := hi
  lower_eq := hlo
  upper_eq := hhi
  lower_le := hle
  upper_le e := (hh e).trans (grow s cap hc hL hd _)
  reduced := by
    intro p e he
    have hp := ExtendComparisons.side_some_old C he
    have he' : C.side (ExtendComparisons.project p hp)=some e := by
      simpa only [ExtendComparisons.comparisons,ExtendComparisons.side,dif_pos hp] using he
    have hg := hred (ExtendComparisons.project p hp) e he'
    rw [←ExtendComparisons.embed_project (grow s cap hc hL hd) p hp]
    change RawDecomposition.dart (fun p=>seg s cap hc p++tail s cap hc hL hd p) _≠
      RawDecomposition.dart _ (ExtendComparisons.partner C (grow s cap hc hL hd) _) ∧
      RawDecomposition.dart (fun p=>seg s cap hc p++tail s cap hc hL hd p) _ ≠(graph rep r).reverse (RawDecomposition.dart _ (ExtendComparisons.partner C (grow s cap hc hL hd) _))
    rw [ExtendComparisons.partner_embed]
    simpa only [word,WordPositions.dart_prefix] using hg
  rootA := rootA s cap hc hL hd
  rootB := rootB s cap hc hL hd
  compatible := by
    intro p e he
    have hp := ExtendComparisons.side_some_old C he
    have he' : C.side (ExtendComparisons.project p hp)=some e := by
      simpa only [ExtendComparisons.comparisons,ExtendComparisons.side,dif_pos hp] using he
    have hg := hcomp (ExtendComparisons.project p hp) e he'
    rw [←ExtendComparisons.embed_project (grow s cap hc hL hd) p hp]
    change label rep (RawDecomposition.dart (fun p=>seg s cap hc p++tail s cap hc hL hd p) _)=
      if C.reverse e then Types.inverse (label rep (RawDecomposition.dart _ (ExtendComparisons.partner C (grow s cap hc hL hd) _)))
      else label rep (RawDecomposition.dart _ (ExtendComparisons.partner C (grow s cap hc hL hd) _))
    rw [ExtendComparisons.partner_embed]
    simpa only [word,WordPositions.dart_prefix] using hg
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
lemma next {x : Position len} (hx : x.2.val+1<(len x.1:ℤ)) :
    (perm len x).2.val=x.2.val+1 := by
  let i : Fin (len x.1) := ⟨x.2.val.toNat,by have hb:=bounds x.2; omega⟩
  have he := apply_fin len x.1 i
  change perm len ((fin len).symm (fin len x))=(fin len).symm ⟨x.1,finRotate (len x.1) i⟩ at he
  rw [Equiv.symm_apply_apply] at he
  rw [he]
  change ((finRotate (len x.1) i).val:ℤ)=x.2.val+1
  have hb := bounds x.2
  have hp : 0<len x.1 := by omega
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : len x.1≠0)
  have hc : ∀ i : Fin (len x.1),i.val+1<len x.1 → (finRotate (len x.1) i).val=i.val+1 := by
    rw [hn]
    intro i hi
    apply coe_finRotate_of_ne_last
    intro he
    rw [he,Fin.val_last] at hi
    omega
  rw [hc _ (by change x.2.val.toNat+1<len x.1; omega)]
  change ((x.2.val.toNat+1:ℕ):ℤ)=x.2.val+1
  push_cast
  rw [Int.toNat_of_nonneg hb.1]
variable [Fintype T]

def ends : Finset (Position len) := Finset.univ.filter (fun x=>x.2.val+1=len x.1)
lemma ends_le : (ends len).card≤Fintype.card T := by
  let f : {x // x∈ends len} → T := fun x=>x.val.1
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply PlanarIntervals.position_ext h
    have hx := (Finset.mem_filter.mp x.property).2
    have hy := (Finset.mem_filter.mp y.property).2
    change x.val.1=y.val.1 at h
    have hh := congrArg (fun t=>(len t:ℤ)) h
    omega
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi
end

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T A : Type} [Fintype T] (len : T → ℕ) (root : Option T)
    (label : Position len → A) (bar : A → A) (α : Equiv.Perm (Position len))
    (hr : Function.Involutive α)
    (hcomp : ∀ x,label (α x)=bar (label x))
    (hred : ∀ x,root≠some x.1 ∨ x∉ends len → label (perm len x)≠bar (label x))
include hr hcomp hred in
lemma fixed_root_end {x : Position len} (hx : PlanarRotation.opposite (perm len) α x=x) :
    root=some x.1 ∧ x∈ends len := by
  have he : perm len x=α x := by
    have hh := congrArg α hx
    change α (α (perm len x))=α x at hh
    rwa [hr] at hh
  have hl : label (perm len x)=bar (label x) := he ▸ hcomp x
  constructor
  · by_contra hn
    exact hred x (Or.inl hn) hl
  · by_contra hn
    exact hred x (Or.inr hn) hl
include hr hcomp hred in
lemma monogons_le : (fixed (PlanarRotation.opposite (perm len) α)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [fixed,Finset.mem_filter,Finset.mem_univ,true_and] at hx hy
  have hx := fixed_root_end len root label bar α hr hcomp hred hx
  have hy := fixed_root_end len root label bar α hr hcomp hred hy
  have hs : x.1=y.1 := Option.some.inj (hx.1.symm.trans hy.1)
  apply PlanarIntervals.position_ext hs
  have hx' := (Finset.mem_filter.mp hx.2).2
  have hy' := (Finset.mem_filter.mp hy.2).2
  have hh := congrArg (fun t=>(len t:ℤ)) hs
  omega
end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions
variable {T : Type} (len : T → ℕ)
lemma last_next {x : Position len} (hx : x.2.val+1=(len x.1:ℤ)) : (perm len x).2.val=0 := by
  have hb := bounds x.2
  let i : Fin (len x.1) := ⟨x.2.val.toNat,by omega⟩
  have he := apply_fin len x.1 i
  change perm len ((fin len).symm (fin len x))=(fin len).symm ⟨x.1,finRotate (len x.1) i⟩ at he
  rw [Equiv.symm_apply_apply] at he
  rw [he]
  change ((finRotate (len x.1) i).val:ℤ)=0
  have hn : len x.1≠0 := by omega
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hc : ∀ j : Fin (len x.1),j.val+1=len x.1 → (finRotate (len x.1) j).val=0 := by
    rw [hn]
    intro j hj
    have he : j=Fin.last n := by apply Fin.ext; simp only [Fin.val_last]; omega
    rw [he,finRotate_last]
    rfl
  rw [hc _ (by dsimp only [i]; omega)]
  rfl
variable {A : Type} (w : T → List A) (R : A → A → Prop)
lemma step_nonlast (hc : ∀t,(w t).IsChain R) (x : Position (fun t=>(w t).length))
    (hx : x.2.val+1<(w x.1).length) :
    R (RawDecomposition.dart w x) (RawDecomposition.dart w (perm (fun t=>(w t).length) x)) := by
  have hb := bounds x.2
  have hh := next (fun t=>(w t).length) hx
  have hi : x.2.val.toNat+1<(w x.1).length := by omega
  have hn : (perm (fun t=>(w t).length) x).2.val.toNat=x.2.val.toNat+1 := by omega
  have hc := (List.isChain_iff_getElem.mp (hc x.1)) x.2.val.toNat hi
  change R (w x.1)[x.2.val.toNat] (w x.1)[(perm (fun t=>(w t).length) x).2.val.toNat]
  simpa only [hn] using hc
lemma step_last (hne : ∀t,w t≠[]) (x : Position (fun t=>(w t).length))
    (hx : x.2.val+1=(w x.1).length)
    (hcyc : ∀ᵉ (a∈(w x.1).getLast?) (b∈(w x.1).head?),R a b) :
    R (RawDecomposition.dart w x) (RawDecomposition.dart w (perm (fun t=>(w t).length) x)) := by
  have hb := bounds x.2
  have hn : x.2.val.toNat=(w x.1).length-1 := by omega
  have hh := last_next (fun t=>(w t).length) hx
  have hc := hcyc ((w x.1).getLast (hne x.1)) (List.getLast_mem_getLast? (hne x.1))
    ((w x.1).head (hne x.1)) (List.head_mem_head? (hne x.1))
  change R (w x.1)[x.2.val.toNat] (w x.1)[(perm (fun t=>(w t).length) x).2.val.toNat]
  simpa only [hn,hh,List.getLast_eq_getElem,List.head_eq_getElem,Int.toNat_zero] using hc
end TorsionFreeZeroDivisors.BoundaryRotation

namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions BoundaryRotation WeightedMoore ActualPatternEvent GirthAsymptotics
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} (s : PathSystem rep r x y)
lemma step_label {d e : DA rep⊕DB rep}
    (h : PortWalk.step (graph rep r).origin (graph rep r).reverse d e) :
    label rep e≠Types.inverse (label rep d) := by
  intro he
  exact h.2 (immersed rep r e ((graph rep r).reverse d) h.1.symm
    (he.trans (label_reverse rep r d).symm))
lemma boundary_reduced (p : Position (fun t=>(s.paths t).length))
    (hp : s.root≠some p.1 ∨ p∉BoundaryRotation.ends (fun t=>(s.paths t).length)) :
    label rep (RawDecomposition.dart s.paths (perm (fun t=>(s.paths t).length) p))≠
      Types.inverse (label rep (RawDecomposition.dart s.paths p)) := by
  have hb : 0≤p.2.val ∧ p.2.val<((s.paths p.1).length:ℤ) := bounds p.2
  apply step_label
  by_cases hl : p.2.val+1=(s.paths p.1).length
  · apply step_last s.paths _ s.nonempty p hl
    apply s.cyclic_chain p.1
    apply (ClosedWords.cyclic_iff _ _).mpr
    rcases hp with hp|hp
    · exact hp
    · exact False.elim (hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩))
  · exact step_nonlast s.paths _ s.path_chain p (by omega)
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
abbrev len (p : BalancedWords.Piece w cap) := (BalancedWords.segment w cap hc p).length
abbrev e := WordPositions.segments w cap hc
omit [Fintype T] in
lemma value (x : Position (len w cap hc)) : (e w cap hc x).2.val=
    (ConsecutivePieces.offset (BalancedPieces.sizes (w x.1.1).length cap) x.1.2:ℤ)+x.2.val :=
  WordPositions.join_value w cap hc (ComparisonGeometry.position (Equiv.refl _) (BalancedWords.segment_length w cap hc) x)
def perm : Equiv.Perm (Position (len w cap hc)) :=
  (e w cap hc).symm.permCongr (BoundaryRotation.perm (fun t=>(w t).length))
omit [Fintype T] in
lemma transport (x : Position (len w cap hc)) :
    e w cap hc (perm w cap hc x)=BoundaryRotation.perm (fun t=>(w t).length) (e w cap hc x) := by
  simp only [perm,Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
lemma same_source {x y : Position (len w cap hc)} (h : x.1.1=y.1.1) : (perm w cap hc).SameCycle x y := by
  have hh := BoundaryRotation.same_first (fun t=>(w t).length) (x:=e w cap hc x) (y:=e w cap hc y) h
  have hp := PermutationTransport.sameCycle (e w cap hc).symm _ hh
  change ((e w cap hc).symm.permCongr (BoundaryRotation.perm (fun t=>(w t).length))).SameCycle x y
  simpa only [Equiv.symm_apply_apply] using hp
omit [Fintype T] in
lemma step {x : Position (len w cap hc)} (hx : x.2.val+1<(len w cap hc x.1:ℤ)) :
    (perm w cap hc x).1=x.1 ∧ (perm w cap hc x).2.val=x.2.val+1 := by
  have hb := bounds x.2
  let y : Position (len w cap hc) := ⟨x.1,⟨x.2.val+1,by
    simp only [AffineIntervals.nat_positions,Finset.mem_Ico]
    exact ⟨by omega,hx⟩⟩⟩
  have hy := bounds (e w cap hc y).2
  have hxe := value w cap hc x
  have hye := value w cap hc y
  dsimp only [y] at hye
  have ht : (e w cap hc x).2.val+1<((w (e w cap hc x).1).length:ℤ) := by
    have hy2 := hy.2
    change (e w cap hc y).2.val<((w x.1.1).length:ℤ) at hy2
    change (e w cap hc y).2.val=_+ (x.2.val+1) at hye
    change (e w cap hc x).2.val+1<((w x.1.1).length:ℤ)
    omega
  have he : e w cap hc (perm w cap hc x)=e w cap hc y := by
    rw [transport]
    apply PlanarIntervals.position_ext
    · exact BoundaryRotation.first _ _
    · rw [BoundaryRotation.next _ ht,hxe,hye]
      omega
  have he := (e w cap hc).injective he
  rw [he]
  exact ⟨rfl,rfl⟩
lemma hits (x : Position (len w cap hc)) :
    ∃ y∈BoundaryRotation.ends (len w cap hc),(perm w cap hc).SameCycle x y := by
  have hb := bounds x.2
  let j : Fin (len w cap hc x.1) := ⟨len w cap hc x.1-1,by omega⟩
  let y := (fin (len w cap hc)).symm ⟨x.1,j⟩
  refine ⟨y,?_,same_source w cap hc rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  change ((len w cap hc x.1-1:ℕ):ℤ)+1=len w cap hc x.1
  omega
lemma cycles_le : Fintype.card (Cycle (perm w cap hc))≤Fintype.card (BalancedWords.Piece w cap) := by
  have hT : Fintype.card (Cycle (perm w cap hc))≤Fintype.card T := by
    let f : Cycle (perm w cap hc) → T := fun c=>(Quotient.out c).1.1
    have hf : Function.Injective f := by
      intro c d hd
      have hh := same_source w cap hc hd
      have he := (cycle_eq (perm w cap hc)).mpr hh
      simpa only [cycle,Quotient.out_eq] using he
    exact Fintype.card_le_of_injective f hf
  apply hT.trans
  let f : T → BalancedWords.Piece w cap := fun t=>⟨t,⟨0,BalancedPieces.number_pos hc⟩⟩
  exact Fintype.card_le_of_injective f (fun _ _ h=>congrArg Sigma.fst h)
end TorsionFreeZeroDivisors.BalancedRotation

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
/-- The full inverse-letter pairing of the original boundary words, retaining
actual graph lifts. Planarity is additional data, not asserted here. -/
structure FullPairing (s : PathSystem rep r x y) where
  perm : Equiv.Perm (Position (fun t=>(s.paths t).length))
  involutive : Function.Involutive perm
  fixed_free : ∀p,perm p≠p
  compatible : ∀p,label rep (RawDecomposition.dart s.paths (perm p))=
    Types.inverse (label rep (RawDecomposition.dart s.paths p))
  reduced : ∀p,RawDecomposition.dart s.paths p≠RawDecomposition.dart s.paths (perm p) ∧
    RawDecomposition.dart s.paths p≠(graph rep r).reverse (RawDecomposition.dart s.paths (perm p))
namespace FullPairing
variable {s : PathSystem rep r x y} (a : FullPairing s) (cap : ℕ) (hc : 0<cap)
def α : Equiv.Perm (Position (BalancedRotation.len s.paths cap hc)) := (BalancedRotation.e s.paths cap hc).symm.permCongr a.perm
lemma α_involutive : Function.Involutive (a.α cap hc) :=
  PermutationTransport.involutive (BalancedRotation.e s.paths cap hc).symm a.perm a.involutive
lemma α_fixed_free (p : Position (BalancedRotation.len s.paths cap hc)) : a.α cap hc p≠p :=
  PermutationTransport.fixed_free (BalancedRotation.e s.paths cap hc).symm a.perm a.fixed_free p
lemma transport (p : Position (BalancedRotation.len s.paths cap hc)) : BalancedRotation.e s.paths cap hc (a.α cap hc p)=a.perm (BalancedRotation.e s.paths cap hc p) := by
  simp only [α,Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
def cuts : PlanarRuns.CutSystem (BalancedRotation.perm s.paths cap hc) :=
  PlanarRuns.CutSystem.ofMarks (a.α cap hc) (BoundaryRotation.ends (BalancedRotation.len s.paths cap hc))
    (BalancedRotation.hits s.paths cap hc)
theorem paired : (a.cuts cap hc).Paired (a.α cap hc) :=
  PlanarRuns.CutSystem.ofMarks_paired (a.α cap hc) (BoundaryRotation.ends (BalancedRotation.len s.paths cap hc))
    (BalancedRotation.hits s.paths cap hc) (a.α_involutive cap hc) (a.α_fixed_free cap hc)
lemma step (p : Position (BalancedRotation.len s.paths cap hc)) (hp : p∉(a.cuts cap hc).cut) :
    (BalancedRotation.perm s.paths cap hc p).1=p.1 ∧ (BalancedRotation.perm s.paths cap hc p).2.val=p.2.val+1 := by
  apply BalancedRotation.step
  have hb := WordPositions.bounds p.2
  have hn : p∉BoundaryRotation.ends (BalancedRotation.len s.paths cap hc) := by
    intro hm
    apply hp
    simp only [cuts,PlanarRuns.CutSystem.ofMarks,PlanarRotation.cuts,Finset.mem_union]
    exact Or.inl (Or.inr hm)
  have hn : p.2.val+1≠(BalancedRotation.len s.paths cap hc p.1:ℤ) := by
    intro he
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  omega
abbrev Side := {p // p∈(a.cuts cap hc).cut}
def comparisons : Comparisons (E:=a.Side cap hc) (BalancedRotation.len s.paths cap hc) :=
  PlanarIntervals.comparisons (a.cuts cap hc) (a.paired cap hc) (a.step cap hc)
def lower (d : a.Side cap hc) : ℕ := (PlanarIntervals.lower (a.cuts cap hc) (a.paired cap hc) d).toNat
def upper (d : a.Side cap hc) : ℕ := (PlanarIntervals.upper (a.cuts cap hc) d).toNat
lemma bounds (d : a.Side cap hc) :
    0≤PlanarIntervals.lower (a.cuts cap hc) (a.paired cap hc) d ∧
    PlanarIntervals.lower (a.cuts cap hc) (a.paired cap hc) d<PlanarIntervals.upper (a.cuts cap hc) d ∧
    PlanarIntervals.upper (a.cuts cap hc) d≤BalancedRotation.len s.paths cap hc ((a.paired cap hc).first d).1 :=
  PlanarIntervals.bounds (a.cuts cap hc) (a.paired cap hc) (a.step cap hc) d
lemma lower_eq (d : a.Side cap hc) : (a.comparisons cap hc).lo d=a.lower cap hc d := by
  change (PlanarIntervals.lower (a.cuts cap hc) (a.paired cap hc) d:ℝ)=_
  rw [lower,←Int.cast_natCast,Int.toNat_of_nonneg (a.bounds cap hc d).1]
lemma upper_eq (d : a.Side cap hc) : (a.comparisons cap hc).hi d=a.upper cap hc d := by
  change (PlanarIntervals.upper (a.cuts cap hc) d:ℝ)=_
  rw [upper,←Int.cast_natCast,Int.toNat_of_nonneg (by have := a.bounds cap hc d; omega)]
lemma lower_le (d : a.Side cap hc) : a.lower cap hc d≤a.upper cap hc d := by
  have := a.bounds cap hc d
  dsimp only [lower,upper]
  omega
lemma upper_le (d : a.Side cap hc) : a.upper cap hc d≤BalancedRotation.len s.paths cap hc ((a.comparisons cap hc).source d) := by
  exact Int.toNat_le.mpr (a.bounds cap hc d).2.2
lemma dart (p : Position (BalancedRotation.len s.paths cap hc)) : RawDecomposition.dart (ClosedWords.seg s cap hc) p=
    RawDecomposition.dart s.paths (BalancedRotation.e s.paths cap hc p) := WordPositions.segments_dart s.paths cap hc p
lemma balanced_reduced (p : Position (BalancedRotation.len s.paths cap hc)) :
    RawDecomposition.dart (ClosedWords.seg s cap hc) p≠RawDecomposition.dart (ClosedWords.seg s cap hc) (a.α cap hc p) ∧
    RawDecomposition.dart (ClosedWords.seg s cap hc) p≠(graph rep r).reverse (RawDecomposition.dart (ClosedWords.seg s cap hc) (a.α cap hc p)) := by
  rw [dart cap hc,dart cap hc,a.transport]
  exact a.reduced (BalancedRotation.e s.paths cap hc p)
lemma balanced_compatible (p : Position (BalancedRotation.len s.paths cap hc)) :
    label rep (RawDecomposition.dart (ClosedWords.seg s cap hc) p)=
      Types.inverse (label rep (RawDecomposition.dart (ClosedWords.seg s cap hc) (a.α cap hc p))) := by
  rw [dart cap hc,dart cap hc,a.transport,a.compatible,Types.inverse_inverse]
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
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    {s : PathSystem rep r x y} (a : FullPairing s) (cap : ℕ) (hc : 0<cap)
lemma opposite_eq : opposite (BalancedRotation.perm s.paths cap hc) (a.α cap hc)=
    (BalancedRotation.e s.paths cap hc).symm.permCongr
      (opposite (BoundaryRotation.perm (fun t=>(s.paths t).length)) a.perm) := by
  exact (PermutationTransport.mul (BalancedRotation.e s.paths cap hc).symm a.perm _).symm
lemma opposite_transport (p : Position (BalancedRotation.len s.paths cap hc)) :
    BalancedRotation.e s.paths cap hc (opposite (BalancedRotation.perm s.paths cap hc) (a.α cap hc) p)=
      opposite (BoundaryRotation.perm (fun t=>(s.paths t).length)) a.perm (BalancedRotation.e s.paths cap hc p) := by
  change BalancedRotation.e s.paths cap hc (a.α cap hc (BalancedRotation.perm s.paths cap hc p))=_
  rw [a.transport,BalancedRotation.transport]
  rfl
lemma monogons : (fixed (opposite (BalancedRotation.perm s.paths cap hc) (a.α cap hc))).card≤1 := by
  have ho := BoundaryRotation.monogons_le (fun t=>(s.paths t).length) s.root
    (fun p=>label rep (RawDecomposition.dart s.paths p)) Types.inverse a.perm a.involutive
    a.compatible s.boundary_reduced
  apply Finset.card_le_one.mpr
  intro p hp q hq
  simp only [fixed,Finset.mem_filter,Finset.mem_univ,true_and] at hp hq
  apply (BalancedRotation.e s.paths cap hc).injective
  apply Finset.card_le_one.mp ho
  · simp only [fixed,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [←a.opposite_transport,hp]
  · simp only [fixed,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [←a.opposite_transport,hq]
/-- Only Euler planarity is needed in the interval-count argument. This file
proves neither Euler planarity for an abstract pairing nor its PL realization. -/
def Euler : Prop := Fintype.card (Position (fun t=>(s.paths t).length))+4≤
  2*Fintype.card (Cycle (BoundaryRotation.perm (fun t=>(s.paths t).length)))+
  2*Fintype.card (Cycle (opposite (BoundaryRotation.perm (fun t=>(s.paths t).length)) a.perm))
lemma balanced_euler (h : a.Euler) : Fintype.card (Position (BalancedRotation.len s.paths cap hc))+4≤
    2*Fintype.card (Cycle (BalancedRotation.perm s.paths cap hc))+
    2*Fintype.card (Cycle (opposite (BalancedRotation.perm s.paths cap hc) (a.α cap hc))) := by
  rw [a.opposite_eq,PermutationTransport.card_cycles]
  change _≤2*Fintype.card (Cycle ((BalancedRotation.e s.paths cap hc).symm.permCongr
    (BoundaryRotation.perm (fun t=>(s.paths t).length))))+_
  rw [PermutationTransport.card_cycles,Fintype.card_congr (BalancedRotation.e s.paths cap hc)]
  exact h
lemma sides_le (h : a.Euler) : Fintype.card (a.Side cap hc)≤12*Fintype.card (ClosedWords.Piece s cap) := by
  rw [Fintype.card_coe]
  apply cuts_le_twelve
  · exact a.balanced_euler cap hc h
  · exact a.monogons cap hc
  · exact BalancedRotation.cycles_le s.paths cap hc
  · have hm := BoundaryRotation.ends_le (BalancedRotation.len s.paths cap hc)
    exact hm.trans (Nat.le_add_left _ _)
end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    {s : PathSystem rep r x y} (a : FullPairing s) (cap : ℕ) (hc : 0<cap)
    (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
/-- The actual balanced and short-closed system, with all cut comparisons and
all closure positions left unpaired. -/
def closed : PathSystem rep r x y := ClosedWords.system s cap hc hL hd (a.comparisons cap hc)
  (a.lower cap hc) (a.upper cap hc) (a.lower_eq cap hc) (a.upper_eq cap hc)
  (a.lower_le cap hc) (a.upper_le cap hc)
  (fun p _ _=>a.balanced_reduced cap hc p) (fun p _ _=>a.balanced_compatible cap hc p)
lemma closed_fixed : (Finset.univ.filter (fun p=>(a.closed cap hc hL hd).comparisons.pairing.partner p=p)).card=
    ∑t,(ClosedWords.tail s cap hc hL hd t).length :=
  WordPositions.fixed_card (ClosedWords.seg s cap hc) (ClosedWords.tail s cap hc hL hd)
    (a.comparisons cap hc) (a.α_fixed_free cap hc)
lemma closed_old (p : Position (fun t=>((a.closed cap hc hL hd).paths t).length))
    (hp : (a.closed cap hc hL hd).comparisons.pairing.partner p≠p) :
    p.2.val∈positions 0 (BalancedWords.old s.paths cap p.1) := by
  have hh := WordPositions.nonfixed_old (ClosedWords.seg s cap hc) (ClosedWords.tail s cap hc hL hd)
    (a.comparisons cap hc) p hp
  convert hh using 2
  exact_mod_cast (BalancedWords.segment_length s.paths cap hc p.1).symm
end TorsionFreeZeroDivisors.SampleGraph.FullPairing

/-! Recursive separation. This is the actual deletion-set
construction and sharp charging estimate. The one-step Lipton–Tarjan theorem
is kept as an explicit dependency, not asserted from an unspecified planar
predicate.  No claim of a completed planar realization is made here. -/
namespace TorsionFreeZeroDivisors.RecursiveSeparator
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] (R : V → V → Prop)

/-- Every retained vertex lies in a small set closed under all retained edges. -/
def Small (S : Finset V) (K : ℕ) : Prop :=
  ∀ x∈S, ∃ T : Finset V, T⊆S ∧ x∈T ∧ T.card≤K ∧
    ∀ y∈T, ∀ z∈S, R y z → z∈T

omit [DecidableEq V] in
lemma small_of_card {S : Finset V} {K : ℕ} (h : S.card≤K) : Small R S K := by
  intro x hx
  exact ⟨S,Finset.Subset.refl _,hx,h,fun _ _ _ hz _ => hz⟩

namespace Split
variable {R} {S : Finset V} (P : Split R S)
lemma subset {b : Finset V} (hb : b∈P.parts) : b⊆S\P.remove := by
  intro x hx
  rw [←P.cover]
  exact Finset.mem_biUnion.mpr ⟨b,hb,hx⟩
lemma mass : (∑ b∈P.parts,b.card)+P.remove.card=S.card := by
  have h := Finset.card_biUnion P.disjoint
  change (P.parts.biUnion id).card=∑ b∈P.parts,b.card at h
  rw [P.cover] at h
  rw [←h,Finset.card_sdiff_of_subset P.remove_subset]
  exact Nat.sub_add_cancel (Finset.card_le_card P.remove_subset)
lemma smaller {b : Finset V} (hb : b∈P.parts) (hS : 0<S.card) : b.card<S.card := by
  have h := P.size b hb
  omega
end Split

lemma q_pos : 0<q := Real.sqrt_pos.mpr (by norm_num)
lemma q_lt_one : q<1 := by
  unfold q
  have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤2/3) (by norm_num : (2/3:ℝ)<1)
  simpa only [Real.sqrt_one] using h
lemma a_pos : 0<a := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
lemma Csep_pos : 0<Csep := div_pos a_pos (sub_pos.mpr q_lt_one)
lemma Csep_identity : Csep*(1-q)=a := div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr q_lt_one))

lemma sqrt_size {b s : ℕ} (h : 3*b≤2*s) : Real.sqrt b≤q*Real.sqrt s := by
  unfold q
  rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤2/3)]
  apply Real.sqrt_le_sqrt
  have hh : 3*(b:ℝ)≤2*(s:ℝ) := by exact_mod_cast h
  linarith

/-- Charge bound for one recursive child, including leaves that incur no cost. -/
lemma child_charge {K s b : ℕ} (hK : 0<K) (hs : K<s) (hb : 3*b≤2*s)
    {d : ℝ} (hd : if b≤K then d=0 else d≤Csep*b/Real.sqrt K-Csep*q*Real.sqrt b) :
    d≤Csep*b/Real.sqrt K-Csep*b/Real.sqrt s := by
  have hKp : 0<Real.sqrt (K:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hK)
  have hsp : 0<Real.sqrt (s:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (hK.trans hs))
  have hKs : Real.sqrt (K:ℝ)≤Real.sqrt (s:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hs.le)
  by_cases hbK : b≤K
  · rw [if_pos hbK] at hd
    rw [hd]
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left (mul_nonneg Csep_pos.le (Nat.cast_nonneg _)) hKp hKs
  · rw [if_neg hbK] at hd
    apply hd.trans
    apply sub_le_sub_left
    have hh := mul_le_mul_of_nonneg_left (sqrt_size hb) (Real.sqrt_nonneg (b:ℝ))
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _)] at hh
    have hh' : (b:ℝ)/Real.sqrt s≤q*Real.sqrt b := by
      apply (div_le_iff₀ hsp).mpr
      nlinarith only [hh]
    have hh'' := mul_le_mul_of_nonneg_left hh' Csep_pos.le
    simpa only [mul_div_assoc,mul_assoc] using hh''

lemma parent_charge {K s d : ℕ} (hK : 0<K) (hs : K<s) (hd : d ≤ s)
    (hcost : (d:ℝ)≤a*Real.sqrt s) :
    (d:ℝ)+Csep*((s-d:ℕ):ℝ)/Real.sqrt K-Csep*((s-d:ℕ):ℝ)/Real.sqrt s
      ≤ Csep*s/Real.sqrt K-Csep*q*Real.sqrt s := by
  have hKp : 0<Real.sqrt (K:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hK)
  have hsp : 0<Real.sqrt (s:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (hK.trans hs))
  have hKs : Real.sqrt (K:ℝ)≤Real.sqrt (s:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hs.le)
  have hcoeff : 0≤Csep/Real.sqrt K-Csep/Real.sqrt s := sub_nonneg.mpr
    (div_le_div_of_nonneg_left Csep_pos.le hKp hKs)
  have hnonneg := mul_nonneg (Nat.cast_nonneg d) hcoeff
  have he : (s:ℝ)/Real.sqrt s=Real.sqrt s := by
    apply (div_eq_iff (ne_of_gt hsp)).mpr
    exact (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
  rw [Nat.cast_sub hd]
  have hc := Csep_identity
  calc
    _ ≤ a*Real.sqrt s+Csep*s/Real.sqrt K-Csep*s/Real.sqrt s := by
      simp only [div_eq_mul_inv] at hnonneg ⊢
      nlinarith only [hnonneg,hcost]
    _ = _ := by
      have he' : Csep*(s:ℝ)/Real.sqrt s=Csep*Real.sqrt s := by rw [mul_div_assoc,he]
      rw [he']
      have hcs := congrArg (fun x : ℝ => x*Real.sqrt s) hc
      nlinarith only [hcs]

namespace Split
variable {R} {S : Finset V} (P : Split R S) (D : Finset V → Finset V)
def combined : Finset V := P.remove∪P.parts.biUnion D
lemma child_deleted {b : Finset V} (hb : b∈P.parts) : D b⊆P.combined D := by
  intro x hx
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b,hb,hx⟩)
lemma combined_subset (hD : ∀ b∈P.parts,D b⊆b) : P.combined D⊆S := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx|hx
  · exact P.remove_subset hx
  · obtain ⟨b,hb,hx⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_sdiff.mp (P.subset hb (hD b hb hx))).1
lemma combined_small {K : ℕ} (hsmall : ∀ b∈P.parts,Small R (b\D b) K) :
    Small R (S\P.combined D) K := by
  intro x hx
  have hxS := (Finset.mem_sdiff.mp hx).1
  have hxr : x∉P.remove := fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ h)
  have hcover : x∈P.parts.biUnion id := by rw [P.cover]; exact Finset.mem_sdiff.mpr ⟨hxS,hxr⟩
  obtain ⟨b,hb,hxb⟩ := Finset.mem_biUnion.mp hcover
  have hxd : x∉D b := fun h => (Finset.mem_sdiff.mp hx).2 (P.child_deleted D hb h)
  obtain ⟨T,hTb,hxT,hTK,hclosed⟩ := hsmall b hb x (Finset.mem_sdiff.mpr ⟨hxb,hxd⟩)
  refine ⟨T∩(S\P.combined D),Finset.inter_subset_right,Finset.mem_inter.mpr ⟨hxT,hx⟩,
    (Finset.card_le_card Finset.inter_subset_left).trans hTK,?_⟩
  intro y hy z hz hyz
  have hyT := (Finset.mem_inter.mp hy).1
  have hyb := (Finset.mem_sdiff.mp (hTb hyT)).1
  have hzS := (Finset.mem_sdiff.mp hz).1
  have hzr : z∉P.remove := fun h => (Finset.mem_sdiff.mp hz).2 (Finset.mem_union_left _ h)
  have hzb := P.closed b hb y hyb z (Finset.mem_sdiff.mpr ⟨hzS,hzr⟩) hyz
  have hzd : z∉D b := fun h => (Finset.mem_sdiff.mp hz).2 (P.child_deleted D hb h)
  exact Finset.mem_inter.mpr ⟨hclosed y hyT z (Finset.mem_sdiff.mpr ⟨hzb,hzd⟩) hyz,hz⟩
lemma combined_card : (P.combined D).card≤P.remove.card+∑ b∈P.parts,(D b).card := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_biUnion_le) _)
end Split

/-- Exact recursive deletion, with a stronger potential bound used internally. -/
theorem recursive (K : ℕ) (hK : 0<K)
    (oneStep : ∀ S : Finset V,K<S.card → Nonempty (Split R S)) (S : Finset V) :
    ∃ D : Finset V,D⊆S ∧ Small R (S\D) K ∧
      (if S.card≤K then D=∅ else
        (D.card:ℝ)≤Csep*S.card/Real.sqrt K-Csep*q*Real.sqrt S.card) := by
  suffices ∀ m,∀ S : Finset V,S.card=m →
      ∃ D : Finset V,D⊆S ∧ Small R (S\D) K ∧
        (if S.card≤K then D=∅ else
          (D.card:ℝ)≤Csep*S.card/Real.sqrt K-Csep*q*Real.sqrt S.card) from this _ S rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro S hm
    by_cases hSK : S.card≤K
    · refine ⟨∅,Finset.empty_subset _,?_,by simp only [if_pos hSK]⟩
      simpa only [Finset.sdiff_empty] using small_of_card R hSK
    have hKS : K<S.card := lt_of_not_ge hSK
    let P := (oneStep S hKS).some
    have hchild : ∀ b∈P.parts,∃ D : Finset V,D⊆b ∧ Small R (b\D) K ∧
        (if b.card≤K then D=∅ else
          (D.card:ℝ)≤Csep*b.card/Real.sqrt K-Csep*q*Real.sqrt b.card) := by
      intro b hb
      exact ih b.card (hm ▸ P.smaller hb (hK.trans hKS)) b rfl
    let D : Finset V → Finset V := fun b => if hb : b∈P.parts then (hchild b hb).choose else ∅
    have hD : ∀ b∈P.parts,D b⊆b ∧ Small R (b\D b) K ∧
        (if b.card≤K then D b=∅ else
          ((D b).card:ℝ)≤Csep*b.card/Real.sqrt K-Csep*q*Real.sqrt b.card) := by
      intro b hb
      dsimp only [D]
      rw [dif_pos hb]
      exact (hchild b hb).choose_spec
    refine ⟨P.combined D,P.combined_subset D (fun b hb => (hD b hb).1),
      P.combined_small D (fun b hb => (hD b hb).2.1),?_⟩
    rw [if_neg hSK]
    have hcharge : ∀ b∈P.parts,((D b).card:ℝ)≤
        Csep*b.card/Real.sqrt K-Csep*b.card/Real.sqrt S.card := by
      intro b hb
      apply child_charge hK hKS (P.size b hb)
      have hh := (hD b hb).2.2
      split_ifs at hh ⊢ with hc
      · simp only [hh,Finset.card_empty,Nat.cast_zero]
      · exact hh
    have hsummass : (∑ b∈P.parts,(b.card:ℝ))=(S.card:ℝ)-P.remove.card := by
      have hh : (∑ b∈P.parts,(b.card:ℝ))+(P.remove.card:ℝ)=S.card := by exact_mod_cast P.mass
      linarith
    have hsum : (∑ b∈P.parts,((D b).card:ℝ))≤
        Csep*((S.card:ℝ)-P.remove.card)/Real.sqrt K-
        Csep*((S.card:ℝ)-P.remove.card)/Real.sqrt S.card := by
      calc
        _ ≤ ∑ b∈P.parts,(Csep*b.card/Real.sqrt K-Csep*b.card/Real.sqrt S.card) :=
          Finset.sum_le_sum hcharge
        _ = _ := by rw [Finset.sum_sub_distrib,←Finset.sum_div,←Finset.mul_sum,
          ←Finset.sum_div,←Finset.mul_sum,hsummass]
    have hcard : ((P.combined D).card:ℝ)≤P.remove.card+∑ b∈P.parts,((D b).card:ℝ) := by
      exact_mod_cast P.combined_card D
    have hp := parent_charge hK hKS (Finset.card_le_card P.remove_subset) P.cost
    rw [Nat.cast_sub (Finset.card_le_card P.remove_subset)] at hp
    linarith only [hcard,hsum,hp]

/-- Source recursive planar-separation bound, once the actual one-step planar
separator is supplied for every induced subgraph. -/
theorem separator (K : ℕ) (hK : 1≤K)
    (oneStep : ∀ S : Finset V,K<S.card → Nonempty (Split R S)) (S : Finset V) :
    ∃ D : Finset V,D⊆S ∧ Small R (S\D) K ∧ (D.card:ℝ)≤Csep*S.card/Real.sqrt K := by
  obtain ⟨D,hD,hsmall,hcost⟩ := recursive R K hK oneStep S
  refine ⟨D,hD,hsmall,?_⟩
  split_ifs at hcost with h
  · rw [hcost,Finset.card_empty,Nat.cast_zero]
    exact div_nonneg (mul_nonneg Csep_pos.le (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  · exact hcost.trans (sub_le_self _ (mul_nonneg (mul_nonneg Csep_pos.le q_pos.le) (Real.sqrt_nonneg _)))
end TorsionFreeZeroDivisors.RecursiveSeparator

namespace TorsionFreeZeroDivisors.PlanarParameters
open scoped Classical
open RecursiveSeparator
variable (ε : ℝ) (D : ℕ)
lemma U_ge : 3≤U ε D := le_max_left _ _
lemma U_pos : 0<U ε D := lt_of_lt_of_le (by norm_num) (U_ge ε D)
lemma η_pos (hε : 0<ε) : 0<η ε D := by
  have hu : (0:ℝ)<U ε D := by exact_mod_cast U_pos ε D
  exact lt_min (by positivity) (by positivity)
lemma K_pos : 0<K ε D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)

lemma closure_loss (hε : 0<ε) : 3*(D:ℝ)/(U ε D:ℝ)≤ε/32 := by
  have hu : (0:ℝ)<U ε D := by exact_mod_cast U_pos ε D
  have hc : 96*(D:ℝ)/ε≤U ε D :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hh := (div_le_iff₀ hε).mp hc
  apply (div_le_iff₀ hu).mpr
  nlinarith
lemma deletion_loss : 2*η ε D*(U ε D:ℝ)≤1/16 := by
  have hu : (0:ℝ)<U ε D := by exact_mod_cast U_pos ε D
  have h := min_le_left (1/(32*(U ε D:ℝ))) (ε/(64*(U ε D:ℝ)))
  change η ε D≤1/(32*(U ε D:ℝ)) at h
  have hh := (le_div_iff₀ (mul_pos (by norm_num) hu)).mp h
  nlinarith
lemma unpaired_loss : 2*η ε D*(U ε D:ℝ)≤ε/32 := by
  have hu : (0:ℝ)<U ε D := by exact_mod_cast U_pos ε D
  have h := min_le_right (1/(32*(U ε D:ℝ))) (ε/(64*(U ε D:ℝ)))
  change η ε D≤ε/(64*(U ε D:ℝ)) at h
  have hh := (le_div_iff₀ (mul_pos (by norm_num) hu)).mp h
  nlinarith
lemma separator_factor (hε : 0<ε) : Csep/Real.sqrt (K ε D:ℝ)≤η ε D := by
  have he := η_pos ε D hε
  have hk : (0:ℝ)<K ε D := by exact_mod_cast K_pos ε D
  have hq : (Csep/η ε D)^2≤K ε D :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have hs := Real.sqrt_nonneg (K ε D:ℝ)
  have hs2 := Real.sq_sqrt hk.le
  have hp : 0<Csep/η ε D := div_pos Csep_pos he
  have hs' : Csep/η ε D≤Real.sqrt (K ε D:ℝ) := by nlinarith
  have hh := (div_le_iff₀ he).mp hs'
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hk)).mpr
  nlinarith

/-- No planar theorem is hidden here: this uses the actual one-step Split
objects and constructs a literal deletion set, with the fixed source K. -/
theorem delete {V : Type} [Fintype V] (R : V → V → Prop) (hε : 0<ε)
    (oneStep : ∀ S : Finset V,K ε D<S.card → Nonempty (Split R S)) :
    ∃ A : Finset V,Small R (Finset.univ\A) (K ε D) ∧
      (A.card:ℝ)≤η ε D*Fintype.card V := by
  obtain ⟨A,_hA,hsmall,hcost⟩ := separator R (K ε D) (K_pos ε D) oneStep Finset.univ
  refine ⟨A,hsmall,?_⟩
  apply hcost.trans
  rw [Finset.card_univ,mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right (separator_factor ε D hε) (Nat.cast_nonneg _)
end TorsionFreeZeroDivisors.PlanarParameters

namespace TorsionFreeZeroDivisors.LocalizationCounts
open scoped Classical BigOperators
open ComparedBlocks BlockAlignment
variable {T E : Type} [Fintype T] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop) (old : T → ℕ)
    (hprefix : ∀ p : Position len,C.pairing.partner p≠p → p.2.val∈positions 0 (old p.1))

def deletedMap (p : {p : Position len // ¬keep p.1 ∧ C.pairing.partner p≠p}) :
    Position (fun t : {t // ¬keep t}=>old t.val) :=
  ⟨⟨p.val.1,p.property.1⟩,⟨p.val.2.val,hprefix p.val p.property.2⟩⟩
omit [Fintype T] in
lemma deleted_injective : Function.Injective (deletedMap C keep old hprefix) := by
  intro a b h
  have ht : a.val.1=b.val.1 := congrArg (fun p=>p.1.val) h
  have hq : a.val.2.val=b.val.2.val := congrArg (fun p=>p.2.val) h
  apply Subtype.ext
  rcases a with ⟨⟨t,x⟩,ha⟩
  rcases b with ⟨⟨u,y⟩,hb⟩
  dsimp only at ht hq ⊢
  subst u
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hq))

include hprefix in
/-- Only deleted ORIGINAL occurrences, not closures, can destroy a partner. -/
lemma deleted_nonfixed_le :
    (Finset.univ.filter (fun p : Position len=>¬keep p.1 ∧ C.pairing.partner p≠p)).card≤
      ∑t∈Finset.univ.filter (fun t=>¬keep t),old t := by
  have hh := Fintype.card_le_of_injective _ (deleted_injective C keep old hprefix)
  have hs : (∑t : {t // ¬keep t},old t.val)=∑t∈Finset.univ.filter (fun t=>¬keep t),old t :=
    (Finset.sum_subtype _ (by intro t; simp) old).symm
  rw [FiniteChunking.position_card,hs] at hh
  simpa only [Fintype.card_subtype] using hh

/-- The exact removed-original-position bound, from the actual deletion set. -/
lemma deleted_mass {U L : ℕ} {η H₀ : ℝ}
    (hcap : ∀ t,old t≤U*L) (hη : 0≤η)
    (hcount : ((Finset.univ.filter (fun t=>¬keep t)).card:ℝ)≤η*Fintype.card T)
    (hpieces : (Fintype.card T:ℝ)*L≤2*H₀) :
    (∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ))≤2*η*U*H₀ := by
  calc
    _ ≤ ∑_t∈Finset.univ.filter (fun t=>¬keep t),(U:ℝ)*L := by
      apply Finset.sum_le_sum
      intro t _
      exact_mod_cast hcap t
    _ = ((Finset.univ.filter (fun t=>¬keep t)).card:ℝ)*(U:ℝ)*L := by simp; ring
    _ ≤ (η*Fintype.card T)*(U:ℝ)*L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _ = η*U*((Fintype.card T:ℝ)*L) := by ring
    _ ≤ η*U*(2*H₀) := mul_le_mul_of_nonneg_left hpieces (mul_nonneg hη (Nat.cast_nonneg _))
    _ = _ := by ring
end TorsionFreeZeroDivisors.LocalizationCounts

namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs ComparedBlocks ClusterLocalization
lemma ε_pos : 0<ε := StageFusion.epsilon_pos (by norm_num) (by norm_num)
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y)
local instance : Fintype s.P := s.fP
local instance : Fintype s.E := s.fE

/-- The complete deterministic separator-to-forbidden-system implication.
The one-step separator is explicitly the still-missing planar geometry input;
the deletion set, losses, clusters, and realized forbidden words are constructed. -/
theorem excluded_of_separator (D : ℕ) (H₀ : ℝ) (old : s.P → ℕ)
    (hH₀ : 0<H₀) (hL : 0<L (size rep))
    (ho : ∀ t,old t≤(s.paths t).length)
    (hcapOld : ∀ t,old t≤PlanarParameters.U ε D*L (size rep))
    (hcap : ∀ t,(s.paths t).length≤(PlanarParameters.U ε D+D)*L (size rep))
    (hbase : H₀≤∑t,(old t:ℝ))
    (hpieces : (Fintype.card s.P:ℝ)*L (size rep)≤2*H₀)
    (hadded : ((Finset.univ.filter (fun p=>s.comparisons.pairing.partner p=p)).card:ℝ)≤
      3*(D:ℝ)/PlanarParameters.U ε D*H₀)
    (hprefix : ∀ p : Position (fun t=>(s.paths t).length),s.comparisons.pairing.partner p≠p →
      p.2.val∈BlockAlignment.positions 0 (old p.1))
    (hcompare : Fintype.card s.E≤12*Fintype.card s.P)
    (hlong : ∀ t,s.root≠some t → L (size rep)≤(s.paths t).length)
    (hroot : ∀ t,s.root=some t → (s.paths t).length<L (size rep) → ((s.paths t).length:ℝ)≤H₀/2)
    (oneStep : ∀ S : Finset s.P,PlanarParameters.K ε D<S.card →
      Nonempty (RecursiveSeparator.Split
        (PairingClusters.Rel (fun p : Position (fun t=>(s.paths t).length)=>p.1) s.comparisons.pairing.partner) S))
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C ε D) (PlanarParameters.K ε D)
      (PlanarParameters.sides ε D) rep r x y)) : False := by
  classical
  let R := PairingClusters.Rel (fun p : Position (fun t=>(s.paths t).length)=>p.1) s.comparisons.pairing.partner
  obtain ⟨A,hsmall,hA⟩ := PlanarParameters.delete ε D R ε_pos oneStep
  let keep : s.P → Prop := fun t=>t∉A
  have hcount : ((Finset.univ.filter (fun t=>¬keep t)).card:ℝ)≤PlanarParameters.η ε D*Fintype.card s.P := by
    simpa only [keep,not_not,Finset.filter_mem_eq_inter,Finset.univ_inter] using hA
  have hsize : ∀ c : Cluster s.comparisons keep,(ClusterLocalization.paths s.comparisons keep c).card≤PlanarParameters.K ε D := by
    apply ClusterLocalization.paths_card_le
    intro t ht
    obtain ⟨B,_hB,htB,hBK,hcl⟩ := hsmall t (by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and] using ht)
    refine ⟨B,htB,hBK,?_⟩
    intro a ha b hb hab
    exact hcl a ha b (by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and] using hb) hab
  have hη := (PlanarParameters.η_pos ε D ε_pos).le
  have hd : (∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ))≤2*PlanarParameters.η ε D*PlanarParameters.U ε D*H₀ := by
    convert LocalizationCounts.deleted_mass keep old hcapOld hη (by
      convert hcount using 1
      congr 2
      ext t
      simp) hpieces using 1
    congr 1
    ext t
    simp
  have hdshort : (∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ))≤H₀/16 := by
    apply hd.trans
    have hh := mul_le_mul_of_nonneg_right (PlanarParameters.deletion_loss ε D) hH₀.le
    nlinarith
  have hdε : (∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ))≤ε/32*H₀ := by
    exact hd.trans (mul_le_mul_of_nonneg_right (PlanarParameters.unpaired_loss ε D) hH₀.le)
  have hb : ((Finset.univ.filter (fun p=>s.comparisons.pairing.partner p=p)).card:ℝ)+
      ((Finset.univ.filter (fun p=>¬keep p.1 ∧ s.comparisons.pairing.partner p≠p)).card:ℝ)≤ε/16*H₀ := by
    have hnew : ((Finset.univ.filter (fun p=>¬keep p.1 ∧ s.comparisons.pairing.partner p≠p)).card:ℝ)≤
        ∑t∈Finset.univ.filter (fun t=>¬keep t),(old t:ℝ) := by
      have hn := LocalizationCounts.deleted_nonfixed_le s.comparisons keep old hprefix
      have hn' : (Finset.univ.filter (fun p=>¬keep p.1 ∧ s.comparisons.pairing.partner p≠p)).card≤
          ∑t∈Finset.univ.filter (fun t=>¬keep t),old t := by
        convert hn using 1 <;> congr 1 <;> ext t <;> simp
      exact_mod_cast hn'
    have ha := mul_le_mul_of_nonneg_right (PlanarParameters.closure_loss ε D ε_pos) hH₀.le
    linarith
  have hcomp : (Fintype.card s.E:ℝ)/2≤(192:ℝ)/(16*L (size rep))*H₀ := by
    have hh : (Fintype.card s.E:ℝ)≤12*Fintype.card s.P := by exact_mod_cast hcompare
    have hLr : (0:ℝ)<L (size rep) := by exact_mod_cast hL
    rw [show (192:ℝ)/(16*L (size rep))*H₀=12*H₀/L (size rep) by ring]
    apply (le_div_iff₀ hLr).mpr
    have hc := mul_le_mul_of_nonneg_right hh hLr.le
    nlinarith
  have hi : ⌈2*(192:ℝ)*(PlanarParameters.K ε D*(PlanarParameters.U ε D+D):ℝ)⌉₊=
      PlanarParameters.sides ε D := by
    rw [show 2*(192:ℝ)*(PlanarParameters.K ε D*(PlanarParameters.U ε D+D):ℝ)=
      (2*192*(PlanarParameters.K ε D*(PlanarParameters.U ε D+D)):ℕ) by push_cast; ring]
    rw [Nat.ceil_natCast]
    rfl
  have havoid' : IsEmpty (BoundedSystem (PlanarParameters.K ε D*(PlanarParameters.U ε D+D))
      (PlanarParameters.K ε D) ⌈2*(192:ℝ)*(PlanarParameters.K ε D*(PlanarParameters.U ε D+D):ℝ)⌉₊ rep r x y) := by
    rw [hi]
    exact havoid
  exact s.excluded_of_local_totals keep (PlanarParameters.K ε D) (PlanarParameters.U ε D+D)
    192 H₀ old ho hH₀ hL (by norm_num) hsize hcap hbase (by
      convert hdshort using 1
      congr 1
      ext t
      simp) (by
      convert hb using 1
      congr 3
      ext t
      simp) hcomp hlong hroot (by
      convert havoid' using 1
      push_cast
      rfl)
end TorsionFreeZeroDivisors.SampleGraph.PathSystem

namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
abbrev U₀ : ℕ := PlanarParameters.U PathSystem.ε ClosedWords.D
lemma U₀_ge : 3≤U₀ := PlanarParameters.U_ge _ _
lemma cap_lower {rep : ℕ} (hL : 2≤L (size rep)) : 6≤U₀*L (size rep) := by
  have := U₀_ge
  nlinarith
abbrev cap_positive {rep : ℕ} (hL : 2≤L (size rep)) : 0<U₀*L (size rep) := by
  have := cap_lower hL
  omega
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    {s : PathSystem rep r x y} (a : FullPairing s) (hL : 2≤L (size rep))
    (hd : GraphSample.Diameters rep r)
def prepared : PathSystem rep r x y := a.closed (U₀*L (size rep)) (cap_positive hL) (by omega) hd
/-- Literal full-pairing exclusion. Euler planarity and the one-step separator
are the two remaining geometric inputs, not extra source hypotheses on the
main theorem. No claim of their unconditional existence is made here. -/
theorem excluded (hr : r∈samples rep) (hordinary : ∃t,s.root≠some t) (heuler : a.Euler)
    (oneStep : ∀ S : Finset (a.prepared hL hd).P,PlanarParameters.K PathSystem.ε ClosedWords.D<S.card →
      Nonempty (RecursiveSeparator.Split
        (PairingClusters.Rel (fun p : Position (fun t=>((a.prepared hL hd).paths t).length)=>p.1)
          (a.prepared hL hd).comparisons.pairing.partner) S))
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
      (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y)) : False := by
  have hLl : 1≤L (size rep) := by omega
  have hc := cap_positive hL
  have hcp := cap_lower hL
  have hH : 0<(ClosedWords.H₀ s:ℝ) := by
    have hm := ClosedWords.H₀_ge s hr hordinary
    have : 0<ClosedWords.H₀ s := by omega
    exact_mod_cast this
  apply (a.prepared hL hd).excluded_of_separator ClosedWords.D (ClosedWords.H₀ s)
    (BalancedWords.old s.paths (U₀*L (size rep))) hH (by omega)
  · exact ClosedWords.old_le_word s _ hc hLl hd
  · exact BalancedWords.old_le s.paths _ hcp
  · intro t
    change (ClosedWords.word s _ hc hLl hd t).length≤_
    have hh := ClosedWords.word_bound s _ hc hLl hd hcp t
    simpa only [Nat.add_mul] using hh
  · change (ClosedWords.H₀ s:ℝ)≤∑t : ClosedWords.Piece s (U₀*L (size rep)),
      (BalancedWords.old s.paths (U₀*L (size rep)) t:ℝ)
    rw [←Nat.cast_sum,BalancedWords.old_sum s.paths _ hc]
  · have hh := ClosedWords.piece_charge s U₀ U₀_ge hcp hr hordinary
    exact_mod_cast hh
  · change ((Finset.univ.filter (fun p=>(a.closed _ hc hLl hd).comparisons.pairing.partner p=p)).card:ℝ)≤_
    rw [a.closed_fixed,Nat.cast_sum]
    exact ClosedWords.added_real s U₀ U₀_ge hLl hcp hd
  · exact a.closed_old _ hc hLl hd
  · exact a.sides_le _ hc heuler
  · exact ClosedWords.lower_word s U₀ U₀_ge hLl hcp hd hr
  · intro t ht hs
    have hh := ClosedWords.root_mass s U₀ hLl hcp hd hr hordinary t ht hs
    have hh' : 2*((ClosedWords.word s _ hc hLl hd t).length:ℝ)≤ClosedWords.H₀ s := by exact_mod_cast hh
    change ((ClosedWords.word s _ hc hLl hd t).length:ℝ)≤_
    linarith
  · exact oneStep
  · exact havoid
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

structure Data (inv : A → A) (label : Fin n → A) where
  partner : Equiv.Perm (Fin n)
  involutive : Function.Involutive partner
  distinct : ∀ i,partner i≠i
  compatible : ∀ i,label (partner i)=inv (label i)
  noncrossing : ∀ i j,i<j → j<partner i → partner i<partner j → False

namespace Ear
variable (k : ℕ)

variable {inv : A → A} {label : Fin n → A} (d : Data inv label)
end Ear
end

section
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Data
variable (d : Data inv label)
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

variable (d : Data inv label)

end TorsionFreeZeroDivisors.WordPairing.Ear

namespace TorsionFreeZeroDivisors.PermutationCycles
variable (O : Type) [Fintype O]
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.WordPairing

section
open PermutationCycles
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Ear
variable (k : ℕ) (hk : k≤n) (d : Data inv label)
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
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin (n+2)→A} (d : Data inv label) (k : ℕ) (hk : k≤n)
end TorsionFreeZeroDivisors.WordPairing.EraseEar
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
variable {A : Type*} {inv : A → A}
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
/-- Exact Euler lower bound used by the source interval estimate, extracted
from actual combinatorial genus zero. No connectivity is assumed: one actual
occurrence suffices to make the component count positive. -/
theorem euler_of_genusZero [Nonempty O] (hz : GenusZero σ α) (hf : ∀x,α x≠x) :
    Fintype.card O+4≤2*Fintype.card (Cycle σ)+2*Fintype.card (Cycle (α*σ)) := by
  let : Nonempty (Component σ α) := ⟨component σ α (Classical.choice inferInstance)⟩
  have hc : 0<Nat.card (Component σ α) := Nat.card_pos
  have he : α.support.card=Fintype.card O := by
    simp only [Equiv.Perm.support,hf,ne_eq,not_false_eq_true,Finset.filter_true,Finset.card_univ]
  dsimp only [GenusZero] at hz
  simp only [Nat.card_eq_fintype_card] at hz hc
  rw [he] at hz
  omega
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
variable (hlabel : ∀d,label (Γ.reverse d)=inv (label d))
  (himm : ∀d e,Γ.origin d=Γ.origin e → label d=label e → d=e)
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

namespace TorsionFreeZeroDivisors.CycleLists
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
def orbit (x : O) : List O := if f x=x then [x] else f.toList x
lemma mem_orbit {x y : O} : y∈orbit f x ↔ f.SameCycle x y := by
  by_cases hx : f x=x
  · simp only [orbit,if_pos hx,List.mem_singleton]
    exact ⟨fun h=>h.symm.sameCycle f,fun h=>(h.eq_of_left hx).symm⟩
  · rw [orbit,if_neg hx,Equiv.Perm.mem_toList_iff]
    exact and_iff_left (Equiv.Perm.mem_support.mpr hx)
lemma orbit_nonempty (x : O) : orbit f x≠[] :=
  List.ne_nil_of_mem ((mem_orbit f).mpr (Equiv.Perm.SameCycle.refl f x))
lemma orbit_nodup (x : O) : (orbit f x).Nodup := by
  by_cases hx : f x=x
  · simp only [orbit,if_pos hx,List.nodup_singleton]
  · rw [orbit,if_neg hx]
    exact f.nodup_toList x
lemma orbit_next {x y : O} (hy : y∈orbit f x) : (orbit f x).next y hy=f y := by
  by_cases hx : f x=x
  · have he : y=x := by simpa only [orbit,if_pos hx,List.mem_singleton] using hy
    subst y
    simp [orbit,hx]
  · simpa only [orbit,if_neg hx] using f.next_toList_eq_apply x y
      (by simpa only [orbit,if_neg hx] using hy)
lemma orbit_rotate (x : O) (i : Fin (orbit f x).length) :
    (orbit f x)[(finRotate (orbit f x).length i).val]=f ((orbit f x)[i.val]) := by
  have h := orbit_next f (List.getElem_mem i.isLt)
  rw [List.next_getElem _ (orbit_nodup f x)] at h
  have hv : (finRotate (orbit f x).length i).val=(i.val+1)%(orbit f x).length := by
    let _ := i.neZero
    rw [finRotate_apply,Fin.val_add,Fin.val_one',Nat.add_mod_mod]
  simpa only [hv] using h
lemma orbit_succ (x : O) (i : ℕ) (hi : i+1<(orbit f x).length) :
    f ((orbit f x)[i])=(orbit f x)[i+1] := by
  have h := orbit_next f (List.getElem_mem (by omega : i<(orbit f x).length))
  rw [List.next_getElem _ (orbit_nodup f x)] at h
  simpa only [Nat.mod_eq_of_lt hi] using h.symm
lemma orbit_last (x : O) :
    f ((orbit f x).getLast (orbit_nonempty f x))=(orbit f x).head (orbit_nonempty f x) := by
  exact (orbit_next f (List.getLast_mem (orbit_nonempty f x))).symm.trans
    (List.next_getLast_eq_head (orbit f x) (orbit_nonempty f x) (orbit_nodup f x))
variable (rep : Cycle f→O) (hrep : ∀c,cycle f (rep c)=c)
def words (c : Cycle f) : List O := orbit f (rep c)
def atIndex (p : Σc : Cycle f,Fin (words f rep c).length) : O := (words f rep p.1)[p.2.val]
include hrep in
lemma atIndex_cycle (p : Σc : Cycle f,Fin (words f rep c).length) :
    cycle f (atIndex f rep p)=p.1 := by
  have hm : atIndex f rep p∈orbit f (rep p.1) := List.getElem_mem p.2.isLt
  exact ((cycle_eq f).mpr ((mem_orbit f).mp hm)).symm.trans (hrep p.1)
include hrep in
lemma atIndex_bijective : Function.Bijective (atIndex f rep) := by
  constructor
  · rintro ⟨c,i⟩ ⟨d,j⟩ he
    have hd : c=d := (atIndex_cycle f rep hrep ⟨c,i⟩).symm.trans
      ((congrArg (cycle f) he).trans (atIndex_cycle f rep hrep ⟨d,j⟩))
    subst d
    have hi : i=j := (List.nodup_iff_injective_getElem.mp (orbit_nodup f (rep c))) he
    subst j
    rfl
  · intro x
    let c := cycle f x
    have hx : x∈words f rep c := (mem_orbit f).mpr ((cycle_eq f).mp (hrep c))
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
    exact ⟨⟨c,⟨i,hi⟩⟩,he⟩
def coordinates : (Σc : Cycle f,Fin (words f rep c).length)≃O :=
  Equiv.ofBijective (atIndex f rep) (atIndex_bijective f rep hrep)
end TorsionFreeZeroDivisors.CycleLists

namespace TorsionFreeZeroDivisors.FinitePicture.Data
open scoped Classical
open PermutationCycles CycleLists
variable {V D A O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D} {label : D→A} {inv : A→A} {x y : V} (hxy : x≠y)
end TorsionFreeZeroDivisors.FinitePicture.Data

namespace TorsionFreeZeroDivisors.ComparedBlocks.Comparisons
open scoped Classical
open BlockAlignment
def empty {T : Type} (len : T→ℕ) : Comparisons (E:=Empty) len where
  pairing := ⟨id,fun _=>rfl⟩
  side := fun _=>none
  flip := Empty.elim
  flip_inv := fun e=>Empty.elim e
  flip_ne := fun e=>Empty.elim e
  side_partner := fun _ e=>Empty.elim e
  none_iff := fun _=>⟨fun _=>rfl,fun _=>rfl⟩
  source := Empty.elim
  lo := Empty.elim
  hi := Empty.elim
  reverse := Empty.elim
  offset := Empty.elim
  side_iff := fun _ e=>Empty.elim e
  partner_source := fun _ e=>Empty.elim e
  partner_coordinate := fun _ e=>Empty.elim e
  target_range := fun e=>Empty.elim e
end TorsionFreeZeroDivisors.ComparedBlocks.Comparisons
namespace TorsionFreeZeroDivisors.SampleGraph.Picture
open scoped Classical
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep} {z w : VA rep⊕VB rep} {O : Type} [Fintype O] (hzw : z≠w) (hz : z=Sum.inl x ∨ z=Sum.inr y)

end TorsionFreeZeroDivisors.SampleGraph.Picture

end

end OAI
end

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
variable {A : Type*} {ns : List ℕ} {inv : A→A} {label : Fin ns.sum→A}

end TorsionFreeZeroDivisors.BlockBoundary
/-! Algebraic disk-picture certificates. The relator words are retained literally,
not replaced by their reduced representatives. Connector words may be arbitrary.
No planar-surface realization or minimal-band theorem is assumed here. -/
namespace TorsionFreeZeroDivisors.AlgebraicPictures
open FreeGroup
variable {A I : Type*} (rel : I → List (A×Bool))

namespace Term
end Term

variable (outer : List (A×Bool))

end TorsionFreeZeroDivisors.AlgebraicPictures

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
/-- Performing literal vertex cuts in one boundary fiber performs the same
cuts in the whole occurrence set, leaving every other fiber unchanged. -/
lemma fiber {i : I} {σ τ : Equiv.Perm (O i)} (h : Cuts σ τ)
    (ρ : ∀j,Equiv.Perm (O j)) :
    Cuts (Equiv.sigmaCongrRight (Function.update ρ i σ))
      (Equiv.sigmaCongrRight (Function.update ρ i τ)) := by
  induction h with
  | refl=>exact .refl _
  | step σ p q hn hc=>
    have he : Equiv.sigmaCongrRight (Function.update ρ i (Equiv.swap p q*σ))=
        Equiv.swap (Sigma.mk i p) (Sigma.mk i q)*
          Equiv.sigmaCongrRight (Function.update ρ i σ) := by
      apply Equiv.ext
      rintro ⟨j,x⟩
      by_cases hj : j=i
      · subst j
        simp only [Equiv.sigmaCongrRight_apply,Function.update_self,Equiv.Perm.mul_apply]
        by_cases hp : σ x=p
        · rw [hp];simp
        · by_cases hq : σ x=q
          · rw [hq];simp
          · simp [Equiv.swap_apply_def,hp,hq]
      · have h₁ : (⟨j,ρ j x⟩ : Sigma O)≠⟨i,p⟩ := fun he=>hj (congrArg Sigma.fst he)
        have h₂ : (⟨j,ρ j x⟩ : Sigma O)≠⟨i,q⟩ := fun he=>hj (congrArg Sigma.fst he)
        simp only [Equiv.sigmaCongrRight_apply,Function.update_of_ne hj,
          Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne h₁ h₂]
    rw [he]
    have hh := Cuts.step (Equiv.sigmaCongrRight (Function.update ρ i σ))
      (Sigma.mk i p) (Sigma.mk i q)
      (fun he=>hn (eq_of_heq (Sigma.mk.inj_iff.mp he).2))
      (mapped_sameCycle (Sigma.mk i) σ (Equiv.sigmaCongrRight (Function.update ρ i σ))
        (fun x=>by simp) hc)
    convert hh using 1
    apply Equiv.ext
    intro x
    simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_def]
    split_ifs <;> rfl
  | trans h h' ih ih'=>exact ih.trans ih'
variable [Fintype I]
/-- All of a finite family's contiguous boundary refinements may be carried
out simultaneously, with the matching on the whole occurrence set retained. -/
lemma sigma {σ τ : ∀i,Equiv.Perm (O i)} (h : ∀i,Cuts (σ i) (τ i)) :
    Cuts (Equiv.sigmaCongrRight σ) (Equiv.sigmaCongrRight τ) := by
  let mix (s : Finset I) (i : I) := if i∈s then τ i else σ i
  have hm : ∀s : Finset I,Cuts (Equiv.sigmaCongrRight σ) (Equiv.sigmaCongrRight (mix s)) := by
    intro s
    induction s using Finset.induction_on with
    | empty=>simpa only [mix,Finset.notMem_empty,ite_false] using (Cuts.refl (Equiv.sigmaCongrRight σ))
    | @insert i s hi ih=>
      have h₁ : Function.update (mix s) i (σ i)=mix s := by
        apply funext
        intro j
        by_cases hj : j=i
        · subst j;simp [mix,hi]
        · simp [Function.update_of_ne hj]
      have h₂ : Function.update (mix s) i (τ i)=mix (insert i s) := by
        apply funext
        intro j
        by_cases hj : j=i
        · subst j;simp [mix]
        · simp [mix,hj]
      have hh := fiber (h i) (mix s)
      rw [h₁,h₂] at hh
      exact ih.trans hh
  simpa only [mix,Finset.mem_univ,ite_true] using hm Finset.univ

end

open scoped Classical BigOperators
lemma finCongr_rotate {n m : ℕ} (h : n=m) :
    (finCongr h).permCongr (finRotate n)=finRotate m := by
  subst m
  rfl
lemma sigmaCongrLeft_rotation {I J : Type} {O : J→Type} (e : I≃J)
    (σ : ∀j,Equiv.Perm (O j)) :
    (e.sigmaCongrLeft).permCongr (Equiv.sigmaCongrRight fun i=>σ (e i))=
      Equiv.sigmaCongrRight σ := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,j⟩,rfl⟩ := e.sigmaCongrLeft.surjective x
  simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  rfl
lemma sumSigma_rotation {I J : Type} {O : I⊕J→Type}
    (σ : ∀j,Equiv.Perm (O j)) :
    (Equiv.sumSigmaDistrib O).permCongr (Equiv.sigmaCongrRight σ)=
      Equiv.sumCongr (Equiv.sigmaCongrRight fun i=>σ (Sum.inl i))
        (Equiv.sigmaCongrRight fun j=>σ (Sum.inr j)) := by
  apply Equiv.ext
  rintro (⟨i,x⟩|⟨j,x⟩) <;> rfl
/-- The pinned `finSigmaFinEquiv` is the literal consecutive sum indexing;
cutting exactly at its fiber boundaries preserves the entire matching. -/
lemma fin_refinement {m : ℕ} (n : Fin m→ℕ) :
    Cuts (finSigmaFinEquiv.symm.permCongr (finRotate (∑i,n i)))
      (Equiv.sigmaCongrRight fun i=>finRotate (n i)) := by
  induction m with
  | zero=>
    have he : finSigmaFinEquiv.symm.permCongr (finRotate (∑i,n i))=
        Equiv.sigmaCongrRight (fun i=>finRotate (n i)) := by
      apply Equiv.ext
      rintro ⟨i,j⟩
      exact i.elim0
    rw [he]
    exact .refl _
  | succ m ih=>
    let L : Fin m→ℕ := fun i=>n i.castSucc
    let R : Fin 1→ℕ := fun i=>n (Fin.natAdd m i)
    let e₁ : ((i : Fin m⊕Fin 1) × Fin (n (finSumFinEquiv i)))≃((i : Fin (m+1)) × Fin (n i)) :=
      Equiv.sigmaCongrLeft (β:=fun i=>Fin (n i)) (@finSumFinEquiv m 1)
    let e₂ := Equiv.sumSigmaDistrib (fun i : Fin m⊕Fin 1=>Fin (n (finSumFinEquiv i)))
    let e₃ : (((i : Fin m) × Fin (L i))⊕((i : Fin 1) × Fin (R i)))≃
      (Fin (∑i,L i)⊕Fin (n (Fin.last m))) :=
      Equiv.sumCongr finSigmaFinEquiv (Equiv.uniqueSigma _)
    let e : (((i : Fin m) × Fin (L i))⊕((i : Fin 1) × Fin (R i)))≃
      ((i : Fin (m+1)) × Fin (n i)) := e₂.symm.trans e₁
    have hh := conjugate (BlockBoundary.fin_cut (∑i,L i) (n (Fin.last m))) e₃.symm
    have he₁ : e₃.symm.permCongr
        (finSumFinEquiv.symm.permCongr (finRotate ((∑i,L i)+n (Fin.last m))))=
        e.symm.permCongr (finSigmaFinEquiv.symm.permCongr (finRotate (∑i,n i))) := by
      have hf : (finSigmaFinEquiv : ((i : Fin (m+1)) × Fin (n i))≃Fin (∑i,n i))=
          e.symm.trans (e₃.trans (finSumFinEquiv.trans (finCongr (Fin.sum_univ_castSucc n).symm))) := rfl
      rw [hf]
      have hc := finCongr_rotate (Fin.sum_univ_castSucc n)
      apply Equiv.ext
      intro x
      have hc' := congrArg (fun f=>f (finSumFinEquiv (e₃ x))) hc
      simp only [Equiv.permCongr_apply] at hc'
      simp only [Equiv.permCongr_apply,Equiv.trans_apply,Equiv.symm_trans_apply,
        Equiv.symm_symm,Equiv.symm_apply_apply]
      congr 2
      exact hc'.symm
    have he₂ : e₃.symm.permCongr (Equiv.sumCongr (finRotate (∑i,L i)) (finRotate (n (Fin.last m))))=
        Equiv.sumCongr (finSigmaFinEquiv.symm.permCongr (finRotate (∑i,L i)))
          (Equiv.sigmaCongrRight fun i=>finRotate (R i)) := by
      apply Equiv.ext
      rintro (x|x)
      · rfl
      · rcases x with ⟨i,j⟩
        have hi : i=default := Subsingleton.elim _ _
        subst i
        rfl
    rw [he₁,he₂] at hh
    have hl := hh.trans (left (ih L) (Equiv.sigmaCongrRight fun i=>finRotate (R i)))
    have ht := conjugate hl e
    have he₃ : e.permCongr (Equiv.sumCongr (Equiv.sigmaCongrRight fun i=>finRotate (L i))
        (Equiv.sigmaCongrRight fun i=>finRotate (R i)))=
        Equiv.sigmaCongrRight fun i=>finRotate (n i) := by
      have hd := sumSigma_rotation (fun i : Fin m⊕Fin 1=>finRotate (n (finSumFinEquiv i)))
      change e₂.permCongr (Equiv.sigmaCongrRight fun i=>finRotate (n (finSumFinEquiv i)))=
        Equiv.sumCongr (Equiv.sigmaCongrRight fun i=>finRotate (L i))
          (Equiv.sigmaCongrRight fun i=>finRotate (R i)) at hd
      rw [←hd]
      change e₁.permCongr (e₂.symm.permCongr (e₂.permCongr _))=_
      rw [←Equiv.permCongr_symm,Equiv.symm_apply_apply]
      exact sigmaCongrLeft_rotation (O:=fun i=>Fin (n i)) (@finSumFinEquiv m 1) (fun i=>finRotate (n i))
    simpa only [←Equiv.permCongr_symm,Equiv.apply_symm_apply,he₃] using ht

lemma fin_index_refinement {m h : ℕ} (n : Fin m→ℕ) (hs : (∑i,n i)=h) :
    Cuts ((finSigmaFinEquiv.trans (finCongr hs)).symm.permCongr (finRotate h))
      (Equiv.sigmaCongrRight fun i=>finRotate (n i)) := by
  have hc := finCongr_rotate hs.symm
  have he : (finSigmaFinEquiv.trans (finCongr hs)).symm.permCongr (finRotate h)=
      finSigmaFinEquiv.symm.permCongr (finRotate (∑i,n i)) := by
    change finSigmaFinEquiv.symm.permCongr ((finCongr hs).symm.permCongr (finRotate h))=_
    rw [show (finCongr hs).symm=finCongr hs.symm from rfl,hc]
  rw [he]
  exact fin_refinement n
end TorsionFreeZeroDivisors.BoundaryRefinement
namespace TorsionFreeZeroDivisors.BalancedGenus
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions BoundaryRefinement
variable {T A : Type} [Fintype T] (w : T→List A) (cap : ℕ) (hc : 0<cap)
lemma join_refinement : Cuts
    ((WordPositions.join w cap hc).symm.permCongr (BoundaryRotation.perm fun t=>(w t).length))
    (BoundaryRotation.perm (BalancedWords.old w cap)) := by
  let N (t : T) := BalancedPieces.number (w t).length cap
  let n (t : T) : Fin (N t)→ℕ := BalancedPieces.sizes (w t).length cap
  let idx (t : T) := ConsecutivePieces.index (w t) (n t) (BalancedPieces.sizes_sum hc)
  have hh : ∀ t,Cuts ((idx t).symm.permCongr (finRotate (w t).length))
      (Equiv.sigmaCongrRight fun i=>finRotate (n t i)) :=
    fun t=>fin_index_refinement (n t) (BalancedPieces.sizes_sum hc)
  let e : ((t : T) × (i : Fin (N t)) × Fin (n t i))≃Position (BalancedWords.old w cap) :=
    (Equiv.sigmaAssoc fun t i=>Fin (n t i)).symm.trans (fin _).symm
  have ht := conjugate (sigma hh) e
  have he₁ : e.permCongr (Equiv.sigmaCongrRight fun t=>(idx t).symm.permCongr (finRotate (w t).length))=
      (WordPositions.join w cap hc).symm.permCongr (BoundaryRotation.perm fun t=>(w t).length) := by
    apply Equiv.ext
    intro p
    simp only [e,WordPositions.join,WordPositions.joinFin,BoundaryRotation.perm,
      Equiv.permCongr_apply,Equiv.trans_apply,Equiv.symm_trans_apply,
      Equiv.symm_symm]
    rfl
  have he₂ : e.permCongr (Equiv.sigmaCongrRight fun t=>Equiv.sigmaCongrRight fun i=>finRotate (n t i))=
      BoundaryRotation.perm (BalancedWords.old w cap) := by
    apply Equiv.ext
    intro p
    simp only [e,BoundaryRotation.perm,Equiv.permCongr_apply,Equiv.symm_symm]
    rfl
  rwa [he₁,he₂] at ht
lemma position_refinement {T : Type} {l k : T→ℕ} (h : ∀t,l t=k t) :
    (ComparisonGeometry.position (Equiv.refl T) h).permCongr (BoundaryRotation.perm l)=
      BoundaryRotation.perm k := by
  have he : l=k := funext h
  subst k
  rfl
lemma refinement : Cuts (BalancedRotation.perm w cap hc)
    (BoundaryRotation.perm (BalancedRotation.len w cap hc)) := by
  let g := ComparisonGeometry.position (Equiv.refl _) (BalancedWords.segment_length w cap hc)
  have ht := conjugate (join_refinement w cap hc) g.symm
  have hr := position_refinement (BalancedWords.segment_length w cap hc)
  change g.permCongr (BoundaryRotation.perm (BalancedRotation.len w cap hc))=
    BoundaryRotation.perm (BalancedWords.old w cap) at hr
  rw [←hr,←Equiv.permCongr_symm,Equiv.symm_apply_apply] at ht
  exact ht
lemma genusZero (α : Equiv.Perm (Position fun t=>(w t).length))
    (hi : Function.Involutive α) (hz : MapEuler.GenusZero
      (BoundaryRotation.perm fun t=>(w t).length) α) :
    MapEuler.GenusZero (BoundaryRotation.perm (BalancedRotation.len w cap hc))
      ((BalancedRotation.e w cap hc).symm.permCongr α) :=
  preserves (refinement w cap hc) _ (PermutationTransport.involutive _ _ hi)
    (MapConjugation.genusZero (BalancedRotation.e w cap hc).symm _ _ hz)

end TorsionFreeZeroDivisors.BalancedGenus
namespace TorsionFreeZeroDivisors.ExtendComparisons
open scoped Classical
open BlockAlignment ComparedBlocks
variable {T E : Type} {len more : T→ℕ} (C : Comparisons (E:=E) len)
  (hle : ∀t,len t ≤ more t)
/-- Added closure letters are fixed; they introduce no interaction between
DIFFERENT boundary pieces. This statement does not discard self-loops silently. -/
lemma rel_iff {p q : T} (hpq : p≠q) :
    PairingClusters.Rel (fun x : Position more=>x.1) (partner C hle) p q ↔
      PairingClusters.Rel (fun x : Position len=>x.1) C.pairing.partner p q := by
  constructor
  · rintro ⟨x,hx,hy⟩
    by_cases ho : Old (len:=len) x
    · refine ⟨project x ho,hx,?_⟩
      simpa only [partner,dif_pos ho,embed] using hy
    · rw [partner_new C hle x ho] at hy
      exact False.elim (hpq (hx.symm.trans hy))
  · rintro ⟨x,hx,hy⟩
    refine ⟨embed hle x,hx,?_⟩
    rw [partner_embed]
    exact hy

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
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
  {s : PathSystem rep r x y} (a : FullPairing s) (cap : ℕ) (hc : 0<cap)
  (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
lemma closed_rel {p q : ClosedWords.Piece s cap} (hpq : p≠q) :
    PairingClusters.Rel (fun z : Position (fun t=>((a.closed cap hc hL hd).paths t).length)=>z.1)
      (a.closed cap hc hL hd).comparisons.pairing.partner p q ↔
    PairingClusters.Rel (fun z : Position (BalancedRotation.len s.paths cap hc)=>z.1)
      (a.α cap hc) p q := by
  exact ExtendComparisons.rel_iff (a.comparisons cap hc)
    (ClosedWords.grow s cap hc hL hd) hpq

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
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
  {s : PathSystem rep r x y} (a : FullPairing s) (cap : ℕ) (hc : 0<cap)
  (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
/-- Transfer the SAME separator sets/parts/cost to the actual short-closed
paths. In particular no extra charge for the appended tails is introduced. -/
def closed_split (d : DecidableEq (ClosedWords.Piece s cap)) (S : Finset (ClosedWords.Piece s cap))
    (P : @RecursiveSeparator.Split (ClosedWords.Piece s cap) d
      (PairingClusters.Rel (fun z : Position (BalancedRotation.len s.paths cap hc)=>z.1)
        (a.α cap hc)) S) :
    @RecursiveSeparator.Split (ClosedWords.Piece s cap) d
      (PairingClusters.Rel (fun z : Position (fun t=>((a.closed cap hc hL hd).paths t).length)=>z.1)
        (a.closed cap hc hL hd).comparisons.pairing.partner) S :=
  @RecursiveSeparator.Split.of_off_diagonal (ClosedWords.Piece s cap) d _ _ _
      (fun _ _ h=>(a.closed_rel cap hc hL hd h).symm) P

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

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} (σ α : Equiv.Perm O) (ha : Function.Involutive α)

variable [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)

end

open scoped Classical BigOperators
open PermutationCycles
variable {O : Type} (σ α : Equiv.Perm O) (ha : Function.Involutive α)

variable (T : SimpleGraph (Cycle σ))

variable [Fintype O]

end TorsionFreeZeroDivisors.MapEuler

end

end OAI
end

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

def boundaryRep (c : Cycle a.rotation) : O := Quotient.out c
lemma boundaryRep_cycle (c : Cycle a.rotation) : cycle a.rotation (a.boundaryRep c)=c := Quotient.out_eq c
def occurrences (c : Cycle a.rotation) : List O := orbit a.rotation (a.boundaryRep c)
def paths (c : Cycle a.rotation) : List D := (a.occurrences c).map a.dart
lemma occurrences_nonempty (c : Cycle a.rotation) : a.occurrences c≠[] := orbit_nonempty _ _
lemma paths_nonempty (c : Cycle a.rotation) : a.paths c≠[] := by
  intro he
  exact a.occurrences_nonempty c (List.map_eq_nil_iff.mp he)
lemma paths_length (c : Cycle a.rotation) : (a.paths c).length=(a.occurrences c).length := List.length_map _
lemma occurrences_succ (c : Cycle a.rotation) (i : ℕ) (hi : i+1<(a.occurrences c).length) :
    a.rotation ((a.occurrences c)[i])=(a.occurrences c)[i+1] := orbit_succ _ _ _ hi
lemma occurrences_last (c : Cycle a.rotation) :
    a.rotation ((a.occurrences c).getLast (a.occurrences_nonempty c))=
      (a.occurrences c).head (a.occurrences_nonempty c) := orbit_last _ _

variable (hr : a.Reduced)
include hr in
lemma paths_chain (c : Cycle a.rotation) : (a.paths c).IsChain
    (fun d e=>Γ.origin (Γ.reverse d)=Γ.origin e ∧ e≠Γ.reverse d) := by
  rw [paths,List.isChain_map,List.isChain_iff_getElem]
  intro i hi
  have hh := a.consistent ((a.occurrences c)[i])
  have hb := hr.2 ((a.occurrences c)[i])
  rw [a.occurrences_succ c i hi] at hh hb
  exact ⟨hh,hb⟩
include hr in
lemma paths_closed (c : Cycle a.rotation) :
    Γ.origin (Γ.reverse ((a.paths c).getLast (a.paths_nonempty c)))=
      Γ.origin ((a.paths c).head (a.paths_nonempty c)) ∧
    (a.paths c).head (a.paths_nonempty c)≠Γ.reverse ((a.paths c).getLast (a.paths_nonempty c)) := by
  have hh := a.consistent ((a.occurrences c).getLast (a.occurrences_nonempty c))
  have hb := hr.2 ((a.occurrences c).getLast (a.occurrences_nonempty c))
  rw [a.occurrences_last c] at hh hb
  simpa only [paths,List.head_map,List.getLast_map] using And.intro hh hb

def pathCoordinates : (Σc : Cycle a.rotation,Fin (a.paths c).length)≃O :=
  (Equiv.sigmaCongrRight fun c=>finCongr (a.paths_length c)).trans
    (coordinates a.rotation a.boundaryRep a.boundaryRep_cycle)
lemma pathCoordinates_apply (p : Σc : Cycle a.rotation,Fin (a.paths c).length) :
    a.pathCoordinates p=(a.occurrences p.1)[p.2.val]'(by simpa only [a.paths_length] using p.2.isLt) := rfl
lemma paths_dart (p : Σc : Cycle a.rotation,Fin (a.paths c).length) :
    (a.paths p.1)[p.2.val]=a.dart (a.pathCoordinates p) := by
  rw [a.pathCoordinates_apply p]
  exact List.getElem_map _
lemma pathCoordinates_rotate (c : Cycle a.rotation) (i : Fin (a.paths c).length) :
    a.pathCoordinates ⟨c,finRotate (a.paths c).length i⟩=a.rotation (a.pathCoordinates ⟨c,i⟩) := by
  simp only [pathCoordinates_apply]
  have hh := orbit_rotate a.rotation (a.boundaryRep c) (finCongr (a.paths_length c) i)
  have commute : ∀{m n : ℕ}(h : m=n)(i : Fin m),finCongr h (finRotate m i)=finRotate n (finCongr h i) := by
    intro m n h i;subst n;rfl
  exact (congrArg (fun j : Fin (a.occurrences c).length=>(a.occurrences c)[j.val])
    (commute (a.paths_length c) i)).trans hh
end Data
end TorsionFreeZeroDivisors.SphericalPicture

namespace TorsionFreeZeroDivisors.SampleGraph.SpherePicture
open scoped Classical
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep}
  {O : Type} [Fintype O]
  (a : SphericalPicture.Data (O:=O) (graph rep r) (label rep) Types.inverse) (hr : a.Reduced)

def system : PathSystem rep r x y where
  P := Cycle a.rotation
  E := Empty
  paths := a.paths
  nonempty := a.paths_nonempty
  root := none
  path_chain := a.paths_chain hr
  cyclic_chain c _ := by
    intro d hd e he
    rw [List.getLast?_eq_some_getLast (a.paths_nonempty c)] at hd
    rw [Option.mem_some] at hd
    rw [List.head?_eq_some_head (a.paths_nonempty c)] at he
    rw [Option.mem_some] at he
    subst d
    subst e
    exact a.paths_closed hr c
  comparisons := Comparisons.empty _
  lower := Empty.elim
  upper := Empty.elim
  lower_eq := fun e=>Empty.elim e
  upper_eq := fun e=>Empty.elim e
  lower_le := fun e=>Empty.elim e
  upper_le := fun e=>Empty.elim e
  reduced := fun _ e=>Empty.elim e
  rootA q hq := by cases hq
  rootB q hq := by cases hq
  compatible := fun _ e=>Empty.elim e

def coordinates : Position (fun c=>(a.paths c).length)≃O :=
  (WordPositions.fin _).trans a.pathCoordinates
lemma dart (p : Position (fun c=>(a.paths c).length)) :
    RawDecomposition.dart a.paths p=a.dart (coordinates a p) := by
  rw [←(WordPositions.fin _).symm_apply_apply p,WordPositions.dart_fin]
  exact a.paths_dart _
lemma rotation (p : Position (fun c=>(a.paths c).length)) :
    coordinates a (BoundaryRotation.perm (fun c=>(a.paths c).length) p)=a.rotation (coordinates a p) := by
  generalize he : (WordPositions.fin (fun c=>(a.paths c).length)) p=q
  have hp : p=(WordPositions.fin _).symm q := by rw [←he,Equiv.symm_apply_apply]
  rw [hp]
  rcases q with ⟨c,i⟩
  rw [BoundaryRotation.apply_fin]
  simp only [coordinates,Equiv.trans_apply,Equiv.apply_symm_apply]
  exact a.pathCoordinates_rotate c i
lemma rotation_conjugate : BoundaryRotation.perm (fun c=>(a.paths c).length)=
    (coordinates a).symm.permCongr a.rotation := by
  apply Equiv.ext
  intro p
  apply (coordinates a).injective
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  exact rotation a p
lemma partner_compatible (p : Position (fun c=>(a.paths c).length)) :
    label rep (RawDecomposition.dart a.paths ((coordinates a).symm.permCongr a.partner p))=
      Types.inverse (label rep (RawDecomposition.dart a.paths p)) := by
  rw [dart,dart]
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  exact a.compatible _
include hr in
lemma partner_reduced (p : Position (fun c=>(a.paths c).length)) :
    RawDecomposition.dart a.paths p≠RawDecomposition.dart a.paths ((coordinates a).symm.permCongr a.partner p) ∧
    RawDecomposition.dart a.paths p≠(graph rep r).reverse
      (RawDecomposition.dart a.paths ((coordinates a).symm.permCongr a.partner p)) := by
  rw [dart,dart]
  simp only [Equiv.permCongr_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  constructor
  · intro he
    have hh := a.compatible (coordinates a p)
    rw [←he] at hh
    exact Types.inverse_ne _ hh.symm
  · intro he
    apply hr.1 (coordinates a p)
    have hh := congrArg (graph rep r).reverse he
    rw [(graph rep r).reverse_reverse] at hh
    exact hh.symm

def pairing : FullPairing (system (x:=x) (y:=y) a hr) where
  perm := (coordinates a).symm.permCongr a.partner
  involutive := PermutationTransport.involutive _ _ a.involutive
  fixed_free := PermutationTransport.fixed_free _ _ a.fixed_free
  compatible p := partner_compatible a p
  reduced p := partner_reduced a hr p
lemma pairing_genusZero : MapEuler.GenusZero
    (BoundaryRotation.perm (fun c=>(a.paths c).length)) (pairing (x:=x) (y:=y) a hr).perm := by
  change MapEuler.GenusZero (BoundaryRotation.perm (fun c=>(a.paths c).length))
    ((coordinates a).symm.permCongr a.partner)
  rw [rotation_conjugate]
  exact MapConjugation.genusZero (coordinates a).symm _ _ a.genusZero
lemma pairing_euler [Nonempty O] : (pairing (x:=x) (y:=y) a hr).Euler := by
  let : Nonempty (Position (fun c=>((system (x:=x) (y:=y) a hr).paths c).length)) :=
    ⟨(coordinates a).symm (Classical.choice inferInstance)⟩
  exact MapEuler.euler_of_genusZero _ _ (pairing_genusZero a hr) (pairing a hr).fixed_free
lemma system_ordinary [Nonempty O] : ∃c,(system (x:=x) (y:=y) a hr).root≠some c :=
  ⟨cycle a.rotation (Classical.choice inferInstance),by intro h;cases h⟩

/-- Unconditional sharp split for the prepared all-cyclic spherical system. -/
lemma separator (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
    (S : Finset ((pairing (x:=x) (y:=y) a hr).prepared hL hd).P) :
    Nonempty (RecursiveSeparator.Split (PairingClusters.Rel
      (fun p : Position (fun t=>(((pairing a hr).prepared hL hd).paths t).length)=>p.1)
      ((pairing a hr).prepared hL hd).comparisons.pairing.partner) S) := by
  let s := system (x:=x) (y:=y) a hr
  let cap := FullPairing.U₀*GirthAsymptotics.L (TypedGraphs.size rep)
  let hc : 0<cap := FullPairing.cap_positive hL
  have hp : ∀p,0<BalancedRotation.len s.paths cap hc p := fun p=>
    List.length_pos_iff.mpr (BalancedWords.segment_nonempty s.paths cap hc s.nonempty p)
  have hz := BalancedGenus.genusZero s.paths cap hc (pairing a hr).perm
    (pairing a hr).involutive (pairing_genusZero a hr)
  obtain ⟨P⟩ := BoundaryRotation.split (BalancedRotation.len s.paths cap hc) hp
    ((pairing a hr).α cap hc) ((pairing a hr).α_involutive cap hc) hz S
  exact ⟨(pairing a hr).closed_split cap hc (by omega) hd _ S P⟩

include a hr in
/-- There is no NONEMPTY reduced spherical boundary certificate in the sample. -/
theorem excluded_dev [Nonempty O] (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep))
    (hd : GraphSample.Diameters rep r) (hsample : r∈ActualPatternEvent.samples rep)
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
      (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y)) :
    False :=
  FullPairing.excluded (pairing a hr) hL hd hsample (system_ordinary a hr) (pairing_euler a hr)
    (fun S _=>separator a hr hL hd S) havoid
end TorsionFreeZeroDivisors.SampleGraph.SpherePicture

namespace TorsionFreeZeroDivisors.SphericalPicture
open scoped Classical
variable {V D A : Type} (Γ : PortSubdivision.PortGraph V D) (label : D→A) (inv : A→A)
variable {Γ label inv}
namespace Data
variable {O : Type} [Fintype O] (p q : O) (hpq : p≠q)
end Data
end TorsionFreeZeroDivisors.SphericalPicture
namespace TorsionFreeZeroDivisors.SampleGraph.SpherePicture
open scoped Classical
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep}
end TorsionFreeZeroDivisors.SampleGraph.SpherePicture

namespace TorsionFreeZeroDivisors.ConePicture
open PortSubdivision GraphPresentation SphericalPicture
open scoped Classical
variable {V D A : Type} (Γ : PortGraph V D) (R : Routes Γ)
variable (label : D→A) (inv : A→A)
variable {Γ R label inv} {O : Type} [Fintype O]
variable (hi : Function.Involutive inv) (hl : ∀d,label (Γ.reverse d)=inv (label d))
end TorsionFreeZeroDivisors.ConePicture

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
open OAI.TorsionFreeZeroDivisors OAI.TorsionFreeZeroDivisors.SampleGraph OAI.TorsionFreeZeroDivisors.SampleGraph.SpherePicture in
theorem solution {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep}
    {O : Type} [Fintype O]
    (a : SphericalPicture.Data (O:=O) (graph rep r) (label rep) Types.inverse) (hr : a.Reduced)
    [Nonempty O] (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep))
    (hd : GraphSample.Diameters rep r) (hsample : r∈ActualPatternEvent.samples rep)
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
      (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y)) :
    False :=
  OAI.TorsionFreeZeroDivisors.SampleGraph.SpherePicture.excluded_dev a hr hL hd hsample havoid
