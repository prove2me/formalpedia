-- Prove2me | solution 1 for OAI.Erdos3.no_interval_invariant_of_descent_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:50:42.681588+00:00
-- url     : https://prove2.me/submissions/81ce79f2-07eb-4788-99d4-bff98a190380

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B035
import Definitions.Def_OAIE3v2B117

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReplacementCellPotential
namespace OAI

section

namespace Erdos3

theorem no_invariant_of_descent {S : Type*} (P : S → Prop) (potential : S → ℝ)
    (T : ℝ)
    (h_nonneg : ∀ x, P x → 0 ≤ potential x)
    (h_terminal : ∀ x, P x → potential x ≤ T → False)
    (h_step : ∀ x, P x → T < potential x →
      ∃ y, P y ∧ potential y + 1 ≤ potential x) :
    ∀ x, ¬ P x := by
  have h : ∀ n : ℕ, ∀ x, ⌊potential x⌋₊ = n → ¬ P x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx hPx
      have hlarge : T < potential x := lt_of_not_ge (h_terminal x hPx)
      obtain ⟨y, hPy, hdec⟩ := h_step x hPx hlarge
      have hfloor := Nat.floor_mono hdec
      rw [Nat.floor_add_one (h_nonneg y hPy), hx] at hfloor
      exact ih ⌊potential y⌋₊ (by omega) y rfl hPy
  intro x
  exact h _ x rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Energy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem mean_finsetIndicator {α : Type*}
    [Fintype α] [DecidableEq α] (A : Finset α) :
    mean (finsetIndicator A) =
      (A.card : ℝ) / Fintype.card α := by
  rw [mean, Fintype.expect_eq_sum_div_card]
  simp [finsetIndicator]

theorem mean₂_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean₂ f = mean₂ (fun y x => f x y) := by
  exact Finset.expect_comm Finset.univ Finset.univ f

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem cyclicAPProduct_nonneg {k N : ℕ} {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a d : ZMod N) :
    0 ≤ cyclicAPProduct k N f a d := by
  exact Finset.prod_nonneg fun j _ => hf (cyclicAPTerm a d j)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem mean_finset_sum {α κ : Type*}
    [Fintype α]
    (s : Finset κ) (f : κ → α → ℝ) :
    mean (fun x => ∑ q ∈ s, f q x) =
      ∑ q ∈ s, mean (f q) := by
  simpa [mean] using
    (Finset.expect_sum_comm
      (s := (Finset.univ : Finset α)) s
      (fun x q => f q x))

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem mean_prod_type
    {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℝ) :
    mean (fun p : α × β => F p.1 p.2) = mean₂ F := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) F)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem conditionalMean_nonneg {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Ω) :
    0 ≤ conditionalMean P f x := by
  exact Finset.expect_nonneg fun y _ => hf y

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

namespace FacePartition

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem representative_mem
    (P : FacePartition Ω) (a : P.parts) :
    P.representative a ∈ a.1 :=
  Classical.choose_spec (P.nonempty_of_mem_parts a.2)

end FacePartition

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BundleCountingRecurrence
namespace OAI

section

namespace Erdos3.FixedDensity

theorem mean_mul_sq_le_product
    {Ω : Type*} [Fintype Ω]
    (u v : Ω → ℝ) :
    mean (fun x => u x * v x) ^ 2 ≤
      mean (fun x => u x ^ 2) *
        mean (fun x => v x ^ 2) := by
  simpa [mean] using
    (Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) u v)

theorem mean_sq_eq_mean_pair_mul
    {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    mean f ^ 2 =
      mean (fun p : Ω × Ω => f p.1 * f p.2) := by
  calc
    mean f ^ 2 = mean f * mean f := pow_two _
    _ = mean₂ (fun x y => f x * f y) := by
      unfold mean₂ mean
      exact
        Finset.expect_mul_expect
          Finset.univ Finset.univ f f
    _ = mean (fun p : Ω × Ω => f p.1 * f p.2) :=
      (mean_prod_type fun x y => f x * f y).symm

theorem mean_inner_sq_eq_mean₂_pair
    {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℝ) :
    mean (fun x => mean (F x) ^ 2) =
      mean₂ (fun x => fun p : Y × Y =>
        F x p.1 * F x p.2) := by
  unfold mean₂
  apply congrArg mean
  funext x
  exact mean_sq_eq_mean_pair_mul (F x)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

theorem edge_card_le_order
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    g.card ≤ B.order := by
  exact Finset.le_sup hg

theorem eraseEdge_order_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).order ≤ B.order := by
  unfold order eraseEdge
  apply Finset.sup_le
  intro g hg
  exact B.edge_card_le_order (Finset.mem_of_mem_erase hg)

theorem eraseEdge_closed_of_maximal
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (_hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card) :
    (B.eraseEdge g₀).IsClosedUnderInclusion := by
  intro g hg f hfg
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have hfB : f ∈ B.edges :=
    hclosed hgB hfg
  apply Finset.mem_erase.mpr
  refine ⟨?_, hfB⟩
  intro hfg₀
  subst f
  have hcard₂ : g.card ≤ g₀.card :=
    hmax g hgB
  have heq : g₀ = g :=
    Finset.eq_of_subset_of_card_le hfg hcard₂
  exact (Finset.mem_erase.mp hg).1 heq.symm

theorem pullbackBaseEdgeWeight_unitInterval
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    0 ≤ B.pullbackBaseEdgeWeight A g y ∧
      B.pullbackBaseEdgeWeight A g y ≤ 1 := by
  rw [B.pullbackBaseEdgeWeight_of_mem A hg y]
  exact hA _ (B.projection_mem_base g hg) _

theorem pullbackBaseEdgeWeight_weightsInUnitInterval
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A) :
    B.WeightsInUnitInterval
      (B.pullbackBaseEdgeWeight A) := by
  intro g hg y
  exact B.pullbackBaseEdgeWeight_unitInterval A hA hg y

theorem bundleProduct_nonneg
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (x : K → G) :
    0 ≤ B.bundleProduct A x := by
  unfold bundleProduct
  exact Finset.prod_nonneg fun g hg =>
    (hA g hg (edgeTuple g x)).1

theorem bundleCount_nonneg
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A) :
    0 ≤ B.bundleCount A :=
  mean_nonneg (B.bundleProduct_nonneg hA)

theorem bundleCount_eq_edgeContribution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges) :
    B.bundleCount A =
      B.edgeContribution g₀ (A g₀) A := by
  unfold bundleCount edgeContribution edgeRemainder
  apply congrArg mean
  funext x
  exact
    (Finset.mul_prod_erase B.edges
      (fun g => A g (edgeTuple g x)) hg₀).symm

theorem bundleCount_decompose_edge
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (p : ℝ)
    (b c : ({v : K // v ∈ g₀} → G) → ℝ)
    (hdecomp : ∀ y, A g₀ y = p + b y + c y) :
    B.bundleCount A =
      p * (B.eraseEdge g₀).bundleCount A +
        B.edgeContribution g₀ b A +
        B.edgeContribution g₀ c A := by
  rw [B.bundleCount_eq_edgeContribution A hg₀]
  unfold edgeContribution bundleCount
  calc
    mean (fun x : K → G =>
        A g₀ (edgeTuple g₀ x) *
          B.edgeRemainder g₀ A x) =
        mean (fun x : K → G =>
          p * B.edgeRemainder g₀ A x +
            b (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x +
            c (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) := by
      apply congrArg mean
      funext x
      rw [hdecomp]
      ring
    _ =
        mean (fun x : K → G =>
          p * B.edgeRemainder g₀ A x) +
          mean (fun x : K → G =>
            b (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) +
          mean (fun x : K → G =>
            c (edgeTuple g₀ x) *
              B.edgeRemainder g₀ A x) := by
      rw [mean_add, mean_add]
    _ =
        p * (B.eraseEdge g₀).bundleCount A +
          B.edgeContribution g₀ b A +
          B.edgeContribution g₀ c A := by
      rw [mean_smul]
      rfl

theorem edgeContribution_const
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (p : ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ (fun _ => p) A =
      p * (B.eraseEdge g₀).bundleCount A := by
  unfold edgeContribution bundleCount
  rw [← mean_smul]
  rfl

theorem mean_splitEdge
    [Fintype K] [Fintype G]
    (g : Finset K) (f : (K → G) → ℝ) :
    mean f =
      mean₂ (fun y : {v : K // v ∈ g} → G =>
        fun z : EdgeComplement g → G =>
          f ((splitEdgeEquiv g).symm (y, z))) := by
  calc
    mean f =
        mean (fun p :
          ({v : K // v ∈ g} → G) ×
            (EdgeComplement g → G) =>
              f ((splitEdgeEquiv g).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv (splitEdgeEquiv g)
      intro x
      simp
    _ = _ := by
      simpa only [Prod.eta] using
        (mean_prod_type
          (fun y : {v : K // v ∈ g} → G =>
            fun z : EdgeComplement g → G =>
              f ((splitEdgeEquiv g).symm (y, z))))

theorem edgeContribution_eq_mean_mul_remainderAverage
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A =
      mean (fun y =>
        q y * B.edgeRemainderAverage g₀ A y) := by
  unfold edgeContribution
  rw [mean_splitEdge g₀]
  unfold mean₂ edgeRemainderAverage edgeRemainderFiber
  apply congrArg mean
  funext y
  simp only [edgeTuple_splitEdgeEquiv_symm]
  rw [mean_smul]

theorem edgeContribution_eq_mean_frozenEdgeCorrelation
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A =
      mean (B.frozenEdgeCorrelation g₀ q A) := by
  unfold edgeContribution
  rw [mean_splitEdge g₀, mean₂_comm]
  unfold frozenEdgeCorrelation edgeRemainderFiber mean₂
  apply congrArg mean
  funext z
  apply congrArg mean
  funext y
  change
    q (edgeTuple g₀
        ((splitEdgeEquiv g₀).symm (y, z))) *
        B.edgeRemainder g₀ A
          ((splitEdgeEquiv g₀).symm (y, z)) =
      q y *
        B.edgeRemainder g₀ A
          ((splitEdgeEquiv g₀).symm (y, z))
  rw [edgeTuple_splitEdgeEquiv_symm]

theorem abs_edgeContribution_le_of_frozen
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {ε : ℝ}
    (hfrozen :
      ∀ z, |B.frozenEdgeCorrelation g₀ q A z| ≤ ε) :
    |B.edgeContribution g₀ q A| ≤ ε := by
  rw [B.edgeContribution_eq_mean_frozenEdgeCorrelation]
  calc
    |mean (B.frozenEdgeCorrelation g₀ q A)| ≤
        mean (fun z =>
          |B.frozenEdgeCorrelation g₀ q A z|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _z : EdgeComplement g₀ → G => ε) :=
      mean_mono hfrozen
    _ = ε := mean_const _

theorem doubledRemainderMoment_nonneg
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    0 ≤ B.doubledRemainderMoment g₀ A :=
  mean_nonneg fun _ => sq_nonneg _

theorem doubledRemainderMoment_eq_mean₂_pair
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.doubledRemainderMoment g₀ A =
      mean₂ (fun y :
          {v : K // v ∈ g₀} → G =>
        fun z :
          (EdgeComplement g₀ → G) ×
            (EdgeComplement g₀ → G) =>
          B.edgeRemainderFiber g₀ A y z.1 *
            B.edgeRemainderFiber g₀ A y z.2) := by
  unfold doubledRemainderMoment edgeRemainderAverage
  exact mean_inner_sq_eq_mean₂_pair
    (B.edgeRemainderFiber g₀ A)

theorem edgeContribution_sq_le_localSquare_mul_doubled
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A ^ 2 ≤
      mean (fun y => q y ^ 2) *
        B.doubledRemainderMoment g₀ A := by
  rw [B.edgeContribution_eq_mean_mul_remainderAverage]
  exact mean_mul_sq_le_product q
    (B.edgeRemainderAverage g₀ A)

end HypergraphBundle

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.PolynomialApproximation
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped Pointwise

theorem IsUnitBounded.nonneg
    {Ω : Type*} {g : Ω → ℝ} (hg : IsUnitBounded g) :
    ∀ x, 0 ≤ g x :=
  hg.1

theorem IsUnitBounded.le_one
    {Ω : Type*} {g : Ω → ℝ} (hg : IsUnitBounded g) :
    ∀ x, g x ≤ 1 :=
  hg.2

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SimplexTelescoping
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem apSimplexSystem_simplexWeight
    (k N : ℕ) (f : ZMod N → ℝ)
    (x : Fin k → ZMod N) :
    (apSimplexSystem k N f).simplexWeight x =
      cyclicAPProduct k N f
        (simplexCoordinateMoment k N x)
        (-simplexCoordinateSum k N x) := by
  apply Finset.prod_congr rfl
  intro j _
  change
    f (apSimplexForm k N j (deleteCoordinate x j)) =
      f (cyclicAPTerm
        (simplexCoordinateMoment k N x)
        (-simplexCoordinateSum k N x) j)
  congr 1
  rw [apSimplexForm_deleteCoordinate]
  simp [cyclicAPTerm]
  ring

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem mean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → ℝ) (g : β → ℝ)
    (h : ∀ x, f x = g (e x)) :
    mean f = mean g := by
  exact Fintype.expect_equiv e f g h

theorem mean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean (fun p : α × β => f p.1 p.2) = mean₂ f := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) f)

theorem mean_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] (f : α → ℝ) :
    mean (fun p : α × β => f p.1) = mean f := by
  calc
    mean (fun p : α × β => f p.1) =
        mean₂ (fun a (_ : β) => f a) := by
      exact mean_prod (fun a (_ : β) => f a)
    _ = mean f := by
      simp [mean₂]

theorem apSimplexSystem_simplexCount_eq_cyclicAPCount
    (r N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    (apSimplexSystem (r + 2) N f).simplexCount =
      cyclicAPCount (r + 2) N f := by
  rw [WeightedSimplexSystem.simplexCount, cyclicAPCount]
  calc
    mean (apSimplexSystem (r + 2) N f).simplexWeight =
        mean (fun x : Fin (r + 2) → ZMod N =>
          cyclicAPProduct (r + 2) N f
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)) := by
      apply congrArg mean
      funext x
      exact apSimplexSystem_simplexWeight (r + 2) N f x
    _ =
        mean (fun y :
            (ZMod N × ZMod N) × (Fin r → ZMod N) =>
          cyclicAPProduct (r + 2) N f y.1.1 y.1.2) := by
      apply mean_equiv (simplexAPEquiv r N)
      intro x
      rfl
    _ =
        mean (fun p : ZMod N × ZMod N =>
          cyclicAPProduct (r + 2) N f p.1 p.2) := by
      exact mean_prod_fst
        (fun p : ZMod N × ZMod N =>
          cyclicAPProduct (r + 2) N f p.1 p.2)
    _ =
        mean₂ (fun a d =>
          cyclicAPProduct (r + 2) N f a d) := by
      exact mean_prod
        (fun a d => cyclicAPProduct (r + 2) N f a d)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace SimplexHypergraph

theorem toWeighted_simplexWeight_eq_indicator {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)]
    (H : SimplexHypergraph V) (x : (i : Fin k) → V i) :
    H.toWeighted.simplexWeight x =
      finsetIndicator H.simplexFinset x := by
  classical
  by_cases hx : x ∈ H.simplexFinset
  · have hedges :
        ∀ j, H.edge j (deleteCoordinate x j) :=
      (H.mem_simplexFinset x).mp hx
    simp [WeightedSimplexSystem.simplexWeight, toWeighted,
      finsetIndicator, hx, hedges]
  · have hnot :
        ¬∀ j, H.edge j (deleteCoordinate x j) := by
      simpa using hx
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    have hzero :
        ∏ i : Fin k,
            H.toWeighted.edgeWeight i (deleteCoordinate x i) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact toWeighted_edgeWeight_of_not_edge H hj
    rw [WeightedSimplexSystem.simplexWeight, hzero]
    exact (finsetIndicator_of_not_mem hx).symm

theorem toWeighted_simplexCount_eq_card_div {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    H.toWeighted.simplexCount =
      (H.simplexFinset.card : ℝ) /
        Fintype.card ((i : Fin k) → V i) := by
  classical
  rw [WeightedSimplexSystem.simplexCount]
  have hfun :
      H.toWeighted.simplexWeight =
        finsetIndicator H.simplexFinset := by
    funext x
    exact toWeighted_simplexWeight_eq_indicator H x
  rw [hfun, mean_finsetIndicator]

end SimplexHypergraph

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BooleanCutReduction
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem IsBoundedCutTest.nonneg
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) :
    ∀ i x, 0 ≤ u i x :=
  hu.1

theorem IsBoundedCutTest.le_one
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) :
    ∀ i x, u i x ≤ 1 :=
  hu.2

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators Polynomial

theorem bernoulliAssignmentWeight_nonneg
    {κ : Type*} [Fintype κ]
    {p : κ → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (b : κ → Bool) :
    0 ≤ bernoulliAssignmentWeight p b := by
  apply Finset.prod_nonneg
  intro i _
  by_cases hi : b i
  · simpa [hi] using hp0 i
  · simp only [hi, Bool.false_eq_true,
      ↓reduceIte]
    linarith [hp1 i]

theorem sum_bernoulliAssignmentWeight
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) :
    ∑ b : κ → Bool, bernoulliAssignmentWeight p b = 1 := by
  change
    (∑ b : κ → Bool,
      ∏ i, if b i then p i else 1 - p i) = 1
  calc
    (∑ b : κ → Bool,
        ∏ i, if b i then p i else 1 - p i) =
        ∏ i, ∑ bit : Bool,
          if bit then p i else 1 - p i :=
      (Fintype.prod_sum
        (fun i : κ => fun bit : Bool =>
          if bit then p i else 1 - p i)).symm
    _ = ∏ _i : κ, (1 : ℝ) := by
      apply Fintype.prod_congr
      intro i
      simp
    _ = 1 := by simp

theorem sum_bernoulliAssignmentWeight_mul_selected
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) (s : Finset κ) :
    ∑ b : κ → Bool,
        bernoulliAssignmentWeight p b *
          ∏ i ∈ s, booleanValue b i =
      ∏ i ∈ s, p i := by
  calc
    (∑ b : κ → Bool,
        bernoulliAssignmentWeight p b *
          ∏ i ∈ s, booleanValue b i) =
        ∑ b : κ → Bool,
          ∏ i,
            (if b i then p i else 1 - p i) *
              (if i ∈ s then booleanValue b i else 1) := by
      apply Fintype.sum_congr
      intro b
      have hselected :
          (∏ i ∈ s, booleanValue b i) =
            ∏ i, if i ∈ s then booleanValue b i else 1 :=
        (Fintype.prod_ite_mem s
          (fun i => booleanValue b i)).symm
      rw [bernoulliAssignmentWeight, hselected]
      rw [← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ bit : Bool,
          (if bit then p i else 1 - p i) *
            (if i ∈ s then
              (if bit then (1 : ℝ) else 0) else 1) :=
      (Fintype.prod_sum
        (fun i : κ => fun bit : Bool =>
          (if bit then p i else 1 - p i) *
            (if i ∈ s then
              (if bit then (1 : ℝ) else 0) else 1))).symm
    _ = ∏ i, if i ∈ s then p i else 1 := by
      apply Fintype.prod_congr
      intro i
      by_cases hi : i ∈ s <;> simp [hi]
    _ = ∏ i ∈ s, p i := by
      exact Fintype.prod_ite_mem s p

theorem sum_bernoulliAssignmentWeight_mul_embedding
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (p : κ → ℝ) (e : ι ↪ κ) :
    ∑ b : κ → Bool,
        bernoulliAssignmentWeight p b *
          ∏ i : ι, booleanValue b (e i) =
      ∏ i : ι, p (e i) := by
  simpa only [Finset.prod_map, Finset.mem_univ, true_and,
    Finset.coe_univ, Function.Embedding.coeFn_mk] using
    (sum_bernoulliAssignmentWeight_mul_selected p
      (Finset.univ.map e))

theorem cutTestProduct_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (u : CutTestFamily G r) (x : Fin r → G) :
    cutTestProduct u x =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutTestProduct
            (cutTestFamilyOfBooleanAssignment b) x := by
  classical
  symm
  simpa [cutTestProduct, cutTestCoordinateValue,
    cutTestFamilyOfBooleanAssignment,
    usedCutTestCoordinateEmbedding_apply] using
    (sum_bernoulliAssignmentWeight_mul_embedding
      (cutTestCoordinateValue u)
      (usedCutTestCoordinateEmbedding x))

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.GeneratorCells
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem booleanFaceCutSupport_eval
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) (x : Fin r → G) :
    (booleanFaceCutSupport b).eval x =
      cutTestProduct (cutTestFamilyOfBooleanAssignment b) x := by
  classical
  by_cases h : ∀ i, b ⟨i, eraseCoordinate i x⟩ = true
  · have hx : x ∈ booleanFaceCutSupport b := by
      simp [booleanFaceCutSupport, h]
    rw [BooleanCutTest.eval_of_mem _ hx]
    unfold cutTestProduct
    symm
    apply Finset.prod_eq_one
    intro i _
    simp [cutTestFamilyOfBooleanAssignment, booleanValue, h i]
  · have hx : x ∉ booleanFaceCutSupport b := by
      simpa [booleanFaceCutSupport] using h
    rw [BooleanCutTest.eval_of_not_mem _ hx]
    obtain ⟨i, hi⟩ := not_forall.mp h
    cases hb : b ⟨i, eraseCoordinate i x⟩ with
    | false =>
        unfold cutTestProduct
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [cutTestFamilyOfBooleanAssignment,
          booleanValue, hb]
    | true =>
        exact (hi hb).elim

namespace FaceRegularityState

theorem faceCutCorrelation_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ)
    (b : BooleanCutAssignment G r) :
    S.faceCutCorrelation f
        (cutTestFamilyOfBooleanAssignment b) =
      S.booleanCutCorrelation f (booleanFaceCutSupport b) := by
  unfold faceCutCorrelation booleanCutCorrelation
  apply congrArg mean
  funext x
  rw [booleanFaceCutSupport_eval]

theorem faceCutCorrelation_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : CutTestFamily G r) :
    S.faceCutCorrelation f u =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          S.faceCutCorrelation f
            (cutTestFamilyOfBooleanAssignment b) := by
  unfold faceCutCorrelation
  calc
    mean (fun x : Fin r → G =>
        S.residual f x * cutTestProduct u x) =
        mean (fun x : Fin r → G =>
          ∑ b : BooleanCutAssignment G r,
            bernoulliAssignmentWeight
                (cutTestCoordinateValue u) b *
              (S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x)) := by
      apply congrArg mean
      funext x
      rw [cutTestProduct_eq_sum_boolean u x,
        Finset.mul_sum]
      apply Fintype.sum_congr
      intro b
      ring
    _ =
        ∑ b : BooleanCutAssignment G r,
          mean (fun x : Fin r → G =>
            bernoulliAssignmentWeight
                (cutTestCoordinateValue u) b *
              (S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x)) := by
      unfold mean
      exact Finset.expect_sum_comm Finset.univ Finset.univ _
    _ =
        ∑ b : BooleanCutAssignment G r,
          bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            mean (fun x : Fin r → G =>
              S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x) := by
      apply Fintype.sum_congr
      intro b
      exact mean_smul
        (bernoulliAssignmentWeight
          (cutTestCoordinateValue u) b) _
    _ = _ := by
      rfl

end FaceRegularityState

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedPattern
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem mean_splitOrderedFace
    {G : Type*} [Fintype G] {k r : ℕ}
    (e : OrderedFace k r) (f : (Fin k → G) → ℝ) :
    mean f =
      mean₂ (fun y : Fin r → G =>
        fun z : OrderedFaceComplement e → G =>
          f ((splitOrderedFaceEquiv e).symm (y, z))) := by
  calc
    mean f =
        mean (fun p :
          (Fin r → G) × (OrderedFaceComplement e → G) =>
            f ((splitOrderedFaceEquiv e).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv
        (splitOrderedFaceEquiv e)
      intro x
      simp
    _ = _ := by
      simpa only [Prod.eta] using
        (mean_prod_type
          (fun y : Fin r → G =>
            fun z : OrderedFaceComplement e → G =>
              f ((splitOrderedFaceEquiv e).symm (y, z))))

namespace OrderedPattern

theorem toWeighted_patternWeight_of_occurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    {x : Fin k → G} (hx : H.IsOccurrence x) :
    H.toWeighted.patternWeight x = 1 := by
  classical
  unfold WeightedOrderedPattern.patternWeight
  apply Finset.prod_eq_one
  intro e _he
  simp [toWeighted, hx e]

theorem toWeighted_patternWeight_of_not_occurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    {x : Fin k → G} (hx : ¬H.IsOccurrence x) :
    H.toWeighted.patternWeight x = 0 := by
  classical
  unfold WeightedOrderedPattern.patternWeight
  obtain ⟨e, he⟩ := not_forall.mp hx
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  simp [toWeighted, he]

theorem toWeighted_patternCount_eq
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : OrderedPattern G k r) :
    H.toWeighted.patternCount =
      (H.occurrenceFinset.card : ℝ) /
        Fintype.card (Fin k → G) := by
  rw [WeightedOrderedPattern.patternCount]
  have hfun :
      H.toWeighted.patternWeight =
        finsetIndicator H.occurrenceFinset := by
    funext x
    by_cases hx : H.IsOccurrence x
    · rw [H.toWeighted_patternWeight_of_occurrence hx,
        finsetIndicator_of_mem]
      exact (H.mem_occurrenceFinset x).2 hx
    · rw [H.toWeighted_patternWeight_of_not_occurrence hx,
        finsetIndicator_of_not_mem]
      exact fun hmem =>
        hx ((H.mem_occurrenceFinset x).1 hmem)
  rw [hfun, mean_finsetIndicator]

end OrderedPattern

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem apSetHypergraph_simplexCount_eq_cyclicAPCount
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N)) :
    (apSetHypergraph (r + 2) N A).toWeighted.simplexCount =
      cyclicAPCount (r + 2) N (finsetIndicator A) := by
  rw [← apSimplexSystem_simplexCount_eq_cyclicAPCount
    r N (finsetIndicator A)]
  simp only [WeightedSimplexSystem.simplexCount]
  apply congrArg mean
  funext x
  apply Finset.prod_congr rfl
  intro j _
  exact apSetHypergraph_toWeighted_edgeWeight
    (r + 2) N A j (deleteCoordinate x j)

theorem diagonalAPSimplex_injective
    (r N : ℕ) (A : Finset (ZMod N)) :
    Function.Injective (diagonalAPSimplex r N A) := by
  intro p q hpq
  apply Prod.ext
  · apply Subtype.ext
    have hmoment :=
      congrArg
        (simplexCoordinateMoment (r + 2) N) hpq
    simpa using hmoment
  · funext i
    exact congrFun hpq i.succ.succ

theorem eq_of_deletedVectorToFinTuple_eq_of_sum_eq
    {G : Type*} [AddCommGroup G] {n : ℕ}
    {x y : Fin (n + 1) → G}
    {j l : Fin (n + 1)}
    (hjl : j = l)
    (hdeleted :
      deletedVectorToFinTuple j (deleteCoordinate x j) =
        deletedVectorToFinTuple l (deleteCoordinate y l))
    (hsum : (∑ i, x i) = ∑ i, y i) :
    x = y := by
  subst l
  have hother :
      ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i =
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          y i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hij
    subst i
    exact congrFun hdeleted t
  have hj : x j = y j := by
    apply add_left_cancel
      (a :=
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i)
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i) + x j =
          ∑ i, x i :=
        Finset.sum_erase_add _ _ (Finset.mem_univ j)
      _ = ∑ i, y i := hsum
      _ =
          (∑ i ∈
              (Finset.univ : Finset (Fin (n + 1))).erase j,
              y i) + y j :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
      _ =
          (∑ i ∈
              (Finset.univ : Finset (Fin (n + 1))).erase j,
              x i) + y j := by
        rw [hother]
  funext i
  by_cases hij : i = j
  · simpa [hij] using hj
  · obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hij
    subst i
    exact congrFun hdeleted t

namespace SimplexHypergraph

theorem mem_deletionSlotFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j)
    (hx : x ∈ deleted j) :
    (j, deletedVectorToFinTuple j x) ∈
      deletionSlotFinset deleted := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem card_deletionSlotFinset_le_deletionCount
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G)) :
    (deletionSlotFinset deleted).card ≤
      deletionCount deleted := by
  classical
  calc
    (deletionSlotFinset deleted).card ≤
        ∑ j : Fin (n + 1),
          ((deleted j).image fun x =>
            (j, deletedVectorToFinTuple j x)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ j : Fin (n + 1), (deleted j).card := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.card_image_le
    _ = deletionCount deleted := rfl

end SimplexHypergraph

theorem diagonalCoveredSlot_mem_deletionSlotFinset
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    diagonalCoveredSlot r N A deleted hcover p ∈
      SimplexHypergraph.deletionSlotFinset deleted := by
  classical
  exact SimplexHypergraph.mem_deletionSlotFinset deleted
    (diagonalCoverColor r N A deleted hcover p)
    (deleteCoordinate (diagonalAPSimplex r N A p)
      (diagonalCoverColor r N A deleted hcover p))
    (diagonalCoverColor_mem r N A deleted hcover p)

theorem diagonalCoveredSlot_injective
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    Function.Injective
      (diagonalCoveredSlot r N A deleted hcover) := by
  intro p q hpq
  apply diagonalAPSimplex_injective r N A
  apply eq_of_deletedVectorToFinTuple_eq_of_sum_eq
  · exact congrArg Prod.fst hpq
  · exact congrArg Prod.snd hpq
  · change
      simplexCoordinateSum (r + 2) N
          (diagonalAPSimplex r N A p) =
        simplexCoordinateSum (r + 2) N
          (diagonalAPSimplex r N A q)
    simp

theorem card_diagonalAPParameter_le_deletionCount
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    Fintype.card (DiagonalAPParameter r N A) ≤
      SimplexHypergraph.deletionCount deleted := by
  classical
  let f := diagonalCoveredSlot r N A deleted hcover
  calc
    Fintype.card (DiagonalAPParameter r N A) =
        (Finset.univ.image f).card := by
      rw [Finset.card_image_of_injective _
        (diagonalCoveredSlot_injective r N A deleted hcover)]
      simp
    _ ≤
        (SimplexHypergraph.deletionSlotFinset deleted).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hy
      exact diagonalCoveredSlot_mem_deletionSlotFinset
        r N A deleted hcover p
    _ ≤ SimplexHypergraph.deletionCount deleted :=
      SimplexHypergraph.card_deletionSlotFinset_le_deletionCount
        deleted

theorem mean_finsetIndicator_div_le_normalizedDeletionCost
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    mean (finsetIndicator A) / (r + 2 : ℝ) ≤
      SimplexHypergraph.normalizedDeletionCost deleted := by
  have hcount :
      A.card * N ^ r ≤
        SimplexHypergraph.deletionCount deleted := by
    simpa using
      card_diagonalAPParameter_le_deletionCount
        r N A deleted hcover
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  rw [mean_finsetIndicator, ZMod.card,
    SimplexHypergraph.normalizedDeletionCost,
    deletionCapacity_zmod]
  calc
    (A.card : ℝ) / (N : ℝ) / (r + 2 : ℝ) =
        ((A.card * N ^ r : ℕ) : ℝ) /
          (((r + 2) * N ^ (r + 1) : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul, Nat.cast_pow]
      field_simp
      ring
    _ ≤
        (SimplexHypergraph.deletionCount deleted : ℝ) /
          (((r + 2) * N ^ (r + 1) : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcount
      · positivity

theorem exists_uniformDenseAPCount_of_simplexRemoval
    (r : ℕ)
    (hrem :
      HasUniformCyclicPartiteSimplexRemoval (r + 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformDenseAPCount (r + 2) δ c := by
  let ε : ℝ := (δ / (r + 2 : ℝ)) / 2
  have hk : 0 < (r + 2 : ℝ) := by positivity
  have hbase : 0 < δ / (r + 2 : ℝ) :=
    div_pos hδ hk
  have hε : 0 < ε := by
    exact div_pos hbase (by norm_num)
  obtain ⟨c, hc, hremove⟩ := hrem ε hε
  refine ⟨c, hc, ?_⟩
  intro N inst A hA
  by_contra hcount
  have hcount_lt :
      cyclicAPCount (r + 2) N (finsetIndicator A) < c :=
    lt_of_not_ge hcount
  have hsimplex_lt :
      (apSetHypergraph (r + 2) N A).toWeighted.simplexCount <
        c := by
    simpa [apSetHypergraph_simplexCount_eq_cyclicAPCount]
      using hcount_lt
  obtain ⟨deleted, hcover, hcost⟩ :=
    hremove N (apSetHypergraph (r + 2) N A) hsimplex_lt
  have hlower :
      mean (finsetIndicator A) / (r + 2 : ℝ) ≤
        SimplexHypergraph.normalizedDeletionCost deleted :=
    mean_finsetIndicator_div_le_normalizedDeletionCost
      r N A deleted hcover
  have hdensity :
      δ / (r + 2 : ℝ) ≤
        mean (finsetIndicator A) / (r + 2 : ℝ) :=
    div_le_div_of_nonneg_right hA hk.le
  have hε_lt : ε < δ / (r + 2 : ℝ) := by
    dsimp [ε]
    linarith
  linarith

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem SimplexHypergraph.toOrderedPattern_isOccurrence_iff
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (x : Fin (n + 1) → G) :
    H.toOrderedPattern.IsOccurrence x ↔
      ∀ j, H.edge j (deleteCoordinate x j) := by
  constructor
  · intro hx j
    have hj := hx (orderedFacet j)
    rw [H.toOrderedPattern_edge_orderedFacet] at hj
    simpa using hj
  · intro hx e
    let j := (orderedFacetEquiv n).symm e
    have he : orderedFacet j = e := by
      rw [← orderedFacetEquiv_apply]
      exact (orderedFacetEquiv n).apply_symm_apply e
    rw [← he]
    rw [H.toOrderedPattern_edge_orderedFacet]
    simpa using hx j

theorem SimplexHypergraph.toOrderedPattern_occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    H.toOrderedPattern.occurrenceFinset =
      H.simplexFinset := by
  ext x
  rw [OrderedPattern.mem_occurrenceFinset,
    SimplexHypergraph.mem_simplexFinset,
    H.toOrderedPattern_isOccurrence_iff]

theorem SimplexHypergraph.toOrderedPattern_patternCount
    {G : Type*} [Fintype G] [Nonempty G]
    {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    H.toOrderedPattern.toWeighted.patternCount =
      H.toWeighted.simplexCount := by
  classical
  rw [OrderedPattern.toWeighted_patternCount_eq,
    SimplexHypergraph.toWeighted_simplexCount_eq_card_div,
    H.toOrderedPattern_occurrenceFinset]

theorem SimplexHypergraph.isSimplexCover_orderedDeletionToSimplex
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (hcover : H.toOrderedPattern.IsCover D) :
    H.IsSimplexCover (orderedDeletionToSimplex D) := by
  intro x hx
  have hxOrdered :
      x ∈ H.toOrderedPattern.occurrenceFinset := by
    rw [H.toOrderedPattern_occurrenceFinset]
    exact hx
  obtain ⟨e, he⟩ := hcover x hxOrdered
  let j := (orderedFacetEquiv n).symm e
  have heq : orderedFacet j = e := by
    rw [← orderedFacetEquiv_apply]
    exact (orderedFacetEquiv n).apply_symm_apply e
  refine ⟨j, (mem_orderedDeletionToSimplex_iff D j _).2 ?_⟩
  rw [
    deletedVectorToFinTuple_deleteCoordinate_eq_orderedFaceTuple,
    heq]
  exact he

theorem colorDeletionDensity_orderedDeletionToSimplex
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1)) :
    SimplexHypergraph.colorDeletionDensity
        (orderedDeletionToSimplex D) j =
      OrderedPattern.faceDeletionDensity
        D (orderedFacet j) := by
  rw [SimplexHypergraph.colorDeletionDensity,
    OrderedPattern.faceDeletionDensity,
    card_orderedDeletionToSimplex]
  have hcard :
      Fintype.card
          (DeletedVector
            (fun _ : Fin (n + 1) => G) j) =
        Fintype.card (Fin n → G) :=
    Fintype.card_congr (deletedVectorFinTupleEquiv j)
  rw [hcard]

theorem normalizedDeletionCost_orderedDeletionToSimplex_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    {ε : ℝ}
    (hD :
      ∀ e, OrderedPattern.faceDeletionDensity D e ≤ ε) :
    SimplexHypergraph.normalizedDeletionCost
        (orderedDeletionToSimplex D) ≤ ε := by
  let M : ℕ := Fintype.card (Fin n → G)
  have hM : 0 < M := Fintype.card_pos
  have hface (j : Fin (n + 1)) :
      Fintype.card
          (DeletedVector
            (fun _ : Fin (n + 1) => G) j) = M := by
    exact Fintype.card_congr (deletedVectorFinTupleEquiv j)
  have hcard (j : Fin (n + 1)) :
      ((orderedDeletionToSimplex D j).card : ℝ) ≤
        ε * M := by
    have hdensity :=
      colorDeletionDensity_orderedDeletionToSimplex D j
    have hbound := hD (orderedFacet j)
    rw [← hdensity] at hbound
    rw [SimplexHypergraph.colorDeletionDensity,
      hface] at hbound
    have hMR : (0 : ℝ) < M := by
      exact_mod_cast hM
    exact (div_le_iff₀ hMR).mp hbound
  have hcount :
      (SimplexHypergraph.deletionCount
          (orderedDeletionToSimplex D) : ℝ) ≤
        (n + 1 : ℝ) * (ε * M) := by
    calc
      (SimplexHypergraph.deletionCount
          (orderedDeletionToSimplex D) : ℝ) =
          ∑ j : Fin (n + 1),
            ((orderedDeletionToSimplex D j).card : ℝ) := by
        simp [SimplexHypergraph.deletionCount]
      _ ≤ ∑ _j : Fin (n + 1), ε * M :=
        Finset.sum_le_sum fun j _ => hcard j
      _ = (n + 1 : ℝ) * (ε * M) := by
        simp
  have hcapacity :
      SimplexHypergraph.deletionCapacity
          (fun _ : Fin (n + 1) => G) =
        (n + 1) * M := by
    unfold SimplexHypergraph.deletionCapacity
    simp_rw [hface]
    simp
  rw [SimplexHypergraph.normalizedDeletionCost,
    hcapacity]
  have hdenom :
      (0 : ℝ) < ((n + 1) * M : ℕ) := by
    exact_mod_cast Nat.mul_pos (by omega) hM
  apply (div_le_iff₀ hdenom).2
  calc
    (SimplexHypergraph.deletionCount
        (orderedDeletionToSimplex D) : ℝ) ≤
        (n + 1 : ℝ) * (ε * M) := hcount
    _ = ε * (((n + 1) * M : ℕ) : ℝ) := by
      push_cast
      ring

theorem hasUniformCyclicPartiteSimplexRemoval_of_ordered
    (n : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (n + 1) n) :
    HasUniformCyclicPartiteSimplexRemoval (n + 1) := by
  intro ε hε
  obtain ⟨c, hc, hremove⟩ := hordered ε hε
  refine ⟨c, hc, ?_⟩
  intro N inst H hcount
  have horderedCount :
      H.toOrderedPattern.toWeighted.patternCount < c := by
    rw [H.toOrderedPattern_patternCount]
    exact hcount
  obtain ⟨D, hcover, hD⟩ :=
    hremove (ZMod N) H.toOrderedPattern horderedCount
  exact
    ⟨orderedDeletionToSimplex D,
      H.isSimplexCover_orderedDeletionToSimplex D hcover,
      normalizedDeletionCost_orderedDeletionToSimplex_le D hD⟩

theorem hasUniformCyclicPartiteSimplexRemoval_add_two_of_ordered
    (r : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (r + 2) (r + 1)) :
    HasUniformCyclicPartiteSimplexRemoval (r + 2) := by
  simpa [Nat.add_assoc] using
    (hasUniformCyclicPartiteSimplexRemoval_of_ordered
      (r + 1) (by simpa [Nat.add_assoc] using hordered))

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

theorem exists_uniformDenseAPCount_of_orderedRemoval
    (r : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (r + 2) (r + 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformDenseAPCount (r + 2) δ c :=
  exists_uniformDenseAPCount_of_simplexRemoval r
    (hasUniformCyclicPartiteSimplexRemoval_add_two_of_ordered
      r hordered)
    hδ

theorem exists_uniformDenseAPCount_of_orderedRemoval_of_two_le
    (k : ℕ) (hk : 2 ≤ k)
    (hordered :
      HasUniformOrderedPatternRemoval k (k - 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformDenseAPCount k δ c := by
  have hcolors : k - 2 + 2 = k := by
    omega
  have hrank : k - 2 + 1 = k - 1 := by
    omega
  have hordered' :
      HasUniformOrderedPatternRemoval
        (k - 2 + 2) (k - 2 + 1) := by
    simpa only [hcolors, hrank] using hordered
  simpa only [hcolors] using
    (exists_uniformDenseAPCount_of_orderedRemoval
      (k - 2) hordered' hδ)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedBoundaryPartition
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedPartitionComplex

theorem Refines.trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C D E : OrderedPartitionComplex G k r}
    (hCD : C.Refines D) (hDE : D.Refines E) :
    C.Refines E :=
  fun j e => le_trans (hCD j e) (hDE j e)

end OrderedPartitionComplex

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedAtomEnergy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem partitionAtomIndicator_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    0 ≤ partitionAtomIndicator Q a x := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

theorem partitionAtomIndicator_le_one
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    partitionAtomIndicator Q a x ≤ 1 := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

theorem partitionAtomEnergy_sub_eq_sum_mean_sq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P R : FacePartition Ω} (hPR : P ≤ R)
    (Q : FacePartition Ω) :
    partitionAtomEnergy P Q - partitionAtomEnergy R Q =
      ∑ a : Q.parts,
        mean (fun x =>
          (conditionalMean P (partitionAtomIndicator Q a) x -
            conditionalMean R (partitionAtomIndicator Q a) x) ^ 2) := by
  unfold partitionAtomEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact partitionEnergy_sub_eq_mean_sq P R hPR
    (partitionAtomIndicator Q a)

theorem orderedAtomEnergy_sub_eq_sum_mean_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (upper : FacePartition (Fin (j + 1) → G)) :
    orderedAtomEnergy fine e upper -
        orderedAtomEnergy coarse e upper =
      ∑ a : upper.parts,
        mean (fun x =>
          (orderedBoundaryStructured fine e
                (partitionAtomIndicator upper a) x -
            orderedBoundaryStructured coarse e
                (partitionAtomIndicator upper a) x) ^ 2) := by
  exact partitionAtomEnergy_sub_eq_sum_mean_sq
    (orderedBoundaryPartition_mono hfc e) upper

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BoundaryBernoulli
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem sum_boundaryBernoulliWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (u : CutTestFamily G (j + 1)) :
    ∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b = 1 := by
  classical
  calc
    (∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b) =
        ∑ b : BooleanCutAssignment G (j + 1),
          bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b := by
      symm
      exact
        Fintype.sum_equiv
          (booleanBoundaryAssignmentEquiv G j)
          (fun b : BooleanCutAssignment G (j + 1) =>
            bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b)
          (fun b : BoundaryBooleanCutAssignment G j =>
            boundaryBernoulliWeight u b)
          (fun b => by simp [boundaryBernoulliWeight])
    _ = 1 :=
      sum_bernoulliAssignmentWeight
        (cutTestCoordinateValue u)

theorem boundaryBernoulliWeight_nonneg
    {G : Type*} [Fintype G]
    {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (hu : IsBoundedCutTest u)
    (b : BoundaryBooleanCutAssignment G j) :
    0 ≤ boundaryBernoulliWeight u b := by
  exact
    bernoulliAssignmentWeight_nonneg
      (p := cutTestCoordinateValue u)
      (fun q => hu.nonneg q.1 q.2)
      (fun q => hu.le_one q.1 q.2)
      (booleanAssignmentOfBoundary b)

theorem eraseBoundaryCoordinate_eq_eraseCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    eraseBoundaryCoordinate i x = eraseCoordinate i x :=
  rfl

theorem boundaryBooleanCutSupport_eq_booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    boundaryBooleanCutSupport b =
      booleanFaceCutSupport (booleanAssignmentOfBoundary b) := by
  classical
  ext x
  rw [mem_boundaryBooleanCutSupport,
    mem_booleanFaceCutSupport]
  simp only [booleanAssignmentOfBoundary,
    eraseBoundaryCoordinate_eq_eraseCoordinate]

namespace FaceRegularityState

theorem faceCutCorrelation_eq_sum_boundaryBoolean
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (S : FaceRegularityState (Fin (j + 1) → G))
    (f : (Fin (j + 1) → G) → ℝ)
    (u : CutTestFamily G (j + 1)) :
    S.faceCutCorrelation f u =
      ∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b) := by
  classical
  rw [S.faceCutCorrelation_eq_sum_boolean]
  exact
    Fintype.sum_equiv
      (booleanBoundaryAssignmentEquiv G j)
      (fun b : BooleanCutAssignment G (j + 1) =>
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          S.faceCutCorrelation f
            (cutTestFamilyOfBooleanAssignment b))
      (fun b : BoundaryBooleanCutAssignment G j =>
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b))
      (fun b => by
        rw [S.faceCutCorrelation_boolean]
        simp [boundaryBernoulliWeight,
          boundaryBooleanCutSupport_eq_booleanFaceCutSupport])

theorem abs_faceCutCorrelation_le_of_boundaryBoolean
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (S : FaceRegularityState (Fin (j + 1) → G))
    (f : (Fin (j + 1) → G) → ℝ)
    {ε : ℝ}
    (u : CutTestFamily G (j + 1))
    (hu : IsBoundedCutTest u)
    (hboolean :
      ∀ b : BoundaryBooleanCutAssignment G j,
        |S.booleanCutCorrelation f
          (boundaryBooleanCutSupport b)| ≤ ε) :
    |S.faceCutCorrelation f u| ≤ ε := by
  rw [S.faceCutCorrelation_eq_sum_boundaryBoolean]
  calc
    |∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b)| ≤
        ∑ b : BoundaryBooleanCutAssignment G j,
          |boundaryBernoulliWeight u b *
            S.booleanCutCorrelation f
              (boundaryBooleanCutSupport b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ b : BoundaryBooleanCutAssignment G j,
          boundaryBernoulliWeight u b * ε := by
      apply Finset.sum_le_sum
      intro b _
      have hw : 0 ≤ boundaryBernoulliWeight u b :=
        boundaryBernoulliWeight_nonneg u hu b
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hboolean b) hw
    _ = ε := by
      rw [← Finset.sum_mul,
        sum_boundaryBernoulliWeight, one_mul]

end FaceRegularityState

theorem IsPreliminaryOrderedRegular.toBounded
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {lower : OrderedFacePartitionSystem G k j}
    {upper : OrderedFacePartitionSystem G k (j + 1)}
    {ε : ℝ}
    (hregular :
      IsPreliminaryOrderedRegular lower upper ε) :
    IsPreliminaryOrderedBoundedRegular
      lower upper ε := by
  intro e a u hu
  exact
    FaceRegularityState.abs_faceCutCorrelation_le_of_boundaryBoolean
      (⟨orderedBoundaryPartition lower e⟩ :
        FaceRegularityState (Fin (j + 1) → G))
      (partitionAtomIndicator (upper e) a)
      u hu (fun b => hregular e a b)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedGoodAtoms
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem partitionAtomAt_eq_iff_mem_part
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (x y : Ω) :
    partitionAtomAt P y = partitionAtomAt P x ↔
      y ∈ P.part x := by
  rw [partitionAtomAt_eq_iff_mem]
  rfl

theorem partitionAtomIndicator_measurable
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (a : P.parts) :
    IsPartitionMeasurable P (partitionAtomIndicator P a) := by
  intro x y hy
  have hxy :
      partitionAtomAt P y = partitionAtomAt P x :=
    (partitionAtomAt_eq_iff_mem_part P x y).2 hy
  by_cases hx : x ∈ a.1
  · have hax : partitionAtomAt P x = a :=
      (partitionAtomAt_eq_iff_mem P x a).2 hx
    have hay : partitionAtomAt P y = a := hxy.trans hax
    have hy' : y ∈ a.1 :=
      (partitionAtomAt_eq_iff_mem P y a).1 hay
    simp [partitionAtomIndicator_of_mem P a hx,
      partitionAtomIndicator_of_mem P a hy']
  · have hy' : y ∉ a.1 := by
      intro hya
      have hay : partitionAtomAt P y = a :=
        (partitionAtomAt_eq_iff_mem P y a).2 hya
      have hax : partitionAtomAt P x = a :=
        hxy.symm.trans hay
      exact hx ((partitionAtomAt_eq_iff_mem P x a).1 hax)
    simp [partitionAtomIndicator_of_not_mem P a hx,
      partitionAtomIndicator_of_not_mem P a hy']

theorem mem_partitionAtomUnion_iff_atomAt_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) (x : Ω) :
    x ∈ partitionAtomUnion P s ↔
      partitionAtomAt P x ∈ s := by
  constructor
  · intro hx
    obtain ⟨a, ha, hxa⟩ :=
      (mem_partitionAtomUnion P s x).1 hx
    have hcanonical :
        partitionAtomAt P x = a :=
      (partitionAtomAt_eq_iff_mem P x a).2 hxa
    simpa [hcanonical] using ha
  · intro hx
    exact
      (mem_partitionAtomUnion P s x).2
        ⟨partitionAtomAt P x, hx,
          P.mem_part (Finset.mem_univ x)⟩

theorem partitionAtomUnion_indicator_measurable
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (s : Finset P.parts) :
    IsPartitionMeasurable P
      (finsetIndicator (partitionAtomUnion P s)) := by
  intro x y hy
  have hxy :
      partitionAtomAt P y = partitionAtomAt P x :=
    (partitionAtomAt_eq_iff_mem_part P x y).2 hy
  have hmem :
      y ∈ partitionAtomUnion P s ↔
        x ∈ partitionAtomUnion P s := by
    rw [mem_partitionAtomUnion_iff_atomAt_mem,
      mem_partitionAtomUnion_iff_atomAt_mem, hxy]
  by_cases hx : x ∈ partitionAtomUnion P s
  · have hy' : y ∈ partitionAtomUnion P s := hmem.mpr hx
    simp [finsetIndicator_of_mem hx,
      finsetIndicator_of_mem hy']
  · have hy' : y ∉ partitionAtomUnion P s :=
      fun h => hx (hmem.mp h)
    simp [finsetIndicator_of_not_mem hx,
      finsetIndicator_of_not_mem hy']

theorem mean_mul_partitionAtomIndicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (a : P.parts) :
    mean (fun x => f x * partitionAtomIndicator P a x) =
      conditionalMean P f (P.representative a) *
        mean (partitionAtomIndicator P a) := by
  rw [FaceRegularityState.mean_mul_eq_mean_conditionalMean_mul
    P f (partitionAtomIndicator P a)
    (partitionAtomIndicator_measurable P a)]
  rw [← mean_smul]
  apply congrArg mean
  funext x
  by_cases hx : x ∈ a.1
  · rw [partitionAtomIndicator_of_mem P a hx,
      mul_one, mul_one]
    have hrep :
        P.representative a ∈ P.part x := by
      rw [P.part_eq_of_mem a.2 hx]
      exact P.representative_mem a
    exact
      (conditionalMean_eq_of_mem_part P f hrep).symm
  · rw [partitionAtomIndicator_of_not_mem P a hx,
      mul_zero, mul_zero]

theorem mean_mul_partitionAtomIndicator_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (a : P.parts)
    {β : ℝ}
    (hβ : conditionalMean P f (P.representative a) ≤ β) :
    mean (fun x => f x * partitionAtomIndicator P a x) ≤
      β * mean (partitionAtomIndicator P a) := by
  rw [mean_mul_partitionAtomIndicator P f a]
  apply mul_le_mul_of_nonneg_right hβ
  exact mean_nonneg fun x =>
    partitionAtomIndicator_nonneg P a x

@[simp]
theorem mem_smallAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (α : ℝ)
    (x : Ω) :
    x ∈ smallAverageBaseSupport P f α ↔
      conditionalMean P f x < α := by
  rw [smallAverageBaseSupport,
    mem_partitionAtomUnion_iff_atomAt_mem]
  simp only [smallAverageBaseAtoms, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hrep :
      P.representative (partitionAtomAt P x) ∈
        P.part x := by
    exact P.representative_mem (partitionAtomAt P x)
  have heq :=
    conditionalMean_eq_of_mem_part P f hrep
  rw [heq]

theorem mean_indicator_inter_smallAverageBaseSupport_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P : FacePartition Ω) (A : Finset Ω)
    {α : ℝ} (hα : 0 ≤ α) :
    mean (finsetIndicator
      (A ∩ smallAverageBaseSupport P (finsetIndicator A) α)) ≤
      α := by
  rw [show
      finsetIndicator
          (A ∩ smallAverageBaseSupport P (finsetIndicator A) α) =
        fun x =>
          finsetIndicator A x *
            finsetIndicator
              (smallAverageBaseSupport
                P (finsetIndicator A) α) x by
    funext x
    by_cases hxA : x ∈ A <;>
      by_cases hxB :
        x ∈ smallAverageBaseSupport P (finsetIndicator A) α <;>
      simp [hxA, hxB]]
  rw [FaceRegularityState.mean_mul_eq_mean_conditionalMean_mul
    P (finsetIndicator A)
      (finsetIndicator
        (smallAverageBaseSupport P (finsetIndicator A) α))
      (partitionAtomUnion_indicator_measurable P
        (smallAverageBaseAtoms P (finsetIndicator A) α))]
  calc
    mean (fun x =>
        conditionalMean P (finsetIndicator A) x *
          finsetIndicator
            (smallAverageBaseSupport P
              (finsetIndicator A) α) x) ≤
        mean (fun _x : Ω => α) := by
      apply mean_mono
      intro x
      by_cases hx :
          x ∈ smallAverageBaseSupport P (finsetIndicator A) α
      · rw [finsetIndicator_of_mem hx, mul_one]
        exact
          (mem_smallAverageBaseSupport
            P (finsetIndicator A) α x).1 hx |>.le
      · rw [finsetIndicator_of_not_mem hx, mul_zero]
        exact hα
    _ = α := mean_const α

@[simp]
theorem mem_largeAverageBaseSupport
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (β : ℝ)
    (x : Ω) :
    x ∈ largeAverageBaseSupport P f β ↔
      β < conditionalMean P f x := by
  rw [largeAverageBaseSupport,
    mem_partitionAtomUnion_iff_atomAt_mem]
  simp only [largeAverageBaseAtoms, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hrep :
      P.representative (partitionAtomAt P x) ∈
        P.part x := by
    exact P.representative_mem (partitionAtomAt P x)
  have heq :=
    conditionalMean_eq_of_mem_part P f hrep
  rw [heq]

theorem mul_mean_indicator_largeAverageBaseSupport_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    {β : ℝ} (_hβ : 0 ≤ β) :
    β * mean (finsetIndicator
        (largeAverageBaseSupport P f β)) ≤
      mean f := by
  rw [← mean_smul]
  calc
    mean (fun x =>
        β * finsetIndicator
          (largeAverageBaseSupport P f β) x) ≤
        mean (conditionalMean P f) := by
      apply mean_mono
      intro x
      by_cases hx : x ∈ largeAverageBaseSupport P f β
      · rw [finsetIndicator_of_mem hx, mul_one]
        exact
          (mem_largeAverageBaseSupport P f β x).1 hx |>.le
      · rw [finsetIndicator_of_not_mem hx, mul_zero]
        exact conditionalMean_nonneg P hf x
    _ = mean f := mean_conditionalMean P f

theorem atomBoundaryDefectSq_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (fine coarse upper : FacePartition Ω)
    (a : upper.parts) (x : Ω) :
    0 ≤ atomBoundaryDefectSq fine coarse upper a x :=
  sq_nonneg _

theorem mean_indicator_inter_union_le_add
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A B C : Finset Ω) :
    mean (finsetIndicator (A ∩ (B ∪ C))) ≤
      mean (finsetIndicator (A ∩ B)) +
        mean (finsetIndicator C) := by
  rw [← mean_add]
  apply mean_mono
  intro x
  by_cases hx : x ∈ A ∩ (B ∪ C)
  · rw [finsetIndicator_of_mem hx]
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).2 with hxB | hxC
    · have hxAB : x ∈ A ∩ B :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hxB⟩
      rw [finsetIndicator_of_mem hxAB]
      exact le_add_of_nonneg_right
        (by
          by_cases hxc : x ∈ C <;> simp [hxc])
    · rw [finsetIndicator_of_mem hxC]
      exact le_add_of_nonneg_left
        (by
          by_cases hxab : x ∈ A ∩ B <;> simp [hxab])
  · rw [finsetIndicator_of_not_mem hx]
    exact add_nonneg
      (by
        by_cases hxab : x ∈ A ∩ B <;> simp [hxab])
      (by
        by_cases hxc : x ∈ C <;> simp [hxc])

namespace ClosedOrderedAtomConfiguration

theorem atom_eq_partitionAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (j : Fin (r + 1)) (e : OrderedFace k j.1) :
    A.atom j e =
      partitionAtomAt (C.partition j e)
        (orderedFaceTuple e A.witness) := by
  apply Subtype.ext
  exact
    ((C.partition j e).part_eq_of_mem
      (A.atom j e).2 (A.mem_atom j e)).symm

end ClosedOrderedAtomConfiguration

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedPatternPartition
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedPartitionComplex

theorem appendTop_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    {fineTop coarseTop :
      OrderedFacePartitionSystem G k (r + 1)}
    (hfc : fine.Refines coarse)
    (htop : OrderedFacePartitionRefines fineTop coarseTop) :
    (appendTop fine fineTop).Refines
      (appendTop coarse coarseTop) := by
  intro j e
  cases j using Fin.lastCases with
  | last =>
      simp only [appendTop, Fin.lastCases_last]
      change OrderedFace k (r + 1) at e
      change fineTop e ≤ coarseTop e
      exact htop e
  | cast i =>
      simp only [appendTop, Fin.lastCases_castSucc]
      change OrderedFace k i.1 at e
      change fine.partition i e ≤ coarse.partition i e
      exact hfc i e

theorem withTopLayer_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r)
    (htop : OrderedFacePartitionRefines top C.topLayer) :
    (withTopLayer C top).Refines C := by
  intro j e
  cases j using Fin.lastCases with
  | last =>
      simp only [withTopLayer, Fin.lastCases_last]
      change OrderedFace k r at e
      change top e ≤ C.partition (Fin.last r) e
      exact htop e
  | cast i =>
      simp only [withTopLayer, Fin.lastCases_castSucc]
      exact le_rfl

end OrderedPartitionComplex

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

theorem complexity_orderedPatternTopPartition_le_two
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    (e : OrderedFace k r) :
    FacePartition.complexity
        (orderedPatternTopPartition H e) ≤ 2 := by
  simpa [orderedPatternTopPartition] using
    FacePartition.complexity_generatedBy_le
      ({H.edgeFinset e} :
        Finset (Finset (Fin r → G)))

theorem mem_of_mem_part_of_le_generatedBy_singleton
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P : FacePartition Ω} {S : Finset Ω}
    (hP : P ≤ FacePartition.generatedBy
      ({S} : Finset (Finset Ω)))
    {x y : Ω} (hx : x ∈ S) (hy : y ∈ P.part x) :
    y ∈ S := by
  have hyGenerated :
      y ∈
        (FacePartition.generatedBy
          ({S} : Finset (Finset Ω))).part x :=
    FacePartition.part_subset_of_le hP x hy
  have hsignature :=
    (FacePartition.mem_part_generatedBy_iff
      ({S} : Finset (Finset Ω)) x y).1 hyGenerated
  exact (hsignature S (by simp)).1 hx

theorem orderedPattern_edge_of_mem_refinedTopAtom
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {P : OrderedFacePartitionSystem G k r}
    (hP : OrderedFacePartitionRefines P
      (orderedPatternTopPartition H))
    (e : OrderedFace k r) {x y : Fin r → G}
    (hx : H.edge e x) (hy : y ∈ (P e).part x) :
    H.edge e y := by
  rw [← H.mem_edgeFinset e y]
  exact
    mem_of_mem_part_of_le_generatedBy_singleton
      (hP e)
      ((H.mem_edgeFinset e x).2 hx) hy

theorem orderedPatternTopPartition_refines_of_complex_refines_initial
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {C : OrderedPartitionComplex G k r}
    (hC : C.Refines (orderedPatternInitialComplex H)) :
    OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H) := by
  intro e
  change
    C.partition (Fin.last r) e ≤
      orderedPatternTopPartition H e
  rw [← orderedPatternInitialComplex_topLayer H]
  exact hC (Fin.last r) e

theorem ClosedOrderedAtomConfiguration.edge_of_mem_topAtom
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {C : OrderedPartitionComplex G k r}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k r C)
    (hA : H.IsOccurrence A.witness)
    (e : OrderedFace k r) (y : Fin r → G)
    (hy : y ∈ (A.atom (Fin.last r) e).1) :
    H.edge e y := by
  apply
    orderedPattern_edge_of_mem_refinedTopAtom
      H hC e (hA e)
  have hw :
      orderedFaceTuple e A.witness ∈
        (A.atom (Fin.last r) e).1 :=
    A.mem_atom (Fin.last r) e
  have hpart :
      (C.topLayer e).part
          (orderedFaceTuple e A.witness) =
        (A.atom (Fin.last r) e).1 := by
    exact
      (C.topLayer e).part_eq_of_mem
        (A.atom (Fin.last r) e).2 hw
  rwa [hpart]

theorem ClosedOrderedAtomConfiguration.isOccurrence_of_mem_topAtoms
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {C : OrderedPartitionComplex G k r}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k r C)
    (hA : H.IsOccurrence A.witness)
    (x : Fin k → G)
    (hx :
      ∀ e : OrderedFace k r,
        orderedFaceTuple e x ∈
          (A.atom (Fin.last r) e).1) :
    H.IsOccurrence x := by
  intro e
  exact A.edge_of_mem_topAtom H hC hA e
    (orderedFaceTuple e x) (hx e)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.CoarseAtomBridge
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedCoarseFineComplex

theorem coarseUpperFaceAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    0 ≤ P.coarseUpperFaceAtomEnergyGap j e := by
  apply sub_nonneg.mpr
  exact orderedAtomEnergy_mono
    (fun f => P.refines j.castSucc f)
    e (P.coarse.partition j.succ e)

theorem coarseUpperLayerAtomEnergyGap_eq_sum_face
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) :
    P.coarseUpperLayerAtomEnergyGap j =
      ∑ e : OrderedFace k (j.1 + 1),
        P.coarseUpperFaceAtomEnergyGap j e := by
  unfold coarseUpperLayerAtomEnergyGap
    coarseUpperFaceAtomEnergyGap
    orderedLayerAtomEnergy
  rw [Finset.sum_sub_distrib]
  rfl

end OrderedCoarseFineComplex

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.CoarseOrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable local instance orderedEnergyFaceLinearOrder_r2b3a8d_1
    (k r : ℕ) : LinearOrder (OrderedFace k r) :=
  (Fintype.equivFin (OrderedFace k r)).linearOrder
theorem mean_comp_orderedFaceTuple
    {G : Type*} [Fintype G] [Nonempty G]
    {k r : ℕ}
    (e : OrderedFace k r)
    (f : (Fin r → G) → ℝ) :
    mean (fun x : Fin k → G =>
      f (orderedFaceTuple e x)) = mean f := by
  rw [mean_splitOrderedFace e]
  unfold mean₂
  simp

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem finsetIndicator_biUnion_le_sum
    {ι Ω : Type*} [DecidableEq Ω]
    (s : Finset ι) (F : ι → Finset Ω) (x : Ω) :
    finsetIndicator (s.biUnion F) x ≤
      ∑ i ∈ s, finsetIndicator (F i) x := by
  by_cases hx : x ∈ s.biUnion F
  · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    rw [finsetIndicator_of_mem hx]
    calc
      1 = finsetIndicator (F i) x :=
        (finsetIndicator_of_mem hxi).symm
      _ ≤ ∑ j ∈ s, finsetIndicator (F j) x := by
        apply Finset.single_le_sum
          (s := s)
          (f := fun j => finsetIndicator (F j) x)
        · intro j hj
          by_cases hxj : x ∈ F j <;> simp [hxj]
        · exact hi
  · rw [finsetIndicator_of_not_mem hx]
    exact Finset.sum_nonneg fun i _ => by
      by_cases hxi : x ∈ F i <;> simp [hxi]

theorem mean_finsetIndicator_biUnion_le_sum
    {ι Ω : Type*} [DecidableEq Ω]
    [Fintype Ω]
    (s : Finset ι) (F : ι → Finset Ω) :
    mean (finsetIndicator (s.biUnion F)) ≤
      ∑ i ∈ s, mean (finsetIndicator (F i)) := by
  calc
    mean (finsetIndicator (s.biUnion F)) ≤
        mean (fun x => ∑ i ∈ s,
          finsetIndicator (F i) x) :=
      mean_mono (finsetIndicator_biUnion_le_sum s F)
    _ = ∑ i ∈ s, mean (finsetIndicator (F i)) :=
      mean_finset_sum s (fun i => finsetIndicator (F i))

theorem exists_orderedFace_factor_through
    {k s r : ℕ} (hsr : s ≤ r) (hrk : r ≤ k)
    (f : OrderedFace k s) :
    ∃ e : OrderedFace k r, ∃ d : OrderedFace r s,
      d.trans e = f := by
  classical
  let sf : Finset (Fin k) :=
    Finset.univ.map f.toEmbedding
  have hsf_card : sf.card = s := by
    rw [show sf.card =
        (Finset.univ : Finset (Fin s)).card by
      exact Finset.card_map f.toEmbedding]
    simp
  have hsf_univ : sf ⊆ Finset.univ :=
    Finset.subset_univ sf
  obtain ⟨t, hsf_t, _ht_univ, ht⟩ :=
    Finset.exists_subsuperset_card_eq
      hsf_univ
      (by simpa [hsf_card] using hsr)
      (by simpa using hrk)
  let e : OrderedFace k r :=
    t.orderEmbOfFin ht
  have hf_mem (i : Fin s) : f i ∈ t := by
    apply hsf_t
    exact Finset.mem_map.mpr
      ⟨i, Finset.mem_univ i, rfl⟩
  let ft : Fin s ↪o t :=
    OrderEmbedding.ofStrictMono
      (fun i => ⟨f i, hf_mem i⟩)
      (fun _ _ hij => f.strictMono hij)
  let d : OrderedFace r s :=
    ft.trans (t.orderIsoOfFin ht).symm.toOrderEmbedding
  refine ⟨e, d, ?_⟩
  apply RelEmbedding.ext
  intro i
  change
    t.orderEmbOfFin ht
        ((t.orderIsoOfFin ht).symm
          ⟨f i, hf_mem i⟩) =
      f i
  rw [← Finset.coe_orderIsoOfFin_apply]
  simp

theorem mean_indicator_orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G)) :
    mean (finsetIndicator
        (orderedFacePullbackFinset d S)) =
      mean (finsetIndicator S) := by
  rw [show
      finsetIndicator (orderedFacePullbackFinset d S) =
        fun y => finsetIndicator S
          (orderedFaceTuple d y) by
    funext y
    by_cases hy : orderedFaceTuple d y ∈ S
    · rw [finsetIndicator_of_mem hy,
        finsetIndicator_of_mem]
      exact
        (mem_orderedFacePullbackFinset d S y).2 hy
    · rw [finsetIndicator_of_not_mem hy,
        finsetIndicator_of_not_mem]
      exact fun h =>
        hy ((mem_orderedFacePullbackFinset d S y).1 h)]
  exact mean_comp_orderedFaceTuple d
    (finsetIndicator S)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.AdaptiveCoarseTargetRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

namespace AdaptiveCoarseTargetSchedule

namespace Landing

theorem index_lt_length {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    ∀ j, P.index j < P.length j := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | node chosen lower ih =>
      intro j
      cases j using Fin.lastCases with
      | last =>
          simp [index, length]
      | cast j =>
          simpa [index, length] using ih j

theorem tolerance_nonneg {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) (hS : S.IsAdmissible) :
    ∀ j n, 0 ≤ P.tolerance j n := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | @node r tolerance budget length next chosen lower ih =>
      rcases hS with ⟨htolerance, _hbudget, _hlength, hnext⟩
      intro j n
      cases j using Fin.lastCases with
      | last =>
          simpa using htolerance n
      | cast j =>
          simpa using ih (hnext chosen) j n

end Landing

theorem Realization.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (S : AdaptiveCoarseTargetSchedule k r)
    (hS : S.IsAdmissible) :
    Nonempty (Realization k r initial S) := by
  induction r with
  | zero =>
      cases S with
      | nil =>
          let landing :
              (AdaptiveCoarseTargetSchedule.nil :
                AdaptiveCoarseTargetSchedule k 0).Landing :=
            Landing.nil
          let certificate :
              CoarseTargetOrderedComplexRegularityCertificate
                G k 0 initial
                  landing.tolerance landing.budget landing.length := {
            index := landing.index
            coarse := initial
            fine := initial
            refines :=
              OrderedPartitionComplex.Refines.refl initial
            coarse_refines_initial :=
              OrderedPartitionComplex.Refines.refl initial
            coarse_topLayer_eq := rfl
            fine_topLayer_eq := rfl
            index_lt := fun j => Fin.elim0 j
            mixedRegular := fun j => Fin.elim0 j
            gap_nonneg := fun j => Fin.elim0 j
            gap_le := fun j => Fin.elim0 j
            coarse_complexity := fun j => Fin.elim0 j
            fine_complexity := fun j => Fin.elim0 j }
          exact ⟨{
            landing := landing
            certificate := certificate
            index_eq := rfl }⟩
  | succ r ih =>
      cases S with
      | @node _ tolerance budget length next =>
          rcases hS with
            ⟨htolerance, hbudget, hlength, hnext⟩
          let lowerInitial :
              OrderedFacePartitionSystem G k r :=
            initial.dropTop.topLayer
          let upper :
              OrderedFacePartitionSystem G k (r + 1) :=
            initial.topLayer
          let topChoice :=
            chosenFixedUpperLayerCoarseFine
              lowerInitial upper tolerance budget
              htolerance hbudget length hlength
          let chosen : Fin length :=
            ⟨topChoice.index, topChoice.index_lt⟩
          let prepared :
              OrderedPartitionComplex G k r :=
            initial.dropTop.withTopLayer topChoice.coarse
          obtain ⟨lowerRealization⟩ :=
            ih prepared (next chosen) (hnext chosen)
          let lowerLanding := lowerRealization.landing
          let lowerCertificate := lowerRealization.certificate
          have hindexLower :
              lowerCertificate.index = lowerLanding.index :=
            lowerRealization.index_eq
          let landing :
              (AdaptiveCoarseTargetSchedule.node
                tolerance budget length next).Landing :=
            Landing.node
              (tolerance := tolerance) (budget := budget)
              chosen lowerLanding
          let coarsePrefix :
              OrderedPartitionComplex G k r :=
            lowerCertificate.coarse
          let finePrefix :
              OrderedPartitionComplex G k r :=
            lowerCertificate.fine.withTopLayer topChoice.fine
          let coarse :
              OrderedPartitionComplex G k (r + 1) :=
            coarsePrefix.appendTop upper
          let fine :
              OrderedPartitionComplex G k (r + 1) :=
            finePrefix.appendTop upper
          have hlowerFineTop :
              lowerCertificate.fine.topLayer =
                topChoice.coarse := by
            calc
              lowerCertificate.fine.topLayer =
                  prepared.topLayer :=
                lowerCertificate.fine_topLayer_eq
              _ = topChoice.coarse :=
                OrderedPartitionComplex.topLayer_withTopLayer
                  initial.dropTop topChoice.coarse
          have hlowerCoarseTop :
              lowerCertificate.coarse.topLayer =
                topChoice.coarse := by
            calc
              lowerCertificate.coarse.topLayer =
                  prepared.topLayer :=
                lowerCertificate.coarse_topLayer_eq
              _ = topChoice.coarse :=
                OrderedPartitionComplex.topLayer_withTopLayer
                  initial.dropTop topChoice.coarse
          let certificate :
              CoarseTargetOrderedComplexRegularityCertificate
                G k (r + 1) initial
                  landing.tolerance landing.budget landing.length := {
            index := landing.index
            coarse := coarse
            fine := fine
            refines := by
              have hprefix :
                  finePrefix.Refines coarsePrefix := by
                intro q e
                cases q using Fin.lastCases with
                | last =>
                    simp only [finePrefix, coarsePrefix,
                      OrderedPartitionComplex.withTopLayer,
                      Fin.lastCases_last]
                    change OrderedFace k r at e
                    have heq :
                        lowerCertificate.coarse.partition
                            (Fin.last r) e =
                          topChoice.coarse e :=
                      congrFun hlowerCoarseTop e
                    rw [heq]
                    exact topChoice.refines e
                | cast i =>
                    simp only [finePrefix, coarsePrefix,
                      OrderedPartitionComplex.withTopLayer,
                      Fin.lastCases_castSucc]
                    exact lowerCertificate.refines
                      i.castSucc e
              exact OrderedPartitionComplex.appendTop_refines
                hprefix
                (OrderedFacePartitionRefines.refl upper)
            coarse_refines_initial := by
              have hprepared :
                  prepared.Refines initial.dropTop := by
                exact
                  OrderedPartitionComplex.withTopLayer_refines
                    initial.dropTop topChoice.coarse
                    (by
                      simpa only [lowerInitial] using
                        topChoice.coarse_refines_initial)
              have hprefix :
                  coarsePrefix.Refines initial.dropTop :=
                OrderedPartitionComplex.Refines.trans
                  lowerCertificate.coarse_refines_initial
                  hprepared
              have happend :=
                OrderedPartitionComplex.appendTop_refines
                  hprefix
                  (OrderedFacePartitionRefines.refl upper)
              simpa [coarse, coarsePrefix, upper] using happend
            coarse_topLayer_eq := by
              simp [coarse, upper]
            fine_topLayer_eq := by
              simp [fine, upper]
            index_lt := by
              exact landing.index_lt_length
            mixedRegular := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.appendTop_partition_last,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last, Fin.succ_last]
                  change
                    IsPreliminaryOrderedRegular
                      topChoice.fine upper
                      (landing.tolerance (Fin.last r)
                        (landing.index (Fin.last r)))
                  simpa [landing, chosen] using
                    topChoice.fine_regular
              | cast i =>
                  have hregular :=
                    lowerCertificate.mixedRegular i
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  change
                    @IsPreliminaryOrderedRegular
                      G _ _ k i.1
                      (lowerCertificate.fine.partition
                        i.castSucc)
                      (lowerCertificate.coarse.partition
                        i.succ)
                      (landing.tolerance i.castSucc
                        (landing.index i.castSucc))
                  rw [show landing.tolerance i.castSucc =
                      lowerLanding.tolerance i by
                        simp [landing]]
                  rw [show landing.index i.castSucc =
                      lowerLanding.index i by
                        simp [landing]]
                  rw [← congrFun hindexLower i]
                  exact hregular
            gap_nonneg := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  have hgap := topChoice.gap_nonneg
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.appendTop_partition_last,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last, Fin.succ_last]
                  change
                    0 ≤
                      orderedLayerAtomEnergy
                          topChoice.fine upper -
                        orderedLayerAtomEnergy
                          lowerCertificate.coarse.topLayer
                          upper
                  rw [hlowerCoarseTop]
                  exact hgap
              | cast i =>
                  have hgap :=
                    lowerCertificate.gap_nonneg i
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  convert hgap using 1
            gap_le := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  have hgap := topChoice.gap_le
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.appendTop_partition_last,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last, Fin.succ_last]
                  change
                    orderedLayerAtomEnergy
                          topChoice.fine upper -
                        orderedLayerAtomEnergy
                          lowerCertificate.coarse.topLayer
                          upper ≤
                      (Fintype.card
                        (OrderedFace k (r + 1)) : ℝ) /
                          (landing.length (Fin.last r) : ℝ)
                  rw [hlowerCoarseTop]
                  simpa [landing] using hgap
              | cast i =>
                  have hgap :=
                    lowerCertificate.gap_le i
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  change
                    orderedLayerAtomEnergy
                          (lowerCertificate.fine.partition
                            i.castSucc)
                          (lowerCertificate.coarse.partition
                            i.succ) -
                        orderedLayerAtomEnergy
                          (lowerCertificate.coarse.partition
                            i.castSucc)
                          (lowerCertificate.coarse.partition
                            i.succ) ≤
                      (Fintype.card
                        (OrderedFace k (i.1 + 1)) : ℝ) /
                          (landing.length i.castSucc : ℝ)
                  rw [show landing.length i.castSucc =
                      lowerLanding.length i by
                        simp [landing]]
                  exact hgap
            coarse_complexity := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  intro e
                  change OrderedFace k r at e
                  have hcomplexity :=
                    topChoice.coarse_complexity e
                  simp only [coarse, coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc]
                  change
                    FacePartition.complexity
                        (lowerCertificate.coarse.partition
                          (Fin.last r) e) ≤
                      fixedUpperLayerComplexityFactor
                          r (landing.budget (Fin.last r))
                          (landing.index (Fin.last r)) *
                        FacePartition.complexity
                          (initial.partition
                            (Fin.last r).castSucc e)
                  have heq :
                      lowerCertificate.coarse.partition
                          (Fin.last r) e =
                        topChoice.coarse e :=
                    congrFun hlowerCoarseTop e
                  rw [heq]
                  simp only [landing, chosen,
                    Landing.budget_node_last,
                    Landing.index_node_last]
                  convert hcomplexity using 1; rfl
              | cast i =>
                  intro e
                  change OrderedFace k i.1 at e
                  have hcomplexity :=
                    lowerCertificate.coarse_complexity i e
                  simp only [coarse, coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc]
                  change
                    FacePartition.complexity
                        (lowerCertificate.coarse.partition
                          i.castSucc e) ≤
                      fixedUpperLayerComplexityFactor
                          i.1 (landing.budget i.castSucc)
                          (landing.index i.castSucc) *
                        FacePartition.complexity
                          (initial.partition
                            i.castSucc.castSucc e)
                  rw [show landing.budget i.castSucc =
                      lowerLanding.budget i by
                        simp [landing]]
                  rw [show landing.index i.castSucc =
                      lowerLanding.index i by
                        simp [landing]]
                  rw [← congrFun hindexLower i]
                  simp only [prepared,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc,
                    OrderedPartitionComplex.dropTop] at hcomplexity
                  convert hcomplexity using 1
            fine_complexity := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  intro e
                  change OrderedFace k r at e
                  have hcomplexity :=
                    topChoice.fine_complexity e
                  simp only [fine, finePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last]
                  change
                    FacePartition.complexity
                        (topChoice.fine e) ≤
                      fixedUpperLayerComplexityFactor
                          r (landing.budget (Fin.last r))
                          (landing.index (Fin.last r) + 1) *
                        FacePartition.complexity
                          (initial.partition
                            (Fin.last r).castSucc e)
                  simp only [landing, chosen,
                    Landing.budget_node_last,
                    Landing.index_node_last]
                  convert hcomplexity using 1
                  rfl
              | cast i =>
                  intro e
                  change OrderedFace k i.1 at e
                  have hcomplexity :=
                    lowerCertificate.fine_complexity i e
                  simp only [fine, finePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc]
                  change
                    FacePartition.complexity
                        (lowerCertificate.fine.partition
                          i.castSucc e) ≤
                      fixedUpperLayerComplexityFactor
                          i.1 (landing.budget i.castSucc)
                          (landing.index i.castSucc + 1) *
                        FacePartition.complexity
                          (initial.partition
                            i.castSucc.castSucc e)
                  rw [show landing.budget i.castSucc =
                      lowerLanding.budget i by
                        simp [landing]]
                  rw [show landing.index i.castSucc =
                      lowerLanding.index i by
                        simp [landing]]
                  rw [← congrFun hindexLower i]
                  simp only [prepared,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc,
                    OrderedPartitionComplex.dropTop] at hcomplexity
                  convert hcomplexity using 1 }
          exact ⟨{
            landing := landing
            certificate := certificate
            index_eq := rfl }⟩

theorem exists_landing_certificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (S : AdaptiveCoarseTargetSchedule k r)
    (hS : S.IsAdmissible) :
    ∃ P : S.Landing,
      ∃ R :
          CoarseTargetOrderedComplexRegularityCertificate
            G k r initial P.tolerance P.budget P.length,
        R.index = P.index := by
  obtain ⟨realization⟩ :=
    Realization.nonempty initial S hS
  exact
    ⟨realization.landing, realization.certificate,
      realization.index_eq⟩

end AdaptiveCoarseTargetSchedule

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedConfigurationCounting
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace PositiveOrderedFace

theorem boundary_rank_lt
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    (e.boundary hpos i).rank < e.rank := by
  simp only [rank, boundary_lowerRank]
  omega

end PositiveOrderedFace

theorem configurationFaceWeight_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    0 ≤ configurationFaceWeight A e y :=
  partitionAtomIndicator_nonneg _ _ _

theorem configurationFaceWeight_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    configurationFaceWeight A e y ≤ 1 :=
  partitionAtomIndicator_le_one _ _ _

theorem partialConfigurationWeight_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (x : Fin k → G) :
    partialConfigurationWeight A s x ≤ 1 := by
  unfold partialConfigurationWeight
  apply Finset.prod_le_one
  · intro e he
    exact configurationFaceWeight_nonneg A e _
  · intro e he
    exact configurationFaceWeight_le_one A e _

theorem coarse_boundary_mem_of_boundary_weight_ne_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1))
    (x : Fin k → G)
    (hweight :
      configurationFaceWeight A (e.boundary hpos i)
          (orderedFaceTuple (e.boundary hpos i).face x) ≠
        0) :
    eraseBoundaryCoordinate i (orderedFaceTuple e.face x) ∈
      (positiveFaceLowerLayer P.coarse e
        (eraseBoundaryFace e.face i)).part
        (eraseBoundaryCoordinate i
          (orderedFaceTuple e.face A.witness)) := by
  rcases e with ⟨⟨n, hn⟩, eface⟩
  cases n with
  | zero =>
      simp at hpos
  | succ n =>
      let f :=
        (⟨⟨n, by omega⟩,
            eraseBoundaryFace eface i⟩ :
          PositiveOrderedFace k r)
      have hfine :
          orderedFaceTuple f.face x ∈
            (A.atom f.lowerRank.succ f.face).1 := by
        by_contra hnot
        exact hweight
          (partitionAtomIndicator_of_not_mem
            (P.fine.partition f.lowerRank.succ f.face)
            (A.atom f.lowerRank.succ f.face) hnot)
      have hcanonical :
          (A.atom f.lowerRank.succ f.face).1 =
            (P.fine.partition f.lowerRank.succ f.face).part
              (orderedFaceTuple f.face A.witness) := by
        exact congrArg Subtype.val
          (A.atom_eq_partitionAtomAt
            f.lowerRank.succ f.face)
      rw [hcanonical] at hfine
      have hcoarse :
          orderedFaceTuple f.face x ∈
            (P.coarse.partition f.lowerRank.succ f.face).part
              (orderedFaceTuple f.face A.witness) :=
        FacePartition.part_subset_of_le
          (P.refines f.lowerRank.succ f.face)
          (orderedFaceTuple f.face A.witness) hfine
      let j : Fin (r + 1) :=
        ⟨n + 1, Nat.lt_succ_of_lt hn⟩
      have hfj : f.lowerRank.succ = j := by
        apply Fin.ext
        rfl
      have hcoarse' :
          orderedFaceTuple f.face x ∈
            (P.coarse.partition j f.face).part
              (orderedFaceTuple f.face A.witness) := by
        subst j
        exact hcoarse
      simpa [f, j, positiveFaceLowerLayer,
        OrderedPartitionComplex.layer] using hcoarse'

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.ConfigurationWeightedDefect
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem mixedConfigurationFaceWeight_decompose
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    configurationFaceWeight A e y =
      mixedConfigurationCoarseDensity P A e +
        mixedConfigurationDefect P A e y +
        mixedConfigurationUniform P A e y := by
  unfold mixedConfigurationDefect mixedConfigurationUniform
  ring

theorem coarse_boundary_mem_of_coarse_configuration_weight_ne_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1))
    (x : Fin k → G)
    (hweight :
      configurationFaceWeight A (e.boundary hpos i)
          (orderedFaceTuple (e.boundary hpos i).face x) ≠
        0) :
    eraseBoundaryCoordinate i (orderedFaceTuple e.face x) ∈
      (positiveFaceLowerLayer P.coarse e
        (eraseBoundaryFace e.face i)).part
        (eraseBoundaryCoordinate i
          (orderedFaceTuple e.face A.witness)) := by
  exact
    coarse_boundary_mem_of_boundary_weight_ne_zero
      P.coarseDiagonal A e hpos i x hweight

theorem mixedConfigurationFace_isFaceCutRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (e : PositiveOrderedFace k r) :
    (⟨orderedBoundaryPartition
        (positiveFaceLowerLayer P.fine e) e.face⟩ :
      FaceRegularityState
        (Fin (e.lowerRank.1 + 1) → G)).IsFaceCutRegular
      (partitionAtomIndicator
        (P.coarse.partition e.lowerRank.succ e.face)
        (A.atom e.lowerRank.succ e.face))
      (τ e.lowerRank) := by
  rw [positiveFaceLowerLayer]
  exact
    (hregular e.lowerRank).toBounded
      e.face
      (A.atom e.lowerRank.succ e.face)

theorem mixedConfigurationDefect_mul_boundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    mixedConfigurationDefect P A e y *
        mixedConfigurationBoundaryIndicator P A e y =
      orderedAtomBoundaryDefect
          (positiveFaceLowerLayer P.fine e)
          (positiveFaceLowerLayer P.coarse e)
          e.face
          (P.coarse.partition e.lowerRank.succ e.face)
          (A.atom e.lowerRank.succ e.face) y *
        mixedConfigurationBoundaryIndicator P A e y := by
  let Q :=
    orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face
  let b : Q.parts :=
    orderedBoundaryAtomAt
      (positiveFaceLowerLayer P.coarse e) e.face
      (orderedFaceTuple e.face A.witness)
  let f :
      (Fin (e.lowerRank.1 + 1) → G) → ℝ :=
    partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face)
  by_cases hy : y ∈ b.1
  · have hcoarse :
        conditionalMean Q f y =
          conditionalMean Q f
            (orderedFaceTuple e.face A.witness) := by
      exact conditionalMean_eq_of_mem_part Q f hy
    rw [mixedConfigurationBoundaryIndicator,
      partitionAtomIndicator_of_mem _ _ hy,
      mul_one, mul_one]
    change
      conditionalMean
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.fine e) e.face)
            f y -
          conditionalMean Q f
            (orderedFaceTuple e.face A.witness) =
        conditionalMean
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.fine e) e.face)
            f y -
          conditionalMean Q f y
    rw [hcoarse]
  · rw [mixedConfigurationBoundaryIndicator,
      partitionAtomIndicator_of_not_mem _ _ hy,
      mul_zero, mul_zero]

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleFiltration
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

theorem doubledVertexLift_injective
    (g₀ : Finset K) (copy : Bool) :
    Function.Injective (doubledVertexLift g₀ copy) := by
  intro v w hvw
  have h :=
    congrArg (doubledVertexForget g₀) hvw
  simpa using h

theorem mean_splitDoubledAssignment
    [Fintype K] [Fintype G]
    (g₀ : Finset K)
    (f : (DoubledOccurrenceVertex g₀ → G) → ℝ) :
    mean f =
      mean₂ (fun y : {v : K // v ∈ g₀} → G =>
        fun z :
          (EdgeComplement g₀ → G) ×
            (EdgeComplement g₀ → G) =>
          f (doubledAssignment g₀ y z)) := by
  calc
    mean f =
        mean (fun p :
          ({v : K // v ∈ g₀} → G) ×
            ((EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G)) =>
          f ((splitDoubledAssignmentEquiv g₀).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv
        (splitDoubledAssignmentEquiv g₀)
      intro x
      simp
    _ = _ := by
      change
        mean (fun p :
          ({v : K // v ∈ g₀} → G) ×
            ((EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G)) =>
          f (doubledAssignment g₀ p.1 p.2)) =
        _
      exact
        mean_prod_type
          (fun y : {v : K // v ∈ g₀} → G =>
            fun z :
              (EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G) =>
              f (doubledAssignment g₀ y z))

@[simp]
theorem card_doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).card = g.card := by
  rw [doubledEdge,
    Finset.card_image_of_injective _
      (doubledVertexLift_injective g₀ copy)]

theorem doubledEdge_copy_independent_of_subset
    (g₀ : Finset K) {g : Finset K}
    (hg : g ⊆ g₀) (copy copy' : Bool) :
    doubledEdge g₀ copy g =
      doubledEdge g₀ copy' g := by
  unfold doubledEdge
  apply Finset.image_congr
  intro v hv
  simp [doubledVertexLift, hg hv]

theorem doubledEdge_false_ne_true_of_mem_complement
    (g₀ : Finset K) {g : Finset K}
    {v : K} (hvg : v ∈ g) (hvoutside : v ∉ g₀) :
    doubledEdge g₀ false g ≠
      doubledEdge g₀ true g := by
  intro hedges
  have hv :
      doubledVertexLift g₀ false v ∈
        doubledEdge g₀ true g := by
    rw [← hedges]
    exact mem_doubledEdge g₀ false g v hvg
  obtain ⟨w, hwg, hwv⟩ :=
    Finset.mem_image.mp hv
  have hwv' : w = v := by
    have := congrArg
      (doubledVertexForget g₀) hwv
    simpa using this
  subst w
  simp [doubledVertexLift, hvoutside] at hwv

theorem doubledEdge_false_eq_true_iff_subset
    (g₀ : Finset K) (g : Finset K) :
    doubledEdge g₀ false g =
        doubledEdge g₀ true g ↔
      g ⊆ g₀ := by
  constructor
  · intro hedges v hvg
    by_contra hvoutside
    exact
      doubledEdge_false_ne_true_of_mem_complement
        g₀ hvg hvoutside hedges
  · intro hg
    exact doubledEdge_copy_independent_of_subset
      g₀ hg false true

theorem doubledSourceProduct_doubledAssignment
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    B.doubledSourceProduct g₀ A
        (doubledAssignment g₀ y z) =
      B.edgeRemainderFiber g₀ A y z.1 *
        B.edgeRemainderFiber g₀ A y z.2 := by
  classical
  unfold doubledSourceProduct
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  simp_rw [doubledAssignment_lift_true,
    doubledAssignment_lift_false]
  have hfalse :
      (∏ g : {g : Finset K //
          g ∈ B.edges.erase g₀},
        A g.1 (fun v =>
          (splitEdgeEquiv g₀).symm
            (y, z.1) v.1)) =
        ∏ g ∈ B.edges.erase g₀,
          A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.1))) := by
    calc
      _ = ∏ g : {g : Finset K //
            g ∈ B.edges.erase g₀},
          A g.1 (edgeTuple g.1
            ((splitEdgeEquiv g₀).symm
              (y, z.1))) := by
        apply Finset.prod_congr rfl
        intro g _hg
        apply congrArg (A g.1)
        rfl
      _ = _ :=
        Finset.prod_coe_sort
          (B.edges.erase g₀)
          (fun g => A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.1))))
  have htrue :
      (∏ g : {g : Finset K //
          g ∈ B.edges.erase g₀},
        A g.1 (fun v =>
          (splitEdgeEquiv g₀).symm
            (y, z.2) v.1)) =
        ∏ g ∈ B.edges.erase g₀,
          A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.2))) := by
    calc
      _ = ∏ g : {g : Finset K //
            g ∈ B.edges.erase g₀},
          A g.1 (edgeTuple g.1
            ((splitEdgeEquiv g₀).symm
              (y, z.2))) := by
        apply Finset.prod_congr rfl
        intro g _hg
        apply congrArg (A g.1)
        rfl
      _ = _ :=
        Finset.prod_coe_sort
          (B.edges.erase g₀)
          (fun g => A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.2))))
  rw [htrue, hfalse]
  unfold edgeRemainderFiber edgeRemainder bundleProduct
  rw [mul_comm]
  rfl

theorem doubledRemainderMoment_eq_mean_doubledSourceProduct
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.doubledRemainderMoment g₀ A =
      mean (B.doubledSourceProduct g₀ A) := by
  rw [B.doubledRemainderMoment_eq_mean₂_pair]
  rw [mean_splitDoubledAssignment]
  simp_rw [B.doubledSourceProduct_doubledAssignment]

theorem duplicateOutside_edge_card
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ∈ (B.duplicateOutside g₀).edges) :
    ∃ g ∈ B.edges.erase g₀, d.card = g.card := by
  obtain ⟨copy, g, hg, hgd⟩ :=
    (B.mem_doubledEdges_iff g₀ d).1 hd
  subst d
  exact ⟨g, hg, card_doubledEdge g₀ copy g⟩

theorem duplicateOutside_order_le_eraseEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).order ≤
      (B.eraseEdge g₀).order := by
  unfold order
  apply Finset.sup_le
  intro d hd
  obtain ⟨g, hg, hdg⟩ :=
    B.duplicateOutside_edge_card g₀ hd
  rw [hdg]
  exact (B.eraseEdge g₀).edge_card_le_order hg

theorem duplicateOutside_order_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).order ≤ B.order :=
  (B.duplicateOutside_order_le_eraseEdge g₀).trans
    (B.eraseEdge_order_le g₀)

theorem card_doubledEdges_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.doubledEdges g₀).card ≤
      2 * (B.edges.erase g₀).card := by
  unfold doubledEdges
  calc
    (Finset.univ.image
        (B.doubledEdgeOfSource g₀)).card ≤
        (Finset.univ :
          Finset (B.DoubledEdgeSource g₀)).card :=
      Finset.card_image_le
    _ = 2 * (B.edges.erase g₀).card := by
      simp [DoubledEdgeSource]

theorem doubledEdge_image_forget_of_subset
    (g₀ : Finset K) (copy : Bool)
    {g : Finset K}
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ⊆ doubledEdge g₀ copy g) :
    doubledEdge g₀ copy
        (d.image (doubledVertexForget g₀)) = d := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp hw
    have huLift :
        doubledVertexLift g₀ copy
            (doubledVertexForget g₀ u) = u := by
      obtain ⟨t, ht, rfl⟩ :=
        Finset.mem_image.mp (hd hu)
      simp
    rw [← hwv, ← huw, huLift]
    exact hu
  · intro hv
    have hvLift :
        doubledVertexLift g₀ copy
            (doubledVertexForget g₀ v) = v := by
      obtain ⟨t, ht, rfl⟩ :=
        Finset.mem_image.mp (hd hv)
      simp
    exact Finset.mem_image.mpr
      ⟨doubledVertexForget g₀ v,
        Finset.mem_image.mpr ⟨v, hv, rfl⟩,
        hvLift⟩

theorem duplicateOutside_closed
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (hclosed :
      (B.eraseEdge g₀).IsClosedUnderInclusion) :
    (B.duplicateOutside g₀).IsClosedUnderInclusion := by
  intro d hd f hfd
  obtain ⟨copy, g, hg, rfl⟩ :=
    (B.mem_doubledEdges_iff g₀ d).1 hd
  let h : Finset K :=
    f.image (doubledVertexForget g₀)
  have hhg : h ⊆ g := by
    intro v hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, huw⟩ :=
      Finset.mem_image.mp (hfd hw)
    rw [← hwv, ← huw]
    simpa using hu
  have hh : h ∈ B.edges.erase g₀ :=
    hclosed hg hhg
  have hlift :
      doubledEdge g₀ copy h = f :=
    doubledEdge_image_forget_of_subset
      g₀ copy hfd
  rw [← hlift]
  exact
    (B.mem_doubledEdges_iff g₀
      (doubledEdge g₀ copy h)).2
      ⟨copy, h, hh, rfl⟩

theorem duplicateOutside_closed_of_maximal
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card) :
    (B.duplicateOutside g₀).IsClosedUnderInclusion :=
  B.duplicateOutside_closed g₀
    (B.eraseEdge_closed_of_maximal
      hclosed hg₀ hmax)

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

theorem card_filterEdges_edges_le
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).edges.card ≤ B.edges.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem filterEdges_closed
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (hclosed : B.IsClosedUnderInclusion)
    (hP : ∀ ⦃g⦄, P g →
      ∀ ⦃f⦄, f ⊆ g → P f) :
    (B.filterEdges P).IsClosedUnderInclusion := by
  intro g hg f hfg
  have hg' := (B.mem_filterEdges_edges P g).1 hg
  exact (B.mem_filterEdges_edges P f).2
    ⟨hclosed hg'.1 hfg, hP hg'.2 hfg⟩

theorem lowerOrder_order_lt
    (B : HypergraphBundle J K H)
    {d : ℕ} (hd : 0 < d) :
    (B.lowerOrder d).order < d := by
  unfold order
  rw [Finset.sup_lt_iff hd]
  intro g hg
  exact (Finset.mem_filter.mp hg).2

theorem card_lowerOrder_edges_le
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges.card ≤ B.edges.card :=
  B.card_filterEdges_edges_le _

theorem lowerOrder_closed
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (d : ℕ) :
    (B.lowerOrder d).IsClosedUnderInclusion := by
  apply B.filterEdges_closed _ hclosed
  intro g hg f hfg
  exact (Finset.card_le_card hfg).trans_lt hg

theorem strictBoundary_order_lt
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀.Nonempty) :
    (B.strictBoundary g₀).order < g₀.card := by
  unfold order
  rw [Finset.sup_lt_iff (Finset.card_pos.mpr hg₀)]
  intro g hg
  exact Finset.card_lt_card (Finset.mem_filter.mp hg).2

theorem card_strictBoundary_edges_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges.card ≤ B.edges.card :=
  B.card_filterEdges_edges_le _

theorem strictBoundary_closed
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (g₀ : Finset K) :
    (B.strictBoundary g₀).IsClosedUnderInclusion := by
  apply B.filterEdges_closed _ hclosed
  intro g hg f hfg
  exact lt_of_le_of_lt hfg hg

theorem bundleMainProduct_eraseEdge_mul
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges) :
    (B.eraseEdge g₀).bundleMainProduct p *
        p (g₀.image B.projection) =
      B.bundleMainProduct p := by
  classical
  unfold bundleMainProduct
  simp only [eraseEdge]
  rw [Finset.prod_erase_mul _ _ hg₀]

theorem doubledEdge_injective
    (g₀ : Finset K) (copy : Bool) :
    Function.Injective (doubledEdge g₀ copy) := by
  intro g h hgh
  have himage :=
    congrArg
      (Finset.image (doubledVertexForget g₀)) hgh
  simpa using himage

theorem doubledEdges_eq_image_union
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    B.doubledEdges g₀ =
      (B.edges.erase g₀).image
          (doubledEdge g₀ false) ∪
        (B.edges.erase g₀).image
          (doubledEdge g₀ true) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    cases copy
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  · intro hd
    rcases Finset.mem_union.mp hd with hd | hd
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hd
      exact (B.mem_doubledEdges_iff g₀ _).2
        ⟨false, g, hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hd
      exact (B.mem_doubledEdges_iff g₀ _).2
        ⟨true, g, hg, rfl⟩

theorem image_true_sdiff_image_false
    (g₀ : Finset K) (s : Finset (Finset K)) :
    s.image (doubledEdge g₀ true) \
        s.image (doubledEdge g₀ false) =
      (s.filter fun g => ¬ g ⊆ g₀).image
        (doubledEdge g₀ true) := by
  classical
  ext d
  constructor
  · intro hd
    have hdtrue :
        d ∈ s.image (doubledEdge g₀ true) :=
      (Finset.mem_sdiff.mp hd).1
    obtain ⟨g, hg, hgd⟩ :=
      Finset.mem_image.mp hdtrue
    subst d
    apply Finset.mem_image.mpr
    refine ⟨g, Finset.mem_filter.mpr ⟨hg, ?_⟩, rfl⟩
    intro hgsub
    apply (Finset.mem_sdiff.mp hd).2
    apply Finset.mem_image.mpr
    refine ⟨g, hg, ?_⟩
    exact
      (doubledEdge_copy_independent_of_subset
        g₀ hgsub false true)
  · intro hd
    obtain ⟨g, hg, hgd⟩ :=
      Finset.mem_image.mp hd
    subst d
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_image.mpr
      ⟨g, (Finset.mem_filter.mp hg).1, rfl⟩, ?_⟩
    intro hfalse
    obtain ⟨h, hh, hhg⟩ :=
      Finset.mem_image.mp hfalse
    have hgh : h = g := by
      have himage :=
        congrArg
          (Finset.image (doubledVertexForget g₀)) hhg
      simpa using himage
    subst h
    exact (Finset.mem_filter.mp hg).2
      ((doubledEdge_false_eq_true_iff_subset
        g₀ g).1 hhg)

theorem prod_image_doubledEdge_main
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (copy : Bool)
    (s : Finset (Finset K))
    (p : Finset J → ℝ) :
    (∏ d ∈ s.image (doubledEdge g₀ copy),
        p (d.image (B.doubledProjection g₀))) =
      ∏ g ∈ s, p (g.image B.projection) := by
  classical
  rw [Finset.prod_image
    (doubledEdge_injective g₀ copy).injOn]
  simp

theorem bundleMainProduct_duplicateOutside
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    (B.duplicateOutside g₀).bundleMainProduct p =
      (∏ g ∈ (B.edges.erase g₀).filter
          (fun g => g ⊆ g₀),
        p (g.image B.projection)) *
      ∏ g ∈ (B.edges.erase g₀).filter
          (fun g => ¬ g ⊆ g₀),
        (p (g.image B.projection)) ^ 2 := by
  classical
  let s := B.edges.erase g₀
  let first :=
    s.image (doubledEdge g₀ false)
  let second :=
    s.image (doubledEdge g₀ true)
  have hsplit :
      (∏ g ∈ s.filter (fun g => g ⊆ g₀),
          p (g.image B.projection)) *
          (∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            p (g.image B.projection)) =
        ∏ g ∈ s, p (g.image B.projection) :=
    Finset.prod_filter_mul_prod_filter_not
      s (fun g => g ⊆ g₀)
        (fun g => p (g.image B.projection))
  calc
    (B.duplicateOutside g₀).bundleMainProduct p =
        ∏ d ∈ first ∪ second,
          p (d.image (B.doubledProjection g₀)) := by
      unfold bundleMainProduct first second
      simp only [duplicateOutside_edges,
        duplicateOutside_projection]
      rw [B.doubledEdges_eq_image_union g₀]
    _ = ∏ d ∈ first ∪ (second \ first),
          p (d.image (B.doubledProjection g₀)) := by
      rw [Finset.union_sdiff_self_eq_union]
    _ =
        (∏ d ∈ first,
          p (d.image (B.doubledProjection g₀))) *
        ∏ d ∈ second \ first,
          p (d.image (B.doubledProjection g₀)) := by
      exact Finset.prod_union Finset.disjoint_sdiff
    _ =
        (∏ g ∈ s, p (g.image B.projection)) *
        ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
          p (g.image B.projection) := by
      unfold first second
      rw [image_true_sdiff_image_false]
      rw [B.prod_image_doubledEdge_main g₀ false]
      rw [B.prod_image_doubledEdge_main g₀ true]
    _ =
        ((∏ g ∈ s.filter (fun g => g ⊆ g₀),
            p (g.image B.projection)) *
          ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            p (g.image B.projection)) *
        ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
          p (g.image B.projection) := by
      rw [hsplit]
    _ =
        (∏ g ∈ s.filter (fun g => g ⊆ g₀),
            p (g.image B.projection)) *
          ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            (p (g.image B.projection)) ^ 2 := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      simp only [pow_two]
    _ = _ := rfl

theorem bundleMainProduct_duplicateOutside_lowerOrder
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct p =
      (B.strictBoundary g₀).bundleMainProduct p *
      ∏ g ∈ B.edges.filter
          (fun g => g.card < g₀.card ∧ ¬ g ⊆ g₀),
        (p (g.image B.projection)) ^ 2 := by
  classical
  rw [(B.lowerOrder g₀.card).bundleMainProduct_duplicateOutside g₀ p]
  have hg₀' :
      g₀ ∉ B.edges.filter (fun g => g.card < g₀.card) := by
    simp
  have hboundary :
      (B.edges.filter (fun g => g.card < g₀.card)).filter
          (fun g => g ⊆ g₀) =
        B.edges.filter (fun g => g ⊂ g₀) := by
    ext g
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hgB, hgcard⟩, hgsub⟩
      exact ⟨hgB,
        Finset.ssubset_iff_subset_ne.mpr
          ⟨hgsub, fun hgeq => by
            subst g
            exact (Nat.lt_irrefl _ hgcard)⟩⟩
    · rintro ⟨hgB, hgstrict⟩
      exact ⟨⟨hgB,
        Finset.card_lt_card hgstrict⟩, hgstrict.1⟩
  have hexterior :
      (B.edges.filter (fun g => g.card < g₀.card)).filter
          (fun g => ¬ g ⊆ g₀) =
        B.edges.filter
          (fun g => g.card < g₀.card ∧ ¬ g ⊆ g₀) := by
    ext g
    simp only [Finset.mem_filter]
    tauto
  simp only [lowerOrder, strictBoundary,
    filterEdges, bundleMainProduct]
  rw [Finset.erase_eq_of_notMem hg₀',
    hboundary, hexterior]

end HypergraphBundle

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleEnvelopeSelection
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

theorem cast_finsetPi_apply
    {α G' : Type*} {s t : Finset α} (h : s = t)
    (f : {a : α // a ∈ s} → G')
    (a : {a : α // a ∈ t}) :
    cast
        (congrArg
          (fun u : Finset α =>
            ({a : α // a ∈ u} → G'))
          h)
        f a =
      f ((finsetMembershipEquivOfEq h).symm a) := by
  subst t
  rfl

theorem prod_comp_eq_prod_image_of_idempotent
    {α β M : Type*} [DecidableEq β]
    [CommMonoid M]
    (s : Finset α) (f : α → β) (w : β → M)
    (hw : ∀ b ∈ s.image f, w b * w b = w b) :
    (∏ a ∈ s, w (f a)) =
      ∏ b ∈ s.image f, w b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hw' :
          ∀ b ∈ s.image f, w b * w b = w b := by
        intro b hb
        exact hw b (by
          rw [Finset.image_insert]
          exact Finset.mem_insert_of_mem hb)
      rw [Finset.prod_insert ha, ih hw',
        Finset.image_insert]
      by_cases hfa : f a ∈ s.image f
      · rw [Finset.insert_eq_of_mem hfa]
        calc
          w (f a) * ∏ b ∈ s.image f, w b =
              w (f a) *
                (w (f a) *
                  ∏ b ∈ (s.image f).erase (f a), w b) := by
            rw [Finset.mul_prod_erase (s.image f) w hfa]
          _ =
              w (f a) *
                ∏ b ∈ (s.image f).erase (f a), w b := by
            rw [← mul_assoc,
              hw (f a) (by
                rw [Finset.image_insert]
                exact Finset.mem_insert_self _ _)]
          _ = ∏ b ∈ s.image f, w b :=
            Finset.mul_prod_erase (s.image f) w hfa
      · rw [Finset.prod_insert hfa]

theorem pullbackBaseEdgeWeight_duplicateOutside_doubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (copy : Bool) {g : Finset K}
    (hg : g ∈ B.edges.erase g₀)
    (x : DoubledOccurrenceVertex g₀ → G) :
    (B.duplicateOutside g₀).pullbackBaseEdgeWeight A
        (doubledEdge g₀ copy g)
        (edgeTuple (doubledEdge g₀ copy g) x) =
      B.pullbackBaseEdgeWeight A g
        (fun v => x (doubledVertexLift g₀ copy v.1)) := by
  classical
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have hd :
      doubledEdge g₀ copy g ∈
        (B.duplicateOutside g₀).edges := by
    exact
      (B.mem_doubledEdges_iff g₀
        (doubledEdge g₀ copy g)).2
        ⟨copy, g, hg, rfl⟩
  rw [(B.duplicateOutside g₀).pullbackBaseEdgeWeight_of_mem
      A hd,
    B.pullbackBaseEdgeWeight_of_mem A hgB]
  have himage :
      (doubledEdge g₀ copy g).image
          (B.duplicateOutside g₀).projection =
        g.image B.projection := by
    exact B.image_doubledProjection_doubledEdge g₀ copy g
  let lhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨(doubledEdge g₀ copy g).image
        (B.duplicateOutside g₀).projection,
      (B.duplicateOutside g₀).projectedEdgeTuple hd
        (edgeTuple (doubledEdge g₀ copy g) x)⟩
  let rhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image B.projection,
      B.projectedEdgeTuple hgB
        (fun v =>
          x (doubledVertexLift g₀ copy v.1))⟩
  change
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) lhsInput =
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) rhsInput
  apply congrArg
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2)
  apply Sigma.ext himage
  apply heq_of_eqRec_eq
    (congrArg
      (fun e : Finset J =>
        ({j : J // j ∈ e} → G))
      himage)
  funext j
  change
    cast
        (congrArg
          (fun e : Finset J =>
            ({j : J // j ∈ e} → G))
          himage)
        lhsInput.2 j =
      rhsInput.2 j
  rw [cast_finsetPi_apply himage]
  let jleft :
      {j : J //
        j ∈ (doubledEdge g₀ copy g).image
          (B.duplicateOutside g₀).projection} :=
    (finsetMembershipEquivOfEq himage).symm j
  let v : {v : K // v ∈ g} :=
    (B.projectionEquiv hgB).symm j
  have hjv :
      (⟨B.projection v.1,
          Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
        {j : J // j ∈ g.image B.projection}) = j := by
    exact
      (B.projectionEquiv hgB).apply_symm_apply j
  have hvlift :
      doubledVertexLift g₀ copy v.1 ∈
        doubledEdge g₀ copy g :=
    mem_doubledEdge g₀ copy g v.1 v.2
  have hpreimage :
      ((B.duplicateOutside g₀).projectionEquiv hd).symm jleft =
        ⟨doubledVertexLift g₀ copy v.1, hvlift⟩ := by
    apply ((B.duplicateOutside g₀).projectionEquiv hd).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    calc
      jleft.1 = j.1 := by
        exact
          finsetMembershipEquivOfEq_symm_val
            himage j
      _ = B.projection v.1 :=
        congrArg Subtype.val hjv.symm
      _ =
          (((B.duplicateOutside g₀).projectionEquiv hd)
            ⟨doubledVertexLift g₀ copy v.1,
              hvlift⟩).1 := by
        rw [projectionEquiv_apply_val,
          duplicateOutside_projection,
          doubledProjection_lift]
  unfold lhsInput rhsInput projectedEdgeTuple edgeTuple
  change
    x (((B.duplicateOutside g₀).projectionEquiv hd).symm
        jleft).1 =
      x (doubledVertexLift g₀ copy v.1)
  rw [hpreimage]

theorem doubledBundleEdgeFactor_doubledEdgeOfSource
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (x : DoubledOccurrenceVertex g₀ → G)
    (s : B.DoubledEdgeSource g₀) :
    B.doubledBundleEdgeFactor g₀ A x
        (B.doubledEdgeOfSource g₀ s) =
      B.pullbackBaseEdgeWeight A s.2.1
        (fun v =>
          x (doubledVertexLift g₀ s.1 v.1)) := by
  exact
    B.pullbackBaseEdgeWeight_duplicateOutside_doubledEdge
      g₀ A s.1 s.2.2 x

theorem doubledBundleEdgeFactor_idempotent
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A)
    (x : DoubledOccurrenceVertex g₀ → G)
    (d : Finset (DoubledOccurrenceVertex g₀))
    (hd : d ∈ B.doubledEdges g₀) :
    B.doubledBundleEdgeFactor g₀ A x d *
        B.doubledBundleEdgeFactor g₀ A x d =
      B.doubledBundleEdgeFactor g₀ A x d := by
  classical
  unfold doubledBundleEdgeFactor
  rw [(B.duplicateOutside g₀).pullbackBaseEdgeWeight_of_mem
      A hd]
  exact hA _ ((B.duplicateOutside g₀).projection_mem_base d hd) _

theorem doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A)
    (x : DoubledOccurrenceVertex g₀ → G) :
    B.doubledSourceProduct g₀
        (B.pullbackBaseEdgeWeight A) x =
      (B.duplicateOutside g₀).bundleProduct
        ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
  classical
  unfold doubledSourceProduct
  calc
    (∏ s : B.DoubledEdgeSource g₀,
        B.pullbackBaseEdgeWeight A s.2.1
          (fun v =>
            x (doubledVertexLift g₀ s.1 v.1))) =
        ∏ s : B.DoubledEdgeSource g₀,
          B.doubledBundleEdgeFactor g₀ A x
            (B.doubledEdgeOfSource g₀ s) := by
      apply Finset.prod_congr rfl
      intro s _hs
      exact
        (B.doubledBundleEdgeFactor_doubledEdgeOfSource
          g₀ A x s).symm
    _ =
        ∏ d ∈
            (Finset.univ :
              Finset (B.DoubledEdgeSource g₀)).image
                (B.doubledEdgeOfSource g₀),
          B.doubledBundleEdgeFactor g₀ A x d := by
      apply prod_comp_eq_prod_image_of_idempotent
      intro d hd
      apply B.doubledBundleEdgeFactor_idempotent
        g₀ A hA x d
      simpa [doubledEdges] using hd
    _ =
        (B.duplicateOutside g₀).bundleProduct
          ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
      rfl

theorem doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A) :
    B.doubledRemainderMoment g₀
        (B.pullbackBaseEdgeWeight A) =
      (B.duplicateOutside g₀).bundleCount
        ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) := by
  have _hduplicateClosed :
      (B.duplicateOutside g₀).IsClosedUnderInclusion :=
    B.duplicateOutside_closed_of_maximal
      hclosed hg₀ hmax
  rw [B.doubledRemainderMoment_eq_mean_doubledSourceProduct]
  unfold bundleCount
  apply congrArg mean
  funext x
  exact
    B.doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
      g₀ A hA x

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

theorem strictBoundaryLocalProduct_edgeTuple
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) :
    B.strictBoundaryLocalProduct g₀ A
        (edgeTuple g₀ x) =
      (B.strictBoundary g₀).bundleProduct A x := by
  classical
  unfold strictBoundaryLocalProduct
  calc
    (∏ g :
        {g : Finset K //
          g ∈ (B.strictBoundary g₀).edges},
      A g.1
        (restrictEdgeTuple
          (((B.mem_strictBoundary_edges g₀ g.1).1
            g.2).2.1)
          (edgeTuple g₀ x))) =
        ∏ g :
          {g : Finset K //
            g ∈ (B.strictBoundary g₀).edges},
          A g.1 (edgeTuple g.1 x) := by
      apply Finset.prod_congr rfl
      intro g _hg
      apply congrArg (A g.1)
      exact restrictEdgeTuple_edgeTuple _ x
    _ =
        ∏ g ∈ (B.strictBoundary g₀).edges,
          A g (edgeTuple g x) :=
      Finset.prod_coe_sort
        (B.strictBoundary g₀).edges
        (fun g => A g (edgeTuple g x))
    _ = (B.strictBoundary g₀).bundleProduct A x := by
      rfl

theorem strictBoundary_edges_subset_erase
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges ⊆
      B.edges.erase g₀ := by
  intro g hg
  have hg' :=
    (B.mem_strictBoundary_edges g₀ g).1 hg
  exact Finset.mem_erase.mpr
    ⟨hg'.2.ne, hg'.1⟩

theorem pullbackBaseEdgeWeight_weightsIdempotent
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A) :
    B.WeightsIdempotent
      (B.pullbackBaseEdgeWeight A) := by
  intro g hg y
  rw [B.pullbackBaseEdgeWeight_of_mem A hg y]
  exact hA _ (B.projection_mem_base g hg) _

theorem prod_mul_prod_eq_right_of_subset_of_idempotent
    {ι : Type*}
    (s t : Finset ι) (f : ι → ℝ)
    (hst : s ⊆ t)
    (hf : ∀ i ∈ s, f i * f i = f i) :
    (∏ i ∈ s, f i) * (∏ i ∈ t, f i) =
      ∏ i ∈ t, f i := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hat : a ∈ t :=
        hst (Finset.mem_insert_self a s)
      have hst' : s ⊆ t.erase a := by
        intro i hi
        exact Finset.mem_erase.mpr
          ⟨fun hia => ha (hia ▸ hi),
            hst (Finset.mem_insert_of_mem hi)⟩
      have hf' :
          ∀ i ∈ s, f i * f i = f i := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha]
      rw [← Finset.mul_prod_erase t f hat]
      calc
        (f a * ∏ i ∈ s, f i) *
              (f a * ∏ i ∈ t.erase a, f i) =
            (f a * f a) *
              ((∏ i ∈ s, f i) *
                ∏ i ∈ t.erase a, f i) := by
          ring
        _ =
            f a *
              ((∏ i ∈ s, f i) *
                ∏ i ∈ t.erase a, f i) := by
          rw [hf a (Finset.mem_insert_self a s)]
        _ = f a * ∏ i ∈ t.erase a, f i := by
          rw [ih (t.erase a) hst' hf']

theorem strictBoundaryLocalProduct_mul_edgeRemainder
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (hA : B.WeightsIdempotent A)
    (x : K → G) :
    B.strictBoundaryLocalProduct g₀ A
          (edgeTuple g₀ x) *
        B.edgeRemainder g₀ A x =
      B.edgeRemainder g₀ A x := by
  rw [B.strictBoundaryLocalProduct_edgeTuple]
  unfold edgeRemainder bundleProduct
  apply prod_mul_prod_eq_right_of_subset_of_idempotent
    (B.strictBoundary g₀).edges
    (B.edges.erase g₀)
    (fun g => A g (edgeTuple g x))
    (B.strictBoundary_edges_subset_erase g₀)
  intro g hg
  exact hA g
    (Finset.mem_of_mem_erase
      (B.strictBoundary_edges_subset_erase g₀ hg))
    (edgeTuple g x)

theorem edgeContribution_mul_strictBoundaryLocalProduct
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (hA : B.WeightsIdempotent A) :
    B.edgeContribution g₀ q A =
      B.edgeContribution g₀
        (fun y =>
          q y *
            B.strictBoundaryLocalProduct g₀ A y)
        A := by
  unfold edgeContribution
  apply congrArg mean
  funext x
  rw [mul_assoc,
    B.strictBoundaryLocalProduct_mul_edgeRemainder
      g₀ A hA x]

theorem card_image_projection
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card = g.card := by
  have hcard :=
    Fintype.card_congr (B.projectionEquiv hg)
  simpa using hcard.symm

theorem bundleMainProduct_nonneg
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ)
    (hp : ∀ e ∈ H, 0 ≤ p e) :
    0 ≤ B.bundleMainProduct p := by
  unfold bundleMainProduct
  exact Finset.prod_nonneg fun g hg =>
    hp _ (B.projection_mem_base g hg)

theorem bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.lowerOrder g₀.card).bundleMainProduct p =
      (B.strictBoundary g₀).bundleMainProduct p *
        B.lowerExteriorMainProduct g₀ p := by
  classical
  let s :=
    B.edges.filter
      (fun g => g.card < g₀.card)
  have hboundary :
      s.filter (fun g => g ⊆ g₀) =
        B.edges.filter (fun g => g ⊂ g₀) := by
    ext g
    simp only [s, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hgB, hgcard⟩, hgsub⟩
      exact ⟨hgB,
        Finset.ssubset_iff_subset_ne.mpr
          ⟨hgsub, fun hgeq => by
            subst g
            exact (Nat.lt_irrefl _ hgcard)⟩⟩
    · rintro ⟨hgB, hgstrict⟩
      exact ⟨⟨hgB, Finset.card_lt_card hgstrict⟩,
        hgstrict.1⟩
  have hexterior :
      s.filter (fun g => ¬ g ⊆ g₀) =
        B.edges.filter
          (fun g =>
            g.card < g₀.card ∧ ¬ g ⊆ g₀) := by
    ext g
    simp only [s, Finset.mem_filter]
    tauto
  have hsplit :=
    Finset.prod_filter_mul_prod_filter_not
      s (fun g => g ⊆ g₀)
        (fun g => p (g.image B.projection))
  unfold bundleMainProduct lowerExteriorMainProduct
  simp only [lowerOrder_edges, strictBoundary_edges]
  rw [← hboundary, ← hexterior]
  exact hsplit.symm

theorem boundary_mul_duplicateLower_main_eq_lowerOrder_sq
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.strictBoundary g₀).bundleMainProduct p *
        ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct p =
      ((B.lowerOrder g₀.card).bundleMainProduct p) ^ 2 := by
  rw [B.bundleMainProduct_duplicateOutside_lowerOrder
    g₀ p]
  rw [Finset.prod_pow]
  rw [B.bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
    g₀ p]
  unfold lowerExteriorMainProduct
  ring

theorem lowerOrder_mul_maximalRemainder_eq_erase_main
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.lowerOrder g₀.card).bundleMainProduct p *
        B.maximalRemainderMainProduct g₀ p =
      (B.eraseEdge g₀).bundleMainProduct p := by
  classical
  have hlower :
      (B.edges.erase g₀).filter
          (fun g => g.card < g₀.card) =
        B.edges.filter
          (fun g => g.card < g₀.card) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_hne, hgB⟩, hgcard⟩
      exact ⟨hgB, hgcard⟩
    · rintro ⟨hgB, hgcard⟩
      exact ⟨⟨fun hgg₀ => by
        subst g
        exact Nat.lt_irrefl _ hgcard, hgB⟩,
        hgcard⟩
  have hsplit :=
    Finset.prod_filter_mul_prod_filter_not
      (B.edges.erase g₀)
      (fun g => g.card < g₀.card)
      (fun g => p (g.image B.projection))
  unfold bundleMainProduct maximalRemainderMainProduct
  simp only [lowerOrder_edges, eraseEdge_edges]
  rw [← hlower]
  exact hsplit

theorem card_eq_selected_of_mem_maximalRemainder
    (B : HypergraphBundle J K H)
    {g₀ g : Finset K}
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hg :
      g ∈ (B.edges.erase g₀).filter
        (fun f => ¬ f.card < g₀.card)) :
    g.card = g₀.card := by
  have hg' := Finset.mem_filter.mp hg
  exact Nat.le_antisymm
    (hmax g (Finset.mem_of_mem_erase hg'.1))
    (Nat.le_of_not_gt hg'.2)

theorem card_maximalRemainder_le_erase
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    ((B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card)).card ≤
        (B.edges.erase g₀).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem pow_card_maximalRemainder_le
    (B : HypergraphBundle J K H)
    {g₀ : Finset K}
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp :
      ∀ e ∈ H, e.card = g₀.card →
        a ≤ p e) :
    a ^
          ((B.edges.erase g₀).filter
            (fun g => ¬ g.card < g₀.card)).card ≤
      B.maximalRemainderMainProduct g₀ p := by
  classical
  unfold maximalRemainderMainProduct
  calc
    a ^
          ((B.edges.erase g₀).filter
            (fun g => ¬ g.card < g₀.card)).card =
        ∏ _g ∈
            (B.edges.erase g₀).filter
              (fun g => ¬ g.card < g₀.card),
          a := by
      simp
    _ ≤
        ∏ g ∈
            (B.edges.erase g₀).filter
              (fun g => ¬ g.card < g₀.card),
          p (g.image B.projection) := by
      apply Finset.prod_le_prod
      · intro g hg
        exact ha
      · intro g hg
        apply hp _ (B.projection_mem_base g
          (Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hg).1))
        rw [B.card_image_projection
          (Finset.mem_of_mem_erase
            (Finset.mem_filter.mp hg).1)]
        exact B.card_eq_selected_of_mem_maximalRemainder
          hmax hg

theorem pullbackBaseEdgeWeight_eq_of_projection_eq
    (B C : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hprojection : B.projection = C.projection)
    {g : Finset K}
    (hgB : g ∈ B.edges) (hgC : g ∈ C.edges)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight A g y =
      C.pullbackBaseEdgeWeight A g y := by
  classical
  rw [B.pullbackBaseEdgeWeight_of_mem A hgB y,
    C.pullbackBaseEdgeWeight_of_mem A hgC y]
  have himage :
      g.image B.projection = g.image C.projection :=
    congrArg (fun q : K → J => g.image q) hprojection
  let lhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image B.projection,
      B.projectedEdgeTuple hgB y⟩
  let rhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image C.projection,
      C.projectedEdgeTuple hgC y⟩
  change
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) lhsInput =
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) rhsInput
  apply congrArg
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2)
  apply Sigma.ext himage
  apply heq_of_eqRec_eq
    (congrArg
      (fun e : Finset J =>
        ({j : J // j ∈ e} → G))
      himage)
  funext j
  change
    cast
        (congrArg
          (fun e : Finset J =>
            ({j : J // j ∈ e} → G))
          himage)
        lhsInput.2 j =
      rhsInput.2 j
  rw [cast_finsetPi_apply himage]
  let jB :
      {j : J // j ∈ g.image B.projection} :=
    (finsetMembershipEquivOfEq himage).symm j
  let vB := (B.projectionEquiv hgB).symm jB
  let vC := (C.projectionEquiv hgC).symm j
  have hjB : jB.1 = j.1 :=
    finsetMembershipEquivOfEq_symm_val himage j
  have hvB :
      B.projection vB.1 = jB.1 := by
    exact congrArg Subtype.val
      ((B.projectionEquiv hgB).apply_symm_apply jB)
  have hvC' :
      C.projection vC.1 = j.1 := by
    exact congrArg Subtype.val
      ((C.projectionEquiv hgC).apply_symm_apply j)
  have hvC :
      B.projection vC.1 = j.1 := by
    rw [hprojection]
    exact hvC'
  have hval : vB.1 = vC.1 :=
    B.projection_injective_on_edge g hgB
      vB.2 vC.2
      ((hvB.trans hjB).trans hvC.symm)
  unfold lhsInput rhsInput projectedEdgeTuple
  change y vB = y vC
  exact congrArg y (Subtype.ext hval)

theorem doubledEdges_lowerOrder_subset
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.lowerOrder g₀.card).doubledEdges g₀ ⊆
      B.doubledEdges g₀ := by
  intro d hd
  obtain ⟨copy, g, hg, hgd⟩ :=
    ((B.lowerOrder g₀.card).mem_doubledEdges_iff
      g₀ d).1 hd
  apply (B.mem_doubledEdges_iff g₀ d).2
  refine ⟨copy, g, ?_, hgd⟩
  have hgLower :
      g ∈ (B.lowerOrder g₀.card).edges :=
    Finset.mem_of_mem_erase hg
  exact Finset.mem_erase.mpr
    ⟨(Finset.mem_erase.mp hg).1,
      ((B.mem_lowerOrder_edges g₀.card g).1
        hgLower).1⟩

theorem duplicateOutside_bundleProduct_le_lowerOrder
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A)
    (x : DoubledOccurrenceVertex g₀ → G) :
    (B.duplicateOutside g₀).bundleProduct
          ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x ≤
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleProduct
          (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
  classical
  let C := B.duplicateOutside g₀
  let D := (B.lowerOrder g₀.card).duplicateOutside g₀
  have hDC : D.edges ⊆ C.edges := by
    simpa [C, D] using
      B.doubledEdges_lowerOrder_subset g₀
  have hprojection : C.projection = D.projection := by
    rfl
  unfold bundleProduct
  calc
    (∏ d ∈ C.edges,
        C.pullbackBaseEdgeWeight A
          d (edgeTuple d x)) ≤
        ∏ d ∈ D.edges,
          C.pullbackBaseEdgeWeight A
            d (edgeTuple d x) := by
      apply Finset.prod_le_prod_of_subset_of_le_one
        hDC
      · intro d hd
        exact
          (C.pullbackBaseEdgeWeight_unitInterval
            A hA hd (edgeTuple d x)).1
      · intro d hd _hdD
        exact
          (C.pullbackBaseEdgeWeight_unitInterval
            A hA hd (edgeTuple d x)).2
    _ =
        ∏ d ∈ D.edges,
          D.pullbackBaseEdgeWeight A
            d (edgeTuple d x) := by
      apply Finset.prod_congr rfl
      intro d hd
      exact C.pullbackBaseEdgeWeight_eq_of_projection_eq
        D A hprojection (hDC hd) hd (edgeTuple d x)

theorem doubledRemainderMoment_pullback_le_lowerOrder
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA01 : BaseWeightsInUnitInterval H A)
    (hAidempotent : BaseWeightsIdempotent H A) :
    B.doubledRemainderMoment g₀
          (B.pullbackBaseEdgeWeight A) ≤
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
          (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A) := by
  rw [B.doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
    hclosed hg₀ hmax A hAidempotent]
  unfold bundleCount
  apply mean_mono
  intro x
  exact B.duplicateOutside_bundleProduct_le_lowerOrder
    g₀ A hA01 x

theorem abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA01 : BaseWeightsInUnitInterval H A)
    (hAidempotent : BaseWeightsIdempotent H A)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    {β : ℝ} (hβ : 0 ≤ β)
    (hlocalized :
      mean (fun y => q y ^ 2) ≤
        β *
          (B.strictBoundary g₀).bundleCount
            ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)) :
    |B.edgeContribution g₀ q
        (B.pullbackBaseEdgeWeight A)| ≤
      Real.sqrt
        ((β *
            (B.strictBoundary g₀).bundleCount
              ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)) *
          ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
              (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A)) := by
  let boundaryCount :=
    (B.strictBoundary g₀).bundleCount
      ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)
  let lowerDoubledCount :=
    ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
        (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A)
  have hboundary0 : 0 ≤ boundaryCount := by
    apply (B.strictBoundary g₀).bundleCount_nonneg
    exact
      (B.strictBoundary g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
          A hA01
  have hlower0 : 0 ≤ lowerDoubledCount := by
    apply
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount_nonneg
    exact
      ((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
          A hA01
  have hmoment0 :
      0 ≤ B.doubledRemainderMoment g₀
        (B.pullbackBaseEdgeWeight A) :=
    B.doubledRemainderMoment_nonneg g₀
      (B.pullbackBaseEdgeWeight A)
  have hmoment :
      B.doubledRemainderMoment g₀
          (B.pullbackBaseEdgeWeight A) ≤
        lowerDoubledCount :=
    B.doubledRemainderMoment_pullback_le_lowerOrder
      hclosed hg₀ hmax A hA01 hAidempotent
  have hsq :
      B.edgeContribution g₀ q
          (B.pullbackBaseEdgeWeight A) ^ 2 ≤
        (β * boundaryCount) * lowerDoubledCount := by
    calc
      B.edgeContribution g₀ q
            (B.pullbackBaseEdgeWeight A) ^ 2 ≤
          mean (fun y => q y ^ 2) *
            B.doubledRemainderMoment g₀
              (B.pullbackBaseEdgeWeight A) :=
        B.edgeContribution_sq_le_localSquare_mul_doubled
          g₀ q (B.pullbackBaseEdgeWeight A)
      _ ≤
          (β * boundaryCount) *
            B.doubledRemainderMoment g₀
              (B.pullbackBaseEdgeWeight A) :=
        mul_le_mul_of_nonneg_right hlocalized hmoment0
      _ ≤ (β * boundaryCount) * lowerDoubledCount :=
        mul_le_mul_of_nonneg_left hmoment
          (mul_nonneg hβ hboundary0)
  have hradicand :
      0 ≤ (β * boundaryCount) * lowerDoubledCount :=
    mul_nonneg (mul_nonneg hβ hboundary0) hlower0
  apply
    (sq_le_sq₀
      (abs_nonneg
        (B.edgeContribution g₀ q
          (B.pullbackBaseEdgeWeight A)))
      (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hradicand]
  exact hsq

end HypergraphBundle

theorem IsBundleCountingEnvelope.add_stepIncrement_le
    {α β μ : ℕ → ℝ} {τ : ℝ}
    {E : ℕ → ℕ → ℝ}
    (hE : IsBundleCountingEnvelope α β μ τ E)
    (d n : ℕ) :
    E (d + 1) n +
        bundleCountingStepIncrement α β μ τ E d n ≤
      E (d + 1) (n + 1) := by
  simpa [bundleCountingStepIncrement, add_assoc] using hE.step d n

theorem IsBundleCountingEnvelope.lower_correction_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    {E : ℕ → ℕ → ℝ}
    (hE : IsBundleCountingEnvelope α β μ τ E)
    (d n : ℕ) :
    0 ≤
      (1 + E d (n + 1)) *
        (1 + E d (2 * (n + 1))) := by
  exact mul_nonneg
    (by linarith [hE.error_nonneg d (n + 1)])
    (by linarith [hE.error_nonneg d (2 * (n + 1))])

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleRelativeCounting
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

theorem bundleProduct_pullback_eq_of_subset_of_projection_eq
    (B C : HypergraphBundle J K H)
    (hCB : C.edges ⊆ B.edges)
    (hprojection : B.projection = C.projection)
    (A : BaseEdgeWeight J G)
    (x : K → G) :
    C.bundleProduct (B.pullbackBaseEdgeWeight A) x =
      C.bundleProduct (C.pullbackBaseEdgeWeight A) x := by
  unfold bundleProduct
  apply Finset.prod_congr rfl
  intro g hg
  exact B.pullbackBaseEdgeWeight_eq_of_projection_eq
    C A hprojection (hCB hg) hg (edgeTuple g x)

theorem bundleCount_pullback_eq_of_subset_of_projection_eq
    [Fintype K] [Fintype G]
    (B C : HypergraphBundle J K H)
    (hCB : C.edges ⊆ B.edges)
    (hprojection : B.projection = C.projection)
    (A : BaseEdgeWeight J G) :
    C.bundleCount (B.pullbackBaseEdgeWeight A) =
      C.bundleCount (C.pullbackBaseEdgeWeight A) := by
  unfold bundleCount
  apply congrArg mean
  funext x
  exact B.bundleProduct_pullback_eq_of_subset_of_projection_eq
    C hCB hprojection A x

theorem eraseEdge_bundleCount_pullback
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (A : BaseEdgeWeight J G) :
    (B.eraseEdge g₀).bundleCount
        (B.pullbackBaseEdgeWeight A) =
      (B.eraseEdge g₀).bundleCount
        ((B.eraseEdge g₀).pullbackBaseEdgeWeight A) := by
  apply B.bundleCount_pullback_eq_of_subset_of_projection_eq
    (B.eraseEdge g₀)
  · exact Finset.erase_subset _ _
  · rfl

theorem duplicateOutside_lowerOrder_closed
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (g₀ : Finset K) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).IsClosedUnderInclusion := by
  apply (B.lowerOrder g₀.card).duplicateOutside_closed
    g₀
  intro g hg f hfg
  have hgLower :
      g ∈ (B.lowerOrder g₀.card).edges :=
    Finset.mem_of_mem_erase hg
  have hfLower :
      f ∈ (B.lowerOrder g₀.card).edges :=
    B.lowerOrder_closed hclosed g₀.card
      hgLower hfg
  apply Finset.mem_erase.mpr
  refine ⟨?_, hfLower⟩
  intro hfg₀
  subst f
  have hgcard :
      g.card < g₀.card :=
    ((B.mem_lowerOrder_edges g₀.card g).1
      hgLower).2
  have hcardle : g₀.card ≤ g.card :=
    Finset.card_le_card hfg
  exact (Nat.not_le_of_gt hgcard) hcardle

theorem duplicateOutside_lowerOrder_order_lt
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀.Nonempty) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).order <
      g₀.card := by
  exact
    ((B.lowerOrder g₀.card).duplicateOutside_order_le
      g₀).trans_lt
      (B.lowerOrder_order_lt
        (Finset.card_pos.mpr hg₀))

theorem card_duplicateOutside_lowerOrder_le
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).edges.card ≤
      2 * B.edges.card := by
  calc
    ((B.lowerOrder g₀.card).duplicateOutside g₀).edges.card =
        ((B.lowerOrder g₀.card).doubledEdges g₀).card := by
      rfl
    _ ≤
        2 *
          ((B.lowerOrder g₀.card).edges.erase g₀).card :=
      (B.lowerOrder g₀.card).card_doubledEdges_le g₀
    _ ≤ 2 * (B.lowerOrder g₀.card).edges.card :=
      Nat.mul_le_mul_left 2
        Finset.card_erase_le
    _ ≤ 2 * B.edges.card :=
      Nat.mul_le_mul_left 2
        (B.card_lowerOrder_edges_le g₀.card)

theorem exists_edge_card_eq_order
    (B : HypergraphBundle J K H)
    (horder : 0 < B.order) :
    ∃ g₀ ∈ B.edges,
      g₀.card = B.order ∧
        ∀ g ∈ B.edges, g.card ≤ g₀.card := by
  have hedges : B.edges.Nonempty := by
    by_contra hempty
    have hbe : B.edges = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    simp [order, hbe] at horder
  obtain ⟨g₀, hg₀, hsup⟩ :=
    Finset.exists_mem_eq_sup B.edges hedges Finset.card
  refine ⟨g₀, hg₀, ?_, ?_⟩
  · simpa [order] using hsup.symm
  · intro g hg
    rw [← hsup]
    exact Finset.le_sup hg

theorem count_le_one_add_error_mul_main
    {count main error : ℝ}
    (herror : |count - main| ≤ error * main) :
    count ≤ (1 + error) * main := by
  have hleft : count - main ≤ |count - main| :=
    le_abs_self _
  calc
    count ≤ main + |count - main| := by
      linarith
    _ ≤ main + error * main :=
      add_le_add_right herror main
    _ = (1 + error) * main := by
      ring

theorem pow_card_edges_le_bundleMainProduct_of_edges
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp :
      ∀ g ∈ B.edges,
        a ≤ p (g.image B.projection)) :
    a ^ B.edges.card ≤ B.bundleMainProduct p := by
  classical
  unfold bundleMainProduct
  calc
    a ^ B.edges.card =
        ∏ _g ∈ B.edges, a := by
      simp
    _ ≤
        ∏ g ∈ B.edges,
          p (g.image B.projection) := by
      apply Finset.prod_le_prod
      · intro g hg
        exact ha
      · intro g hg
        exact hp g hg

theorem pow_card_edges_le_selected_mul_maximalRemainder
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (p : Finset J → ℝ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hp :
      ∀ e ∈ H, e.card = g₀.card →
        a ≤ p e) :
    a ^ B.edges.card ≤
      p (g₀.image B.projection) *
        B.maximalRemainderMainProduct g₀ p := by
  let s :=
    (B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card)
  have hscard :
      s.card ≤ (B.edges.erase g₀).card :=
    B.card_maximalRemainder_le_erase g₀
  have hpmax :
      a ^ s.card ≤
        B.maximalRemainderMainProduct g₀ p :=
    B.pow_card_maximalRemainder_le
      hmax p ha0 hp
  have hpow :
      a ^ (B.edges.erase g₀).card ≤
        a ^ s.card :=
    pow_le_pow_of_le_one ha0 ha1 hscard
  have hremain :
      a ^ (B.edges.erase g₀).card ≤
        B.maximalRemainderMainProduct g₀ p :=
    hpow.trans hpmax
  have hselected :
      a ≤ p (g₀.image B.projection) := by
    apply hp _ (B.projection_mem_base g₀ hg₀)
    exact B.card_image_projection hg₀
  have hselected0 :
      0 ≤ p (g₀.image B.projection) :=
    ha0.trans hselected
  calc
    a ^ B.edges.card =
        a * a ^ (B.edges.erase g₀).card := by
      rw [← Finset.card_erase_add_one hg₀,
        pow_succ, mul_comm]
    _ ≤
        p (g₀.image B.projection) *
          a ^ (B.edges.erase g₀).card :=
      mul_le_mul_of_nonneg_right hselected
        (pow_nonneg ha0 _)
    _ ≤
        p (g₀.image B.projection) *
          B.maximalRemainderMainProduct g₀ p :=
      mul_le_mul_of_nonneg_left hremain hselected0

theorem bundleCount_eq_bundleMainProduct_of_order_zero
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (hAempty :
      ∀ y :
        {j : J // j ∈ (∅ : Finset J)} → G,
        A ∅ y = 1)
    (hpempty : p ∅ = 1)
    (horder : B.order = 0) :
    B.bundleCount (B.pullbackBaseEdgeWeight A) =
      B.bundleMainProduct p := by
  have hedgeEmpty :
      ∀ g ∈ B.edges, g = ∅ := by
    intro g hg
    apply Finset.card_eq_zero.mp
    exact Nat.le_zero.mp
      (horder ▸ B.edge_card_le_order hg)
  have hproduct :
      ∀ x : K → G,
        B.bundleProduct
            (B.pullbackBaseEdgeWeight A) x = 1 := by
    intro x
    unfold bundleProduct
    apply Finset.prod_eq_one
    intro g hg
    have hge : g = ∅ :=
      hedgeEmpty g hg
    subst g
    rw [B.pullbackBaseEdgeWeight_of_mem A hg]
    exact hAempty _
  have hmain :
      B.bundleMainProduct p = 1 := by
    unfold bundleMainProduct
    apply Finset.prod_eq_one
    intro g hg
    rw [hedgeEmpty g hg]
    simp [hpempty]
  rw [hmain]
  unfold bundleCount
  calc
    mean
        (B.bundleProduct
          (B.pullbackBaseEdgeWeight A)) =
        mean (fun _x : K → G => 1) := by
      apply congrArg mean
      funext x
      exact hproduct x
    _ = 1 := mean_const 1

end HypergraphBundle

universe uJ uG

variable {J : Type uJ} {G : Type uG}
  [DecidableEq J] [Fintype G] [DecidableEq G]
  {H : Finset (Finset J)}

omit [DecidableEq G] in

theorem abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
    [Nonempty G]
    (A : HypergraphBundle.BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hA01 :
      HypergraphBundle.BaseWeightsInUnitInterval H A)
    (_hAidempotent :
      HypergraphBundle.BaseWeightsIdempotent H A)
    (hAempty :
      ∀ y :
        {j : J // j ∈ (∅ : Finset J)} → G,
        A ∅ y = 1)
    (hpempty : p ∅ = 1)
    (hpLower :
      ∀ e ∈ H, α e.card ≤ p e)
    (hstep :
      HasTaoBundleCountingStep
        (H := H) A p β τ)
    (hE :
      IsBundleCountingEnvelope α β μ τ E)
    {K : Type} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion) :
    |B.bundleCount (B.pullbackBaseEdgeWeight A) -
        B.bundleMainProduct p| ≤
      E B.order B.edges.card *
        B.bundleMainProduct p := by
  let P : ℕ → ℕ → Prop :=
    fun d n =>
      ∀ (K' : Type) [Fintype K'] [DecidableEq K']
        (C : HypergraphBundle J K' H),
        C.order ≤ d →
        C.edges.card ≤ n →
        C.IsClosedUnderInclusion →
        |C.bundleCount (C.pullbackBaseEdgeWeight A) -
            C.bundleMainProduct p| ≤
          E d n * C.bundleMainProduct p
  have hp0 :
      ∀ e ∈ H, 0 ≤ p e := by
    intro e he
    exact (hE.density_pos e.card).le.trans
      (hpLower e he)
  unfold HasTaoBundleCountingStep at hstep
  have hP : ∀ d n, P d n := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ihOrder =>
        intro n
        induction n using Nat.strong_induction_on with
        | h n ihCard =>
            dsimp [P]
            intro K' _instK' _decK' C hCd hCn hclosedC
            by_cases horderEq : C.order = d
            · by_cases hcardEq : C.edges.card = n
              · by_cases hd0 : d = 0
                · have hzero : C.order = 0 :=
                    horderEq.trans hd0
                  have hexact :=
                    C.bundleCount_eq_bundleMainProduct_of_order_zero
                      A p hAempty hpempty hzero
                  rw [hexact, sub_self, abs_zero]
                  exact mul_nonneg
                    (hE.error_nonneg d n)
                    (C.bundleMainProduct_nonneg p hp0)
                · have hdpos : 0 < d :=
                    Nat.pos_of_ne_zero hd0
                  obtain ⟨g₀, hg₀, hgcard, hmax⟩ :=
                    C.exists_edge_card_eq_order
                      (horderEq.symm ▸ hdpos)
                  have hgcardD : g₀.card = d :=
                    hgcard.trans horderEq
                  have hg₀ne : g₀.Nonempty := by
                    apply Finset.card_pos.mp
                    rw [hgcardD]
                    exact hdpos
                  obtain ⟨d₀, rfl⟩ :=
                    Nat.exists_eq_succ_of_ne_zero hd0
                  have hn0 : n ≠ 0 := by
                    intro hn
                    have hcardzero : C.edges.card = 0 :=
                      hcardEq.trans hn
                    exact
                      (Finset.card_ne_zero.mpr
                        ⟨g₀, hg₀⟩) hcardzero
                  obtain ⟨n₀, rfl⟩ :=
                    Nat.exists_eq_succ_of_ne_zero hn0
                  let Cerase := C.eraseEdge g₀
                  let Cboundary := C.strictBoundary g₀
                  let Clower :=
                    (C.lowerOrder g₀.card).duplicateOutside g₀
                  have hCeraseClosed :
                      Cerase.IsClosedUnderInclusion :=
                    C.eraseEdge_closed_of_maximal
                      hclosedC hg₀ hmax
                  have hCeraseOrder :
                      Cerase.order ≤ d₀ + 1 := by
                    exact
                      (C.eraseEdge_order_le g₀).trans_eq
                        horderEq
                  have hCeraseCard :
                      Cerase.edges.card ≤ n₀ := by
                    have hcard :
                        Cerase.edges.card = n₀ := by
                      simp [Cerase,
                        Finset.card_erase_of_mem hg₀,
                        hcardEq]
                    exact hcard.le
                  have hEraseIH :=
                    (ihCard n₀ (Nat.lt_succ_self n₀))
                      K' Cerase hCeraseOrder
                        hCeraseCard hCeraseClosed
                  have hCboundaryClosed :
                      Cboundary.IsClosedUnderInclusion :=
                    C.strictBoundary_closed hclosedC g₀
                  have hCboundaryOrder :
                      Cboundary.order ≤ d₀ := by
                    have hlt :
                        Cboundary.order < d₀ + 1 := by
                      simpa [Cboundary, hgcardD,
                        Nat.succ_eq_add_one] using
                        C.strictBoundary_order_lt hg₀ne
                    omega
                  have hCboundaryCard :
                      Cboundary.edges.card ≤ n₀ + 1 := by
                    exact
                      (C.card_strictBoundary_edges_le g₀).trans_eq
                        hcardEq
                  have hBoundaryIH :=
                    (ihOrder d₀ (Nat.lt_succ_self d₀)
                      (n₀ + 1))
                      K' Cboundary hCboundaryOrder
                        hCboundaryCard hCboundaryClosed
                  have hClowerClosed :
                      Clower.IsClosedUnderInclusion := by
                    dsimp [Clower]
                    exact C.duplicateOutside_lowerOrder_closed
                      hclosedC g₀
                  have hClowerOrder :
                      Clower.order ≤ d₀ := by
                    have hlt :
                        Clower.order < d₀ + 1 := by
                      simpa [Clower, hgcardD,
                        Nat.succ_eq_add_one] using
                        C.duplicateOutside_lowerOrder_order_lt
                          hg₀ne
                    omega
                  have hClowerCard :
                      Clower.edges.card ≤
                        2 * (n₀ + 1) := by
                    dsimp [Clower]
                    exact
                      (C.card_duplicateOutside_lowerOrder_le
                        g₀).trans_eq
                        (congrArg (fun m => 2 * m)
                          hcardEq)
                  have hLowerIH :=
                    (ihOrder d₀ (Nat.lt_succ_self d₀)
                      (2 * (n₀ + 1)))
                      (HypergraphBundle.DoubledOccurrenceVertex g₀)
                      Clower hClowerOrder
                        hClowerCard hClowerClosed
                  let mainErase :=
                    Cerase.bundleMainProduct p
                  let mainBoundary :=
                    Cboundary.bundleMainProduct p
                  let mainLower :=
                    Clower.bundleMainProduct p
                  let mainLowerOrder :=
                    (C.lowerOrder g₀.card).bundleMainProduct p
                  let mainMax :=
                    C.maximalRemainderMainProduct g₀ p
                  let mainC := C.bundleMainProduct p
                  let countErase :=
                    Cerase.bundleCount
                      (Cerase.pullbackBaseEdgeWeight A)
                  let countBoundary :=
                    Cboundary.bundleCount
                      (Cboundary.pullbackBaseEdgeWeight A)
                  let countLower :=
                    Clower.bundleCount
                      (Clower.pullbackBaseEdgeWeight A)
                  let p₀ :=
                    p (g₀.image C.projection)
                  have hmainErase0 : 0 ≤ mainErase := by
                    dsimp [mainErase, Cerase]
                    exact
                      (C.eraseEdge g₀).bundleMainProduct_nonneg p hp0
                  have hmainBoundary0 :
                      0 ≤ mainBoundary := by
                    dsimp [mainBoundary, Cboundary]
                    exact
                      (C.strictBoundary g₀).bundleMainProduct_nonneg p hp0
                  have hmainLower0 :
                      0 ≤ mainLower := by
                    dsimp [mainLower, Clower]
                    exact
                      ((C.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct_nonneg
                        p hp0
                  have hmainLowerOrder0 :
                      0 ≤ mainLowerOrder := by
                    dsimp [mainLowerOrder]
                    exact
                      (C.lowerOrder g₀.card).bundleMainProduct_nonneg p hp0
                  have hmainC0 : 0 ≤ mainC := by
                    dsimp [mainC]
                    exact C.bundleMainProduct_nonneg p hp0
                  have hcountBoundary0 :
                      0 ≤ countBoundary := by
                    dsimp [countBoundary, Cboundary]
                    exact
                      (C.strictBoundary g₀).bundleCount_nonneg
                        ((C.strictBoundary g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
                            A hA01)
                  have hcountLower0 :
                      0 ≤ countLower := by
                    dsimp [countLower, Clower]
                    exact
                      ((C.lowerOrder g₀.card).duplicateOutside g₀).bundleCount_nonneg
                          (HypergraphBundle.pullbackBaseEdgeWeight_weightsInUnitInterval
                            ((C.lowerOrder g₀.card).duplicateOutside g₀) A hA01)
                  have hcountBoundary :
                      countBoundary ≤
                        (1 + E d₀ (n₀ + 1)) *
                          mainBoundary :=
                    HypergraphBundle.count_le_one_add_error_mul_main
                      hBoundaryIH
                  have hcountLower :
                      countLower ≤
                        (1 + E d₀
                            (2 * (n₀ + 1))) *
                          mainLower :=
                    HypergraphBundle.count_le_one_add_error_mul_main
                      hLowerIH
                  have hcorrection0 :
                      0 ≤
                        (1 + E d₀ (n₀ + 1)) *
                          (1 + E d₀
                            (2 * (n₀ + 1))) :=
                    hE.lower_correction_nonneg d₀ n₀
                  have hfirstCorrection0 :
                      0 ≤ 1 + E d₀ (n₀ + 1) := by
                    linarith
                      [hE.error_nonneg d₀ (n₀ + 1)]
                  have hβ0 :
                      0 ≤ β (d₀ + 1) :=
                    hE.defect_nonneg _
                  have hradicand :
                      β (d₀ + 1) *
                            countBoundary * countLower ≤
                        β (d₀ + 1) *
                            ((1 + E d₀ (n₀ + 1)) *
                              mainBoundary) *
                          ((1 + E d₀
                              (2 * (n₀ + 1))) *
                            mainLower) := by
                    calc
                      β (d₀ + 1) *
                            countBoundary * countLower ≤
                          β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                mainBoundary) *
                            countLower :=
                        mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left
                            hcountBoundary hβ0)
                          hcountLower0
                      _ ≤
                          β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                mainBoundary) *
                            ((1 + E d₀
                                (2 * (n₀ + 1))) *
                              mainLower) :=
                        mul_le_mul_of_nonneg_left
                          hcountLower
                          (mul_nonneg hβ0
                            (mul_nonneg
                              hfirstCorrection0
                              hmainBoundary0))
                  let rootCorrection :=
                    Real.sqrt
                      (β (d₀ + 1) *
                        (1 + E d₀ (n₀ + 1)) *
                        (1 + E d₀
                          (2 * (n₀ + 1))))
                  have hrootCorrection0 :
                      0 ≤ rootCorrection :=
                    Real.sqrt_nonneg _
                  have hmainBoundaryLower :
                      mainBoundary * mainLower =
                        mainLowerOrder ^ 2 := by
                    dsimp [mainBoundary, mainLower,
                      mainLowerOrder, Cboundary, Clower]
                    exact
                      C.boundary_mul_duplicateLower_main_eq_lowerOrder_sq
                        g₀ p
                  have hcoefficient0 :
                      0 ≤
                        β (d₀ + 1) *
                          (1 + E d₀ (n₀ + 1)) *
                          (1 + E d₀
                            (2 * (n₀ + 1))) := by
                    rw [mul_assoc]
                    exact mul_nonneg hβ0 hcorrection0
                  have hsqrt :
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                        rootCorrection * mainLowerOrder := by
                    calc
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                          Real.sqrt
                            (β (d₀ + 1) *
                              ((1 + E d₀ (n₀ + 1)) *
                                mainBoundary) *
                              ((1 + E d₀
                                  (2 * (n₀ + 1))) *
                                mainLower)) :=
                        Real.sqrt_le_sqrt hradicand
                      _ =
                          Real.sqrt
                              ((β (d₀ + 1) *
                                  (1 + E d₀ (n₀ + 1)) *
                                  (1 + E d₀
                                    (2 * (n₀ + 1)))) *
                                (mainBoundary * mainLower)) := by
                        congr 1
                        ring
                      _ =
                          Real.sqrt
                              ((β (d₀ + 1) *
                                  (1 + E d₀ (n₀ + 1)) *
                                  (1 + E d₀
                                    (2 * (n₀ + 1)))) *
                                mainLowerOrder ^ 2) := by
                        congr 1
                        rw [hmainBoundaryLower]
                      _ = rootCorrection * mainLowerOrder := by
                        dsimp [rootCorrection]
                        rw [Real.sqrt_mul hcoefficient0]
                        rw [Real.sqrt_sq hmainLowerOrder0]
                  have hαp :
                      α (d₀ + 1) ^ (n₀ + 1) ≤
                        p₀ * mainMax := by
                    dsimp [p₀, mainMax]
                    have hpow :=
                      C.pow_card_edges_le_selected_mul_maximalRemainder
                        hg₀ hmax p
                        (hE.density_pos g₀.card).le
                        (hE.density_le_one g₀.card)
                        (fun e he hcard =>
                          hpLower e he |>
                            fun h => by
                              simpa [hcard] using h)
                    simpa [hgcardD, hcardEq,
                      Nat.succ_eq_add_one] using hpow
                  have hαpowpos :
                      0 < α (d₀ + 1) ^ (n₀ + 1) :=
                    pow_pos (hE.density_pos _) _
                  have hmainFactor :
                      mainLowerOrder * (p₀ * mainMax) =
                        mainC := by
                    dsimp [mainLowerOrder, p₀, mainMax,
                      mainC, Cerase]
                    calc
                      (C.lowerOrder g₀.card).bundleMainProduct p *
                          (p (g₀.image C.projection) *
                            C.maximalRemainderMainProduct
                              g₀ p) =
                          ((C.lowerOrder g₀.card).bundleMainProduct p *
                            C.maximalRemainderMainProduct
                              g₀ p) *
                            p (g₀.image C.projection) := by
                        ring
                      _ =
                          (C.eraseEdge g₀).bundleMainProduct p *
                            p (g₀.image C.projection) := by
                        rw [
                          C.lowerOrder_mul_maximalRemainder_eq_erase_main
                            g₀ p]
                      _ = C.bundleMainProduct p :=
                        C.bundleMainProduct_eraseEdge_mul
                          p hg₀
                  have hsqrtNormalized :
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                        (rootCorrection /
                            α (d₀ + 1) ^ (n₀ + 1)) *
                          mainC := by
                    have hscaled :
                        rootCorrection ≤
                          (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            (p₀ * mainMax) := by
                      calc
                        rootCorrection =
                            (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              α (d₀ + 1) ^ (n₀ + 1) := by
                          field_simp
                        _ ≤
                            (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              (p₀ * mainMax) :=
                          mul_le_mul_of_nonneg_left hαp
                            (div_nonneg hrootCorrection0
                              hαpowpos.le)
                    calc
                      Real.sqrt
                            (β (d₀ + 1) *
                              countBoundary * countLower) ≤
                          rootCorrection * mainLowerOrder :=
                        hsqrt
                      _ ≤
                          ((rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            (p₀ * mainMax)) *
                              mainLowerOrder :=
                        mul_le_mul_of_nonneg_right
                          hscaled hmainLowerOrder0
                      _ =
                          (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                            mainC := by
                        rw [← hmainFactor]
                        ring
                  have hμmain :
                      μ (d₀ + 1) ^ (n₀ + 1) ≤
                        mainC := by
                    dsimp [mainC]
                    have hpow :=
                      C.pow_card_edges_le_bundleMainProduct_of_edges
                        p (hE.floor_pos (d₀ + 1)).le
                        (fun g hg => by
                          have hcard :
                              g.card ≤ d₀ + 1 := by
                            exact
                              (C.edge_card_le_order hg).trans_eq
                                (by
                                  simpa [Nat.succ_eq_add_one] using
                                    horderEq)
                          exact
                            (hE.rankFloor hcard).trans
                              (hpLower _
                                (C.projection_mem_base g hg) |>
                                  fun h => by
                                    simpa [C.card_image_projection hg]
                                      using h))
                    simpa [hcardEq] using hpow
                  have hμpowpos :
                      0 < μ (d₀ + 1) ^ (n₀ + 1) :=
                    pow_pos (hE.floor_pos _) _
                  have huniformNormalized :
                      τ ≤
                        (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                          mainC := by
                    calc
                      τ =
                          (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                              μ (d₀ + 1) ^ (n₀ + 1) := by
                        field_simp
                      _ ≤
                          (τ /
                            μ (d₀ + 1) ^ (n₀ + 1)) *
                            mainC :=
                        mul_le_mul_of_nonneg_left hμmain
                          (div_nonneg hE.uniform_nonneg
                            hμpowpos.le)
                  have hstepRaw :=
                    hstep K' C hclosedC hg₀ hmax
                  have hstepNormalized :
                      |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| ≤
                        (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1) +
                            τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                          mainC := by
                    calc
                      |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| ≤
                          Real.sqrt
                              (β (d₀ + 1) *
                                countBoundary * countLower) +
                            τ := by
                        simpa [p₀, countErase,
                          countBoundary, countLower,
                          Cerase, Cboundary, Clower,
                          hgcardD] using hstepRaw
                      _ ≤
                          (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1)) *
                              mainC +
                            (τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                              mainC :=
                        add_le_add hsqrtNormalized
                          huniformNormalized
                      _ =
                          (rootCorrection /
                                α (d₀ + 1) ^ (n₀ + 1) +
                              τ /
                                μ (d₀ + 1) ^ (n₀ + 1)) *
                            mainC := by
                        ring
                  have hp₀0 : 0 ≤ p₀ := by
                    dsimp [p₀]
                    exact hp0 _
                      (C.projection_mem_base g₀ hg₀)
                  have hmainEraseFactor :
                      p₀ * mainErase = mainC := by
                    dsimp [p₀, mainErase, mainC,
                      Cerase]
                    rw [mul_comm]
                    exact
                      C.bundleMainProduct_eraseEdge_mul
                        p hg₀
                  have hEraseNormalized :
                      p₀ *
                          |countErase - mainErase| ≤
                        E (d₀ + 1) n₀ * mainC := by
                    calc
                      p₀ *
                            |countErase - mainErase| ≤
                          p₀ *
                            (E (d₀ + 1) n₀ *
                              mainErase) :=
                        mul_le_mul_of_nonneg_left
                          hEraseIH hp₀0
                      _ =
                          E (d₀ + 1) n₀ * mainC := by
                        rw [← hmainEraseFactor]
                        ring
                  have hdecompose :
                      C.bundleCount
                            (C.pullbackBaseEdgeWeight A) -
                          mainC =
                        (C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase) +
                          p₀ * (countErase - mainErase) := by
                    rw [← hmainEraseFactor]
                    ring
                  rw [hdecompose]
                  calc
                    |(C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase) +
                          p₀ * (countErase - mainErase)| ≤
                        |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| +
                          |p₀ * (countErase - mainErase)| :=
                      abs_add_le _ _
                    _ =
                        |C.bundleCount
                              (C.pullbackBaseEdgeWeight A) -
                            p₀ * countErase| +
                          p₀ * |countErase - mainErase| := by
                      rw [abs_mul, abs_of_nonneg hp₀0]
                    _ ≤
                        (rootCorrection /
                              α (d₀ + 1) ^ (n₀ + 1) +
                            τ /
                              μ (d₀ + 1) ^ (n₀ + 1)) *
                            mainC +
                          E (d₀ + 1) n₀ * mainC :=
                      add_le_add hstepNormalized
                        hEraseNormalized
                    _ =
                        (E (d₀ + 1) n₀ +
                            (rootCorrection /
                                α (d₀ + 1) ^ (n₀ + 1) +
                              τ /
                                μ (d₀ + 1) ^ (n₀ + 1))) *
                          mainC := by
                      ring
                    _ ≤
                        E (d₀ + 1) (n₀ + 1) *
                          mainC := by
                      apply mul_le_mul_of_nonneg_right
                      · simpa [rootCorrection,
                          bundleCountingStepIncrement,
                          add_assoc] using
                          hE.add_stepIncrement_le d₀ n₀
                      · exact hmainC0
              · have hcardLt : C.edges.card < n :=
                  lt_of_le_of_ne hCn
                    hcardEq
                have hsmall :=
                  (ihCard C.edges.card hcardLt)
                    K' C hCd le_rfl hclosedC
                have hmain0 :
                    0 ≤ C.bundleMainProduct p :=
                  C.bundleMainProduct_nonneg p hp0
                exact hsmall.trans
                  (mul_le_mul_of_nonneg_right
                    (hE.error_mono_card hCn) hmain0)
            · have horderLt : C.order < d :=
                lt_of_le_of_ne hCd
                  horderEq
              have hsmall :=
                (ihOrder C.order horderLt n)
                  K' C le_rfl hCn hclosedC
              have hmain0 :
                  0 ≤ C.bundleMainProduct p :=
                C.bundleMainProduct_nonneg p hp0
              exact hsmall.trans
                (mul_le_mul_of_nonneg_right
                  (hE.error_mono_order hCd) hmain0)
  exact
    (hP B.order B.edges.card)
      K B le_rfl le_rfl hclosed

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleFrozenUniformity
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem positiveOrderedFaceEdge_injective
    {k r : ℕ} :
    Function.Injective
      (positiveOrderedFaceEdge :
        PositiveOrderedFace k r → Finset (Fin k)) := by
  intro e f hef
  have hrank : e.rank = f.rank := by
    rw [← positiveOrderedFaceEdge_card e,
      ← positiveOrderedFaceEdge_card f, hef]
  rcases e with ⟨je, e⟩
  rcases f with ⟨jf, f⟩
  simp only [PositiveOrderedFace.rank] at hrank
  have hj : je = jf := by
    apply Fin.ext
    omega
  subst jf
  have hrange : Set.range e = Set.range f := by
    ext v
    have hv :=
      congrArg
        (fun s : Finset (Fin k) => v ∈ s) hef
    simpa [positiveOrderedFaceEdge] using hv
  have hef' : e = f :=
    (OrderEmbedding.range_inj).mp hrange
  subst f
  rfl

@[simp]
theorem positiveOrderedFaceOfEdge_edge
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    positiveOrderedFaceOfEdge
        (positiveOrderedFaceEdge e)
        (positiveOrderedFaceEdge_nonempty e)
        (positiveOrderedFaceEdge_card_le e) = e := by
  apply positiveOrderedFaceEdge_injective
  exact positiveOrderedFaceEdge_ofEdge
    (positiveOrderedFaceEdge e)
    (positiveOrderedFaceEdge_nonempty e)
    (positiveOrderedFaceEdge_card_le e)

theorem empty_not_mem_positiveOrderedFaceEdge_image
    (k r : ℕ) :
    (∅ : Finset (Fin k)) ∉
      Finset.univ.image
        (positiveOrderedFaceEdge :
          PositiveOrderedFace k r → Finset (Fin k)) := by
  intro h
  obtain ⟨e, _he, hedge⟩ :=
    Finset.mem_image.mp h
  exact (positiveOrderedFaceEdge_nonempty e).ne_empty
    hedge

theorem orderedConfigurationInitialBundle_closed
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).IsClosedUnderInclusion := by
  intro g hg f hfg
  rw [orderedConfigurationInitialBundle_edges] at hg ⊢
  rw [mem_orderedConfigurationBaseEdges_iff] at hg ⊢
  exact (Finset.card_le_card hfg).trans hg

@[simp]
theorem orderedConfigurationBaseWeight_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y :
      {v : Fin k // v ∈ positiveOrderedFaceEdge e} → G) :
    orderedConfigurationBaseWeight A
        (positiveOrderedFaceEdge e) y =
      configurationFaceWeight A e
        (fun i =>
          y ⟨e.face i,
            (mem_positiveOrderedFaceEdge e
              (e.face i)).2 ⟨i, rfl⟩⟩) := by
  classical
  simp only [orderedConfigurationBaseWeight,
    dif_pos (positiveOrderedFaceEdge_nonempty e),
    dif_pos (positiveOrderedFaceEdge_card_le e)]
  change
    (fun p :
        (Σ f : PositiveOrderedFace k r,
          Fin (f.lowerRank.1 + 1) → G) =>
      configurationFaceWeight A p.1 p.2)
        ⟨positiveOrderedFaceOfEdge
            (positiveOrderedFaceEdge e)
            (positiveOrderedFaceEdge_nonempty e)
            (positiveOrderedFaceEdge_card_le e),
          orderedConfigurationEdgeTuple
            (positiveOrderedFaceEdge e)
            (positiveOrderedFaceEdge_nonempty e)
            (positiveOrderedFaceEdge_card_le e) y⟩ =
      (fun p :
          (Σ f : PositiveOrderedFace k r,
            Fin (f.lowerRank.1 + 1) → G) =>
        configurationFaceWeight A p.1 p.2)
          ⟨e, fun i =>
            y ⟨e.face i,
              (mem_positiveOrderedFaceEdge e
                (e.face i)).2 ⟨i, rfl⟩⟩⟩
  apply congrArg
    (fun p :
        (Σ f : PositiveOrderedFace k r,
          Fin (f.lowerRank.1 + 1) → G) =>
      configurationFaceWeight A p.1 p.2)
  have he :
      positiveOrderedFaceOfEdge
          (positiveOrderedFaceEdge e)
          (positiveOrderedFaceEdge_nonempty e)
          (positiveOrderedFaceEdge_card_le e) = e :=
    positiveOrderedFaceOfEdge_edge e
  apply Sigma.ext he
  simp only
  apply Function.hfunext
    (congrArg
      (fun f : PositiveOrderedFace k r =>
        Fin (f.lowerRank.1 + 1)) he)
  intro i i' hii
  apply heq_of_eq
  unfold orderedConfigurationEdgeTuple
  apply congrArg y
  apply Subtype.ext
  have hn :
      (positiveOrderedFaceOfEdge
          (positiveOrderedFaceEdge e)
          (positiveOrderedFaceEdge_nonempty e)
          (positiveOrderedFaceEdge_card_le e)).lowerRank.1 + 1 =
        e.lowerRank.1 + 1 :=
    congrArg (fun f : PositiveOrderedFace k r =>
      f.lowerRank.1 + 1) he
  have hval : i.1 = i'.1 := by
    have hcast :
        cast (congrArg Fin hn) i = i' := by
      exact eq_of_heq
        ((cast_heq (congrArg Fin hn) i).trans hii)
    calc
      i.1 = (cast (congrArg Fin hn) i).1 := by
        symm
        have hcastVal :
            ∀ {m n : ℕ} (h : m = n) (a : Fin m),
              (cast (congrArg Fin h) a).1 = a.1 := by
          intro m n h a
          cases h
          rfl
        exact hcastVal hn i
      _ = i'.1 := congrArg Fin.val hcast
  rw [Finset.coe_orderIsoOfFin_apply]
  calc
    (positiveOrderedFaceEdge e).orderEmbOfFin _ i =
        (positiveOrderedFaceEdge e).orderEmbOfFin _ i' :=
      Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr hval
    _ = e.face i' := by
      simpa only [Finset.coe_orderIsoOfFin_apply] using
        positiveOrderedFaceEdge_orderIsoOfFin_val e i'

theorem orderedConfigurationBaseWeight_unitInterval
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseWeightsInUnitInterval
      (orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A) := by
  intro t ht y
  unfold orderedConfigurationBaseWeight
  by_cases ht0 : t.Nonempty
  · simp only [dif_pos ht0]
    by_cases htr : t.card ≤ r
    · simp only [dif_pos htr]
      exact
        ⟨configurationFaceWeight_nonneg A _ _,
          configurationFaceWeight_le_one A _ _⟩
    · simp [htr]
  · simp [ht0]

theorem orderedConfigurationBaseWeight_idempotent
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseWeightsIdempotent
      (orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A) := by
  intro t ht y
  unfold orderedConfigurationBaseWeight
  by_cases ht0 : t.Nonempty
  · simp only [dif_pos ht0]
    by_cases htr : t.card ≤ r
    · simp only [dif_pos htr]
      simpa [configurationFaceWeight, pow_two] using
        (partitionAtomIndicator_sq
          (C.partition
            (positiveOrderedFaceOfEdge t ht0 htr).lowerRank.succ
            (positiveOrderedFaceOfEdge t ht0 htr).face)
          (A.atom
            (positiveOrderedFaceOfEdge t ht0 htr).lowerRank.succ
            (positiveOrderedFaceOfEdge t ht0 htr).face)
          (orderedConfigurationEdgeTuple t ht0 htr y))
    · simp [htr]
  · simp [ht0]

@[simp]
theorem orderedConfigurationBaseDensity_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) :
    orderedConfigurationBaseDensity P A
        (positiveOrderedFaceEdge e) =
      mixedConfigurationCoarseDensity P A e := by
  classical
  unfold orderedConfigurationBaseDensity
  simp only [dif_pos (positiveOrderedFaceEdge_nonempty e)]
  have hcard :
      (positiveOrderedFaceEdge e).card ≤ r := by
    simpa [positiveOrderedFaceEdge_card] using
      positiveOrderedFaceEdge_card_le e
  simp only [dif_pos hcard]
  exact congrArg (mixedConfigurationCoarseDensity P A)
    (positiveOrderedFaceOfEdge_edge e)

theorem orderedConfigurationInitialBundle_projectedEdgeTuple
    {G : Type*} {k r : ℕ}
    {g : Finset (Fin k)}
    (hg :
      g ∈ (orderedConfigurationInitialBundle k r).edges)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).projectedEdgeTuple hg
          (HypergraphBundle.edgeTuple g x) =
      fun j => x j.1 := by
  funext j
  have hj :
      (((orderedConfigurationInitialBundle k r).projectionEquiv hg).symm j).1 =
        j.1 := by
    have happly :=
      congrArg Subtype.val
        (((orderedConfigurationInitialBundle k r).projectionEquiv hg).apply_symm_apply j)
    change
      (orderedConfigurationInitialBundle k r).projection
          (((orderedConfigurationInitialBundle k r).projectionEquiv hg).symm j).1 =
        j.1 at happly
    change
      (((orderedConfigurationInitialBundle k r).projectionEquiv hg).symm j).1 =
        j.1 at happly
    exact happly
  unfold HypergraphBundle.projectedEdgeTuple
    HypergraphBundle.edgeTuple
  exact congrArg x hj

theorem orderedConfigurationInitialBundle_pullback_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) ∅
          (HypergraphBundle.edgeTuple ∅ x) = 1 := by
  rw [(orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight_of_mem
      (orderedConfigurationBaseWeight A)
      (empty_mem_orderedConfigurationBaseEdges k r)]
  exact orderedConfigurationBaseWeight_empty A _

theorem orderedConfigurationInitialBundle_pullback_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A)
          (positiveOrderedFaceEdge e)
          (HypergraphBundle.edgeTuple
            (positiveOrderedFaceEdge e) x) =
      configurationFaceWeight A e
        (orderedFaceTuple e.face x) := by
  have hedge :
      positiveOrderedFaceEdge e ∈
        (orderedConfigurationInitialBundle k r).edges := by
    rw [orderedConfigurationInitialBundle_edges,
      mem_orderedConfigurationBaseEdges_iff]
    exact positiveOrderedFaceEdge_card_le e
  rw [(orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight_of_mem
    (orderedConfigurationBaseWeight A) hedge]
  have himage :
      (positiveOrderedFaceEdge e).image
          (orderedConfigurationInitialBundle k r).projection =
        positiveOrderedFaceEdge e := by
    simpa only [orderedConfigurationInitialBundle_projection] using
      (Finset.image_id :
        (positiveOrderedFaceEdge e).image id =
          positiveOrderedFaceEdge e)
  have hpair :
      (⟨(positiveOrderedFaceEdge e).image
            (orderedConfigurationInitialBundle k r).projection,
          (orderedConfigurationInitialBundle k r).projectedEdgeTuple
            hedge
            (HypergraphBundle.edgeTuple
              (positiveOrderedFaceEdge e) x)⟩ :
        Σ t : Finset (Fin k), ({j : Fin k // j ∈ t} → G)) =
      ⟨positiveOrderedFaceEdge e,
        HypergraphBundle.edgeTuple
          (positiveOrderedFaceEdge e) x⟩ := by
    apply Sigma.ext himage
    simp only
    apply Function.hfunext
      (congrArg
        (fun t : Finset (Fin k) =>
          {j : Fin k // j ∈ t}) himage)
    intro j j' hjj
    apply heq_of_eq
    rw [congrFun
      (orderedConfigurationInitialBundle_projectedEdgeTuple
        hedge x) j]
    apply congrArg x
    exact
      (Subtype.heq_iff_coe_eq
        (fun v : Fin k => by
          rw [himage])).1 hjj
  have hweight :=
    congrArg
      (fun p :
          (Σ t : Finset (Fin k),
            ({j : Fin k // j ∈ t} → G)) =>
        orderedConfigurationBaseWeight A p.1 p.2)
      hpair
  rw [hweight]
  rw [orderedConfigurationBaseWeight_positiveOrderedFaceEdge]
  apply congrArg (configurationFaceWeight A e)
  funext i
  rfl

theorem orderedConfigurationInitialBundle_bundleProduct
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).bundleProduct
        ((orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) x =
      partialConfigurationWeight A Finset.univ x := by
  classical
  change
    (∏ g ∈ (orderedConfigurationInitialBundle k r).edges,
      (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (HypergraphBundle.edgeTuple g x)) =
      partialConfigurationWeight A Finset.univ x
  rw [orderedConfigurationInitialBundle_edges]
  change
    (∏ g ∈ insert ∅
        (Finset.univ.image
          (positiveOrderedFaceEdge :
            PositiveOrderedFace k r → Finset (Fin k))),
      (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (HypergraphBundle.edgeTuple g x)) =
      partialConfigurationWeight A Finset.univ x
  rw [
    Finset.prod_insert
      (empty_not_mem_positiveOrderedFaceEdge_image k r)]
  rw [orderedConfigurationInitialBundle_pullback_empty]
  simp only [one_mul]
  rw [Finset.prod_image
    positiveOrderedFaceEdge_injective.injOn]
  unfold partialConfigurationWeight
  apply Finset.prod_congr rfl
  intro e he
  exact
    orderedConfigurationInitialBundle_pullback_positiveOrderedFaceEdge
      A e x

theorem orderedConfigurationInitialBundle_bundleCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    (orderedConfigurationInitialBundle k r).bundleCount
        ((orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) =
      fullConfigurationCount A := by
  unfold HypergraphBundle.bundleCount
    fullConfigurationCount partialConfigurationCount
  apply congrArg mean
  funext x
  exact orderedConfigurationInitialBundle_bundleProduct A x

theorem orderedConfigurationInitialBundle_bundleMainProduct
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    (orderedConfigurationInitialBundle k r).bundleMainProduct
          (orderedConfigurationBaseDensity P A) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e := by
  classical
  change
    (∏ g ∈ (orderedConfigurationInitialBundle k r).edges,
      orderedConfigurationBaseDensity P A
        (g.image
          (orderedConfigurationInitialBundle k r).projection)) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e
  rw [orderedConfigurationInitialBundle_edges,
    orderedConfigurationInitialBundle_projection]
  simp only [Function.id_def, Finset.image_id']
  change
    (∏ g ∈ insert ∅
        (Finset.univ.image
          (positiveOrderedFaceEdge :
            PositiveOrderedFace k r → Finset (Fin k))),
      orderedConfigurationBaseDensity P A g) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e
  rw [
    Finset.prod_insert
      (empty_not_mem_positiveOrderedFaceEdge_image k r),
    orderedConfigurationBaseDensity_empty,
    one_mul]
  rw [Finset.prod_image
    positiveOrderedFaceEdge_injective.injOn]
  simp

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

theorem orderedConfigurationBaseDensity_projectedEdge
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    orderedConfigurationBaseDensity P A
        (g.image B.projection) =
      mixedConfigurationCoarseDensity P A
        (B.orderedConfigurationBundleFace hg hne) := by
  unfold orderedConfigurationBaseDensity
  simp only [
    dif_pos (B.projectedEdge_nonempty hg hne),
    dif_pos (B.projectedEdge_card_le hg)]
  rfl

theorem pullback_orderedConfigurationBaseWeight_decompose
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g y =
      orderedConfigurationBaseDensity P A
          (g.image B.projection) +
        B.orderedConfigurationBundleDefect P A hg hne y +
        B.orderedConfigurationBundleUniform P A hg hne y := by
  rw [B.pullbackBaseEdgeWeight_of_mem
    (orderedConfigurationBaseWeight A) hg y]
  rw [B.orderedConfigurationBaseDensity_projectedEdge
    P A hg hne]
  unfold orderedConfigurationBaseWeight
  simp only [
    dif_pos (B.projectedEdge_nonempty hg hne),
    dif_pos (B.projectedEdge_card_le hg)]
  exact
    mixedConfigurationFaceWeight_decompose P A
      (B.orderedConfigurationBundleFace hg hne)
      (B.orderedConfigurationBundleFaceTuple hg hne y)

theorem hasTaoBundleCountingStep_orderedConfiguration
    [Nonempty G]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (β : ℕ → ℝ) (τ : ℝ)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hlocalized :
      HasOrderedConfigurationBundleLocalizedDefect P A β)
    (hfrozen :
      HasOrderedConfigurationBundleFrozenUniformity P A τ) :
    HasTaoBundleCountingStep
      (H := orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      β τ := by
  intro K _instK _decK B hclosed g₀ hg₀ hmax
  by_cases hne : g₀.Nonempty
  · let W :=
      B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)
    let p :=
      orderedConfigurationBaseDensity P A
        (g₀.image B.projection)
    let b :=
      B.orderedConfigurationBundleDefect
        P A hg₀ hne
    let c :=
      B.orderedConfigurationBundleUniform
        P A hg₀ hne
    let bLocalized :=
      B.orderedConfigurationBundleLocalizedDefect
        P A hg₀ hne
    have hdecomp :
        ∀ y, W g₀ y = p + b y + c y := by
      intro y
      simpa only [W, p, b, c] using
        B.pullback_orderedConfigurationBaseWeight_decompose
          P A hg₀ hne y
    have hcount :
        B.bundleCount W =
          p * (B.eraseEdge g₀).bundleCount W +
            B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W :=
      B.bundleCount_decompose_edge
        W hg₀ p b c hdecomp
    have herase :
        (B.eraseEdge g₀).bundleCount W =
          (B.eraseEdge g₀).bundleCount
            ((B.eraseEdge g₀).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) := by
      exact
        B.eraseEdge_bundleCount_pullback g₀
          (orderedConfigurationBaseWeight A)
    have hIdempotent :
        B.WeightsIdempotent W := by
      exact B.pullbackBaseEdgeWeight_weightsIdempotent
        (orderedConfigurationBaseWeight A)
        (orderedConfigurationBaseWeight_idempotent A)
    have hlocalizeContribution :
        B.edgeContribution g₀ b W =
          B.edgeContribution g₀ bLocalized W := by
      change B.edgeContribution g₀ b W =
        B.edgeContribution g₀
          (fun y =>
            b y * B.strictBoundaryLocalProduct g₀ W y) W
      exact B.edgeContribution_mul_strictBoundaryLocalProduct
        g₀ b W hIdempotent
    have hdefect :
        |B.edgeContribution g₀ b W| ≤
          Real.sqrt
            ((β g₀.card *
                (B.strictBoundary g₀).bundleCount
                  ((B.strictBoundary g₀).pullbackBaseEdgeWeight
                      (orderedConfigurationBaseWeight A))) *
              ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                  (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                      (orderedConfigurationBaseWeight A))) := by
      rw [hlocalizeContribution]
      exact
        B.abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
          hclosed hg₀ hmax
          (orderedConfigurationBaseWeight A)
          (orderedConfigurationBaseWeight_unitInterval A)
          (orderedConfigurationBaseWeight_idempotent A)
          bLocalized (hβ g₀.card)
          (hlocalized K B hclosed hg₀ hmax hne)
    have huniform :
        |B.edgeContribution g₀ c W| ≤ τ := by
      exact B.abs_edgeContribution_le_of_frozen
        g₀ c W
        (hfrozen K B hclosed hg₀ hmax hne)
    rw [hcount, herase]
    calc
      |p *
              (B.eraseEdge g₀).bundleCount
                ((B.eraseEdge g₀).pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) +
            B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W -
          p *
              (B.eraseEdge g₀).bundleCount
                ((B.eraseEdge g₀).pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A))| =
          |B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W| := by
        congr 1
        ring
      _ ≤
          |B.edgeContribution g₀ b W| +
            |B.edgeContribution g₀ c W| :=
        abs_add_le _ _
      _ ≤
          Real.sqrt
              ((β g₀.card *
                  (B.strictBoundary g₀).bundleCount
                    ((B.strictBoundary g₀).pullbackBaseEdgeWeight
                        (orderedConfigurationBaseWeight A))) *
                ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                    (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                        (orderedConfigurationBaseWeight A))) +
            τ :=
        add_le_add hdefect huniform
  · have hg₀empty : g₀ = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    subst g₀
    let W :=
      B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)
    have hweight :
        ∀ y, W ∅ y = 1 := by
      intro y
      dsimp only [W]
      rw [B.pullbackBaseEdgeWeight_of_mem
        (orderedConfigurationBaseWeight A) hg₀ y]
      simp only [Finset.image_empty]
      exact orderedConfigurationBaseWeight_empty A
        (B.projectedEdgeTuple hg₀ y)
    have hcount :
        B.bundleCount W =
          (B.eraseEdge ∅).bundleCount
            ((B.eraseEdge ∅).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) := by
      calc
        B.bundleCount W =
            B.edgeContribution ∅ (W ∅) W :=
          B.bundleCount_eq_edgeContribution W hg₀
        _ =
            B.edgeContribution ∅ (fun _ => 1) W := by
          apply congrArg
            (fun q => B.edgeContribution ∅ q W)
          funext y
          exact hweight y
        _ = (B.eraseEdge ∅).bundleCount W := by
          rw [B.edgeContribution_const]
          simp
        _ =
            (B.eraseEdge ∅).bundleCount
              ((B.eraseEdge ∅).pullbackBaseEdgeWeight
                (orderedConfigurationBaseWeight A)) :=
          B.eraseEdge_bundleCount_pullback ∅
            (orderedConfigurationBaseWeight A)
    rw [hcount, Finset.image_empty,
      orderedConfigurationBaseDensity_empty,
      one_mul, sub_self, abs_zero]
    exact add_nonneg (Real.sqrt_nonneg _) hτ

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

theorem hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (hcut :
      HasOrderedConfigurationBundleFrozenCutRepresentation P A) :
    HasOrderedConfigurationBundleFrozenUniformity P A τ := by
  intro K _instK _decK B hclosed g₀ hg₀ hmax hne z
  obtain ⟨u, hu, hreindex⟩ :=
    hcut K B hclosed hg₀ hmax hne z
  rw [hreindex]
  exact
    mixedConfigurationFace_isFaceCutRegular
      P A (fun _ => τ) hregular
      (B.orderedConfigurationBundleFace hg₀ hne)
      u hu

end HypergraphBundle

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedFullBoundary
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem orderedFullLowerBoundaryPartition_le_immediate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    orderedFullLowerBoundaryPartition C e ≤
      orderedBoundaryPartition
        (positiveFaceLowerLayer C e) e.face := by
  exact FacePartition.join_le_left _ _

theorem mem_orderedFullLowerBoundaryPartition_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    y ∈ (orderedFullLowerBoundaryPartition C e).part x ↔
      y ∈
          (orderedBoundaryPartition
            (positiveFaceLowerLayer C e) e.face).part x ∧
        ∀ d : ProperPositiveOrderedSubface e.lowerRank.1,
          orderedFaceTuple d.face y ∈
            (C.partition
              (orderedFullLowerComplexRank e d)
              (orderedFullLowerAmbientFace e d)).part
              (orderedFaceTuple d.face x) := by
  rw [orderedFullLowerBoundaryPartition, FacePartition.part_join,
    Finset.mem_inter, orderedFullLowerPositivePartition,
    FacePartition.mem_part_joinFinset_iff]
  simp only [Finset.mem_univ, forall_const,
    orderedFullLowerConstituentPartition,
    FacePartition.mem_part_pullback_iff_image_mem]

theorem SourceFullMixedGoodAtFace.localized_defect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ)
    (hgood : SourceFullMixedGoodAtFace P A e α β) :
    sourceFullMixedLocalizedDefectSq P A e ≤
      β * mean (sourceFullMixedBoundaryWeight P A e) := by
  unfold sourceFullMixedLocalizedDefectSq
  apply mean_mul_partitionAtomIndicator_le
    (orderedFullLowerBoundaryPartition P.coarse e)
    (fun y => sourceFullMixedDefect P A e y ^ 2)
    (orderedFullLowerBoundaryAtomAt P.coarse e
      (orderedFaceTuple e.face A.witness))
  have hrep :
      (orderedFullLowerBoundaryPartition P.coarse e).representative
          (orderedFullLowerBoundaryAtomAt P.coarse e
            (orderedFaceTuple e.face A.witness)) ∈
        (orderedFullLowerBoundaryPartition P.coarse e).part
          (orderedFaceTuple e.face A.witness) := by
    exact
      (orderedFullLowerBoundaryPartition P.coarse e).representative_mem
        (orderedFullLowerBoundaryAtomAt P.coarse e
          (orderedFaceTuple e.face A.witness))
  have heq :=
    conditionalMean_eq_of_mem_part
      (orderedFullLowerBoundaryPartition P.coarse e)
      (fun y => sourceFullMixedDefect P A e y ^ 2)
      hrep
  rw [heq]
  exact hgood.2

theorem ClosedOrderedAtomConfiguration.IsSourceFullMixedGood.localized_defect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (e : PositiveOrderedFace k r) :
    sourceFullMixedLocalizedDefectSq P A e ≤
      β e.rank *
        mean (sourceFullMixedBoundaryWeight P A e) :=
  (hgood e).localized_defect P A e
    (α e.rank) (β e.rank)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleSourceGoodnessBridge
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

theorem ambientPositiveFaceOfProperSubface_edge_ssubset
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    positiveOrderedFaceEdge
        (ambientPositiveFaceOfProperSubface e d) ⊂
      positiveOrderedFaceEdge e := by
  constructor
  · intro v hv
    rw [mem_positiveOrderedFaceEdge] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨d.face i, rfl⟩
  · intro h
    have hcard :=
      Finset.card_le_card h
    rw [positiveOrderedFaceEdge_card,
      positiveOrderedFaceEdge_card] at hcard
    exact
      (Nat.not_le_of_gt
        (properPositiveOrderedSubface_rank_lt_upper d)) hcard

theorem exists_properPositiveOrderedSubface_of_edge_ssubset
    (e f : PositiveOrderedFace k r)
    (hfe :
      positiveOrderedFaceEdge f ⊂
        positiveOrderedFaceEdge e) :
    ∃ d : ProperPositiveOrderedSubface e.lowerRank.1,
      ambientPositiveFaceOfProperSubface e d = f := by
  have hrank : f.rank < e.rank := by
    rw [← positiveOrderedFaceEdge_card,
      ← positiveOrderedFaceEdge_card]
    exact Finset.card_lt_card hfe
  have hrange :
      Set.range f.face ⊆ Set.range e.face := by
    intro v hv
    rw [← mem_positiveOrderedFaceEdge] at hv ⊢
    exact hfe.1 hv
  choose q hq using fun i : Fin (f.lowerRank.1 + 1) =>
    hrange ⟨i, rfl⟩
  have hqmono : StrictMono q := by
    intro i j hij
    apply e.face.lt_iff_lt.mp
    rw [hq i, hq j]
    exact f.face.strictMono hij
  let dface : OrderedFace
      (e.lowerRank.1 + 1) (f.lowerRank.1 + 1) :=
    OrderEmbedding.ofStrictMono q hqmono
  have hdlt : f.lowerRank.1 < e.lowerRank.1 := by
    simpa [PositiveOrderedFace.rank] using hrank
  let d : ProperPositiveOrderedSubface e.lowerRank.1 :=
    ⟨⟨f.lowerRank.1, hdlt⟩, dface⟩
  refine ⟨d, ?_⟩
  apply positiveOrderedFaceEdge_injective
  apply Finset.Subset.antisymm
  · intro v hv
    rw [mem_positiveOrderedFaceEdge] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨i, (hq i).symm⟩
  · intro v hv
    rw [mem_positiveOrderedFaceEdge] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨i, hq i⟩

theorem positiveOrderedFaceEdge_boundary_ssubset
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    positiveOrderedFaceEdge (e.boundary hpos i) ⊂
      positiveOrderedFaceEdge e := by
  rcases e with ⟨⟨j, hjr⟩, eface⟩
  cases j with
  | zero =>
      simp at hpos
  | succ n =>
      constructor
      · intro v hv
        rw [mem_positiveOrderedFaceEdge] at hv ⊢
        obtain ⟨q, rfl⟩ := hv
        exact ⟨i.succAbove q, rfl⟩
      · intro h
        have hc := Finset.card_le_card h
        rw [positiveOrderedFaceEdge_card,
          positiveOrderedFaceEdge_card] at hc
        exact
          (Nat.not_le_of_gt
            ((⟨⟨n + 1, hjr⟩, eface⟩ :
                PositiveOrderedFace k r).boundary_rank_lt
              hpos i)) hc

theorem sourceFullMixedBoundaryWeight_eq_strictFaceProduct
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    sourceFullMixedBoundaryWeight P A e y =
      partialConfigurationWeight A
        (orderedConfigurationStrictFaceFamily e)
        (extendConfigurationFaceTuple P A e y) := by
  classical
  let x := extendConfigurationFaceTuple P A e y
  have hxe : orderedFaceTuple e.face x = y :=
    orderedFaceTuple_extendConfigurationFaceTuple P A e y
  by_cases hy :
      y ∈ (orderedFullLowerBoundaryPartition P.coarse e).part
        (orderedFaceTuple e.face A.witness)
  · rw [show sourceFullMixedBoundaryWeight P A e y = 1 by
          exact partitionAtomIndicator_of_mem _ _ hy]
    unfold partialConfigurationWeight
    symm
    apply Finset.prod_eq_one
    intro f hf
    have hfe :
      positiveOrderedFaceEdge f ⊂
          positiveOrderedFaceEdge e :=
      (mem_orderedConfigurationStrictFaceFamily e f).1
        hf
    obtain ⟨d, rfl⟩ :=
      exists_properPositiveOrderedSubface_of_edge_ssubset e f hfe
    unfold configurationFaceWeight
    apply partitionAtomIndicator_of_mem
    have hd :=
      (mem_orderedFullLowerBoundaryPartition_part_iff
        P.coarse e
        (orderedFaceTuple e.face A.witness) y).1 hy |>.2 d
    change
      orderedFaceTuple
          (orderedFullLowerAmbientFace e d) x ∈
        (A.atom
          (orderedFullLowerComplexRank e d)
          (orderedFullLowerAmbientFace e d)).1
    rw [A.atom_eq_partitionAtomAt]
    change
      orderedFaceTuple d.face
          (orderedFaceTuple e.face x) ∈
        (P.coarse.partition
          (orderedFullLowerComplexRank e d)
          (orderedFullLowerAmbientFace e d)).part
          (orderedFaceTuple d.face
            (orderedFaceTuple e.face A.witness))
    rw [hxe]
    exact hd
  · rw [show sourceFullMixedBoundaryWeight P A e y = 0 by
          exact partitionAtomIndicator_of_not_mem _ _ hy]
    by_contra hprod
    have hprod' :
        partialConfigurationWeight A
            (orderedConfigurationStrictFaceFamily e) x ≠ 0 :=
      fun hz => hprod hz.symm
    have hall :
        ∀ f ∈ orderedConfigurationStrictFaceFamily e,
          configurationFaceWeight A f
              (orderedFaceTuple f.face x) ≠ 0 := by
      intro f hf
      exact Finset.prod_ne_zero_iff.mp
        (by simpa [partialConfigurationWeight] using hprod') f hf
    exfalso
    apply hy
    apply
      (mem_orderedFullLowerBoundaryPartition_part_iff
        P.coarse e
        (orderedFaceTuple e.face A.witness) y).2
    constructor
    · rw [mem_orderedBoundaryPartition_part_iff]
      intro i
      by_cases he0 : e.lowerRank.1 = 0
      · have hsub :
            eraseBoundaryCoordinate i y =
              eraseBoundaryCoordinate i
                (orderedFaceTuple e.face A.witness) :=
          by
            funext q
            have hq : q.1 < 0 := by
              simpa [he0] using q.2
            omega
        rw [hsub]
        exact
          (positiveFaceLowerLayer P.coarse e
            (eraseBoundaryFace e.face i)).mem_part
            (Finset.mem_univ _)
      · have hepos : 0 < e.lowerRank.1 :=
          Nat.pos_of_ne_zero he0
        let f := e.boundary hepos i
        have hfstrict :
            positiveOrderedFaceEdge f ⊂
              positiveOrderedFaceEdge e := by
          exact positiveOrderedFaceEdge_boundary_ssubset
            e hepos i
        have hfmem :
            f ∈ orderedConfigurationStrictFaceFamily e :=
          (mem_orderedConfigurationStrictFaceFamily e f).2 hfstrict
        have hfweight := hall f hfmem
        rw [← hxe]
        exact
          coarse_boundary_mem_of_coarse_configuration_weight_ne_zero
            P A e hepos i x hfweight
    · intro d
      let f := ambientPositiveFaceOfProperSubface e d
      have hfmem :
          f ∈ orderedConfigurationStrictFaceFamily e :=
        (mem_orderedConfigurationStrictFaceFamily e f).2
          (ambientPositiveFaceOfProperSubface_edge_ssubset e d)
      have hfweight := hall f hfmem
      unfold configurationFaceWeight at hfweight
      have hfatom :
          orderedFaceTuple f.face x ∈
            (A.atom f.lowerRank.succ f.face).1 := by
        by_contra hnot
        exact hfweight
          (partitionAtomIndicator_of_not_mem _ _ hnot)
      rw [A.atom_eq_partitionAtomAt] at hfatom
      change
        orderedFaceTuple
            (orderedFullLowerAmbientFace e d) x ∈
          (P.coarse.partition
            (orderedFullLowerComplexRank e d)
            (orderedFullLowerAmbientFace e d)).part
            (orderedFaceTuple
              (orderedFullLowerAmbientFace e d) A.witness)
        at hfatom
      simp only [orderedFaceTuple_orderedFullLowerAmbientFace]
        at hfatom
      simpa only [hxe] using hfatom

theorem liftProjectedSubedge_subset
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (g₀ : Finset K) (t : Finset (Fin k)) :
    B.liftProjectedSubedge g₀ t ⊆ g₀ := by
  exact Finset.filter_subset _ _

theorem image_liftProjectedSubedge
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (g₀ : Finset K) {t : Finset (Fin k)}
    (ht : t ⊆ g₀.image B.projection) :
    (B.liftProjectedSubedge g₀ t).image B.projection = t := by
  ext j
  constructor
  · intro hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hv).2
  · intro hj
    obtain ⟨v, hvg, hvj⟩ :=
      Finset.mem_image.mp (ht hj)
    apply Finset.mem_image.mpr
    refine ⟨v, Finset.mem_filter.mpr ⟨hvg, ?_⟩, hvj⟩
    exact hvj ▸ hj

theorem liftProjectedSubedge_image_eq
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hgg₀ : g ⊆ g₀) :
    B.liftProjectedSubedge g₀
        (g.image B.projection) = g := by
  ext v
  constructor
  · intro hv
    have hvg₀ := (Finset.mem_filter.mp hv).1
    obtain ⟨w, hwg, hwv⟩ :=
      Finset.mem_image.mp (Finset.mem_filter.mp hv).2
    have hwg₀ : w ∈ g₀ := hgg₀ hwg
    have hwv' : w = v :=
      B.projection_injective_on_edge g₀ hg₀ hwg₀ hvg₀ hwv
    exact hwv' ▸ hwg
  · intro hv
    exact Finset.mem_filter.mpr
      ⟨hgg₀ hv,
        Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

theorem strictBoundaryLocalProduct_orderedConfiguration_eq_sourceFull
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (y : {v : K // v ∈ g₀} → G) :
    B.strictBoundaryLocalProduct g₀
        (B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A)) y =
      sourceFullMixedBoundaryWeight P A
        (B.orderedConfigurationBundleFace hg₀ hne)
        (B.orderedConfigurationBundleFaceTuple hg₀ hne y) := by
  classical
  let e := B.orderedConfigurationBundleFace hg₀ hne
  let u := B.orderedConfigurationBundleFaceTuple hg₀ hne y
  let x := extendConfigurationFaceTuple P A e u
  have heedge :
      positiveOrderedFaceEdge e =
        g₀.image B.projection := by
    dsimp [e, orderedConfigurationBundleFace]
    exact positiveOrderedFaceEdge_ofEdge
      (g₀.image B.projection)
      (B.projectedEdge_nonempty hg₀ hne)
      (B.projectedEdge_card_le hg₀)
  let z : EdgeComplement g₀ → G :=
    fun v => A.witness (B.projection v.1)
  let xK : K → G :=
    (splitEdgeEquiv g₀).symm (y, z)
  have hxK : edgeTuple g₀ xK = y := by
    exact edgeTuple_splitEdgeEquiv_symm g₀ y z
  have hlocalProduct :
      B.strictBoundaryLocalProduct g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) y =
        (B.strictBoundary g₀).bundleProduct
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) xK := by
    calc
      B.strictBoundaryLocalProduct g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) y =
        B.strictBoundaryLocalProduct g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A))
          (edgeTuple g₀ xK) := by
            rw [hxK]
      _ =
        (B.strictBoundary g₀).bundleProduct
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) xK :=
        B.strictBoundaryLocalProduct_edgeTuple g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) xK
  have hempty : ∅ ∈ (B.strictBoundary g₀).edges := by
    apply (B.mem_strictBoundary_edges g₀ ∅).2
    refine ⟨hclosed hg₀ (Finset.empty_subset g₀), ?_⟩
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.empty_subset _, hne.ne_empty.symm⟩
  have hemptyWeight :
      B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) ∅
          (edgeTuple ∅ xK) = 1 := by
    rw [B.pullbackBaseEdgeWeight_of_mem
      (orderedConfigurationBaseWeight A)
      ((B.mem_strictBoundary_edges g₀ ∅).1 hempty).1]
    exact orderedConfigurationBaseWeight_empty A _
  rw [hlocalProduct]
  rw [sourceFullMixedBoundaryWeight_eq_strictFaceProduct P A e u]
  unfold bundleProduct partialConfigurationWeight
  rw [← Finset.prod_erase_mul _ _ hempty,
    hemptyWeight, mul_one]
  apply Finset.prod_bij
    (fun g _hg =>
      positiveOrderedFaceOfEdge
        (g.image B.projection)
        (Finset.image_nonempty.mpr
          (Finset.nonempty_iff_ne_empty.mpr
            (Finset.mem_erase.mp _hg).1))
        (B.projectedEdge_card_le
          (((B.mem_strictBoundary_edges g₀ g).1
            (Finset.mem_of_mem_erase _hg)).1)))
  · intro g hg
    simp only [Finset.mem_erase] at hg
    rw [mem_orderedConfigurationStrictFaceFamily]
    rw [positiveOrderedFaceEdge_ofEdge]
    rw [heedge]
    have hgstrict :=
      ((B.mem_strictBoundary_edges g₀ g).1 hg.2).2
    constructor
    · intro j hj
      obtain ⟨v, hvg, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_image.mpr
        ⟨v, hgstrict.1 hvg, rfl⟩
    · intro hreverse
      apply hgstrict.2
      intro v hvg₀
      obtain ⟨w, hwg, hwv⟩ :=
        Finset.mem_image.mp
          (hreverse
            (Finset.mem_image.mpr
              ⟨v, hvg₀, rfl⟩))
      have hwg₀ : w ∈ g₀ := hgstrict.1 hwg
      have hwv' : w = v :=
        B.projection_injective_on_edge
          g₀ hg₀ hwg₀ hvg₀ hwv
      exact hwv' ▸ hwg
  · intro g₁ hg₁ g₂ hg₂ heq
    have himage :
        g₁.image B.projection =
          g₂.image B.projection := by
      simpa only [positiveOrderedFaceEdge_ofEdge] using
        congrArg positiveOrderedFaceEdge heq
    have hg₁sub :=
      ((B.mem_strictBoundary_edges g₀ g₁).1
        (Finset.mem_of_mem_erase hg₁)).2.1
    have hg₂sub :=
      ((B.mem_strictBoundary_edges g₀ g₂).1
        (Finset.mem_of_mem_erase hg₂)).2.1
    rw [← B.liftProjectedSubedge_image_eq hg₀ hg₁sub,
      ← B.liftProjectedSubedge_image_eq hg₀ hg₂sub,
      himage]
  · intro f hf
    have hfe :=
      (mem_orderedConfigurationStrictFaceFamily e f).1 hf
    let t := positiveOrderedFaceEdge f
    let g := B.liftProjectedSubedge g₀ t
    have ht : t ⊆ g₀.image B.projection := by
      simpa [e, orderedConfigurationBundleFace,
        positiveOrderedFaceEdge_ofEdge] using hfe.1
    have hgsub : g ⊆ g₀ :=
      B.liftProjectedSubedge_subset g₀ t
    have hgmem : g ∈ B.edges :=
      hclosed hg₀ hgsub
    have himage : g.image B.projection = t :=
      B.image_liftProjectedSubedge g₀ ht
    have hgne : g ≠ ∅ := by
      intro hzero
      have : t = ∅ := by simpa [hzero] using himage.symm
      have htne := positiveOrderedFaceEdge_nonempty f
      change t.Nonempty at htne
      rw [this] at htne
      exact Finset.not_nonempty_empty htne
    have hgproper : g ⊂ g₀ := by
      refine ⟨hgsub, ?_⟩
      intro hgg
      have hgeq : g = g₀ :=
        Finset.Subset.antisymm hgsub hgg
      have : t = g₀.image B.projection := by
        rw [← himage, hgeq]
      apply hfe.2
      rw [heedge, ← this]
    refine ⟨g, Finset.mem_erase.mpr
      ⟨hgne,
        (B.mem_strictBoundary_edges g₀ g).2
          ⟨hgmem, hgproper⟩⟩, ?_⟩
    apply positiveOrderedFaceEdge_injective
    simpa only [positiveOrderedFaceEdge_ofEdge] using himage
  · intro g hg
    simp only [Finset.mem_erase] at hg
    have hgB :=
      ((B.mem_strictBoundary_edges g₀ g).1 hg.2).1
    rw [B.pullbackBaseEdgeWeight_of_mem
      (orderedConfigurationBaseWeight A) hgB]
    unfold orderedConfigurationBaseWeight
    simp only [dif_pos (Finset.image_nonempty.mpr
      (Finset.nonempty_iff_ne_empty.mpr hg.1))]
    simp only [dif_pos (B.projectedEdge_card_le hgB)]
    congr 1
    have hgne : g.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hg.1
    change
      B.orderedConfigurationBundleFaceTuple
          hgB hgne (edgeTuple g xK) =
        orderedFaceTuple
          (B.orderedConfigurationBundleFace hgB hgne).face x
    funext i
    let v : {v : K // v ∈ g} :=
      (B.projectionEquiv hgB).symm
        (B.projectedEdgeOrderIso hgB hgne i)
    have hgsub :
        g ⊆ g₀ :=
      ((B.mem_strictBoundary_edges g₀ g).1 hg.2).2.1
    let v₀ : {v : K // v ∈ g₀} :=
      ⟨v.1, hgsub v.2⟩
    have hprojection :
        (B.orderedConfigurationBundleFace hgB hgne).face i =
          B.projection v₀.1 := by
      calc
        (B.orderedConfigurationBundleFace hgB hgne).face i =
            (B.projectedEdgeOrderIso hgB hgne i).1 := by
          rw [B.projectedEdgeOrderIso_apply_val]
        _ = ((B.projectionEquiv hgB) v).1 := by
          rw [Equiv.apply_symm_apply]
        _ = B.projection v.1 :=
          B.projectionEquiv_apply_val hgB v
        _ = B.projection v₀.1 := rfl
    calc
      B.orderedConfigurationBundleFaceTuple
          hgB hgne (edgeTuple g xK) i =
          xK v.1 := by
        rfl
      _ = y v₀ := by
        have hv := congrFun hxK v₀
        exact hv
      _ = x (B.projection v₀.1) := by
        symm
        exact
          B.extendConfigurationFaceTuple_projection
            P A hg₀ hne y v₀
      _ =
          orderedFaceTuple
            (B.orderedConfigurationBundleFace hgB hgne).face
            x i := by
        rw [orderedFaceTuple, hprojection]

theorem strictBoundary_bundleCount_orderedConfiguration_eq_sourceFullMass
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty) :
    (B.strictBoundary g₀).bundleCount
        ((B.strictBoundary g₀).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A)) =
      mean (sourceFullMixedBoundaryWeight P A
        (B.orderedConfigurationBundleFace hg₀ hne)) := by
  classical
  rw [← B.bundleCount_pullback_eq_of_subset_of_projection_eq
    (B.strictBoundary g₀)
    (Finset.filter_subset _ _)
    rfl
    (orderedConfigurationBaseWeight A)]
  cases isEmpty_or_nonempty G with
  | inl hG =>
      let : IsEmpty G := hG
      have : Nonempty K := ⟨hne.choose⟩
      have :
          Nonempty
            (Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1)) :=
        ⟨⟨0, Nat.succ_pos _⟩⟩
      simp only [bundleCount, mean_empty]
  | inr hG =>
      let : Nonempty G := hG
      unfold bundleCount
      rw [mean_splitEdge g₀]
      unfold mean₂
      have hfiber :
          ∀ y : {v : K // v ∈ g₀} → G,
            mean (fun z : EdgeComplement g₀ → G =>
                (B.strictBoundary g₀).bundleProduct
                  (B.pullbackBaseEdgeWeight
                    (orderedConfigurationBaseWeight A))
                  ((splitEdgeEquiv g₀).symm (y, z))) =
              sourceFullMixedBoundaryWeight P A
                (B.orderedConfigurationBundleFace hg₀ hne)
                (B.orderedConfigurationBundleFaceTupleEquiv
                  hg₀ hne y) := by
        intro y
        calc
          mean (fun z : EdgeComplement g₀ → G =>
              (B.strictBoundary g₀).bundleProduct
                (B.pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A))
                ((splitEdgeEquiv g₀).symm (y, z))) =
              mean (fun _z : EdgeComplement g₀ → G =>
                B.strictBoundaryLocalProduct g₀
                  (B.pullbackBaseEdgeWeight
                    (orderedConfigurationBaseWeight A)) y) := by
            apply congrArg mean
            funext z
            rw [← B.strictBoundaryLocalProduct_edgeTuple g₀
              (B.pullbackBaseEdgeWeight
                (orderedConfigurationBaseWeight A))
              ((splitEdgeEquiv g₀).symm (y, z))]
            rw [edgeTuple_splitEdgeEquiv_symm]
          _ =
              B.strictBoundaryLocalProduct g₀
                (B.pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) y := by
            exact mean_const _
          _ =
              sourceFullMixedBoundaryWeight P A
                (B.orderedConfigurationBundleFace hg₀ hne)
                (B.orderedConfigurationBundleFaceTuple hg₀ hne y) :=
            B.strictBoundaryLocalProduct_orderedConfiguration_eq_sourceFull
              P A hclosed hg₀ hne y
          _ =
              sourceFullMixedBoundaryWeight P A
                (B.orderedConfigurationBundleFace hg₀ hne)
                (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne y) := by
            rw [orderedConfigurationBundleFaceTupleEquiv_apply]
      rw [show
        (fun y : {v : K // v ∈ g₀} → G =>
          mean (fun z : EdgeComplement g₀ → G =>
            (B.strictBoundary g₀).bundleProduct
              (B.pullbackBaseEdgeWeight
                (orderedConfigurationBaseWeight A))
              ((splitEdgeEquiv g₀).symm (y, z)))) =
          fun y =>
            sourceFullMixedBoundaryWeight P A
              (B.orderedConfigurationBundleFace hg₀ hne)
              (B.orderedConfigurationBundleFaceTupleEquiv
                hg₀ hne y) by
        funext y
        exact hfiber y]
      exact mean_equiv
        (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne)
        (fun y =>
          sourceFullMixedBoundaryWeight P A
            (B.orderedConfigurationBundleFace hg₀ hne)
            (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne y))
        (sourceFullMixedBoundaryWeight P A
          (B.orderedConfigurationBundleFace hg₀ hne))
        (fun _ => rfl)

theorem hasOrderedConfigurationBundleLocalizedDefect_of_sourceFullMixedGood
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsSourceFullMixedGood P α β) :
    HasOrderedConfigurationBundleLocalizedDefect P A β := by
  intro K _ _ B hclosed g₀ hg₀ hmax hne
  let e := B.orderedConfigurationBundleFace hg₀ hne
  have hrank : e.rank = g₀.card := by
    unfold e orderedConfigurationBundleFace
    rw [← positiveOrderedFaceEdge_card]
    rw [positiveOrderedFaceEdge_ofEdge]
    exact B.card_image_projection hg₀
  have hlocal := hgood.localized_defect P A α β e
  rw [← hrank]
  rw [B.strictBoundary_bundleCount_orderedConfiguration_eq_sourceFullMass
    P A hclosed hg₀ hne]
  calc
    mean (fun y =>
        B.orderedConfigurationBundleLocalizedDefect
            P A hg₀ hne y ^ 2) =
        sourceFullMixedLocalizedDefectSq P A e := by
      apply mean_equiv
        (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne)
      intro y
      unfold orderedConfigurationBundleLocalizedDefect
        orderedConfigurationBundleDefect
        sourceFullMixedDefect
      rw [B.strictBoundaryLocalProduct_orderedConfiguration_eq_sourceFull
        P A hclosed hg₀ hne y]
      rw [mul_pow, sourceFullMixedBoundaryWeight_sq]
      rw [orderedConfigurationBundleFaceTupleEquiv_apply]
    _ ≤
        β e.rank *
          mean (sourceFullMixedBoundaryWeight P A e) :=
      hlocal

end HypergraphBundle

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.RankwiseBundleEnvelopeSelection
namespace OAI

section

namespace Erdos3.FixedDensity

open Filter Topology

theorem bundleRankwiseDensityFloor_pos
    {α : ℕ → ℝ} (hα : ∀ d, 0 < α d) :
    ∀ d, 0 < bundleRankwiseDensityFloor α d := by
  intro d
  induction d with
  | zero => simpa using hα 0
  | succ d ih =>
      simpa using lt_min ih (hα (d + 1))

theorem bundleRankwiseDensityFloor_le
    (α : ℕ → ℝ) {i d : ℕ} (hid : i ≤ d) :
    bundleRankwiseDensityFloor α d ≤ α i := by
  induction d with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hid
      subst i
      exact le_rfl
  | succ d ih =>
      rw [bundleRankwiseDensityFloor_succ]
      by_cases hi : i = d + 1
      · subst i
        exact min_le_right _ _
      · exact (min_le_left _ _).trans (ih (Nat.le_of_lt_succ (lt_of_le_of_ne hid hi)))

theorem bundleRankwiseStepIncrement_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) (lower : ℕ → ℝ) (d n : ℕ) :
    0 ≤ bundleRankwiseStepIncrement α β μ τ lower d n := by
  unfold bundleRankwiseStepIncrement
  exact add_nonneg
    (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hα _) _))
    (div_nonneg hτ (pow_nonneg (hμ _) _))

theorem bundleRankwiseNextRow_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) (d : ℕ) (lower : ℕ → ℝ) :
    ∀ n, 0 ≤ bundleRankwiseNextRow α β μ τ d lower n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [bundleRankwiseNextRow_succ]
      exact le_max_of_le_right
        (add_nonneg ih
          (bundleRankwiseStepIncrement_nonneg hα hμ hτ lower d n))

theorem bundleRankwiseEnvelopeError_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) :
    ∀ d n, 0 ≤ bundleRankwiseEnvelopeError α β μ τ d n := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d _ih =>
      intro n
      rw [bundleRankwiseEnvelopeError_succ_order]
      exact bundleRankwiseNextRow_nonneg hα hμ hτ d _ n

theorem bundleRankwiseEnvelopeError_monotone_card
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) (d : ℕ) :
    Monotone (bundleRankwiseEnvelopeError α β μ τ d) := by
  apply monotone_nat_of_le_succ
  intro n
  cases d with
  | zero => simp
  | succ d =>
      rw [bundleRankwiseEnvelopeError_succ_order,
        bundleRankwiseEnvelopeError_succ_order,
        bundleRankwiseNextRow_succ]
      exact le_max_of_le_right
        (le_add_of_nonneg_right
          (bundleRankwiseStepIncrement_nonneg hα hμ hτ _ d n))

theorem bundleRankwiseEnvelopeError_le_succ_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ d n ≤
      bundleRankwiseEnvelopeError α β μ τ (d + 1) n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [bundleRankwiseEnvelopeError_succ_order,
        bundleRankwiseNextRow_succ]
      exact le_max_left _ _

theorem bundleRankwiseEnvelopeError_monotone_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    Monotone (fun d => bundleRankwiseEnvelopeError α β μ τ d n) := by
  apply monotone_nat_of_le_succ
  exact fun d => bundleRankwiseEnvelopeError_le_succ_order α β μ τ d n

theorem bundleRankwiseEnvelopeError_isEnvelope
    {α β : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 < α d) (hα_one : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d) (hτ : 0 ≤ τ) :
    IsBundleCountingEnvelope α β
      (bundleRankwiseDensityFloor α) τ
      (bundleRankwiseEnvelopeError α β
        (bundleRankwiseDensityFloor α) τ) := by
  let μ := bundleRankwiseDensityFloor α
  have hμ : ∀ d, 0 < μ d := bundleRankwiseDensityFloor_pos hα
  refine
    { density_pos := hα
      density_le_one := hα_one
      defect_nonneg := hβ
      uniform_nonneg := hτ
      floor_pos := hμ
      rankFloor := ?_
      error_nonneg := bundleRankwiseEnvelopeError_nonneg
        (fun d => (hα d).le) (fun d => (hμ d).le) hτ
      error_mono_order := ?_
      error_mono_card := ?_
      step := ?_ }
  · intro i d hid
    exact bundleRankwiseDensityFloor_le α hid
  · intro d d' n hdd'
    exact (bundleRankwiseEnvelopeError_monotone_order α β μ τ n) hdd'
  · intro d n n' hnn'
    exact (bundleRankwiseEnvelopeError_monotone_card
      (fun q => (hα q).le) (fun q => (hμ q).le) hτ d) hnn'
  · intro d n
    have hstep :
        bundleRankwiseNextRow α β μ τ d
              (bundleRankwiseEnvelopeError α β μ τ d) n +
            bundleRankwiseStepIncrement α β μ τ
              (bundleRankwiseEnvelopeError α β μ τ d) d n ≤
          max (bundleRankwiseEnvelopeError α β μ τ d (n + 1))
            (bundleRankwiseNextRow α β μ τ d
                (bundleRankwiseEnvelopeError α β μ τ d) n +
              bundleRankwiseStepIncrement α β μ τ
                (bundleRankwiseEnvelopeError α β μ τ d) d n) :=
      le_max_right _ _
    simp [μ, bundleRankwiseStepIncrement, add_assoc] at hstep ⊢

theorem bundleReverseDoublingHorizon_two_mul_succ
    {rankBound edgeBound d : ℕ} (hd : d < rankBound) :
    2 * bundleReverseDoublingHorizon rankBound edgeBound (d + 1) =
      bundleReverseDoublingHorizon rankBound edgeBound d := by
  have hsub : rankBound - d = rankBound - (d + 1) + 1 := by
    omega
  simp only [bundleReverseDoublingHorizon, hsub, pow_succ]
  ring

theorem bundleReverseDoublingHorizon_le_zero
    (rankBound edgeBound d : ℕ) :
    bundleReverseDoublingHorizon rankBound edgeBound d ≤
      bundleReverseDoublingHorizon rankBound edgeBound 0 := by
  unfold bundleReverseDoublingHorizon
  apply Nat.mul_le_mul_left
  exact (pow_right_monotone (by norm_num : (1 : ℕ) ≤ 2))
    (Nat.sub_le rankBound d)

theorem bundleRankwiseStepIncrement_le_of_lower_le
    {α β μ : ℕ → ℝ} {τ B η : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hβ : ∀ d, 0 ≤ β d)
    (lower : ℕ → ℝ) (d n : ℕ)
    (hlower_nonneg : ∀ m, 0 ≤ lower m)
    (hlower₁ : lower (n + 1) ≤ B)
    (hlower₂ : lower (2 * (n + 1)) ≤ B)
    (hdefect :
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform :
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    bundleRankwiseStepIncrement α β μ τ lower d n ≤ η := by
  have hlower₁nonneg : 0 ≤ 1 + lower (n + 1) := by
    linarith [hlower_nonneg (n + 1)]
  have hlower₂nonneg : 0 ≤ 1 + lower (2 * (n + 1)) := by
    linarith [hlower_nonneg (2 * (n + 1))]
  have hB₁nonneg : 0 ≤ 1 + B := by
    linarith [hlower_nonneg (n + 1), hlower₁]
  have hproduct :
      (1 + lower (n + 1)) * (1 + lower (2 * (n + 1))) ≤
        (1 + B) * (1 + B) := by
    exact mul_le_mul
      (by linarith)
      (by linarith)
      hlower₂nonneg hB₁nonneg
  have hradicand :
      β (d + 1) *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1))) ≤
        β (d + 1) * (1 + B) * (1 + B) := by
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hproduct (hβ (d + 1))
  have hsqrt :
      Real.sqrt
          (β (d + 1) *
            (1 + lower (n + 1)) *
            (1 + lower (2 * (n + 1)))) ≤
        Real.sqrt (β (d + 1) * (1 + B) * (1 + B)) :=
    Real.sqrt_le_sqrt hradicand
  have hnormalized :
      Real.sqrt
            (β (d + 1) *
              (1 + lower (n + 1)) *
              (1 + lower (2 * (n + 1)))) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2 :=
    (div_le_div_of_nonneg_right hsqrt
      (pow_nonneg (hα (d + 1)) (n + 1))).trans hdefect
  unfold bundleRankwiseStepIncrement
  linarith

theorem bundleRankwiseEnvelopeError_le_finiteBudget
    {α β μ : ℕ → ℝ} {τ η B : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hβ : ∀ d, 0 ≤ β d)
    (hμ : ∀ d, 0 ≤ μ d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound : ℕ) (horizon : ℕ → ℕ)
    (hreverse : ∀ d, d < rankBound →
      2 * horizon (d + 1) ≤ horizon d)
    (hzero : ∀ d, d ≤ rankBound → horizon d ≤ horizon 0)
    (hcap :
      (rankBound : ℝ) * (horizon 0 : ℝ) * η ≤ B)
    (hdefect : ∀ d, d < rankBound → ∀ n, n < horizon (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n, n < horizon (d + 1) →
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    ∀ d, d ≤ rankBound → ∀ n, n ≤ horizon d →
      bundleRankwiseEnvelopeError α β μ τ d n ≤
        (d : ℝ) * (horizon 0 : ℝ) * η := by
  intro d hd
  induction d with
  | zero =>
      intro n hn
      simp
  | succ d ih =>
      have hdlt : d < rankBound := Nat.lt_of_succ_le hd
      let lower := bundleRankwiseEnvelopeError α β μ τ d
      have hlower_nonneg : ∀ m, 0 ≤ lower m :=
        bundleRankwiseEnvelopeError_nonneg hα hμ hτ d
      have hdle : d ≤ rankBound := Nat.le_of_lt hdlt
      have hdbound :
          (d : ℝ) * (horizon 0 : ℝ) * η ≤ B := by
        have hdcast : (d : ℝ) ≤ rankBound := by exact_mod_cast hdle
        have hq0 : 0 ≤ (horizon 0 : ℝ) := by positivity
        have hscale : 0 ≤ (horizon 0 : ℝ) * η := mul_nonneg hq0 hη
        calc
          (d : ℝ) * (horizon 0 : ℝ) * η =
              (d : ℝ) * ((horizon 0 : ℝ) * η) := by ring
          _ ≤ (rankBound : ℝ) * ((horizon 0 : ℝ) * η) :=
            mul_le_mul_of_nonneg_right hdcast hscale
          _ = (rankBound : ℝ) * (horizon 0 : ℝ) * η := by ring
          _ ≤ B := hcap
      have hrow : ∀ m, m ≤ horizon (d + 1) →
          bundleRankwiseNextRow α β μ τ d lower m ≤
            (d : ℝ) * (horizon 0 : ℝ) * η + (m : ℝ) * η := by
        intro m hm
        induction m with
        | zero =>
            simp only [bundleRankwiseNextRow_zero, Nat.cast_zero, zero_mul,
              add_zero]
            exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) hη
        | succ m ihm =>
            have hmle : m ≤ horizon (d + 1) := Nat.le_trans (Nat.le_succ m) hm
            have hm_lt : m < horizon (d + 1) := Nat.lt_of_succ_le hm
            have hsmall₁ : m + 1 ≤ horizon d := by
              have hrev := hreverse d hdlt
              omega
            have hsmall₂ : 2 * (m + 1) ≤ horizon d := by
              have hrev := hreverse d hdlt
              omega
            have hlower₁raw := ih hdle (m + 1) hsmall₁
            have hlower₂raw := ih hdle (2 * (m + 1)) hsmall₂
            have hlower₁ : lower (m + 1) ≤ B := hlower₁raw.trans hdbound
            have hlower₂ : lower (2 * (m + 1)) ≤ B := hlower₂raw.trans hdbound
            have hincrement :
                bundleRankwiseStepIncrement α β μ τ lower d m ≤ η :=
              bundleRankwiseStepIncrement_le_of_lower_le hα hβ lower d m
                hlower_nonneg hlower₁ hlower₂
                (hdefect d hdlt m hm_lt) (huniform d hdlt m hm_lt)
            rw [bundleRankwiseNextRow_succ]
            apply max_le
            · calc
                lower (m + 1) ≤
                    (d : ℝ) * (horizon 0 : ℝ) * η := hlower₁raw
                _ ≤ (d : ℝ) * (horizon 0 : ℝ) * η +
                    ((m + 1 : ℕ) : ℝ) * η :=
                  le_add_of_nonneg_right (mul_nonneg (by positivity) hη)
            · calc
                bundleRankwiseNextRow α β μ τ d lower m +
                      bundleRankwiseStepIncrement α β μ τ lower d m ≤
                    ((d : ℝ) * (horizon 0 : ℝ) * η + (m : ℝ) * η) + η :=
                  add_le_add (ihm hmle) hincrement
                _ = (d : ℝ) * (horizon 0 : ℝ) * η +
                    ((m + 1 : ℕ) : ℝ) * η := by
                  push_cast
                  ring
      intro n hn
      rw [bundleRankwiseEnvelopeError_succ_order]
      have hmain := hrow n hn
      have hnzero : n ≤ horizon 0 := hn.trans (hzero (d + 1) hd)
      have hncast : (n : ℝ) ≤ horizon 0 := by exact_mod_cast hnzero
      have hηscale : (n : ℝ) * η ≤ (horizon 0 : ℝ) * η :=
        mul_le_mul_of_nonneg_right hncast hη
      calc
        bundleRankwiseNextRow α β μ τ d lower n ≤
            (d : ℝ) * (horizon 0 : ℝ) * η + (n : ℝ) * η := hmain
        _ ≤ (d : ℝ) * (horizon 0 : ℝ) * η +
            (horizon 0 : ℝ) * η := add_le_add_right hηscale _
        _ = ((d + 1 : ℕ) : ℝ) * (horizon 0 : ℝ) * η := by
          push_cast
          ring

theorem bundleRankwiseEnvelopeError_le_reverseDoublingBudget
    {α β μ : ℕ → ℝ} {τ η B : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hβ : ∀ d, 0 ≤ β d)
    (hμ : ∀ d, 0 ≤ μ d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound edgeBound : ℕ)
    (hcap :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η ≤ B)
    (hdefect : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    bundleRankwiseEnvelopeError α β μ τ rankBound (edgeBound + 1) ≤
      (rankBound : ℝ) *
        (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η := by
  apply bundleRankwiseEnvelopeError_le_finiteBudget hα hβ hμ hτ hη
    rankBound (bundleReverseDoublingHorizon rankBound edgeBound)
    (fun d hd => (bundleReverseDoublingHorizon_two_mul_succ hd).le)
    (fun d _hd => bundleReverseDoublingHorizon_le_zero rankBound edgeBound d)
    hcap hdefect huniform rankBound le_rfl (edgeBound + 1)
  simp [bundleReverseDoublingHorizon]

theorem bundleRankwiseEnvelope_and_error_lt_half_of_reverseDoublingBudget
    {α β : ℕ → ℝ} {τ η : ℝ}
    (hα : ∀ d, 0 < α d) (hα_one : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound edgeBound : ℕ)
    (hcap :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η ≤ 1)
    (hfinal :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η < 1 / 2)
    (hdefect : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + (1 : ℝ)) * (1 + (1 : ℝ))) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      τ /
          (bundleRankwiseDensityFloor α (d + 1)) ^ (n + 1) ≤
        η / 2) :
    IsBundleCountingEnvelope α β
        (bundleRankwiseDensityFloor α) τ
        (bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ) ∧
      bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ rankBound edgeBound < 1 / 2 := by
  have hμ : ∀ d, 0 ≤ bundleRankwiseDensityFloor α d :=
    fun d => (bundleRankwiseDensityFloor_pos hα d).le
  have hbound :=
    bundleRankwiseEnvelopeError_le_reverseDoublingBudget
      (fun d => (hα d).le) hβ hμ hτ hη rankBound edgeBound
      hcap hdefect huniform
  have hcard :
      bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ rankBound edgeBound ≤
        bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ rankBound (edgeBound + 1) :=
    (bundleRankwiseEnvelopeError_monotone_card
      (fun d => (hα d).le) hμ hτ rankBound) (Nat.le_succ edgeBound)
  exact ⟨bundleRankwiseEnvelopeError_isEnvelope hα hα_one hβ hτ,
    (hcard.trans hbound).trans_lt hfinal⟩

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SourceFullOrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

theorem partialConfigurationWeight_univ_eq_zero_of_not_occurrence
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness)
    {x : Fin k → G} (hx : ¬H.IsOccurrence x) :
    partialConfigurationWeight A Finset.univ x = 0 := by
  have hmissing :
      ∃ e : OrderedFace k (n + 1),
        orderedFaceTuple e x ∉
          (A.atom (Fin.last (n + 1)) e).1 := by
    by_contra h
    push Not at h
    exact hx
      (A.isOccurrence_of_mem_topAtoms
        H hC hA x h)
  obtain ⟨e, he⟩ := hmissing
  unfold partialConfigurationWeight
  apply Finset.prod_eq_zero
    (Finset.mem_univ (topPositiveOrderedFace e))
  unfold configurationFaceWeight
  change
    partitionAtomIndicator
        (C.partition (Fin.last (n + 1)) e)
        (A.atom (Fin.last (n + 1)) e)
        (orderedFaceTuple e x) =
      0
  exact
    partitionAtomIndicator_of_not_mem
      (C.partition (Fin.last (n + 1)) e)
      (A.atom (Fin.last (n + 1)) e) he

theorem partialConfigurationWeight_univ_le_patternWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness)
    (x : Fin k → G) :
    partialConfigurationWeight A Finset.univ x ≤
      H.toWeighted.patternWeight x := by
  by_cases hx : H.IsOccurrence x
  · rw [H.toWeighted_patternWeight_of_occurrence hx]
    exact partialConfigurationWeight_le_one
      A Finset.univ x
  · rw [H.toWeighted_patternWeight_of_not_occurrence hx,
      partialConfigurationWeight_univ_eq_zero_of_not_occurrence
        H hC A hA hx]

theorem fullConfigurationCount_le_patternCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness) :
    fullConfigurationCount A ≤
      H.toWeighted.patternCount := by
  unfold fullConfigurationCount partialConfigurationCount
    WeightedOrderedPattern.patternCount
  exact mean_mono
    (partialConfigurationWeight_univ_le_patternWeight
      H hC A hA)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedCoarseFineComplex

theorem sourceFullAtomDefectSq_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    0 ≤ P.sourceFullAtomDefectSq e upper a x := by
  exact atomBoundaryDefectSq_nonneg _ _ upper a x

@[simp]
theorem mem_sourceFullLargeDefectBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (β : ℝ)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullLargeDefectBaseSupport e upper a β ↔
      β <
        conditionalMean
          (orderedFullLowerBoundaryPartition P.coarse e)
          (P.sourceFullAtomDefectSq e upper a) x := by
  exact
    mem_largeAverageBaseSupport
      (orderedFullLowerBoundaryPartition P.coarse e)
      (P.sourceFullAtomDefectSq e upper a) β x

theorem mul_mean_indicator_sourceFullLargeDefectBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {β : ℝ} (hβ : 0 ≤ β) :
    β * mean (finsetIndicator
        (P.sourceFullLargeDefectBaseSupport e upper a β)) ≤
      mean (P.sourceFullAtomDefectSq e upper a) := by
  exact
    mul_mean_indicator_largeAverageBaseSupport_le
      (orderedFullLowerBoundaryPartition P.coarse e)
      (P.sourceFullAtomDefectSq e upper a)
      (P.sourceFullAtomDefectSq_nonneg e upper a)
      hβ

theorem mean_indicator_sourceFullLargeDefectBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {β : ℝ} (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullLargeDefectBaseSupport e upper a β)) ≤
      mean (P.sourceFullAtomDefectSq e upper a) / β := by
  apply (le_div_iff₀ hβ).2
  simpa [mul_comm] using
    P.mul_mean_indicator_sourceFullLargeDefectBaseSupport_le
      e upper a hβ.le

theorem orderedAtomEnergy_sub_eq_sum_mean_sourceFullAtomDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G)) :
    orderedAtomEnergy
          (positiveFaceLowerLayer P.fine e) e.face upper -
        orderedAtomEnergy
          (positiveFaceLowerLayer P.coarse e) e.face upper =
      ∑ a : upper.parts,
        mean (P.sourceFullAtomDefectSq e upper a) := by
  rw [orderedAtomEnergy_sub_eq_sum_mean_sq
    (fine := positiveFaceLowerLayer P.fine e)
    (coarse := positiveFaceLowerLayer P.coarse e)
    (fun f => P.refines e.lowerRank.castSucc f)
    e.face upper]
  rfl

@[simp]
theorem mem_sourceFullAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (α β : ℝ)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullAtomBadBaseSupport e upper a α β ↔
      conditionalMean
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          (partitionAtomIndicator upper a) x < α ∨
        β <
          conditionalMean
            (orderedFullLowerBoundaryPartition P.coarse e)
            (P.sourceFullAtomDefectSq e upper a) x := by
  rw [sourceFullAtomBadBaseSupport, Finset.mem_union,
    mem_smallAverageBaseSupport,
    P.mem_sourceFullLargeDefectBaseSupport]

theorem mean_indicator_atom_inter_sourceFullAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (a.1 ∩ P.sourceFullAtomBadBaseSupport
          e upper a α β)) ≤
      α + mean (P.sourceFullAtomDefectSq e upper a) / β := by
  calc
    mean (finsetIndicator
        (a.1 ∩ P.sourceFullAtomBadBaseSupport
          e upper a α β)) ≤
        mean (finsetIndicator
          (a.1 ∩
            smallAverageBaseSupport
              (orderedBoundaryPartition
                (positiveFaceLowerLayer P.coarse e) e.face)
              (partitionAtomIndicator upper a) α)) +
          mean (finsetIndicator
            (P.sourceFullLargeDefectBaseSupport
              e upper a β)) := by
      exact
        mean_indicator_inter_union_le_add
          a.1
          (smallAverageBaseSupport
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.coarse e) e.face)
            (partitionAtomIndicator upper a) α)
          (P.sourceFullLargeDefectBaseSupport e upper a β)
    _ ≤
        α + mean (P.sourceFullAtomDefectSq e upper a) / β :=
      add_le_add
        (mean_indicator_inter_smallAverageBaseSupport_le
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          a.1 hα)
        (P.mean_indicator_sourceFullLargeDefectBaseSupport_le
          e upper a hβ)

@[simp]
theorem mem_sourceFullOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (α β : ℝ) (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullOwnAtomBadBaseSupport e upper α β ↔
      x ∈ P.sourceFullAtomBadBaseSupport e upper
        (partitionAtomAt upper x) α β := by
  classical
  constructor
  · intro hx
    rw [sourceFullOwnAtomBadBaseSupport] at hx
    obtain ⟨a, _ha, hxpart⟩ :=
      Finset.mem_biUnion.mp hx
    have hxa : x ∈ a.1 :=
      (Finset.mem_inter.mp hxpart).1
    have hbad :
        x ∈ P.sourceFullAtomBadBaseSupport
          e upper a α β :=
      (Finset.mem_inter.mp hxpart).2
    have hcanonical : partitionAtomAt upper x = a :=
      (partitionAtomAt_eq_iff_mem upper x a).2 hxa
    simpa [hcanonical] using hbad
  · intro hbad
    rw [sourceFullOwnAtomBadBaseSupport]
    apply Finset.mem_biUnion.mpr
    refine ⟨partitionAtomAt upper x, Finset.mem_univ _, ?_⟩
    exact Finset.mem_inter.mpr
      ⟨upper.mem_part (Finset.mem_univ x), hbad⟩

theorem mean_indicator_sourceFullOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullOwnAtomBadBaseSupport
          e upper α β)) ≤
      (FacePartition.complexity upper : ℝ) * α +
        (orderedAtomEnergy
            (positiveFaceLowerLayer P.fine e) e.face upper -
          orderedAtomEnergy
            (positiveFaceLowerLayer P.coarse e) e.face upper) / β := by
  calc
    mean (finsetIndicator
        (P.sourceFullOwnAtomBadBaseSupport
          e upper α β)) ≤
        ∑ a : upper.parts,
          mean (finsetIndicator
            (a.1 ∩ P.sourceFullAtomBadBaseSupport
              e upper a α β)) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ : Finset upper.parts)
          (fun a =>
            a.1 ∩ P.sourceFullAtomBadBaseSupport
              e upper a α β)
    _ ≤
        ∑ a : upper.parts,
          (α + mean
            (P.sourceFullAtomDefectSq e upper a) / β) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact
        P.mean_indicator_atom_inter_sourceFullAtomBadBaseSupport_le
          e upper a hα hβ
    _ =
        (FacePartition.complexity upper : ℝ) * α +
          (orderedAtomEnergy
              (positiveFaceLowerLayer P.fine e) e.face upper -
            orderedAtomEnergy
              (positiveFaceLowerLayer P.coarse e) e.face upper) / β := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      rw [Fintype.card_coe]
      rw [← P.orderedAtomEnergy_sub_eq_sum_mean_sourceFullAtomDefectSq
        e upper]
      rfl

@[simp]
theorem mem_sourceFullCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullCoarseOwnAtomBadBaseSupport e α β ↔
      x ∈ P.sourceFullAtomBadBaseSupport e
        (P.coarse.partition e.lowerRank.succ e.face)
        (partitionAtomAt
          (P.coarse.partition e.lowerRank.succ e.face) x)
        α β := by
  exact
    P.mem_sourceFullOwnAtomBadBaseSupport e
      (P.coarse.partition e.lowerRank.succ e.face) α β x

theorem mean_indicator_sourceFullCoarseOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullCoarseOwnAtomBadBaseSupport e α β)) ≤
      (FacePartition.complexity
          (P.coarse.partition e.lowerRank.succ e.face) : ℝ) * α +
        P.coarseUpperFaceAtomEnergyGap
          e.lowerRank e.face / β := by
  unfold sourceFullCoarseOwnAtomBadBaseSupport
    coarseUpperFaceAtomEnergyGap
  exact
    P.mean_indicator_sourceFullOwnAtomBadBaseSupport_le
      e (P.coarse.partition e.lowerRank.succ e.face) hα hβ

end OrderedCoarseFineComplex

theorem sourceFullMixedDefect_eq_orderedAtomBoundaryDefect_of_mem
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G)
    (hy :
      y ∈
        (orderedFullLowerBoundaryPartition P.coarse e).part
          (orderedFaceTuple e.face A.witness)) :
    sourceFullMixedDefect P A e y =
      orderedAtomBoundaryDefect
        (positiveFaceLowerLayer P.fine e)
        (positiveFaceLowerLayer P.coarse e)
        e.face
        (P.coarse.partition e.lowerRank.succ e.face)
        (A.atom e.lowerRank.succ e.face) y := by
  have himmediate :
      y ∈
        (orderedBoundaryPartition
          (positiveFaceLowerLayer P.coarse e) e.face).part
          (orderedFaceTuple e.face A.witness) :=
    FacePartition.part_subset_of_le
      (orderedFullLowerBoundaryPartition_le_immediate
        P.coarse e)
      (orderedFaceTuple e.face A.witness) hy
  have hindicator :
      mixedConfigurationBoundaryIndicator P A e y = 1 := by
    unfold mixedConfigurationBoundaryIndicator
    exact partitionAtomIndicator_of_mem _ _ himmediate
  have h :=
    mixedConfigurationDefect_mul_boundaryIndicator P A e y
  rw [hindicator, mul_one, mul_one] at h
  simpa [sourceFullMixedDefect] using h

theorem conditionalMean_sourceFullMixedDefect_sq_eq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) :
    conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (fun y => sourceFullMixedDefect P A e y ^ 2)
        (orderedFaceTuple e.face A.witness) =
      conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (P.sourceFullAtomDefectSq e
          (P.coarse.partition e.lowerRank.succ e.face)
          (A.atom e.lowerRank.succ e.face))
        (orderedFaceTuple e.face A.witness) := by
  unfold conditionalMean
  apply Finset.expect_congr rfl
  intro y hy
  rw [sourceFullMixedDefect_eq_orderedAtomBoundaryDefect_of_mem
    P A e y hy]
  rfl

namespace ClosedOrderedAtomConfiguration

theorem sourceFullMixedGoodAtFace_of_not_mem_badBase
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ)
    (havoid :
      orderedFaceTuple e.face A.witness ∉
        P.sourceFullCoarseOwnAtomBadBaseSupport e α β) :
    SourceFullMixedGoodAtFace P A e α β := by
  let upper :=
    P.coarse.partition e.lowerRank.succ e.face
  let a : upper.parts :=
    A.atom e.lowerRank.succ e.face
  let x : Fin (e.lowerRank.1 + 1) → G :=
    orderedFaceTuple e.face A.witness
  have hcanonical :
      partitionAtomAt upper x = a := by
    exact (A.atom_eq_partitionAtomAt
      e.lowerRank.succ e.face).symm
  have hlocal :
      x ∉ P.sourceFullAtomBadBaseSupport
        e upper a α β := by
    intro hbad
    apply havoid
    apply
      (P.mem_sourceFullCoarseOwnAtomBadBaseSupport
        e α β x).2
    change
      x ∈ P.sourceFullAtomBadBaseSupport
        e upper (partitionAtomAt upper x) α β
    rw [hcanonical]
    exact hbad
  have hlow :
      x ∉
        smallAverageBaseSupport
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          (partitionAtomIndicator upper a) α := by
    intro h
    exact hlocal (Finset.mem_union_left _ h)
  have hlarge :
      x ∉
        P.sourceFullLargeDefectBaseSupport
          e upper a β := by
    intro h
    exact hlocal (Finset.mem_union_right _ h)
  constructor
  · have hdensity :
        α ≤
          conditionalMean
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.coarse e) e.face)
            (partitionAtomIndicator upper a) x :=
      not_lt.mp fun h =>
        hlow
          ((mem_smallAverageBaseSupport
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.coarse e) e.face)
            (partitionAtomIndicator upper a) α x).2 h)
    simpa [sourceFullMixedCoarseDensity,
      mixedConfigurationCoarseDensity, upper, a, x,
      orderedBoundaryStructured] using hdensity
  · rw [conditionalMean_sourceFullMixedDefect_sq_eq P A e]
    have hdefect :
        conditionalMean
            (orderedFullLowerBoundaryPartition P.coarse e)
            (P.sourceFullAtomDefectSq e upper a) x ≤
          β :=
      not_lt.mp fun h =>
        hlarge
          ((P.mem_sourceFullLargeDefectBaseSupport
            e upper a β x).2 h)
    simpa [upper, a, x] using hdefect

theorem isSourceFullMixedGood_of_avoids_badBases
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (havoid : A.AvoidsSourceFullBadBases P α β) :
    A.IsSourceFullMixedGood P α β := by
  intro e
  exact
    A.sourceFullMixedGoodAtFace_of_not_mem_badBase
      P e (α e.rank) (β e.rank) (havoid e)

end ClosedOrderedAtomConfiguration

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace OrderedCoarseFineComplex

theorem mean_indicator_sourceFullTopBadBaseDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1)) :
    mean (finsetIndicator
        (P.sourceFullTopBadBaseDeletion e α β)) ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          P.coarseUpperFaceAtomEnergyGap
              q.1 (q.2.trans e) /
            β (q.1.1 + 1)) := by
  calc
    mean (finsetIndicator
        (P.sourceFullTopBadBaseDeletion e α β)) ≤
        ∑ q : OrderedPositiveSubface r,
          mean (finsetIndicator
            (orderedFacePullbackFinset q.2
              (P.sourceFullCoarseOwnAtomBadBaseSupport
                ({ lowerRank := q.1
                   face := q.2.trans e } :
                  PositiveOrderedFace k r)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ : Finset (OrderedPositiveSubface r))
          (fun q =>
            orderedFacePullbackFinset q.2
              (P.sourceFullCoarseOwnAtomBadBaseSupport
                ({ lowerRank := q.1
                   face := q.2.trans e } :
                  PositiveOrderedFace k r)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))
    _ ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap
                q.1 (q.2.trans e) /
              β (q.1.1 + 1)) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [mean_indicator_orderedFacePullbackFinset]
      exact
        P.mean_indicator_sourceFullCoarseOwnAtomBadBaseSupport_le
          ({ lowerRank := q.1
             face := q.2.trans e } : PositiveOrderedFace k r)
          (hα q.1.1) (hβ q.1.1)

theorem faceDeletionDensity_sourceFullBadBaseDeletionFamily_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1))
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.sourceFullBadBaseDeletionFamily α β) e ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          P.coarseUpperFaceAtomEnergyGap
              q.1 (q.2.trans e) /
            β (q.1.1 + 1)) := by
  rw [show
      OrderedPattern.faceDeletionDensity
          (P.sourceFullBadBaseDeletionFamily α β) e =
        mean (finsetIndicator
          (P.sourceFullTopBadBaseDeletion e α β)) by
    unfold OrderedPattern.faceDeletionDensity
      sourceFullBadBaseDeletionFamily
    rw [mean_finsetIndicator]]
  exact
    P.mean_indicator_sourceFullTopBadBaseDeletion_le
      e α β hα hβ

end OrderedCoarseFineComplex

namespace ClosedOrderedAtomConfiguration

theorem isSourceFullMixedGood_of_avoids_sourceFullTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (hrk : r ≤ k)
    (P : OrderedCoarseFineComplex G k r)
    (x : Fin k → G) (α β : ℕ → ℝ)
    (havoid :
      ∀ e : OrderedFace k r,
        orderedFaceTuple e x ∉
          P.sourceFullTopBadBaseDeletion e α β) :
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).IsSourceFullMixedGood P α β := by
  apply
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).isSourceFullMixedGood_of_avoids_badBases
      P α β
  intro f hbad
  obtain ⟨e, d, hde⟩ :=
    exists_orderedFace_factor_through
      (Nat.succ_le_iff.mpr f.lowerRank.2) hrk f.face
  apply havoid e
  rw [OrderedCoarseFineComplex.sourceFullTopBadBaseDeletion]
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨f.lowerRank, d⟩, Finset.mem_univ _, ?_⟩
  rw [mem_orderedFacePullbackFinset]
  change
    orderedFaceTuple (d.trans e) x ∈
      P.sourceFullCoarseOwnAtomBadBaseSupport
        ({ lowerRank := f.lowerRank
           face := d.trans e } : PositiveOrderedFace k r)
        (α (f.lowerRank.1 + 1))
        (β (f.lowerRank.1 + 1))
  rw [hde]
  exact hbad

end ClosedOrderedAtomConfiguration

theorem sourceFullBadBaseDeletionFamily_isCover_of_sourceFullMixedGood_count
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrk : n + 1 ≤ k)
    (H : OrderedPattern G k (n + 1))
    (P : OrderedCoarseFineComplex G k (n + 1))
    (hinitial :
      P.coarse.Refines (orderedPatternInitialComplex H))
    (α β : ℕ → ℝ) (c : ℝ)
    (hcount : H.toWeighted.patternCount < c)
    (hgoodCount :
      ∀ A : ClosedOrderedAtomConfiguration
          G k (n + 1) P.coarse,
        A.IsSourceFullMixedGood P α β →
          c ≤ fullConfigurationCount A) :
    H.IsCover
      (P.sourceFullBadBaseDeletionFamily α β) := by
  intro x hx
  by_contra hsurvives
  push Not at hsurvives
  let A :
      ClosedOrderedAtomConfiguration
        G k (n + 1) P.coarse :=
    ClosedOrderedAtomConfiguration.ofTuple P.coarse x
  have hgood : A.IsSourceFullMixedGood P α β := by
    exact
      ClosedOrderedAtomConfiguration.isSourceFullMixedGood_of_avoids_sourceFullTopBadBaseDeletion
        hrk P x α β hsurvives
  have hcA : c ≤ fullConfigurationCount A :=
    hgoodCount A hgood
  have htop :
      OrderedFacePartitionRefines P.coarse.topLayer
        (orderedPatternTopPartition H) :=
    orderedPatternTopPartition_refines_of_complex_refines_initial
      H hinitial
  have hAH :
      fullConfigurationCount A ≤
        H.toWeighted.patternCount :=
    fullConfigurationCount_le_patternCount
      H htop A ((H.mem_occurrenceFinset x).1 hx)
  linarith

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemovalAssembly
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem orderedRemovalRegularityBudget_spec
    {k j : ℕ} {τ : ℝ} (hτ : 0 < τ) :
    (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
      (orderedRemovalRegularityBudget k j τ : ℝ) * τ ^ 2 := by
  have hsq : 0 < τ ^ 2 := sq_pos_of_pos hτ
  have hquot :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
          τ ^ 2 <
        (orderedRemovalRegularityBudget k j τ : ℝ) := by
    unfold orderedRemovalRegularityBudget
    calc
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
            τ ^ 2 ≤
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) /
                τ ^ 2) : ℝ) :=
        Nat.le_ceil _
      _ <
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) /
                τ ^ 2) : ℝ) + 1 := by
        linarith
      _ =
          ((Nat.ceil
              ((Fintype.card
                (OrderedFace k (j + 1)) : ℝ) /
                  τ ^ 2) + 1 : ℕ) : ℝ) := by
        norm_num
  exact (div_lt_iff₀ hsq).1 hquot

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

namespace NatGrowthFunction

theorem monotone (F : NatGrowthFunction) :
    Monotone F :=
  F.monotone'

theorem positive (F : NatGrowthFunction) (n : ℕ) :
    0 < F n := by
  exact lt_of_lt_of_le (Nat.zero_lt_succ n)
    (F.above_diagonal n)

end NatGrowthFunction

theorem growthRegularityStepTolerance_pos
    (F : NatGrowthFunction) (M : ℕ) :
    0 < growthRegularityStepTolerance F M := by
  unfold growthRegularityStepTolerance
  exact one_div_pos.mpr
    (by exact_mod_cast F.positive M)

theorem growthRegularityLength_pos
    (k j : ℕ) (γ : ℝ) :
    0 < growthRegularityLength k j γ := by
  unfold growthRegularityLength
  omega

theorem orderedFace_card_div_growthRegularityLength_lt
    {k j : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    (Fintype.card
        (OrderedFace k (j + 1)) : ℝ) /
        (growthRegularityLength k j γ : ℝ) <
      γ := by
  let A : ℝ :=
    (Fintype.card
      (OrderedFace k (j + 1)) : ℝ)
  let L : ℕ :=
    growthRegularityLength k j γ
  have hLNat : 0 < L :=
    growthRegularityLength_pos k j γ
  have hLCast : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast hLNat
  have hquot : A / γ < (L : ℝ) := by
    dsimp only [A, L]
    unfold growthRegularityLength
    calc
      (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) / γ ≤
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) / γ) : ℝ) :=
        Nat.le_ceil _
      _ <
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) / γ) : ℝ) + 1 := by
        linarith
      _ =
          ((Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) / γ) + 1 : ℕ) : ℝ) := by
        norm_num
  have hA : A < (L : ℝ) * γ :=
    (div_lt_iff₀ hγ).1 hquot
  apply (div_lt_iff₀ hLCast).2
  simpa [mul_comm] using hA

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem complexity_orderedPatternInitialComplex_le_two
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
      FacePartition.complexity
          ((orderedPatternInitialComplex H).partition j e) ≤ 2 := by
  intro j
  cases j using Fin.lastCases with
  | last =>
      intro e
      change
        FacePartition.complexity
            ((orderedPatternInitialComplex H).topLayer e) ≤ 2
      rw [orderedPatternInitialComplex_topLayer]
      exact complexity_orderedPatternTopPartition_le_two H e
  | cast i =>
      intro e
      simp [orderedPatternInitialComplex,
        indiscreteOrderedPartitionComplex,
        OrderedPartitionComplex.withTopLayer]

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.TowerDominatingGrowth
namespace OAI

section

namespace Erdos3.FixedDensity

theorem le_finiteMaximum :
    ∀ {n : ℕ} (value : Fin n → ℕ) (i : Fin n),
      value i ≤ finiteMaximum n value
  | 0, _, i => Fin.elim0 i
  | n + 1, value, i => by
      cases i using Fin.lastCases with
      | last =>
          rw [finiteMaximum]
          exact le_max_right _ _
      | cast i =>
          rw [finiteMaximum]
          exact
            (le_finiteMaximum
              (fun q => value q.castSucc) i).trans
              (le_max_left _ _)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SourceFullCoarseTargetRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

theorem sourceFullCommonTolerance_pos
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ) :
    0 < sourceFullCommonTolerance F scale := by
  unfold sourceFullCommonTolerance
  exact one_div_pos.mpr
    (by exact_mod_cast F.positive (scale 0))

namespace SourceFullCoarseTargetSchedule

theorem sourceFullStageTolerance_pos
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    0 <
      sourceFullStageTolerance
        initialBound F topScale lowerBuilder n := by
  exact growthRegularityStepTolerance_pos F
    (sourceFullStagePlan
      initialBound F topScale lowerBuilder n).ceiling

theorem bounded_nonempty
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    Nonempty
      (Bounded k r initialBound F scaleFloor) := by
  induction r generalizing scaleFloor with
  | zero =>
      exact
        ⟨boundedZero
          k initialBound F scaleFloor⟩
  | succ r ih =>
      let topScale : ℕ :=
        max scaleFloor
          (initialBound (Fin.last (r + 1)))
      let gap : ℝ :=
        1 / (F topScale : ℝ) ^ 2
      let length : ℕ :=
        growthRegularityLength k r gap
      let lowerBuilder :
          (bound : Fin (r + 1) → ℕ) →
            Bounded k r bound F (F topScale) :=
        fun bound =>
          Classical.choice
            (ih bound (F topScale))
      let tolerance : ℕ → ℝ :=
        sourceFullStageTolerance
          initialBound F topScale lowerBuilder
      let budget : ℕ → ℕ :=
        sourceFullStageBudget
          initialBound F topScale lowerBuilder
      let next :
          (i : Fin length) →
            Bounded k r
              (lowerInitialBound initialBound budget i)
              F (F topScale) :=
        fun i =>
          sourceFullStageNext
            initialBound F topScale lowerBuilder i
      have hgap_pos : 0 < gap := by
        dsimp only [gap]
        exact one_div_pos.mpr
          (sq_pos_of_pos
            (by exact_mod_cast F.positive topScale))
      let plan :
          SourceFullCoarseTargetSchedule
            k (r + 1) initialBound F scaleFloor :=
        node topScale tolerance budget length
          (fun i => (next i).plan)
          (by
            intro n
            exact
              (sourceFullStageTolerance_pos
                initialBound F topScale lowerBuilder n).le)
          (by
            intro n
            change
              (Fintype.card
                  (OrderedFace k (r + 1)) : ℝ) <
                (sourceFullStageBudget
                    initialBound F topScale lowerBuilder n : ℝ) *
                  (sourceFullStageTolerance
                    initialBound F topScale lowerBuilder n) ^ 2
            exact
              orderedRemovalRegularityBudget_spec
                (sourceFullStageTolerance_pos
                  initialBound F topScale lowerBuilder n))
          (by
            exact growthRegularityLength_pos k r gap)
          (by
            exact le_max_left _ _)
          (by
            exact le_max_right _ _)
          (by
            intro i P
            have hscale :
                (next i).plan.scale P 0 ≤
                  (sourceFullStagePlan
                    initialBound F topScale
                      lowerBuilder i.1).ceiling := by
              exact
                ((next i).scale_zero_le P).trans_eq
                  (sourceFullStageNext_ceiling
                    initialBound F topScale
                      lowerBuilder i)
            change
              growthRegularityStepTolerance F
                    (sourceFullStagePlan
                      initialBound F topScale
                        lowerBuilder i.1).ceiling ≤
                sourceFullCommonTolerance F
                  ((next i).plan.scale P)
            unfold growthRegularityStepTolerance
              sourceFullCommonTolerance
            apply one_div_le_one_div_of_le
            · exact_mod_cast
                F.positive ((next i).plan.scale P 0)
            · exact_mod_cast F.monotone hscale)
          (by
            have hgap :=
              orderedFace_card_div_growthRegularityLength_lt
                (k := k) (j := r) hgap_pos
            exact hgap.le)
      let ceiling : ℕ :=
        finiteMaximum length
          (fun i => (next i).ceiling)
      refine ⟨{
        plan := plan
        ceiling := ceiling
        scale_zero_le := ?_ }⟩
      intro P
      cases P with
      | node chosen lower =>
          dsimp only [plan, ceiling, node]
          change
            nodeScale topScale
                (fun i => (next i).plan.scale)
                (AdaptiveCoarseTargetSchedule.Landing.node
                  chosen lower) 0 ≤
              finiteMaximum length
                (fun i => (next i).ceiling)
          rw [show
            (0 : Fin (r + 2)) =
              (0 : Fin (r + 1)).castSucc by rfl]
          rw [nodeScale_node_castSucc]
          exact
            ((next chosen).scale_zero_le lower).trans
              (le_finiteMaximum
                (fun i => (next i).ceiling) chosen)

end SourceFullCoarseTargetSchedule

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SourceFullBundleRemovalParameters
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem sourceBundleDensity_pos
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    0 < sourceBundleDensity δ m := by
  unfold sourceBundleDensity
  positivity

theorem sourceBundleDensity_nonneg
    {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    0 ≤ sourceBundleDensity δ m := by
  unfold sourceBundleDensity
  positivity

theorem sourceBundleDensity_le_one
    {δ : ℝ} (hδ : δ ≤ 1) (hδ0 : 0 ≤ δ) (m : ℕ) :
    sourceBundleDensity δ m ≤ 1 := by
  unfold sourceBundleDensity
  have hden : (1 : ℝ) ≤ (m + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  exact (div_le_self hδ0 hden).trans hδ

theorem sourceBundleDensity_antitone
    {δ : ℝ} (hδ : 0 ≤ δ) :
    Antitone (sourceBundleDensity δ) := by
  intro a b hab
  unfold sourceBundleDensity
  apply div_le_div_of_nonneg_left hδ
  · positivity
  · exact_mod_cast Nat.add_le_add_right hab 1

theorem mul_sourceBundleDensity_le
    {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    (m : ℝ) * sourceBundleDensity δ m ≤ δ := by
  unfold sourceBundleDensity
  have hden : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  calc
    (m : ℝ) * (δ / (m + 1 : ℕ)) =
        δ * ((m : ℝ) / (m + 1 : ℕ)) := by ring
    _ ≤ δ * 1 := by
      apply mul_le_mul_of_nonneg_left _ hδ
      exact (div_le_one hden).2 (by norm_num)
    _ = δ := mul_one δ

theorem sourceBundleDefectScale_pos
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (N m : ℕ) :
    0 < sourceBundleDefectScale δ η N m := by
  unfold sourceBundleDefectScale
  exact mul_pos hη (pow_pos (sourceBundleDensity_pos hδ m) N)

theorem sourceBundleDefectScale_nonneg
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (N m : ℕ) :
    0 ≤ sourceBundleDefectScale δ η N m := by
  unfold sourceBundleDefectScale
  exact mul_nonneg hη
    (pow_nonneg (sourceBundleDensity_nonneg hδ m) N)

theorem sourceBundleSelectedScale_of_le
    {r d : ℕ} (scale : Fin (r + 1) → ℕ) (hd : d ≤ r) :
    sourceBundleSelectedScale scale d =
      scale ⟨d, Nat.lt_succ_iff.mpr hd⟩ := by
  simp [sourceBundleSelectedScale, Nat.min_eq_left hd]

theorem sourceBundleRankwiseDensity_pos
    {r : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    0 < sourceBundleRankwiseDensity δ scale d :=
  sourceBundleDensity_pos hδ _

theorem sourceBundleRankwiseDensity_le_one
    {r : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hδ_one : δ ≤ 1)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    sourceBundleRankwiseDensity δ scale d ≤ 1 :=
  sourceBundleDensity_le_one hδ_one hδ _

theorem sourceBundleRankwiseDefect_nonneg
    {r : ℕ} (δ κ : ℝ) (N : ℕ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    0 ≤ sourceBundleRankwiseDefect δ κ N scale d :=
  sq_nonneg _

theorem sourceBundleRankwiseDensity_zero_le
    {r : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    {scale : Fin (r + 1) → ℕ} (hscale : Antitone scale)
    (d : ℕ) :
    sourceBundleRankwiseDensity δ scale 0 ≤
      sourceBundleRankwiseDensity δ scale d := by
  apply sourceBundleDensity_antitone hδ
  exact hscale (Fin.zero_le _)

theorem le_bundleRankwiseDensityFloor_of_zero_le
    {α : ℕ → ℝ} (hα : ∀ d, α 0 ≤ α d) :
    ∀ d, α 0 ≤ bundleRankwiseDensityFloor α d := by
  intro d
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
      rw [bundleRankwiseDensityFloor_succ]
      exact le_min ih (hα (d + 1))

theorem sourceBundleRemovalGrowth_polynomial_le
    (Q N m : ℕ) :
    Q * (m + 1) ^ N ≤ sourceBundleRemovalGrowth Q N m := by
  rw [sourceBundleRemovalGrowth_apply]
  exact Nat.le_add_right _ _

theorem exists_sourceBundleRemovalGrowthCoefficient
    {δ η : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hη : 0 < η) (_hη_one : η ≤ 1) (N : ℕ) :
    ∃ Q : ℕ,
      SourceBundleRemovalGrowthConditions δ η N Q := by
  let x : ℝ := η ^ 2 * δ ^ (2 * N + 1)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  obtain ⟨Q, hQ⟩ := exists_nat_gt (1 / x)
  have hQpos : 0 < (Q : ℝ) := (div_pos one_pos hx).trans hQ
  have hQone : (1 : ℝ) ≤ Q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (by exact_mod_cast ne_of_gt hQpos))
  have hQx : 1 < (Q : ℝ) * x := by
    calc
      1 = (1 / x) * x := by field_simp
      _ < (Q : ℝ) * x := mul_lt_mul_of_pos_right hQ hx
  refine ⟨Q, ?_, ?_⟩
  · have hpow : δ ^ (2 * N + 1) ≤ δ ^ N := by
      exact pow_le_pow_of_le_one hδ.le hδ_one (by omega)
    calc
      1 ≤ (Q : ℝ) * x := hQx.le
      _ ≤ (Q : ℝ) * η ^ 2 * δ ^ N := by
        dsimp [x]
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpow (sq_nonneg η))
            hQpos.le)
  · calc
      1 ≤ (Q : ℝ) * x := hQx.le
      _ ≤ (Q : ℝ) * ((Q : ℝ) * x) := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hQone
            (mul_nonneg hQpos.le hx.le))
      _ = δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N) := by
        dsimp [x]
        ring

theorem one_div_sourceBundleRemovalGrowth_le
    {δ η : ℝ} {N Q : ℕ}
    (hδ : 0 < δ) (hη : 0 < η)
    (hQ : SourceBundleRemovalGrowthConditions δ η N Q)
    (m : ℕ) :
    1 / (sourceBundleRemovalGrowth Q N m : ℝ) ≤
      η ^ 2 * sourceBundleDensity δ m ^ N := by
  have hx : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hF : (0 : ℝ) < sourceBundleRemovalGrowth Q N m := by
    exact_mod_cast (sourceBundleRemovalGrowth Q N).positive m
  apply (div_le_iff₀ hF).2
  have hpoly :
      (Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N ≤
        (sourceBundleRemovalGrowth Q N m : ℕ) := by
    exact_mod_cast sourceBundleRemovalGrowth_polynomial_le Q N m
  calc
    1 ≤ (Q : ℝ) * η ^ 2 * δ ^ N := hQ.uniform
    _ =
        (η ^ 2 * sourceBundleDensity δ m ^ N) *
          ((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) := by
      unfold sourceBundleDensity
      rw [div_pow]
      field_simp
    _ ≤
        (η ^ 2 * sourceBundleDensity δ m ^ N) *
          (sourceBundleRemovalGrowth Q N m : ℕ) := by
      apply mul_le_mul_of_nonneg_left hpoly
      exact mul_nonneg (sq_nonneg η)
        (pow_nonneg (sourceBundleDensity_nonneg hδ.le m) N)

theorem sourceFullRankGap_div_sourceBundleDefectScale_sq_le
    {δ η : ℝ} {N Q : ℕ}
    (hδ : 0 < δ) (hη : 0 < η)
    (hQ : SourceBundleRemovalGrowthConditions δ η N Q)
    (m : ℕ) :
    (1 / (sourceBundleRemovalGrowth Q N m : ℝ) ^ 2) /
          sourceBundleDefectScale δ η N m ^ 2 ≤
      δ := by
  have hx : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hF : (0 : ℝ) < sourceBundleRemovalGrowth Q N m := by
    exact_mod_cast (sourceBundleRemovalGrowth Q N).positive m
  have ht : 0 < sourceBundleDefectScale δ η N m :=
    sourceBundleDefectScale_pos hδ hη N m
  rw [div_le_iff₀ (sq_pos_of_pos ht)]
  rw [div_le_iff₀ (sq_pos_of_pos hF)]
  have hpoly :
      (Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N ≤
        (sourceBundleRemovalGrowth Q N m : ℕ) := by
    exact_mod_cast sourceBundleRemovalGrowth_polynomial_le Q N m
  have hpolySq :
      ((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) ^ 2 ≤
        (sourceBundleRemovalGrowth Q N m : ℝ) ^ 2 := by
    exact
      (sq_le_sq₀
        (mul_nonneg (Nat.cast_nonneg Q) (pow_nonneg hx.le N))
        hF.le).2 hpoly
  calc
    1 ≤ δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N) := hQ.gap
    _ =
        δ * (((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) ^ 2 *
          sourceBundleDefectScale δ η N m ^ 2) := by
      unfold sourceBundleDefectScale sourceBundleDensity
      rw [div_pow]
      field_simp
      ring
    _ ≤
        δ * ((sourceBundleRemovalGrowth Q N m : ℝ) ^ 2 *
          sourceBundleDefectScale δ η N m ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      exact mul_le_mul_of_nonneg_right hpolySq (sq_nonneg _)
    _ =
        δ * sourceBundleDefectScale δ η N m ^ 2 *
          (sourceBundleRemovalGrowth Q N m : ℝ) ^ 2 := by
      ring

theorem sqrt_sourceBundleDefectScale_sq_four_div_pow_le
    {δ κ step : ℝ} {N p m : ℕ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hκ : 0 ≤ κ) (hκ_step : 4 * κ ≤ step)
    (hp : p ≤ N) :
    Real.sqrt
          (sourceBundleDefectScale δ κ N m ^ 2 *
            (1 + (1 : ℝ)) * (1 + (1 : ℝ))) /
        sourceBundleDensity δ m ^ p ≤
      step / 2 := by
  let a := sourceBundleDensity δ m
  let t := sourceBundleDefectScale δ κ N m
  have ha : 0 < a := sourceBundleDensity_pos hδ m
  have ha_one : a ≤ 1 :=
    sourceBundleDensity_le_one hδ_one hδ.le m
  have ht : 0 ≤ t :=
    sourceBundleDefectScale_nonneg hδ.le hκ N m
  have hpow : a ^ N ≤ a ^ p :=
    pow_le_pow_of_le_one ha.le ha_one hp
  have hsqrt :
      Real.sqrt (t ^ 2 * (1 + (1 : ℝ)) * (1 + (1 : ℝ))) =
        2 * t := by
    rw [show
      t ^ 2 * (1 + (1 : ℝ)) * (1 + (1 : ℝ)) =
        (2 * t) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (by norm_num) ht)
  rw [show sourceBundleDefectScale δ κ N m = t by rfl,
    show sourceBundleDensity δ m = a by rfl, hsqrt]
  have hnormalized : 2 * t / a ^ p ≤ 2 * κ := by
    apply (div_le_iff₀ (pow_pos ha p)).2
    calc
      2 * t = (2 * κ) * a ^ N := by
        dsimp [t, a, sourceBundleDefectScale]
        ring
      _ ≤ (2 * κ) * a ^ p :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
  exact hnormalized.trans (by linarith)

theorem div_pow_le_sq_of_le_scaled_pow
    {τ κ a μ : ℝ} {p N : ℕ}
    (ha : 0 < a) (ha_one : a ≤ 1) (haμ : a ≤ μ)
    (hτ : τ ≤ κ ^ 2 * a ^ N) (hp : p ≤ N) :
    τ / μ ^ p ≤ κ ^ 2 := by
  have hμ : 0 < μ := ha.trans_le haμ
  have hpow₁ : a ^ N ≤ a ^ p :=
    pow_le_pow_of_le_one ha.le ha_one hp
  have hpow₂ : a ^ p ≤ μ ^ p :=
    pow_le_pow_left₀ ha.le haμ p
  apply (div_le_iff₀ (pow_pos hμ p)).2
  exact hτ.trans
    (mul_le_mul_of_nonneg_left (hpow₁.trans hpow₂) (sq_nonneg κ))

theorem sourceBundleRankwiseEnvelope_and_error_lt_half
    {r edgeBound Q : ℕ} {δ κ step : ℝ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hκ : 0 < κ) (hstep : 0 ≤ step)
    (hκ_step : 4 * κ ≤ step)
    (hκ_sq : κ ^ 2 ≤ step / 2)
    (hcap :
      (r : ℝ) *
          (bundleReverseDoublingHorizon r edgeBound 0 : ℝ) * step ≤ 1)
    (hfinal :
      (r : ℝ) *
          (bundleReverseDoublingHorizon r edgeBound 0 : ℝ) * step < 1 / 2)
    (hQ : SourceBundleRemovalGrowthConditions δ κ
      (bundleReverseDoublingHorizon r edgeBound 0) Q)
    (scale : Fin (r + 1) → ℕ) (hscale : Antitone scale) :
    IsBundleCountingEnvelope
        (sourceBundleRankwiseDensity δ scale)
        (sourceBundleRankwiseDefect δ κ
          (bundleReverseDoublingHorizon r edgeBound 0) scale)
        (bundleRankwiseDensityFloor
          (sourceBundleRankwiseDensity δ scale))
        (sourceFullCommonTolerance
          (sourceBundleRemovalGrowth Q
            (bundleReverseDoublingHorizon r edgeBound 0)) scale)
        (bundleRankwiseEnvelopeError
          (sourceBundleRankwiseDensity δ scale)
          (sourceBundleRankwiseDefect δ κ
            (bundleReverseDoublingHorizon r edgeBound 0) scale)
          (bundleRankwiseDensityFloor
            (sourceBundleRankwiseDensity δ scale))
          (sourceFullCommonTolerance
            (sourceBundleRemovalGrowth Q
              (bundleReverseDoublingHorizon r edgeBound 0)) scale)) ∧
      bundleRankwiseEnvelopeError
          (sourceBundleRankwiseDensity δ scale)
          (sourceBundleRankwiseDefect δ κ
            (bundleReverseDoublingHorizon r edgeBound 0) scale)
          (bundleRankwiseDensityFloor
            (sourceBundleRankwiseDensity δ scale))
          (sourceFullCommonTolerance
            (sourceBundleRemovalGrowth Q
              (bundleReverseDoublingHorizon r edgeBound 0)) scale)
          r edgeBound < 1 / 2 := by
  let N := bundleReverseDoublingHorizon r edgeBound 0
  let α := sourceBundleRankwiseDensity δ scale
  let β := sourceBundleRankwiseDefect δ κ N scale
  let μ := bundleRankwiseDensityFloor α
  let τ := sourceFullCommonTolerance
    (sourceBundleRemovalGrowth Q N) scale
  have hα : ∀ d, 0 < α d := by
    intro d
    exact sourceBundleRankwiseDensity_pos hδ scale d
  have hα_one : ∀ d, α d ≤ 1 := by
    intro d
    exact sourceBundleRankwiseDensity_le_one hδ.le hδ_one scale d
  have hβ : ∀ d, 0 ≤ β d := by
    intro d
    exact sourceBundleRankwiseDefect_nonneg δ κ N scale d
  have hτ : 0 ≤ τ := by
    exact (sourceFullCommonTolerance_pos
      (sourceBundleRemovalGrowth Q N) scale).le
  have hαzero : ∀ d, α 0 ≤ α d := by
    intro d
    exact sourceBundleRankwiseDensity_zero_le hδ.le hscale d
  have hfinitePower :
      ∀ d, d < r → ∀ n,
        n < bundleReverseDoublingHorizon r edgeBound (d + 1) →
          n + 1 ≤ N := by
    intro d _hd n hn
    have hhorizon :=
      bundleReverseDoublingHorizon_le_zero r edgeBound (d + 1)
    dsimp only [N]
    omega
  apply
    (bundleRankwiseEnvelope_and_error_lt_half_of_reverseDoublingBudget
      hα hα_one hβ hτ hstep r edgeBound hcap hfinal)
  · intro d hd n hn
    have hp := hfinitePower d hd n hn
    simpa only [α, β, N, sourceBundleRankwiseDefect,
      sourceBundleRankwiseDensity] using
      (sqrt_sourceBundleDefectScale_sq_four_div_pow_le
        hδ hδ_one hκ.le hκ_step hp)
  · intro d hd n hn
    have hp := hfinitePower d hd n hn
    have ha0 : 0 < α 0 := hα 0
    have ha0_one : α 0 ≤ 1 := hα_one 0
    have ha0μ : α 0 ≤ μ (d + 1) :=
      le_bundleRankwiseDensityFloor_of_zero_le hαzero (d + 1)
    have hτscaled : τ ≤ κ ^ 2 * (α 0) ^ N := by
      simpa only [τ, α, N, sourceFullCommonTolerance,
        sourceBundleRankwiseDensity, sourceBundleSelectedScale_zero] using
        (one_div_sourceBundleRemovalGrowth_le hδ hκ hQ (scale 0))
    exact
      (div_pow_le_sq_of_le_scaled_pow
        ha0 ha0_one ha0μ hτscaled hp).trans hκ_sq

namespace SourceFullCoarseTargetSchedule.Certificate

theorem scale_antitone
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (C : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor) :
    Antitone C.scale := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  exact
    (Nat.le_succ _).trans
      ((F.above_diagonal (C.scale j.succ)).trans
        (C.scale_hierarchy j))

end SourceFullCoarseTargetSchedule.Certificate

namespace SourceFullCoarseTargetSchedule.Bounded

theorem certificate_nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F scaleFloor)
    (initial : OrderedPartitionComplex G k r)
    (hinitial :
      ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
        FacePartition.complexity
            (initial.partition q e) ≤
          initialBound q) :
    Nonempty (Certificate S initial) := by
  obtain ⟨P, R, hindex⟩ :=
    S.plan.schedule.exists_landing_certificate
      initial S.plan.schedule_admissible
  let C : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor :=
    { tolerance := P.tolerance
      budget := P.budget
      length := P.length
      regularity := R
      scale := S.plan.scale P
      scaleFloor_le := S.plan.scaleFloor_le P
      scale_hierarchy := S.plan.scale_hierarchy P
      selected_tolerance_nonneg := by
        intro j
        simp only [selectedOrderedComplexTolerance]
        rw [congrFun hindex j]
        exact
          P.tolerance_nonneg S.plan.schedule_admissible
            j (P.index j)
      selected_tolerance_le_common := by
        intro j
        simpa [selectedOrderedComplexTolerance, hindex] using
          S.plan.selected_tolerance_le_common P j
      rank_gap_le := by
        intro j
        have hgap := R.gap_le j
        have hreciprocal := S.plan.reciprocal_gap_le P j
        change
          orderedLayerAtomEnergy
                (R.fine.partition j.castSucc)
                (R.coarse.partition j.succ) -
              orderedLayerAtomEnergy
                (R.coarse.partition j.castSucc)
                (R.coarse.partition j.succ) ≤
            sourceFullRankGap F (S.plan.scale P) j
        exact hgap.trans hreciprocal
      coarse_complexity := by
        intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            have htop := congrFun R.coarse_topLayer_eq e
            simp only [OrderedPartitionComplex.topLayer] at htop
            rw [htop]
            calc
              FacePartition.complexity
                    (initial.partition (Fin.last r) e) ≤
                  initialBound (Fin.last r) :=
                hinitial (Fin.last r) e
              _ = adaptiveSelectedCoarseLayerBound
                    initialBound P (Fin.last r) := by
                simp [adaptiveSelectedCoarseLayerBound]
              _ ≤ S.plan.scale P (Fin.last r) :=
                S.plan.selected_coarse_bound P (Fin.last r)
        | cast j =>
            intro e
            calc
              FacePartition.complexity
                    (R.coarse.partition j.castSucc e) ≤
                  fixedUpperLayerComplexityFactor
                        j.1 (P.budget j) (P.index j) *
                    FacePartition.complexity
                        (initial.partition j.castSucc e) := by
                rw [← congrFun hindex j]
                exact R.coarse_complexity j e
              _ ≤ fixedUpperLayerComplexityFactor
                        j.1 (P.budget j) (P.index j) *
                    initialBound j.castSucc :=
                Nat.mul_le_mul_left _ (hinitial j.castSucc e)
              _ = adaptiveSelectedCoarseLayerBound
                    initialBound P j.castSucc := by
                simp [adaptiveSelectedCoarseLayerBound]
              _ ≤ S.plan.scale P j.castSucc :=
                S.plan.selected_coarse_bound P j.castSucc }
  exact ⟨⟨C, S.scale_zero_le P⟩⟩

end SourceFullCoarseTargetSchedule.Bounded

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Conclusions
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

theorem frozenBundleMissingVertex_not_mem
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K}
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀) :
    (B.frozenBundleMissingVertex hmax hne g).1 ∉ g := by
  classical
  simp only [frozenBundleMissingVertex, dif_pos hg]
  exact
    (Classical.choose_spec
      (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax)).2

omit [Fintype G] [DecidableEq G] in
theorem splitEdgeEquiv_symm_apply_of_mem
    {K : Type*} [DecidableEq K]
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G)
    {v : K} (hv : v ∈ g₀) :
    (splitEdgeEquiv g₀).symm (y, z) v = y ⟨v, hv⟩ := by
  have h :=
    congrFun (edgeTuple_splitEdgeEquiv_symm g₀ y z) ⟨v, hv⟩
  exact h

omit [Fintype G] [DecidableEq G] in
theorem splitEdgeEquiv_symm_apply_of_not_mem
    {K : Type*} [DecidableEq K]
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G)
    {v : K} (hv : v ∉ g₀) :
    (splitEdgeEquiv g₀).symm (y, z) v = z ⟨v, hv⟩ := by
  unfold splitEdgeEquiv
  convert
    Equiv.piCongrLeft_sumInr
      (fun _ : K => G) (edgeSumEquiv g₀)
      y z ⟨v, hv⟩ using 1 ;
    simp [edgeSumEquiv]

omit [Fintype G] [DecidableEq G] in

theorem edgeTuple_frozenBundleInsertedAssignment
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀)
    (a : G)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) →
        G)
    (z : EdgeComplement g₀ → G) :
    edgeTuple g
        (B.frozenBundleInsertedAssignment hg₀ hne
          (B.frozenBundleMissingCoordinate hg₀ hmax hne g)
          a
          (Fin.removeNth
            (B.frozenBundleMissingCoordinate hg₀ hmax hne g) x)
          z) =
      edgeTuple g
        ((splitEdgeEquiv g₀).symm
          ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x, z)) := by
  classical
  funext w
  unfold edgeTuple
  let i :=
    B.frozenBundleMissingCoordinate hg₀ hmax hne g
  by_cases hw₀ : w.1 ∈ g₀
  · unfold frozenBundleInsertedAssignment
    rw [splitEdgeEquiv_symm_apply_of_mem g₀ _ _ hw₀]
    rw [splitEdgeEquiv_symm_apply_of_mem g₀ _ _ hw₀]
    unfold frozenBundleInsertedSelectedTuple
    rw [B.frozenBundleFaceTupleEquiv_symm_apply]
    rw [B.frozenBundleFaceTupleEquiv_symm_apply]
    let q :=
      (B.frozenOccurrenceOrderEquiv hg₀ hne).symm
        (⟨w.1, hw₀⟩ : {v : K // v ∈ g₀})
    have hqi : q ≠ i := by
      intro h
      have hsub :
          (⟨w.1, hw₀⟩ : {v : K // v ∈ g₀}) =
            B.frozenBundleMissingVertex hmax hne g := by
        apply (B.frozenOccurrenceOrderEquiv hg₀ hne).symm.injective
        simpa only [q, i, frozenBundleMissingCoordinate] using h
      apply B.frozenBundleMissingVertex_not_mem hmax hne hg
      have hwval :
          w.1 =
            (B.frozenBundleMissingVertex hmax hne g).1 :=
        congrArg Subtype.val hsub
      rw [← hwval]
      exact w.2
    change
      Fin.insertNth i a (Fin.removeNth i x) q = x q
    rw [Fin.insertNth_removeNth]
    simp [hqi]
  · unfold frozenBundleInsertedAssignment
    rw [splitEdgeEquiv_symm_apply_of_not_mem g₀ _ _ hw₀]
    rw [splitEdgeEquiv_symm_apply_of_not_mem g₀ _ _ hw₀]

theorem frozenBundleRemainderCutTest_bounded
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (a : G)
    (z : EdgeComplement g₀ → G) :
    IsBoundedCutTest
      (B.frozenBundleRemainderCutTest A hg₀ hmax hne a z) := by
  constructor
  · intro i y
    unfold frozenBundleRemainderCutTest
    apply Finset.prod_nonneg
    intro g hg
    split_ifs
    · exact
        (B.pullbackBaseEdgeWeight_unitInterval
          (orderedConfigurationBaseWeight A)
          (orderedConfigurationBaseWeight_unitInterval A)
          (Finset.mem_of_mem_erase hg) _).1
    · positivity
  · intro i y
    unfold frozenBundleRemainderCutTest
    apply Finset.prod_le_one
    · intro g hg
      split_ifs
      · exact
          (B.pullbackBaseEdgeWeight_unitInterval
            (orderedConfigurationBaseWeight A)
            (orderedConfigurationBaseWeight_unitInterval A)
            (Finset.mem_of_mem_erase hg) _).1
      · positivity
    · intro g hg
      split_ifs
      · exact
          (B.pullbackBaseEdgeWeight_unitInterval
            (orderedConfigurationBaseWeight A)
            (orderedConfigurationBaseWeight_unitInterval A)
            (Finset.mem_of_mem_erase hg) _).2
      · exact le_rfl

theorem cutTestProduct_frozenBundleRemainderCutTest
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (a : G)
    (z : EdgeComplement g₀ → G)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) →
        G) :
    cutTestProduct
        (B.frozenBundleRemainderCutTest A hg₀ hmax hne a z) x =
      B.edgeRemainderFiber g₀
        (B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A))
        ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x) z := by
  classical
  unfold cutTestProduct frozenBundleRemainderCutTest
  rw [Finset.prod_comm]
  unfold edgeRemainderFiber edgeRemainder bundleProduct
  apply Finset.prod_congr rfl
  intro g hg
  let i :=
    B.frozenBundleMissingCoordinate hg₀ hmax hne g
  calc
    (∏ q :
        Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1),
        if hcoord :
            B.frozenBundleMissingCoordinate hg₀ hmax hne g = q
        then
          B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A) g
            (edgeTuple g
              (B.frozenBundleInsertedAssignment hg₀ hne q a
                (Fin.removeNth q x) z))
        else 1) =
        (if hcoord :
            B.frozenBundleMissingCoordinate hg₀ hmax hne g = i
        then
          B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A) g
            (edgeTuple g
            (B.frozenBundleInsertedAssignment hg₀ hne i a
                (Fin.removeNth i x) z))
        else 1) := by
      apply Fintype.prod_eq_single i
      intro q hqi
      have hnecoord :
          B.frozenBundleMissingCoordinate hg₀ hmax hne g ≠ q := by
        intro h
        exact hqi h.symm
      simp [hnecoord]
    _ =
        B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (edgeTuple g
            (B.frozenBundleInsertedAssignment hg₀ hne i a
              (Fin.removeNth i x) z)) := by
      simp [i]
    _ =
        B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x, z))) := by
      rw [B.edgeTuple_frozenBundleInsertedAssignment
        hg₀ hmax hne hg a x z]

theorem hasOrderedConfigurationBundleFrozenCutRepresentation
    [Nonempty G]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    HasOrderedConfigurationBundleFrozenCutRepresentation P A := by
  intro K _instK _decK B _hclosed g₀ hg₀ hmax hne z
  let a : G := Classical.choice inferInstance
  let u :=
    B.frozenBundleRemainderCutTest A hg₀ hmax hne a z
  refine ⟨u, ?_, ?_⟩
  · exact
      B.frozenBundleRemainderCutTest_bounded
        P A hg₀ hmax hne a z
  · unfold frozenEdgeCorrelation
    unfold FaceRegularityState.faceCutCorrelation
    apply mean_equiv
      (B.frozenBundleFaceTupleEquiv hg₀ hne)
    intro y
    rw [B.cutTestProduct_frozenBundleRemainderCutTest
      P A hg₀ hmax hne a z]
    simp only [Equiv.symm_apply_apply]
    rw [B.frozenBundleFaceTupleEquiv_apply]
    rfl

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem orderedConfigurationInitialBundle_order_le
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).order ≤ r := by
  unfold HypergraphBundle.order
  rw [orderedConfigurationInitialBundle_edges]
  apply Finset.sup_le
  intro e he
  exact (mem_orderedConfigurationBaseEdges_iff e).1 he

theorem SourceFullCoarseTargetSchedule.Certificate.isFullyMixedPreliminaryOrderedRegular_common
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (R : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor) :
    IsFullyMixedPreliminaryOrderedRegular
      R.regularity.toCoarseFine
      (fun _ => sourceFullCommonTolerance F R.scale) := by
  intro j e a b
  exact
    (R.regularity.mixedRegular j e a b).trans
      (R.selected_tolerance_le_common j)

theorem orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood_rankwise
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hgood : A.IsSourceFullMixedGood P α β) :
    ∀ e ∈ orderedConfigurationBaseEdges k r,
      α e.card ≤ orderedConfigurationBaseDensity P A e := by
  intro e he
  by_cases he0 : e = ∅
  · subst e
    simpa using hαzero
  · have hene : e.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr he0
    have her : e.card ≤ r :=
      (mem_orderedConfigurationBaseEdges_iff e).1 he
    have hdensity :=
      (hgood (positiveOrderedFaceOfEdge e hene her)).1
    have hrank :
        (positiveOrderedFaceOfEdge e hene her).rank = e.card := by
      rw [← positiveOrderedFaceEdge_card,
        positiveOrderedFaceEdge_ofEdge]
    rw [hrank] at hdensity
    simpa [sourceFullMixedCoarseDensity,
      orderedConfigurationBaseDensity, hene, her] using hdensity

theorem hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull_rankwise
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) (τ : ℝ)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ)) :
    HasTaoBundleCountingStep
      (H := orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      β τ := by
  apply HypergraphBundle.hasTaoBundleCountingStep_orderedConfiguration
      P A β τ hβ hτ
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleLocalizedDefect_of_sourceFullMixedGood
        P A α β hgood
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
        P A τ hregular
        (HypergraphBundle.hasOrderedConfigurationBundleFrozenCutRepresentation
          P A)

theorem abs_bundleCount_orderedConfiguration_sub_main_le_rankwiseEnvelope
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    {K : Type} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion) :
    |B.bundleCount
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) -
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A)| ≤
      E B.order B.edges.card *
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A) := by
  exact
    @abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
      (Fin k) G inferInstance inferInstance
      (orderedConfigurationBaseEdges k r) inferInstance
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      α β μ τ E
      (orderedConfigurationBaseWeight_unitInterval A)
      (orderedConfigurationBaseWeight_idempotent A)
      (orderedConfigurationBaseWeight_empty A)
      (orderedConfigurationBaseDensity_empty P A)
      (orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood_rankwise
        P A α β hαzero hgood)
      (hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull_rankwise
        P A α β τ hβ hτ hgood hregular)
      henvelope K inferInstance inferInstance B hclosed

theorem one_sub_rankwiseEnvelope_mul_densityProduct_le_fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E) :
    (1 - E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card) *
        (∏ e : PositiveOrderedFace k r,
          mixedConfigurationCoarseDensity P A e) ≤
      fullConfigurationCount A := by
  have hcount :=
    abs_bundleCount_orderedConfiguration_sub_main_le_rankwiseEnvelope
      P A α β μ τ E hαzero hβ hτ hgood hregular henvelope
      (orderedConfigurationInitialBundle k r)
      (orderedConfigurationInitialBundle_closed k r)
  rw [orderedConfigurationInitialBundle_bundleCount A,
    orderedConfigurationInitialBundle_bundleMainProduct P A] at hcount
  have hlower :
      - (E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card *
            (∏ e : PositiveOrderedFace k r,
              mixedConfigurationCoarseDensity P A e)) ≤
        fullConfigurationCount A -
          (∏ e : PositiveOrderedFace k r,
            mixedConfigurationCoarseDensity P A e) :=
    neg_le_of_abs_le hcount
  linarith

theorem half_rankwiseDensityProduct_le_fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hα : ∀ d, 0 < α d)
    (hαone : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    (herror :
      E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card <
        1 / 2) :
    (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) ≤
      fullConfigurationCount A := by
  have hlower :=
    one_sub_rankwiseEnvelope_mul_densityProduct_le_fullConfigurationCount
      P A α β μ τ E (hαone 0) hβ hτ hgood hregular henvelope
  have hfloorProduct_nonneg :
      0 ≤ ∏ e : PositiveOrderedFace k r, α e.rank := by
    exact Finset.prod_nonneg fun e _ => (hα e.rank).le
  have hdensityProduct :
      (∏ e : PositiveOrderedFace k r, α e.rank) ≤
        ∏ e : PositiveOrderedFace k r,
          mixedConfigurationCoarseDensity P A e := by
    apply Finset.prod_le_prod
    · intro e _he
      exact (hα e.rank).le
    · intro e _he
      simpa [sourceFullMixedCoarseDensity] using (hgood e).1
  have hone :
      (1 / 2 : ℝ) ≤
        1 - E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card := by
    linarith
  have hone_nonneg :
      0 ≤
        1 - E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card := by
    linarith
  calc
    (1 / 2 : ℝ) *
          (∏ e : PositiveOrderedFace k r, α e.rank) ≤
        (1 - E
            (orderedConfigurationInitialBundle k r).order
            (orderedConfigurationInitialBundle k r).edges.card) *
          (∏ e : PositiveOrderedFace k r, α e.rank) :=
      mul_le_mul_of_nonneg_right hone hfloorProduct_nonneg
    _ ≤
        (1 - E
            (orderedConfigurationInitialBundle k r).order
            (orderedConfigurationInitialBundle k r).edges.card) *
          (∏ e : PositiveOrderedFace k r,
            mixedConfigurationCoarseDensity P A e) := by
      exact mul_le_mul_of_nonneg_left hdensityProduct hone_nonneg
    _ ≤ fullConfigurationCount A :=
      hlower

theorem half_rankwiseDensityProduct_le_fullConfigurationCount_of_rankBound
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hα : ∀ d, 0 < α d)
    (hαone : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    (herror :
      E r (orderedConfigurationInitialBundle k r).edges.card <
        1 / 2) :
    (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) ≤
      fullConfigurationCount A := by
  apply
    half_rankwiseDensityProduct_le_fullConfigurationCount
      P A α β μ τ E hα hαone hβ hτ hgood hregular henvelope
  exact
    (henvelope.error_mono_order
      (orderedConfigurationInitialBundle_order_le k r)).trans_lt
      herror

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem sourceBundleRemovalDensityBudget_pos
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    0 < sourceBundleRemovalDensityBudget ε r := by
  unfold sourceBundleRemovalDensityBudget
  positivity

theorem sourceBundleRemovalDensityBudget_le_one
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    sourceBundleRemovalDensityBudget ε r ≤ 1 := by
  unfold sourceBundleRemovalDensityBudget
  have hmin : min ε 1 ≤ 1 := min_le_right _ _
  have hden : (1 : ℝ) ≤
      (4 * (Fintype.card (OrderedPositiveSubface r) + 1 : ℕ) : ℕ) := by
    push_cast
    have hcard :
        (0 : ℝ) ≤ Fintype.card (OrderedPositiveSubface r) := by
      positivity
    nlinarith
  exact (div_le_self (le_of_lt (lt_min hε zero_lt_one)) hden).trans hmin

theorem card_mul_two_sourceBundleRemovalDensityBudget_le
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    (Fintype.card (OrderedPositiveSubface r) : ℝ) *
        (sourceBundleRemovalDensityBudget ε r +
          sourceBundleRemovalDensityBudget ε r) ≤ ε := by
  let s := Fintype.card (OrderedPositiveSubface r)
  let x : ℝ := min ε 1
  have hx : 0 < x := lt_min hε zero_lt_one
  have hden : (0 : ℝ) < (4 * (s + 1 : ℕ) : ℕ) := by
    positivity
  have hs : (0 : ℝ) ≤ s := by positivity
  calc
    (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (sourceBundleRemovalDensityBudget ε r +
            sourceBundleRemovalDensityBudget ε r) =
        ((2 * (s : ℝ)) * x) / (4 * (s + 1 : ℕ) : ℕ) := by
      simp only [sourceBundleRemovalDensityBudget, s, x]
      ring
    _ ≤ x := by
      apply (div_le_iff₀ hden).2
      push_cast
      nlinarith
    _ ≤ ε := min_le_left _ _

theorem sourceBundleRemovalStep_pos (k r : ℕ) :
    0 < sourceBundleRemovalStep k r := by
  unfold sourceBundleRemovalStep
  positivity

theorem sourceBundleRemovalStep_le_one (k r : ℕ) :
    sourceBundleRemovalStep k r ≤ 1 := by
  unfold sourceBundleRemovalStep
  apply (div_le_one (by positivity)).2
  push_cast
  have hr : (0 : ℝ) ≤ r := by positivity
  have hH : (0 : ℝ) ≤ sourceBundleRemovalHorizon k r := by
    positivity
  nlinarith [mul_nonneg hr hH]

theorem sourceBundleRemovalKappa_pos (k r : ℕ) :
    0 < sourceBundleRemovalKappa k r := by
  unfold sourceBundleRemovalKappa
  exact div_pos (sourceBundleRemovalStep_pos k r) (by norm_num)

theorem sourceBundleRemovalKappa_le_one (k r : ℕ) :
    sourceBundleRemovalKappa k r ≤ 1 := by
  unfold sourceBundleRemovalKappa
  have hstep := sourceBundleRemovalStep_le_one k r
  nlinarith [sourceBundleRemovalStep_pos k r]

theorem four_mul_sourceBundleRemovalKappa_le_step (k r : ℕ) :
    4 * sourceBundleRemovalKappa k r ≤
      sourceBundleRemovalStep k r := by
  unfold sourceBundleRemovalKappa
  nlinarith [sourceBundleRemovalStep_pos k r]

theorem sourceBundleRemovalKappa_sq_le_half_step (k r : ℕ) :
    sourceBundleRemovalKappa k r ^ 2 ≤
      sourceBundleRemovalStep k r / 2 := by
  unfold sourceBundleRemovalKappa
  have hpos := sourceBundleRemovalStep_pos k r
  have hone := sourceBundleRemovalStep_le_one k r
  nlinarith [sq_nonneg (sourceBundleRemovalStep k r)]

theorem sourceBundleRemovalStep_total_le_quarter (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r ≤ 1 / 4 := by
  let p := r * sourceBundleRemovalHorizon k r
  have hden : (0 : ℝ) < (4 * (p + 1 : ℕ) : ℕ) := by
    positivity
  rw [show
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
          sourceBundleRemovalStep k r =
        (p : ℝ) / (4 * (p + 1 : ℕ) : ℕ) by
      simp only [sourceBundleRemovalStep, p]
      push_cast
      ring]
  apply (div_le_iff₀ hden).2
  push_cast
  have hp : (0 : ℝ) ≤ p := by positivity
  nlinarith

theorem sourceBundleRemovalStep_total_le_one (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r ≤ 1 :=
  (sourceBundleRemovalStep_total_le_quarter k r).trans (by norm_num)

theorem sourceBundleRemovalStep_total_lt_half (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r < 1 / 2 :=
  (sourceBundleRemovalStep_total_le_quarter k r).trans_lt (by norm_num)

theorem sourceBundleRemovalCountThreshold_pos
    {δ : ℝ} (hδ : 0 < δ) (k r ceiling : ℕ) :
    0 < sourceBundleRemovalCountThreshold k r ceiling δ := by
  unfold sourceBundleRemovalCountThreshold
  exact mul_pos (by norm_num)
    (pow_pos (sourceBundleDensity_pos hδ ceiling) _)

theorem hasUniformOrderedPatternRemoval_sourceFull
    (k n : ℕ) (hrank : n + 1 ≤ k) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  intro ε hε
  let r : ℕ := n + 1
  let edgeBound : ℕ :=
    (orderedConfigurationInitialBundle k r).edges.card
  let N : ℕ := sourceBundleRemovalHorizon k r
  let δ : ℝ := sourceBundleRemovalDensityBudget ε r
  let step : ℝ := sourceBundleRemovalStep k r
  let κ : ℝ := sourceBundleRemovalKappa k r
  have hδ : 0 < δ := by
    exact sourceBundleRemovalDensityBudget_pos hε r
  have hδ_one : δ ≤ 1 := by
    exact sourceBundleRemovalDensityBudget_le_one hε r
  have hstep : 0 < step := by
    exact sourceBundleRemovalStep_pos k r
  have hκ : 0 < κ := by
    exact sourceBundleRemovalKappa_pos k r
  have hκ_one : κ ≤ 1 := by
    exact sourceBundleRemovalKappa_le_one k r
  have hκ_step : 4 * κ ≤ step := by
    exact four_mul_sourceBundleRemovalKappa_le_step k r
  have hκ_sq : κ ^ 2 ≤ step / 2 := by
    exact sourceBundleRemovalKappa_sq_le_half_step k r
  obtain ⟨Q, hQ⟩ :=
    exists_sourceBundleRemovalGrowthCoefficient
      hδ hδ_one hκ hκ_one N
  let F : NatGrowthFunction := sourceBundleRemovalGrowth Q N
  let initialBound : Fin (r + 1) → ℕ := fun _ => 2
  let S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F 0 :=
    Classical.choice
      (SourceFullCoarseTargetSchedule.bounded_nonempty
        k r initialBound F 0)
  let c : ℝ :=
    sourceBundleRemovalCountThreshold k r S.ceiling δ
  have hc : 0 < c := by
    exact sourceBundleRemovalCountThreshold_pos hδ k r S.ceiling
  refine ⟨c, hc, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty H hcount
  let initial : OrderedPartitionComplex G k r :=
    orderedPatternInitialComplex H
  obtain ⟨Cbounded⟩ :=
    S.certificate_nonempty initial (by
      intro q e
      exact complexity_orderedPatternInitialComplex_le_two H q e)
  let C := Cbounded.toSourceFull
  let P : OrderedCoarseFineComplex G k r :=
    C.regularity.toCoarseFine
  let α : ℕ → ℝ := sourceBundleRankwiseDensity δ C.scale
  let β : ℕ → ℝ := sourceBundleRankwiseDefect δ κ N C.scale
  let μ : ℕ → ℝ := bundleRankwiseDensityFloor α
  let τ : ℝ := sourceFullCommonTolerance F C.scale
  let E : ℕ → ℕ → ℝ :=
    bundleRankwiseEnvelopeError α β μ τ
  let D : OrderedPattern.DeletionFamily (G := G) k r :=
    P.sourceFullBadBaseDeletionFamily α β
  have hα : ∀ d, 0 < α d := by
    intro d
    exact sourceBundleRankwiseDensity_pos hδ C.scale d
  have hα_one : ∀ d, α d ≤ 1 := by
    intro d
    exact sourceBundleRankwiseDensity_le_one hδ.le hδ_one C.scale d
  have hβ : ∀ d, 0 ≤ β d := by
    intro d
    exact sourceBundleRankwiseDefect_nonneg δ κ N C.scale d
  have hβ_pos : ∀ d, 0 < β d := by
    intro d
    unfold β sourceBundleRankwiseDefect
    exact sq_pos_of_pos
      (sourceBundleDefectScale_pos hδ hκ N _)
  have hτ : 0 ≤ τ := by
    exact (sourceFullCommonTolerance_pos F C.scale).le
  have hscale : Antitone C.scale := C.scale_antitone
  have henvelopeRaw :=
    sourceBundleRankwiseEnvelope_and_error_lt_half
      (r := r) (edgeBound := edgeBound) (Q := Q)
      hδ hδ_one hκ hstep.le hκ_step hκ_sq
      (by
        simpa [step, N, edgeBound, sourceBundleRemovalHorizon] using
          sourceBundleRemovalStep_total_le_one k r)
      (by
        simpa [step, N, edgeBound, sourceBundleRemovalHorizon] using
          sourceBundleRemovalStep_total_lt_half k r)
      (by simpa [N, edgeBound, sourceBundleRemovalHorizon] using hQ)
      C.scale hscale
  have henvelope : IsBundleCountingEnvelope α β μ τ E := by
    simpa [α, β, μ, τ, E, F, N, edgeBound,
      sourceBundleRemovalHorizon] using henvelopeRaw.1
  have herror : E r edgeBound < 1 / 2 := by
    simpa [α, β, μ, τ, E, F, N, edgeBound,
      sourceBundleRemovalHorizon] using henvelopeRaw.2
  have hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ) := by
    simpa [P, τ] using
      C.isFullyMixedPreliminaryOrderedRegular_common
  have hthreshold :
      c ≤ (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) := by
    have hfloor : 0 ≤ sourceBundleDensity δ S.ceiling :=
      (sourceBundleDensity_pos hδ S.ceiling).le
    have hpoint : ∀ e : PositiveOrderedFace k r,
        sourceBundleDensity δ S.ceiling ≤ α e.rank := by
      intro e
      unfold α sourceBundleRankwiseDensity
      apply sourceBundleDensity_antitone hδ.le
      exact
        (hscale (Fin.zero_le _)).trans
          Cbounded.scale_zero_le_ceiling
    have hprod :
        sourceBundleDensity δ S.ceiling ^
            Fintype.card (PositiveOrderedFace k r) ≤
          ∏ e : PositiveOrderedFace k r, α e.rank := by
      calc
        sourceBundleDensity δ S.ceiling ^
              Fintype.card (PositiveOrderedFace k r) =
            ∏ _e : PositiveOrderedFace k r,
              sourceBundleDensity δ S.ceiling := by simp
        _ ≤ ∏ e : PositiveOrderedFace k r, α e.rank := by
          apply Finset.prod_le_prod
          · intro e _he
            exact hfloor
          · intro e _he
            exact hpoint e
    simpa [c, sourceBundleRemovalCountThreshold] using
      (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hgoodCount :
      ∀ A : ClosedOrderedAtomConfiguration G k r P.coarse,
        A.IsSourceFullMixedGood P α β →
          c ≤ fullConfigurationCount A := by
    intro A hgood
    exact hthreshold.trans
      (half_rankwiseDensityProduct_le_fullConfigurationCount_of_rankBound
        P A α β μ τ E hα hα_one hβ hτ hgood hregular
        henvelope (by simpa [edgeBound] using herror))
  have hinitial :
      P.coarse.Refines (orderedPatternInitialComplex H) := by
    simpa [P, initial,
      CoarseTargetOrderedComplexRegularityCertificate.toCoarseFine] using
        C.regularity.coarse_refines_initial
  have hcover : H.IsCover D := by
    exact
      sourceFullBadBaseDeletionFamily_isCover_of_sourceFullMixedGood_count
        (by simpa [r] using hrank) H P hinitial α β c hcount hgoodCount
  refine ⟨D, hcover, ?_⟩
  intro e
  have hbase :=
    P.faceDeletionDensity_sourceFullBadBaseDeletionFamily_le
      α β (fun j => (hα (j + 1)).le) (fun j => hβ_pos (j + 1)) e
  calc
    OrderedPattern.faceDeletionDensity D e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1)) := by
      simpa [D] using hbase
    _ ≤ ∑ _q : OrderedPositiveSubface r, (δ + δ) := by
      apply Finset.sum_le_sum
      intro q _hq
      have hd : q.1.1 + 1 ≤ r := by omega
      have hselected :
          sourceBundleSelectedScale C.scale (q.1.1 + 1) =
            C.scale q.1.succ := by
        calc
          sourceBundleSelectedScale C.scale (q.1.1 + 1) =
              C.scale
                ⟨q.1.1 + 1, Nat.lt_succ_iff.mpr hd⟩ :=
            sourceBundleSelectedScale_of_le C.scale hd
          _ = C.scale q.1.succ := by
            apply congrArg C.scale
            exact Fin.ext rfl
      have hcomplexity :
          FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) ≤
            C.scale q.1.succ := by
        simpa [P,
          CoarseTargetOrderedComplexRegularityCertificate.toCoarseFine] using
          C.coarse_complexity q.1.succ (q.2.trans e)
      have hlow :
          (FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                α (q.1.1 + 1) ≤ δ := by
        calc
          (FacePartition.complexity
                (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                  α (q.1.1 + 1) ≤
              (C.scale q.1.succ : ℝ) * α (q.1.1 + 1) :=
            mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr hcomplexity) (hα _).le
          _ = (C.scale q.1.succ : ℝ) *
                sourceBundleDensity δ (C.scale q.1.succ) := by
            simp [α, sourceBundleRankwiseDensity, hselected]
          _ ≤ δ := mul_sourceBundleDensity_le hδ.le _
      have hfaceLayer :
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) ≤
            P.coarseUpperLayerAtomEnergyGap q.1 := by
        rw [P.coarseUpperLayerAtomEnergyGap_eq_sum_face q.1]
        exact Finset.single_le_sum
          (fun f _ => P.coarseUpperFaceAtomEnergyGap_nonneg q.1 f)
          (Finset.mem_univ (q.2.trans e))
      have hlayer :
          P.coarseUpperLayerAtomEnergyGap q.1 ≤
            sourceFullRankGap F C.scale q.1 := by
        simpa [P] using C.rank_gap_le q.1
      have hdefect :
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1) ≤ δ := by
        calc
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1) ≤
              sourceFullRankGap F C.scale q.1 /
                β (q.1.1 + 1) :=
            div_le_div_of_nonneg_right
              (hfaceLayer.trans hlayer) (hβ _)
          _ =
              (1 /
                  (sourceBundleRemovalGrowth Q N
                    (C.scale q.1.succ) : ℝ) ^ 2) /
                sourceBundleDefectScale δ κ N
                    (C.scale q.1.succ) ^ 2 := by
            simp [F, sourceFullRankGap, β,
              sourceBundleRankwiseDefect, hselected]
          _ ≤ δ :=
            sourceFullRankGap_div_sourceBundleDefectScale_sq_le
              hδ hκ hQ (C.scale q.1.succ)
      exact add_le_add hlow hdefect
    _ = (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (δ + δ) := by
      simp [mul_add]
    _ ≤ ε := by
      simpa [δ, r] using
        card_mul_two_sourceBundleRemovalDensityBudget_le hε (n + 1)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

theorem szemeredi (k : ℕ) (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ HasUniformDenseAPCount k δ c := by
  refine
    exists_uniformDenseAPCount_of_orderedRemoval_of_two_le
      k hk ?_ hδ
  have hrank : k - 1 = (k - 2) + 1 := by omega
  rw [hrank]
  exact hasUniformOrderedPatternRemoval_sourceFull
    k (k - 2) (by omega)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.CountExtraction
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem cyclicAPDiagonalMass_eq_sum_pow
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPDiagonalMass k N f = ∑ a : ZMod N, f a ^ k := by
  simp [cyclicAPDiagonalMass]

theorem pow_le_pow_pred_mul
    {x B : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B)
    {k : ℕ} (hk : 1 ≤ k) :
    x ^ k ≤ B ^ (k - 1) * x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hB0 : 0 ≤ B := hx0.trans hxB
  have hpow : x ^ m ≤ B ^ m :=
    pow_le_pow_left₀ hx0 hxB m
  simpa [Nat.add_comm, pow_succ', Nat.add_sub_cancel, mul_comm] using
    (mul_le_mul_of_nonneg_right hpow hx0)

theorem cyclicAPDiagonalMass_le
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ} {B : ℝ}
    (hk : 1 ≤ k)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∀ x, f x ≤ B) :
    cyclicAPDiagonalMass k N f ≤
      B ^ (k - 1) * (N : ℝ) * mean f := by
  rw [cyclicAPDiagonalMass_eq_sum_pow]
  calc
    ∑ a : ZMod N, f a ^ k ≤
        ∑ a : ZMod N, B ^ (k - 1) * f a := by
      exact Finset.sum_le_sum fun a _ =>
        pow_le_pow_pred_mul (hf0 a) (hfB a) hk
    _ = B ^ (k - 1) * ∑ a : ZMod N, f a := by
      rw [Finset.mul_sum]
    _ = B ^ (k - 1) * ((N : ℝ) * mean f) := by
      rw [← Fintype.card_mul_expect]
      simp [mean, ZMod.card]
    _ = B ^ (k - 1) * (N : ℝ) * mean f := by ring

theorem cyclicAPMass_eq_diagonal_add_offDiagMass
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPMass k N f =
      cyclicAPDiagonalMass k N f + cyclicAPOffDiagMass k N f := by
  classical
  rw [cyclicAPMass, cyclicAPDiagonalMass, cyclicAPOffDiagMass,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hdiagonal :
      ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d = 0),
        cyclicAPProduct k N f a d =
          cyclicAPProduct k N f a 0 := by
    apply Finset.sum_eq_single 0
    · intro d hd hd0
      exact (hd0 (Finset.mem_filter.mp hd).2).elim
    · simp
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun d : ZMod N => d = 0)
    (f := fun d => cyclicAPProduct k N f a d)]
  rw [hdiagonal]

theorem cyclicAPOffDiagMass_pos_of_diagonal_lt_mass
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ)
    (h :
      cyclicAPDiagonalMass k N f <
        cyclicAPMass k N f) :
    0 < cyclicAPOffDiagMass k N f := by
  rw [cyclicAPMass_eq_diagonal_add_offDiagMass] at h
  linarith

theorem cyclicAPCount_eq_mass_div_div
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPCount k N f =
      cyclicAPMass k N f / (N : ℝ) / (N : ℝ) := by
  simp [cyclicAPCount, cyclicAPMass, mean₂, mean,
    Fintype.expect_eq_sum_div_card, ZMod.card, Finset.sum_div]

theorem cyclicAPMass_eq_mul_mul_count
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPMass k N f =
      (N : ℝ) * (N : ℝ) * cyclicAPCount k N f := by
  rw [cyclicAPCount_eq_mass_div_div]
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  field_simp

theorem cyclicAPOffDiagMass_pos_of_count
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ} {B : ℝ}
    (hk : 1 ≤ k)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∀ x, f x ≤ B)
    (hcount :
      B ^ (k - 1) * mean f <
        (N : ℝ) * cyclicAPCount k N f) :
    0 < cyclicAPOffDiagMass k N f := by
  apply cyclicAPOffDiagMass_pos_of_diagonal_lt_mass
  have hN : 0 < (N : ℝ) := by
    exact_mod_cast NeZero.pos N
  calc
    cyclicAPDiagonalMass k N f ≤
        B ^ (k - 1) * (N : ℝ) * mean f :=
      cyclicAPDiagonalMass_le hk hf0 hfB
    _ = (N : ℝ) * (B ^ (k - 1) * mean f) := by ring
    _ < (N : ℝ) *
        ((N : ℝ) * cyclicAPCount k N f) :=
      mul_lt_mul_of_pos_left hcount hN
    _ = cyclicAPMass k N f := by
      rw [cyclicAPMass_eq_mul_mul_count]
      ring

theorem cyclicAPProduct_pos_iff_of_nonneg
    {k N : ℕ} {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a d : ZMod N) :
    0 < cyclicAPProduct k N f a d ↔
      ∀ j : Fin k, 0 < f (cyclicAPTerm a d j) := by
  constructor
  · intro hprod j
    have hprod_ne :
        (∏ i : Fin k, f (cyclicAPTerm a d i)) ≠ 0 := by
      simpa only [cyclicAPProduct] using ne_of_gt hprod
    have hfactor_ne : f (cyclicAPTerm a d j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hprod_ne j (Finset.mem_univ j)
    exact lt_of_le_of_ne (hf _) (Ne.symm hfactor_ne)
  · intro hfactor
    rw [cyclicAPProduct]
    exact Finset.prod_pos fun j _ => hfactor j

theorem exists_cyclicAP_of_offDiagMass_pos
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x)
    (hmass : 0 < cyclicAPOffDiagMass k N f) :
    ∃ a d : ZMod N, d ≠ 0 ∧
      ∀ j : Fin k, 0 < f (cyclicAPTerm a d j) := by
  classical
  rw [cyclicAPOffDiagMass] at hmass
  have houter_nonneg :
      ∀ a ∈ (Finset.univ : Finset (ZMod N)),
        0 ≤
          ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
            cyclicAPProduct k N f a d := by
    intro a _
    exact Finset.sum_nonneg fun d _ => cyclicAPProduct_nonneg hf a d
  obtain ⟨a, _, ha⟩ :=
    (Finset.sum_pos_iff_of_nonneg houter_nonneg).mp hmass
  have hinner_nonneg :
      ∀ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
        0 ≤ cyclicAPProduct k N f a d := by
    intro d _
    exact cyclicAPProduct_nonneg hf a d
  obtain ⟨d, hdmem, hdpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg hinner_nonneg).mp ha
  refine ⟨a, d, (Finset.mem_filter.mp hdmem).2, ?_⟩
  exact (cyclicAPProduct_pos_iff_of_nonneg hf a d).mp hdpos

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.ShortInterval
namespace OAI

section

namespace Erdos3.FixedDensity

theorem abs_secondDifference_le {L U z₀ z₁ z₂ : ℤ}
    (hz₀ : L ≤ z₀ ∧ z₀ ≤ U)
    (hz₁ : L ≤ z₁ ∧ z₁ ≤ U)
    (hz₂ : L ≤ z₂ ∧ z₂ ≤ U) :
    |z₂ - 2 * z₁ + z₀| ≤ 2 * (U - L) := by
  rw [abs_le]
  constructor <;> linarith

theorem cyclicAPVal_secondDifference_eq_zero {k N : ℕ} [NeZero N]
    (a d : ZMod N) (L U : ℤ)
    (hmem :
      ∀ i : ℕ, i < k →
        L ≤ cyclicAPVal a d i ∧ cyclicAPVal a d i ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ))
    (j : ℕ) (hj : j + 2 < k) :
    (cyclicAPVal a d (j + 2) : ℤ) -
        2 * cyclicAPVal a d (j + 1) +
        cyclicAPVal a d j = 0 := by
  let z : ℤ :=
    (cyclicAPVal a d (j + 2) : ℤ) -
      2 * cyclicAPVal a d (j + 1) +
      cyclicAPVal a d j
  apply Int.eq_zero_of_abs_lt_dvd (m := (N : ℤ)) (x := z)
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    dsimp [z]
    push_cast
    simp only [cyclicAPVal_cast, Nat.cast_add, Nat.cast_ofNat]
    ring
  · exact lt_of_le_of_lt
      (abs_secondDifference_le
        (hmem j (by omega))
        (hmem (j + 1) (by omega))
        (hmem (j + 2) hj))
      hwidth

theorem eq_affine_of_secondDifference_zero
    (z : ℕ → ℤ) (k : ℕ)
    (hsecond :
      ∀ j : ℕ, j + 2 < k →
        z (j + 2) - 2 * z (j + 1) + z j = 0) :
    ∀ j : ℕ, j < k →
      z j = z 0 + (j : ℤ) * (z 1 - z 0) := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero =>
      intro
      ring
  | one =>
      intro
      ring
  | more j ihj ihj₁ =>
      intro hj
      have hj₀ : j < k := by omega
      have hj₁ : j + 1 < k := by omega
      have hs := hsecond j hj
      rw [ihj hj₀, ihj₁ hj₁] at hs
      push_cast at hs ⊢
      linarith

theorem cyclicAPVal_eq_affine {k N : ℕ} [NeZero N]
    (a d : ZMod N) (L U : ℤ)
    (hmem :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ)) :
    ∀ j : ℕ, j < k →
      (cyclicAPVal a d j : ℤ) =
        cyclicAPVal a d 0 +
          (j : ℤ) *
            ((cyclicAPVal a d 1 : ℤ) - cyclicAPVal a d 0) := by
  apply eq_affine_of_secondDifference_zero
  intro j hj
  exact cyclicAPVal_secondDifference_eq_zero a d L U hmem hwidth j hj

theorem cyclicAPVal_one_sub_zero_ne_zero {N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) :
    (cyclicAPVal a d 1 : ℤ) - cyclicAPVal a d 0 ≠ 0 := by
  intro hzero
  have hval : cyclicAPVal a d 1 = cyclicAPVal a d 0 := by
    exact_mod_cast sub_eq_zero.mp hzero
  have had : a + d = a := by
    apply ZMod.val_injective N
    simpa [cyclicAPVal] using hval
  apply hd
  apply add_left_cancel (a := a)
  simpa using had

theorem cyclicAPVal_isIntegerAP {k N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) (L U : ℤ)
    (hmem :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ)) :
    ∃ s : ℤ, s ≠ 0 ∧
      ∀ j : ℕ, j < k →
        (cyclicAPVal a d j : ℤ) =
          cyclicAPVal a d 0 + (j : ℤ) * s := by
  refine ⟨(cyclicAPVal a d 1 : ℤ) - cyclicAPVal a d 0,
    cyclicAPVal_one_sub_zero_ne_zero a d hd, ?_⟩
  exact cyclicAPVal_eq_affine a d L U hmem hwidth

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeSourceDensityParameter
namespace OAI

section

namespace Erdos3

theorem densityParameter_ge_two (α : ℝ) : 2 ≤ densityParameter α := le_max_left _ _

end Erdos3

end

section

namespace Erdos3.FixedDensity

theorem exists_naturalAP_of_cyclicAPVal_shortInterval
    {A : Set ℕ} {k N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) (hk : 2 ≤ k)
    (L U : ℤ)
    (hinterval :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ))
    (hA : ∀ j : ℕ, j < k → cyclicAPVal a d j ∈ A) :
    ∃ x step : ℕ, 1 ≤ step ∧
      ∀ j : ℕ, j < k → x + step * j ∈ A := by
  obtain ⟨s, hs, haffine⟩ :=
    cyclicAPVal_isIntegerAP a d hd L U hinterval hwidth
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · let step : ℕ := (-s).toNat
    have hstep_cast : (step : ℤ) = -s := by
      exact Int.natCast_toNat_eq_self.mpr (neg_nonneg.mpr hsneg.le)
    have hstep_pos : 0 < step := by omega
    refine ⟨cyclicAPVal a d (k - 1), step, hstep_pos, ?_⟩
    intro j hj
    have hlast : k - 1 < k := by omega
    have hrev : k - 1 - j < k := by omega
    have hindex :
        ((k - 1 - j : ℕ) : ℤ) = (k - 1 : ℕ) - (j : ℤ) := by
      omega
    have hterm :
        cyclicAPVal a d (k - 1) + step * j =
          cyclicAPVal a d (k - 1 - j) := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [hstep_cast, haffine (k - 1) hlast,
        haffine (k - 1 - j) hrev, hindex]
      ring
    rw [hterm]
    exact hA (k - 1 - j) hrev
  · let step : ℕ := s.toNat
    have hstep_cast : (step : ℤ) = s := by
      exact Int.natCast_toNat_eq_self.mpr hspos.le
    have hstep_pos : 0 < step := by omega
    refine ⟨cyclicAPVal a d 0, step, hstep_pos, ?_⟩
    intro j hj
    have hterm :
        cyclicAPVal a d 0 + step * j = cyclicAPVal a d j := by
      apply Int.ofNat_inj.mp
      push_cast
      rw [hstep_cast, haffine j hj]
      ring
    rw [hterm]
    exact hA j hj

end Erdos3.FixedDensity

namespace Erdos3

open FixedDensity

theorem cyclicIntervalSet_card {S : Finset ℕ} {N m : ℕ} [NeZero m]
    (hS : S ⊆ Finset.range N) (hNm : N ≤ m) : (cyclicIntervalSet S m).card = S.card := by
  classical
  symm
  apply Finset.card_bij (fun (x : ℕ) _ => (x : ZMod m))
  · intro x hx
    have hxm : x < m := (Finset.mem_range.mp (hS hx)).trans_le hNm
    simpa only [cyclicIntervalSet, Finset.mem_filter, Finset.mem_univ, true_and,
      ZMod.val_natCast_of_lt hxm] using hx
  · intro x hx y hy hxy
    have hxm : x < m := (Finset.mem_range.mp (hS hx)).trans_le hNm
    have hym : y < m := (Finset.mem_range.mp (hS hy)).trans_le hNm
    simpa only [ZMod.val_natCast_of_lt hxm, ZMod.val_natCast_of_lt hym] using
      congrArg (ZMod.val : ZMod m → ℕ) hxy
  · intro z hz
    have hzS : z.val ∈ S := (Finset.mem_filter.mp hz).2
    exact ⟨z.val, hzS, ZMod.natCast_zmod_val z⟩

theorem fixed_density_hasAP (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ S : Finset ℕ,
      S ⊆ Finset.range N → δ * N ≤ (S.card : ℝ) → HasAP (S : Set ℕ) k := by
  classical
  let K := max 2 k
  obtain ⟨c, hc, hcount⟩ := FixedDensity.szemeredi K (le_max_left _ _)
    (div_pos hδ (by norm_num : (0 : ℝ) < 4))
  let N₀ := ⌈1 / c⌉₊ + 1
  refine ⟨N₀, by dsimp [N₀]; omega, ?_⟩
  intro N hN S hS hdensity
  have hN0 : 0 < N := by dsimp [N₀] at hN; omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hNc : 1 / c < (N : ℝ) := by
    have hlo := Nat.le_ceil (1 / c)
    have hhi : (⌈1 / c⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith
  let m := 4 * N
  let : NeZero m := ⟨by dsimp [m]; omega⟩
  let T := cyclicIntervalSet S m
  have hNm : N ≤ m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := by dsimp [m]; positivity
  have hmean : δ / 4 ≤ mean (finsetIndicator T) := by
    rw [mean_finsetIndicator, cyclicIntervalSet_card hS hNm, ZMod.card]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hmR).mpr
    dsimp [m]
    push_cast
    nlinarith
  have hcyclic := hcount m T hmean
  have hf0 : ∀ x : ZMod m, 0 ≤ finsetIndicator T x := by
    intro x
    unfold finsetIndicator
    split <;> norm_num
  have hf1 : ∀ x : ZMod m, finsetIndicator T x ≤ 1 := by
    intro x
    unfold finsetIndicator
    split <;> norm_num
  have hmean1 : mean (finsetIndicator T) ≤ 1 := mean_le_of_le_const hf1
  have hmc : 1 < (m : ℝ) * c := by
    have hNc' := (div_lt_iff₀ hc).mp hNc
    have hNmR : (N : ℝ) ≤ m := by exact_mod_cast hNm
    exact hNc'.trans_le (mul_le_mul_of_nonneg_right hNmR hc.le)
  have hoff : 0 < cyclicAPOffDiagMass K m (finsetIndicator T) := by
    apply cyclicAPOffDiagMass_pos_of_count (by dsimp [K]; omega) hf0 hf1
    calc
      _ = mean (finsetIndicator T) := by simp
      _ ≤ 1 := hmean1
      _ < (m : ℝ) * c := hmc
      _ ≤ _ := mul_le_mul_of_nonneg_left hcyclic hmR.le
  obtain ⟨a, d, hd, hpos⟩ := exists_cyclicAP_of_offDiagMass_pos hf0 hoff
  have hterms (j : ℕ) (hj : j < K) : cyclicAPVal a d j ∈ S := by
    have hpositive := hpos (⟨j, hj⟩ : Fin K)
    have hmem : cyclicAPTerm a d (⟨j, hj⟩ : Fin K) ∈ T := by
      by_contra hn
      rw [finsetIndicator_of_not_mem hn] at hpositive
      linarith
    simpa only [T, cyclicIntervalSet, Finset.mem_filter, Finset.mem_univ, true_and,
      cyclicAPVal, cyclicAPTerm] using hmem
  have hinterval : ∀ j < K, (0 : ℤ) ≤ cyclicAPVal a d j ∧ (cyclicAPVal a d j : ℤ) ≤ N := by
    intro j hj
    have hlt := Finset.mem_range.mp (hS (hterms j hj))
    exact ⟨by positivity, by exact_mod_cast hlt.le⟩
  have hwidth : 2 * ((N : ℤ) - 0) < (m : ℤ) := by dsimp [m]; omega
  obtain ⟨a', d', hd', hAP⟩ := exists_naturalAP_of_cyclicAPVal_shortInterval
    a d hd (le_max_left _ _) 0 N hinterval hwidth hterms
  refine ⟨a', d', by omega, ?_⟩
  intro j hj
  simpa only [mul_comm] using hAP j (hj.trans_le (le_max_right 2 k))

end Erdos3

end

section

namespace Erdos3

theorem exp_neg_le_density_of_parameter_le {α T : ℝ}
    (hα : 0 < α) (hT : densityParameter α ≤ T) : Real.exp (-T) ≤ α := by
  have hlog : Real.log (2 / α) ≤ T := (le_max_right _ _).trans hT
  rw [Real.log_div (by norm_num) hα.ne'] at hlog
  apply (Real.le_log_iff_exp_le hα).mp
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

theorem fixed_density_terminal (k : ℕ) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (S : Finset ℕ), 1 < N →
      S ⊆ Finset.range N → APFree (S : Set ℕ) k → S.Nonempty →
      densityParameter (intervalDensity N S) ≤ T → C ≤ Real.log (Real.log N) → False := by
  obtain ⟨N₀, _, hN₀⟩ := fixed_density_hasAP k (Real.exp_pos (-T))
  let M := max 2 N₀
  have hM1 : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by dsimp [M]; omega)
  let C := max 0 (Real.log (Real.log M))
  refine ⟨C, le_max_left _ _, ?_⟩
  intro N S hN hS hfree hnonempty hp hsize
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hMNlog : Real.log M ≤ Real.log N :=
    (Real.log_le_log_iff (Real.log_pos hM1) (Real.log_pos hN1)).mp
      ((le_max_right _ _).trans hsize)
  have hMNreal : (M : ℝ) ≤ N :=
    (Real.log_le_log_iff (by linarith) (by linarith)).mp hMNlog
  have hMN : M ≤ N := by exact_mod_cast hMNreal
  have hN₀N : N₀ ≤ N := (le_max_right 2 N₀).trans hMN
  have hα : 0 < intervalDensity N S := intervalDensity_pos (by omega) hnonempty
  have hdensity := exp_neg_le_density_of_parameter_le hα hp
  have hcard : Real.exp (-T) * N ≤ (S.card : ℝ) :=
    (le_div_iff₀ (by linarith : (0 : ℝ) < N)).mp hdensity
  exact hfree (hN₀ N hN₀N S hS hcard)

end Erdos3

end

section

namespace Erdos3

namespace APFreeInterval

variable {k : ℕ}

theorem parameter_ge_two (S : APFreeInterval k) : 2 ≤ S.parameter := densityParameter_ge_two _

end APFreeInterval

theorem no_interval_invariant_of_descent_s2_oai (k : ℕ) (T Cmin : ℝ) :
    ∃ C₀ : ℝ, Cmin ≤ C₀ ∧ 0 ≤ C₀ ∧ ∀ A β : ℝ, 0 ≤ A →
      (∀ S : APFreeInterval k, A * S.parameter ^ β + C₀ ≤ Real.log (Real.log S.length) →
        T < S.parameter → ∃ S' : APFreeInterval k,
          A * S'.parameter ^ β + C₀ ≤ Real.log (Real.log S'.length) ∧
          S'.parameter + 1 ≤ S.parameter) →
      ∀ S : APFreeInterval k, ¬ A * S.parameter ^ β + C₀ ≤ Real.log (Real.log S.length) := by
  obtain ⟨C, hC, hterminal⟩ := fixed_density_terminal k T
  refine ⟨max Cmin C, le_max_left _ _, hC.trans (le_max_right _ _), ?_⟩
  intro A β hA hstep
  apply no_invariant_of_descent
    (P := fun S : APFreeInterval k => A * S.parameter ^ β + max Cmin C ≤ Real.log (Real.log S.length))
    APFreeInterval.parameter T
  · intro S _
    linarith [S.parameter_ge_two]
  · intro S hinvariant hsmall
    apply hterminal S.length S.points S.length_gt_one S.subset S.free S.nonempty hsmall
    have hnonneg : 0 ≤ A * S.parameter ^ β := mul_nonneg hA (Real.rpow_nonneg (by linarith [S.parameter_ge_two]) _)
    have hreserve : C ≤ max Cmin C := le_max_right _ _
    linarith
  · exact hstep

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.no_interval_invariant_of_descent_s2_oai := @OAI.Erdos3.no_interval_invariant_of_descent_s2_oai
