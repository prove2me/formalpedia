-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.PublishedInputs.whitneySurfaceInput
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:07.525736+00:00
-- url     : https://prove2.me/submissions/f1278e95-28e3-4609-88d9-ecbce589caee

import Mathlib
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Ring.Subring.Order
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.AddTorsor.Coord
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.AmpleSet
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.AffineSpace.Matrix
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.Ring
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Choose
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Germ
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_CrosscapCoordinateStrip_formal_pair
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_clean_finite_quadratic_map
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_exists_crosscap_coordinate_strip
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_exists_finite_quadratic_crosscap_map
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_prepared_smooth_crosscap_arc

section
-- module Solutions.OAIQ249_SI.Local_DualPair
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.Path.extend_div_self _root_.StepLandscape.improveStep_apply _root_.StepLandscape.improveStep_apply_φ
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-! # Dual pairs

Convex integration improves maps by successively modify their derivative in a direction of a
vector field (almost) without changing their derivative along some complementary hyperplace.

In this file we introduce the linear algebra part of the story of such modifications.
The main gadget here are dual pairs on a real topological vector space `E`.
Each `p : DualPair E` is made of a (continuous) linear form `p.π : E →L[ℝ] ℝ` and a vector
`p.v : E` such that `p.π p.v = 1`.

Those pairs are used to build the updating operation turning `φ : E →L[ℝ] F` into
`p.update φ w` which equals `φ` on `ker p.π` and sends `v` to the given `w : F`.

After formalizing the above definitions, we first record a number of trivial algebraic lemmas.
Then we prove a lemma which is geometrically obvious but not so easy to formalize:
`injective_update_iff` states, starting with an injective `φ`, that the updated
map `p.update φ w` is injective if and only if `w` isn't in the image of `ker p.π` under `φ`.
This is crucial in order to apply convex integration to immersions.

Then we prove continuity and smoothness lemmas for this operation.
-/

section


noncomputable section

open Function ContinuousLinearMap

open LinearMap (ker)

open scoped ContDiff

/-! ## General theory -/

section NoNorm

variable (E : Type*) {E' F G : Type*}

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

variable [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace DualPair

variable {E}

attribute [local simp] ContinuousLinearMap.toSpanSingleton_apply

theorem ker_pi_ne_top (p : DualPair E) : p.π.ker ≠ ⊤ := fun H ↦ by
  have : p.π.toLinearMap p.v = 1 := p.pairing
  simpa [LinearMap.ker_eq_top.mp H]

theorem mem_spanV (p : DualPair E) {u : E} : u ∈ p.spanV ↔ ∃ t : ℝ, u = t • p.v := by
  simp [DualPair.spanV, Submodule.mem_span_singleton, eq_comm]

theorem sup_eq_top (p : DualPair E) : p.π.ker ⊔ p.spanV = ⊤ := by
  rw [Submodule.sup_eq_top_iff]
  intro x
  refine ⟨x - p.π x • p.v, ?_, p.π x • p.v, ?_, ?_⟩ <;>
    simp [DualPair.spanV, Submodule.mem_span_singleton, p.pairing]

theorem decomp (p : DualPair E) (e : E) : ∃ u ∈ p.π.ker, ∃ t : ℝ, e = u + t • p.v := by
  have : e ∈ p.π.ker ⊔ p.spanV := by
    rw [p.sup_eq_top]
    exact Submodule.mem_top
  simp_rw [Submodule.mem_sup, DualPair.mem_spanV] at this
  rcases this with ⟨u, hu, -, ⟨t, rfl⟩, rfl⟩
  exact ⟨u, hu, t, rfl⟩

/-! ## Injectivity criterion -/


@[simp]
theorem injective_update_iff (p : DualPair E) {φ : E →L[ℝ] F} (hφ : Injective φ) {w : F} :
    Injective (p.update φ w) ↔ w ∉ (p.π.ker).map (φ : E →ₛₗ[.id ℝ] F) := by
  constructor
  · rintro h ⟨u, hu, rfl⟩
    have : p.update φ (φ u) p.v = φ u := p.update_v φ (φ u)
    nth_rw 2 [← p.update_ker_pi φ (φ u) hu] at this
    simp [← h this, p.pairing] at hu
  · intro hw
    refine (injective_iff_map_eq_zero (p.update φ w)).mpr fun x hx ↦ ?_
    rcases p.decomp x with ⟨u, hu, t, rfl⟩
    rw [map_add, map_smul, update_v, p.update_ker_pi _ _ hu] at hx
    obtain rfl : t = 0 := by
      by_contra ht
      apply hw
      refine ⟨-t⁻¹ • u, (p.π.ker).smul_mem _ hu, ?_⟩
      rw [map_smul]
      have : -t⁻¹ • (φ u + t • w) + w = -t⁻¹ • (0 : F) + w := congr_arg (-t⁻¹ • · + w) hx
      rwa [smul_add, neg_smul, neg_smul, inv_smul_smul₀ ht, smul_zero, zero_add,
        neg_add_cancel_right, ← neg_smul] at this
    rw [zero_smul, add_zero] at hx ⊢
    exact (injective_iff_map_eq_zero φ).mp hφ u hx

end DualPair

end NoNorm

/-! ## Smoothness and continuity -/
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_OneJet
attribute [-instance] _root_.RelLoc.instCoeOutFormalSolJetSec _root_.RelLoc.instFunLikeFamilyFormalSolJetSec _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self _root_.RelLoc.FormalSol.coe_apply _root_.RelLoc.FormalSol.toJetSec_eq_coe _root_.StepLandscape.improveStep_apply _root_.StepLandscape.improveStep_apply_f _root_.StepLandscape.improveStep_apply_φ
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-! # Spaces of 1-jets and their sections

For real normed spaces `E` and `F`, this file defines the space `OneJetSec E F` of 1-jets
of maps from `E` to `F` as `E × F × (E →L[ℝ] F)`.

A section `𝓕 : JetSet E F` of this space is a map `(𝓕.f, 𝓕.φ) : E → F × (E →L[ℝ] F)`.

It is holonomic at `x`, spelled `𝓕.IsHolonomicAt x` if the differential of `𝓕.f` at `x`
is `𝓕.φ x`.

We then introduced parametrized families of sections, and especially homotopies of sections,
with type `HtpyJetSec E F` and their concatenation operation `HtpyJetSec.comp`.


Implementation note: the time parameter `t` for homotopies is any real number, but all the
homotopies we will construct will be constant for `t ≤ 0` and `t ≥ 1`. It looks like this imposes
more smoothness constraints at `t = 0` and `t = 1` (requiring flat functions), but this is needed
for smooth concatenations anyway.
 -/

section


noncomputable section

open Set Function Real Filter

open scoped unitInterval Topology ContDiff


variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]

/-! ## Spaces of 1-jets -/


namespace JetSec

variable {E F}

theorem eq_iff {𝓕 𝓕' : JetSec E F} {x : E} : 𝓕 x = 𝓕' x ↔ 𝓕.f x = 𝓕'.f x ∧ 𝓕.φ x = 𝓕'.φ x :=
  Prod.ext_iff

/-! ## Holonomic sections-/

theorem _root_.Filter.Eventually.isPartHolonomicAt_congr {𝓕 𝓕' : JetSec E F} {s : Set E}
    (h : ∀ᶠ x near s, 𝓕 x = 𝓕' x) (E' : Submodule ℝ E) :
    ∀ᶠ x near s, 𝓕.IsPartHolonomicAt E' x ↔ 𝓕'.IsPartHolonomicAt E' x := by
  apply h.eventually_nhdsSet.mono
  intro x hx
  have hf : 𝓕.f =ᶠ[𝓝 x] 𝓕'.f := by
    apply hx.mono
    simp_rw [eq_iff]
    tauto
  unfold JetSec.IsPartHolonomicAt
  rw [hf.fderiv_eq, (eq_iff.mp hx.self_of_nhds).2]

theorem IsPartHolonomicAt.sup (𝓕 : JetSec E F) {E' E'' : Submodule ℝ E} {x : E}
    (h' : 𝓕.IsPartHolonomicAt E' x) (h'' : 𝓕.IsPartHolonomicAt E'' x) :
    𝓕.IsPartHolonomicAt (E' ⊔ E'') x := LinearMap.eqOn_sup h' h''

theorem isPartHolonomicAt_top {𝓕 : JetSec E F} {x : E} :
    IsPartHolonomicAt 𝓕 ⊤ x ↔ IsHolonomicAt 𝓕 x := by
  simp only [IsPartHolonomicAt, Submodule.mem_top, forall_true_left, IsHolonomicAt]
  simp only [← funext_iff, DFunLike.ext_iff]

end JetSec

/-! ## Homotopies of sections -/

section HtpyJetSec

variable {E F P}

/-! ## Concatenation of homotopies of sections

In this part of the file we build a concatenation operation for homotopies of 1-jet sections.
We first need to introduce a smooth step function on `ℝ`. There is already a version
of this in mathlib called `smooth_transition` but that version is not locally constant
near `0` and `1`, which is not convenient enough for gluing purposes.
-/


theorem smoothStep.mem (t : ℝ) : smoothStep t ∈ I :=
  ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩

theorem smoothStep.abs_le (t : ℝ) : |smoothStep t| ≤ 1 :=
  _root_.abs_le.mpr ⟨by linarith [(smoothStep.mem t).1], by apply smoothTransition.le_one _⟩

theorem HtpyJetSec.comp_le_0 (𝓕 𝓖 : HtpyJetSec E F) (h) :
    ∀ᶠ t near Iic 0, 𝓕.comp 𝓖 h t = 𝓕 0 := by
  have : Iio (1 / 8 : ℝ) ∈ 𝓝ˢ (Iic (0 : ℝ)) :=
    mem_nhdsSet_iff_forall.mpr fun (x : ℝ) (hx : x ≤ 0) ↦ Iio_mem_nhds <| by linarith
  apply mem_of_superset this
  rintro t (ht : t < 1 / 8)
  have ht' : t ≤ 1 / 2 := by linarith
  change 𝓕.comp 𝓖 h t = 𝓕 0
  rw [HtpyJetSec.comp_of_le _ _ h ht']
  have ht'' : 2 * t < 1 / 4 := by linarith
  rw [smoothStep.of_lt ht'']

theorem HtpyJetSec.comp_ge_1 (𝓕 𝓖 : HtpyJetSec E F) (h) : ∀ᶠ t near Ici 1, 𝓕.comp 𝓖 h t = 𝓖 1 := by
  have : Ioi (7 / 8 : ℝ) ∈ 𝓝ˢ (Ici (1 : ℝ)) :=
    mem_nhdsSet_iff_forall.mpr fun (x : ℝ) (hx : 1 ≤ x) ↦ Ioi_mem_nhds <| by linarith
  apply mem_of_superset this
  rintro t (ht : 7 / 8 < t)
  have ht' : ¬t ≤ 1 / 2 := by linarith
  change 𝓕.comp 𝓖 h t = 𝓖 1
  rw [HtpyJetSec.comp_of_not_le _ _ h ht']
  have ht'' : 3 / 4 < 2 * t - 1 := by linarith
  rw [smoothStep.of_gt ht'']

@[simp]
theorem HtpyJetSec.comp_1 (𝓕 𝓖 : HtpyJetSec E F) (h) : 𝓕.comp 𝓖 h 1 = 𝓖 1 :=
  (𝓕.comp_ge_1 𝓖 h).self_of_nhdsSet 1 self_mem_Iic

end HtpyJetSec
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_Relation
attribute [-instance] _root_.instVAddIntReal_solutions
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Local partial differential relations and their formal solutions

This file defines `RelLoc E F`, the type of first order partial differential relations
for maps between two real normed spaces `E` and `F`.

To any `R : RelLoc E F` we associate the type `sol R` of maps `f : E → F` of
solutions of `R`, and its formal counterpart `FormalSol R`.
(FIXME(grunweg): `sol` is never mentioned; is this docstring outdated?)

The h-principle question is whether we can deform any formal solution into a solution.
The type of deformations is `HtpyJetSet E F` (homotopies of 1-jet sections).
-/

section


noncomputable section

open Set Function Real Filter

open scoped unitInterval Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]

variable {E F}

namespace RelLoc

variable {R : RelLoc E F}

theorem FormalSol.eq_iff {𝓕 𝓕' : FormalSol R} {x : E} :
    𝓕 x = 𝓕' x ↔ 𝓕.f x = 𝓕'.f x ∧ 𝓕.φ x = 𝓕'.φ x :=
  JetSec.eq_iff

-- TODO: this should come from a lemma about `JetSec`
theorem FormalSol.isHolonomicAt_congr (𝓕 𝓕' : FormalSol R) {s : Set E}
    (h : ∀ᶠ x near s, 𝓕 x = 𝓕' x) : ∀ᶠ x near s, 𝓕.IsHolonomicAt x ↔ 𝓕'.IsHolonomicAt x := by
  apply h.eventually_nhdsSet.mono
  intro x hx
  have hf : 𝓕.f =ᶠ[𝓝 x] 𝓕'.f := by
    apply hx.mono
    simp_rw [RelLoc.FormalSol.eq_iff]
    tauto
  unfold RelLoc.FormalSol.IsHolonomicAt
  rw [hf.fderiv_eq, (RelLoc.FormalSol.eq_iff.mp hx.self_of_nhds).2]

open RelLoc

end RelLoc
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_AmpleRelation
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.Path.extend_div_self _root_.StepLandscape.improveStep_apply _root_.StepLandscape.improveStep_apply_f _root_.StepLandscape.improveStep_apply_φ
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-! # Slices of first order relations

Recal that a first order partial differential relation for maps between real normed vector spaces
`E` and `F` is a set `R` in `OneJet E F := E × F × (E →L[ℝ] F)`. In this file we study slices
of such relations. The word slice is meant to convey the idea of intersecting with an affine
subspace. Here we fix `(x, y, φ) : OneJet E F` and some hyperplane `H` in `E`. The points
`x` and `y` are fixed and we will take a slice in `E →L[ℝ] F` by intersecting `R` with the affine
subspace of linear maps that coincide with `φ` on `H`.

It will be convenient for convex integration purposes to identify this slice with `F`. There is
no natural identification but we can build one by fixing more data that a hyperplane in `E`.
Namely we fix `p : DualPair E` (where `ker p.π` is the relevant hyperplane) and reformulate
"linear map that coincides with `φ` on `H`" as `p.update φ w` for some `w : F`.

This `slice` definition allows to define `RelLoc.isAmple`, the ampleness condition for first
order relations: a relation is ample if all its slices are ample sets.

At the end of the file we consider 1-jet sections and slices corresponding to points in their image.
-/

section


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

variable {R : RelLoc E F}

open Set

/-! ## Slices and ampleness -/


namespace RelLoc

theorem mem_slice (R : RelLoc E F) {p : DualPair E} {θ : E × F × (E →L[ℝ] F)} {w : F} :
    w ∈ R.slice p θ ↔ (θ.1, θ.2.1, p.update θ.2.2 w) ∈ R :=
  Iff.rfl

theorem IsAmple.mem_hull (h : IsAmple R) {θ : E × F × (E →L[ℝ] F)} (hθ : θ ∈ R) (v : F) (p) :
    v ∈ hull (connectedComponentIn (R.slice p θ) (θ.2.2 p.v)) := by
  rw [h p θ (θ.2.2 p.v)]
  · exact mem_univ _
  rw [mem_slice, p.update_self]
  exact hθ

theorem slice_update {θ : E × F × (E →L[ℝ] F)} {p : DualPair E} (x : F) :
    R.slice p (θ.1, θ.2.1, p.update θ.2.2 x) = R.slice p θ := by
  ext1 w
  dsimp [slice]
  rw [p.update_update]

/-- In order to check ampleness, it suffices to consider slices through elements of the relation. -/
theorem isAmple_iff :
    R.IsAmple ↔ ∀ ⦃θ : OneJet E F⦄ (p : DualPair E), θ ∈ R → AmpleSet (R.slice p θ) := by
  refine ⟨fun h θ p _ ↦ h p θ, fun h p θ w hw ↦ ?_⟩
  dsimp [slice] at hw
  have := h p hw
  rw [slice_update] at this
  exact this w hw

open scoped Pointwise

theorem ample_slice_of_forall (R : RelLoc E F) {x y φ} (p : DualPair E)
    (h : ∀ w, (x, y, p.update φ w) ∈ R) : AmpleSet (R.slice p (x, y, φ)) := by
  rw [show R.slice p (x, y, φ) = univ from eq_univ_of_forall h]
  exact ampleSet_univ

end RelLoc

open RelLoc

/-! ## Slices for 1-jet sections and formal solutions. -/

theorem RelLoc.IsAmple.isShortAt (hR : IsAmple R) (𝓕 : FormalSol R) (p : DualPair E) (x : E) :
    𝓕.IsShortAt p x :=
  hR.mem_hull (𝓕.is_sol x) _ p
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Analysis_Calculus
attribute [-instance] _root_.hasUncurryLoop
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open Set Function Filter

open scoped Topology ContDiff

section Calculus

open ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] {E₂ : Type*}
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : WithTop ℕ∞}

variable (𝕜)

@[inherit_doc] local notation "∂₁" => partialFDerivFst

variable {𝕜}

theorem ContDiff.continuous_partial_fst {φ : E → F → G} {n : ℕ}
    (h : ContDiff 𝕜 ((n + 1 : ℕ) : ℕ∞) <| uncurry φ) : Continuous ↿(∂₁ 𝕜 φ) :=
  h.contDiff_partial_fst.continuous

end Calculus

open Filter

theorem const_mul_one_div_lt {ε : ℝ} (ε_pos : 0 < ε) (C : ℝ) : ∀ᶠ N : ℝ in atTop, C * ‖1 / N‖ < ε :=
  have h : Tendsto (fun N : ℝ ↦ C * ‖1 / N‖) atTop (𝓝 (C * ‖(0 : ℝ)‖)) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.div_atTop tendsto_id).norm
  Filter.Tendsto.eventually_lt h tendsto_const_nhds <| by simpa
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_MeasureTheory_ParametricIntervalIntegral
attribute [-instance] _root_.hasUncurryLoop _root_.instMetricSpaceOneJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

open TopologicalSpace MeasureTheory Filter FirstCountableTopology Metric Set Function
open scoped Topology

section

universe v u

variable {E : Type u}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H : Type v}
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

theorem ContDiff.fderiv_parametric_integral {F : H → ℝ → E} (hF : ContDiff ℝ 1 ↿F) (a b : ℝ) :
    (fderiv ℝ fun x : H ↦ ∫ t in a..b, F x t) = fun x : H ↦
      ∫ t in a..b, fderiv ℝ (fun x' ↦ F x' t) x := by
  ext x₀
  obtain ⟨int, h⟩ := hasFDerivAt_parametric_primitive_of_contDiff' hF contDiff_const x₀ a
  rw [h.fderiv, fderiv_fun_const]
  simp only [ContinuousLinearMap.comp_zero, add_zero, Pi.zero_apply]

end
end
end

section
-- module Solutions.OAIQ249_SI.Loops_Basic
attribute [-instance] _root_.SmoothSurroundingFamily.instCoeFunForallLoop _root_.instMembershipProdContinuousLinearMapRealIdRelLoc
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Loop.zero_vadd _root_.Path.extend_div_self _root_.SmoothSurroundingFamily.centeringDensity_average _root_.SmoothSurroundingFamily.localCenteringDensity_average _root_.SmoothSurroundingFamily.reparametrize_average _root_.StepLandscape.improveStep_apply _root_.StepLandscape.improveStep_apply_φ _root_.SurroundingFamily.path_extend_fract _root_.SurroundingFamily.path_t₀ _root_.SurroundingFamily.range_path _root_.sfHomotopy_one _root_.sfHomotopy_zero _root_.surroundingLoop_zero_left _root_.surroundingLoop_zero_right
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Basic definitions and properties of loops
-/

section

open Set Function FiniteDimensional Int TopologicalSpace

open scoped Topology unitInterval

noncomputable section

variable {K X X' Y Z : Type*}

-- variable [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-! ## Definition and periodicity lemmas -/


variable (X)

initialize_simps_projections Loop (toFun → apply)

variable {X}

namespace Loop

/-! ## Support of a loop family -/


theorem isConst_of_eq {γ : Loop X} {f : X} (H : ∀ t, γ t = f) : γ.IsConst := fun t t' ↦ by
  rw [H, H]

variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]

omit [TopologicalSpace X'] in
theorem not_mem_support {γ : X → Loop X'} {x : X} (h : ∀ᶠ y in 𝓝 x, (γ y).IsConst) :
    x ∉ Loop.support γ := by
  intro hx
  rw [support, mem_closure_iff_nhds] at hx
  rcases hx _ h with ⟨z, hz, hz'⟩
  exact hz' hz

/-! ## From paths to loops -/


/-! ## Round trips -/


attribute [fun_prop] Path.trans_continuous_family

/-! ## Average value of a loop -/
section Average

theorem isConst_iff_forall_avg [CompleteSpace F] {γ : Loop F} :
    γ.IsConst ↔ ∀ t, γ t = γ.average := by
  constructor <;> intro h
  · intro t
    have : γ = Loop.const (γ t) := by
      ext s
      exact h s t
    rw [this]
    simp [average, const_apply, intervalIntegral.integral_const, one_smul, sub_zero]
  · exact isConst_of_eq h

open MeasureTheory

theorem isConst_iff_const_avg [CompleteSpace F] {γ : Loop F} : γ.IsConst ↔ γ = const γ.average := by
  rw [Loop.isConst_iff_forall_avg, Loop.ext_iff, funext_iff]; rfl

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem isConst_of_not_mem_support {γ : X → Loop F} {x : X} (hx : x ∉ support γ) :
    (γ x).IsConst := by
  by_contra H
  exact hx (subset_closure H)

@[simp]
theorem normalize_of_isConst [CompleteSpace F] {γ : Loop F} (h : γ.IsConst) : γ.normalize = 0 := by
  ext t
  simp [isConst_iff_forall_avg.mp h]

end Average

end Loop

section C1

/-! ## Differentiation of loop families -/


variable (π : E → ℝ) (N : ℝ) (γ : E → Loop F) (hγ : IsCompact (Loop.support γ))

@[fun_prop]
theorem Loop.continuous_diff {γ : E → Loop F} (h : 𝒞 1 ↿γ) : Continuous ↿(Loop.diff γ) :=
  ContDiff.continuous_partial_fst (h : _)

theorem ContDiff.partial_loop {γ : E → Loop F} {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) :
    ∀ t, 𝒞 n fun e ↦ γ e t := by
  fun_prop

variable [FiniteDimensional ℝ F]

set_option backward.isDefEq.respectTransparency.types false in
theorem Loop.support_diff {γ : E → Loop F} : Loop.support (Loop.diff γ) ⊆ Loop.support γ := by
  unfold Loop.support
  erw [closure_compl, closure_compl]
  rw [compl_subset_compl]
  intro x hx
  rw [mem_interior_iff_mem_nhds] at *
  rcases mem_nhds_iff.mp hx with ⟨U, hU, U_op, hxU⟩
  apply Filter.mem_of_superset (U_op.mem_nhds hxU) fun y hy ↦ ?_
  have Hy : ∀ t, (fun z ↦ γ z t) =ᶠ[𝓝 y] fun z ↦ (γ z).average :=
    fun t ↦ Filter.mem_of_superset (U_op.mem_nhds hy)
      (fun z hz ↦ Loop.isConst_iff_forall_avg.mp (hU hz) t)
  have : ∀ t : ℝ, Loop.diff γ y t = D (fun z : E ↦ (γ z).average) y := fun t ↦ (Hy t).fderiv_eq
  intro t s
  simp only [this]


variable [FiniteDimensional ℝ E]

theorem Loop.average_diff {γ : E → Loop F} (hγ_diff : 𝒞 1 ↿γ) (e : E) :
    (Loop.diff γ e).average = D (fun e ↦ (γ e).average) e := by
  change 𝒞 1 ↿fun (e : E) (t : ℝ) ↦ γ e t at hγ_diff
  simp only [Loop.average, hγ_diff.fderiv_parametric_integral]
  rfl

attribute [fun_prop] contDiff_parametric_integral_of_contDiff
theorem ContDiff.loop_average {γ : E → Loop F} {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) :
    𝒞 n fun e ↦ (γ e).average := by
  unfold Loop.average; fun_prop

theorem Loop.diff_normalize {γ : E → Loop F} (hγ_diff : 𝒞 1 ↿γ) (e : E) :
    (Loop.diff γ e).normalize = Loop.diff (fun e ↦ (γ e).normalize) e := by
  ext t x
  simp only [Loop.diff_apply, Loop.normalize_apply, partialFDerivFst]
  rw [fderiv_fun_sub ((hγ_diff.partial_loop t).differentiable (by simp)).differentiableAt,
    Loop.average_diff hγ_diff]
  exact (hγ_diff.loop_average.differentiable (by simp)).differentiableAt

variable {γ}

theorem contDiff_sub_average {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) :
    𝒞 n ↿fun (x : E) (t : ℝ) ↦ (γ x) t - (γ x).average := by
  unfold Loop.average; fun_prop

end C1
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Algebra_Ring_Periodic
attribute [-instance] _root_.hasUncurryLoop _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

-- TODO: the file this references doesn't exist in mathlib any more; rename this one appropriately!

/-!

# Boundedness property of periodic function

The main purpose of that file it to prove
```
lemma Continuous.bounded_of_onePeriodic_of_isCompact {f : X → ℝ → E} (cont : Continuous ↿f)
  (hper : ∀ x, OnePeriodic (f x)) {K : Set X} (hK : IsCompact K) (hfK : ∀ x ∉ K, f x = 0) :
  ∃ C, ∀ x t, ‖f x t‖ ≤ C
```

This is done by introducing the quotient 𝕊₁ = ℝ/ℤ as a compact topological space.
Patrick is not sure this is the optimal version.

In the first part, generalize many lemmas to any period and add to `Algebra.Ring.Periodic.lean`?
-/

section


noncomputable section

open Set Function Filter TopologicalSpace Int

open scoped Topology

section OnePeriodic

variable {α : Type*}

section

attribute [local instance] transOne

theorem 𝕊₁.repr_mem (x : 𝕊₁) : x.repr ∈ (Ico 0 1 : Set ℝ) :=
  ⟨fract_nonneg _, fract_lt_one _⟩

theorem 𝕊₁.proj_repr (x : 𝕊₁) : proj𝕊₁ x.repr = x := by
  symm
  conv_lhs => rw [← Quotient.out_eq x]
  rw [← fract_add_floor (Quotient.out x)]
  apply proj𝕊₁_add_int

theorem image_proj𝕊₁_Ico : proj𝕊₁ '' Ico 0 1 = univ := by
  rw [eq_univ_iff_forall]
  exact fun x ↦ ⟨x.repr, x.repr_mem, x.proj_repr⟩

theorem image_proj𝕊₁_Icc : proj𝕊₁ '' Icc 0 1 = univ :=
  eq_univ_of_subset (image_mono Ico_subset_Icc_self) image_proj𝕊₁_Ico

theorem isOpenQuotientMap_proj𝕊₁ : IsOpenQuotientMap proj𝕊₁ := QuotientAddGroup.isOpenQuotientMap_mk

@[continuity, fun_prop]
theorem continuous_proj𝕊₁ : Continuous proj𝕊₁ := isOpenQuotientMap_proj𝕊₁.continuous

theorem isOpenMap_proj𝕊₁ : IsOpenMap proj𝕊₁ := isOpenQuotientMap_proj𝕊₁.isOpenMap

theorem quotientMap_id_proj𝕊₁ {X : Type*} [TopologicalSpace X] :
    Topology.IsQuotientMap fun p : X × ℝ ↦ (p.1, proj𝕊₁ p.2) :=
  (IsOpenMap.id.prodMap isOpenMap_proj𝕊₁).isQuotientMap (by fun_prop)
    (surjective_id.prodMap Quotient.exists_rep)

end

@[inherit_doc] local notation "π" => proj𝕊₁

instance instCompactSpace𝕊₁ : CompactSpace 𝕊₁ :=
  ⟨by rw [← image_proj𝕊₁_Icc]; exact isCompact_Icc.image continuous_proj𝕊₁⟩

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]

theorem Continuous.bounded_on_compact_of_onePeriodic {f : X → ℝ → E} (cont : Continuous ↿f)
    (hper : ∀ x, OnePeriodic (f x)) {K : Set X} (hK : IsCompact K) :
    ∃ C, ∀ x ∈ K, ∀ t, ‖f x t‖ ≤ C := by
  let F : X × 𝕊₁ → E := fun p : X × 𝕊₁ ↦ (hper p.1).lift p.2
  have Fcont : Continuous F := by
    have qm : Topology.IsQuotientMap fun p : X × ℝ ↦ (p.1, π p.2) := quotientMap_id_proj𝕊₁
    -- avoid weird elaboration issue
    have : ↿f = F ∘ fun p : X × ℝ ↦ (p.1, π p.2) := by ext p; rfl
    rwa [this, ← qm.continuous_iff] at cont
  obtain ⟨C, hC⟩ :=
    (hK.prod isCompact_univ).bddAbove_image (continuous_norm.comp Fcont).continuousOn
  exact ⟨C, fun x x_in t ↦ hC ⟨(x, π t), ⟨x_in, mem_univ _⟩, rfl⟩⟩

end OnePeriodic
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_Corrugation
attribute [-instance] _root_.SmoothSurroundingFamily.instCoeFunForallLoop _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet
attribute [-simp] _root_.Loop.zero_vadd _root_.Path.extend_div_self _root_.SmoothSurroundingFamily.centeringDensity_average _root_.SmoothSurroundingFamily.localCenteringDensity_average _root_.SmoothSurroundingFamily.reparametrize_average _root_.StepLandscape.improveStep_apply _root_.StepLandscape.improveStep_apply_f _root_.StepLandscape.improveStep_apply_φ _root_.SurroundingFamily.path_extend_fract _root_.SurroundingFamily.path_t₀ _root_.SurroundingFamily.range_path _root_.sfHomotopy_one _root_.sfHomotopy_zero _root_.surroundingLoop_zero_left _root_.surroundingLoop_zero_right
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-! # Theillière's corrugation operation

This files introduces the fundamental calculus tool of convex integration. The version of convex
integration that we formalize is Theillière's corrugation-based convex integration.
It improves a map `f : E → F` by adding to it some corrugation map
`fun x ↦ (1/N) • ∫ t in 0..(N*π x), (γ x t - (γ x).average)` where `γ` is a family of loops in
`F` parametrized by `E` and `N` is some (very large) real number.

Under the assumption that `∀ x, (γ x).average = D f x p.v` for some dual pair `p`, this improved
map will have a derivative which is almost a value of `γ x` in direction `p.v` and almost the
derivative of `f` in direction `ker p.π`. More precisely, its derivative will be almost
`p.update (D f x) (γ x (N*p.π x))`. In addition the improved map will be very close to `f`
in C⁰ topology. All those "almost" and "very close" refer to the asymptotic behavior when `N`
is very large.

The main definition is `corrugation`. The main results are:
* `fderiv_corrugated_map` computing the difference between `D (f + corrugation p.π N γ) x` and
    `p.update (D f x) (γ x (N*p.π x)) + corrugation.remainder p.π N γ x`
* `remainder_c0_small_on` saying this difference is very small
* `corrugation.c0_small_on` saying that corrugations are C⁰-small

-/

section

noncomputable section

open Set Function Filter MeasureTheory ContinuousLinearMap
open scoped Topology unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {π : E →L[ℝ] ℝ} (N : ℝ) (γ : E → Loop F)

open scoped Borelize

@[inherit_doc] local notation "𝒯" => corrugation π

/-- The integral appearing in corrugations is periodic. -/
theorem per_corrugation (γ : Loop F) (hγ : ∀ s t, IntervalIntegrable γ volume s t) :
    OnePeriodic fun s ↦ ∫ t in (0)..s, γ t - γ.average := by
  have int_avg : ∀ s t, IntervalIntegrable (fun _ : ℝ ↦ γ.average) volume s t := fun s t ↦
    intervalIntegrable_const
  intro s
  have int₁ : IntervalIntegrable (fun t ↦ γ t - γ.average) volume 0 s := (hγ _ _).sub (int_avg _ _)
  have int₂ : IntervalIntegrable (fun t ↦ γ t - γ.average) volume s (s + 1) :=
    (hγ _ _).sub (int_avg _ _)
  have int₃ : IntervalIntegrable γ volume s (s + 1) := hγ _ _
  have int₄ : IntervalIntegrable (fun _ ↦ γ.average) volume s (s + 1) := int_avg _ _
  dsimp only
  /- Rmk: Lean doesn't want to rewrite using `intervalIntegral.integral_sub` without being
      given the integrability assumptions :-( -/
  rw [← intervalIntegral.integral_add_adjacent_intervals int₁ int₂,
    intervalIntegral.integral_sub int₃ int₄, γ.periodic.intervalIntegral_add_eq s 0, zero_add,
    Loop.average]
  simp only [add_zero, add_tsub_cancel_left, intervalIntegral.integral_const, one_smul, sub_self]

@[simp]
theorem corrugation_const {x : E} (h : (γ x).IsConst) : 𝒯 N γ x = 0 := by
  unfold corrugation
  rw [Loop.isConst_iff_const_avg] at h
  rw [h]
  simp only [intervalIntegral.integral_const, Loop.const_apply, Loop.average_const,
    smul_zero, sub_self]

variable (π)

theorem corrugation.support : support (𝒯 N γ) ⊆ Loop.support γ := fun x x_in ↦ by
  apply subset_closure
  intro h
  apply x_in
  simp [h]

theorem corrugation_eq_zero (x) (H : x ∉ Loop.support γ) : corrugation π N γ x = 0 :=
  notMem_support.mp fun hx ↦ H (corrugation.support π N γ hx)

open intervalIntegral in
theorem corrugation.c0_small_on
    {γ : ℝ → E → Loop F} {K : Set E} (hK : IsCompact K) (h_le : ∀ x, ∀ t ≤ 0, γ t x = γ 0 x)
    (h_ge : ∀ x, ∀ t ≥ 1, γ t x = γ 1 x) (hγ_cont : Continuous ↿γ) {ε : ℝ} (ε_pos : 0 < ε) :
    ∀ᶠ N in atTop, ∀ x ∈ K, ∀ (t), ‖𝒯 N (γ t) x‖ < ε := by
  set φ := fun (q : ℝ × E) t ↦ ∫ t in (0)..t, (γ q.1 q.2) t - (γ q.1 q.2).average
  have cont' : Continuous ↿φ := by
    refine continuous_parametric_intervalIntegral_of_continuous ?_ continuous_snd
    refine (hγ_cont.comp₃ continuous_fst.fst.fst continuous_fst.fst.snd continuous_snd).sub ?_
    refine Loop.continuous_average ?_
    exact hγ_cont.comp₃ continuous_fst.fst.fst.fst continuous_fst.fst.fst.snd continuous_snd
  have hper : ∀ q, OnePeriodic (φ q) := fun _ ↦ per_corrugation _ fun _ _ ↦
    (hγ_cont.comp₃ continuous_const continuous_const continuous_id).intervalIntegrable _ _
  rcases cont'.bounded_on_compact_of_onePeriodic hper ((isCompact_Icc : IsCompact I).prod hK)
    with ⟨C, hC⟩
  · apply (const_mul_one_div_lt ε_pos C).mono
    intro N hN x hx t
    rw [corrugation, norm_smul, mul_comm]
    apply (mul_le_mul_of_nonneg_right _ (norm_nonneg <| 1 / N)).trans_lt hN
    obtain (ht | ht) := le_or_gt t 0
    · rw [h_le x t ht]
      apply hC (0, x)
      simp [hx]
    · obtain (ht' | ht') := le_or_gt 1 t
      · rw [h_ge x t ht']
        apply hC (1, x)
        simp [hx]
      · exact hC (t, x) (mk_mem_prod ⟨ht.le, ht'.le⟩ hx) _

variable {γ}

theorem corrugation.contDiff [FiniteDimensional ℝ E] {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) : 𝒞 n (𝒯 N γ) :=
  (contDiff_parametric_primitive_of_contDiff (contDiff_sub_average hγ_diff)
    (π.contDiff.const_smul N) 0).const_smul _

notation "∂₁" => partialFDerivFst ℝ

@[inherit_doc] local notation "R" => corrugation.remainder π

variable [FiniteDimensional ℝ E]

theorem remainder_eq (N : ℝ) {γ : E → Loop F} (h : 𝒞 1 ↿γ) :
    R N γ = fun x ↦ (1 / N) • ∫ t in (0)..N * π x, (Loop.diff γ x).normalize t := by
  simp_rw [Loop.diff_normalize h]; rfl

@[simp]
theorem remainder_eq_zero (N : ℝ) {γ : E → Loop F} (h : 𝒞 1 ↿γ) {x : E} (hx : x ∉ Loop.support γ) :
    R N γ x = 0 := by
  have hx' : x ∉ Loop.support (Loop.diff γ) := fun h ↦ hx <| Loop.support_diff h
  simp [remainder_eq π N h, Loop.normalize_of_isConst (Loop.isConst_of_not_mem_support hx')]

theorem corrugation.fderiv_eq {N : ℝ} (hN : N ≠ 0) (hγ_diff : 𝒞 1 ↿γ) :
    D (𝒯 N γ) = fun x : E ↦ ((γ x (N * π x) - (γ x).average) ⬝ π) + R N γ x := by
  ext1 x₀
  have hπ_diff : 𝒞 1 π := π.contDiff
  have diff := contDiff_sub_average hγ_diff
  have key := (hasFDerivAt_parametric_primitive_of_contDiff' diff (hπ_diff.const_smul N) x₀ 0).2
  erw [fderiv_const_smul key.differentiableAt, key.fderiv, smul_add, add_comm]
  congr 1
  rw [fderiv_fun_const_smul (hπ_diff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt N, π.fderiv]
  simp only [smul_smul, inv_mul_cancel₀ hN, one_div, smul_eq_mul, one_smul,
    ContinuousLinearMap.comp_smul]

theorem corrugation.fderiv_apply (hN : N ≠ 0) (hγ_diff : 𝒞 1 ↿γ) (x v : E) :
    D (𝒯 N γ) x v = π v • (γ x (N * π x) - (γ x).average) + R N γ x v := by
  simp only [corrugation.fderiv_eq _ hN hγ_diff, toSpanSingleton_apply, add_apply,
    ContinuousLinearMap.comp_apply]

theorem fderiv_corrugated_map (hN : N ≠ 0) (hγ_diff : 𝒞 1 ↿γ) {f : E → F} (hf : 𝒞 1 f)
    (p : DualPair E) {x} (hfγ : (γ x).average = D f x p.v) :
    D (f + corrugation p.π N γ) x =
      p.update (D f x) (γ x (N * p.π x)) + corrugation.remainder p.π N γ x := by
  ext v
  erw [fderiv_add (hf.differentiable (by simp)).differentiableAt
      ((corrugation.contDiff _ N hγ_diff).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt]
  simp_rw [add_apply, corrugation.fderiv_apply _ N hN hγ_diff, hfγ,
    DualPair.update, add_apply, p.π.comp_toSpanSingleton_apply, add_assoc]

open scoped ContDiff

set_option linter.style.multiGoal false in
theorem remainder_c0_small_on {K : Set E} (hK : IsCompact K) (hγ_diff : 𝒞 1 ↿γ) {ε : ℝ}
    (ε_pos : 0 < ε) : ∀ᶠ N in atTop, ∀ x ∈ K, ‖R N γ x‖ < ε := by
  simp_rw [fun N ↦ remainder_eq π N hγ_diff]
  let g : ℝ → E → Loop (E →L[ℝ] F) := fun _ ↦ Loop.diff γ
  have g_le : ∀ (x) (t : ℝ), t ≤ 0 → g t x = g 0 x := fun _ _ _ ↦ rfl
  have g_ge : ∀ (x) (t : ℝ), t ≥ 1 → g t x = g 1 x := fun _ _ _ ↦ rfl
  have g_cont : Continuous ↿g := (Loop.continuous_diff hγ_diff).snd'
  apply (corrugation.c0_small_on _ hK g_le g_ge g_cont ε_pos).mono
  intro N H x x_in
  exact H x x_in 0
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_HPrinciple
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Local h-principle for open and ample relations

This file proves `lem:h_principle_open_ample_loc` from the blueprint. This is the local
version of the h-principle for open and ample relations. The proof brings together the
main result `exist_loops` from the loop folder (Chapter 1 in the blueprint) and
the corrugation technique.

One formalization issue is that the whole construction carries around a lot of data.
On paper it is easy to state one lemma listing once all this data and proving many properties.
Here it is more convenient to give each property its own lemma so carrying around data,
assumptions and constructions requires some planning. Our way to mitigate this issue
is to use two ad-hoc structures `Landscape` and `StepLandscape` which partly bundle
all this.

The `Landscape` structure record three sets in a vector space, a closed
set `C` and two nested compact sets `K₀` and `K₁`. This is the ambient data for
the local h-principle result. We call this partly bundled because it doesn't include
the data of the formal solution we want to improve. Instead we have a Prop-valued
structure `Landscape.accepts` that takes a landscape and a formal solution and assert
some compatibility conditions. There are four conditions, which is already enough
motivation to introduce a structure instead of one definition using the logical
conjunction operator that would lead to awkward and error prone access to the
individual conditions.

The proof of this proposition involves an induction on a flag of subspaces (nested
subspaces of increasing dimensions). For the purpose of this induction we use
a second structure `StepLandscape` that extends `Landscape` with two more pieces
of data, a subspace and a dual pair, and a compatibility condition, namely the subspace
has to be in the hyperplane defined by the dual pair.

In this setup, given `(L : StepLandscape E) {𝓕 : FormalSol R} (h : L.accepts R 𝓕)`,
the loop family constructed by Chapter 2 is `L.loop h`. Together with corrugation,
it is used to build `L.improveStep h` which is the homotopy of 1-jet sections improving
the formal solution `𝓕` in that step of the main inductive proof. A rather long series of
lemmas prove all the required properties of that homotopy, corresponding to
lemma `lem:integration_step` from the blueprint.

The inductive proof itself is the proof of `RelLoc.FormalSol.improve`.
Here all conclusions are stated at once this the induction requires to know about each
of them to proceed to the next step. We could have introduced one more ad-hoc structure
to record those conclusion but this isn't needed (at least in that Chapter) since we
need to access its components only once.

-/

section


noncomputable section

open scoped unitInterval Filter Topology ContDiff

open Filter Set RelLoc

open LinearMap (ker)

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

section ImproveStep

/-!
## Improvement step

This section proves `lem:integration_step`.
-/


variable {E}

variable (R : RelLoc E F)

namespace StepLandscape

variable {R}

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

open scoped Borelize
variable (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕)

theorem update_zero (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) (x : E) (s : ℝ) :
    L.p.update (𝓕.φ x) ((L.loop h 0 x) s) = 𝓕.φ x := by
  rw [(L.nice h).t_zero x s]
  exact L.p.update_self _

theorem loop_C1 (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) :
    ∀ t, 𝒞 1 ↿(L.loop h t) := fun _ ↦
  (L.loop_smooth' h contDiff_const contDiff_snd contDiff_fst).of_le (mod_cast le_top)

variable (L : StepLandscape E)

theorem ρ_mem (L : StepLandscape E) (x : E) : L.ρ x ∈ I :=
  (exists_contDiff_one_nhds_of_interior L.hK₀.isClosed L.h₀₁).choose_spec.2.2.2 x

theorem ρ_le (L : StepLandscape E) (x : E) : |L.ρ x| ≤ 1 := by
  obtain ⟨h, h'⟩ := L.ρ_mem x
  rw [abs_le]
  exact ⟨by linarith, h'⟩

theorem hρ₀ (L : StepLandscape E) : ∀ᶠ x near L.K₀, L.ρ x = 1 :=
  (exists_contDiff_one_nhds_of_interior L.hK₀.isClosed L.h₀₁).choose_spec.2.1

theorem hρ_compl_K₁ (L : StepLandscape E) {x : E} : x ∉ L.K₁ → L.ρ x = 0 :=
  (exists_contDiff_one_nhds_of_interior L.hK₀.isClosed L.h₀₁).choose_spec.2.2.1 x

variable {L}
variable {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) (N : ℝ)

variable {h N} in
theorem improveStep_of_support {t : ℝ} {x : E} (H : ∀ t, x ∉ Loop.support (L.loop h t)) :
    L.improveStep h N t x = 𝓕 x := by
  have : ∀ t s, L.loop h t x s = 𝓕.φ x L.v := by
    intro t s
    rw [Loop.isConst_of_not_mem_support (H t) s 0]
    apply (L.nice h).s_zero x t
  rw [improveStep_apply (L := L) h, corrugation_eq_zero _ _ _ _ (H t),
    remainder_eq_zero _ _ (L.loop_C1 h 1) (H 1)]
  simp only [smul_zero, add_zero, this]
  erw [L.p.update_self]
  rfl

theorem improveStep_rel_t_eq_0 : L.improveStep h N 0 = 𝓕 := by
  ext x : 2
  · simp [improveStep_apply_f h]
  · rw [improveStep_apply_φ h]
    simp only [MulZeroClass.zero_mul, smoothStep.zero, zero_smul,
      add_zero]
    erw [L.update_zero h]

theorem improveStep_rel_compl_K₁ {x} (hx : x ∉ L.K₁) (t) : L.improveStep h N t x = 𝓕 x := by
  rw [improveStep_apply h, L.hρ_compl_K₁ hx]
  simp only [MulZeroClass.mul_zero, zero_smul, add_zero]
  erw [L.update_zero h]
  rfl

theorem improveStep_rel_K : ∀ᶠ x near L.K, ∀ t, L.improveStep h N t x = 𝓕 x := by
  have : ∀ᶠ x near L.K, ∀ t, x ∉ Loop.support (L.loop h t) := by
    apply (L.nice h).rel_K.eventually_nhdsSet.mono
    intro x hx t
    apply Loop.not_mem_support
    apply hx.mono
    intro y hy
    exact Loop.isConst_of_eq (hy t)
  apply this.mono
  intro x hx t
  exact improveStep_of_support hx

theorem improveStep_rel_C : ∀ᶠ x near L.C, ∀ t, L.improveStep h N t x = 𝓕 x := by
  apply Eventually.filter_mono (L.hK₁.isClosed.nhdsSet_le_sup' L.C)
  rw [eventually_sup]
  constructor
  · apply improveStep_rel_K
  · rw [eventually_principal]
    exact fun x ↦ improveStep_rel_compl_K₁ h N

-- In the next lemma, we reintroduce `F` to appease the unused argument linter
-- since `FiniteDimensional ℝ F` isn't needed here.
theorem bu_lt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (t : ℝ) (x : E) {v : F} {ε : ℝ}
    (hv : ‖v‖ < ε) : ‖(smoothStep t * L.ρ x) • v‖ < ε :=
  calc
    ‖(smoothStep t * L.ρ x) • v‖ = |smoothStep t| * |L.ρ x| * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul]
    _ ≤ ‖v‖ := by
      apply mul_le_of_le_one_left (norm_nonneg _)
      exact mul_le_one₀ (smoothStep.abs_le t) (abs_nonneg _) (L.ρ_le x)
    _ < ε := hv

theorem improveStep_c0_close {ε : ℝ} (ε_pos : 0 < ε) :
    ∀ᶠ N in atTop, ∀ x t, ‖(L.improveStep h N t).f x - 𝓕.f x‖ ≤ ε := by
  set γ := L.loop h
  have γ_cont : Continuous ↿fun t x ↦ γ t x := (L.nice h).smooth.continuous
  have γ_C1 : 𝒞 1 ↿(γ 1) := ((L.nice h).smooth.comp (contDiff_prodMk_right 1)).of_le
    (mod_cast le_top)
  apply
    ((corrugation.c0_small_on _ L.hK₁ (L.nice h).t_le_zero (L.nice h).t_ge_one γ_cont ε_pos).and <|
        remainder_c0_small_on L.π L.hK₁ γ_C1 ε_pos).mono
  · rintro N ⟨H, _⟩ x t
    by_cases hx : x ∈ L.K₁
    · rw [improveStep_apply_f h]
      suffices ‖(smoothStep t * L.ρ x) • corrugation L.π N (L.loop h t) x‖ ≤ ε by simpa
      exact (bu_lt _ _ <| H _ hx t).le
    · rw [show (L.improveStep h N t).f x = 𝓕.f x from
          congr_arg Prod.fst (improveStep_rel_compl_K₁ h N hx t)]
      simp [ε_pos.le]

theorem improveStep_part_hol {N : ℝ} (hN : N ≠ 0) :
    ∀ᶠ x near L.K₀, (L.improveStep h N 1).IsPartHolonomicAt (L.p.spanV ⊔ L.E') x := by
  have γ_C1 : 𝒞 1 ↿(L.loop h 1) := ((L.nice h).smooth.comp (contDiff_prodMk_right 1)).of_le
    (mod_cast le_top)
  let 𝓕' : JetSec E F :=
    { f := fun x ↦ 𝓕.f x + corrugation L.π N (L.loop h 1) x
      f_diff := 𝓕.f_diff.add (corrugation.contDiff' _ _ (L.loop_smooth h) contDiff_id
        contDiff_const)
      φ := fun x ↦
        L.p.update (𝓕.φ x) (L.loop h 1 x <| N * L.π x) +
          corrugation.remainder L.p.π N (L.loop h 1) x
      φ_diff := by
        apply ContDiff.add
        · apply L.p.smooth_update
          · apply 𝓕.φ_diff
          apply L.loop_smooth'
          · apply contDiff_const
          · apply contDiff_const.mul L.π.contDiff
          · exact contDiff_id
        exact Remainder.smooth _ _ (L.loop_smooth h) contDiff_id contDiff_const }
  have H : ∀ᶠ x near L.K₀, L.improveStep h N 1 x = 𝓕' x := by
    apply L.hρ₀.mono
    intro x hx
    simp [𝓕', improveStep_apply h, hx]
  have fderiv_𝓕' := fun x ↦
    fderiv_corrugated_map N hN γ_C1 (𝓕.f_diff.of_le (mod_cast le_top)) L.p ((L.nice h).avg x)
  rw [eventually_congr (H.isPartHolonomicAt_congr (L.p.spanV ⊔ L.E'))]
  apply h.hK₀.mono
  intro x hx
  apply JetSec.IsPartHolonomicAt.sup
  · intro u hu
    rcases Submodule.mem_span_singleton.mp hu with ⟨l, rfl⟩
    rw [(D 𝓕'.f x).map_smul, (𝓕'.φ x).map_smul]
    apply congr_arg
    erw [fderiv_𝓕', add_apply, L.p.update_v, add_apply, L.p.update_v]
    rfl
  · intro u hu
    have hu_ker := L.hEp hu
    erw [fderiv_𝓕', add_apply, L.p.update_ker_pi _ _ hu_ker,
      add_apply, L.p.update_ker_pi _ _ hu_ker, hx u hu]

theorem improveStep_formalSol : ∀ᶠ N in atTop, ∀ t, (L.improveStep h N t).IsFormalSol R := by
  set γ := L.loop h
  have γ_cont : Continuous ↿fun t x ↦ γ t x := (L.nice h).smooth.continuous
  have γ_C1 : 𝒞 1 ↿(γ 1) := ((L.nice h).smooth.comp (contDiff_prodMk_right 1)).of_le
    (mod_cast le_top)
  set K :=
    (fun p : E × ℝ × ℝ ↦ (p.1, 𝓕.f p.1, L.p.update (𝓕.φ p.1) (L.loop h p.2.1 p.1 p.2.2))) ''
      L.K₁ ×ˢ I ×ˢ I
  have K_cpt : IsCompact K := by
    refine (L.hK₁.prod (isCompact_Icc.prod isCompact_Icc)).image ?_
    refine continuous_fst.prodMk (𝓕.f_diff.continuous.fst'.prodMk ?_)
    apply L.p.continuous_update 𝓕.φ_diff.continuous.fst'
    change Continuous (↿(L.loop h) ∘ fun g : E × ℝ × ℝ ↦ (g.snd.fst, g.fst, g.snd.snd))
    exact (L.loop_smooth h).continuous.comp₃ continuous_snd.fst continuous_fst continuous_snd.snd
  have K_sub : K ⊆ R := by
    rintro _ ⟨⟨x, t, s⟩, _, rfl⟩
    exact (L.nice h).mem_Ω x t s
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε, 0 < ε ∧ Metric.thickening ε K ⊆ R :=
    K_cpt.exists_thickening_subset_open h.h_op K_sub
  apply
    ((corrugation.c0_small_on _ L.hK₁ (L.nice h).t_le_zero (L.nice h).t_ge_one γ_cont ε_pos).and <|
        remainder_c0_small_on L.π L.hK₁ γ_C1 ε_pos).mono
  · rintro N ⟨H, H'⟩ t x
    by_cases hxK₁ : x ∈ L.K₁
    · apply hε
      rw [Metric.mem_thickening_iff]
      refine ⟨(x, 𝓕.f x, L.p.update (𝓕.φ x) <| L.loop h (smoothStep t * L.ρ x) x <| N * L.π x),
        ?_, ?_⟩
      · exact ⟨⟨x, smoothStep t * L.ρ x, Int.fract (N * L.π x)⟩,
          ⟨hxK₁, unitInterval.mul_mem (smoothStep.mem t) (L.ρ_mem x), unitInterval.fract_mem _⟩,
          by simp only [Loop.fract_eq]⟩
      · simp only [improveStep_apply_f, improveStep_apply_φ]
        rw [Prod.dist_eq, max_lt_iff, Prod.dist_eq, max_lt_iff]
        refine ⟨by simpa using ε_pos, ?_, ?_⟩ <;> dsimp only <;> rw [dist_self_add_left]
        · exact bu_lt _ _ <| H _ hxK₁ _
        -- adaptation note(2024-03-28): `exact` used to work; started failing after mathlib bump
        · apply bu_lt _ _ <| H' _ hxK₁
    · rw [show ((L.improveStep h N) t).f x = 𝓕.f x from
          congr_arg Prod.fst <| improveStep_rel_compl_K₁ h N hxK₁ t,
        show ((L.improveStep h N) t).φ x = 𝓕.φ x from
          congr_arg Prod.snd <| improveStep_rel_compl_K₁ h N hxK₁ t]
      exact 𝓕.is_sol _

end StepLandscape

end ImproveStep

section Improve

/-!
## Full improvement

This section proves `lem:h_principle_open_ample_loc`.
-/

open Submodule StepLandscape

variable {E}
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {R : RelLoc E F} (h_op : IsOpen R)
  (h_ample : R.IsAmple)

variable (L : Landscape E)

variable {ε : ℝ} (ε_pos : 0 < ε)

include ε_pos h_op h_ample in
/--
Homotopy of formal solutions obtained by successive corrugations in some landscape `L` to improve a
formal solution `𝓕` until it becomes holonomic near `L.K₀`.
-/
theorem RelLoc.FormalSol.improve (𝓕 : FormalSol R) (h_hol : ∀ᶠ x near L.C, 𝓕.IsHolonomicAt x) :
    ∃ H : HtpyJetSec E F,
      (∀ᶠ t near Iic 0, H t = 𝓕) ∧
        (∀ᶠ t near Ici 1, H t = H 1) ∧
          (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x) ∧
            (∀ x ∉ L.K₁, ∀ t, H t x = 𝓕 x) ∧
              (∀ x t, ‖(H t).f x - 𝓕.f x‖ ≤ ε) ∧
                (∀ t, (H t).IsFormalSol R) ∧ ∀ᶠ x near L.K₀, (H 1).IsHolonomicAt x := by
  let n := Module.finrank ℝ E
  let e := Module.finBasis ℝ E
  let E' := e.flag
  suffices
    ∀ k : Fin (n + 1),
      ∀ δ > (0 : ℝ),
        ∃ H : HtpyJetSec E F,
          (∀ᶠ t near Iic 0, H t = 𝓕) ∧
            (∀ᶠ t near Ici 1, H t = H 1) ∧
              (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x) ∧
                (∀ x ∉ L.K₁, ∀ t, H t x = 𝓕 x) ∧
                  (∀ x t, ‖(H t).f x - 𝓕.f x‖ ≤ δ) ∧
                    (∀ t, (H t).IsFormalSol R) ∧ ∀ᶠ x near L.K₀, (H 1).IsPartHolonomicAt (E' k) x by
    simpa only [show E' (Fin.last n) = ⊤ from e.flag_last, JetSec.isPartHolonomicAt_top] using
      this (Fin.last n) ε ε_pos
  intro k
  induction k using Fin.induction with
  | zero =>
    intro δ δ_pos
    use 𝓕.toJetSec.constHtpy
    simp [show E' 0 = ⊥ from e.flag_zero, le_of_lt δ_pos]
  | succ k HH =>
    rintro δ δ_pos
    rcases HH (δ / 2) (half_pos δ_pos) with ⟨H, hH₀, _, hHC, hHK₁, hHc0, hH_sol, hH_hol⟩; clear HH
    let S : StepLandscape E :=
      { L with
        E' := E' k.castSucc
        p := e.dualPair k
        hEp := by simpa only [E', Module.Basis.dualPair] using! e.flag_le_ker_dual k }
    set H₁ : FormalSol R := (hH_sol 1).formalSol
    have h_span : E' k.succ = S.p.spanV ⊔ S.E' := e.flag_succ k
    have acc : S.Accepts R H₁ :=
      { h_op
        hK₀ := hH_hol.mono (fun x hx ↦ hx)
        hShort := fun x ↦ h_ample.isShortAt H₁ S.p x
        hC := by
          apply h_hol.congr (FormalSol.isHolonomicAt_congr _ _ _)
          apply hHC.mono (fun x h ↦ (h 1).symm) }
    have hH₁_rel_C : ∀ᶠ x : E near S.C, H₁ x = 𝓕 x := hHC.mono (fun x hx ↦ hx _)
    have hH₁_K₁ : ∀ x ∉ (L.K₁), H₁ x = 𝓕 x := by
      intro x hx
      apply hHK₁ x hx
    obtain ⟨N, ⟨hN_close, hN_sol⟩, hNneq⟩ :=
      (((improveStep_c0_close acc <| half_pos δ_pos).and (improveStep_formalSol acc)).and <|
          eventually_ne_atTop (0 : ℝ)).exists
    have glue : H 1 = S.improveStep acc N 0 := by
      rw [improveStep_rel_t_eq_0]
      rfl
    refine ⟨H.comp (S.improveStep acc N) glue, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply (H.comp_le_0 _ _).mono
      · intro t ht
        rw [ht]
        exact hH₀.self_of_nhdsSet 0 self_mem_Iic
    -- t = 0
    · apply (H.comp_ge_1 _ _).mono
      · intro t ht
        rw [ht, H.comp_1]
    · -- rel C
      apply (hHC.and <| hH₁_rel_C.and <| improveStep_rel_C acc N).mono
      rintro x ⟨hx, hx', hx''⟩ t
      by_cases ht : t ≤ 1 / 2
      · simp only [ht, hx, HtpyJetSec.comp_of_le]
      · simp only [ht, hx', hx'', HtpyJetSec.comp_of_not_le, not_false_iff]
    · -- rel K₁
      intro x hx t
      by_cases ht : t ≤ 1 / 2
      · simp only [ht, hx, hHK₁, HtpyJetSec.comp_of_le, not_false_iff]
      · simp only [ht, hx, hH₁_K₁, improveStep_rel_compl_K₁, HtpyJetSec.comp_of_not_le,
          not_false_iff, S]
    · -- C⁰-close
      intro x t
      by_cases ht : t ≤ 1 / 2
      · apply le_trans _ (half_le_self <| le_of_lt δ_pos)
        simp only [ht, hHc0, HtpyJetSec.comp_of_le]
      · simp only [ht, HtpyJetSec.comp_of_not_le, not_false_iff]
        rw [← add_halves δ]
        exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans <| add_le_add (hN_close _ _)
          (hHc0 _ _)
    · -- formal solution
      intro t
      by_cases ht : t ≤ 1 / 2
      · simp only [ht, hH_sol, HtpyJetSec.comp_of_le]
      · simp only [ht, hN_sol, HtpyJetSec.comp_of_not_le, not_false_iff]
    · -- part-hol E' (k + 1)
      rw [h_span, HtpyJetSec.comp_1]
      apply improveStep_part_hol acc hNneq

include ε_pos h_op h_ample in
/-- A repackaging of `RelLoc.FormalSol.improve` for convenience. -/
theorem RelLoc.FormalSol.improve_htpy' (𝓕 : FormalSol R)
    (h_hol : ∀ᶠ x near L.C, 𝓕.IsHolonomicAt x) :
    ∃ H : HtpyFormalSol R,
      (∀ᶠ t near Iic 0, H t = 𝓕) ∧
        (∀ᶠ t near Ici 1, H t = H 1) ∧
          (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x) ∧
            (∀ x ∉ L.K₁, ∀ t, H t x = 𝓕 x) ∧
              (∀ x t, ‖(H t).f x - 𝓕.f x‖ < ε) ∧ ∀ᶠ x near L.K₀, (H 1).IsHolonomicAt x := by
  rcases 𝓕.improve h_op h_ample L (half_pos ε_pos) h_hol with ⟨H, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  exact
    ⟨{ H with is_sol := h₆ }, h₁, h₂, h₃, h₄, fun x t ↦ (h₅ x t).trans_lt (half_lt_self ε_pos), h₇⟩

end Improve
end
end
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinatePushforward
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension of a supported coordinate change through any smooth surface
coordinate neighborhood, including the constructed crosscap coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M]
variable {V : Type*} [NormedAddCommGroup V]

lemma coordinatePushforward_source (c : OpenPartialHomeomorph M Base)
    (δ : Base → V) {q : M} (hq : q ∈ c.source) :
    coordinatePushforward c δ q = δ (c q) := indicator_of_mem hq _

lemma coordinatePushforward_zero_off (c : OpenPartialHomeomorph M Base)
    (δ : Base → V) {q : M} (hq : q ∉ c.symm '' tsupport δ) :
    coordinatePushforward c δ q = 0 := by
  by_cases hs : q ∈ c.source
  · rw [coordinatePushforward_source c δ hs]
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    exact hq ⟨c q,hz,c.left_inv hs⟩
  · exact indicator_of_notMem hs _

variable [T2Space M]

lemma coordinatePushforward_tsupport (c : OpenPartialHomeomorph M Base)
    {δ : Base → V} (hc : HasCompactSupport δ) (hs : tsupport δ ⊆ c.target) :
    tsupport (coordinatePushforward c δ) ⊆ c.symm '' tsupport δ := by
  have hK : IsCompact (c.symm '' tsupport δ) :=
    hc.image_of_continuousOn (c.continuousOn_symm.mono hs)
  apply closure_minimal _ hK.isClosed
  intro q hq
  by_contra hn
  exact hq (coordinatePushforward_zero_off c δ hn)

variable [ChartedSpace Plane M] [NormedSpace ℝ V]

lemma coordinatePushforward_smooth (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    {δ : Base → V} (hd : ContDiff ℝ ∞ δ) (hc : HasCompactSupport δ)
    (hs : tsupport δ ⊆ c.target) :
    ContMDiff planeModel 𝓘(ℝ,V) ∞ (coordinatePushforward c δ) := by
  intro q
  by_cases hq : q ∈ tsupport (coordinatePushforward c δ)
  · obtain ⟨z,hz,rfl⟩ := coordinatePushforward_tsupport c hc hs hq
    have hsource := c.map_target (hs hz)
    have hlocal := hd.contMDiff.contMDiffAt.comp _
      (hcs.contMDiffAt (c.open_source.mem_nhds hsource))
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds hsource] with y hy
    exact coordinatePushforward_source c δ hy
  · exact contMDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hq)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicPrimitive
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The normalized periodic antiderivative used by the finite periodic expansion.
The primitive is constructed by integration, followed by subtraction of its
mean.  The period is one, matching `UnitAddCircle`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem rawPrimitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (rawPrimitive f) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem rawPrimitive_contDiff {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (rawPrimitive f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (rawPrimitive_hasDerivAt hf.continuous x).differentiableAt, ?_⟩
  have he : deriv (rawPrimitive f) = f := by
    funext x
    exact (rawPrimitive_hasDerivAt hf.continuous x).deriv
  rwa [he]

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MonotoneGermExtension
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extending an oriented smooth coordinate germ to a globally increasing
smooth real function, with derivative one outside a compact set. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem increasing_smooth_germ_extension {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ℝ) (ha : 0 < deriv h a) :
    ∃ (g : ℝ → ℝ) (K : Set ℝ), ContDiff ℝ ∞ g ∧ StrictMono g ∧
      g =ᶠ[𝓝 a] h ∧ (∀ x, 0 < deriv g x) ∧ IsCompact K ∧
      ∀ x ∉ K, deriv g x = 1 := by
  have hd : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  let U := {x | 0 < deriv h x}
  have hU : IsOpen U := isOpen_lt continuous_const hd.continuous
  obtain ⟨W,hW,haW,hWU,φ,χ,hφ,hχ,hφc,hχc,hφr,hχr,hχs,hφs,hφone,hχone⟩ :=
    CollarVelocity.nested_compact_cutoffs (isCompact_singleton (x := a)) hU
      (singleton_subset_iff.mpr ha)
  let v : ℝ → ℝ := fun x => φ x * deriv h x + (1-φ x)
  have hv : ContDiff ℝ ∞ v := (hφ.mul hd).add (contDiff_const.sub hφ)
  have hvpos : ∀ x, 0 < v x := by
    intro x
    by_cases hx : x ∈ U
    · have hdpos : 0 < deriv h x := hx
      have hφnonneg := (hφr x).1
      have hφle := (hφr x).2
      by_cases hzero : φ x = 0
      · simp [v,hzero]
      · have hφpos : 0 < φ x := lt_of_le_of_ne hφnonneg (Ne.symm hzero)
        have hmul := mul_pos hφpos hdpos
        dsimp [v]
        linarith
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hin => hx (hφs hin))
      simp [v,hz]
  let g : ℝ → ℝ := fun x => h a +
    PeriodicPrimitive.rawPrimitive v x - PeriodicPrimitive.rawPrimitive v a
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_const.add (PeriodicPrimitive.rawPrimitive_contDiff hv)).sub contDiff_const
  have hgder : ∀ x, deriv g x = v x := by
    intro x
    exact (((PeriodicPrimitive.rawPrimitive_hasDerivAt hv.continuous x).const_add (h a)).sub_const _).deriv
  have hag : g a = h a := by dsimp [g] <;> ring
  obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hW a (haW (by simp))
  have heq : EqOn g h (Metric.ball a r) := by
    apply isOpen_ball.eqOn_of_deriv_eq (convex_ball a r).isPreconnected
      (hg.differentiable (by simp)).differentiableOn (hh.differentiable (by simp)).differentiableOn
    · intro x hx
      rw [hgder]
      dsimp [v]
      rw [hφone x (hrW hx)]
      ring
    · exact Metric.mem_ball_self hr
    · exact hag
  refine ⟨g,tsupport φ,hg,strictMono_of_deriv_pos (fun x => (hgder x) ▸ hvpos x),
    heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds (Metric.mem_ball_self hr)),
    fun x => (hgder x) ▸ hvpos x,hφc,?_⟩
  intro x hx
  rw [hgder]
  have hz := image_eq_zero_of_notMem_tsupport hx
  simp [v,hz]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MonotoneGermDiffeomorphism
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The increasing extensions are global diffeomorphisms, allowing local
arc coordinates to be joined without changing their germs. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma affine_tails_of_deriv_one {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {K : Set ℝ} (hK : IsCompact K) (hd : ∀ x ∉ K, deriv g x = 1) :
    ∃ R cPos cNeg : ℝ, (∀ x, R < x → g x = x+cPos) ∧
      ∀ x, x < -R → g x = x+cNeg := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (continuous_id : Continuous (id : ℝ → ℝ)).continuousOn
  let R := |C|+1
  have hout : ∀ x, R < |x| → x ∉ K := by
    intro x hx hin
    have hb := hC x hin
    change ‖x‖ ≤ C at hb
    rw [Real.norm_eq_abs] at hb
    have hc := le_abs_self C
    dsimp [R] at hx
    linarith
  have hplus : EqOn g (fun x => x+(g (R+1)-(R+1))) (Ioi R) := by
    apply isOpen_Ioi.eqOn_of_deriv_eq (convex_Ioi R).isPreconnected
      (hg.differentiable (by simp)).differentiableOn
      (differentiable_id.add_const _).differentiableOn
    · intro x hx
      rw [hd x (hout x (lt_of_lt_of_le hx (le_abs_self x)))]
      simp
    · change R < R+1
      linarith
    · dsimp only [id]
      ring
  have hminus : EqOn g (fun x => x+(g (-R-1)-(-R-1))) (Iio (-R)) := by
    apply isOpen_Iio.eqOn_of_deriv_eq (convex_Iio (-R)).isPreconnected
      (hg.differentiable (by simp)).differentiableOn
      (differentiable_id.add_const _).differentiableOn
    · intro x hx
      have hxr : x < -R := hx
      have habs : R < |x| := by linarith [neg_le_abs x]
      rw [hd x (hout x habs)]
      simp
    · change -R-1 < -R
      linarith
    · dsimp only [id]
      ring
  exact ⟨R,g (R+1)-(R+1),g (-R-1)-(-R-1),fun x hx => hplus hx,fun x hx => hminus hx⟩

lemma surjective_of_deriv_one_off_compact {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {K : Set ℝ} (hK : IsCompact K) (hd : ∀ x ∉ K, deriv g x = 1) :
    Function.Surjective g := by
  obtain ⟨R,cPos,cNeg,hplus,hminus⟩ := affine_tails_of_deriv_one hg hK hd
  have htop : Tendsto g atTop atTop := by
    apply (tendsto_atTop_add_const_right atTop cPos tendsto_id).congr'
    filter_upwards [eventually_gt_atTop R] with x hx
    exact (hplus x hx).symm
  have hbot : Tendsto g atBot atBot := by
    apply (tendsto_atBot_add_const_right atBot cNeg tendsto_id).congr'
    filter_upwards [eventually_lt_atBot (-R)] with x hx
    exact (hminus x hx).symm
  exact hg.continuous.surjective htop hbot

theorem increasing_smooth_germ_diffeomorphism {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ℝ) (ha : 0 < deriv h a) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      StrictMono e ∧ e =ᶠ[𝓝 a] h := by
  obtain ⟨g,K,hg,hmono,he,hpos,hK,hd⟩ := increasing_smooth_germ_extension hh a ha
  have hsurj := surjective_of_deriv_one_off_compact hg hK hd
  let e := (hmono.orderIsoOfSurjective g hsurj).toHomeomorph
  have heq : (e : ℝ → ℝ) = g := rfl
  refine ⟨e,by simpa only [heq] using hg,?_,by simpa only [heq] using hmono,by simpa only [heq] using he⟩
  apply e.contDiff_symm_deriv (f' := deriv g)
  · intro x
    exact ne_of_gt (hpos x)
  · intro x
    change HasDerivAt g (deriv g x) x
    exact (hg.differentiable (by simp) x).hasDerivAt
  · simpa only [heq] using hg

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothArcJoin
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth joining at a common germ, with regularity and injectivity
retained on the two ordered pieces of the parameter interval. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*}

lemma joinedCurve_germ_left (a : ℝ) (γ δ : ℝ → M) {t : ℝ} (ht : t < a) :
    joinedCurve a γ δ =ᶠ[𝓝 t] γ := by
  filter_upwards [eventually_lt_nhds ht] with s hs
  simp only [joinedCurve,ite_eq_left hs.le]

lemma joinedCurve_germ_right (a : ℝ) (γ δ : ℝ → M) {t : ℝ} (ht : a < t) :
    joinedCurve a γ δ =ᶠ[𝓝 t] δ := by
  filter_upwards [eventually_gt_nhds ht] with s hs
  simp only [joinedCurve,ite_eq_right (not_le.mpr hs)]

lemma joinedCurve_germ_center (a : ℝ) {γ δ : ℝ → M} (he : γ =ᶠ[𝓝 a] δ) :
    joinedCurve a γ δ =ᶠ[𝓝 a] γ := by
  filter_upwards [he] with s hs
  dsimp only [joinedCurve]
  split_ifs
  · rfl
  · exact hs.symm

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem joinedCurve_smooth_on (a : ℝ) {γ δ : ℝ → M} {U : Set ℝ}
    (hγ : ∀ t ∈ U, t ≤ a → ContMDiffAt 𝓘(ℝ) I ∞ γ t)
    (hδ : ∀ t ∈ U, a ≤ t → ContMDiffAt 𝓘(ℝ) I ∞ δ t)
    (he : γ =ᶠ[𝓝 a] δ) :
    ContMDiffOn 𝓘(ℝ) I ∞ (joinedCurve a γ δ) U := by
  intro t ht
  rcases lt_trichotomy t a with h | heq | h
  · exact ((hγ t ht h.le).congr_of_eventuallyEq (joinedCurve_germ_left a γ δ h)).contMDiffWithinAt
  · subst t
    exact ((hγ a ht le_rfl).congr_of_eventuallyEq (joinedCurve_germ_center a he)).contMDiffWithinAt
  · exact ((hδ t ht h.le).congr_of_eventuallyEq (joinedCurve_germ_right a γ δ h)).contMDiffWithinAt

theorem joinedCurve_regular_on (a : ℝ) {γ δ : ℝ → M} {U : Set ℝ}
    (hγ : ∀ t ∈ U, t ≤ a → Function.Injective (mfderiv 𝓘(ℝ) I γ t))
    (hδ : ∀ t ∈ U, a ≤ t → Function.Injective (mfderiv 𝓘(ℝ) I δ t))
    (he : γ =ᶠ[𝓝 a] δ) :
    ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) I (joinedCurve a γ δ) t) := by
  intro t ht
  rcases lt_trichotomy t a with h | heq | h
  · rw [(joinedCurve_germ_left a γ δ h).mfderiv_eq]
    exact hγ t ht h.le
  · subst t
    rw [(joinedCurve_germ_center a he).mfderiv_eq]
    exact hγ a ht le_rfl
  · rw [(joinedCurve_germ_right a γ δ h).mfderiv_eq]
    exact hδ t ht h.le

end Smooth

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_IntervalDerivativeZero
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth scalar coordinate vanishing on a one-sided interval has
zero derivative at its endpoint as well. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem deriv_zero_of_interval_germ {g : ℝ → ℝ} {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b) (hg : DifferentiableAt ℝ g t)
    (he : g =ᶠ[𝓝[Icc a b] t] fun _ => 0) : deriv g t = 0 := by
  have hz : HasDerivWithinAt g 0 (Icc a b) t :=
    (hasDerivWithinAt_const t (Icc a b) (0:ℝ)).congr_of_eventuallyEq_of_mem he ht
  exact ((uniqueDiffOn_Icc hab) t ht).eq_deriv (Icc a b) hg.hasDerivAt.hasDerivWithinAt hz

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NonzeroGermDiffeomorphism
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A scalar smooth coordinate with nonzero derivative has a global smooth
homeomorphism representative of either orientation. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem nonzero_smooth_germ_diffeomorphism {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ℝ) (ha : deriv h a ≠ 0) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      (StrictMono e ∨ StrictAnti e) ∧ e =ᶠ[𝓝 a] h := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hn : ContDiff ℝ ∞ (fun x => -h x) := hh.neg
    have hd : 0 < deriv (fun x => -h x) a := by
      rw [show (fun x => -h x) = -h from rfl, deriv.neg]
      exact neg_pos.mpr hneg
    obtain ⟨e,hes,hei,hem,he⟩ := increasing_smooth_germ_diffeomorphism hn a hd
    let E := e.trans (Homeomorph.neg ℝ)
    have hEs : ContDiff ℝ ∞ E := contDiff_neg.comp hes
    have hEi : ContDiff ℝ ∞ E.symm := hei.comp contDiff_neg
    have hEm : StrictAnti E := by
      intro x y hxy
      exact neg_lt_neg (hem hxy)
    refine ⟨E,hEs,hEi,Or.inr hEm,?_⟩
    filter_upwards [he] with x hx
    change -e x = h x
    rw [hx,neg_neg]
  · obtain ⟨e,hes,hei,hem,he⟩ := increasing_smooth_germ_diffeomorphism hh a hpos
    exact ⟨e,hes,hei,Or.inl hem,he⟩

theorem nonzero_local_germ_diffeomorphism {h : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) {a : ℝ}
    (haU : a ∈ U) (ha : deriv h a ≠ 0) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      (StrictMono e ∨ StrictAnti e) ∧ e =ᶠ[𝓝 a] h := by
  obtain ⟨W,hW,haW,_,H,hH,hEH⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := a)) hU (singleton_subset_iff.mpr haU) hh
  have he : H =ᶠ[𝓝 a] h := hEH.eventuallyEq_of_mem (hW.mem_nhds (haW (by simp)))
  have hd : deriv H a ≠ 0 := by rw [he.deriv_eq]; exact ha
  obtain ⟨e,hes,hei,hem,hee⟩ := nonzero_smooth_germ_diffeomorphism hH a hd
  exact ⟨e,hes,hei,hem,hee.trans he⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_StandardCrosscapDerivative
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The standard umbrella has one singular point and a transverse double ray. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardBaseNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardBaseSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardTripleNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardTripleSpace
lemma standardCrosscap_hasFDerivAt (x : Base) :
    HasFDerivAt standardCrosscap (standardCrosscapDerivative x) x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x
  have h := (((h0.mul h1).smul_const ((![1,0],0) : Base × ℝ)).add
    ((h1.pow 2).smul_const ((![0,1],0) : Base × ℝ))).add
      (h0.smul_const ((0,1) : Base × ℝ))
  have he : (fun y : Base => (y 0*y 1) • ((![1,0],0) : Base × ℝ) +
      (y 1)^2 • ((![0,1],0) : Base × ℝ) + y 0 • ((0,1) : Base × ℝ)) =
      standardCrosscap := by
    funext y
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [standardCrosscap]
    · simp [standardCrosscap]
  change HasFDerivAt (fun y : Base => (y 0*y 1) • ((![1,0],0) : Base × ℝ) +
    (y 1)^2 • ((![0,1],0) : Base × ℝ) + y 0 • ((0,1) : Base × ℝ)) _ x at h
  rw [he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [standardCrosscapDerivative]
    ring
  · simp [standardCrosscapDerivative]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapAxisCurve
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The kernel axis of an actual crosscap chart gives a smooth regular
source curve through the singular point, even though its image velocity vanishes. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma crosscapAxis_apply (t : ℝ) : crosscapAxis t = ![0,t] := by
  ext i
  fin_cases i <;> rfl

lemma crosscapAxis_injective : Function.Injective crosscapAxis := by
  intro x y he
  simpa only [crosscapAxis_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using congrFun he 1

lemma crosscapAxis_regular (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) crosscapAxis t) := by
  have hd : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ,Base) crosscapAxis t crosscapAxis :=
    crosscapAxis.hasFDerivAt.hasMFDerivAt
  exact hd.mfderiv.symm ▸ crosscapAxis_injective

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

theorem axis_curve (c : SurfaceCrosscapCoordinates f p) :
    ∃ U : Set ℝ, IsOpen U ∧ 0 ∈ U ∧
      ContMDiffOn 𝓘(ℝ) planeModel ∞ c.axisCurve U ∧
      (∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) planeModel c.axisCurve t)) ∧
      c.axisCurve 0 = p ∧
      (∀ t ∈ U, c.axisCurve t ∈ c.source.source ∧ c.source (c.axisCurve t) = ![0,t]) := by
  let U := crosscapAxis ⁻¹' c.source.target
  have hU : IsOpen U := c.source.open_target.preimage crosscapAxis.continuous
  have h0 : (0:ℝ) ∈ U := by
    change crosscapAxis 0 ∈ c.source.target
    rw [map_zero,← c.source_center]
    exact c.source.map_source c.source_mem
  have hk : ContMDiff 𝓘(ℝ) 𝓘(ℝ,Base) ∞ crosscapAxis := crosscapAxis.contDiff.contMDiff
  have hs : ContMDiffOn 𝓘(ℝ) planeModel ∞ c.axisCurve U :=
    c.source_inverse_smooth.comp hk.contMDiffOn (fun _ ht => ht)
  have hdif : c.source.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨c.source_inverse_smooth.mdifferentiableOn (by simp),c.source_smooth.mdifferentiableOn (by simp)⟩
  refine ⟨U,hU,h0,hs,?_,?_,?_⟩
  · intro t ht
    change Function.Injective (mfderiv 𝓘(ℝ) planeModel (c.source.symm ∘ crosscapAxis) t)
    rw [mfderiv_comp t
      ((c.source_inverse_smooth.contMDiffAt (c.source.open_target.mem_nhds ht)).mdifferentiableAt (by simp))
      (hk.mdifferentiable (by simp) t)]
    exact (hdif.mfderiv_injective ht).comp (crosscapAxis_regular t)
  · change c.source.symm (crosscapAxis 0) = p
    rw [map_zero,← c.source_center,c.source.left_inv c.source_mem]
  · intro t ht
    exact ⟨c.source.map_target ht,(c.source.right_inv ht).trans (crosscapAxis_apply t)⟩

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RegularCurveGerms
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regularity under smooth reparameterization and actual curve germs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma regular_curve_reparameterization {γ : ℝ → M} (e : ℝ ≃ₜ ℝ)
    (hes : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ) planeModel ∞ γ (e t))
    (hi : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ (e t))) :
    Function.Injective (mfderiv 𝓘(ℝ) planeModel (γ ∘ e) t) := by
  have heD : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ) 𝓘(ℝ) :=
    ⟨hes.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn,
      hei.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn⟩
  rw [mfderiv_comp t (hγ.mdifferentiableAt (by simp)) (hes.contMDiff.mdifferentiable (by simp) t)]
  exact hi.comp (heD.mfderiv_injective (mem_univ t))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapAxisCoordinates
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction of the two source branches from their scalar
kernel-axis parameter in the actual crosscap chart. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

lemma axisCurve_coordinate (c : SurfaceCrosscapCoordinates f p) {x : M}
    (hx : x ∈ c.source.source) (hzero : c.source x 0 = 0) :
    c.axisCurve (c.source x 1) = x := by
  have he : crosscapAxis (c.source x 1) = c.source x := by
    rw [crosscapAxis_apply]
    ext i
    fin_cases i
    · exact hzero.symm
    · rfl
  change c.source.symm (crosscapAxis (c.source x 1)) = x
  rw [he,c.source.left_inv hx]

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothArcStartGerm
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replace only the exterior germ of a compact smooth arc, retaining
its entire closed trace and its opposite endpoint germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
namespace SmoothCompactArc

theorem replace_start_germ (P : SmoothCompactArc I N) {γ : ℝ → N} {U : Set ℝ}
    (hU : IsOpen U) (hsU : P.start ∈ U)
    (hsmooth : ContMDiffOn 𝓘(ℝ) I ∞ γ U)
    (hregular : ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) I γ t))
    (hEq : EqOn γ P.curve (U ∩ Icc P.start P.finish)) :
    ∃ R : SmoothCompactArc I N, R.start = P.start ∧ R.finish = P.finish ∧
      EqOn R.curve P.curve (Icc P.start P.finish) ∧
      R.curve =ᶠ[𝓝 P.start] γ ∧ R.curve =ᶠ[𝓝 P.finish] P.curve := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU P.start hsU
  let d := min (r/2) ((P.finish-P.start)/2)
  have hd : 0 < d := lt_min (half_pos hr) (half_pos (sub_pos.mpr P.start_lt_finish))
  let b := P.start+d
  have hsb : P.start < b := by dsimp [b] <;> linarith
  have hbf : b < P.finish := by
    have h := min_le_right (r/2) ((P.finish-P.start)/2)
    dsimp [b,d] <;> linarith
  have hbr : b-P.start < r := by
    have h := min_le_left (r/2) ((P.finish-P.start)/2)
    dsimp [b,d] <;> linarith
  have hBU : Icc P.start b ⊆ U := by
    intro t ht
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hbU := hBU (right_mem_Icc.mpr hsb.le)
  have hmatch : γ =ᶠ[𝓝 b] P.curve := by
    filter_upwards [hU.mem_nhds hbU,Ioo_mem_nhds hsb hbf] with t htU ht
    exact hEq ⟨htU,ht.1.le,ht.2.le⟩
  let W := (U ∩ Iio b) ∪ (P.domain ∩ Ioi b) ∪ (U ∩ P.domain)
  have hW : IsOpen W := ((hU.inter isOpen_Iio).union
    (P.domain_open.inter isOpen_Ioi)).union (hU.inter P.domain_open)
  have hleft : ∀ t ∈ W, t ≤ b → t ∈ U := by
    intro t ht htb
    rcases ht with (ht | ht) | ht
    · exact ht.1
    · exact False.elim (not_lt_of_ge htb ht.2)
    · exact ht.1
  have hright : ∀ t ∈ W, b ≤ t → t ∈ P.domain := by
    intro t ht hbt
    rcases ht with (ht | ht) | ht
    · exact False.elim (not_lt_of_ge hbt ht.2)
    · exact ht.1
    · exact ht.2
  have hsub : Icc P.start P.finish ⊆ W := by
    intro t ht
    rcases lt_trichotomy t b with h | rfl | h
    · exact Or.inl (Or.inl ⟨hBU ⟨ht.1,h.le⟩,h⟩)
    · exact Or.inr ⟨hbU,P.interval_subset ⟨hsb.le,hbf.le⟩⟩
    · exact Or.inl (Or.inr ⟨P.interval_subset ht,h⟩)
  have hs : ContMDiffOn 𝓘(ℝ) I ∞ (joinedCurve b γ P.curve) W := by
    apply joinedCurve_smooth_on
    · intro t ht htb
      exact hsmooth.contMDiffAt (hU.mem_nhds (hleft t ht htb))
    · intro t ht hbt
      exact P.smooth.contMDiffAt (P.domain_open.mem_nhds (hright t ht hbt))
    · exact hmatch
  have hr' : ∀ t ∈ W, Function.Injective (mfderiv 𝓘(ℝ) I (joinedCurve b γ P.curve) t) := by
    apply joinedCurve_regular_on
    · intro t ht htb
      exact hregular t (hleft t ht htb)
    · intro t ht hbt
      exact P.regular t (hright t ht hbt)
    · exact hmatch
  have he : EqOn (joinedCurve b γ P.curve) P.curve (Icc P.start P.finish) := by
    intro t ht
    by_cases htb : t ≤ b
    · simp only [joinedCurve,ite_eq_left htb]
      exact hEq ⟨hBU ⟨ht.1,htb⟩,ht⟩
    · simp only [joinedCurve,ite_eq_right htb]
  have hi : (Icc P.start P.finish).InjOn (joinedCurve b γ P.curve) := by
    intro s hs t ht hst
    apply P.injective hs ht
    rw [← he hs,← he ht]
    exact hst
  let R : SmoothCompactArc I N := ⟨_,P.start,P.finish,P.start_lt_finish,W,hW,hsub,hs,hr',hi⟩
  exact ⟨R,rfl,rfl,he,joinedCurve_germ_left b γ P.curve hsb,
    joinedCurve_germ_right b γ P.curve hbf⟩

end SmoothCompactArc
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothArcReverse
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversing a compact smooth regular arc preserves its image and
exchanges the endpoint germs, with no loss of regularity. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
namespace SmoothCompactArc

theorem reverse_arc (P : SmoothCompactArc I N) :
    ∃ R : SmoothCompactArc I N,
      R.start = -P.finish ∧ R.finish = -P.start ∧
      R.domain = (fun t : ℝ => -t) ⁻¹' P.domain ∧
      R.curve = (fun t => P.curve (-t)) ∧
      R.curve '' Icc R.start R.finish = P.curve '' Icc P.start P.finish := by
  let e : ℝ ≃ₜ ℝ := Homeomorph.neg ℝ
  have hes : ContDiff ℝ ∞ e := contDiff_neg
  have hei : ContDiff ℝ ∞ e.symm := contDiff_neg
  have heD : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ) 𝓘(ℝ) :=
    ⟨hes.contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.mdifferentiableOn,
      hei.contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.mdifferentiableOn⟩
  let U := e ⁻¹' P.domain
  have hsub : Icc (-P.finish) (-P.start) ⊆ U := by
    intro t ht
    apply P.interval_subset
    change P.start ≤ -t ∧ -t ≤ P.finish
    constructor <;> linarith [ht.1,ht.2]
  have hs : ContMDiffOn 𝓘(ℝ) I ∞ (P.curve ∘ e) U :=
    P.smooth.comp hes.contMDiff.contMDiffOn (fun _ ht => ht)
  have hr : ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) I (P.curve ∘ e) t) := by
    intro t ht
    rw [mfderiv_comp t
      ((P.smooth.contMDiffAt (P.domain_open.mem_nhds ht)).mdifferentiableAt (by simp))
      (hes.contMDiff.mdifferentiable (by simp) t)]
    exact (P.regular _ ht).comp (heD.mfderiv_injective (mem_univ t))
  have hi : InjOn (P.curve ∘ e) (Icc (-P.finish) (-P.start)) := by
    intro t ht u hu heq
    have ht' : -t ∈ Icc P.start P.finish := by constructor <;> linarith [ht.1,ht.2]
    have hu' : -u ∈ Icc P.start P.finish := by constructor <;> linarith [hu.1,hu.2]
    exact neg_injective (P.injective ht' hu' heq)
  let R : SmoothCompactArc I N := ⟨P.curve ∘ e,-P.finish,-P.start,
    neg_lt_neg P.start_lt_finish,U,P.domain_open.preimage e.continuous,hsub,hs,hr,hi⟩
  refine ⟨R,rfl,rfl,rfl,rfl,?_⟩
  apply Set.Subset.antisymm
  · rintro y ⟨t,ht,rfl⟩
    refine ⟨-t,?_,rfl⟩
    constructor <;> linarith [ht.1,ht.2]
  · rintro y ⟨t,ht,rfl⟩
    refine ⟨-t,?_,?_⟩
    · constructor <;> linarith [ht.1,ht.2]
    · change P.curve (- -t) = P.curve t
      rw [neg_neg]

end SmoothCompactArc
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothCrosscapAxisTangent
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smoothed source arc has a nonzero axial velocity and
zero image velocity at its singular endpoint. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

theorem smooth_crosscap_axis_tangent (c : SurfaceCrosscapCoordinates f p)
    (P : SmoothCompactArc planeModel M) {t : ℝ} (ht : t ∈ Icc P.start P.finish)
    (hPt : P.curve t = p) {V : Set M} (hV : IsOpen V) (hpV : p ∈ V)
    (haxis : ∀ u ∈ Icc P.start P.finish, P.curve u ∈ V →
      P.curve u ∈ c.source.source ∧ c.source (P.curve u) 0 = 0) :
    deriv (c.source ∘ P.curve) t 0 = 0 ∧
      deriv (c.source ∘ P.curve) t 1 ≠ 0 ∧ deriv (f ∘ P.curve) t = 0 := by
  have hPtS : P.curve t ∈ c.source.source := hPt ▸ c.source_mem
  have hPc := P.smooth.contMDiffAt (P.domain_open.mem_nhds (P.interval_subset ht))
  have hcc := c.source_smooth.contMDiffAt (c.source.open_source.mem_nhds hPtS)
  let g : ℝ → Base := c.source ∘ P.curve
  have hgc : ContDiffAt ℝ ∞ g t := (hcc.comp t hPc).contDiffAt
  have hgd := hgc.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hg0 : g t = 0 := by change c.source (P.curve t) = 0; rw [hPt,c.source_center]
  have hgi : Function.Injective (fderiv ℝ g t) := by
    have hd : c.source.MDifferentiable planeModel 𝓘(ℝ,Base) :=
      ⟨c.source_smooth.mdifferentiableOn (by simp),c.source_inverse_smooth.mdifferentiableOn (by simp)⟩
    rw [← mfderiv_eq_fderiv,mfderiv_comp t (hcc.mdifferentiableAt (by simp))
      (hPc.mdifferentiableAt (by simp))]
    exact (hd.mfderiv_injective hPtS).comp (P.regular t (P.interval_subset ht))
  have hnear : ∀ᶠ u in 𝓝 t, P.curve u ∈ V := hPc.continuousAt.eventually (hV.mem_nhds (hPt ▸ hpV))
  have he : (fun u => g u 0) =ᶠ[𝓝[Icc P.start P.finish] t] fun _ => (0:ℝ) := by
    filter_upwards [self_mem_nhdsWithin,hnear.filter_mono nhdsWithin_le_nhds] with u hu huV
    exact (haxis u hu huV).2
  have hd0 : HasDerivAt (fun u => g u 0) (deriv g t 0) t :=
    (ContinuousLinearMap.proj (0:Fin 2) : Base →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hgd.hasDerivAt
  have hz : deriv g t 0 = 0 := hd0.deriv.symm.trans
    (deriv_zero_of_interval_germ P.start_lt_finish ht hd0.differentiableAt he)
  have hn : deriv g t 1 ≠ 0 := by
    intro hn
    have hgz : deriv g t = 0 := by
      ext i
      fin_cases i
      · exact hz
      · exact hn
    have h01 : fderiv ℝ g t 1 = fderiv ℝ g t 0 := by
      rw [fderiv_apply_one_eq_deriv,hgz,map_zero]
    have h := hgi h01
    norm_num at h
  have hstd : HasDerivAt (standardCrosscap ∘ g) 0 t := by
    have hh := (standardCrosscap_hasFDerivAt (g t)).comp_hasDerivAt t hgd.hasDerivAt
    have hval : standardCrosscapDerivative (g t) (deriv g t) = 0 := by
      rw [hg0]
      apply Prod.ext
      · ext i
        fin_cases i <;> simp [standardCrosscapDerivative]
      · simpa [standardCrosscapDerivative] using hz
    exact hval ▸ hh
  have htarget := (c.target_smooth.differentiable (by simp) (standardCrosscap (g t))).hasFDerivAt.comp_hasDerivAt t hstd
  have hmatch : f ∘ P.curve =ᶠ[𝓝 t] c.target ∘ (standardCrosscap ∘ g) := by
    filter_upwards [hPc.continuousAt.eventually (c.source.open_source.mem_nhds hPtS)] with u hu
    exact c.model_eq (P.curve u) hu
  refine ⟨hz,hn,?_⟩
  rw [hmatch.deriv_eq,htarget.deriv,map_zero]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapAxisStartGerm
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Straighten the exterior start germ to the actual crosscap kernel
axis, without changing any point of the compact source arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

theorem crosscap_axis_start_germ (c : SurfaceCrosscapCoordinates f p)
    (P : SmoothCompactArc planeModel M) (hPs : P.curve P.start = p)
    {V : Set M} (hV : IsOpen V) (hpV : p ∈ V)
    (haxis : ∀ u ∈ Icc P.start P.finish, P.curve u ∈ V →
      P.curve u ∈ c.source.source ∧ c.source (P.curve u) 0 = 0) :
    ∃ (R : SmoothCompactArc planeModel M) (e : ℝ ≃ₜ ℝ),
      R.start = P.start ∧ R.finish = P.finish ∧
      EqOn R.curve P.curve (Icc P.start P.finish) ∧
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ e P.start = 0 ∧
      R.curve =ᶠ[𝓝 P.start] c.axisCurve ∘ e ∧
      R.curve =ᶠ[𝓝 P.finish] P.curve := by
  let g : ℝ → Base := c.source ∘ P.curve
  let h : ℝ → ℝ := fun t => g t 1
  let U := P.domain ∩ P.curve ⁻¹' c.source.source
  have hU : IsOpen U := P.smooth.continuousOn.isOpen_inter_preimage
    P.domain_open c.source.open_source
  have hsP := P.interval_subset (left_mem_Icc.mpr P.start_lt_finish.le)
  have hsU : P.start ∈ U := ⟨hsP,hPs ▸ c.source_mem⟩
  have hg : ContDiffOn ℝ ∞ g U := (c.source_smooth.comp
    (P.smooth.mono inter_subset_left) (fun _ ht => ht.2)).contDiffOn
  have hh : ContDiffOn ℝ ∞ h U := (contDiff_apply ℝ ℝ (1:Fin 2)).comp_contDiffOn hg
  have hgd := (hg.contDiffAt (hU.mem_nhds hsU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd1 : HasDerivAt h (deriv g P.start 1) P.start :=
    (ContinuousLinearMap.proj (1:Fin 2) : Base →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt P.start hgd.hasDerivAt
  have hn : deriv h P.start ≠ 0 := by
    rw [hd1.deriv]
    exact (smooth_crosscap_axis_tangent c P (left_mem_Icc.mpr P.start_lt_finish.le)
      hPs hV hpV haxis).2.1
  obtain ⟨e,hes,hei,_,he⟩ := nonzero_local_germ_diffeomorphism hU hh hsU hn
  have he0 : e P.start = 0 := by
    rw [he.eq_of_nhds]
    change c.source (P.curve P.start) 1 = 0
    rw [hPs,c.source_center]
    rfl
  obtain ⟨A,hA,h0A,hAs,hAr,_,_⟩ := c.axis_curve
  let G : ℝ → M := c.axisCurve ∘ e
  let B := e ⁻¹' A
  have hB : IsOpen B := hA.preimage e.continuous
  have hsB : P.start ∈ B := by change e P.start ∈ A; rwa [he0]
  have hGs : ContMDiffOn 𝓘(ℝ) planeModel ∞ G B :=
    hAs.comp hes.contMDiff.contMDiffOn (fun _ ht => ht)
  have hGr : ∀ t ∈ B, Function.Injective (mfderiv 𝓘(ℝ) planeModel G t) := by
    intro t ht
    exact regular_curve_reparameterization e hes hei
      (hAs.contMDiffAt (hA.mem_nhds ht)) (hAr _ ht)
  obtain ⟨W,hEq,hW,hsW⟩ := eventually_nhds_iff.mp he
  let D := P.domain ∩ P.curve ⁻¹' V
  have hD : IsOpen D := P.smooth.continuousOn.isOpen_inter_preimage P.domain_open hV
  have hsD : P.start ∈ D := ⟨hsP,by change P.curve P.start ∈ V; rwa [hPs]⟩
  let O := (B ∩ W) ∩ D
  have hO : IsOpen O := (hB.inter hW).inter hD
  have hsO : P.start ∈ O := ⟨⟨hsB,hsW⟩,hsD⟩
  have hGP : EqOn G P.curve (O ∩ Icc P.start P.finish) := by
    intro t ht
    change c.axisCurve (e t) = P.curve t
    rw [hEq t ht.1.1.2]
    exact c.axisCurve_coordinate (haxis t ht.2 ht.1.2.2).1 (haxis t ht.2 ht.1.2.2).2
  obtain ⟨R,hRs,hRf,hRP,hRG,hRPf⟩ := P.replace_start_germ hO hsO
    (hGs.mono (fun _ ht => ht.1.1)) (fun t ht => hGr t ht.1.1) hGP
  exact ⟨R,e,hRs,hRf,hRP,hes,hei,he0,hRG,hRPf⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapAxisFinishGerm
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The terminal exterior germ can likewise be made an exact kernel-axis
germ while preserving the closed trace and the initial germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {q : M}

theorem crosscap_axis_finish_germ (c : SurfaceCrosscapCoordinates f q)
    (P : SmoothCompactArc planeModel M) (hPf : P.curve P.finish = q)
    {V : Set M} (hV : IsOpen V) (hqV : q ∈ V)
    (haxis : ∀ u ∈ Icc P.start P.finish, P.curve u ∈ V →
      P.curve u ∈ c.source.source ∧ c.source (P.curve u) 0 = 0) :
    ∃ (R : SmoothCompactArc planeModel M) (e : ℝ ≃ₜ ℝ),
      R.start = P.start ∧ R.finish = P.finish ∧
      EqOn R.curve P.curve (Icc P.start P.finish) ∧
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ e P.finish = 0 ∧
      R.curve =ᶠ[𝓝 P.finish] c.axisCurve ∘ e ∧
      R.curve =ᶠ[𝓝 P.start] P.curve := by
  obtain ⟨S,hSs,hSf,_,hSc,_⟩ := P.reverse_arc
  have hSstart : S.curve S.start = q := by rw [hSc,hSs]; simpa using hPf
  have hSaxis : ∀ u ∈ Icc S.start S.finish, S.curve u ∈ V →
      S.curve u ∈ c.source.source ∧ c.source (S.curve u) 0 = 0 := by
    intro u hu hUV
    rw [hSs,hSf] at hu
    rw [hSc] at hUV ⊢
    exact haxis (-u) ⟨by linarith [hu.2],by linarith [hu.1]⟩ hUV
  obtain ⟨T,e,hTs,hTf,hTS,hes,hei,he0,hTe,hTSf⟩ :=
    crosscap_axis_start_germ c S hSstart hV hqV hSaxis
  obtain ⟨R,hRs,hRf,_,hRc,_⟩ := T.reverse_arc
  let E := (Homeomorph.neg ℝ).trans e
  have hEs : ContDiff ℝ ∞ E := hes.comp contDiff_neg
  have hEi : ContDiff ℝ ∞ E.symm := contDiff_neg.comp hei
  have hEs0 : E P.finish = 0 := by
    change e (-P.finish) = 0
    rwa [hSs] at he0
  have hRS : R.start = P.start := by rw [hRs,hTf,hSf,neg_neg]
  have hRF : R.finish = P.finish := by rw [hRf,hTs,hSs,neg_neg]
  have hRP : EqOn R.curve P.curve (Icc P.start P.finish) := by
    intro u hu
    have hneg : -u ∈ Icc S.start S.finish := by rw [hSs,hSf]; constructor <;> linarith [hu.1,hu.2]
    rw [hRc]
    dsimp only
    rw [hTS hneg,hSc]
    simp only [neg_neg]
  have hnFinish : Tendsto (fun u : ℝ => -u) (𝓝 P.finish) (𝓝 S.start) := by
    rw [hSs]
    exact continuous_neg.continuousAt
  have hnStart : Tendsto (fun u : ℝ => -u) (𝓝 P.start) (𝓝 S.finish) := by
    rw [hSf]
    exact continuous_neg.continuousAt
  have hRgerm : R.curve =ᶠ[𝓝 P.finish] c.axisCurve ∘ E := by
    filter_upwards [hnFinish.eventually hTe] with u hu
    rw [hRc]
    exact hu
  have hRold : R.curve =ᶠ[𝓝 P.start] P.curve := by
    filter_upwards [hnStart.eventually hTSf] with u hu
    rw [hRc]
    dsimp only
    rw [hu,hSc]
    simp only [neg_neg]
  exact ⟨R,E,hRS,hRF,hRP,hEs,hEi,hEs0,hRgerm,hRold⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapAxisEndpointGerms
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both exterior germs of the actual compact source arc can be made
exact crosscap kernel axes simultaneously, keeping every closed-arc point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem crosscap_axis_endpoint_germs (cp : SurfaceCrosscapCoordinates f p)
    (cq : SurfaceCrosscapCoordinates f q) (P : SmoothCompactArc planeModel M)
    (hPs : P.curve P.start = p) (hPf : P.curve P.finish = q)
    {V W : Set M} (hV : IsOpen V) (hpV : p ∈ V) (hW : IsOpen W) (hqW : q ∈ W)
    (hleft : ∀ u ∈ Icc P.start P.finish, P.curve u ∈ V →
      P.curve u ∈ cp.source.source ∧ cp.source (P.curve u) 0 = 0)
    (hright : ∀ u ∈ Icc P.start P.finish, P.curve u ∈ W →
      P.curve u ∈ cq.source.source ∧ cq.source (P.curve u) 0 = 0) :
    ∃ (R : SmoothCompactArc planeModel M) (e₀ e₁ : ℝ ≃ₜ ℝ),
      R.start = P.start ∧ R.finish = P.finish ∧
      EqOn R.curve P.curve (Icc P.start P.finish) ∧
      ContDiff ℝ ∞ e₀ ∧ ContDiff ℝ ∞ e₀.symm ∧ e₀ P.start = 0 ∧
      ContDiff ℝ ∞ e₁ ∧ ContDiff ℝ ∞ e₁.symm ∧ e₁ P.finish = 0 ∧
      R.curve =ᶠ[𝓝 P.start] cp.axisCurve ∘ e₀ ∧
      R.curve =ᶠ[𝓝 P.finish] cq.axisCurve ∘ e₁ := by
  obtain ⟨Q,e₀,hQs,hQf,hQP,h₀s,h₀i,h₀0,hQe,_⟩ := crosscap_axis_start_germ cp P hPs hV hpV hleft
  have hQq : Q.curve Q.finish = q := by
    rw [hQf,hQP (right_mem_Icc.mpr P.start_lt_finish.le),hPf]
  have hQright : ∀ u ∈ Icc Q.start Q.finish, Q.curve u ∈ W →
      Q.curve u ∈ cq.source.source ∧ cq.source (Q.curve u) 0 = 0 := by
    intro u hu huW
    rw [hQs,hQf] at hu
    rw [hQP hu] at huW ⊢
    exact hright u hu huW
  obtain ⟨R,e₁,hRs,hRf,hRQ,h₁s,h₁i,h₁0,hRe,hRold⟩ := crosscap_axis_finish_germ cq Q hQq hW hqW hQright
  have hRP : EqOn R.curve P.curve (Icc P.start P.finish) := by
    intro u hu
    have huQ : u ∈ Icc Q.start Q.finish := by rwa [hQs,hQf]
    exact (hRQ huQ).trans (hQP hu)
  refine ⟨R,e₀,e₁,hRs.trans hQs,hRf.trans hQf,hRP,h₀s,h₀i,h₀0,h₁s,h₁i,?_,?_,?_⟩
  · rwa [hQf] at h₁0
  · rw [hQs] at hRold
    exact hRold.trans hQe
  · rwa [hQf] at hRe

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapConnectingArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual geometric data for transporting the crosscap-pair replacement.
The arc is embedded and smooth through both endpoint kernel axes. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem exists_crosscap_connecting_arc [CompactSpace M] {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (hsimple : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∀ q, f q = f p → q = p)
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)))
    (p : M) (hp : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) :
    ∃ q : M, q ≠ p ∧ ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f q) ∧
      Nonempty (CrosscapConnectingArc f p q) := by
  obtain ⟨q,cp,cq,P,V,W,hqp,hq,hV,hpV,hW,hqW,hPs,hPf,hPr,hleft,hright⟩ :=
    prepared_smooth_crosscap_arc hf hfin hreg hsimple hrep p hp
  obtain ⟨R,e₀,e₁,hRs,hRf,hRP,h₀s,h₀i,h₀0,h₁s,h₁i,h₁0,hleft',hright'⟩ :=
    crosscap_axis_endpoint_germs cp cq P hPs hPf hV hpV hW hqW hleft hright
  refine ⟨q,hqp,hq,⟨⟨cp,cq,R,?_,?_,?_,e₀,e₁,h₀s,h₀i,h₁s,h₁i,?_,?_,?_,?_⟩⟩⟩
  · rw [hRs,hRP (left_mem_Icc.mpr P.start_lt_finish.le),hPs]
  · rw [hRf,hRP (right_mem_Icc.mpr P.start_lt_finish.le),hPf]
  · intro t ht
    rw [hRs,hRf] at ht
    rw [hRP ⟨ht.1.le,ht.2.le⟩]
    exact hPr t ht
  · rwa [hRs]
  · rwa [hRf]
  · rwa [hRs]
  · rwa [hRf]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SourceMapRepresentative
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original surface map in the constructed full-arc coordinates,
with an actual globally smooth representative near the entire rectangle. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem coordinate_representative_immersion_iff (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    {f : M → V} (hf : ContMDiff planeModel 𝓘(ℝ,V) ∞ f)
    {φ : Base → V} {U : Set Base} (hU : IsOpen U) (hUt : U ⊆ c.target)
    (hEq : EqOn φ (f ∘ c.symm) U) {x : Base} (hx : x ∈ U) :
    Function.Injective (fderiv ℝ φ x) ↔
      Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f (c.symm x)) := by
  have hcD : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨hci.mdifferentiableOn (by simp),hcs.mdifferentiableOn (by simp)⟩
  have hbij := hcD.mfderiv_bijective (hUt hx)
  rw [(hEq.eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq,← mfderiv_eq_fderiv,
    mfderiv_comp x (hf.mdifferentiable (by simp) _) (hcD.mdifferentiableAt (hUt hx))]
  change Function.Injective ((mfderiv planeModel 𝓘(ℝ,V) f (c.symm x)) ∘
    (mfderiv 𝓘(ℝ,Base) planeModel c.symm x)) ↔ _
  constructor
  · intro h v w hvw
    obtain ⟨v',rfl⟩ := hbij.2 v
    obtain ⟨w',rfl⟩ := hbij.2 w
    exact congrArg (mfderiv 𝓘(ℝ,Base) planeModel c.symm x) (h hvw)
  · intro h
    exact h.comp hbij.1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_LinearAlgebra_FiniteDimensional
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

open Module Submodule

variable {𝕜 : Type*} [Field 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E] {E' : Type*}
  [AddCommGroup E'] [Module 𝕜 E']

theorem one_lt_rank_of_rank_lt_rank [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] {π : E →ₗ[𝕜] 𝕜}
    (hπ : LinearMap.ker π ≠ ⊤) (h : finrank 𝕜 E < finrank 𝕜 E') (φ : E →ₗ[𝕜] E') :
    1 < Module.rank 𝕜 (E' ⧸ Submodule.map φ (LinearMap.ker π)) := by
  suffices 2 ≤ finrank 𝕜 (E' ⧸ (LinearMap.ker π).map φ) by
    rw [← finrank_eq_rank]
    exact_mod_cast this
  apply le_of_add_le_add_right
  rw [Submodule.finrank_quotient_add_finrank ((LinearMap.ker π).map φ)]
  have := calc finrank 𝕜 ((LinearMap.ker π).map φ)
      _ ≤ finrank 𝕜 (LinearMap.ker π) := finrank_map_le φ (LinearMap.ker π)
      _ < finrank 𝕜 E := Submodule.finrank_lt hπ
  linarith
end
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RelativeImmersionHPrinciple
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

lemma localizedImmersionRel_open {K : Set Plane} (hK : IsClosed K) :
    IsOpen (localizedImmersionRel K) :=
  (hK.isOpen_compl.preimage continuous_fst).union
    (ContinuousLinearMap.isOpen_injective.preimage continuous_snd.snd)

lemma localizedImmersionRel_ample (K : Set Plane) :
    (localizedImmersionRel K).IsAmple := by
  apply RelLoc.isAmple_iff.mpr
  intro q p hq
  by_cases hx : q.1 ∈ K
  · have hi : Function.Injective q.2.2 := hq.resolve_left (not_not.mpr hx)
    have hs : (localizedImmersionRel K).slice p q =
        ((p.π.ker).map q.2.2.toLinearMap : Set Vec)ᶜ := by
      ext w
      simp only [RelLoc.mem_slice,localizedImmersionRel,mem_ofPred_eq,hx,not_true_eq_false,
        false_or,Set.mem_compl_iff,p.injective_update_iff hi]
      rfl
    rw [hs]
    apply AmpleSet.of_one_lt_codim
    exact one_lt_rank_of_rank_lt_rank p.ker_pi_ne_top (by simp [Plane,Vec]) q.2.2.toLinearMap
  · apply RelLoc.ample_slice_of_forall
    intro w
    exact Or.inl hx

end ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

namespace ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

/-- The local h-principle realizes an injective formal differential while
preserving the prescribed exterior germs. -/
theorem realize_relative_frame {f : Plane → Vec} {A : Plane → Plane →L[ℝ] Vec}
    (hf : ContDiff ℝ ∞ f) (hA : ContDiff ℝ ∞ A)
    (L : Landscape Plane) (hcover : L.K₀ ∪ L.C = Set.univ)
    (hAI : ∀ x ∈ L.K₁, Function.Injective (A x))
    (hhol : ∀ᶠ x in 𝓝ˢ L.C, fderiv ℝ f x = A x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Plane → Vec, ContDiff ℝ ∞ g ∧
      tsupport (g-f) ⊆ L.K₁ ∧ (∀ x, ‖g x-f x‖ < ε) ∧
      (∀ x ∈ L.K₁, Function.Injective (fderiv ℝ g x)) ∧
      ∀ x ∈ L.C, g =ᶠ[𝓝 x] f := by
  let S : (localizedImmersionRel L.K₁).FormalSol :=
    { f := f, f_diff := hf, φ := A, φ_diff := hA,
      is_sol := fun x => by
        by_cases hx : x ∈ L.K₁
        · exact Or.inr (hAI x hx)
        · exact Or.inl hx }
  have hShol : ∀ᶠ x in 𝓝ˢ L.C, S.IsHolonomicAt x := hhol
  obtain ⟨H,_hzero,_hone,hC,hout,hclose,hend⟩ :=
    RelLoc.FormalSol.improve_htpy' (localizedImmersionRel_open L.hK₁.isClosed)
      (localizedImmersionRel_ample L.K₁) L hε S hShol
  let g := (H 1).f
  have hg : ContDiff ℝ ∞ g := (H 1).f_diff
  have houtside : ∀ x ∉ L.K₁, g x = f x := by
    intro x hx
    exact congrArg Prod.fst (hout x hx 1)
  have hCgerm : ∀ x ∈ L.C, g =ᶠ[𝓝 x] f := by
    intro x hx
    have he : ∀ᶠ y in 𝓝 x, ∀ t, H t y = S y :=
      hC.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [he] with y hy
    exact congrArg Prod.fst (hy 1)
  refine ⟨g,hg,?_,fun x => hclose x 1,?_,hCgerm⟩
  · apply closure_minimal _ L.hK₁.isClosed
    intro x hx
    by_contra hn
    exact hx (sub_eq_zero.mpr (houtside x hn))
  · intro x hx
    have hsol : Function.Injective ((H 1).φ x) :=
      (H.is_sol 1 x).resolve_left (not_not.mpr hx)
    by_cases hx0 : x ∈ L.K₀
    · have hh := hend.self_of_nhdsSet x hx0
      change fderiv ℝ g x = (H 1).φ x at hh
      rwa [hh]
    · have hxC : x ∈ L.C := by
        have hxU : x ∈ L.K₀ ∪ L.C := hcover.symm ▸ Set.mem_univ x
        exact hxU.resolve_left hx0
      rw [(hCgerm x hxC).fderiv_eq, hhol.self_of_nhdsSet x hxC]
      exact hAI x hx

end ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SupportedFormalImmersion
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact relative realization of a constructed smooth formal immersion.
This only removes singularities where an injective formal field is supplied. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

/-- A compact formal correction is integrated without changing exterior germs. -/
theorem supported_formal_immersion {f : Plane → Vec} {A : Plane → Plane →L[ℝ] Vec}
    (hf : ContDiff ℝ ∞ f) (hA : ContDiff ℝ ∞ A)
    {K₀ K₁ : Set Plane} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (h01 : K₀ ⊆ interior K₁)
    (hs : tsupport (A-fderiv ℝ f) ⊆ interior K₀)
    (hAI : ∀ x ∈ K₁, Function.Injective (A x)) :
    ∃ g : Plane → Vec, ContDiff ℝ ∞ g ∧ tsupport (g-f) ⊆ K₁ ∧
      (∀ x ∈ K₁, Function.Injective (fderiv ℝ g x)) ∧
      (∀ x ∉ interior K₀, g =ᶠ[𝓝 x] f) ∧
      ∀ x ∉ K₁, Function.Injective (fderiv ℝ g x) ↔
        Function.Injective (fderiv ℝ f x) := by
  let L : Landscape Plane :=
    { C := (interior K₀)ᶜ, K₀ := K₀, K₁ := K₁,
      hC := isOpen_interior.isClosed_compl, hK₀ := hK₀, hK₁ := hK₁, h₀₁ := h01 }
  have hcover : L.K₀ ∪ L.C = univ := by
    ext x
    simp only [L, mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hx : x ∈ K₀
    · exact Or.inl hx
    · exact Or.inr (fun h => hx (interior_subset h))
  have hhol : ∀ᶠ x in 𝓝ˢ L.C, fderiv ℝ f x = A x := by
    have hC : L.C ⊆ (tsupport (A-fderiv ℝ f))ᶜ := by
      intro x hx hxs
      exact hx (hs hxs)
    have hN : (tsupport (A-fderiv ℝ f))ᶜ ∈ 𝓝ˢ L.C :=
      (isClosed_tsupport _).isOpen_compl.mem_nhdsSet.mpr hC
    filter_upwards [hN] with x hx
    have hz : (A-fderiv ℝ f) x = 0 := image_eq_zero_of_notMem_tsupport hx
    exact (sub_eq_zero.mp hz).symm
  obtain ⟨g,hg,hsupp,_hclose,hgI,hgC⟩ :=
    realize_relative_frame hf hA L hcover hAI hhol (by norm_num : (0:ℝ)<1)
  refine ⟨g,hg,hsupp,hgI,hgC,?_⟩
  intro x hx
  have hxC : x ∉ interior K₀ := by
    intro hi
    exact hx (interior_subset (h01 (interior_subset hi)))
  rw [(hgC x hxC).fderiv_eq]

end ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SurfaceFormalImmersion
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative local convex integration transferred through an actual surface chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [T2Space M]

/-- A constructed injective field removes precisely the singularities in the
chosen compact coordinate region; every exterior germ is preserved. -/
theorem surface_formal_immersion (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    {f : M → ProjectionTarget 3} (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ)
    {O : Set Base} (hO : IsOpen O) (hOt : O ⊆ c.target)
    (hmatch : EqOn φ (f ∘ c.symm) O)
    {A : Base → Base →L[ℝ] ProjectionTarget 3} (hA : ContDiff ℝ ∞ A)
    {K₀ K₁ : Set Base} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (h01 : K₀ ⊆ interior K₁) (hK₁O : K₁ ⊆ O)
    (hs : tsupport (A-fderiv ℝ φ) ⊆ interior K₀)
    (hAI : ∀ x ∈ K₁, Function.Injective (A x)) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      (∀ x ∉ c.symm '' K₁, g =ᶠ[𝓝 x] f) ∧
      ∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
        x ∈ c.symm '' K₁ ∨
          Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) := by
  obtain ⟨F,hF,hsF,hFI,_hgC,_hreg⟩ :=
    HPrincipleBridge.supported_formal_immersion hφ hA hK₀ hK₁ h01 hs hAI
  let Q := F-φ
  have hQ : ContDiff ℝ ∞ Q := hF.sub hφ
  have hcQ : HasCompactSupport Q := hK₁.of_isClosed_subset (isClosed_tsupport Q) hsF
  have hsQ : tsupport Q ⊆ O := hsF.trans hK₁O
  let g := f+coordinatePushforward c Q
  have hg : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g :=
    hf.add (coordinatePushforward_smooth c hcs hQ hcQ (hsQ.trans hOt))
  have hout : ∀ x ∉ c.symm '' K₁, g =ᶠ[𝓝 x] f := by
    intro x hx
    have hn : x ∉ tsupport (coordinatePushforward c Q) := by
      intro hh
      obtain ⟨z,hz,he⟩ := coordinatePushforward_tsupport c hcQ (hsQ.trans hOt) hh
      exact hx ⟨z,hsF hz,he⟩
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
    change f y+coordinatePushforward c Q y = f y
    simp only [Pi.zero_apply] at hy
    rw [hy,add_zero]
  have hmatchG : EqOn F (g ∘ c.symm) O := by
    intro x hx
    have hxt := hOt hx
    change F x = f (c.symm x)+coordinatePushforward c Q (c.symm x)
    rw [coordinatePushforward_source c Q (c.map_target hxt),c.right_inv hxt]
    have he := hmatch hx
    change φ x = f (c.symm x) at he
    change F x = f (c.symm x)+(F x-φ x)
    rw [←he]
    abel
  refine ⟨g,hg,hout,?_⟩
  intro x
  by_cases hx : x ∈ c.symm '' K₁
  · obtain ⟨z,hz,rfl⟩ := hx
    have hI := (coordinate_representative_immersion_iff c hcs hci hg hO hOt hmatchG
      (hK₁O hz)).mp (hFI z hz)
    exact iff_of_true hI (Or.inl ⟨z,hz,rfl⟩)
  · rw [(hout x hx).mfderiv_eq]
    exact (or_iff_right hx).symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapGeometricCancellation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual supported cancellation of the two singularities on a crosscap
connecting arc, obtained from the constructed relative differential. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem cancel_crosscap_pair {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {p q : M} (A : CrosscapConnectingArc f p q) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      (∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
        x = p ∨ x = q ∨ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) ∧
      ∀ x, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) →
        x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f := by
  obtain ⟨S⟩ := exists_crosscap_coordinate_strip hf A
  obtain ⟨V,B,K,hV,hVD,hAV,hB,hK,hKV,hBs,hBI,hregV⟩ := S.formal_pair hf
  let Z := crosscapAxis '' Icc A.arc.start A.arc.finish
  have hZ : IsCompact Z := isCompact_Icc.image crosscapAxis.continuous
  have hZV : Z ⊆ V := by rintro x ⟨t,ht,rfl⟩; exact hAV t ht
  obtain ⟨U₀,hU₀,hKU₀,hK₀,hK₀V⟩ :=
    CollarVelocity.compact_open_thickening (hK.union hZ) hV (union_subset hKV hZV)
  obtain ⟨U₁,hU₁,hK₀U₁,hK₁,hK₁V⟩ := CollarVelocity.compact_open_thickening hK₀ hV hK₀V
  have hU₀i : U₀ ⊆ interior (closure U₀) := hU₀.subset_interior_iff.mpr subset_closure
  have hU₁i : U₁ ⊆ interior (closure U₁) := hU₁.subset_interior_iff.mpr subset_closure
  have h01 : closure U₀ ⊆ interior (closure U₁) := hK₀U₁.trans hU₁i
  have hsup : tsupport (B-fderiv ℝ S.model) ⊆ interior (closure U₀) :=
    hBs.trans ((subset_union_left.trans hKU₀).trans hU₀i)
  obtain ⟨g,hg,hout,hIg⟩ := surface_formal_immersion S.chart S.chart_smooth S.inverse_smooth hf
    S.model_smooth S.domain_open S.domain_target S.model_eq hB hK₀ hK₁ h01
    (hK₁V.trans hVD) hsup (fun x hx => hBI x (hK₁V hx))
  have hrec : ∀ t ∈ Icc A.arc.start A.arc.finish,
      S.chart.symm (crosscapAxis t) = A.arc.curve t := by
    intro t ht
    rw [crosscapAxis_apply,←(S.axis t ht).2,S.chart.left_inv (S.axis t ht).1]
  have hzK : Z ⊆ closure U₁ :=
    ((subset_union_right.trans hKU₀).trans subset_closure).trans (h01.trans interior_subset)
  have hpimage : p ∈ S.chart.symm '' closure U₁ := by
    refine ⟨crosscapAxis A.arc.start,hzK ⟨A.arc.start,left_mem_Icc.mpr A.arc.start_lt_finish.le,rfl⟩,?_⟩
    rw [hrec _ (left_mem_Icc.mpr A.arc.start_lt_finish.le),A.source]
  have hqimage : q ∈ S.chart.symm '' closure U₁ := by
    refine ⟨crosscapAxis A.arc.finish,hzK ⟨A.arc.finish,right_mem_Icc.mpr A.arc.start_lt_finish.le,rfl⟩,?_⟩
    rw [hrec _ (right_mem_Icc.mpr A.arc.start_lt_finish.le),A.target]
  have hbad : ∀ x ∈ S.chart.symm '' closure U₁,
      ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) → x = p ∨ x = q := by
    rintro x ⟨z,hz,rfl⟩ hx
    have hzV := hK₁V hz
    have hn : ¬ Function.Injective (fderiv ℝ S.model z) := by
      intro hi
      exact hx ((coordinate_representative_immersion_iff S.chart S.chart_smooth S.inverse_smooth hf
        S.domain_open S.domain_target S.model_eq (hVD hzV)).mp hi)
    have he : z = crosscapAxis A.arc.start ∨ z = crosscapAxis A.arc.finish := by
      have hh : ¬ (z ≠ crosscapAxis A.arc.start ∧ z ≠ crosscapAxis A.arc.finish) :=
        fun hh => hn ((hregV z hzV).mpr hh)
      simpa only [not_and_or,not_not] using hh
    rcases he with rfl | rfl
    · left
      rw [hrec _ (left_mem_Icc.mpr A.arc.start_lt_finish.le),A.source]
    · right
      rw [hrec _ (right_mem_Icc.mpr A.arc.start_lt_finish.le),A.target]
  refine ⟨g,hg,?_,?_⟩
  · intro x
    rw [hIg x]
    constructor
    · rintro (hx | hx)
      · by_cases hr : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)
        · exact Or.inr (Or.inr hr)
        · rcases hbad x hx hr with he | he
          · exact Or.inl he
          · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr hx)
    · rintro (rfl | rfl | hx)
      · exact Or.inl hpimage
      · exact Or.inl hqimage
      · exact Or.inr hx
  · intro x hx hxp hxq
    apply hout x
    intro hi
    exact (hbad x hi hx).elim hxp hxq

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FiniteCrosscapCancellation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reprepare the double points between genuine cancellations. The singular
set strictly decreases, while all remaining quadratic germs are retained. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem cancel_finite_quadratic_pair {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hrep : QuadraticCrosscapGerms f) (p : M)
    (hp : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)} ⊂
        {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)} ∧
      QuadraticCrosscapGerms g := by
  classical
  obtain ⟨F,hF,hI,hreg,hsimple,hrepF⟩ := clean_finite_quadratic_map hf hfin hrep
  have hfinF : {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F x)}.Finite :=
    hfin.subset (fun x hx => (hI x).not.mp hx)
  have hpF := (hI p).not.mpr hp
  obtain ⟨q,_hqp,_hqF,⟨A⟩⟩ := exists_crosscap_connecting_arc hF hfinF hreg hsimple hrepF p hpF
  obtain ⟨g,hg,hIg,hgerm⟩ := cancel_crosscap_pair hF A
  have hsub : {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)} ⊆
      {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)} := by
    intro x hx
    apply (hI x).not.mp
    intro hFx
    exact hx ((hIg x).mpr (Or.inr (Or.inr hFx)))
  have hpG : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g p) :=
    (hIg p).mpr (Or.inl rfl)
  refine ⟨g,hg,Set.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩,?_⟩
  · intro he
    have hpin : p ∈ {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)} := by
      rw [he]
      exact hp
    exact hpin hpG
  · intro x hx
    have hFx : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F x) := by
      intro hi
      exact hx ((hIg x).mpr (Or.inr (Or.inr hi)))
    have hxp : x ≠ p := fun he => hx ((hIg x).mpr (Or.inl he))
    have hxq : x ≠ q := fun he => hx ((hIg x).mpr (Or.inr (Or.inl he)))
    obtain ⟨c,φ,b,t,hxc,hφ,he,hz,hR⟩ := hrepF x hFx
    exact ⟨c,φ,b,t,hxc,hφ,(hgerm x hFx hxp hxq).trans he,hz,hR⟩

theorem remove_finite_quadratic_crosscaps {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hrep : QuadraticCrosscapGerms f) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      ∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) := by
  classical
  have h : ∀ n : ℕ, ∀ f : M → ProjectionTarget 3,
      ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f →
      {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite →
      QuadraticCrosscapGerms f →
      {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.ncard = n →
      ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
        ∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf hfin hrep hn
      by_cases he : {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)} = ∅
      · refine ⟨f,hf,?_⟩
        intro x
        by_contra hx
        have : x ∈ (∅ : Set M) := by
          rw [←he]
          exact hx
        exact this.elim
      · obtain ⟨p,hp⟩ := Set.nonempty_iff_ne_empty.mpr he
        obtain ⟨g,hg,hsub,hrepG⟩ := cancel_finite_quadratic_pair hf hfin hrep p hp
        have hfinG := hfin.subset hsub.subset
        have hlt := Set.ncard_lt_ncard hsub hfin
        rw [hn] at hlt
        exact ih _ hlt g hg hfinG hrepG rfl
  exact h _ f hf hfin hrep rfl

/-- Whitney's compact surface immersion, with smoothness retained. -/
theorem smooth_three_space_immersion :
    ∃ f : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f ∧
      ∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) := by
  obtain ⟨f,hf,hfin,hrep⟩ := exists_finite_quadratic_crosscap_map (M := M)
  exact remove_finite_quadratic_crosscaps hf hfin hrep

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_WhitneySurfaceImmersion
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_one _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_zero
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact surface specialization of Whitney (1944), Theorem 8,
discharged by finite generic crosscap preparation and supported cancellation. -/
noncomputable section
open Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem whitneySurfaceInput_oai : WhitneySurfaceInput M := by
  obtain ⟨f,hf,hI⟩ := FiniteOrderSmoothing.smooth_three_space_immersion (M := M)
  exact ⟨f,hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),hI⟩

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.PublishedInputs.whitneySurfaceInput_oai.{u_1} := @OAI.ClosedSurfaceR4.PublishedInputs.whitneySurfaceInput_oai.{u_1}
