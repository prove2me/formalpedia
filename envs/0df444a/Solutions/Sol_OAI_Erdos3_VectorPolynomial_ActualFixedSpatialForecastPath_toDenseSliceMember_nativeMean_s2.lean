-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.toDenseSliceMember_nativeMean_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:42:41.802626+00:00
-- url     : https://prove2.me/submissions/9986ee67-67f0-4c95-bb62-2fac9a29a9e9

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B252
import Definitions.Def_OAIE3v2B261
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFiberSliceLaw_sliced_source_complexMean_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem complexMean_congr_support {f g : X → ℂ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.complexMean f = p.complexMean g := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, Complex.ofReal_zero, zero_mul]
  · rw [h x hx]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActualFiberSlicedBoundedTwistPrecision
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "ActiveInput" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => degree (Subtype.val a))

variable {keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop} [DecidablePred keep]
variable {q : ℕ}
variable (slice : ResidueBoxSlice
  (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val) q)
variable (hlen : ∀ k, 0 < slice.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧
  fixed k < ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

variable (hactive : ∀ j : PrincipalTupleIndex
  (fun a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val), keep (Sum.inr ⟨j.1.val, j.2⟩))

include hlen hfixed hactive in
theorem allocatedFiberActiveContainedProgression_eq_common
    (v : ∀ j : ActiveInput,
      IntegerScalarCubeBox Empty (slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))) :
    allocatedActiveContainedProgression B U basis S
      (fun j : ActiveInput => ResidueBoxSlice.fiberParameterStride
        (keep := keep) (q := q) (Sum.inr ⟨j.1.val, j.2⟩))
      (fun j : ActiveInput => slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))
      (fun j : ActiveInput => slice.fiberParameterStart fixed (Sum.inr ⟨j.1.val, j.2⟩))
      (allocatedFiberActiveProgression_contained B U basis S slice hlen fixed hfixed) v =
    allocatedActiveContainedProgression B U basis S (fun _ => q)
      (fun j : ActiveInput => slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))
      (fun j : ActiveInput => slice.fiberParameterStart fixed (Sum.inr ⟨j.1.val, j.2⟩))
      (allocatedFiberActiveProgression_common_contained B U basis S slice hlen fixed hfixed hactive) v := by
  funext j a
  apply Subtype.ext
  simp only [allocatedActiveContainedProgression, ResidueBoxSlice.fiberParameterStride,
    if_pos (hactive j)]

theorem allocatedFiberPhysicalRoot_eq_raw
    (z : integerBox (Sum.elim (fun _ : G => S.value) sides)) :
    allocatedPhysicalCubeRoot B U basis S (fun _ => 0)
      (kernelZeroTupleFromSumIntegerBox B degree (fun _ : G => S.value) sides z)
      (principalZeroTupleFromSumIntegerBox B degree (fun _ : G => S.value) sides z) = z.val := by
  funext k
  cases k <;> simp only [allocatedPhysicalCubeRoot, Sum.elim_inl, Sum.elim_inr,
    kernelZeroTupleFromSumIntegerBox, principalZeroTupleFromSumIntegerBox, zero_add]

variable {X : Type*} [Fintype X]
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (base : X → ℤ) (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (box : X → ℕ) (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hkernelLength : ∀ g, 2 ≤ slice.length ⟨Sum.inl g, hkernel g⟩)
variable (hactiveLength : ∀ j : PrincipalTupleIndex
  (fun a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val),
  2 ≤ slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))

theorem allocatedFiberSliceLaw_native_complexMean :
    (slice.fiberSliceLaw hlen fixed hfixed).complexMean (fun z =>
      W.eval box nativePoly (fun a => base a + integerPhysicalSite z.val integerFrame a)) =
    allocatedSlicedNativeEvalMean B U basis S W base integerFrame box nativePoly
      (fun j => slice.fiberParameterLength (Sum.inr j))
      (fun j => ResidueBoxSlice.fiberParameterStride (keep := keep) (q := q) (Sum.inr j))
      (fun j => slice.fiberParameterStart fixed (Sum.inr j))
      (slice.fiberPrincipalParameter_inside hlen fixed hfixed)
      (fun j => slice.fiberParameterLength_pos hlen (Sum.inr j))
      (fun g => slice.length ⟨Sum.inl g, hkernel g⟩) hkernelLength
      (fun g => (slice.start ⟨Sum.inl g, hkernel g⟩ : ℤ)) q
      (slice.fiberKernelProgression_contained hkernel)
      (fun j : ActiveInput => slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))
      (fun j : ActiveInput => slice.fiberParameterStart fixed (Sum.inr ⟨j.1.val, j.2⟩))
      hactiveLength
      (allocatedFiberActiveProgression_common_contained B U basis S slice hlen fixed hfixed hactive) := by
  have he := allocatedFiberSliceLaw_sliced_source_complexMean_s2 B U basis S
    slice hlen fixed hfixed hkernel (fun x y => W.eval box nativePoly (fun a => base a +
      integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) integerFrame a))
  simp only [allocatedFiberPhysicalRoot_eq_raw] at he
  unfold allocatedSlicedNativeEvalMean
  refine he.trans ?_
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro u _
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro x _
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro v _
  have hy := allocatedFiberActiveContainedProgression_eq_common B U basis S
    slice hlen fixed hfixed hactive v
  exact congrArg (fun y => W.eval box nativePoly (fun a => base a + integerPhysicalSite
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0)
        (fun g => containedProgressionCubeMap Empty S.value
          (slice.length ⟨Sum.inl g, hkernel g⟩) q (slice.start ⟨Sum.inl g, hkernel g⟩)
          S.positive (slice.fiberKernelProgression_contained hkernel g) (x g)) y) integerFrame a))
    (congrArg (principalAxisJoin short u) hy)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ δslice δbase PpresBase : ℝ}
variable {s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice}
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ)
  physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))

omit [Fintype Tsp] in
theorem toDenseSliceMember_nativeMean_s2_oai :
    (path.toDenseSliceMember input).slice.nativeMean s W originalpoly =
      (input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN (path.physicalPolynomial originalpoly)
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) := by
  let member := path.toDenseSliceMember input
  have hactiveLength (j : PrincipalTupleIndex
      (fun a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)) :
      2 ≤ input.box.fiberParameterLength (Sum.inr ⟨j.1.val,j.2⟩) :=
    member.slice.activeLength_two s.hδslice j.1 j.2
  exact (allocatedFiberSliceLaw_native_complexMean B U b S input.box input.length_pos
    input.fixed input.fixed_inside input.kernel_kept (fun j => input.active_kept j.1 j.2)
    W path.base path.noise physicalN (path.physicalPolynomial originalpoly)
    (fun g => (input.kernel_geometry g).1) hactiveLength).symm

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.toDenseSliceMember_nativeMean_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.toDenseSliceMember_nativeMean_s2_oai
