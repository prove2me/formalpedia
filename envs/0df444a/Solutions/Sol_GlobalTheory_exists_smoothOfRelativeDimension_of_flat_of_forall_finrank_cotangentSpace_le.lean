-- Prove2me | solution 1 for GlobalTheory.exists_smoothOfRelativeDimension_of_flat_of_forall_finrank_cotangentSpace_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:30.027865+00:00
-- url     : https://prove2.me/submissions/31cb5627-01c5-4e52-8fa9-47b57279cec5

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Theorems.Thm_GlobalTheory_exists_smoothOfRelativeDimension_of_flat_of_finrank_cotangentSpace_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory Topology
variable (V K k : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [PerfectField (ResidueField V)] [Field K] [Algebra V K] [IsFractionRing V K]
  [Field k] [Algebra V k] (hk : Function.Surjective (algebraMap V k))
  {X X₀ X₁ : Scheme.{u}} {f : X ⟶ Spec (.of V)} [LocallyOfFiniteType f] [Flat f]
  {i₀ : X₀ ⟶ X} {p₀ : X₀ ⟶ Spec (.of k)} {i₁ : X₁ ⟶ X} {p₁ : X₁ ⟶ Spec (.of K)}
  (h₀ : IsPullback i₀ p₀ f (Spec.map (CommRingCat.ofHom (algebraMap V k))))
  (h₁ : IsPullback i₁ p₁ f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
include hk h₀ h₁
namespace GlobalTheory
theorem _root_.solution {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X₁, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z)
    (hx : ∀ x : X₀, IsClosed ({x} : Set X₀) → Module.finrank (ResidueField (X₀.presheaf.stalk x))
      (CotangentSpace (X₀.presheaf.stalk x)) ≤ d) :
    ∃ U : X.Opens, Set.range i₀ ⊆ U ∧ SmoothOfRelativeDimension d (U.ι ≫ f) := by
  have : LocallyOfFiniteType p₀ := MorphismProperty.of_isPullback h₀ ‹_›
  have : JacobsonSpace X₀ := LocallyOfFiniteType.jacobsonSpace p₀
  choose U hU hs using fun x : closedPoints X₀ ↦
    (exists_smoothOfRelativeDimension_of_flat_of_finrank_cotangentSpace_le V K k hk h₀ h₁ hd x.1
      x.2 (hx x.1 x.2)).1
  refine ⟨⨆ x, U x, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨x, hx₁, hx₂⟩ := nonempty_inter_closedPoints (Z := closure {z})
      ⟨z, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    exact ((specializes_iff_mem_closure.mpr hx₁).map i₀.continuous).mem_open (⨆ x, U x).isOpen
      (le_iSup U ⟨x, hx₂⟩ (hU ⟨x, hx₂⟩))
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
    refine IsZariskiLocalAtSource.of_openCover (Scheme.Opens.iSupOpenCover U) fun x ↦ ?_
    have : (Scheme.Opens.iSupOpenCover U).f x ≫ (⨆ x, U x).ι = (U x).ι := by
      simp [Scheme.Opens.iSupOpenCover]
    rw [← Category.assoc, this]
    exact hs x
end GlobalTheory
