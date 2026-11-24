-- Prove2me | solution 1 for GlobalTheory.OpenDim.ringKrullDim_affineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:04:50.993129+00:00
-- url     : https://prove2.me/submissions/ded3cfc9-3168-45f6-b753-a3b3a80323eb

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfIsIsoRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OpenDim
namespace GlobalTheory.OpenDim
theorem _root_.solution (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (f : Y ⟶ Sp F) [LocallyOfFiniteType f] {U : Y.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) :
    letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
    ∃ d : ℕ, ringKrullDim Γ(Y, U) = d ∧ Algebra.trdeg F Y.functionField = d := by
  let := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
  have : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  let φ := Spec.preimage (hU.fromSpec ≫ f)
  have hφ : Spec.map φ = hU.fromSpec ≫ f := Spec.map_preimage _
  let : Algebra F Γ(Y, U) := φ.hom.toAlgebra
  have hft : Algebra.FiniteType F Γ(Y, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  have hη : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hcomp : φ ≫ Y.presheaf.germ U _ hη =
      Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, Spec.map_preimage, ← hU.fromSpecStalk_eq_fromSpecStalk hη,
      IsAffineOpen.fromSpecStalk, Category.assoc]
  have : IsScalarTower F Γ(Y, U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ congr($(hcomp).hom a).symm
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have : Algebra.IsAlgebraic Γ(Y, U) Y.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have : FaithfulSMul F Γ(Y, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(Y, U)).injective
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  exact ⟨d, h₁, (trdeg_eq_of_isAlgebraic_top F Γ(Y, U) Y.functionField).trans h₂⟩
end GlobalTheory.OpenDim
