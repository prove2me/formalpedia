-- Prove2me | solution 1 for GlobalTheory.Conv.exists_point_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:16.364881+00:00
-- url     : https://prove2.me/submissions/f3a0f605-efd8-48f4-bc3f-9a6066e0dde9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
import Theorems.Thm_GlobalTheory_Conv_coe_expandConv
import Theorems.Thm_GlobalTheory_Conv_coe_expandConvLaurent
import Theorems.Thm_GlobalTheory_Conv_evLoc_algebraMap
import Theorems.Thm_GlobalTheory_Conv_expandConv_u
import Theorems.Thm_GlobalTheory_HolHom_valR_spMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Conv.coe_expandConv
attribute [local simp] GlobalTheory.Conv.coe_expandConvLaurent
attribute [local simp] GlobalTheory.Conv.evLoc_algebraMap
attribute [local simp] GlobalTheory.Conv.expandConv_u



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
open GlobalTheory GlobalTheory.Conv
variable {A : Type} [CommRing A] {Z : Scheme.{0}}
namespace GlobalTheory.Conv
theorem _root_.solution {V : Z.Opens} (hV : IsAffineOpen V) (ψ : Γ(Z, V) →+* A) :
    ∃ x : Sp A ⟶ Z, ⊤ ≤ x ⁻¹ᵁ V ∧ ∀ f, valR x V f = ψ f := by
  let x₀ : Sp Γ(Z, V) ⟶ Z := hV.fromSpec
  have h₀ : ⊤ ≤ x₀ ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  refine ⟨spMap ψ ≫ x₀, fun p _ => h₀ (x := spMap ψ p) trivial, fun f => ?_⟩
  rw [valR_spMap ψ x₀ V h₀, valR_eq _ _ h₀]
  congr 1
  have h : hV.fromSpec.appLE V ⊤ h₀ = (Scheme.ΓSpecIso Γ(Z, V)).inv := by
    rw [Scheme.Hom.appLE, hV.fromSpec_app_self]
    simp [← Functor.map_comp]
  change (Scheme.ΓSpecIso Γ(Z, V)).hom.hom ((hV.fromSpec.appLE V ⊤ h₀).hom f) = f
  rw [h]
  exact (Scheme.ΓSpecIso Γ(Z, V)).inv_hom_id_apply f
end GlobalTheory.Conv
