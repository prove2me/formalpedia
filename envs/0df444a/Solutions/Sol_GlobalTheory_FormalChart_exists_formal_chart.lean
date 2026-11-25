-- Prove2me | solution 1 for GlobalTheory.FormalChart.exists_formal_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:54.078811+00:00
-- url     : https://prove2.me/submissions/c59d56b2-4d48-428e-956e-d7385ed99321

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LePreimageOfClosedPoint
import Theorems.Thm_GlobalTheory_FormalChart_exists_expansion
import Theorems.Thm_GlobalTheory_FormalChart_exists_factor
import Theorems.Thm_GlobalTheory_FormalChart_spMap_valH
import Theorems.Thm_GlobalTheory_FormalChart_valH_spMap
import Theorems.Thm_GlobalTheory_FormalChart_spMap_comp
import Theorems.Thm_GlobalTheory_FormalChart_fromSpec_comp
import Theorems.Thm_GlobalTheory_FormalChart_le_preimage_of_closedPoint
import Theorems.Thm_GlobalTheory_KeyKa_EtBaseChange_valT_eq
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.FormalChart
open GlobalTheory.KeyKa.EtBaseChange
namespace GlobalTheory.FormalChart
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Scheme.{0}) (h : X ⟶ Sp O) (g : ℕ) (z : Sp O ⟶ X), SmoothOfRelativeDimension g h → z ≫ h = 𝟙 _ → ∃ θ : Sp (MvPowerSeries (Fin g) O) ⟶ X, θ (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) = z (IsLocalRing.closedPoint O) ∧ θ ≫ h = spMap (algebraMap O (MvPowerSeries (Fin g) O)) ∧ (∃ (V : X.Opens) (t : Fin g → Γ(X, V)), ⊤ ≤ θ ⁻¹ᵁ V ∧ ∀ i, valT (T := (MvPowerSeries (Fin g) O)) θ V (t i) = MvPowerSeries.X i) ∧ (∀ (T : Type) [CommRing T] [IsLocalRing T] [Algebra O T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T] (w : Sp T ⟶ X), w ≫ h = spMap (algebraMap O T) → w (IsLocalRing.closedPoint T) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) → ∃ e : (MvPowerSeries (Fin g) O) →ₐ[O] T, (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal T) ∧ spMap e.toRingHom ≫ θ = w) := by
  intro O _ _ X h g z hG hz
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (z (IsLocalRing.closedPoint O))
  have hU' : U = ⊤ := by
    have h1 : (z ≫ h) (IsLocalRing.closedPoint O) ∈ U :=
      (Scheme.Hom.comp_apply z h (IsLocalRing.closedPoint O)).symm ▸ e hx
    have h2 := le_preimage_of_closedPoint (z ≫ h) h1
    rw [hz] at h2
    exact eq_top_iff.2 h2
  subst hU'
  let a : O →+* Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ h.appLE ⊤ V le_top).hom
  have ha : hV.fromSpec ≫ h = spMap (R' := Γ(X, V)) a := fromSpec_comp hV h
  have h2 : RingHom.IsStandardSmoothOfRelativeDimension g a :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv hs
  obtain ⟨π₀, hπ1, hπ⟩ := h2.exists_etale_mvPolynomial
  clear_value a
  letI : Algebra O Γ(X, V) := a.toAlgebra
  let π : MvPolynomial (Fin g) O →ₐ[O] Γ(X, V) := { π₀ with commutes' := fun r => RingHom.congr_fun hπ1 r }
  have hpt : ∀ (T : Type) [CommRing T] [Algebra O T] (w : Sp T ⟶ X), ⊤ ≤ w ⁻¹ᵁ V →
      w ≫ h = spMap (algebraMap O T) →
      ∃ ψ : Γ(X, V) →ₐ[O] T, spMap (R := Γ(X, V)) ψ.toRingHom ≫ hV.fromSpec = w := by
    intro T _ _ w hw hw'
    have e1 := spMap_valH hV w hw
    have e2 : spMap ((valH w V hw).comp a) = spMap (algebraMap O T) := by
      rw [spMap_comp, ← ha, ← Category.assoc, e1, hw']
    have e3 : (valH w V hw).comp a = algebraMap O T :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
    exact ⟨⟨valH w V hw, fun r => RingHom.congr_fun e3 r⟩, e1⟩
  obtain ⟨ε, rfl⟩ := hpt O z (le_preimage_of_closedPoint z hx) (hz.trans (Spec.map_id _).symm)
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_expansion π hπ ε
  have hcl : (spMap (R := Γ(X, V)) φ.toRingHom ≫ hV.fromSpec)
      (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) =
      (spMap (R := Γ(X, V)) ε.toRingHom ≫ hV.fromSpec) (IsLocalRing.closedPoint O) := by
    refine congrArg hV.fromSpec (PrimeSpectrum.ext (Ideal.ext fun b => ?_))
    show φ b ∈ IsLocalRing.maximalIdeal _ ↔ ε b ∈ IsLocalRing.maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff, hφ₁]
  refine ⟨spMap (R := Γ(X, V)) φ.toRingHom ≫ hV.fromSpec, hcl, ?_,
    ⟨V, fun j => π (MvPolynomial.X j) - algebraMap O _ (ε (π (MvPolynomial.X j))), le_preimage hV _,
      fun j => ?_⟩, ?_⟩
  · rw [Category.assoc, ha, ← spMap_comp]
    exact congrArg spMap φ.comp_algebraMap
  · rw [valT_eq _ _ (le_preimage hV _), valH_spMap]
    exact hφ₂ j
  · intro T _ _ _ _ w hw hw'
    rw [hcl] at hw'
    obtain ⟨ψ, rfl⟩ := hpt T w (le_preimage_of_closedPoint w (hw' ▸ hx)) hw
    have h3 := congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective hw')
    obtain ⟨v, hv, rfl⟩ := exists_factor π hπ ε φ hφ₁ hφ₂ (IsLocalRing.maximalIdeal T) ψ fun b => by
      have h4 : b - algebraMap O _ (ε b) ∈ (IsLocalRing.maximalIdeal O).comap ε.toRingHom := by
        show ε (b - algebraMap O _ (ε b)) ∈ IsLocalRing.maximalIdeal O
        simp
      have h5 : ψ (b - algebraMap O _ (ε b)) ∈ IsLocalRing.maximalIdeal T := h3.ge h4
      rwa [map_sub, AlgHom.commutes] at h5
    refine ⟨v, hv, ?_⟩
    rw [← Category.assoc, ← spMap_comp]
    rfl
end GlobalTheory.FormalChart
