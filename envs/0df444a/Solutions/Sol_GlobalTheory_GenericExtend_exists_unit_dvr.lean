-- Prove2me | solution 1 for GlobalTheory.GenericExtend.exists_unit_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:35.104552+00:00
-- url     : https://prove2.me/submissions/6f6d9eb1-8a85-4b33-b5a7-2ef0e4ee9bc0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
import Theorems.Thm_GlobalTheory_GenericExtend_gm_res_pullU
import Theorems.Thm_GlobalTheory_GenericExtend_Compat_res_pullU
import Theorems.Thm_GlobalTheory_DvrModel_existsUnique_isUnit_appLE_eq
import Theorems.Thm_GlobalTheory_isIntegral_of_geometricallyIntegral
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenericExtend
namespace GlobalTheory.GenericExtend
theorem _root_.solution {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] {X P Q H Z : Scheme.{0}}
    {f : H ⟶ Spec (.of V)} [Smooth f] [GeometricallyIntegral f] {k : Z ⟶ H} {fK : Z ⟶ Spec (.of K)}
    (hK : IsPullback k fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
    {N : LB P} (hN : N.IsLB) {J : Q ⟶ P} {φ : H ⟶ P} {ψ : Z ⟶ Q} (hψ : ψ ≫ J = k ≫ φ)
    (hW : ∀ A : P.Opens, k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ A)
    {e : X ⟶ P} {l : Spec (.of V) ⟶ X} {eV : Spec (.of V) ⟶ H} (heV : eV ≫ φ = l ≫ e)
    (heV' : eV ≫ f = 𝟙 _) {eK : Spec (.of K) ⟶ Z}
    (heK : eK ≫ k = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ eV)
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N J τ) {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : ∀ z a, e (l (Spec.map (CommRingCat.ofHom (algebraMap V K)) z)) ∈ N.U a →
      gm (eK ≫ ψ) z (J ⁻¹ᵁ N.U a) (τ a) =
        gm (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l) z (e ⁻¹ᵁ N.U a) (ρ a)) (a : N.ι) :
    ∃ s : Γ(H, φ ⁻¹ᵁ N.U a)ˣ, res le_rfl (pullU k _ s) = res (hW _) (pullU ψ _ (τ a)) := by
  have hs := IsPullback.of_hasPullback f
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  set n := Spec.map (CommRingCat.ofHom (algebraMap V K)) with hn
  obtain ⟨a₀, h₀⟩ := exists_chart hN (e (l (IsLocalRing.closedPoint V)))
  have hA : l ⁻¹ᵁ e ⁻¹ᵁ N.U a₀ ≤ eV ⁻¹ᵁ φ ⁻¹ᵁ N.U a₀ := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, heV]
  have hA' : n ⁻¹ᵁ l ⁻¹ᵁ e ⁻¹ᵁ N.U a₀ ≤ eK ⁻¹ᵁ k ⁻¹ᵁ φ ⁻¹ᵁ N.U a₀ := by
    rw [← Scheme.Hom.comp_preimage eK, heK]
    exact n.preimage_mono hA
  have hu : res le_rfl (pullU n _ (pullU l _ (ρ a₀))) =
      res hA' (pullU eK _ (res (hW _) (pullU ψ _ (τ a₀)))) := by
    refine unit_ext fun z hz ↦ ?_
    rw [gm_res_pullU (𝟙 _) n z le_rfl hz, gm_res_pullU (𝟙 _) eK z hA' hz, Category.id_comp,
      Category.id_comp, gm_pull n l z _ hz, gm_res_pullU eK ψ z (hW _) (hA' hz), hρ z a₀ hz]
  obtain ⟨s, ⟨hsu, -, hsr⟩, -⟩ := DvrModel.existsUnique_isUnit_appLE_eq hK hs
    (U := fun a ↦ φ ⁻¹ᵁ N.U a) (g := fun a b ↦ (pullU φ _ (N.g a b)).val)
    (W := fun a ↦ k ⁻¹ᵁ φ ⁻¹ᵁ N.U a) (fun _ ↦ rfl) (fun x ↦ exists_chart hN (φ x))
    (fun a b ↦ Units.isUnit _) (r := fun a ↦ (res (hW _) (pullU ψ _ (τ a))).val)
    (fun a b ↦ congrArg Units.val (hτ.res_pullU hψ hW a b))
    (fun a ↦ Units.isUnit _) heV' heK (a₀ := a₀) (A := l ⁻¹ᵁ e ⁻¹ᵁ N.U a₀) h₀ hA rfl hA'
    (pullU l _ (ρ a₀)).isUnit (congrArg Units.val hu)
  exact ⟨(hsu a).unit, Units.ext (hsr a)⟩
end GlobalTheory.GenericExtend
