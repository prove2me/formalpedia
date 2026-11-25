-- Prove2me | solution 1 for GlobalTheory.GenericExtend.extAt_of_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:28:06.185867+00:00
-- url     : https://prove2.me/submissions/3357b6cd-5d63-4888-8694-2e6e64380bed

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
import Theorems.Thm_GlobalTheory_GenericExtend_extAt_apply
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


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
theorem _root_.solution {Q Y H Z : Scheme.{0}} [IsLocallyNoetherian Y] [GlobalTheory.IsNormalScheme Y]
    [IsReduced Q] (J : Q ⟶ Y) [IsPreimmersion J] (φ : H ⟶ Y) [IsPreimmersion φ] (k : Z ⟶ H)
    (ψ : Z ⟶ Q) (w : ψ ≫ J = k ≫ φ) (W : Y.Opens) (f : Γ(Q, J ⁻¹ᵁ W)) (s : Γ(H, φ ⁻¹ᵁ W))
    {O : Z.Opens} (h₁ : O ≤ k ⁻¹ᵁ φ ⁻¹ᵁ W) (h₂ : O ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ W)
    (hs : (k.appLE _ O h₁).hom s = (ψ.appLE _ O h₂).hom f) (z : Z) (hz : z ∈ O) (h : H)
    (hh : φ h ∈ W) (hg : ∀ y, y ⤳ φ h → φ (k z) ⤳ y) : ExtAt J W f (φ h) := by
  obtain ⟨V, hV, s₀, hhV, hs₀⟩ := extAt_apply φ W s h hh
  let C : irreducibleComponents Y := ⟨_, irreducibleComponent_mem_irreducibleComponents (φ h)⟩
  have hξ := (isIrreducible_irreducibleComponent (x := φ h)).isGenericPoint_genericPoint
    isClosed_irreducibleComponent
  have hw : J (ψ z) = φ (k z) := by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  let V' := V ⊓ IsNormalScheme.component C
  have hV' : φ h ∈ V' := ⟨hhV, mem_irreducibleComponent⟩
  refine ⟨V', inf_le_left.trans hV, resG Y inf_le_left s₀, hV', ?_⟩
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
  intro q hq
  exfalso
  have hqV := Q.basicOpen_le _ hq
  obtain ⟨A, hA, hAO⟩ := J.isEmbedding.isInducing.isOpen_iff.1 (Q.basicOpen
    ((J.appLE V' (J ⁻¹ᵁ V') le_rfl).hom (resG Y inf_le_left s₀) -
      resG Q (J.preimage_mono (inf_le_left.trans hV)) f)).isOpen
  have hq' : J q ∈ A := by rw [← SetLike.mem_coe, ← hAO] at hq; exact hq
  have hzA : J (ψ z) ∈ A := by
    rw [hw]
    exact (hg _ (hξ.specializes mem_irreducibleComponent)).mem_open hA
      ((hξ.mem_open_set_iff hA).2 ⟨J q, hqV.2, hq'⟩)
  have hzV : φ (k z) ∈ V' := (hg _ specializes_rfl).mem_open V'.isOpen hV'
  let O' : Z.Opens := O ⊓ ψ ⁻¹ᵁ J ⁻¹ᵁ V'
  have hO' : O' ≤ k ⁻¹ᵁ φ ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, ← w]
    exact fun x hx ↦ hx.2.1
  have hz' : z ∈ Z.basicOpen ((ψ.appLE _ O' inf_le_right).hom
      ((J.appLE V' (J ⁻¹ᵁ V') le_rfl).hom (resG Y inf_le_left s₀) -
      resG Q (J.preimage_mono (inf_le_left.trans hV)) f)) := by
    rw [Scheme.basicOpen_appLE]
    refine ⟨⟨hz, show J (ψ z) ∈ V' from hw ▸ hzV⟩, ?_⟩
    change ψ z ∈ (Q.basicOpen _ : Set Q)
    rw [← hAO]
    exact hzA
  have e₁ := congrArg (resG Z (inf_le_left : O' ≤ O)) hs
  rw [res_appLE_apply, res_appLE_apply] at e₁
  have e₂ := congrArg (k.appLE _ O' hO').hom hs₀
  rw [appLE_res_apply, e₁, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE] at e₂
  have e₃ : ∀ (g : Z ⟶ Y) (_ : g = k ≫ φ) (hg), (g.appLE V O' hg).hom s₀ =
      ((k ≫ φ).appLE V O' hO').hom s₀ := by
    rintro _ rfl _; rfl
  rw [map_sub, appLE_res_apply, appLE_res_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, e₃ _ w, e₂, sub_self, Scheme.basicOpen_zero] at hz'
  exact hz'
end GlobalTheory.GenericExtend
