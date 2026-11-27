-- Prove2me | solution 1 for GlobalTheory.exists_finite_dvr_torusExtension_specialFibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:43.997944+00:00
-- url     : https://prove2.me/submissions/6cabb5cc-3914-4dad-af21-e0a81b79f57b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableCompleteSplit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteDvrTorusExtensionSpecialFibre
import Theorems.Thm_GlobalTheory_nonempty_torusExtension_of_comp_eq
import Theorems.Thm_GlobalTheory_FieldModel_exists_finite_torusExtension_range
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_nb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution : ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [IsAdicComplete (IsLocalRing.maximalIdeal V') V'] (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], IsSemiAbelian G → ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'') (_ : IsAdicComplete (IsLocalRing.maximalIdeal V'') V'') (_ : Algebra V' V''), Module.Finite V' V'' ∧ Function.Injective (algebraMap V' V'') ∧ IsLocalHom (algebraMap V' V'') ∧ IsSemiAbelian (baseChange V' V'' G) ∧ Nonempty (TorusExtension (specialFibre V'' (baseChange V' V'' G))) := by
  intro V' _ _ _ _ G _ hG
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue V'))).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := h₀.smooth
  haveI := h₀.quasiCompact
  haveI := h₀.separated
  let k := ResidueField V'
  let Ω := AlgebraicClosure k
  obtain ⟨T⟩ := h₀.fibres Ω (spMap (algebraMap k Ω))
  obtain ⟨s, hs, H⟩ := FieldModel.exists_finite_torusExtension_range (algebraMap k Ω) _ T
  haveI : Finite s := hs.to_subtype
  haveI : FiniteDimensional k (IntermediateField.adjoin k s) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨V'', i1, i2, i3, i4, i5, hf, hi, hl, e, he⟩ := nb V' (IntermediateField.adjoin k s)
  refine ⟨V'', i1, i2, i3, i4, i5, hf, hi, hl, IsSemiAbelian.pullback _ G hG, ?_⟩
  have hT := H _ (ResidueField.map (algebraMap V' V''))
    ((algebraMap (IntermediateField.adjoin k s) Ω).comp e.symm.toRingHom)
    (by
      rw [← he]
      ext x
      simp [k])
    (fun x hx => ⟨e ⟨x, IntermediateField.subset_adjoin _ _ hx⟩, by simp⟩)
  refine nonempty_torusExtension_of_comp_eq ?_ G hT
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ResidueField.map_comp_residue]
  rfl
end GlobalTheory
