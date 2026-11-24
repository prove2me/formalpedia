-- Prove2me | solution 1 for GlobalTheory.existsUnique_lift_of_isOpenImmersion_of_isDominant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:12.548989+00:00
-- url     : https://prove2.me/submissions/76cb7a64-fd56-45c2-827b-20f0058b39f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway
import Theorems.Thm_GlobalTheory_existsUnique_lift_of_isIso_fromNormalization
import Theorems.Thm_GlobalTheory_isIso_fromNormalization_of_birational


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {U T Z Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (j : U ⟶ T) [IsOpenImmersion j]
    [IsDominant j] [IsNormalScheme T] [IsLocallyNoetherian T]
    (p : Z ⟶ Y) [IsIntegralHom p] (a : U ⟶ Z) (b : T ⟶ Y) (h : a ≫ p = j ≫ b) :
    ∃! c : T ⟶ Z, j ≫ c = a ∧ c ≫ p = b := by
  have hloc : ∀ t : T, ∃ W : T.Opens, t ∈ W ∧ IsIrreducible (W : Set T) := by
    intro t
    have ht : t ∈ (⨆ V : T.affineOpens, (V : T.Opens)) := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨V, htV⟩ := TopologicalSpace.Opens.mem_iSup.mp ht
    have : IsNoetherianRing Γ(T, V) := IsLocallyNoetherian.component_noetherian V
    have : NoetherianSpace (V : T.Opens) := noetherianSpace_of_isAffineOpen V.1 V.2
    set V' : T.Opens := V.1
    let x0 : V' := ⟨t, htV⟩
    have hGT : IsIrreducible {y : T | y ⤳ t} := by
      rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _
        (T.fromSpecStalk t).continuous.continuousOn
    have hG : IsIrreducible {v : V' | v ⤳ x0} := by
      refine ⟨⟨x0, specializes_rfl⟩, ?_⟩
      have heq : {v : V' | v ⤳ x0} = Subtype.val ⁻¹' {y : T | y ⤳ t} := by
        ext v; exact (Topology.IsInducing.subtypeVal.specializes_iff).symm
      rw [heq]
      exact hGT.2.preimage V'.2.isOpenEmbedding_subtypeVal
    have huniq : ∀ Z ∈ irreducibleComponents V', x0 ∈ Z → Z = closure {v | v ⤳ x0} := by
      intro Z hZ hx0
      obtain ⟨ζ, hζ⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
      have hsub : Z ⊆ closure {v | v ⤳ x0} := by
        rw [← (hζ : closure {ζ} = Z)]
        exact closure_mono (Set.singleton_subset_iff.mpr (hζ.specializes hx0))
      exact le_antisymm hsub (hZ.2 hG.closure hsub)
    have hS : irreducibleComponent x0 ∈ irreducibleComponents V' :=
      irreducibleComponent_mem_irreducibleComponents x0
    have hα := NoetherianSpace.finite_irreducibleComponents (α := V')
    let O := (⋃₀ (irreducibleComponents V' \ {irreducibleComponent x0}))ᶜ
    have hOo : IsOpen O := by
      show IsOpen (⋃₀ (irreducibleComponents V' \ {irreducibleComponent x0}))ᶜ
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hα.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
    have hOS : O ⊆ irreducibleComponent x0 :=
      subset_closure.trans (closure_sUnion_irreducibleComponents_sdiff_singleton hα _ hS).le
    have hx0O : x0 ∈ O := by
      intro hmem
      obtain ⟨Z, ⟨hZ, hZS⟩, hx0Z⟩ := hmem
      exact hZS ((huniq Z hZ hx0Z).trans (huniq _ hS mem_irreducibleComponent).symm)
    have hOirr : IsIrreducible O :=
      ⟨⟨x0, hx0O⟩, isIrreducible_irreducibleComponent.2.open_subset hOo hOS⟩
    exact ⟨⟨Subtype.val '' O, V'.2.isOpenMap_subtype_val O hOo⟩, ⟨x0, hx0O, rfl⟩,
      hOirr.image _ continuous_subtype_val.continuousOn⟩
  suffices IsIso j.fromNormalization from existsUnique_lift_of_isIso_fromNormalization j p a b h
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro t
  obtain ⟨W, htW, hW⟩ := hloc t
  refine ⟨W, htW, ?_⟩
  have : IrreducibleSpace W := Subtype.irreducibleSpace hW
  have : IsIntegral W.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨u, hu⟩ : ∃ u : U, j u ∈ W := j.denseRange.exists_mem_open W.2 ⟨t, htW⟩
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := W.ι) u ⟨j u, hu⟩ rfl
  have : Nonempty ↥(pullback j W.ι) := ⟨z⟩
  have : IsIntegral (pullback j W.ι) := isIntegral_of_isOpenImmersion (pullback.snd j W.ι)
  have : IsDominant (pullback.snd j W.ι) :=
    ⟨(pullback.snd j W.ι).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hY : ∀ w : W.toScheme, IsIntegrallyClosed (W.toScheme.presheaf.stalk w) :=
    fun w => inferInstance
  have := isIso_fromNormalization_of_birational (pullback.snd j W.ι) hY
  have e' : pullback.snd j.fromNormalization W.ι =
      inv (j.normalizationPullback W.ι) ≫ (pullback.snd j W.ι).fromNormalization :=
    (IsIso.eq_inv_comp _).mpr (Scheme.Hom.normalizationPullback_snd j W.ι)
  have : IsIso (pullback.snd j.fromNormalization W.ι) := by rw [e']; infer_instance
  show IsIso ((pullbackRestrictIsoRestrict _ _).inv ≫ pullback.snd _ _)
  infer_instance
end GlobalTheory
