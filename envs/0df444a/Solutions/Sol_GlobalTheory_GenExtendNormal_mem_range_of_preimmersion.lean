-- Prove2me | solution 1 for GlobalTheory.GenExtendNormal.mem_range_of_preimmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:14:45.987013+00:00
-- url     : https://prove2.me/submissions/95813919-3b9c-4f7b-9b0e-dec928d4b5b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Theorems.Thm_GlobalTheory_genericPoint_mem_opens
import Theorems.Thm_GlobalTheory_germToFunctionField_mem_range_stalk
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenExtendNormal
open GlobalTheory.DvrModel
namespace GlobalTheory.GenExtendNormal
theorem _root_.solution {H Y Z : Scheme.{0}} [IsIntegral H] (g : Y ⟶ H)
    [IsPreimmersion g] (k : Z ⟶ Y) (z : Z) (hz : g (k z) = genericPoint H) (y : Y)
    (A : H.Opens) [Nonempty A] (τ : Γ(H, A)) (O : Y.Opens) (hy : y ∈ O) (c : Γ(Y, O))
    (h : gs k z O c = gs (k ≫ g) z A τ) :
    H.germToFunctionField A τ ∈ (algebraMap (H.presheaf.stalk (g y)) H.functionField).range := by
  obtain ⟨u, hu⟩ := g.stalkMap_surjective y (Y.presheaf.germ O y hy c)
  obtain ⟨B, hB, σ, rfl⟩ := H.presheaf.germ_exist u
  rw [Scheme.Hom.germ_stalkMap_apply] at hu
  obtain ⟨O', hO', i₁, i₂, hO⟩ := Y.presheaf.germ_eq y _ _ _ _ hu
  have hsp : k z ⤳ y := by
    rw [← g.isEmbedding.isInducing.specializes_iff, hz]
    exact (genericPoint_spec H).specializes trivial
  have hkz : k z ∈ O' := hsp.mem_open O'.isOpen hO'
  have : Nonempty B := ⟨⟨_, hB⟩⟩
  have hA : (k ≫ g) z ∈ A := by
    rw [Scheme.Hom.comp_apply, hz]; exact genericPoint_mem_opens A
  have hB' : (k ≫ g) z ∈ B := by
    rw [Scheme.Hom.comp_apply, hz]; exact genericPoint_mem_opens B
  have h₁ : gs (k ≫ g) z B σ = gs (k ≫ g) z A τ := by
    rw [← h, ← gs_pull k g z B hB', ← gs_res k z i₁.le hkz, ← gs_res k z i₂.le hkz]
    exact congrArg _ hO
  rw [gs_eq _ _ _ hA, gs_eq _ _ _ hB', ← Scheme.Hom.germ_stalkMap_apply,
    ← Scheme.Hom.germ_stalkMap_apply] at h₁
  have key : ∀ (w : H) (hw : w = genericPoint H) {R : Type} [CommRing R] [Nontrivial R]
      (f : H.presheaf.stalk w →+* R) (hwA : w ∈ A) (hwB : w ∈ B),
      f (H.presheaf.germ B w hwB σ) = f (H.presheaf.germ A w hwA τ) →
      H.germToFunctionField B σ = H.germToFunctionField A τ := by
    rintro _ rfl R _ _ f _ _ hf
    exact RingHom.injective (R := H.functionField) f hf
  rw [← key _ hz ((k ≫ g).stalkMap z).hom hA hB' h₁]
  exact germToFunctionField_mem_range_stalk B σ hB
end GlobalTheory.GenExtendNormal
