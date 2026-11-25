-- Prove2me | solution 1 for GlobalTheory.PerfectPairing.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:23:46.218658+00:00
-- url     : https://prove2.me/submissions/3dd02b1e-35af-4a24-bcb7-b8c14a071e01

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOneLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsReducedTorsionGeometricFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinRepExistsIsPullbackSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAlgHomLocalizationAugmentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CardAlgHomReducedTraceSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsUnitDetPairingOfBicharacterOfDvdTraceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubWeilPerfectOfGeneric
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_finRep_exists_isPullback_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.PerfectPairing
variable {O : Type} [CommRing O]
namespace GlobalTheory.PerfectPairing
theorem _root_.solution [IsLocalRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (n : ℕ)
    (hfin : IsFinite ((𝟙 A) ^ n : A ⟶ A).left) (hflat : Flat ((𝟙 A) ^ n : A ⟶ A).left) :
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra O H), Module.Free O H ∧ Module.Finite O H ∧
      ∃ y : specO O H ⟶ A, y ^ n = 1 ∧ ∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ A), z ^ n = 1 →
        ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z := by
  obtain ⟨H, φ, y, hφf, hφl, hpb⟩ := finRep_exists_isPullback_spec ((𝟙 A) ^ n : A ⟶ A).left
    (CommRingCat.of O) (eSec A)
  letI : Algebra O H := φ.hom.toAlgebra
  haveI : Module.Finite O H := hφf
  haveI : Module.Flat O H := hφl
  have hpow : ∀ {T : Over (Sp O)} (z : T ⟶ A),
      z.left ≫ ((𝟙 A) ^ n : A ⟶ A).left = (z ^ n).left := by
    intro T z
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have he : eSec A ≫ A.hom = 𝟙 _ := Over.w (η[A])
  have hy : y ≫ A.hom = (specO O H).hom := by
    rw [← Over.w ((𝟙 A) ^ n : A ⟶ A), ← Category.assoc, hpb.w, Category.assoc, he]
    exact Category.comp_id _
  let y' : specO O H ⟶ A := Over.homMk y hy
  refine ⟨H, inferInstance, inferInstance, Module.free_of_flat_of_isLocalRing, inferInstance, y', ?_, ?_⟩
  · apply Over.OverMorphism.ext
    rw [← hpow, GlobalTheory.UU.one_left]
    exact hpb.w
  · intro S _ _ z hz
    have hw : z.left ≫ ((𝟙 A) ^ n : A ⟶ A).left =
        Spec.map (CommRingCat.ofHom (algebraMap O S)) ≫ eSec A := by
      rw [hpow, hz, GlobalTheory.UU.one_left]
      rfl
    let l : Spec (CommRingCat.of S) ⟶ Spec H := hpb.lift _ _ hw
    have hl : Spec.map (Spec.preimage l) = l := Spec.map_preimage l
    have h1 : φ ≫ Spec.preimage l = CommRingCat.ofHom (algebraMap O S) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hl]
      exact hpb.lift_snd _ _ hw
    refine ⟨⟨(Spec.preimage l).hom, fun r => congrArg (fun f => f.hom r) h1⟩, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      change Spec.map (Spec.preimage l) ≫ y = z.left
      rw [hl]
      exact hpb.lift_fst _ _ hw
    · intro ψ hψ
      have h2 : Spec.map (CommRingCat.ofHom ψ.toRingHom : H ⟶ CommRingCat.of S) = l := by
        apply hpb.hom_ext
        · rw [hpb.lift_fst _ _ hw, ← hψ]
          rfl
        · rw [hpb.lift_snd _ _ hw, ← Spec.map_comp]
          congr 1
          ext r
          exact ψ.commutes r
      have h3 := Spec.map_injective (h2.trans hl.symm)
      ext a
      exact congrArg (fun f => f.hom a) h3
end GlobalTheory.PerfectPairing
