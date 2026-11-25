-- Prove2me | solution 1 for GlobalTheory.SerreRegular.pd_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:45.070833+00:00
-- url     : https://prove2.me/submissions/61b7701d-dab0-4d38-92ee-1a44152209a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_baseChange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct
open GlobalTheory
open GlobalTheory.SerreRegular
namespace GlobalTheory.SerreRegular
theorem _root_.solution {A B : Type} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (Good : ModuleCat.{0} A → Prop)
    (hG : ∀ (M : ModuleCat.{0} A) (r : ℕ) (f : (Fin r → A) →ₗ[A] M), Function.Surjective f →
      Good M → Good (ModuleCat.of A (LinearMap.ker f)) ∧
        Function.Injective ((LinearMap.ker f).subtype.lTensor B)) (n : ℕ) :
    ∀ (M : ModuleCat.{0} A) [Module.Finite A M], Good M → HasProjectiveDimensionLE M n →
      HasProjectiveDimensionLE (ModuleCat.of B (B ⊗[A] M)) n := by
  induction n with
  | zero =>
    intro M _ _ h
    simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one] at h ⊢
    have : Module.Projective A M := (IsProjective.iff_projective M).mpr h
    exact (IsProjective.iff_projective _).mp inferInstance
  | succ n ih =>
    intro M _ hM h
    obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' A M
    obtain ⟨hK, hinj⟩ := hG M r f hf hM
    have hS : f.shortComplexKer.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have hP : Projective f.shortComplexKer.X₂ :=
      (IsProjective.iff_projective (Fin r → A)).mp inferInstance
    have hKn : HasProjectiveDimensionLE (ModuleCat.of A (LinearMap.ker f)) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n hP).1 h
    have h1 := ih (ModuleCat.of A (LinearMap.ker f)) hK hKn
    have hex : Function.Exact ((LinearMap.ker f).subtype.baseChange B) (f.baseChange B) :=
      lTensor_exact B (LinearMap.exact_subtype_ker_map f) hf
    have hS' : (ModuleCat.shortComplexOfCompEqZero _ _ hex.linearMap_comp_eq_zero).ShortExact :=
      ModuleCat.shortComplex_shortExact _ hex hinj (LinearMap.lTensor_surjective B hf)
    have hP' : Projective (ModuleCat.shortComplexOfCompEqZero _ _ hex.linearMap_comp_eq_zero).X₂ :=
      (IsProjective.iff_projective (B ⊗[A] (Fin r → A))).mp inferInstance
    exact (hS'.hasProjectiveDimensionLT_X₃_iff n hP').2 h1
end GlobalTheory.SerreRegular
