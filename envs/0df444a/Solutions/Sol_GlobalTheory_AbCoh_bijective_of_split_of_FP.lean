-- Prove2me | solution 1 for GlobalTheory.AbCoh.bijective_of_split_of_FP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:58:17.456699+00:00
-- url     : https://prove2.me/submissions/f0c3a527-2067-46ee-aed2-69943a953eb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfSplitInjectiveFgProjectiveConstantRan
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (R : Type) [CommRing R] (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ), FP R M n → FP R N n → ∀ (f : M →ₗ[R] N) (r : N →ₗ[R] M), (∀ x, r (f x) = x) → Function.Bijective f := by
  intro R _ M N _ _ _ _ n hM hN f r hrf
  obtain ⟨hMf, hMp, hMr⟩ := hM
  obtain ⟨hNf, hNp, hNr⟩ := hN
  have hinj : Function.Injective f := fun a b h => by
    have := congrArg r h; rwa [hrf, hrf] at this
  let K := LinearMap.ker r
  let π : N →ₗ[R] K := LinearMap.codRestrict K (LinearMap.id - f ∘ₗ r) (fun x => by
    show r (x - f (r x)) = 0
    simp [hrf])
  have hπ : ∀ k : K, π (k : N) = k := fun k => by
    ext; simp [π, LinearMap.mem_ker.1 k.2]
  haveI : Module.Finite R K := Module.Finite.of_surjective π (fun k => ⟨k, hπ k⟩)
  haveI : Module.Projective R K := Module.Projective.of_split K.subtype π (by ext k; simp [hπ])
  let e : N ≃ₗ[R] M × K :=
    { toFun := fun x => (r x, π x)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp
      invFun := fun p => f p.1 + (p.2 : N)
      left_inv := fun x => by simp [π]
      right_inv := fun p => by
        obtain ⟨m, k⟩ := p
        have hk : r (k : N) = 0 := k.2
        ext
        · simp [hrf, hk]
        · simp [π, hrf, hk] }
  have hK : Module.rankAtStalk (R := R) K = 0 := by
    have h1 := Module.rankAtStalk_eq_of_equiv e
    rw [Module.rankAtStalk_prod] at h1
    funext p
    have h2 := congrFun h1 p
    simp only [Pi.add_apply, hMr p, hNr p] at h2
    simp only [Pi.zero_apply]; omega
  haveI : Subsingleton K := Module.rankAtStalk_eq_zero_iff_subsingleton.1 hK
  refine ⟨hinj, fun y => ⟨r y, ?_⟩⟩
  have : π y = 0 := Subsingleton.elim _ _
  have h3 := congrArg Subtype.val this
  simp [π, sub_eq_zero] at h3
  exact h3.symm
end GlobalTheory.AbCoh
