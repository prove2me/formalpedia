-- Prove2me | solution 1 for GlobalTheory.TopForm.isBaseChange_exteriorPower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:34:48.011933+00:00
-- url     : https://prove2.me/submissions/48154619-ca80-429e-8163-8d18866682ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Theorems.Thm_GlobalTheory_TopForm_extProj_coe
import Theorems.Thm_GlobalTheory_TopForm_exists_algHom_of_isBaseChange
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
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
namespace GlobalTheory.TopForm
theorem _root_.solution {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) (D : ℕ) :
    IsBaseChange B (exteriorPowerMapOver B D φ) := by
  obtain ⟨F, hF⟩ := exists_algHom_of_isBaseChange hφ
  let G : (⋀[B]^D N) →ₗ[B] B ⊗[A] (⋀[A]^D M) :=
    ((extProj A M D).baseChange B) ∘ₗ F.toLinearMap ∘ₗ (⋀[B]^D N).subtype
  let H : B ⊗[A] (⋀[A]^D M) →ₗ[B] ⋀[B]^D N := (exteriorPowerMapOver B D φ).liftBaseChange B
  have hG (x : ⋀[A]^D M) : G (exteriorPowerMapOver B D φ x) = 1 ⊗ₜ x := by
    have : (G.restrictScalars A) ∘ₗ (exteriorPowerMapOver B D φ) = TensorProduct.mk A B _ 1 := by
      apply exteriorPower.linearMap_ext
      ext1 v
      have e : F (ExteriorAlgebra.ιMulti B D fun k => φ (v k)) =
          1 ⊗ₜ ExteriorAlgebra.ιMulti A D v := by
        rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod,
          List.map_ofFn]
        have := map_list_prod (Algebra.TensorProduct.includeRight (R := A) (A := B)
          (B := ExteriorAlgebra A M)) (List.ofFn fun i => ExteriorAlgebra.ι A (v i))
        rw [Algebra.TensorProduct.includeRight_apply, List.map_ofFn] at this
        rw [this]
        congr 2
        funext k
        exact hF _
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        exteriorPowerMapOver_ιMulti, LinearMap.restrictScalars_apply, G, Submodule.subtype_apply,
        exteriorPower.ιMulti_apply_coe, AlgHom.toLinearMap_apply, e, LinearMap.baseChange_tmul,
        TensorProduct.mk_apply]
      rw [← exteriorPower.ιMulti_apply_coe, extProj_coe]
    exact LinearMap.congr_fun this x
  have h1 : G ∘ₗ H = LinearMap.id := by
    refine TensorProduct.AlgebraTensorModule.ext fun b x => ?_
    simp [H, hG, TensorProduct.smul_tmul']
  have h2 : Function.Surjective H := by
    rw [← LinearMap.range_eq_top, eq_top_iff,
      ← exteriorPower.ιMulti_span_of_span B D N (s := Set.range φ) (by
        rw [eq_top_iff]
        rintro n -
        induction n using hφ.inductionOn with
        | zero => simp
        | smul s n h => exact Submodule.smul_mem _ _ h
        | add a b ha hb => exact add_mem ha hb
        | tmul m => exact Submodule.subset_span ⟨m, rfl⟩), Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    choose v hv using fun k => hw (Set.mem_range_self k)
    refine ⟨1 ⊗ₜ exteriorPower.ιMulti A D v, ?_⟩
    simp [H, hv]
  have h3 : Function.Injective H :=
    Function.LeftInverse.injective (g := G) fun x => LinearMap.congr_fun h1 x
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective H ⟨h3, h2⟩) fun x => by
    change H _ = _
    simp [H]
end GlobalTheory.TopForm
