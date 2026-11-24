-- Prove2me | solution 1 for GlobalTheory.CechDR.coneMap_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:00:40.155129+00:00
-- url     : https://prove2.me/submissions/930356da-3dd2-499b-bdd5-a4dbac76940d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Theorems.Thm_GlobalTheory_CechDR_coneMap_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_eq_zero_of_isInitial
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Fil1_eq_range
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_dOne
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_of_algHom
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_oneFormMap_comp_oneFormMap
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_oneFormMap_eq_self_of_id
import Theorems.Thm_GlobalTheory_CechDR_ofForm_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
open CatCoh
universe v u v' u' v'' u''
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
variable {R B} {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (e : ∀ T : C, B →ₐ[R] F.obj T) (he : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (b : B), mp F φ (e T b) = e T' b)
namespace GlobalTheory.CechDR
theorem _root_.solution {T₀ : C} (h : Limits.IsInitial T₀) (hb : Function.Bijective (e T₀)) :
    Function.Bijective (coneMap e he) := by
  let i := (AlgEquiv.ofBijective _ hb).symm.toAlgHom
  have hi : ∀ b, i (e T₀ b) = b := (AlgEquiv.ofBijective _ hb).symm_apply_apply
  have hi' : ∀ b, e T₀ (i b) = b := (AlgEquiv.ofBijective _ hb).apply_symm_apply
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨g, -, hg⟩ := ofForm_eq_zero.1 hc
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨i (g T₀), ?_⟩
    have := congrArg (SemiHom.of_algHom i).m1 (hg T₀)
    rw [SemiHom.m1_D, coneForm_apply] at this
    exact this.trans ((SemiHom.oneFormMap_comp_oneFormMap _ _ (SemiHom.of_algHom (AlgHom.id R B)) (fun b ↦ hi b) _).trans
      (SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) _))
  · intro c
    have hc : c ∈ Fil1 F := H1.eq_zero_of_isInitial F h _
    rw [Fil1_eq_range] at hc
    obtain ⟨ω, rfl⟩ := hc
    refine ⟨Submodule.Quotient.mk ⟨(SemiHom.of_algHom i).m1 (ω.1.1 T₀), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, ← SemiHom.mOm_dOne, ω.2 T₀, map_zero]
    · rw [coneMap_mk]
      refine congrArg _ (Subtype.ext (Subtype.ext (funext fun T ↦ ?_)))
      rw [coneForm_apply, ω.1.2 (h.to T)]
      exact SemiHom.oneFormMap_comp_oneFormMap _ _ (semiHom_mp F (h.to T))
        (fun b ↦ ((he (h.to T) (i b)).symm.trans (congrArg _ (hi' b)))) _
end GlobalTheory.CechDR
