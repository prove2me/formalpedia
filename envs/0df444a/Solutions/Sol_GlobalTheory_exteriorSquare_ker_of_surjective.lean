-- Prove2me | solution 1 for GlobalTheory.exteriorSquare_ker_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:42:14.512054+00:00
-- url     : https://prove2.me/submissions/a6c24cab-4b71-440f-b862-7abff54c07ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorSquareKerOfSurjective
import Theorems.Thm_GlobalTheory_ExtSqKer_fin_two_vector_eq_matrixVecCons
import Theorems.Thm_GlobalTheory_ExtSqKer_congr_two
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
open GlobalTheory.ExtSqKer
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R] (W M H : Type)
    [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
    (i : W →ₗ[R] M) (p : M →ₗ[R] H) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (t : ⋀[R]^2 M) (ht : exteriorPower.map 2 p t = 0) :
    ∃ (n : ℕ) (a : Fin n → M) (w : Fin n → W),
      t = ∑ k, exteriorPower.ιMulti R 2 ![a k, i (w k)] := by
  set S : Set (⋀[R]^2 M) := {x | ∃ (a : M) (w : W), x = exteriorPower.ιMulti R 2 ![a, i w]}
  set N : Submodule R (⋀[R]^2 M) := Submodule.span R S
  let F : M [⋀^Fin 2]→ₗ[R] (⋀[R]^2 M ⧸ N) := N.mkQ.compAlternatingMap (exteriorPower.ιMulti R 2)
  have hF : ∀ (u : Fin 2 → M) (j : Fin 2), p (u j) = 0 → F u = 0 := by
    intro u j hj
    obtain ⟨w, hw⟩ := (hex (u j)).1 hj
    simp only [F, LinearMap.compAlternatingMap_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    fin_cases j
    · have e : u = ![u 1, i w] ∘ Equiv.swap 0 1 := by
        ext k; fin_cases k <;> simp [hw]
      rw [e, AlternatingMap.map_swap _ _ (by decide)]
      exact N.neg_mem (Submodule.subset_span ⟨u 1, w, rfl⟩)
    · rw [fin_two_vector_eq_matrixVecCons u]
      exact Submodule.subset_span ⟨u 0, w, by simp [hw]⟩
  let g := exteriorPower.alternatingMapLinearEquiv (descend p hp F hF)
  have hg : g ∘ₗ exteriorPower.map 2 p = N.mkQ := by
    apply exteriorPower.linearMap_ext
    ext m
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      exteriorPower.map_apply_ιMulti, g, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change F _ = F m
    exact congr_two p F hF _ _ (fun k => by simp [Function.surjInv_eq hp])
  have hN : t ∈ N := by
    have := congrArg (fun f => f t) hg
    simp only [LinearMap.coe_comp, Function.comp_apply, ht, map_zero, Submodule.mkQ_apply] at this
    exact (Submodule.Quotient.mk_eq_zero N).1 this.symm
  obtain ⟨n, c, x, hx⟩ := Submodule.mem_span_set'.1 hN
  choose a w haw using fun k => (x k).2
  refine ⟨n, fun k => c k • a k, w, ?_⟩
  rw [← hx]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [haw k]
  have e : ![c k • a k, i (w k)] = Function.update ![a k, i (w k)] 0 (c k • a k) := by
    ext l; fin_cases l <;> simp
  rw [e, AlternatingMap.map_update_smul]
  congr 2
  ext l; fin_cases l <;> simp
end GlobalTheory
