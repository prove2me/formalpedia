-- Prove2me | solution 1 for GlobalTheory.exists_integral_basis_linear_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:37.956858+00:00
-- url     : https://prove2.me/submissions/7c74a0a3-27ff-43c2-bc29-71bbc21fdb86

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralBasisLinearCoordinates
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V K C : Type) [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field C] [Algebra K C] (R : Subring C), (∀ x : V, algebraMap K C (algebraMap V K x) ∈ R) → ∀ s : Finset C, (∀ x ∈ s, x ∈ R) → ∃ (r : ℕ) (c : Fin r → C) (φ : Fin r → (C →ₗ[K] K)), (∀ j, c j ∈ R) ∧ ∀ x ∈ s, (∀ j, φ j x ∈ (algebraMap V K).range) ∧ x = ∑ j, algebraMap K C (φ j x) * c j := by
  intro V K C _ _ _ _ _ _ _ _ R hR s hs
  classical
  letI : Algebra V C := ((algebraMap K C).comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap V C) :=
    (algebraMap K C).injective.comp (IsFractionRing.injective V K)
  haveI : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hinj
  let M : Submodule V C := Submodule.span V (s : Set C)
  haveI : Module.Finite V M := Module.Finite.span_of_finite V s.finite_toSet
  haveI : Module.Free V M := inferInstance
  have hMR : ∀ x ∈ M, x ∈ R := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hs x hx
    | zero => exact R.zero_mem
    | add x y _ _ hx hy => exact R.add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def]
      exact R.mul_mem (hR a) hx
  let b := Module.finBasis V M
  let c : Fin (Module.finrank V M) → C := fun j => (b j : C)
  have hcV : LinearIndependent V c :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hcK : LinearIndependent K c := (LinearIndependent.iff_fractionRing V K).1 hcV
  obtain ⟨g, hg⟩ := (Fintype.linearCombination K c).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (by
      exact hcK.fintypeLinearCombination_injective))
  refine ⟨_, c, fun j => (LinearMap.proj j).comp g, fun j => hMR _ (b j).2, ?_⟩
  intro x hx
  have hxM : x ∈ M := Submodule.subset_span hx
  have h1 : x = Fintype.linearCombination K c (fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j)) := by
    have := congrArg Subtype.val (b.sum_repr ⟨x, hxM⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at this
    rw [Fintype.linearCombination_apply]
    simp only [algebraMap_smul]
    exact this.symm
  have h2 : g x = fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j) := by
    have := LinearMap.congr_fun hg (fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j))
    rw [LinearMap.comp_apply, ← h1] at this
    exact this
  refine ⟨fun j => ⟨b.repr ⟨x, hxM⟩ j, ?_⟩, ?_⟩
  · simp [h2]
  · simp only [LinearMap.comp_apply, LinearMap.proj_apply, h2, ← Algebra.smul_def]
    rw [Fintype.linearCombination_apply] at h1
    exact h1
end GlobalTheory
