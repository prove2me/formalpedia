-- Prove2me | solution 1 for GlobalTheory.exists_integral_dual_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:24:57.78839+00:00
-- url     : https://prove2.me/submissions/3c44bcdf-5509-4812-9a87-5b37afcd6aa0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ComapSingleSpanAlgebraMapNumberField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E M : Type) [Field E] [NumberField E] [Field M]
    [NumberField M] [Algebra E M] :
    ∃ (k : ℕ) (b : Fin k → 𝓞 M) (l : Fin k → M →ₗ[E] E),
      (∀ j (c : 𝓞 M), ∃ a : 𝓞 E, l j (c : M) = (a : E)) ∧
      ∀ y : M, y = ∑ j, (b j : M) * algebraMap E M (l j y) := by
  haveI : Module.Finite (𝓞 E) (𝓞 M) := inferInstance
  haveI : Module.Flat (𝓞 E) (𝓞 M) := inferInstance
  haveI : Module.FinitePresentation (𝓞 E) (𝓞 M) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) (𝓞 M) := Module.Flat.projective_of_finitePresentation
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' (𝓞 E) (𝓞 M)
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  haveI hL : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 M) (nonZeroDivisors (𝓞 E))) M :=
    IsIntegralClosure.isLocalization (𝓞 E) E M (𝓞 M)
  haveI hL' : IsLocalizedModule (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr hL
  have hu : ∀ x : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) x
  let l0 : Fin k → M →ₗ[𝓞 E] E := fun j =>
    IsLocalizedModule.lift (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap
      (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj j ∘ₗ σ) hu
  let l : Fin k → M →ₗ[E] E := fun j =>
    (l0 j).extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E
  have hl : ∀ j (c : 𝓞 M), l j (c : M) = ((σ c j : 𝓞 E) : E) := by
    intro j c
    exact IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap
      (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj j ∘ₗ σ) hu c
  refine ⟨k, fun j => π (Pi.single j 1), l, fun j c => ⟨_, hl j c⟩, ?_⟩
  have hc : ∀ c : 𝓞 M, (c : M) = ∑ j, ((π (Pi.single j 1) : 𝓞 M) : M) * algebraMap E M (l j c) := by
    intro c
    have h1 : c = ∑ j, σ c j • π (Pi.single j 1) := by
      have h2 : π (σ c) = c := LinearMap.congr_fun hσ c
      conv_lhs => rw [← h2, LinearMap.pi_apply_eq_sum_univ π (σ c)]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 2
      ext i
      simp [Pi.single_apply, eq_comm]
    have h3 := congrArg (algebraMap (𝓞 M) M) h1
    rw [map_sum] at h3
    refine h3.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [hl, Algebra.smul_def, map_mul, mul_comm, ← IsScalarTower.algebraMap_apply]
    rfl
  intro y
  obtain ⟨⟨c, a⟩, ha⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap y
  have ha' : ((a : 𝓞 E) : E) • y = (c : M) := by
    have : (a : 𝓞 E) • y = (c : M) := ha
    rw [← this]
    exact algebraMap_smul E (a : 𝓞 E) y
  have hne : ((a : 𝓞 E) : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero a.2
    exact_mod_cast this
  have h4 := hc c
  rw [← ha'] at h4
  apply smul_right_injective M hne
  dsimp only
  rw [h4, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]
  ring
end GlobalTheory
