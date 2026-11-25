-- Prove2me | solution 1 for GlobalTheory.Mass.Hyperplane.exists_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:12:59.479329+00:00
-- url     : https://prove2.me/submissions/4ba0425f-18b0-4321-a757-8ad847603574

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StarMemLocR
import Theorems.Thm_GlobalTheory_UnimodQuot_isLocalizedModule_subtype


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Hyperplane
variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable [NumberField K]
omit [StarRing K]
namespace GlobalTheory.Mass.Hyperplane
theorem _root_.solution {M L : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) {P : Ideal (𝓞 K)}
    (φ : (↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P)) :
    ∃ (f : V →ₗ[K] K) (ψ : M →ₗ[𝓞 K] 𝓞 K), (∀ y : M, f y = algebraMap (𝓞 K) K (ψ y)) ∧
      ∀ y : M, ψ y ∈ P ↔ (y : V) ∈ L := by
  have hflat : Module.Flat (𝓞 K) M := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨a, ha⟩
    have h2 : (algebraMap (𝓞 K) K a) • (x : V) = 0 := by
      rw [algebraMap_smul]; exact congrArg Subtype.val ha
    have h3 : algebraMap (𝓞 K) K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    exact Subtype.ext ((smul_eq_zero.1 h2).resolve_left h3)
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property (Submodule.mkQ P)
    (φ.toLinearMap ∘ₗ (L.comap M.subtype).mkQ) (Submodule.mkQ_surjective P)
  have := GlobalTheory.UnimodQuot.isLocalizedModule_subtype hM
  have hu : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) K) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (Algebra.linearMap (𝓞 K) K) x
  refine ⟨LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K
      (IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) M.subtype (Algebra.linearMap (𝓞 K) K ∘ₗ ψ) hu), ψ,
    fun y => IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 K)) M.subtype _ hu y, fun y => ?_⟩
  have e : Submodule.mkQ P (ψ y) = φ ((L.comap M.subtype).mkQ y) := LinearMap.congr_fun hψ y
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, e, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  rfl
end GlobalTheory.Mass.Hyperplane
