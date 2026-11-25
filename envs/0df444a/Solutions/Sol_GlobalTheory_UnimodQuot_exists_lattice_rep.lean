-- Prove2me | solution 1 for GlobalTheory.UnimodQuot.exists_lattice_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:36:56.545807+00:00
-- url     : https://prove2.me/submissions/b2271dcd-17b7-4a47-8a74-abaf07c0f7ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Theorems.Thm_GlobalTheory_UnimodQuot_exists_rep
import Theorems.Thm_GlobalTheory_UnimodQuot_star_mem_one
import Theorems.Thm_GlobalTheory_UnimodQuot_isLocalizedModule_subtype
import Theorems.Thm_GlobalTheory_UnimodQuot_exists_extension
import Theorems.Thm_GlobalTheory_HermLat_isLatMod_top_bot_iff
import Theorems.Thm_GlobalTheory_HermLat_mem_dual_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnimodQuot
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.UnimodQuot
theorem _root_.solution (H : HermSpace K V) {L : Submodule (𝓞 K) V} (hU : IsUnimod H L) (S : Submodule K V)
    (φ : ↥(L ⊓ rs (𝓞 K) S) →ₗ[𝓞 K] 𝓞 K) :
    ∃ y ∈ L, ∀ x : ↥(L ⊓ rs (𝓞 K) S), H.B x y = (φ x : K) := by
  have hL := (isLatMod_top_bot_iff L).1 hU.1
  obtain ⟨ψ, hψ⟩ := exists_extension hL S φ
  have := isLocalizedModule_subtype hL
  have hu : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) K) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (Algebra.linearMap (𝓞 K) K) x
  let f : V →ₗ[K] K := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K
      (IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) L.subtype (Algebra.linearMap (𝓞 K) K ∘ₗ ψ) hu)
  have hf : ∀ y : L, f y = algebraMap (𝓞 K) K (ψ y) := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 K)) L.subtype _ hu y
  obtain ⟨y, hy⟩ := exists_rep H f
  refine ⟨y, ?_, fun x => ?_⟩
  · rw [← hU.2, mem_dual_iff]
    refine ⟨by rw [hL.span_eq_top]; trivial, fun x hx => ?_⟩
    rw [← H.herm, hy]
    apply star_mem_one
    rw [hf ⟨x, hx⟩]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  · rw [hy, ← hψ]
    exact hf ⟨x, x.2.1⟩
end GlobalTheory.UnimodQuot
