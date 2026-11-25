-- Prove2me | solution 1 for GlobalTheory.Mass.Hyperplane.exists_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:57.513193+00:00
-- url     : https://prove2.me/submissions/7ac4077a-cbc4-4778-befe-e83205d8bb62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StarMemLocR
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Hyperplane
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.Hyperplane
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : ∀ x y, star (h x y) = h y x) (v : V) (a : K)
    (ha : a + star a = a * star a * h v v) :
    ∃ g ∈ isom h, (∀ x, g x = x - (a * h v x) • v) ∧ ∀ x, g.symm x = x - (star a * h v x) • v := by
  let f : K → V →ₗ[K] V := fun c => LinearMap.id - (c • h v).smulRight v
  have hf : ∀ c x, f c x = x - (c * h v x) • v := fun c x => by simp [f]
  have key : ∀ c d : K, c + d = c * d * h v v → f c ∘ₗ f d = LinearMap.id := by
    intro c d hcd
    ext x
    rw [LinearMap.comp_apply, hf, hf, map_sub, map_smul, smul_eq_mul, sub_sub, ← add_smul]
    have : d * h v x + c * (h v x - d * h v x * h v v) = 0 := by linear_combination (h v x) * hcd
    rw [this, zero_smul, sub_zero, LinearMap.id_apply]
  refine ⟨LinearEquiv.ofLinear (f a) (f (star a)) (key _ _ ha) (key _ _ (by linear_combination ha)), ?_,
    fun x => hf _ x, fun x => hf _ x⟩
  intro x y
  change h (f a x) (f a y) = h x y
  rw [hf, hf]
  simp only [map_sub, map_smul, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_mul', hs]
  linear_combination (-(h x v * h v y)) * ha
end GlobalTheory.Mass.Hyperplane
