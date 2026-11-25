-- Prove2me | solution 1 for GlobalTheory.Mass.Witt.exists_isom_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:31:30.943459+00:00
-- url     : https://prove2.me/submissions/721e9d5f-70b8-4b6e-9a43-78484d762bd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.Witt
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
private lemma h_sub_smul_sub_smul_eq_of_hww (h : V →ₗ⋆[K] V →ₗ[K] K) (hsym : ∀ a b, star (h a b) = h b a)
    (w : V) (α : K) (hα : α ≠ 0) (hww : h w w = α + star α) (a b : V) :
    h (a - (α⁻¹ * h w a) • w) (b - (α⁻¹ * h w b) • w) = h a b := by
  have hα' : star α ≠ 0 := star_ne_zero.mpr hα
  simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
    starRingEnd_apply]
  rw [← hsym w a, hww, star_mul, star_inv₀]
  field_simp
  ring
end GlobalTheory.Mass.Witt
end

set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Witt
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.Witt
theorem _root_.solution [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x, h x x = 0 → x = 0) (x y : V) (hxy : h x x = h y y) :
    ∃ g ∈ isom h, g x = y ∧ ∀ v, h (x - y) v = 0 → g v = v := by
  have hsym : ∀ a b, star (h a b) = h b a := fun a b => by
    rw [← starRingEnd_apply]; exact hs.eq a b
  have hww : h (x - y) (x - y) = h (x - y) x + star (h (x - y) x) := by
    rw [hsym]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hxy]; ring
  by_cases hα : h (x - y) x = 0
  · have h0 : h (x - y) (x - y) = 0 := by rw [hww, hα, star_zero, add_zero]
    have hxy' : x = y := sub_eq_zero.mp (ha _ h0)
    exact ⟨1, (isom h).one_mem, by simp [hxy'], fun v _ => rfl⟩
  · let f : V →ₗ[K] V :=
      LinearMap.id - LinearMap.smulRight ((h (x - y) x)⁻¹ • h (x - y)) (x - y)
    have hf : ∀ v, f v = v - ((h (x - y) x)⁻¹ * h (x - y) v) • (x - y) := fun v => rfl
    have key : ∀ a b, h (f a) (f b) = h a b := fun a b => by
      rw [hf, hf]; exact h_sub_smul_sub_smul_eq_of_hww h hsym (x - y) _ hα hww a b
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro a ha0
      apply ha a
      rw [← key a a, ha0, map_zero]
    let g : V ≃ₗ[K] V := LinearEquiv.ofInjectiveEndo f hinj
    have hg : ∀ v, g v = f v := fun v => rfl
    refine ⟨g, fun a b => by rw [hg, hg, key], ?_, fun v hv => ?_⟩
    · rw [hg, hf, inv_mul_cancel₀ hα, one_smul, sub_sub_cancel]
    · rw [hg, hf, hv, mul_zero, zero_smul, sub_zero]
end GlobalTheory.Mass.Witt
