-- Prove2me | solution 1 for GlobalTheory.Mass.LocWitt.refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:05:38.539831+00:00
-- url     : https://prove2.me/submissions/60307b21-4c96-4dc3-8b84-b6d5142edef9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
import Theorems.Thm_P2M_GlobalTheory_Mass_LocWitt_symm__0e7d45bf81cc

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LocWitt
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.LocWitt
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {Λ : AddSubgroup V} {A : Subring K}
    (hA : ∀ a ∈ A, star a ∈ A) (hΛ : ∀ a ∈ A, ∀ v ∈ Λ, a • v ∈ Λ) (hi : ∀ v ∈ Λ, ∀ w ∈ Λ, h v w ∈ A)
    {u : V} (hu : u ∈ Λ) {c : K} (hc0 : c ≠ 0) (hc : c⁻¹ ∈ A) (e : c + star c = h u u) :
    ∃ g ∈ isom h, (∀ v, g v ∈ Λ ↔ v ∈ Λ) ∧ ∀ v, g v = v - (c⁻¹ * h u v) • u := by
  have hc1 : star c ≠ 0 := star_ne_zero.2 hc0
  let s : K → V →ₗ[K] V := fun b => LinearMap.id - (b • h u).smulRight u
  have hsv : ∀ b v, s b v = v - (b * h u v) • u := fun b v => by simp [s]
  have inv : ∀ b b' : K, b + b' = b * b' * h u u → ∀ v, s b (s b' v) = v := by
    intro b b' eb v
    rw [hsv, hsv, sub_sub, ← add_smul]
    have : b' * h u v + b * h u (v - (b' * h u v) • u) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul]
      linear_combination (h u v) * eb
    rw [this]; simp
  have e1 : c⁻¹ + (star c)⁻¹ = c⁻¹ * (star c)⁻¹ * h u u := by
    rw [← e]; field_simp; ring
  have e2 : (star c)⁻¹ + c⁻¹ = (star c)⁻¹ * c⁻¹ * h u u := by
    rw [← e]; field_simp
  have mem : ∀ b ∈ A, ∀ v ∈ Λ, s b v ∈ Λ := fun b hb v hv => by
    rw [hsv]
    exact Λ.sub_mem hv (hΛ _ (A.mul_mem hb (hi _ hu _ hv)) _ hu)
  have hc' : (star c)⁻¹ ∈ A := by rw [← star_inv₀]; exact hA _ hc
  let g : V ≃ₗ[K] V := LinearEquiv.ofLinear (s c⁻¹) (s (star c)⁻¹)
    (LinearMap.ext (inv _ _ e1)) (LinearMap.ext (inv _ _ e2))
  have hg : ∀ v, g v = s c⁻¹ v := fun v => rfl
  refine ⟨g, ?_, fun v => ⟨fun hv => ?_, fun hv => mem _ hc v hv⟩, fun v => by rw [hg, hsv]⟩
  · intro v w
    rw [hg, hg, hsv, hsv]
    simp only [map_sub, map_smul, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply, star_mul', star_inv₀, symm' hs, RingHom.id_apply]
    linear_combination (-(h v u) * (h u w)) * e1
  · have := mem _ hc' _ hv
    rwa [hg, inv _ _ e2] at this
end GlobalTheory.Mass.LocWitt
