-- Prove2me | solution 1 for GlobalTheory.exists_linear_increment
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:52.782803+00:00
-- url     : https://prove2.me/submissions/bcc3a898-9baa-48f1-bf40-c24badef4c9c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Theorems.Thm_GlobalTheory_exists_mem_four_of_open_dense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution {U : Set V} (ho : IsOpen U) (hd : Dense U) {f : V → ℂ} {c₀ : ℂ}
    (hf : ∀ a ∈ U, ∀ b ∈ U, -a - b ∈ U → c₀ + f a + f b + f (-a - b) = 0)
    {a₀ : V} (ha₀ : a₀ ∈ U) (hdf : DifferentiableAt ℂ f a₀) :
    ∃ L : V →L[ℂ] ℂ, ∀ a t, a ∈ U → a + t ∈ U → f (a + t) - f a = L t := by
  have h1 : ∀ t a b, a ∈ U → a + t ∈ U → b ∈ U → b + t ∈ U → -a - t - b ∈ U →
      f (a + t) - f a = f (b + t) - f b := by
    intro t a b ha hat hb hbt hab
    have e1 : -(a + t) - b = -a - t - b := by abel
    have e2 : -a - (b + t) = -a - t - b := by abel
    have h1 := hf _ hat _ hb (e1 ▸ hab)
    have h2 := hf _ ha _ hbt (e2 ▸ hab)
    rw [e1] at h1
    rw [e2] at h2
    linear_combination h1 - h2
  have h2 : ∀ t a b, a ∈ U → a + t ∈ U → b ∈ U → b + t ∈ U →
      f (a + t) - f a = f (b + t) - f b := by
    intro t a b ha hat hb hbt
    obtain ⟨d, hd1, hd2, hd3, hd4⟩ := exists_mem_four_of_open_dense ho hd (Homeomorph.refl V)
      (Homeomorph.addRight t) (Homeomorph.subLeft (-a - t)) (Homeomorph.subLeft (-b - t))
    rw [h1 t a d ha hat hd1 hd2 hd3, h1 t b d hb hbt hd1 hd2 hd4]
  have h3 : ∀ t : V, ∃ p, p ∈ U ∧ p + t ∈ U := by
    intro t
    obtain ⟨d, hd1, hd2, -⟩ := exists_mem_four_of_open_dense ho hd (Homeomorph.refl V)
      (Homeomorph.addRight t) (Homeomorph.refl V) (Homeomorph.refl V)
    exact ⟨d, hd1, hd2⟩
  choose p hp hpt using h3
  set l : V → ℂ := fun t => f (p t + t) - f (p t) with hl
  have hla : ∀ a t, a ∈ U → a + t ∈ U → f (a + t) - f a = l t := fun a t ha hat =>
    h2 t a (p t) ha hat (hp t) (hpt t)
  have hadd : ∀ s t, l (s + t) = l s + l t := by
    intro s t
    obtain ⟨d, hd1, hd2, hd3, -⟩ := exists_mem_four_of_open_dense ho hd (Homeomorph.refl V)
      (Homeomorph.addRight s) (Homeomorph.addRight (s + t)) (Homeomorph.refl V)
    have hd1' : d ∈ U := hd1
    have hd2' : d + s ∈ U := hd2
    have hd3' : d + (s + t) ∈ U := hd3
    rw [← hla d _ hd1' hd3', ← hla d _ hd1' hd2', ← hla (d + s) t hd2' (by rwa [add_assoc]),
      add_assoc]
    ring
  have hl0 : l 0 = 0 := by simp [hl]
  set L := fderiv ℂ f a₀
  have hL0 : HasFDerivAt l L 0 := by
    have hA : HasFDerivAt (fun t => f (a₀ + t) - f a₀) L 0 := by
      refine HasFDerivAt.sub_const _ ?_
      have : HasFDerivAt f L (a₀ + 0) := by simpa using hdf.hasFDerivAt
      exact (hasFDerivAt_comp_add_left a₀).2 this
    refine hA.congr_of_eventuallyEq ?_
    have : ∀ᶠ t in 𝓝 (0 : V), a₀ + t ∈ U :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (ho.mem_nhds (by simpa using ha₀))
    filter_upwards [this] with t ht
    exact (hla a₀ t ha₀ ht).symm
  have hL : ∀ x, HasFDerivAt l L x := by
    intro x
    have hA : HasFDerivAt (fun t => l x + l (-x + t)) L x := by
      refine HasFDerivAt.const_add _ ?_
      have : HasFDerivAt l L (-x + x) := by simpa using hL0
      exact (hasFDerivAt_comp_add_left (-x)).2 this
    have : (fun t => l x + l (-x + t)) = l := by
      funext t
      rw [← hadd]; congr 1; abel
    rwa [this] at hA
  refine ⟨L, fun a t ha hat => ?_⟩
  have hz : ∀ x, HasFDerivAt (fun t => l t - L t) (0 : V →L[ℂ] ℂ) x := fun x => by
    have := (hL x).sub (L.hasFDerivAt (x := x))
    rw [sub_self] at this
    exact this
  have := is_const_of_fderiv_eq_zero (𝕜 := ℂ) (f := fun t => l t - L t)
    (fun x => (hz x).differentiableAt) (fun x => (hz x).fderiv) t 0
  rw [hla a t ha hat]
  simp only [hl0, map_zero, sub_zero] at this
  exact sub_eq_zero.1 this
end GlobalTheory
