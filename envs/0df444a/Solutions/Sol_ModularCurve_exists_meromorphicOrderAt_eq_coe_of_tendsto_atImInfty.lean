-- Prove2me | solution 1 for ModularCurve.exists_meromorphicOrderAt_eq_coe_of_tendsto_atImInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a4321306-7a2a-594c-b3ad-0ed45bf9decc

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_meromorphicOrderAt_eq_coe_of_tendsto_atImInfty

noncomputable section

open UpperHalfPlane Filter
open scoped MatrixGroups Topology

namespace ModularCurve
namespace OrderFiniteProof

def UHP : Set ℂ := {z : ℂ | 0 < z.im}

theorem convex_UHP : Convex ℝ UHP := convex_halfSpace_im_gt 0

theorem isPreconnected_UHP : IsPreconnected UHP := convex_UHP.isPreconnected

theorem coe_mem_UHP (τ : ℍ) : (τ : ℂ) ∈ UHP := τ.im_pos

theorem meromorphicOn_of_forall (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) :
    MeromorphicOn (fun z : ℂ => F (ofComplex z)) UHP := by
  intro z hz
  have := hF ⟨z, hz⟩
  simpa using this

theorem exists_forall_ne_zero_of_tendsto (F : ℍ → ℂ) {L : ℂ} (hL : L ≠ 0)
    (h : Tendsto F atImInfty (𝓝 L)) :
    ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → F τ ≠ 0 := by
  have hev : ∀ᶠ τ in atImInfty, F τ ≠ 0 := h.eventually_ne hL
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 hev
  exact ⟨A, fun τ hτ => hA τ hτ⟩

theorem exists_meromorphicOrderAt_ne_top (F : ℍ → ℂ)
    {L : ℂ} (hL : L ≠ 0) (h : Tendsto F atImInfty (𝓝 L)) :
    ∃ τ₀ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ₀ : ℂ) ≠ ⊤ := by
  obtain ⟨A, hA⟩ := exists_forall_ne_zero_of_tendsto F hL h

  set y : ℝ := max A 0 + 1 with hy
  have hypos : 0 < y := by rw [hy]; positivity
  have hyA : A < y := by rw [hy]; exact lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  let τ₀ : ℍ := ⟨Complex.I * y, by simpa using hypos⟩
  have him : (τ₀ : ℂ).im = y := by
    change (Complex.I * y).im = y
    simp
  refine ⟨τ₀, ?_⟩
  intro htop
  rw [meromorphicOrderAt_eq_top_iff] at htop

  have hnhds : ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), A < z.im ∧ 0 < z.im := by
    apply eventually_nhdsWithin_of_eventually_nhds
    have hc : ContinuousAt Complex.im (τ₀ : ℂ) := Complex.continuous_im.continuousAt
    have h1 : ∀ᶠ z in 𝓝 (τ₀ : ℂ), A < z.im :=
      hc.eventually (lt_mem_nhds (by rw [him]; exact hyA))
    have h2 : ∀ᶠ z in 𝓝 (τ₀ : ℂ), 0 < z.im :=
      hc.eventually (lt_mem_nhds (by rw [him]; exact hypos))
    exact h1.and h2
  obtain ⟨z, hz0, hzA, hzim⟩ := (htop.and hnhds).exists
  refine hA ⟨z, hzim⟩ ?_ ?_
  · change A ≤ z.im
    exact hzA.le
  · simpa [ofComplex_apply_of_im_pos hzim] using hz0

theorem meromorphicOrderAt_ne_top (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    {L : ℂ} (hL : L ≠ 0) (h : Tendsto F atImInfty (𝓝 L)) (τ : ℍ) :
    meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ ⊤ := by
  obtain ⟨τ₀, hτ₀⟩ := exists_meromorphicOrderAt_ne_top F hL h
  exact (meromorphicOn_of_forall F hF).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_UHP (coe_mem_UHP τ₀) (coe_mem_UHP τ) hτ₀

end ModularCurve.OrderFiniteProof

end

open UpperHalfPlane
open scoped MatrixGroups Topology

open ModularCurve.OrderFiniteProof in
theorem solution
    (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∀ τ : ℍ, ∃ n : ℤ,
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) := by
  intro τ
  obtain ⟨L, hL, hT⟩ := hcusp 1
  simp only [one_smul] at hT
  exact ⟨_, (WithTop.coe_untop _ (meromorphicOrderAt_ne_top F hF hL hT τ)).symm⟩

end S_ModularCurve_exists_meromorphicOrderAt_eq_coe_of_tendsto_atImInfty
end P2MW
export P2MW.S_ModularCurve_exists_meromorphicOrderAt_eq_coe_of_tendsto_atImInfty (solution)
