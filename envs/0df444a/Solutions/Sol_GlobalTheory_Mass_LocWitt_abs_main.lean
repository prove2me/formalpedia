-- Prove2me | solution 1 for GlobalTheory.Mass.LocWitt.abs_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:02:14.368784+00:00
-- url     : https://prove2.me/submissions/c368c400-14be-4cbd-b552-265b4e13e164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
import Theorems.Thm_GlobalTheory_Mass_LocWitt_Rel_trans
import Theorems.Thm_P2M_GlobalTheory_Mass_LocWitt_symm__0e7d45bf81cc
import Theorems.Thm_GlobalTheory_Mass_LocWitt_refl

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
    {M : AddSubgroup K}
    (hA : ∀ a ∈ A, star a ∈ A) (hΛ : ∀ a ∈ A, ∀ v ∈ Λ, a • v ∈ Λ) (hi : ∀ v ∈ Λ, ∀ w ∈ Λ, h v w ∈ A)
    (hM : ∀ a ∈ A, ∀ m ∈ M, a * m ∈ M) (h1 : (1 : K) ∉ M) (hinv : ∀ a ∈ A, a ∉ M → a⁻¹ ∈ A)
    {θ : K} (hθ : θ ∈ A) (hδ : θ - star θ ∉ M)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) (hn : h x x = h y y)
    (px : ∃ w ∈ Λ, h w x = 1) (py : ∃ w ∈ Λ, h w y = 1) : Rel h Λ x y := by
  have ne0 : ∀ {a : K}, a ∉ M → a ≠ 0 := fun ha e => ha (e ▸ M.zero_mem)
  have umul : ∀ {a b : K}, a ∈ A → a ∉ M → b ∉ M → a * b ∉ M := by
    intro a b ha ha' hb hab
    have := hM _ (hinv a ha ha') _ hab
    rw [← mul_assoc, inv_mul_cancel₀ (ne0 ha'), one_mul] at this
    exact hb this
  have uinv : ∀ {a : K}, a ∈ A → a ∉ M → a⁻¹ ∉ M := by
    intro a ha ha' hb
    have := hM _ ha _ hb
    rw [mul_inv_cancel₀ (ne0 ha')] at this
    exact h1 this
  have ustar : ∀ {a : K}, a ∈ A → a ∉ M → star a ∉ M := by
    intro a ha ha' hb
    have := hM _ (hA _ (hinv a ha ha')) _ hb
    rw [← star_mul', inv_mul_cancel₀ (ne0 ha'), star_one] at this
    exact h1 this
  have uadd : ∀ {a m : K}, a ∉ M → m ∈ M → a + m ∉ M := by
    intro a m ha hm e
    exact ha (by simpa using M.sub_mem e hm)
  have step : ∀ x ∈ Λ, ∀ y ∈ Λ, h x x = h y y → h x x - h y x ∉ M → Rel h Λ x y := by
    intro x hx y hy hn hc
    have hcA : h x x - h y x ∈ A := A.sub_mem (hi _ hx _ hx) (hi _ hy _ hx)
    obtain ⟨g, g1, g2, g3⟩ := refl hs hA hΛ hi (Λ.sub_mem hx hy) (ne0 hc) (hinv _ hcA hc) (by
      simp only [map_sub, LinearMap.sub_apply, star_sub, symm' hs]
      linear_combination hn)
    refine ⟨g, g1, g2, ?_⟩
    rw [g3, map_sub, LinearMap.sub_apply, inv_mul_cancel₀ (ne0 hc)]
    simp
  by_cases hc : h x x - h y x ∈ M
  swap
  · exact step x hx y hy hn hc
  have hsθ := hA _ hθ
  have hδA : θ - star θ ∈ A := A.sub_mem hθ hsθ
  by_cases hnM : h x x ∈ M
  · obtain ⟨w, hw, w1, w2⟩ : ∃ w ∈ Λ, h w x ∉ M ∧ h w y ∉ M := by
      obtain ⟨w, hw, e⟩ := px
      obtain ⟨w', hw', e'⟩ := py
      by_cases a : h w y ∈ M
      · by_cases b : h w' x ∈ M
        · refine ⟨w + w', Λ.add_mem hw hw', ?_, ?_⟩
          · rw [map_add, LinearMap.add_apply, e]; exact uadd h1 b
          · rw [map_add, LinearMap.add_apply, e', add_comm]; exact uadd h1 a
        · exact ⟨w', hw', b, e' ▸ h1⟩
      · exact ⟨w, hw, e ▸ h1, a⟩
    obtain ⟨c, cA, cM, ce⟩ : ∃ c ∈ A, c ∉ M ∧ c + star c = h w w := by
      have h0 := ne0 hδ
      have h0' : star θ - θ ≠ 0 := fun e => h0 (by linear_combination -e)
      have tA : θ * (θ - star θ)⁻¹ * h w w ∈ A :=
        A.mul_mem (A.mul_mem hθ (hinv _ hδA hδ)) (hi _ hw _ hw)
      have te : θ * (θ - star θ)⁻¹ * h w w + star (θ * (θ - star θ)⁻¹ * h w w) = h w w := by
        simp only [star_mul', star_inv₀, star_sub, star_star, symm' hs]
        field_simp
        ring
      by_cases a : θ * (θ - star θ)⁻¹ * h w w ∈ M
      · refine ⟨(θ - star θ) + θ * (θ - star θ)⁻¹ * h w w, A.add_mem hδA tA, uadd hδ a, ?_⟩
        rw [star_add, star_sub, star_star]
        linear_combination te
      · exact ⟨_, tA, a, te⟩
    obtain ⟨g, g1, g2, g3⟩ := refl hs hA hΛ hi hw (ne0 cM) (hinv _ cA cM) ce
    have hgx : h (g x) (g x) = h x x := g1 x x
    refine Rel.trans ⟨g, g1, g2, rfl⟩ (step _ ((g2 x).2 hx) y hy (hgx.trans hn) ?_)
    have : h (g x) (g x) - h y (g x) = (c⁻¹ * (h w x * star (h w y))) + (h x x - h y x) := by
      rw [hgx, g3, symm' hs]
      simp only [map_sub, map_smul, smul_eq_mul]
      ring
    rw [this]
    exact uadd (umul (hinv _ cA cM) (uinv cA cM) (umul (hi _ hw _ hx) w1 (ustar (hi _ hw _ hy) w2))) hc
  · have θM : θ ∉ M := fun a => by
      by_cases b : star θ ∈ M
      · exact hδ (M.sub_mem a b)
      · exact ustar hsθ b (by rwa [star_star])
    have sM := ustar hθ θM
    have t0 := ne0 θM
    have s0 := ne0 sM
    have hxx := hi _ hx _ hx
    have μA : star θ * θ⁻¹ ∈ A := A.mul_mem hsθ (hinv _ hθ θM)
    have hz := hΛ _ μA y hy
    have e1 : ∀ v, h ((star θ * θ⁻¹) • y) v = θ * (star θ)⁻¹ * h y v := fun v => by
      simp [LinearMap.map_smulₛₗ, starRingEnd_apply, star_mul', star_inv₀]
    have e2 : h ((star θ * θ⁻¹) • y) ((star θ * θ⁻¹) • y) = h y y := by
      rw [e1, map_smul, smul_eq_mul]; field_simp
    refine Rel.trans (step x hx _ hz (hn.trans e2.symm) ?_) (step _ hz y hy e2 ?_)
    · have : h x x - h ((star θ * θ⁻¹) • y) x =
          -((θ - star θ) * ((star θ)⁻¹ * h x x)) + θ * (star θ)⁻¹ * (h x x - h y x) := by
        rw [e1]; field_simp; ring
      rw [this]
      refine uadd ?_ (hM _ (A.mul_mem hθ (hinv _ hsθ sM)) _ hc)
      rw [neg_mem_iff]
      exact umul hδA hδ (umul (hinv _ hsθ sM) (uinv hsθ sM) hnM)
    · have : h ((star θ * θ⁻¹) • y) ((star θ * θ⁻¹) • y) - h y ((star θ * θ⁻¹) • y) =
          (θ - star θ) * (θ⁻¹ * h x x) := by
        rw [e2, map_smul, smul_eq_mul, hn]; field_simp
      rw [this]
      exact umul hδA hδ (umul (hinv _ hθ θM) (uinv hθ θM) hnM)
end GlobalTheory.Mass.LocWitt
