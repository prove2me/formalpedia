-- Prove2me | solution 1 for GlobalTheory.CompRat.exists_complex_linear_of_pure_types
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:47.836121+00:00
-- url     : https://prove2.me/submissions/3d9246c0-cee1-43c0-b01c-660f2e7ea530

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsComplexLinearOfPureTypes
import Theorems.Thm_GlobalTheory_CompRat_exists_real_extension_of_lattice
import Theorems.Thm_GlobalTheory_PureType_period_rt_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CompRat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
namespace GlobalTheory.CompRat
namespace _root_.GlobalTheory.CompRat
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) (hP' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D' ty P') (Φ : D.La ≃ₗ[𝓞 E] D'.La), _root_.GlobalTheory.CompRat.IsSplit hP → (∀ a ∈ _root_.GlobalTheory.PureType.lat hP H.rt0, Φ a ∈ _root_.GlobalTheory.PureType.lat hP' H.rt0) → (∀ a ∈ _root_.GlobalTheory.PureType.lat hP (-H.rt0), Φ a ∈ _root_.GlobalTheory.PureType.lat hP' (-H.rt0)) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' (Φ a) = L (P a) := by
  intro E _ _ _ H D D' g ty P P' hP hP' Φ hsplit h₁ h₂
  have hP₀ := hP
  have hP'₀ := hP'
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod at hP₀ hP'₀
  obtain ⟨-, hi, hd, hs, -⟩ := hP₀
  obtain ⟨-, hi', hd', hs', -⟩ := hP'₀
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice P hi hd hs
    (P'.comp Φ.toLinearMap.toAddMonoidHom)
  obtain ⟨r', hr'⟩ := _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice P' hi' hd' hs'
    (P.comp Φ.symm.toLinearMap.toAddMonoidHom)
  have hr₁ : ∀ a, r (P a) = P' (Φ a) := hr
  have hr'₁ : ∀ b, r' (P' b) = P (Φ.symm b) := hr'
  have him : H.rt0.im ≠ 0 := by
    intro h0
    have hsq : (H.rt0 ^ 2).re = H.rt0.re ^ 2 := by simp [pow_two, Complex.mul_re, h0]
    rw [H.sqrt_neg_disc_sq] at hsq
    have h2 : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    simp at hsq
    nlinarith [sq_nonneg H.rt0.re]
  have hsplit' : _root_.GlobalTheory.PureType.lat hP H.rt0 ⊔ _root_.GlobalTheory.PureType.lat hP (-H.rt0) = ⊤ :=
    hsplit
  have hkey : ∀ a, r (H.rt0 • P a) = H.rt0 • r (P a) := by
    intro a
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hsplit' ▸ Submodule.mem_top : a ∈ _)
    have ry : r (H.rt0 • P y) = H.rt0 • r (P y) := by
      rw [← _root_.GlobalTheory.PureType.period_rt_smul hP hy, hr₁, hr₁, map_smul,
        _root_.GlobalTheory.PureType.period_rt_smul hP' (h₁ y hy)]
    have rz : r (-H.rt0 • P z) = -H.rt0 • r (P z) := by
      rw [← _root_.GlobalTheory.PureType.period_rt_smul hP hz, hr₁, hr₁, map_smul,
        _root_.GlobalTheory.PureType.period_rt_smul hP' (h₂ z hz)]
    have rz' : r (H.rt0 • P z) = H.rt0 • r (P z) := by
      rw [neg_smul, map_neg, neg_smul, neg_inj] at rz
      exact rz
    simp only [map_add, smul_add, ry, rz']
  have hrot : ∀ v, r (H.rt0 • v) = H.rt0 • r v := by
    have hext : r.comp (H.rt0 • LinearMap.id) = (H.rt0 • LinearMap.id).comp r :=
      LinearMap.ext_on_range hs fun a => by simpa using hkey a
    intro v
    simpa using LinearMap.congr_fun hext v
  have hlin : ∀ (c : ℂ) v, r (c • v) = c • r v := by
    intro c v
    have hc : c = ((c.re - c.im / H.rt0.im * H.rt0.re : ℝ) : ℂ) +
        ((c.im / H.rt0.im : ℝ) : ℂ) * H.rt0 := by
      apply Complex.ext <;> simp <;> field_simp <;> ring
    rw [hc, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_add, map_smul, map_smul,
      hrot, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  have hl : ∀ v, r' (r v) = v := by
    have hext : r'.comp r = LinearMap.id :=
      LinearMap.ext_on_range hs fun a => by simp [hr₁, hr'₁]
    exact fun v => LinearMap.congr_fun hext v
  have hrr : ∀ w, r (r' w) = w := by
    have hext : r.comp r' = LinearMap.id :=
      LinearMap.ext_on_range hs' fun b => by simp [hr₁, hr'₁]
    exact fun w => LinearMap.congr_fun hext w
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := r, map_add' := r.map_add, map_smul' := hlin }
  exact ⟨LinearEquiv.ofBijective L ⟨Function.LeftInverse.injective (g := r') hl,
    fun w => ⟨r' w, hrr w⟩⟩, fun a => (hr₁ a).symm⟩
end _root_.GlobalTheory.CompRat
end GlobalTheory.CompRat
