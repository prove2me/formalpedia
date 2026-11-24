-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.uop_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:24:40.651924+00:00
-- url     : https://prove2.me/submissions/57843f96-d96c-432f-b58c-f11fdedb9d36

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_w_scale
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_ux_map
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpMain_uop_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_exists_GL_first_basis_eq
import Theorems.Thm_GlobalTheory_T_card_affine_hyperplane
import Theorems.Thm_GlobalTheory_T_card_two_affine_hyperplanes
import Theorems.Thm_GlobalTheory_T_hermitian_count_from_hyperplanes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpMain
variable {k : Type} [Field k] [Fintype k] {n : ℕ} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
  {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {red : Γ →* GL (Fin (n + 1)) k} {ρ : Γ →* Module.End ℂ V} {t : Module.End ℂ V}
  {v : Submodule k (Fin (n + 1) → k) → V}
namespace GlobalTheory.CompanionTheory.GapOpMain
theorem _root_.solution (hD : LatData k n B red ρ t v) {gam : (Fin (n + 1) → k) → Γ} (hc : IsCov red gam)
    {y : V} (hy : y ∈ stabV red ρ) :
    (Fintype.card k : ℝ) ^ ((n : ℝ) - 1) * (B y y).re ≤ (B (uop ρ t gam y) (uop ρ t gam y)).re := by
  have hq : (0 : ℝ) < Fintype.card k := by exact_mod_cast Fintype.card_pos
  have hpos : ∀ x : V, 0 ≤ (B x x).re := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hD.pos x hx).le
  have hw : ∀ a : Fin (n + 1) → k, a ≠ 0 → ∀ s : k, s ≠ 0 → ρ (gam (s • a)) (t y) = ρ (gam a) (t y) :=
    fun a ha s hs => w_scale hD hc hy ha hs
  have hc' : ∀ a : Fin (n + 1) → k, a ≠ 0 → (B (ρ (gam a) (t y)) (ρ (gam a) (t y))).re = (B y y).re := by
    intro a _
    rw [hD.unit, hD.isom]
  have hA : ∀ x : Fin (n + 1) → k, x ≠ 0 →
      (B (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), ρ (gam a) (t y))
        (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), ρ (gam a) (t y))).re =
      (B (uop ρ t gam y) (uop ρ t gam y)).re := by
    intro x hx
    obtain ⟨g, hg⟩ := exists_GL_first_basis_eq x hx
    obtain ⟨γ, rfl⟩ := hD.surj g
    have h1 : ux ρ t gam y x = ρ γ (uop ρ t gam y) := by
      rw [uop_apply, ux_map hD hc hy, hg]
    show (B (ux ρ t gam y x) (ux ρ t gam y x)).re = _
    rw [h1, hD.unit]
  have key := GlobalTheory.T.hermitian_count_from_hyperplanes k n V B (fun a => ρ (gam a) (t y)) (B y y).re (B (uop ρ t gam y) (uop ρ t gam y)).re
    hpos (GlobalTheory.T.card_affine_hyperplane k n) (GlobalTheory.T.card_two_affine_hyperplanes k n) hw hc' hA
  have hrpow : (Fintype.card k : ℝ) ^ ((n : ℝ) - 1) = (Fintype.card k : ℝ) ^ n / Fintype.card k := by
    rw [Real.rpow_sub hq, Real.rpow_one, Real.rpow_natCast]
  rw [hrpow, div_mul_eq_mul_div, div_le_iff₀ hq]
  linarith [key]
end GlobalTheory.CompanionTheory.GapOpMain
