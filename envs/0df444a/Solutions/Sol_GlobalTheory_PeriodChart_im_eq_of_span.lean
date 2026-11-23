-- Prove2me | solution 1 for GlobalTheory.PeriodChart.im_eq_of_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:51.029989+00:00
-- url     : https://prove2.me/submissions/c4811746-3703-4cb0-8122-c3e2e13973a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}
variable {M : Type} [AddCommGroup M]
namespace GlobalTheory.PeriodChart
theorem _root_.solution (P : M → (Fin g → ℂ)) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ) (S T S' T' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (h : ∀ a b, (F (S (P a)) (T (P b))).im = (F' (S' (P a)) (T' (P b))).im) (z w : Fin g → ℂ) :
    (F (S z) (T w)).im = (F' (S' z) (T' w)).im := by
  have hre : ∀ (r : ℝ) (v : Fin g → ℂ), r • v = (r : ℂ) • v := fun r v => (Complex.coe_smul r v).symm
  have hmem : ∀ v, v ∈ Submodule.span ℝ (Set.range P) := by
    intro v
    rw [hs]
    exact Submodule.mem_top

  have step : ∀ x b, (F (S x) (T (P b))).im = (F' (S' x) (T' (P b))).im := by
    intro x
    induction hmem x using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact fun b => h a b
    | zero => intro b; simp
    | add y y' _ _ hy hy' =>
      intro b
      simp only [map_add, LinearMap.add_apply, Complex.add_im, hy b, hy' b]
    | smul r y _ hy =>
      intro b
      simp only [map_smul]
      simp only [hre]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.im_ofReal_mul, hy b]

  induction hmem w using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact step z b
  | zero => simp
  | add y y' _ _ hy hy' =>
    simp only [map_add, Complex.add_im, hy, hy']
  | smul r y _ hy =>
    simp only [map_smul]
    simp only [hre]
    simp only [map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul, Complex.im_ofReal_mul, hy]
end GlobalTheory.PeriodChart
