-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.UnitaryConv.conv_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:03:11.640257+00:00
-- url     : https://prove2.me/submissions/0cd54c9f-132a-439c-ab3b-a6ad83601a97

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolic
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_cos_mk_eq_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_cos_eq_of_rep
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_rep_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis GlobalTheory.CompanionTheory.RgEis.UnitaryConv
open PositivityTheory.RgEis
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.RgEis.UnitaryConv
theorem _root_.solution {Γ P₁ P₂ : Subgroup G} {l₁ l₂ : G → ℝ}
    (h₁ : ∀ γ ∈ Γ, γ ∈ P₁ → ∀ g, l₁ (γ * g) = l₁ g) (h₂ : ∀ γ ∈ Γ, γ ∈ P₂ → ∀ g, l₂ (γ * g) = l₂ g)
    (c₁ : Conv Γ P₁ l₁) (c₂ : Conv Γ P₂ l₂) : Conv Γ (P₁ ⊓ P₂) fun g => l₁ g + l₂ g := by
  intro g
  have hinj : Function.Injective (fun q : Cos (P₁ ⊓ P₂) Γ =>
      ((Quotient.mk _ (Quotient.out q) : Cos P₁ Γ), (Quotient.mk _ (Quotient.out q) : Cos P₂ Γ))) := by
    intro q q' h
    have e1 := (cos_mk_eq_iff (P := P₁) (Γ := Γ) _ _).mp (congrArg Prod.fst h)
    have e2 := (cos_mk_eq_iff (P := P₂) (Γ := Γ) _ _).mp (congrArg Prod.snd h)
    exact cos_eq_of_rep (Subgroup.mem_inf.mpr ⟨e1, e2⟩)
  have hprod : Summable fun x : Cos P₁ Γ × Cos P₂ Γ =>
      Real.exp (l₁ (rep x.1 * g)) * Real.exp (l₂ (rep x.2 * g)) := by
    exact Summable.mul_of_nonneg (c₁ g) (c₂ g) (fun _ => (Real.exp_pos _).le)
      (fun _ => (Real.exp_pos _).le)
  refine (hprod.comp_injective hinj).congr fun q => ?_
  obtain ⟨p₁, hp₁Γ, hp₁P, hp₁⟩ := rep_mk (P := P₁) (Γ := Γ) (Quotient.out q)
  obtain ⟨p₂, hp₂Γ, hp₂P, hp₂⟩ := rep_mk (P := P₂) (Γ := Γ) (Quotient.out q)
  show Real.exp (l₁ (rep (Quotient.mk _ (Quotient.out q) : Cos P₁ Γ) * g)) *
      Real.exp (l₂ (rep (Quotient.mk _ (Quotient.out q) : Cos P₂ Γ) * g)) =
    Real.exp (l₁ (rep q * g) + l₂ (rep q * g))
  rw [hp₁, hp₂, mul_assoc, mul_assoc, h₁ p₁ hp₁Γ hp₁P, h₂ p₂ hp₂Γ hp₂P, Real.exp_add]
  rfl
end GlobalTheory.CompanionTheory.RgEis.UnitaryConv
