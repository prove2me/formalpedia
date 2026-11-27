-- Prove2me | solution 1 for GlobalTheory.chowla_selberg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:36:15.556623+00:00
-- url     : https://prove2.me/submissions/00169a6f-800f-4222-bcfd-3c423e891d0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_GlobalTheory_LFunction_one_eq_classNumber
import Theorems.Thm_GlobalTheory_chowla_selberg_eta
import Theorems.Thm_GlobalTheory_chowla_selberg_lattice
import Theorems.Thm_GlobalTheory_chowla_selberg_discriminant
import Theorems.Thm_GlobalTheory_dedekindZeta_eq_mul_LFunction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution [NeZero d] (h2 : finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
    {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) (σ : K →+* ℂ) :
    (∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) ∧
    χ.LFunction 1 = (π * classNumber K / √d : ℝ) ∧
    (∀ τ : ClassGroup (𝓞 K) → ℍ, (∀ c, IsIdealClassPoint σ c (τ c)) →
      (((∑ c, Real.log (4 * π * (τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4)) / classNumber K : ℝ) : ℂ)
        = (Real.eulerMascheroniConstant + Real.log (2 * π / √d) : ℝ)
          - deriv χ.LFunction 1 / χ.LFunction 1) ∧
    ∀ (𝔞 : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : ClassGroup (𝓞 K) → PeriodPair),
      (∀ c, ClassGroup.mk K (𝔞 c) = c) → (∀ c, ((L c).lattice : Set ℂ) = σ '' (𝔞 c).1) →
      (((∑ c, latticeLogPeriod (L c)) / classNumber K : ℝ) : ℂ)
        = (Real.eulerMascheroniConstant + Real.log (2 * π / √d) : ℝ)
          - deriv χ.LFunction 1 / χ.LFunction 1 ∧
      (((∑ c, Real.log ((absNorm (𝔞 c).1 : ℝ) ^ 6 * ‖(L c).g₂ ^ 3 - 27 * (L c).g₃ ^ 2‖))
          / classNumber K : ℝ) : ℂ)
        = (12 * Real.log (2 * π) - 6 * Real.log d + 6 * Real.eulerMascheroniConstant : ℝ)
          - 6 * (deriv χ.LFunction 1 / χ.LFunction 1) :=
  ⟨fun _ hs => dedekindZeta_eq_mul_LFunction h2 hD hχ hs,
    LFunction_one_eq_classNumber h2 hD hd hχ σ,
    fun _ hτ => chowla_selberg_eta h2 hD hd hχ σ hτ,
    fun _ _ h𝔞 hL => ⟨chowla_selberg_lattice h2 hD hd hχ σ h𝔞 hL,
      chowla_selberg_discriminant h2 hD hd hχ σ h𝔞 hL⟩⟩
end GlobalTheory
