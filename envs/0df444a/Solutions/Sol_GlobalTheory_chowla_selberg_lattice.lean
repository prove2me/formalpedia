-- Prove2me | solution 1 for GlobalTheory.chowla_selberg_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:56.773793+00:00
-- url     : https://prove2.me/submissions/ce7d1027-6bbe-40f2-8940-1f6935b6b9c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_GlobalTheory_latticeLogPeriod_eq
import Theorems.Thm_GlobalTheory_chowla_selberg_eta

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
variable [NeZero d] (h2 : finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
  {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) (σ : K →+* ℂ)
include h2 hD hd hχ
variable {𝔞 : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ}
  (h𝔞 : ∀ c, ClassGroup.mk K (𝔞 c) = c) {L : ClassGroup (𝓞 K) → PeriodPair}
  (hL : ∀ c, ((L c).lattice : Set ℂ) = σ '' (𝔞 c).1)
include h𝔞 hL
namespace GlobalTheory
theorem _root_.solution :
    (((∑ c, latticeLogPeriod (L c)) / classNumber K : ℝ) : ℂ)
      = (Real.eulerMascheroniConstant + Real.log (2 * π / √d) : ℝ)
        - deriv χ.LFunction 1 / χ.LFunction 1 := by
  choose a τ ha h using fun c => exists_lattice_eq_mul_tau (L c)
  simp only [fun c => latticeLogPeriod_eq (ha c) (h c)]
  exact chowla_selberg_eta h2 hD hd hχ σ fun c =>
    ⟨𝔞 c, a c, h𝔞 c, fun z => by rw [← hL, SetLike.mem_coe, h]⟩
end GlobalTheory
