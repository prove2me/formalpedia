-- Prove2me | solution 1 for GlobalTheory.PDivGroup.Test.swap_ne_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:08:33.483467+00:00
-- url     : https://prove2.me/submissions/a67facee-d245-43ea-950e-8438a93a9380

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
import Theorems.Thm_GlobalTheory_PDivGroup_Test_padicAction_const_injective
import Theorems.Thm_GlobalTheory_PDivGroup_Test_swap_mul_swap
import Theorems.Thm_GlobalTheory_PDivGroup_Test_incl_fst
import Theorems.Thm_GlobalTheory_PDivGroup_Test_incl_swap_fst
import Theorems.Thm_ReciprocityTheory_PGsh_IsPtDer_map_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.PDivGroup.Test
open PDiv
variable {p : ℕ} {O : Type} [CommRing O]
namespace GlobalTheory.PDivGroup.Test
theorem _root_.solution [Fact p.Prime] [Nontrivial O] (a : ℤ_[p]) :
    swapAction (const p O) Polynomial.X ≠ padicAction _ a := fun h => by
  have h0 : swap (const p O) = a • 𝟙 _ := by
    have : swapAction (const p O) Polynomial.X = swap (const p O) := Polynomial.aeval_X _
    rw [this] at h
    exact h.trans (Algebra.algebraMap_eq_smul_one a)
  have h1 := incl_swap_fst (const p O)
  rw [h0, Linear.smul_comp, Category.id_comp, Linear.comp_smul, incl_fst] at h1
  have ha : a = 0 := padicAction_const_injective (O := O)
    ((Algebra.algebraMap_eq_smul_one a).trans (h1.trans (map_zero _).symm))
  have h2 := swap_mul_swap (const p O)
  rw [h0, ha, zero_smul] at h2
  have h3 : 𝟙 (prod (const p O) (const p O)) = 0 := h2.symm.trans (mul_zero (M₀ := End _) _)
  have h4 : 𝟙 (const p O) = 0 := by
    rw [← incl_fst (const p O) (const p O), ← Category.id_comp (fst _ _), h3, Limits.zero_comp,
      Limits.comp_zero]
  exact one_ne_zero (padicAction_const_injective (p := p) (O := O)
    ((map_one _).trans (h4.trans (map_zero _).symm)))
end GlobalTheory.PDivGroup.Test
