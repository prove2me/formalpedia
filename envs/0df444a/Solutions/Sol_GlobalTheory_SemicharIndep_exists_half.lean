-- Prove2me | solution 1 for GlobalTheory.SemicharIndep.exists_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:59.147088+00:00
-- url     : https://prove2.me/submissions/3f0c0e65-298a-4d14-bfbc-20611fd31a92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Theorems.Thm_GlobalTheory_SemicharIndep_B_skew
import Theorems.Thm_GlobalTheory_SemicharIndep_B_add_left
import Theorems.Thm_GlobalTheory_SemicharIndep_EFf_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.SemicharIndep
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.SemicharIndep
theorem _root_.solution (X : DataX E r) (y : Fin r → E)
    (hy : ∀ u ∈ X.Λ, ∃ k : ℤ, B X.toData u y = 2 * k) :
    ∃ x ∈ X.Λ, ∀ u ∈ X.Λ, B X.toData u y = 2 * B X.toData u x := by
  choose! f hf using hy
  let φ : X.Λ →+ ℤ := AddMonoidHom.mk' (fun u => f u) (fun u v => by
    have h1 := hf _ (u + v).2
    have h2 := hf _ u.2
    have h3 := hf _ v.2
    rw [Submodule.coe_add, B_add_left, h2, h3] at h1
    have : ((f ((u : Fin r → E) + v) : ℤ) : ℚ) = f u + f v := by linarith
    exact_mod_cast this)
  obtain ⟨x, hx, h⟩ := X.EF_perf φ
  refine ⟨x, hx, fun u hu => ?_⟩
  have h1 := h ⟨u, hu⟩
  rw [EFf_eq, ← B_skew] at h1
  rw [hf u hu, ← h1]
  rfl
end GlobalTheory.SemicharIndep
