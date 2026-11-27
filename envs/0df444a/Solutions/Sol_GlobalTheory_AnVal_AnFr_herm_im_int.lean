-- Prove2me | solution 1 for GlobalTheory.AnVal.AnFr.herm_im_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:39:24.177276+00:00
-- url     : https://prove2.me/submissions/6c48f634-a2d6-4748-a989-5cc885af6151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppellHumbertFrameSemicharacter
import Theorems.Thm_P2M_GlobalTheory_AnVal_AnFr___add_7e58f427dd4e
import Theorems.Thm_P2M_GlobalTheory_AnVal_AnFr___ne_zero_214992ab8eb4
import Theorems.Thm_GlobalTheory_AnVal_AnFr_herm_im_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.AnVal
namespace AnFr
theorem _root_.solution {a b : Fin g → ℂ} (ha : a ∈ Φ.lat) (hb : b ∈ Φ.lat) :
    ∃ k : ℤ, (hermForm Φ.Hm a b).im = k := by
  have h1 := Φ.χ_add ha hb
  have h2 := Φ.χ_add hb ha
  rw [add_comm b a, h1, Φ.herm_im_swap a b, mul_comm (Φ.χ b)] at h2
  have h3 := mul_left_cancel₀ (mul_ne_zero (Φ.χ_ne_zero ha) (Φ.χ_ne_zero hb)) h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h3
  refine ⟨n, ?_⟩
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : (((hermForm Φ.Hm a b).im : ℝ) : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ hπ
    push_cast at hn
    linear_combination hn
  exact_mod_cast this
end AnFr
end GlobalTheory.AnVal
