-- Prove2me | solution 1 for GlobalTheory.PsiQuadratic.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:30.608613+00:00
-- url     : https://prove2.me/submissions/87e144b2-a30b-4be5-89e1-b868b4d82bfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinear
import Theorems.Thm_P2M_GlobalTheory_PsiQuadratic___self_27515abbac20
import Theorems.Thm_GlobalTheory_PsiQuadratic_s_nsmul
import Theorems.Thm_P2M_GlobalTheory_PsiQuadratic___nsmul_8ec651840e68
import Theorems.Thm_GlobalTheory_Ex_NumD_Gt_pow_s


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.PsiQuadratic
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.PsiQuadratic
theorem _root_.solution : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n : ℕ) (y : N.X),
    N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) ∧ N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) ∧
    ∀ (g : N.Gt), g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n ∧
      (g ^ n).s y * cubN N.θ n 1 g.b (N.c y) = g.s y ^ n :=
  fun _ _ N n y => ⟨τ_self N y, ψ_nsmul N n y, fun g => ⟨s_nsmul N g n y, g.pow_s n y⟩⟩
end GlobalTheory.PsiQuadratic
