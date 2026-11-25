-- Prove2me | solution 1 for GlobalTheory.Ex.mulq_laws
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:02:04.006137+00:00
-- url     : https://prove2.me/submissions/0ca8da06-d053-423d-90eb-b87aedc35a32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws
import Theorems.Thm_GlobalTheory_Ex_NumB_dbl_pow
import Theorems.Thm_GlobalTheory_Ex_NumB_mulq_mul
import Theorems.Thm_GlobalTheory_Ex_NumB_mulq_mul_point
import Theorems.Thm_GlobalTheory_Ex_NumB_mulq_inv

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
open GlobalTheory GlobalTheory.Ex
namespace GlobalTheory.Ex
theorem _root_.solution : ∀ (O : Type) [CommRing O] (B : NumB O) (a b : ℕ) (x y : B.A), mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) ∧ mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y * (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) ∧ dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) = dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 ∧ mulq B.θ B.σ a x⁻¹ * B.σ x ^ (a ^ 2) = mulq B.θ B.σ a x * B.σ (x ^ a) :=
  fun _ _ B a b x y => ⟨B.mulq_mul a b x, B.mulq_mul_point a x y, B.dbl_pow a x, B.mulq_inv a x⟩
end GlobalTheory.Ex
