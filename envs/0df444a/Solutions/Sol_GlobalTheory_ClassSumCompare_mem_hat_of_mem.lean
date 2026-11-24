-- Prove2me | solution 1 for GlobalTheory.ClassSumCompare.mem_hat_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:29:32.625964+00:00
-- url     : https://prove2.me/submissions/1c9d7535-79a3-44a5-8894-d256ebd34293

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicNormWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulInt
import Theorems.Thm_GlobalTheory_AdLat_mul_mem_adelicCompletionOfElementSet_of_mul_mem
import Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_tmul_mem_adelicCompletion_of_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassSumCompare
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
open scoped TensorProduct nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.ClassSumCompare
theorem _root_.solution {x : AdE E} (hx : x ∈ intAd E) :
    (show GlobalTheory.AdLat.RA (maximalRealSubfield E) E from x) ∈
      GlobalTheory.AdLat.hat1 (maximalRealSubfield E) ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  have h1 : (1 : E) ∈ ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := FractionalIdeal.one_mem_one _
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, ha, rfl⟩ | ⟨o, rfl⟩
    · exact GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral _ ha h1
    · exact GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
  | zero => exact zero_mem _
  | one => exact GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet _ h1
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy =>
    refine GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem _ (fun a ha b hb => ?_) hx hy
    have := FractionalIdeal.mul_mem_mul ha hb
    rwa [mul_one] at this
end GlobalTheory.ClassSumCompare
