-- Prove2me | solution 1 for GlobalTheory.Mem.PosDirichlet.exp_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:50:12.059074+00:00
-- url     : https://prove2.me/submissions/4e72bf0a-5665-4e91-8a3e-22bb097027a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_congr
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_const
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_mul
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_pow
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_tsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem
open GlobalTheory.Mem.PosDirichlet
namespace GlobalTheory.Mem.PosDirichlet
theorem _root_.solution {F : ℂ → ℂ} (hF : PosDirichlet F) :
    PosDirichlet (fun s => Complex.exp (F s) - 1) := by
  have h1 : ∀ z : ℂ, HasSum (fun j : ℕ => z ^ (j + 1) / ((j + 1).factorial : ℂ))
      (Complex.exp z - 1) := by
    intro z
    have := NormedSpace.expSeries_div_hasSum_exp z
    rw [← Complex.exp_eq_exp_ℂ, ← hasSum_nat_add_iff' 1] at this
    simpa using this
  refine (tsum (F := fun (j : ℕ) s => F s ^ (j + 1) / ((j + 1).factorial : ℂ)) (fun j => ?_)
    (fun s _ => (h1 _).summable)).congr fun s _ => (h1 _).tsum_eq
  refine ((hF.pow (j + 1)).mul (const (c := ((j + 1).factorial : ℝ)⁻¹) (by positivity))).congr
    fun s _ => ?_
  push_cast
  rw [div_eq_mul_inv]
end GlobalTheory.Mem.PosDirichlet
