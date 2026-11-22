-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.integralFunctional_wellDefined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:39.895242+00:00
-- url     : https://prove2.me/submissions/c98afc7b-d6cf-4304-a690-ad72bc7699e2

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
public import Definitions.Def_LeanPool_NemytskiiLebesgue_IntegralFunctional
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_of_growth


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {a : Ω → ℝ} (ha : Integrable a μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCp : ∀ᵐ ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ p.toReal)
    {u : Ω → D} (hup : MemLp u p μ) :
    Integrable (fun ω : Ω => f ω (u ω)) μ := by
  rw [←memLp_one_iff_integrable]
  exact
    hf.memLp_nemytskii_of_growth
      h1p
      hp
      le_rfl
      ENNReal.one_ne_top
      (memLp_one_iff_integrable.← ha)
      hC
      ((div_one p).symm ▸ hfaCp)
      hup
end IsCaratheodory
end NemytskiiLebesgue
