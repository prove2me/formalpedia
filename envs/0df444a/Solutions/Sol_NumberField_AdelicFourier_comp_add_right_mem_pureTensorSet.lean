-- Prove2me | solution 1 for NumberField.AdelicFourier.comp_add_right_mem_pureTensorSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7af3f192-0d65-52f1-937c-8a3469b92e87

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_comp_add_right_mem_pureTensorSet

open NumberField NumberField.AdelicFourier
open scoped SchwartzMap Classical

theorem solution
    {F : Type*} [Field F] [NumberField F] (y : AdeleRing (𝓞 F) F)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x => f (x + y)) ∈ pureTensorSet F := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hf
  set c := InfiniteAdeleRing.ringEquiv_mixedSpace F y.1
  have hTG : Function.HasTemperateGrowth (fun z : mixedEmbedding.mixedSpace F => z + c) :=
    Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const c)
  have hUp : ∃ (k : ℕ) (C : ℝ), ∀ z : mixedEmbedding.mixedSpace F,
      ‖z‖ ≤ C * (1 + ‖z + c‖) ^ k := by
    refine ⟨1, 1 + ‖c‖, fun z => ?_⟩
    have h1 : ‖z‖ ≤ ‖z + c‖ + ‖c‖ := by
      have := norm_add_le (z + c) (-c); simp only [add_neg_cancel_right, norm_neg] at this
      exact this
    nlinarith [norm_nonneg (z + c), norm_nonneg c]
  refine ⟨SchwartzMap.compCLM ℝ hTG hUp g, fun z => h (z + y.2),
    hlc.comp_continuous (continuous_add_right y.2),
    hcs.comp_homeomorph (Homeomorph.addRight y.2), ?_⟩
  funext x

  simp only [SchwartzMap.compCLM_apply, Function.comp_apply]
  congr 1
  rw [show (x + y).1 = x.1 + y.1 from rfl]
  exact congrArg g (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) x.1 y.1)

end S_NumberField_AdelicFourier_comp_add_right_mem_pureTensorSet
end P2MW
export P2MW.S_NumberField_AdelicFourier_comp_add_right_mem_pureTensorSet (solution)
