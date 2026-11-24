-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSSmLin.smLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:05:05.821805+00:00
-- url     : https://prove2.me/submissions/9332389d-318c-4651-9597-1aa8ca3fceba

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MulMemUJset
import Theorems.Thm_GlobalTheory_CompanionTheory_DSSmLin_mul_mem_UJset
import Theorems.Thm_GlobalTheory_CompanionTheory_DSSmLin_ex_mem_UJset
import Theorems.Thm_GlobalTheory_CompanionTheory_DSSmLin_inG_add
import Theorems.Thm_GlobalTheory_CompanionTheory_DSSmLin_inG_smul
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_differentiableAt
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix PI.UpqRep CompanionTheory.D.Upq.Sm
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSSmLin
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.CompanionTheory.DSSmLin
theorem _root_.solution : CompanionTheory.D.DSIC.SmLin := by
  intro n ε H _ _ σ hσ
  obtain ⟨⟨h1, hm⟩, -, -⟩ := hσ
  have h : RepOn (UJset ε) σ := ⟨by simp [UJset, inUJ], fun a ha b hb => mul_mem_UJset ε a b ha hb, h1, hm⟩
  refine ⟨(IsSm.zero : IsSm (UJset ε) σ 0), fun v hv w hw => ?_, fun c v hv => ?_, fun g hg v hv => ?_,
    fun X hX v hv => ?_, fun X Y hX hY v hv => ?_⟩
  · exact IsSm.add (G := UJset ε) hv hw
  · exact IsSm.smul (G := UJset ε) hv c
  · exact IsSm.apply h hv hg
  · have hv' : IsSm (UJset ε) σ v := hv
    refine ⟨hv'.dsW h (W := [X]) fun Y hY t => ?_, (hv'.differentiableAt h (ex_mem_UJset hX)).hasDerivAt⟩
    rw [List.mem_singleton.1 hY]
    exact ex_mem_UJset hX t
  · have hv' : IsSm (UJset ε) σ v := hv
    obtain ⟨U, F, hU, h1U, hF, hfF⟩ := hv' 1 h.one_mem
    have key : ∀ Z, inG ε Z → PI.PhMeasCore.dsig σ Z v = fderiv ℝ F 1 Z := fun Z hZ => by
      have hd : HasDerivAt (fun t => ex Z t) Z 0 := by simpa using hasDerivAt_mul_ex 1 Z
      exact (hasDerivAt_local (f := fun g => σ g v) (ex_mem_UJset hZ) (ex_zero Z) hd hU h1U hF hfF).deriv
    refine ⟨?_, fun s => ?_⟩
    · rw [key _ (inG_add hX hY), key _ hX, key _ hY, map_add]
    · rw [key _ (inG_smul hX s), key _ hX, Complex.coe_smul, Complex.coe_smul, map_smul]
end GlobalTheory.CompanionTheory.DSSmLin
