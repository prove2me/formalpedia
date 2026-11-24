-- Prove2me | solution 1 for GlobalTheory.PRep.IsAdmissible.finiteDimensional_range_smoothOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:05:38.784337+00:00
-- url     : https://prove2.me/submissions/55752093-40d9-474c-b6e6-97bd830ab481

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_isOpen_leftStabilizer
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_mem_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
open GlobalTheory.PRep
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace G]
variable [IsTopologicalGroup G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
  {ρ : Representation ℂ G V} {f f' : G → ℂ}
namespace GlobalTheory.OpTrace
namespace _root_.GlobalTheory.PRep.IsAdmissible
theorem _root_.solution [μ.IsMulLeftInvariant] (hρ : IsAdmissible ρ)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) :
    FiniteDimensional ℂ (LinearMap.range (smoothOp ρ μ f)) := by
  have h1 := isOpen_leftStabilizer hf hc
  have := hρ.2 (K ⊓ leftStabilizer f) (ho.inter h1)
    (hK.inter_right (Subgroup.isClosed_of_isOpen _ h1))
  refine Submodule.finiteDimensional_of_le (S₂ := fixed ρ (K ⊓ leftStabilizer f)) ?_
  rintro _ ⟨v, rfl⟩
  exact hρ.1.smoothOp_mem_fixed hf hc
    (fun k hk => show k ∈ leftStabilizer f from (Subgroup.mem_inf.1 hk).2) v
end _root_.GlobalTheory.PRep.IsAdmissible
end GlobalTheory.OpTrace
