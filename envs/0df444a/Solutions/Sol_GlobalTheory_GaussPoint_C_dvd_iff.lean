-- Prove2me | solution 1 for GlobalTheory.GaussPoint.C_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:00:26.623527+00:00
-- url     : https://prove2.me/submissions/f0ee4681-892f-478a-835a-c6c5db296d1b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGaussPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj IsLocalRing
open GlobalTheory GlobalTheory.GaussPoint
namespace GlobalTheory.GaussPoint
theorem _root_.solution {V : Type*} [CommRing V] (a : V) (f : PowerSeries V) :
    PowerSeries.C a ∣ f ↔ ∀ n, a ∣ PowerSeries.coeff n f := by
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [PowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose c hc using h
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]
end GlobalTheory.GaussPoint
