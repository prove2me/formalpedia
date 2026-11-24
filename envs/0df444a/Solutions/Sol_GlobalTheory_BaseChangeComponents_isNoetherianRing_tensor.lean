-- Prove2me | solution 1 for GlobalTheory.BaseChangeComponents.isNoetherianRing_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:01:25.954457+00:00
-- url     : https://prove2.me/submissions/f7fa15cf-509e-47fe-ade8-66d1a0454dd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsNoetherianRingTensor
import Theorems.Thm_GlobalTheory_BaseChangeComponents_isLocalization_incl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.BaseChangeComponents
variable {K Ω : Type} (F : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
namespace GlobalTheory.BaseChangeComponents
theorem _root_.solution (R : Subalgebra K Ω) (hfg : R.FG)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) : IsNoetherianRing (F ⊗[K] Ω) :=
  by
    letI := (incl F R).toAlgebra
    haveI := isLocalization_incl F R hR
    haveI : Algebra.FiniteType K R := (Subalgebra.fg_iff_finiteType R).1 hfg
    haveI : IsNoetherianRing (F ⊗[K] R) := Algebra.FiniteType.isNoetherianRing F (F ⊗[K] R)
    exact IsLocalization.isNoetherianRing (denoms F R) (F ⊗[K] Ω) inferInstance
end GlobalTheory.BaseChangeComponents
