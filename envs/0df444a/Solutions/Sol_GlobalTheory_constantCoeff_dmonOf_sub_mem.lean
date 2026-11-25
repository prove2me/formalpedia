-- Prove2me | solution 1 for GlobalTheory.constantCoeff_dmonOf_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:45:14.703956+00:00
-- url     : https://prove2.me/submissions/fa6695f3-8f3f-4511-99a1-536b05c836f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Theorems.Thm_GlobalTheory_EigenCongruence_dmonOf_sub_mem

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι]
      (u : ι → Fin d → R) (y : ι → R) (f : PS R 1 d),
      (∀ l mo, coeff mo (Dof F (u l) f - C (y l) * f) ∈ I) →
      ∀ m : ι →₀ ℕ, constantCoeff (DmonOf F u m f) - (∏ l, y l ^ m l) * constantCoeff f ∈ I := by
  intro R _ d F I ι _ u y f hf m
  have h := EigenCongruence.dmonOf_sub_mem F u y f hf m 0
  rwa [coeff_zero_eq_constantCoeff, map_sub, map_mul, constantCoeff_C] at h
end GlobalTheory
