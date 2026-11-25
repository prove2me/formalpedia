-- Prove2me | solution 1 for GlobalTheory.EigenCongruence.dof_iterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:21:34.908472+00:00
-- url     : https://prove2.me/submissions/e200311e-6a75-4602-9ebf-b4652d0315da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Theorems.Thm_GlobalTheory_EigenCongruence_dof_step

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
open GlobalTheory GlobalTheory.EigenCongruence
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.EigenCongruence
theorem _root_.solution (F : Fin d → PS R 2 d) (v : Fin d → R) (y c : R) {I : Ideal R}
    {f g : PS R 1 d} (hf : Dof F v f - C y * f ∈ coeffIdeal I) (hg : g - C c * f ∈ coeffIdeal I)
    (n : ℕ) : (Dof F v)^[n] g - C (y ^ n * c) * f ∈ coeffIdeal I := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
    exact dof_step F v y _ hf ih
end GlobalTheory.EigenCongruence
