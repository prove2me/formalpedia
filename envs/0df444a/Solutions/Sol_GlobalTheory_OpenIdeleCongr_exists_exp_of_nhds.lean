-- Prove2me | solution 1 for GlobalTheory.OpenIdeleCongr.exists_exp_of_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:31:04.341058+00:00
-- url     : https://prove2.me/submissions/176cadf8-2be3-4247-b5b8-e27aa9d4ff48

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenIdeleSubgroupContainsCongruenceUnits
import Theorems.Thm_GlobalTheory_OpenIdeleCongr_exists_ne_zero_lt_val_subset_of_mem_nhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open GlobalTheory GlobalTheory.OpenIdeleCongr
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.OpenIdeleCongr
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (u : Set (v.adicCompletion F)) (hu : u ∈ nhds 1) :
    ∃ M : ℕ, ∀ y : v.adicCompletion F, Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ)) → y ∈ u := by
  obtain ⟨c, hc, hsub⟩ := exists_ne_zero_lt_val_subset_of_mem_nhds hu
  have h0 : Valued.v c ≠ 0 := by simpa using hc
  set k := WithZero.log (Valued.v c) with hkdef
  have hk : Valued.v c = WithZero.exp k := (WithZero.exp_log h0).symm
  refine ⟨(-k).toNat + 1, fun y hy => hsub ?_⟩
  show Valued.v (y - 1) < Valued.v c
  refine lt_of_le_of_lt hy ?_
  rw [hk, WithZero.exp_lt_exp]
  have := Int.self_le_toNat (-k)
  push_cast
  omega
end GlobalTheory.OpenIdeleCongr
