-- Prove2me | solution 1 for GlobalTheory.OpenIdeleCongr.exists_ne_zero_lt_val_subset_of_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:16:13.169315+00:00
-- url     : https://prove2.me/submissions/9a15659f-0748-459d-b0db-6a4246db6a6e

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenIdeleSubgroupContainsCongruenceUnits

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
theorem _root_.solution {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] {s : Set K} {x : K} :
    s ∈ nhds x → ∃ c : K, c ≠ 0 ∧ {y | Valued.v (y - x) < Valued.v c} ⊆ s := by
  rw [Valued.mem_nhds]
  rintro ⟨γ, hγ⟩
  obtain ⟨c, hc⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass (Valued.v : Valuation K Γ)) γ.1
  have hc' : (Valued.v : Valuation K Γ).restrict c = γ.1 := hc
  refine ⟨c, ?_, fun y hy => hγ ?_⟩
  · rintro rfl
    rw [map_zero] at hc'
    exact γ.ne_zero hc'.symm
  · change (Valued.v : Valuation K Γ).restrict (y - x) < γ.1
    rw [← hc', Valuation.restrict_lt_iff]
    exact hy
end GlobalTheory.OpenIdeleCongr
