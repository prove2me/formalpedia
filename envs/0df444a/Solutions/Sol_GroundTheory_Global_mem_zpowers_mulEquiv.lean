-- Prove2me | solution 1 for GroundTheory.Global.mem_zpowers_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:37:25.201068+00:00
-- url     : https://prove2.me/submissions/660b2beb-811d-4f00-80f5-597f095c520d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.GroupCoh
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {k H G V W : Type*} [CommRing k] [Group H] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ' : Representation k H V} {ρ : Representation k G W}
variable [Fintype H] [Fintype G]
omit [Fintype H] [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution (e : H ≃* G) {τ : H} (hτ : ∀ h, h ∈ Subgroup.zpowers τ) (g : G) :
    g ∈ Subgroup.zpowers (e τ) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hτ (e.symm g))
  refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
  rw [← map_zpow, hn, MulEquiv.apply_symm_apply]
end GroundTheory.Global
