-- Prove2me | solution 1 for GlobalTheory.IntegralFrameAllCompare.extension_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:52:37.39491+00:00
-- url     : https://prove2.me/submissions/7f3a2bd4-50f6-437c-a92a-e8ed1ad992e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_IntegralFrameAcquisition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_VVNonnegIffLeOne
import Theorems.Thm_GlobalTheory_IntegralFrameAllCompare_mem_range_iff
import Theorems.Thm_GlobalTheory_IntegralFrameAllCompare_exists_scale
import Theorems.Thm_GlobalTheory_IntegralFrameAllCompare_index_eq
import Theorems.Thm_GlobalTheory_IntegralFrameAllCompare_finite_of_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameAllCompare
open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition
namespace GlobalTheory.IntegralFrameAllCompare
theorem _root_.solution {F : Type} [Field F] [NumberField F] {la : HeightOneSpectrum (𝓞 F)} {T T' : CDVR}
    {io : F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) (hT' : T'.FinRes) (j : T.Fr →+* T'.Fr) (e' : ℕ) :
    (OverLa la T'.V (j.comp io) e' ∧
        ∀ a : T.V, j (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) ↔
      ∃ r : ℕ, e' = r * e ∧ IsFiniteValuedExt T T' j r ∧ OverLa la T'.V (j.comp io) (r * e) := by
  constructor
  · rintro ⟨ho', hj⟩
    obtain ⟨r, hr⟩ := exists_scale j hj
    obtain rfl := index_eq ho ho' hr
    have h0 : 0 < r := Nat.pos_of_mul_pos_right ho'.1
    exact ⟨r, rfl, ⟨finite_of_scale j h0 hr hT', h0, hr⟩, ho'⟩
  · rintro ⟨r, rfl, ⟨-, -, hr⟩, ho'⟩
    refine ⟨ho', fun a => (mem_range_iff _).2 ?_⟩
    rw [hr]
    exact mul_nonneg (by positivity) ((mem_range_iff _).1 ⟨a, rfl⟩)
end GlobalTheory.IntegralFrameAllCompare
