-- Prove2me | solution 1 for GroundTheory.Global.asIdeal_dvd_finprod_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:36.713803+00:00
-- url     : https://prove2.me/submissions/4d6da6e6-c1a4-43ef-aa3d-ec3201bbfc4e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Theorems.Thm_GroundTheory_Global_mulSupport_asIdeal_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
namespace GroundTheory.Global
theorem _root_.solution {a : HeightOneSpectrum R → ℕ} (ha : (support a).Finite)
    (v : HeightOneSpectrum R) :
    v.asIdeal ∣ ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w ↔ 1 ≤ a v := by
  have hfa : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v := by
    rw [HasFiniteMulSupport, mulSupport_asIdeal_pow]
    exact ha
  constructor
  · intro h
    classical
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := ha.toFinset)
      (by rw [mulSupport_asIdeal_pow, ha.coe_toFinset])] at h
    obtain ⟨w, hw, hvw⟩ := ((HeightOneSpectrum.prime v).dvd_finsetProd_iff _).1 h
    have hvw' := (HeightOneSpectrum.prime v).dvd_of_dvd_pow hvw
    have heq : v = w := HeightOneSpectrum.ext (associated_iff_eq.1
      ((HeightOneSpectrum.prime v).associated_of_dvd (HeightOneSpectrum.prime w) hvw'))
    subst heq
    rw [Set.Finite.mem_toFinset, mem_support] at hw
    omega
  · intro h
    exact (dvd_pow_self _ (by omega)).trans (finprod_mem_dvd v hfa)
end GroundTheory.Global
