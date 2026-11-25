-- Prove2me | solution 1 for GroundTheory.ProfCoh.eq_one_of_mem_unitFiltration_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:14.690393+00:00
-- url     : https://prove2.me/submissions/c9848be3-65e2-4416-befe-f68176819026

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
import Theorems.Thm_GroundTheory_ProfCoh_pow_mem_unitFiltration_succ_iff
import Theorems.Thm_GroundTheory_LocalField_eq_zero_of_forall_pow_dvd
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {p : ℕ} (hp : p.Prime) {e : ℕ} {ε : 𝒪[K]ˣ}
  (hpe : (p : 𝒪[K]) = ϖ ^ e * ε)
include hϖ hp hpe
namespace GroundTheory.ProfCoh
theorem _root_.solution {k : ℕ} (hk : e + 1 ≤ k) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K k) (h : u ^ p = 1) : u = 1 := by
  have hall : ∀ n, u ∈ unitFiltration K (k + n) := by
    intro n
    induction n with
    | zero => simpa using hu
    | succ n ih =>
      have := (pow_mem_unitFiltration_succ_iff hϖ hp hpe (by omega) ih).mp
        (by rw [h]; exact one_mem _)
      simpa [add_assoc] using this
  have h0 : (u : 𝒪[K]) - 1 = 0 := by
    refine eq_zero_of_forall_pow_dvd hϖ fun N => ?_
    have := unitFiltration_antitone K (Nat.le_add_left N k) (hall N)
    exact (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp this)
  ext
  simpa [sub_eq_zero] using h0
end GroundTheory.ProfCoh
