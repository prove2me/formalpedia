-- Prove2me | solution 1 for GroundTheory.Global.differentIdeal_le_pow_of_le_differentExponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:35.505455+00:00
-- url     : https://prove2.me/submissions/9d565a0f-766e-42fe-a65c-add186828db0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
import Theorems.Thm_GroundTheory_Global_forall_valued_trace_le_one_iff
import Theorems.Thm_GroundTheory_Global_mem_inv_pow_iff
import Theorems.Thm_GroundTheory_Global_valued_trace_le_one_of_valuation_le_one
import Theorems.Thm_GroundTheory_Global_trace_mem_range_of_forall
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_field
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
open GroundTheory GroundTheory.Global
open SemiLocal
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
namespace GroundTheory.Global
theorem _root_.solution {n : ℕ}
    (hn : n ≤ differentExponent (v.adicCompletion K) (w.adicCompletion M)) :
    differentIdeal (𝓞 K) (𝓞 M) ≤ w.asIdeal ^ n := by
  have hI : w.asIdeal ^ n ≠ ⊥ := pow_ne_zero _ w.ne_bot
  rw [differentialIdeal_le_iff (K := K) (L := M) hI, Submodule.map_le_iff_le_comap]
  intro x hx
  obtain ⟨hxw, hxu⟩ := (mem_inv_pow_iff w n x).1 hx
  rw [Submodule.mem_comap]
  have hloc : ∀ (v' : HeightOneSpectrum (𝓞 K)) (u : PlacesOver M v'),
      Valued.v (Algebra.trace (v'.adicCompletion K) (u.1.adicCompletion M)
        (algebraMap M (u.1.adicCompletion M) x)) ≤ 1 := by
    intro v' u
    by_cases hu : u.1 = w
    · obtain ⟨u1, hu1⟩ := u
      simp only at hu
      subst hu
      have hv : v' = v := HeightOneSpectrum.ext
        ((Ideal.over_def u1.asIdeal v'.asIdeal).trans (Ideal.over_def u1.asIdeal v.asIdeal).symm)
      subst hv
      refine (forall_valued_trace_le_one_iff v' u1 n).2 hn _ ?_
      rw [valued_algebraMap_field]
      exact hxw
    · exact valued_trace_le_one_of_valuation_le_one v' u (hxu u.1 hu)
  obtain ⟨a, ha⟩ := trace_mem_range_of_forall (K := K) x hloc
  exact Submodule.mem_one.2 ⟨a, ha⟩
end GroundTheory.Global
