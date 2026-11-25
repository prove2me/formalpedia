-- Prove2me | solution 1 for GroundTheory.Global.le_differentExponent_of_differentIdeal_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:31:16.914818+00:00
-- url     : https://prove2.me/submissions/df520635-94f2-40f0-8160-8db249d883b6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
import Theorems.Thm_GroundTheory_Global_forall_valued_trace_le_one_iff
import Theorems.Thm_GroundTheory_Global_mem_inv_pow_iff
import Theorems.Thm_GroundTheory_Global_exists_valuation_eq_exp
import Theorems.Thm_GroundTheory_Global_valued_trace_le_one_of_valuation_le_one
import Theorems.Thm_GroundTheory_Global_SemiLocal_algebraMap_trace_eq_sum
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_field
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_int_le_one
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
    (h : differentIdeal (𝓞 K) (𝓞 M) ≤ w.asIdeal ^ n) :
    n ≤ differentExponent (v.adicCompletion K) (w.adicCompletion M) := by
  classical
  have hI : w.asIdeal ^ n ≠ ⊥ := pow_ne_zero _ w.ne_bot
  rw [differentialIdeal_le_iff (K := K) (L := M) hI, Submodule.map_le_iff_le_comap] at h
  let w0 : PlacesOver M v := ⟨w, inferInstance⟩

  have hX : ∀ X : M, w.valuation M X ≤ WithZero.exp (n : ℤ) →
      (∀ u : HeightOneSpectrum (𝓞 M), u ≠ w → u.valuation M X ≤ 1) →
      Valued.v (Algebra.trace (v.adicCompletion K) (w.adicCompletion M)
        (algebraMap M (w.adicCompletion M) X)) ≤ 1 := by
    intro X hXw hXu
    obtain ⟨a, ha⟩ := Submodule.mem_one.1
      (Submodule.mem_comap.1 (h ((mem_inv_pow_iff w n X).2 ⟨hXw, hXu⟩)))
    have ha' : algebraMap (𝓞 K) K a = Algebra.trace K M X := ha
    have htot : Valued.v (algebraMap K (v.adicCompletion K) (Algebra.trace K M X)) ≤ 1 := by
      rw [← ha', ← IsScalarTower.algebraMap_apply]
      exact valued_algebraMap_int_le_one v a
    rw [algebraMap_trace_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ w0)] at htot
    have hrest : Valued.v (∑ u ∈ Finset.univ.erase w0,
        Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
          (algebraMap M (u.1.adicCompletion M) X)) ≤ 1 :=
      Valuation.map_sum_le _ fun u hu ↦ valued_trace_le_one_of_valuation_le_one v u
        (hXu u.1 fun he ↦ Finset.ne_of_mem_erase hu (Subtype.ext he))
    have hsplit : Algebra.trace (v.adicCompletion K) (w.adicCompletion M)
        (algebraMap M (w.adicCompletion M) X) =
        (Algebra.trace (v.adicCompletion K) (w0.1.adicCompletion M)
          (algebraMap M (w0.1.adicCompletion M) X) + ∑ u ∈ Finset.univ.erase w0,
            Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
              (algebraMap M (u.1.adicCompletion M) X)) - ∑ u ∈ Finset.univ.erase w0,
            Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
              (algebraMap M (u.1.adicCompletion M) X) := by
      rw [add_sub_cancel_right]
    rw [hsplit]
    exact (Valuation.map_sub _ _ _).trans (max_le htot hrest)
  rw [← forall_valued_trace_le_one_iff v w n]
  intro y hy
  obtain ⟨x0, hx0w, hx0u⟩ := exists_valuation_eq_exp w n
  set X0 := algebraMap M (w.adicCompletion M) x0 with hX0def
  have hX0 : Valued.v X0 = WithZero.exp (n : ℤ) := by
    rw [hX0def, valued_algebraMap_field]
    exact hx0w
  have hX00 : X0 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hX0
    exact WithZero.zero_ne_coe hX0
  set z := X0⁻¹ * y with hzdef
  have hz : Valued.v z ≤ 1 := by
    rw [hzdef, map_mul, map_inv₀, hX0]
    calc (WithZero.exp (n : ℤ))⁻¹ * Valued.v y
        ≤ (WithZero.exp (n : ℤ))⁻¹ * WithZero.exp (n : ℤ) := by gcongr
      _ = 1 := inv_mul_cancel₀ (by simp)
  have hzmem : z ∈ (w.adicCompletionIntegers M : Set (w.adicCompletion M)) := hz
  have hopen : IsOpen ((fun s ↦ X0 * (z - s)) ⁻¹'
      ((Valued.v : Valuation (w.adicCompletion M) ℤᵐ⁰).integer : Set (w.adicCompletion M))) :=
    (Valued.isOpen_integer (w.adicCompletion M)).preimage (continuous_const.mul (continuous_const.sub continuous_id))
  have hzU : z ∈ ((fun s ↦ X0 * (z - s)) ⁻¹'
      ((Valued.v : Valuation (w.adicCompletion M) ℤᵐ⁰).integer : Set (w.adicCompletion M))) := by
    simp
  obtain ⟨_, hs, b, rfl⟩ := mem_closure_iff.1
    (adicCompletionIntegers_subset_closure_ringOfIntegers w hzmem) _ hopen hzU
  have hs' : Valued.v (X0 * (z - algebraMap M (w.adicCompletion M) (algebraMap (𝓞 M) M b))) ≤ 1 :=
    hs
  have hb : ∀ u : HeightOneSpectrum (𝓞 M), u.valuation M (algebraMap (𝓞 M) M b) ≤ 1 :=
    fun u ↦ u.valuation_le_one b
  have key := hX (x0 * algebraMap (𝓞 M) M b)
    (by simpa [map_mul, hx0w] using mul_le_mul' (le_refl (WithZero.exp (n : ℤ))) (hb w))
    (fun u hu ↦ by simpa [map_mul] using mul_le_mul' (hx0u u hu) (hb u))
  have hy : y = X0 * (z - algebraMap M (w.adicCompletion M) (algebraMap (𝓞 M) M b)) +
      algebraMap M (w.adicCompletion M) (x0 * algebraMap (𝓞 M) M b) := by
    rw [map_mul, ← hX0def, hzdef, mul_sub, ← mul_assoc, mul_inv_cancel₀ hX00, one_mul,
      sub_add_cancel]
  rw [hy, map_add]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ key)
  refine (forall_valued_trace_le_one_iff v w 0).2 (Nat.zero_le _) _ ?_
  rw [Nat.cast_zero, WithZero.exp_zero]
  exact hs'
end GroundTheory.Global
