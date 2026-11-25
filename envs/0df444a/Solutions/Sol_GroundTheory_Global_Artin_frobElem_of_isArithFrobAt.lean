-- Prove2me | solution 1 for GroundTheory.Global.Artin.frobElem_of_isArithFrobAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:34.668805+00:00
-- url     : https://prove2.me/submissions/fea15ca7-d61c-4274-960f-498bc6d9ef4d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
import Theorems.Thm_GroundTheory_Global_Artin_mk_pow_smul_of_isArithFrobAt
import Theorems.Thm_GroundTheory_Global_Artin_card_quotient_subfieldPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))
namespace GroundTheory.Global.Artin
theorem _root_.solution {φ : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal)
    (x : Gal(L/K)) (φx : H) (h : IsArithFrobAt (𝓞 (fixedField H)) φx (x • w.asIdeal)) :
    ∃ i ∈ (MulAut.conj x • w.asIdeal.inertia Gal(L/K) : Subgroup Gal(L/K)),
      (φx : Gal(L/K)) = x * φ ^ (frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal)
        (w.asIdeal.inertia Gal(L/K)) x : ℤ) * x⁻¹ * i := by
  set r := frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.asIdeal.inertia Gal(L/K)) x
  have hψ : IsArithFrobAt (𝓞 K) (x * φ * x⁻¹) (x • w.asIdeal) := hφ.conj x
  have hN : Nat.card (𝓞 (fixedField H) ⧸ (x • w.asIdeal).under (𝓞 (fixedField H))) =
      Nat.card (𝓞 K ⧸ (x • w.asIdeal).under (𝓞 K)) ^ r := card_quotient_subfieldPlace H w x

  have hj : (φx : Gal(L/K)) * ((x * φ * x⁻¹) ^ r)⁻¹ ∈ (x • w.asIdeal).inertia Gal(L/K) := by
    intro y
    rw [Submodule.mem_toAddSubgroup, ← Ideal.Quotient.eq, mul_smul]
    have h1 := mk_pow_smul_of_isArithFrobAt hψ r (((x * φ * x⁻¹) ^ r)⁻¹ • y)
    rw [smul_inv_smul] at h1
    rw [h1]
    change Ideal.Quotient.mk _ (φx • (((x * φ * x⁻¹) ^ r)⁻¹ • y)) = _
    erw [h.mk_apply]
    rw [hN]
  have hs : ((x * φ * x⁻¹) ^ r)⁻¹ ∈ MulAction.stabilizer Gal(L/K) (x • w.asIdeal) :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ hψ.mem_stabilizer r)
  have hi := mul_mul_inv_mem_inertia hs hj
  rw [inv_inv, show ((x * φ * x⁻¹) ^ r)⁻¹ * ((φx : Gal(L/K)) * ((x * φ * x⁻¹) ^ r)⁻¹) *
    (x * φ * x⁻¹) ^ r = ((x * φ * x⁻¹) ^ r)⁻¹ * φx by group] at hi
  refine ⟨((x * φ * x⁻¹) ^ r)⁻¹ * φx, ?_, ?_⟩
  · rw [mem_conj_smul_iff, ← mem_inertia_smul_iff]
    exact hi
  · rw [zpow_natCast, ← conj_pow]
    group
end GroundTheory.Global.Artin
