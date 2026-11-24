-- Prove2me | solution 1 for GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:07:23.58348+00:00
-- url     : https://prove2.me/submissions/355b6951-7c08-4a5b-833d-8898e21883cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FractionalIdealNormPowSixMulDiscriminantClassInv
import Theorems.Thm_GlobalTheory_DiscClass_latDisc_eq_of_mul
import Theorems.Thm_GlobalTheory_DiscClass_abs_norm_eq_norm_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DiscClass
namespace GlobalTheory.DiscClass
theorem _root_.solution {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (h2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λa Λb : PeriodPair)
    (ha : IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λa) (hb : IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λb)
    (hcl : ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟) :
    nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λa‖ = nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λb‖ := by

  have h1 : ClassGroup.mk K (𝔟 * 𝔞⁻¹) = 1 := by rw [map_mul, map_inv, ← hcl, mul_inv_cancel]
  obtain ⟨c, hcE⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h1)
  have hb' : (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ c * 𝔞 := by
    rw [← hcE, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply 𝔟.ne_zero
    rw [hb', FractionalIdeal.spanSingleton_zero, zero_mul]
  have hu : φK c ≠ 0 := (map_ne_zero φK).2 hc0

  have hlat : ∀ w, φK c * w ∈ Λb.lattice ↔ w ∈ Λa.lattice := by
    intro w
    have eb : φK c * w ∈ Λb.lattice ↔ φK c * w ∈ φK '' ((𝔟 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
      rw [← hb]; rfl
    have ea : w ∈ Λa.lattice ↔ w ∈ φK '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
      rw [← ha]; rfl
    rw [eb, ea]
    constructor
    · rintro ⟨y, hy, e⟩
      have hy' : y ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K) := hy
      rw [hb', FractionalIdeal.mem_singleton_mul] at hy'
      obtain ⟨y', hy', rfl⟩ := hy'
      refine ⟨y', hy', ?_⟩
      rw [map_mul] at e
      exact mul_left_cancel₀ hu e
    · rintro ⟨y, hy, rfl⟩
      refine ⟨c * y, ?_, map_mul _ _ _⟩
      show c * y ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K)
      rw [hb', FractionalIdeal.mem_singleton_mul]
      exact ⟨y, hy, rfl⟩
  have hD := latDisc_eq_of_mul Λa Λb (φK c) hu hlat

  have hN : nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = ‖φK c‖ ^ 2 * nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
    unfold nrm
    rw [hb', map_mul, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, abs_norm_eq_norm_sq φK h2 hc c]
  rw [hN, hD, norm_mul, norm_pow]
  ring
end GlobalTheory.DiscClass
