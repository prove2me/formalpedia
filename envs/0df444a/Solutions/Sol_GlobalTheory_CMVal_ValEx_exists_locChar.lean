-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.exists_locChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:43.725729+00:00
-- url     : https://prove2.me/submissions/1c421870-0b80-43c5-aabf-31e92791712a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_ValEx_cong_anti
import Theorems.Thm_GlobalTheory_CMVal_ValEx_val_binom
import Theorems.Thm_GlobalTheory_CMVal_ValEx_exp_one_sq
import Theorems.Thm_GlobalTheory_CMVal_ValEx_eq_one_of_cong
import Theorems.Thm_GlobalTheory_CMVal_ValEx_isOpen_cong
import Theorems.Thm_GlobalTheory_CMVal_ValEx_val_alg
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_exists_unitary_char_of_open_subgroup_and_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution {l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (w : HeightOneSpectrum (𝓞 E))
    (hv : w.valuation E (l : E) = WithZero.exp (-1 : ℤ)) (θ : Eˣ →* ℂˣ)
    (u : Eˣ) (hu : (u : E) = 1 + l) :
    ∃ ch : (w.adicCompletion E)ˣ →* ℂˣ, Continuous ch ∧ (∀ x, ‖((ch x : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ x ∈ cong (Valued.v : Valuation (w.adicCompletion E) ℤᵐ⁰) 2, ch x = 1) ∧
      (∀ z, IsOfFinOrder z → ch (toLoc w z) = θ z) ∧ ch (toLoc w u) ≠ 1 := by
  have hω := Complex.isPrimitiveRoot_exp l hl.ne_zero
  have hω1 := hω.norm'_eq_one hl.ne_zero
  generalize Complex.exp (2 * Real.pi * Complex.I / l) = ω at hω hω1
  let ω' : ℂˣ := Units.mk0 ω (hω.ne_zero hl.ne_zero)
  have hω' : ω' ^ l = 1 := Units.ext (by simpa [ω'] using hω.pow_eq_one)
  have hmem : ∀ n (k : Eˣ), toLoc w k ∈ cong (Valued.v : Valuation (w.adicCompletion E) ℤᵐ⁰) n ↔
      k ∈ cong (w.valuation E) n := fun n k => by
    change (Valued.v (algebraMap E (w.adicCompletion E) k) = 1 ∧
      Valued.v (algebraMap E (w.adicCompletion E) k - 1) ≤ _) ↔ _
    rw [← map_one (algebraMap E (w.adicCompletion E)), ← map_sub, val_alg, val_alg]
    rfl
  have hlt : w.valuation E (l : E) < 1 := by
    rw [hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hu1 : u ∈ cong (w.valuation E) 1 := ⟨by rw [hu]; exact Valuation.map_one_add_of_lt _ hlt, by
    rw [hu, add_sub_cancel_left, hv]; simp⟩
  have hu2 : u ∉ cong (w.valuation E) 2 := fun h => by
    have := h.2
    rw [hu, add_sub_cancel_left, hv, WithZero.exp_le_exp] at this
    omega
  have hul : u ^ l ∈ cong (w.valuation E) 2 := ⟨((cong _ 1).pow_mem hu1 l).1, by
    have e : ((u ^ l : Eˣ) : E) - 1 = ((1 + (l : E)) ^ l - 1 - l * l) + l * l := by
      rw [Units.val_pow_eq_pow_val, hu]; ring
    have e2 : w.valuation E (l : E) * w.valuation E (l : E) = WithZero.exp (-((2 : ℕ) : ℤ)) := by
      rw [hv, exp_one_sq]; rfl
    rw [e, ← e2]
    exact Valuation.map_add_le _ (val_binom _ hlt.le l) (map_mul _ _ _).le⟩
  haveI := Fact.mk hl
  have hord : orderOf (QuotientGroup.mk' (cong (w.valuation E) 2) u) = l :=
    orderOf_eq_prime (by rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).2 hul)
      (fun h => hu2 ((QuotientGroup.eq_one_iff _).1 h))
  obtain ⟨ch, h1, h3, h4, h5⟩ := exists_unitary_char_of_open_subgroup_and_hom _
    (CommGroup.torsion Eˣ × Multiplicative ℤ) _ (isOpen_cong w 2)
    ((toLoc w).comp ((CommGroup.torsion Eˣ).subtype.coprod (zpowersHom _ u)))
    ((θ.comp (CommGroup.torsion Eˣ).subtype).coprod (zpowersHom _ ω')) 1 continuous_const (by simp)
    (fun y => by
      have hθ : ‖((θ y.1 : ℂˣ) : ℂ)‖ = 1 := (((Units.coeHom ℂ).comp θ).isOfFinOrder y.1.2).norm_eq_one
      simp [hθ, ω', hω1]) (fun y hy => by
      have hy' : (y.1 : Eˣ) * u ^ y.2.toAdd ∈ cong (w.valuation E) 2 := (hmem 2 _).1 hy
      have hz : (y.1 : Eˣ) = 1 := eq_one_of_cong _ hl h2 hv y.1.2
        ((Subgroup.mul_mem_cancel_right _ ((cong _ 1).zpow_mem hu1 _)).1 (cong_anti _ (by norm_num) hy'))
      rw [hz, one_mul, ← QuotientGroup.eq_one_iff] at hy'
      have hd : ((orderOf (QuotientGroup.mk' (cong (w.valuation E) 2) u) : ℕ) : ℤ) ∣ y.2.toAdd :=
        orderOf_dvd_iff_zpow_eq_one.2 (by rw [← map_zpow]; exact hy')
      rw [hord] at hd
      obtain ⟨m, hm⟩ := hd
      change θ (y.1 : Eˣ) * ω' ^ y.2.toAdd = 1
      rw [hz, hm, zpow_mul, zpow_natCast, hω']; simp)
  refine ⟨ch, h1, h3, h4, fun z hz => ?_, ?_⟩
  · simpa using h5 (⟨z, hz⟩, 1)
  · have := h5 (1, Multiplicative.ofAdd 1)
    simp only [MonoidHom.comp_apply, MonoidHom.coprod_apply, map_one, one_mul, zpowersHom_apply, toAdd_ofAdd, zpow_one] at this
    rw [this]
    exact fun h => hω.ne_one hl.one_lt (congrArg Units.val h)
end GlobalTheory.CMVal.ValEx
