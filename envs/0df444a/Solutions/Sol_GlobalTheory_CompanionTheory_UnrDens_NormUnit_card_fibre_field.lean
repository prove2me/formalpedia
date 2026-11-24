-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fibre_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:47:33.778235+00:00
-- url     : https://prove2.me/submissions/9f283e8a-7333-49ef-be73-2221bd53d9b1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_finite_of_resAlg
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_nontrivial_of_resAlg
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_fixed_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_isUnit_of_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_units
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_normU_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_coe_tauU
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_mem_ker_normU
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_ker_ratioU
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_range_ratioU
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_sq_sub_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormUnit
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormUnit
theorem _root_.solution (h : ResAlg E τ q ε) (hf : IsField E) {t : E} (ht : τ t = t)
    (t0 : t ≠ 0) : Nat.card {a : E // a * τ a = t} = q + 1 := by
  have := finite_of_resAlg h
  have := nontrivial_of_resAlg h
  have hq := h.one_lt
  have hU : Nat.card Eˣ = q ^ 2 - 1 := card_units h hf
  have hsq := sq_sub_one hq
  have lag : ∀ f : Eˣ →* Eˣ, Nat.card Eˣ = Nat.card f.range * Nat.card f.ker := fun f => by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hR : Nat.card (ratioU τ).range = q + 1 := by
    have e := lag (ratioU τ)
    rw [card_ker_ratioU h, hU, hsq, mul_comm (q - 1)] at e
    exact (Nat.eq_of_mul_eq_mul_right (by omega) e).symm
  have hK : Nat.card (normU τ).ker = q + 1 := by
    rw [← range_ratioU h hf]
    exact hR
  have hN : Nat.card (normU τ).range = q - 1 := by
    have e := lag (normU τ)
    rw [hK, hU, hsq] at e
    exact (Nat.eq_of_mul_eq_mul_right (by omega) e).symm
  let S : Set Eˣ := {k | τ (k : E) = k}
  have hS : Nat.card S = q - 1 := by
    rw [← card_fixed_ne h]
    exact Nat.card_congr
      { toFun := fun k => ⟨((k.1 : Eˣ) : E), k.2, k.1.ne_zero⟩
        invFun := fun x => ⟨(h.fixedUnit x.1 x.2.1 x.2.2).unit, x.2.1⟩
        left_inv := fun k => Subtype.ext (Units.ext rfl)
        right_inv := fun x => rfl }
  have hsub : ((normU τ).range : Set Eˣ) ⊆ S := by
    intro k hk
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hk
    show τ ((normU τ b : Eˣ) : E) = normU τ b
    rw [normU_apply, Units.val_mul, coe_tauU, map_mul, h.inv, mul_comm]
  have heq : ((normU τ).range : Set Eˣ) = S := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite S)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hS]
    exact hN.ge
  have htu : IsUnit t := isUnit_of_ne hf t0
  have hmem : htu.unit ∈ (normU τ).range := by
    rw [← SetLike.mem_coe, heq]
    exact ht
  obtain ⟨a₀, ha₀⟩ := MonoidHom.mem_range.1 hmem
  have hn : ∀ b : Eˣ, (b : E) * τ b = t → normU τ b = htu.unit := fun b hb =>
    Units.ext (by rw [normU_apply, Units.val_mul, coe_tauU, IsUnit.unit_spec]; exact hb)
  have hna : (a₀ : E) * τ a₀ = t := by
    have h5 := congrArg Units.val ha₀
    rwa [normU_apply, Units.val_mul, coe_tauU, IsUnit.unit_spec] at h5
  have hau : ∀ a : {a : E // a * τ a = t}, IsUnit a.1 := fun a =>
    isUnit_of_mul_isUnit_left (show IsUnit (a.1 * τ a.1) by rw [a.2]; exact htu)
  have hna' : ∀ a : {a : E // a * τ a = t}, normU τ (hau a).unit = htu.unit := fun a =>
    hn _ (by rw [IsUnit.unit_spec]; exact a.2)
  rw [← hK]
  symm
  exact Nat.card_congr
    { toFun := fun k => ⟨(((k : Eˣ) * a₀ : Eˣ) : E), by
        have hk := mem_ker_normU.1 k.2
        rw [Units.val_mul, map_mul]
        linear_combination ((a₀ : E) * τ (a₀ : E)) * hk + hna⟩
      invFun := fun a => ⟨(hau a).unit * a₀⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ha₀, hna' a, mul_inv_cancel]⟩
      left_inv := fun k => Subtype.ext (Units.ext (by simp [mul_assoc]))
      right_inv := fun a => Subtype.ext (by simp [mul_assoc]) }
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
