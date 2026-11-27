-- Prove2me | solution 1 for GlobalTheory.exists_coset_representatives_of_finite_subgroup_padicInt_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:38:10.233465+00:00
-- url     : https://prove2.me/submissions/9e9a856f-97ff-4ef9-96e4-9be2e3bac4b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCosetRepresentativesOfFiniteSubgroupPadicI
import Theorems.Thm_GlobalTheory_padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {l : ℕ} [hl : Fact l.Prime]
    (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (h2 : l ≠ 2) :
    ∃ (e : ℕ) (a : Fin e → ℕ), e * Nat.card Δ = l - 1 ∧ (∀ τ, ¬ l ∣ a τ) ∧
      (∀ τ τ', τ ≠ τ' → (a τ : ZMod l) ^ Nat.card Δ ≠ (a τ' : ZMod l) ^ Nat.card Δ) ∧
      ∀ x : ZMod l, x ≠ 0 → ∃! p : Fin e × Δ,
        x = (a p.1 : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) := by
  classical
  let g : Δ →* (ZMod l)ˣ :=
    (Units.map (PadicInt.toZMod (p := l) : ℤ_[l] →+* ZMod l).toMonoidHom).comp Δ.subtype
  have hg : ∀ d : Δ, (g d : ZMod l) = PadicInt.toZMod ((d : ℤ_[l]ˣ) : ℤ_[l]) := fun _ => rfl
  have hs : Nat.card Δ ≠ 0 := Nat.card_pos.ne'
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : PadicInt.toZMod ((d : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by rw [← hg, hd]; rfl
    have hp : ((d : ℤ_[l]ˣ) : ℤ_[l]) ^ Nat.card Δ = 1 := by
      have : d ^ Nat.card Δ = 1 := pow_card_eq_one'
      have := congrArg (fun z : Δ => ((z : ℤ_[l]ˣ) : ℤ_[l])) this
      simpa only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one] using this
    exact Subtype.ext (Units.ext (padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one h2 _ hs hp h1))
  let H : Subgroup (ZMod l)ˣ := g.range
  have hH : Nat.card H = Nat.card Δ := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hHmem : ∀ x : (ZMod l)ˣ, x ^ Nat.card Δ = 1 → x ∈ H := by
    intro x hx
    have hle : H ≤ (powMonoidHom (Nat.card Δ) : (ZMod l)ˣ →* (ZMod l)ˣ).ker := by
      intro y hy
      have : (⟨y, hy⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
      rw [hH] at this
      simpa using congrArg Subtype.val this
    have hc : Nat.card (powMonoidHom (Nat.card Δ) : (ZMod l)ˣ →* (ZMod l)ˣ).ker ≤ Nat.card H := by
      rw [IsCyclic.card_powMonoidHom_ker, hH]
      exact Nat.gcd_le_right _ (Nat.pos_of_ne_zero hs)
    rw [Subgroup.eq_of_le_of_card_ge hle hc]
    simpa using hx
  let φ : ((ZMod l)ˣ ⧸ H) ≃ Fin (Nat.card ((ZMod l)ˣ ⧸ H)) := Finite.equivFin _
  let r : Fin (Nat.card ((ZMod l)ˣ ⧸ H)) → (ZMod l)ˣ := fun τ => (φ.symm τ).out
  have hr : ∀ τ, ((r τ : (ZMod l)ˣ) : (ZMod l)ˣ ⧸ H) = φ.symm τ := fun τ => Quotient.out_eq _
  have hcast : ∀ τ, (((r τ : ZMod l).val : ℕ) : ZMod l) = r τ := fun τ => ZMod.natCast_zmod_val _
  have hreq : ∀ τ τ', (r τ)⁻¹ * r τ' ∈ H → τ = τ' := by
    intro τ τ' h
    have := QuotientGroup.eq.mpr h
    rw [hr, hr] at this
    exact φ.symm.injective this
  refine ⟨_, fun τ => (r τ : ZMod l).val, ?_, ?_, ?_, ?_⟩
  · rw [← hH, ← Subgroup.card_eq_card_quotient_mul_card_subgroup, Nat.card_eq_fintype_card,
      ZMod.card_units]
  · intro τ h
    have := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [hcast] at this
    exact (r τ).ne_zero this
  · intro τ τ' hne h
    simp only [hcast] at h
    have h' : r τ ^ Nat.card Δ = r τ' ^ Nat.card Δ := Units.ext (by simpa using h)
    exact hne (hreq _ _ (hHmem _ (by rw [mul_pow, inv_pow, h', inv_mul_cancel])))
  · intro x hx
    let u : (ZMod l)ˣ := Units.mk0 x hx
    have hu : (r (φ u))⁻¹ * u ∈ H := by
      rw [← QuotientGroup.eq, hr, Equiv.symm_apply_apply]
    obtain ⟨d, hd⟩ := hu
    have hform : ∀ p : Fin (Nat.card ((ZMod l)ˣ ⧸ H)) × Δ,
        x = (((r p.1 : ZMod l).val : ℕ) : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l]) ↔
          u = r p.1 * g p.2 := by
      intro p
      rw [hcast, ← hg, Units.ext_iff]
      rfl
    have hd' : u = r (φ u) * g d := by rw [hd, mul_inv_cancel_left]
    refine ⟨(φ u, d), (hform _).mpr hd', ?_⟩
    rintro ⟨τ, d'⟩ hp
    have hp' : u = r τ * g d' := (hform _).mp hp
    have hτ : τ = φ u := by
      apply hreq
      refine ⟨d' * d⁻¹, ?_⟩
      rw [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hp', mul_inv_eq_iff_eq_mul]
      exact hd'
    rw [hτ] at hp'
    have : g d' = g d := mul_left_cancel (hp'.symm.trans hd')
    rw [hτ, hinj this]
end GlobalTheory
