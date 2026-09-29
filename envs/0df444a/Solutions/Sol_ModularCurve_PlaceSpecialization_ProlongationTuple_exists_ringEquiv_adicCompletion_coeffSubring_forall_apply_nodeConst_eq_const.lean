-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_ringEquiv_adicCompletion_coeffSubring_forall_apply_nodeConst_eq_const
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a82aeda4-ff6a-5381-b164-e170ac8f6448

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible
import Theorems.Thm_PowerSeries_exists_ringEquiv_adicCompletion_quotient_span_X_sub_C
import Theorems.Thm_ModularCurve_NodeLocalized_finite_residueField_coeffSubring
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_coeffSubring_forall_apply_nodeConst_eq_const
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

universe u

namespace F6Skel

open IsLocalRing Polynomial

theorem residue_pow_card {S : Type*} [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] (a : S) :
    a ^ Nat.card (ResidueField S) - a ∈ maximalIdeal S := by
  haveI : Fintype (ResidueField S) := Fintype.ofFinite _
  rw [← residue_eq_zero_iff, map_sub, map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]

theorem natCast_card_mem {S : Type*} [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] :
    ((Nat.card (ResidueField S) : ℕ) : S) ∈ maximalIdeal S := by
  haveI : Fintype (ResidueField S) := Fintype.ofFinite _
  rw [← residue_eq_zero_iff, map_natCast, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]

theorem teichmuller_unique {S : Type*} [CommRing S] [IsLocalRing S] [Finite (ResidueField S)]
    (t₁ t₂ : S) (h₁ : t₁ ^ Nat.card (ResidueField S) = t₁) (h₂ : t₂ ^ Nat.card (ResidueField S) = t₂)
    (h : t₁ - t₂ ∈ maximalIdeal S) : t₁ = t₂ := by
  haveI : Fintype (ResidueField S) := Fintype.ofFinite _
  set Q := Nat.card (ResidueField S) with hQ

  set s : S := ∑ i ∈ Finset.range Q, t₁ ^ i * t₂ ^ (Q - 1 - i) with hs
  have hgeom : s * (t₁ - t₂) = t₁ ^ Q - t₂ ^ Q := (Commute.all t₁ t₂).geom_sum₂_mul Q
  have hres12 : residue S t₁ = residue S t₂ := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact h
  have hsm : s ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff, hs, map_sum]
    have : ∀ i ∈ Finset.range Q, residue S (t₁ ^ i * t₂ ^ (Q - 1 - i)) = residue S t₂ ^ (Q - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, hres12, ← pow_add]
      congr 1
      rw [Finset.mem_range] at hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hQ0 : ((Q : ℕ) : ResidueField S) = 0 := by
      rw [hQ, Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero _
    rw [hQ0, zero_mul]

  have hkey : (t₁ - t₂) * (s - 1) = 0 := by
    have : (t₁ - t₂) * (s - 1) = s * (t₁ - t₂) - (t₁ - t₂) := by ring
    rw [this, hgeom, h₁, h₂, sub_self]
  have hu : IsUnit (s - 1) := by
    have : IsUnit (1 - s) :=
      (isUnit_or_isUnit_one_sub_self s).resolve_left (fun hu => ((mem_maximalIdeal _).mp hsm) hu)
    rw [show s - 1 = -(1 - s) by ring]
    exact this.neg
  have h0 : t₁ - t₂ = 0 := (hu.mul_left_eq_zero).mp hkey
  exact sub_eq_zero.mp h0

theorem existsUnique_teichmuller {S : Type*} [CommRing S] [IsLocalRing S] [HenselianLocalRing S]
    [Finite (IsLocalRing.ResidueField S)] (a : S) :
    ∃! t : S, t ^ Nat.card (IsLocalRing.ResidueField S) = t ∧ t - a ∈ IsLocalRing.maximalIdeal S := by
  haveI : Fintype (ResidueField S) := Fintype.ofFinite _
  set Q := Nat.card (ResidueField S) with hQ
  have hQ2 : 2 ≤ Q := by
    rw [hQ, Nat.card_eq_fintype_card]; exact Fintype.one_lt_card

  set F : S[X] := X ^ Q - X with hF
  have hmonic : F.Monic := by
    rw [hF]; exact monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by omega : 1 < Q))
  have hFa : F.eval a ∈ maximalIdeal S := by
    rw [hF, eval_sub, eval_pow, eval_X]; exact residue_pow_card a
  have hF'a : IsUnit (F.derivative.eval a) := by
    rw [hF, derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_pow, eval_X, eval_one]

    rw [eval_C]
    have hm : (Q : S) * a ^ (Q - 1) ∈ maximalIdeal S := Ideal.mul_mem_right _ _ natCast_card_mem
    have : IsUnit (1 - (Q : S) * a ^ (Q - 1)) :=
      (isUnit_or_isUnit_one_sub_self _).resolve_left (fun hu => ((mem_maximalIdeal _).mp hm) hu)
    rw [show (Q : S) * a ^ (Q - 1) - 1 = -(1 - (Q : S) * a ^ (Q - 1)) by ring]
    exact this.neg
  obtain ⟨t, ht, hta⟩ := HenselianLocalRing.is_henselian F hmonic a hFa hF'a
  have ht' : t ^ Q = t := by
    have := ht
    rw [IsRoot, hF, eval_sub, eval_pow, eval_X, sub_eq_zero] at this
    exact this
  refine ⟨t, ⟨ht', hta⟩, ?_⟩
  rintro t₂ ⟨ht₂, ht₂a⟩
  refine teichmuller_unique t₂ t ht₂ ht' ?_
  have : t₂ - t = (t₂ - a) - (t - a) := by ring
  rw [this]; exact sub_mem ht₂a hta

theorem teichmuller_map {S S' : Type*} [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] [HenselianLocalRing S']
    [Finite (IsLocalRing.ResidueField S')] (f : S →+* S') [IsLocalHom f] (Q : ℕ) (hQ : Q = Nat.card (IsLocalRing.ResidueField S'))
    (t : S) (ht : t ^ Q = t) (t' : S') (ht' : t' ^ Q = t') (h : t' - f t ∈ IsLocalRing.maximalIdeal S') : f t = t' := by
  subst hQ
  have hft : (f t) ^ Nat.card (ResidueField S') = f t := by rw [← map_pow, ht]
  exact (teichmuller_unique t' (f t) ht' hft h).symm

end F6Skel

namespace F6Skel

open IsLocalRing Polynomial

theorem henselianLocalRing_of_isAdicComplete (S : Type*) [CommRing S] [IsLocalRing S]
    [IsAdicComplete (maximalIdeal S) S] : HenselianLocalRing S where
  is_henselian f hf a₀ h₁ h₂ :=
    HenselianRing.is_henselian (I := maximalIdeal S) f hf a₀ h₁ (h₂.map _)

theorem exists_teichmuller_digits {S : Type*} [CommRing S] [IsLocalRing S] [HenselianLocalRing S]
    [Finite (ResidueField S)] (t : S) (ht : maximalIdeal S = Ideal.span {t}) (x : S) (n : ℕ) :
    ∃ d : ℕ → S, (∀ i, d i ^ Nat.card (ResidueField S) = d i) ∧
      x - ∑ i ∈ Finset.range n, d i * t ^ i ∈ Ideal.span {t ^ n} := by
  haveI : Fintype (ResidueField S) := Fintype.ofFinite _
  have hQ1 : 1 ≤ Nat.card (ResidueField S) := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos
  induction n with
  | zero =>
      refine ⟨fun _ => 0, fun i => by rw [zero_pow (by omega)], ?_⟩
      simp
  | succ n ih =>
      obtain ⟨d, hd, hx⟩ := ih
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hx

      obtain ⟨τ, ⟨hτ, hτy⟩, -⟩ := existsUnique_teichmuller y
      rw [ht] at hτy
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hτy
      refine ⟨Function.update d n τ, fun i => ?_, ?_⟩
      · by_cases hi : i = n
        · subst hi; rw [Function.update_self]; exact hτ
        · rw [Function.update_of_ne hi]; exact hd i
      · rw [Finset.sum_range_succ, Function.update_self]
        have hsum : ∑ i ∈ Finset.range n, Function.update d n τ i * t ^ i = ∑ i ∈ Finset.range n, d i * t ^ i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mem_range] at hi
          rw [Function.update_of_ne (by omega)]
        rw [hsum]

        have : x - (∑ i ∈ Finset.range n, d i * t ^ i + τ * t ^ n) = -(z * t ^ (n + 1)) := by
          have h1 : x - ∑ i ∈ Finset.range n, d i * t ^ i = y * t ^ n := hy.symm
          rw [pow_succ]
          linear_combination h1 + t ^ n * hz
        rw [this]
        exact (Ideal.span {t ^ (n + 1)}).neg_mem (Ideal.mem_span_singleton'.mpr ⟨z, rfl⟩)

end F6Skel

namespace F6Skel
open IsLocalRing

theorem teichmuller_unique_of_natCast_mem {S : Type*} [CommRing S] [IsLocalRing S] (Q : ℕ)
    (hQ : ((Q : ℕ) : S) ∈ maximalIdeal S)
    (t₁ t₂ : S) (h₁ : t₁ ^ Q = t₁) (h₂ : t₂ ^ Q = t₂) (h : t₁ - t₂ ∈ maximalIdeal S) : t₁ = t₂ := by
  set s : S := ∑ i ∈ Finset.range Q, t₁ ^ i * t₂ ^ (Q - 1 - i) with hs
  have hgeom : s * (t₁ - t₂) = t₁ ^ Q - t₂ ^ Q := (Commute.all t₁ t₂).geom_sum₂_mul Q
  have hres12 : residue S t₁ = residue S t₂ := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact h
  have hsm : s ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff, hs, map_sum]
    have : ∀ i ∈ Finset.range Q, residue S (t₁ ^ i * t₂ ^ (Q - 1 - i)) = residue S t₂ ^ (Q - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, hres12, ← pow_add]
      congr 1
      rw [Finset.mem_range] at hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hQ0 : ((Q : ℕ) : ResidueField S) = 0 := by
      rw [← map_natCast (residue S), residue_eq_zero_iff]; exact hQ
    rw [hQ0, zero_mul]
  have hkey : (t₁ - t₂) * (s - 1) = 0 := by
    have : (t₁ - t₂) * (s - 1) = s * (t₁ - t₂) - (t₁ - t₂) := by ring
    rw [this, hgeom, h₁, h₂, sub_self]
  have hu : IsUnit (s - 1) := by
    have : IsUnit (1 - s) :=
      (isUnit_or_isUnit_one_sub_self s).resolve_left (fun hu => ((mem_maximalIdeal _).mp hsm) hu)
    rw [show s - 1 = -(1 - s) by ring]
    exact this.neg
  have h0 : t₁ - t₂ = 0 := (hu.mul_left_eq_zero).mp hkey
  exact sub_eq_zero.mp h0

end F6Skel

section CrossingLocal
open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

namespace F6Skel

variable {W : Type u} [CommRing W] [IsLocalRing W]

theorem not_isUnit_crossing (π : W) (hπ : π ∈ maximalIdeal W) :
    ¬ IsUnit ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C π) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  simp only [map_sub, map_mul, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, zero_mul, zero_sub,
    IsUnit.neg_iff]
  exact (mem_maximalIdeal _).mp hπ

private theorem _root_.F6Skel.isLocalRing_uvCrossingModel (π : W) (hπ : π ∈ maximalIdeal W) : IsLocalRing (UVCrossingModel W π) := by
  haveI : Nontrivial (UVCrossingModel W π) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top (not_isUnit_crossing π hπ))
  exact IsLocalRing.of_surjective' (mk π) (mk_surjective π)

p2m_export "F6Skel" "isLocalRing_uvCrossingModel"

theorem isLocalHom_mk (π : W) (hπ : π ∈ maximalIdeal W) : IsLocalHom (mk (W := W) π) := by
  unfold mk
  refine isLocalHom_of_le_jacobson_bot _ ?_
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
  exact (mem_maximalIdeal _).mpr (not_isUnit_crossing π hπ)

theorem isUnit_mk_iff (π : W) (hπ : π ∈ maximalIdeal W) (F : MvPowerSeries (Fin 2) W) :
    IsUnit (mk π F) ↔ IsUnit (MvPowerSeries.constantCoeff F) := by
  haveI := isLocalHom_mk π hπ
  rw [← MvPowerSeries.isUnit_iff_constantCoeff]
  exact ⟨fun h => isUnit_of_map_unit (mk π) F h, fun h => h.map _⟩

private theorem _root_.F6Skel.not_isUnit_const (π : W) (hπ : π ∈ maximalIdeal W) (w : W) (hw : w ∈ maximalIdeal W) :
    ¬ IsUnit (const π w) := by
  show ¬ IsUnit (mk π (MvPowerSeries.C w))
  rw [isUnit_mk_iff π hπ, MvPowerSeries.constantCoeff_C]; exact (mem_maximalIdeal _).mp hw

p2m_export "F6Skel" "not_isUnit_const"

theorem not_isUnit_U (π : W) (hπ : π ∈ maximalIdeal W) : ¬ IsUnit (U π) := by
  show ¬ IsUnit (mk π (MvPowerSeries.X 0))
  rw [isUnit_mk_iff π hπ, MvPowerSeries.constantCoeff_X]; exact not_isUnit_zero

theorem not_isUnit_V (π : W) (hπ : π ∈ maximalIdeal W) : ¬ IsUnit (V π) := by
  show ¬ IsUnit (mk π (MvPowerSeries.X 1))
  rw [isUnit_mk_iff π hπ, MvPowerSeries.constantCoeff_X]; exact not_isUnit_zero

theorem exists_not_isUnit_sub_const (π : W) (hπ : π ∈ maximalIdeal W) (r : UVCrossingModel W π) :
    ∃ w : W, ¬ IsUnit (r - const π w) := by
  obtain ⟨F, rfl⟩ := mk_surjective π r
  refine ⟨MvPowerSeries.constantCoeff F, ?_⟩
  show ¬ IsUnit (mk π F - mk π (MvPowerSeries.C _))
  rw [← map_sub, isUnit_mk_iff π hπ, map_sub, MvPowerSeries.constantCoeff_C, sub_self]; exact not_isUnit_zero

theorem exists_const_of_pow_card_eq [HenselianLocalRing W] [Finite (ResidueField W)]
    (π : W) (hπ : π ∈ maximalIdeal W) (ρ : UVCrossingModel W π)
    (hρ : ρ ^ Nat.card (ResidueField W) = ρ) :
    ∃ w : W, w ^ Nat.card (ResidueField W) = w ∧ ρ = const π w := by
  haveI := isLocalRing_uvCrossingModel π hπ
  obtain ⟨w₀, hw₀⟩ := exists_not_isUnit_sub_const π hπ ρ
  obtain ⟨w, ⟨hw, hww₀⟩, -⟩ := existsUnique_teichmuller w₀
  refine ⟨w, hw, ?_⟩
  have hcw : (const π w) ^ Nat.card (ResidueField W) = const π w := by
    rw [← constHom_apply, ← map_pow, hw]
  have hcong : ρ - const π w ∈ maximalIdeal (UVCrossingModel W π) := by
    have : ρ - const π w = (ρ - const π w₀) - (const π w - const π w₀) := by ring
    rw [this]
    refine sub_mem ((mem_maximalIdeal _).mpr hw₀) ?_
    rw [← constHom_apply, ← constHom_apply, ← map_sub, constHom_apply]
    exact (mem_maximalIdeal _).mpr (not_isUnit_const π hπ _ hww₀)
  have hQm : ((Nat.card (ResidueField W) : ℕ) : UVCrossingModel W π) ∈ maximalIdeal (UVCrossingModel W π) := by
    have : ((Nat.card (ResidueField W) : ℕ) : UVCrossingModel W π) = const π (Nat.card (ResidueField W) : W) := by
      rw [← constHom_apply, map_natCast]
    rw [this]
    exact (mem_maximalIdeal _).mpr (not_isUnit_const π hπ _ natCast_card_mem)
  exact teichmuller_unique_of_natCast_mem _ hQm ρ (const π w) hρ hcw hcong

end F6Skel
end CrossingLocal

namespace F6Skel
open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem exists_teichmuller_digits_global {S : Type*} [CommRing S] [IsLocalRing S] [HenselianLocalRing S]
    [Finite (ResidueField S)] (t : S) (ht : maximalIdeal S = Ideal.span {t}) (x : S) :
    ∃ d : ℕ → S, (∀ i, d i ^ Nat.card (ResidueField S) = d i) ∧
      ∀ n, x - ∑ i ∈ Finset.range n, d i * t ^ i ∈ Ideal.span {t ^ n} := by
  classical

  let T : S → S := fun r => Classical.choose (existsUnique_teichmuller r).exists
  have hT : ∀ r, T r ^ Nat.card (ResidueField S) = T r ∧ T r - r ∈ maximalIdeal S :=
    fun r => Classical.choose_spec (existsUnique_teichmuller r).exists
  have hTz : ∀ r, ∃ z, z * t = r - T r := by
    intro r
    have h := (hT r).2
    rw [ht] at h
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp h
    exact ⟨-z, by rw [neg_mul, hz]; ring⟩
  let N : S → S := fun r => Classical.choose (hTz r)
  have hN : ∀ r, N r * t = r - T r := fun r => Classical.choose_spec (hTz r)

  let rem : ℕ → S := fun n => Nat.rec x (fun _ r => N r) n
  have rem_zero : rem 0 = x := rfl
  have rem_succ : ∀ n, rem (n + 1) = N (rem n) := fun n => rfl
  refine ⟨fun i => T (rem i), fun i => (hT _).1, fun n => ?_⟩

  have inv : ∀ n, x - ∑ i ∈ Finset.range n, T (rem i) * t ^ i = rem n * t ^ n := by
    intro n
    induction n with
    | zero => simp [rem_zero]
    | succ n ih =>
        rw [Finset.sum_range_succ, rem_succ, pow_succ]
        have h := hN (rem n)
        linear_combination ih - t ^ n * h
  rw [inv n]
  exact Ideal.mem_span_singleton'.mpr ⟨rem n, rfl⟩

theorem exists_const_of_pow_card_pow_eq {W : Type u} [CommRing W] [IsLocalRing W] [HenselianLocalRing W]
    [Finite (ResidueField W)] (π : W) (hπ : π ∈ maximalIdeal W) (b : ℕ) (hb : 1 ≤ b)
    (ρ : UVCrossingModel W π) (hρ : ρ ^ (Nat.card (ResidueField W) ^ b) = ρ) :
    ∃ w : W, w ^ Nat.card (ResidueField W) = w ∧ ρ = const π w := by
  haveI := isLocalRing_uvCrossingModel π hπ
  set Q := Nat.card (ResidueField W) with hQ
  obtain ⟨w₀, hw₀⟩ := exists_not_isUnit_sub_const π hπ ρ
  obtain ⟨w, ⟨hw, hww₀⟩, -⟩ := existsUnique_teichmuller w₀
  refine ⟨w, hw, ?_⟩
  have hwb : ∀ c : ℕ, w ^ (Q ^ c) = w := by
    intro c
    induction c with
    | zero => simp
    | succ c ih => rw [pow_succ, pow_mul, ih, hw]
  have hcw : (const π w) ^ (Q ^ b) = const π w := by
    rw [← constHom_apply, ← map_pow, hwb]
  have hcong : ρ - const π w ∈ maximalIdeal (UVCrossingModel W π) := by
    have : ρ - const π w = (ρ - const π w₀) - (const π w - const π w₀) := by ring
    rw [this]
    refine sub_mem ((mem_maximalIdeal _).mpr hw₀) ?_
    rw [← constHom_apply, ← constHom_apply, ← map_sub, constHom_apply]
    exact (mem_maximalIdeal _).mpr (not_isUnit_const π hπ _ hww₀)
  have hQm : (((Q ^ b : ℕ) : ℕ) : UVCrossingModel W π) ∈ maximalIdeal (UVCrossingModel W π) := by
    have : (((Q ^ b : ℕ) : ℕ) : UVCrossingModel W π) = const π ((Q : W) ^ b) := by
      rw [← constHom_apply, map_pow, map_natCast]; push_cast; rfl
    rw [this]
    refine (mem_maximalIdeal _).mpr (not_isUnit_const π hπ _ ?_)
    exact Ideal.pow_mem_of_mem _ natCast_card_mem _ hb
  exact teichmuller_unique_of_natCast_mem _ hQm ρ (const π w) hρ hcw hcong

end F6Skel

namespace F6Skel
open IsLocalRing

theorem injective_of_map_irreducible_ne_zero {S₀ W : Type*} [CommRing S₀] [IsDomain S₀] [IsDiscreteValuationRing S₀]
    [CommRing W] [IsDomain W] (τ : S₀ →+* W) (t : S₀) (ht : Irreducible t) (h : τ t ≠ 0) :
    Function.Injective τ := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have hker : RingHom.ker τ ≠ ⊥ := by
    intro hb
    have : a ∈ RingHom.ker τ := ha
    rw [hb, Ideal.mem_bot] at this
    exact ha0 this
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hker ht
  have htn : t ^ n ∈ RingHom.ker τ := by rw [hn]; exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_pow] at htn
  exact h (pow_eq_zero_iff'.mp htn |>.1)

theorem maximalIdeal_pow_smul_top {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (t : S) (ht : Irreducible t) (n : ℕ) :
    (maximalIdeal S ^ n • ⊤ : Submodule S S) = Ideal.span {t ^ n} := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht, Ideal.span_singleton_pow, smul_eq_mul,
    Ideal.mul_top]

theorem surjective_of_forall_sub_mem {S₀ W : Type*} [CommRing S₀] [IsDomain S₀] [IsDiscreteValuationRing S₀]
    [IsAdicComplete (maximalIdeal S₀) S₀]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (τ : S₀ →+* W) (t : S₀) (ht : Irreducible t) (π : W) (hπ : Irreducible π) (hτ : τ t = π)
    (hres : ∀ w : W, ∃ s : S₀, w - τ s ∈ maximalIdeal W) :
    Function.Surjective τ := by
  classical
  intro w
  have hmW : maximalIdeal W = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ

  have step : ∀ (n : ℕ) (s : S₀) (u : W), w - τ s = π ^ n * u →
      ∃ (a : S₀) (u' : W), w - τ (s + t ^ n * a) = π ^ (n + 1) * u' := by
    intro n s u hsu
    obtain ⟨a, ha⟩ := hres u
    rw [hmW] at ha
    obtain ⟨u', hu'⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨a, u', ?_⟩
    rw [map_add, map_mul, map_pow, hτ, pow_succ]
    linear_combination hsu - π ^ n * hu'

  let P : ℕ → Type _ := fun n => {p : S₀ × W // w - τ p.1 = π ^ n * p.2}
  let P0 : P 0 := ⟨(0, w), by simp⟩
  let Psucc : ∀ n, P n → P (n + 1) := fun n p =>
    ⟨(p.1.1 + t ^ n * Classical.choose (step n p.1.1 p.1.2 p.2),
      Classical.choose (Classical.choose_spec (step n p.1.1 p.1.2 p.2))),
      Classical.choose_spec (Classical.choose_spec (step n p.1.1 p.1.2 p.2))⟩
  let seq : ∀ n, P n := fun n => Nat.rec P0 Psucc n
  let f : ℕ → S₀ := fun n => (seq n).1.1
  have hf : ∀ n, w - τ (f n) ∈ Ideal.span {π ^ n} := fun n =>
    Ideal.mem_span_singleton'.mpr ⟨(seq n).1.2, by rw [mul_comm]; exact ((seq n).2).symm⟩
  have hfsucc : ∀ n, f (n + 1) - f n ∈ Ideal.span {t ^ n} := by
    intro n
    show (seq (n + 1)).1.1 - (seq n).1.1 ∈ _
    have : (seq (n + 1)).1.1 = (seq n).1.1 + t ^ n * Classical.choose (step n (seq n).1.1 (seq n).1.2 (seq n).2) := rfl
    rw [this, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

  have hcauchy : ∀ m n, m ≤ n → f m - f n ∈ Ideal.span {t ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
        have h1 := hfsucc n
        have h2 : Ideal.span {t ^ n} ≤ Ideal.span {t ^ m} :=
          Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow t hmn)
        have : f m - f (n + 1) = (f m - f n) - (f (n + 1) - f n) := by ring
        rw [this]
        exact sub_mem ih (h2 h1)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal S₀) f (fun {m n} hmn => by
    rw [SModEq.sub_mem, maximalIdeal_pow_smul_top t ht m]
    exact hcauchy m n hmn)

  have hτpow : ∀ n (x : S₀), x ∈ Ideal.span {t ^ n} → τ x ∈ Ideal.span {π ^ n} := by
    intro n x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, map_pow, hτ]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨L, ?_⟩

  have hall : ∀ n, w - τ L ∈ Ideal.span {π ^ n} := by
    intro n
    have h1 := hf n
    have h2 : f n - L ∈ Ideal.span {t ^ n} := by
      have := hL n
      rw [SModEq.sub_mem, maximalIdeal_pow_smul_top t ht n] at this
      exact this
    have : w - τ L = (w - τ (f n)) + τ (f n - L) := by rw [map_sub]; ring
    rw [this]
    exact add_mem h1 (hτpow n _ h2)
  have hzero : w - τ L = 0 := by
    refine IsHausdorff.haus' (I := maximalIdeal W) _ (fun n => ?_)
    rw [SModEq.sub_mem, sub_zero, maximalIdeal_pow_smul_top π hπ n]
    exact hall n
  exact (sub_eq_zero.mp hzero).symm

end F6Skel

namespace F6Skel

open IsLocalRing

section ResidueFinite
variable {O : Type*} [CommRing O] [IsLocalRing O]

private theorem aug_exists (ϖ : O) :
    ∃ ε : (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}) →+* O ⧸ Ideal.span {ϖ},
      ∀ F : PowerSeries O, ε (Ideal.Quotient.mk _ F) = Ideal.Quotient.mk _ (PowerSeries.constantCoeff F) := by
  have hker : ∀ f ∈ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ},
      ((Ideal.Quotient.mk (Ideal.span {ϖ})).comp (PowerSeries.constantCoeff (R := O))) f = 0 := by
    intro f hf
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [RingHom.comp_apply, map_mul, map_sub, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, zero_sub, map_mul,
      map_neg, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), neg_zero, mul_zero]
  exact ⟨Ideal.Quotient.lift _ _ hker, fun F => by rw [Ideal.Quotient.lift_mk]; rfl⟩

theorem isUnit_of_isUnit_mk_C (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O) (o : O)
    (h : IsUnit (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}) (PowerSeries.C o))) :
    IsUnit o := by
  obtain ⟨ε, hε⟩ := aug_exists ϖ
  have h1 := h.map ε
  rw [hε, PowerSeries.constantCoeff_C] at h1

  obtain ⟨v, hv⟩ := h1
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (↑v⁻¹ : O ⧸ Ideal.span {ϖ})
  have hos : Ideal.Quotient.mk (Ideal.span {ϖ}) (o * s) = 1 := by rw [map_mul, ← hv, hs, Units.mul_inv]
  rw [← (Ideal.Quotient.mk (Ideal.span {ϖ})).map_one, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hos
  obtain ⟨t, ht⟩ := hos

  have hu : IsUnit (o * s) := by
    have : o * s = 1 - (-(t * ϖ)) := by rw [sub_neg_eq_add, ht]; ring
    rw [this]
    apply isUnit_one_sub_self_of_mem_nonunits
    rw [← mem_maximalIdeal]
    exact neg_mem (Ideal.mul_mem_left _ _ hϖ)
  exact isUnit_of_mul_isUnit_left hu

theorem finite_residueField_quotient_span_X_sub_C [Finite (ResidueField O)] (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O)
    [IsLocalRing (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})] :
    Finite (ResidueField (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})) := by
  set I : Ideal (PowerSeries O) := Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ} with hI
  let φ : O →+* PowerSeries O ⧸ I := (Ideal.Quotient.mk I).comp PowerSeries.C

  have hloc : ∀ o ∈ maximalIdeal O, φ o ∈ maximalIdeal (PowerSeries O ⧸ I) := by
    intro o ho
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_maximalIdeal _ |>.mp ho) (isUnit_of_isUnit_mk_C ϖ hϖ o hu)
  have hX : Ideal.Quotient.mk I PowerSeries.X = φ ϖ := by
    show Ideal.Quotient.mk I PowerSeries.X = Ideal.Quotient.mk I (PowerSeries.C ϖ)
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span rfl

  have hker : ∀ o ∈ maximalIdeal O, ((residue (PowerSeries O ⧸ I)).comp φ) o = 0 := by
    intro o ho
    rw [RingHom.comp_apply, residue_eq_zero_iff]
    exact hloc o ho
  let ψ : ResidueField O →+* ResidueField (PowerSeries O ⧸ I) := Ideal.Quotient.lift (maximalIdeal O) _ hker
  refine Finite.of_surjective ψ fun z => ?_
  obtain ⟨y, rfl⟩ := residue_surjective z
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨residue O (PowerSeries.constantCoeff F), ?_⟩
  show Ideal.Quotient.lift (maximalIdeal O) _ hker (Ideal.Quotient.mk _ (PowerSeries.constantCoeff F)) = _
  rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]

  have hF : F = PowerSeries.C (PowerSeries.constantCoeff F) + PowerSeries.X * PowerSeries.mk fun p => PowerSeries.coeff (p + 1) F := by
    rw [← PowerSeries.sub_const_eq_X_mul_shift, add_sub_cancel]
  apply (Ideal.Quotient.eq (I := maximalIdeal (PowerSeries O ⧸ I))).mpr
  have hmkF : Ideal.Quotient.mk I F = φ (PowerSeries.constantCoeff F) +
      φ ϖ * Ideal.Quotient.mk I (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) F) := by
    conv_lhs => rw [hF]
    rw [map_add, map_mul, hX]
    rfl
  show φ (PowerSeries.constantCoeff F) - Ideal.Quotient.mk I F ∈ maximalIdeal (PowerSeries O ⧸ I)
  rw [hmkF, sub_add_eq_sub_sub, sub_self, zero_sub]
  exact neg_mem (Ideal.mul_mem_right _ _ (hloc ϖ hϖ))

end ResidueFinite

section Card

theorem exists_pow_card_residueField_eq {S₁ S₂ : Type*} [CommRing S₁] [IsLocalRing S₁] [Finite (ResidueField S₁)]
    [CommRing S₂] [IsLocalRing S₂] [Finite (ResidueField S₂)] (q : ℕ) [Fact q.Prime]
    (h₁ : ((q : ℕ) : S₁) ∈ maximalIdeal S₁) (h₂ : ((q : ℕ) : S₂) ∈ maximalIdeal S₂) :
    ∃ a b : ℕ, 1 ≤ b ∧ Nat.card (ResidueField S₁) ^ a = Nat.card (ResidueField S₂) ^ b := by
  classical
  have hq : q.Prime := Fact.out
  haveI : Fintype (ResidueField S₁) := Fintype.ofFinite _
  haveI : Fintype (ResidueField S₂) := Fintype.ofFinite _
  haveI : CharP (ResidueField S₁) q :=
    (CharP.charP_iff_prime_eq_zero hq).mpr (by rw [← map_natCast (residue S₁), residue_eq_zero_iff]; exact h₁)
  haveI : CharP (ResidueField S₂) q :=
    (CharP.charP_iff_prime_eq_zero hq).mpr (by rw [← map_natCast (residue S₂), residue_eq_zero_iff]; exact h₂)
  obtain ⟨n₁, -, hn₁⟩ := FiniteField.card (ResidueField S₁) q
  obtain ⟨n₂, -, hn₂⟩ := FiniteField.card (ResidueField S₂) q
  refine ⟨(n₂ : ℕ), (n₁ : ℕ), n₁.one_le, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hn₁, hn₂, ← pow_mul, ← pow_mul, mul_comm]

end Card

end F6Skel

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.UVCrossingModel

namespace F6Core

section Stubs
variable {W : Type u} [CommRing W] [IsLocalRing W]

private theorem _root_.F6Core.isLocalRing_uvCrossingModel (π : W) (hπ : π ∈ maximalIdeal W) : IsLocalRing (UVCrossingModel W π) :=
  F6Skel.isLocalRing_uvCrossingModel π hπ
p2m_export "F6Core" "isLocalRing_uvCrossingModel"
private theorem _root_.F6Core.not_isUnit_const (π : W) (hπ : π ∈ maximalIdeal W) (w : W) (hw : w ∈ maximalIdeal W) : ¬ IsUnit (const π w) :=
  F6Skel.not_isUnit_const π hπ w hw
p2m_export "F6Core" "not_isUnit_const"
theorem exists_const_of_pow_eq_of_pow [HenselianLocalRing W] [Finite (ResidueField W)] (π : W) (hπ : π ∈ maximalIdeal W)
    (b : ℕ) (hb : 1 ≤ b) (ρ : UVCrossingModel W π) (hρ : ρ ^ (Nat.card (ResidueField W) ^ b) = ρ) :
    ∃ w : W, w ^ Nat.card (ResidueField W) = w ∧ ρ = const π w :=
  F6Skel.exists_const_of_pow_card_pow_eq π hπ b hb ρ hρ
theorem exists_not_isUnit_sub_const' (π : W) (hπ : π ∈ maximalIdeal W) (r : UVCrossingModel W π) :
    ∃ w : W, ¬ IsUnit (r - const π w) :=
  F6Skel.exists_not_isUnit_sub_const π hπ r
private theorem _root_.F6Core.natCast_card_mem {S : Type*} [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] :
    ((Nat.card (ResidueField S) : ℕ) : S) ∈ maximalIdeal S := F6Skel.natCast_card_mem
p2m_export "F6Core" "natCast_card_mem"
private theorem _root_.F6Core.henselianLocalRing_of_isAdicComplete (S : Type*) [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S] :
    HenselianLocalRing S := F6Skel.henselianLocalRing_of_isAdicComplete S
p2m_export "F6Core" "henselianLocalRing_of_isAdicComplete"
private theorem _root_.F6Core.exists_teichmuller_digits_global {S : Type*} [CommRing S] [IsLocalRing S] [HenselianLocalRing S] [Finite (ResidueField S)]
    (t : S) (ht : maximalIdeal S = Ideal.span {t}) (x : S) :
    ∃ d : ℕ → S, (∀ i, d i ^ Nat.card (ResidueField S) = d i) ∧ ∀ n, x - ∑ i ∈ Finset.range n, d i * t ^ i ∈ Ideal.span {t ^ n} :=
  F6Skel.exists_teichmuller_digits_global t ht x
p2m_export "F6Core" "exists_teichmuller_digits_global"
end Stubs

section ConstNZ
open ModularCurve.UVCrossingModel

theorem Ws30.mem_span_of_const_eq_zero {W : Type*} [CommRing W] (π c : W) (h : const π c = 0) : c ∈ Ideal.span {π} := by
  classical
  have hker : ∀ f ∈ uvCrossingIdeal W π, ((Ideal.Quotient.mk (Ideal.span {π})).comp MvPowerSeries.constantCoeff) f = 0 := by
    intro f hf
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    have hP : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C π :
        MvPowerSeries (Fin 2) W) = -π := by
      rw [map_sub, map_mul, MvPowerSeries.constantCoeff_X, zero_mul, MvPowerSeries.constantCoeff_C, zero_sub]
    rw [RingHom.comp_apply, map_mul, hP, map_mul, map_neg, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π),
      neg_zero, mul_zero]
  have hρ : Ideal.Quotient.lift _ _ hker (const π c) = Ideal.Quotient.mk (Ideal.span {π}) c := by
    show Ideal.Quotient.lift _ _ hker (UVCrossingModel.mk π (MvPowerSeries.C c)) = _
    rw [UVCrossingModel.mk, Ideal.Quotient.lift_mk, RingHom.comp_apply, MvPowerSeries.constantCoeff_C]
  have := congrArg (Ideal.Quotient.lift _ _ hker) h
  rw [hρ, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

theorem Ws30.const_ne_zero {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (c : W) (hc : c ≠ 0) : const (ϖ ^ e) c ≠ 0 := by
  classical
  have hπ0 : ϖ ^ e ∈ nonZeroDivisors W := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hϖ.ne_zero)
  have hnzd := ModularCurve.UVCrossingModel.const_mem_nonZeroDivisors (W := W) hπ0

  suffices key : ∀ (n : ℕ) (c : W), c ≠ 0 → IsDiscreteValuationRing.addVal W c ≤ n → const (ϖ ^ e) c ≠ 0 by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ((IsDiscreteValuationRing.addVal_eq_top_iff.not).mpr hc)
    exact key n c hc (by rw [← hn])
  intro n
  induction n with
  | zero =>
    intro c hc hv h0
    have hcm : c ∈ Ideal.span {ϖ} :=
      Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self ϖ (by omega)) (Ws30.mem_span_of_const_eq_zero _ _ h0)
    rw [Ideal.mem_span_singleton] at hcm
    have h1 : (1 : ℕ∞) ≤ IsDiscreteValuationRing.addVal W c := by
      rw [← IsDiscreteValuationRing.addVal_uniformizer hϖ]
      exact IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hcm
    have := h1.trans hv
    simp at this
  | succ n ih =>
    intro c hc hv h0
    obtain ⟨c₁, rfl⟩ := Ideal.mem_span_singleton'.mp (Ws30.mem_span_of_const_eq_zero _ _ h0)
    have hc₁ : c₁ ≠ 0 := fun h => hc (by rw [h, zero_mul])
    have h0' : const (ϖ ^ e) c₁ = 0 := by
      have : const (ϖ ^ e) c₁ * const (ϖ ^ e) (ϖ ^ e) = 0 := by
        rw [← UVCrossingModel.constHom_apply, ← UVCrossingModel.constHom_apply, ← map_mul]; exact h0
      exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hnzd).mp this
    have hv₁ : IsDiscreteValuationRing.addVal W c₁ ≤ n := by
      have hadd : IsDiscreteValuationRing.addVal W (c₁ * ϖ ^ e) =
          IsDiscreteValuationRing.addVal W c₁ + (e : ℕ∞) := by
        rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]
        simp
      rw [hadd] at hv
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp ((IsDiscreteValuationRing.addVal_eq_top_iff.not).mpr hc₁)
      rw [← hm] at hv ⊢
      have : (m : ℕ∞) + (e : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) := hv
      norm_cast at this ⊢
      omega
    exact ih c₁ hc₁ hv₁ h0'
end ConstNZ

section Core
variable {S₀ : Type*} [CommRing S₀] [IsDomain S₀] [IsDiscreteValuationRing S₀] [IsAdicComplete (maximalIdeal S₀) S₀]
  [Finite (ResidueField S₀)]
  {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
  [Finite (ResidueField W)]

theorem const_sub' (π : W) (a b : W) : const π (a - b) = const π a - const π b := map_sub (constHom π) a b
theorem const_mul' (π : W) (a b : W) : const π (a * b) = const π a * const π b := map_mul (constHom π) a b
theorem const_pow' (π : W) (a : W) (n : ℕ) : const π (a ^ n) = const π a ^ n := map_pow (constHom π) a n
theorem const_sum' (π : W) (n : ℕ) (f : ℕ → W) : const π (∑ i ∈ Finset.range n, f i) = ∑ i ∈ Finset.range n, const π (f i) :=
  map_sum (constHom π) f (Finset.range n)

theorem const_injective (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E) :
    Function.Injective (const (π ^ E) : W → UVCrossingModel W (π ^ E)) := by
  intro a b h
  by_contra hab
  exact Ws30.const_ne_zero π hπ E hE (a - b) (sub_ne_zero.mpr hab) (by rw [const_sub', h, sub_self])

theorem exists_eq_const (t : S₀) (ht : Irreducible t) (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (a b : ℕ) (hb : 1 ≤ b) (hab : Nat.card (ResidueField S₀) ^ a = Nat.card (ResidueField W) ^ b)
    (g : S₀ →+* UVCrossingModel W (π ^ E)) (hg : g t = const (π ^ E) π)
    (hsep : ∀ r : UVCrossingModel W (π ^ E), (∀ n, r ∈ Ideal.span {const (π ^ E) π ^ n}) → r = 0)
    (s : S₀) : ∃ w : W, g s = const (π ^ E) w := by
  haveI : HenselianLocalRing S₀ := henselianLocalRing_of_isAdicComplete S₀
  haveI : HenselianLocalRing W := henselianLocalRing_of_isAdicComplete W
  have hπm : π ^ E ∈ maximalIdeal W :=
    Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).mpr hπ.not_isUnit) _ (Nat.pos_of_ne_zero (by omega))
  obtain ⟨d, hd, hds⟩ := exists_teichmuller_digits_global t ht.maximalIdeal_eq s
  have hpow' : ∀ i k, (g (d i)) ^ (Nat.card (ResidueField S₀) ^ k) = g (d i) := by
    intro i k
    induction k with
    | zero => rw [pow_zero, pow_one]
    | succ m ih => rw [pow_succ, pow_mul, ih, ← map_pow, hd i]
  have hpow : ∀ i, (g (d i)) ^ (Nat.card (ResidueField W) ^ b) = g (d i) := fun i => by rw [← hab]; exact hpow' i a
  choose e he using fun i => exists_const_of_pow_eq_of_pow (π ^ E) hπm b hb (g (d i)) (hpow i)
  let wseq : ℕ → W := fun n => ∑ i ∈ Finset.range n, e i * π ^ i
  have hcong : ∀ n, g s - const (π ^ E) (wseq n) ∈ Ideal.span {const (π ^ E) π ^ n} := by
    intro n
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hds n)
    have hs : s = ∑ i ∈ Finset.range n, d i * t ^ i + r * t ^ n := by linear_combination -hr
    have hgs : g s = ∑ i ∈ Finset.range n, const (π ^ E) (e i) * const (π ^ E) π ^ i + g r * const (π ^ E) π ^ n := by
      rw [hs, map_add, map_mul, map_pow, hg, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_pow, hg, ← (he i).2]
    have hw : const (π ^ E) (wseq n) = ∑ i ∈ Finset.range n, const (π ^ E) (e i) * const (π ^ E) π ^ i := by
      simp only [wseq, const_sum', const_mul', const_pow']
    rw [hgs, hw, add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hcau : ∀ {m n : ℕ}, m ≤ n → wseq m ≡ wseq n [SMOD (maximalIdeal W ^ m • ⊤ : Submodule W W)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
    have : wseq m - wseq n = -∑ i ∈ Finset.Ico m n, e i * π ^ i := by
      simp only [wseq]
      rw [← Finset.sum_range_add_sum_Ico _ hmn]
      ring
    rw [this]
    refine neg_mem (Ideal.sum_mem _ fun i hi => ?_)
    obtain ⟨hmi, -⟩ := Finset.mem_Ico.mp hi
    exact Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right (pow_dvd_pow π hmi) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' wseq hcau
  refine ⟨L, ?_⟩
  have hall : ∀ n, g s - const (π ^ E) L ∈ Ideal.span {const (π ^ E) π ^ n} := by
    intro n
    have h2 : const (π ^ E) (wseq n) - const (π ^ E) L ∈ Ideal.span {const (π ^ E) π ^ n} := by
      have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton'] at h
      obtain ⟨c, hc⟩ := h
      rw [← const_sub', ← hc, const_mul', const_pow']
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have := Ideal.add_mem _ (hcong n) h2
    rwa [sub_add_sub_cancel] at this
  exact sub_eq_zero.mp (hsep _ hall)

end Core

section Tau
variable {S₀ : Type*} [CommRing S₀] [IsDomain S₀] [IsDiscreteValuationRing S₀] [IsAdicComplete (maximalIdeal S₀) S₀]
  [Finite (ResidueField S₀)]
  {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
  [Finite (ResidueField W)]

private theorem _root_.F6Core.injective_of_map_irreducible_ne_zero (τ : S₀ →+* W) (t : S₀) (ht : Irreducible t) (h : τ t ≠ 0) :
    Function.Injective τ := F6Skel.injective_of_map_irreducible_ne_zero τ t ht h
p2m_export "F6Core" "injective_of_map_irreducible_ne_zero"
private theorem _root_.F6Core.surjective_of_forall_sub_mem (τ : S₀ →+* W) (t : S₀) (ht : Irreducible t) (π : W) (hπ : Irreducible π)
    (hτ : τ t = π) (hres : ∀ w : W, ∃ s : S₀, w - τ s ∈ maximalIdeal W) : Function.Surjective τ :=
  F6Skel.surjective_of_forall_sub_mem τ t ht π hπ hτ hres

p2m_export "F6Core" "surjective_of_forall_sub_mem"

theorem exists_ringEquiv (t : S₀) (ht : Irreducible t) (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (a b : ℕ) (hb : 1 ≤ b) (hab : Nat.card (ResidueField S₀) ^ a = Nat.card (ResidueField W) ^ b)
    (g : S₀ →+* UVCrossingModel W (π ^ E)) (hg : g t = const (π ^ E) π)
    (hsep : ∀ r : UVCrossingModel W (π ^ E), (∀ n, r ∈ Ideal.span {const (π ^ E) π ^ n}) → r = 0)
    (hres : ∀ w : W, ∃ s : S₀, ¬ IsUnit (const (π ^ E) w - g s)) :
    ∃ τ : S₀ ≃+* W, (∀ s, g s = const (π ^ E) (τ s)) ∧ τ t = π := by
  choose τf hτf using exists_eq_const t ht π hπ E hE a b hb hab g hg hsep
  have hinj := const_injective π hπ E hE
  have h1 : τf 1 = 1 := hinj (by rw [← hτf, map_one, ← constHom_apply, map_one])
  have hmul : ∀ x y, τf (x * y) = τf x * τf y := fun x y =>
    hinj (by rw [← hτf, map_mul, hτf, hτf, const_mul'])
  have h0 : τf 0 = 0 := hinj (by rw [← hτf, map_zero, ← constHom_apply, map_zero])
  have hadd : ∀ x y, τf (x + y) = τf x + τf y := fun x y =>
    hinj (by rw [← hτf, map_add, hτf, hτf, ← constHom_apply, ← constHom_apply, ← constHom_apply, map_add])
  let τ : S₀ →+* W :=
    { toFun := τf, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd }
  have hτ : ∀ s, τ s = τf s := fun _ => rfl
  have hτt : τ t = π := hinj (by rw [hτ, ← hτf, hg])
  have hτinj : Function.Injective τ :=
    injective_of_map_irreducible_ne_zero τ t ht (by rw [hτt]; exact hπ.ne_zero)
  have hτsurj : Function.Surjective τ := by
    refine surjective_of_forall_sub_mem τ t ht π hπ hτt fun w => ?_
    obtain ⟨s, hs⟩ := hres w
    refine ⟨s, (mem_maximalIdeal _).mpr fun hu => hs ?_⟩
    rw [hτf s, ← hτ, ← const_sub']
    exact hu.map (constHom (π ^ E))
  refine ⟨RingEquiv.ofBijective τ ⟨hτinj, hτsurj⟩, fun s => ?_, ?_⟩
  · exact hτf s
  · exact hτt
end Tau

end F6Core

namespace F6Skel
section J
variable {O B : Type*} [CommRing O] [IsLocalRing O] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

scoped instance isAdicComplete_map_maximalIdeal :
    IsAdicComplete ((IsLocalRing.maximalIdeal B).map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)))
      (AdicCompletion (IsLocalRing.maximalIdeal B) B) :=
  by rw [IsAdicComplete.map_algebraMap_iff]; exact AdicCompletion.isAdicComplete (IsNoetherian.noetherian _)

theorem exists_sub_algebraMap_mem_map (x : AdicCompletion (IsLocalRing.maximalIdeal B) B) :
    ∃ b : B, x - algebraMap B _ b ∈ (IsLocalRing.maximalIdeal B).map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) := by
  obtain ⟨sq, rfl⟩ := AdicCompletion.mk_surjective (IsLocalRing.maximalIdeal B) B x
  refine ⟨sq 1, ?_⟩
  have hk : AdicCompletion.mk _ _ sq - algebraMap B _ (sq 1) ∈
      ((IsLocalRing.maximalIdeal B) ^ 1 • ⊤ : Submodule B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian _), LinearMap.mem_ker,
      AdicCompletion.eval_apply, AdicCompletion.val_sub_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, AdicCompletion.of_apply]
    exact sub_self _
  rw [pow_one, Ideal.smul_top_eq_map] at hk
  exact hk

theorem not_isUnit_of_mem_map_maximalIdeal (x : AdicCompletion (IsLocalRing.maximalIdeal B) B)
    (hx : x ∈ (IsLocalRing.maximalIdeal B).map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B))) : ¬ IsUnit x := by
  intro hu
  have hker : (IsLocalRing.maximalIdeal B).map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) ≤
      RingHom.ker (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal B) 1).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, AdicCompletion.evalₐ_of, pow_one,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hb
  have h0 := hker hx
  rw [RingHom.mem_ker] at h0
  have h01 : (0 : B ⧸ IsLocalRing.maximalIdeal B ^ 1) = 1 := isUnit_zero_iff.mp (h0 ▸ hu.map _)
  have h1 : (1 : B) ∈ IsLocalRing.maximalIdeal B ^ 1 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]; exact h01.symm
  rw [pow_one] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem eq_zero_of_forall_mem_pow (x : AdicCompletion (IsLocalRing.maximalIdeal B) B)
    (hx : ∀ n, x ∈ (IsLocalRing.maximalIdeal B).map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) ^ n) : x = 0 :=
  IsHausdorff.haus (inferInstance : IsHausdorff ((IsLocalRing.maximalIdeal B).map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B))) _) _
    fun n => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact hx n

theorem exists_ringHom_adicCompletion (c : O →+* B) (hc : ∀ o ∈ IsLocalRing.maximalIdeal O, c o ∈ IsLocalRing.maximalIdeal B) :
    ∃ j : AdicCompletion (IsLocalRing.maximalIdeal O) O →+* AdicCompletion (IsLocalRing.maximalIdeal B) B,
      ∀ o : O, j (algebraMap O _ o) = algebraMap B _ (c o) := by
  set J : Ideal (AdicCompletion (IsLocalRing.maximalIdeal B) B) :=
    (IsLocalRing.maximalIdeal B).map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) with hJ

  have hle : ∀ n : ℕ, IsLocalRing.maximalIdeal O ^ n ≤ (J ^ n).comap ((algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).comp c) := by
    intro n
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    refine Ideal.pow_right_mono ?_ n
    rw [Ideal.map_le_iff_le_comap]
    intro o ho
    rw [Ideal.mem_comap, RingHom.comp_apply, hJ]
    exact Ideal.mem_map_of_mem _ (hc o ho)
  let f : (n : ℕ) → AdicCompletion (IsLocalRing.maximalIdeal O) O →+* AdicCompletion (IsLocalRing.maximalIdeal B) B ⧸ J ^ n :=
    fun n => (Ideal.quotientMap (J ^ n) ((algebraMap B _).comp c) (hle n)).comp (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal O) n).toRingHom
  have hf : ∀ {m n : ℕ} (hmn : m ≤ n), (Ideal.Quotient.factorPow J hmn).comp (f n) = f m := by
    intro m n hmn
    apply RingHom.ext
    intro x
    obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective (IsLocalRing.maximalIdeal O) O x
    simp only [f, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AdicCompletion.evalₐ_mk,
      Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]

    rw [Ideal.Quotient.eq]
    have hs : s.val m - s.val n ∈ IsLocalRing.maximalIdeal O ^ m := by
      have := (s.property hmn)
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
      exact this
    have := hle m (neg_mem hs)
    rw [Ideal.mem_comap, map_neg, map_sub, neg_sub] at this
    exact this
  refine ⟨IsAdicComplete.liftRingHom J f hf, fun o => ?_⟩

  refine (IsHausdorff.eq_iff_smodEq (I := J)).mpr fun n => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom]
  show f n (AdicCompletion.of _ _ o) = _
  simp only [f, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]
end J
end F6Skel
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_coeffSubring_forall_apply_nodeConst_eq_const.F6Skel"

open ModularCurve.UVCrossingModel in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N))
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ})
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π) :
    ∃ τ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) ≃+* W,
      (∀ o : ↥(NodeLocalized.coeffSubring A K), ι (algebraMap _ _ (R.nodeConst K w o)) = const (π ^ E) (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o))) ∧
        τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ ϖ) = π := by
  classical

  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖgen
  have hπE : π ^ E ∈ IsLocalRing.maximalIdeal W :=
    Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit) _ (Nat.pos_of_ne_zero (by omega))
  haveI hRloc : IsLocalRing (UVCrossingModel W (π ^ E)) := F6Core.isLocalRing_uvCrossingModel (π ^ E) hπE
  have hcπ : ¬ IsUnit (const (π ^ E) π) := F6Core.not_isUnit_const (π ^ E) hπE π ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)
  have hϖB : R.nodeConst K w ϖ ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
    refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => hcπ ?_
    rw [← hιϖ]; exact (hu.map _).map ι
  have hc𝔪 : ∀ o ∈ IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K), R.nodeConst K w o ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
    intro o ho
    rw [hϖgen, Ideal.mem_span_singleton'] at ho
    obtain ⟨a, rfl⟩ := ho
    rw [map_mul]; exact Ideal.mul_mem_left _ _ hϖB

  have hqO : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) ∈ IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) := by
    refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_
    have h := hu.map (NodeLocalized.redRestrict red K)
    rw [map_natCast, CharP.cast_eq_zero] at h
    exact not_isUnit_zero h

  obtain ⟨instD₀, instV₀, instC₀, hirr₀⟩ := PowerSeries.isAdicComplete_quotient_span_X_sub_C_of_irreducible ϖ hϖirr
  obtain ⟨e₀, he₀⟩ := PowerSeries.exists_ringEquiv_adicCompletion_quotient_span_X_sub_C ϖ hϖirr

  obtain ⟨j, hj⟩ := F6Skel.exists_ringHom_adicCompletion (R.nodeConst K w) hc𝔪

  let g : (PowerSeries ↥(NodeLocalized.coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K)) - PowerSeries.C ϖ}) →+* UVCrossingModel W (π ^ E) := (ι.toRingHom.comp j).comp e₀.symm.toRingHom
  have hgo : ∀ o : ↥(NodeLocalized.coeffSubring A K), g (Ideal.Quotient.mk _ (PowerSeries.C o)) = ι (algebraMap _ _ (R.nodeConst K w o)) := by
    intro o
    show ι (j (e₀.symm (Ideal.Quotient.mk _ (PowerSeries.C o)))) = _
    rw [← he₀ o, RingEquiv.symm_apply_apply, hj o]
  have hg : g (Ideal.Quotient.mk _ (PowerSeries.C ϖ)) = const (π ^ E) π := by rw [hgo, hιϖ]

  set J : Ideal (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)) := (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)).map (algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))) with hJ
  have hϖJ : algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)) (R.nodeConst K w ϖ) ∈ J := Ideal.mem_map_of_mem _ hϖB
  have hsep : ∀ r : UVCrossingModel W (π ^ E), (∀ n, r ∈ Ideal.span {const (π ^ E) π ^ n}) → r = 0 := by
    intro r hr
    have hmem : ∀ n, ι.symm r ∈ J ^ n := by
      intro n
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hr n)
      rw [← hy, map_mul, map_pow, ← hιϖ, RingEquiv.symm_apply_apply]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hϖJ n)
    have h0 : ι.symm r = 0 := F6Skel.eq_zero_of_forall_mem_pow _ hmem
    simpa using congrArg ι h0
  have hJunit : ∀ x ∈ J, ¬ IsUnit x := fun x hx => F6Skel.not_isUnit_of_mem_map_maximalIdeal x hx

  have hres' : ∀ x : W, ∃ s : (PowerSeries ↥(NodeLocalized.coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K)) - PowerSeries.C ϖ}), ¬ IsUnit (const (π ^ E) x - g s) := by
    intro x
    obtain ⟨bq, hdens⟩ := F6Skel.exists_sub_algebraMap_mem_map (ι.symm (const (π ^ E) x))
    obtain ⟨o, ho⟩ := hres bq
    refine ⟨Ideal.Quotient.mk _ (PowerSeries.C o), fun hu => ?_⟩
    rw [hgo o] at hu
    have hmem : ι.symm (const (π ^ E) x) - algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)) (R.nodeConst K w o) ∈ J := by
      have h2 : algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)) bq - algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)) (R.nodeConst K w o) ∈ J := by
        rw [← map_sub]; exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr ho)
      have := Ideal.add_mem _ hdens h2
      rwa [sub_add_sub_cancel] at this
    refine hJunit _ hmem ?_
    have hu' := hu.map ι.symm
    rwa [map_sub, RingEquiv.symm_apply_apply] at hu'

  have hqA : ((q : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_
    have h := hu.map red
    rw [map_natCast, CharP.cast_eq_zero] at h
    exact not_isUnit_zero h
  haveI hfinO : Finite (IsLocalRing.ResidueField ↥(NodeLocalized.coeffSubring A K)) := ModularCurve.NodeLocalized.finite_residueField_coeffSubring hqA K
  have hϖO : ϖ ∈ IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) := by rw [hϖgen]; exact Ideal.mem_span_singleton_self _
  haveI hfin₀ : Finite (IsLocalRing.ResidueField (PowerSeries ↥(NodeLocalized.coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K)) - PowerSeries.C ϖ})) :=
    F6Skel.finite_residueField_quotient_span_X_sub_C ϖ hϖO
  let cW : ↥(NodeLocalized.coeffSubring A K) →+* (PowerSeries ↥(NodeLocalized.coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K)) - PowerSeries.C ϖ}) := (Ideal.Quotient.mk _).comp (PowerSeries.C (R := ↥(NodeLocalized.coeffSubring A K)))
  have hcWloc : ∀ o ∈ IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K), cW o ∈ IsLocalRing.maximalIdeal (PowerSeries ↥(NodeLocalized.coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K)) - PowerSeries.C ϖ}) := by
    intro o ho
    rw [hϖgen, Ideal.mem_span_singleton'] at ho
    obtain ⟨a, rfl⟩ := ho
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hirr₀.not_isUnit)
  have hq₀ : ((q : ℕ) : (PowerSeries ↥(NodeLocalized.coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K)) - PowerSeries.C ϖ})) ∈ IsLocalRing.maximalIdeal (PowerSeries ↥(NodeLocalized.coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K)) - PowerSeries.C ϖ}) := by
    have := hcWloc _ hqO; rwa [map_natCast] at this
  have hqR : ¬ IsUnit ((q : ℕ) : UVCrossingModel W (π ^ E)) := by
    have h1 : ((q : ℕ) : UVCrossingModel W (π ^ E)) = ι (algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)) (R.nodeConst K w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)))) := by
      rw [map_natCast, map_natCast, map_natCast]
    rw [h1]
    intro hu
    refine hJunit _ (Ideal.mem_map_of_mem _ (hc𝔪 _ hqO)) ?_
    simpa using hu.map ι.symm
  have hqW : ((q : ℕ) : W) ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
    hqR (by have := hu.map (constHom (π ^ E)); rwa [map_natCast] at this)

  haveI : IsLocalHom g := ⟨fun s hs => by
    by_contra hns
    have hmem : s ∈ IsLocalRing.maximalIdeal (PowerSeries ↥(NodeLocalized.coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K)) - PowerSeries.C ϖ}) := (IsLocalRing.mem_maximalIdeal _).mpr hns
    rw [hirr₀.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, rfl⟩ := hmem
    rw [map_mul, hg] at hs
    exact hcπ (isUnit_of_mul_isUnit_right hs)⟩
  haveI : IsLocalHom (constHom (π ^ E) : W →+* UVCrossingModel W (π ^ E)) := ⟨fun x hx => by
    by_contra hnx
    exact F6Core.not_isUnit_const (π ^ E) hπE x ((IsLocalRing.mem_maximalIdeal _).mpr hnx) hx⟩
  haveI hfinR : Finite (IsLocalRing.ResidueField (UVCrossingModel W (π ^ E))) := by
    refine Finite.of_surjective (IsLocalRing.ResidueField.map g) fun y => ?_
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨x, hx⟩ := F6Core.exists_not_isUnit_sub_const' (π ^ E) hπE r
    obtain ⟨s, hs⟩ := hres' x
    refine ⟨IsLocalRing.residue _ s, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have h1 : r - const (π ^ E) x ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).mpr hx
    have h2 : const (π ^ E) x - g s ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).mpr hs
    have := Ideal.add_mem _ h1 h2
    rw [sub_add_sub_cancel] at this
    rw [← neg_sub]; exact neg_mem this
  haveI hfinW : Finite (IsLocalRing.ResidueField W) :=
    Finite.of_injective (IsLocalRing.ResidueField.map (constHom (π ^ E))) (RingHom.injective _)
  obtain ⟨a, b, hb, hab⟩ := F6Skel.exists_pow_card_residueField_eq (S₁ := (PowerSeries ↥(NodeLocalized.coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(NodeLocalized.coeffSubring A K)) - PowerSeries.C ϖ})) (S₂ := W) q hq₀ hqW
  obtain ⟨τ, hτ, hτt⟩ := F6Core.exists_ringEquiv (Ideal.Quotient.mk _ (PowerSeries.C ϖ)) hirr₀ π hπ E hE a b hb hab g hg hsep hres'
  refine ⟨e₀.trans τ, fun o => ?_, ?_⟩
  · rw [RingEquiv.trans_apply, he₀ o, ← hτ, hgo o]
  · rw [RingEquiv.trans_apply, he₀ ϖ, hτt]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_coeffSubring_forall_apply_nodeConst_eq_const
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_coeffSubring_forall_apply_nodeConst_eq_const (solution)
