-- Prove2me | solution 1 for ModularCurve.valuationSubring_eq_of_comap_eq_of_forall_exists_coeffMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d868d9d6-fec9-542e-802e-52459d1724e7

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_valuationSubring_eq_of_comap_eq_of_forall_exists_coeffMap_eq

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
open IsLocalRing ModularCurve

namespace GaussMatchGeneric

section Laurent

variable {κ : Type*} [Field κ]

private theorem orderTop_nonneg_of_mem_adjoin {y : LaurentSeries κ} (hy : 0 < y.orderTop)
    {z : LaurentSeries κ} (hz : z ∈ Algebra.adjoin κ ({y} : Set (LaurentSeries κ))) :
    0 ≤ z.orderTop := by
  induction hz using Algebra.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hy.le
  | algebraMap c =>
    rw [ModularCurve.algebraMap_laurentSeries_eq_single]
    by_cases hc : c = 0
    · simp [hc]
    · rw [HahnSeries.orderTop_single hc]; exact le_rfl
  | add a b _ _ ha hb =>
    exact le_trans (le_min ha hb) HahnSeries.min_orderTop_le_orderTop_add
  | mul a b _ _ ha hb =>
    exact le_trans (add_nonneg ha hb) HahnSeries.orderTop_add_le_mul

private theorem eq_zero_of_isAlgebraic_of_orderTop_pos {y : LaurentSeries κ} (halg : IsAlgebraic κ y)
    (hy : 0 < y.orderTop) : y = 0 := by
  by_contra hy0
  have hint : IsIntegral κ y := halg.isIntegral
  have h0 : (minpoly κ y).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hy0

  have heval : Polynomial.aeval y ((minpoly κ y).divX * Polynomial.X + Polynomial.C ((minpoly κ y).coeff 0)) = 0 := by
    rw [Polynomial.divX_mul_X_add]; exact minpoly.aeval κ y
  rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at heval

  have hz : 0 ≤ (Polynomial.aeval y (minpoly κ y).divX).orderTop :=
    orderTop_nonneg_of_mem_adjoin hy (Polynomial.aeval_mem_adjoin_singleton κ y)
  have hpos : (0 : WithTop ℤ) < (Polynomial.aeval y (minpoly κ y).divX * y).orderTop :=
    lt_of_lt_of_le (lt_of_lt_of_le hy (le_add_of_nonneg_left hz)) HahnSeries.orderTop_add_le_mul
  have hc0 : (Polynomial.aeval y (minpoly κ y).divX * y).coeff 0 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hpos
  have := congrArg (fun w : LaurentSeries κ => w.coeff 0) heval
  simp only [HahnSeries.coeff_add, hc0, zero_add, HahnSeries.coeff_zero] at this
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_same] at this
  exact h0 this

private theorem eq_C_of_isAlgebraic (x : LaurentSeries κ) (halg : IsAlgebraic κ x) :
    x = HahnSeries.C (x.coeff 0) := by
  set y : LaurentSeries κ := x - HahnSeries.C (x.coeff 0) with hydef
  have hyalg : IsAlgebraic κ y := by
    refine halg.sub ?_
    rw [HahnSeries.C_apply, ← ModularCurve.algebraMap_laurentSeries_eq_single]
    exact isAlgebraic_algebraMap (x.coeff 0)
  suffices hy : y = 0 by rwa [hydef, sub_eq_zero] at hy
  by_contra hy0
  have hy00 : y.coeff 0 = 0 := by simp [hydef]
  have hord : y.order ≠ 0 := fun h => hy0 (HahnSeries.coeff_order_eq_zero.mp (h ▸ hy00))
  rcases lt_or_gt_of_ne hord with hneg | hpos
  ·
    have hinv0 : y⁻¹ ≠ 0 := inv_ne_zero hy0
    have hordinv : 0 < y⁻¹.orderTop := by
      have h1 := HahnSeries.order_mul hy0 hinv0
      rw [mul_inv_cancel₀ hy0, HahnSeries.order_one] at h1
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hinv0, WithTop.coe_pos]
      omega
    exact hinv0 (eq_zero_of_isAlgebraic_of_orderTop_pos hyalg.inv hordinv)
  · have : 0 < y.orderTop := by
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hy0, WithTop.coe_pos]
      exact hpos
    exact hy0 (eq_zero_of_isAlgebraic_of_orderTop_pos hyalg this)

end Laurent

section Val

variable {L : Type*} [Field L]

private theorem eq_of_le_of_forall_nonunit_div {W W' : ValuationSubring L} (hle : W ≤ W') {ϖ : L} (hϖ0 : ϖ ≠ 0)
    (hϖ : ϖ ∈ W'.nonunits) (hdiv : ∀ f ∈ W.nonunits, (f : L) * ϖ⁻¹ ∈ W) : W = W' := by
  refine le_antisymm hle fun f hf => ?_
  by_contra hfW
  have hfi : f⁻¹ ∈ W := (W.mem_or_inv_mem f).resolve_left hfW
  have hf0 : f ≠ 0 := by rintro rfl; exact hfW W.zero_mem
  have hnu : f⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr hfW)
  have h1 : f⁻¹ * ϖ⁻¹ ∈ W' := hle (hdiv _ hnu)
  have h2 : ϖ⁻¹ ∈ W' := by
    have := W'.mul_mem _ _ hf h1
    rwa [← mul_assoc, mul_inv_cancel₀ hf0, one_mul] at this
  rcases W'.mem_nonunits_iff_or.mp hϖ with h | h
  · exact hϖ0 h
  · exact h h2

private theorem eq_of_le_of_forall_exists_pow_mul {W W' : ValuationSubring L} (hle : W ≤ W') {ϖ : L} (hϖ0 : ϖ ≠ 0)
    (hϖ : ϖ ∈ W'.nonunits)
    (hdisc : ∀ g ∈ W, g ≠ 0 → ∃ n : ℕ, ∃ u ∈ W, u⁻¹ ∈ W ∧ g = ϖ ^ n * u) : W = W' := by
  refine le_antisymm hle fun g hg => ?_
  by_contra hgW
  have hgi : g⁻¹ ∈ W := (W.mem_or_inv_mem g).resolve_left hgW
  have hg0 : g ≠ 0 := by rintro rfl; exact hgW W.zero_mem
  obtain ⟨n, u, hu, hui, hgu⟩ := hdisc _ hgi (inv_ne_zero hg0)
  have hu0 : u ≠ 0 := by rintro rfl; exact inv_ne_zero hg0 (by simpa using hgu)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, one_mul] at hgu
    apply hgW
    have : g = u⁻¹ := by rw [← inv_inv g, hgu]
    rwa [this]
  ·
    have hϖn : (ϖ ^ n)⁻¹ = u * g := by
      have : ϖ ^ n = g⁻¹ * u⁻¹ := by rw [hgu, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
      rw [this, mul_inv, inv_inv, inv_inv, mul_comm]
    have hmem : (ϖ ^ n)⁻¹ ∈ W' := by rw [hϖn]; exact W'.mul_mem _ _ (hle hu) hg
    have h2 : ϖ⁻¹ ∈ W' := by
      have : ϖ⁻¹ = ϖ ^ (n - 1) * (ϖ ^ n)⁻¹ := by
        rw [← pow_sub_one_mul (Nat.pos_iff_ne_zero.mp hn) ϖ, mul_inv, ← mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ hϖ0), one_mul]
      rw [this]
      exact W'.mul_mem _ _ (W'.pow_mem (W'.nonunits_subset hϖ) _) hmem
    rcases W'.mem_nonunits_iff_or.mp hϖ with h | h
    · exact hϖ0 h
    · exact h h2

private theorem mul_mem_nonunits {W : ValuationSubring L} {ϖ : L} (hϖ : ϖ ∈ W.nonunits) {u : L} (hu : u ∈ W) :
    ϖ * u ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hϖ ⊢
  rw [map_mul]
  calc W.valuation ϖ * W.valuation u ≤ W.valuation ϖ * 1 :=
        mul_le_mul_right ((W.valuation_le_one_iff u).mpr hu) _
    _ < 1 := by rwa [mul_one]

private theorem inv_one_add_mem {W : ValuationSubring L} {x : L} (hx : x ∈ W.nonunits) :
    (1 + x)⁻¹ ∈ W ∧ 1 + x ≠ 0 := by
  have hxW : x ∈ W := W.nonunits_subset hx
  have hmax : (⟨x, hxW⟩ : W) ∈ IsLocalRing.maximalIdeal W := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hx
  have hunit : IsUnit ((1 : W) + ⟨x, hxW⟩) := by
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(⟨x, hxW⟩ : W))
      ((IsLocalRing.maximalIdeal W).neg_mem hmax)
    rwa [sub_neg_eq_add] at this
  obtain ⟨z, hz⟩ := hunit.exists_right_inv
  have hzL : (1 + x) * (z : L) = 1 := by
    have := congrArg (fun w : W => (w : L)) hz
    simpa using this
  have hne : (1 + x) ≠ 0 := fun h => by simp [h] at hzL
  refine ⟨?_, hne⟩
  have : (1 + x)⁻¹ = (z : L) := (eq_inv_of_mul_eq_one_right hzL).symm
  rw [this]; exact z.2

private theorem eq_of_forall_mem_or_dvd {𝒱 𝒲 : ValuationSubring L} {ϖ : L} (hϖ0 : ϖ ≠ 0)
    (hϖ𝒱 : ϖ ∈ 𝒱.nonunits) (hϖ𝒲 : ϖ ∈ 𝒲.nonunits)
    (hdisc : ∀ g ∈ 𝒱, g ≠ 0 → ∃ n : ℕ, ∃ u ∈ 𝒱, u⁻¹ ∈ 𝒱 ∧ g = ϖ ^ n * u)
    (S : Set L) (hS𝒱 : S ⊆ 𝒱) (hS𝒲 : S ⊆ 𝒲)
    (hfield : ∀ s ∈ S, (∃ t ∈ S, ∃ u ∈ S, s * t = 1 + ϖ * u) ∨ (∃ t ∈ S, s = ϖ * t))
    (hfrac : ∀ g : L, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ g = a / b) :
    𝒱 = 𝒲 := by
  have hϖi𝒱 : ϖ⁻¹ ∉ 𝒱 := fun h => (𝒱.mem_nonunits_iff_or.mp hϖ𝒱).elim hϖ0 fun h' => h' h

  have hunit : ∀ b' ∈ S, (∃ t ∈ S, ∃ u ∈ S, b' * t = 1 + ϖ * u) → b'⁻¹ ∈ 𝒱 ∧ b'⁻¹ ∈ 𝒲 ∧ b' ≠ 0 := by
    rintro b' hb' ⟨t, ht, u, hu, h⟩
    obtain ⟨h𝒱, hne⟩ := inv_one_add_mem (mul_mem_nonunits hϖ𝒱 (hS𝒱 hu))
    obtain ⟨h𝒲, -⟩ := inv_one_add_mem (mul_mem_nonunits hϖ𝒲 (hS𝒲 hu))
    have hb0 : b' ≠ 0 := by rintro rfl; rw [zero_mul] at h; exact hne h.symm
    have ht0 : t ≠ 0 := by rintro rfl; rw [mul_zero] at h; exact hne h.symm
    have hinv : b'⁻¹ = t * (1 + ϖ * u)⁻¹ := by
      rw [← h, mul_inv, mul_left_comm, mul_inv_cancel₀ ht0, mul_one]
    refine ⟨?_, ?_, hb0⟩
    · rw [hinv]; exact 𝒱.mul_mem _ _ (hS𝒱 ht) h𝒱
    · rw [hinv]; exact 𝒲.mul_mem _ _ (hS𝒲 ht) h𝒲

  have hred : ∀ (N : ℕ) (b : L), b ∈ S → b ≠ 0 → (∃ u ∈ 𝒱, u⁻¹ ∈ 𝒱 ∧ b = ϖ ^ N * u) →
      ∃ n : ℕ, ∃ b' ∈ S, b = ϖ ^ n * b' ∧ ∃ t ∈ S, ∃ u ∈ S, b' * t = 1 + ϖ * u := by
    intro N
    induction N with
    | zero =>
      rintro b hb hb0 ⟨u, hu, hui, hbu⟩
      rw [pow_zero, one_mul] at hbu
      subst hbu
      rcases hfield b hb with h | ⟨t, ht, rfl⟩
      · exact ⟨0, b, hb, by rw [pow_zero, one_mul], h⟩
      · exfalso
        rcases 𝒱.mem_nonunits_iff_or.mp (mul_mem_nonunits hϖ𝒱 (hS𝒱 ht)) with h | h
        · exact hb0 h
        · exact h hui
    | succ M ih =>
      rintro b hb hb0 ⟨u, hu, hui, hbu⟩
      rcases hfield b hb with h | ⟨t, ht, rfl⟩
      · exact ⟨0, b, hb, by rw [pow_zero, one_mul], h⟩
      · have ht0 : t ≠ 0 := by rintro rfl; exact hb0 (mul_zero ϖ)
        have htu : t = ϖ ^ M * u := by
          apply mul_left_cancel₀ hϖ0
          rw [hbu, pow_succ]; ring
        obtain ⟨n, b', hb', htb', hunit'⟩ := ih t ht ht0 ⟨u, hu, hui, htu⟩
        refine ⟨n + 1, b', hb', ?_, hunit'⟩
        rw [htb', pow_succ]; ring

  have hle : 𝒱 ≤ 𝒲 := by
    intro g hg
    obtain ⟨a, ha, b, hb, hb0, rfl⟩ := hfrac g
    by_cases ha0 : a = 0
    · rw [ha0, zero_div]; exact 𝒲.zero_mem
    obtain ⟨Na, ua, hua, huai, haua⟩ := hdisc a (hS𝒱 ha) ha0
    obtain ⟨Nb, ub, hub, hubi, hbub⟩ := hdisc b (hS𝒱 hb) hb0
    obtain ⟨m, a', ha', haa', hunita⟩ := hred Na a ha ha0 ⟨ua, hua, huai, haua⟩
    obtain ⟨n, b', hb', hbb', hunitb⟩ := hred Nb b hb hb0 ⟨ub, hub, hubi, hbub⟩
    obtain ⟨ha'𝒱, ha'𝒲, ha'0⟩ := hunit a' ha' hunita
    obtain ⟨hb'𝒱, hb'𝒲, hb'0⟩ := hunit b' hb' hunitb
    rcases le_or_gt n m with hnm | hmn
    ·
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
      have : a / b = ϖ ^ d * a' * b'⁻¹ := by
        rw [haa', hbb', div_eq_iff (mul_ne_zero (pow_ne_zero _ hϖ0) hb'0)]
        field_simp
        ring
      rw [this]
      exact 𝒲.mul_mem _ _ (𝒲.mul_mem _ _ (𝒲.pow_mem (𝒲.nonunits_subset hϖ𝒲) _) (hS𝒲 ha')) hb'𝒲
    ·
      exfalso
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
      apply hϖi𝒱
      have hϖinv : ϖ⁻¹ = ϖ ^ d * ((a / b) * b' * a'⁻¹) := by
        rw [haa', hbb']
        field_simp
        ring
      rw [hϖinv]
      exact 𝒱.mul_mem _ _ (𝒱.pow_mem (𝒱.nonunits_subset hϖ𝒱) _)
        (𝒱.mul_mem _ _ (𝒱.mul_mem _ _ hg (hS𝒱 hb')) ha'𝒱)

  exact eq_of_le_of_forall_exists_pow_mul hle hϖ0 hϖ𝒲 hdisc

end Val

section Alg

open Polynomial

private theorem exists_map_ne_zero_and_aeval_eq_zero {O : Type*} [CommRing O] [IsDomain O]
    (ιO : O →+* AlgebraicClosure ℚ) (hι : Function.Injective ιO) (p : ℕ) [Fact p.Prime] (a : O) :
    ∃ Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧ Polynomial.aeval a Q = 0 := by

  have halgQ : IsAlgebraic ℚ (ιO a) := by
    have h := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic (ιO a)
    convert h <;> first | rfl | exact Subsingleton.elim _ _
  have halgZ : IsAlgebraic ℤ (ιO a) := (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr halgQ
  obtain ⟨Q₀, hQ₀, hroot⟩ := halgZ
  refine ⟨Q₀.primPart, ?_, ?_⟩
  · intro hmap
    have hdvd : Polynomial.C ((p : ℕ) : ℤ) ∣ Q₀.primPart := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have := congrArg (fun q : Polynomial (ZMod p) => q.coeff i) hmap
      simp only [Polynomial.coeff_map, eq_intCast, Polynomial.coeff_zero] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
    have hunit := Q₀.isPrimitive_primPart _ hdvd
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hunit
    exact (Fact.out : p.Prime).one_lt.ne' hunit
  · rw [Polynomial.aeval_def] at hroot
    have h1 : Polynomial.eval₂ (algebraMap ℤ (AlgebraicClosure ℚ)) (ιO a) Q₀.primPart = 0 :=
      Polynomial.eval₂_primPart_eq_zero (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int hQ₀ hroot
    apply hι
    rw [map_zero, ← h1, Polynomial.aeval_def, Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _

end Alg

section LD

open Polynomial ModularCurve

private theorem irreducible_map_of_forall_exists_coeffMap {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] (ι₀ : ZMod p →+* k) {K : Type*} [Field K] (ιK : ZMod p →+* K)
    (ρ : K →+* LaurentSeries k)
    (hρ : ∀ e : K, ∃ y : LaurentSeries (ZMod p), coeffMap ι₀ y = ρ e)
    {m : Polynomial (ZMod p)} (hm : Irreducible m) (hmo : m.Monic) :
    Irreducible (m.map ιK) := by

  letI alg : Algebra (ZMod p) (LaurentSeries k) :=
    ((coeffMap ι₀).comp (algebraMap (ZMod p) (LaurentSeries (ZMod p)))).toAlgebra
  let cm : LaurentSeries (ZMod p) →ₐ[ZMod p] LaurentSeries k :=
    { coeffMap ι₀ with commutes' := fun c => rfl }
  have hcm_inj : Function.Injective cm := by
    intro x y h
    ext n
    have := congrArg (fun z : LaurentSeries k => z.coeff n) h
    exact ι₀.injective (by simpa [cm] using this)
  have halg : (algebraMap (ZMod p) (LaurentSeries k)) = ρ.comp ιK := RingHom.ext_zmod _ _

  have hm1 : m.map ιK ≠ 1 := by
    intro h
    have hdeg := congrArg Polynomial.natDegree h
    rw [hmo.natDegree_map, Polynomial.natDegree_one] at hdeg
    have := Polynomial.degree_pos_of_irreducible hm
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, hdeg] at this
    exact lt_irrefl _ (by exact_mod_cast this)
  rw [Polynomial.irreducible_of_monic (hmo.map ιK) hm1]
  intro f g hf hg hfg

  have hdvd : f.map ρ ∣ m.map (algebraMap (ZMod p) (LaurentSeries k)) := by
    rw [halg, ← Polynomial.map_map, ← hfg, Polynomial.map_mul]
    exact dvd_mul_right _ _
  have hint : ∀ i, IsIntegral (ZMod p) ((f.map ρ).coeff i) :=
    Polynomial.isIntegral_coeff_of_dvd m (f.map ρ) hmo (hf.map ρ) hdvd

  have hlift : f.map ρ ∈ Polynomial.lifts (algebraMap (ZMod p) (LaurentSeries k)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    obtain ⟨y, hy⟩ := hρ (f.coeff i)
    have hyint : IsIntegral (ZMod p) y := by
      rw [← isIntegral_algHom_iff cm hcm_inj]
      have : cm y = (f.map ρ).coeff i := by rw [Polynomial.coeff_map, ← hy]; rfl
      rw [this]; exact hint i
    have hyC := eq_C_of_isAlgebraic y hyint.isAlgebraic
    refine ⟨y.coeff 0, ?_⟩
    rw [Polynomial.coeff_map, ← hy]
    conv_rhs => rw [hyC]
    change coeffMap ι₀ (algebraMap (ZMod p) (LaurentSeries (ZMod p)) (y.coeff 0)) = coeffMap ι₀ (HahnSeries.C (y.coeff 0))
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  obtain ⟨f₀, hf₀, hdegf₀, hf₀mo⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hf.map ρ)
  have hf₀dvd : f₀ ∣ m := by
    rw [← Polynomial.map_dvd_map (algebraMap (ZMod p) (LaurentSeries k))
      (algebraMap (ZMod p) (LaurentSeries k)).injective hf₀mo, hf₀]
    exact hdvd
  obtain ⟨r, hr⟩ := hf₀dvd
  have hdegf : f.natDegree = f₀.natDegree := by
    rw [hdegf₀, Polynomial.natDegree_map_eq_of_injective ρ.injective]
  rcases hm.isUnit_or_isUnit hr with hu | hu
  · left
    have h0 : f₀.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    exact Polynomial.eq_one_of_monic_natDegree_zero hf (hdegf.trans h0)
  · right
    have hr0 : r.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdegm : m.natDegree = f₀.natDegree := by
      rw [hr, Polynomial.natDegree_mul hf₀mo.ne_zero (fun h => by simp [h] at hu), hr0, add_zero]

    have hdeg2 := congrArg Polynomial.natDegree hfg
    rw [Polynomial.natDegree_mul hf.ne_zero hg.ne_zero, hmo.natDegree_map, hdegm, ← hdegf] at hdeg2
    exact Polynomial.eq_one_of_monic_natDegree_zero hg (by omega)

end LD

end GaussMatchGeneric

open ModularCurve Polynomial
open GaussMatchGeneric

set_option maxHeartbeats 6400000 in

theorem solution (p : ℕ) [Fact p.Prime]
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (ιO : O →+* AlgebraicClosure ℚ)
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k p] (red : A →+* k)
    (hιA : ∀ a : O, ιO a ∈ A)
    {F : Type*} [Field F] {L : Type*} [Field L] (θO : O →+* L) (θF : F →+* L)
    (hgen : Subfield.closure (Set.range θF ∪ Set.range θO) = ⊤)
    (𝒱 𝒲 : ValuationSubring L) (hpL : ((p : ℕ) : L) ≠ 0)
    (hp𝒱 : ((p : ℕ) : L) ∈ 𝒱.nonunits) (hp𝒲 : ((p : ℕ) : L) ∈ 𝒲.nonunits)
    (hdisc : ∀ g ∈ 𝒱, g ≠ 0 → ∃ n : ℕ, ∃ u ∈ 𝒱, u⁻¹ ∈ 𝒱 ∧ g = ((p : ℕ) : L) ^ n * u)
    (hO𝒱 : ∀ a, θO a ∈ 𝒱) (hO𝒲 : ∀ a, θO a ∈ 𝒲)
    (htr : 𝒱.comap θF = 𝒲.comap θF)
    (hpt : ((p : ℕ) : F) ∈ (𝒱.comap θF).nonunits)
    (hdivt : ∀ f ∈ (𝒱.comap θF).nonunits, f * ((p : ℕ) : F)⁻¹ ∈ 𝒱.comap θF)
    (ρ : ↥𝒲 →+* LaurentSeries k)
    (hker : ∀ g : ↥𝒲, ρ g = 0 ↔ (g : L) ∈ 𝒲.nonunits)
    (hρO : ∀ a, ρ ⟨θO a, hO𝒲 a⟩ = HahnSeries.C (red ⟨ιO a, hιA a⟩))
    (hρF : ∀ (f : F) (h : θF f ∈ 𝒲), ∃ y : LaurentSeries (ZMod p),
      coeffMap (ZMod.castHom (dvd_refl p) k) y = ρ ⟨θF f, h⟩) :
    𝒱 = 𝒲 := by
  classical
  set ι₀ : ZMod p →+* k := ZMod.castHom (dvd_refl p) k with hι₀

  have hirr : Irreducible ((p : ℕ) : O) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hϖ
  have hιinj : Function.Injective ιO := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hirr
    rw [map_mul, map_pow, map_natCast] at hx
    exact mul_ne_zero (u.isUnit.map ιO).ne_zero (pow_ne_zero _ (NeZero.ne _)) hx
  let redO : O →+* k := red.comp (ιO.codRestrict A hιA)
  have hredO : ∀ a, redO a = red ⟨ιO a, hιA a⟩ := fun a => rfl
  have hredOp : redO p = 0 := by
    have : ((p : ℕ) : k) = 0 := CharP.cast_eq_zero k p
    rw [← this, map_natCast]
  have hpO : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by rw [hϖ]; exact Ideal.mem_span_singleton_self _
  have hmemO : ∀ a : O, a ∈ IsLocalRing.maximalIdeal O ↔ ∃ c, a = p * c := fun a => by
    rw [hϖ, Ideal.mem_span_singleton']
    exact ⟨fun ⟨c, hc⟩ => ⟨c, by rw [← hc, mul_comm]⟩, fun ⟨c, hc⟩ => ⟨c, by rw [hc, mul_comm]⟩⟩

  haveI : CharP (IsLocalRing.ResidueField O) p := by
    rw [CharP.charP_iff_prime_eq_zero]
    · rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
      exact hpO
    · exact Fact.out
  letI algO : Algebra (ZMod p) (IsLocalRing.ResidueField O) := ZMod.algebra _ p
  have hσ : ∀ a ∈ IsLocalRing.maximalIdeal O, redO a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := (hmemO a).mp ha
    rw [map_mul, hredOp, zero_mul]
  let σ : IsLocalRing.ResidueField O →+* k := Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) redO hσ
  have hσres : ∀ a, σ (IsLocalRing.residue O a) = redO a := fun a => Ideal.Quotient.lift_mk _ _ _
  have hσalg : σ.comp (algebraMap (ZMod p) (IsLocalRing.ResidueField O)) = ι₀ := RingHom.ext_zmod _ _

  have hintO : ∀ a : O, IsIntegral (ZMod p) (IsLocalRing.residue O a) := by
    intro a
    obtain ⟨Q, hQ0, hQa⟩ := exists_map_ne_zero_and_aeval_eq_zero ιO hιinj p a
    refine (IsAlgebraic.isIntegral ⟨Q.map (Int.castRingHom (ZMod p)), hQ0, ?_⟩)
    have hc : (algebraMap (ZMod p) (IsLocalRing.ResidueField O)).comp (Int.castRingHom (ZMod p)) =
        (IsLocalRing.residue O).comp (algebraMap ℤ O) := RingHom.ext_int _ _
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hQa, map_zero]

  obtain ⟨Wt, hWt⟩ : ∃ W : ValuationSubring F, W = 𝒱.comap θF := ⟨_, rfl⟩
  rw [← hWt] at hpt hdivt
  have hWt𝒲 : Wt = 𝒲.comap θF := hWt.trans htr
  have hmemWt𝒱 : ∀ f : F, f ∈ Wt ↔ θF f ∈ 𝒱 := fun f => by rw [hWt, ValuationSubring.mem_comap]
  have hmemWt𝒲 : ∀ f : F, f ∈ Wt ↔ θF f ∈ 𝒲 := fun f => by rw [hWt𝒲, ValuationSubring.mem_comap]
  have hpWt : ((p : ℕ) : F) ∈ Wt := Wt.nonunits_subset hpt
  have hpF0 : ((p : ℕ) : F) ≠ 0 := fun h => hpL (by rw [← map_natCast θF, h, map_zero])

  have hnuWt : ∀ f : F, f ∈ Wt.nonunits ↔ θF f ∈ 𝒲.nonunits := fun f => by
    rw [Wt.mem_nonunits_iff_or, 𝒲.mem_nonunits_iff_or, map_eq_zero_iff θF θF.injective, ← map_inv₀, ← hmemWt𝒲]

  have hmaxWt : ∀ w : ↥Wt, w ∈ IsLocalRing.maximalIdeal ↥Wt ↔ ∃ v : ↥Wt, w = (p : ↥Wt) * v := by
    intro w
    constructor
    · intro hw
      rw [← ValuationSubring.coe_mem_nonunits_iff] at hw
      refine ⟨⟨(w : F) * ((p : ℕ) : F)⁻¹, hdivt _ hw⟩, Subtype.ext ?_⟩
      push_cast
      rw [mul_left_comm, mul_inv_cancel₀ hpF0, mul_one]
    · rintro ⟨v, rfl⟩
      apply Ideal.mul_mem_right
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      push_cast
      exact hpt

  let τ : ↥Wt →+* ↥𝒲 := θF.restrict Wt 𝒲 fun f hf => (hmemWt𝒲 f).mp hf
  have hτ : ∀ w : ↥Wt, (τ w : L) = θF w := fun w => RingHom.coe_restrict_apply _ _ _ _ w
  let τL : ↥Wt →+* L := θF.comp Wt.subtype
  have hτL : ∀ w : ↥Wt, τL w = θF w := fun w => rfl
  have hτL' : (𝒲.subtype).comp τ = τL := RingHom.ext fun w => hτ w
  let ρW : ↥Wt →+* LaurentSeries k := ρ.comp τ
  have hρW : ∀ w, ρW w = ρ (τ w) := fun w => rfl
  have hkerW : ∀ w : ↥Wt, ρW w = 0 ↔ w ∈ IsLocalRing.maximalIdeal ↥Wt := fun w => by
    rw [hρW, hker, hτ, ← hnuWt, ValuationSubring.coe_mem_nonunits_iff]

  haveI : CharP (IsLocalRing.ResidueField ↥Wt) p := by
    rw [CharP.charP_iff_prime_eq_zero]
    · rw [← map_natCast (IsLocalRing.residue ↥Wt), IsLocalRing.residue_eq_zero_iff, hmaxWt]
      exact ⟨1, by rw [mul_one]⟩
    · exact Fact.out
  let ιK : ZMod p →+* IsLocalRing.ResidueField ↥Wt := ZMod.castHom (dvd_refl p) _
  let ρK : IsLocalRing.ResidueField ↥Wt →+* LaurentSeries k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥Wt) ρW fun w hw => (hkerW w).mpr hw
  have hρK : ∀ w, ρK (IsLocalRing.residue ↥Wt w) = ρW w := fun w => Ideal.Quotient.lift_mk _ _ _
  have hρKres : ρK.comp (IsLocalRing.residue ↥Wt) = ρW := RingHom.ext hρK
  have hρKrat : ∀ e : IsLocalRing.ResidueField ↥Wt, ∃ y : LaurentSeries (ZMod p), coeffMap ι₀ y = ρK e := by
    intro e
    obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective e
    obtain ⟨y, hy⟩ := hρF (w : F) ((hmemWt𝒲 _).mp w.2)
    refine ⟨y, ?_⟩
    rw [hy, hρK, hρW]
    congr 1
  have hρKι : ρK.comp ιK = (HahnSeries.C : k →+* LaurentSeries k).comp ι₀ := RingHom.ext_zmod _ _

  let Ψ : TensorProduct ℤ ↥Wt O →ₐ[ℤ] L :=
    Algebra.TensorProduct.lift τL.toIntAlgHom θO.toIntAlgHom fun x y => Commute.all _ _
  have hΨ : ∀ (w : ↥Wt) (a : O), Ψ (w ⊗ₜ a) = θF w * θO a := fun w a =>
    Algebra.TensorProduct.lift_tmul _ _ _ w a
  set S : Set L := Set.range Ψ with hSdef
  have hSΨ : ∀ t, Ψ t ∈ S := fun t => ⟨t, rfl⟩
  have hSsub : S = (Ψ.range.toSubring : Set L) := by rw [hSdef]; rfl
  have hS0 : (0 : L) ∈ S := ⟨0, map_zero Ψ⟩
  have hSadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x + y, map_add Ψ x y⟩
  have hSmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, map_mul Ψ x y⟩
  have hSsub' : ∀ a ∈ S, ∀ b ∈ S, a - b ∈ S := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x - y, map_sub Ψ x y⟩
  have hSθF : ∀ w : ↥Wt, θF w ∈ S := fun w => ⟨w ⊗ₜ 1, by rw [hΨ, map_one, mul_one]⟩
  have hSθO : ∀ a : O, θO a ∈ S := fun a => ⟨1 ⊗ₜ a, by rw [hΨ, OneMemClass.coe_one, map_one, one_mul]⟩
  have hSp : ((p : ℕ) : L) ∈ S := by rw [← map_natCast θO]; exact hSθO _
  have hS𝒱 : S ⊆ 𝒱 := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact 𝒱.zero_mem
    | tmul w a => rw [hΨ]; exact 𝒱.mul_mem _ _ ((hmemWt𝒱 _).mp w.2) (hO𝒱 a)
    | add x y hx hy => rw [map_add]; exact 𝒱.add_mem _ _ hx hy
  have hS𝒲 : S ⊆ 𝒲 := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact 𝒲.zero_mem
    | tmul w a => rw [hΨ]; exact 𝒲.mul_mem _ _ ((hmemWt𝒲 _).mp w.2) (hO𝒲 a)
    | add x y hx hy => rw [map_add]; exact 𝒲.add_mem _ _ hx hy

  have hclS : Subfield.closure S = ⊤ := by
    rw [eq_top_iff, ← hgen, Subfield.closure_le]
    rintro _ (⟨f, rfl⟩ | ⟨a, rfl⟩)
    · rcases Wt.mem_or_inv_mem f with hf | hf
      · exact Subfield.subset_closure (hSθF ⟨f, hf⟩)
      · have : θF f = (θF f⁻¹)⁻¹ := by rw [map_inv₀, inv_inv]
        rw [this]
        exact inv_mem (Subfield.subset_closure (hSθF ⟨f⁻¹, hf⟩))
    · exact Subfield.subset_closure (hSθO a)
  have hfrac : ∀ g : L, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ g = a / b := by
    intro g
    have hg : g ∈ Subfield.closure S := by rw [hclS]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp hg
    have hcl : Subring.closure S ≤ Ψ.range.toSubring := by rw [Subring.closure_le, hSsub]
    have hy' : y ∈ S := by rw [hSsub]; exact hcl hy
    have hz' : z ∈ S := by rw [hSsub]; exact hcl hz
    by_cases hz0 : z = 0
    · refine ⟨0, hS0, 1, ?_, one_ne_zero, by rw [hz0, div_zero, zero_div]⟩
      rw [← map_one θO]; exact hSθO 1
    · exact ⟨y, hy', z, hz', hz0, rfl⟩

  have hfield : ∀ s ∈ S, (∃ t ∈ S, ∃ u ∈ S, s * t = 1 + p * u) ∨ (∃ t ∈ S, s = p * t) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨T, hT⟩ := TensorProduct.exists_finset t

    have hQ : ∃ b : O, ∀ i ∈ T, ∃ Qz : Polynomial ℤ,
        IsLocalRing.residue O i.2 = IsLocalRing.residue O (Polynomial.aeval b Qz) := by
      let E : IntermediateField (ZMod p) (IsLocalRing.ResidueField O) :=
        IntermediateField.adjoin (ZMod p) (↑(T.image fun i => IsLocalRing.residue O i.2) : Set (IsLocalRing.ResidueField O))
      haveI : FiniteDimensional (ZMod p) E := by
        apply IntermediateField.finiteDimensional_adjoin
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
        exact hintO i.2
      haveI : Algebra.IsSeparable (ZMod p) E := Algebra.IsAlgebraic.isSeparable_of_perfectField
      obtain ⟨α, hα⟩ := Field.exists_primitive_element (ZMod p) E
      obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective (α : IsLocalRing.ResidueField O)
      have halgα : IsAlgebraic (ZMod p) α := Algebra.IsAlgebraic.isAlgebraic α
      refine ⟨b, fun i hi => ?_⟩
      have hxE : IsLocalRing.residue O i.2 ∈ E :=
        IntermediateField.subset_adjoin _ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hi))
      have hxtop : (⟨_, hxE⟩ : E) ∈ (⊤ : IntermediateField (ZMod p) E) := IntermediateField.mem_top
      rw [← hα, ← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halgα,
        Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hxtop
      obtain ⟨Qp, hQp⟩ := hxtop
      obtain ⟨Qz, rfl⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective Qp
      refine ⟨Qz, ?_⟩
      have h1 := congrArg (fun e : E => (e : IsLocalRing.ResidueField O)) hQp
      simp only at h1
      rw [← IntermediateField.coe_val, ← Polynomial.aeval_algHom_apply, IntermediateField.coe_val] at h1
      change Polynomial.aeval (α : IsLocalRing.ResidueField O) (Qz.map (Int.castRingHom (ZMod p))) = IsLocalRing.residue O i.2 at h1
      rw [← h1, ← hb]
      have hc : (algebraMap (ZMod p) (IsLocalRing.ResidueField O)).comp (Int.castRingHom (ZMod p)) =
          (IsLocalRing.residue O).comp (algebraMap ℤ O) := RingHom.ext_int _ _
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def]
    obtain ⟨b, hQ⟩ := hQ
    choose! Q hQ using hQ
    have hc : ∀ i ∈ T, ∃ c : O, i.2 = Polynomial.aeval b (Q i) + p * c := by
      intro i hi
      have : i.2 - Polynomial.aeval b (Q i) ∈ IsLocalRing.maximalIdeal O := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]; exact hQ i hi
      obtain ⟨c, hc⟩ := (hmemO _).mp this
      exact ⟨c, by rw [← hc, add_sub_cancel]⟩
    choose! c hc using hc

    have hintb := hintO b
    obtain ⟨m, hmmap, -, hmmo⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      ((Polynomial.mem_lifts _).mpr (Polynomial.map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective _))
      (minpoly.monic hintb)
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : O, Polynomial.aeval b m = p * c₀ := by
      apply (hmemO _).mp
      rw [← IsLocalRing.residue_eq_zero_iff]
      have hc : (algebraMap (ZMod p) (IsLocalRing.ResidueField O)).comp (Int.castRingHom (ZMod p)) =
          (IsLocalRing.residue O).comp (algebraMap ℤ O) := RingHom.ext_int _ _
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, ← hc, ← Polynomial.eval₂_map, hmmap, ← Polynomial.aeval_def]
      exact minpoly.aeval _ _

    let ev : Polynomial ↥Wt →+* L := Polynomial.eval₂RingHom τL (θO b)
    have hev : ∀ H, ev H = Polynomial.eval₂ τL (θO b) H := fun H => rfl
    have hevC : ∀ w : ↥Wt, ev (Polynomial.C w) = θF w := fun w => by rw [hev, Polynomial.eval₂_C]; rfl
    have hevX : ev Polynomial.X = θO b := by rw [hev, Polynomial.eval₂_X]
    have hevS : ∀ H, ev H ∈ S := by
      intro H
      induction H using Polynomial.induction_on with
      | C a => rw [hevC]; exact hSθF a
      | add P Q hP hQ => rw [map_add]; exact hSadd _ hP _ hQ
      | monomial n a h => rw [pow_succ, ← mul_assoc, map_mul, hevX]; exact hSmul _ h _ (hSθO b)
    have hevmap : ∀ Qz : Polynomial ℤ, ev (Qz.map (Int.castRingHom ↥Wt)) = θO (Polynomial.aeval b Qz) := by
      intro Qz
      have h1 : τL.comp (Int.castRingHom ↥Wt) = θO.comp (algebraMap ℤ O) := RingHom.ext_int _ _
      rw [hev, Polynomial.eval₂_map, h1, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def]
    have hevp : ev (Polynomial.C (p : ↥Wt)) = p := by
      rw [hevC, show ((p : ↥Wt) : F) = p by push_cast; rfl, map_natCast]

    let G : Polynomial ↥Wt := ∑ i ∈ T, Polynomial.C i.1 * (Q i).map (Int.castRingHom ↥Wt)
    let s₁ : L := Ψ (∑ i ∈ T, i.1 ⊗ₜ c i)
    have hs₁ : s₁ = ∑ i ∈ T, θF i.1 * θO (c i) := by
      change Ψ _ = _; rw [map_sum]; exact Finset.sum_congr rfl fun i _ => hΨ _ _
    have hs₁S : s₁ ∈ S := hSΨ _
    have hevG : ev G = ∑ i ∈ T, θF i.1 * θO (Polynomial.aeval b (Q i)) := by
      change ev (∑ i ∈ T, _) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hevC, hevmap]
    have hsG : Ψ t = ev G + p * s₁ := by
      rw [hT, map_sum, hevG, hs₁, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hΨ, hc i hi, map_add, map_mul, map_natCast]
      ring

    let ev𝒲 : Polynomial ↥Wt →+* ↥𝒲 := Polynomial.eval₂RingHom τ ⟨θO b, hO𝒲 b⟩
    have hev𝒲 : ∀ H, (ev𝒲 H : L) = ev H := by
      intro H
      change 𝒲.subtype (Polynomial.eval₂ τ ⟨θO b, hO𝒲 b⟩ H) = _
      rw [Polynomial.hom_eval₂, hτL']
      rfl
    let evK : Polynomial (IsLocalRing.ResidueField ↥Wt) →+* LaurentSeries k :=
      Polynomial.eval₂RingHom ρK (HahnSeries.C (redO b))
    have hevK : ∀ H, evK H = Polynomial.eval₂ ρK (HahnSeries.C (redO b)) H := fun H => rfl
    have hρev : ∀ H, ρ (ev𝒲 H) = evK (H.map (IsLocalRing.residue ↥Wt)) := by
      intro H
      change ρ (Polynomial.eval₂ τ ⟨θO b, hO𝒲 b⟩ H) = _
      rw [Polynomial.hom_eval₂, hevK, Polynomial.eval₂_map, hρKres, hρO b, hredO]

    have hirrK : Irreducible ((minpoly (ZMod p) (IsLocalRing.residue O b)).map ιK) :=
      irreducible_map_of_forall_exists_coeffMap ι₀ ιK ρK hρKrat (minpoly.irreducible hintb) (minpoly.monic hintb)
    have hrootK : evK ((minpoly (ZMod p) (IsLocalRing.residue O b)).map ιK) = 0 := by
      rw [hevK, Polynomial.eval₂_map, hρKι, ← Polynomial.hom_eval₂, ← hσres, ← hσalg, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, minpoly.aeval, map_zero, map_zero]
    letI algK : Algebra (IsLocalRing.ResidueField ↥Wt) (LaurentSeries k) := ρK.toAlgebra
    have hminK : (minpoly (ZMod p) (IsLocalRing.residue O b)).map ιK =
        minpoly (IsLocalRing.ResidueField ↥Wt) (HahnSeries.C (redO b) : LaurentSeries k) :=
      minpoly.eq_of_irreducible_of_monic hirrK (by rw [Polynomial.aeval_def]; exact hrootK) ((minpoly.monic hintb).map ιK)
    have hmW : (m.map (Int.castRingHom ↥Wt)).map (IsLocalRing.residue ↥Wt) =
        (minpoly (ZMod p) (IsLocalRing.residue O b)).map ιK := by
      rw [Polynomial.map_map, ← hmmap, Polynomial.map_map]
      congr 1
      exact RingHom.ext_int _ _
    have hevm : ev (m.map (Int.castRingHom ↥Wt)) = p * θO c₀ := by rw [hevmap, hc₀, map_mul, map_natCast]

    have hkermap : ∀ D : Polynomial ↥Wt, D.map (IsLocalRing.residue ↥Wt) = 0 → ∃ J, D = Polynomial.C (p : ↥Wt) * J := by
      intro D hD
      have hDmem : D ∈ (Ideal.span {(p : ↥Wt)}).map Polynomial.C := by
        rw [Ideal.mem_map_C_iff]
        intro n
        have := congrArg (fun q => Polynomial.coeff q n) hD
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
        rw [IsLocalRing.residue_eq_zero_iff, hmaxWt] at this
        obtain ⟨v, hv⟩ := this
        rw [hv]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hDmem
      obtain ⟨J, hJ⟩ := hDmem
      exact ⟨J, by rw [← hJ, mul_comm]⟩

    by_cases h0 : ρ (ev𝒲 G) = 0
    ·
      right
      have hdvd : (minpoly (ZMod p) (IsLocalRing.residue O b)).map ιK ∣ G.map (IsLocalRing.residue ↥Wt) := by
        rw [hminK]
        apply minpoly.dvd
        rw [Polynomial.aeval_def]
        change evK _ = 0
        rw [← hρev, h0]
      obtain ⟨HK, hHK⟩ := hdvd
      obtain ⟨H, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue ↥Wt) IsLocalRing.residue_surjective HK
      obtain ⟨J, hJ⟩ := hkermap (G - m.map (Int.castRingHom ↥Wt) * H)
        (by rw [Polynomial.map_sub, Polynomial.map_mul, hmW, hHK, sub_self])
      refine ⟨θO c₀ * ev H + ev J + s₁, hSadd _ (hSadd _ (hSmul _ (hSθO _) _ (hevS _)) _ (hevS _)) _ hs₁S, ?_⟩
      have hG : G = m.map (Int.castRingHom ↥Wt) * H + Polynomial.C (p : ↥Wt) * J := by
        rw [← hJ, add_sub_cancel]
      rw [hsG, hG, map_add, map_mul, map_mul, hevm, hevp]
      ring
    ·
      left
      have hndvd : ¬ (minpoly (ZMod p) (IsLocalRing.residue O b)).map ιK ∣ G.map (IsLocalRing.residue ↥Wt) := by
        rintro ⟨X', hX'⟩
        apply h0
        rw [hρev, hX', map_mul, hrootK, zero_mul]
      obtain ⟨UK, VK, hUV⟩ := (hirrK.coprime_iff_not_dvd).mpr hndvd
      obtain ⟨U, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue ↥Wt) IsLocalRing.residue_surjective UK
      obtain ⟨V, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue ↥Wt) IsLocalRing.residue_surjective VK
      obtain ⟨J, hJ⟩ := hkermap (U * m.map (Int.castRingHom ↥Wt) + V * G - 1)
        (by rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hmW, hUV,
          Polynomial.map_one, sub_self])
      refine ⟨ev V, hevS _, ev J - ev U * θO c₀ + ev V * s₁,
        hSadd _ (hSsub' _ (hevS _) _ (hSmul _ (hevS _) _ (hSθO _))) _ (hSmul _ (hevS _) _ hs₁S), ?_⟩
      have hev1 : ev U * (p * θO c₀) + ev V * ev G - 1 = p * ev J := by
        have := congrArg ev hJ
        rw [map_sub, map_add, map_mul, map_mul, hevm, map_one, map_mul, hevp] at this
        exact this
      rw [hsG]
      linear_combination hev1

  exact eq_of_forall_mem_or_dvd hpL hp𝒱 hp𝒲 hdisc S hS𝒱 hS𝒲 hfield hfrac

end S_ModularCurve_valuationSubring_eq_of_comap_eq_of_forall_exists_coeffMap_eq
end P2MW
export P2MW.S_ModularCurve_valuationSubring_eq_of_comap_eq_of_forall_exists_coeffMap_eq (solution)
