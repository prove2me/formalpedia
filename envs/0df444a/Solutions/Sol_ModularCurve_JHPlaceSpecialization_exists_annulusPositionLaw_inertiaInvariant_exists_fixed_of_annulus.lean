-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_annulusPositionLaw_inertiaInvariant_exists_fixed_of_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ad989ba2-51a0-5b7f-b701-8e31f9e60eb7

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Definitions.Def_ModularCurve_JHTwistType
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_AlgebraicCurve_Place_evalAt_smul_smul_eq_baseAut_evalAt
import Theorems.Thm_ModularCurve_exists_mem_dom_forall_inertia_smul_eq_and_evalAt_param_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_annulusPositionLaw_inertiaInvariant_exists_fixed_of_annulus
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups Pointwise

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace PosH

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} [hp : Fact p.Prime]

local notation "QQ" => AlgebraicClosure ℚ
local notation "v" => ValuationSubring.valuation A

theorem vp_pos (hA : A.LiesOverPrime p) : 0 < v ((p : ℕ) : QQ) := by
  rw [Valuation.pos_iff]
  exact_mod_cast hp.out.ne_zero

theorem vp_lt_one (hA : A.LiesOverPrime p) : v ((p : ℕ) : QQ) < 1 :=
  (ValuationSubring.mem_nonunits_iff A).mp hA

theorem vp_ne_zero (hA : A.LiesOverPrime p) : v ((p : ℕ) : QQ) ≠ 0 := (vp_pos A hA).ne'

theorem valuation_natCast_eq_one (hA : A.LiesOverPrime p) {m : ℕ} (hm : ¬ p ∣ m) : v ((m : ℕ) : QQ) = 1 := by
  have hmem : ((m : ℕ) : QQ) ∈ A := by simp
  have hle : v ((m : ℕ) : QQ) ≤ 1 := (A.valuation_le_one_iff _).mpr hmem
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    have hcop : IsCoprime (m : ℤ) (p : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm))
    obtain ⟨a, b, hab⟩ := hcop
    have hmemA : ∀ z : ℤ, ((z : ℤ) : QQ) ∈ A := fun z => by simp
    have h1 : v (((a : ℤ) : QQ) * m + ((b : ℤ) : QQ) * p) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · calc v (((a : ℤ) : QQ) * m) = v ((a : ℤ) : QQ) * v ((m : ℕ) : QQ) := map_mul _ _ _
          _ ≤ 1 * v ((m : ℕ) : QQ) := by gcongr; exact (A.valuation_le_one_iff _).mpr (hmemA a)
          _ < 1 := by rw [one_mul]; exact hlt
      · calc v (((b : ℤ) : QQ) * p) = v ((b : ℤ) : QQ) * v ((p : ℕ) : QQ) := map_mul _ _ _
          _ ≤ 1 * v ((p : ℕ) : QQ) := by gcongr; exact (A.valuation_le_one_iff _).mpr (hmemA b)
          _ < 1 := by rw [one_mul]; exact vp_lt_one A hA
    have hcast : ((a : ℤ) : QQ) * m + ((b : ℤ) : QQ) * p = 1 := by exact_mod_cast hab
    rw [hcast, map_one] at h1
    exact lt_irrefl _ h1
  · exact heq

theorem exists_valuation_intCast (hA : A.LiesOverPrime p) {z : ℤ} (hz : z ≠ 0) :
    ∃ i : ℕ, v ((z : ℤ) : QQ) = v ((p : ℕ) : QQ) ^ i := by
  obtain ⟨i, n, hn, hzn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hz) p hp.out.ne_one
  refine ⟨i, ?_⟩
  have habs : v ((z : ℤ) : QQ) = v ((z.natAbs : ℕ) : QQ) := by
    rcases Int.natAbs_eq z with h | h
    · conv_lhs => rw [h]
      simp
    · conv_lhs => rw [h]
      simp [Valuation.map_neg]
  rw [habs, hzn]
  push_cast
  rw [map_mul, map_pow, valuation_natCast_eq_one A hA hn, mul_one]

theorem exists_valuation_ratCast (hA : A.LiesOverPrime p) {a : ℚ} (ha : a ≠ 0) :
    ∃ k : ℤ, v ((a : ℚ) : QQ) = v ((p : ℕ) : QQ) ^ k := by
  obtain ⟨i, hi⟩ := exists_valuation_intCast A hA (Rat.num_ne_zero.mpr ha)
  obtain ⟨j, hj⟩ := exists_valuation_intCast A hA (z := (a.den : ℤ)) (by exact_mod_cast a.den_pos.ne')
  refine ⟨(i : ℤ) - j, ?_⟩
  have hden0 : ((a.den : ℕ) : QQ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
  have hq : ((a : ℚ) : QQ) = ((a.num : ℤ) : QQ) / ((a.den : ℕ) : QQ) := by
    rw [eq_div_iff hden0]; exact_mod_cast Rat.mul_den_eq_num a
  have hj' : v ((a.den : ℕ) : QQ) = v ((p : ℕ) : QQ) ^ j := by exact_mod_cast hj
  rw [hq, map_div₀, hi, hj', zpow_sub₀ (vp_ne_zero A hA), zpow_natCast, zpow_natCast]

theorem exists_pow_valuation_eq_zpow (hA : A.LiesOverPrime p) {x : QQ} (hx : x ≠ 0) :
    ∃ N : ℕ, N ≠ 0 ∧ ∃ k : ℤ, v x ^ N = v ((p : ℕ) : QQ) ^ k := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  obtain ⟨f, hf0, hfx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x
  rw [Polynomial.aeval_eq_sum_range] at hfx
  set t : ℕ → QQ := fun i => f.coeff i • x ^ i with ht
  set S := (Finset.range (f.natDegree + 1)).filter (fun i => f.coeff i ≠ 0) with hS
  have hsum : ∑ i ∈ S, t i = 0 := by
    rw [← hfx, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · push Not at h
      rw [ht]; dsimp only
      rw [h, zero_smul]
  have hSne : S.Nonempty := ⟨f.natDegree, by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.self_mem_range_succ _, fun h => hf0 (Polynomial.leadingCoeff_eq_zero.mp h)⟩⟩
  have htv : ∀ i, v (t i) = v ((f.coeff i : ℚ) : QQ) * v x ^ i := fun i => by
    rw [ht]; dsimp only
    rw [Algebra.smul_def, map_mul, map_pow]
    congr 1
  have ht0 : ∀ i ∈ S, v (t i) ≠ 0 := by
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    rw [htv]
    refine mul_ne_zero ?_ (pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hx))
    rw [Valuation.ne_zero_iff]
    exact_mod_cast hi.2
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image S (fun i => v (t i)) hSne

  have htwice : ∃ j ∈ S, j ≠ i₀ ∧ v (t j) = v (t i₀) := by
    by_contra hno
    push Not at hno
    have hlt : ∀ j ∈ S.erase i₀, v (t j) < v (t i₀) := by
      intro j hj
      obtain ⟨hji, hjS⟩ := Finset.mem_erase.mp hj
      exact lt_of_le_of_ne (hmax j hjS) (hno j hjS hji)
    have hrest : v (∑ j ∈ S.erase i₀, t j) < v (t i₀) := Valuation.map_sum_lt _ (ht0 i₀ hi₀) hlt
    have heq : v (t i₀ + ∑ j ∈ S.erase i₀, t j) = v (t i₀) := Valuation.map_add_eq_of_lt_left _ hrest
    rw [Finset.add_sum_erase _ _ hi₀, hsum, map_zero] at heq
    exact ht0 i₀ hi₀ heq.symm
  obtain ⟨j, hj, hji, hvj⟩ := htwice

  have hci : (f.coeff i₀ : ℚ) ≠ 0 := by rw [hS, Finset.mem_filter] at hi₀; exact hi₀.2
  have hcj : (f.coeff j : ℚ) ≠ 0 := by rw [hS, Finset.mem_filter] at hj; exact hj.2
  have hvx0 : v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [htv, htv] at hvj

  have key : ∀ (a b : ℕ) (c c' : ℚ), c ≠ 0 → c' ≠ 0 → a < b →
      v ((c : ℚ) : QQ) * v x ^ a = v ((c' : ℚ) : QQ) * v x ^ b → ∃ k : ℤ, v x ^ (b - a) = v ((p : ℕ) : QQ) ^ k := by
    intro a b c c' hc hc' hab h
    obtain ⟨k, hk⟩ := exists_valuation_ratCast A hA (div_ne_zero hc hc')
    refine ⟨k, ?_⟩
    have hvc' : v ((c' : ℚ) : QQ) ≠ 0 := by rw [Valuation.ne_zero_iff]; exact_mod_cast hc'
    have hsplit : v x ^ b = v x ^ a * v x ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hab.le]
    rw [hsplit, ← mul_assoc] at h
    have h2 : v ((c : ℚ) : QQ) = v ((c' : ℚ) : QQ) * v x ^ (b - a) := by
      have := mul_right_cancel₀ (pow_ne_zero a hvx0) (h.trans (mul_right_comm _ _ _))
      exact this
    rw [← hk]
    push_cast
    rw [map_div₀, h2, mul_div_cancel_left₀ _ hvc']
  rcases lt_or_gt_of_ne hji with hlt | hgt
  · obtain ⟨k, hk⟩ := key j i₀ _ _ hcj hci hlt hvj
    exact ⟨i₀ - j, Nat.sub_ne_zero_of_lt hlt, k, hk⟩
  · obtain ⟨k, hk⟩ := key i₀ j _ _ hci hcj hgt hvj.symm
    exact ⟨j - i₀, Nat.sub_ne_zero_of_lt hgt, k, hk⟩

theorem pow_inj {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} {n : ℕ} (hn : n ≠ 0) (h : a ^ n = b ^ n) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ne_of_lt (pow_lt_pow_left₀ hab zero_le' hn))
  · exact hab
  · exact absurd h.symm (ne_of_lt (pow_lt_pow_left₀ hab zero_le' hn))

theorem exists_rat_position (hA : A.LiesOverPrime p) {x : QQ} (hx : x ≠ 0) (e : ℕ)
    (hlt : v x < 1) (hgt : v ((p : ℕ) : QQ) ^ e < v x) :
    ∃ r : ℚ, 0 < r ∧ r < e ∧ v x ^ r.den = v ((p : ℕ) : QQ) ^ r.num.toNat := by
  obtain ⟨N, hN, k, hk⟩ := exists_pow_valuation_eq_zpow A hA hx
  have hvp := vp_pos A hA
  have hvp1 := vp_lt_one A hA
  have hanti : StrictAnti (fun n : ℤ => v ((p : ℕ) : QQ) ^ n) := by
    intro m n hmn
    exact zpow_lt_zpow_right_of_lt_one₀ hvp hvp1 hmn

  have hk0 : 0 < k := by
    have h1 : v x ^ N < 1 := pow_lt_one₀ zero_le' hlt hN
    rw [hk, ← zpow_zero (v ((p : ℕ) : QQ))] at h1
    by_contra hle
    push Not at hle
    exact absurd h1 (not_lt.mpr (hanti.antitone hle))

  have hkE : k < (e : ℤ) * N := by
    have h1 : (v ((p : ℕ) : QQ) ^ e) ^ N < v x ^ N := pow_lt_pow_left₀ hgt zero_le' hN
    rw [hk, ← pow_mul, ← zpow_natCast] at h1
    push_cast at h1
    by_contra hle
    push Not at hle
    exact absurd h1 (not_lt.mpr (hanti.antitone hle))
  set r : ℚ := (k : ℚ) / N with hr
  have hN0 : (0 : ℚ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  refine ⟨r, div_pos (by exact_mod_cast hk0) hN0, ?_, ?_⟩
  · rw [hr, div_lt_iff₀ hN0]; exact_mod_cast hkE
  ·
    have hcross : (r.num : ℚ) * N = k * r.den := by
      have h1 : r * r.den = r.num := Rat.mul_den_eq_num r
      have h2 : r * N = k := by rw [hr]; field_simp
      nlinarith [h1, h2, hN0, (show (0 : ℚ) < r.den by exact_mod_cast r.den_pos)]
    have hnum0 : 0 ≤ r.num := (Rat.num_nonneg).mpr (div_pos (by exact_mod_cast hk0) hN0).le
    have hcrossZ : r.num * (N : ℤ) = k * (r.den : ℤ) := by exact_mod_cast hcross
    apply pow_inj hN
    rw [← pow_mul, ← pow_mul, mul_comm r.den N, pow_mul, hk, ← zpow_natCast, ← zpow_mul, ← zpow_natCast]
    congr 1
    push_cast
    rw [Int.toNat_of_nonneg hnum0]
    linarith [hcrossZ]

theorem rat_position_unique (hA : A.LiesOverPrime p) {x : QQ} {r r' : ℚ} (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (h : v x ^ r.den = v ((p : ℕ) : QQ) ^ r.num.toNat) (h' : v x ^ r'.den = v ((p : ℕ) : QQ) ^ r'.num.toNat) : r = r' := by
  have hvp := vp_pos A hA
  have hvp1 := vp_lt_one A hA
  have hanti : StrictAnti (fun n : ℕ => v ((p : ℕ) : QQ) ^ n) := pow_right_strictAnti₀ hvp hvp1
  have hnum : 0 ≤ r.num := Rat.num_nonneg.mpr hr
  have hnum' : 0 ≤ r'.num := Rat.num_nonneg.mpr hr'
  have hx : (v x ^ r.den) ^ r'.den = (v x ^ r'.den) ^ r.den := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [h, h', ← pow_mul, ← pow_mul] at hx
  have hexp : r.num.toNat * r'.den = r'.num.toNat * r.den := hanti.injective hx
  have hexpZ : r.num * r'.den = r'.num * r.den := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hexp
    push_cast at this
    rwa [Int.toNat_of_nonneg hnum, Int.toNat_of_nonneg hnum'] at this
  rw [← Rat.num_div_den r, ← Rat.num_div_den r', div_eq_div_iff (by exact_mod_cast r.den_pos.ne') (by exact_mod_cast r'.den_pos.ne')]
  exact_mod_cast hexpZ

theorem valuation_pow_eq_of_smul_eq (hA : A.LiesOverPrime p) (σ : QQ ≃ₐ[ℚ] QQ) (hσ : σ • A = A)
    {x : QQ} (hx : x ≠ 0) {n k : ℕ} (h : v x ^ n = v ((p : ℕ) : QQ) ^ k) : v (σ x) ^ n = v ((p : ℕ) : QQ) ^ k := by
  have hp0 : ((p : ℕ) : QQ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set y : QQ := x ^ n / (p : QQ) ^ k with hy
  have hvy : v y = 1 := by
    rw [hy, map_div₀, map_pow, map_pow, h, div_self (pow_ne_zero _ (vp_ne_zero A hA))]

  have hmem : y ∈ A := (A.valuation_le_one_iff _).mp hvy.le
  have hmem' : y⁻¹ ∈ A := (A.valuation_le_one_iff _).mp (by rw [map_inv₀, hvy, inv_one])
  have hσy : σ y ∈ A := by rw [← hσ]; exact ValuationSubring.smul_mem_pointwise_smul σ y A hmem
  have hσy' : (σ y)⁻¹ ∈ A := by rw [← map_inv₀, ← hσ]; exact ValuationSubring.smul_mem_pointwise_smul σ _ A hmem'
  have hvσy : v (σ y) = 1 := by
    apply le_antisymm ((A.valuation_le_one_iff _).mpr hσy)
    have h1 := (A.valuation_le_one_iff _).mpr hσy'
    rw [map_inv₀] at h1
    have hy0 : y ≠ 0 := fun h0 => by rw [h0, map_zero] at hvy; exact zero_ne_one hvy
    have hne : v (σ y) ≠ 0 := (Valuation.ne_zero_iff _).mpr ((map_ne_zero σ).mpr hy0)
    exact (inv_le_one₀ (zero_lt_iff.mpr hne)).mp h1
  have hσyeq : σ y = (σ x) ^ n / (p : QQ) ^ k := by
    rw [hy, map_div₀, map_pow, map_pow, map_natCast]
  rw [hσyeq, map_div₀, map_pow, map_pow, div_eq_one_iff_eq (pow_ne_zero _ (vp_ne_zero A hA))] at hvσy
  exact hvσy

end PosH

namespace PosH

theorem restrictAlong_smul_of_forall_map_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (g : SemilinearAut K F) (g' : SemilinearAut K F')
    (hcomm : ∀ u : F, φ (g • u) = g' • φ u) (w : Place K F') :
    (g' • w).restrictAlong φ hφ = g • (w.restrictAlong φ hφ) := by
  have hcomm' : ∀ u : F, φ (g⁻¹ • u) = g'⁻¹ • φ u := fun u => by
    have := hcomm (g⁻¹ • u)
    rw [smul_inv_smul] at this
    rw [this, inv_smul_smul]
  apply Place.ext
  ext x
  show φ x ∈ (g' • w).toValuationSubring ↔ x ∈ g • (w.restrictAlong φ hφ).toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  show g'⁻¹ • φ x ∈ w.toValuationSubring ↔ φ (g⁻¹ • x) ∈ w.toValuationSubring
  rw [hcomm']

end PosH

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem PosH.reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)
    :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W) = Psp.reduceFst α hα W ∧
      Psp.reduceSnd β hβ δ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W) = Psp.reduceSnd β hβ δ W := by
  intro σ hσ W

  set G := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ with hG
  set G' := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ with hG'
  have hαeq : ∀ u, α (G' • u) = G • α u := fun u => by
    apply Subtype.ext
    rw [hα_coe, hG', coe_arithmeticGalois_smul, hG, coe_arithmeticGalois_smul, hα_coe]
  have hβapp : ∀ u, β u = θ (α u) := fun u => by rw [hβθ]; rfl
  have hβeq : ∀ u, β (G' • u) = G • β u := fun u => by
    rw [hβapp, hβapp, hαeq, hG, hθgal]
  refine ⟨?_, ?_⟩
  · show Psp.sp ((G • W).restrictAlong α hα) = Psp.sp (W.restrictAlong α hα)
    rw [PosH.restrictAlong_smul_of_forall_map_smul α hα G' G hαeq W, hG']
    exact Psp.d6_inertia σ hσ _
  · show δ (Psp.sp ((G • W).restrictAlong β hβ)) = δ (Psp.sp (W.restrictAlong β hβ))
    rw [PosH.restrictAlong_smul_of_forall_map_smul β hβ G' G hβeq W, hG']
    rw [Psp.d6_inertia σ hσ]

namespace PosH

section AnnulusVal

variable {L F : Type*} [Field L] [Field F] [Algebra L F] {A : ValuationSubring L}

theorem inv_mem_of_isUnit' {S : ValuationSubring F} {x : F} (hx : x ∈ S) (hu : IsUnit (⟨x, hx⟩ : S)) :
    x⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : S) : F) = x := by rw [hu]
  have h1 : x * (((u⁻¹ : Sˣ) : S) : F) = 1 := by
    rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  have : (((u⁻¹ : Sˣ) : S) : F) = x⁻¹ := (eq_inv_of_mul_eq_one_right h1)
  rw [← this]; exact SetLike.coe_mem _

theorem evalAt_flip (An : AlgebraicCurve.Annulus A F) {V : Place L F} (hV : V ∈ An.dom) :
    V.IsRational ∧ V.evalAt An.param ≠ 0 ∧
      V.evalAt (algebraMap L F ((An.modulus : A) : L) * An.param⁻¹) = ((An.modulus : A) : L) * (V.evalAt An.param)⁻¹ := by
  obtain ⟨hrat, hzmem, -, hz0, -⟩ := An.mem_dom V hV
  refine ⟨hrat, hz0, ?_⟩

  have hunit : IsUnit (⟨An.param, hzmem⟩ : V.toValuationSubring) := by
    by_contra hnu
    have hmax := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← IsLocalRing.residue_eq_zero_iff] at hmax
    apply hz0
    have h := V.algebraMap_evalAt hrat hzmem
    rw [hmax] at h
    exact (map_eq_zero _).mp h
  have hinv : An.param⁻¹ ∈ V.toValuationSubring := inv_mem_of_isUnit' hzmem hunit
  have hz' : An.param ≠ 0 := fun h0 => hz0 (by
    have : (⟨An.param, hzmem⟩ : V.toValuationSubring) = 0 := Subtype.ext h0
    have h := V.algebraMap_evalAt hrat hzmem
    rw [this, map_zero] at h
    exact (map_eq_zero _).mp h)
  have hev : V.evalAt An.param⁻¹ = (V.evalAt An.param)⁻¹ := by
    have hmul := V.evalAt_mul_of_mem hrat hzmem hinv
    rw [mul_inv_cancel₀ hz', V.evalAt_one] at hmul
    exact eq_inv_of_mul_eq_one_right hmul.symm
  rw [V.evalAt_mul_of_mem hrat (V.algebraMap_mem' _) hinv, V.evalAt_algebraMap_eq, hev]

end AnnulusVal

end PosH

open PosH in
open Classical in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hFixFin : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C))

    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (hAnn : ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS,
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
            ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))) :
    ∃ pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ,
      JHPlaceSpecialization.AnnulusPositionLaw SS e An pos ∧
      (∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        pos s ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = pos s V) ∧
      (∀ (s : ↥SS) (d : ℕ), 0 < d → d < e s → ∃ V ∈ (An s).dom,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ pos s V = d) := by

  have hvp := PosH.vp_pos A (p := p) hA
  have hvp1 := PosH.vp_lt_one A (p := p) hA
  have hvp0 := PosH.vp_ne_zero A (p := p) hA
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  have hmod : ∀ s : ↥SS, ((An s).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
      A.valuation ((An s).modulus : AlgebraicClosure ℚ) = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ (e s) := by
    intro s
    obtain ⟨u, hu, hmu⟩ := (hAn s).2.1
    have hvu : A.valuation (u : AlgebraicClosure ℚ) = 1 := (A.valuation_eq_one_iff u).mp hu
    have hcoe : ((An s).modulus : AlgebraicClosure ℚ) = ((p : ℕ) : AlgebraicClosure ℚ) ^ (e s) * (u : AlgebraicClosure ℚ) := by
      rw [hmu]; push_cast; rfl
    refine ⟨?_, ?_⟩
    · rw [hcoe]
      refine mul_ne_zero (pow_ne_zero _ hp0) ?_
      intro h0
      rw [h0, map_zero] at hvu
      exact zero_ne_one hvu
    · rw [hcoe, map_mul, map_pow, hvu, mul_one]

  have hx : ∀ (s : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An s).dom →
      V.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * ((An s).param)⁻¹) ≠ 0 ∧
      A.valuation (V.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * ((An s).param)⁻¹)) < 1 ∧
      A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ (e s) <
        A.valuation (V.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * ((An s).param)⁻¹)) := by
    intro s V hV
    obtain ⟨hrat, hz0, hflip⟩ := PosH.evalAt_flip (An s) hV
    obtain ⟨-, -, ⟨hzA, hzmax⟩, -, m, hm, hπ⟩ := (An s).mem_dom V hV
    rw [hflip]
    have hm0 : (m : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      apply (hmod s).1
      rw [hπ, h0, mul_zero]
    have hxm : (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (V.evalAt (An s).param)⁻¹ = (m : AlgebraicClosure ℚ) := by
      rw [hπ, mul_comm (V.evalAt (An s).param), mul_assoc, mul_inv_cancel₀ hz0, mul_one]
    rw [hxm]
    refine ⟨hm0, (A.valuation_lt_one_iff m).mp hm, ?_⟩
    rw [← (hmod s).2, hπ, map_mul]
    have hvz : A.valuation (V.evalAt (An s).param) < 1 := (A.valuation_lt_one_iff ⟨_, hzA⟩).mp hzmax
    have hvm0 : 0 < A.valuation (m : AlgebraicClosure ℚ) := (Valuation.pos_iff _).mpr hm0
    calc A.valuation (V.evalAt (An s).param) * A.valuation (m : AlgebraicClosure ℚ)
        < 1 * A.valuation (m : AlgebraicClosure ℚ) := by gcongr
      _ = A.valuation (m : AlgebraicClosure ℚ) := one_mul _

  let pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ := fun s V =>
    if hV : V ∈ (An s).dom then Classical.choose (PosH.exists_rat_position A hA (hx s V hV).1 (e s) (hx s V hV).2.1 (hx s V hV).2.2) else 0
  have hpos_spec : ∀ (s : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV : V ∈ (An s).dom),
      0 < pos s V ∧ pos s V < e s ∧
        A.valuation (V.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * ((An s).param)⁻¹)) ^ (pos s V).den =
          A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ (pos s V).num.toNat := by
    intro s V hV
    have h := Classical.choose_spec (PosH.exists_rat_position A hA (hx s V hV).1 (e s) (hx s V hV).2.1 (hx s V hV).2.2)
    simp only [pos, dif_pos hV]
    exact h

  have hpos_uniq : ∀ (s : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV : V ∈ (An s).dom) (r : ℚ), 0 ≤ r →
      A.valuation (V.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * ((An s).param)⁻¹)) ^ r.den =
        A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ r.num.toNat → pos s V = r := by
    intro s V hV r hr h
    exact PosH.rat_position_unique A hA (hpos_spec s V hV).1.le hr (hpos_spec s V hV).2.2 h

  have hK2 := PosH.reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn
    p M H hpM hpM2 hHp A hA θ α (θ.toAlgHom.comp α) hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hreg hnv hα_coe hβ_coe hθgal rfl
  have hdomσ : ∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ W ∈ (An s).dom,
      (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • W ∈ (An s).dom := by
    intro s σ hσ W hW
    obtain ⟨hWr, hWf, hWs⟩ := ((hAn s).1 W).mp hW
    have hread := hK2 σ hσ W
    refine ((hAn s).1 _).mpr ⟨hread.1.trans hWr, ?_, ?_⟩
    · unfold JHPlaceSpecialization.IsStrictFst at hWf ⊢
      rw [hread.1, hread.2]; exact hWf
    · unfold JHPlaceSpecialization.IsStrictSnd at hWs ⊢
      rw [hread.1, hread.2]; exact hWs
  have hAσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • A = A := by
    intro σ hσ
    obtain ⟨τ, -, rfl⟩ := Subgroup.mem_map.mp hσ
    exact τ.2
  have hvalσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ y : AlgebraicClosure ℚ, y ≠ 0 → A.valuation (σ y) = A.valuation y := by
    intro σ hσ y hy
    obtain ⟨N, hN, k, hk⟩ := PosH.exists_pow_valuation_eq_zpow A hA hy

    have key : ∀ (a : AlgebraicClosure ℚ), a ≠ 0 → ∀ (n : ℕ), n ≠ 0 → ∀ (kk : ℤ), A.valuation a ^ n = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ kk →
        A.valuation (σ a) ^ n = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ kk := by
      intro a ha n hn kk h
      rcases Int.eq_nat_or_neg kk with ⟨j, rfl | rfl⟩
      · rw [zpow_natCast] at h ⊢
        exact PosH.valuation_pow_eq_of_smul_eq A hA σ (hAσ σ hσ) ha h
      ·
        have h' : A.valuation a⁻¹ ^ n = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ (j : ℕ) := by
          rw [map_inv₀, inv_pow, h, zpow_neg, zpow_natCast, inv_inv]
        have := PosH.valuation_pow_eq_of_smul_eq A hA σ (hAσ σ hσ) (inv_ne_zero ha) h'
        rw [map_inv₀, map_inv₀, inv_pow] at this
        rw [zpow_neg, zpow_natCast, ← this, inv_inv]
    have h1 := key y hy N hN k hk
    rw [← hk] at h1
    exact PosH.pow_inj hN h1
  have hzσ : ∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V ∈ (An s).dom,
      ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V).evalAt (An s).param = σ (V.evalAt (An s).param) := by
    intro s σ hσ V hV
    have hrat : V.IsRational := ((An s).mem_dom V hV).1
    have hrat' := ((An s).mem_dom _ (hdomσ s σ hσ V hV)).1
    have h := AlgebraicCurve.Place.evalAt_smul_smul_eq_baseAut_evalAt (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) V hrat hrat' (An s).param
    rw [(hAn s).2.2.1 σ hσ, baseAut_arithmeticGalois] at h
    exact h
  refine ⟨pos, ?_, ?_, ?_⟩
  ·
    intro s V hV
    exact hpos_spec s V hV
  ·
    intro s σ hσ V
    by_cases hV : V ∈ (An s).dom
    · have hV' := hdomσ s σ hσ V hV
      apply hpos_uniq s _ hV' (pos s V) (hpos_spec s V hV).1.le

      obtain ⟨-, hz0, hflip⟩ := PosH.evalAt_flip (An s) hV
      obtain ⟨-, hz0', hflip'⟩ := PosH.evalAt_flip (An s) hV'
      rw [hflip', hzσ s σ hσ V hV, map_mul, map_inv₀, hvalσ σ hσ _ hz0, ← map_inv₀, ← map_mul, ← hflip]
      exact (hpos_spec s V hV).2.2
    · have hV' : (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V ∉ (An s).dom := by
        intro h
        apply hV
        have := hdomσ s σ⁻¹ (inv_mem hσ) _ h
        rwa [map_inv, inv_smul_smul] at this
      simp only [pos, dif_neg hV, dif_neg hV']
  ·
    intro s d hd hde
    have hpA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A := (A.valuation_le_one_iff _).mp hvp1.le
    let c : ↥A := ⟨((p : ℕ) : AlgebraicClosure ℚ) ^ (e s - d), pow_mem hpA _⟩
    have hc_coe : (c : AlgebraicClosure ℚ) = ((p : ℕ) : AlgebraicClosure ℚ) ^ (e s - d) := rfl
    have hc0 : (c : AlgebraicClosure ℚ) ≠ 0 := by rw [hc_coe]; exact pow_ne_zero _ hp0
    have hcmax : c ∈ maximalIdeal ↥A := by
      rw [A.valuation_lt_one_iff, hc_coe, map_pow]
      exact pow_lt_one₀ zero_le' hvp1 (Nat.sub_ne_zero_of_lt hde)
    obtain ⟨u, hu, hmu⟩ := (hAn s).2.1
    have hcm : ∃ m ∈ maximalIdeal ↥A, (((An s).modulus : ↥A) : AlgebraicClosure ℚ) = (c : AlgebraicClosure ℚ) * m := by
      refine ⟨⟨((p : ℕ) : AlgebraicClosure ℚ) ^ d, pow_mem hpA _⟩ * u, ?_, ?_⟩
      · rw [A.valuation_lt_one_iff]
        push_cast
        rw [map_mul, map_pow, (A.valuation_eq_one_iff u).mp hu, mul_one]
        exact pow_lt_one₀ zero_le' hvp1 hd.ne'
      · rw [hmu, hc_coe]; push_cast
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hde.le]
    have hcσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (c : AlgebraicClosure ℚ) = c := by
      intro σ _; rw [hc_coe, map_pow, map_natCast]
    obtain ⟨W, hW, hWσ, hWz⟩ := ModularCurve.exists_mem_dom_forall_inertia_smul_eq_and_evalAt_param_eq A (xHFunctionField M H) (An s)
      ((hAn s).2.2.1) (fun σ hσ W hW => hdomσ s σ hσ W hW) c hcmax hc0 hcm hcσ
    refine ⟨W, hW, hWσ, ?_⟩
    apply hpos_uniq s W hW (d : ℚ) (by exact_mod_cast hd.le)

    obtain ⟨-, -, hflip⟩ := PosH.evalAt_flip (An s) hW
    rw [hflip, hWz, hc_coe]
    have hval : A.valuation ((((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (((p : ℕ) : AlgebraicClosure ℚ) ^ (e s - d))⁻¹) =
        A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ d := by
      rw [map_mul, map_inv₀, map_pow, (hmod s).2, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hvp0, ← zpow_natCast]
      congr 1
      omega
    rw [hval]
    simp

end S_ModularCurve_JHPlaceSpecialization_exists_annulusPositionLaw_inertiaInvariant_exists_fixed_of_annulus
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_annulusPositionLaw_inertiaInvariant_exists_fixed_of_annulus (solution)
