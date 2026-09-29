-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_twistSp_eq_zero_of_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/289242e6-5e63-5a02-84cb-8010e13e2e85

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Definitions.Def_ModularCurve_JHTwistType
import Definitions.Def_ModularCurve_JHTwistedDatum
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_twistSp_eq_zero_of_annulus
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_hasValue_residue_div_pow_and_div_eq_twistAngFactor_of_coupled_of_inertiaStable
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus
import Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_twistSp_eq_zero_of_annulus
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JHPlaceSpecialization_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_twistSp_eq_zero_of_annulus.AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP"
open scoped MatrixGroups

namespace CsHEqv

theorem restrictAlong_semilinearAut_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : SemilinearAut.IntertwinesAlong φ.toRingHom g g') (w : Place K F') :
    (g' • w).restrictAlong φ hφ = g • (w.restrictAlong φ hφ) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact SemilinearAut.restrict_smul (F := F) (g := g) (g' := g') (fun x => hgg' x) w

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p]

theorem smul_alpha
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • α u =
      α (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ • u) := by
  apply Subtype.ext
  rw [coe_arithmeticGalois_smul, hα_coe, hα_coe, coe_arithmeticGalois_smul]

theorem reduceFst_smul (Psp : JHPlaceSpecialization p M H hpM A)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Psp.reduceFst α hα (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W) = Psp.reduceFst α hα W := by
  show Psp.sp ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W).restrictAlong α hα) = Psp.sp (W.restrictAlong α hα)
  rw [restrictAlong_semilinearAut_smul α hα
      (g := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ)
      (g' := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ)
      (fun x => smul_alpha α hα_coe σ x) W]
  exact Psp.d6_inertia σ hσ _

theorem reduceSnd_smul (Psp : JHPlaceSpecialization p M H hpM A)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W) =
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W := by
  show δ (Psp.sp ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W).restrictAlong (θ.toAlgHom.comp α) hβ)) =
    δ (Psp.sp (W.restrictAlong (θ.toAlgHom.comp α) hβ))
  rw [restrictAlong_semilinearAut_smul (θ.toAlgHom.comp α) hβ
      (g := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ)
      (g' := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ)
      (fun x => by
        show arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ (α x) = θ (α _)
        rw [← hθgal, smul_alpha α hα_coe σ x]) W]
  exact congrArg δ (Psp.d6_inertia σ hσ _)

end CsHEqv

namespace CoupledH

theorem sum_second_diff (a : ℕ → ℤ) (n : ℕ) :
    ∑ d ∈ Finset.Ico 1 (n + 1), (a (d - 1) - 2 * a d + a (d + 1)) = a 0 - a 1 - a n + a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

theorem sum_mul_neg_laplacian (c : ℕ → ℤ) (e : ℕ) (he : 1 ≤ e) :
    ∑ d ∈ Finset.Ico 1 e, (d : ℤ) * (-(c (d - 1) - 2 * c d + c (d + 1))) =
      (e : ℤ) * (c (e - 1) - c e) + (c e - c 0) := by
  induction e with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n), ih hn]
      have h1 : n + 1 - 1 = n := by omega
      rw [h1]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

theorem tent_eval (δ : ℚ) (h0 : 0 ≤ δ) (d : ℕ) :
    max 0 (1 - |δ - (d : ℚ)|) =
      (if d = ⌊δ⌋₊ then 1 - (δ - ⌊δ⌋₊) else 0) + (if d = ⌊δ⌋₊ + 1 then δ - ⌊δ⌋₊ else 0) := by
  have hfl : (⌊δ⌋₊ : ℚ) ≤ δ := Nat.floor_le h0
  have hlt : δ < ⌊δ⌋₊ + 1 := Nat.lt_floor_add_one δ
  by_cases h1 : d = ⌊δ⌋₊
  · subst h1
    have h2 : ¬ (⌊δ⌋₊ = ⌊δ⌋₊ + 1) := by omega
    rw [if_pos rfl, if_neg h2, add_zero, abs_of_nonneg (by linarith)]
    exact max_eq_right (by linarith)
  · rw [if_neg h1, zero_add]
    by_cases h2 : d = ⌊δ⌋₊ + 1
    · subst h2
      rw [if_pos rfl, abs_of_nonpos (by push_cast; linarith)]
      push_cast
      rw [max_eq_right (by linarith)]
      ring
    · rw [if_neg h2]
      apply max_eq_left
      rcases Nat.lt_or_gt_of_ne h1 with h | h
      · have : (d : ℚ) + 1 ≤ ⌊δ⌋₊ := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have : (⌊δ⌋₊ : ℚ) + 2 ≤ d := by exact_mod_cast (show ⌊δ⌋₊ + 2 ≤ d by omega)
        rw [abs_of_nonpos (by linarith)]
        linarith

theorem tent_sum (n : ℕ) (δ : ℚ) (h0 : 0 ≤ δ) (hn : δ ≤ n) :
    ∑ d ∈ Finset.range (n + 1), max 0 (1 - |δ - (d : ℚ)|) = 1 := by
  have hfl : (⌊δ⌋₊ : ℚ) ≤ δ := Nat.floor_le h0
  have hmn : ⌊δ⌋₊ ≤ n := Nat.floor_le_of_le (by exact_mod_cast hn)
  rw [Finset.sum_congr rfl (fun d _ => tent_eval δ h0 d), Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hm : ⌊δ⌋₊ ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [if_pos hm]
  by_cases hm1 : ⌊δ⌋₊ + 1 ∈ Finset.range (n + 1)
  · rw [if_pos hm1]; ring
  · rw [if_neg hm1, add_zero]
    have h3 : ⌊δ⌋₊ = n := by rw [Finset.mem_range] at hm1; omega
    have h4 : δ = n := le_antisymm hn (by rw [← h3]; exact hfl)
    rw [h4]; simp

theorem tent_sum_mul (n : ℕ) (δ : ℚ) (h0 : 0 ≤ δ) (hn : δ ≤ n) :
    ∑ d ∈ Finset.range (n + 1), (d : ℚ) * max 0 (1 - |δ - (d : ℚ)|) = δ := by
  have hfl : (⌊δ⌋₊ : ℚ) ≤ δ := Nat.floor_le h0
  have hmn : ⌊δ⌋₊ ≤ n := Nat.floor_le_of_le (by exact_mod_cast hn)
  have hre : ∀ d ∈ Finset.range (n + 1), (d : ℚ) * max 0 (1 - |δ - (d : ℚ)|) =
      (if d = ⌊δ⌋₊ then (⌊δ⌋₊ : ℚ) * (1 - (δ - ⌊δ⌋₊)) else 0) +
        (if d = ⌊δ⌋₊ + 1 then ((⌊δ⌋₊ : ℚ) + 1) * (δ - ⌊δ⌋₊) else 0) := by
    intro d _
    rw [tent_eval δ h0 d, mul_add]
    congr 1
    · split_ifs with h
      · subst h; rfl
      · rw [mul_zero]
    · split_ifs with h
      · subst h; push_cast; rfl
      · rw [mul_zero]
  rw [Finset.sum_congr rfl hre, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hm : ⌊δ⌋₊ ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [if_pos hm]
  by_cases hm1 : ⌊δ⌋₊ + 1 ∈ Finset.range (n + 1)
  · rw [if_pos hm1]; ring
  · rw [if_neg hm1, add_zero]
    have h3 : ⌊δ⌋₊ = n := by rw [Finset.mem_range] at hm1; omega
    have h4 : δ = n := le_antisymm hn (by rw [← h3]; exact hfl)
    rw [h3, h4]; ring

section ValueGroup
open Classical
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem eq_one_of_pow_eq_one {x : Γ} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : x = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; rw [zero_pow hn] at h; exact zero_ne_one h
  set u : Γˣ := Units.mk0 x hx0 with hu
  have hun : u ^ n = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0, h, Units.val_one])
  have hu1 : u = 1 := by
    rcases lt_trichotomy u 1 with hlt | heq | hgt
    · exact absurd hun (pow_lt_one' hlt hn).ne
    · exact heq
    · exact absurd hun (one_lt_pow' hgt hn).ne'
  have := congrArg (fun v : Γˣ => (v : Γ)) hu1
  simpa [hu] using this

theorem prod_zpow_eq_zpow_sum₀ {Γ : Type*} [CommGroupWithZero Γ] {ι : Type*} (s : Finset ι) (γ : Γ) (hγ : γ ≠ 0)
    (f : ι → ℤ) : ∏ i ∈ s, γ ^ f i = γ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hγ]

theorem prod_zpow_mul_zpow_eq_one {ι : Type*} (s : Finset ι) (y : ι → Γ) (g : Γ) (hg : g ≠ 0)
    (e : ι → ℤ) (δ : ι → ℚ) (hδ : ∀ i ∈ s, 0 ≤ δ i)
    (hy : ∀ i ∈ s, y i ^ (δ i).den = g ^ (δ i).num.toNat)
    (m : ℤ) (hm : ∑ i ∈ s, (e i : ℚ) * δ i = m) :
    (∏ i ∈ s, y i ^ (-(e i))) * g ^ m = 1 := by
  classical
  set N : ℕ := ∏ i ∈ s, (δ i).den with hN
  have hNpos : 0 < N := Finset.prod_pos fun i _ => (δ i).den_pos
  have hdvd : ∀ i ∈ s, (δ i).den ∣ N := fun i hi => Finset.dvd_prod_of_mem _ hi

  have hterm : ∀ i ∈ s, (y i ^ (-(e i))) ^ N = g ^ ((((δ i).num.toNat * (N / (δ i).den) : ℕ) : ℤ) * (-(e i))) := by
    intro i hi
    obtain ⟨c, hc⟩ := hdvd i hi
    have hNd : N / (δ i).den = c := by rw [hc, Nat.mul_div_cancel_left _ (δ i).den_pos]
    rw [hNd]
    calc (y i ^ (-(e i))) ^ N = ((y i) ^ N) ^ (-(e i)) := by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      _ = (g ^ ((δ i).num.toNat * c)) ^ (-(e i)) := by rw [hc, pow_mul, hy i hi, ← pow_mul]
      _ = g ^ ((((δ i).num.toNat * c : ℕ) : ℤ) * (-(e i))) := by rw [← zpow_natCast, ← zpow_mul]

  have hexp : (∑ i ∈ s, (((δ i).num.toNat * (N / (δ i).den) : ℕ) : ℤ) * (-(e i))) + m * N = 0 := by
    have hi : ∀ i ∈ s, ((((δ i).num.toNat * (N / (δ i).den) : ℕ) : ℤ) : ℚ) * (-(e i : ℚ)) =
        (N : ℚ) * (-((e i : ℚ) * δ i)) := by
      intro i hi
      obtain ⟨c, hc⟩ := hdvd i hi
      have hNd : N / (δ i).den = c := by rw [hc, Nat.mul_div_cancel_left _ (δ i).den_pos]
      have hnum' : ((δ i).num.toNat : ℚ) = (δ i).num := by
        have : ((δ i).num.toNat : ℤ) = (δ i).num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hδ i hi))
        exact_mod_cast this
      have hδeq : ((δ i).num : ℚ) = δ i * (δ i).den := (Rat.mul_den_eq_num (δ i)).symm
      rw [hNd, Int.cast_natCast, Nat.cast_mul, hnum', hδeq, hc, Nat.cast_mul]
      ring
    have hq : (((∑ i ∈ s, (((δ i).num.toNat * (N / (δ i).den) : ℕ) : ℤ) * (-(e i))) + m * N : ℤ) : ℚ) = 0 := by
      rw [Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_natCast,
        Finset.sum_congr rfl (fun i hi' => by rw [Int.cast_mul, Int.cast_neg, hi i hi']), ← Finset.mul_sum,
        Finset.sum_neg_distrib, hm]
      ring
    exact_mod_cast hq
  apply eq_one_of_pow_eq_one hNpos.ne'
  rw [mul_pow, ← Finset.prod_pow, Finset.prod_congr rfl hterm, prod_zpow_eq_zpow_sum₀ s g hg, ← zpow_natCast (g ^ m),
    ← zpow_mul, ← zpow_add₀ hg, hexp, zpow_zero]

end ValueGroup

section Book

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]
variable (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
  (e : ↥SS → ℕ) (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
  (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)

theorem chainVal_zero (a : JHPlaceSpecialization.TwistVec ↥SS) (s : ↥SS) :
    JHPlaceSpecialization.twistChainVal SS e a s 0 = a.aZ := by
  unfold JHPlaceSpecialization.twistChainVal; simp

theorem chainVal_width (a : JHPlaceSpecialization.TwistVec ↥SS) (s : ↥SS) (hs : 1 ≤ e s) :
    JHPlaceSpecialization.twistChainVal SS e a s (e s) = a.aZ' := by
  unfold JHPlaceSpecialization.twistChainVal
  rw [if_neg (by omega), if_pos le_rfl]

open Classical in

theorem sum_annulus_eq_sum_circleDeg (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS)
    (hdep : ∀ V ∈ D.support, V ∈ (An s).dom → 0 ≤ pos s V ∧ pos s V ≤ e s) :
    ∑ V ∈ D.support with V ∈ (An s).dom, (D V : ℚ) =
      ∑ d ∈ Finset.range (e s + 1), JHPlaceSpecialization.twistCircleDeg SS An pos D s d := by
  unfold JHPlaceSpecialization.twistCircleDeg
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Finset.mem_filter] at hV
  obtain ⟨hVs, hVd⟩ := hV
  rw [← Finset.mul_sum, CoupledH.tent_sum _ _ (hdep V hVs hVd).1 (hdep V hVs hVd).2, mul_one]

open Classical in

theorem posMoment_eq_sum_mul_circleDeg (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS)
    (hdep : ∀ V ∈ D.support, V ∈ (An s).dom → 0 ≤ pos s V ∧ pos s V ≤ e s) :
    JHPlaceSpecialization.twistPosMoment SS An pos D s =
      ∑ d ∈ Finset.range (e s + 1), (d : ℚ) * JHPlaceSpecialization.twistCircleDeg SS An pos D s d := by
  unfold JHPlaceSpecialization.twistPosMoment JHPlaceSpecialization.twistCircleDeg
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Finset.mem_filter] at hV
  obtain ⟨hVs, hVd⟩ := hV
  have hre : ∑ d ∈ Finset.range (e s + 1), (d : ℚ) * ((D V : ℚ) * max 0 (1 - |pos s V - d|)) =
      (D V : ℚ) * ∑ d ∈ Finset.range (e s + 1), (d : ℚ) * max 0 (1 - |pos s V - d|) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [hre, CoupledH.tent_sum_mul _ _ (hdep V hVs hVd).1 (hdep V hVs hVd).2]

theorem sum_range_circleDeg_eq (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (a : JHPlaceSpecialization.TwistVec ↥SS) (s : ↥SS) (hs : 1 ≤ e s)
    (hcirc : ∀ d : ℕ, 1 ≤ d → d + 1 ≤ e s →
      JHPlaceSpecialization.twistCircleDeg SS An pos D s d =
        -((JHPlaceSpecialization.twistChainVal SS e a s (d - 1) - 2 * JHPlaceSpecialization.twistChainVal SS e a s d +
            JHPlaceSpecialization.twistChainVal SS e a s (d + 1) : ℤ) : ℚ))
    (hint0 : (JHPlaceSpecialization.twistCircleDeg SS An pos D s 0).den = 1)
    (hintw : (JHPlaceSpecialization.twistCircleDeg SS An pos D s (e s)).den = 1) :
    ∑ d ∈ Finset.range (e s + 1), JHPlaceSpecialization.twistCircleDeg SS An pos D s d =
      ((JHPlaceSpecialization.twistEndOrderFst SS e An pos a D s + JHPlaceSpecialization.twistEndOrderSnd SS e An pos a D s : ℤ) : ℚ) := by
  have h0 : JHPlaceSpecialization.twistCircleDeg SS An pos D s 0 = ((JHPlaceSpecialization.twistEndShareFst SS An pos D s : ℤ) : ℚ) := by
    unfold JHPlaceSpecialization.twistEndShareFst
    rw [if_pos hint0]
    exact (Rat.coe_int_num_of_den_eq_one hint0).symm
  have hE : JHPlaceSpecialization.twistCircleDeg SS An pos D s (e s) = ((JHPlaceSpecialization.twistEndShareSnd SS e An pos D s : ℤ) : ℚ) := by
    unfold JHPlaceSpecialization.twistEndShareSnd
    rw [if_pos hintw]
    exact (Rat.coe_int_num_of_den_eq_one hintw).symm
  have hmid : ∑ d ∈ Finset.Ico 1 (e s), JHPlaceSpecialization.twistCircleDeg SS An pos D s d =
      (((JHPlaceSpecialization.twistChainVal SS e a s 1 - JHPlaceSpecialization.twistChainVal SS e a s 0) +
        (JHPlaceSpecialization.twistChainVal SS e a s (e s - 1) - JHPlaceSpecialization.twistChainVal SS e a s (e s)) : ℤ) : ℚ) := by
    obtain ⟨n, hn⟩ : ∃ n, e s = n + 1 := ⟨e s - 1, by omega⟩
    rw [Finset.sum_congr rfl (fun d hd => hcirc d (Finset.mem_Ico.mp hd).1
      (by have := (Finset.mem_Ico.mp hd).2; omega)), Finset.sum_neg_distrib, ← Int.cast_sum, hn,
      CoupledH.sum_second_diff]
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), zero_add, hmid, h0, hE]
  unfold JHPlaceSpecialization.twistEndOrderFst JHPlaceSpecialization.twistEndOrderSnd
  push_cast
  ring

theorem sum_range_mul_circleDeg_eq (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (a : JHPlaceSpecialization.TwistVec ↥SS) (s : ↥SS) (hs : 1 ≤ e s)
    (hcirc : ∀ d : ℕ, 1 ≤ d → d + 1 ≤ e s →
      JHPlaceSpecialization.twistCircleDeg SS An pos D s d =
        -((JHPlaceSpecialization.twistChainVal SS e a s (d - 1) - 2 * JHPlaceSpecialization.twistChainVal SS e a s d +
            JHPlaceSpecialization.twistChainVal SS e a s (d + 1) : ℤ) : ℚ))
    (hintw : (JHPlaceSpecialization.twistCircleDeg SS An pos D s (e s)).den = 1) :
    ∑ d ∈ Finset.range (e s + 1), (d : ℚ) * JHPlaceSpecialization.twistCircleDeg SS An pos D s d =
      ((e s * JHPlaceSpecialization.twistEndOrderSnd SS e An pos a D s + (a.aZ' - a.aZ) : ℤ) : ℚ) := by
  have hE : JHPlaceSpecialization.twistCircleDeg SS An pos D s (e s) = ((JHPlaceSpecialization.twistEndShareSnd SS e An pos D s : ℤ) : ℚ) := by
    unfold JHPlaceSpecialization.twistEndShareSnd
    rw [if_pos hintw]
    exact (Rat.coe_int_num_of_den_eq_one hintw).symm
  have hmid : ∑ d ∈ Finset.Ico 1 (e s), (d : ℚ) * JHPlaceSpecialization.twistCircleDeg SS An pos D s d =
      ((e s * (JHPlaceSpecialization.twistChainVal SS e a s (e s - 1) - JHPlaceSpecialization.twistChainVal SS e a s (e s)) + (a.aZ' - a.aZ) : ℤ) : ℚ) := by
    have hre : ∀ d ∈ Finset.Ico 1 (e s), (d : ℚ) * JHPlaceSpecialization.twistCircleDeg SS An pos D s d =
        (((d : ℤ) * (-(JHPlaceSpecialization.twistChainVal SS e a s (d - 1) - 2 * JHPlaceSpecialization.twistChainVal SS e a s d +
            JHPlaceSpecialization.twistChainVal SS e a s (d + 1))) : ℤ) : ℚ) := by
      intro d hd
      rw [hcirc d (Finset.mem_Ico.mp hd).1 (by have := (Finset.mem_Ico.mp hd).2; omega)]
      push_cast
      ring
    rw [Finset.sum_congr rfl hre, ← Int.cast_sum, CoupledH.sum_mul_neg_laplacian _ _ hs, chainVal_zero,
      chainVal_width SS e a s hs]
  rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), Nat.cast_zero, zero_mul,
    zero_add, hmid, hE]
  unfold JHPlaceSpecialization.twistEndOrderSnd
  push_cast
  ring

open Classical in

theorem sum_annulus_eq_endOrders (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (a : JHPlaceSpecialization.TwistVec ↥SS) (s : ↥SS) (hs : 1 ≤ e s)
    (hcirc : ∀ d : ℕ, 1 ≤ d → d + 1 ≤ e s →
      JHPlaceSpecialization.twistCircleDeg SS An pos D s d =
        -((JHPlaceSpecialization.twistChainVal SS e a s (d - 1) - 2 * JHPlaceSpecialization.twistChainVal SS e a s d +
            JHPlaceSpecialization.twistChainVal SS e a s (d + 1) : ℤ) : ℚ))
    (hdep : ∀ V ∈ D.support, V ∈ (An s).dom → 0 ≤ pos s V ∧ pos s V ≤ e s)
    (hint : ∀ d : ℕ, (JHPlaceSpecialization.twistCircleDeg SS An pos D s d).den = 1) :
    ∑ V ∈ D.support with V ∈ (An s).dom, D V =
      JHPlaceSpecialization.twistEndOrderFst SS e An pos a D s + JHPlaceSpecialization.twistEndOrderSnd SS e An pos a D s := by
  have h := sum_annulus_eq_sum_circleDeg SS e An pos D s hdep
  rw [sum_range_circleDeg_eq SS e An pos D a s hs hcirc (hint 0) (hint _), ← Int.cast_sum] at h
  exact_mod_cast h

open Classical in

theorem posMoment_eq (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (a : JHPlaceSpecialization.TwistVec ↥SS) (s : ↥SS) (hs : 1 ≤ e s)
    (hcirc : ∀ d : ℕ, 1 ≤ d → d + 1 ≤ e s →
      JHPlaceSpecialization.twistCircleDeg SS An pos D s d =
        -((JHPlaceSpecialization.twistChainVal SS e a s (d - 1) - 2 * JHPlaceSpecialization.twistChainVal SS e a s d +
            JHPlaceSpecialization.twistChainVal SS e a s (d + 1) : ℤ) : ℚ))
    (hdep : ∀ V ∈ D.support, V ∈ (An s).dom → 0 ≤ pos s V ∧ pos s V ≤ e s)
    (hint : ∀ d : ℕ, (JHPlaceSpecialization.twistCircleDeg SS An pos D s d).den = 1) :
    JHPlaceSpecialization.twistPosMoment SS An pos D s =
      ((e s * JHPlaceSpecialization.twistEndOrderSnd SS e An pos a D s + (a.aZ' - a.aZ) : ℤ) : ℚ) := by
  rw [posMoment_eq_sum_mul_circleDeg SS e An pos D s hdep, sum_range_mul_circleDeg_eq SS e An pos D a s hs hcirc (hint _)]

end Book

end CoupledH

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along SemilinearAut.IntertwinesAlong Place Place.ord_zero Divisor Divisor.degree Divisor.degZero SemilinearAut SemilinearAut.ofAlgAut SemilinearAut.divisor_smul_apply_smul Place.HasValue GluingData GluingData.admissible GluedPic0 GluedPic0.mk IsCurveOver IsCurveOver.finiteResidue Annulus Annulus.IsAttached SemilinearAut.restrict_smul"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ext ResidueField ord ord_zero toValuationSubring mk HasValue hasValue_one exists_isUnit_of_ord_eq_zero IsRational evalAt algebraMap_evalAt"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

open Classical

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

namespace HasValue p2m_export "AlgebraicCurve.Place.HasValue" "mul isUnit ne_zero inv" end HasValue
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
private theorem _root_.AlgebraicCurve.Place.HasValue.pow' {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using v.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.pow'"
namespace HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
private theorem _root_.AlgebraicCurve.Place.HasValue.zpow' {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) (n : ℤ) : v.HasValue (g ^ n) (a ^ n) := by
  rcases n with (n | n)
  · simpa using h.pow' n
  · rw [zpow_negSucc, zpow_negSucc]
    exact (h.pow' (n + 1)).inv (pow_ne_zero _ ha)

end HasValue
p2m_export "AlgebraicCurve.Place" "HasValue.zpow'"
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
theorem HasValue.prod' {ι : Type*} (s : Finset ι) {g : ι → F} {a : ι → K}
    (h : ∀ i ∈ s, v.HasValue (g i) (a i)) : v.HasValue (∏ i ∈ s, g i) (∏ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simpa using v.hasValue_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
theorem HasValue.prod_zpow' {ι : Type*} (s : Finset ι) {g : ι → F} {a : ι → K} (n : ι → ℤ)
    (h : ∀ i ∈ s, v.HasValue (g i) (a i)) (ha : ∀ i ∈ s, a i ≠ 0) :
    v.HasValue (∏ i ∈ s, g i ^ n i) (∏ i ∈ s, a i ^ n i) :=
  HasValue.prod' s fun i hi => (h i hi).zpow' (ha i hi) (n i)

end AlgebraicCurve.Place

namespace CoupledH

section Beta
open Classical
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem prod_zpow_eq_mul_prod_erase (W : Finset (Place K F)) (π : Place K F → F) (n : Place K F → ℤ)
    (w : Place K F) (hw : w ∈ W) :
    ∏ w' ∈ W, π w' ^ n w' = π w ^ n w * ∏ w' ∈ W.erase w, π w' ^ n w' := by
  rw [← Finset.mul_prod_erase W (fun w' => π w' ^ n w') hw]

private theorem _root_.CoupledH.hasValue_corrected_of_flat (v : Place K F) (W : Finset (Place K F)) (w : Place K F) (hw : w ∈ W)
    (ρ g ybar : F) (π : Place K F → F) (n : Place K F → ℤ) (o : ℤ)
    (hybar : ybar ≠ 0) (hπw : π w ≠ 0)
    (α lam c : K) (cross : Place K F → K)
    (hα : v.HasValue (ρ / ybar ^ o) α) (hlam : v.HasValue (ybar / π w) lam) (hlam0 : lam ≠ 0)
    (hg : v.HasValue g c)
    (hcross : ∀ w' ∈ W.erase w, v.HasValue (π w') (cross w')) (hcross0 : ∀ w' ∈ W.erase w, cross w' ≠ 0)
    (hflat : o + n w = 0) :
    v.HasValue (ρ * g * ∏ w' ∈ W, π w' ^ n w') (α * lam ^ o * c * ∏ w' ∈ W.erase w, cross w' ^ n w') := by

  have hρ : ρ = (ρ / ybar ^ o) * (ybar / π w) ^ o * π w ^ o := by
    rw [div_zpow]
    field_simp
  have hnw : n w = -o := by omega
  rw [prod_zpow_eq_mul_prod_erase W π n w hw, hnw, hρ]
  have key : (ρ / ybar ^ o) * (ybar / π w) ^ o * π w ^ o * g * (π w ^ (-o) * ∏ w' ∈ W.erase w, π w' ^ n w')
      = (ρ / ybar ^ o) * (ybar / π w) ^ o * g * ∏ w' ∈ W.erase w, π w' ^ n w' := by
    rw [zpow_neg]
    field_simp
  rw [key]
  exact ((hα.mul (hlam.zpow' hlam0 o)).mul hg).mul (Place.HasValue.prod_zpow' (W.erase w) n hcross hcross0)
p2m_export "CoupledH" "hasValue_corrected_of_flat"
end Beta

section Unif
open Classical
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ne_zero_of_ord_ne_zero {v : Place K F} {g : F} (h : v.ord g ≠ 0) : g ≠ 0 := by
  rintro rfl; exact h (Place.ord_zero v)

theorem prod_zpow_ne_zero (W : Finset (Place K F)) (f : Place K F → F) (n : Place K F → ℤ)
    (hf : ∀ w ∈ W, f w ≠ 0) : ∏ w ∈ W, f w ^ n w ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun w hw => zpow_ne_zero _ (hf w hw)

theorem unifFst_facts (W : Finset (Place K F)) (Rc : Place K F → (Place K F →₀ ℤ))
    (π : Place K F → F)
    (hunif : ∀ w' ∈ W, ∀ v : Place K F, (Finsupp.single w' (1 : ℤ) + Rc w') v = v.ord (π w'))
    (hoff : ∀ w' ∈ W, ∀ v ∈ W, Rc w' v = 0) :
    (∀ w' ∈ W, π w' ≠ 0) ∧
    (∀ w ∈ W, ∀ w' ∈ W, w.ord (π w') = if w' = w then 1 else 0) := by
  have key : ∀ w ∈ W, ∀ w' ∈ W, w.ord (π w') = if w' = w then 1 else 0 := by
    intro w hw w' hw'
    rw [← hunif w' hw' w, Finsupp.add_apply, hoff w' hw' w hw, add_zero, Finsupp.single_apply]
  refine ⟨fun w' hw' => ne_zero_of_ord_ne_zero (v := w') ?_, key⟩
  rw [key w' hw' w' hw', if_pos rfl]
  exact one_ne_zero

theorem unifSnd_facts (W : Finset (Place K F)) (Rc : Place K F → (Place K F →₀ ℤ))
    (φ : Place K F → Place K F) (hφ : Function.Injective φ) (hφW : ∀ w ∈ W, φ w ∈ W)
    (π' : Place K F → F)
    (hunif : ∀ w' ∈ W, ∀ v : Place K F, (Finsupp.single (φ w') (1 : ℤ) + Rc w') v = v.ord (π' w'))
    (hoff : ∀ w' ∈ W, ∀ v ∈ W, Rc w' v = 0) :
    (∀ w' ∈ W, π' w' ≠ 0) ∧
    (∀ w ∈ W, ∀ w' ∈ W, (φ w).ord (π' w') = if w' = w then 1 else 0) := by
  have key : ∀ w ∈ W, ∀ w' ∈ W, (φ w).ord (π' w') = if w' = w then 1 else 0 := by
    intro w hw w' hw'
    rw [← hunif w' hw' (φ w), Finsupp.add_apply, hoff w' hw' (φ w) (hφW w hw), add_zero, Finsupp.single_apply]
    by_cases h : w' = w
    · subst h; simp
    · rw [if_neg (fun h' => h (hφ h')), if_neg h]
  refine ⟨fun w' hw' => ne_zero_of_ord_ne_zero (v := φ w') ?_, key⟩
  rw [key w' hw' w' hw', if_pos rfl]
  exact one_ne_zero

theorem unif_facts {ι : Type*} (I : Finset ι) (node : ι → Place K F) (hnode : Set.InjOn node I)
    (Rc : ι → (Place K F →₀ ℤ)) (π : ι → F)
    (hunif : ∀ i ∈ I, ∀ v : Place K F, (Finsupp.single (node i) (1 : ℤ) + Rc i) v = v.ord (π i))
    (hoff : ∀ i ∈ I, ∀ j ∈ I, Rc i (node j) = 0) :
    (∀ i ∈ I, π i ≠ 0) ∧
    (∀ j ∈ I, ∀ i ∈ I, (node j).ord (π i) = if i = j then 1 else 0) := by
  have key : ∀ j ∈ I, ∀ i ∈ I, (node j).ord (π i) = if i = j then 1 else 0 := by
    intro j hj i hi
    rw [← hunif i hi (node j), Finsupp.add_apply, hoff i hi j hj, add_zero, Finsupp.single_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (fun h' => h (hnode hi hj h')), if_neg h]
  refine ⟨fun i hi => ne_zero_of_ord_ne_zero (v := node i) ?_, key⟩
  rw [key i hi i hi, if_pos rfl]
  exact one_ne_zero

end Unif

theorem surjective_algebraMap_residueField {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (v : Place K F) : Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

end CoupledH

namespace CsHGen

section Flat
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_corrected_of_flat {ι : Type*} [DecidableEq ι] (v : Place K F) (I : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ I)
    (ρ g ybar : F) (π : ι → F) (n : ι → ℤ) (o : ℤ)
    (hybar : ybar ≠ 0) (hπ : π i₀ ≠ 0)
    (α lam c : K) (cross : ι → K)
    (hα : v.HasValue (ρ / ybar ^ o) α) (hlam : v.HasValue (ybar / π i₀) lam) (hlam0 : lam ≠ 0)
    (hg : v.HasValue g c)
    (hcross : ∀ i ∈ I.erase i₀, v.HasValue (π i) (cross i)) (hcross0 : ∀ i ∈ I.erase i₀, cross i ≠ 0)
    (hflat : o + n i₀ = 0) :
    v.HasValue (ρ * g * ∏ i ∈ I, π i ^ n i) (α * lam ^ o * c * ∏ i ∈ I.erase i₀, cross i ^ n i) := by
  have hρ : ρ = (ρ / ybar ^ o) * (ybar / π i₀) ^ o * π i₀ ^ o := by
    rw [div_zpow]
    field_simp
  have hn : n i₀ = -o := by omega
  rw [← Finset.mul_prod_erase I (fun i => π i ^ n i) hi₀, hn, hρ]
  have key : (ρ / ybar ^ o) * (ybar / π i₀) ^ o * π i₀ ^ o * g * (π i₀ ^ (-o) * ∏ i ∈ I.erase i₀, π i ^ n i)
      = (ρ / ybar ^ o) * (ybar / π i₀) ^ o * g * ∏ i ∈ I.erase i₀, π i ^ n i := by
    rw [zpow_neg]
    field_simp
  rw [key]
  exact ((hα.mul (hlam.zpow' hlam0 o)).mul hg).mul (Place.HasValue.prod_zpow' (I.erase i₀) n hcross hcross0)

theorem hasValue_evalAt_of_ord_eq_zero (v : Place K F) (hv : v.IsRational) {g : F} (hg0 : g ≠ 0) (hord : v.ord g = 0) :
    v.HasValue g (v.evalAt g) ∧ v.evalAt g ≠ 0 := by
  obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg0 hord
  have h1 : IsLocalRing.residue (R := ↥v.toValuationSubring) ⟨g, hm⟩ = algebraMap K v.ResidueField (v.evalAt g) :=
    (v.algebraMap_evalAt hv hm).symm
  refine ⟨⟨hm, h1⟩, fun h0 => ?_⟩
  rw [h0, map_zero] at h1
  exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu) h1

end Flat

section Key

theorem key_of_ratio {k : Type*} [Field k] {ι : Type*} (T : Finset ι)
    (AF Θ : kˣ) (cr₁ cr₂ : ι → kˣ) (e₁ e₂ : ι → ℤ)
    (α₁ α₂ u0 lam mu av bv : kˣ) (o₁ o₂ n₁ n₂ dX dDf : ℤ)
    (hratio : α₁ / α₂ = (-1) ^ dDf * u0 ^ o₂ * Θ)
    (hν : av / bv = (-1) ^ dX * u0 ^ n₂ * lam ^ n₁ * (mu ^ n₂)⁻¹ * AF *
        ∏ i ∈ T, ((cr₁ i) ^ (e₁ i))⁻¹ * (cr₂ i) ^ (e₂ i))
    (hΘ : Θ * AF = 1) (hd : dDf = -dX)
    (hflat₁ : o₁ + n₁ = 0) (hflat₂ : o₂ + n₂ = 0) :
    (α₁ : k) * (lam : k) ^ o₁ * (av : k) * ∏ i ∈ T, (cr₁ i : k) ^ (e₁ i) =
      (α₂ : k) * (mu : k) ^ o₂ * (bv : k) * ∏ i ∈ T, (cr₂ i : k) ^ (e₂ i) := by
  have ho₁ : o₁ = -n₁ := by omega
  have ho₂ : o₂ = -n₂ := by omega
  suffices hK : α₁ * lam ^ o₁ * av * ∏ i ∈ T, (cr₁ i) ^ (e₁ i) = α₂ * mu ^ o₂ * bv * ∏ i ∈ T, (cr₂ i) ^ (e₂ i) by
    have := congrArg (fun u : kˣ => (u : k)) hK
    push_cast at this
    exact this
  have hT : (∏ i ∈ T, ((cr₁ i) ^ (e₁ i))⁻¹ * (cr₂ i) ^ (e₂ i)) * ∏ i ∈ T, (cr₁ i) ^ (e₁ i) =
      ∏ i ∈ T, (cr₂ i) ^ (e₂ i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have hsign : ((-1 : kˣ) ^ dDf) * (-1) ^ dX = 1 := by
    rw [hd, ← zpow_add, neg_add_cancel, zpow_zero]
  have hlam : lam ^ o₁ * lam ^ n₁ = 1 := by rw [ho₁, ← zpow_add, neg_add_cancel, zpow_zero]
  have hu0 : u0 ^ o₂ * u0 ^ n₂ = 1 := by rw [ho₂, ← zpow_add, neg_add_cancel, zpow_zero]
  have hα : α₁ = α₂ * ((-1) ^ dDf * u0 ^ o₂ * Θ) := by
    rw [← hratio, mul_div_cancel]
  have hav : av = bv * ((-1) ^ dX * u0 ^ n₂ * lam ^ n₁ * (mu ^ n₂)⁻¹ * AF *
      ∏ i ∈ T, ((cr₁ i) ^ (e₁ i))⁻¹ * (cr₂ i) ^ (e₂ i)) := by
    rw [← hν, mul_div_cancel]
  rw [hα, hav]
  set Sgm := (-1 : kˣ) ^ dDf
  set Sgp := (-1 : kˣ) ^ dX
  set U' := u0 ^ o₂
  set U0 := u0 ^ n₂
  set L := lam ^ n₁
  set Lo := lam ^ o₁
  set Mn := mu ^ n₂
  set C := ∏ i ∈ T, ((cr₁ i) ^ (e₁ i))⁻¹ * (cr₂ i) ^ (e₂ i)
  set P₁ := ∏ i ∈ T, (cr₁ i) ^ (e₁ i)
  set P₂ := ∏ i ∈ T, (cr₂ i) ^ (e₂ i)
  have hM : mu ^ o₂ = Mn⁻¹ := by rw [ho₂, zpow_neg]
  calc α₂ * (Sgm * U' * Θ) * Lo * (bv * (Sgp * U0 * L * Mn⁻¹ * AF * C)) * P₁
      = α₂ * bv * Mn⁻¹ * (U' * U0) * (Sgm * Sgp) * (Θ * AF) * (Lo * L) * (C * P₁) := by ac_rfl
    _ = α₂ * bv * Mn⁻¹ * P₂ := by rw [hu0, hsign, hΘ, hlam, hT]; simp only [mul_one]
    _ = α₂ * mu ^ o₂ * bv * P₂ := by rw [hM]; ac_rfl

end Key

section Ang
open Classical

noncomputable def redUnit {L : Type*} [Field L] (A : ValuationSubring L) (q : ℚ) (x : L) : (IsLocalRing.ResidueField ↥A)ˣ :=
  if h : q.den = 1 ∧ ∃ hmem : x ∈ A, IsLocalRing.residue (R := ↥A) ⟨_, hmem⟩ ≠ 0
  then Units.mk0 (IsLocalRing.residue (R := ↥A) ⟨_, h.2.choose⟩) h.2.choose_spec else 1

theorem redUnit_val_of {L : Type*} [Field L] (A : ValuationSubring L) (q : ℚ) (x : L) (hok : q.den = 1) (hmem : x ∈ A)
    (hres : IsLocalRing.residue (R := ↥A) ⟨_, hmem⟩ ≠ 0) :
    ((redUnit A q x : (IsLocalRing.ResidueField ↥A)ˣ) : IsLocalRing.ResidueField ↥A) = IsLocalRing.residue (R := ↥A) ⟨_, hmem⟩ := by
  have h : q.den = 1 ∧ ∃ hmem : x ∈ A, IsLocalRing.residue (R := ↥A) ⟨_, hmem⟩ ≠ 0 := ⟨hok, hmem, hres⟩
  unfold redUnit
  rw [dif_pos h, Units.val_mk0]

theorem redUnit_of_not {L : Type*} [Field L] (A : ValuationSubring L) (q : ℚ) (x : L)
    (h : ¬ (q.den = 1 ∧ ∃ hmem : x ∈ A, IsLocalRing.residue (R := ↥A) ⟨_, hmem⟩ ≠ 0)) : redUnit A q x = 1 := by
  unfold redUnit
  rw [dif_neg h]

theorem inv_eq_coe_unit_inv {L : Type*} [Field L] (A : ValuationSubring L) {x : L} {hmem : x ∈ A} (u : (↥A)ˣ)
    (hu : (u : ↥A) = ⟨x, hmem⟩) : x⁻¹ = (((u⁻¹ : (↥A)ˣ) : ↥A) : L) := by
  have hxu : ((u : ↥A) : L) = x := congrArg Subtype.val hu
  have hmul : x * (((u⁻¹ : (↥A)ˣ) : ↥A) : L) = 1 := by
    rw [← hxu, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  exact (inv_eq_of_mul_eq_one_right hmul)

theorem redUnit_inv_mul {L : Type*} [Field L] (A : ValuationSubring L) (q : ℚ) (x : L) :
    redUnit A q x⁻¹ * redUnit A q x = 1 := by
  by_cases hx : q.den = 1 ∧ ∃ hmem : x ∈ A, IsLocalRing.residue (R := ↥A) ⟨_, hmem⟩ ≠ 0
  · obtain ⟨hok, hmem, hres⟩ := hx
    have hu : IsUnit (⟨x, hmem⟩ : ↥A) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
    obtain ⟨u, hu'⟩ := hu
    have hxinv : x⁻¹ = (((u⁻¹ : (↥A)ˣ) : ↥A) : L) := inv_eq_coe_unit_inv A u hu'
    have hmem' : x⁻¹ ∈ A := by rw [hxinv]; exact SetLike.coe_mem _
    have hsub : (⟨x⁻¹, hmem'⟩ : ↥A) = ((u⁻¹ : (↥A)ˣ) : ↥A) := Subtype.ext hxinv
    have hres' : IsLocalRing.residue (R := ↥A) ⟨_, hmem'⟩ ≠ 0 := by
      rw [hsub]
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (Units.isUnit _)
    apply Units.ext
    rw [Units.val_mul, redUnit_val_of A q x⁻¹ hok hmem' hres', redUnit_val_of A q x hok hmem hres, Units.val_one,
      ← map_mul, ← map_one (IsLocalRing.residue (R := ↥A))]
    congr 1
    rw [hsub, ← hu', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · rw [redUnit_of_not A q x hx, mul_one]
    apply redUnit_of_not
    rintro ⟨hok, hmem', hres'⟩
    apply hx
    have hu : IsUnit (⟨x⁻¹, hmem'⟩ : ↥A) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres'
    obtain ⟨u, hu'⟩ := hu
    have hxeq : x = (((u⁻¹ : (↥A)ˣ) : ↥A) : L) := by
      rw [← inv_inv x]
      exact inv_eq_coe_unit_inv A u hu'
    have hmem : x ∈ A := by rw [hxeq]; exact SetLike.coe_mem _
    refine ⟨hok, hmem, ?_⟩
    have hsub : (⟨x, hmem⟩ : ↥A) = ((u⁻¹ : (↥A)ˣ) : ↥A) := Subtype.ext hxeq
    rw [hsub]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (Units.isUnit _)

theorem redUnit_congr {L : Type*} [Field L] (A : ValuationSubring L) (q q' : ℚ) (x : L) (hq : q.den = q'.den) :
    redUnit A q x = redUnit A q' x := by
  by_cases hx : q.den = 1 ∧ ∃ hmem : x ∈ A, IsLocalRing.residue (R := ↥A) ⟨_, hmem⟩ ≠ 0
  · obtain ⟨hok, hmem, hres⟩ := hx
    apply Units.ext
    rw [redUnit_val_of A q x hok hmem hres, redUnit_val_of A q' x (hq ▸ hok) hmem hres]
  · rw [redUnit_of_not A q x hx, redUnit_of_not A q' x (fun h => hx ⟨hq.symm ▸ h.1, h.2⟩)]

end Ang

end CsHGen

open Classical in
set_option maxHeartbeats 3200000 in
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

    (hVSlope : ∀ An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
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
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))) →
      ∀ k : ℕ, (∀ s : ↥SS, e s ∣ k) →
        ∃ (f : ↥(xHFunctionFieldBar M H)) (c : AlgebraicClosure ℚ) (hc : c • f ∈ Rpd.R₁.integers),
          f ≠ 0 ∧ Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
          (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) → Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G) ∧
          (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) →
            (∀ s ∈ SS, Psp.reduceFst α hα V ≠ s.1) → V.ord f = 0) ∧
          (∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
            v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0) ∧
          (∀ s : ↥SS, ∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord f = 0 ∧
            ∃ h : P.evalAt f * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hFixReadFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → V.ord g = 0) →
        v.ord (Rpd.R₁.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0)
    (hFixReadSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → V.ord g = 0) →
        v.ord (Rpd.R₂.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0)

    (hFixRegFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₁.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hFixRegSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₂.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

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
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
    (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)
    (hpos : JHPlaceSpecialization.AnnulusPositionLaw SS e An pos)
    (hposσ : ∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      pos s ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = pos s V)
    (hposD : ∀ (s : ↥SS) (d : ℕ), 0 < d → d < e s → ∃ V ∈ (An s).dom,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ pos s V = d)

    (dat : JHPlaceSpecialization.TwistedFibreDatum (p := p) (M := M) (H := H) (hpM := hpM) (A := A) SS)

    (hunifFst : ∀ s : ↥SS,
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (Finsupp.single (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 (1 : ℤ) + dat.corrFst s) v = v.ord (dat.unifFst s)) ∧
      (∀ s' ∈ SS, dat.corrFst s s'.1 = 0 ∧ dat.corrFst s s'.2 = 0) ∧ Divisor.degree (dat.corrFst s) = -1)
    (hunifSnd : ∀ s : ↥SS,
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (Finsupp.single (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2 (1 : ℤ) + dat.corrSnd s) v = v.ord (dat.unifSnd s)) ∧
      (∀ s' ∈ SS, dat.corrSnd s s'.1 = 0 ∧ dat.corrSnd s s'.2 = 0) ∧ Divisor.degree (dat.corrSnd s) = -1)

    (hu0 : ∀ s : ↥SS, ∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u ∧ IsLocalRing.residue ↥A u = dat.u0 s)

    (hlam : ∀ (s : ↥SS) (h₁ : JHPlaceSpecialization.flipParam SS An s ∈ Rpd.R₁.integers),
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.HasValue
        ((Rpd.R₁.residue ⟨_, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) / dat.unifFst s) (dat.lam s : ResidueField ↥A))
    (hmu : ∀ (s : ↥SS) (h₂ : (An s).param ∈ Rpd.R₂.integers),
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.HasValue
        ((Rpd.R₂.residue ⟨_, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) / dat.unifSnd s) (dat.mu s : ResidueField ↥A))
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
      (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1))
    (a : JHPlaceSpecialization.TwistVec ↥SS)
    (ha : Psp.IsTwistOf α (θ.toAlgHom.comp α) hα hβ δ SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)))
    (hadm : Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS)
    (hsp : GluedPic0.mk SS ⟨Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm⟩ = 0)

    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hQ₁ : ∀ i, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (Q₁ i)) (hQ₂ : ∀ j, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ (Q₂ j))
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hE0 : 0 ≤ E)
    (f : ↥(xHFunctionFieldBar M H)) (hf0 : f ≠ 0)
    (hdivf : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) V = V.ord f) :
    ∃ δ' : ℚ,

      (∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • f, h⟩ ≠ 0 →
        ∀ s : ↥SS, δ' ≤ (e s : ℚ) * ((((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c • f, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : ℤ) : ℚ) + (JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s : ℚ))) ∧

      (∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨c • f, h⟩ ≠ 0 →
        ∀ s : ↥SS, -((e s : ℚ) * ((((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨c • f, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : ℤ) : ℚ) + (JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s : ℚ))) ≤ δ') ∧

      (∃ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ Rpd.R₁.integers) (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0 ∧
        ∀ (g₁ g₂ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (av bv : ↥SS → (ResidueField ↥A)ˣ),
          (∀ v, (Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).1 v = v.ord g₁) →
          (∀ v, (Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).2.1 v = v.ord g₂) →
          (∀ s : ↥SS,
            (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.HasValue g₁ (av s) ∧ (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.HasValue g₂ (bv s)) →
          ((Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).2.2 = fun s => Additive.ofMul (av s / bv s)) →
          ∀ s : ↥SS, δ' = 0 →
            (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨c₂ • f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) + JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s = 0 →
            ((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) + JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s = 0 ∧
             ∃ c : (ResidueField ↥A)ˣ,
               (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.HasValue
                 ((Rpd.R₁.residue ⟨c₁ • f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) * g₁ * ∏ s' : ↥SS, dat.unifFst s' ^ JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s') (c : ResidueField ↥A) ∧
               (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.HasValue
                 ((Rpd.R₂.residue ⟨c₂ • f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) * g₂ * ∏ s' : ↥SS, dat.unifSnd s' ^ JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s') (c : ResidueField ↥A))) := by
  classical
  have hCH := ModularCurve.JHPlaceSpecialization.exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_twistSp_eq_zero_of_annulus p M H hpM hpM2 hHp A hA θ α hα hβ hα_coe pb hpb δ hδ SS hSS Psp Rpd hFix hTD hmodel hO hreg hnv hθgal hβ_coe hFixFin hLFst hLSnd hUnit hcusp horientInf horient0 e he hAnn hVSlope hFixReadFst hFixReadSnd hFixRegFst hFixRegSnd An hAn pos hpos hposσ hposD dat hunifFst hunifSnd hu0 hlam hmu X hXst hXsupp a ha hadm hsp Q₁ Q₂ hQ₁ hQ₂ E hE0 f hf0 hdivf
  obtain ⟨δ', hA₁, hA₂, hA₃, hA₄⟩ := hCH
  refine ⟨δ', hA₁, hA₂, ?_⟩

  obtain ⟨c₁, h₁, hr₁⟩ := Rpd.R₁.exists_smul_mem f hf0
  by_cases hδ0 : δ' = 0
  swap
  ·
    obtain ⟨c₂, h₂, hr₂⟩ := Rpd.R₂.exists_smul_mem f hf0
    refine ⟨c₁, h₁, c₂, h₂, hr₁, hr₂, ?_⟩
    intro g₁ g₂ av bv _ _ _ _ s hδ _
    exact absurd hδ hδ0

  obtain ⟨h₂, hr₂⟩ := hA₄.mp hδ0 c₁ h₁ hr₁
  refine ⟨c₁, h₁, _, h₂, hr₁, hr₂, ?_⟩
  intro g₁ g₂ av bv hdivg₁ hdivg₂ hgvals hgratio s _hδ hflat₂
  obtain ⟨hflat₁, hEs⟩ := hA₃ hδ0 c₁ h₁ _ h₂ hr₁ hr₂ s hflat₂
  refine ⟨hflat₁, ?_⟩

  have hφinj := (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (ΓN p M H hpM)).1
  have hX1 : ∀ s₁ ∈ SS, ∀ s₂ ∈ SS, s₁.1 = s₂.1 → s₁ = s₂ := by
    intro s₁ hs₁ s₂ hs₂ h
    have e₁ := (mem_ssNodePairsQExp_iff _).mp ((hSS s₁).mp hs₁)
    have e₂ := (mem_ssNodePairsQExp_iff _).mp ((hSS s₂).mp hs₂)
    exact Prod.ext h (hφinj (e₁.2.symm.trans (h.trans e₂.2)))
  have hX1' : ∀ s₁ ∈ SS, ∀ s₂ ∈ SS, s₁.2 = s₂.2 → s₁ = s₂ := by
    intro s₁ hs₁ s₂ hs₂ h
    have e₁ := (mem_ssNodePairsQExp_iff _).mp ((hSS s₁).mp hs₁)
    have e₂ := (mem_ssNodePairsQExp_iff _).mp ((hSS s₂).mp hs₂)
    refine Prod.ext ?_ h
    rw [e₁.2, e₂.2, h]
  have hs2 := (mem_ssNodePairsQExp_iff _).mp ((hSS s).mp s.2)
  have hX2 : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 →
      ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V := by
    intro V hV
    have hfix2 := hFix (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2 hs2.1
    have hFixed1 : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 := by
      rw [hs2.2]; exact hfix2.2
    refine ⟨fun hst => hst.2 (hV ▸ hFixed1), fun hst => hst.2 ?_⟩
    have h3 : qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V) =
        qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2 := hst.1.symm.trans (hV.trans hs2.2)
    rw [hφinj h3]
    exact hfix2.1
  have hdom : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V ∈ (An s).dom ↔ Psp.reduceFst α hα V = (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 :=
    fun V => ((hAn s).1 V).trans ⟨fun h => h.1, fun h => ⟨h, hX2 V h⟩⟩

  obtain ⟨Df, hDfdef⟩ : ∃ Df : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Df = E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) := ⟨_, rfl⟩
  have hDf : ∀ V, Df V = V.ord f := fun V => by rw [hDfdef]; exact hdivf V
  have hneg : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 → Df V = -((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V) := by
    intro V hV
    obtain ⟨hns1, hns2⟩ := hX2 V hV
    have hE : E V = 0 := hEs V hV
    have hE₁ : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) V = 0 := by
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hns1 (hQ₁ i)
    have hE₂ : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) V = 0 := by
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hns2 (hQ₂ j)
    rw [hDfdef, Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.add_apply, hE, hE₁, hE₂]
    ring
  have hfilt : Df.support.filter (fun V => V ∈ (An s).dom) = (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support.filter (fun V => V ∈ (An s).dom) := by
    ext V
    simp only [Finset.mem_filter, Finsupp.mem_support_iff]
    constructor
    · rintro ⟨h0, hV⟩
      refine ⟨fun h => h0 ?_, hV⟩
      rw [hneg V ((hdom V).mp hV), h, neg_zero]
    · rintro ⟨h0, hV⟩
      refine ⟨?_, hV⟩
      rw [hneg V ((hdom V).mp hV)]
      exact neg_ne_zero.mpr h0
  have hdegDf : JHPlaceSpecialization.twistAnnulusDeg SS An Df s = -JHPlaceSpecialization.twistAnnulusDeg SS An (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s := by
    unfold JHPlaceSpecialization.twistAnnulusDeg
    rw [hfilt, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun V hV => hneg V ((hdom V).mp (Finset.mem_filter.mp hV).2)
  have hmomDf : JHPlaceSpecialization.twistPosMoment SS An pos Df s = -JHPlaceSpecialization.twistPosMoment SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s := by
    unfold JHPlaceSpecialization.twistPosMoment
    rw [hfilt, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun V hV => ?_
    rw [hneg V ((hdom V).mp (Finset.mem_filter.mp hV).2)]
    push_cast
    ring

  have he1 : 1 ≤ e s := he s
  have hcirc := ha.2.2 s
  have hdep : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support, V ∈ (An s).dom → 0 ≤ pos s V ∧ pos s V ≤ e s :=
    fun V _ hV => ⟨(hpos s V hV).1.le, (hpos s V hV).2.1.le⟩
  have hint : ∀ d : ℕ, (JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s d).den = 1 := fun d =>
    ModularCurve.JHPlaceSpecialization.den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus p M H hpM hpM2 hHp A hA θ α hα hβ hα_coe pb hpb δ hδ SS hSS Psp Rpd hFix hTD hmodel hO hreg hnv hθgal hβ_coe hFixFin hLFst hLSnd hUnit hcusp horientInf horient0 e he hAnn An hAn pos hpos hposσ X hXst s d
  have hsumD := CoupledH.sum_annulus_eq_endOrders SS e An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) a s he1 hcirc hdep hint
  have hmomD := CoupledH.posMoment_eq SS e An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) a s he1 hcirc hdep hint

  obtain ⟨hz₂', hordz, hslope₂⟩ := (hAn s).2.2.2.2.2.1
  obtain ⟨hz₁, hordπ, hslope₁⟩ := (hAn s).2.2.2.2.2.2
  have hz₁' : JHPlaceSpecialization.flipParam SS An s ∈ Rpd.R₁.integers := hz₁
  have hdomσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ W ∈ (An s).dom, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • W ∈ (An s).dom := by
    intro σ hσ W hW
    rw [hdom] at hW ⊢
    rw [CsHEqv.reduceFst_smul Psp α hα hα_coe σ hσ]
    exact hW
  have hXσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V := by
    intro σ hσ V
    have hsm := SemilinearAut.divisor_smul_apply_smul (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V
    rw [hXst σ hσ] at hsm
    exact hsm
  have hDfst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V ∈ (An s).dom, Df ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = Df V := by
    intro σ hσ V hV
    rw [hneg V ((hdom V).mp hV), hneg _ ((hdom _).mp (hdomσ σ hσ V hV)), hXσ σ hσ V]
  have hmom : (JHPlaceSpecialization.twistPosMoment SS An pos Df s).den = 1 := by
    rw [hmomDf, hmomD, ← Int.cast_neg]
    exact Rat.den_intCast _
  have hN : JHPlaceSpecialization.twistAnnulusDeg SS An Df s = (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) + (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨(c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := by
    rw [hdegDf]
    unfold JHPlaceSpecialization.twistAnnulusDeg
    rw [hsumD]
    omega

  obtain ⟨α₁, α₂, hv₁, hv₂, hratio⟩ :=
    ModularCurve.JHPlaceSpecialization.exists_hasValue_residue_div_pow_and_div_eq_twistAngFactor_of_coupled_of_inertiaStable p M H hpM hpM2 hHp A hA θ α hα hβ hα_coe pb hpb δ hδ SS hSS Psp Rpd hFix hTD hmodel hO hreg hnv hθgal hβ_coe hFixFin hLFst hLSnd hUnit hcusp horientInf horient0 e he hAnn hVSlope hFixReadFst hFixReadSnd hFixRegFst hFixRegSnd An hAn pos hpos hposσ hposD dat hunifFst hunifSnd hu0 hlam hmu X hXst hXsupp a ha hadm hsp
      s f hf0 Df hDf hDfst hmom c₁ h₁ hr₁ (a.aZ' - a.aZ) h₂ hr₂ hz₁' hz₂' hN

  have hT : ModularGroup.T ∈ ΓN p M H hpM := by
    apply ModularCurve.Gamma1_le_GammaH
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  haveI : (ΓN p M H hpM).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
  haveI hCO : IsCurveOver (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A) (ΓN p M H hpM) hT
  have hrat : ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v.IsRational := fun v =>
    CoupledH.surjective_algebraMap_residueField v

  have hinj1 : Set.InjOn (fun s' : ↥SS => (s' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1) (Finset.univ : Finset ↥SS) :=
    fun s₁ _ s₂ _ h => Subtype.ext (hX1 _ s₁.2 _ s₂.2 h)
  have hinj2 : Set.InjOn (fun s' : ↥SS => (s' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2) (Finset.univ : Finset ↥SS) :=
    fun s₁ _ s₂ _ h => Subtype.ext (hX1' _ s₁.2 _ s₂.2 h)
  obtain ⟨hπ₁0, hπ₁ord⟩ := CoupledH.unif_facts (Finset.univ : Finset ↥SS) (fun s' : ↥SS => (s' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1) hinj1
    dat.corrFst dat.unifFst (fun s' _ v => (hunifFst s').1 v) (fun s' _ s'' _ => ((hunifFst s').2.1 s'' s''.2).1)
  obtain ⟨hπ₂0, hπ₂ord⟩ := CoupledH.unif_facts (Finset.univ : Finset ↥SS) (fun s' : ↥SS => (s' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2) hinj2
    dat.corrSnd dat.unifSnd (fun s' _ v => (hunifSnd s').1 v) (fun s' _ s'' _ => ((hunifSnd s').2.1 s'' s''.2).2)

  have hcross₁ : ∀ s' ∈ (Finset.univ : Finset ↥SS).erase s,
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.HasValue (dat.unifFst s') ((JHPlaceSpecialization.twistCrossFst SS dat s' s : (ResidueField ↥A)ˣ) : ResidueField ↥A) := by
    intro s' hs'
    have hne : s' ≠ s := (Finset.mem_erase.mp hs').1
    obtain ⟨hval, hne0⟩ := CsHGen.hasValue_evalAt_of_ord_eq_zero _ (hrat _) (hπ₁0 s' (Finset.mem_univ _))
      (by rw [hπ₁ord s (Finset.mem_univ _) s' (Finset.mem_univ _), if_neg hne])
    have hc : ((JHPlaceSpecialization.twistCrossFst SS dat s' s : (ResidueField ↥A)ˣ) : ResidueField ↥A) = (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.evalAt (dat.unifFst s') := by
      unfold JHPlaceSpecialization.twistCrossFst
      rw [dif_pos hne0, Units.val_mk0]
    rw [hc]
    exact hval
  have hcross₂ : ∀ s' ∈ (Finset.univ : Finset ↥SS).erase s,
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.HasValue (dat.unifSnd s') ((JHPlaceSpecialization.twistCrossSnd SS dat s' s : (ResidueField ↥A)ˣ) : ResidueField ↥A) := by
    intro s' hs'
    have hne : s' ≠ s := (Finset.mem_erase.mp hs').1
    obtain ⟨hval, hne0⟩ := CsHGen.hasValue_evalAt_of_ord_eq_zero _ (hrat _) (hπ₂0 s' (Finset.mem_univ _))
      (by rw [hπ₂ord s (Finset.mem_univ _) s' (Finset.mem_univ _), if_neg hne])
    have hc : ((JHPlaceSpecialization.twistCrossSnd SS dat s' s : (ResidueField ↥A)ˣ) : ResidueField ↥A) = (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.evalAt (dat.unifSnd s') := by
      unfold JHPlaceSpecialization.twistCrossSnd
      rw [dif_pos hne0, Units.val_mk0]
    rw [hc]
    exact hval

  have hlam' := hlam s hz₁'
  have hmu' := hmu s hz₂'
  have hybar0 : (Rpd.R₁.residue ⟨_, hz₁'⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ≠ 0 := by
    intro h0
    apply hlam'.ne_zero (Units.ne_zero _)
    rw [h0, zero_div]
  have hxbar0 : (Rpd.R₂.residue ⟨_, hz₂'⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ≠ 0 := by
    intro h0
    apply hmu'.ne_zero (Units.ne_zero _)
    rw [h0, zero_div]

  have hν : av s / bv s =
      (-1 : (ResidueField ↥A)ˣ) ^ (JHPlaceSpecialization.twistAnnulusDeg SS An (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s) *
      dat.u0 s ^ (JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s) *
      dat.lam s ^ (JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s) *
      (dat.mu s ^ (JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s))⁻¹ *
      JHPlaceSpecialization.twistAngFactor SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s *
      (∏ s' ∈ Finset.univ.erase s,
        (JHPlaceSpecialization.twistCrossFst SS dat s' s ^ (JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s'))⁻¹ *
          JHPlaceSpecialization.twistCrossSnd SS dat s' s ^ (JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s')) := by
    have h1 := congrFun hgratio s
    have h2 : JHPlaceSpecialization.twistNodeUnit SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s = Additive.ofMul (av s / bv s) := h1
    unfold JHPlaceSpecialization.twistNodeUnit at h2
    exact (Additive.ofMul.injective h2).symm

  have hP : (∏ V ∈ Df.support with V ∈ (An s).dom, (V.evalAt (JHPlaceSpecialization.flipParam SS An s)) ^ (-(Df V))) *
        ((p : ℕ) : AlgebraicClosure ℚ) ^ (JHPlaceSpecialization.twistPosMoment SS An pos Df s).num =
      ((∏ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support with V ∈ (An s).dom, (V.evalAt (JHPlaceSpecialization.flipParam SS An s)) ^ (-((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V))) *
        ((p : ℕ) : AlgebraicClosure ℚ) ^ (JHPlaceSpecialization.twistPosMoment SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s).num)⁻¹ := by
    rw [hfilt, hmomDf, Rat.neg_num, zpow_neg, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun V hV => ?_
    rw [← zpow_neg, hneg V ((hdom V).mp (Finset.mem_filter.mp hV).2)]
  have eΘ : ∀ D' : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.twistAngFactor SS An pos D' s =
      CsHGen.redUnit A (JHPlaceSpecialization.twistPosMoment SS An pos D' s)
        ((∏ V ∈ D'.support with V ∈ (An s).dom, (V.evalAt (JHPlaceSpecialization.flipParam SS An s)) ^ (-(D' V))) *
          ((p : ℕ) : AlgebraicClosure ℚ) ^ (JHPlaceSpecialization.twistPosMoment SS An pos D' s).num) := fun D' => rfl
  have hΘ : JHPlaceSpecialization.twistAngFactor SS An pos Df s * JHPlaceSpecialization.twistAngFactor SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s = 1 := by
    rw [eΘ, eΘ, hP, CsHGen.redUnit_congr A _ (JHPlaceSpecialization.twistPosMoment SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s) _ (by rw [hmomDf, Rat.neg_den])]
    exact CsHGen.redUnit_inv_mul A _ _

  have hkey := CsHGen.key_of_ratio (Finset.univ.erase s)
    (JHPlaceSpecialization.twistAngFactor SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s) (JHPlaceSpecialization.twistAngFactor SS An pos Df s)
    (fun s' => JHPlaceSpecialization.twistCrossFst SS dat s' s) (fun s' => JHPlaceSpecialization.twistCrossSnd SS dat s' s)
    (fun s' => JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s') (fun s' => JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s')
    α₁ α₂ (dat.u0 s) (dat.lam s) (dat.mu s) (av s) (bv s)
    ((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨(c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s) (JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s)
    (JHPlaceSpecialization.twistAnnulusDeg SS An (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s) (JHPlaceSpecialization.twistAnnulusDeg SS An Df s)
    hratio hν hΘ hdegDf hflat₁ hflat₂
  beta_reduce at hkey
  have hval₁ := CsHGen.hasValue_corrected_of_flat (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 (Finset.univ : Finset ↥SS) s (Finset.mem_univ s)
    (Rpd.R₁.residue ⟨c₁ • f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) g₁ (Rpd.R₁.residue ⟨_, hz₁'⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (fun s' => dat.unifFst s') (fun s' => JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s') ((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    hybar0 (hπ₁0 s (Finset.mem_univ _)) (α₁ : ResidueField ↥A) (dat.lam s : ResidueField ↥A) (av s : ResidueField ↥A)
    (fun s' => ((JHPlaceSpecialization.twistCrossFst SS dat s' s : (ResidueField ↥A)ˣ) : ResidueField ↥A))
    hv₁ hlam' (Units.ne_zero _) (hgvals s).1 hcross₁ (fun _ _ => Units.ne_zero _) hflat₁
  have hval₂ := CsHGen.hasValue_corrected_of_flat (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2 (Finset.univ : Finset ↥SS) s (Finset.mem_univ s)
    (Rpd.R₂.residue ⟨(c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) g₂ (Rpd.R₂.residue ⟨_, hz₂'⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (fun s' => dat.unifSnd s') (fun s' => JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s') ((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨(c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    hxbar0 (hπ₂0 s (Finset.mem_univ _)) (α₂ : ResidueField ↥A) (dat.mu s : ResidueField ↥A) (bv s : ResidueField ↥A)
    (fun s' => ((JHPlaceSpecialization.twistCrossSnd SS dat s' s : (ResidueField ↥A)ˣ) : ResidueField ↥A))
    hv₂ hmu' (Units.ne_zero _) (hgvals s).2 hcross₂ (fun _ _ => Units.ne_zero _) hflat₂
  beta_reduce at hval₁ hval₂
  have hc0 : (α₁ : ResidueField ↥A) * (dat.lam s : ResidueField ↥A) ^ ((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) * (av s : ResidueField ↥A) *
      ∏ s' ∈ Finset.univ.erase s, ((JHPlaceSpecialization.twistCrossFst SS dat s' s : (ResidueField ↥A)ˣ) : ResidueField ↥A) ^
        (JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s') ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (zpow_ne_zero _ (Units.ne_zero _))) (Units.ne_zero _)) ?_
    exact Finset.prod_ne_zero_iff.mpr fun s' _ => zpow_ne_zero _ (Units.ne_zero _)
  refine ⟨Units.mk0 _ hc0, ?_, ?_⟩
  · exact hval₁
  · rw [Units.val_mk0, hkey]
    exact hval₂

end S_ModularCurve_JHPlaceSpecialization_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_twistSp_eq_zero_of_annulus
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_twistSp_eq_zero_of_annulus (solution)
