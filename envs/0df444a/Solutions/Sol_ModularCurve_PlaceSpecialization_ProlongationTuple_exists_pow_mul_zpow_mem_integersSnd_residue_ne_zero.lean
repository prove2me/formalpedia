-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2ae2fb30-81b8-5b39-bd95-7bd2242ca272

import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ValuationSubring_exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open ModularCurve AlgebraicCurve IsLocalRing

noncomputable section

namespace OneSidedWitnessExponent

private theorem eq_one_of_pow_eq_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a : Γ₀} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = 1) : a = 1 := by
  have hle1 : ∀ m : ℕ, a ≤ 1 → a ^ m ≤ 1 := fun m ha => by
    induction m with
    | zero => rw [pow_zero]
    | succ m ih =>
      rw [pow_succ]
      calc a ^ m * a ≤ 1 * 1 := mul_le_mul' ih ha
        _ = 1 := one_mul 1
  have hge1 : ∀ m : ℕ, 1 ≤ a → 1 ≤ a ^ m := fun m ha => by
    induction m with
    | zero => rw [pow_zero]
    | succ m ih =>
      rw [pow_succ]
      calc (1 : Γ₀) = 1 * 1 := (one_mul 1).symm
        _ ≤ a ^ m * a := mul_le_mul' ih ha
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rcases lt_trichotomy a 1 with ha | ha | ha
  · exfalso
    have hle : a ^ (m + 1) ≤ a := by
      rw [pow_succ]
      calc a ^ m * a ≤ 1 * a := mul_le_mul' (hle1 m ha.le) le_rfl
        _ = a := one_mul a
    rw [h] at hle
    exact absurd (lt_of_le_of_lt hle ha) (lt_irrefl 1)
  · exact ha
  · exfalso
    have hle : a ≤ a ^ (m + 1) := by
      rw [pow_succ]
      calc a = 1 * a := (one_mul a).symm
        _ ≤ a ^ m * a := mul_le_mul' (hge1 m ha.le) le_rfl
    rw [h] at hle
    exact absurd (lt_of_lt_of_le ha hle) (lt_irrefl 1)

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem mem_decompositionSubgroup_of_mem_inertiaSubgroupIn
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    σ ∈ A.decompositionSubgroup ℚ := by
  unfold ValuationSubring.inertiaSubgroupIn at hσ
  exact Subgroup.map_subtype_le _ hσ

private theorem valuation_map_eq_of_mem_inertiaSubgroupIn
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (z : AlgebraicClosure ℚ) : A.valuation (σ z) = A.valuation z :=
  ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A
    (mem_decompositionSubgroup_of_mem_inertiaSubgroupIn A hσ) z

private theorem exists_inertia_fixed_valuation_eq_pow (x : AlgebraicClosure ℚ) (hx : x ≠ 0) :
    ∃ (e : ℕ) (y : AlgebraicClosure ℚ), e ≠ 0 ∧ y ≠ 0 ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ → σ y = y) ∧
      A.valuation y = A.valuation x ^ e := by
  classical

  set O : Set (AlgebraicClosure ℚ) :=
    {z | ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ ∧ σ x = z}
    with hO_def
  have hint : IsIntegral ℚ x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hroot : Polynomial.aeval x (minpoly ℚ x) = 0 := minpoly.aeval ℚ x
  have hsub : O ⊆ (minpoly ℚ x).rootSet (AlgebraicClosure ℚ) := by
    rintro z ⟨σ, -, rfl⟩
    refine Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, hroot, map_zero]
  have hfin : O.Finite := (Polynomial.rootSet_finite _ _).subset hsub
  have hmemS : ∀ z, z ∈ hfin.toFinset ↔ ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.inertiaSubgroupIn ℚ ∧ σ x = z := fun z => by
    rw [Set.Finite.mem_toFinset]
    rfl
  have hxS : x ∈ hfin.toFinset := (hmemS x).mpr ⟨1, Subgroup.one_mem _, rfl⟩

  have himage : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ A.inertiaSubgroupIn ℚ →
      hfin.toFinset.image τ = hfin.toFinset := fun τ hτ => by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨σ, hσ, rfl⟩ := (hmemS w).mp hw
      exact (hmemS _).mpr ⟨τ * σ, Subgroup.mul_mem _ hτ hσ, rfl⟩
    · exact (Finset.card_image_of_injective _ τ.injective).ge
  refine ⟨hfin.toFinset.card, ∏ z ∈ hfin.toFinset, z, ?_, ?_, ?_, ?_⟩
  · exact Finset.card_ne_zero.mpr ⟨x, hxS⟩
  · rw [Finset.prod_ne_zero_iff]
    intro z hz
    obtain ⟨σ, -, rfl⟩ := (hmemS z).mp hz
    exact (map_ne_zero σ).mpr hx
  · intro τ hτ
    rw [map_prod]
    have hinj : ∀ a ∈ hfin.toFinset, ∀ b ∈ hfin.toFinset, τ a = τ b → a = b :=
      fun a _ b _ h => τ.injective h
    have himg := Finset.prod_image (f := fun z : AlgebraicClosure ℚ => z) hinj
    rw [himage τ hτ] at himg
    exact himg.symm
  · rw [map_prod]
    have hconst : ∀ z ∈ hfin.toFinset, A.valuation z = A.valuation x := fun z hz => by
      obtain ⟨σ, hσ, rfl⟩ := (hmemS z).mp hz
      exact valuation_map_eq_of_mem_inertiaSubgroupIn A hσ x
    rw [Finset.prod_congr rfl hconst, Finset.prod_const]

variable {A}

private theorem valuation_eq_one_of_mem_of_inv_mem {u : AlgebraicClosure ℚ} (hu0 : u ≠ 0)
    (hu : u ∈ A) (hu' : u⁻¹ ∈ A) : A.valuation u = 1 := by
  have h1 : A.valuation u ≤ 1 := (A.valuation_le_one_iff u).mpr hu
  have h2 : A.valuation u⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr hu'
  by_contra hne
  have hlt : A.valuation u < 1 := lt_of_le_of_ne h1 hne
  have hprod : A.valuation u * A.valuation u⁻¹ < 1 :=
    calc A.valuation u * A.valuation u⁻¹ ≤ A.valuation u * 1 := mul_le_mul' le_rfl h2
      _ = A.valuation u := mul_one _
      _ < 1 := hlt
  rw [← map_mul, mul_inv_cancel₀ hu0, map_one] at hprod
  exact lt_irrefl _ hprod

private theorem exists_valuation_eq_zpow_of_inertia_fixed {q : ℕ} [Fact q.Prime]
    (hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (y : AlgebraicClosure ℚ) (hy : y ≠ 0)
    (hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ → σ y = y) :
    ∃ s : ℤ, A.valuation y = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ s := by
  rcases A.mem_or_inv_mem y with hyA | hyA
  · obtain ⟨s, u, huA, hu'A, hyeq⟩ :=
      ValuationSubring.exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn q A hA y hyA hy hfix
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hyeq
      exact hy hyeq
    refine ⟨s, ?_⟩
    rw [hyeq, map_mul, map_pow, valuation_eq_one_of_mem_of_inv_mem hu0 huA hu'A, mul_one,
      zpow_natCast]
  · have hy' : y⁻¹ ≠ 0 := inv_ne_zero hy
    have hfix' : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        σ ∈ A.inertiaSubgroupIn ℚ → σ y⁻¹ = y⁻¹ := fun σ hσ => by
      rw [map_inv₀, hfix σ hσ]
    obtain ⟨s, u, huA, hu'A, hyeq⟩ :=
      ValuationSubring.exists_eq_pow_mul_of_forall_mem_inertiaSubgroupIn q A hA y⁻¹ hyA hy' hfix'
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hyeq
      exact hy' hyeq
    refine ⟨-(s : ℤ), ?_⟩
    have hv : A.valuation y⁻¹ = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ s := by
      rw [hyeq, map_mul, map_pow, valuation_eq_one_of_mem_of_inv_mem hu0 huA hu'A, mul_one]
    rw [map_inv₀] at hv
    rw [zpow_neg, zpow_natCast, ← hv, inv_inv]

private theorem exists_pow_mul_zpow_valuation_eq_one {q : ℕ} [Fact q.Prime]
    (hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (c d : AlgebraicClosure ℚ) (hc : c ≠ 0) (hd : d ≠ 0) (hd1 : A.valuation d ≠ 1) :
    ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧ A.valuation (c ^ m * d ^ j) = 1 := by
  set V := A.valuation ((q : ℕ) : AlgebraicClosure ℚ) with hV_def
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hV0 : V ≠ 0 := (map_ne_zero _).mpr hq0
  obtain ⟨ec, yc, hec, hyc, hfixc, hvc⟩ := exists_inertia_fixed_valuation_eq_pow A c hc
  obtain ⟨ed, yd, hed, hyd, hfixd, hvd⟩ := exists_inertia_fixed_valuation_eq_pow A d hd
  obtain ⟨sc, hsc⟩ := exists_valuation_eq_zpow_of_inertia_fixed hA yc hyc hfixc
  obtain ⟨sd, hsd⟩ := exists_valuation_eq_zpow_of_inertia_fixed hA yd hyd hfixd

  have hc' : A.valuation c ^ (ec : ℤ) = V ^ sc := by rw [zpow_natCast, ← hvc, hsc]
  have hd' : A.valuation d ^ (ed : ℤ) = V ^ sd := by rw [zpow_natCast, ← hvd, hsd]

  have hsd0 : sd ≠ 0 := by
    rintro rfl
    rw [zpow_zero, zpow_natCast] at hd'
    exact hd1 (eq_one_of_pow_eq_one hed hd')
  rcases lt_or_gt_of_ne hsd0 with hneg | hpos
  ·
    refine ⟨ec * sd.natAbs, (ed : ℤ) * sc, ?_, ?_⟩
    · exact Nat.mul_ne_zero hec (Int.natAbs_ne_zero.mpr hsd0)
    have habs : ((sd.natAbs : ℕ) : ℤ) = -sd := Int.ofNat_natAbs_of_nonpos hneg.le
    rw [map_mul, map_zpow₀, map_pow, ← zpow_natCast, Nat.cast_mul, habs, zpow_mul, hc',
      zpow_mul, hd', ← zpow_mul, ← zpow_mul, ← zpow_add₀ hV0]
    have : sc * -sd + sd * sc = 0 := by ring
    rw [this, zpow_zero]
  ·
    refine ⟨ec * sd.natAbs, -((ed : ℤ) * sc), ?_, ?_⟩
    · exact Nat.mul_ne_zero hec (Int.natAbs_ne_zero.mpr hsd0)
    have habs : ((sd.natAbs : ℕ) : ℤ) = sd := Int.natAbs_of_nonneg hpos.le
    rw [map_mul, map_zpow₀, map_pow, ← zpow_natCast, Nat.cast_mul, habs, zpow_mul, hc',
      zpow_neg, zpow_mul, hd', ← zpow_mul, ← zpow_neg, ← zpow_mul, ← zpow_add₀ hV0]
    have : sc * sd + sd * -sc = 0 := by ring
    rw [this, zpow_zero]

end OneSidedWitnessExponent

end

set_option maxHeartbeats 3200000 in
open ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple AlgebraicCurve IsLocalRing OneSidedWitnessExponent in

theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (u : modularFunctionFieldBar (N * q)) (hu0 : u ≠ 0)
    (hu : ∀ h₂ : u ∈ R.R₂.integers, R.R₂.residue ⟨u, h₂⟩ = 0)
    (f : modularFunctionFieldBar (N * q)) (hf : f ≠ 0) :
    ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
      ∃ h₂ : f ^ m * u ^ j ∈ R.R₂.integers, R.R₂.residue ⟨f ^ m * u ^ j, h₂⟩ ≠ 0 := by

  have hres_const : ∀ (a : AlgebraicClosure ℚ) (haA : a ∈ A), A.valuation a = 1 →
      ∀ hmem : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) a ∈ R.R₂.integers,
        R.R₂.residue ⟨_, hmem⟩ ≠ 0 := fun a haA hva hmem => by
    have key : R.R₂.residue ⟨_, hmem⟩ =
        algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)
          (IsLocalRing.residue A ⟨a, haA⟩) := R.R₂.residue_algebraMap ⟨a, haA⟩
    have hunit : IsUnit (⟨a, haA⟩ : A) := by
      rw [A.valuation_eq_one_iff]
      exact hva
    intro h0
    rw [key, map_eq_zero_iff _ (algebraMap (ResidueField A)
      (modularFunctionFieldFullC (ResidueField A) N)).injective,
      IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h0
    exact h0 hunit

  have hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    have hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
    rcases ((A.valuation_le_one_iff _).mpr hqA).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hunit : IsUnit ((q : ℕ) : A) := by
        rw [A.valuation_eq_one_iff]
        exact_mod_cast heq
      have h0 : red ((q : ℕ) : A) = 0 := by rw [map_natCast, CharP.cast_eq_zero]
      exact (hunit.map red).ne_zero h0

  obtain ⟨cf, hcf, hcfres⟩ := R.R₂.exists_smul_mem f hf
  obtain ⟨cu, hcu, hcures⟩ := R.R₂.exists_smul_mem u hu0
  have hcf0 : cf ≠ 0 := R.R₂.smul_const_ne_zero hcf hcfres
  have hcu0 : cu ≠ 0 := R.R₂.smul_const_ne_zero hcu hcures

  have hcu1 : A.valuation cu ≠ 1 := by
    intro h1
    have hvinv : A.valuation cu⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
    have hcu'A : cu⁻¹ ∈ A := (A.valuation_le_one_iff _).mp hvinv.le
    have hconst : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) cu⁻¹
        ∈ R.R₂.integers := (R.R₂.algebraMap_mem_iff _).mpr hcu'A
    have hueq : u =
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) cu⁻¹ * (cu • u) := by
      rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hcu0, map_one, one_mul]
    have h₂ : u ∈ R.R₂.integers := by
      rw [hueq]
      exact mul_mem hconst hcu
    have hprod : (⟨u, h₂⟩ : R.R₂.integers) = ⟨_, hconst⟩ * ⟨cu • u, hcu⟩ := Subtype.ext hueq
    have hne : R.R₂.residue ⟨u, h₂⟩ ≠ 0 := by
      rw [hprod, map_mul]
      exact mul_ne_zero (hres_const cu⁻¹ hcu'A hvinv hconst) hcures
    exact hne (hu h₂)

  obtain ⟨m, j, hm, hval⟩ := exists_pow_mul_zpow_valuation_eq_one hA cf cu hcf0 hcu0 hcu1
  set e : AlgebraicClosure ℚ := cf ^ m * cu ^ j with he_def
  have he0 : e ≠ 0 := mul_ne_zero (pow_ne_zero _ hcf0) (zpow_ne_zero _ hcu0)
  have heA : e ∈ A := (A.valuation_le_one_iff _).mp hval.le
  have hvinv : A.valuation e⁻¹ = 1 := by rw [map_inv₀, hval, inv_one]
  have he'A : e⁻¹ ∈ A := (A.valuation_le_one_iff _).mp hvinv.le

  set wu : (R.R₂.integers)ˣ := (R.R₂.isUnit_of_residue_ne_zero hcures).unit with hwu_def
  have hwu_val : ((wu : R.R₂.integers) : modularFunctionFieldBar (N * q)) = cu • u := by
    rw [hwu_def, IsUnit.unit_spec]
  have hzpow : ((((wu ^ j : (R.R₂.integers)ˣ) : R.R₂.integers) : modularFunctionFieldBar (N * q)))
      = (cu • u) ^ j := by
    have := congrArg
      (fun x : (modularFunctionFieldBar (N * q))ˣ => (x : modularFunctionFieldBar (N * q)))
      (map_zpow (Units.map (R.R₂.integers.subtype : R.R₂.integers →* modularFunctionFieldBar (N * q)))
        wu j)
    simp only [Units.coe_map, Units.val_zpow_eq_zpow_val] at this
    rw [← hwu_val]
    exact this
  have hmem_pow : (cf • f) ^ m ∈ R.R₂.integers := pow_mem hcf m
  have hmem_zpow : (cu • u) ^ j ∈ R.R₂.integers := by
    rw [← hzpow]
    exact ((wu ^ j : (R.R₂.integers)ˣ) : R.R₂.integers).2
  have hconst' : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) e⁻¹
      ∈ R.R₂.integers := (R.R₂.algebraMap_mem_iff _).mpr he'A

  have hφ0 : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) e ≠ 0 :=
    (map_ne_zero _).mpr he0
  have hid0 : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) e * (f ^ m * u ^ j)
      = (cf • f) ^ m * (cu • u) ^ j := by
    rw [he_def, Algebra.smul_def, Algebra.smul_def, mul_pow, mul_zpow, map_mul, map_pow, map_zpow₀]
    ring
  have hid : f ^ m * u ^ j =
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) e⁻¹ *
        ((cf • f) ^ m * (cu • u) ^ j) := by
    rw [map_inv₀]
    exact (eq_inv_mul_iff_mul_eq₀ hφ0).mpr hid0
  have hmem : f ^ m * u ^ j ∈ R.R₂.integers := by
    rw [hid]
    exact mul_mem hconst' (mul_mem hmem_pow hmem_zpow)
  refine ⟨m, j, hm, hmem, ?_⟩

  have hres_pow : R.R₂.residue ⟨(cf • f) ^ m, hmem_pow⟩ ≠ 0 := by
    have hpow : (⟨(cf • f) ^ m, hmem_pow⟩ : R.R₂.integers) = (⟨cf • f, hcf⟩ : R.R₂.integers) ^ m :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow])
    rw [hpow, map_pow]
    exact pow_ne_zero _ hcfres
  have hres_zpow : R.R₂.residue ⟨(cu • u) ^ j, hmem_zpow⟩ ≠ 0 := by
    have hzp : (⟨(cu • u) ^ j, hmem_zpow⟩ : R.R₂.integers) =
        ((wu ^ j : (R.R₂.integers)ˣ) : R.R₂.integers) := Subtype.ext hzpow.symm
    rw [hzp]
    exact R.R₂.residue_ne_zero_of_isUnit (Units.isUnit _)
  have hsplit : (⟨f ^ m * u ^ j, hmem⟩ : R.R₂.integers) =
      ⟨_, hconst'⟩ * (⟨(cf • f) ^ m, hmem_pow⟩ * ⟨(cu • u) ^ j, hmem_zpow⟩) :=
    Subtype.ext hid
  rw [hsplit, map_mul, map_mul]
  exact mul_ne_zero (hres_const e⁻¹ he'A hvinv hconst') (mul_ne_zero hres_pow hres_zpow)

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero (solution)
