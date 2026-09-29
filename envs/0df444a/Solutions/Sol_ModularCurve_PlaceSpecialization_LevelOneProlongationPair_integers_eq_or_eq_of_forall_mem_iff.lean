-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.integers_eq_or_eq_of_forall_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e581ff93-b56e-5949-aa25-cb8f8729c231

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_eq_or_eq_of_transcendental
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_jFun_jqFun
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_eq_or_eq_of_forall_mem_iff
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve IsLocalRing ModularCurve Polynomial

namespace ValRingKit
namespace Hall

theorem exists_valuation_monomial_eq {K₁ F Γ₀ : Type*} [Field K₁] [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) (φ : K₁ →+* F)
    {f : F} (hf : f ≠ 0) {p : K₁[X]} (hp : p ≠ 0) (hpf : p.eval₂ φ f = 0) :
    ∃ i j : ℕ, i ≠ j ∧ p.coeff i ≠ 0 ∧ p.coeff j ≠ 0 ∧
      v (φ (p.coeff i) * f ^ i) = v (φ (p.coeff j) * f ^ j) := by
  classical
  have hne : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image p.support (fun i => v (φ (p.coeff i) * f ^ i)) hne
  have hterm : ∀ i ∈ p.support, v (φ (p.coeff i) * f ^ i) ≠ 0 := by
    intro i hi
    rw [Valuation.ne_zero_iff]
    exact mul_ne_zero ((map_ne_zero φ).mpr (mem_support_iff.mp hi)) (pow_ne_zero _ hf)
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ i ∈ p.support \ {i₀}, v (φ (p.coeff i) * f ^ i) < v (φ (p.coeff i₀) * f ^ i₀) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    refine lt_of_le_of_ne (hmax i hi.1) fun heq => ?_
    exact hcon i i₀ hi.2 (mem_support_iff.mp hi.1) (mem_support_iff.mp hi₀) heq
  have hsum := Valuation.map_sum_eq_of_lt v hi₀ hlt
  have hzero : (∑ i ∈ p.support, φ (p.coeff i) * f ^ i) = 0 := by
    rw [← hpf, eval₂_eq_sum, sum_def]
  rw [hzero, map_zero] at hsum
  exact hterm i₀ hi₀ hsum.symm

theorem exists_pow_valuation_eq {K₁ F Γ₀ : Type*} [Field K₁] [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) (φ : K₁ →+* F)
    {f : F} (hf : f ≠ 0) {p : K₁[X]} (hp : p ≠ 0) (hpf : p.eval₂ φ f = 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ g : K₁, g ≠ 0 ∧ v (f ^ m) = v (φ g) := by
  obtain ⟨i, j, hij, hi, hj, hv⟩ := exists_valuation_monomial_eq v φ hf hp hpf

  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm hj hi hv.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  refine ⟨j - i, Nat.sub_pos_of_lt hlt, p.coeff i / p.coeff j, div_ne_zero hi hj, ?_⟩
  have hvf : v f ≠ 0 := (Valuation.ne_zero_iff v).mpr hf
  have hvj : v (φ (p.coeff j)) ≠ 0 := (Valuation.ne_zero_iff v).mpr ((map_ne_zero φ).mpr hj)
  rw [map_mul, map_mul, map_pow, map_pow] at hv
  rw [map_div₀, map_div₀, map_pow, eq_div_iff hvj]

  have hsplit : v f ^ j = v f ^ i * v f ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hlt.le]
  rw [hsplit] at hv
  have hfi : v f ^ i ≠ 0 := pow_ne_zero _ hvf
  calc v f ^ (j - i) * v (φ (p.coeff j))
      = (v (φ (p.coeff j)) * (v f ^ i * v f ^ (j - i))) * (v f ^ i)⁻¹ := by field_simp
    _ = (v (φ (p.coeff i)) * v f ^ i) * (v f ^ i)⁻¹ := by rw [hv]
    _ = v (φ (p.coeff i)) := by field_simp

theorem eq_one_of_pow_eq_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {x : Γ₀} {m : ℕ}
    (hm : m ≠ 0) (h : x ^ m = 1) : x = 1 :=
  (pow_eq_one_iff_of_nonneg zero_le' hm).mp h

theorem valuation_inv_mul_eq_one {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) {f d : F} (hd : d ≠ 0) {m : ℕ} (hm : 0 < m) (h : v (f ^ m) = v (d ^ m)) :
    v (d⁻¹ * f) = 1 := by
  have hvd : v d ≠ 0 := (Valuation.ne_zero_iff v).mpr hd
  apply eq_one_of_pow_eq_one (Nat.pos_iff_ne_zero.mp hm)
  rw [← map_pow, mul_pow, map_mul, inv_pow, map_inv₀, h, map_pow, inv_mul_cancel₀ (pow_ne_zero _ hvd)]

theorem mem_and_isUnit_of_valuation_eq_one {F : Type*} [Field F] (O : ValuationSubring F) {x : F}
    (h : O.valuation x = 1) : ∃ hx : x ∈ O, IsUnit (⟨x, hx⟩ : O) := by
  have hx : x ∈ O := (O.valuation_le_one_iff x).mp h.le
  exact ⟨hx, (O.valuation_eq_one_iff ⟨x, hx⟩).mpr h⟩

theorem inv_mem_of_isUnit {F : Type*} [Field F] (O : ValuationSubring F) {y : F} (hy : y ∈ O)
    (hu : IsUnit (⟨y, hy⟩ : O)) : y⁻¹ ∈ O := by
  have h1 : O.valuation y = 1 := (O.valuation_eq_one_iff ⟨y, hy⟩).mp hu
  rw [← O.valuation_le_one_iff, map_inv₀, h1, inv_one]

theorem valuation_eq_one_of_mem_of_inv_mem {F : Type*} [Field F] (O : ValuationSubring F) {x : F}
    (hx0 : x ≠ 0) (hx : x ∈ O) (hx' : x⁻¹ ∈ O) : O.valuation x = 1 := by
  apply le_antisymm ((O.valuation_le_one_iff x).mpr hx)
  have h := (O.valuation_le_one_iff x⁻¹).mpr hx'
  rw [map_inv₀] at h
  exact (inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0))).mp h

end ValRingKit.Hall

open ValRingKit.Hall

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (O : ValuationSubring ↥(modularFunctionFieldBar (1 * q)))
    (hO : ∀ g : ↥(modularFunctionFieldBar 1),
      heckeAlphaBar (AlgebraicClosure ℚ) 1 q g ∈ O ↔ heckeAlphaBar (AlgebraicClosure ℚ) 1 q g ∈ R.R₁.integers) :
    O = R.R₁.integers ∨ O = R.R₂.integers := by
  classical

  let α := heckeAlphaBar (AlgebraicClosure ℚ) 1 q
  have hαinj : Function.Injective α := α.toRingHom.injective

  have hconst : ∀ c : AlgebraicClosure ℚ,
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c ∈ O ↔ c ∈ A := by
    intro c
    rw [← α.commutes c, hO, α.commutes]
    exact R.R₁.algebraMap_mem_iff c

  have hA : A.LiesOverPrime q := by
    have hq : ((q : A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by norm_cast
    show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
    rw [← hq, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h := hu.map red
    rw [map_natCast, CharP.cast_eq_zero] at h
    exact not_isUnit_zero h

  obtain ⟨h₁, -, -, -, hres₁, -, -, -⟩ :=
    ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_jFun_jqFun hA R

  let jOne : ↥(modularFunctionFieldBar 1) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full 1 (jq_mem 1))⟩
  have hαj : α jOne = PlaceSpecialization.jFun (q := q) := Subtype.ext (coe_heckeAlphaBar (L := AlgebraicClosure ℚ) (N := 1) (ℓ := q) (x := jOne))
  have hjO : PlaceSpecialization.jFun (q := q) ∈ O := by
    rw [← hαj]
    exact (hO jOne).mpr (hαj ▸ h₁)

  have hunitO : ∀ g : ↥(modularFunctionFieldBar 1), g ≠ 0 → α g ∈ R.R₁.integers → (α g)⁻¹ ∈ R.R₁.integers →
      O.valuation (α g) = 1 := by
    intro g hg hm hinv
    refine valuation_eq_one_of_mem_of_inv_mem O ((map_ne_zero_iff _ hαinj).mpr hg) ((hO g).mpr hm) ?_
    rw [← map_inv₀, hO, map_inv₀]; exact hinv

  have hreg : ∀ f : ↥(modularFunctionFieldBar (1 * q)), f ≠ 0 →
      ∃ c : AlgebraicClosure ℚ, ∃ h : c • f ∈ O, IsLocalRing.residue O ⟨c • f, h⟩ ≠ 0 := by
    intro f hf
    obtain ⟨p, hpm, hpf⟩ := hα f
    obtain ⟨m, hm, g, hg0, hvg⟩ := exists_pow_valuation_eq O.valuation α.toRingHom hf hpm.ne_zero hpf

    have hαg0 : α g ≠ 0 := (map_ne_zero_iff _ hαinj).mpr hg0
    obtain ⟨c₀, hc₀mem, hc₀res⟩ := R.R₁.exists_smul_mem (α g) hαg0
    have hc₀ : c₀ ≠ 0 := R.R₁.smul_const_ne_zero hc₀mem hc₀res
    have hunit₁ : IsUnit (⟨c₀ • α g, hc₀mem⟩ : R.R₁.integers) := R.R₁.isUnit_of_residue_ne_zero hc₀res
    have hsmul : c₀ • α g = α (c₀ • g) := by rw [Algebra.smul_def, Algebra.smul_def, map_mul, α.commutes]
    have hval : O.valuation (α (c₀ • g)) = 1 := by
      refine hunitO (c₀ • g) (smul_ne_zero hc₀ hg0) (hsmul ▸ hc₀mem) ?_
      rw [← hsmul]; exact inv_mem_of_isUnit _ hc₀mem hunit₁

    obtain ⟨d₀, hd₀⟩ := IsAlgClosed.exists_pow_nat_eq (c₀⁻¹) hm
    have hd₀0 : d₀ ≠ 0 := by
      rintro rfl; rw [zero_pow hm.ne'] at hd₀; exact inv_ne_zero hc₀ hd₀.symm
    have hd₀F : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) d₀ ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap _ _).injective).mpr hd₀0
    have hvfm : O.valuation (f ^ m)
        = O.valuation ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) d₀) ^ m) := by
      rw [hvg, ← map_pow, hd₀, map_inv₀ (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))), map_inv₀]

      have : O.valuation (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c₀) * O.valuation (α g) = 1 := by
        rw [← map_mul, ← Algebra.smul_def, hsmul, hval]
      show O.valuation ((α : ↥(modularFunctionFieldBar 1) →+* ↥(modularFunctionFieldBar (1 * q))) g) = _
      exact eq_inv_of_mul_eq_one_right this
    have hone := valuation_inv_mul_eq_one O.valuation hd₀F hm hvfm
    obtain ⟨hmem, hunit⟩ := mem_and_isUnit_of_valuation_eq_one O hone
    have hsm : d₀⁻¹ • f = (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) d₀)⁻¹ * f := by
      rw [Algebra.smul_def, map_inv₀]
    refine ⟨d₀⁻¹, hsm ▸ hmem, ?_⟩
    have heq : (⟨d₀⁻¹ • f, hsm ▸ hmem⟩ : O)
        = ⟨(algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) d₀)⁻¹ * f, hmem⟩ :=
      Subtype.ext hsm
    rw [heq]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hunit

  let toO : A →+* O :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).comp A.subtype).codRestrict O.toSubring
      (fun a => (hconst a).mpr a.2)
  have htoO : ∀ a : A, ((toO a : O) : ↥(modularFunctionFieldBar (1 * q)))
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) a := fun a => rfl
  haveI : IsLocalHom toO := by
    refine ⟨fun a ha => ?_⟩
    have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
      rintro h0
      have : toO a = 0 := Subtype.ext (by rw [htoO, h0, map_zero]; rfl)
      rw [this] at ha; exact not_isUnit_zero ha
    have hinv : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) a)⁻¹ ∈ O :=
      inv_mem_of_isUnit O (by rw [← htoO]; exact (toO a).2) (by exact ha)
    rw [← map_inv₀, hconst] at hinv
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
  letI : Algebra (ResidueField A) (ResidueField O) := (IsLocalRing.ResidueField.map toO).toAlgebra
  have hcompat : ∀ a : A, algebraMap (ResidueField A) (ResidueField O) (IsLocalRing.residue A a)
      = IsLocalRing.residue O (toO a) := fun a => rfl

  let Rreg : RegularProlongation A ↥(modularFunctionFieldBar (1 * q)) (ResidueField O) :=
    { integers := O
      residue := IsLocalRing.residue O
      algebraMap_mem_iff := hconst
      residue_surjective := IsLocalRing.residue_surjective
      ker_residue := IsLocalRing.ker_residue
      residue_algebraMap := fun a => (hcompat a).symm
      exists_smul_mem := hreg }

  have htr : Transcendental (ResidueField A) (Rreg.residue ⟨_, hjO⟩) := by
    intro halg
    obtain ⟨p, hp0, hpx⟩ := halg
    obtain ⟨Pl, hPl⟩ := Polynomial.map_surjective (IsLocalRing.residue A) IsLocalRing.residue_surjective p

    let toK₁ : A →+* ↥(modularFunctionFieldBar 1) :=
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 1)).comp A.subtype
    let toR₁ : A →+* R.R₁.integers :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).comp A.subtype).codRestrict
        R.R₁.integers.toSubring (fun a => (R.R₁.algebraMap_mem_iff a).mpr a.2)
    have hcoef : (O.subtype.comp toO : A →+* ↥(modularFunctionFieldBar (1 * q)))
        = (α : ↥(modularFunctionFieldBar 1) →+* ↥(modularFunctionFieldBar (1 * q))).comp toK₁ := by
      refine RingHom.ext fun a => ?_
      show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) a
        = α (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 1) (a : AlgebraicClosure ℚ))
      rw [α.commutes]
    have hcoef₁ : (R.R₁.integers.subtype.comp toR₁ : A →+* ↥(modularFunctionFieldBar (1 * q)))
        = (α : ↥(modularFunctionFieldBar 1) →+* ↥(modularFunctionFieldBar (1 * q))).comp toK₁ := by
      refine RingHom.ext fun a => ?_
      show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) a
        = α (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 1) (a : AlgebraicClosure ℚ))
      rw [α.commutes]

    let Y₁ : ↥(modularFunctionFieldBar 1) := Pl.eval₂ toK₁ jOne
    let J : O := ⟨_, hjO⟩
    let Y : O := (Pl.map toO).eval J
    have hYcoe : (Y : ↥(modularFunctionFieldBar (1 * q))) = α Y₁ := by
      show O.subtype ((Pl.map toO).eval J)
        = (α : ↥(modularFunctionFieldBar 1) →+* ↥(modularFunctionFieldBar (1 * q))) (Pl.eval₂ toK₁ jOne)
      rw [Polynomial.eval_map, Polynomial.hom_eval₂, hcoef, Polynomial.hom_eval₂]
      congr 1
    have hYres : IsLocalRing.residue O Y = 0 := by
      show IsLocalRing.residue O ((Pl.map toO).eval J) = 0
      rw [Polynomial.eval_map, Polynomial.hom_eval₂]
      have hc : (IsLocalRing.residue O).comp toO
          = (algebraMap (ResidueField A) (ResidueField O)).comp (IsLocalRing.residue A) :=
        RingHom.ext fun a => (hcompat a).symm
      rw [hc, ← Polynomial.eval₂_map, hPl, ← Polynomial.aeval_def]
      exact hpx

    have hY₁R : α Y₁ ∈ R.R₁.integers := (hO Y₁).mp (hYcoe ▸ Y.2)
    let J₁ : R.R₁.integers := ⟨_, h₁⟩
    have hY₁eq : (⟨α Y₁, hY₁R⟩ : R.R₁.integers) = (Pl.map toR₁).eval J₁ := by
      apply Subtype.ext
      show (α : ↥(modularFunctionFieldBar 1) →+* ↥(modularFunctionFieldBar (1 * q))) (Pl.eval₂ toK₁ jOne)
        = R.R₁.integers.subtype ((Pl.map toR₁).eval J₁)
      rw [Polynomial.eval_map, Polynomial.hom_eval₂ Pl toR₁, hcoef₁, Polynomial.hom_eval₂]
      congr 1
    have hres₁Y : R.R₁.residue ⟨α Y₁, hY₁R⟩ = aeval (R.R₁.residue J₁) p := by
      rw [hY₁eq, Polynomial.eval_map, Polynomial.hom_eval₂]
      have hc : R.R₁.residue.comp toR₁
          = (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1)).comp
              (IsLocalRing.residue A) :=
        RingHom.ext fun a => R.R₁.residue_algebraMap a
      rw [hc, ← Polynomial.eval₂_map, hPl, ← Polynomial.aeval_def]

    have htr₁ : Transcendental (ResidueField A) (R.R₁.residue J₁) := by
      intro h
      have h' := h.algHom (IntermediateField.val (modularFunctionFieldFullC (ResidueField A) 1))
      rw [IntermediateField.coe_val] at h'
      have hcoeJ : ((R.R₁.residue J₁ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) :
          LaurentSeries (ResidueField A)) = jqModC (ResidueField A) := hres₁
      rw [hcoeJ] at h'
      exact transcendental_jqModC (ResidueField A) h'
    have hne : R.R₁.residue ⟨α Y₁, hY₁R⟩ ≠ 0 := by
      rw [hres₁Y]
      intro h0
      exact htr₁ ⟨p, hp0, h0⟩

    have hu₁ : IsUnit (⟨α Y₁, hY₁R⟩ : R.R₁.integers) := R.R₁.isUnit_of_residue_ne_zero hne
    have hY₁0 : α Y₁ ≠ 0 := by
      intro h0
      apply hne
      have : (⟨α Y₁, hY₁R⟩ : R.R₁.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    have hinvO : (α Y₁)⁻¹ ∈ O := by
      rw [← map_inv₀, hO, map_inv₀]
      exact inv_mem_of_isUnit _ hY₁R hu₁
    have hvalY : O.valuation (α Y₁) = 1 :=
      valuation_eq_one_of_mem_of_inv_mem O hY₁0 (hYcoe ▸ Y.2) hinvO
    have hYunit : IsUnit Y := by
      rw [O.valuation_eq_one_iff]
      rw [← hYcoe] at hvalY
      exact hvalY
    exact (IsLocalRing.residue_ne_zero_iff_isUnit Y).mpr hYunit hYres

  exact ModularCurve.PlaceSpecialization.LevelOneProlongationPair.integers_eq_or_eq_of_transcendental hA R Rreg hjO htr

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_eq_or_eq_of_forall_mem_iff
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_integers_eq_or_eq_of_forall_mem_iff (solution)
