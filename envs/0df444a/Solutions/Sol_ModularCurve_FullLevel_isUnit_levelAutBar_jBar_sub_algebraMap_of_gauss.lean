-- Prove2me | solution 1 for ModularCurve.FullLevel.isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/767e50d2-5f2e-5882-9bfb-28a38aaec716

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qTwist_of_redQ_eq_unipotent
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq coeff_jq_neg_one jq_mem modularFunctionField_le_full coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqModC_rat map_jqModC jqModC_eq_map_intCast qTwist qTwist_coeff FullLevel.coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "fieldBar Idx levelAutBar redQ coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd coe_levelAutBar_apply_eq_qTwist_of_redQ_eq_unipotent levelAutBar_mul"
namespace LevelAutGaussUnit
p2m_open "ModularCurve.FullLevel ModularCurve"

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}

private theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd _ _ hk, qExpand_coeff_of_not_dvd _ _ hk, map_zero]

private theorem coeffMap_single_zero {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    coeffMap f (HahnSeries.single 0 r) = HahnSeries.single 0 (f r) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hk : k = 0
  · subst hk; rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_same]
  · rw [HahnSeries.coeff_single_of_ne hk, HahnSeries.coeff_single_of_ne hk, map_zero]

omit [Fact q.Prime] [NeZero M'] in

private theorem exists_mem_isUnit_of_coe_eq_coeffMap (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (f : fieldBar q M') (X : LaurentSeries A)
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype X)
    (hX : coeffMap (IsLocalRing.residue A) X ≠ 0) :
    ∃ h : f ∈ O, IsUnit (⟨f, h⟩ : O) := by
  have h1 : coeffMap (IsLocalRing.residue A) (1 : LaurentSeries A) ≠ 0 := by
    rw [map_one]; exact one_ne_zero
  have hfO : f ∈ O := (hO f).mpr ⟨X, 1, h1, by rw [map_one, mul_one, hf]⟩
  have hX0 : X ≠ 0 := by rintro rfl; exact hX (map_zero _)
  have hf0 : f ≠ 0 := by
    intro h
    apply hX0
    have h' : coeffMap A.subtype X = 0 := by rw [← hf, h]; rfl
    ext k
    have hk := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff k) h'
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at hk
    rw [HahnSeries.coeff_zero, ZeroMemClass.coe_zero]
    exact hk
  have hinvO : f⁻¹ ∈ O := (hO f⁻¹).mpr ⟨1, X, hX, by
    rw [map_one, ← hf]
    show ((f⁻¹ * f : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) = 1
    rw [inv_mul_cancel₀ hf0]; rfl⟩
  exact ⟨hfO, isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hinvO⟩, Subtype.ext (mul_inv_cancel₀ hf0)⟩⟩

omit [Fact q.Prime] [NeZero M'] in

private theorem exists_mem_isUnit_sub_algebraMap_of_coeffMap (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (f : fieldBar q M') (X : LaurentSeries A)
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype X)
    (n : ℤ) (hn : n ≠ 0) (hXn : IsLocalRing.residue A (X.coeff n) ≠ 0) (a : A) :
    ∃ h : f - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ O,
      IsUnit (⟨_, h⟩ : O) := by
  refine exists_mem_isUnit_of_coe_eq_coeffMap O hO _ (X - HahnSeries.single 0 a) ?_ ?_
  · have e1 : ((f - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) : fieldBar q M') :
        LaurentSeries (AlgebraicClosure ℚ)) =
        (f : LaurentSeries (AlgebraicClosure ℚ)) - algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a :=
      rfl
    rw [e1, map_sub, hf, coeffMap_single_zero, algebraMap_laurentSeries_eq_single]
    rfl
  · intro h0
    apply hXn
    have hk := congrArg (fun s : LaurentSeries (ResidueField A) => s.coeff n) h0
    simp only [map_sub, coeffMap_coeff, HahnSeries.coeff_zero, HahnSeries.coeff_sub,
      coeffMap_single_zero, HahnSeries.coeff_single_of_ne hn, sub_zero] at hk
    exact hk

omit [Fact q.Prime] [NeZero M'] in

private theorem exists_mem_isUnit_sub_algebraMap_of_coeffMap_of_isUnit (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (f : fieldBar q M') (X : LaurentSeries A)
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype X)
    (n : ℤ) (hn : n ≠ 0) (hXn : IsUnit (X.coeff n)) (a : A) :
    ∃ h : f - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ O,
      IsUnit (⟨_, h⟩ : O) :=
  exists_mem_isUnit_sub_algebraMap_of_coeffMap O hO f X hf n hn
    (fun h0 => (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hXn h0) a

omit [Fact q.Prime] in

private theorem coe_inclusion_jBar (hle : modularFunctionFieldBar M' ≤ fieldBar q M') :
    ((IntermediateField.inclusion hle
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      jqModC (AlgebraicClosure ℚ) := by
  rw [IntermediateField.coe_inclusion]
  show coeffEmb (AlgebraicClosure ℚ) jq = _
  rw [← jqModC_rat]
  exact map_jqModC _

omit [Fact q.Prime] [NeZero M'] in
private theorem coeffMap_subtype_jqModC : coeffMap A.subtype (jqModC A) = jqModC (AlgebraicClosure ℚ) :=
  map_jqModC _

private theorem coeff_jqModC_neg_one (K : Type*) [CommRing K] : (jqModC K).coeff (-1) = 1 := by
  have hZ : (jqModC ℤ).coeff (-1) = 1 := by
    have h := coeff_jq_neg_one
    rw [← jqModC_rat, jqModC_eq_map_intCast ℚ, HahnSeries.map_coeff, eq_intCast] at h
    exact_mod_cast h
  rw [jqModC_eq_map_intCast K, HahnSeries.map_coeff, hZ, map_one]

private theorem exists_mem_isUnit_levelAutBar_sub_of_dvd (hqM' : ¬ q ∣ M')
    (ζ : Idx q) (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M')
    (ha : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (x : fieldBar q M') (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (a : A) :
    ∃ h : levelAutBar q M' ζ δ x - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ O,
      IsUnit (⟨_, h⟩ : O) := by
  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩
  have hlaw := ModularCurve.FullLevel.coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd q M' hqM' ζ δ hδ ha x hx
  refine exists_mem_isUnit_sub_algebraMap_of_coeffMap O hO _ (qExpand A (q ^ 2) (jqModC A)) ?_ (-(q ^ 2 : ℕ)) ?_ ?_ a
  · rw [hlaw, coeffMap_qExpand, coeffMap_subtype_jqModC]
  · exact neg_ne_zero.mpr (by exact_mod_cast (NeZero.ne (q ^ 2)))
  · have e : (-(q ^ 2 : ℕ) : ℤ) = ((q ^ 2 : ℕ) : ℤ) * (-1) := by ring
    rw [e, qExpand_coeff_mul, coeff_jqModC_neg_one, map_one]
    exact one_ne_zero

private theorem zeta_mem (ζ : Idx q) : ζ.val ∈ A := by
  have hprim : IsPrimitiveRoot ζ.val q := (mem_primitiveRoots (Fact.out : q.Prime).pos).mp ζ.2
  have hpow : ζ.val ^ q = 1 := hprim.pow_eq_one
  rcases A.mem_or_inv_mem ζ.val with h | h
  · exact h
  · have hq : q - 1 + 1 = q := Nat.sub_add_cancel (Fact.out : q.Prime).one_lt.le
    have hz0 : ζ.val ≠ 0 := hprim.ne_zero (Fact.out : q.Prime).ne_zero
    have e : (ζ.val⁻¹) ^ (q - 1) = ζ.val := by
      have h1 : (ζ.val⁻¹) ^ (q - 1) * ζ.val⁻¹ = 1 := by
        rw [← pow_succ, hq, inv_pow, hpow, inv_one]
      calc (ζ.val⁻¹) ^ (q - 1) = (ζ.val⁻¹) ^ (q - 1) * ζ.val⁻¹ * ζ.val := by
            rw [mul_assoc, inv_mul_cancel₀ hz0, mul_one]
        _ = ζ.val := by rw [h1, one_mul]
    rw [← e]
    exact pow_mem h _

private noncomputable def zetaUnit (ζ : Idx q) : (A)ˣ :=
  ⟨⟨ζ.val, zeta_mem ζ⟩, ⟨ζ.val ^ (q - 1), pow_mem (zeta_mem ζ) _⟩,
    Subtype.ext (by
      have hprim : IsPrimitiveRoot ζ.val q := (mem_primitiveRoots (Fact.out : q.Prime).pos).mp ζ.2
      show ζ.val * ζ.val ^ (q - 1) = 1
      rw [← pow_succ', Nat.sub_add_cancel (Fact.out : q.Prime).one_lt.le, hprim.pow_eq_one]),
    Subtype.ext (by
      have hprim : IsPrimitiveRoot ζ.val q := (mem_primitiveRoots (Fact.out : q.Prime).pos).mp ζ.2
      show ζ.val ^ (q - 1) * ζ.val = 1
      rw [← pow_succ, Nat.sub_add_cancel (Fact.out : q.Prime).one_lt.le, hprim.pow_eq_one])⟩

@[scoped simp] private theorem coe_zetaUnit (ζ : Idx q) : (((zetaUnit ζ : (A)ˣ) : A) : AlgebraicClosure ℚ) = ζ.val := rfl

omit [Fact q.Prime] [NeZero M'] in

private theorem coeffMap_qTwist (uA : (A)ˣ) (u : (AlgebraicClosure ℚ)ˣ) (hu : ((uA : A) : AlgebraicClosure ℚ) = (u : AlgebraicClosure ℚ))
    (t : ℤ) (X : LaurentSeries A) :
    coeffMap A.subtype (qTwist (uA ^ t) X) = qTwist (u ^ t) (coeffMap A.subtype X) := by
  have hmap : Units.map (A.subtype : A →* AlgebraicClosure ℚ) uA = u := Units.ext hu
  ext k
  rw [coeffMap_coeff, qTwist_coeff, qTwist_coeff, coeffMap_coeff, map_mul]
  congr 1
  rw [← hmap, ← map_zpow, ← map_zpow, Units.coe_map]
  rfl

omit [NeZero M'] in

private theorem exists_mem_isUnit_sub_algebraMap_of_coe_eq_qTwist (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (ζ : Idx q) (u : (AlgebraicClosure ℚ)ˣ) (hu : (u : AlgebraicClosure ℚ) = ζ.val) (t : ℤ)
    (f : fieldBar q M')
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) = qTwist (u ^ t) (jqModC (AlgebraicClosure ℚ))) (a : A) :
    ∃ h : f - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ O,
      IsUnit (⟨_, h⟩ : O) := by
  refine exists_mem_isUnit_sub_algebraMap_of_coeffMap_of_isUnit O hO f
    (qTwist ((zetaUnit ζ : (A)ˣ) ^ t) (jqModC A)) ?_ (-1) (by norm_num) ?_ a
  · rw [hf, coeffMap_qTwist (zetaUnit ζ) u ((coe_zetaUnit ζ).trans hu.symm) t, coeffMap_subtype_jqModC]
  · rw [qTwist_coeff, coeff_jqModC_neg_one, mul_one]
    exact Units.isUnit _

private theorem exists_mem_Gamma0_dvd (M' : ℕ) (hqM' : ¬ q ∣ M') :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M' ∧ (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
  have hcop : IsCoprime (q : ℤ) (M' : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM')
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨⟨!![(q : ℤ), -v; (M' : ℤ), u], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination huv
  · rw [Gamma0_mem]
    simp
  · simp

private theorem levelAutBar_apply_eq_self_of_dvd (hqM' : ¬ q ∣ M') (ζ : Idx q) (α : SL(2, ℤ))
    (hα : α ∈ Gamma0 M') (h01 : (q : ℤ) ∣ (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1)
    (x : fieldBar q M') (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    levelAutBar q M' ζ α x = x := by
  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩
  obtain ⟨δ, hδ, hδ00⟩ := exists_mem_Gamma0_dvd (q := q) M' hqM'
  have hαδ : α * δ ∈ Gamma0 M' := Subgroup.mul_mem _ hα hδ
  have h00 : (q : ℤ) ∣ ((α * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact dvd_add (dvd_mul_of_dvd_right hδ00 _) (dvd_mul_of_dvd_left h01 _)
  have h1 := coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd q M' hqM' ζ (α * δ) hαδ h00 x hx
  have h2 := coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd q M' hqM' ζ δ hδ hδ00 x hx
  have h12 : levelAutBar q M' ζ (α * δ) x = levelAutBar q M' ζ δ x := Subtype.ext (h1.trans h2.symm)
  rw [levelAutBar_mul q M' hqM' ζ α δ hα hδ, AlgEquiv.trans_apply] at h12
  exact (levelAutBar q M' ζ δ).injective h12

private theorem T_zpow_mem_Gamma0 (M' : ℕ) (t : ℤ) : ModularGroup.T ^ t ∈ Gamma0 M' := by
  rw [Gamma0_mem, ModularGroup.coe_T_zpow]
  simp

private theorem redQ_T_zpow (t : ℤ) : redQ q (ModularGroup.T ^ t) = CuspidalType.unipotent q (t : ZMod q) := by
  apply Units.ext
  simp only [redQ, MonoidHom.coe_comp, Function.comp_apply]
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CuspidalType.unipotent]

private theorem exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd (hqM' : ¬ q ∣ M') (ζ : Idx q) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 M') (ha : ¬ (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
    (u : (AlgebraicClosure ℚ)ˣ) (hu : (u : AlgebraicClosure ℚ) = ζ.val)
    (x : fieldBar q M') (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ∃ t : ℤ, ((levelAutBar q M' ζ γ x : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.qTwist (u ^ t) (jqModC (AlgebraicClosure ℚ)) := by
  set a : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha_def
  set b : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb_def
  have ha0 : (a : ZMod q) ≠ 0 := fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a q).mp h)
  set t : ℤ := (((b : ZMod q) * (a : ZMod q)⁻¹).val : ℤ) with ht_def
  have htq : (t : ZMod q) = (b : ZMod q) * (a : ZMod q)⁻¹ := by
    rw [ht_def, Int.cast_natCast, ZMod.natCast_zmod_val]
  set α : SL(2, ℤ) := γ * (ModularGroup.T ^ t)⁻¹ with hα_def
  have hT : ModularGroup.T ^ t ∈ Gamma0 M' := T_zpow_mem_Gamma0 M' t
  have hαmem : α ∈ Gamma0 M' := Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ hT)
  have hγeq : γ = α * ModularGroup.T ^ t := by rw [hα_def, inv_mul_cancel_right]
  have h01 : (q : ℤ) ∣ (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
    have hcoe : (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = a * (-t) + b * 1 := by
      rw [hα_def, ← zpow_neg, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
        Fin.sum_univ_two]
      simp [ha_def, hb_def]
    rw [hcoe, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [htq, mul_one, mul_neg, mul_comm (a : ZMod q), inv_mul_cancel_right₀ ha0, neg_add_cancel]
  refine ⟨t, ?_⟩
  rw [hγeq, levelAutBar_mul q M' hqM' ζ α (ModularGroup.T ^ t) hαmem hT, AlgEquiv.trans_apply,
    levelAutBar_apply_eq_self_of_dvd hqM' ζ α hαmem h01 x hx,
    coe_levelAutBar_apply_eq_qTwist_of_redQ_eq_unipotent q M' hqM' ζ (ModularGroup.T ^ t) hT
      ⟨(t : ZMod q), redQ_T_zpow t⟩ u hu x, hx, ModularGroup.coe_T_zpow]
  simp

end ModularCurve.FullLevel.LevelAutGaussUnit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss.ModularCurve P2MW.S_ModularCurve_FullLevel_isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss.ModularCurve.FullLevel.LevelAutGaussUnit"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss.ModularCurve P2MW.S_ModularCurve_FullLevel_isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss.ModularCurve.FullLevel"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss.ModularCurve"

open ModularCurve.FullLevel.LevelAutGaussUnit in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M') (ζ : Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M')
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (a : A) :
    ∃ h : levelAutBar q M' ζ γ (IntermediateField.inclusion hle
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')))
        - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ O,
      IsUnit (⟨_, h⟩ : O) := by
  by_cases ha : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  · exact exists_mem_isUnit_levelAutBar_sub_of_dvd hqM' ζ γ hγ ha O hO _ (coe_inclusion_jBar hle) a
  · have hζ0 : ζ.val ≠ 0 := ζ.isPrimitiveRoot.ne_zero (Fact.out : q.Prime).ne_zero
    obtain ⟨t, ht⟩ := exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd hqM' ζ γ hγ ha (Units.mk0 _ hζ0) rfl _
      (coe_inclusion_jBar hle)
    exact exists_mem_isUnit_sub_algebraMap_of_coe_eq_qTwist O hO ζ (Units.mk0 _ hζ0) rfl t _ ht a

end S_ModularCurve_FullLevel_isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss
end P2MW
export P2MW.S_ModularCurve_FullLevel_isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss (solution)
