-- Prove2me | solution 1 for ModularCurve.delta_pow_mul_deuringPolynomial_lambda_pow_twelve
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e16f2ae9-54d0-514f-9207-063118bf44aa

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_LegendreJ
import Definitions.Def_ModularCurve_TateFormal
import Theorems.Thm_WeierstrassCurve_hasseInvariant_legendreCurve
import Theorems.Thm_WeierstrassCurve_isElliptic_legendreCurve_iff
import Theorems.Thm_WeierstrassCurve_j_legendreCurve
import Theorems.Thm_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq
import Theorems.Thm_WeierstrassCurve_hasseInvariant_tatePowerSeries_map
import Theorems.Thm_ModularCurve_delta_tateLaurent
import Theorems.Thm_ModularCurve_j_tateLaurent
import Theorems.Thm_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_delta_pow_mul_deuringPolynomial_lambda_pow_twelve
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "HahnSeries Polynomial ModularCurve P2MW.S_ModularCurve_delta_pow_mul_deuringPolynomial_lambda_pow_twelve.ModularCurve WeierstrassCurve P2MW.S_ModularCurve_delta_pow_mul_deuringPolynomial_lambda_pow_twelve.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ isUnit_Δ map_map map map_b₂ b₂ twoTorsionPolynomial map_j map_b₆ map_Δ b₆ b₈ Δ j b₄ hasseInvariant legendreCurve hasseInvariant_legendreCurve isElliptic_legendreCurve_iff j_legendreCurve hasseInvariant_pow_mul_delta_pow_eq_of_j_eq hasseInvariant_tatePowerSeries_map"
namespace DKfam
p2m_open "WeierstrassCurve"

variable {R S : Type*} [CommRing R] [CommRing S]

theorem hasseInvariant_map (q : ℕ) (W : WeierstrassCurve R) (φ : R →+* S) :
    (W.map φ).hasseInvariant q = φ (W.hasseInvariant q) := by
  unfold hasseInvariant
  have h : (W.map φ).twoTorsionPolynomial.toPoly = W.twoTorsionPolynomial.toPoly.map φ := by
    rw [← Cubic.map_toPoly]
    simp only [twoTorsionPolynomial, Cubic.map, map_b₂, map_b₄, map_b₆, map_ofNat, map_mul]
  rw [h, ← Polynomial.map_pow, Polynomial.coeff_map]

end WeierstrassCurve.DKfam

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd etaProd constantCoeff_etaProd dedekindEtaUnit dedekindEtaUnitInv jqModC lambdaInt lambdaModC laurentMap laurentMap_coeff laurentMap_single laurentMap_ofPowerSeries laurentMap_qExpand laurentMap_injective jqInt laurentMap_jqInt legendreJ tatePowerSeries laurentOfInt tateLaurent delta_tateLaurent j_tateLaurent qExpand_two_jq_mul_lambdaModC_sq"
namespace L7
p2m_open "ModularCurve"

def IsOneUnit {R : Type*} [CommRing R] (x : LaurentSeries R) : Prop := x.coeff 0 = 1 ∧ ∀ n < 0, x.coeff n = 0

namespace IsOneUnit

variable {R : Type*} [CommRing R]

theorem ofPowerSeries (P : PowerSeries R) (hP : PowerSeries.constantCoeff P = 1) :
    IsOneUnit (HahnSeries.ofPowerSeries ℤ R P) := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [PowerSeries.coeff_coe, if_neg (by omega)]; simpa using hP
  · rw [PowerSeries.coeff_coe, if_pos hn]

theorem mul {x y : LaurentSeries R} (hx : IsOneUnit x) (hy : IsOneUnit y) : IsOneUnit (x * y) := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [HahnSeries.coeff_mul, Finset.sum_eq_single ((0, 0) : ℤ × ℤ)]
    · rw [hx.1, hy.1, mul_one]
    · intro ij hij hne
      rw [Finset.mem_antidiagonal] at hij
      obtain ⟨h1, h2, h3⟩ := hij
      have hi : 0 ≤ ij.1 := by
        by_contra h; rw [not_le] at h; exact (HahnSeries.mem_support _ _).mp h1 (hx.2 _ h)
      have hj : 0 ≤ ij.2 := by
        by_contra h; rw [not_le] at h; exact (HahnSeries.mem_support _ _).mp h2 (hy.2 _ h)
      exfalso; apply hne
      exact Prod.ext (by omega) (by omega)
    · intro h
      rw [Finset.mem_antidiagonal, not_and_or, not_and_or] at h
      rcases h with h | h | h
      · rw [HahnSeries.mem_support, not_not] at h; rw [h, zero_mul]
      · rw [HahnSeries.mem_support, not_not] at h; rw [h, mul_zero]
      · exact absurd (by simp) h
  · rw [HahnSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    exfalso
    by_cases hi : ij.1 < 0
    · exact (HahnSeries.mem_support _ _).mp h1 (hx.2 _ hi)
    · exact (HahnSeries.mem_support _ _).mp h2 (hy.2 _ (by omega))

theorem pow {x : LaurentSeries R} (hx : IsOneUnit x) (n : ℕ) : IsOneUnit (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact ⟨by simp, fun n hn => by rw [HahnSeries.coeff_one, if_neg hn.ne]⟩
  | succ n ih => rw [pow_succ]; exact ih.mul hx

theorem qExpand {x : LaurentSeries R} (hx : IsOneUnit x) (N : ℕ) [NeZero N] : IsOneUnit (ModularCurve.qExpand R N x) := by
  refine ⟨?_, fun n hn => ?_⟩
  · have h := qExpand_coeff_mul (R := R) N x 0
    rw [mul_zero] at h
    rw [h, hx.1]
  · by_cases hd : (N : ℤ) ∣ n
    · obtain ⟨c, rfl⟩ := hd
      rw [qExpand_coeff_mul]
      have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      exact hx.2 c (by nlinarith)
    · exact qExpand_coeff_of_not_dvd N x hd

end IsOneUnit

theorem lambdaInt_eq : lambdaInt = HahnSeries.single (1 : ℤ) (1 : ℤ) *
    (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 * ModularCurve.qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
      ModularCurve.qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)) := by
  rw [lambdaInt]; ring

theorem isOneUnit_lambdaInt_tail : IsOneUnit
    (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 * ModularCurve.qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
      ModularCurve.qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)) := by
  have hE : IsOneUnit (HahnSeries.ofPowerSeries ℤ ℤ etaProd) := IsOneUnit.ofPowerSeries _ constantCoeff_etaProd
  have hD : IsOneUnit (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv) := by
    refine IsOneUnit.ofPowerSeries _ ?_
    rw [dedekindEtaUnitInv, PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]
  exact ((hE.pow 8).mul ((hE.pow 16).qExpand 4)).mul (hD.qExpand 2)

theorem coeff_lambdaInt_one : lambdaInt.coeff 1 = 1 := by
  have h := HahnSeries.coeff_single_mul_add (r := (1 : ℤ))
    (x := HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 * ModularCurve.qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
      ModularCurve.qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)) (a := 0) (b := (1 : ℤ))
  rw [zero_add, one_mul] at h
  rw [lambdaInt_eq, h]
  exact isOneUnit_lambdaInt_tail.1

theorem coeff_lambdaInt_of_lt {n : ℤ} (hn : n < 1) : lambdaInt.coeff n = 0 := by
  have h := HahnSeries.coeff_single_mul_add (r := (1 : ℤ))
    (x := HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 * ModularCurve.qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
      ModularCurve.qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)) (a := n - 1) (b := (1 : ℤ))
  rw [sub_add_cancel, one_mul] at h
  rw [lambdaInt_eq, h]
  exact isOneUnit_lambdaInt_tail.2 _ (by omega)

variable {k : Type*} [Field k]

theorem coeff_lambdaModC_one : (lambdaModC k).coeff 1 = 1 := by
  rw [lambdaModC, laurentMap_coeff, coeff_lambdaInt_one, map_one]

theorem coeff_lambdaModC_of_lt {n : ℤ} (hn : n < 1) : (lambdaModC k).coeff n = 0 := by
  rw [lambdaModC, laurentMap_coeff, coeff_lambdaInt_of_lt hn, map_zero]

theorem lambdaModC_ne_zero : lambdaModC k ≠ 0 :=
  HahnSeries.ne_zero_of_coeff_ne_zero (by rw [coeff_lambdaModC_one]; exact one_ne_zero)

theorem sixteen_mul_lambdaModC_ne_one : 16 * lambdaModC k ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries k => x.coeff 0) h
  simp only [HahnSeries.coeff_one, if_true] at h1
  rw [show (16 : LaurentSeries k) = ((16 : ℕ) : LaurentSeries k) by norm_num,
    ← map_natCast (HahnSeries.C (Γ := ℤ) (R := k)) 16, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
    coeff_lambdaModC_of_lt (by norm_num), smul_zero] at h1
  exact zero_ne_one h1

theorem laurentMap_jqInt_eq_jqModC (R : Type*) [CommRing R] : laurentMap (Int.castRingHom R) jqInt = jqModC R := by
  rw [jqInt, map_mul, laurentMap_single, laurentMap_ofPowerSeries, map_one]
  rfl

theorem jLambda (k' : Type*) [Field k'] :
    ModularCurve.qExpand k' 2 (jqModC k') * lambdaModC k' ^ 2 * (16 * lambdaModC k' - 1) ^ 2
      = (256 * lambdaModC k' ^ 2 - 16 * lambdaModC k' + 1) ^ 3 := by
  have hZ : ModularCurve.qExpand ℤ 2 jqInt * lambdaInt ^ 2 * (16 * lambdaInt - 1) ^ 2
      = (256 * lambdaInt ^ 2 - 16 * lambdaInt + 1) ^ 3 := by
    apply laurentMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
    simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, laurentMap_qExpand, laurentMap_jqInt]
    exact qExpand_two_jq_mul_lambdaModC_sq
  have h := congrArg (laurentMap (Int.castRingHom k')) hZ
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, laurentMap_qExpand, laurentMap_jqInt_eq_jqModC] at h
  rw [lambdaModC]
  exact h

theorem w0b_field {F : Type*} [Field F] (q : ℕ) [Fact q.Prime] [CharP F q]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic] (hj : W.j = W'.j) :
    W.hasseInvariant q ^ 12 * W'.Δ ^ (q - 1) = W'.hasseInvariant q ^ 12 * W.Δ ^ (q - 1) := by
  let F' := AlgebraicClosure F
  let ι : F →+* F' := algebraMap F F'
  haveI : CharP F' q := charP_of_injective_ringHom ι.injective q
  haveI : (W.map ι).IsElliptic := ⟨by rw [WeierstrassCurve.map_Δ]; exact (W.isUnit_Δ).map ι⟩
  haveI : (W'.map ι).IsElliptic := ⟨by rw [WeierstrassCurve.map_Δ]; exact (W'.isUnit_Δ).map ι⟩
  have hjj : (W.map ι).j = (W'.map ι).j := by rw [WeierstrassCurve.map_j, WeierstrassCurve.map_j, hj]
  have h := hasseInvariant_pow_mul_delta_pow_eq_of_j_eq q (W.map ι) (W'.map ι) hjj
  rw [WeierstrassCurve.DKfam.hasseInvariant_map, WeierstrassCurve.DKfam.hasseInvariant_map, WeierstrassCurve.map_Δ,
    WeierstrassCurve.map_Δ, ← map_pow, ← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul] at h
  exact ι.injective h

theorem main (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (k : Type*) [Field k] [CharP k q] :
    ModularCurve.qExpand k 2 (HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit))) ^ (q - 1)
        * (Polynomial.aeval (16 * lambdaModC k) ((Polynomial.deuringPolynomial q).map (Int.castRingHom k))) ^ 12
      = (lambdaModC k * (1 - 16 * lambdaModC k)) ^ (2 * (q - 1)) := by
  have hp : q.Prime := Fact.out
  have hcast : ∀ a : ℕ, 0 < a → a < q → (a : k) ≠ 0 := fun a ha haq h =>
    absurd (Nat.le_of_dvd ha ((CharP.cast_eq_zero_iff k q a).mp h)) (not_le.mpr haq)
  have h2k : (2 : k) ≠ 0 := by exact_mod_cast hcast 2 (by norm_num) (by omega)
  obtain ⟨m, hqm⟩ : ∃ m, q - 1 = 2 * m := by obtain ⟨r, hr⟩ := hp.even_sub_one (by omega); exact ⟨r, by omega⟩
  have hm : (q - 1) / 2 = m := by omega

  set F := LaurentSeries k
  haveI : CharP F q := charP_of_injective_ringHom (HahnSeries.C_injective (Γ := ℤ) (R := k)) q
  have h2F : (2 : F) ≠ 0 := by
    rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := k)) 2]; exact fun h => h2k (HahnSeries.C_injective (by rw [h, map_zero]))
  have h16F : (16 : F) ≠ 0 := by
    have : (16 : F) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero _ h2F
  set μ : F := lambdaModC k with hμ
  set t : F := 16 * μ with ht
  set D₂ : F := ModularCurve.qExpand k 2 (HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit))) with hD₂
  set J₂ : F := ModularCurve.qExpand k 2 (jqModC k) with hJ₂
  set Hk := (Polynomial.deuringPolynomial q).map (Int.castRingHom k) with hHk

  have ht0 : t ≠ 0 := mul_ne_zero h16F lambdaModC_ne_zero
  have ht1 : t ≠ 1 := sixteen_mul_lambdaModC_ne_one
  haveI hLE : (legendreCurve t).IsElliptic := (isElliptic_legendreCurve_iff t h2F).mpr ⟨ht0, ht1⟩
  have hHasseL : (legendreCurve t).hasseInvariant q = (-4) ^ m * Polynomial.aeval t Hk := by
    rw [hasseInvariant_legendreCurve (hp.odd_of_ne_two (by omega)) t, hm]
    congr 1
    rw [hHk, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval_map]
    congr 1
    exact RingHom.ext_int _ _
  have hΔL : (legendreCurve t).Δ = 16 * t ^ 2 * (t - 1) ^ 2 := by
    simp only [legendreCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    ring
  have hjL : (legendreCurve t).j = J₂ := by
    rw [j_legendreCurve t, legendreJ]
    have hden : t ^ 2 * (t - 1) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1))
    rw [div_eq_iff hden]
    have hJ := jLambda k
    rw [← hμ, ← hJ₂] at hJ

    rw [ht]
    linear_combination (-256 : F) * hJ

  haveI hTE : ((tateLaurent k).map (ModularCurve.qExpand k 2)).IsElliptic :=
    ⟨by rw [WeierstrassCurve.map_Δ]; exact ((tateLaurent k).isUnit_Δ).map _⟩
  have hjT : ((tateLaurent k).map (ModularCurve.qExpand k 2)).j = J₂ := by rw [WeierstrassCurve.map_j, j_tateLaurent]
  have hΔT : ((tateLaurent k).map (ModularCurve.qExpand k 2)).Δ = D₂ := by rw [WeierstrassCurve.map_Δ, delta_tateLaurent]
  have hHT : (tateLaurent k).hasseInvariant q = 1 := by
    set φ : ZMod q →+* k := ZMod.castHom (dvd_refl q) k with hφ
    have hint : Int.castRingHom k = φ.comp (Int.castRingHom (ZMod q)) := RingHom.ext_int _ _
    have hT : tateLaurent k = ((tatePowerSeries.map (PowerSeries.map (Int.castRingHom (ZMod q)))).map
        (PowerSeries.map φ)).map (HahnSeries.ofPowerSeries ℤ k) := by
      rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, tateLaurent, laurentOfInt, hint, PowerSeries.map_comp]; rfl
    rw [hT, WeierstrassCurve.DKfam.hasseInvariant_map, WeierstrassCurve.DKfam.hasseInvariant_map,
      hasseInvariant_tatePowerSeries_map q (by omega), map_one, map_one]
  have hHasseT : ((tateLaurent k).map (ModularCurve.qExpand k 2)).hasseInvariant q = 1 := by
    rw [WeierstrassCurve.DKfam.hasseInvariant_map, hHT, map_one]

  have hW0 := w0b_field q (legendreCurve t) ((tateLaurent k).map (ModularCurve.qExpand k 2)) (hjL.trans hjT.symm)
  rw [hHasseL, hΔT, hHasseT, one_pow, one_mul, hΔL] at hW0

  have key : (16 : F) ^ (3 * (q - 1)) * (D₂ ^ (q - 1) * Polynomial.aeval t Hk ^ 12)
      = (16 : F) ^ (3 * (q - 1)) * (μ * (1 - 16 * μ)) ^ (2 * (q - 1)) := by
    have e1 : ((-4 : F) ^ m) ^ 12 = (16 : F) ^ (3 * (q - 1)) := by
      rw [← pow_mul, show m * 12 = 2 * (3 * (q - 1)) by omega, pow_mul]; norm_num
    have e2 : (16 * t ^ 2 * (t - 1) ^ 2) ^ (q - 1) = (16 : F) ^ (3 * (q - 1)) * (μ * (1 - 16 * μ)) ^ (2 * (q - 1)) := by
      rw [ht, show (16 : F) * (16 * μ) ^ 2 * (16 * μ - 1) ^ 2 = 16 ^ 3 * (μ * (1 - 16 * μ)) ^ 2 by ring, mul_pow, ← pow_mul,
        ← pow_mul, mul_comm 2 (q - 1)]
    calc (16 : F) ^ (3 * (q - 1)) * (D₂ ^ (q - 1) * Polynomial.aeval t Hk ^ 12)
        = ((-4 : F) ^ m * Polynomial.aeval t Hk) ^ 12 * D₂ ^ (q - 1) := by rw [mul_pow, e1]; ring
      _ = (16 * t ^ 2 * (t - 1) ^ 2) ^ (q - 1) := hW0
      _ = (16 : F) ^ (3 * (q - 1)) * (μ * (1 - 16 * μ)) ^ (2 * (q - 1)) := e2
  exact mul_left_cancel₀ (pow_ne_zero _ h16F) key

end ModularCurve.L7

theorem solution (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (k : Type*) [Field k] [CharP k q] :
    ModularCurve.qExpand k 2 (HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * ModularCurve.dedekindEtaUnit))) ^ (q - 1)
        * (Polynomial.aeval (16 * ModularCurve.lambdaModC k) ((Polynomial.deuringPolynomial q).map (Int.castRingHom k))) ^ 12
      = (ModularCurve.lambdaModC k * (1 - 16 * ModularCurve.lambdaModC k)) ^ (2 * (q - 1)) :=
  ModularCurve.L7.main q hq k

end S_ModularCurve_delta_pow_mul_deuringPolynomial_lambda_pow_twelve
end P2MW
export P2MW.S_ModularCurve_delta_pow_mul_deuringPolynomial_lambda_pow_twelve (solution)
