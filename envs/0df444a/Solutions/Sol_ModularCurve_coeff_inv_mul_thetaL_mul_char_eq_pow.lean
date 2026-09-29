-- Prove2me | solution 1 for ModularCurve.coeff_inv_mul_thetaL_mul_char_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f330a7d5-83de-5493-ba78-3d10f193f68c

import Mathlib
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_theta_mul
import Theorems.Thm_ModularCurve_coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_inv_mul_thetaL_mul_char_eq_pow
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_coeff_inv_mul_thetaL_mul_char_eq_pow.ModularCurve HahnSeries Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "thetaL thetaL_apply coeffMap coeffMap_coeff theta_coeff theta_mul coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order"
p2m_open "ModularCurve"

namespace CartierDlog

variable {k : Type*} [Field k]

def dlog (f : LaurentSeries k) : LaurentSeries k := f⁻¹ * thetaL k f

theorem thetaL_coeff' (f : LaurentSeries k) (n : ℤ) : (thetaL k f).coeff n = (n : k) * f.coeff n := by
  rw [thetaL_apply, theta_coeff, zsmul_eq_mul]

theorem thetaL_mul' (f g : LaurentSeries k) : thetaL k (f * g) = f * thetaL k g + g * thetaL k f := by
  rw [thetaL_apply, theta_mul, ← thetaL_apply, ← thetaL_apply]

theorem thetaL_single (m : ℤ) (c : k) : thetaL k (single m c) = (m : k) • single m c := by
  ext j
  rw [thetaL_coeff', HahnSeries.coeff_smul, coeff_single, smul_eq_mul]
  split_ifs with h
  · subst h; rfl
  · rw [mul_zero, mul_zero]

theorem thetaL_C (c : k) : thetaL k (HahnSeries.C c) = 0 := by
  rw [C_apply, thetaL_single, Int.cast_zero, zero_smul]

theorem thetaL_one : thetaL k (1 : LaurentSeries k) = 0 := by
  rw [← map_one (HahnSeries.C (R := k) (Γ := ℤ)), thetaL_C]

theorem dlog_mul {f g : LaurentSeries k} (hf : f ≠ 0) (hg : g ≠ 0) : dlog (f * g) = dlog f + dlog g := by
  unfold dlog
  rw [thetaL_mul']
  field_simp
  ring

theorem dlog_C (c : k) : dlog (HahnSeries.C c : LaurentSeries k) = 0 := by
  unfold dlog; rw [thetaL_C, mul_zero]

theorem dlog_one : dlog (1 : LaurentSeries k) = 0 := by
  unfold dlog; rw [thetaL_one, mul_zero]

theorem single_ne_zero' (m : ℤ) {c : k} (hc : c ≠ 0) : (single m c : LaurentSeries k) ≠ 0 := by
  rw [Ne, single_eq_zero_iff]; exact hc

theorem dlog_single_one (m : ℤ) : dlog (single m (1 : k) : LaurentSeries k) = HahnSeries.C ((m : ℤ) : k) := by
  unfold dlog
  rw [thetaL_single, ← C_mul_eq_smul, mul_comm (HahnSeries.C _) _, ← mul_assoc,
    inv_mul_cancel₀ (single_ne_zero' m one_ne_zero), one_mul]

variable (p : ℕ) [hp : Fact p.Prime]

def IsFixed (H : LaurentSeries k) : Prop := ∀ n : ℤ, H.coeff (n * p) = (H.coeff n) ^ p

variable {p}

theorem IsFixed.zero : IsFixed p (0 : LaurentSeries k) := fun n => by
  rw [HahnSeries.coeff_zero, HahnSeries.coeff_zero, zero_pow hp.out.ne_zero]

theorem IsFixed.add [CharP k p] {H H' : LaurentSeries k} (h : IsFixed p H) (h' : IsFixed p H') :
    IsFixed p (H + H') := fun n => by
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add, h n, h' n, add_pow_char]

theorem mul_natCast_ne_zero {n : ℤ} (hn : n ≠ 0) : n * (p : ℤ) ≠ 0 :=
  mul_ne_zero hn (by exact_mod_cast hp.out.ne_zero)

theorem isFixed_C_intCast [CharP k p] (m : ℤ) : IsFixed p (HahnSeries.C ((m : ℤ) : k) : LaurentSeries k) := by
  intro n
  rw [C_apply, coeff_single, coeff_single]
  by_cases hn : n = 0
  · subst hn
    simp only [zero_mul, if_true]
    have h := map_intCast (frobenius k p) m
    rw [frobenius_def] at h
    exact h.symm
  · rw [if_neg (mul_natCast_ne_zero hn), if_neg hn, zero_pow hp.out.ne_zero]

theorem one_sub_single_mul_geom (a : k) :
    (1 - single 1 a : LaurentSeries k) *
        ((PowerSeries.mk fun n => a ^ n : PowerSeries k) : LaurentSeries k) = 1 := by
  have hcoe : (1 - single 1 a : LaurentSeries k) =
      (((1 : PowerSeries k) - PowerSeries.C a * PowerSeries.X : PowerSeries k) : LaurentSeries k) := by
    rw [map_sub, map_one, map_mul, ofPowerSeries_C, ofPowerSeries_X, C_apply, single_mul_single,
      zero_add, mul_one]
  rw [hcoe, ← PowerSeries.coe_mul]
  have h1 : ((1 : PowerSeries k) - PowerSeries.C a * PowerSeries.X) *
      (PowerSeries.mk fun n => a ^ n) = 1 := by
    ext n
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_one, mul_assoc,
      PowerSeries.coeff_C_mul]
    cases n with
    | zero =>
        rw [if_pos rfl, pow_zero]
        simp [PowerSeries.coeff_zero_eq_constantCoeff]
    | succ n =>
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), pow_succ]
        ring
  rw [h1]
  exact map_one _

theorem coeff_dlog_one_sub (a : k) (m : ℤ) :
    (dlog (1 - single 1 a : LaurentSeries k)).coeff m = if 1 ≤ m then -a ^ m.toNat else 0 := by
  set G : LaurentSeries k := ((PowerSeries.mk fun n => a ^ n : PowerSeries k) : LaurentSeries k) with hG
  have hne : (1 - single 1 a : LaurentSeries k) ≠ 0 := by
    intro h
    have := one_sub_single_mul_geom a
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have hinv : (1 - single 1 a : LaurentSeries k)⁻¹ = G :=
    inv_eq_of_mul_eq_one_right (one_sub_single_mul_geom a)
  have hθ : thetaL k (1 - single 1 a : LaurentSeries k) = -single 1 a := by
    rw [map_sub, thetaL_one, thetaL_single, Int.cast_one, one_smul, zero_sub]
  have hGc : ∀ j : ℤ, G.coeff j = if j < 0 then 0 else a ^ j.toNat := by
    intro j
    rw [hG, PowerSeries.coeff_coe]
    split_ifs with hj
    · rfl
    · rw [PowerSeries.coeff_mk]
      congr 1
      have h0 : 0 ≤ j := not_lt.mp hj
      omega
  unfold dlog
  rw [hinv, hθ, mul_neg, HahnSeries.coeff_neg, mul_comm]
  have hm : m = (m - 1) + 1 := by ring
  rw [hm, coeff_single_mul_add, hGc]
  have hm' : m - 1 + 1 = m := by ring
  rw [hm']
  by_cases h1 : 1 ≤ m
  · rw [if_neg (by omega), if_pos h1]
    have : m.toNat = (m - 1).toNat + 1 := by omega
    rw [this, pow_succ, mul_comm]
  · rw [if_pos (by omega), if_neg h1, mul_zero, neg_zero]

theorem isFixed_dlog_one_sub [CharP k p] (a : k) : IsFixed p (dlog (1 - single 1 a : LaurentSeries k)) := by
  intro n
  rw [coeff_dlog_one_sub, coeff_dlog_one_sub]
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  by_cases hn : 1 ≤ n
  · have hnp : 1 ≤ n * p := by nlinarith
    rw [if_pos hnp, if_pos hn, neg_pow, neg_one_pow_char, neg_one_mul, ← pow_mul]
    congr 2
    have h0 : 0 ≤ n := by omega
    have : (n * p).toNat = n.toNat * p := by
      have h1 : ((n * p).toNat : ℤ) = ((n.toNat * p : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (by nlinarith), Nat.cast_mul, Int.toNat_of_nonneg h0]
      exact_mod_cast h1
    rw [this]
  · have hnp : ¬ 1 ≤ n * p := by
      intro h
      apply hn
      by_contra h'
      have : n * p ≤ 0 := by nlinarith
      omega
    rw [if_neg hnp, if_neg hn, zero_pow hp.out.ne_zero]

theorem coe_one_sub_C_mul_X (a : k) :
    (((1 - Polynomial.C a * X : k[X]) : PowerSeries k) : LaurentSeries k) = 1 - single 1 a := by
  rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
    map_sub, map_one, map_mul, ofPowerSeries_C, ofPowerSeries_X, C_apply, single_mul_single, zero_add,
    mul_one]

theorem coe_coe_ne_zero {P : k[X]} (hP : P ≠ 0) : ((P : PowerSeries k) : LaurentSeries k) ≠ 0 := by
  intro h
  apply hP
  have h1 : (P : PowerSeries k) = 0 := ofPowerSeries_injective (by rw [h]; exact (map_zero _).symm)
  exact Polynomial.coe_eq_zero_iff.mp h1

theorem ne_zero_of_eval_zero_eq_one {P : k[X]} (hP : P.eval 0 = 1) : P ≠ 0 := by
  rintro rfl
  rw [eval_zero] at hP
  exact zero_ne_one hP

theorem isFixed_dlog_poly [CharP k p] [IsAlgClosed k] :
    ∀ (N : ℕ) (P : k[X]), P.natDegree ≤ N → P.eval 0 = 1 →
      IsFixed p (dlog ((P : PowerSeries k) : LaurentSeries k)) := by
  intro N
  induction N with
  | zero =>
      intro P hdeg heval
      have hP : P = 1 := by
        rw [eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hdeg), coeff_zero_eq_eval_zero, heval, map_one]
      rw [hP, Polynomial.coe_one, map_one, dlog_one]
      exact IsFixed.zero
  | succ N ih =>
      intro P hdeg heval
      by_cases hle : P.natDegree ≤ N
      · exact ih P hle heval
      have hdegP : P.natDegree = N + 1 := by omega
      have hP0 : P ≠ 0 := ne_zero_of_eval_zero_eq_one heval
      have hdeg0 : P.degree ≠ 0 := by
        rw [degree_eq_natDegree hP0, hdegP]
        exact_mod_cast Nat.succ_ne_zero N
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root P hdeg0
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [IsRoot.def, heval] at hr
        exact one_ne_zero hr

      set Q : k[X] := P /ₘ (X - Polynomial.C r) with hQ
      have hPQ : (X - Polynomial.C r) * Q = P := mul_divByMonic_eq_iff_isRoot.mpr hr
      set P₁ : k[X] := Polynomial.C (-r) * Q with hP₁
      have hfac : P = (1 - Polynomial.C r⁻¹ * X) * P₁ := by
        rw [hP₁, ← hPQ, ← mul_assoc]
        congr 1
        have h1 : Polynomial.C r⁻¹ * Polynomial.C r = (1 : k[X]) := by
          rw [← map_mul, inv_mul_cancel₀ hr0, map_one]
        rw [map_neg]
        linear_combination (-X) * h1
      have hdeg₁ : P₁.natDegree ≤ N := by
        rw [hP₁, natDegree_C_mul (neg_ne_zero.mpr hr0), hQ, natDegree_divByMonic P (monic_X_sub_C r),
          natDegree_X_sub_C, hdegP]
        omega
      have heval₁ : P₁.eval 0 = 1 := by
        have h := heval
        rw [hfac, eval_mul] at h
        simpa using h
      have h1ne : ((((1 - Polynomial.C r⁻¹ * X : k[X])) : PowerSeries k) : LaurentSeries k) ≠ 0 := by
        refine coe_coe_ne_zero (ne_zero_of_eval_zero_eq_one ?_)
        simp
      have hP₁ne : ((P₁ : PowerSeries k) : LaurentSeries k) ≠ 0 :=
        coe_coe_ne_zero (ne_zero_of_eval_zero_eq_one heval₁)
      rw [hfac, Polynomial.coe_mul, PowerSeries.coe_mul, dlog_mul h1ne hP₁ne]
      refine IsFixed.add ?_ (ih P₁ hdeg₁ heval₁)
      rw [coe_one_sub_C_mul_X]
      exact isFixed_dlog_one_sub r⁻¹

def IsPS (x : LaurentSeries k) : Prop := ∃ P : PowerSeries k, (P : LaurentSeries k) = x

theorem isPS_coe (P : PowerSeries k) : IsPS (P : LaurentSeries k) := ⟨P, rfl⟩

theorem IsPS.add {x y : LaurentSeries k} (hx : IsPS x) (hy : IsPS y) : IsPS (x + y) := by
  obtain ⟨P, rfl⟩ := hx; obtain ⟨Q, rfl⟩ := hy; exact ⟨P + Q, map_add _ _ _⟩

theorem IsPS.sub {x y : LaurentSeries k} (hx : IsPS x) (hy : IsPS y) : IsPS (x - y) := by
  obtain ⟨P, rfl⟩ := hx; obtain ⟨Q, rfl⟩ := hy; exact ⟨P - Q, map_sub _ _ _⟩

theorem IsPS.mul {x y : LaurentSeries k} (hx : IsPS x) (hy : IsPS y) : IsPS (x * y) := by
  obtain ⟨P, rfl⟩ := hx; obtain ⟨Q, rfl⟩ := hy; exact ⟨P * Q, map_mul _ _ _⟩

theorem IsPS.smul {x : LaurentSeries k} (hx : IsPS x) (c : k) : IsPS (c • x) := by
  obtain ⟨P, rfl⟩ := hx
  refine ⟨PowerSeries.C c * P, ?_⟩
  rw [PowerSeries.coe_mul, ofPowerSeries_C, C_mul_eq_smul]

theorem IsPS.thetaL {x : LaurentSeries k} (hx : IsPS x) : IsPS (thetaL k x) := by
  obtain ⟨u, rfl⟩ := hx
  refine ⟨PowerSeries.mk fun n => (n : k) * PowerSeries.coeff n u, ?_⟩
  ext j
  rw [thetaL_coeff', PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · rw [mul_zero]
  · rw [PowerSeries.coeff_mk]
    congr 1
    have : (j.natAbs : ℤ) = j := Int.natAbs_of_nonneg (not_lt.mp h)
    rw [← this, Int.cast_natCast, Int.natAbs_natCast]

theorem IsPS.coeff_zero_eq {x : LaurentSeries k} {P : PowerSeries k} (h : (P : LaurentSeries k) = x) :
    x.coeff 0 = PowerSeries.constantCoeff P := by
  rw [← h, PowerSeries.coeff_coe, if_neg (lt_irrefl 0), ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rfl

theorem IsPS.inv {x : LaurentSeries k} (hx : IsPS x) (h0 : x.coeff 0 ≠ 0) : IsPS x⁻¹ := by
  obtain ⟨P, rfl⟩ := hx
  have hP : PowerSeries.constantCoeff P ≠ 0 := by rwa [← IsPS.coeff_zero_eq rfl]
  refine ⟨P⁻¹, ?_⟩
  symm
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← PowerSeries.coe_mul, PowerSeries.mul_inv_cancel P hP]
  exact map_one _

theorem coeff_single_mul_eq_zero_of_lt {x : LaurentSeries k} (hx : IsPS x) (M j : ℤ) (hj : j < M) :
    (single M (1 : k) * x).coeff j = 0 := by
  obtain ⟨P, rfl⟩ := hx
  have : j = (j - M) + M := by ring
  rw [this, coeff_single_mul_add, one_mul, PowerSeries.coeff_coe, if_pos (by linarith)]

theorem dlog_add_sub_dlog (V S R W : LaurentSeries k) (hV : V ≠ 0) (hU : V + S * R ≠ 0)
    (hθ : thetaL k (S * R) = S * W) :
    dlog (V + S * R) - dlog V = S * ((V * W - R * thetaL k V) * ((V + S * R) * V)⁻¹) := by
  unfold dlog
  rw [map_add, hθ, mul_inv]
  field_simp
  ring

theorem coe_ne_zero_of_constantCoeff {P : PowerSeries k} (h : PowerSeries.constantCoeff P ≠ 0) :
    (P : LaurentSeries k) ≠ 0 := by
  intro h0
  apply h
  rw [← IsPS.coeff_zero_eq (x := (P : LaurentSeries k)) rfl, h0, HahnSeries.coeff_zero]

theorem coeff_dlog_eq_coeff_dlog_trunc (U : PowerSeries k) (hU : PowerSeries.constantCoeff U ≠ 0)
    (M : ℕ) (j : ℤ) (hj : j < ((M + 1 : ℕ) : ℤ)) :
    (dlog (U : LaurentSeries k)).coeff j =
      (dlog (((PowerSeries.trunc (M + 1) U : k[X]) : PowerSeries k) : LaurentSeries k)).coeff j := by

  have hdvd : (PowerSeries.X : PowerSeries k) ^ (M + 1) ∣
      U - ((PowerSeries.trunc (M + 1) U : k[X]) : PowerSeries k) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]
  obtain ⟨R, hR⟩ := hdvd
  have hV0 : PowerSeries.constantCoeff ((PowerSeries.trunc (M + 1) U : k[X]) : PowerSeries k) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, PowerSeries.coeff_trunc,
      if_pos (Nat.succ_pos M), PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hU
  have hUVR : (U : LaurentSeries k) = ((PowerSeries.trunc (M + 1) U : k[X]) : PowerSeries k) +
      single (((M + 1 : ℕ) : ℤ)) (1 : k) * (R : LaurentSeries k) := by
    have h := congrArg (HahnSeries.ofPowerSeries ℤ k) hR
    rw [map_sub, map_mul, ofPowerSeries_X_pow] at h
    rw [← h, add_sub_cancel]

  have hθS : thetaL k (single (((M + 1 : ℕ) : ℤ)) (1 : k) * (R : LaurentSeries k)) =
      single (((M + 1 : ℕ) : ℤ)) (1 : k) *
        (thetaL k (R : LaurentSeries k) + HahnSeries.C ((((M + 1 : ℕ) : ℤ) : k)) * (R : LaurentSeries k)) := by
    rw [thetaL_mul', thetaL_single, mul_add, ← C_mul_eq_smul]
    ring
  have hdiff := dlog_add_sub_dlog _ _ _ _ (coe_ne_zero_of_constantCoeff hV0)
    (by rw [← hUVR]; exact coe_ne_zero_of_constantCoeff hU) hθS
  rw [← hUVR] at hdiff

  have hZps : IsPS (((((PowerSeries.trunc (M + 1) U : k[X]) : PowerSeries k) : LaurentSeries k) *
      (thetaL k (R : LaurentSeries k) + HahnSeries.C ((((M + 1 : ℕ) : ℤ) : k)) * (R : LaurentSeries k)) -
      (R : LaurentSeries k) * thetaL k (((PowerSeries.trunc (M + 1) U : k[X]) : PowerSeries k) : LaurentSeries k)) *
      ((U : LaurentSeries k) * (((PowerSeries.trunc (M + 1) U : k[X]) : PowerSeries k) : LaurentSeries k))⁻¹) := by
    have hRps : IsPS (R : LaurentSeries k) := isPS_coe R
    have hVps : IsPS ((((PowerSeries.trunc (M + 1) U : k[X]) : PowerSeries k) : LaurentSeries k)) := isPS_coe _
    have hUps : IsPS (U : LaurentSeries k) := isPS_coe U
    have hCps : IsPS (HahnSeries.C ((((M + 1 : ℕ) : ℤ) : k)) : LaurentSeries k) := by
      have := isPS_coe (k := k) (PowerSeries.C ((((M + 1 : ℕ) : ℤ) : k)))
      rwa [ofPowerSeries_C] at this
    refine ((hVps.mul (hRps.thetaL.add (hCps.mul hRps))).sub (hRps.mul hVps.thetaL)).mul
      ((hUps.mul hVps).inv ?_)
    rw [IsPS.coeff_zero_eq (P := U * ((PowerSeries.trunc (M + 1) U : k[X]) : PowerSeries k))
      (by rw [PowerSeries.coe_mul]), map_mul]
    exact mul_ne_zero hU hV0
  have hj' : (dlog (U : LaurentSeries k)).coeff j -
      (dlog (((PowerSeries.trunc (M + 1) U : k[X]) : PowerSeries k) : LaurentSeries k)).coeff j = 0 := by
    rw [← HahnSeries.coeff_sub, hdiff]
    exact coeff_single_mul_eq_zero_of_lt hZps _ j hj
  exact sub_eq_zero.mp hj'

theorem coeff_dlog_C_mul {c : k} (hc : c ≠ 0) {x : LaurentSeries k} (hx : x ≠ 0) :
    dlog (HahnSeries.C c * x) = dlog x := by
  rw [dlog_mul (by rw [Ne, HahnSeries.C_apply, single_eq_zero_iff]; exact hc) hx, dlog_C, zero_add]

theorem coeff_dlog_mul_char [CharP k p] [IsAlgClosed k] (f : LaurentSeries k) (hf : f ≠ 0) (n : ℤ) :
    (dlog f).coeff (n * p) = ((dlog f).coeff n) ^ p := by
  obtain ⟨hneg, hzero⟩ := coeff_inv_mul_thetaL_eq_zero_and_coeff_zero_eq_order k f hf
  change ∀ m : ℤ, m < 0 → (dlog f).coeff m = 0 at hneg
  change (dlog f).coeff 0 = _ at hzero
  rcases lt_trichotomy n 0 with hn | rfl | hn
  ·
    have hnp : n * p < 0 := mul_neg_of_neg_of_pos hn (by exact_mod_cast hp.out.pos)
    rw [hneg n hn, hneg _ hnp, zero_pow hp.out.ne_zero]
  ·
    rw [zero_mul, hzero]
    have h := map_intCast (frobenius k p) f.order
    rw [frobenius_def] at h
    exact h.symm
  ·
    set U : PowerSeries k := f.powerSeriesPart with hU
    have hU0 : PowerSeries.constantCoeff U ≠ 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hU, LaurentSeries.powerSeriesPart_coeff,
        Nat.cast_zero, add_zero]
      exact fun h => hf (coeff_order_eq_zero.mp h)
    have hUL0 : (U : LaurentSeries k) ≠ 0 := coe_ne_zero_of_constantCoeff hU0
    have hf' : f = single f.order 1 * (U : LaurentSeries k) :=
      (LaurentSeries.single_order_mul_powerSeriesPart f).symm

    have hsplit : ∀ m : ℤ, m ≠ 0 → (dlog f).coeff m = (dlog (U : LaurentSeries k)).coeff m := by
      intro m hm
      rw [hf', dlog_mul (single_ne_zero' _ one_ne_zero) hUL0, dlog_single_one, HahnSeries.coeff_add,
        C_apply, coeff_single_of_ne hm, zero_add]
    have hn0 : n ≠ 0 := hn.ne'
    rw [hsplit n hn0, hsplit _ (mul_natCast_ne_zero hn0)]

    set M : ℕ := (n * p).toNat with hM
    have hnpM : n * p < ((M + 1 : ℕ) : ℤ) := by
      have : ((M : ℕ) : ℤ) = n * p := Int.toNat_of_nonneg (by positivity)
      push_cast
      omega
    have hnM : n < ((M + 1 : ℕ) : ℤ) := by
      have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.out.one_lt.le
      have : n ≤ n * p := by nlinarith
      exact lt_of_le_of_lt this hnpM
    rw [coeff_dlog_eq_coeff_dlog_trunc U hU0 M _ hnpM, coeff_dlog_eq_coeff_dlog_trunc U hU0 M _ hnM]

    set T : k[X] := PowerSeries.trunc (M + 1) U with hT
    have hT0 : T.eval 0 = PowerSeries.constantCoeff U := by
      rw [← coeff_zero_eq_eval_zero, hT, PowerSeries.coeff_trunc, if_pos (Nat.succ_pos M),
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
    set c : k := PowerSeries.constantCoeff U with hc
    set T₁ : k[X] := Polynomial.C c⁻¹ * T with hT₁
    have hT₁0 : T₁.eval 0 = 1 := by
      rw [hT₁, eval_C_mul, hT0, inv_mul_cancel₀ hU0]
    have hTT₁ : ((T : PowerSeries k) : LaurentSeries k) = HahnSeries.C c * ((T₁ : PowerSeries k) : LaurentSeries k) := by
      rw [hT₁, Polynomial.coe_mul, Polynomial.coe_C, PowerSeries.coe_mul, ofPowerSeries_C, ← mul_assoc,
        ← map_mul, mul_inv_cancel₀ hU0, map_one, one_mul]
    have hT₁ne : ((T₁ : PowerSeries k) : LaurentSeries k) ≠ 0 :=
      coe_coe_ne_zero (ne_zero_of_eval_zero_eq_one hT₁0)
    rw [hTT₁, coeff_dlog_C_mul hU0 hT₁ne]
    exact isFixed_dlog_poly T₁.natDegree T₁ le_rfl hT₁0 n

theorem coeffMap_thetaL {K' : Type*} [Field K'] (ι : k →+* K') (x : LaurentSeries k) :
    coeffMap ι (thetaL k x) = thetaL K' (coeffMap ι x) := by
  ext n
  rw [coeffMap_coeff, thetaL_coeff', thetaL_coeff', coeffMap_coeff, map_mul, map_intCast]

theorem coeffMap_dlog {K' : Type*} [Field K'] (ι : k →+* K') (f : LaurentSeries k) :
    coeffMap ι (dlog f) = dlog (coeffMap ι f) := by
  unfold dlog
  rw [map_mul, map_inv₀, coeffMap_thetaL]

theorem main [CharP k p] (f : LaurentSeries k) (hf : f ≠ 0) (n : ℤ) :
    (f⁻¹ * thetaL k f).coeff (n * p) = ((f⁻¹ * thetaL k f).coeff n) ^ p := by
  let ι : k →+* AlgebraicClosure k := algebraMap k (AlgebraicClosure k)
  haveI : CharP (AlgebraicClosure k) p := charP_of_injective_algebraMap ι.injective p
  have hf' : coeffMap ι f ≠ 0 := by
    intro h
    apply hf
    ext m
    have hm := congrArg (fun s : LaurentSeries (AlgebraicClosure k) => s.coeff m) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at hm
    rw [HahnSeries.coeff_zero]
    exact ι.injective (by rw [hm, map_zero])
  have h := coeff_dlog_mul_char (p := p) (coeffMap ι f) hf' n
  rw [← coeffMap_dlog, coeffMap_coeff, coeffMap_coeff, ← map_pow] at h
  exact ι.injective h

end CartierDlog

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeff_inv_mul_thetaL_mul_char_eq_pow.ModularCurve in
theorem solution
    (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : LaurentSeries k) (hf : f ≠ 0) (n : ℤ) :
    (f⁻¹ * thetaL k f).coeff (n * p) = ((f⁻¹ * thetaL k f).coeff n) ^ p :=
  ModularCurve.CartierDlog.main f hf n

end S_ModularCurve_coeff_inv_mul_thetaL_mul_char_eq_pow
end P2MW
export P2MW.S_ModularCurve_coeff_inv_mul_thetaL_mul_char_eq_pow (solution)
