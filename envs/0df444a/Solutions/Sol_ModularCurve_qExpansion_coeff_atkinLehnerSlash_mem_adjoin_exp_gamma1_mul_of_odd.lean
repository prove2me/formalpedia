-- Prove2me | solution 1 for ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d8d9c26b-54fe-542f-9783-b48e6398ec69

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp
import Theorems.Thm_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_even
import Theorems.Thm_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_odd
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

namespace ALRATODD

theorem coeff_mem_of_mul_eq {S : Subfield ℂ} {x a b : PowerSeries ℂ}
    (hb : ∀ n, b.coeff n ∈ S) (hb0 : b ≠ 0) (ha : ∀ n, a.coeff n ∈ S) (h : x * b = a) :
    ∀ n, x.coeff n ∈ S := by
  classical
  have hex : ∃ r, b.coeff r ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hb0 (PowerSeries.ext fun n => by simpa using hno n)
  let r := Nat.find hex
  have hr : b.coeff r ≠ 0 := Nat.find_spec hex
  have hlt : ∀ j, j < r → b.coeff j = 0 := fun j hj => by
    have := Nat.find_min hex hj; simpa using this
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn := congrArg (fun s : PowerSeries ℂ => s.coeff (n + r)) h
    simp only [PowerSeries.coeff_mul] at hn
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hn

    have hsplit : ∑ i ∈ Finset.range (n + r + 1), x.coeff i * b.coeff (n + r - i)
        = ∑ i ∈ Finset.range (n + 1), x.coeff i * b.coeff (n + r - i) := by
      have hsub : Finset.range (n + 1) ⊆ Finset.range (n + r + 1) := Finset.range_subset_range.mpr (by omega)
      rw [← Finset.sum_subset hsub]
      intro i hi hi'
      simp only [Finset.mem_range] at hi hi'
      rw [hlt (n + r - i) (by omega), mul_zero]
    rw [hsplit, Finset.sum_range_succ, Nat.add_sub_cancel_left] at hn
    have hxn : x.coeff n = (a.coeff (n + r) - ∑ i ∈ Finset.range n, x.coeff i * b.coeff (n + r - i)) / b.coeff r := by
      rw [eq_div_iff hr, ← hn]; ring
    rw [hxn]
    refine div_mem (sub_mem (ha _) (sum_mem fun i hi => mul_mem (ih i (Finset.mem_range.mp hi)) (hb _))) (hb r)

abbrev Γ1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_Γ1 {N : ℕ} : (1 : ℝ) ∈ (Γ1 N).strictPeriods := by simp [Γ1]

theorem coe_eq_zero_of_odd {N : ℕ} (hN : N ∣ 2) {k : ℤ} (hk : Odd k) (f : ModularForm (Γ1 N) k) :
    (⇑f : ℍ → ℂ) = 0 := by
  have hmem : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma1 N := by
    rw [CongruenceSubgroup.Gamma1_mem]
    have h2 : ((-1 : ℤ) : ZMod N) = 1 := by
      have h2' : ((2 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 N).mpr (by exact_mod_cast hN)
      have h' : ((-1 : ℤ) : ZMod N) = 1 - ((2 : ℤ) : ZMod N) := by push_cast; ring
      rw [h', h2', sub_zero]
    simp [h2]
  ext τ
  have h := SlashInvariantForm.slash_action_eqn'' f (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hmem) τ
  have hsmul : ((Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) • τ) = τ := by
    show ((-1 : SL(2, ℤ)) • τ) = τ
    rw [ModularGroup.SL_neg_smul, one_smul]
  have hden : denom ((Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ = -1 := by
    simp [denom]
  rw [hsmul, hden, hk.neg_one_zpow, neg_one_mul] at h
  have : f τ = 0 := by
    have : (2 : ℂ) * f τ = 0 := by linear_combination h
    simpa using this
  simpa using this

theorem isIntegralQExp_mul {N : ℕ} {k k' : ℤ} {f : ModularForm (Γ1 N) k} {h : ModularForm (Γ1 N) k'}
    {r s : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp f r) (hh : ModularCurve.IsIntegralQExp h s) :
    ModularCurve.IsIntegralQExp (f.mul h) (r * s) := by
  unfold ModularCurve.IsIntegralQExp at *
  rw [ModularForm.coe_mul, ← ModularForm.coe_mul, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_Γ1, map_mul, hf, hh]

end ALRATODD

open ALRATODD UpperHalfPlane in
open scoped MatrixGroups ModularForm in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ} (hk : Odd k)
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    {p₀ : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp f p₀)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n ∈
      IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by
  classical
  set K := IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) with hKdef
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hM1 : 1 ≤ M := Nat.pos_of_ne_zero (NeZero.ne M)
  rcases lt_or_ge (M * p) 3 with hsmall | hMp
  ·
    have hN : M * p ∣ 2 := by
      have : M * p = 2 := by nlinarith
      rw [this]
    have hf0 : (⇑f : ℍ → ℂ) = 0 := coe_eq_zero_of_odd hN hk f
    have : (fun τ : ℍ => ((⇑f : ℍ → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) = 0 := by
      ext τ; simp [hf0, SlashAction.zero_slash]
    rw [this, UpperHalfPlane.qExpansion_zero]
    simp
  ·
    obtain ⟨k', h, r, hk', hh, hh0, hhK⟩ :=
      ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp p M hpM hMp γ hγ hγp

    obtain ⟨Ff, hFf⟩ := ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul p M hpM f γ hγ hγp
    obtain ⟨Fh, hFh⟩ := ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul p M hpM h γ hγ hγp
    have hfh : ModularCurve.IsIntegralQExp (f.mul h) (p₀ * r) := isIntegralQExp_mul hf hh
    have heven : Even (k + k') := Odd.add_odd hk hk'
    have hA : ∀ n : ℕ, (qExpansion 1 (⇑(Ff.mul Fh) : ℍ → ℂ)).coeff n ∈ K := by
      intro n
      have := ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_even p M hpM heven (f.mul h) hfh γ hγ hγp n
      have hfun : (fun τ : ℍ => ((⇑(f.mul h) : ℍ → ℂ) ∣[k + k'] γ) (ModularForm.heckeDiagMatrix p • τ)) = ⇑(Ff.mul Fh) := by
        ext τ
        rw [ModularForm.coe_mul, ModularForm.coe_mul, ModularForm.mul_slash_SL2, Pi.mul_apply, Pi.mul_apply, hFf, hFh]
      rwa [hfun] at this
    have hB : ∀ n : ℕ, (qExpansion 1 (⇑Fh : ℍ → ℂ)).coeff n ∈ K := by
      intro n; rw [hFh]; exact hhK n

    have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have hB0 : qExpansion 1 (⇑Fh : ℍ → ℂ) ≠ 0 := by
      intro h0
      have hFh0 : Fh = 0 := (ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_Γ1 Fh).mp h0
      apply hh0

      have hslash : ((⇑h : ℍ → ℂ) ∣[k'] γ) = 0 := by
        ext τ

        let τ' : ℍ := ⟨(τ : ℂ) / p, by
          rw [Complex.div_natCast_im]; exact div_pos τ.im_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp0))⟩
        have hτ : ModularForm.heckeDiagMatrix p • τ' = τ := by
          apply UpperHalfPlane.ext
          rw [ModularForm.coe_heckeDiagMatrix_smul hp0]
          show (p : ℂ) * ((τ : ℂ) / p) = τ
          rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hp0)]
        have := congrFun hFh τ'
        rw [hFh0, hτ] at this
        simpa using this.symm
      have : (⇑h : ℍ → ℂ) = (((⇑h : ℍ → ℂ) ∣[k'] γ) ∣[k'] γ⁻¹) := by
        rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
      rw [this, hslash, SlashAction.zero_slash]
    have hmul : qExpansion 1 (⇑Ff : ℍ → ℂ) * qExpansion 1 (⇑Fh : ℍ → ℂ) = qExpansion 1 (⇑(Ff.mul Fh) : ℍ → ℂ) :=
      (ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_Γ1 Ff Fh).symm
    have hX := coeff_mem_of_mul_eq (S := K.toSubfield) (fun n => hB n) hB0 (fun n => hA n) hmul n
    rwa [hFf] at hX

end S_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_odd
end P2MW
export P2MW.S_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul_of_odd (solution)
