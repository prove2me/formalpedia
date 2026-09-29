-- Prove2me | solution 1 for ModularCurve.isLevelPStructure_tateBase_cuspData_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/a280bbf3-1088-525e-a1fe-2714fe4376b7

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_mazurCusp
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivY
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isLevelPStructure_tateBase_cuspData_of_dvd
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open ModularCurve

namespace P2MKcTateLevelDvd

universe u

variable {R : Type u} [CommRing R]

theorem ofPowerSeries_eq_qExpand (m : ℕ) [NeZero m] (g g' : PowerSeries R)
    (h : ∀ n : ℕ, PowerSeries.coeff n g' = if m ∣ n then PowerSeries.coeff (n / m) g else 0) :
    HahnSeries.ofPowerSeries ℤ R g' = qExpand R m (HahnSeries.ofPowerSeries ℤ R g) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  ext k
  rcases lt_or_ge k 0 with hk | hk
  · rw [ofPowerSeries_coeff_of_neg _ hk]
    by_cases hdk : (m : ℤ) ∣ k
    · obtain ⟨k', rfl⟩ := hdk
      rw [qExpand_coeff_mul]
      have hk' : k' < 0 := by
        by_contra h'
        have : (0 : ℤ) ≤ (m : ℤ) * k' := by push_cast at h' ⊢; nlinarith
        omega
      rw [ofPowerSeries_coeff_of_neg _ hk']
    · rw [qExpand_coeff_of_not_dvd m _ hdk]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, h n]
    by_cases hdn : m ∣ n
    · obtain ⟨n', rfl⟩ := hdn
      rw [if_pos (dvd_mul_right m n'), Nat.mul_div_cancel_left n' hm, Nat.cast_mul, qExpand_coeff_mul,
        HahnSeries.ofPowerSeries_apply_coeff]
    · rw [if_neg hdn, qExpand_coeff_of_not_dvd m]
      exact fun h' => hdn (Int.natCast_dvd_natCast.mp h')

section NonToric

variable (p : ℕ) (c : Rˣ) (j : ℕ) (m : ℕ)

def bracket (α β γ : R) (n M e : ℕ) : R :=
  (if n = p * M + j * e then α else 0) + (if n + j * e = p * M then β else 0) + (if n = p * M then γ else 0)

theorem bracket_level_mul (hm : 0 < m) (α β γ : R) (n M e : ℕ) :
    bracket (m * p) (m * j) α β γ n M e = if m ∣ n then bracket p j α β γ (n / m) M e else 0 := by
  by_cases hdn : m ∣ n
  · obtain ⟨n', rfl⟩ := hdn
    rw [if_pos (dvd_mul_right m n'), Nat.mul_div_cancel_left n' hm, bracket, bracket]
    have h1 : (m * n' = m * p * M + m * j * e) ↔ (n' = p * M + j * e) := by
      constructor
      · intro h; exact Nat.eq_of_mul_eq_mul_left hm (by rw [h]; ring)
      · intro h; rw [h]; ring
    have h2 : (m * n' + m * j * e = m * p * M) ↔ (n' + j * e = p * M) := by
      constructor
      · intro h; exact Nat.eq_of_mul_eq_mul_left hm (by linear_combination h)
      · intro h; rw [show m * n' + m * j * e = m * (n' + j * e) by ring, h]; ring
    have h3 : (m * n' = m * p * M) ↔ (n' = p * M) := by
      constructor
      · intro h; exact Nat.eq_of_mul_eq_mul_left hm (by rw [h]; ring)
      · intro h; rw [h]; ring
    simp only [h1, h2, h3]
  · rw [if_neg hdn, bracket]
    have h1 : ¬ n = m * p * M + m * j * e := fun h => hdn ⟨p * M + j * e, by rw [h]; ring⟩
    have h2 : ¬ n + m * j * e = m * p * M := by
      intro h
      apply hdn
      refine ⟨p * M - j * e, ?_⟩
      rw [Nat.mul_sub, ← Nat.mul_assoc, ← Nat.mul_assoc, ← h, Nat.add_sub_cancel]
    have h3 : ¬ n = m * p * M := fun h => hdn ⟨p * M, by rw [h]; ring⟩
    rw [if_neg h1, if_neg h2, if_neg h3, add_zero, add_zero]

theorem bracket_eq_zero_of_lt (hjp : j < p) (α β γ : R) (n M e : ℕ) (hM : n < M) (he : e ∈ M.divisors) :
    bracket p j α β γ n M e = 0 := by
  have heM : e ≤ M := Nat.divisor_le he
  have hp : 1 ≤ p := by omega
  rw [bracket]
  have h1 : ¬ n = p * M + j * e := by
    intro h; have : p * M ≥ 1 * M := Nat.mul_le_mul_right M hp; omega
  have h2 : ¬ n + j * e = p * M := by
    intro h
    have hje : j * e ≤ (p - 1) * e := Nat.mul_le_mul_right e (by omega)
    have h' : (p - 1) * e ≤ (p - 1) * M := Nat.mul_le_mul_left _ heM
    have h'' : (p - 1) * M + M = p * M := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel (Nat.mul_le_mul_right M hp |>.trans' (by simp))]
    omega
  have h3 : ¬ n = p * M := by
    intro h; have : p * M ≥ 1 * M := Nat.mul_le_mul_right M hp; omega
  rw [if_neg h1, if_neg h2, if_neg h3, add_zero, add_zero]

theorem sum_bracket_range_eq (hjp : j < p) (α β γ : ℕ → R) (n N : ℕ) (hN : n ≤ N) :
    ∑ M ∈ Finset.range (N + 1), ∑ e ∈ M.divisors, bracket p j (α e) (β e) (γ e) n M e =
      ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, bracket p j (α e) (β e) (γ e) n M e := by
  symm
  apply Finset.sum_subset
  · intro M hM
    rw [Finset.mem_range] at hM ⊢
    omega
  · intro M hM hM'
    rw [Finset.mem_range] at hM hM'
    exact Finset.sum_eq_zero fun e he => bracket_eq_zero_of_lt p j hjp _ _ _ n M e (by omega) he

theorem head_level_mul (hm : 0 < m) (hj : 0 < j) (δ : ℕ → R) (n : ℕ) :
    (if m * j ∣ n then δ (n / (m * j)) * (c : R) ^ (n / (m * j)) else 0) =
      if m ∣ n then (if j ∣ n / m then δ (n / m / j) * (c : R) ^ (n / m / j) else 0) else 0 := by
  by_cases hdn : m ∣ n
  · obtain ⟨n', rfl⟩ := hdn
    rw [if_pos (dvd_mul_right m n'), Nat.mul_div_cancel_left n' hm]
    by_cases hj' : j ∣ n'
    · rw [if_pos (Nat.mul_dvd_mul_left m hj'), if_pos hj', ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left n' hm]
    · rw [if_neg hj', if_neg]
      exact fun h => hj' ((Nat.mul_dvd_mul_iff_left hm).mp h)
  · rw [if_neg hdn, if_neg]
    exact fun h => hdn (Dvd.dvd.trans (dvd_mul_right m j) h)

theorem coeff_slotSubst_tateUnivX_level_mul (hj : 0 < j) (hjp : j < p) (hm : 0 < m) (n : ℕ) :
    PowerSeries.coeff n (slotSubst R (m * p) c (m * j) tateUnivX) =
      if m ∣ n then PowerSeries.coeff (n / m) (slotSubst R p c j tateUnivX) else 0 := by
  have hmj : 0 < m * j := Nat.mul_pos hm hj
  have hmjp : m * j < m * p := Nat.mul_lt_mul_of_pos_left hjp hm

  have key : ∀ (P J : ℕ) (N : ℕ), PowerSeries.coeff N (slotSubst R P c J tateUnivX) =
      PowerSeries.coeff N (slotSubst R P c J tateUnivX) := fun _ _ _ => rfl
  have formX : ∀ (P J : ℕ) (hJ : 0 < J) (hJP : J < P) (N : ℕ),
      PowerSeries.coeff N (slotSubst R P c J tateUnivX) =
        (if J ∣ N then ((N / J : ℕ) : R) * (c : R) ^ (N / J) else 0) +
          ∑ M ∈ Finset.range (N + 1), ∑ e ∈ M.divisors,
            bracket P J ((e : R) * (c : R) ^ e) ((e : R) * ((c⁻¹ : Rˣ) : R) ^ e) (-(2 * (e : R))) N M e := by
    intro P J hJ hJP N
    rw [coeff_slotSubst_tateUnivX P c J hJ hJP N]
    congr 1
    refine Finset.sum_congr rfl fun M _ => Finset.sum_congr rfl fun e _ => ?_
    rw [bracket]
    split_ifs <;> ring
  rw [formX (m * p) (m * j) hmj hmjp n]
  by_cases hdn : m ∣ n
  · rw [if_pos hdn, formX p j hj hjp (n / m)]
    obtain ⟨n', rfl⟩ := hdn
    have hn' : m * n' / m = n' := Nat.mul_div_cancel_left n' hm
    rw [head_level_mul c j m hm hj (fun d => ((d : ℕ) : R)) (m * n'), if_pos (dvd_mul_right m n'), hn']
    congr 1
    rw [← sum_bracket_range_eq p j hjp (fun e => (e : R) * (c : R) ^ e)
      (fun e => (e : R) * ((c⁻¹ : Rˣ) : R) ^ e) (fun e => -(2 * (e : R))) n' (m * n')
      (Nat.le_mul_of_pos_left n' hm)]
    refine Finset.sum_congr rfl fun M _ => Finset.sum_congr rfl fun e _ => ?_
    rw [bracket_level_mul p j m hm, if_pos (dvd_mul_right m n'), hn']
  · rw [if_neg hdn, head_level_mul c j m hm hj (fun d => ((d : ℕ) : R)) n, if_neg hdn, zero_add]
    refine Finset.sum_eq_zero fun M _ => Finset.sum_eq_zero fun e _ => ?_
    rw [bracket_level_mul p j m hm, if_neg hdn]

theorem coeff_slotSubst_tateUnivY_level_mul (hj : 0 < j) (hjp : j < p) (hm : 0 < m) (n : ℕ) :
    PowerSeries.coeff n (slotSubst R (m * p) c (m * j) tateUnivY) =
      if m ∣ n then PowerSeries.coeff (n / m) (slotSubst R p c j tateUnivY) else 0 := by
  have hmj : 0 < m * j := Nat.mul_pos hm hj
  have hmjp : m * j < m * p := Nat.mul_lt_mul_of_pos_left hjp hm
  have formY : ∀ (P J : ℕ) (hJ : 0 < J) (hJP : J < P) (N : ℕ),
      PowerSeries.coeff N (slotSubst R P c J tateUnivY) =
        (if J ∣ N then (((N / J).choose 2 : ℕ) : R) * (c : R) ^ (N / J) else 0) +
          ∑ M ∈ Finset.range (N + 1), ∑ e ∈ M.divisors,
            bracket P J (((e.choose 2 : ℕ) : R) * (c : R) ^ e)
              (-((((e + 1).choose 2 : ℕ) : R) * ((c⁻¹ : Rˣ) : R) ^ e)) (e : R) N M e := by
    intro P J hJ hJP N
    rw [coeff_slotSubst_tateUnivY P c J hJ hJP N]
    congr 1
    refine Finset.sum_congr rfl fun M _ => Finset.sum_congr rfl fun e _ => ?_
    rw [bracket]
    split_ifs <;> ring
  rw [formY (m * p) (m * j) hmj hmjp n]
  by_cases hdn : m ∣ n
  · rw [if_pos hdn, formY p j hj hjp (n / m)]
    obtain ⟨n', rfl⟩ := hdn
    have hn' : m * n' / m = n' := Nat.mul_div_cancel_left n' hm
    rw [head_level_mul c j m hm hj (fun d => (((d.choose 2 : ℕ)) : R)) (m * n'), if_pos (dvd_mul_right m n'), hn']
    congr 1
    rw [← sum_bracket_range_eq p j hjp (fun e => ((e.choose 2 : ℕ) : R) * (c : R) ^ e)
      (fun e => -((((e + 1).choose 2 : ℕ) : R) * ((c⁻¹ : Rˣ) : R) ^ e)) (fun e => (e : R)) n' (m * n')
      (Nat.le_mul_of_pos_left n' hm)]
    refine Finset.sum_congr rfl fun M _ => Finset.sum_congr rfl fun e _ => ?_
    rw [bracket_level_mul p j m hm, if_pos (dvd_mul_right m n'), hn']
  · rw [if_neg hdn, head_level_mul c j m hm hj (fun d => (((d.choose 2 : ℕ)) : R)) n, if_neg hdn, zero_add]
    refine Finset.sum_eq_zero fun M _ => Finset.sum_eq_zero fun e _ => ?_
    rw [bracket_level_mul p j m hm, if_neg hdn]

theorem nonToricPoint_level_mul [NeZero m] (hj : 0 < j) (hjp : j < p) :
    nonToricPoint R (m * p) c (m * j) =
      (qExpand R m (nonToricPoint R p c j).1, qExpand R m (nonToricPoint R p c j).2) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [nonToricPoint, nonToricPoint, Prod.mk.injEq]
  exact ⟨ofPowerSeries_eq_qExpand m _ _ (coeff_slotSubst_tateUnivX_level_mul p c j m hj hjp hm),
    ofPowerSeries_eq_qExpand m _ _ (coeff_slotSubst_tateUnivY_level_mul p c j m hj hjp hm)⟩

end NonToric

section Toric

variable (p m : ℕ) (c : Rˣ)

theorem sum_divisors_level_mul (hm : 0 < m) (F : ℕ → R) (n' : ℕ) :
    (∑ d ∈ (m * n').divisors, if m * p ∣ d then F (m * n' / d) else 0) =
      ∑ d ∈ n'.divisors, if p ∣ d then F (n' / d) else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun d => d / m) (fun d => m * d) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    obtain ⟨⟨hdn, hn0⟩, hpd⟩ := hd
    obtain ⟨d', rfl⟩ : m ∣ d := Dvd.dvd.trans (dvd_mul_right m p) hpd
    rw [Nat.mul_div_cancel_left d' hm]
    exact ⟨⟨Nat.dvd_of_mul_dvd_mul_left hm hdn, fun h => hn0 (by rw [h, mul_zero])⟩,
      (Nat.mul_dvd_mul_iff_left hm).mp hpd⟩
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    obtain ⟨⟨hdn, hn0⟩, hpd⟩ := hd
    exact ⟨⟨Nat.mul_dvd_mul_left m hdn, Nat.mul_ne_zero (by omega) hn0⟩, Nat.mul_dvd_mul_left m hpd⟩
  · intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨d', rfl⟩ : m ∣ d := Dvd.dvd.trans (dvd_mul_right m p) hd.2
    rw [Nat.mul_div_cancel_left d' hm]
  · intro d hd
    exact Nat.mul_div_cancel_left d hm
  · intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨d', rfl⟩ : m ∣ d := Dvd.dvd.trans (dvd_mul_right m p) hd.2
    rw [Nat.mul_div_cancel_left d' hm]
    rcases Nat.eq_zero_or_pos d' with rfl | hd'
    · simp
    · rw [Nat.mul_div_mul_left n' d' hm]

theorem sum_divisors_eq_zero_of_not_dvd (F : ℕ → R) (n : ℕ) (hdn : ¬ m ∣ n) :
    (∑ d ∈ n.divisors, if m * p ∣ d then F (n / d) else 0) = 0 := by
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [if_neg]
  intro h
  exact hdn (Dvd.dvd.trans (Dvd.dvd.trans (dvd_mul_right m p) h) (Nat.dvd_of_mem_divisors hd))

theorem toric_coeff_level_mul (hm : 0 < m) (κ : R) (F : ℕ → R) (s : R) (n : ℕ) :
    (if n = 0 then κ
      else (∑ d ∈ n.divisors, if m * p ∣ d then F (n / d) else 0)
        + s * (if m * p ∣ n then ∑ e ∈ (n / (m * p)).divisors, (e : R) else 0)) =
      if m ∣ n then
        (if n / m = 0 then κ
          else (∑ d ∈ (n / m).divisors, if p ∣ d then F (n / m / d) else 0)
            + s * (if p ∣ n / m then ∑ e ∈ (n / m / p).divisors, (e : R) else 0))
      else 0 := by
  by_cases hdn : m ∣ n
  · obtain ⟨n', rfl⟩ := hdn
    rw [if_pos (dvd_mul_right m n'), Nat.mul_div_cancel_left n' hm]
    by_cases hn' : n' = 0
    · subst hn'; simp
    · rw [if_neg (Nat.mul_ne_zero (by omega) hn'), if_neg hn', sum_divisors_level_mul p m hm F n',
        Nat.mul_div_mul_left n' p hm]
      simp only [Nat.mul_dvd_mul_iff_left hm]
  · rw [if_neg hdn]
    have hn0 : n ≠ 0 := fun h => hdn (h ▸ dvd_zero m)
    rw [if_neg hn0, sum_divisors_eq_zero_of_not_dvd p m F n hdn, if_neg, mul_zero, add_zero]
    exact fun h => hdn (Dvd.dvd.trans (dvd_mul_right m p) h)

theorem tateToricPoint_level_mul [NeZero m] :
    tateToricPoint R (m * p) c =
      (qExpand R m (tateToricPoint R p c).1, qExpand R m (tateToricPoint R p c).2) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [tateToricPoint, tateToricPoint, Prod.mk.injEq]
  refine ⟨ofPowerSeries_eq_qExpand m _ _ fun n => ?_, ofPowerSeries_eq_qExpand m _ _ fun n => ?_⟩
  · rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    have e2 : ∀ A B : R, A - 2 * B = A + (-2) * B := fun A B => by ring
    simp only [e2]
    exact toric_coeff_level_mul p m hm _
      (fun t => ((t : ℕ) : R) * ((c : R) ^ t + ((c⁻¹ : Rˣ) : R) ^ t)) (-2) n
  · rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    have := toric_coeff_level_mul p m hm ((c : R) ^ 2 * Ring.inverse (1 - (c : R)) ^ 3)
      (fun t => ((t.choose 2 : ℕ) : R) * (c : R) ^ t - (((t + 1).choose 2 : ℕ) : R) * ((c⁻¹ : Rˣ) : R) ^ t) 1 n
    simpa only [one_mul] using this

end Toric

section Assembly

variable (ℓ m : ℕ) [Fact ℓ.Prime] [NeZero m]

theorem tateBase_level_mul : tateBase R (m * ℓ) = (tateBase R ℓ).map (qExpand R m) := by
  rw [tateBase, tateBase, WeierstrassCurve.map_map]
  congr 1
  ext f : 1
  exact (qExpand_qExpand ℓ m f).symm

scoped instance : Fact (1 < ℓ) := ⟨(Fact.out : ℓ.Prime).one_lt⟩

theorem lt_mul : m < m * ℓ := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hℓ : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  nlinarith

theorem val_cast_m : ((m : ZMod (m * ℓ))).val = m := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_mul ℓ m)]

theorem cast_m_ne_zero : (m : ZMod (m * ℓ)) ≠ 0 := by
  intro h
  have := val_cast_m ℓ m
  rw [h, ZMod.val_zero] at this
  exact NeZero.ne m this.symm

theorem cuspPoint_fst_level_mul (ζ : Rˣ) :
    cuspPoint R (m * ℓ) ζ ![(m : ZMod (m * ℓ)), 0] =
      (qExpand R m (cuspPoint R ℓ (ζ ^ m) ![1, 0]).1, qExpand R m (cuspPoint R ℓ (ζ ^ m) ![1, 0]).2) := by
  have h1 : (![(m : ZMod (m * ℓ)), 0] : Fin 2 → ZMod (m * ℓ)) 1 = 0 := rfl
  have h1' : (![(1 : ZMod ℓ), 0] : Fin 2 → ZMod ℓ) 1 = 0 := rfl
  rw [cuspPoint_of_eq_zero ζ h1, cuspPoint_of_eq_zero (ζ ^ m) h1']
  have h0 : (![(m : ZMod (m * ℓ)), 0] : Fin 2 → ZMod (m * ℓ)) 0 = (m : ZMod (m * ℓ)) := rfl
  have h0' : (![(1 : ZMod ℓ), 0] : Fin 2 → ZMod ℓ) 0 = 1 := rfl
  rw [h0, h0', val_cast_m ℓ m, ZMod.val_one, pow_one]
  exact tateToricPoint_level_mul ℓ m (ζ ^ m)

theorem cuspPoint_snd_level_mul (ζ : Rˣ) :
    cuspPoint R (m * ℓ) ζ ![0, (m : ZMod (m * ℓ))] =
      (qExpand R m (cuspPoint R ℓ (ζ ^ m) ![0, 1]).1, qExpand R m (cuspPoint R ℓ (ζ ^ m) ![0, 1]).2) := by
  have h1 : (![0, (m : ZMod (m * ℓ))] : Fin 2 → ZMod (m * ℓ)) 1 = (m : ZMod (m * ℓ)) := rfl
  have h1' : (![0, (1 : ZMod ℓ)] : Fin 2 → ZMod ℓ) 1 = 1 := rfl
  have hne : (![0, (m : ZMod (m * ℓ))] : Fin 2 → ZMod (m * ℓ)) 1 ≠ 0 := by
    rw [h1]; exact cast_m_ne_zero ℓ m
  have hne' : (![0, (1 : ZMod ℓ)] : Fin 2 → ZMod ℓ) 1 ≠ 0 := by rw [h1']; exact one_ne_zero
  rw [cuspPoint_of_ne_zero ζ hne, cuspPoint_of_ne_zero (ζ ^ m) hne']
  have h0 : (![0, (m : ZMod (m * ℓ))] : Fin 2 → ZMod (m * ℓ)) 0 = 0 := rfl
  have h0' : (![0, (1 : ZMod ℓ)] : Fin 2 → ZMod ℓ) 0 = 0 := rfl
  rw [h0, h0', h1, h1', ZMod.val_zero, ZMod.val_zero, pow_zero, pow_zero, val_cast_m ℓ m, ZMod.val_one]
  have := nonToricPoint_level_mul (R := R) ℓ 1 1 m one_pos (Fact.out : ℓ.Prime).one_lt
  rwa [mul_one] at this

theorem cuspData_level_mul (ζ : Rˣ) :
    cuspData R (m * ℓ) ζ ![(m : ZMod (m * ℓ)), 0] ![0, (m : ZMod (m * ℓ))] =
      (cuspData R ℓ (ζ ^ m) ![1, 0] ![0, 1]).map (qExpand R m) := by
  ext
  · rw [cuspData_xP, LevelPData.map_xP, cuspData_xP, cuspPoint_fst_level_mul]
  · rw [cuspData_yP, LevelPData.map_yP, cuspData_yP, cuspPoint_fst_level_mul]
  · rw [cuspData_xQ, LevelPData.map_xQ, cuspData_xQ, cuspPoint_snd_level_mul]
  · rw [cuspData_yQ, LevelPData.map_yQ, cuspData_yQ, cuspPoint_snd_level_mul]

theorem main (hℓ2 : ℓ ≠ 2) (hℓ : IsUnit (ℓ : R)) (ζ : Rˣ)
    (hζ : ∑ i ∈ Finset.range ℓ, ((ζ : R) ^ m) ^ i = 0) :
    IsLevelPStructure (tateBase R (m * ℓ)) ℓ
      (cuspData R (m * ℓ) ζ ![(m : ZMod (m * ℓ)), 0] ![0, (m : ZMod (m * ℓ))]) := by
  have hζ' : ∑ i ∈ Finset.range ℓ, ((ζ ^ m : Rˣ) : R) ^ i = 0 := by
    simpa only [Units.val_pow_eq_pow_val] using hζ
  have base := isLevelPStructure_tateBase_cuspData_mazurCusp (R := R) (p := ℓ) hℓ2 hℓ (ζ ^ m) hζ' 1 one_ne_zero
  rw [tateBase_level_mul, cuspData_level_mul]
  exact base.map (qExpand R m)

end Assembly

end P2MKcTateLevelDvd
p2m_reactivate "P2MW.S_ModularCurve_isLevelPStructure_tateBase_cuspData_of_dvd.P2MKcTateLevelDvd"

end
p2m_reactivate "P2MW.S_ModularCurve_isLevelPStructure_tateBase_cuspData_of_dvd.P2MKcTateLevelDvd"

open ModularCurve

universe u in

theorem solution
    {R : Type u} [CommRing R] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓ : IsUnit (ℓ : R))
    (n : ℕ) [NeZero n] (hn : ℓ ∣ n)
    (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range ℓ, ((ζ : R) ^ (n / ℓ)) ^ i = 0) :
    ModularCurve.IsLevelPStructure (ModularCurve.tateBase R n) ℓ
      (ModularCurve.cuspData R n ζ ![((n / ℓ : ℕ) : ZMod n), 0] ![0, ((n / ℓ : ℕ) : ZMod n)]) := by
  obtain ⟨m, rfl⟩ := exists_eq_mul_left_of_dvd hn
  have hℓpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have hm0 : m ≠ 0 := fun h => NeZero.ne (m * ℓ) (by rw [h, zero_mul])
  haveI : NeZero m := ⟨hm0⟩
  rw [Nat.mul_div_cancel m hℓpos] at hζ ⊢
  exact P2MKcTateLevelDvd.main ℓ m hℓ2 hℓ ζ hζ

end S_ModularCurve_isLevelPStructure_tateBase_cuspData_of_dvd
end P2MW
export P2MW.S_ModularCurve_isLevelPStructure_tateBase_cuspData_of_dvd (solution)
