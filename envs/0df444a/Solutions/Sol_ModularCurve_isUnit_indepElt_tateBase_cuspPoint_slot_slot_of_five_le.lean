-- Prove2me | solution 1 for ModularCurve.isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/defdd34c-b8bb-5f0e-bf71-91abe888fe79

import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_exists_chordSlope_nonToricPoint
import Theorems.Thm_ModularCurve_exists_tangentSlope_nonToricPoint
import Theorems.Thm_ModularCurve_equation_tateBase_nonToricPoint
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivY
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_phi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

namespace KTORDTors

private theorem key_of_halfSystem {G : Type*} [AddCommGroup G] (p H : ℕ)
    (hpH : p = 2 * H + 1) (hH2 : 2 ≤ H) (Q : ℕ → G)
    (hrig : ∀ a b, 1 ≤ a → a ≤ H → 1 ≤ b → b ≤ H → (Q a = Q b ∨ Q a = -Q b) → a = b)
    (hchord : ∀ i j m, 1 ≤ i → i ≤ H → 1 ≤ j → j ≤ H → i ≠ j → 1 ≤ m → m ≤ H →
      (m = i + j ∨ i + j + m = p) → Q i + Q j = Q m ∨ Q i + Q j = -Q m)
    (htang : ∀ k m, 1 ≤ k → k ≤ H → 1 ≤ m → m ≤ H → (m = 2 * k ∨ 2 * k + m = p) →
      Q k + Q k = Q m ∨ Q k + Q k = -Q m) :
    ∀ k, 1 ≤ k → k ≤ H → k • Q 1 = Q k := by
  intro k
  induction k with
  | zero => intro h1 _; exact absurd h1 (by omega)
  | succ n ih =>
    intro _ hsucc
    by_cases hn0 : n = 0
    · subst hn0
      simp
    · have h1n : 1 ≤ n := by omega
      have hnH : n ≤ H := by omega
      have ihn := ih h1n hnH
      have hsum : (n + 1) • Q 1 = Q n + Q 1 := by rw [succ_nsmul, ihn]
      have hland : Q n + Q 1 = Q (n + 1) ∨ Q n + Q 1 = -Q (n + 1) := by
        by_cases hn1 : n = 1
        · subst hn1
          exact htang 1 2 le_rfl (by omega) (by omega) (by omega) (Or.inl (by omega))
        · exact hchord n 1 (n + 1) h1n hnH le_rfl (by omega) hn1 (by omega) hsucc
            (Or.inl (by omega))
      rcases hland with hgood | hbad
      · rw [hsum, hgood]
      · exfalso
        have hQn1 : Q (n + 1) = -(Q n + Q 1) := neg_eq_iff_eq_neg.mp hbad.symm
        obtain ⟨m', h1m', hm'H, hm'⟩ :
            ∃ m', 1 ≤ m' ∧ m' ≤ H ∧ (m' = (n + 1) + n ∨ (n + 1) + n + m' = p) := by
          by_cases hc : 2 * n + 1 ≤ H
          · exact ⟨2 * n + 1, by omega, hc, Or.inl (by omega)⟩
          · exact ⟨p - (2 * n + 1), by omega, by omega, Or.inr (by omega)⟩
        have hsum2 : Q (n + 1) + Q n = Q m' ∨ Q (n + 1) + Q n = -Q m' :=
          hchord (n + 1) n m' (by omega) hsucc h1n hnH (by omega) h1m' hm'H hm'
        have hL : Q (n + 1) + Q n = -Q 1 := by rw [hQn1]; abel
        have h1m : (1 : ℕ) = m' := by
          apply hrig 1 m' le_rfl (by omega) h1m' hm'H
          rcases hsum2 with h2 | h2
          · exact Or.inr (neg_eq_iff_eq_neg.mp (hL.symm.trans h2))
          · exact Or.inl (neg_injective (hL.symm.trans h2))
        omega

private theorem torsion_of_halfSystem {G : Type*} [AddCommGroup G] (p H : ℕ)
    (hpH : p = 2 * H + 1) (hH2 : 2 ≤ H) (Q : ℕ → G)
    (hQ1 : Q 1 ≠ 0)
    (hrig : ∀ a b, 1 ≤ a → a ≤ H → 1 ≤ b → b ≤ H → (Q a = Q b ∨ Q a = -Q b) → a = b)
    (hchord : ∀ i j m, 1 ≤ i → i ≤ H → 1 ≤ j → j ≤ H → i ≠ j → 1 ≤ m → m ≤ H →
      (m = i + j ∨ i + j + m = p) → Q i + Q j = Q m ∨ Q i + Q j = -Q m)
    (htang : ∀ k m, 1 ≤ k → k ≤ H → 1 ≤ m → m ≤ H → (m = 2 * k ∨ 2 * k + m = p) →
      Q k + Q k = Q m ∨ Q k + Q k = -Q m) :
    ∀ k, 1 ≤ k → k ≤ H → p • Q k = 0 := by
  have key := key_of_halfSystem p H hpH hH2 Q hrig hchord htang

  have hp1 : p • Q 1 = 0 := by
    have hkeyH := key H (by omega) le_rfl
    have hfin : Q H + Q 1 = Q H ∨ Q H + Q 1 = -Q H :=
      hchord H 1 H (by omega) le_rfl le_rfl (by omega) (by omega) (by omega) le_rfl
        (Or.inr (by omega))
    rcases hfin with hgood | hbad
    · exact absurd (add_left_cancel (a := Q H) (by rw [hgood, add_zero])) hQ1
    · have e1 : (H + 1) • Q 1 = -Q H := by rw [succ_nsmul, hkeyH, hbad]
      have e2 : p • Q 1 = (H + 1) • Q 1 + H • Q 1 := by
        rw [show p = (H + 1) + H by omega, add_nsmul]
      rw [e2, e1, hkeyH]
      exact neg_add_cancel (Q H)

  intro k h1k hkH
  rw [← key k h1k hkH, ← mul_nsmul, Nat.mul_comm, mul_nsmul, hp1, smul_zero]

open ModularCurve WeierstrassCurve.Affine

private noncomputable def slotPt (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (b : ℕ)
    (hNS : ∀ m, 1 ≤ m → m ≤ p / 2 → (tateBase K p).toAffine.Nonsingular
      (nonToricPoint K p (ζ ^ (b * m)) m).1 (nonToricPoint K p (ζ ^ (b * m)) m).2)
    (m : ℕ) : (tateBase K p).toAffine.Point :=
  if hm : 1 ≤ m ∧ m ≤ p / 2 then .some _ _ (hNS m hm.1 hm.2) else 0

private theorem slotPt_eq (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) (b : ℕ)
    (hNS : ∀ m, 1 ≤ m → m ≤ p / 2 → (tateBase K p).toAffine.Nonsingular
      (nonToricPoint K p (ζ ^ (b * m)) m).1 (nonToricPoint K p (ζ ^ (b * m)) m).2)
    (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ p / 2) :
    slotPt K p ζ b hNS m = .some _ _ (hNS m h1 h2) :=
  dif_pos ⟨h1, h2⟩

private theorem dev_core (K : Type*) [Field K] [DecidableEq (LaurentSeries K)]
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (ζ : Kˣ) (hζ : ζ ^ p = 1) (b : ℕ)
    (hNS : ∀ m, 1 ≤ m → m ≤ p / 2 → (tateBase K p).toAffine.Nonsingular
      (nonToricPoint K p (ζ ^ (b * m)) m).1 (nonToricPoint K p (ζ ^ (b * m)) m).2) :
    (∀ k, 1 ≤ k → k ≤ p / 2 → k • slotPt K p ζ b hNS 1 = slotPt K p ζ b hNS k) ∧
      (∀ k, 1 ≤ k → k ≤ p / 2 → p • slotPt K p ζ b hNS k = 0) := by
  have hp' : p.Prime := Fact.out
  have hodd : p % 2 = 1 := by
    rcases hp'.eq_two_or_odd with h2 | ho
    · omega
    · exact ho
  have hpH : p = 2 * (p / 2) + 1 := by omega
  have hH2 : 2 ≤ p / 2 := by omega

  have hQ1 : slotPt K p ζ b hNS 1 ≠ 0 := by
    rw [slotPt_eq K p ζ b hNS 1 le_rfl (by omega)]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _

  have hxinj : ∀ a c, 1 ≤ a → a ≤ p / 2 → 1 ≤ c → c ≤ p / 2 →
      (nonToricPoint K p (ζ ^ (b * a)) a).1 = (nonToricPoint K p (ζ ^ (b * c)) c).1 →
      a = c := by
    intro a c h1a haH h1c hcH hxe
    by_contra hne
    obtain ⟨m, h1m, hmH, hm⟩ : ∃ m, 1 ≤ m ∧ m ≤ p / 2 ∧ (m = a + c ∨ a + c + m = p) := by
      by_cases hc' : a + c ≤ p / 2
      · exact ⟨a + c, by omega, hc', Or.inl rfl⟩
      · exact ⟨p - (a + c), by omega, by omega, Or.inr (by omega)⟩
    have hu := (ModularCurve.exists_chordSlope_nonToricPoint K p hp5 ζ hζ b a c m
      h1a h1c hne haH hcH h1m hmH hm).1
    rw [hxe, sub_self] at hu
    exact not_isUnit_zero hu
  have hrig : ∀ a c, 1 ≤ a → a ≤ p / 2 → 1 ≤ c → c ≤ p / 2 →
      (slotPt K p ζ b hNS a = slotPt K p ζ b hNS c ∨
        slotPt K p ζ b hNS a = -slotPt K p ζ b hNS c) → a = c := by
    intro a c h1a haH h1c hcH hor
    apply hxinj a c h1a haH h1c hcH
    rw [slotPt_eq K p ζ b hNS a h1a haH, slotPt_eq K p ζ b hNS c h1c hcH] at hor
    exact WeierstrassCurve.Affine.Point.X_eq_iff.mpr hor

  have hchord : ∀ i j m, 1 ≤ i → i ≤ p / 2 → 1 ≤ j → j ≤ p / 2 → i ≠ j → 1 ≤ m →
      m ≤ p / 2 → (m = i + j ∨ i + j + m = p) →
      slotPt K p ζ b hNS i + slotPt K p ζ b hNS j = slotPt K p ζ b hNS m ∨
        slotPt K p ζ b hNS i + slotPt K p ζ b hNS j = -slotPt K p ζ b hNS m := by
    intro i j m h1i hiH h1j hjH hij h1m hmH hm
    obtain ⟨hu, ℓ, hℓ, hland⟩ := ModularCurve.exists_chordSlope_nonToricPoint K p hp5 ζ hζ b
      i j m h1i h1j hij hiH hjH h1m hmH hm
    have hxne : (nonToricPoint K p (ζ ^ (b * i)) i).1 ≠
        (nonToricPoint K p (ζ ^ (b * j)) j).1 := sub_ne_zero.mp hu.ne_zero
    rw [slotPt_eq K p ζ b hNS i h1i hiH, slotPt_eq K p ζ b hNS j h1j hjH,
      slotPt_eq K p ζ b hNS m h1m hmH,
      WeierstrassCurve.Affine.Point.add_of_X_ne hxne]
    apply WeierstrassCurve.Affine.Point.X_eq_iff.mp
    have hsl : (tateBase K p).toAffine.slope (nonToricPoint K p (ζ ^ (b * i)) i).1
        (nonToricPoint K p (ζ ^ (b * j)) j).1 (nonToricPoint K p (ζ ^ (b * i)) i).2
        (nonToricPoint K p (ζ ^ (b * j)) j).2 = ℓ := by
      rw [slope_of_X_ne hxne, eq_comm, eq_div_iff (sub_ne_zero.mpr hxne)]
      exact hℓ
    rw [hsl]
    simp only [WeierstrassCurve.Affine.addX]
    linear_combination hland

  have htang : ∀ c m, 1 ≤ c → c ≤ p / 2 → 1 ≤ m → m ≤ p / 2 →
      (m = 2 * c ∨ 2 * c + m = p) →
      slotPt K p ζ b hNS c + slotPt K p ζ b hNS c = slotPt K p ζ b hNS m ∨
        slotPt K p ζ b hNS c + slotPt K p ζ b hNS c = -slotPt K p ζ b hNS m := by
    intro c m h1c hcH h1m hmH hm
    obtain ⟨hu, ℓ, hℓ, hland⟩ := ModularCurve.exists_tangentSlope_nonToricPoint K p hp5 ζ hζ b
      c m h1c hcH h1m hmH hm
    have hyne : (nonToricPoint K p (ζ ^ (b * c)) c).2 ≠
        (tateBase K p).toAffine.negY (nonToricPoint K p (ζ ^ (b * c)) c).1
          (nonToricPoint K p (ζ ^ (b * c)) c).2 := by
      intro hcontra
      rw [WeierstrassCurve.Affine.negY] at hcontra
      exact hu.ne_zero (by linear_combination hcontra)
    have hden : (nonToricPoint K p (ζ ^ (b * c)) c).2 -
        (tateBase K p).toAffine.negY (nonToricPoint K p (ζ ^ (b * c)) c).1
          (nonToricPoint K p (ζ ^ (b * c)) c).2 =
        2 * (nonToricPoint K p (ζ ^ (b * c)) c).2 +
          (tateBase K p).a₁ * (nonToricPoint K p (ζ ^ (b * c)) c).1 + (tateBase K p).a₃ := by
      rw [WeierstrassCurve.Affine.negY]
      ring
    rw [slotPt_eq K p ζ b hNS c h1c hcH, slotPt_eq K p ζ b hNS m h1m hmH,
      WeierstrassCurve.Affine.Point.add_of_Y_ne hyne]
    apply WeierstrassCurve.Affine.Point.X_eq_iff.mp
    have hsl : (tateBase K p).toAffine.slope (nonToricPoint K p (ζ ^ (b * c)) c).1
        (nonToricPoint K p (ζ ^ (b * c)) c).1 (nonToricPoint K p (ζ ^ (b * c)) c).2
        (nonToricPoint K p (ζ ^ (b * c)) c).2 = ℓ := by
      rw [slope_of_Y_ne rfl hyne, eq_comm, eq_div_iff (sub_ne_zero.mpr hyne), hden]
      exact hℓ
    rw [hsl]
    simp only [WeierstrassCurve.Affine.addX]
    linear_combination hland
  exact ⟨key_of_halfSystem p (p / 2) hpH hH2 (slotPt K p ζ b hNS) hrig hchord htang,
    torsion_of_halfSystem p (p / 2) hpH hH2 (slotPt K p ζ b hNS) hQ1 hrig hchord htang⟩

end KTORDTors

namespace KTORDAlpha

open ModularCurve

variable {K K' : Type*} [CommRing K] [CommRing K'] (h : K →+* K')

def laurentMap : LaurentSeries K →+* LaurentSeries K' where
  toFun x := x.map h
  map_one' := HahnSeries.map_one h.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul h.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero h.toZeroHom
  map_add' _ _ := HahnSeries.map_add h.toAddMonoidHom

@[scoped simp]
theorem laurentMap_coeff (x : LaurentSeries K) (n : ℤ) :
    (laurentMap h x).coeff n = h (x.coeff n) :=
  rfl

private theorem laurentMap_nonToricPoint_fst (p : ℕ) (c : Kˣ) (j : ℕ)
    (hj : 0 < j) (hjp : j < p) :
    laurentMap h (nonToricPoint K p c j).1 =
      (nonToricPoint K' p (Units.map (h : K →* K') c) j).1 := by
  ext n
  rw [laurentMap_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [nonToricPoint_fst, nonToricPoint_fst, ModularCurve.ofPowerSeries_coeff_of_neg _ hn,
      ModularCurve.ofPowerSeries_coeff_of_neg _ hn, map_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [nonToricPoint_fst, nonToricPoint_fst, HahnSeries.ofPowerSeries_apply_coeff,
      HahnSeries.ofPowerSeries_apply_coeff,
      ModularCurve.coeff_slotSubst_tateUnivX p c j hj hjp m,
      ModularCurve.coeff_slotSubst_tateUnivX p (Units.map (h : K →* K') c) j hj hjp m]
    simp only [map_add, map_mul, map_sum, map_sub, map_pow, map_natCast, map_ofNat,
      apply_ite h, map_zero, ← map_inv, Units.coe_map, MonoidHom.coe_coe]

private theorem laurentMap_nonToricPoint_snd (p : ℕ) (c : Kˣ) (j : ℕ)
    (hj : 0 < j) (hjp : j < p) :
    laurentMap h (nonToricPoint K p c j).2 =
      (nonToricPoint K' p (Units.map (h : K →* K') c) j).2 := by
  ext n
  rw [laurentMap_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [nonToricPoint_snd, nonToricPoint_snd, ModularCurve.ofPowerSeries_coeff_of_neg _ hn,
      ModularCurve.ofPowerSeries_coeff_of_neg _ hn, map_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [nonToricPoint_snd, nonToricPoint_snd, HahnSeries.ofPowerSeries_apply_coeff,
      HahnSeries.ofPowerSeries_apply_coeff,
      ModularCurve.coeff_slotSubst_tateUnivY p c j hj hjp m,
      ModularCurve.coeff_slotSubst_tateUnivY p (Units.map (h : K →* K') c) j hj hjp m]
    simp only [map_add, map_mul, map_sum, map_sub, map_pow, map_natCast,
      apply_ite h, map_zero, ← map_inv, Units.coe_map, MonoidHom.coe_coe]

private theorem laurentMap_qExpand_laurentOfInt (p : ℕ) [NeZero p] (F : PowerSeries ℤ) :
    laurentMap h (qExpand K p (laurentOfInt K F)) = qExpand K' p (laurentOfInt K' F) := by
  ext n
  rw [laurentMap_coeff]
  by_cases hdvd : (p : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, qExpand_coeff_mul]
    rcases lt_or_ge k 0 with hk | hk
    · rw [laurentOfInt_apply, laurentOfInt_apply, ModularCurve.ofPowerSeries_coeff_of_neg _ hk,
        ModularCurve.ofPowerSeries_coeff_of_neg _ hk, map_zero]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      rw [laurentOfInt_apply, laurentOfInt_apply, HahnSeries.ofPowerSeries_apply_coeff,
        HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_map]
      simp
  · rw [qExpand_coeff_of_not_dvd _ _ hdvd, qExpand_coeff_of_not_dvd _ _ hdvd, map_zero]

private theorem map_tateBase (p : ℕ) [NeZero p] :
    (tateBase K p).map (laurentMap h) = tateBase K' p := by
  rw [tateBase, tateBase, tateLaurent, tateLaurent, WeierstrassCurve.map_map,
    WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  suffices hcomp : ((laurentMap h).comp (qExpand K p)).comp (laurentOfInt K) =
      (qExpand K' p).comp (laurentOfInt K') by rw [hcomp]
  refine RingHom.ext fun F => ?_
  simpa using laurentMap_qExpand_laurentOfInt h p F

theorem alpha_main (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    ((tateBase K' p).preΨ p).eval (nonToricPoint K' p (Units.map (h : K →* K') c) j).1 =
      laurentMap h (((tateBase K p).preΨ p).eval (nonToricPoint K p c j).1) := by
  rw [← laurentMap_nonToricPoint_fst h p c j hj hjp, ← map_tateBase h p,
    WeierstrassCurve.map_preΨ, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (laurentMap h) _

end KTORDAlpha
p2m_reactivate "P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDAlpha"

namespace KTORDBeta

open Polynomial

variable (p : ℕ)

abbrev U : Type := AdjoinRoot (X ^ p - 1 : ℤ[X])

noncomputable def uT : U p := AdjoinRoot.root _

theorem uT_pow : uT p ^ p = 1 := by
  have h := AdjoinRoot.eval₂_root (X ^ p - 1 : ℤ[X])
  rw [eval₂_sub, eval₂_X_pow, eval₂_one, sub_eq_zero] at h
  exact h

noncomputable def uTunit [NeZero p] : (U p)ˣ :=
  Units.mkOfMulEqOne (uT p) (uT p ^ (p - 1))
    (by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne p)), uT_pow])

theorem val_uTunit [NeZero p] : (uTunit p : U p) = uT p := rfl

noncomputable def spec (R : Type*) [CommRing R] (c : R) (hc : c ^ p = 1) : U p →+* R :=
  AdjoinRoot.lift (Int.castRingHom R) c (by rw [eval₂_sub, eval₂_X_pow, eval₂_one, hc, sub_self])

theorem spec_uT (R : Type*) [CommRing R] (c : R) (hc : c ^ p = 1) : spec p R c hc (uT p) = c :=
  AdjoinRoot.lift_root _

theorem spec_mk (R : Type*) [CommRing R] (c : R) (hc : c ^ p = 1) (g : ℤ[X]) :
    spec p R c hc (AdjoinRoot.mk _ g) = g.eval₂ (Int.castRingHom R) c :=
  AdjoinRoot.lift_mk _ g

theorem spec_val_uTunit [NeZero p] (R : Type*) [CommRing R] (c : R) (hc : c ^ p = 1) :
    spec p R c hc (uTunit p : U p) = c :=
  spec_uT p R c hc

noncomputable def ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

theorem ζ_isPrimitiveRoot [NeZero p] : IsPrimitiveRoot (ζ p) p :=
  Complex.isPrimitiveRoot_exp p (NeZero.ne p)

noncomputable def e₁ : U p →+* ℚ := spec p ℚ 1 (one_pow p)

noncomputable def e₂ [NeZero p] : U p →+* ℂ := spec p ℂ (ζ p) (ζ_isPrimitiveRoot p).pow_eq_one

theorem e₁_uT : e₁ p (uT p) = 1 := spec_uT p ℚ 1 _

theorem e₂_uT [NeZero p] : e₂ p (uT p) = ζ p := spec_uT p _ _ _

theorem e₁_mk (g : ℤ[X]) : e₁ p (AdjoinRoot.mk _ g) = ((g.eval 1 : ℤ) : ℚ) := by
  rw [e₁, spec_mk, eval₂_at_one, eq_intCast]

theorem e₂_mk [NeZero p] (g : ℤ[X]) : e₂ p (AdjoinRoot.mk _ g) = aeval (ζ p) g := by
  rw [e₂, spec_mk, aeval_def, algebraMap_int_eq]

theorem eq_zero_of_e₁_e₂ [hp : Fact p.Prime] (x : U p) (h1 : e₁ p x = 0) (h2 : e₂ p x = 0) :
    x = 0 := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  have hζ : IsPrimitiveRoot (ζ p) p := ζ_isPrimitiveRoot p

  rw [e₁_mk, Int.cast_eq_zero] at h1
  obtain ⟨h, rfl⟩ : X - C (1 : ℤ) ∣ g := dvd_iff_isRoot.mpr h1

  rw [e₂_mk, map_mul, map_sub, aeval_X, aeval_C, algebraMap_int_eq, eq_intCast, Int.cast_one]
    at h2
  have hζ1 : ζ p - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hp.out.one_lt)
  have hh : aeval (ζ p) h = 0 := (mul_eq_zero.mp h2).resolve_left hζ1

  have hdvd : cyclotomic p ℤ ∣ h := by
    have hh' : aeval (ζ p) (h.map (Int.castRingHom ℚ)) = 0 := by
      rw [← algebraMap_int_eq, aeval_map_algebraMap ℚ]
      exact hh
    have hdvdQ : (cyclotomic p ℤ).map (Int.castRingHom ℚ) ∣ h.map (Int.castRingHom ℚ) := by
      rw [map_cyclotomic_int, cyclotomic_eq_minpoly_rat hζ hp.out.pos]
      exact minpoly.dvd ℚ _ hh'
    exact (map_dvd_map (Int.castRingHom ℚ) (RingHom.injective_int _)
      (cyclotomic.monic p ℤ)).mp hdvdQ

  refine AdjoinRoot.mk_eq_zero.mpr ?_
  rw [← cyclotomic_prime_mul_X_sub_one ℤ p, mul_comm (cyclotomic p ℤ), ← C_1]
  exact mul_dvd_mul_left _ hdvd

theorem hahnSeries_eq_zero [Fact p.Prime] {Γ : Type*} [PartialOrder Γ] (F : HahnSeries Γ (U p))
    (h1 : F.map (e₁ p) = 0) (h2 : F.map (e₂ p) = 0) : F = 0 := by
  ext n
  have h1n := congrArg (fun G => G.coeff n) h1
  have h2n := congrArg (fun G => G.coeff n) h2
  simp only [HahnSeries.map_coeff, HahnSeries.coeff_zero] at h1n h2n
  exact eq_zero_of_e₁_e₂ p (F.coeff n) h1n h2n

theorem hahnSeries_eq_of_map_eq [Fact p.Prime] {Γ : Type*} [PartialOrder Γ]
    (F G : HahnSeries Γ (U p))
    (h1 : F.map (e₁ p) = G.map (e₁ p)) (h2 : F.map (e₂ p) = G.map (e₂ p)) : F = G := by
  ext n
  have h1n := congrArg (fun H => H.coeff n) h1
  have h2n := congrArg (fun H => H.coeff n) h2
  simp only [HahnSeries.map_coeff] at h1n h2n
  rw [← sub_eq_zero]
  exact eq_zero_of_e₁_e₂ p _ (by rw [map_sub, h1n, sub_self]) (by rw [map_sub, h2n, sub_self])

theorem powerSeries_eq_zero [Fact p.Prime] (F : PowerSeries (U p))
    (h1 : PowerSeries.map (e₁ p) F = 0) (h2 : PowerSeries.map (e₂ p) F = 0) : F = 0 := by
  ext n
  have h1n := congrArg (PowerSeries.coeff n) h1
  have h2n := congrArg (PowerSeries.coeff n) h2
  simp only [PowerSeries.coeff_map, map_zero] at h1n h2n
  exact eq_zero_of_e₁_e₂ p _ h1n h2n

theorem powerSeries_eq_of_map_eq [Fact p.Prime] (F G : PowerSeries (U p))
    (h1 : PowerSeries.map (e₁ p) F = PowerSeries.map (e₁ p) G)
    (h2 : PowerSeries.map (e₂ p) F = PowerSeries.map (e₂ p) G) : F = G := by
  rw [← sub_eq_zero]
  exact powerSeries_eq_zero p (F - G) (by rw [map_sub, h1, sub_self])
    (by rw [map_sub, h2, sub_self])

end KTORDBeta
p2m_reactivate "P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDAlpha"

namespace KTORDFold

open ModularCurve MvPowerSeries Finsupp

abbrev σE : Fin 2 ↪ Fin 2 := (Equiv.swap (0 : Fin 2) 1).toEmbedding

theorem σE_comp_self : (⇑σE : Fin 2 → Fin 2) ∘ ⇑σE = id := by
  ext x; simp [σE]

theorem tateUnivX_swap (e : Fin 2 →₀ ℕ) :
    tateUnivX (e.mapDomain σE) = tateUnivX e := by
  have hinj : Function.Injective (⇑σE) := σE.injective
  have h0 : (e.mapDomain σE) 0 = e 1 := by
    have h01 : σE 1 = 0 := by simp [σE]
    rw [← h01, Finsupp.mapDomain_apply hinj]
  have h1 : (e.mapDomain σE) 1 = e 0 := by
    have h10 : σE 0 = 1 := by simp [σE]
    rw [← h10, Finsupp.mapDomain_apply hinj]
  unfold tateUnivX
  simp only [h0, h1]
  rcases lt_trichotomy (e 0) (e 1) with hlt | heq | hgt
  · rw [if_neg (Nat.ne_of_gt hlt), if_pos hlt, if_neg (Nat.ne_of_lt hlt),
      if_neg (not_lt.mpr hlt.le)]
    have hkey : (e 1 - e 0 ∣ e 0) = (e 1 - e 0 ∣ e 1) := by
      refine propext ⟨fun hd => ?_, fun hd => ?_⟩
      · have h' : e 1 - e 0 ∣ e 0 + (e 1 - e 0) := dvd_add hd (dvd_refl _)
        rwa [Nat.add_sub_cancel' hlt.le] at h'
      · have h' : e 1 - e 0 ∣ e 1 - (e 1 - e 0) := Nat.dvd_sub hd (dvd_refl _)
        rwa [Nat.sub_sub_self hlt.le] at h'
    simp only [hkey]
  · rw [if_pos heq.symm, if_pos heq, heq]
  · rw [if_neg (Nat.ne_of_lt hgt), if_neg (not_lt.mpr hgt.le),
      if_neg (Nat.ne_of_gt hgt), if_pos hgt]
    have hkey : (e 0 - e 1 ∣ e 0) = (e 0 - e 1 ∣ e 1) := by
      refine propext ⟨fun hd => ?_, fun hd => ?_⟩
      · have h' : e 0 - e 1 ∣ e 0 - (e 0 - e 1) := Nat.dvd_sub hd (dvd_refl _)
        rwa [Nat.sub_sub_self hgt.le] at h'
      · have h' : e 0 - e 1 ∣ e 1 + (e 0 - e 1) := dvd_add hd (dvd_refl _)
        rwa [Nat.add_sub_cancel' hgt.le] at h'
    simp only [hkey]

theorem rename_swap_tateUnivX : rename (⇑σE) tateUnivX = tateUnivX := by
  ext e
  have hsurj : e = Finsupp.embDomain σE (e.mapDomain σE) := by
    rw [Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp, σE_comp_self,
      Finsupp.mapDomain_id]
  conv_lhs => rw [hsurj]
  rw [coeff_embDomain_rename σE tateUnivX (e.mapDomain σE)]
  rw [MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply]
  exact tateUnivX_swap e

variable (K : Type*) [CommRing K]

theorem hasSubst_slotFamily (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    HasSubst (slotFamily K p c j) := by
  refine hasSubst_of_constantCoeff_zero ?_
  intro i; fin_cases i
  · show PowerSeries.constantCoeff (PowerSeries.C (c : K) * PowerSeries.X ^ j) = 0
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hj.ne', mul_zero]
  · show PowerSeries.constantCoeff
        (PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)) = 0
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X,
      zero_pow (Nat.sub_ne_zero_of_lt hjp), mul_zero]

theorem slotFamily_swap (p : ℕ) (c : Kˣ) (j : ℕ) (hjp : j < p) :
    slotFamily K p c⁻¹ (p - j) = slotFamily K p c j ∘ σE := by
  have hp : p - (p - j) = j := Nat.sub_sub_self hjp.le
  funext i
  fin_cases i
  · show slotFamily K p c⁻¹ (p - j) 0 = slotFamily K p c j (σE 0)
    simp only [σE, Equiv.coe_toEmbedding, Equiv.swap_apply_left]
    rfl
  · show slotFamily K p c⁻¹ (p - j) 1 = slotFamily K p c j (σE 1)
    simp only [σE, Equiv.coe_toEmbedding, Equiv.swap_apply_right, slotFamily,
      Matrix.cons_val_one, Matrix.cons_val_zero, inv_inv, hp]

theorem slotSubst_fold_tateUnivX (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    slotSubst K p c⁻¹ (p - j) tateUnivX = slotSubst K p c j tateUnivX := by
  have ha := hasSubst_slotFamily K p c j hj hjp
  have hXσ : HasSubst ((X : Fin 2 → MvPowerSeries (Fin 2) ℤ) ∘ σE) :=
    HasSubst.X_comp (R := ℤ) (f := ⇑σE)
  have hcomp := subst_comp_subst (R := ℤ) (a := (X : Fin 2 → MvPowerSeries (Fin 2) ℤ) ∘ σE)
    (b := slotFamily K p c j) hXσ ha
  have hstep : (fun s => subst (slotFamily K p c j)
        (((X : Fin 2 → MvPowerSeries (Fin 2) ℤ) ∘ σE) s))
      = slotFamily K p c j ∘ σE := by
    funext s; simp only [Function.comp_apply, subst_X ha]
  calc slotSubst K p c⁻¹ (p - j) tateUnivX
      = subst (slotFamily K p c⁻¹ (p - j)) tateUnivX := rfl
    _ = subst (slotFamily K p c j ∘ σE) tateUnivX := by rw [slotFamily_swap K p c j hjp]
    _ = subst (fun s => subst (slotFamily K p c j)
          (((X : Fin 2 → MvPowerSeries (Fin 2) ℤ) ∘ σE) s)) tateUnivX := by rw [hstep]
    _ = subst (slotFamily K p c j)
          (subst ((X : Fin 2 → MvPowerSeries (Fin 2) ℤ) ∘ σE) tateUnivX) := by
        exact (congrFun hcomp tateUnivX).symm
    _ = subst (slotFamily K p c j) (rename (⇑σE) tateUnivX) := by
        congr 1; rw [rename_eq_subst]
    _ = subst (slotFamily K p c j) tateUnivX := by rw [rename_swap_tateUnivX]
    _ = slotSubst K p c j tateUnivX := rfl

theorem nonToricPoint_fst_fold (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (nonToricPoint K p c⁻¹ (p - j)).1 = (nonToricPoint K p c j).1 := by
  rw [nonToricPoint_fst, nonToricPoint_fst, slotSubst_fold_tateUnivX K p c j hj hjp]

end KTORDFold
p2m_reactivate "P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDAlpha"

namespace KTORDLine

open ModularCurve KTORDBeta

theorem pow_eq_pow_of_mod_eq {M : Type*} [Monoid M] {p : ℕ} {u : M} (hu : u ^ p = 1)
    {m n : ℕ} (h : m % p = n % p) : u ^ m = u ^ n := by
  calc u ^ m = u ^ (p * (m / p) + m % p) := by rw [Nat.div_add_mod]
    _ = u ^ (m % p) := by rw [pow_add, pow_mul, hu, one_pow, one_mul]
    _ = u ^ (n % p) := by rw [h]
    _ = u ^ (p * (n / p) + n % p) := by rw [pow_add, pow_mul, hu, one_pow, one_mul]
    _ = u ^ n := by rw [Nat.div_add_mod]

theorem nsmul_eq_nsmul_mod {G : Type*} [AddCommGroup G] {p : ℕ} {P : G} (hP : p • P = 0)
    (n : ℕ) : n • P = (n % p) • P := by
  calc n • P = (p * (n / p) + n % p) • P := by rw [Nat.div_add_mod]
    _ = (n % p) • P := by rw [add_nsmul, mul_nsmul, hP, smul_zero, zero_add]

theorem exists_pow_mul_eq {M : Type*} [Monoid M] (p : ℕ) (hp : p.Prime) (c : M) (hc : c ^ p = 1)
    (j : ℕ) (hj : 0 < j) (hjp : j < p) : ∃ b : ℕ, c ^ (b * j) = c := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.coprime_of_lt_prime hj.ne' hjp hp).symm hp.one_lt
  refine ⟨m, ?_⟩
  have hdecomp : m * j = p * (m * j / p) + 1 := by
    have h := Nat.div_add_mod (m * j) p
    rw [Nat.mul_comm m j, hm] at h
    rw [Nat.mul_comm m j]
    exact h.symm
  rw [hdecomp, pow_add, pow_mul, hc, one_pow, one_mul, pow_one]

theorem pow_eq_one_of_geom_sum_eq_zero {R : Type*} [CommRing R] {p : ℕ} (z : R)
    (hz : ∑ i ∈ Finset.range p, z ^ i = 0) : z ^ p = 1 := by
  have h := geom_sum_mul z p
  rw [hz, zero_mul] at h
  exact sub_eq_zero.mp h.symm

section HasX

variable {F : Type*} [Field F] {W : WeierstrassCurve F}

def HasX (P : W.toAffine.Point) (x : F) : Prop :=
  ∃ (y : F) (h : W.toAffine.Nonsingular x y), P = .some x y h

theorem HasX.neg {P : W.toAffine.Point} {x : F} (hP : HasX P x) : HasX (-P) x := by
  obtain ⟨y, h, rfl⟩ := hP
  exact ⟨_, _, WeierstrassCurve.Affine.Point.neg_some h⟩

end HasX
p2m_reactivate "P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDAlpha"

section FieldCase

variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]

theorem family (hp5 : 5 ≤ p) (ζ : Kˣ) (hζ : ζ ^ p = 1) (b : ℕ)
    (n₁ n₂ a : ℕ) (h1 : 0 < n₁) (h1p : n₁ < p) (h2 : 0 < n₂) (h2p : n₂ < p)
    (hrel : (a * n₁) % p = n₂ ∨ (n₂ + a * n₁) % p = 0) :
    (nonToricPoint K p (ζ ^ (b * n₂)) n₂).1 *
        ((tateBase K p).ΨSq a).eval (nonToricPoint K p (ζ ^ (b * n₁)) n₁).1 =
      ((tateBase K p).Φ a).eval (nonToricPoint K p (ζ ^ (b * n₁)) n₁).1 := by
  classical
  have hp' : p.Prime := Fact.out
  have hodd : p % 2 = 1 := by
    rcases hp'.eq_two_or_odd with h | h
    · omega
    · exact h

  have hEq : ∀ n, 0 < n → n < p → (tateBase K p).toAffine.Equation
      (nonToricPoint K p (ζ ^ (b * n)) n).1 (nonToricPoint K p (ζ ^ (b * n)) n).2 :=
    fun n hn hnp => ModularCurve.equation_tateBase_nonToricPoint K p (ζ ^ (b * n)) n hn hnp
  have hNS : ∀ n, 0 < n → n < p → (tateBase K p).toAffine.Nonsingular
      (nonToricPoint K p (ζ ^ (b * n)) n).1 (nonToricPoint K p (ζ ^ (b * n)) n).2 :=
    fun n hn hnp => WeierstrassCurve.Affine.equation_iff_nonsingular.mp (hEq n hn hnp)
  have hNS' : ∀ m, 1 ≤ m → m ≤ p / 2 → (tateBase K p).toAffine.Nonsingular
      (nonToricPoint K p (ζ ^ (b * m)) m).1 (nonToricPoint K p (ζ ^ (b * m)) m).2 :=
    fun m hm hmH => hNS m hm (by omega)

  obtain ⟨hwalk, htors⟩ := KTORDTors.dev_core K p hp5 ζ hζ b hNS'
  set P₁ := KTORDTors.slotPt K p ζ b hNS' 1 with hP₁
  have hpP1 : p • P₁ = 0 := htors 1 le_rfl (by omega)

  have hX : ∀ n, 0 < n → n < p →
      HasX (n • P₁) (nonToricPoint K p (ζ ^ (b * n)) n).1 := by
    intro n hn hnp
    by_cases hnH : n ≤ p / 2
    · refine ⟨_, hNS n hn hnp, ?_⟩
      rw [hwalk n hn hnH, KTORDTors.slotPt_eq K p ζ b hNS' n hn hnH]
    · have hn' : 1 ≤ p - n := by omega
      have hn'H : p - n ≤ p / 2 := by omega
      have hneg : n • P₁ = -((p - n) • P₁) := by
        apply eq_neg_of_add_eq_zero_left
        rw [← add_nsmul, Nat.add_sub_of_le hnp.le, hpP1]
      have hX' : HasX ((p - n) • P₁) (nonToricPoint K p (ζ ^ (b * (p - n))) (p - n)).1 :=
        ⟨_, hNS' (p - n) hn' hn'H, by
          rw [hwalk (p - n) hn' hn'H, KTORDTors.slotPt_eq K p ζ b hNS' (p - n) hn' hn'H]⟩
      have hu : ζ ^ (b * (p - n)) = (ζ ^ (b * n))⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hnp.le, pow_mul', hζ, one_pow]
      have hxeq : (nonToricPoint K p (ζ ^ (b * (p - n))) (p - n)).1 =
          (nonToricPoint K p (ζ ^ (b * n)) n).1 := by
        rw [hu]
        exact KTORDFold.nonToricPoint_fst_fold K p (ζ ^ (b * n)) n hn hnp
      rw [hneg]
      exact (hxeq ▸ hX').neg

  obtain ⟨y₁, hy₁, hn₁⟩ := hX n₁ h1 h1p
  have hQ : (WeierstrassCurve.Affine.Point.some _ _ (hNS n₁ h1 h1p) :
        (tateBase K p).toAffine.Point) = n₁ • P₁ ∨
      (WeierstrassCurve.Affine.Point.some _ _ (hNS n₁ h1 h1p) :
        (tateBase K p).toAffine.Point) = -(n₁ • P₁) := by
    rw [hn₁]
    exact WeierstrassCurve.Affine.Point.X_eq_iff.mp rfl

  have hmul : HasX ((a * n₁) • P₁) (nonToricPoint K p (ζ ^ (b * n₂)) n₂).1 := by
    rcases hrel with hr | hr
    · rw [nsmul_eq_nsmul_mod hpP1 (a * n₁), hr]
      exact hX n₂ h2 h2p
    · have hsum : (n₂ + a * n₁) • P₁ = 0 := by
        rw [nsmul_eq_nsmul_mod hpP1 (n₂ + a * n₁), hr, zero_nsmul]
      have hna : (a * n₁) • P₁ = -(n₂ • P₁) := by
        apply eq_neg_of_add_eq_zero_left
        rw [← add_nsmul, Nat.add_comm]
        exact hsum
      rw [hna]
      exact (hX n₂ h2 h2p).neg

  have haQ : HasX (a • (WeierstrassCurve.Affine.Point.some _ _ (hNS n₁ h1 h1p) :
        (tateBase K p).toAffine.Point)) (nonToricPoint K p (ζ ^ (b * n₂)) n₂).1 := by
    rcases hQ with hq | hq
    · rw [hq, ← mul_nsmul']
      exact hmul
    · rw [hq, neg_nsmul, ← mul_nsmul']
      exact hmul.neg

  obtain ⟨y₂, hy₂, haP⟩ := haQ
  have hz := WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq (tateBase K p) (a : ℤ)
    (hNS n₁ h1 h1p) hy₂ (by rw [natCast_zsmul]; exact haP)
  rw [WeierstrassCurve.Affine.evalEval_psi_sq (tateBase K p) (hEq n₁ h1 h1p) (a : ℤ),
    WeierstrassCurve.Affine.evalEval_phi (tateBase K p) (hEq n₁ h1 h1p) (a : ℤ)] at hz
  exact hz

theorem field_card (hp5 : 5 ≤ p) (ξ : Kˣ) (hξ : ξ ^ p = 1)
    (n₀ k n₀' m t a : ℕ) (hk : 0 < k) (hkp : k < p) (ht : 0 < t) (htp : t < p)
    (hn₀' : n₀' % p = (t * n₀) % p) (hm : m = (t * k) % p)
    (ha : a = if t ≤ p / 2 then t else p - t) :
    (nonToricPoint K p (ξ ^ n₀') m).1 *
        ((tateBase K p).ΨSq a).eval (nonToricPoint K p (ξ ^ n₀) k).1 =
      ((tateBase K p).Φ a).eval (nonToricPoint K p (ξ ^ n₀) k).1 := by
  have hp' : p.Prime := Fact.out
  subst hm
  have hc : (ξ ^ n₀) ^ p = 1 := by rw [← pow_mul, pow_mul', hξ, one_pow]
  obtain ⟨b, hb⟩ := exists_pow_mul_eq p hp' (ξ ^ n₀) hc k hk hkp
  have hm0 : 0 < (t * k) % p := by
    apply Nat.pos_of_ne_zero
    intro h0
    rcases (Nat.Prime.dvd_mul hp').mp (Nat.dvd_of_mod_eq_zero h0) with h | h
    · exact Nat.not_dvd_of_pos_of_lt ht htp h
    · exact Nat.not_dvd_of_pos_of_lt hk hkp h
  have hmp : (t * k) % p < p := Nat.mod_lt _ hp'.pos
  have hrel : (a * k) % p = (t * k) % p ∨ ((t * k) % p + a * k) % p = 0 := by
    rw [ha]
    split_ifs with hle
    · exact Or.inl rfl
    · refine Or.inr (Nat.mod_eq_zero_of_dvd (Nat.modEq_zero_iff_dvd.mp ?_))
      have h2 : (t * k) % p + (p - t) * k ≡ t * k + (p - t) * k [MOD p] :=
        (Nat.mod_modEq (t * k) p).add_right _
      rw [← Nat.add_mul, Nat.add_sub_of_le htp.le] at h2
      exact h2.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right p k))
  have hu₂ : (ξ ^ n₀) ^ (b * ((t * k) % p)) = ξ ^ n₀' := by
    rw [pow_eq_pow_of_mod_eq hc ((Nat.mod_modEq (t * k) p).mul_left b),
      show b * (t * k) = (b * k) * t by ring, pow_mul, hb, ← pow_mul]
    exact pow_eq_pow_of_mod_eq hξ (by rw [hn₀', Nat.mul_comm])
  have key := family K p hp5 (ξ ^ n₀) hc b k ((t * k) % p) a hk hkp hm0 hmp hrel
  rw [hb, hu₂] at key
  exact key

end FieldCase
p2m_reactivate "P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDAlpha"

noncomputable def lineExpr (S : Type*) [CommRing S] (p : ℕ) [NeZero p] (u : Sˣ)
    (n₀ k n₀' m a : ℕ) : LaurentSeries S :=
  (nonToricPoint S p (u ^ n₀') m).1 * ((tateBase S p).ΨSq a).eval (nonToricPoint S p (u ^ n₀) k).1 -
    ((tateBase S p).Φ a).eval (nonToricPoint S p (u ^ n₀) k).1

theorem laurentMap_lineExpr {S S' : Type*} [CommRing S] [CommRing S'] (h : S →+* S') (p : ℕ)
    [NeZero p] (u : Sˣ) (n₀ k n₀' m a : ℕ) (hk : 0 < k) (hkp : k < p) (hm : 0 < m) (hmp : m < p) :
    KTORDAlpha.laurentMap h (lineExpr S p u n₀ k n₀' m a) =
      lineExpr S' p (Units.map (h : S →* S') u) n₀ k n₀' m a := by
  unfold lineExpr
  rw [map_sub, map_mul, ← map_pow, ← map_pow,
    ← KTORDAlpha.laurentMap_nonToricPoint_fst h p (u ^ n₀') m hm hmp,
    ← KTORDAlpha.laurentMap_nonToricPoint_fst h p (u ^ n₀) k hk hkp,
    ← KTORDAlpha.map_tateBase h p, WeierstrassCurve.map_ΨSq, WeierstrassCurve.map_Φ,
    Polynomial.eval_map, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    Polynomial.eval₂_at_apply]

theorem uTunit_pow (p : ℕ) [NeZero p] : uTunit p ^ p = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, val_uTunit, uT_pow, Units.val_one])

theorem units_map_spec_uTunit (p : ℕ) [NeZero p] (R : Type*) [CommRing R] (c : Rˣ)
    (hc : (c : R) ^ p = 1) :
    Units.map (spec p R (c : R) hc : U p →* R) (uTunit p) = c :=
  Units.ext (spec_val_uTunit p R (c : R) hc)

theorem units_map_uTunit_pow (p : ℕ) [NeZero p] {R : Type*} [CommRing R] (f : U p →+* R) :
    Units.map (f : U p →* R) (uTunit p) ^ p = 1 := by
  rw [← map_pow, uTunit_pow, map_one]

theorem ring_identity (R : Type*) [CommRing R] (p : ℕ) [hpr : Fact p.Prime] (hp5 : 5 ≤ p)
    (ζ : Rˣ) (hζ : ζ ^ p = 1)
    (n₀ k n₀' m t a : ℕ) (hk : 0 < k) (hkp : k < p) (ht : 0 < t) (htp : t < p)
    (hn₀' : n₀' % p = (t * n₀) % p) (hm : m = (t * k) % p)
    (ha : a = if t ≤ p / 2 then t else p - t) :
    (nonToricPoint R p (ζ ^ n₀') m).1 *
        ((tateBase R p).ΨSq a).eval (nonToricPoint R p (ζ ^ n₀) k).1 =
      ((tateBase R p).Φ a).eval (nonToricPoint R p (ζ ^ n₀) k).1 := by
  have hp' : p.Prime := Fact.out
  have hm0 : 0 < m := by
    rw [hm]
    apply Nat.pos_of_ne_zero
    intro h0
    rcases (Nat.Prime.dvd_mul hp').mp (Nat.dvd_of_mod_eq_zero h0) with h | h
    · exact Nat.not_dvd_of_pos_of_lt ht htp h
    · exact Nat.not_dvd_of_pos_of_lt hk hkp h
  have hmp : m < p := by rw [hm]; exact Nat.mod_lt _ hp'.pos
  suffices h0 : lineExpr R p ζ n₀ k n₀' m a = 0 by
    unfold lineExpr at h0
    exact sub_eq_zero.mp h0
  have hζR : (ζ : R) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  have hnat := laurentMap_lineExpr (spec p R (ζ : R) hζR) p (uTunit p) n₀ k n₀' m a hk hkp hm0 hmp
  rw [units_map_spec_uTunit] at hnat
  rw [← hnat]
  suffices hU : lineExpr (U p) p (uTunit p) n₀ k n₀' m a = 0 by rw [hU, map_zero]
  refine KTORDBeta.hahnSeries_eq_zero p _ ?_ ?_
  · change KTORDAlpha.laurentMap (e₁ p) _ = 0
    rw [laurentMap_lineExpr (e₁ p) p (uTunit p) n₀ k n₀' m a hk hkp hm0 hmp]
    unfold lineExpr
    exact sub_eq_zero.mpr (field_card ℚ p hp5 _ (units_map_uTunit_pow p (e₁ p))
      n₀ k n₀' m t a hk hkp ht htp hn₀' hm ha)
  · change KTORDAlpha.laurentMap (e₂ p) _ = 0
    rw [laurentMap_lineExpr (e₂ p) p (uTunit p) n₀ k n₀' m a hk hkp hm0 hmp]
    unfold lineExpr
    exact sub_eq_zero.mpr (field_card ℂ p hp5 _ (units_map_uTunit_pow p (e₂ p))
      n₀ k n₀' m t a hk hkp ht htp hn₀' hm ha)

end KTORDLine
p2m_reactivate "P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDAlpha"

namespace KTORDZeta

private theorem pow_mod {R : Type*} [CommRing R] {ζ : R} {p : ℕ} (hζp : ζ ^ p = 1) (a : ℕ) :
    ζ ^ a = ζ ^ (a % p) := by
  conv_lhs => rw [← Nat.div_add_mod a p, pow_add, pow_mul, hζp, one_pow, one_mul]

private theorem zeta_pow_p {R : Type*} [CommRing R] {p : ℕ} {ζ : R}
    (hζ : ∑ i ∈ Finset.range p, ζ ^ i = 0) : ζ ^ p = 1 := by
  have h := geom_sum_mul ζ p
  rw [hζ, zero_mul] at h
  exact sub_eq_zero.mp h.symm

private theorem geom_sum_pow_mul {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] {ζ : R}
    (hζ : ∑ i ∈ Finset.range p, ζ ^ i = 0) {m : ℕ} (hm : ¬ p ∣ m) :
    ∑ k ∈ Finset.range p, ζ ^ (m * k) = 0 := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hζp : ζ ^ p = 1 := zeta_pow_p hζ
  have hm0 : (m : ZMod p) ≠ 0 := fun h0 => hm ((CharP.cast_eq_zero_iff (ZMod p) p m).mp h0)
  have hinj : ∀ k₁ ∈ Finset.range p, ∀ k₂ ∈ Finset.range p,
      (m * k₁) % p = (m * k₂) % p → k₁ = k₂ := by
    intro k₁ hk₁ k₂ hk₂ h
    have hc : ((m * k₁ : ℕ) : ZMod p) = ((m * k₂ : ℕ) : ZMod p) := by
      rw [← ZMod.natCast_mod (m * k₁) p, ← ZMod.natCast_mod (m * k₂) p, h]
    push_cast at hc
    have hk := mul_left_cancel₀ hm0 hc
    have h1 : ((k₁ : ℕ) : ZMod p).val = ((k₂ : ℕ) : ZMod p).val := by rw [hk]
    rwa [ZMod.val_cast_of_lt (Finset.mem_range.mp hk₁),
      ZMod.val_cast_of_lt (Finset.mem_range.mp hk₂)] at h1
  have himg : (Finset.range p).image (fun k => (m * k) % p) = Finset.range p := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      rcases Finset.mem_image.mp hr with ⟨k, _, rfl⟩
      exact Finset.mem_range.mpr (Nat.mod_lt _ hp0)
    · rw [Finset.card_image_of_injOn (fun k₁ hk₁ k₂ hk₂ h =>
        hinj k₁ (Finset.mem_coe.mp hk₁) k₂ (Finset.mem_coe.mp hk₂) h)]
  calc ∑ k ∈ Finset.range p, ζ ^ (m * k)
      = ∑ k ∈ Finset.range p, ζ ^ ((m * k) % p) :=
        Finset.sum_congr rfl fun k _ => pow_mod hζp _
    _ = ∑ r ∈ (Finset.range p).image (fun k => (m * k) % p), ζ ^ r :=
        (Finset.sum_image hinj).symm
    _ = ∑ r ∈ Finset.range p, ζ ^ r := by rw [himg]
    _ = 0 := hζ

private theorem telescope {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (1 - x) * ∑ k ∈ Finset.range n, (k : R) * x ^ k =
      (∑ k ∈ Finset.range n, x ^ k) - 1 - ((n : R) - 1) * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun k => x ^ k)]
    push_cast
    linear_combination ih

theorem isUnit_one_sub_zeta_pow (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp : IsUnit (p : R)) (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0)
    (m : ℕ) (hm : ¬ p ∣ m) : IsUnit (1 - (ζ : R) ^ m) := by
  have hζp : (ζ : R) ^ p = 1 := zeta_pow_p hζ
  have hxp : ((ζ : R) ^ m) ^ p = 1 := by
    rw [← pow_mul, mul_comm m p, pow_mul, hζp, one_pow]
  have hG : ∑ k ∈ Finset.range p, ((ζ : R) ^ m) ^ k = 0 := by
    calc ∑ k ∈ Finset.range p, ((ζ : R) ^ m) ^ k
        = ∑ k ∈ Finset.range p, (ζ : R) ^ (m * k) :=
          Finset.sum_congr rfl fun k _ => by rw [← pow_mul]
      _ = 0 := geom_sum_pow_mul hζ hm
  have htel := telescope ((ζ : R) ^ m) p
  rw [hG, hxp] at htel
  have key : (1 - (ζ : R) ^ m) * ∑ k ∈ Finset.range p, (k : R) * ((ζ : R) ^ m) ^ k
      = -(p : R) := by rw [htel]; ring
  have hmain : (1 - (ζ : R) ^ m) *
      (-(↑hp.unit⁻¹ : R) * ∑ k ∈ Finset.range p, (k : R) * ((ζ : R) ^ m) ^ k) = 1 := by
    have h2 : (1 - (ζ : R) ^ m) *
        (-(↑hp.unit⁻¹ : R) * ∑ k ∈ Finset.range p, (k : R) * ((ζ : R) ^ m) ^ k)
        = (↑hp.unit⁻¹ : R) *
          -((1 - (ζ : R) ^ m) * ∑ k ∈ Finset.range p, (k : R) * ((ζ : R) ^ m) ^ k) := by
      ring
    rw [h2, key, neg_neg]
    exact hp.val_inv_mul
  exact ⟨⟨1 - (ζ : R) ^ m,
    -(↑hp.unit⁻¹ : R) * ∑ k ∈ Finset.range p, (k : R) * ((ζ : R) ^ m) ^ k,
    hmain, by rw [mul_comm]; exact hmain⟩, rfl⟩

end KTORDZeta
p2m_reactivate "P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDAlpha"

namespace KTORDDet

theorem smul_ne_and_smul_ne_neg {R : Type*} [CommRing R] (v w : Fin 2 → R)
    (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0) (a : R) : a • v ≠ w ∧ a • v ≠ -w := by
  refine ⟨fun h => hvw ?_, fun h => hvw ?_⟩
  · have h0 : a * v 0 = w 0 := by rw [← h, Pi.smul_apply, smul_eq_mul]
    have h1 : a * v 1 = w 1 := by rw [← h, Pi.smul_apply, smul_eq_mul]
    rw [← h0, ← h1]; ring
  · have h0 : a * v 0 = -w 0 := by rw [← Pi.neg_apply, ← h, Pi.smul_apply, smul_eq_mul]
    have h1 : a * v 1 = -w 1 := by rw [← Pi.neg_apply, ← h, Pi.smul_apply, smul_eq_mul]
    rw [show w 0 = -(a * v 0) by rw [h0, neg_neg], show w 1 = -(a * v 1) by rw [h1, neg_neg]]
    ring

theorem coord_ne_of_det_ne_zero {R : Type*} [CommRing R] (v w : Fin 2 → R)
    (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0) (a : R) :
    ¬ (a * v 0 = w 0 ∧ a * v 1 = w 1) ∧ ¬ (a * v 0 = -w 0 ∧ a * v 1 = -w 1) := by
  refine ⟨fun h => hvw ?_, fun h => hvw ?_⟩
  · rw [← h.1, ← h.2]; ring
  · rw [show w 0 = -(a * v 0) by rw [h.1, neg_neg], show w 1 = -(a * v 1) by rw [h.2, neg_neg]]
    ring

theorem fst_ne_of_snd_eq {R : Type*} [CommRing R] (v w : Fin 2 → R)
    (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0) (a : R) :
    ((a • v) 1 = w 1 → (a • v) 0 ≠ w 0) ∧ ((a • v) 1 = -w 1 → (a • v) 0 ≠ -w 0) := by
  obtain ⟨h1, h2⟩ := coord_ne_of_det_ne_zero v w hvw a
  simp only [Pi.smul_apply, smul_eq_mul]
  exact ⟨fun hs h0 => h1 ⟨h0, hs⟩, fun hs h0 => h2 ⟨h0, hs⟩⟩

end KTORDDet
p2m_reactivate "P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDAlpha"

namespace KTORDPsiUnit

open Polynomial

private theorem unit_left {S : Type*} [CommMonoid S] {a b : S} (h : IsUnit (a * b)) :
    IsUnit a := by
  obtain ⟨u, hu⟩ := h
  exact ⟨⟨a, b * (↑u⁻¹ : S), by rw [← mul_assoc, ← hu, Units.mul_inv],
    by rw [mul_comm, ← mul_assoc, ← hu, Units.mul_inv]⟩, rfl⟩

theorem psiSq_one_eval {S : Type*} [CommRing S] (W : WeierstrassCurve S) (x₁ : S) :
    (W.ΨSq ((1 : ℕ) : ℤ)).eval x₁ = 1 := by
  simp

private theorem key_step {S : Type*} [CommRing S] (W : WeierstrassCurve S)
    (x₁ xa : S) (n : ℕ)
    (hstep : (W.Φ (((n + 1 : ℕ)) : ℤ)).eval x₁ = xa * (W.ΨSq (((n + 1 : ℕ)) : ℤ)).eval x₁) :
    (W.ΨSq (((n + 2 : ℕ)) : ℤ)).eval x₁ * (W.ΨSq ((n : ℕ) : ℤ)).eval x₁
      = (x₁ - xa) ^ 2 * ((W.ΨSq (((n + 1 : ℕ)) : ℤ)).eval x₁) ^ 2 := by
  have hΦ := congrArg (Polynomial.eval x₁) (W.Φ_ofNat n)
  have hc : ((n : ℤ) + 1) = (((n + 1 : ℕ)) : ℤ) := by push_cast; ring
  rw [hc] at hΦ
  rw [hΦ] at hstep
  rw [WeierstrassCurve.ΨSq_ofNat] at hstep
  rw [WeierstrassCurve.ΨSq_ofNat, WeierstrassCurve.ΨSq_ofNat, WeierstrassCurve.ΨSq_ofNat]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one, apply_ite (Polynomial.eval x₁)] at hstep ⊢
  rcases Nat.even_or_odd n with hn | hn
  · have h1 : ¬ Even (n + 1) := by rw [Nat.even_iff] at hn ⊢; omega
    have h2 : Even (n + 2) := by rw [Nat.even_iff] at hn ⊢; omega
    simp only [if_pos hn, if_neg h1, if_pos h2] at hstep ⊢
    linear_combination (-((x₁ - xa) * (W.preΨ' (n + 1)).eval x₁ ^ 2 +
      (W.preΨ' (n + 2)).eval x₁ * (W.preΨ' n).eval x₁ * (W.Ψ₂Sq).eval x₁)) * hstep
  · have hn' : ¬ Even n := by rw [Nat.odd_iff] at hn; rw [Nat.even_iff]; omega
    have h1 : Even (n + 1) := by rw [Nat.odd_iff] at hn; rw [Nat.even_iff]; omega
    have h2 : ¬ Even (n + 2) := by rw [Nat.odd_iff] at hn; rw [Nat.even_iff]; omega
    simp only [if_neg hn', if_pos h1, if_neg h2] at hstep ⊢
    linear_combination (-((x₁ - xa) * (W.preΨ' (n + 1)).eval x₁ ^ 2 * (W.Ψ₂Sq).eval x₁ +
      (W.preΨ' (n + 2)).eval x₁ * (W.preΨ' n).eval x₁)) * hstep

theorem isUnit_psiSq_eval {S : Type*} [CommRing S] (W : WeierstrassCurve S)
    (x : ℕ → S) (B : ℕ)
    (h2 : IsUnit ((W.ΨSq ((2 : ℕ) : ℤ)).eval (x 1)))
    (hstep : ∀ a, 2 ≤ a → a < B →
      (W.Φ ((a : ℕ) : ℤ)).eval (x 1) = x a * (W.ΨSq ((a : ℕ) : ℤ)).eval (x 1))
    (hsub : ∀ a, 2 ≤ a → a < B → IsUnit (x 1 - x a)) :
    ∀ a, 1 ≤ a → a ≤ B → IsUnit ((W.ΨSq ((a : ℕ) : ℤ)).eval (x 1)) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha1 haB
    match a, ha1 with
    | 1, _ => rw [psiSq_one_eval]; exact isUnit_one
    | 2, _ => exact h2
    | (n + 3), _ =>
      have hs2 : 2 ≤ n + 2 := by omega
      have hsB : n + 2 < B := by omega
      have hkey := key_step W (x 1) (x (n + 2)) (n + 1) (by
        have h := hstep (n + 2) hs2 hsB
        rwa [show n + 1 + 1 = n + 2 from by omega])
      rw [show n + 1 + 2 = n + 3 from by omega,
        show n + 1 + 1 = n + 2 from by omega] at hkey
      have hU : IsUnit ((W.ΨSq (((n + 3 : ℕ)) : ℤ)).eval (x 1) *
          (W.ΨSq (((n + 1 : ℕ)) : ℤ)).eval (x 1)) := by
        rw [hkey]
        exact ((hsub (n + 2) hs2 hsB).pow 2).mul
          ((ih (n + 2) (by omega) (by omega) (by omega)).pow 2)
      exact unit_left hU

end KTORDPsiUnit
p2m_reactivate "P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDAlpha"

namespace KTORDCross

open ModularCurve

theorem isUnit_sub_cross_family (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (ζ : Rˣ) (hζp : ζ ^ p = 1)
    (half : ∀ (c d : Rˣ) (k l : ℕ), 1 ≤ k → k ≤ p / 2 → 1 ≤ l → l ≤ p / 2 →
      (k ≠ l ∨ ∃ m, ¬ p ∣ m ∧ (c : R) = (ζ : R) ^ m * (d : R)) →
      IsUnit ((nonToricPoint R p c k).1 - (nonToricPoint R p d l).1))
    (fold : ∀ (c : Rˣ) (j : ℕ), 0 < j → j < p →
      (nonToricPoint R p c⁻¹ (p - j)).1 = (nonToricPoint R p c j).1)
    (w : Fin 2 → ZMod p) (hw : w 1 ≠ 0)
    (n₀' k' : ℕ) (hk' : 0 < k') (hkp' : k' < p)
    (hne : ¬ ((n₀' : ZMod p) = w 0 ∧ (k' : ZMod p) = w 1) ∧
           ¬ ((n₀' : ZMod p) = -w 0 ∧ (k' : ZMod p) = -w 1)) :
    IsUnit ((nonToricPoint R p (ζ ^ (w 0).val) (w 1).val).1 -
            (nonToricPoint R p (ζ ^ n₀') k').1) := by
  have hpr : p.Prime := Fact.out
  have hodd : p % 2 = 1 := by
    rcases hpr.eq_two_or_odd with h | h
    · omega
    · exact h
  have hk : 0 < (w 1).val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero (w 1)).mpr hw)
  have hkp : (w 1).val < p := ZMod.val_lt (w 1)
  have hζR : (ζ : R) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hζp, Units.val_one]

  have hpe : ∀ e : ℕ, (p - 1) * e + e = p * e := fun e => by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left e hpr.pos)]
  have hinv : ∀ e : ℕ, (ζ ^ e)⁻¹ = ζ ^ ((p - 1) * e) := fun e =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_add, Nat.add_comm, hpe, pow_mul, hζp, one_pow])
  have hval0 : (((w 0).val : ℕ) : ZMod p) = w 0 := ZMod.natCast_zmod_val (w 0)
  have hval1 : (((w 1).val : ℕ) : ZMod p) = w 1 := ZMod.natCast_zmod_val (w 1)
  have hp1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hpr.one_le, Nat.cast_one, ZMod.natCast_self, zero_sub]
  have hneg : ∀ e : ℕ, (((p - 1) * e : ℕ) : ZMod p) = -(e : ZMod p) := fun e => by
    rw [Nat.cast_mul, hp1, neg_one_mul]
  have hsubcast : ∀ j : ℕ, j ≤ p → ((p - j : ℕ) : ZMod p) = -(j : ZMod p) := fun j hj => by
    rw [Nat.cast_sub hj, ZMod.natCast_self, zero_sub]

  have hem : ∀ e₁ e₂ : ℕ, (e₁ : ZMod p) ≠ (e₂ : ZMod p) →
      ∃ m, ¬ p ∣ m ∧ ((ζ ^ e₁ : Rˣ) : R) = (ζ : R) ^ m * ((ζ ^ e₂ : Rˣ) : R) := by
    intro e₁ e₂ hne12
    refine ⟨e₁ + (p - 1) * e₂, ?_, ?_⟩
    · intro hdvd
      apply hne12
      have h0 : ((e₁ + (p - 1) * e₂ : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      rw [Nat.cast_add, hneg, ← sub_eq_add_neg, sub_eq_zero] at h0
      exact h0
    · rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← pow_add, Nat.add_assoc, hpe,
        pow_add, pow_mul, hζR, one_pow, mul_one]
  by_cases hkH : (w 1).val ≤ p / 2 <;> by_cases hk'H : k' ≤ p / 2
  ·
    refine half _ _ _ _ hk hkH hk' hk'H ?_
    rcases eq_or_ne (w 1).val k' with heq | hneq
    · refine Or.inr (hem _ _ ?_)
      rw [hval0]
      intro h
      exact hne.1 ⟨h.symm, by rw [← heq, hval1]⟩
    · exact Or.inl hneq
  ·
    rw [← fold (ζ ^ n₀') k' hk' hkp', hinv n₀']
    refine half _ _ _ _ hk hkH (by omega) (by omega) ?_
    rcases eq_or_ne (w 1).val (p - k') with heq | hneq
    · refine Or.inr (hem _ _ ?_)
      rw [hval0, hneg]
      intro h
      refine hne.2 ⟨by rw [h, neg_neg], ?_⟩
      rw [show k' = p - (w 1).val by omega, hsubcast _ hkp.le, hval1]
    · exact Or.inl hneq
  ·
    rw [← fold (ζ ^ (w 0).val) (w 1).val hk hkp, hinv (w 0).val]
    refine half _ _ _ _ (by omega) (by omega) hk' hk'H ?_
    rcases eq_or_ne (p - (w 1).val) k' with heq | hneq
    · refine Or.inr (hem _ _ ?_)
      rw [hneg, hval0]
      intro h
      refine hne.2 ⟨by rw [← h], ?_⟩
      rw [← heq, hsubcast _ hkp.le, hval1]
    · exact Or.inl hneq
  ·
    rw [← fold (ζ ^ (w 0).val) (w 1).val hk hkp, hinv (w 0).val,
      ← fold (ζ ^ n₀') k' hk' hkp', hinv n₀']
    refine half _ _ _ _ (by omega) (by omega) (by omega) (by omega) ?_
    rcases eq_or_ne (p - (w 1).val) (p - k') with heq | hneq
    · refine Or.inr (hem _ _ ?_)
      rw [hneg, hneg, hval0]
      intro h
      refine hne.1 ⟨(neg_inj.mp h).symm, ?_⟩
      rw [show k' = (w 1).val by omega, hval1]
    · exact Or.inl hneq

theorem hne_of_two_le (p : ℕ) [Fact p.Prime] (v : Fin 2 → ZMod p) (hv : v 1 ≠ 0)
    (a : ℕ) (h2a : 2 ≤ a) (hap : a ≤ (p - 1) / 2) :
    ¬ ((((a * (v 0).val) % p : ℕ) : ZMod p) = v 0 ∧
        (((a * (v 1).val) % p : ℕ) : ZMod p) = v 1) ∧
    ¬ ((((a * (v 0).val) % p : ℕ) : ZMod p) = -v 0 ∧
        (((a * (v 1).val) % p : ℕ) : ZMod p) = -v 1) := by
  have hpr : p.Prime := Fact.out
  have hcast : (((a * (v 1).val) % p : ℕ) : ZMod p) = (a : ZMod p) * v 1 := by
    rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_zmod_val]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : ((a : ZMod p) - 1) * v 1 = 0 := by rw [sub_mul, one_mul, ← hcast, h.2, sub_self]
    have h2 : (a : ZMod p) - 1 = 0 := (mul_eq_zero.mp h1).resolve_right hv
    have h3 : ((a - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]; exact h2
    have h4 : p ∣ a - 1 := (ZMod.natCast_eq_zero_iff _ _).mp h3
    have := Nat.le_of_dvd (by omega) h4
    omega
  · have h1 : ((a : ZMod p) + 1) * v 1 = 0 := by rw [add_mul, one_mul, ← hcast, h.2, neg_add_cancel]
    have h2 : (a : ZMod p) + 1 = 0 := (mul_eq_zero.mp h1).resolve_right hv
    have h3 : ((a + 1 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_add, Nat.cast_one]; exact h2
    have h4 : p ∣ a + 1 := (ZMod.natCast_eq_zero_iff _ _).mp h3
    have := Nat.le_of_dvd (by omega) h4
    omega

end KTORDCross
p2m_reactivate "P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDAlpha"

namespace KTORDPsi2

open ModularCurve

private theorem tateBase_a₁' {R : Type*} [CommRing R] (p : ℕ) [NeZero p] :
    (tateBase R p).a₁ = 1 := by simp [tateBase, tateLaurent, tatePowerSeries]

private theorem tateBase_a₃' {R : Type*} [CommRing R] (p : ℕ) [NeZero p] :
    (tateBase R p).a₃ = 0 := by simp [tateBase, tateLaurent, tatePowerSeries]

private theorem sq_tangentDenom {S : Type*} [CommRing S] (W : WeierstrassCurve S)
    (x y : S) (h : W.toAffine.Equation x y) :
    (2 * y + W.a₁ * x + W.a₃) ^ 2 = W.Ψ₂Sq.eval x := by
  rw [WeierstrassCurve.Affine.equation_iff'] at h
  have h' : y ^ 2 + W.a₁ * x * y + W.a₃ * y
      - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := h
  unfold WeierstrassCurve.Ψ₂Sq WeierstrassCurve.b₂ WeierstrassCurve.b₄ WeierstrassCurve.b₆
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  linear_combination 4 * h'

private theorem half_core {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
    (hofp : ∀ (f : PowerSeries R) (N : ℕ), (∀ n < N, PowerSeries.coeff n f = 0) →
      IsUnit (PowerSeries.coeff N f) → IsUnit (HahnSeries.ofPowerSeries ℤ R f))
    (hcoeff : ∀ (d : Rˣ) (k : ℕ), 1 ≤ k → k ≤ p / 2 →
      (∀ n < k, PowerSeries.coeff n
        (2 * slotSubst R p d k tateUnivY + slotSubst R p d k tateUnivX) = 0) ∧
      PowerSeries.coeff k
        (2 * slotSubst R p d k tateUnivY + slotSubst R p d k tateUnivX) = (d : R))
    (hEq : ∀ (d : Rˣ) (k : ℕ), 0 < k → k < p →
      (tateBase R p).toAffine.Equation (nonToricPoint R p d k).1 (nonToricPoint R p d k).2)
    (d : Rˣ) (k : ℕ) (h1k : 1 ≤ k) (hkp : k ≤ p / 2) :
    IsUnit ((tateBase R p).Ψ₂Sq.eval (nonToricPoint R p d k).1) := by
  have hp' : p.Prime := Fact.out
  have hkp' : k < p := lt_of_le_of_lt hkp (Nat.div_lt_self hp'.pos one_lt_two)
  have hu : IsUnit (2 * (nonToricPoint R p d k).2
      + (tateBase R p).a₁ * (nonToricPoint R p d k).1 + (tateBase R p).a₃) := by
    rw [tateBase_a₁', tateBase_a₃', one_mul, add_zero, nonToricPoint_fst, nonToricPoint_snd,
      ← map_ofNat (HahnSeries.ofPowerSeries ℤ R) 2, ← map_mul, ← map_add]
    refine hofp _ k (hcoeff d k h1k hkp).1 ?_
    rw [(hcoeff d k h1k hkp).2]
    exact Units.isUnit _
  rw [← sq_tangentDenom (tateBase R p) _ _ (hEq d k h1k hkp')]
  exact hu.pow 2

theorem isUnit_psi2Sq_eval {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (c : Rˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (hofp : ∀ (f : PowerSeries R) (N : ℕ), (∀ n < N, PowerSeries.coeff n f = 0) →
      IsUnit (PowerSeries.coeff N f) → IsUnit (HahnSeries.ofPowerSeries ℤ R f))
    (hcoeff : ∀ (d : Rˣ) (k : ℕ), 1 ≤ k → k ≤ p / 2 →
      (∀ n < k, PowerSeries.coeff n
        (2 * slotSubst R p d k tateUnivY + slotSubst R p d k tateUnivX) = 0) ∧
      PowerSeries.coeff k
        (2 * slotSubst R p d k tateUnivY + slotSubst R p d k tateUnivX) = (d : R))
    (hfold : ∀ (d : Rˣ) (m : ℕ), 0 < m → m < p →
      (nonToricPoint R p d⁻¹ (p - m)).1 = (nonToricPoint R p d m).1)
    (hEq : ∀ (d : Rˣ) (k : ℕ), 0 < k → k < p →
      (tateBase R p).toAffine.Equation (nonToricPoint R p d k).1 (nonToricPoint R p d k).2) :
    IsUnit ((tateBase R p).Ψ₂Sq.eval (nonToricPoint R p c j).1) := by
  have hp' : p.Prime := Fact.out
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp'.odd_of_ne_two (by omega))
  by_cases hle : j ≤ p / 2
  · exact half_core p hofp hcoeff hEq c j hj hle
  · have h1 : 1 ≤ p - j := by omega
    have h2 : p - j ≤ p / 2 := by omega
    rw [← hfold c j hj hjp]
    exact half_core p hofp hcoeff hEq c⁻¹ (p - j) h1 h2

end KTORDPsi2
p2m_reactivate "P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDAlpha"

namespace KTORDUnit

open ModularCurve

variable (K : Type*) [CommRing K] (p : ℕ) [Fact p.Prime]

scoped instance instNeZeroPrime : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem isUnit_ofPowerSeries_of_coeff {R : Type*} [CommRing R] (f : PowerSeries R) (N : ℕ)
    (hlow : ∀ n < N, PowerSeries.coeff n f = 0) (hN : IsUnit (PowerSeries.coeff N f)) :
    IsUnit ((HahnSeries.ofPowerSeries ℤ R) f) := by

  set g : PowerSeries R := PowerSeries.mk fun n => PowerSeries.coeff (n + N) f with hg
  have hg0 : PowerSeries.coeff 0 g = PowerSeries.coeff N f := by
    simp only [hg, PowerSeries.coeff_mk, zero_add]
  have hgU : IsUnit g := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0] using hN
  have hfac : f = PowerSeries.X ^ N * g := by
    ext n
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with h
    · simp only [hg, PowerSeries.coeff_mk, Nat.sub_add_cancel h]
    · exact hlow n (Nat.lt_of_not_le h)
  rw [hfac, map_mul, map_pow]
  refine IsUnit.mul (IsUnit.pow N ?_) (hgU.map _)
  rw [HahnSeries.ofPowerSeries_X]
  exact ⟨⟨HahnSeries.single (1 : ℤ) (1 : R), HahnSeries.single (-1 : ℤ) (1 : R),
    by rw [HahnSeries.single_mul_single]; simp,
    by rw [HahnSeries.single_mul_single]; simp⟩, rfl⟩

variable (hp5 : 5 ≤ p)

include hp5 in

theorem slotSubstX_coeff_low (c : Kˣ) (j : ℕ) (h1j : 1 ≤ j) (hjp : j ≤ p / 2) :
    (∀ n < j, PowerSeries.coeff n (slotSubst K p c j tateUnivX) = 0) ∧
    PowerSeries.coeff j (slotSubst K p c j tateUnivX) = (c : K) := by
  have hjp' : j < p := lt_of_le_of_lt hjp
    (Nat.div_lt_self ((Fact.out : p.Prime).pos) one_lt_two)
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h2j : 2 * j < p := by rcases hodd with ⟨w, hw⟩; omega

  have tails (n : ℕ) (hn : n ≤ j) :
      (∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
        (e : K) * (((if n = p * M + j * e then (c : K) ^ e else 0)
          + if n + j * e = p * M then (↑c⁻¹ : K) ^ e else 0)
          - if n = p * M then 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun M hM => Finset.sum_eq_zero fun e he => ?_
    rcases Nat.eq_zero_or_pos M with rfl | hM1
    · simp at he
    have heM : e ≤ M := Nat.le_of_dvd hM1 (Nat.mem_divisors.mp he).1
    have hMn : M ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hM)
    have h1 : ¬ n = p * M + j * e := by nlinarith [hM1, hjp']
    have h3 : ¬ n = p * M := by nlinarith [hM1, hjp']
    have h2 : ¬ n + j * e = p * M := by
      intro heq
      have : n ≥ (p - j) * M := by nlinarith [heM]
      have : p - j ≤ n := le_trans (Nat.le_mul_of_pos_right _ hM1) this
      omega
    simp [h1, h2, h3]
  constructor
  · intro n hn
    rw [coeff_slotSubst_tateUnivX p c j h1j hjp' n, tails n hn.le, add_zero]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · exact if_neg fun hd => absurd (Nat.le_of_dvd hn0 hd) (not_le.mpr hn)
  · rw [coeff_slotSubst_tateUnivX p c j h1j hjp' j, tails j le_rfl, add_zero,
      if_pos (dvd_refl j), Nat.div_self h1j, Nat.cast_one, one_mul, pow_one]

include hp5 in

theorem slotSubst_tangentDenom_coeff_low (c : Kˣ) (j : ℕ) (h1j : 1 ≤ j) (hjp : j ≤ p / 2) :
    (∀ n < j, PowerSeries.coeff n
      (2 * slotSubst K p c j tateUnivY + slotSubst K p c j tateUnivX) = 0) ∧
    PowerSeries.coeff j
      (2 * slotSubst K p c j tateUnivY + slotSubst K p c j tateUnivX) = (c : K) := by
  have hjp' : j < p := lt_of_le_of_lt hjp
    (Nat.div_lt_self ((Fact.out : p.Prime).pos) one_lt_two)
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h2j : 2 * j < p := by rcases hodd with ⟨w, hw⟩; omega

  have tailsY (n : ℕ) (hn : n ≤ j) :
      (∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
        (((if n = p * M + j * e then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0)
          - if n + j * e = p * M then (((e + 1).choose 2 : ℕ) : K) * (↑c⁻¹ : K) ^ e else 0)
          + if n = p * M then ((e : ℕ) : K) else 0)) = 0 := by
    refine Finset.sum_eq_zero fun M hM => Finset.sum_eq_zero fun e he => ?_
    rcases Nat.eq_zero_or_pos M with rfl | hM1
    · simp at he
    have heM : e ≤ M := Nat.le_of_dvd hM1 (Nat.mem_divisors.mp he).1
    have hMn : M ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hM)
    have h1 : ¬ n = p * M + j * e := by nlinarith [hM1, hjp']
    have h3 : ¬ n = p * M := by nlinarith [hM1, hjp']
    have h2 : ¬ n + j * e = p * M := by
      intro heq; have : n ≥ (p - j) * M := by nlinarith [heM]
      have : p - j ≤ n := le_trans (Nat.le_mul_of_pos_right _ hM1) this; omega
    simp [h1, h2, h3]

  have hYlow (n : ℕ) (hn : n ≤ j) :
      PowerSeries.coeff n (slotSubst K p c j tateUnivY) = 0 := by
    rw [coeff_slotSubst_tateUnivY p c j h1j hjp' n, tailsY n hn, add_zero]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    rcases eq_or_lt_of_le hn with rfl | hlt
    · simp [Nat.div_self h1j]
    · exact if_neg fun hd => absurd (Nat.le_of_dvd hn0 hd) (not_le.mpr hlt)
  have hX := slotSubstX_coeff_low K p hp5 c j h1j hjp
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [two_mul, map_add, map_add, hYlow n hn.le, hX.1 n hn, add_zero, add_zero]
  · rw [two_mul, map_add, map_add, hYlow j le_rfl, hX.2, add_zero, zero_add]

variable (hp : IsUnit (p : K)) (ζ : Kˣ) (hζs : ∑ i ∈ Finset.range p, (ζ : K) ^ i = 0)

include hp5 hp hζs in

theorem isUnit_sub_nonToricPoint_fst_half (c d : Kˣ)
    (k l : ℕ) (h1k : 1 ≤ k) (hkp : k ≤ p / 2) (h1l : 1 ≤ l) (hlp : l ≤ p / 2)
    (hne : k ≠ l ∨
           ∃ m, ¬ p ∣ m ∧ (c : K) = (ζ : K) ^ m * (d : K)) :
    IsUnit ((nonToricPoint K p c k).1 - (nonToricPoint K p d l).1) := by
  rcases lt_trichotomy k l with hlt | heq | hgt
  · rw [nonToricPoint_fst, nonToricPoint_fst, ← map_sub]
    refine isUnit_ofPowerSeries_of_coeff _ k ?_ ?_
    · intro n hn
      have h0 := (slotSubstX_coeff_low K p hp5 c k h1k hkp).1 n hn
      have h1 := (slotSubstX_coeff_low K p hp5 d l h1l hlp).1 n (hn.trans hlt)
      simp [map_sub, h0, h1]
    · have h0 := (slotSubstX_coeff_low K p hp5 c k h1k hkp).2
      have h1 := (slotSubstX_coeff_low K p hp5 d l h1l hlp).1 k hlt
      simp only [map_sub, h0, h1, sub_zero]
      exact Units.isUnit _
  · subst heq
    obtain ⟨m, hm, hcoe⟩ := hne.resolve_left (absurd rfl)
    rw [nonToricPoint_fst, nonToricPoint_fst, ← map_sub]
    refine isUnit_ofPowerSeries_of_coeff _ k ?_ ?_
    · intro n hn
      have h0 := (slotSubstX_coeff_low K p hp5 c k h1k hkp).1 n hn
      have h1 := (slotSubstX_coeff_low K p hp5 d k h1k hkp).1 n hn
      simp [map_sub, h0, h1]
    · have h0 := (slotSubstX_coeff_low K p hp5 c k h1k hkp).2
      have h1 := (slotSubstX_coeff_low K p hp5 d k h1k hkp).2
      simp only [map_sub, h0, h1]
      rw [hcoe, show ((ζ : K) ^ m * (d : K) - (d : K)) = ((ζ : K) ^ m - 1) * (d : K) by ring,
        show (ζ : K) ^ m - 1 = -(1 - (ζ : K) ^ m) by ring]
      exact ((KTORDZeta.isUnit_one_sub_zeta_pow K p hp ζ hζs m hm).neg).mul (Units.isUnit d)
  · rw [show (nonToricPoint K p c k).1 - (nonToricPoint K p d l).1
      = -((nonToricPoint K p d l).1 - (nonToricPoint K p c k).1) from (neg_sub _ _).symm,
      nonToricPoint_fst, nonToricPoint_fst, ← map_sub]
    refine (isUnit_ofPowerSeries_of_coeff _ l ?_ ?_).neg
    · intro n hn
      have h0 := (slotSubstX_coeff_low K p hp5 d l h1l hlp).1 n hn
      have h1 := (slotSubstX_coeff_low K p hp5 c k h1k hkp).1 n (hn.trans hgt)
      simp [map_sub, h0, h1]
    · have h0 := (slotSubstX_coeff_low K p hp5 d l h1l hlp).2
      have h1 := (slotSubstX_coeff_low K p hp5 c k h1k hkp).1 l hgt
      simp only [map_sub, h0, h1, sub_zero]
      exact Units.isUnit _

end KTORDUnit
p2m_reactivate "P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDAlpha P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDUnit"

namespace KTORDIndep2

open ModularCurve

theorem isUnit_psiSq_at_slot (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hp : IsUnit (p : R)) (ζ : Rˣ) (hζs : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0)
    (v : Fin 2 → ZMod p) (hv : v 1 ≠ 0) (a : ℕ) (ha : 1 ≤ a) (hap : a ≤ (p - 1) / 2) :
    IsUnit (((tateBase R p).ΨSq (a : ℤ)).eval
      (nonToricPoint R p (ζ ^ (v 0).val) (v 1).val).1) := by
  have hpr : p.Prime := Fact.out
  have hζp : ζ ^ p = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact KTORDLine.pow_eq_one_of_geom_sum_eq_zero (ζ : R) hζs)
  have hvk : 0 < (v 1).val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero (v 1)).mpr hv)
  have hvkp : (v 1).val < p := ZMod.val_lt (v 1)
  have hm1 : ∀ i, (1 * (v i).val) % p = (v i).val := fun i => by
    rw [one_mul, Nat.mod_eq_of_lt (ZMod.val_lt (v i))]

  rw [show (nonToricPoint R p (ζ ^ (v 0).val) (v 1).val).1 =
      (nonToricPoint R p (ζ ^ ((1 * (v 0).val) % p)) ((1 * (v 1).val) % p)).1 from by
    rw [hm1 0, hm1 1]]
  refine KTORDPsiUnit.isUnit_psiSq_eval (tateBase R p)
    (fun a' => (nonToricPoint R p (ζ ^ ((a' * (v 0).val) % p)) ((a' * (v 1).val) % p)).1)
    ((p - 1) / 2) ?_ ?_ ?_ a ha hap
  ·
    try dsimp only
    rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) from rfl, WeierstrassCurve.ΨSq_two, hm1 0, hm1 1]
    exact KTORDPsi2.isUnit_psi2Sq_eval p hp5 (ζ ^ (v 0).val) (v 1).val hvk hvkp
      KTORDUnit.isUnit_ofPowerSeries_of_coeff
      (KTORDUnit.slotSubst_tangentDenom_coeff_low R p hp5)
      (KTORDFold.nonToricPoint_fst_fold R p)
      (fun d k hk hkp => equation_tateBase_nonToricPoint R p d k hk hkp)
  ·
    intro a' ha'2 ha'B
    have ha'p : a' < p := by omega
    try dsimp only
    rw [hm1 0, hm1 1]
    exact (KTORDLine.ring_identity R p hp5 ζ hζp (v 0).val (v 1).val
      ((a' * (v 0).val) % p) ((a' * (v 1).val) % p) a' a'
      hvk hvkp (by omega) ha'p (Nat.mod_mod _ _) rfl
      (if_pos (show a' ≤ p / 2 by omega)).symm).symm
  ·
    intro a' ha'2 ha'B
    try dsimp only
    rw [hm1 0, hm1 1]
    have ha'p : a' < p := by omega
    have hm0 : 0 < (a' * (v 1).val) % p := by
      apply Nat.pos_of_ne_zero; intro h0
      rcases (hpr.dvd_mul).mp (Nat.dvd_of_mod_eq_zero h0) with h | h
      · exact Nat.not_dvd_of_pos_of_lt (by omega) ha'p h
      · exact Nat.not_dvd_of_pos_of_lt hvk hvkp h
    exact KTORDCross.isUnit_sub_cross_family R p hp5 ζ hζp
      (KTORDUnit.isUnit_sub_nonToricPoint_fst_half R p hp5 hp ζ hζs)
      (KTORDFold.nonToricPoint_fst_fold R p) v hv
      ((a' * (v 0).val) % p) ((a' * (v 1).val) % p)
      hm0 (Nat.mod_lt _ hpr.pos)
      (KTORDCross.hne_of_two_le p v hv a' ha'2 (by omega))

private theorem _root_.KTORDIndep2.isUnit_sub_cross_family (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hp : IsUnit (p : R)) (ζ : Rˣ) (hζs : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0)
    (w : Fin 2 → ZMod p) (hw : w 1 ≠ 0)
    (n₀' k' : ℕ) (hk' : 0 < k') (hkp' : k' < p)
    (hne : ¬ ((n₀' : ZMod p) = w 0 ∧ (k' : ZMod p) = w 1) ∧
           ¬ ((n₀' : ZMod p) = -w 0 ∧ (k' : ZMod p) = -w 1)) :
    IsUnit ((nonToricPoint R p (ζ ^ (w 0).val) (w 1).val).1 -
            (nonToricPoint R p (ζ ^ n₀') k').1) := by
  have hζp : ζ ^ p = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact KTORDLine.pow_eq_one_of_geom_sum_eq_zero (ζ : R) hζs)
  exact KTORDCross.isUnit_sub_cross_family R p hp5 ζ hζp
    (KTORDUnit.isUnit_sub_nonToricPoint_fst_half R p hp5 hp ζ hζs)
    (KTORDFold.nonToricPoint_fst_fold R p) w hw n₀' k' hk' hkp' hne

p2m_export "KTORDIndep2" "isUnit_sub_cross_family"

theorem isUnit_indepElt_slot_slot (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hp : IsUnit (p : R)) (ζ : Rˣ) (hζs : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0)
    (v : Fin 2 → ZMod p) (hv : v 1 ≠ 0) (w : Fin 2 → ZMod p)
    (hw : w 1 ≠ 0) (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    IsUnit (indepElt (tateBase R p) p
      (nonToricPoint R p (ζ ^ (v 0).val) (v 1).val).1
      (nonToricPoint R p (ζ ^ (w 0).val) (w 1).val).1) := by
  have hζp : ζ ^ p = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact KTORDLine.pow_eq_one_of_geom_sum_eq_zero (ζ : R) hζs)
  have hvk : 0 < (v 1).val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero (v 1)).mpr hv)
  have hvkp : (v 1).val < p := ZMod.val_lt (v 1)
  unfold indepElt
  refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one ?_
  intro a ha
  rw [Finset.mem_Icc] at ha
  obtain ⟨ha1, haH⟩ := ha
  have hap : a < p := lt_of_le_of_lt haH (by
    have := (Fact.out : p.Prime).pos; omega)
  have hri := KTORDLine.ring_identity R p hp5 ζ hζp
    (v 0).val (v 1).val ((a * (v 0).val) % p) ((a * (v 1).val) % p) a a
    hvk hvkp ha1 hap (Nat.mod_mod _ _) rfl (by
      have : a ≤ p / 2 := by omega
      exact (if_pos this).symm)
  rw [show (nonToricPoint R p (ζ ^ (w 0).val) (w 1).val).1 *
          ((tateBase R p).ΨSq (a : ℤ)).eval (nonToricPoint R p (ζ ^ (v 0).val) (v 1).val).1 -
        ((tateBase R p).Φ (a : ℤ)).eval (nonToricPoint R p (ζ ^ (v 0).val) (v 1).val).1 =
      ((nonToricPoint R p (ζ ^ (w 0).val) (w 1).val).1 -
        (nonToricPoint R p (ζ ^ ((a * (v 0).val) % p)) ((a * (v 1).val) % p)).1) *
      ((tateBase R p).ΨSq (a : ℤ)).eval (nonToricPoint R p (ζ ^ (v 0).val) (v 1).val).1 from by
    rw [sub_mul, hri]]
  refine IsUnit.mul ?_ (isUnit_psiSq_at_slot R p hp5 hp ζ hζs v hv a ha1 haH)
  have hm0 : 0 < (a * (v 1).val) % p := by
    apply Nat.pos_of_ne_zero
    intro h0
    rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp (Nat.dvd_of_mod_eq_zero h0) with h | h
    · exact Nat.not_dvd_of_pos_of_lt ha1 hap h
    · exact Nat.not_dvd_of_pos_of_lt hvk hvkp h
  refine isUnit_sub_cross_family R p hp5 hp ζ hζs w hw
    ((a * (v 0).val) % p) ((a * (v 1).val) % p)
    hm0 (Nat.mod_lt _ (Fact.out : p.Prime).pos) ?_
  have hd := KTORDDet.coord_ne_of_det_ne_zero v w hvw (a : ZMod p)
  have hcast : ∀ i, (((a * (v i).val) % p : ℕ) : ZMod p) = (a : ZMod p) * v i := by
    intro i; rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_zmod_val]
  exact ⟨fun ⟨h0, h1⟩ => hd.1 ⟨(hcast 0) ▸ h0, (hcast 1) ▸ h1⟩,
         fun ⟨h0, h1⟩ => hd.2 ⟨(hcast 0) ▸ h0, (hcast 1) ▸ h1⟩⟩

end KTORDIndep2
p2m_reactivate "P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDAlpha P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.KTORDUnit"

universe u

theorem solution {R : Type u} [CommRing R]
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hp : IsUnit (p : R)) (ζ : Rˣ)
    (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) (v w : Fin 2 → ZMod p)
    (hv : v 1 ≠ 0) (hw : w 1 ≠ 0) (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    IsUnit (ModularCurve.indepElt (ModularCurve.tateBase R p) p
      (ModularCurve.cuspPoint R p ζ v).1 (ModularCurve.cuspPoint R p ζ w).1) := by
  rw [ModularCurve.cuspPoint_of_ne_zero ζ hv, ModularCurve.cuspPoint_of_ne_zero ζ hw]
  exact KTORDIndep2.isUnit_indepElt_slot_slot R p hp5 hp ζ hζ v hv w hw hvw

end S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le
end P2MW
export P2MW.S_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le (solution)
