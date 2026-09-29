-- Prove2me | solution 1 for ModularCurve.IsLevelPStructure.exists_eq_nsmul_add_nsmul_of_isLevelPStructure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/281c4ac3-2412-54a0-94d2-b92efc078032

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsLevelPStructure_exists_eq_nsmul_add_nsmul_of_isLevelPStructure
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

p2m_open "ModularCurve P2MW.S_ModularCurve_IsLevelPStructure_exists_eq_nsmul_add_nsmul_of_isLevelPStructure.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData IsLevelPStructure indepElt_eq_zero_iff_mem_zmultiples"
namespace Relabel
p2m_open "ModularCurve"

open WeierstrassCurve

section Group

variable {G : Type*} [AddCommGroup G]

theorem zsmul_eq_of_intCast_eq {ℓ : ℕ} {P : G} (hP : ℓ • P = 0) {m n : ℤ}
    (h : (m : ZMod ℓ) = (n : ZMod ℓ)) : m • P = n • P := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  have hn : n = m + k * (ℓ : ℤ) := by linarith
  rw [hn, add_zsmul, ← smul_smul, natCast_zsmul, hP, smul_zero, add_zero]

theorem intCast_val_sub {ℓ : ℕ} [NeZero ℓ] (a b : ZMod ℓ) :
    (((a.val : ℤ) - (b.val : ℤ) : ℤ) : ZMod ℓ) = a - b := by
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem injective_pair (ℓ : ℕ) [Fact ℓ.Prime] (P Q : G) (hP : ℓ • P = 0) (hQ : ℓ • Q = 0)
    (hP0 : P ≠ 0) (hQP : Q ∉ AddSubgroup.zmultiples P) :
    Function.Injective (fun ij : ZMod ℓ × ZMod ℓ => ij.1.val • P + ij.2.val • Q) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only at h

  have h' : ((i.val : ℤ) - (i'.val : ℤ)) • P = ((j'.val : ℤ) - (j.val : ℤ)) • Q := by
    rw [← sub_eq_zero]
    have e : ((i.val : ℤ) - (i'.val : ℤ)) • P - ((j'.val : ℤ) - (j.val : ℤ)) • Q =
        (i.val • P + j.val • Q) - (i'.val • P + j'.val • Q) := by
      simp only [sub_zsmul, natCast_zsmul]
      abel
    rw [e, h, sub_self]
  by_cases hj : j = j'
  · subst hj
    rw [sub_self, zero_zsmul] at h'
    by_contra hne
    have hii : (i : ZMod ℓ) - i' ≠ 0 := by
      intro h0; apply hne; rw [sub_eq_zero.mp h0]
    set c : ZMod ℓ := ((i : ZMod ℓ) - i')⁻¹ with hc
    have h1 : (((c.val : ℤ) * ((i.val : ℤ) - (i'.val : ℤ)) : ℤ) : ZMod ℓ) = ((1 : ℤ) : ZMod ℓ) := by
      rw [Int.cast_mul, intCast_val_sub, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_one]
      exact inv_mul_cancel₀ hii
    have h2 := zsmul_eq_of_intCast_eq hP h1
    rw [one_zsmul, ← smul_smul, h', smul_zero] at h2
    exact hP0 h2.symm
  · exfalso
    have hjj : (j' : ZMod ℓ) - j ≠ 0 := by
      intro h0; apply hj; exact (sub_eq_zero.mp h0).symm
    set c : ZMod ℓ := ((j' : ZMod ℓ) - j)⁻¹ with hc
    have h1 : (((c.val : ℤ) * ((j'.val : ℤ) - (j.val : ℤ)) : ℤ) : ZMod ℓ) = ((1 : ℤ) : ZMod ℓ) := by
      rw [Int.cast_mul, intCast_val_sub, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_one]
      exact inv_mul_cancel₀ hjj
    have h2 := zsmul_eq_of_intCast_eq hQ h1
    rw [one_zsmul, ← smul_smul, ← h', smul_smul] at h2
    exact hQP (AddSubgroup.mem_zmultiples_iff.mpr ⟨_, h2⟩)

end Group

section Torsion

variable {K : Type u} [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]

def xOf : W.toAffine.Point → K
  | .zero => 0
  | .some x _ _ => x

omit [W.IsElliptic] in
theorem card_filter_xOf_le_two (s : Finset W.toAffine.Point) (h0 : (0 : W.toAffine.Point) ∉ s)
    (b : K) : (s.filter (fun P => xOf W P = b)).card ≤ 2 := by
  by_contra h
  push Not at h
  obtain ⟨P₁, h₁, P₂, h₂, P₃, h₃, h12, h13, h23⟩ := Finset.two_lt_card.mp h
  rw [Finset.mem_filter] at h₁ h₂ h₃
  rcases P₁ with _ | ⟨x₁, y₁, n₁⟩
  · exact h0 (by rw [WeierstrassCurve.Affine.Point.zero_def]; exact h₁.1)
  rcases P₂ with _ | ⟨x₂, y₂, n₂⟩
  · exact h0 (by rw [WeierstrassCurve.Affine.Point.zero_def]; exact h₂.1)
  rcases P₃ with _ | ⟨x₃, y₃, n₃⟩
  · exact h0 (by rw [WeierstrassCurve.Affine.Point.zero_def]; exact h₃.1)
  simp only [xOf] at h₁ h₂ h₃
  obtain ⟨-, rfl⟩ := h₁
  obtain ⟨-, rfl⟩ := h₂
  obtain ⟨-, hx3⟩ := h₃
  have hy12 : y₁ ≠ y₂ := by
    intro hy; apply h12; subst hy; rfl
  have hy32 : y₃ ≠ y₂ := by
    intro hy; apply h23; subst hy; subst hx3; rfl
  have e1 : y₁ = W.toAffine.negY x₂ y₂ := by
    by_contra hne; exact hy12 (WeierstrassCurve.Affine.Y_eq_of_Y_ne n₁.1 n₂.1 rfl hne)
  have e3 : y₃ = W.toAffine.negY x₂ y₂ := by
    by_contra hne; exact hy32 (WeierstrassCurve.Affine.Y_eq_of_Y_ne n₃.1 n₂.1 hx3 hne)
  apply h13
  subst hx3
  have : y₁ = y₃ := e1.trans e3.symm
  subst this
  rfl

theorem card_le_of_forall_nsmul_eq_zero {ℓ : ℕ} (hℓ : Odd ℓ) (hℓK : (ℓ : K) ≠ 0)
    (s : Finset W.toAffine.Point) (hs : ∀ P ∈ s, ℓ • P = 0) : s.card ≤ ℓ ^ 2 := by
  classical
  set s1 := s.filter (fun P => ¬ P = 0) with hs1
  have h0card : (s.filter (fun P => P = 0)).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    rw [ha.2, hb.2]
  have hsplit : s.card ≤ 1 + s1.card := by
    have := Finset.card_filter_add_card_filter_not (s := s) (fun P => P = 0)
    rw [hs1]
    omega
  have h0s1 : (0 : W.toAffine.Point) ∉ s1 := by
    rw [hs1, Finset.mem_filter]; exact fun h => h.2 rfl
  have himg : s1.image (xOf W) ⊆ (W.preΨ' ℓ).roots.toFinset := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨P, hP, rfl⟩ := hb
    rw [hs1, Finset.mem_filter] at hP
    obtain ⟨hPs, hP0⟩ := hP
    rcases P with _ | ⟨x, y, hxy⟩
    · exact absurd WeierstrassCurve.Affine.Point.zero_def.symm hP0
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots (W.preΨ'_ne_zero hℓK)]
      exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hℓ hxy).mp (hs _ hPs)
  have hroots : ((W.preΨ' ℓ).roots.toFinset).card ≤ (ℓ ^ 2 - 1) / 2 := by
    refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
    rw [W.natDegree_preΨ' hℓK, if_neg (Nat.not_even_iff_odd.mpr hℓ)]
  have hs1c : s1.card ≤ 2 * (s1.image (xOf W)).card :=
    Finset.card_le_mul_card_image _ _ (fun b _ => card_filter_xOf_le_two W s1 h0s1 b)
  have himgc := Finset.card_le_card himg
  have h2 : 2 * ((ℓ ^ 2 - 1) / 2) ≤ ℓ ^ 2 - 1 := Nat.mul_div_le (ℓ ^ 2 - 1) 2
  have hℓpos : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ hℓ.pos
  have : 2 * (s1.image (xOf W)).card ≤ 2 * ((ℓ ^ 2 - 1) / 2) :=
    Nat.mul_le_mul_left 2 (himgc.trans hroots)
  omega

theorem exists_eq_nsmul_add_nsmul {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (P Q : W.toAffine.Point) (hP : ℓ • P = 0) (hQ : ℓ • Q = 0) (hP0 : P ≠ 0)
    (hQP : Q ∉ AddSubgroup.zmultiples P) (R : W.toAffine.Point) (hR : ℓ • R = 0) :
    ∃ i j : ℕ, R = i • P + j • Q := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hℓodd : Odd ℓ := (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2
  let g : ZMod ℓ × ZMod ℓ → W.toAffine.Point := fun ij => ij.1.val • P + ij.2.val • Q
  have hg : Function.Injective g := injective_pair ℓ P Q hP hQ hP0 hQP
  let H : Finset W.toAffine.Point := (Finset.univ : Finset (ZMod ℓ × ZMod ℓ)).image g
  have hH : H.card = ℓ ^ 2 := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_prod, ZMod.card, pow_two]
  by_contra hne
  push Not at hne
  have hRH : R ∉ H := by
    intro h
    rw [Finset.mem_image] at h
    obtain ⟨⟨i, j⟩, -, hij⟩ := h
    exact hne i.val j.val hij.symm
  have htors : ∀ S ∈ insert R H, ℓ • S = 0 := by
    intro S hS
    rw [Finset.mem_insert] at hS
    rcases hS with rfl | hS
    · exact hR
    · rw [Finset.mem_image] at hS
      obtain ⟨⟨i, j⟩, -, rfl⟩ := hS
      show ℓ • (i.val • P + j.val • Q) = 0
      rw [smul_add, smul_smul, smul_smul, mul_comm ℓ, mul_comm ℓ, ← smul_smul, ← smul_smul, hP, hQ,
        smul_zero, smul_zero, add_zero]
  have hcard := card_le_of_forall_nsmul_eq_zero W hℓodd hℓK (insert R H) htors
  rw [Finset.card_insert_of_notMem hRH, hH] at hcard
  omega

end Torsion

section ModScalar

variable {G : Type*} [AddCommGroup G]

theorem nsmul_eq_mod_nsmul' {ℓ : ℕ} {P : G} (hP : ℓ • P = 0) (n : ℕ) : n • P = (n % ℓ) • P := by
  conv_lhs => rw [← Nat.div_add_mod n ℓ]
  rw [add_nsmul, mul_comm, ← smul_smul, hP, smul_zero, zero_add]

theorem val_nsmul_eq {ℓ : ℕ} [NeZero ℓ] {P : G} (hP : ℓ • P = 0) (n : ℕ) : (n : ZMod ℓ).val • P = n • P := by
  rw [ZMod.val_natCast, ← nsmul_eq_mod_nsmul' hP]

theorem val_mul_nsmul {ℓ : ℕ} [NeZero ℓ] {P : G} (hP : ℓ • P = 0) (a b : ZMod ℓ) :
    (a * b).val • P = a.val • (b.val • P) := by
  rw [smul_smul, ← val_nsmul_eq hP (a.val * b.val), Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

end ModScalar

end ModularCurve.Relabel

open ModularCurve.Relabel in

theorem solution
    {F : Type u} [Field F] [DecidableEq F] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓF : (ℓ : F) ≠ 0)
    (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ)
    (D₁ D₂ : LevelPData F) (h₁ : IsLevelPStructure W ℓ D₁) (h₂ : IsLevelPStructure W ℓ D₂) :
    ∃ (n₁P : W.toAffine.Nonsingular D₁.xP D₁.yP) (n₁Q : W.toAffine.Nonsingular D₁.xQ D₁.yQ)
      (n₂P : W.toAffine.Nonsingular D₂.xP D₂.yP) (n₂Q : W.toAffine.Nonsingular D₂.xQ D₂.yQ)
      (a b c d : ZMod ℓ), a * d - b * c ≠ 0 ∧
      WeierstrassCurve.Affine.Point.some _ _ n₂P =
        a.val • WeierstrassCurve.Affine.Point.some _ _ n₁P + b.val • WeierstrassCurve.Affine.Point.some _ _ n₁Q ∧
      WeierstrassCurve.Affine.Point.some _ _ n₂Q =
        c.val • WeierstrassCurve.Affine.Point.some _ _ n₁P + d.val • WeierstrassCurve.Affine.Point.some _ _ n₁Q := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hℓ2 : ℓ ≠ 2 := by omega
  have hℓodd : Odd ℓ := (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2
  haveI : W.IsElliptic := ⟨hΔ⟩
  have n₁P := W.toAffine.equation_iff_nonsingular.mp h₁.equation_P
  have n₁Q := W.toAffine.equation_iff_nonsingular.mp h₁.equation_Q
  have n₂P := W.toAffine.equation_iff_nonsingular.mp h₂.equation_P
  have n₂Q := W.toAffine.equation_iff_nonsingular.mp h₂.equation_Q
  have tors : ∀ {x y : F} (n : W.toAffine.Nonsingular x y),
      (W.preΨ ℓ).eval x = 0 → ℓ • WeierstrassCurve.Affine.Point.some _ _ n = 0 := by
    intro x y n hx
    rw [WeierstrassCurve.preΨ_ofNat] at hx
    exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hℓodd n).mpr hx
  have t₁P := tors n₁P h₁.preΨ_P
  have t₁Q := tors n₁Q h₁.preΨ_Q
  have t₂P := tors n₂P h₂.preΨ_P
  have t₂Q := tors n₂Q h₂.preΨ_Q
  have hP0 : WeierstrassCurve.Affine.Point.some _ _ n₁P ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  have hQP : WeierstrassCurve.Affine.Point.some _ _ n₁Q ∉
      AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.some _ _ n₁P) := fun hmem =>
    h₁.isUnit_indepElt_PQ.ne_zero ((ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hℓ2 n₁P n₁Q t₁P).mpr hmem)
  have hQP₂ : WeierstrassCurve.Affine.Point.some _ _ n₂Q ∉
      AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.some _ _ n₂P) := fun hmem =>
    h₂.isUnit_indepElt_PQ.ne_zero ((ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hℓ2 n₂P n₂Q t₂P).mpr hmem)
  obtain ⟨i, j, hij⟩ := exists_eq_nsmul_add_nsmul W hℓ2 hℓF _ _ t₁P t₁Q hP0 hQP _ t₂P
  obtain ⟨i', j', hij'⟩ := exists_eq_nsmul_add_nsmul W hℓ2 hℓF _ _ t₁P t₁Q hP0 hQP _ t₂Q
  set P₁ := WeierstrassCurve.Affine.Point.some _ _ n₁P with hP₁
  set Q₁ := WeierstrassCurve.Affine.Point.some _ _ n₁Q with hQ₁
  set P₂ := WeierstrassCurve.Affine.Point.some _ _ n₂P with hP₂
  set Q₂ := WeierstrassCurve.Affine.Point.some _ _ n₂Q with hQ₂
  have eP : P₂ = (i : ZMod ℓ).val • P₁ + (j : ZMod ℓ).val • Q₁ := by
    rw [val_nsmul_eq t₁P, val_nsmul_eq t₁Q]; exact hij
  have eQ : Q₂ = (i' : ZMod ℓ).val • P₁ + (j' : ZMod ℓ).val • Q₁ := by
    rw [val_nsmul_eq t₁P, val_nsmul_eq t₁Q]; exact hij'
  refine ⟨n₁P, n₁Q, n₂P, n₂Q, (i : ZMod ℓ), (j : ZMod ℓ), (i' : ZMod ℓ), (j' : ZMod ℓ), ?_, eP, eQ⟩

  intro hdet
  set a : ZMod ℓ := (i : ZMod ℓ) with ha
  set b : ZMod ℓ := (j : ZMod ℓ) with hb
  set c : ZMod ℓ := (i' : ZMod ℓ) with hc
  set d : ZMod ℓ := (j' : ZMod ℓ) with hd

  have hsm : ∀ lam : ZMod ℓ, lam.val • P₂ = (lam * a).val • P₁ + (lam * b).val • Q₁ := by
    intro lam
    rw [eP, smul_add, val_mul_nsmul t₁P, val_mul_nsmul t₁Q]
  have hP₂0 : P₂ ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  apply hQP₂
  show Q₂ ∈ AddSubgroup.zmultiples P₂
  by_cases ha0 : a = 0
  · have hb0 : b ≠ 0 := by
      intro hb0
      apply hP₂0
      rw [eP, ha0, hb0, ZMod.val_zero, zero_smul, zero_smul, add_zero]
    have hc0 : c = 0 := by
      have : b * c = 0 := by linear_combination (-1 : ZMod ℓ) * hdet + d * ha0
      exact (mul_eq_zero.mp this).resolve_left hb0

    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨((d * b⁻¹).val : ℤ), ?_⟩
    rw [natCast_zsmul, hsm, eQ, hc0, ha0, mul_zero, mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  ·
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨((c * a⁻¹).val : ℤ), ?_⟩
    have hd' : c * a⁻¹ * b = d := by
      field_simp
      linear_combination (-1 : ZMod ℓ) * hdet
    rw [natCast_zsmul, hsm, eQ, mul_assoc c a⁻¹ a, inv_mul_cancel₀ ha0, mul_one, hd']

end S_ModularCurve_IsLevelPStructure_exists_eq_nsmul_add_nsmul_of_isLevelPStructure
end P2MW
export P2MW.S_ModularCurve_IsLevelPStructure_exists_eq_nsmul_add_nsmul_of_isLevelPStructure (solution)
