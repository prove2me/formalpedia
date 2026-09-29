-- Prove2me | solution 1 for ModularCurve.LevelP.exists_levelPData_map_eq_relabel_univData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/939d70d7-135b-5472-b36b-6db068dcb93e

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelP_exists_levelPData_map_eq_relabel_univData
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u w
set_option linter.unusedVariables false

open scoped Classical

namespace KatzRelabelUniv

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve WeierstrassCurve.Affine

section Formulas

variable {T : Type*} [CommRing T] (W : WeierstrassCurve T)

noncomputable def chordL (P Q : T × T) : T := (P.2 - Q.2) * Ring.inverse (P.1 - Q.1)

noncomputable def dblL (P : T × T) : T :=
  (3 * P.1 ^ 2 + 2 * W.a₂ * P.1 + W.a₄ - W.a₁ * P.2) * Ring.inverse (P.2 - W.toAffine.negY P.1 P.2)

def addXY (P Q : T × T) (L : T) : T × T := (W.toAffine.addX P.1 Q.1 L, W.toAffine.addY P.1 Q.1 P.2 L)

noncomputable def chord (P Q : T × T) : T × T := addXY W P Q (chordL P Q)

noncomputable def dbl (P : T × T) : T × T := addXY W P P (dblL W P)

noncomputable def mulPt (P : T × T) : ℕ → T × T
  | 0 => P
  | 1 => P
  | 2 => dbl W P
  | (n + 3) => chord W (mulPt P (n + 2)) P

noncomputable def linComb (P Q : T × T) (a c : ℕ) : T × T :=
  if c = 0 then mulPt W P a else if a = 0 then mulPt W Q c else chord W (mulPt W P a) (mulPt W Q c)

variable {T' : Type*} [CommRing T'] (f : T →+* T')

def pmap (P : T × T) : T' × T' := (f P.1, f P.2)

@[scoped simp] theorem pmap_fst (P : T × T) : (pmap f P).1 = f P.1 := rfl
@[scoped simp] theorem pmap_snd (P : T × T) : (pmap f P).2 = f P.2 := rfl
@[scoped simp] theorem pmap_mk (x y : T) : pmap f (x, y) = (f x, f y) := rfl

theorem map_ringInverse {u : T} (hu : IsUnit u) : f (Ring.inverse u) = Ring.inverse (f u) := by
  have h1 : f (Ring.inverse u) * f u = 1 := by rw [← map_mul, Ring.inverse_mul_cancel _ hu, map_one]
  have h2 : Ring.inverse (f u) * f u = 1 := Ring.inverse_mul_cancel _ (hu.map f)
  exact (hu.map f).mul_left_inj.1 (h1.trans h2.symm)

theorem map_addXY (P Q : T × T) (L : T) :
    pmap f (addXY W P Q L) = addXY (W.map f) (pmap f P) (pmap f Q) (f L) := by
  simp only [addXY, pmap, map_addX, map_addY]

theorem map_chord (P Q : T × T) (hu : IsUnit (P.1 - Q.1)) :
    pmap f (chord W P Q) = chord (W.map f) (pmap f P) (pmap f Q) := by
  rw [chord, chord, map_addXY]
  congr 1
  simp only [chordL, pmap, map_mul, map_sub, map_ringInverse f hu]

theorem map_dbl (P : T × T) (hu : IsUnit (P.2 - W.toAffine.negY P.1 P.2)) :
    pmap f (dbl W P) = dbl (W.map f) (pmap f P) := by
  rw [dbl, dbl, map_addXY]
  congr 1
  simp only [dblL, pmap, map_mul, map_sub, map_add, map_pow, map_ringInverse f hu, ← map_negY,
    map_ofNat, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]

end Formulas

section FieldFormulas

variable {F : Type*} [Field F] (E : WeierstrassCurve F)

theorem chord_eq {x₁ y₁ x₂ y₂ : F} (h₁ : E.toAffine.Nonsingular x₁ y₁) (h₂ : E.toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂) :
    chord E (x₁, y₁) (x₂, y₂) = ofPoint E (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) := by
  rw [Point.add_of_X_ne hx]
  show addXY E (x₁, y₁) (x₂, y₂) (chordL (x₁, y₁) (x₂, y₂)) = _
  have hL : chordL (x₁, y₁) (x₂, y₂) = E.toAffine.slope x₁ x₂ y₁ y₂ := by
    rw [slope_of_X_ne hx, chordL, Ring.inverse_eq_inv, div_eq_mul_inv]
  rw [hL]
  rfl

theorem dbl_eq {x y : F} (h : E.toAffine.Nonsingular x y) (hy : y ≠ E.toAffine.negY x y) :
    dbl E (x, y) = ofPoint E (Point.some x y h + Point.some x y h) := by
  rw [Point.add_self_of_Y_ne hy]
  show addXY E (x, y) (x, y) (dblL E (x, y)) = _
  have hL : dblL E (x, y) = E.toAffine.slope x x y y := by
    rw [slope_of_Y_ne rfl hy, dblL, Ring.inverse_eq_inv, div_eq_mul_inv]
  rw [hL]
  rfl

theorem ofPoint_some {x y : F} (h : E.toAffine.Nonsingular x y) : ofPoint E (Point.some x y h) = (x, y) := rfl

theorem exists_eq_some {S : E.toAffine.Point} (hS : S ≠ 0) :
    ∃ (x y : F) (h : E.toAffine.Nonsingular x y), S = Point.some x y h := by
  rcases S with _ | ⟨x, y, h⟩
  · exact (hS rfl).elim
  · exact ⟨x, y, h, rfl⟩

end FieldFormulas

section FieldTorsion

variable {F : Type*} [Field F] (E : WeierstrassCurve F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hΔ : IsUnit E.Δ)

include hℓ3 in
theorem odd_ell : Odd ℓ := (Fact.out : ℓ.Prime).odd_of_ne_two (by omega)

include hℓ3 hΔ in
theorem ell_smul_eq_zero {x y : F} (h : E.toAffine.Nonsingular x y) (hx : (E.preΨ ℓ).eval x = 0) :
    (ℓ : ℤ) • Point.some x y h = 0 := by
  haveI : E.IsElliptic := ⟨hΔ⟩
  rw [natCast_zsmul]
  rw [WeierstrassCurve.preΨ_ofNat] at hx
  exact (Point.nsmul_some_eq_zero_iff_eval_prePsi E (odd_ell ℓ hℓ3) h).2 hx

include hℓ3 hΔ in
theorem exists_smul_smul_eq {x y : F} (h : E.toAffine.Nonsingular x y) (hx : (E.preΨ ℓ).eval x = 0)
    {c : ℤ} (hc : ¬ (ℓ : ℤ) ∣ c) : ∃ v : ℤ, v • (c • Point.some x y h) = Point.some x y h := by
  have hcop : IsCoprime (ℓ : ℤ) c := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Nat.Coprime ℓ c.natAbs := by
      rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : ℓ.Prime)]
      intro hd
      exact hc (Int.natCast_dvd.2 hd)
    simpa [Int.gcd] using h1
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨b, ?_⟩
  have h0 := ell_smul_eq_zero E ℓ hℓ3 hΔ h hx
  calc b • (c • Point.some x y h)
      = (a * (ℓ : ℤ) + b * c) • Point.some x y h - a • ((ℓ : ℤ) • Point.some x y h) := by
        rw [add_smul, mul_smul, mul_smul]; abel
    _ = Point.some x y h := by rw [hab, h0, smul_zero, sub_zero, one_smul]

include hℓ3 hΔ in

theorem smul_eq_smul_of_dvd_sub {x y : F} (h : E.toAffine.Nonsingular x y) (hx : (E.preΨ ℓ).eval x = 0)
    {m m' : ℤ} (hmm' : (ℓ : ℤ) ∣ m - m') : m • Point.some x y h = m' • Point.some x y h := by
  obtain ⟨k, hk⟩ := hmm'
  have : m = m' + (ℓ : ℤ) * k := by omega
  rw [this, add_smul, mul_comm, mul_smul, ell_smul_eq_zero E ℓ hℓ3 hΔ h hx, smul_zero, add_zero]

include hℓ3 hΔ in

theorem smul_ne_zero {x y : F} (h : E.toAffine.Nonsingular x y) (hx : (E.preΨ ℓ).eval x = 0)
    {m : ℤ} (hm : ¬ (ℓ : ℤ) ∣ m) : m • Point.some x y h ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := exists_smul_smul_eq E ℓ hℓ3 hΔ h hx hm
  rw [h0, smul_zero] at hv
  exact Point.some_ne_zero _ hv.symm

include hℓ3 hΔ in

theorem dvd_and_dvd_of_smul_add_smul_eq_zero {D : LevelPData F} (hD : IsLevelPStructure E ℓ D)
    (hP : E.toAffine.Nonsingular D.xP D.yP) (hQ : E.toAffine.Nonsingular D.xQ D.yQ) (a c : ℤ)
    (h : a • Point.some D.xP D.yP hP + c • Point.some D.xQ D.yQ hQ = 0) :
    (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ c := by
  set P := Point.some D.xP D.yP hP with hPd
  set Q := Point.some D.xQ D.yQ hQ with hQd
  have hℓ2 : ℓ ≠ 2 := by omega
  have hPℓ : (ℓ : ℤ) • P = 0 := ell_smul_eq_zero E ℓ hℓ3 hΔ _ hD.preΨ_P
  have hQℓ : (ℓ : ℤ) • Q = 0 := ell_smul_eq_zero E ℓ hℓ3 hΔ _ hD.preΨ_Q
  have hQP : Q ∉ AddSubgroup.zmultiples P := by
    intro hmem
    have hz : ModularCurve.indepElt E ℓ D.xP D.xQ = 0 :=
      (ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hℓ2 hP hQ (by
          have := hPℓ; rwa [natCast_zsmul] at this)).2 hmem
    exact hD.isUnit_indepElt_PQ.ne_zero hz
  have hcQ : c • Q = (-a) • P := by
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm, h]
  have hc : (ℓ : ℤ) ∣ c := by
    by_contra hc
    obtain ⟨v, hv⟩ := exists_smul_smul_eq E ℓ hℓ3 hΔ hQ hD.preΨ_Q hc
    apply hQP
    rw [← hQd] at hv
    rw [← hv, hcQ, smul_smul]
    exact ⟨v * -a, rfl⟩
  refine ⟨?_, hc⟩
  obtain ⟨k, rfl⟩ := hc
  have haP : a • P = 0 := by
    have : ((ℓ : ℤ) * k) • Q = 0 := by rw [mul_comm, mul_smul, hQℓ, smul_zero]
    rwa [this, add_zero] at h
  by_contra ha
  exact smul_ne_zero E ℓ hℓ3 hΔ hP hD.preΨ_P ha haP

end FieldTorsion

section Chain

variable {T : Type} [CommRing T] (W : WeierstrassCurve T) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
  (hℓΔ : IsUnit (((ℓ : ℕ) : T) * W.Δ))

theorem isUnit_of_forall_field {a : T}
    (h : ∀ (F : Type) [Field F] (φ : T →+* F), φ a ≠ 0) : IsUnit a := by
  by_contra ha
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {a}) (Ideal.span_singleton_ne_top ha)
  letI := Ideal.Quotient.field M
  exact h (T ⧸ M) (Ideal.Quotient.mk M) (Ideal.Quotient.eq_zero_iff_mem.2 (hle (Ideal.subset_span rfl)))

include hℓΔ in
theorem field_data {F : Type*} [Field F] (φ : T →+* F) : (ℓ : F) ≠ 0 ∧ IsUnit (W.map φ).Δ := by
  have h := hℓΔ.map φ
  rw [map_mul, map_natCast, ← WeierstrassCurve.map_Δ] at h
  exact ⟨(isUnit_of_mul_isUnit_left h).ne_zero, isUnit_of_mul_isUnit_right h⟩

include hℓΔ in
theorem nonsingular_map {F : Type*} [Field F] (φ : T →+* F) {x y : T} (hxy : W.toAffine.Equation x y) :
    (W.map φ).toAffine.Nonsingular (φ x) (φ y) :=
  (equation_iff_nonsingular_of_Δ_ne_zero (field_data W ℓ hℓΔ φ).2.ne_zero).1 (hxy.map φ)

theorem preΨ_map {F : Type*} [Field F] (φ : T →+* F) {x : T} (hx : (W.preΨ ℓ).eval x = 0) :
    ((W.map φ).preΨ ℓ).eval (φ x) = 0 := by
  rw [WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply, hx, map_zero]

include hℓ3 hℓΔ in

theorem dbl_step {x y : T} (hxy : W.toAffine.Equation x y) (hx : (W.preΨ ℓ).eval x = 0)
    {F : Type w} [Field F] (φ : T →+* F) :
    pmap φ (mulPt W (x, y) 2) =
      ofPoint (W.map φ) ((2 : ℤ) • Point.some (φ x) (φ y) (nonsingular_map W ℓ hℓΔ φ hxy)) := by
  have hu : IsUnit ((x, y).2 - W.toAffine.negY (x, y).1 (x, y).2) := by
    have := WeierstrassCurve.isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd W
      (isUnit_of_mul_isUnit_right hℓΔ) (odd_ell ℓ hℓ3) hxy hx
    convert this using 1
    simp only [negY]; ring
  show pmap φ (dbl W (x, y)) = _
  rw [map_dbl W φ (x, y) hu]
  have hy : φ y ≠ (W.map φ).toAffine.negY (φ x) (φ y) := by
    intro h
    have h1 := hu.map φ
    simp only [map_sub] at h1
    rw [← map_negY] at h1
    exact h1.ne_zero (sub_eq_zero.2 h)
  show dbl (W.map φ) (φ x, φ y) = _
  rw [dbl_eq (W.map φ) (nonsingular_map W ℓ hℓΔ φ hxy) hy, two_smul]

include hℓ3 hℓΔ in

theorem smul_map_ne_zero {x y : T} (hxy : W.toAffine.Equation x y) (hx : (W.preΨ ℓ).eval x = 0)
    {F : Type w} [Field F] (φ : T →+* F) {m : ℕ} (hm : 1 ≤ m) (hm' : m ≤ ℓ - 1) :
    (m : ℤ) • Point.some (φ x) (φ y) (nonsingular_map W ℓ hℓΔ φ hxy) ≠ 0 := by
  refine smul_ne_zero (W.map φ) ℓ hℓ3 (field_data W ℓ hℓΔ φ).2 _ (preΨ_map W ℓ φ hx) ?_
  intro hd
  have := Int.le_of_dvd (by exact_mod_cast hm) hd
  omega

include hℓ3 hℓΔ in

theorem chord_step {x y : T} (hxy : W.toAffine.Equation x y) (hx : (W.preΨ ℓ).eval x = 0)
    (n : ℕ) (hn : n + 3 ≤ ℓ - 1) (hu : IsUnit ((mulPt W (x, y) (n + 2)).1 - (x, y).1))
    {F : Type w} [Field F] (φ : T →+* F)
    (ih : pmap φ (mulPt W (x, y) (n + 2)) =
      ofPoint (W.map φ) (((n + 2 : ℕ) : ℤ) • Point.some (φ x) (φ y) (nonsingular_map W ℓ hℓΔ φ hxy))) :
    pmap φ (mulPt W (x, y) (n + 3)) =
      ofPoint (W.map φ) (((n + 3 : ℕ) : ℤ) • Point.some (φ x) (φ y) (nonsingular_map W ℓ hℓΔ φ hxy)) := by
  show pmap φ (chord W (mulPt W (x, y) (n + 2)) (x, y)) = _
  rw [map_chord W φ _ _ hu, ih]
  obtain ⟨xk, yk, hk', hS⟩ := exists_eq_some (W.map φ)
    (smul_map_ne_zero W ℓ hℓ3 hℓΔ hxy hx φ (m := n + 2) (by omega) (by omega))
  rw [hS, ofPoint_some]
  have hxx : xk ≠ φ x := by
    intro hxx
    have e := congrArg Prod.fst ih
    simp only [pmap_fst] at e
    have h1 := hu.map φ
    rw [map_sub, e, hS, ofPoint_some] at h1
    exact h1.ne_zero (sub_eq_zero.2 hxx)
  show chord (W.map φ) (xk, yk) (φ x, φ y) = _
  rw [chord_eq (W.map φ) hk' (nonsingular_map W ℓ hℓΔ φ hxy) hxx, ← hS]
  congr 1
  have e2 : (((n + 3 : ℕ)) : ℤ) = ((n + 2 : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [e2, add_smul, one_smul]

include hℓ3 hℓΔ in

theorem isUnit_step {x y : T} (hxy : W.toAffine.Equation x y) (hx : (W.preΨ ℓ).eval x = 0)
    (n : ℕ) (hn : n + 3 ≤ ℓ - 1)
    (ih0 : ∀ (F : Type) [Field F] (φ : T →+* F), pmap φ (mulPt W (x, y) (n + 2)) =
      ofPoint (W.map φ) (((n + 2 : ℕ) : ℤ) • Point.some (φ x) (φ y) (nonsingular_map W ℓ hℓΔ φ hxy))) :
    IsUnit ((mulPt W (x, y) (n + 2)).1 - (x, y).1) := by
  refine isUnit_of_forall_field fun F _ φ => ?_
  have e := congrArg Prod.fst (ih0 F φ)
  simp only [pmap_fst] at e
  rw [map_sub, e]
  obtain ⟨xk, yk, hk', hS⟩ := exists_eq_some (W.map φ)
    (smul_map_ne_zero W ℓ hℓ3 hℓΔ hxy hx φ (m := n + 2) (by omega) (by omega))
  rw [hS, ofPoint_some]
  intro hxx
  have hxx' : xk = φ x := sub_eq_zero.1 hxx
  rcases Y_eq_of_X_eq hk'.left (nonsingular_map W ℓ hℓΔ φ hxy).left hxx' with hyy | hyy
  ·
    have hPeq : Point.some xk yk hk' = Point.some (φ x) (φ y) (nonsingular_map W ℓ hℓΔ φ hxy) := by
      subst hxx'; subst hyy; rfl
    apply smul_map_ne_zero W ℓ hℓ3 hℓΔ hxy hx φ (m := n + 1) (by omega) (by omega)
    have := hS
    rw [hPeq] at this
    have e2 : (((n + 2 : ℕ)) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [e2, add_smul, one_smul] at this
    simpa using this
  ·
    have hPeq : Point.some xk yk hk' = -Point.some (φ x) (φ y) (nonsingular_map W ℓ hℓΔ φ hxy) := by
      rw [Point.neg_some]
      subst hxx'; subst hyy; rfl
    apply smul_map_ne_zero W ℓ hℓ3 hℓΔ hxy hx φ (m := n + 3) (by omega) hn
    have := hS
    rw [hPeq] at this
    have e2 : (((n + 3 : ℕ)) : ℤ) = ((n + 2 : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [e2, add_smul, one_smul, this, neg_add_cancel]

include hℓ3 hℓΔ in

theorem map_mulPt₀ {x y : T} (hxy : W.toAffine.Equation x y) (hx : (W.preΨ ℓ).eval x = 0) :
    ∀ n : ℕ, n + 1 ≤ ℓ - 1 →
      ∀ (F : Type) [Field F] (φ : T →+* F),
        pmap φ (mulPt W (x, y) (n + 1)) =
          ofPoint (W.map φ) (((n + 1 : ℕ) : ℤ) • Point.some (φ x) (φ y) (nonsingular_map W ℓ hℓΔ φ hxy)) := by
  intro n
  induction n with
  | zero =>
    intro _ F _ φ
    simp [mulPt, ofPoint_some]
  | succ n ih =>
    intro hn F _ φ
    rcases n with _ | n
    · simpa using dbl_step W ℓ hℓ3 hℓΔ hxy hx φ
    · have hu := isUnit_step W ℓ hℓ3 hℓΔ hxy hx n (by omega) (ih (by omega))
      exact chord_step W ℓ hℓ3 hℓΔ hxy hx n (by omega) hu φ (ih (by omega) F φ)

include hℓ3 hℓΔ in

theorem map_mulPt {x y : T} (hxy : W.toAffine.Equation x y) (hx : (W.preΨ ℓ).eval x = 0) :
    ∀ n : ℕ, n + 1 ≤ ℓ - 1 →
      ∀ (F : Type w) [Field F] (φ : T →+* F),
        pmap φ (mulPt W (x, y) (n + 1)) =
          ofPoint (W.map φ) (((n + 1 : ℕ) : ℤ) • Point.some (φ x) (φ y) (nonsingular_map W ℓ hℓΔ φ hxy)) := by
  intro n
  induction n with
  | zero =>
    intro _ F _ φ
    simp [mulPt, ofPoint_some]
  | succ n ih =>
    intro hn F _ φ
    rcases n with _ | n
    · simpa using dbl_step W ℓ hℓ3 hℓΔ hxy hx φ
    · have hu := isUnit_step W ℓ hℓ3 hℓΔ hxy hx n (by omega)
        (map_mulPt₀ W ℓ hℓ3 hℓΔ hxy hx (n + 1) (by omega))
      exact chord_step W ℓ hℓ3 hℓΔ hxy hx n (by omega) hu φ (ih (by omega) F φ)

include hℓ3 hℓΔ in

theorem map_mulPt' {x y : T} (hxy : W.toAffine.Equation x y) (hx : (W.preΨ ℓ).eval x = 0)
    {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ ℓ - 1) {F : Type w} [Field F] (φ : T →+* F) :
    pmap φ (mulPt W (x, y) k) =
      ofPoint (W.map φ) ((k : ℤ) • Point.some (φ x) (φ y) (nonsingular_map W ℓ hℓΔ φ hxy)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact map_mulPt W ℓ hℓ3 hℓΔ hxy hx n hk' F φ

variable (D : LevelPData T) (hD : IsLevelPStructure W ℓ D)

include hℓ3 hℓΔ hD in

theorem map_linComb {a c : ℕ} (ha : a ≤ ℓ - 1) (hc : c ≤ ℓ - 1) (hac : ¬ (a = 0 ∧ c = 0))
    {F : Type w} [Field F] (φ : T →+* F) :
    pmap φ (linComb W (D.xP, D.yP) (D.xQ, D.yQ) a c) =
      ofPoint (W.map φ) ((a : ℤ) • Point.some (φ D.xP) (φ D.yP) (nonsingular_map W ℓ hℓΔ φ hD.equation_P) +
        (c : ℤ) • Point.some (φ D.xQ) (φ D.yQ) (nonsingular_map W ℓ hℓΔ φ hD.equation_Q)) := by
  unfold linComb
  by_cases hc0 : c = 0
  · subst hc0
    have ha1 : 1 ≤ a := by omega
    rw [if_pos rfl, map_mulPt' W ℓ hℓ3 hℓΔ hD.equation_P hD.preΨ_P ha1 ha φ]
    simp
  rw [if_neg hc0]
  by_cases ha0 : a = 0
  · subst ha0
    have hc1 : 1 ≤ c := by omega
    rw [if_pos rfl, map_mulPt' W ℓ hℓ3 hℓΔ hD.equation_Q hD.preΨ_Q hc1 hc φ]
    simp
  rw [if_neg ha0]
  have ha1 : 1 ≤ a := by omega
  have hc1 : 1 ≤ c := by omega
  set Pφ := Point.some (φ D.xP) (φ D.yP) (nonsingular_map W ℓ hℓΔ φ hD.equation_P) with hPφ
  set Qφ := Point.some (φ D.xQ) (φ D.yQ) (nonsingular_map W ℓ hℓΔ φ hD.equation_Q) with hQφ
  have hDφ : IsLevelPStructure (W.map φ) ℓ (D.map φ) := hD.map φ

  have hadv : ¬ (ℓ : ℤ) ∣ (a : ℤ) := by
    intro hd; have := Int.le_of_dvd (by exact_mod_cast ha1) hd; omega
  have hcdv : ¬ (ℓ : ℤ) ∣ (c : ℤ) := by
    intro hd; have := Int.le_of_dvd (by exact_mod_cast hc1) hd; omega

  have hu : IsUnit ((mulPt W (D.xP, D.yP) a).1 - (mulPt W (D.xQ, D.yQ) c).1) := by
    refine isUnit_of_forall_field fun F' _ ψ => ?_
    have eP := congrArg Prod.fst (map_mulPt' W ℓ hℓ3 hℓΔ hD.equation_P hD.preΨ_P ha1 ha ψ)
    have eQ := congrArg Prod.fst (map_mulPt' W ℓ hℓ3 hℓΔ hD.equation_Q hD.preΨ_Q hc1 hc ψ)
    simp only [pmap_fst] at eP eQ
    rw [map_sub, eP, eQ]
    have hDψ : IsLevelPStructure (W.map ψ) ℓ (D.map ψ) := hD.map ψ
    have hΔψ := (field_data W ℓ hℓΔ ψ).2
    obtain ⟨xa, ya, hka, hSa⟩ := exists_eq_some (W.map ψ)
      (smul_ne_zero (W.map ψ) ℓ hℓ3 hΔψ (nonsingular_map W ℓ hℓΔ ψ hD.equation_P) (preΨ_map W ℓ ψ hD.preΨ_P) hadv)
    obtain ⟨xc, yc, hkc, hSc⟩ := exists_eq_some (W.map ψ)
      (smul_ne_zero (W.map ψ) ℓ hℓ3 hΔψ (nonsingular_map W ℓ hℓΔ ψ hD.equation_Q) (preΨ_map W ℓ ψ hD.preΨ_Q) hcdv)
    rw [hSa, hSc, ofPoint_some, ofPoint_some]
    intro hxx
    have hxx' : xa = xc := sub_eq_zero.1 hxx

    have key : ∀ s : ℤ, (s = 1 ∨ s = -1) → Point.some xa ya hka = s • Point.some xc yc hkc → False := by
      intro s hs heq
      have h0 : (a : ℤ) • Point.some (ψ D.xP) (ψ D.yP) (nonsingular_map W ℓ hℓΔ ψ hD.equation_P) +
          (-(s * c) : ℤ) • Point.some (ψ D.xQ) (ψ D.yQ) (nonsingular_map W ℓ hℓΔ ψ hD.equation_Q) = 0 := by
        rw [hSa, heq, ← hSc, smul_smul, neg_smul, add_neg_cancel]
      have := (dvd_and_dvd_of_smul_add_smul_eq_zero (W.map ψ) ℓ hℓ3 hΔψ
        (D := D.map ψ) hDψ (nonsingular_map W ℓ hℓΔ ψ hD.equation_P)
        (nonsingular_map W ℓ hℓΔ ψ hD.equation_Q) _ _ h0).1
      exact hadv this
    rcases Y_eq_of_X_eq hka.left hkc.left hxx' with hyy | hyy
    · exact key 1 (Or.inl rfl) (by rw [one_smul]; subst hxx'; subst hyy; rfl)
    · exact key (-1) (Or.inr rfl) (by rw [neg_smul, one_smul, Point.neg_some]; subst hxx'; subst hyy; rfl)
  rw [map_chord W φ _ _ hu, map_mulPt' W ℓ hℓ3 hℓΔ hD.equation_P hD.preΨ_P ha1 ha φ,
    map_mulPt' W ℓ hℓ3 hℓΔ hD.equation_Q hD.preΨ_Q hc1 hc φ, ← hPφ, ← hQφ]
  obtain ⟨xa, ya, hka, hSa⟩ := exists_eq_some (W.map φ)
    (smul_ne_zero (W.map φ) ℓ hℓ3 (field_data W ℓ hℓΔ φ).2 (nonsingular_map W ℓ hℓΔ φ hD.equation_P)
      (preΨ_map W ℓ φ hD.preΨ_P) hadv)
  obtain ⟨xc, yc, hkc, hSc⟩ := exists_eq_some (W.map φ)
    (smul_ne_zero (W.map φ) ℓ hℓ3 (field_data W ℓ hℓΔ φ).2 (nonsingular_map W ℓ hℓΔ φ hD.equation_Q)
      (preΨ_map W ℓ φ hD.preΨ_Q) hcdv)
  rw [← hPφ] at hSa
  rw [← hQφ] at hSc
  rw [hSa, hSc, ofPoint_some, ofPoint_some]
  have hxx : xa ≠ xc := by
    intro hxx
    have h1 := hu.map φ
    have eP := congrArg Prod.fst (map_mulPt' W ℓ hℓ3 hℓΔ hD.equation_P hD.preΨ_P ha1 ha φ)
    have eQ := congrArg Prod.fst (map_mulPt' W ℓ hℓ3 hℓΔ hD.equation_Q hD.preΨ_Q hc1 hc φ)
    simp only [pmap_fst] at eP eQ
    rw [map_sub, eP, eQ, ← hPφ, ← hQφ, hSa, hSc, ofPoint_some, ofPoint_some] at h1
    exact h1.ne_zero (sub_eq_zero.2 hxx)
  show chord (W.map φ) (xa, ya) (xc, yc) = _
  rw [chord_eq (W.map φ) hka hkc hxx]

end Chain

section Univ

open ModularCurve.LevelP

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)

theorem toPoint_of_nonsingular {F : Type*} [Field F] (E : WeierstrassCurve F) {x y : F}
    (h : E.toAffine.Nonsingular x y) : toPoint E x y = Point.some x y h := by
  unfold toPoint; rw [dif_pos h]

theorem dvd_sub_val (z : ℤ) : (ℓ : ℤ) ∣ z - (((z : ZMod ℓ).val : ℕ) : ℤ) := by
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  simp

theorem val_le (z : ℤ) : ((z : ZMod ℓ).val : ℕ) ≤ ℓ - 1 := by
  have := ZMod.val_lt (z : ZMod ℓ)
  omega

include hℓ3 in
theorem main (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) :
    ∃ R : LevelPData (UnivBasisRing ℓ),
      ∀ (F : Type u) [Field F] (φ : UnivBasisRing ℓ →+* F),
        R.map φ = LevelPData.relabel ((univCurveT ℓ).map φ) g ((univData ℓ).map φ) := by
  set W := univCurveT ℓ
  set D := univData ℓ
  have hD : IsLevelPStructure W ℓ D := isLevelPStructure_univData ℓ
  have hℓΔ : IsUnit (((ℓ : ℕ) : UnivBasisRing ℓ) * W.Δ) :=
    (isUnit_natCast_univBasisRing ℓ).mul (isUnit_Δ_univCurveT ℓ)

  let a : Fin 2 → Fin 2 → ℕ := fun i j => ((g i j : ZMod ℓ).val)
  have hane : ∀ j : Fin 2, ¬ (a 0 j = 0 ∧ a 1 j = 0) := by
    intro j ⟨h0, h1⟩
    have e0 : (g.map (Int.castRingHom (ZMod ℓ))) 0 j = 0 := by
      simpa [Matrix.map_apply, a, ZMod.val_eq_zero] using h0
    have e1 : (g.map (Int.castRingHom (ZMod ℓ))) 1 j = 0 := by
      simpa [Matrix.map_apply, a, ZMod.val_eq_zero] using h1
    have hdet : (g.map (Int.castRingHom (ZMod ℓ))).det = 0 := by
      rw [Matrix.det_fin_two]
      fin_cases j
      · simp only [Fin.zero_eta] at e0 e1
        rw [e0, e1]; ring
      · simp only [Fin.mk_one] at e0 e1
        rw [e0, e1]; ring
    rw [hdet] at hg
    exact not_isUnit_zero hg
  let S : Fin 2 → UnivBasisRing ℓ × UnivBasisRing ℓ := fun j =>
    linComb W (D.xP, D.yP) (D.xQ, D.yQ) (a 0 j) (a 1 j)
  refine ⟨⟨(S 0).1, (S 0).2, (S 1).1, (S 1).2⟩, fun F _ φ => ?_⟩
  have hP := nonsingular_map W ℓ hℓΔ φ hD.equation_P
  have hQ := nonsingular_map W ℓ hℓΔ φ hD.equation_Q
  have hΔφ := (field_data W ℓ hℓΔ φ).2
  have hS : ∀ j : Fin 2, pmap φ (S j) =
      ofPoint (W.map φ) (g 0 j • Point.some (φ D.xP) (φ D.yP) hP + g 1 j • Point.some (φ D.xQ) (φ D.yQ) hQ) := by
    intro j
    rw [map_linComb W ℓ hℓ3 hℓΔ D hD (val_le ℓ _) (val_le ℓ _) (hane j) φ]
    congr 2
    · exact (smul_eq_smul_of_dvd_sub (W.map φ) ℓ hℓ3 hΔφ hP (preΨ_map W ℓ φ hD.preΨ_P) (dvd_sub_val ℓ (g 0 j))).symm
    · exact (smul_eq_smul_of_dvd_sub (W.map φ) ℓ hℓ3 hΔφ hQ (preΨ_map W ℓ φ hD.preΨ_Q) (dvd_sub_val ℓ (g 1 j))).symm
  have h0 := hS 0
  have h1 := hS 1

  have hrel : LevelPData.relabel (W.map φ) g (D.map φ) =
      ⟨(ofPoint (W.map φ) (g 0 0 • Point.some (φ D.xP) (φ D.yP) hP + g 1 0 • Point.some (φ D.xQ) (φ D.yQ) hQ)).1,
       (ofPoint (W.map φ) (g 0 0 • Point.some (φ D.xP) (φ D.yP) hP + g 1 0 • Point.some (φ D.xQ) (φ D.yQ) hQ)).2,
       (ofPoint (W.map φ) (g 0 1 • Point.some (φ D.xP) (φ D.yP) hP + g 1 1 • Point.some (φ D.xQ) (φ D.yQ) hQ)).1,
       (ofPoint (W.map φ) (g 0 1 • Point.some (φ D.xP) (φ D.yP) hP + g 1 1 • Point.some (φ D.xQ) (φ D.yQ) hQ)).2⟩ := by
    show LevelPData.relabel (W.map φ) g ⟨φ D.xP, φ D.yP, φ D.xQ, φ D.yQ⟩ = _
    unfold LevelPData.relabel
    simp only [toPoint_of_nonsingular (W.map φ) hP, toPoint_of_nonsingular (W.map φ) hQ]
  rw [hrel, ← h0, ← h1]
  rfl

end Univ

end KatzRelabelUniv
p2m_reactivate "P2MW.S_ModularCurve_LevelP_exists_levelPData_map_eq_relabel_univData.KatzRelabelUniv"

theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) :
    ∃ R : ModularCurve.LevelPData (ModularCurve.LevelP.UnivBasisRing ℓ),
      ∀ (F : Type u) [Field F] (φ : ModularCurve.LevelP.UnivBasisRing ℓ →+* F),
        R.map φ = ModularCurve.LevelRelabelling.LevelPData.relabel ((ModularCurve.LevelP.univCurveT ℓ).map φ) g
          ((ModularCurve.LevelP.univData ℓ).map φ) :=
  KatzRelabelUniv.main ℓ hℓ3 g hg

end S_ModularCurve_LevelP_exists_levelPData_map_eq_relabel_univData
end P2MW
export P2MW.S_ModularCurve_LevelP_exists_levelPData_map_eq_relabel_univData (solution)
