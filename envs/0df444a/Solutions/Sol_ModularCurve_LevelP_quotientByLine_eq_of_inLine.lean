-- Prove2me | solution 1 for ModularCurve.LevelP.quotientByLine_eq_of_inLine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4b79cd8e-91d7-58b1-8279-44d56185a670

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPQuotient
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_ModularCurve_LevelP_quotientByLine_eq_veluQuotient_oddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit
import Theorems.Thm_Polynomial_isReduced_quotient_span_singleton_of_separable_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelP_quotientByLine_eq_of_inLine
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

noncomputable section

namespace CMPP4c

open WeierstrassCurve ModularCurve Polynomial

theorem eq_of_forall_algClosed {R : Type u} [CommRing R] [IsReduced R] {s t : R}
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (φ : R →+* K), φ s = φ t) : s = t := by
  rw [← sub_eq_zero]
  apply IsReduced.eq_zero (s - t)
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  let K := AlgebraicClosure (FractionRing (R ⧸ J))
  let φ : R →+* K := (algebraMap (R ⧸ J) K).comp (Ideal.Quotient.mk J)
  have hφ : φ (s - t) = 0 := by rw [map_sub, sub_eq_zero]; exact h K φ
  have hinj : Function.Injective (algebraMap (R ⧸ J) K) := by
    rw [IsScalarTower.algebraMap_eq (R ⧸ J) (FractionRing (R ⧸ J)) K]
    exact (algebraMap (FractionRing (R ⧸ J)) K).injective.comp
      (IsFractionRing.injective (R ⧸ J) (FractionRing (R ⧸ J)))
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply hinj
  rw [map_zero]
  exact hφ

theorem curve_eq_of_forall_algClosed {R : Type u} [CommRing R] [IsReduced R]
    {W₁ W₂ : WeierstrassCurve R}
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (φ : R →+* K), W₁.map φ = W₂.map φ) :
    W₁ = W₂ := by
  ext
  · exact eq_of_forall_algClosed fun K _ _ φ => by
      have := congrArg WeierstrassCurve.a₁ (h K φ); simpa only [map_a₁] using this
  · exact eq_of_forall_algClosed fun K _ _ φ => by
      have := congrArg WeierstrassCurve.a₂ (h K φ); simpa only [map_a₂] using this
  · exact eq_of_forall_algClosed fun K _ _ φ => by
      have := congrArg WeierstrassCurve.a₃ (h K φ); simpa only [map_a₃] using this
  · exact eq_of_forall_algClosed fun K _ _ φ => by
      have := congrArg WeierstrassCurve.a₄ (h K φ); simpa only [map_a₄] using this
  · exact eq_of_forall_algClosed fun K _ _ φ => by
      have := congrArg WeierstrassCurve.a₆ (h K φ); simpa only [map_a₆] using this

section Univ

variable (p : ℕ) [Fact p.Prime]

theorem genericCurve_Δ_ne_zero : (LevelP.genericCurve).Δ ≠ 0 := by
  intro h0
  let W₀ : WeierstrassCurve ℤ := ⟨0, 0, 1, 0, 0⟩
  have h1 := congrArg (LevelP.genericLift W₀) h0
  rw [← WeierstrassCurve.map_Δ, LevelP.genericCurve_map_genericLift, map_zero] at h1
  have h2 : W₀.Δ = -27 := by
    simp only [W₀, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    norm_num
  rw [h2] at h1
  norm_num at h1

theorem pDelta_ne_zero : LevelP.pDelta p ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) genericCurve_Δ_ne_zero

theorem isDomain_univBase : IsDomain (LevelP.UnivBase p) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers (LevelP.pDelta p))
    (LevelP.UnivBase p) (powers_le_nonZeroDivisors_of_noZeroDivisors (pDelta_ne_zero p))

abbrev U : Type := LevelP.PsiRoot (LevelP.univCurve p) p

abbrev 𝒲 : WeierstrassCurve (U p) :=
  (LevelP.univCurve p).map (LevelP.PsiRoot.ofBase (LevelP.univCurve p) p)

abbrev ξ : U p := LevelP.psiRootX (LevelP.univCurve p) p

omit [Fact p.Prime] in
theorem eval_preΨ_ξ : ((𝒲 p).preΨ p).eval (ξ p) = 0 := by
  rw [WeierstrassCurve.map_preΨ, Polynomial.eval_map]
  exact LevelP.preΨ_eval₂_psiRootX (LevelP.univCurve p) p

omit [Fact p.Prime] in
theorem isUnit_p_mul_Δ_𝒲 : IsUnit ((p : U p) * (𝒲 p).Δ) := by
  have h := (LevelP.isUnit_natCast_mul_Δ_univCurve p).map
    (LevelP.PsiRoot.ofBase (LevelP.univCurve p) p)
  rwa [map_mul, map_natCast, ← WeierstrassCurve.map_Δ] at h

theorem isReduced_U (hp2 : p ≠ 2) : IsReduced (U p) := by
  haveI : IsDomain (LevelP.UnivBase p) := isDomain_univBase p
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  set D := LevelP.UnivBase p
  set ψ : D[X] := (LevelP.univCurve p).preΨ p with hψ
  have hpu : IsUnit (p : D) := LevelP.isUnit_natCast_univBase p
  have hp0 : (p : D) ≠ 0 := hpu.ne_zero
  set c : D := ↑hpu.unit⁻¹ with hcdef
  have hc : c * (p : D) = 1 := hpu.val_inv_mul
  have hcu : IsUnit c := Units.isUnit _

  set g : D[X] := C c * ψ with hg
  have hlead : ψ.leadingCoeff = p := by
    rw [hψ, WeierstrassCurve.preΨ_ofNat, WeierstrassCurve.leadingCoeff_preΨ' _ hp0,
      if_neg (Nat.not_even_iff_odd.mpr hodd)]
  have hmonic : g.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hlead, hc])
  have hsep : (g.map (algebraMap D (FractionRing D))).Separable := by
    rw [hg, Polynomial.map_mul, Polynomial.map_C, hψ, WeierstrassCurve.preΨ_ofNat,
      ← WeierstrassCurve.map_preΨ']
    refine Separable.unit_mul (Polynomial.isUnit_C.mpr (hcu.map _)) ?_
    refine WeierstrassCurve.separable_prePsi_of_isUnit _ hodd ?_
    have h := (LevelP.isUnit_natCast_mul_Δ_univCurve p).map (algebraMap D (FractionRing D))
    rwa [map_mul, map_natCast, ← WeierstrassCurve.map_Δ] at h
  have hred : IsReduced (D[X] ⧸ Ideal.span {g}) :=
    Polynomial.isReduced_quotient_span_singleton_of_separable_map hmonic hsep
  have hspan : (Ideal.span {ψ} : Ideal D[X]) = Ideal.span {g} := by
    rw [hg, Ideal.span_singleton_mul_left_unit (Polynomial.isUnit_C.mpr hcu)]
  exact isReduced_of_injective (Ideal.quotEquivOfEq hspan).toRingHom
    (Ideal.quotEquivOfEq hspan).injective

end Univ

section FieldPart

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

omit [DecidableEq F] in
theorem smulX_eq_div (a : ℤ) (x : F) :
    LevelP.smulX W a x = (W.Φ a).eval x / (W.ΨSq a).eval x := by
  rw [LevelP.smulX, Ring.inverse_eq_inv, div_eq_mul_inv]

omit [DecidableEq F] in

theorem exists_equation [IsAlgClosed F] (W : WeierstrassCurve F) (x : F) :
    ∃ y, W.toAffine.Equation x y := by
  let q : F[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  have hq : q.degree = 2 := by
    simp only [q]
    compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hq]; norm_num)
  refine ⟨y, ?_⟩
  rw [Affine.equation_iff]
  simp only [q, IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hy
  linear_combination hy

theorem addOrderOf_eq_of_prime {p : ℕ} [Fact p.Prime] {Q : W.toAffine.Point} (hQ : p • Q = 0)
    (hQ0 : Q ≠ 0) : addOrderOf Q = p := by
  have h1 : addOrderOf Q ∣ p := addOrderOf_dvd_of_nsmul_eq_zero hQ
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h1 with h | h
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hQ0
  · exact h

theorem addOrderOf_nsmul_eq {p : ℕ} [Fact p.Prime] {Q : W.toAffine.Point} (hQ : addOrderOf Q = p)
    {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p) : addOrderOf (a • Q) = p := by
  refine addOrderOf_eq_of_prime ?_ ?_
  · rw [smul_smul, mul_comm, ← smul_smul, ← hQ, addOrderOf_nsmul_eq_zero, smul_zero]
  · exact nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; exact hap)

theorem nsmul_eq_some_smulX {p : ℕ} {x y : F} (h : W.toAffine.Nonsingular x y)
    (hQ : addOrderOf (Affine.Point.some x y h) = p) {k : ℕ} (hk : k ∈ Finset.Icc 1 ((p - 1) / 2)) :
    ∃ (y' : F) (h' : W.toAffine.Nonsingular (LevelP.smulX W k x) y'),
      k • Affine.Point.some x y h = Affine.Point.some (LevelP.smulX W k x) y' h' := by
  rw [Finset.mem_Icc] at hk
  have hne : k • Affine.Point.some x y h ≠ 0 :=
    nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  have hψ : (W.ψ k).evalEval x y ≠ 0 := by
    rw [Ne, ← Affine.Point.smul_some_eq_zero_iff W h (k : ℤ), natCast_zsmul]
    exact hne
  obtain ⟨y', h', e⟩ := Affine.Point.zsmul_some_eq_some_div W h hψ
  rw [natCast_zsmul] at e
  rw [smulX_eq_div]
  exact ⟨y', h', e⟩

omit [DecidableEq F] in

theorem eq_of_coordsOrZero_eq {P P' : W.toAffine.Point} (hP : P ≠ 0) (hP' : P' ≠ 0)
    (h : P.coordsOrZero = P'.coordsOrZero) : P = P' := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd rfl hP
  rcases P' with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hP'
  rw [Affine.Point.coordsOrZero_some, Affine.Point.coordsOrZero_some, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem injOn_coordsOrZero_nsmul {p : ℕ} {Q : W.toAffine.Point} (hQ : addOrderOf Q = p) :
    Set.InjOn (fun k : ℕ => (k • Q).coordsOrZero) (Finset.Icc 1 ((p - 1) / 2) : Finset ℕ) := by
  intro k hk k' hk' hkk'
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'
  have hne : k • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  have hne' : k' • Q ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  have hpt : k • Q = k' • Q := eq_of_coordsOrZero_eq hne hne' hkk'
  rw [nsmul_inj_mod, hQ, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hpt
  exact hpt

def tPt (W : WeierstrassCurve F) (P : W.toAffine.Point) : F := W.veluT P.coordsOrZero.1 P.coordsOrZero.2

def wPt (W : WeierstrassCurve F) (P : W.toAffine.Point) : F := W.veluW P.coordsOrZero.1 P.coordsOrZero.2

omit [DecidableEq F] in
theorem tPt_neg (P : W.toAffine.Point) : tPt W (-P) = tPt W P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]
    simp only [tPt, Affine.Point.coordsOrZero_some, veluT_negY]

omit [DecidableEq F] in
theorem wPt_neg (P : W.toAffine.Point) : wPt W (-P) = wPt W P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]
    simp only [wPt, Affine.Point.coordsOrZero_some, veluW_negY]

theorem veluTSum_oddOrderSummingSet {p : ℕ} {Q : W.toAffine.Point} (hQ : addOrderOf Q = p) :
    W.veluTSum (W.oddOrderSummingSet Q ((p - 1) / 2)) =
      ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), tPt W (k • Q) := by
  rw [veluTSum, oddOrderSummingSet, Finset.sum_image (injOn_coordsOrZero_nsmul hQ)]
  rfl

theorem veluWSum_oddOrderSummingSet {p : ℕ} {Q : W.toAffine.Point} (hQ : addOrderOf Q = p) :
    W.veluWSum (W.oddOrderSummingSet Q ((p - 1) / 2)) =
      ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), wPt W (k • Q) := by
  rw [veluWSum, oddOrderSummingSet, Finset.sum_image (injOn_coordsOrZero_nsmul hQ)]
  rfl

theorem sum_half_nsmul_mul {p : ℕ} [Fact p.Prime] {Q : W.toAffine.Point} (hQ : addOrderOf Q = p)
    {β : Type*} [AddCommMonoid β] (h : W.toAffine.Point → β) (heven : ∀ P, h (-P) = h P)
    {a : ℕ} (ha : ¬ p ∣ a) :
    ∑ k ∈ Finset.Ico 1 (p / 2).succ, h ((a * k) • Q) =
      ∑ k ∈ Finset.Ico 1 (p / 2).succ, h (k • Q) := by
  have hap : ((a : ZMod p)) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]

  have hfold : ∀ k ∈ Finset.Ico 1 (p / 2).succ,
      h ((a * k) • Q) = h ((((a : ZMod p) * k).valMinAbs.natAbs) • Q) := by
    intro k _
    set z : ZMod p := (a : ZMod p) * k with hz
    set m : ℕ := z.valMinAbs.natAbs with hm
    have hcast : (((a * k : ℕ) : ℤ) : ZMod p) = z := by simp [hz]
    have hzQ : z.valMinAbs • Q = (a * k) • Q := by
      rw [← natCast_zsmul Q (a * k), zsmul_eq_zsmul_iff_modEq, hQ, ← ZMod.intCast_eq_intCast_iff,
        ZMod.coe_valMinAbs, hcast]
    rcases Int.natAbs_eq z.valMinAbs with h1 | h1
    · rw [← hzQ, h1, ← hm, natCast_zsmul]
    · rw [← hzQ, h1, ← hm, neg_zsmul, natCast_zsmul, heven]
  rw [Finset.sum_congr rfl hfold, Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  have hmap : (Finset.Ico 1 (p / 2).succ).1.map
      (fun k : ℕ => h ((((a : ZMod p) * k).valMinAbs.natAbs) • Q)) =
      ((Finset.Ico 1 (p / 2).succ).1.map (fun k : ℕ => ((a : ZMod p) * k).valMinAbs.natAbs)).map
        (fun m : ℕ => h (m • Q)) := by
    rw [Multiset.map_map]
    rfl
  rw [hmap, ZMod.Ico_map_valMinAbs_natAbs_eq_Ico_map_id p (a : ZMod p) hap, Multiset.map_map]
  rfl

theorem veluQuotient_oddOrderSummingSet_nsmul {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Q : W.toAffine.Point} (hQ : addOrderOf Q = p) {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ (p - 1) / 2) :
    W.veluQuotient (W.oddOrderSummingSet (a • Q) ((p - 1) / 2)) =
      W.veluQuotient (W.oddOrderSummingSet Q ((p - 1) / 2)) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hp1 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hap : a < p := by
    have : (p - 1) / 2 < p := by omega
    omega
  have hpa : ¬ p ∣ a := fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hIcc : Finset.Icc 1 ((p - 1) / 2) = Finset.Ico 1 (p / 2).succ := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    obtain ⟨m, rfl⟩ := hodd
    omega
  have haQ : addOrderOf (a • Q) = p := addOrderOf_nsmul_eq hQ ha1 hap
  have hT : W.veluTSum (W.oddOrderSummingSet (a • Q) ((p - 1) / 2)) =
      W.veluTSum (W.oddOrderSummingSet Q ((p - 1) / 2)) := by
    rw [veluTSum_oddOrderSummingSet haQ, veluTSum_oddOrderSummingSet hQ, hIcc]
    have e : ∀ k ∈ Finset.Ico 1 (p / 2).succ, tPt W (k • a • Q) = tPt W ((a * k) • Q) := by
      intro k _; rw [smul_smul, mul_comm]
    rw [Finset.sum_congr rfl e]
    exact sum_half_nsmul_mul hQ (tPt W) tPt_neg hpa
  have hW' : W.veluWSum (W.oddOrderSummingSet (a • Q) ((p - 1) / 2)) =
      W.veluWSum (W.oddOrderSummingSet Q ((p - 1) / 2)) := by
    rw [veluWSum_oddOrderSummingSet haQ, veluWSum_oddOrderSummingSet hQ, hIcc]
    have e : ∀ k ∈ Finset.Ico 1 (p / 2).succ, wPt W (k • a • Q) = wPt W ((a * k) • Q) := by
      intro k _; rw [smul_smul, mul_comm]
    rw [Finset.sum_congr rfl e]
    exact sum_half_nsmul_mul hQ (wPt W) wPt_neg hpa
  ext
  · rfl
  · rfl
  · rfl
  · rw [veluQuotient_a₄, veluQuotient_a₄, hT]
  · rw [veluQuotient_a₆, veluQuotient_a₆, hT, hW']

theorem quotientByLine_smulX_field [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {x : F} (hx : (W.preΨ p).eval x = 0)
    {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ (p - 1) / 2) :
    LevelP.quotientByLine W p (LevelP.smulX W a x) = LevelP.quotientByLine W p x := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨y, hxy⟩ := exists_equation W x
  have hns : W.toAffine.Nonsingular x y := (Affine.equation_iff_nonsingular).mp hxy
  have hpQ : p • Affine.Point.some x y hns = 0 := by
    rw [WeierstrassCurve.preΨ_ofNat] at hx
    exact (Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd hns).mpr hx
  have hord : addOrderOf (Affine.Point.some x y hns) = p :=
    addOrderOf_eq_of_prime hpQ (Affine.Point.some_ne_zero hns)
  obtain ⟨y', h', e⟩ := nsmul_eq_some_smulX hns hord (k := a) (Finset.mem_Icc.mpr ⟨ha1, ha2⟩)
  have hap : a < p := by
    have : (p - 1) / 2 < p := by have := (Fact.out : p.Prime).ne_zero; omega
    omega
  have hord' : addOrderOf (Affine.Point.some (LevelP.smulX W a x) y' h') = p := by
    rw [← e]; exact addOrderOf_nsmul_eq hord ha1 hap
  rw [ModularCurve.LevelP.quotientByLine_eq_veluQuotient_oddOrderSummingSet W hodd h' hord',
    ModularCurve.LevelP.quotientByLine_eq_veluQuotient_oddOrderSummingSet W hodd hns hord, ← e]
  exact veluQuotient_oddOrderSummingSet_nsmul hp2 hord ha1 ha2

end FieldPart

section Assembly

variable (p : ℕ) [Fact p.Prime]

theorem not_dvd_of_mem_Icc {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ (p - 1) / 2) : ¬ (p : ℤ) ∣ a := by
  intro hd
  have hd' : p ∣ a := Int.natCast_dvd_natCast.mp hd
  have hp := (Fact.out : p.Prime).two_le
  have := Nat.le_of_dvd (by omega) hd'
  omega

theorem isUnit_ΨSq_of_mem {A : Type*} [CommRing A] (W : WeierstrassCurve A) (hp2 : p ≠ 2)
    (hW : IsUnit ((p : A) * W.Δ)) {x : A} (hx : (W.preΨ p).eval x = 0) :
    ∀ b ∈ Finset.Icc 1 ((p - 1) / 2), IsUnit ((W.ΨSq b).eval x) := by
  intro b hb
  rw [Finset.mem_Icc] at hb
  exact (WeierstrassCurve.eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero W hp2 hW hx
    (not_dvd_of_mem_Icc p hb.1 hb.2)).1

theorem quotientByLine_smulX_univ (hp2 : p ≠ 2) {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ (p - 1) / 2) :
    LevelP.quotientByLine (𝒲 p) p (LevelP.smulX (𝒲 p) a (ξ p)) =
      LevelP.quotientByLine (𝒲 p) p (ξ p) := by
  haveI : IsReduced (U p) := isReduced_U p hp2
  have hU := isUnit_p_mul_Δ_𝒲 p
  have hξ := eval_preΨ_ξ p
  have hfa := WeierstrassCurve.eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero (𝒲 p)
    hp2 hU hξ (not_dvd_of_mem_Icc p ha1 ha2)

  have hξ' : ((𝒲 p).preΨ p).eval (LevelP.smulX (𝒲 p) a (ξ p)) = 0 := hfa.2
  refine curve_eq_of_forall_algClosed fun K _ _ κ => ?_
  classical
  rw [LevelP.quotientByLine_map _ _ _ κ (isUnit_ΨSq_of_mem p (𝒲 p) hp2 hU hξ'),
    LevelP.quotientByLine_map _ _ _ κ (isUnit_ΨSq_of_mem p (𝒲 p) hp2 hU hξ),
    LevelP.map_smulX (𝒲 p) κ hfa.1]

  have hK : IsUnit ((p : K) * ((𝒲 p).map κ).Δ) := by
    have h := hU.map κ
    rwa [map_mul, map_natCast, ← WeierstrassCurve.map_Δ] at h
  haveI : ((𝒲 p).map κ).IsElliptic := ⟨isUnit_of_mul_isUnit_right hK⟩
  have hxK : (((𝒲 p).map κ).preΨ p).eval (κ (ξ p)) = 0 := by
    rw [WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply, hξ, map_zero]
  exact quotientByLine_smulX_field ((𝒲 p).map κ) hp2 hxK ha1 ha2

end Assembly

end CMPP4c

end

open WeierstrassCurve ModularCurve CMPP4c in
theorem solution
    {A : Type u} [CommRing A] (W : WeierstrassCurve A) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hW : IsUnit ((p : A) * W.Δ)) {x x' : A} (hx : (W.preΨ p).eval x = 0)
    (h : ModularCurve.InLine W p x x') :
    ModularCurve.LevelP.quotientByLine W p x' = ModularCurve.LevelP.quotientByLine W p x := by
  obtain ⟨a, ha1, ha2, hxa⟩ := h

  let φ₀ : LevelP.UnivBase p →+* A := LevelP.UnivBase.lift p W hW
  have hφ₀ : (LevelP.univCurve p).map φ₀ = W := LevelP.univCurve_map_lift p W hW
  have hx₀ : (((LevelP.univCurve p).map φ₀).preΨ p).eval x = 0 := by rw [hφ₀]; exact hx
  let Φ : U p →+* A := LevelP.PsiRoot.lift (LevelP.univCurve p) p φ₀ x hx₀
  have hΦξ : Φ (ξ p) = x := LevelP.PsiRoot.lift_psiRootX (LevelP.univCurve p) p φ₀ x hx₀
  have hΦ𝒲 : (𝒲 p).map Φ = W := by
    rw [WeierstrassCurve.map_map]
    have hc : Φ.comp (LevelP.PsiRoot.ofBase (LevelP.univCurve p) p) = φ₀ :=
      RingHom.ext fun b => LevelP.PsiRoot.lift_ofBase (LevelP.univCurve p) p φ₀ x hx₀ b
    rw [hc, hφ₀]

  have hU := isUnit_p_mul_Δ_𝒲 p
  have hξ := eval_preΨ_ξ p
  have hfa := WeierstrassCurve.eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero (𝒲 p)
    hp2 hU hξ (not_dvd_of_mem_Icc p ha1 ha2)
  have hξ' : ((𝒲 p).preΨ p).eval (LevelP.smulX (𝒲 p) a (ξ p)) = 0 := hfa.2
  have hfaA := WeierstrassCurve.eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero W
    hp2 hW hx (not_dvd_of_mem_Icc p ha1 ha2)

  have hx' : x' = LevelP.smulX W a x := by
    rw [LevelP.smulX, ← hxa, mul_assoc, Ring.mul_inverse_cancel _ hfaA.1, mul_one]

  have key := congrArg (fun V => WeierstrassCurve.map V Φ) (quotientByLine_smulX_univ p hp2 ha1 ha2)
  rw [LevelP.quotientByLine_map _ _ _ Φ (isUnit_ΨSq_of_mem p (𝒲 p) hp2 hU hξ'),
    LevelP.quotientByLine_map _ _ _ Φ (isUnit_ΨSq_of_mem p (𝒲 p) hp2 hU hξ),
    LevelP.map_smulX (𝒲 p) Φ hfa.1, hΦ𝒲, hΦξ] at key
  rw [hx']
  exact key

end S_ModularCurve_LevelP_quotientByLine_eq_of_inLine
end P2MW
export P2MW.S_ModularCurve_LevelP_quotientByLine_eq_of_inLine (solution)
