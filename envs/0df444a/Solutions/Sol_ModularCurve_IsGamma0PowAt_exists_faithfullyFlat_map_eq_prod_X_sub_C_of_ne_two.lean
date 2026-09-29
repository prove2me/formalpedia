-- Prove2me | solution 1 for ModularCurve.IsGamma0PowAt.exists_faithfullyFlat_map_eq_prod_X_sub_C_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/82ca99d1-8192-58c8-8eb5-78d7483e4c28

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsGamma0PowAt_exists_faithfullyFlat_map_eq_prod_X_sub_C_of_ne_two
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

open Polynomial

namespace KernelSplit

noncomputable def quadAt {A : Type u} [CommRing A] (W : WeierstrassCurve A) (x : A) : A[X] :=
  X ^ 2 + (C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))

theorem monic_quadAt {A : Type u} [CommRing A] [Nontrivial A] (W : WeierstrassCurve A) (x : A) : (quadAt W x).Monic := by
  unfold quadAt
  refine (monic_X_pow 2).add_of_left ?_
  rw [degree_X_pow]
  refine (degree_sub_le _ _).trans_lt ?_
  rw [max_lt_iff]
  exact ⟨(degree_C_mul_X_le _).trans_lt (by norm_num), degree_C_le.trans_lt (by norm_num)⟩

theorem natDegree_quadAt {A : Type u} [CommRing A] [Nontrivial A] (W : WeierstrassCurve A) (x : A) :
    (quadAt W x).natDegree = 2 := by
  unfold quadAt
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  refine (degree_sub_le _ _).trans_lt ?_
  rw [max_lt_iff]
  exact ⟨(degree_C_mul_X_le _).trans_lt (by norm_num), degree_C_le.trans_lt (by norm_num)⟩

theorem eq_of_eval₂_quad {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (b c : A) (y : B)
    (h : (X ^ 2 + (C b * X - C c)).eval₂ f y = 0) : y ^ 2 + f b * y - f c = 0 := by
  rw [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X, eval₂_C] at h
  linear_combination h

theorem equation_root_quadAt {A : Type u} [CommRing A] (W : WeierstrassCurve A) (x : A) :
    (W.map (algebraMap A (AdjoinRoot (quadAt W x)))).toAffine.Equation
      (algebraMap A (AdjoinRoot (quadAt W x)) x) (AdjoinRoot.root (quadAt W x)) := by
  have h := eq_of_eval₂_quad (AdjoinRoot.of (quadAt W x)) (W.a₁ * x + W.a₃) (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    (AdjoinRoot.root (quadAt W x)) (AdjoinRoot.eval₂_root (quadAt W x))
  rw [← AdjoinRoot.algebraMap_eq] at h
  simp only [map_add, map_mul, map_pow] at h
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆]
  linear_combination h

theorem hom_eval {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (p : R[X]) (a : R) :
    (p.map f).eval (f a) = f (p.eval a) := by
  rw [eval_map, eval₂_at_apply]

theorem nontrivial_adjoinRoot {A : Type u} [CommRing A] [Nontrivial A] {g : A[X]} (hg : g.Monic) (hd : 0 < g.natDegree) :
    Nontrivial (AdjoinRoot g) := by
  let b := (AdjoinRoot.powerBasis' hg).basis
  have hdim : 0 < (AdjoinRoot.powerBasis' hg).dim := by rw [AdjoinRoot.powerBasis'_dim]; exact hd
  exact nontrivial_of_ne (b ⟨0, hdim⟩) 0 (b.ne_zero _)

theorem split : ∀ (d : ℕ) {A : Type u} [CommRing A] [Nontrivial A] (W : WeierstrassCurve A) (g : A[X]),
    g.Monic → g.natDegree = d → g.Separable →
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra A S) (_ : Module.FaithfullyFlat A S) (_ : Nontrivial S)
      (x y : Fin d → S),
      (∀ i, (W.map (algebraMap A S)).toAffine.Equation (x i) (y i)) ∧
      g.map (algebraMap A S) = ∏ i, (X - C (x i)) ∧
      (∀ i j, i ≠ j → IsUnit (x i - x j)) := by
  intro d
  induction d with
  | zero =>
    intro A _ _ W g hg hdeg hsep
    have hg1 : g = 1 := eq_one_of_monic_natDegree_zero hg hdeg
    refine ⟨A, inferInstance, Algebra.id A, inferInstance, inferInstance, Fin.elim0, Fin.elim0, fun i => i.elim0, ?_, fun i => i.elim0⟩
    rw [hg1, Polynomial.map_one, Fin.prod_univ_zero]
  | succ d ih =>
    intro A _ _ W g hg hdeg hsep

    haveI : Nontrivial (AdjoinRoot g) := nontrivial_adjoinRoot hg (by omega)
    haveI : Module.Free A (AdjoinRoot g) := hg.free_adjoinRoot
    haveI : Module.FaithfullyFlat A (AdjoinRoot g) := inferInstance
    set A₁ : Type u := AdjoinRoot g with hA₁
    set ξ : AdjoinRoot g := AdjoinRoot.root g with hξ
    have hroot : (g.map (algebraMap A (AdjoinRoot g))).IsRoot ξ := by
      rw [AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.isRoot_root g
    set g₁ : (AdjoinRoot g)[X] := g.map (algebraMap A (AdjoinRoot g)) /ₘ (X - C ξ) with hg₁def
    have hfac : (X - C ξ) * g₁ = g.map (algebraMap A (AdjoinRoot g)) := mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hgm : (g.map (algebraMap A (AdjoinRoot g))).Monic := hg.map _
    have hg₁ : g₁.Monic := Monic.of_mul_monic_left (monic_X_sub_C ξ) (by rw [hfac]; exact hgm)
    have hdeg₁ : g₁.natDegree = d := by
      rw [hg₁def, natDegree_divByMonic _ (monic_X_sub_C ξ), hg.natDegree_map, hdeg, natDegree_X_sub_C]; rfl
    have hsepm : (g.map (algebraMap A (AdjoinRoot g))).Separable := hsep.map
    have hsep₁ : g₁.Separable := hsepm.of_dvd ⟨X - C ξ, by rw [mul_comm, hfac]⟩
    have hcop : IsCoprime (X - C ξ) g₁ := by rw [← hfac] at hsepm; exact hsepm.isCoprime
    have hunit₁ : IsUnit (g₁.eval ξ) := by
      obtain ⟨u, v, huv⟩ := hcop
      have := congrArg (eval ξ) huv
      simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero, zero_add, eval_one] at this
      exact isUnit_iff_exists_inv.mpr ⟨v.eval ξ, by rw [mul_comm]; exact this⟩

    set q : (AdjoinRoot g)[X] := quadAt (W.map (algebraMap A (AdjoinRoot g))) ξ with hqdef
    have hq : q.Monic := monic_quadAt _ _
    haveI : Nontrivial (AdjoinRoot q) := nontrivial_adjoinRoot hq (by rw [hqdef, natDegree_quadAt]; norm_num)
    haveI : Module.Free (AdjoinRoot g) (AdjoinRoot q) := hq.free_adjoinRoot
    haveI : Module.FaithfullyFlat (AdjoinRoot g) (AdjoinRoot q) := inferInstance
    haveI : Module.FaithfullyFlat A (AdjoinRoot q) := Module.FaithfullyFlat.trans A (AdjoinRoot g) (AdjoinRoot q)
    have halg₂ : algebraMap A (AdjoinRoot q) = (algebraMap (AdjoinRoot g) (AdjoinRoot q)).comp (algebraMap A (AdjoinRoot g)) :=
      IsScalarTower.algebraMap_eq A (AdjoinRoot g) (AdjoinRoot q)
    set ξ₂ : AdjoinRoot q := algebraMap (AdjoinRoot g) (AdjoinRoot q) ξ with hξ₂
    set η : AdjoinRoot q := AdjoinRoot.root q with hη
    have heq₂ : (W.map (algebraMap A (AdjoinRoot q))).toAffine.Equation ξ₂ η := by
      have := equation_root_quadAt (W.map (algebraMap A (AdjoinRoot g))) ξ
      rw [WeierstrassCurve.map_map, ← halg₂] at this
      exact this
    set g₂ : (AdjoinRoot q)[X] := g₁.map (algebraMap (AdjoinRoot g) (AdjoinRoot q)) with hg₂def
    have hg₂ : g₂.Monic := hg₁.map _
    have hdeg₂ : g₂.natDegree = d := by rw [hg₂def, hg₁.natDegree_map, hdeg₁]
    have hsep₂ : g₂.Separable := hsep₁.map

    obtain ⟨S, instS, algS, ffS, ntS, x', y', hE', hP', hU'⟩ := ih (W.map (algebraMap A (AdjoinRoot q))) g₂ hg₂ hdeg₂ hsep₂
    letI : Algebra A S := ((algebraMap (AdjoinRoot q) S).comp (algebraMap A (AdjoinRoot q))).toAlgebra
    haveI : IsScalarTower A (AdjoinRoot q) S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Module.FaithfullyFlat A S := Module.FaithfullyFlat.trans A (AdjoinRoot q) S
    have halgS : algebraMap A S = (algebraMap (AdjoinRoot q) S).comp (algebraMap A (AdjoinRoot q)) := rfl
    have hWS : (W.map (algebraMap A (AdjoinRoot q))).map (algebraMap (AdjoinRoot q) S) = W.map (algebraMap A S) := by
      rw [WeierstrassCurve.map_map, ← halgS]
    set x₀ : S := algebraMap (AdjoinRoot q) S ξ₂ with hx₀
    set y₀ : S := algebraMap (AdjoinRoot q) S η with hy₀

    have hev : (g₂.map (algebraMap (AdjoinRoot q) S)).eval x₀ = ∏ j, (x₀ - x' j) := by
      rw [hP', eval_prod]
      simp only [eval_sub, eval_X, eval_C]
    have hunit₀ : IsUnit (∏ j, (x₀ - x' j)) := by
      rw [← hev, hx₀, hom_eval, hg₂def, hξ₂, hom_eval]
      exact (hunit₁.map _).map _
    refine ⟨S, instS, inferInstance, inferInstance, ntS, Fin.cons x₀ x', Fin.cons y₀ y', ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        have := heq₂.map (algebraMap (AdjoinRoot q) S)
        change ((W.map (algebraMap A (AdjoinRoot q))).map (algebraMap (AdjoinRoot q) S)).toAffine.Equation _ _ at this
        rw [hWS] at this
        exact this
      · simp only [Fin.cons_succ]
        have := hE' j
        rw [hWS] at this
        exact this
    · rw [halgS, ← Polynomial.map_map, halg₂, ← Polynomial.map_map, ← hfac, Polynomial.map_mul, Polynomial.map_mul,
        Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_X, Polynomial.map_C, Polynomial.map_C,
        ← hg₂def, hP', Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rfl
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;> intro hij
      · exact absurd rfl hij
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => x₀ - x' j) (Finset.mem_univ j')) hunit₀
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [← neg_sub]
        exact (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => x₀ - x' j) (Finset.mem_univ i')) hunit₀).neg
      · simp only [Fin.cons_succ]
        exact hU' i' j' (fun h => hij (by rw [h]))

end KernelSplit

open KernelSplit in
theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (p k : ℕ) [Fact p.Prime] (hp : IsUnit ((p : ℕ) : T)) (hp2 : p ≠ 2) (h : Polynomial T)
    (hh : ModularCurve.IsGamma0PowAt W p k h) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra T S) (_ : Module.FaithfullyFlat T S)
      (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (x y : ι → S),
      (∀ i, (W.map (algebraMap T S)).toAffine.Equation (x i) (y i)) ∧
      h.map (algebraMap T S) = ∏ i, (Polynomial.X - Polynomial.C (x i)) ∧
      (∀ i j, i ≠ j → IsUnit (x i - x j)) := by
  classical
  have hpp : p.Prime := Fact.out
  have hodd : Odd p := hpp.odd_of_ne_two hp2
  have hpk2 : p ^ k ≠ 2 := by
    intro h2
    have : Odd (p ^ k) := hodd.pow
    rw [h2] at this
    exact absurd this (by decide)
  have hck : W.IsCyclicGenKernel p k h := (ModularCurve.isGamma0PowAt_of_pow_ne_two W hpk2 h).mp hh
  have hmon : h.Monic := hck.monic

  have hdvd : h ∣ W.preΨ' (p ^ k) := by
    have := hck.mul_preΨ_dvd
    have e : W.preΨ ((p : ℤ) ^ k) = W.preΨ' (p ^ k) := by rw [← Nat.cast_pow]; exact WeierstrassCurve.preΨ_ofNat W (p ^ k)
    rw [e] at this
    exact dvd_trans (dvd_mul_right h _) this
  have hsepΨ : (W.preΨ' (p ^ k)).Separable :=
    WeierstrassCurve.separable_prePsi_of_isUnit W hodd.pow (by rw [Nat.cast_pow]; exact (hp.pow k).mul hΔ)
  have hsep : h.Separable := hsepΨ.of_dvd hdvd
  rcases subsingleton_or_nontrivial T with hT | hT
  ·
    refine ⟨T, inferInstance, Algebra.id T, inferInstance, Fin 0, inferInstance, inferInstance, Fin.elim0, Fin.elim0,
      fun i => i.elim0, Subsingleton.elim _ _, fun i => i.elim0⟩
  · obtain ⟨S, instS, algS, ffS, ntS, x, y, hE, hP, hU⟩ := split h.natDegree W h hmon rfl hsep
    exact ⟨S, instS, algS, ffS, Fin h.natDegree, inferInstance, inferInstance, x, y, hE, hP, hU⟩

end S_ModularCurve_IsGamma0PowAt_exists_faithfullyFlat_map_eq_prod_X_sub_C_of_ne_two
end P2MW
export P2MW.S_ModularCurve_IsGamma0PowAt_exists_faithfullyFlat_map_eq_prod_X_sub_C_of_ne_two (solution)
