-- Prove2me | solution 1 for OAI.MaximalSeshadri.BertiniIntegral.etale_generic_hyperplane_section_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:11:56.673221+00:00
-- url     : https://prove2.me/submissions/ac9dc8b2-24f5-44be-aef8-9d67c7c1d610

import Mathlib
import Definitions.Def_Q223SES003
import Definitions.Def_Q223SES004

section
-- module Solutions.Q223_SES.Seshadri_Bertini_LinearForms
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [IsDomain R]

lemma linear_saturated (a b : R) (ha : a ≠ 0)
    (hab : ∀ r : R, a ∣ b * r → a ∣ r) (p : R[X])
    (h : C a * X + C b ∣ C a * p) : C a * X + C b ∣ p := by
  obtain ⟨q, hq⟩ := h
  have hbq : C a ∣ C b * q := by
    refine ⟨p - X * q, ?_⟩
    linear_combination -hq
  have haq : C a ∣ q := by
    rw [C_dvd_iff_dvd_coeff] at hbq ⊢
    intro n
    apply hab
    simpa only [coeff_C_mul] using hbq n
  obtain ⟨r, rfl⟩ := haq
  refine ⟨r, ?_⟩
  apply mul_left_cancel₀ (show C a ≠ 0 by simpa using ha)
  linear_combination hq

lemma linear_pow_saturated (a b : R) (ha : a ≠ 0)
    (hab : ∀ r : R, a ∣ b * r → a ∣ r) (n : ℕ) (p : R[X])
    (h : C a * X + C b ∣ (C a)^n * p) : C a * X + C b ∣ p := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply linear_saturated a b ha hab
    simpa only [pow_succ', mul_assoc] using h

theorem linear_ideal_isPrime (a b : R) (ha : a ≠ 0)
    (hab : ∀ r : R, a ∣ b * r → a ∣ r) :
    (Ideal.span {C a * X + C b} : Ideal R[X]).IsPrime := by
  let S := Localization.Away a
  let : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors
    S (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr ha))
  let : Algebra R[X] S[X] := Polynomial.algebra R S
  let M := (Submonoid.powers a).map (C : R →+* R[X])
  let : IsLocalization M S[X] := Polynomial.isLocalization _ _
  let J : Ideal R[X] := Ideal.span {C a * X + C b}
  let u : Sˣ := (IsLocalization.Away.algebraMap_isUnit (S := S) a).unit
  let z : S := -(↑u⁻¹) * algebraMap R S b
  have hu : (u : S) = algebraMap R S a := IsUnit.unit_spec _
  have he : algebraMap R[X] S[X] (C a * X + C b) =
      C (u : S) * (X - C z) := by
    change Polynomial.map (algebraMap R S) (C a * X + C b) = _
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, map_X]
    rw [← hu]
    rw [mul_sub, ← Polynomial.C_mul]
    have huz : (u : S) * z = -(algebraMap R S b) := by
      dsimp only [z]
      calc
        (u : S) * (-(↑u⁻¹) * algebraMap R S b) =
            -((u : S) * ↑u⁻¹) * algebraMap R S b := by ring
        _ = -(algebraMap R S b) := by simp <;> ring
    rw [huz, Polynomial.C_neg, sub_neg_eq_add]
  have hmap : J.map (algebraMap R[X] S[X]) = Ideal.span {X - C z} := by
    dsimp only [J]
    rw [Ideal.map_span, Set.image_singleton, he]
    exact Ideal.span_singleton_mul_left_unit (u.isUnit.map C) _
  have hprime : (J.map (algebraMap R[X] S[X])).IsPrime := by
    rw [hmap, ← Polynomial.ker_evalRingHom]
    exact RingHom.ker_isPrime (Polynomial.evalRingHom z)
  have hcontract : (J.map (algebraMap R[X] S[X])).comap (algebraMap R[X] S[X]) = J := by
    apply le_antisymm _ Ideal.le_comap_map
    intro p hp
    obtain ⟨m, hm, hmp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M S[X] J p).mp hp
    obtain ⟨r, ⟨n, rfl⟩, rfl⟩ := hm
    rw [Ideal.mem_span_singleton] at hmp ⊢
    apply linear_pow_saturated a b ha hab n p
    simpa only [map_pow] using hmp
  change J.IsPrime
  rw [← hcontract]
  exact hprime.comap _

end

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped nonZeroDivisors
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ]

lemma separateLinearVariable_coeff_one (v : σ → R) (i : σ) :
    (separateLinearVariable (R := R) i (homogeneousLinearForm v)).coeff 1 = C (v i) := by
  classical
  simp only [homogeneousLinearForm, map_sum, map_mul, separateLinearVariable,
    AlgEquiv.trans_apply, renameEquiv_apply, rename_C, rename_X, optionEquivLeft_C]
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Equiv.optionSubtypeNe_symm_of_ne hji]
  · simp

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped nonZeroDivisors
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ]

lemma separateLinearVariable_eq (v : σ → R) (i : σ) :
    separateLinearVariable (R := R) i (homogeneousLinearForm v) =
      Polynomial.C (C (v i)) * Polynomial.X +
        Polynomial.C (homogeneousLinearForm (fun j : {j : σ // j ≠ i} => v j)) := by
  classical
  simp only [homogeneousLinearForm, map_sum, map_mul]
  rw [← Equiv.sum_comp (Equiv.optionSubtypeNe i)]
  rw [Fintype.sum_option]
  simp only [separateLinearVariable, AlgEquiv.trans_apply, renameEquiv_apply,
    rename_C, rename_X, optionEquivLeft_C, Equiv.optionSubtypeNe_symm_self,
    Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some, optionEquivLeft_X_none]
  apply congrArg (fun q : Polynomial (MvPolynomial {j : σ // j ≠ i} R) =>
    Polynomial.C (C (v i)) * Polynomial.X + q)
  apply Finset.sum_congr rfl
  intro j _
  rw [Equiv.optionSubtypeNe_symm_of_ne j.property, optionEquivLeft_X_some]

end
end MaximalSeshadri.BertiniIntegral


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_GenericHyperplanes
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped nonZeroDivisors
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ]

omit [Fintype σ] in
lemma mvC_nonZeroDivisor (a : R) (ha : a ∈ R⁰) : C (σ := σ) a ∈ (MvPolynomial σ R)⁰ := by
  apply mem_nonZeroDivisors_iff_right.mpr
  intro p hp
  ext d
  apply ha.1
  rw [mul_comm] at hp
  have hh := congrArg (fun polynomial : MvPolynomial σ R => polynomial.coeff d) hp
  simpa only [coeff_C_mul, MvPolynomial.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using hh

lemma homogeneousLinearForm_regular_of_coefficient (v : σ → R) (i : σ)
    (hi : v i ∈ R⁰) : homogeneousLinearForm v ∈ (MvPolynomial σ R)⁰ := by
  let e := separateLinearVariable (R := R) i
  have hreg : e (homogeneousLinearForm v) ∈
      (Polynomial (MvPolynomial {j : σ // j ≠ i} R))⁰ := by
    apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
    rw [separateLinearVariable_coeff_one]
    exact mvC_nonZeroDivisor _ hi
  apply mem_nonZeroDivisors_iff_right.mpr
  intro q hq
  apply e.injective
  rw [map_zero]
  apply hreg.2
  simpa only [map_mul, map_zero] using congrArg e hq

lemma quotient_regular_of_dvd (a b : R)
    (hab : ∀ r : R, a ∣ b * r → a ∣ r) :
    Ideal.Quotient.mk (Ideal.span {a}) b ∈ (R ⧸ Ideal.span {a})⁰ := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Ideal.mem_span_singleton]
  apply hab
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  exact hx

lemma linearForm_coefficient_saturated (a : R) (v : σ → R) (j : σ)
    (hab : ∀ r : R, a ∣ v j * r → a ∣ r)
    (p : MvPolynomial σ R) (hp : C a ∣ homogeneousLinearForm v * p) : C a ∣ p := by
  let I := Ideal.span ({a} : Set R)
  let m : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hm : map m (homogeneousLinearForm v * p) = 0 := by
    obtain ⟨q, hq⟩ := hp
    rw [hq]
    have hma : m a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)
    simp only [map_mul, map_C, hma, map_zero, zero_mul]
  have hq := homogeneousLinearForm_regular_of_coefficient (fun i => m (v i)) j
    (quotient_regular_of_dvd a (v j) hab)
  have hp0 : map m p = 0 := by
    apply hq.1
    simpa only [homogeneousLinearForm, map_mul, map_sum, map_C, map_X] using hm
  rw [C_dvd_iff_dvd_coeff]
  intro d
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hh := congrArg (fun polynomial : MvPolynomial σ (R ⧸ I) => polynomial.coeff d) hp0
  simpa only [coeff_map, MvPolynomial.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using hh

theorem homogeneousLinearForm_isPrime_of_regularPair [IsDomain R]
    (v : σ → R) (i j : σ) (hji : j ≠ i) (hi : v i ≠ 0)
    (hij : ∀ r : R, v i ∣ v j * r → v i ∣ r) :
    (Ideal.span {homogeneousLinearForm v} : Ideal (MvPolynomial σ R)).IsPrime := by
  let e := separateLinearVariable (R := R) i
  let J : Ideal (MvPolynomial σ R) := Ideal.span {homogeneousLinearForm v}
  have ha : C (σ := {j : σ // j ≠ i}) (v i) ≠ 0 := by simpa using hi
  have hprime : (J.map e.toRingHom).IsPrime := by
    rw [show J = Ideal.span {homogeneousLinearForm v} from rfl,
      Ideal.map_span, Set.image_singleton]
    change (Ideal.span {e (homogeneousLinearForm v)}).IsPrime
    rw [separateLinearVariable_eq]
    apply linear_ideal_isPrime _ _ ha
    intro p hp
    exact linearForm_coefficient_saturated (v i)
      (fun j : {j : σ // j ≠ i} => v j) ⟨j, hji⟩ hij p hp
  have hcon : (J.map e.toRingHom).comap e.toRingHom = J :=
    Ideal.comap_map_of_bijective _ e.bijective
  change J.IsPrime
  rw [← hcon]
  exact hprime.comap _

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {R A B σ : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

lemma mvPolynomialTensorTo_right (p : (MvPolynomial σ B)) :
    mvPolynomialTensorTo ((1 : (MvPolynomial σ A)) ⊗ₜ[(MvPolynomial σ R)] p) =
      mvPolynomialMapOver (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) p := by
  simp [mvPolynomialTensorTo]

@[simp] lemma mvPolynomialTensorEquiv_right (p : (MvPolynomial σ B)) :
    mvPolynomialTensorEquiv ((1 : (MvPolynomial σ A)) ⊗ₜ[(MvPolynomial σ R)] p) =
      mvPolynomialMapOver (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) p :=
  mvPolynomialTensorTo_right p

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial

theorem tensor_polynomial_relation {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra R[X] A] [IsScalarTower R R[X] A] :
    Nonempty (((A ⊗[R] A) ⧸ Ideal.span
      {algebraMap R[X] A X ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] algebraMap R[X] A X})
        ≃ₐ[R] (A ⊗[R[X]] A)) := by
  let a := algebraMap R[X] A X
  let T := A ⊗[R] A
  let D := A ⊗[R[X]] A
  let I : Ideal T := Ideal.span {a ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] a}
  let Q := T ⧸ I
  let q : T →ₐ[R] Q := Ideal.Quotient.mkₐ R I
  let l : A →ₐ[R] Q := q.comp Algebra.TensorProduct.includeLeft
  let r : A →ₐ[R] Q := q.comp Algebra.TensorProduct.includeRight
  have he : l a = r a := by
    apply sub_eq_zero.mp
    change q (a ⊗ₜ[R] 1) - q (1 ⊗ₜ[R] a) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hp : l.toRingHom.comp (algebraMap R[X] A) =
      r.toRingHom.comp (algebraMap R[X] A) := by
    apply Polynomial.ringHom_ext
    · intro z
      change l (algebraMap R[X] A (C z)) = r (algebraMap R[X] A (C z))
      change l (algebraMap R[X] A (algebraMap R R[X] z)) =
        r (algebraMap R[X] A (algebraMap R R[X] z))
      rw [← IsScalarTower.algebraMap_apply]
      rw [l.commutes, r.commutes]
    · exact he
  let lp : A →ₐ[R[X]] Q := ⟨l.toRingHom, fun _ => rfl⟩
  let rp : A →ₐ[R[X]] Q := ⟨r.toRingHom, fun z => (DFunLike.congr_fun hp z).symm⟩
  let g : D →ₐ[R] Q := (Algebra.TensorProduct.lift lp rp
    (fun _ _ => Commute.all _ _)).restrictScalars R
  let dl : A →ₐ[R] D := (Algebra.TensorProduct.includeLeft : A →ₐ[R[X]] D).restrictScalars R
  let dr : A →ₐ[R] D := (Algebra.TensorProduct.includeRight : A →ₐ[R[X]] D).restrictScalars R
  let f : T →ₐ[R] D := Algebra.TensorProduct.lift dl dr (fun _ _ => Commute.all _ _)
  have hft (x y : A) : f (x ⊗ₜ[R] y) = x ⊗ₜ[R[X]] y := by
    change (x ⊗ₜ[R[X]] (1 : A)) * ((1 : A) ⊗ₜ[R[X]] y) = _
    simp
  have hgt (x y : A) : g (x ⊗ₜ[R[X]] y) = q (x ⊗ₜ[R] y) := by
    change q (x ⊗ₜ[R] (1 : A)) * q ((1 : A) ⊗ₜ[R] y) = _
    rw [← map_mul]
    apply congrArg q
    change (x ⊗ₜ[R] (1 : A)) * ((1 : A) ⊗ₜ[R] y) = x ⊗ₜ[R] y
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hf : I ≤ RingHom.ker f := by
    rw [Ideal.span_le]
    rintro z rfl
    change f (a ⊗ₜ[R] 1 - 1 ⊗ₜ[R] a) = 0
    rw [map_sub, hft, hft]
    apply sub_eq_zero.mpr
    change (algebraMap R[X] A X) ⊗ₜ[R[X]] (1 : A) =
      (1 : A) ⊗ₜ[R[X]] (algebraMap R[X] A X)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let fq : Q →ₐ[R] D := Ideal.Quotient.liftₐ I f hf
  have hfq (t : T) : fq (q t) = f t := rfl
  have hgf : g.comp fq = AlgHom.id R Q := by
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro t
    change g (fq (q t)) = q t
    rw [hfq]
    induction t using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => rw [hft, hgt]
  have hfg : fq.comp g = AlgHom.id R D := by
    apply AlgHom.ext
    intro t
    change fq (g t) = t
    induction t using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => rw [hgt, hfq, hft]
  exact ⟨AlgEquiv.ofAlgHom fq g hfg hgf⟩

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Classical.propDecidable

theorem hyperplaneFamily_double_isDomain {K A σ : Type*} [Field K]
    [CommRing A] [Algebra K A] [Fintype σ] [IsDomain (A ⊗[K] A)]
    [Algebra (Polynomial (MvPolynomial σ K)) (MvPolynomial σ A)]
    [IsScalarTower (MvPolynomial σ K) (Polynomial (MvPolynomial σ K)) (MvPolynomial σ A)]
    (v : σ → A)
    (heq : algebraMap (Polynomial (MvPolynomial σ K)) (MvPolynomial σ A) Polynomial.X =
      homogeneousLinearForm v)
    (i j : σ) (hji : j ≠ i)
    (hi : v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i ≠ 0)
    (hij : ∀ r : A ⊗[K] A,
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣
        (v j ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v j) * r →
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣ r) :
    IsDomain (MvPolynomial σ A ⊗[Polynomial (MvPolynomial σ K)] MvPolynomial σ A) := by
  let T := MvPolynomial σ A ⊗[MvPolynomial σ K] MvPolynomial σ A
  let w : T := homogeneousLinearForm v ⊗ₜ[MvPolynomial σ K] (1 : MvPolynomial σ A) -
    (1 : MvPolynomial σ A) ⊗ₜ[MvPolynomial σ K] homogeneousLinearForm v
  let I : Ideal T := Ideal.span {w}
  let d : σ → A ⊗[K] A := fun t => v t ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v t
  let J : Ideal (MvPolynomial σ (A ⊗[K] A)) := Ideal.span {homogeneousLinearForm d}
  let e := mvPolynomialTensorEquiv (R := K) (A := A) (B := A) (σ := σ)
  have hw : e w = homogeneousLinearForm d := by
    simp only [e, w, map_sub, mvPolynomialTensorEquiv_left, mvPolynomialTensorEquiv_right,
      homogeneousLinearForm, map_sum, map_mul, mvPolynomialMapOver_C, mvPolynomialMapOver_X,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only [d]
    rw [map_sub]
    ring
  have hmap : I.map e.toRingHom = J := by
    change (Ideal.span {w}).map e.toRingHom = J
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {e w} = Ideal.span {homogeneousLinearForm d}
    rw [hw]
  have hJ : J.IsPrime := homogeneousLinearForm_isPrime_of_regularPair d i j hji hi hij
  have hI : I.IsPrime := by
    have hh := hJ.comap e.toRingHom
    rw [← hmap] at hh
    have hc := I.comap_map_of_bijective e.toRingHom e.bijective
    rw [hc] at hh
    exact hh
  let : I.IsPrime := hI
  let : IsDomain (T ⧸ I) := Ideal.Quotient.isDomain I
  obtain ⟨f⟩ := tensor_polynomial_relation (R := MvPolynomial σ K) (A := MvPolynomial σ A)
  rw [heq] at f
  exact f.symm.injective.isDomain f.symm.toRingHom

end
end MaximalSeshadri.BertiniIntegral

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_Derivations
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem aeval_injective_of_derivation {R A : Type*}
    [CommRing R] [IsDomain R] [CharZero R]
    [CommRing A] [IsDomain A] [Algebra R A]
    (hRA : Function.Injective (algebraMap R A))
    (D : Derivation R A A) (x : A) (hx : D x ≠ 0) :
    Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) := by
  apply (injective_iff_map_eq_zero (Polynomial.aeval x : R[X] →ₐ[R] A)).mpr
  intro p
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    intro hp
    by_cases h0 : p.natDegree = 0
    · have he := Polynomial.eq_C_of_natDegree_eq_zero h0
      rw [he, Polynomial.aeval_C] at hp
      have hc : p.coeff 0 = 0 := hRA (hp.trans (map_zero (algebraMap R A)).symm)
      rw [he, hc, Polynomial.C_0]
    · have hd : Polynomial.aeval x p.derivative = 0 := by
        have hd := congrArg D hp
        rw [D.map_zero, D.map_aeval] at hd
        change Polynomial.aeval x p.derivative * D x = 0 at hd
        exact (mul_eq_zero.mp hd).resolve_right hx
      have hdz : p.derivative = 0 := ih p.derivative.natDegree
        (hn ▸ Polynomial.natDegree_derivative_lt h0) p.derivative rfl hd
      exact (h0 (Polynomial.derivative_eq_zero.mp hdz)).elim

theorem hyperplane_aeval_injective {K A σ : Type*} [Field K] [CharZero K]
    [CommRing A] [IsDomain A] [Algebra K A] [Fintype σ]
    (v : σ → A) (D : Derivation K A A) (i : σ) (hi : D (v i) ≠ 0) :
    Function.Injective (Polynomial.aeval (∑ j, MvPolynomial.C (v j) * MvPolynomial.X j) :
      (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] MvPolynomial σ A) := by
  have hinj : Function.Injective
      (algebraMap (MvPolynomial σ K) (MvPolynomial σ A)) := by
    exact MvPolynomial.map_injective (algebraMap K A) (algebraMap K A).injective
  apply aeval_injective_of_derivation hinj (mvParameterDerivation D)
  have he : mvParameterDerivation D (∑ j, MvPolynomial.C (v j) * MvPolynomial.X j) =
      ∑ j, MvPolynomial.C (D (v j)) * MvPolynomial.X j := by
    change (mvCoeffDerivation (σ := σ) D)
      (∑ j, MvPolynomial.C (v j) * MvPolynomial.X j) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [(mvCoeffDerivation D).leibniz, mvCoeffDerivation_C, mvCoeffDerivation_X]
    change MvPolynomial.C (v j) * 0 + MvPolynomial.X j * MvPolynomial.C (D (v j)) =
      MvPolynomial.C (D (v j)) * MvPolynomial.X j
    rw [mul_zero, zero_add, mul_comm]
  rw [he]
  intro hz
  have hh := congrArg (MvPolynomial.eval (fun j => if j = i then (1 : A) else 0)) hz
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    map_zero] at hh
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, if_true] at hh
  exact hi hh

end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

theorem genericFiber_isDomain {P B : Type*} [CommRing P] [IsDomain P]
    [CommRing B] [IsDomain B] [Algebra P B]
    (h : Function.Injective (algebraMap P B)) :
    IsDomain (FractionRing P ⊗[P] B) := by
  let : Algebra B (FractionRing P ⊗[P] B) := Algebra.TensorProduct.rightAlgebra
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (M :=
    Algebra.algebraMapSubmonoid B (nonZeroDivisors P))
  rintro z ⟨a, ha, rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro hz
  exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) (h (by simpa using hz))

theorem doubledGenericFiber_isDomain {P B : Type*} [CommRing P] [IsDomain P]
    [CommRing B] [IsDomain B] [Algebra P B]
    (h : Function.Injective (algebraMap P B)) [IsDomain (B ⊗[P] B)] :
    IsDomain ((FractionRing P ⊗[P] B) ⊗[FractionRing P] (FractionRing P ⊗[P] B)) := by
  have hP : Function.Injective (algebraMap P (B ⊗[P] B)) := by
    intro x y hxy
    apply h
    simpa only [AlgHom.commutes] using congrArg (Algebra.TensorProduct.lmul' P (S := B)) hxy
  let : IsDomain (FractionRing P ⊗[P] (B ⊗[P] B)) := genericFiber_isDomain hP
  let e := doubledBaseChangeEquiv (P := P) (F := FractionRing P) (B := B)
  exact e.injective.isDomain e.toRingHom

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

theorem finiteType_rationalPoint {K A : Type} [Field K] [IsAlgClosed K]
    [CommRing A] [Nontrivial A] [Algebra K A] [Algebra.FiniteType K A] :
    Nonempty (A →ₐ[K] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m)⟩

theorem finiteType_point_nonvanishing {K A : Type} [Field K] [IsAlgClosed K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (a : A) (ha : a ≠ 0) : ∃ f : A →ₐ[K] K, f a ≠ 0 := by
  let C := Localization.Away a
  have hs : Submonoid.powers a ≤ nonZeroDivisors A := by
    rintro x ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n ha)
  let : IsDomain C := IsLocalization.isDomain_localization hs
  obtain ⟨φ⟩ := finiteType_rationalPoint (K := K) (A := C)
  let j : A →ₐ[K] C := IsScalarTower.toAlgHom K A C
  refine ⟨φ.comp j, ?_⟩
  exact ((IsLocalization.map_units C (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)).map
    φ.toMonoidHom).ne_zero

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri
noncomputable section
open scoped TensorProduct

variable {F A B : Type} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

lemma tensorSpecialize_repr {ι : Type} (b : Module.Basis ι F B)
    (φ : A →ₐ[F] F) (z : A ⊗[F] B) (i : ι) :
    b.repr (tensorSpecialize φ z) i = φ ((b.baseChange A).repr z i) := by
  induction z using OAI.tensorInductionOn with
  | tmul x y => simp [tensorSpecialize, Module.Basis.baseChange_repr_tmul, map_smul, mul_comm]
  | add x y hx hy => simp_all

theorem tensorProduct_isDomain [IsAlgClosed F] 
    [IsDomain A] [IsDomain B] [Algebra.FiniteType F A] : IsDomain (A ⊗[F] B) := by
  classical
  let b := Module.Basis.ofVectorSpace F B
  have hex (z : A ⊗[F] B) (hz : z ≠ 0) :
      ∃ i, (b.baseChange A).repr z i ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    apply (b.baseChange A).repr.injective
    ext i
    simpa using h i
  let : Nontrivial (A ⊗[F] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain F A B
      (algebraMap F A).injective (algebraMap F B).injective
  let : NoZeroDivisors (A ⊗[F] B) := ⟨fun {x y} hxy => by
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ := hex x h.1
    obtain ⟨j, hj⟩ := hex y h.2
    obtain ⟨ψ, hψ⟩ := BertiniIntegral.finiteType_point_nonvanishing (K := F)
      ((b.baseChange A).repr x i * (b.baseChange A).repr y j) (mul_ne_zero hi hj)
    rw [map_mul, mul_ne_zero_iff] at hψ
    have hx : tensorSpecialize (B := B) ψ x ≠ 0 := by
      intro heq
      have := tensorSpecialize_repr b ψ x i
      rw [heq, map_zero, Finsupp.zero_apply] at this
      exact hψ.1 this.symm
    have hy : tensorSpecialize (B := B) ψ y ≠ 0 := by
      intro heq
      have := tensorSpecialize_repr b ψ y j
      rw [heq, map_zero, Finsupp.zero_apply] at this
      exact hψ.2 this.symm
    have := congrArg (tensorSpecialize (B := B) ψ) hxy
    simp only [map_mul, map_zero, mul_eq_zero, hx, hy, or_self] at this⟩
  exact NoZeroDivisors.to_isDomain _

end
end MaximalSeshadri


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_GeometricDomains
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial

lemma finite_self_tensor_dimension_one {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] [IsDomain (L ⊗[K] L)] :
    Module.finrank K L = 1 := by
  let : Field (L ⊗[K] L) :=
    (isField_of_isIntegral_of_isField' (R := L) (S := L ⊗[K] L) (Field.toIsField L)).toField
  let μ : L ⊗[K] L →ₐ[L] L := Algebra.TensorProduct.lmul'' K
  have hi : Function.Injective μ := μ.injective
  have hs : Function.Surjective μ := by
    intro x
    exact ⟨x ⊗ₜ[K] 1, by simp [μ, Algebra.TensorProduct.lmul'',
      Algebra.TensorProduct.algHomOfLinearMapTensorProduct_apply]⟩
  let e := LinearEquiv.ofBijective μ.toLinearMap ⟨hi, hs⟩
  have he := e.finrank_eq
  simpa only [Module.finrank_baseChange, Module.finrank_self] using he

theorem relative_algebraic_closure_of_self_tensor_domain
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsDomain (F ⊗[K] F)]
    (x : F) (hx : IsAlgebraic K x) : ∃ c : K, algebraMap K F c = x := by
  let L := IntermediateField.adjoin K ({x} : Set F)
  let : Module.Finite K L := IntermediateField.adjoin.finiteDimensional hx.isIntegral
  let ι : L →ₐ[K] F := L.val
  let ψ : L ⊗[K] L →ₐ[K] F ⊗[K] F := Algebra.TensorProduct.map ι ι
  have hi : Function.Injective ψ := by
    exact TensorProduct.map_injective_of_flat_flat ι.toLinearMap ι.toLinearMap
      ι.injective ι.injective
  let : IsDomain (L ⊗[K] L) := hi.isDomain ψ.toRingHom
  have hd : Module.finrank K L = 1 := finite_self_tensor_dimension_one
  let y : L := ⟨x, IntermediateField.subset_adjoin K _ (Set.mem_singleton x)⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd (one_ne_zero : (1 : L) ≠ 0) y
  refine ⟨c, ?_⟩
  have h := congrArg (fun z : L => (z : F)) hc
  simpa [Algebra.smul_def, y] using h

lemma monic_factor_descends {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hclosed : ∀ x : F, IsAlgebraic K x → ∃ c : K, algebraMap K F c = x)
    (p : K[X]) (q : F[X]) (hp : p.Monic) (hq : q.Monic)
    (hd : q ∣ p.map (algebraMap K F)) :
    ∃ q₀ : K[X], q₀.map (algebraMap K F) = q := by
  apply (Polynomial.mem_lifts q).mp
  apply (Polynomial.lifts_iff_coeff_lifts q).mpr
  intro n
  exact hclosed (q.coeff n) (Polynomial.isIntegral_coeff_of_dvd p q hp hq hd n).isAlgebraic

theorem irreducible_map_of_relative_closure {K F : Type*} [Field K] [Field F]
    [Algebra K F]
    (hclosed : ∀ x : F, IsAlgebraic K x → ∃ c : K, algebraMap K F c = x)
    (p : K[X]) (hp : p.Monic) (hi : Irreducible p) :
    Irreducible (p.map (algebraMap K F)) := by
  apply ((hp.map (algebraMap K F)).irreducible_iff_natDegree).mpr
  have hinj := Polynomial.map_injective (algebraMap K F) (algebraMap K F).injective
  refine ⟨?_, ?_⟩
  · intro he
    apply hi.ne_one
    apply hinj
    simpa using he
  · intro f g hf hg hfg
    obtain ⟨f₀, rfl⟩ := monic_factor_descends hclosed p f hp hf ⟨g, hfg.symm⟩
    obtain ⟨g₀, rfl⟩ := monic_factor_descends hclosed p g hp hg
      ⟨f₀.map (algebraMap K F), by rw [mul_comm]; exact hfg.symm⟩
    have he : f₀ * g₀ = p := hinj (by simpa using hfg)
    obtain hfu | hgu := hi.isUnit_or_isUnit he.symm
    · left
      exact natDegree_eq_zero_of_isUnit (hfu.map (Polynomial.mapRingHom (algebraMap K F)))
    · right
      exact natDegree_eq_zero_of_isUnit (hgu.map (Polynomial.mapRingHom (algebraMap K F)))

theorem finite_separable_tensor_isDomain {K F E : Type*}
    [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] [IsDomain (F ⊗[K] F)] :
    IsDomain (F ⊗[K] E) := by
  let pb := Field.powerBasisOfFiniteOfSeparable K E
  let p := minpoly K pb.gen
  have hp : p.Monic := minpoly.monic pb.isIntegral_gen
  have hi : Irreducible p := minpoly.irreducible pb.isIntegral_gen
  have hm : Irreducible (p.map (algebraMap K F)) :=
    irreducible_map_of_relative_closure
      relative_algebraic_closure_of_self_tensor_domain p hp hi
  let : IsDomain (AdjoinRoot (p.map (algebraMap K F))) :=
    AdjoinRoot.isDomain_of_prime hm.prime
  let e : AdjoinRoot p ≃ₐ[K] E := AdjoinRoot.equiv' p pb
    (by simp [p, Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
      ) (minpoly.aeval K pb.gen)
  let e' : F ⊗[K] E ≃ₐ[F] AdjoinRoot (p.map (algebraMap K F)) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) e.symm).trans (rootBaseChangeEquiv p)
  exact e'.injective.isDomain e'.toRingHom

lemma tensor_sum_in_intermediate_range {K F E : Type*}
    [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
    (L : IntermediateField K E) (s : Finset (F × E))
    (hs : ∀ q ∈ s, q.2 ∈ L) :
    (∑ q ∈ s, q.1 ⊗ₜ[K] q.2) ∈
      (Algebra.TensorProduct.map (AlgHom.id K F) L.val).range := by
  apply Subalgebra.sum_mem
  intro q hq
  exact ⟨q.1 ⊗ₜ[K] (⟨q.2, hs q hq⟩ : L), rfl⟩

theorem separable_tensor_isDomain {K F E : Type*}
    [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
    [Algebra.IsSeparable K E] [IsDomain (F ⊗[K] F)] :
    IsDomain (F ⊗[K] E) := by
  classical
  let : Nontrivial (F ⊗[K] E) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K F E
      (algebraMap K F).injective (algebraMap K E).injective
  let : NoZeroDivisors (F ⊗[K] E) := ⟨fun {x y} hxy => by
    obtain ⟨s, hx⟩ := TensorProduct.exists_finset x
    obtain ⟨t, hy⟩ := TensorProduct.exists_finset y
    let u : Finset E := (s ∪ t).image Prod.snd
    let L := IntermediateField.adjoin K (u : Set E)
    let : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin
      (fun z _ => Algebra.IsSeparable.isIntegral K z)
    let : Algebra.IsSeparable K L := Algebra.IsSeparable.of_algHom K E L.val
    let : IsDomain (F ⊗[K] L) := finite_separable_tensor_isDomain
    let ψ : F ⊗[K] L →ₐ[K] F ⊗[K] E :=
      Algebra.TensorProduct.map (AlgHom.id K F) L.val
    have hi : Function.Injective ψ :=
      TensorProduct.map_injective_of_flat_flat (AlgHom.id K F).toLinearMap
        L.val.toLinearMap Function.injective_id L.val.injective
    have hs : ∀ q ∈ s, q.2 ∈ L := by
      intro q hq
      apply IntermediateField.subset_adjoin
      exact Finset.mem_image.mpr ⟨q, Finset.mem_union_left _ hq, rfl⟩
    have ht : ∀ q ∈ t, q.2 ∈ L := by
      intro q hq
      apply IntermediateField.subset_adjoin
      exact Finset.mem_image.mpr ⟨q, Finset.mem_union_right _ hq, rfl⟩
    obtain ⟨x', hx'⟩ := hx.symm ▸ tensor_sum_in_intermediate_range L s hs
    obtain ⟨y', hy'⟩ := hy.symm ▸ tensor_sum_in_intermediate_range L t ht
    change ψ x' = x at hx'
    change ψ y' = y at hy'
    have hzero : x' * y' = 0 := hi (by simpa only [map_mul, map_zero, hx', hy'] using hxy)
    obtain hxz | hyz := mul_eq_zero.mp hzero
    · left
      rw [← hx', hxz, map_zero]
    · right
      rw [← hy', hyz, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

theorem tensorProduct_isDomain_general {K A B : Type}
    [Field K] [IsAlgClosed K]
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra K A] [Algebra K B] : IsDomain (A ⊗[K] B) := by
  classical
  let : Nontrivial (A ⊗[K] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K A B
      (algebraMap K A).injective (algebraMap K B).injective
  let : NoZeroDivisors (A ⊗[K] B) := ⟨fun {x y} hxy => by
    obtain ⟨s, hx⟩ := TensorProduct.exists_finset x
    obtain ⟨t, hy⟩ := TensorProduct.exists_finset y
    let u : Finset A := (s ∪ t).image Prod.fst
    let C := Algebra.adjoin K (u : Set A)
    let : Algebra.FiniteType K C := Algebra.FiniteType.adjoin_of_finite u.finite_toSet
    let : IsDomain (C ⊗[K] B) := MaximalSeshadri.tensorProduct_isDomain
    let ψ : C ⊗[K] B →ₐ[K] A ⊗[K] B :=
      Algebra.TensorProduct.map C.val (AlgHom.id K B)
    have hi : Function.Injective ψ :=
      TensorProduct.map_injective_of_flat_flat C.val.toLinearMap
        (AlgHom.id K B).toLinearMap Subtype.val_injective Function.injective_id
    have hr (v : Finset (A × B)) (hv : v ⊆ s ∪ t) :
        (∑ q ∈ v, q.1 ⊗ₜ[K] q.2) ∈ ψ.range := by
      apply Subalgebra.sum_mem
      intro q hq
      have hqc : q.1 ∈ C := Algebra.subset_adjoin
        (Finset.mem_image.mpr ⟨q, hv hq, rfl⟩)
      exact ⟨(⟨q.1, hqc⟩ : C) ⊗ₜ[K] q.2, rfl⟩
    obtain ⟨x', hx'⟩ := hx.symm ▸ hr s Finset.subset_union_left
    obtain ⟨y', hy'⟩ := hy.symm ▸ hr t Finset.subset_union_right
    change ψ x' = x at hx'
    change ψ y' = y at hy'
    have hz : x' * y' = 0 := hi (by simpa only [map_mul, map_zero, hx', hy'] using hxy)
    obtain hxz | hyz := mul_eq_zero.mp hz
    · left
      rw [← hx', hxz, map_zero]
    · right
      rw [← hy', hyz, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

theorem self_tensor_domain_geometrically_domain {K F E : Type}
    [Field K] [CharZero K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [IsDomain (F ⊗[K] F)] :
    IsDomain (F ⊗[K] E) := by
  let Ω := AlgebraicClosure K
  let M := AlgebraicClosure E
  let ι : Ω →ₐ[K] M := IsAlgClosed.lift
  let : Algebra Ω M := ι.toRingHom.toAlgebra
  let : IsScalarTower K Ω M := IsScalarTower.of_algebraMap_eq fun z => (ι.commutes z).symm
  let : IsDomain (F ⊗[K] Ω) := separable_tensor_isDomain
  let e₁ := Algebra.TensorProduct.comm K Ω F
  let : IsDomain (Ω ⊗[K] F) := e₁.injective.isDomain e₁.toRingHom
  let : IsDomain (M ⊗[Ω] (Ω ⊗[K] F)) := tensorProduct_isDomain_general
  let e₂ := Algebra.TensorProduct.cancelBaseChange K Ω Ω M F
  let : IsDomain (M ⊗[K] F) := e₂.symm.injective.isDomain e₂.symm.toRingHom
  let e₃ := Algebra.TensorProduct.comm K F M
  let : IsDomain (F ⊗[K] M) := e₃.injective.isDomain e₃.toRingHom
  let η : E →ₐ[K] M := IsScalarTower.toAlgHom K E M
  let ψ : F ⊗[K] E →ₐ[K] F ⊗[K] M :=
    Algebra.TensorProduct.map (AlgHom.id K F) η
  have hi : Function.Injective ψ :=
    TensorProduct.map_injective_of_flat_flat (AlgHom.id K F).toLinearMap
      η.toLinearMap Function.injective_id η.injective
  exact hi.isDomain ψ.toRingHom

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

theorem tensor_localization_isDomain {K A C B : Type}
    [Field K] [CommRing A] [IsDomain A] [CommRing C] [Nontrivial C]
    [CommRing B] [Algebra K A] [Algebra K C] [Algebra K B]
    [Algebra A B] [IsScalarTower K A B]
    (M : Submonoid A) [IsLocalization M B]
    (hM : M ≤ nonZeroDivisors A) [IsDomain (A ⊗[K] C)] :
    IsDomain (B ⊗[K] C) := by
  let f : A ⊗[K] C →ₐ[K] B ⊗[K] C :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A B) (AlgHom.id K C)
  let : Algebra (A ⊗[K] C) (B ⊗[K] C) := f.toRingHom.toAlgebra
  let : IsScalarTower A (A ⊗[K] C) (B ⊗[K] C) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change (algebraMap A B a) ⊗ₜ[K] (1 : C) = f (a ⊗ₜ[K] 1)
      simp [f]
  let : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[K] C) M) (B ⊗[K] C) :=
    IsLocalization.tensorProduct_tensorProduct K C M B (by
      ext c
      change f (1 ⊗ₜ[K] c) = 1 ⊗ₜ[K] c
      simp [f])
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (M :=
    Algebra.algebraMapSubmonoid (A ⊗[K] C) M)
  rintro z ⟨a, ha, rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  have hi : Function.Injective (Algebra.TensorProduct.includeLeft :
      A →ₐ[K] A ⊗[K] C) :=
    Algebra.TensorProduct.includeLeft_injective (algebraMap K C).injective
  exact fun hz => (mem_nonZeroDivisors_iff_ne_zero.mp (hM ha)) (hi (by
    simpa using hz))

theorem fraction_self_tensor_isDomain {K A : Type}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [IsDomain (A ⊗[K] A)] :
    IsDomain (FractionRing A ⊗[K] FractionRing A) := by
  let F := FractionRing A
  let : IsDomain (F ⊗[K] A) :=
    tensor_localization_isDomain (nonZeroDivisors A) le_rfl
  let e := Algebra.TensorProduct.comm K A F
  let : IsDomain (A ⊗[K] F) := e.injective.isDomain e.toRingHom
  exact tensor_localization_isDomain (nonZeroDivisors A) le_rfl

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

theorem self_tensor_domain_geometrically_domain_algebra {K A E : Type}
    [Field K] [CharZero K]
    [CommRing A] [IsDomain A] [Field E] [Algebra K A] [Algebra K E]
    [IsDomain (A ⊗[K] A)] : IsDomain (A ⊗[K] E) := by
  let F := FractionRing A
  let : IsDomain (F ⊗[K] F) := fraction_self_tensor_isDomain
  let : IsDomain (F ⊗[K] E) := self_tensor_domain_geometrically_domain
  let ι : A →ₐ[K] F := IsScalarTower.toAlgHom K A F
  let ψ : A ⊗[K] E →ₐ[K] F ⊗[K] E :=
    Algebra.TensorProduct.map ι (AlgHom.id K E)
  have hi : Function.Injective ψ :=
    TensorProduct.map_injective_of_flat_flat ι.toLinearMap (AlgHom.id K E).toLinearMap
      (IsFractionRing.injective A F) Function.injective_id
  exact hi.isDomain ψ.toRingHom

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_HyperplaneFamilies
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem mvPolynomial_parameter_tensor {R K A σ : Type*}
    [CommRing R] [CommRing K] [CommRing A] [Algebra R K] [Algebra R A]
    [Algebra (MvPolynomial σ R) K] [IsScalarTower R (MvPolynomial σ R) K] :
    ∃ e : (K ⊗[MvPolynomial σ R] MvPolynomial σ A) ≃ₐ[K] (K ⊗[R] A),
      (∀ k a, e (k ⊗ₜ[MvPolynomial σ R] C a) = k ⊗ₜ[R] a) ∧
      ∀ i, e (1 ⊗ₜ[MvPolynomial σ R] (X i : MvPolynomial σ A)) =
        (algebraMap (MvPolynomial σ R) K (X i)) ⊗ₜ[R] 1 := by
  let D := K ⊗[R] A
  let Q := K ⊗[MvPolynomial σ R] MvPolynomial σ A
  let α : σ → K := fun i => algebraMap (MvPolynomial σ R) K (X i)
  let ev : MvPolynomial σ A →ₐ[R] D :=
    { MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : A →ₐ[R] D).toRingHom
        (fun i => α i ⊗ₜ[R] (1 : A)) with
      commutes' := fun r => by
        simp only [MvPolynomial.algebraMap_apply]
        change MvPolynomial.eval₂
          (Algebra.TensorProduct.includeRight : A →ₐ[R] D).toRingHom
          (fun i => α i ⊗ₜ[R] (1 : A)) (C (algebraMap R A r)) = _
        rw [MvPolynomial.eval₂_C]
        exact (Algebra.TensorProduct.includeRight : A →ₐ[R] D).commutes r }
  have heC (a : A) : ev (C a) = (1 : K) ⊗ₜ[R] a := by
    simp only [ev, AlgHom.coe_mk, coe_eval₂Hom, eval₂_C]
    rfl
  have heX (i : σ) : ev (X i) = α i ⊗ₜ[R] (1 : A) := by simp [ev]
  have hemap : ev.toRingHom.comp (algebraMap (MvPolynomial σ R) (MvPolynomial σ A)) =
      algebraMap (MvPolynomial σ R) D := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_C]
      change ev (C (algebraMap R A r)) = algebraMap (MvPolynomial σ R) D (C r)
      rw [heC]
      change (1 : K) ⊗ₜ[R] algebraMap R A r =
        algebraMap (MvPolynomial σ R) D (algebraMap R (MvPolynomial σ R) r)
      rw [← IsScalarTower.algebraMap_apply]
      change (1 : K) ⊗ₜ[R] algebraMap R A r = (algebraMap R K r) ⊗ₜ[R] (1 : A)
      simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_X]
      change ev (X i) = algebraMap (MvPolynomial σ R) D (X i)
      rw [heX]
      rfl
  let evP : MvPolynomial σ A →ₐ[MvPolynomial σ R] D :=
    ⟨ev.toRingHom, fun p => DFunLike.congr_fun hemap p⟩
  let f : Q →ₐ[MvPolynomial σ R] D := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom (MvPolynomial σ R) K D) evP (fun _ _ => Commute.all _ _)
  let lc : K →ₐ[R] Q :=
    (Algebra.TensorProduct.includeLeft : K →ₐ[MvPolynomial σ R] Q).restrictScalars R
  let rc : A →ₐ[R] Q :=
    ((Algebra.TensorProduct.includeRight : MvPolynomial σ A →ₐ[MvPolynomial σ R] Q).restrictScalars R).comp
      (IsScalarTower.toAlgHom R A (MvPolynomial σ A))
  let g : D →ₐ[R] Q := Algebra.TensorProduct.lift lc rc (fun _ _ => Commute.all _ _)
  have hgt (k : K) (a : A) : g (k ⊗ₜ[R] a) = k ⊗ₜ[MvPolynomial σ R] C a := by
    change (k ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ A)) *
      ((1 : K) ⊗ₜ[MvPolynomial σ R] C a) = _
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hft (k : K) (p : MvPolynomial σ A) :
      f (k ⊗ₜ[MvPolynomial σ R] p) = (k ⊗ₜ[R] (1 : A)) * ev p := rfl
  have hfC (k : K) (a : A) : f (k ⊗ₜ[MvPolynomial σ R] C a) = k ⊗ₜ[R] a := by
    rw [hft, heC]
    change (k ⊗ₜ[R] (1 : A)) * ((1 : K) ⊗ₜ[R] a) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hfX (i : σ) : f (1 ⊗ₜ[MvPolynomial σ R] (X i : MvPolynomial σ A)) =
      α i ⊗ₜ[R] (1 : A) := by
    rw [hft, heX]
    change ((1 : K) ⊗ₜ[R] (1 : A)) * (α i ⊗ₜ[R] (1 : A)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
  have hgX (i : σ) : g (ev (X i)) = (1 : K) ⊗ₜ[MvPolynomial σ R] (X i : MvPolynomial σ A) := by
    rw [heX, hgt, map_one]
    have h := TensorProduct.smul_tmul (R := MvPolynomial σ R)
      (X i : MvPolynomial σ R) (1 : K) (1 : MvPolynomial σ A)
    simpa only [Algebra.smul_def, mul_one, MvPolynomial.algebraMap_def, MvPolynomial.map_X] using h
  have hgC (p : MvPolynomial σ A) : g (ev p) = (1 : K) ⊗ₜ[MvPolynomial σ R] p := by
    induction p using MvPolynomial.induction_on with
    | C a => rw [heC, hgt]
    | add p q hp hq => simp only [map_add, hp, hq, TensorProduct.tmul_add]
    | mul_X p i hp =>
      rw [map_mul, map_mul, hp, hgX]
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hgf : ∀ x : Q, g (f x) = x := by
    intro x
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul k p =>
      rw [hft, map_mul, hgt, hgC, map_one]
      change (k ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ A)) *
        ((1 : K) ⊗ₜ[MvPolynomial σ R] p) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hfg : ∀ x : D, f (g x) = x := by
    intro x
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul k a => rw [hgt, hfC]
  let fK : Q →ₐ[K] D :=
    { f.toRingHom with
      commutes' := by
        intro k
        change f (k ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ A)) = k ⊗ₜ[R] (1 : A)
        simpa only [map_one] using hfC k 1 }
  let e := AlgEquiv.ofBijective fK ⟨Function.LeftInverse.injective hgf,
    Function.RightInverse.surjective hfg⟩
  exact ⟨e, hfC, hfX⟩

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial

theorem tensor_base_polynomial_relation {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra R[X] A] [Algebra R[X] B]
    [IsScalarTower R R[X] A] [IsScalarTower R R[X] B] :
    ∃ e : ((A ⊗[R] B) ⧸ Ideal.span
      {algebraMap R[X] A X ⊗ₜ[R] (1 : B) - (1 : A) ⊗ₜ[R] algebraMap R[X] B X})
        ≃ₐ[A] (A ⊗[R[X]] B),
      ∀ (x : A) (y : B), e (Ideal.Quotient.mk _ (x ⊗ₜ[R] y)) = x ⊗ₜ[R[X]] y := by
  let a := algebraMap R[X] A X
  let b := algebraMap R[X] B X
  let T := A ⊗[R] B
  let D := A ⊗[R[X]] B
  let I : Ideal T := Ideal.span {a ⊗ₜ[R] (1 : B) - (1 : A) ⊗ₜ[R] b}
  let Q := T ⧸ I
  let q : T →ₐ[R] Q := Ideal.Quotient.mkₐ R I
  let l : A →ₐ[R] Q := q.comp Algebra.TensorProduct.includeLeft
  let r : B →ₐ[R] Q := q.comp Algebra.TensorProduct.includeRight
  have he : l a = r b := by
    apply sub_eq_zero.mp
    change q (a ⊗ₜ[R] 1) - q (1 ⊗ₜ[R] b) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hp : l.toRingHom.comp (algebraMap R[X] A) =
      r.toRingHom.comp (algebraMap R[X] B) := by
    apply Polynomial.ringHom_ext
    · intro z
      change l (algebraMap R[X] A (C z)) = r (algebraMap R[X] B (C z))
      change l (algebraMap R[X] A (algebraMap R R[X] z)) =
        r (algebraMap R[X] B (algebraMap R R[X] z))
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      rw [l.commutes, r.commutes]
    · exact he
  let lp : A →ₐ[R[X]] Q := ⟨l.toRingHom, fun _ => rfl⟩
  let rp : B →ₐ[R[X]] Q := ⟨r.toRingHom, fun z => (DFunLike.congr_fun hp z).symm⟩
  let g : D →ₐ[R] Q := (Algebra.TensorProduct.lift lp rp
    (fun _ _ => Commute.all _ _)).restrictScalars R
  let dl : A →ₐ[R] D := (Algebra.TensorProduct.includeLeft : A →ₐ[R[X]] D).restrictScalars R
  let dr : B →ₐ[R] D := (Algebra.TensorProduct.includeRight : B →ₐ[R[X]] D).restrictScalars R
  let f : T →ₐ[R] D := Algebra.TensorProduct.lift dl dr (fun _ _ => Commute.all _ _)
  have hft (x : A) (y : B) : f (x ⊗ₜ[R] y) = x ⊗ₜ[R[X]] y := by
    change (x ⊗ₜ[R[X]] (1 : B)) * ((1 : A) ⊗ₜ[R[X]] y) = _
    simp
  have hgt (x : A) (y : B) : g (x ⊗ₜ[R[X]] y) = q (x ⊗ₜ[R] y) := by
    change q (x ⊗ₜ[R] (1 : B)) * q ((1 : A) ⊗ₜ[R] y) = _
    rw [← map_mul]
    apply congrArg q
    change (x ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] y) = x ⊗ₜ[R] y
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hf : I ≤ RingHom.ker f := by
    rw [Ideal.span_le]
    rintro z rfl
    change f (a ⊗ₜ[R] 1 - 1 ⊗ₜ[R] b) = 0
    rw [map_sub, hft, hft]
    apply sub_eq_zero.mpr
    change (algebraMap R[X] A X) ⊗ₜ[R[X]] (1 : B) =
      (1 : A) ⊗ₜ[R[X]] (algebraMap R[X] B X)
    simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let fq : Q →ₐ[R] D := Ideal.Quotient.liftₐ I f hf
  have hfq (t : T) : fq (q t) = f t := rfl
  have hgf : g.comp fq = AlgHom.id R Q := by
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro t
    change g (fq (q t)) = q t
    rw [hfq]
    induction t using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => rw [hft, hgt]
  have hfg : fq.comp g = AlgHom.id R D := by
    apply AlgHom.ext
    intro t
    change fq (g t) = t
    induction t using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => rw [hgt, hfq, hft]
  let e := AlgEquiv.ofAlgHom fq g hfg hgf
  let eA : Q ≃ₐ[A] D :=
    { e.toRingEquiv with
      commutes' := by
        intro z
        change fq (q (z ⊗ₜ[R] (1 : B))) = z ⊗ₜ[R[X]] (1 : B)
        rw [hfq, hft] }
  refine ⟨eA, ?_⟩
  intro x y
  change fq (q (x ⊗ₜ[R] y)) = x ⊗ₜ[R[X]] y
  rw [hfq, hft]

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem hyperplane_specialization_equiv {R K A σ : Type*}
    [CommRing R] [CommRing K] [CommRing A] [Fintype σ]
    [Algebra R K] [Algebra R A]
    [Algebra (MvPolynomial σ R) K] [IsScalarTower R (MvPolynomial σ R) K]
    [Algebra (MvPolynomial σ R)[X] K]
    [IsScalarTower (MvPolynomial σ R) (MvPolynomial σ R)[X] K] (v : σ → A) :
    let := hyperplaneFamilyAlgebra (K := R) v
    Nonempty ((K ⊗[(MvPolynomial σ R)[X]] MvPolynomial σ A) ≃ₐ[K]
      ((K ⊗[R] A) ⧸ Ideal.span {algebraMap (MvPolynomial σ R)[X] K X ⊗ₜ[R] (1 : A) -
        ∑ i, (algebraMap (MvPolynomial σ R) K (MvPolynomial.X i)) ⊗ₜ[R] v i})) := by
  classical
  let := hyperplaneFamilyAlgebra (K := R) v
  let := hyperplaneFamilyAlgebra_tower (K := R) v
  let α := fun i => algebraMap (MvPolynomial σ R) K (MvPolynomial.X i)
  let β := algebraMap (MvPolynomial σ R)[X] K X
  let T := K ⊗[MvPolynomial σ R] MvPolynomial σ A
  let D := K ⊗[R] A
  let q := homogeneousLinearForm v
  let I : Ideal T := Ideal.span {β ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ A) -
    (1 : K) ⊗ₜ[MvPolynomial σ R] q}
  let J : Ideal D := Ideal.span {β ⊗ₜ[R] (1 : A) - ∑ i, α i ⊗ₜ[R] v i}
  obtain ⟨e, heC, heX⟩ := mvPolynomial_parameter_tensor (R := R) (K := K) (A := A) (σ := σ)
  have he1 (k : K) : e (k ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ A)) =
      k ⊗ₜ[R] (1 : A) := by
    simpa only [map_one] using heC k 1
  have het (i : σ) : e ((1 : K) ⊗ₜ[MvPolynomial σ R]
      (MvPolynomial.C (v i) * MvPolynomial.X i)) = α i ⊗ₜ[R] v i := by
    have hq : (1 : K) ⊗ₜ[MvPolynomial σ R] (MvPolynomial.C (v i) * MvPolynomial.X i) =
        ((1 : K) ⊗ₜ[MvPolynomial σ R] MvPolynomial.C (v i)) *
        ((1 : K) ⊗ₜ[MvPolynomial σ R] MvPolynomial.X i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hq, map_mul, heC, heX]
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have heq : e ((1 : K) ⊗ₜ[MvPolynomial σ R] q) = ∑ i, α i ⊗ₜ[R] v i := by
    change e ((1 : K) ⊗ₜ[MvPolynomial σ R]
      (∑ i, MvPolynomial.C (v i) * MvPolynomial.X i)) = _
    rw [TensorProduct.tmul_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => het i
  have hIJ : J = I.map e.toRingHom := by
    change Ideal.span {_} = (Ideal.span {_}).map e.toRingHom
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    change _ = {e (β ⊗ₜ[MvPolynomial σ R] (1 : MvPolynomial σ A) -
      (1 : K) ⊗ₜ[MvPolynomial σ R] q)}
    rw [map_sub, he1, heq]
  obtain ⟨f, _⟩ := tensor_base_polynomial_relation (R := MvPolynomial σ R)
    (A := K) (B := MvPolynomial σ A)
  have hf : Nonempty ((T ⧸ I) ≃ₐ[K] (K ⊗[(MvPolynomial σ R)[X]] MvPolynomial σ A)) := by
    apply Nonempty.intro
    have hqmap : algebraMap (MvPolynomial σ R)[X] (MvPolynomial σ A) X = q := by
      change (aeval (R := MvPolynomial σ R) q) X = q
      exact aeval_X q
    rw [hqmap] at f
    exact f
  obtain ⟨f⟩ := hf
  exact ⟨f.symm.trans (Ideal.quotientEquivAlg I J e hIJ)⟩
end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_EtaleCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial RingTheory
open scoped Pointwise

lemma mem_principal_smul_top_iff_dvd {R : Type*} [CommRing R] (a r : R) :
    r ∈ a • (⊤ : Submodule R R) ↔ a ∣ r := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  simp [dvd_def, eq_comm]

lemma weaklyRegular_pair_iff {R : Type*} [CommRing R] (a b : R) :
    Sequence.IsWeaklyRegular R [a, b] ↔
      IsSMulRegular R a ∧ ∀ r : R, a ∣ b * r → a ∣ r := by
  rw [Sequence.isWeaklyRegular_cons_iff, Sequence.isWeaklyRegular_singleton_iff]
  change (IsSMulRegular R a ∧ IsSMulRegular (R ⧸ (a • (⊤ : Submodule R R))) b) ↔ _
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  simp only [smul_eq_mul, mem_principal_smul_top_iff_dvd]

theorem flat_regular_pair {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (a b : R) (ha : IsSMulRegular R a)
    (hab : ∀ r : R, a ∣ b * r → a ∣ r) :
    IsSMulRegular S (algebraMap R S a) ∧
      ∀ s : S, algebraMap R S a ∣ algebraMap R S b * s → algebraMap R S a ∣ s := by
  have h := ((weaklyRegular_pair_iff a b).mpr ⟨ha, hab⟩).of_flat (S := S)
  simp only [List.map_cons, List.map_nil] at h
  exact (weaklyRegular_pair_iff _ _).mp h

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open MvPolynomial
open scoped TensorProduct
variable {K σ : Type*} [CommRing K]

theorem coordinateDifference_flat :
    (coordinateDifference (K := K) (σ := σ)).Flat := by
  have hl : (Algebra.TensorProduct.includeLeft : MvPolynomial σ K →ₐ[K]
      MvPolynomial σ K ⊗[K] MvPolynomial σ K).Flat := by
    change (algebraMap (MvPolynomial σ K)
      (MvPolynomial σ K ⊗[K] MvPolynomial σ K)).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hs : (shearMinus (K := K) (σ := σ)).Flat :=
    RingHom.Flat.of_bijective (shearEquiv (K := K) (σ := σ)).bijective
  have hc := hl.comp hs
  change ((shearMinus (K := K) (σ := σ)).comp
    Algebra.TensorProduct.includeLeft).Flat at hc
  simpa only [Algebra.TensorProduct.lift_comp_includeLeft] using hc

theorem chartDifference_flat {A : Type*} [CommRing A] [Algebra K A]
    (φ : MvPolynomial σ K →ₐ[K] A) (hφ : φ.Flat) : (chartDifference φ).Flat := by
  exact coordinateDifference_flat.comp (RingHom.Flat.tensorProductMap hφ hφ)

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

theorem chartDifference_regular_pair {K A σ : Type*} [Field K]
    [CommRing A] [Algebra K A] (φ : MvPolynomial σ K →ₐ[K] A)
    (hφ : φ.Flat) (i j : σ) (hij : i ≠ j) :
    IsSMulRegular (A ⊗[K] A) (φ (MvPolynomial.X i) ⊗ₜ[K] (1 : A) -
      (1 : A) ⊗ₜ[K] φ (MvPolynomial.X i)) ∧
    ∀ s : A ⊗[K] A,
      (φ (MvPolynomial.X i) ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] φ (MvPolynomial.X i)) ∣
        (φ (MvPolynomial.X j) ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] φ (MvPolynomial.X j)) * s →
      (φ (MvPolynomial.X i) ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] φ (MvPolynomial.X i)) ∣ s := by
  let : Algebra (MvPolynomial σ K) (A ⊗[K] A) := (chartDifference φ).toRingHom.toAlgebra
  let : Module.Flat (MvPolynomial σ K) (A ⊗[K] A) := chartDifference_flat φ hφ
  have hab : ∀ p : MvPolynomial σ K,
      MvPolynomial.X i ∣ MvPolynomial.X j * p → MvPolynomial.X i ∣ p := by
    intro p hp
    exact (MvPolynomial.X_dvd_mul_iff.mp hp).resolve_left (by simpa using hij)
  have hr := flat_regular_pair (S := A ⊗[K] A) (MvPolynomial.X i) (MvPolynomial.X j)
    (show IsSMulRegular (MvPolynomial σ K) (MvPolynomial.X i) from
      MvPolynomial.isRegular_X.left) hab
  change IsSMulRegular _ (chartDifference φ (MvPolynomial.X i)) ∧
    ∀ s, chartDifference φ (MvPolynomial.X i) ∣ chartDifference φ (MvPolynomial.X j) * s →
      chartDifference φ (MvPolynomial.X i) ∣ s at hr
  simpa only [chartDifference_X] using hr

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_CountableSpecialization
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra
theorem hyperplaneFamily_geometricGeneric_of_injective {K A E σ : Type} [Field K] [CharZero K]
    [CommRing A] [IsDomain A] [Algebra K A] [Fintype σ]
    [IsDomain (A ⊗[K] A)] [Field E]
    [Algebra (FractionRing (MvPolynomial σ K)[X]) E]
    (v : σ → A)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] MvPolynomial σ A))
    (i j : σ) (hji : j ≠ i)
    (hi : v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i ≠ 0)
    (hij : ∀ r : A ⊗[K] A,
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣
        (v j ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v j) * r →
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣ r) :
    let := hyperplaneFamilyAlgebra (K := K) v
    IsDomain ((FractionRing (MvPolynomial σ K)[X] ⊗[(MvPolynomial σ K)[X]]
      MvPolynomial σ A) ⊗[FractionRing (MvPolynomial σ K)[X]] E) := by
  let := hyperplaneFamilyAlgebra (K := K) v
  let := hyperplaneFamilyAlgebra_tower (K := K) v
  let : IsDomain (MvPolynomial σ A ⊗[(MvPolynomial σ K)[X]] MvPolynomial σ A) :=
    hyperplaneFamily_double_isDomain v (by change Polynomial.aeval _ X = _; simp) i j hji hi hij
  let : IsDomain (FractionRing (MvPolynomial σ K)[X] ⊗[(MvPolynomial σ K)[X]]
      MvPolynomial σ A) := genericFiber_isDomain hdom
  let : IsDomain ((FractionRing (MvPolynomial σ K)[X] ⊗[(MvPolynomial σ K)[X]]
      MvPolynomial σ A) ⊗[FractionRing (MvPolynomial σ K)[X]]
      (FractionRing (MvPolynomial σ K)[X] ⊗[(MvPolynomial σ K)[X]]
      MvPolynomial σ A)) := doubledGenericFiber_isDomain hdom
  exact self_tensor_domain_geometrically_domain_algebra

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem hyperplane_injective_descent {R K A A₀ σ : Type*}
    [Field R] [Field K] [Algebra R K]
    [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [CommRing A₀] [Algebra R A₀] [Fintype σ]
    (g : A₀ →ₐ[R] A) (v₀ : σ → A₀) (v : σ → A)
    (hv : ∀ i, g (v₀ i) = v i)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] MvPolynomial σ A)) :
    Function.Injective (Polynomial.aeval (homogeneousLinearForm v₀) :
      (MvPolynomial σ R)[X] →ₐ[MvPolynomial σ R] MvPolynomial σ A₀) := by
  let G : MvPolynomial σ A₀ →+* MvPolynomial σ A := MvPolynomial.map g.toRingHom
  let U : (MvPolynomial σ R)[X] →+* (MvPolynomial σ K)[X] :=
    Polynomial.mapRingHom (MvPolynomial.map (algebraMap R K))
  let f₀ := (Polynomial.aeval (homogeneousLinearForm v₀) :
    (MvPolynomial σ R)[X] →ₐ[MvPolynomial σ R] MvPolynomial σ A₀)
  let f := (Polynomial.aeval (homogeneousLinearForm v) :
    (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] MvPolynomial σ A)
  have hcomp : G.comp f₀.toRingHom = f.toRingHom.comp U := by
    apply Polynomial.ringHom_ext
    · intro p
      change G (f₀ (C p)) = f (U (C p))
      simp only [f₀, f, U, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.aeval_C]
      simp only [MvPolynomial.algebraMap_def, G, MvPolynomial.map_map]
      have hsc : g.toRingHom.comp (algebraMap R A₀) =
          (algebraMap K A).comp (algebraMap R K) := by
        ext r
        exact (g.commutes r).trans (IsScalarTower.algebraMap_apply R K A r)
      exact congrArg (fun h : R →+* A => MvPolynomial.map h p) hsc
    · change G (f₀ X) = f (U X)
      simp only [f₀, f, U, Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.aeval_X]
      simp only [G, homogeneousLinearForm, map_sum, map_mul,
        MvPolynomial.map_C, MvPolynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hv]
  have hU : Function.Injective U :=
    Polynomial.map_injective _ (MvPolynomial.map_injective (algebraMap R K) (FaithfulSMul.algebraMap_injective R K))
  intro p q hpq
  apply hU
  apply hdom
  have hp := DFunLike.congr_fun hcomp p
  have hq := DFunLike.congr_fun hcomp q
  change G (f₀ p) = f (U p) at hp
  change G (f₀ q) = f (U q) at hq
  exact hp.symm.trans ((congrArg G hpq).trans hq)
end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

lemma polynomialQuotientBaseChange_tmul {R K n : Type*} [CommRing R] [CommRing K]
    [Algebra R K] (I : Ideal (MvPolynomial n R)) (p : MvPolynomial n R) :
    polynomialQuotientBaseChange (K := K) I ((1 : K) ⊗ₜ[R] Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R K) p) := by
  simp [polynomialQuotientBaseChange, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]

theorem countable_model_with_elements {K A : Type} [Field K] [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] {k : ℕ} (v : Fin k → A)
    (c : Set K) (hc : c.Countable) :
    ∃ (S : Subfield K), Countable S ∧ c ⊆ S ∧
      ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) S))
        (e : (K ⊗[S] (MvPolynomial (Fin n) S ⧸ I)) ≃ₐ[K] A)
        (v₀ : Fin k → MvPolynomial (Fin n) S ⧸ I),
        ∀ i, e (1 ⊗ₜ[S] v₀ i) = v i := by
  classical
  let : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨n, I, e, q, hq⟩ := Algebra.FinitePresentation.iff.mp
    (inferInstance : Algebra.FinitePresentation K A)
  have hp : ∀ i, ∃ p : MvPolynomial (Fin n) K, e (Ideal.Quotient.mk I p) = v i := by
    intro i
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (e.symm (v i))
    exact ⟨p, by rw [hp, e.apply_symm_apply]⟩
  choose p hp using hp
  let d : Finset K := (q.biUnion MvPolynomial.coeffs) ∪
    (Finset.univ.biUnion fun i => (p i).coeffs)
  let S := Subfield.closure (c ∪ (d : Set K))
  have hcount : Countable S := Cardinal.mk_le_aleph0_iff.mp
    ((Subfield.cardinalMk_closure_le_max _).trans (max_le
      ((hc.union d.countable_toSet).le_aleph0) le_rfl))
  have lift_poly (f : MvPolynomial (Fin n) K) (hf : f.coeffs ⊆ d) :
      ∃ f₀ : MvPolynomial (Fin n) S, MvPolynomial.map S.subtype f₀ = f := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro x hx
    exact ⟨⟨x, Subfield.subset_closure (Or.inr (hf hx))⟩, rfl⟩
  let I₀ := I.comap (MvPolynomial.map S.subtype)
  have hI : I₀.map (MvPolynomial.map S.subtype) = I := by
    apply le_antisymm Ideal.map_comap_le
    rw [← hq]
    apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨f₀, rfl⟩ := lift_poly f (fun x hx => Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨f, hf, hx⟩))
    apply Ideal.mem_map_of_mem
    exact Ideal.subset_span hf
  have hp₀ : ∀ i, ∃ p₀ : MvPolynomial (Fin n) S, MvPolynomial.map S.subtype p₀ = p i := by
    intro i
    exact lift_poly (p i) (fun x hx => Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩))
  choose p₀ hp₀ using hp₀
  let e₀ := (polynomialQuotientBaseChange (K := K) I₀).trans
    ((Ideal.quotientEquivAlgOfEq K hI).trans e)
  refine ⟨S, hcount, fun x hx => Subfield.subset_closure (Or.inl hx), n, I₀, e₀,
    fun i => Ideal.Quotient.mk I₀ (p₀ i), ?_⟩
  intro i
  change e ((Ideal.quotientEquivAlgOfEq K hI)
    (polynomialQuotientBaseChange I₀ (1 ⊗ₜ[S] Ideal.Quotient.mk I₀ (p₀ i)))) = _
  rw [polynomialQuotientBaseChange_tmul]
  change e ((Ideal.quotientEquivAlgOfEq K hI)
    (Ideal.Quotient.mk _ (MvPolynomial.map S.subtype (p₀ i)))) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rw [hp₀, hp]

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_Descent
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

lemma faithfullyFlat_dvd_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (a b : R) :
    algebraMap R S a ∣ algebraMap R S b ↔ a ∣ b := by
  have h := Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (Ideal.span {a})
  have hm := congrArg (fun I : Ideal R => b ∈ I) h
  simpa only [Ideal.mem_comap, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] using (Iff.of_eq hm)

theorem scalar_regular_pair_descent {R K A : Type*} [Field R] [Field K] [Algebra R K]
    [CommRing A] [Algebra R A] (a b : A)
    (hab : ∀ t : K ⊗[R] A, (1 : K) ⊗ₜ[R] a ∣ ((1 : K) ⊗ₜ[R] b) * t →
      (1 : K) ⊗ₜ[R] a ∣ t) :
    ∀ t : A, a ∣ b * t → a ∣ t := by
  intro t ht
  let e := Algebra.TensorProduct.comm R A K
  apply (faithfullyFlat_dvd_iff (S := A ⊗[R] K) a t).mp
  change a ⊗ₜ[R] (1 : K) ∣ t ⊗ₜ[R] (1 : K)
  apply (map_dvd_iff e).mp
  simp only [e, Algebra.TensorProduct.comm_tmul]
  apply hab
  obtain ⟨u, hu⟩ := ht
  refine ⟨(1 : K) ⊗ₜ[R] u, ?_⟩
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hu]

lemma scalar_model_injective {R K A : Type*} [Field R] [Field K] [Algebra R K]
    [CommRing A] [Algebra R A] :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective A

theorem model_line_conditions {R K A A₀ : Type*} [Field R] [Field K] [Algebra R K]
    [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    [IsDomain A] [IsDomain (A ⊗[K] A)] [CommRing A₀] [Algebra R A₀]
    (e : (K ⊗[R] A₀) ≃ₐ[K] A) (a₀ b₀ : A₀) (a b : A)
    (hea : e (1 ⊗ₜ[R] a₀) = a) (heb : e (1 ⊗ₜ[R] b₀) = b)
    (hb : Transcendental K b)
    (ha : a ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] a ≠ 0)
    (hab : ∀ r : A ⊗[K] A,
      (a ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] a) ∣
        (b ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] b) * r →
      (a ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] a) ∣ r) :
    IsDomain A₀ ∧ IsDomain (A₀ ⊗[R] A₀) ∧ Transcendental R b₀ ∧
      (a₀ ⊗ₜ[R] (1 : A₀) - (1 : A₀) ⊗ₜ[R] a₀ ≠ 0) ∧
      (∀ r : A₀ ⊗[R] A₀,
        (a₀ ⊗ₜ[R] (1 : A₀) - (1 : A₀) ⊗ₜ[R] a₀) ∣
          (b₀ ⊗ₜ[R] (1 : A₀) - (1 : A₀) ⊗ₜ[R] b₀) * r →
        (a₀ ⊗ₜ[R] (1 : A₀) - (1 : A₀) ⊗ₜ[R] a₀) ∣ r) := by
  let g : A₀ →ₐ[R] A := (e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hg : Function.Injective g := e.injective.comp scalar_model_injective
  let eD := (doubleBaseChange (R := R) (K := K) (A := A₀)).trans
    (Algebra.TensorProduct.congr e e)
  have hd (x : A₀) :
      eD ((1 : K) ⊗ₜ[R] (x ⊗ₜ[R] (1 : A₀) - (1 : A₀) ⊗ₜ[R] x)) =
        g x ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] g x := by
    simp only [TensorProduct.tmul_sub, map_sub, eD, AlgEquiv.trans_apply,
      doubleBaseChange_tmul, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom]
    have he1 : e ((1 : K) ⊗ₜ[R] (1 : A₀)) = 1 := e.map_one
    rw [he1]
    rfl
  have hga : g a₀ = a := hea
  have hgb : g b₀ = b := heb
  have hdom : IsDomain (A₀ ⊗[R] A₀) := by
    let : IsDomain (K ⊗[R] (A₀ ⊗[R] A₀)) := eD.injective.isDomain eD.toRingHom
    exact scalar_model_injective.isDomain
      (Algebra.TensorProduct.includeRight : A₀ ⊗[R] A₀ →ₐ[R] K ⊗[R] (A₀ ⊗[R] A₀)).toRingHom
  refine ⟨hg.isDomain g.toRingHom, hdom, ?_, ?_, ?_⟩
  · intro h
    apply hb
    rw [← hgb]
    exact (IsAlgebraic.algHom g h).tower_top K
  · intro hz
    apply ha
    rw [← hga, ← hd, hz, TensorProduct.tmul_zero, map_zero]
  · apply scalar_regular_pair_descent (R := R) (K := K)
    intro t ht
    apply (map_dvd_iff eD).mp
    rw [hd, hga]
    apply hab
    have hh := map_dvd eD ht
    simpa only [map_mul, hd, hga, hgb] using hh

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra
                                                                                               
theorem domain_hyperplane_equation_transport {R K A A₀ σ : Type*}
    [Field R] [Field K] [Algebra R K] [CommRing A] [Algebra K A]
    [CommRing A₀] [Algebra R A₀] [Fintype σ]
    (e : (K ⊗[R] A₀) ≃ₐ[K] A) (v₀ : σ → A₀) (v : σ → A)
    (hv : ∀ i, e (1 ⊗ₜ[R] v₀ i) = v i) (α : σ → K) (β : K)
    [IsDomain ((K ⊗[R] A₀) ⧸ Ideal.span {β ⊗ₜ[R] (1 : A₀) - ∑ i, α i ⊗ₜ[R] v₀ i})] :
    IsDomain (A ⧸ Ideal.span {algebraMap K A β - ∑ i, algebraMap K A (α i) * v i}) := by
  let J : Ideal (K ⊗[R] A₀) := Ideal.span {β ⊗ₜ[R] (1 : A₀) - ∑ i, α i ⊗ₜ[R] v₀ i}
  have he1 (k : K) : e (k ⊗ₜ[R] (1 : A₀)) = algebraMap K A k := e.commutes k
  have het (i : σ) : e (α i ⊗ₜ[R] v₀ i) = algebraMap K A (α i) * v i := by
    have ht : α i ⊗ₜ[R] v₀ i = (α i ⊗ₜ[R] (1 : A₀)) * ((1 : K) ⊗ₜ[R] v₀ i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [ht, map_mul, he1, hv]
  let J' : Ideal A := Ideal.span {algebraMap K A β - ∑ i, algebraMap K A (α i) * v i}
  have hJ : J' = J.map e.toRingHom := by
    change Ideal.span {_} = (Ideal.span {_}).map e.toRingHom
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    change _ = {e (β ⊗ₜ[R] (1 : A₀) - ∑ i, α i ⊗ₜ[R] v₀ i)}
    rw [map_sub, map_sum, he1]
    simp only [het]
  let eQ := Ideal.quotientEquivAlg J J' e hJ
  exact eQ.symm.injective.isDomain eQ.symm.toRingHom

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem hyperplane_integral_fiber_of_injective {R K A σ : Type}
    [Field R] [CharZero R] [Field K] [Algebra R K]
    [CommRing A] [IsDomain A] [Algebra R A] [Fintype σ]
    [IsDomain (A ⊗[R] A)] (v : σ → A)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial σ R)[X] →ₐ[MvPolynomial σ R] MvPolynomial σ A))
    (i j : σ) (hji : j ≠ i)
    (hi : v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i ≠ 0)
    (hij : ∀ r : A ⊗[R] A,
      (v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i) ∣
        (v j ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v j) * r →
      (v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i) ∣ r)
    (f : (MvPolynomial σ R)[X] →ₐ[R] K) (hf : Function.Injective f) :
    let := hyperplaneFamilyAlgebra (K := R) v
    let := f.toRingHom.toAlgebra
    IsDomain (K ⊗[(MvPolynomial σ R)[X]] MvPolynomial σ A) := by
  let := hyperplaneFamilyAlgebra (K := R) v
  let P := (MvPolynomial σ R)[X]
  let : Algebra P K := f.toRingHom.toAlgebra
  let F := FractionRing P
  let g : F →+* K := IsFractionRing.lift (g := f.toRingHom) hf
  let : Algebra F K := g.toAlgebra
  let : IsScalarTower P F K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap hf x).symm
  let : IsDomain ((F ⊗[P] MvPolynomial σ A) ⊗[F] K) :=
    hyperplaneFamily_geometricGeneric_of_injective (E := K) v hdom i j hji hi hij
  let e₁ := Algebra.TensorProduct.comm F K (F ⊗[P] MvPolynomial σ A)
  let : IsDomain (K ⊗[F] (F ⊗[P] MvPolynomial σ A)) := e₁.injective.isDomain e₁.toRingHom
  let e := Algebra.TensorProduct.cancelBaseChange P F K K (MvPolynomial σ A)
  exact e.symm.injective.isDomain e.symm.toRingHom

theorem hyperplane_integral_equation_of_injective {R K A σ : Type}
    [Field R] [CharZero R] [Field K] [Algebra R K]
    [CommRing A] [IsDomain A] [Algebra R A] [Fintype σ]
    [IsDomain (A ⊗[R] A)] (v : σ → A)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial σ R)[X] →ₐ[MvPolynomial σ R] MvPolynomial σ A))
    (i j : σ) (hji : j ≠ i)
    (hi : v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i ≠ 0)
    (hij : ∀ r : A ⊗[R] A,
      (v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i) ∣
        (v j ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v j) * r →
      (v i ⊗ₜ[R] (1 : A) - (1 : A) ⊗ₜ[R] v i) ∣ r)
    (f : (MvPolynomial σ R)[X] →ₐ[R] K) (hf : Function.Injective f) :
    IsDomain ((K ⊗[R] A) ⧸ Ideal.span {f X ⊗ₜ[R] (1 : A) -
      ∑ k, f (C (MvPolynomial.X k)) ⊗ₜ[R] v k}) := by
  let := hyperplaneFamilyAlgebra (K := R) v
  let P := (MvPolynomial σ R)[X]
  let : Algebra P K := f.toRingHom.toAlgebra
  let f₁ : MvPolynomial σ R →ₐ[R] K := f.comp Polynomial.CAlgHom
  let : Algebra (MvPolynomial σ R) K := f₁.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial σ R) K :=
    IsScalarTower.of_algebraMap_eq fun s => (f₁.commutes s).symm
  let : IsScalarTower (MvPolynomial σ R) P K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsDomain (K ⊗[P] MvPolynomial σ A) :=
    hyperplane_integral_fiber_of_injective v hdom i j hji hi hij f hf
  obtain ⟨q⟩ := hyperplane_specialization_equiv (R := R) (K := K) v
  exact q.symm.injective.isDomain q.symm.toRingHom

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_SimultaneousHyperplanes
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra
                                                                                    
theorem generic_hyperplane_section_over_model {R K A A₀ σ : Type}
    [Field R] [CharZero R] [Field K] [CharZero K]
    [Algebra R K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra R A]
    [IsScalarTower R K A] [IsDomain (A ⊗[K] A)]
    [CommRing A₀] [Algebra R A₀] [Fintype σ]
    (e : (K ⊗[R] A₀) ≃ₐ[K] A) (v₀ : σ → A₀) (v : σ → A)
    (hv : ∀ i, e (1 ⊗ₜ[R] v₀ i) = v i)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] MvPolynomial σ A))
    (i j : σ) (hji : j ≠ i) (hj : Transcendental K (v j))
    (hi : v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i ≠ 0)
    (hij : ∀ r : A ⊗[K] A,
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣
        (v j ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v j) * r →
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣ r) :
    ∀ f : (MvPolynomial σ R)[X] →ₐ[R] K, Function.Injective f →
      IsDomain (A ⧸ Ideal.span {algebraMap K A (f X) -
        ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) := by
  intro f hf
  obtain ⟨hA₀, hD₀, _, hi₀, hij₀⟩ := model_line_conditions (R := R) (K := K)
    (A := A) (A₀ := A₀) e (v₀ i) (v₀ j) (v i) (v j) (hv i) (hv j) hj hi hij
  let : IsDomain A₀ := hA₀
  let : IsDomain (A₀ ⊗[R] A₀) := hD₀
  let g : A₀ →ₐ[R] A := (e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hdom₀ := hyperplane_injective_descent (R := R) (K := K) (A := A) (A₀ := A₀)
    g v₀ v hv hdom
  let := hyperplane_integral_equation_of_injective (R := R) (K := K)
    (A := A₀) v₀ hdom₀ i j hji hi₀ hij₀ f hf
  exact domain_hyperplane_equation_transport (R := R) (K := K) (A := A)
    (A₀ := A₀) e v₀ v hv (fun k => f (C (MvPolynomial.X k))) (f X)

theorem generic_hyperplane_section {K A : Type} {n : ℕ}
    [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    [IsDomain (A ⊗[K] A)] (v : Fin n → A)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial (Fin n) K)[X] →ₐ[MvPolynomial (Fin n) K] MvPolynomial (Fin n) A))
    (i j : Fin n) (hji : j ≠ i) (hj : Transcendental K (v j))
    (hi : v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i ≠ 0)
    (hij : ∀ r : A ⊗[K] A,
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣
        (v j ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v j) * r →
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣ r)
    (c : Set K) (hc : c.Countable) :
    ∃ (S : Subfield K), Countable S ∧ c ⊆ S ∧
      ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
        IsDomain (A ⧸ Ideal.span {algebraMap K A (f X) -
          ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) := by
  classical
  obtain ⟨S, hS, hcS, m, I, e, v₀, hv⟩ := countable_model_with_elements v c hc
  let : Countable S := hS
  let A₀ := MvPolynomial (Fin m) S ⧸ I
  refine ⟨S, hS, hcS, ?_⟩
  exact generic_hyperplane_section_over_model (R := S) (K := K)
    (A := A) (A₀ := A₀) e v₀ v hv hdom i j hji hj hi hij

theorem etale_generic_hyperplane_section_s01_oai {K A ι : Type} {n : ℕ} [Field K] [CharZero K]
    [IsAlgClosed K] [Uncountable K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A]
    [Algebra (MvPolynomial ι K) A] [IsScalarTower K (MvPolynomial ι K) A]
    [Algebra.Etale (MvPolynomial ι K) A]
    (v : Fin n → A) (i j : Fin n) (a b : ι) (hab : a ≠ b)
    (hvi : v i = algebraMap (MvPolynomial ι K) A (MvPolynomial.X a))
    (hvj : v j = algebraMap (MvPolynomial ι K) A (MvPolynomial.X b)) (c : Set K) (hc : c.Countable) :
    ∃ (S : Subfield K), Countable S ∧ c ⊆ S ∧
      ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
        IsDomain (A ⧸ Ideal.span {algebraMap K A (f X) -
          ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) := by
  classical
  let : IsDomain (A ⊗[K] A) := tensorProduct_isDomain_general
  let φ : MvPolynomial ι K →ₐ[K] A := IsScalarTower.toAlgHom K (MvPolynomial ι K) A
  have hφ : φ.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  obtain ⟨hr, hreg⟩ := chartDifference_regular_pair φ hφ a b hab
  let δ : Derivation K A A :=
    (etaleCotangentCoordinate (K := K) (A := A) a).compDer (KaehlerDifferential.D K A)
  have hδi : δ (v i) = 1 := by
    rw [hvi]
    simp [δ]
  have hδj : δ (v j) = 0 := by
    rw [hvj]
    change etaleCotangentCoordinate a
      (KaehlerDifferential.D K A (algebraMap (MvPolynomial ι K) A (MvPolynomial.X b))) = 0
    simp [hab.symm]
  have hji : j ≠ i := by
    rintro rfl
    exact one_ne_zero (hδi.symm.trans hδj)
  let δb : Derivation K A A :=
    (etaleCotangentCoordinate (K := K) (A := A) b).compDer (KaehlerDifferential.D K A)
  have hδb : δb (v j) = 1 := by
    rw [hvj]
    simp [δb]
  have hj : Transcendental K (v j) := transcendental_iff_injective.mpr
    (aeval_injective_of_derivation (FaithfulSMul.algebraMap_injective K A)
      δb (v j) (hδb ▸ one_ne_zero))
  apply generic_hyperplane_section v
    (hyperplane_aeval_injective v δ i (hδi ▸ one_ne_zero)) i j hji hj
  · rw [hvi]
    intro hz
    have hz' : φ (MvPolynomial.X a) ⊗ₜ[K] (1 : A) -
        (1 : A) ⊗ₜ[K] φ (MvPolynomial.X a) = 0 := hz
    have : (1 : A ⊗[K] A) = 0 := hr (by rw [hz']; simp)
    exact one_ne_zero this
  · simpa only [hvi, hvj, φ, IsScalarTower.coe_toAlgHom'] using hreg
  · exact hc

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.BertiniIntegral.etale_generic_hyperplane_section_s01_oai := @OAI.MaximalSeshadri.BertiniIntegral.etale_generic_hyperplane_section_s01_oai
