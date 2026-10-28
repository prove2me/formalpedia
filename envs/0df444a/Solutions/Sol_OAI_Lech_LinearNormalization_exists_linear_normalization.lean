-- Prove2me | solution 1 for OAI.Lech.LinearNormalization.exists_linear_normalization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:56:09.174233+00:00
-- url     : https://prove2.me/submissions/5f1b729f-b560-4916-9a4a-191f4bafc435

import Mathlib
import Definitions.Def_OAIQ032L003
import Definitions.Def_OAIQ032L006

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LinearNormalization
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace Lech.LinearNormalization
universe u v
variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

lemma homogeneous_top_coeff {N d : ℕ} (f : MvPolynomial (Fin (N+1)) k)
    (hf : f.IsHomogeneous d) :
    (finSuccEquiv k N f).coeff d = C (eval (Fin.cons 1 0) f) := by
  have hdeg : (finSuccEquiv k N f).natDegree < d+1 :=
    (natDegree_finSuccEquiv f ▸ degreeOf_le_totalDegree f 0).trans_lt
      (Nat.lt_succ_of_le hf.totalDegree_le)
  have hc (i : ℕ) (hi : i ∈ Finset.range d) :
      constantCoeff ((finSuccEquiv k N f).coeff i) = 0 := by
    apply (hf.finSuccEquiv_coeff_isHomogeneous i (d-i) (by
      have := Finset.mem_range.mp hi; omega)).coeff_eq_zero
    simp only [map_zero]
    have := Finset.mem_range.mp hi
    omega
  have he : eval (Fin.cons 1 0) f = constantCoeff ((finSuccEquiv k N f).coeff d) := by
    simp_rw [eval_eq_eval_mv_eval', Polynomial.eval_one_map,
      Polynomial.eval_eq_sum_range' hdeg,eval_zero,one_pow,mul_one,map_sum,
      Finset.sum_range_succ,Finset.sum_eq_zero hc,zero_add]
  rw [he]
  apply totalDegree_eq_zero_iff_eq_C.mp
  exact (totalDegree_zero_iff_isHomogeneous (Fin N)).mpr
    (hf.finSuccEquiv_coeff_isHomogeneous d 0 (by omega))

lemma homogeneous_relation (G : ℕ → Submodule k A) [GradedAlgebra G]
    {N : ℕ} (x : Fin N → A) (hx : ∀ j,x j ∈ G 1)
    (hdep : ¬ Function.Injective (aeval (R:=k) x)) :
    ∃ d : ℕ, ∃ f : MvPolynomial (Fin N) k,
      f ≠ 0 ∧ f.IsHomogeneous d ∧ aeval x f = 0 := by
  classical
  have hk : RingHom.ker (aeval (R:=k) x).toRingHom ≠ ⊥ := by
    exact fun he => hdep ((RingHom.injective_iff_ker_eq_bot _).mpr he)
  obtain ⟨f,hf,hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  change aeval x f = 0 at hf
  have hn : ∃ d∈Finset.range (f.totalDegree+1),homogeneousComponent d f ≠ 0 := by
    by_contra! hn
    exact hf0 (by rw [← sum_homogeneousComponent f]; exact Finset.sum_eq_zero hn)
  obtain ⟨d,_,hd⟩ := hn
  refine ⟨d,homogeneousComponent d f,hd,homogeneousComponent_isHomogeneous _ _,?_⟩
  let g := Grading.polynomialMap G x hx
  have hh := g.map_directSumDecompose (x:=f) (i:=d)
  have hc : (DirectSum.decompose (homogeneousSubmodule (Fin N) k) f d :
      MvPolynomial (Fin N) k) = homogeneousComponent d f := by
    change ((inferInstance : DirectSum.Decomposition
      (homogeneousSubmodule (Fin N) k)).decompose' f d : MvPolynomial (Fin N) k) = _
    rw [Subsingleton.elim (inferInstance : DirectSum.Decomposition
      (homogeneousSubmodule (Fin N) k)) MvPolynomial.decomposition]
    exact MvPolynomial.decomposition.decompose'_apply f d
  rw [hc] at hh
  change aeval x (homogeneousComponent d f) =
    (DirectSum.decompose G (aeval x f) d : A) at hh
  rw [hf] at hh
  simpa using hh

lemma exists_homogeneous_direction [Infinite k] {N d : ℕ}
    (f : MvPolynomial (Fin N) k) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ a : Fin N → k,eval a f ≠ 0 := by
  by_contra! ha
  exact hf0 (hf.eq_zero_of_forall_eval_eq_zero ha)


lemma linearChange_homogeneous {N d : ℕ} (a : Fin (N+1) → k)
    (f : MvPolynomial (Fin (N+1)) k) (hf : f.IsHomogeneous d) :
    (linearChange a f).IsHomogeneous d := by
  let g : Fin (N+1) → MvPolynomial (Fin (N+1)) k :=
    Fin.cons (C (a 0)*X 0) (fun i => X i.succ + C (a i.succ)*X 0)
  have hg (i : Fin (N+1)) : (g i).IsHomogeneous 1 := by
    cases i using Fin.cases with
    | zero => exact isHomogeneous_C_mul_X _ _
    | succ i => exact (isHomogeneous_X _ _).add (isHomogeneous_C_mul_X _ _)
  have H : (aeval g f).IsHomogeneous (1*d) := hf.aeval g hg
  change (aeval g f).IsHomogeneous d
  simpa only [Nat.one_mul] using H

lemma linearChange_eval {N : ℕ} (a : Fin (N+1) → k)
    (f : MvPolynomial (Fin (N+1)) k) :
    eval (Fin.cons 1 0) (linearChange a f) = eval a f := by
  change ((aeval (Fin.cons 1 0)).comp (linearChange a)) f = (aeval a) f
  congr 1
  ext i
  cases i using Fin.cases <;> simp [linearChange]

lemma linearChange_leadingCoeff {N d : ℕ} (a : Fin (N+1) → k)
    (f : MvPolynomial (Fin (N+1)) k) (hf : f.IsHomogeneous d)
    (ha : eval a f ≠ 0) :
    (finSuccEquiv k N (linearChange a f)).leadingCoeff = C (eval a f) := by
  have hc := homogeneous_top_coeff (linearChange a f) (linearChange_homogeneous a f hf)
  rw [linearChange_eval] at hc
  have hle : (finSuccEquiv k N (linearChange a f)).natDegree ≤ d :=
    (natDegree_finSuccEquiv (linearChange a f) ▸
      degreeOf_le_totalDegree (linearChange a f) 0).trans
      (linearChange_homogeneous a f hf).totalDegree_le
  have hne : (finSuccEquiv k N (linearChange a f)).coeff d ≠ 0 := by
    rw [hc]; exact C_ne_zero.mpr ha
  have he : (finSuccEquiv k N (linearChange a f)).natDegree = d :=
    le_antisymm hle (Polynomial.le_natDegree_of_ne_zero hne)
  rwa [Polynomial.leadingCoeff,he]
lemma finSucc_aeval {N : ℕ} (y : Fin N → A) (b : A)
    (f : MvPolynomial (Fin (N+1)) k) :
    Polynomial.aevalTower (aeval (R:=k) y) b (finSuccEquiv k N f) =
      aeval (Fin.cons b y) f := by
  change ((Polynomial.aevalTower (aeval y) b).comp (finSuccEquiv k N).toAlgHom) f = _
  congr 1
  ext i
  cases i using Fin.cases <;> simp [finSuccEquiv_X_zero,finSuccEquiv_X_succ]

lemma linearChange_substitution {N : ℕ} (x : Fin (N+1) → A)
    (a : Fin (N+1) → k) (ha : a 0 ≠ 0) :
    (aeval (Fin.cons ((a 0)⁻¹ • x 0)
      (fun i => x i.succ - a i.succ • ((a 0)⁻¹ • x 0)))).comp (linearChange a) =
      aeval (R:=k) x := by
  ext i
  cases i using Fin.cases with
  | zero => simp [linearChange,← Algebra.smul_def,smul_smul,ha]
  | succ i =>
    simp only [AlgHom.comp_apply,linearChange,aeval_X,Fin.cons_succ,map_add,map_mul,
      aeval_C,Fin.cons_zero]
    rw [← Algebra.smul_def,sub_add_cancel]

lemma integral_over_reduced_generators {N d : ℕ} (x : Fin (N+1) → A)
    (a : Fin (N+1) → k) (ha0 : a 0 ≠ 0)
    (f : MvPolynomial (Fin (N+1)) k) (hf : f.IsHomogeneous d)
    (ha : eval a f ≠ 0) (hx : aeval x f = 0) :
    ∀ j, IsIntegral (Algebra.adjoin k (Set.range
      (fun i : Fin N => x i.succ - a i.succ • ((a 0)⁻¹ • x 0)))) (x j) := by
  classical
  let b : A := (a 0)⁻¹ • x 0
  let y : Fin N → A := fun i => x i.succ - a i.succ • b
  let B := Algebra.adjoin k (Set.range y)
  let ψ : MvPolynomial (Fin N) k →ₐ[k] B :=
    aeval (fun i => ⟨y i,Algebra.subset_adjoin (Set.mem_range_self i)⟩)
  let P := finSuccEquiv k N (linearChange a f)
  have hunit : IsUnit P.leadingCoeff := by
    rw [linearChange_leadingCoeff a f hf ha]
    exact ha.isUnit.map C
  let Q := hunit.unit⁻¹.val • P
  have hmon : Q.Monic := Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hunit
  have hroot : Polynomial.aevalTower (aeval (R:=k) y) b P = 0 := by
    rw [finSucc_aeval]
    change ((aeval (Fin.cons b y)).comp (linearChange a)) f = 0
    rw [linearChange_substitution x a ha0]
    exact hx
  have hrootQ : Polynomial.aevalTower (aeval (R:=k) y) b Q = 0 := by
    change Polynomial.aevalTower (aeval y) b (hunit.unit⁻¹.val • P) = 0
    rw [Polynomial.smul_eq_C_mul,map_mul,hroot,mul_zero]
  have hm : ((Polynomial.aeval b).restrictScalars k).comp (Polynomial.mapAlgHom ψ) =
      Polynomial.aevalTower (aeval (R:=k) y) b := by
    apply Polynomial.algHom_ext'
    · apply AlgHom.ext
      intro r
      simp only [AlgHom.comp_apply,Polynomial.CAlgHom_apply,Polynomial.coe_mapAlgHom,
        Polynomial.map_C,AlgHom.restrictScalars_apply,Polynomial.aeval_C,
        Polynomial.aevalTower_C]
      have he : B.val.comp ψ = aeval y := by ext i; simp [ψ]
      exact AlgHom.congr_fun he r
    · simp
  have hb : IsIntegral B b := by
    refine ⟨Polynomial.map ψ.toRingHom Q,hmon.map _,?_⟩
    change (((Polynomial.aeval b).restrictScalars k).comp
      (Polynomial.mapAlgHom ψ)) Q = 0
    rw [hm]
    exact hrootQ
  have hx0 : a 0 • b = x 0 := by simp [b,smul_smul,ha0]
  intro j
  change IsIntegral B (x j)
  cases j using Fin.cases with
  | zero => rw [← hx0]; exact hb.smul (a 0)
  | succ i =>
    have hy : IsIntegral B (y i) := isIntegral_algebraMap
      (x:= (⟨y i,Algebra.subset_adjoin (Set.mem_range_self i)⟩ : B))
    have h := hy.add (hb.smul (a i.succ))
    simpa only [y,sub_add_cancel] using h

end Lech.LinearNormalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedLinearNormalization
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPolynomial
namespace Lech.LinearNormalization
universe u v
variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

lemma exists_direction_first_nonzero [Infinite k] {N d : ℕ}
    (f : MvPolynomial (Fin (N+1)) k) (hf : f.IsHomogeneous d) (hne : f ≠ 0) :
    ∃ a : Fin (N+1) → k, a 0 ≠ 0 ∧ eval a f ≠ 0 := by
  obtain ⟨a,ha⟩ := exists_homogeneous_direction (f*X 0)
    (hf.mul (isHomogeneous_X k (0 : Fin (N+1)))) (mul_ne_zero hne (X_ne_zero _))
  simp only [map_mul,eval_X,ne_eq,mul_eq_zero,not_or] at ha
  exact ⟨a,ha.2,ha.1⟩

lemma integrality_descends_through_adjoin {N s : ℕ}
    (y : Fin N → A) (z : Fin s → A)
    (hz : ∀ j,z j ∈ (Algebra.adjoin k (Set.range y)))
    (hy : ∀ i,IsIntegral (Algebra.adjoin k (Set.range z)) (y i))
    {x : A} (hx : IsIntegral (Algebra.adjoin k (Set.range y)) x) :
    IsIntegral (Algebra.adjoin k (Set.range z)) x := by
  let B := Algebra.adjoin k (Set.range y)
  let C := Algebra.adjoin k (Set.range z)
  have hCB : C ≤ B := Algebra.adjoin_le_iff.mpr (by rintro _ ⟨j,rfl⟩; exact hz j)
  let : Algebra C B := (Subalgebra.inclusion hCB).toRingHom.toAlgebra
  let : IsScalarTower k C B := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  let : IsScalarTower C B A := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have hB : B ≤ (integralClosure C A).restrictScalars k := by
    apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    exact hy i
  let ι : B →ₐ[C] A := IsScalarTower.toAlgHom C B A
  let : Algebra.IsIntegral C B := ⟨fun b =>
    (isIntegral_algHom_iff ι Subtype.val_injective).mp (hB b.property)⟩
  exact isIntegral_trans x hx

 

theorem exists_linear_normalization_oai [Nontrivial A] [Infinite k]
    (G : ℕ → Submodule k A) [GradedAlgebra G] {N : ℕ}
    (x : Fin N → A) (hx : ∀ i,x i ∈ G 1) :
    ∃ s : ℕ, s ≤ N ∧ ∃ z : Fin s → A,
      (∀ j,z j ∈ Submodule.span k (Set.range x)) ∧
      Function.Injective (aeval (R:=k) z) ∧
      (∀ i,IsIntegral (Algebra.adjoin k (Set.range z)) (x i)) := by
  classical
  induction N with
  | zero =>
    refine ⟨0,le_rfl,x,fun i => Fin.elim0 i,?_,fun i => Fin.elim0 i⟩
    exact aeval_injective_iff_of_isEmpty.mpr (algebraMap k A).injective
  | succ N ih =>
    by_cases hind : Function.Injective (aeval (R:=k) x)
    · refine ⟨N+1,le_rfl,x,fun i => Submodule.subset_span (Set.mem_range_self i),hind,?_⟩
      intro i
      exact isIntegral_algebraMap
        (x := (⟨x i,Algebra.subset_adjoin (Set.mem_range_self i)⟩ :
          Algebra.adjoin k (Set.range x)))
    · obtain ⟨d,f,hf0,hf,hrel⟩ := homogeneous_relation G x hx hind
      obtain ⟨a,ha0,ha⟩ := exists_direction_first_nonzero f hf hf0
      let y : Fin N → A := fun i => x i.succ - a i.succ • ((a 0)⁻¹ • x 0)
      have hyspan (i : Fin N) : y i ∈ Submodule.span k (Set.range x) :=
        Submodule.sub_mem _ (Submodule.subset_span (Set.mem_range_self i.succ))
          (Submodule.smul_mem _ _ (Submodule.smul_mem _ _
            (Submodule.subset_span (Set.mem_range_self 0))))
      have hyG (i : Fin N) : y i ∈ G 1 :=
        Submodule.sub_mem _ (hx i.succ)
          (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hx 0)))
      obtain ⟨s,hs,z,hz,hzi,hyi⟩ := ih y hyG
      have hySpanLe : Submodule.span k (Set.range y) ≤ Submodule.span k (Set.range x) :=
        Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hyspan i)
      have hyAdj : Submodule.span k (Set.range y) ≤
          (Algebra.adjoin k (Set.range y)).toSubmodule :=
        Submodule.span_le.mpr Algebra.subset_adjoin
      refine ⟨s,hs.trans (Nat.le_succ N),z,fun j => hySpanLe (hz j),hzi,?_⟩
      intro i
      apply integrality_descends_through_adjoin y z (fun j => hyAdj (hz j)) hyi
      exact integral_over_reduced_generators x a ha0 f hf ha hrel i

end Lech.LinearNormalization

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.Lech.LinearNormalization.exists_linear_normalization_oai.{u, v} := @OAI.Lech.LinearNormalization.exists_linear_normalization_oai.{u, v}
