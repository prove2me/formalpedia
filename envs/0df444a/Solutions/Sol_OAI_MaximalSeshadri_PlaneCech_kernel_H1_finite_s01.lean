-- Prove2me | solution 1 for OAI.MaximalSeshadri.PlaneCech.kernel_H1_finite_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:17:11.653452+00:00
-- url     : https://prove2.me/submissions/ddc9ba8d-d0ef-42bd-89a7-78e77c3c5d4f

import Mathlib
import Definitions.Def_Q223SES008

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlaneCechLinear
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

theorem fullBoundaries_eq_top (A B C : Submodule K M)
    (h : A ⊓ (B ⊔ C) ≤ (A ⊓ B) ⊔ (A ⊓ C)) :
    fullBoundaries A B C = ⊤ := by
  apply top_unique
  rintro ⟨⟨a,b,c⟩,hx⟩ _
  have he : (a : M) + (b : M) + (c : M) = 0 := by exact hx
  have ha : (a : M) ∈ A ⊓ (B ⊔ C) := by
    refine ⟨a.property,?_⟩
    have haa : (a : M) = -(b : M) + -(c : M) := by
      calc
        _ = (a : M) + b + c - b - c := by abel
        _ = _ := by rw [he]; abel
    rw [haa]
    exact Submodule.add_mem_sup (B.neg_mem b.property) (C.neg_mem c.property)
  obtain ⟨u,hu,v,hv,huv⟩ := Submodule.mem_sup.mp (h ha)
  have hb : (b : M) + u ∈ B ⊓ C := by
    refine ⟨B.add_mem b.property hu.2,?_⟩
    have heq : (b : M) + u = -((c : M) + v) := by
      apply eq_neg_iff_add_eq_zero.mpr
      calc
        _ = (a : M) + b + c := by rw [← huv]; abel
        _ = 0 := he
    rw [heq]
    exact C.neg_mem (C.add_mem c.property hv.2)
  have heq : (⟨⟨a,b,c⟩,hx⟩ : cycles A B C) =
      edgeAB A B C ⟨u,hu⟩ + edgeAC A B C ⟨v,hv⟩ +
        edgeBC A B C ⟨(b : M)+u,hb⟩ := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change (a : M) = u + v + 0
      simpa using huv.symm
    apply Prod.ext
    · apply Subtype.ext; change (b : M) = -u + 0 + ((b : M)+u); abel
    · apply Subtype.ext
      change (c : M) = 0 + -v + -((b : M)+u)
      calc
        _ = -(v + (b : M) + u) := by
          apply eq_neg_iff_add_eq_zero.mpr
          calc
            _ = (a : M) + b + c := by rw [← huv]; abel
            _ = 0 := he
        _ = _ := by abel
  rw [heq]
  exact (fullBoundaries A B C).add_mem
    ((fullBoundaries A B C).add_mem
      ((show (edgeAB A B C).range ≤ fullBoundaries A B C from
        le_sup_of_le_left le_sup_left) ⟨_,rfl⟩)
      ((show (edgeAC A B C).range ≤ fullBoundaries A B C from
        le_sup_of_le_left le_sup_right) ⟨_,rfl⟩))
    ((show (edgeBC A B C).range ≤ fullBoundaries A B C from le_sup_right) ⟨_,rfl⟩)

end
end MaximalSeshadri.PlaneCech

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CechPresentation
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K M P : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup P] [Module K P]

theorem finite_quotient_of_kernel_le {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (f : V →ₗ[K] W) (B : Submodule K V) (h : LinearMap.ker f ≤ B) :
    Module.Finite K (V ⧸ B) := by
  let : Module.Finite K (V ⧸ LinearMap.ker f) := Module.Finite.equiv f.quotKerEquivRange.symm
  let q : (V ⧸ LinearMap.ker f) →ₗ[K] (V ⧸ B) :=
    Submodule.mapQ (LinearMap.ker f) B LinearMap.id h
  apply Module.Finite.of_surjective q
  intro x
  obtain ⟨v,rfl⟩ := B.mkQ_surjective x
  exact ⟨(LinearMap.ker f).mkQ v,rfl⟩

theorem finite_H1_of_presentation
    (f : P →ₗ[K] M) (A B C : Submodule K P) (D E F : Submodule K M)
    (hA : ∀ x ∈ A, f x ∈ D) (hB : ∀ x ∈ B, f x ∈ E)
    (hC : ∀ x ∈ C, f x ∈ F)
    (sA : A →ₗ[K] D) (sB : B →ₗ[K] E) (sC : C →ₗ[K] F)
    (eA : ∀ x, (sA x : M) = f x) (eB : ∀ x, (sB x : M) = f x)
    (eC : ∀ x, (sC x : M) = f x)
    (surA : Function.Surjective sA) (surB : Function.Surjective sB)
    (surC : Function.Surjective sC)
    (Q : Submodule K (cycles D E F))
    (hQ : (fullBoundaries A B C).map (cycleMap f A B C D E F hA hB hC) ≤ Q)
    (acyclic : fullBoundaries A B C = ⊤)
    (hfinite : Module.Finite K ((LinearMap.ker f) ⧸
      (((A.comap (LinearMap.ker f).subtype) ⊔ (B.comap (LinearMap.ker f).subtype)) ⊔
        (C.comap (LinearMap.ker f).subtype)))) :
    Module.Finite K ((cycles D E F) ⧸ Q) := by
  obtain ⟨lA,hlA⟩ := sA.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr surA)
  obtain ⟨lB,hlB⟩ := sB.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr surB)
  obtain ⟨lC,hlC⟩ := sC.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr surC)
  have eltA (x : D) : f (lA x) = x := (eA _).symm.trans (congrArg Subtype.val (LinearMap.congr_fun hlA x))
  have eltB (x : E) : f (lB x) = x := (eB _).symm.trans (congrArg Subtype.val (LinearMap.congr_fun hlB x))
  have eltC (x : F) : f (lC x) = x := (eC _).symm.trans (congrArg Subtype.val (LinearMap.congr_fun hlC x))
  let g : cycles D E F →ₗ[K] LinearMap.ker f :=
    { toFun := fun x => ⟨(lA x.1.1 : P) + (lB x.1.2.1 : P) + (lC x.1.2.2 : P),by
        change f _ = 0
        rw [map_add,map_add,eltA,eltB,eltC]
        exact x.2⟩
      map_add' := by intros; ext; simp; abel
      map_smul' := by intros; ext; simp [smul_add] }
  let R := ((A.comap (LinearMap.ker f).subtype) ⊔ (B.comap (LinearMap.ker f).subtype)) ⊔
    (C.comap (LinearMap.ker f).subtype)
  let := hfinite
  apply finite_quotient_of_kernel_le (R.mkQ.comp g) Q
  intro x hx
  have hxR : g x ∈ R := (Submodule.Quotient.mk_eq_zero R).mp hx
  obtain ⟨ab,hab,c,hc,habc⟩ := Submodule.mem_sup.mp hxR
  obtain ⟨a,ha,b,hb,hab'⟩ := Submodule.mem_sup.mp hab
  have heq : (a : P) + (b : P) + (c : P) =
      (lA x.1.1 : P) + (lB x.1.2.1 : P) + (lC x.1.2.2 : P) := by
    change _ = (g x : P)
    rw [← habc,← hab']; rfl
  let y : cycles A B C := ⟨(⟨(lA x.1.1 : P)-a,A.sub_mem (lA _).2 ha⟩,
    ⟨(lB x.1.2.1 : P)-b,B.sub_mem (lB _).2 hb⟩,
    ⟨(lC x.1.2.2 : P)-c,C.sub_mem (lC _).2 hc⟩),by
    change ((lA x.1.1 : P) - a) + ((lB x.1.2.1 : P) - b) + ((lC x.1.2.2 : P) - c) = 0
    calc
      _ = ((lA x.1.1 : P)+(lB x.1.2.1 : P)+(lC x.1.2.2 : P)) - (a+b+c : P) := by abel
      _ = 0 := by rw [heq]; simp⟩
  have hy : cycleMap f A B C D E F hA hB hC y = x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change f ((lA x.1.1 : P)-a) = (x.1.1 : M)
      rw [map_sub,eltA,show f a = 0 from a.2,sub_zero]
    apply Prod.ext
    · apply Subtype.ext
      change f ((lB x.1.2.1 : P)-b) = (x.1.2.1 : M)
      rw [map_sub,eltB,show f b = 0 from b.2,sub_zero]
    · apply Subtype.ext
      change f ((lC x.1.2.2 : P)-c) = (x.1.2.2 : M)
      rw [map_sub,eltC,show f c = 0 from c.2,sub_zero]
  exact hQ (Submodule.mem_map.mpr ⟨y,acyclic ▸ Submodule.mem_top,hy⟩)

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentPlane
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.LaurentPlane
noncomputable section

variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (Ring K) M] [IsScalarTower K (Ring K) M]

theorem quotient_finite [Module.Finite (Ring K) M]
    (A B C : Submodule K M)
    (hA : ∀ z : ℤ × ℤ, 0 ≤ z.2 → ∀ x ∈ A, T (K := K) z • x ∈ A)
    (hB : ∀ z : ℤ × ℤ, 0 ≤ z.1 → ∀ x ∈ B, T (K := K) z • x ∈ B)
    (hC : ∀ z : ℤ × ℤ, z.1 + z.2 ≤ 0 → ∀ x ∈ C, T (K := K) z • x ∈ C)
    (locA : ∀ x : M, ∃ n : ℕ, T (K := K) (0,(n : ℤ)) • x ∈ A)
    (locB : ∀ x : M, ∃ n : ℕ, T (K := K) ((n : ℤ),0) • x ∈ B)
    (locC : ∀ x : M, ∃ n : ℕ, T (K := K) (0,-(n : ℤ)) • x ∈ C) :
    Module.Finite K (M ⧸ ((A ⊔ B) ⊔ C)) := by
  classical
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := Ring K) (M := M)
  choose a ha using fun i : Fin n => locA (s i)
  choose b hb using fun i : Fin n => locB (s i)
  choose c hc using fun i : Fin n => locC (s i)
  let Q := (A ⊔ B) ⊔ C
  let q := Q.mkQ
  let J := (i : Fin n) ×
    (↥(Finset.Icc (-(c i : ℤ) - a i) (b i : ℤ)) ×
     ↥(Finset.Icc (-(c i : ℤ) - b i) (a i : ℤ)))
  let g : J → M ⧸ Q := fun v => q (T (K := K) (v.2.1.val, v.2.2.val) • s v.1)
  let W := Submodule.span K (Set.range g)
  have monomial (i : Fin n) (z : ℤ × ℤ) : q (T (K := K) z • s i) ∈ W := by
    by_cases hzA : (a i : ℤ) ≤ z.2
    · have he : z = (z.1, z.2 - a i) + (0, (a i : ℤ)) := by ext <;> simp
      have hm : T (K := K) z • s i ∈ A := by
        rw [he, T_add, mul_smul]
        exact hA _ (by dsimp; omega) _ (ha i)
      have hq : q (T (K := K) z • s i) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr
        ((show A ≤ Q from le_sup_of_le_left le_sup_left) hm)
      rw [hq]; exact W.zero_mem
    · by_cases hzB : (b i : ℤ) ≤ z.1
      · have he : z = (z.1 - b i, z.2) + ((b i : ℤ), 0) := by ext <;> simp
        have hm : T (K := K) z • s i ∈ B := by
          rw [he, T_add, mul_smul]
          exact hB _ (by dsimp; omega) _ (hb i)
        have hq : q (T (K := K) z • s i) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr
          ((show B ≤ Q from le_sup_of_le_left le_sup_right) hm)
        rw [hq]; exact W.zero_mem
      · by_cases hzC : z.1 + z.2 ≤ -(c i : ℤ)
        · have he : z = (z.1, z.2 + c i) + (0, -(c i : ℤ)) := by ext <;> simp
          have hm : T (K := K) z • s i ∈ C := by
            rw [he, T_add, mul_smul]
            exact hC _ (by dsimp; omega) _ (hc i)
          have hq : q (T (K := K) z • s i) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr
            ((show C ≤ Q from le_sup_right) hm)
          rw [hq]; exact W.zero_mem
        · exact Submodule.subset_span
            ⟨⟨i, ⟨⟨z.1, Finset.mem_Icc.mpr (by omega)⟩,
                   ⟨z.2, Finset.mem_Icc.mpr (by omega)⟩⟩⟩, rfl⟩
  have scalar_monomial (i : Fin n) (p : Ring K) : q (p • s i) ∈ W := by
    induction p using AddMonoidAlgebra.induction_on with
    | of z => exact monomial i z
    | add p p' hp hp' => simpa only [add_smul, map_add] using W.add_mem hp hp'
    | smul d p hp =>
      rw [smul_assoc, map_smul]
      exact W.smul_mem d hp
  have spans : W = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨m, rfl⟩ := Q.mkQ_surjective x
    have hm : m ∈ Submodule.span (Ring K) (Set.range s) := hs ▸ Submodule.mem_top
    have hp : ∀ p : Ring K, q (p • m) ∈ W := by
      induction hm using Submodule.span_induction with
      | mem m hm => obtain ⟨i,rfl⟩ := hm; exact scalar_monomial i
      | zero => intro p; simp
      | add x y hx hy ihx ihy =>
        intro p
        simpa only [smul_add, map_add] using W.add_mem (ihx p) (ihy p)
      | smul a x hx ih => intro p; simpa only [smul_smul] using ih (p * a)
    change q m ∈ W
    simpa only [one_smul] using hp 1
  exact Module.Finite.of_fg_top (spans ▸ Submodule.fg_span (Set.finite_range g))

end
end MaximalSeshadri.LaurentPlane

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlaneFreeCech
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K : Type*} [Field K]

lemma supported_distrib {ι V : Type*} [AddCommGroup V] [Module K V]
    (S T U : Set ι) :
    Finsupp.supported V K S ⊓ (Finsupp.supported V K T ⊔ Finsupp.supported V K U) =
      (Finsupp.supported V K S ⊓ Finsupp.supported V K T) ⊔
        (Finsupp.supported V K S ⊓ Finsupp.supported V K U) := by
  rw [← Finsupp.supported_union, ← Finsupp.supported_inter,
    Set.inter_union_distrib_left, Finsupp.supported_union,
    Finsupp.supported_inter, Finsupp.supported_inter]

lemma pi_inf_sup_distrib {ι : Type*} {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (A B C : ∀ i, Submodule K (V i))
    (h : ∀ i, A i ⊓ (B i ⊔ C i) ≤ (A i ⊓ B i) ⊔ (A i ⊓ C i)) :
    Submodule.pi Set.univ A ⊓ (Submodule.pi Set.univ B ⊔ Submodule.pi Set.univ C) ≤
      (Submodule.pi Set.univ A ⊓ Submodule.pi Set.univ B) ⊔
        (Submodule.pi Set.univ A ⊓ Submodule.pi Set.univ C) := by
  classical
  rintro m ⟨hm,hBC⟩
  obtain ⟨b,hb,c,hc,hbc⟩ := Submodule.mem_sup.mp hBC
  have hm' (i : ι) : m i ∈ (A i ⊓ B i) ⊔ (A i ⊓ C i) := by
    apply h i
    refine ⟨hm i (Set.mem_univ i),?_⟩
    rw [← hbc]
    exact Submodule.add_mem_sup (hb i (Set.mem_univ i)) (hc i (Set.mem_univ i))
  choose x hx y hy hxy using fun i => Submodule.mem_sup.mp (hm' i)
  apply Submodule.mem_sup.mpr
  refine ⟨x,⟨?_,?_⟩,y,⟨?_,?_⟩,?_⟩
  · exact fun i _ => (hx i).1
  · exact fun i _ => (hx i).2
  · exact fun i _ => (hy i).1
  · exact fun i _ => (hy i).2
  · exact funext hxy

lemma laurentSupported_distrib (S T U : Set (ℤ × ℤ)) :
    laurentSupported (K := K) S ⊓ (laurentSupported T ⊔ laurentSupported U) =
      (laurentSupported S ⊓ laurentSupported T) ⊔
        (laurentSupported S ⊓ laurentSupported U) := by
  let e : LaurentPlane.Ring K ≃ₗ[K] (ℤ × ℤ →₀ K) := AddMonoidAlgebra.coeffLinearEquiv K
  have hsup (P Q : Submodule K (ℤ × ℤ →₀ K)) :
      (P ⊔ Q).comap e.toLinearMap = P.comap e.toLinearMap ⊔ Q.comap e.toLinearMap := by
    simp only [Submodule.comap_equiv_eq_map_symm, Submodule.map_sup]
  change (Finsupp.supported K K S).comap e.toLinearMap ⊓
      ((Finsupp.supported K K T).comap e.toLinearMap ⊔
        (Finsupp.supported K K U).comap e.toLinearMap) = _
  rw [← hsup, ← Submodule.comap_inf, supported_distrib, hsup,
    Submodule.comap_inf, Submodule.comap_inf]
  rfl

theorem free_H1_zero (ι : Type*) (d : ℤ) :
    fullBoundaries (freeA (K := K) ι) (freeB ι) (freeC ι d) = ⊤ := by
  apply fullBoundaries_eq_top
  apply pi_inf_sup_distrib
  intro i
  exact le_of_eq (laurentSupported_distrib coneA coneB (coneC d))

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentSupport
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K]

lemma supported_of_support (r : LaurentPlane.Ring K) (S : Set (ℤ × ℤ))
    (h : ∀ w ∈ r.coeff.support, w ∈ S) : r ∈ laurentSupported S := by
  exact (Finsupp.mem_supported K r.coeff).mpr h

lemma support_bound {ι : Type*} [Fintype ι] (m : ι → LaurentPlane.Ring K) :
    ∃ n : ℕ, ∀ i w, w ∈ (m i).coeff.support →
      -(n : ℤ) ≤ w.1 ∧ w.1 ≤ n ∧ -(n : ℤ) ≤ w.2 ∧ w.2 ≤ n := by
  classical
  let n := Finset.univ.sup (fun i => (m i).coeff.support.sup (fun w => w.1.natAbs+w.2.natAbs))
  refine ⟨n,?_⟩
  intro i w hw
  have hn : w.1.natAbs+w.2.natAbs ≤ n :=
    (Finset.le_sup (f := fun w : ℤ × ℤ => w.1.natAbs+w.2.natAbs) hw).trans
      (Finset.le_sup (f := fun i => (m i).coeff.support.sup (fun w => w.1.natAbs+w.2.natAbs))
        (Finset.mem_univ i))
  have ha := Int.natCast_natAbs w.1
  have hb := Int.natCast_natAbs w.2
  have ha' : w.1 ≤ (w.1.natAbs : ℤ) := Int.le_natAbs
  have hb' : w.2 ≤ (w.2.natAbs : ℤ) := Int.le_natAbs
  have haa : -w.1 ≤ (w.1.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -w.1))
  have hbb : -w.2 ≤ (w.2.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -w.2))
  omega

lemma freeA_stable {ι : Type*} (z : ℤ × ℤ) (hz : 0 ≤ z.2)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeA ι) : T (K := K) z • m ∈ freeA ι := by
  intro i hi
  exact supported_monomial_mul coneA coneA z (by intro w hw; change 0 ≤ z.2+w.2; exact add_nonneg hz hw)
    (m i) (hm i hi)

lemma freeB_stable {ι : Type*} (z : ℤ × ℤ) (hz : 0 ≤ z.1)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeB ι) : T (K := K) z • m ∈ freeB ι := by
  intro i hi
  exact supported_monomial_mul coneB coneB z (by intro w hw; change 0 ≤ z.1+w.1; exact add_nonneg hz hw)
    (m i) (hm i hi)

lemma freeC_stable {ι : Type*} (d : ℤ) (z : ℤ × ℤ) (hz : z.1+z.2 ≤ 0)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeC ι d) : T (K := K) z • m ∈ freeC ι d := by
  intro i hi
  apply supported_monomial_mul (coneC d) (coneC d) z _ (m i) (hm i hi)
  intro w hw
  change w.1+w.2 ≤ d at hw
  change z.1+w.1+(z.2+w.2) ≤ d
  omega

lemma freeA_clearing {ι : Type*} [Fintype ι] (m : ι → LaurentPlane.Ring K) :
    ∃ n : ℕ, T (K := K) (0,(n : ℤ)) • m ∈ freeA ι := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨n,fun i hi => ?_⟩
  apply supported_monomial_mul ((m i).coeff.support : Set (ℤ × ℤ)) coneA (0,(n : ℤ)) _ (m i)
    (supported_of_support (m i) _ (fun w hw => hw))
  intro w hw
  change 0 ≤ (n : ℤ)+w.2
  have := (hn i w hw).2.2.1
  omega

lemma freeB_clearing {ι : Type*} [Fintype ι] (m : ι → LaurentPlane.Ring K) :
    ∃ n : ℕ, T (K := K) ((n : ℤ),0) • m ∈ freeB ι := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨n,fun i hi => ?_⟩
  apply supported_monomial_mul ((m i).coeff.support : Set (ℤ × ℤ)) coneB ((n : ℤ),0) _ (m i)
    (supported_of_support (m i) _ (fun w hw => hw))
  intro w hw
  change 0 ≤ (n : ℤ)+w.1
  have := (hn i w hw).1
  omega

lemma freeC_clearing {ι : Type*} [Fintype ι] (d : ℤ) (m : ι → LaurentPlane.Ring K) :
    ∃ n : ℕ, T (K := K) (0,-(n : ℤ)) • m ∈ freeC ι d := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨2*n+(-d).toNat,fun i hi => ?_⟩
  apply supported_monomial_mul ((m i).coeff.support : Set (ℤ × ℤ)) (coneC d)
    (0,-((2*n+(-d).toNat : ℕ) : ℤ)) _ (m i)
    (supported_of_support (m i) _ (fun w hw => hw))
  intro w hw
  change 0+w.1+(-((2*n+(-d).toNat : ℕ) : ℤ)+w.2) ≤ d
  have := (hn i w hw).2.1
  have := (hn i w hw).2.2.2
  omega

theorem laurent_noetherian : IsNoetherianRing (LaurentPlane.Ring K) := by
  let : Algebra.FiniteType K (LaurentPlane.Ring K) := inferInstance
  exact Algebra.FiniteType.isNoetherianRing K _

theorem submodule_top_finite {ι : Type*} [Fintype ι]
    (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    Module.Finite K (N ⧸
      (((freeA ι).comap (N.subtype.restrictScalars K) ⊔
        (freeB ι).comap (N.subtype.restrictScalars K)) ⊔
        (freeC ι d).comap (N.subtype.restrictScalars K))) := by
  let : IsNoetherianRing (LaurentPlane.Ring K) := laurent_noetherian
  let : Module.Finite (LaurentPlane.Ring K) N := inferInstance
  apply LaurentPlane.quotient_finite (K := K) (M := N)
  · intro z hz x hx
    change (x : ι → LaurentPlane.Ring K) ∈ freeA ι at hx
    change T (K := K) z • (x : ι → LaurentPlane.Ring K) ∈ freeA ι
    exact freeA_stable (K := K) (ι := ι) z hz (x : ι → LaurentPlane.Ring K) hx
  · intro z hz x hx
    change (x : ι → LaurentPlane.Ring K) ∈ freeB ι at hx
    change T (K := K) z • (x : ι → LaurentPlane.Ring K) ∈ freeB ι
    exact freeB_stable (K := K) (ι := ι) z hz (x : ι → LaurentPlane.Ring K) hx
  · intro z hz x hx
    change (x : ι → LaurentPlane.Ring K) ∈ freeC ι d at hx
    change T (K := K) z • (x : ι → LaurentPlane.Ring K) ∈ freeC ι d
    exact freeC_stable (K := K) (ι := ι) d z hz (x : ι → LaurentPlane.Ring K) hx
  · intro x
    exact freeA_clearing (x : ι → LaurentPlane.Ring K)
  · intro x
    exact freeB_clearing (x : ι → LaurentPlane.Ring K)
  · intro x
    exact freeC_clearing d (x : ι → LaurentPlane.Ring K)

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricFreeMap
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

lemma smul_supported_mem (V : Submodule K M) (S : Set (ℤ × ℤ)) (e : M)
    (h : ∀ z ∈ S, T (K := K) z • e ∈ V)
    (r : LaurentPlane.Ring K) (hr : r ∈ laurentSupported S) : r • e ∈ V := by
  rw [laurentSupported_eq_span] at hr
  induction hr using Submodule.span_induction with
  | mem r hr => obtain ⟨z,hz,rfl⟩ := hr; exact h z hz
  | zero => simp
  | add r s hr hs ih ih' => simpa only [add_smul] using V.add_mem ih ih'
  | smul a r hr ih => simpa only [smul_assoc] using V.smul_mem a ih

lemma freeMap_supported {ι : Type*} [Fintype ι] (e : ι → M) (S : Set (ℤ × ℤ))
    (V : Submodule K M) (he : ∀ i z, z ∈ S → T (K := K) z • e i ∈ V)
    (m : ι → LaurentPlane.Ring K)
    (hm : ∀ i, m i ∈ laurentSupported S) : freeMap e m ∈ V := by
  apply Submodule.sum_mem
  intro i hi
  exact smul_supported_mem V S (e i) (he i) (m i) (hm i)

omit [Module K M] [IsScalarTower K (LaurentPlane.Ring K) M] in
lemma freeMap_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → M) (i : ι) (r : LaurentPlane.Ring K) :
    freeMap e (Pi.single i r) = r • e i := by
  simp [freeMap,Pi.single_apply]

lemma single_monomial_mem {ι : Type*} [DecidableEq ι] (S : Set (ℤ × ℤ))
    (i : ι) (z : ℤ × ℤ) (hz : z ∈ S) :
    Pi.single i (T (K := K) z) ∈ Submodule.pi Set.univ (fun _ => laurentSupported S) := by
  intro j hj
  by_cases h : j=i
  · subst j
    simp only [Pi.single_eq_same]
    rw [laurentSupported_eq_span]
    exact Submodule.subset_span ⟨z,hz,rfl⟩
  · simp [Pi.single_eq_of_ne h]

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricPresentation
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M]

lemma clearing_monotone (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    (i j : Fin 3) (x : M) {n d : ℕ} (hd : d ≤ n)
    (hx : T (K := K) (d • (weight j-weight i)) • x ∈ V i) :
    T (K := K) (n • (weight j-weight i)) • x ∈ V i := by
  have he : n • (weight j-weight i) = (n-d) • (weight j-weight i) + d • (weight j-weight i) := by
    rw [← add_nsmul,Nat.sub_add_cancel hd]
  rw [he,T_add,mul_smul]
  exact stable i _ (direction_mem i j (n-d)) _ hx

theorem exists_standard_generators (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    {ι : Fin 3 → Type*} [∀ i, Fintype (ι i)] (g : ∀ i, ι i → M)
    (hg : ∀ i a, g i a ∈ V i)
    (clear : ∀ i j (x : M), x ∈ V j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ V i) :
    ∃ n : ℕ, ∀ (j : Fin 3) (a : ι j) (i : Fin 3),
      T (K := K) (-(n • weight i)) • (T (K := K) (n • weight j) • g j a) ∈ V i := by
  classical
  choose d hd using fun (i j : Fin 3) (a : ι j) => clear i j (g j a) (hg j a)
  let n := Finset.univ.sup (fun p : (Fin 3) × (Σ j, ι j) => d p.1 p.2.1 p.2.2)
  refine ⟨n,?_⟩
  intro j a i
  have hle : d i j a ≤ n := Finset.le_sup (f := fun p : (Fin 3) × (Σ j, ι j) => d p.1 p.2.1 p.2.2)
    (Finset.mem_univ (i,⟨j,a⟩))
  have he : -(n • weight i) + n • weight j = n • (weight j-weight i) := by
    rw [nsmul_sub]; abel
  rw [← mul_smul,← T_add,he]
  exact clearing_monotone V stable i j (g j a) hle (hd i j a)

lemma standard_at_zero (V : Fin 3 → Submodule K M) (n : ℕ) (e : M)
    (he : StandardGenerator V n e) : e ∈ V 0 := by
  simpa [weight, show T (K := K) (0,0) = 1 from T_zero] using he 0

lemma standard_at_one (V : Fin 3 → Submodule K M) (n : ℕ) (e : M)
    (he : StandardGenerator V n e) : T (K := K) (-(n : ℤ),0) • e ∈ V 1 := by
  simpa [weight] using he 1

lemma standard_at_two (V : Fin 3 → Submodule K M) (n : ℕ) (e : M)
    (he : StandardGenerator V n e) : T (K := K) (0,-(n : ℤ)) • e ∈ V 2 := by
  simpa [weight] using he 2

lemma standard_vertex_zero (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    (n : ℕ) (e : M) (he : StandardGenerator V n e) (z : ℤ × ℤ)
    (hz : z ∈ coneA ∩ coneB) : T (K := K) z • e ∈ V 0 :=
  stable 0 z hz e (standard_at_zero V n e he)

lemma standard_vertex_one (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    (n : ℕ) (e : M) (he : StandardGenerator V n e) (z : ℤ × ℤ)
    (hz : z ∈ coneA ∩ coneC (-(n : ℤ))) : T (K := K) z • e ∈ V 1 := by
  have h : z + ((n : ℤ),0) ∈ vertexCone 1 := by
    simp [vertexCone,coneA,coneB,coneC] at hz ⊢
    omega
  have heq : z + ((n : ℤ),0) + (-(n : ℤ),0) = z := by ext <;> simp
  have hm := stable 1 _ h _ (standard_at_one V n e he)
  rw [← mul_smul,← T_add,heq] at hm
  exact hm

lemma standard_vertex_two (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    (n : ℕ) (e : M) (he : StandardGenerator V n e) (z : ℤ × ℤ)
    (hz : z ∈ coneB ∩ coneC (-(n : ℤ))) : T (K := K) z • e ∈ V 2 := by
  have h : z + (0,(n : ℤ)) ∈ vertexCone 2 := by
    simp [vertexCone,coneA,coneB,coneC] at hz ⊢
    omega
  have heq : z + (0,(n : ℤ)) + (0,-(n : ℤ)) = z := by ext <;> simp
  have hm := stable 2 _ h _ (standard_at_two V n e he)
  rw [← mul_smul,← T_add,heq] at hm
  exact hm

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricSpan
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

lemma shift_span_mem {ι : Type*} (S U : Set (ℤ × ℤ)) (g : ι → M)
    (z : ℤ × ℤ) (hz : ∀ w ∈ S, z+w ∈ U) (x : M) (hx : x ∈ monomialSpan (K := K) S g) :
    T (K := K) z • x ∈ monomialSpan (K := K) U g := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,w,hw,rfl⟩ := hx
    rw [← mul_smul,← T_add]
    exact Submodule.subset_span ⟨i,z+w,hz w hw,rfl⟩
  | zero => simp
  | add x y hx hy ih ih' => simpa only [smul_add] using (monomialSpan (K := K) U g).add_mem ih ih'
  | smul a x hx ih =>
    rw [smul_comm]
    exact (monomialSpan (K := K) U g).smul_mem a ih

omit [IsScalarTower K (LaurentPlane.Ring K) M] in
lemma monomialSpan_le {ι : Type*} (S : Set (ℤ × ℤ)) (g : ι → M)
    (V : Submodule K M) (hg : ∀ i, g i ∈ V)
    (h : ∀ z ∈ S, ∀ x ∈ V, T (K := K) z • x ∈ V) : monomialSpan (K := K) S g ≤ V := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,z,hz,rfl⟩
  exact h z hz _ (hg i)

omit [IsScalarTower K (LaurentPlane.Ring K) M] in
lemma generator_mem_span {ι : Type*} (S : Set (ℤ × ℤ)) (hS : (0 : ℤ × ℤ) ∈ S)
    (g : ι → M) (i : ι) : g i ∈ monomialSpan (K := K) S g := by
  exact Submodule.subset_span ⟨i,0,hS,by simp⟩

theorem finite_monomial_generators {σ N : Type*} [AddCommGroup N] [Module K N]
    [Module (MvPolynomial σ K) N] [IsScalarTower K (MvPolynomial σ K) N]
    [Module.Finite (MvPolynomial σ K) N]
    (i : Fin 3) (v : σ → Fin 3) (F : N →ₗ[K] M)
    (stable : ∀ z ∈ vertexCone i, ∀ x ∈ F.range, T (K := K) z • x ∈ F.range)
    (hvars : ∀ j n, F ((MvPolynomial.X j : MvPolynomial σ K) • n) = T (K := K) (weight (v j)-weight i) • F n) :
    ∃ d : ℕ, ∃ g : Fin d → M, (∀ a, g a ∈ F.range) ∧
      F.range = monomialSpan (K := K) (vertexCone i) g := by
  obtain ⟨d,g,hg⟩ := Module.Finite.exists_fin (R := MvPolynomial σ K) (M := N)
  let W := monomialSpan (K := K) (vertexCone i) (fun a => F (g a))
  have hzero : (0 : ℤ × ℤ) ∈ vertexCone i := by simpa using direction_mem i i 0
  have hstable : ∀ j x, x ∈ W → T (K := K) (weight (v j)-weight i) • x ∈ W := by
    intro j x hx
    apply shift_span_mem _ _ _ _ _ x hx
    intro w hw
    exact vertexCone_add i (by simpa using direction_mem i (v j) 1) hw
  have hpoly (p : MvPolynomial σ K) (n : N) (hn : F n ∈ W) : F (p • n) ∈ W := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq,IsScalarTower.algebraMap_smul,map_smul]
      exact W.smul_mem a hn
    | add p q hp hq => simpa only [add_smul,map_add] using W.add_mem hp hq
    | mul_X p j hp =>
      rw [mul_comm,mul_smul,hvars]
      exact hstable j _ hp
  refine ⟨d,fun a => F (g a),fun a => ⟨g a,rfl⟩,le_antisymm ?_ ?_⟩
  · rintro _ ⟨n,rfl⟩
    have hn : n ∈ Submodule.span (MvPolynomial σ K) (Set.range g) := hg ▸ Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem n hn =>
      obtain ⟨a,rfl⟩ := hn
      exact generator_mem_span _ hzero _ a
    | zero => simp
    | add n m hn hm ih ih' => simpa only [map_add] using W.add_mem ih ih'
    | smul p n hn ih => exact hpoly p n ih
  · exact monomialSpan_le _ _ F.range (fun a => ⟨g a,rfl⟩) stable

theorem localized_span {ι : Type*} (S U : Set (ℤ × ℤ)) (g : ι → M)
    (A : Submodule K M) (hg : ∀ a, g a ∈ A)
    (stable : ∀ z ∈ U, ∀ x ∈ A, T (K := K) z • x ∈ A)
    (clear : ∀ x ∈ A, ∃ z : ℤ × ℤ,
      T (K := K) z • x ∈ monomialSpan (K := K) S g ∧ ∀ w ∈ S, -z+w ∈ U) :
    A = monomialSpan (K := K) U g := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z,hz,hshift⟩ := clear x hx
    have hm := shift_span_mem S U g (-z) hshift _ hz
    rw [← mul_smul,← T_add,neg_add_cancel,T_zero,one_smul] at hm
    exact hm
  · exact monomialSpan_le U g A hg stable

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_FreePresentation
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M P : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup P] [Module K P]

lemma cycleMap_fullBoundaries_le
    (f : P →ₗ[K] M) (A B C : Submodule K P) (D E F : Submodule K M)
    (hA : ∀ x ∈ A, f x ∈ D) (hB : ∀ x ∈ B, f x ∈ E)
    (hC : ∀ x ∈ C, f x ∈ F) (Q : Submodule K (cycles D E F))
    (hAB : ∀ x : ↥(A ⊓ B), edgeAB D E F ⟨f x,⟨hA _ x.2.1,hB _ x.2.2⟩⟩ ∈ Q)
    (hAC : ∀ x : ↥(A ⊓ C), edgeAC D E F ⟨f x,⟨hA _ x.2.1,hC _ x.2.2⟩⟩ ∈ Q)
    (hBC : ∀ x : ↥(B ⊓ C), edgeBC D E F ⟨f x,⟨hB _ x.2.1,hC _ x.2.2⟩⟩ ∈ Q) :
    (fullBoundaries A B C).map (cycleMap f A B C D E F hA hB hC) ≤ Q := by
  rw [fullBoundaries,Submodule.map_sup,Submodule.map_sup]
  apply sup_le
  · apply sup_le
    · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
      convert hAB x using 1
      all_goals try with_reducible_and_instances rfl
      ext <;> simp [cycleMap,edgeAB]
    · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
      convert hAC x using 1
      all_goals try with_reducible_and_instances rfl
      ext <;> simp [cycleMap,edgeAC]
  · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    convert hBC x using 1
    all_goals try with_reducible_and_instances rfl
    ext <;> simp [cycleMap,edgeBC]

theorem finite_H1_of_free_presentation {ι : Type*} [Fintype ι]
    [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]
    (f : (ι → LaurentPlane.Ring K) →ₗ[LaurentPlane.Ring K] M) (d : ℤ)
    (D E F : Submodule K M)
    (hA : ∀ x ∈ freeA ι, f x ∈ D) (hB : ∀ x ∈ freeB ι, f x ∈ E)
    (hC : ∀ x ∈ freeC ι d, f x ∈ F)
    (surA : ∀ x ∈ D, ∃ y ∈ freeA ι, f y = x)
    (surB : ∀ x ∈ E, ∃ y ∈ freeB ι, f y = x)
    (surC : ∀ x ∈ F, ∃ y ∈ freeC ι d, f y = x)
    (Q : Submodule K (cycles D E F))
    (hQ : (fullBoundaries (freeA ι) (freeB ι) (freeC ι d)).map
      (cycleMap (f.restrictScalars K) (freeA ι) (freeB ι) (freeC ι d) D E F hA hB hC) ≤ Q) :
    Module.Finite K ((cycles D E F) ⧸ Q) := by
  let sA : freeA (K := K) ι →ₗ[K] D :=
    ((f.restrictScalars K).domRestrict (freeA ι)).codRestrict D (fun x => hA x x.2)
  let sB : freeB (K := K) ι →ₗ[K] E :=
    ((f.restrictScalars K).domRestrict (freeB ι)).codRestrict E (fun x => hB x x.2)
  let sC : freeC (K := K) ι d →ₗ[K] F :=
    ((f.restrictScalars K).domRestrict (freeC ι d)).codRestrict F (fun x => hC x x.2)
  apply finite_H1_of_presentation (f.restrictScalars K) (freeA ι) (freeB ι) (freeC ι d)
    D E F hA hB hC sA sB sC (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) _ _ _ Q hQ
    (free_H1_zero ι d)
  · exact submodule_top_finite (LinearMap.ker f) d
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy,he⟩ := surA x hx
    exact ⟨⟨y,hy⟩,Subtype.ext he⟩
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy,he⟩ := surB x hx
    exact ⟨⟨y,hy⟩,Subtype.ext he⟩
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy,he⟩ := surC x hx
    exact ⟨⟨y,hy⟩,Subtype.ext he⟩

end
end MaximalSeshadri.PlaneCech

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricH1
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                 
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M]

lemma laurentSupported_inter (S U : Set (ℤ × ℤ)) :
    laurentSupported (K := K) (S ∩ U) = laurentSupported S ⊓ laurentSupported U := by
  simp only [laurentSupported,Finsupp.supported_inter,Submodule.comap_inf]

lemma edgeAB_mem_vertexBoundaries (A B C : Submodule K M) (V : Fin 3 → Submodule K M)
    (x : ↥(A ⊓ B)) (hx : (x : M) ∈ V 0) : edgeAB A B C x ∈ vertexBoundaries A B C V := by
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩

lemma edgeAC_mem_vertexBoundaries (A B C : Submodule K M) (V : Fin 3 → Submodule K M)
    (x : ↥(A ⊓ C)) (hx : (x : M) ∈ V 1) : edgeAC A B C x ∈ vertexBoundaries A B C V := by
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_right
  exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩

lemma edgeBC_mem_vertexBoundaries (A B C : Submodule K M) (V : Fin 3 → Submodule K M)
    (x : ↥(B ⊓ C)) (hx : (x : M) ∈ V 2) : edgeBC A B C x ∈ vertexBoundaries A B C V := by
  apply Submodule.mem_sup_right
  exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩

variable [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

lemma freeMap_vertex_relations {ι : Type*} [Fintype ι]
    (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    (n : ℕ) (e : ι → M) (he : ∀ a, StandardGenerator V n (e a))
    (A B C : Submodule K M)
    (hA : ∀ x ∈ freeA ι, freeMap e x ∈ A)
    (hB : ∀ x ∈ freeB ι, freeMap e x ∈ B)
    (hC : ∀ x ∈ freeC ι (-(n : ℤ)), freeMap e x ∈ C) :
    (fullBoundaries (freeA ι) (freeB ι) (freeC ι (-(n : ℤ)))).map
      (cycleMap ((freeMap e).restrictScalars K) (freeA ι) (freeB ι) (freeC ι (-(n : ℤ)))
        A B C hA hB hC) ≤ vertexBoundaries A B C V := by
  apply cycleMap_fullBoundaries_le
  · intro x
    apply edgeAB_mem_vertexBoundaries
    apply freeMap_supported e (coneA ∩ coneB)
    · exact fun a z hz => standard_vertex_zero V stable n (e a) (he a) z hz
    · intro a
      rw [laurentSupported_inter]
      exact ⟨x.2.1 a (Set.mem_univ a),x.2.2 a (Set.mem_univ a)⟩
  · intro x
    apply edgeAC_mem_vertexBoundaries
    apply freeMap_supported e (coneA ∩ coneC (-(n : ℤ)))
    · exact fun a z hz => standard_vertex_one V stable n (e a) (he a) z hz
    · intro a
      rw [laurentSupported_inter]
      exact ⟨x.2.1 a (Set.mem_univ a),x.2.2 a (Set.mem_univ a)⟩
  · intro x
    apply edgeBC_mem_vertexBoundaries
    apply freeMap_supported e (coneB ∩ coneC (-(n : ℤ)))
    · exact fun a z hz => standard_vertex_two V stable n (e a) (he a) z hz
    · intro a
      rw [laurentSupported_inter]
      exact ⟨x.2.1 a (Set.mem_univ a),x.2.2 a (Set.mem_univ a)⟩

theorem toric_H1_finite (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    {ι : Fin 3 → Type*} [∀ i, Fintype (ι i)] (g : ∀ i, ι i → M)
    (hg : ∀ i a, g i a ∈ V i)
    (clear : ∀ i j (x : M), x ∈ V j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ V i)
    (A B C : Submodule K M)
    (hA : ∀ z ∈ coneA, ∀ x ∈ A, T (K := K) z • x ∈ A)
    (hB : ∀ z ∈ coneB, ∀ x ∈ B, T (K := K) z • x ∈ B)
    (hC : ∀ z ∈ coneC 0, ∀ x ∈ C, T (K := K) z • x ∈ C)
    (incA : V 0 ≤ A) (incB : V 0 ≤ B) (incC : V 1 ≤ C)
    (genA : A = monomialSpan (K := K) coneA (g 0)) (genB : B = monomialSpan (K := K) coneB (g 0))
    (genC : C = monomialSpan (K := K) (coneC 0) (g 1)) :
    Module.Finite K ((cycles A B C) ⧸ vertexBoundaries A B C V) := by
  classical
  obtain ⟨n,hn⟩ := exists_standard_generators V stable g hg clear
  let e : (Σ i, ι i) → M := fun a => T (K := K) (n • weight a.1) • g a.1 a.2
  have he (a : Σ i, ι i) : StandardGenerator V n (e a) := hn a.1 a.2
  have fA : ∀ x ∈ freeA (K := K) (Σ i, ι i), freeMap e x ∈ A := by
    intro x hx
    apply freeMap_supported e coneA A
    · intro a z hz
      exact hA z hz _ (incA (standard_at_zero V n (e a) (he a)))
    · exact fun a => hx a (Set.mem_univ a)
  have fB : ∀ x ∈ freeB (K := K) (Σ i, ι i), freeMap e x ∈ B := by
    intro x hx
    apply freeMap_supported e coneB B
    · intro a z hz
      exact hB z hz _ (incB (standard_at_zero V n (e a) (he a)))
    · exact fun a => hx a (Set.mem_univ a)
  have fC : ∀ x ∈ freeC (K := K) (Σ i, ι i) (-(n : ℤ)), freeMap e x ∈ C := by
    intro x hx
    apply freeMap_supported e (coneC (-(n : ℤ))) C
    · intro a z hz
      have hz' : z+((n : ℤ),0) ∈ coneC 0 := by
        change z.1+(n : ℤ)+(z.2+0) ≤ 0
        change z.1+z.2 ≤ -(n : ℤ) at hz
        omega
      have hm := hC _ hz' _ (incC (standard_at_one V n (e a) (he a)))
      rw [← mul_smul,← T_add,show z + ((n : ℤ),0) + (-(n : ℤ),0) = z by ext <;> simp] at hm
      exact hm
    · exact fun a => hx a (Set.mem_univ a)
  have e0 (a : ι 0) : e ⟨0,a⟩ = g 0 a := by
    have h : n • weight 0 = (0,0) := by ext <;> simp [weight]
    simp only [e,h]
    rw [show T (K := K) (0,0) = 1 from rfl,one_smul]
  have e1 (a : ι 1) : e ⟨1,a⟩ = T (K := K) ((n : ℤ),0) • g 1 a := by
    have h : n • weight 1 = ((n : ℤ),0) := by ext <;> simp [weight]
    simp only [e,h]
  apply finite_H1_of_free_presentation (freeMap e) (-(n : ℤ)) A B C fA fB fC _ _ _
    (vertexBoundaries A B C V) (freeMap_vertex_relations V stable n e he A B C fA fB fC)
  · intro x hx
    have hs : A ≤ (freeA (K := K) (Σ i, ι i)).map ((freeMap e).restrictScalars K) := by
      rw [genA]
      apply Submodule.span_le.mpr
      rintro _ ⟨a,z,hz,rfl⟩
      refine ⟨Pi.single ⟨0,a⟩ (T z),single_monomial_mem coneA _ _ hz,?_⟩
      rw [LinearMap.restrictScalars_apply,freeMap_single,e0]
    exact Submodule.mem_map.mp (hs hx)
  · intro x hx
    have hs : B ≤ (freeB (K := K) (Σ i, ι i)).map ((freeMap e).restrictScalars K) := by
      rw [genB]
      apply Submodule.span_le.mpr
      rintro _ ⟨a,z,hz,rfl⟩
      refine ⟨Pi.single ⟨0,a⟩ (T z),single_monomial_mem coneB _ _ hz,?_⟩
      rw [LinearMap.restrictScalars_apply,freeMap_single,e0]
    exact Submodule.mem_map.mp (hs hx)
  · intro x hx
    have hs : C ≤ (freeC (K := K) (Σ i, ι i) (-(n : ℤ))).map ((freeMap e).restrictScalars K) := by
      rw [genC]
      apply Submodule.span_le.mpr
      rintro _ ⟨a,z,hz,rfl⟩
      have hz' : z + (-(n : ℤ),0) ∈ coneC (-(n : ℤ)) := by
        change z.1+ -(n : ℤ)+(z.2+0) ≤ -(n : ℤ)
        change z.1+z.2 ≤ 0 at hz
        omega
      refine ⟨Pi.single ⟨1,a⟩ (T (z+(-(n : ℤ),0))),single_monomial_mem _ _ _ hz',?_⟩
      rw [LinearMap.restrictScalars_apply,freeMap_single,e1,← mul_smul,← T_add,
        show z + (-(n : ℤ),0) + ((n : ℤ),0) = z by ext <;> simp]
    exact Submodule.mem_map.mp (hs hx)

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.LaurentPlane
variable {K : Type*} [CommRing K]
lemma T_nsmul (n : ℕ) (z : ℤ × ℤ) : T (K := K) (n • z) = (T z)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul,T_add,ih,pow_succ]
end MaximalSeshadri.LaurentPlane

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_ToricPolynomial
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K]

lemma vertexPolynomial_monomial (i : Fin 3) (z : ℤ × ℤ) (hz : z ∈ vertexCone i) :
    ∃ p : MvPolynomial (Fin 3) K, vertexPolynomial i p = T z := by
  have lift (j l : Fin 3) (n m : ℕ) (he : n • (weight j-weight i) + m • (weight l-weight i) = z) :
      ∃ p : MvPolynomial (Fin 3) K, vertexPolynomial i p = T z := by
    refine ⟨MvPolynomial.X j ^ n * MvPolynomial.X l ^ m,?_⟩
    rw [map_mul,map_pow,map_pow,vertexPolynomial_X,vertexPolynomial_X,← T_nsmul,← T_nsmul,← T_add,he]
  fin_cases i
  · apply lift 1 2 z.1.toNat z.2.toNat
    have ha : 0 ≤ z.1 := hz.2
    have hb : 0 ≤ z.2 := hz.1
    ext <;> simp [weight,Int.toNat_of_nonneg ha,Int.toNat_of_nonneg hb]
  · apply lift 0 2 (-(z.1+z.2)).toNat z.2.toNat
    have ha : 0 ≤ -(z.1+z.2) := by have := hz.2; change z.1+z.2 ≤ 0 at this; omega
    have hb : 0 ≤ z.2 := hz.1
    ext <;> simp [weight,Int.toNat_of_nonneg hb]
    omega
  · apply lift 0 1 (-(z.1+z.2)).toNat z.1.toNat
    have ha : 0 ≤ -(z.1+z.2) := by have := hz.2; change z.1+z.2 ≤ 0 at this; omega
    have hb : 0 ≤ z.1 := hz.1
    ext <;> simp [weight,Int.toNat_of_nonneg hb]
    omega

variable {M : Type*} [AddCommGroup M] [Module K M]
  [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

lemma vertexModule_tower (i : Fin 3) :
    letI := vertexModule (K := K) (M := M) i
    IsScalarTower K (MvPolynomial (Fin 3) K) M := by
  let := vertexModule (K := K) (M := M) i
  apply IsScalarTower.of_algebraMap_smul
  intro a m
  change vertexPolynomial i (algebraMap K (MvPolynomial (Fin 3) K) a) • m = a • m
  rw [AlgHom.commutes,IsScalarTower.algebraMap_smul]

lemma vertexSubmodule_finite (i : Fin 3) (V : Submodule K M)
    (stable : ∀ z ∈ vertexCone i, ∀ x ∈ V, T (K := K) z • x ∈ V)
    {ι : Type*} [Finite ι] (g : ι → M) (hg : ∀ a, g a ∈ V)
    (hgen : V = monomialSpan (K := K) (vertexCone i) g) :
    letI := vertexModule (K := K) (M := M) i
    Module.Finite (MvPolynomial (Fin 3) K) (vertexSubmodule i V stable) := by
  let := vertexModule (K := K) (M := M) i
  let := vertexModule_tower (K := K) (M := M) i
  let W := vertexSubmodule i V stable
  let H := Submodule.span (MvPolynomial (Fin 3) K) (Set.range g)
  have he : W = H := by
    apply le_antisymm
    · intro x hx
      change x ∈ V at hx
      rw [hgen] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a,z,hz,rfl⟩ := hx
        obtain ⟨p,hp⟩ := vertexPolynomial_monomial (K := K) i z hz
        have hh := H.smul_mem p (Submodule.subset_span (Set.mem_range_self a))
        change vertexPolynomial i p • g a ∈ H at hh
        rwa [hp] at hh
      | zero => exact H.zero_mem
      | add x y hx hy ih ih' => exact H.add_mem ih ih'
      | smul a x hx ih => exact (H.restrictScalars K).smul_mem a ih
    · apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      exact hg a
  change Module.Finite (MvPolynomial (Fin 3) K) W
  rw [he]
  exact Module.Finite.span_of_finite _ (Set.finite_range g)

end
end MaximalSeshadri.PlaneCech

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_FreeVertices
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K]

lemma freeVertex_zero (ι : Type*) (d : ℤ) : freeVertex (K := K) ι d 0 = freeA ι ⊓ freeB ι := by
  have he : twistCone d 0 = coneA ∩ coneB := by
    ext z
    simp [twistCone,weight,vertexCone,coneA,coneB]
  ext m
  simp only [freeVertex,freeA,freeB,he,laurentSupported_inter,Submodule.mem_inf,Submodule.mem_pi]
  aesop
lemma freeVertex_one (ι : Type*) (d : ℤ) : freeVertex (K := K) ι d 1 = freeA ι ⊓ freeC ι d := by
  have he : twistCone d 1 = coneA ∩ coneC d := by
    ext z
    simp [twistCone,weight,vertexCone,coneA,coneC]
    omega
  ext m
  simp only [freeVertex,freeA,freeC,he,laurentSupported_inter,Submodule.mem_inf,Submodule.mem_pi]
  aesop
lemma freeVertex_two (ι : Type*) (d : ℤ) : freeVertex (K := K) ι d 2 = freeB ι ⊓ freeC ι d := by
  have he : twistCone d 2 = coneB ∩ coneC d := by
    ext z
    simp [twistCone,weight,vertexCone,coneB,coneC]
    omega
  ext m
  simp only [freeVertex,freeB,freeC,he,laurentSupported_inter,Submodule.mem_inf,Submodule.mem_pi]
  aesop

lemma freeVertex_monomial_generators {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℤ) (i : Fin 3) :
    freeVertex (K := K) ι d i = monomialSpan (K := K) (vertexCone i)
      (fun a : ι => Pi.single a (T (d • weight i))) := by
  let g : ι → (ι → LaurentPlane.Ring K) := fun a => Pi.single a (T (d • weight i))
  have singleton (a : ι) (z : ℤ × ℤ) : T (K := K) z • g a = Pi.single a (T (z+d • weight i)) := by
    ext b
    by_cases hb : b=a
    · subst b
      simp only [Pi.smul_apply,g,Pi.single_eq_same,smul_eq_mul,← T_add]
    · simp [g,Pi.single_eq_of_ne hb]
  apply le_antisymm
  · intro m hm
    let V := monomialSpan (K := K) (vertexCone i) g
    have hc (a : ι) : (m a) • ((Pi.single a (1 : LaurentPlane.Ring K) : ι → LaurentPlane.Ring K)) ∈ V := by
      apply smul_supported_mem V (twistCone d i) _ _ (m a) (hm a (Set.mem_univ a))
      intro z hz
      have hh : T (K := K) (z-d • weight i) • g a = T (K := K) z • (Pi.single a (1 : LaurentPlane.Ring K) : ι → LaurentPlane.Ring K) := by
        rw [singleton,sub_add_cancel]
        ext b
        by_cases hb : b=a
        · subst b; simp
        · simp [Pi.single_eq_of_ne hb]
      rw [← hh]
      exact Submodule.subset_span ⟨a,z-d • weight i,hz,rfl⟩
    have he : ∑ a, (m a) • (Pi.single a (1 : LaurentPlane.Ring K) : ι → LaurentPlane.Ring K) = m := by
      ext b
      simp [Pi.single_apply]
    rw [← he]
    exact V.sum_mem (fun a _ => hc a)
  · apply monomialSpan_le
    · intro a
      apply single_monomial_mem
      change d • weight i - d • weight i ∈ vertexCone i
      simpa using direction_mem i i 0
    · exact freeVertex_stable d i

lemma freeVertex_finite {ι : Type*} [Fintype ι] (d : ℤ) (i : Fin 3) :
    letI := vertexModule (K := K) (M := ι → LaurentPlane.Ring K) i
    Module.Finite (MvPolynomial (Fin 3) K)
      (vertexSubmodule i (freeVertex (K := K) ι d i) (freeVertex_stable d i)) := by
  classical
  apply vertexSubmodule_finite i (freeVertex ι d i) (freeVertex_stable d i)
    (fun index : ι => Pi.single index (T (d • weight i)))
  · intro a
    apply single_monomial_mem
    change d • weight i - d • weight i ∈ vertexCone i
    simpa using direction_mem i i 0
  · exact freeVertex_monomial_generators d i

end
end MaximalSeshadri.PlaneCech

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_KernelVertices
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

lemma kernelVertex_finite (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) (i : Fin 3) :
    letI := vertexModule (K := K) (M := N) i
    Module.Finite (MvPolynomial (Fin 3) K)
      (vertexSubmodule i (kernelVertex N d i) (kernelVertex_stable N d i)) := by
  let := vertexModule (K := K) (M := N) i
  let := vertexModule (K := K) (M := ι → LaurentPlane.Ring K) i
  let W := vertexSubmodule i (freeVertex (K := K) ι d i) (freeVertex_stable d i)
  let Q := vertexSubmodule i (kernelVertex N d i) (kernelVertex_stable N d i)
  let : Module.Finite (MvPolynomial (Fin 3) K) W := freeVertex_finite d i
  let f : Q →ₗ[MvPolynomial (Fin 3) K] W :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply Module.Finite.of_injective f
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun t : W => (t : ι → LaurentPlane.Ring K)) h))

lemma kernelVertex_generators (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) (i : Fin 3) :
    ∃ n : ℕ, ∃ g : Fin n → N, (∀ a, g a ∈ kernelVertex N d i) ∧
      kernelVertex N d i = monomialSpan (K := K) (vertexCone i) g := by
  let := vertexModule (K := K) (M := N) i
  let := vertexModule_tower (K := K) (M := N) i
  let Q := vertexSubmodule i (kernelVertex N d i) (kernelVertex_stable N d i)
  let : Module.Finite (MvPolynomial (Fin 3) K) Q := kernelVertex_finite N d i
  let F : Q →ₗ[K] N := Q.subtype.restrictScalars K
  have he : F.range = kernelVertex N d i := by
    ext x
    exact ⟨fun ⟨y,hy⟩ => hy ▸ y.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
  obtain ⟨n,g,hg,hgen⟩ := finite_monomial_generators i id F
    (by rw [he]; exact kernelVertex_stable N d i)
    (by intro j x; change vertexPolynomial (K := K) i (MvPolynomial.X j) • (x : N) = _; rw [vertexPolynomial_X]; rfl)
  exact ⟨n,g,by rwa [he] at hg,by rwa [he] at hgen⟩

end
end MaximalSeshadri.PlaneCech

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_FreeVertexClearing
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K]

lemma freeVertex_cross_clearing {ι : Type*} [Fintype ι] (d : ℤ) (i j : Fin 3)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeVertex ι d j) :
    ∃ q : ℕ, T (K := K) (q • (weight j - weight i)) • m ∈ freeVertex ι d i := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨3*n+d.natAbs,fun a ha => ?_⟩
  apply supported_monomial_mul ((m a).coeff.support : Set (ℤ × ℤ)) (twistCone d i)
    ((3*n+d.natAbs) • (weight j-weight i)) _ (m a)
    (supported_of_support (m a) _ (fun w hw => hw))
  intro w hw
  have hbound := hn a w hw
  have hd0 := abs_nonneg d
  have hd1 := neg_abs_le d
  have hd2 := le_abs_self d
  have hj : w ∈ twistCone d j := (Finsupp.mem_supported K (m a).coeff).mp (hm a ha) hw
  fin_cases i <;> fin_cases j <;>
    simp [twistCone,vertexCone,weight,coneA,coneB,coneC] at hj ⊢ <;> omega

lemma freeA_vertex_clearing {ι : Type*} [Fintype ι] (d : ℤ)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeA ι) :
    ∃ q : ℕ, T (K := K) (q • (weight 1-weight 0)) • m ∈ freeVertex ι d 0 := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨n,fun a ha => ?_⟩
  apply supported_monomial_mul ((m a).coeff.support : Set (ℤ × ℤ)) (twistCone d 0)
    (n • (weight 1-weight 0)) _ (m a) (supported_of_support (m a) _ (fun w hw => hw))
  intro w hw
  have hb := hn a w hw
  have hj : w ∈ coneA := (Finsupp.mem_supported K (m a).coeff).mp (hm a ha) hw
  simp [twistCone,vertexCone,weight,coneA,coneB] at hj ⊢
  omega

lemma freeB_vertex_clearing {ι : Type*} [Fintype ι] (d : ℤ)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeB ι) :
    ∃ q : ℕ, T (K := K) (q • (weight 2-weight 0)) • m ∈ freeVertex ι d 0 := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨n,fun a ha => ?_⟩
  apply supported_monomial_mul ((m a).coeff.support : Set (ℤ × ℤ)) (twistCone d 0)
    (n • (weight 2-weight 0)) _ (m a) (supported_of_support (m a) _ (fun w hw => hw))
  intro w hw
  have hb := hn a w hw
  have hj : w ∈ coneB := (Finsupp.mem_supported K (m a).coeff).mp (hm a ha) hw
  simp [twistCone,vertexCone,weight,coneA,coneB] at hj ⊢
  omega

lemma freeC_vertex_clearing {ι : Type*} [Fintype ι] (d : ℤ)
    (m : ι → LaurentPlane.Ring K) (hm : m ∈ freeC ι d) :
    ∃ q : ℕ, T (K := K) (q • (weight 2-weight 1)) • m ∈ freeVertex ι d 1 := by
  obtain ⟨n,hn⟩ := support_bound m
  refine ⟨n,fun a ha => ?_⟩
  apply supported_monomial_mul ((m a).coeff.support : Set (ℤ × ℤ)) (twistCone d 1)
    (n • (weight 2-weight 1)) _ (m a) (supported_of_support (m a) _ (fun w hw => hw))
  intro w hw
  have hb := hn a w hw
  have hj : w ∈ coneC d := (Finsupp.mem_supported K (m a).coeff).mp (hm a ha) hw
  simp [twistCone,vertexCone,weight,coneA,coneC] at hj ⊢
  omega

end
end MaximalSeshadri.PlaneCech

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_KernelH1
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                  
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K] {ι : Type*}

lemma kernelA_stable (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K))
    (z : ℤ × ℤ) (hz : z ∈ coneA) (x : N) (hx : x ∈ kernelA N) :
    T (K := K) z • x ∈ kernelA N := by
  change T (K := K) z • (x : ι → LaurentPlane.Ring K) ∈ freeA ι
  exact freeA_stable z hz (x : ι → LaurentPlane.Ring K) hx
lemma kernelB_stable (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K))
    (z : ℤ × ℤ) (hz : z ∈ coneB) (x : N) (hx : x ∈ kernelB N) :
    T (K := K) z • x ∈ kernelB N := by
  change T (K := K) z • (x : ι → LaurentPlane.Ring K) ∈ freeB ι
  exact freeB_stable z hz (x : ι → LaurentPlane.Ring K) hx
lemma kernelC_stable (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ)
    (z : ℤ × ℤ) (hz : z ∈ coneC 0) (x : N) (hx : x ∈ kernelC N d) :
    T (K := K) z • x ∈ kernelC N d := by
  change T (K := K) z • (x : ι → LaurentPlane.Ring K) ∈ freeC ι d
  exact freeC_stable d z hz (x : ι → LaurentPlane.Ring K) hx

lemma kernelVertex_zero (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    kernelVertex N d 0 = kernelA N ⊓ kernelB N := by
  simp only [kernelVertex,freeVertex_zero,Submodule.comap_inf]
lemma kernelVertex_one (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    kernelVertex N d 1 = kernelA N ⊓ kernelC N d := by
  simp only [kernelVertex,freeVertex_one,Submodule.comap_inf]
lemma kernelVertex_two (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    kernelVertex N d 2 = kernelB N ⊓ kernelC N d := by
  simp only [kernelVertex,freeVertex_two,Submodule.comap_inf]

lemma kernel_boundaries (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    vertexBoundaries (kernelA N) (kernelB N) (kernelC N d) (kernelVertex N d) =
      fullBoundaries (K := K) (kernelA N) (kernelB N) (kernelC N d) := by
  simp only [vertexBoundaries,boundaries,kernelVertex_zero,kernelVertex_one,kernelVertex_two,
    Submodule.comap_subtype_self,Submodule.map_top,fullBoundaries]

variable [Fintype ι]

attribute [local instance] OAI.MaximalSeshadri.PlaneCech.kernelCyclesAddCommGroup
attribute [local instance] OAI.MaximalSeshadri.PlaneCech.kernelCyclesModule
attribute [local instance] OAI.MaximalSeshadri.PlaneCech.kernelCyclesHasQuotient
theorem kernel_H1_finite_s01_oai (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    Module.Finite K ((cycles (K := K) (kernelA N) (kernelB N) (kernelC N d)) ⧸
      fullBoundaries (K := K) (kernelA N) (kernelB N) (kernelC N d)) := by
  choose n g hg hgen using kernelVertex_generators N d
  have incA : kernelVertex N d 0 ≤ kernelA N := by rw [kernelVertex_zero]; exact inf_le_left
  have incB : kernelVertex N d 0 ≤ kernelB N := by rw [kernelVertex_zero]; exact inf_le_right
  have incC : kernelVertex N d 1 ≤ kernelC N d := by rw [kernelVertex_one]; exact inf_le_right
  rw [← kernel_boundaries N d]
  apply toric_H1_finite (kernelVertex N d) (kernelVertex_stable N d) g hg
  · intro i j x hx
    exact freeVertex_cross_clearing d i j (x : ι → LaurentPlane.Ring K) hx
  · exact kernelA_stable N
  · exact kernelB_stable N
  · exact kernelC_stable N d
  · exact incA
  · exact incB
  · exact incC
  · apply localized_span (vertexCone 0) coneA (g 0) (kernelA N) (fun a => incA (hg 0 a))
      (kernelA_stable N)
    intro x hx
    obtain ⟨q,hq⟩ := freeA_vertex_clearing d (x : ι → LaurentPlane.Ring K) hx
    refine ⟨q • (weight 1-weight 0),?_,?_⟩
    · rw [← hgen 0]; exact hq
    · intro w hw
      simp [vertexCone,coneA,weight] at hw ⊢
      exact hw.1
  · apply localized_span (vertexCone 0) coneB (g 0) (kernelB N) (fun a => incB (hg 0 a))
      (kernelB_stable N)
    intro x hx
    obtain ⟨q,hq⟩ := freeB_vertex_clearing d (x : ι → LaurentPlane.Ring K) hx
    refine ⟨q • (weight 2-weight 0),?_,?_⟩
    · rw [← hgen 0]; exact hq
    · intro w hw
      simp [vertexCone,coneB,weight] at hw ⊢
      exact hw.2
  · apply localized_span (vertexCone 1) (coneC 0) (g 1) (kernelC N d) (fun a => incC (hg 1 a))
      (kernelC_stable N d)
    intro x hx
    obtain ⟨q,hq⟩ := freeC_vertex_clearing d (x : ι → LaurentPlane.Ring K) hx
    refine ⟨q • (weight 2-weight 1),?_,?_⟩
    · rw [← hgen 1]; exact hq
    · intro w hw
      simp [vertexCone,coneC,weight] at hw ⊢
      omega
end
end MaximalSeshadri.PlaneCech

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MaximalSeshadri.PlaneCech.kernel_H1_finite_s01_oai.{u_1, u_2} := @OAI.MaximalSeshadri.PlaneCech.kernel_H1_finite_s01_oai.{u_1, u_2}
