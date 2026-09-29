-- Prove2me | solution 1 for IsIntegrallyClosed.isReduced_quotient_span_singleton_of_squarefree_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0b863bd3-82fb-5c4c-8625-da17a34225ef

import Mathlib
import Theorems.Thm_IsIntegrallyClosed_mem_span_singleton_of_mul_mem_of_isIntegral
import Theorems.Thm_IsDiscreteValuationRing_isReduced_adjoin_singleton_quotient_of_squarefree
import Theorems.Thm_IsReduced_quotient_span_singleton_of_injective_of_forall_exists_mul_mem
import Theorems.Thm_IsDiscreteValuationRing_isIntegrallyClosedIn_adjoin_singleton_of_squarefree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_isReduced_quotient_span_singleton_of_squarefree_minpoly

open Polynomial IsLocalRing

universe u

theorem solution
    {R A O F : Type u}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field F]
    [Algebra R A] [Algebra R O] [Algebra R F] [Algebra A F] [Algebra O F]
    [IsScalarTower R A F] [IsScalarTower R O F]
    [FaithfulSMul R A] [FaithfulSMul A F] [FaithfulSMul O F] [Algebra.IsIntegral R A]
    {p : R} (hp : (Ideal.span {p}).IsPrime) (hp0 : p ≠ 0)
    (hpO : Irreducible (algebraMap R O p))
    (hO : ∀ x : O, ∃ s ∉ Ideal.span {p}, ∃ r : R, algebraMap R O r = algebraMap R O s * x)
    {α : F} (hα : IsIntegral O α)
    (hαA : ∃ s ∉ Ideal.span {p}, ∃ a : A, algebraMap A F a = algebraMap R F s * α)
    (hsq : Squarefree ((minpoly O α).map (Ideal.Quotient.mk (Ideal.span {algebraMap R O p}))))
    (hgen : ∀ x : F, ∃ n : ℕ, algebraMap O F (algebraMap R O p) ^ n * x ∈ Algebra.adjoin O {α}) :
    IsReduced (A ⧸ Ideal.span {algebraMap R A p}) := by
  set ϖ : O := algebraMap R O p with hϖdef
  set B : Subalgebra O F := Algebra.adjoin O {α} with hBdef
  haveI hIC : IsIntegrallyClosedIn B F :=
    IsDiscreteValuationRing.isIntegrallyClosedIn_adjoin_singleton_of_squarefree hpO hα hsq hgen

  have hmem : ∀ a : A, algebraMap A F a ∈ B := by
    intro a
    have h1 : IsIntegral R (algebraMap A F a) := (Algebra.IsIntegral.isIntegral (R := R) a).map
      (IsScalarTower.toAlgHom R A F)
    have h2 : IsIntegral O (algebraMap A F a) := h1.tower_top
    have h3 : IsIntegral B (algebraMap A F a) := h2.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral h3
    rw [← hy]
    exact y.2
  let f : A →+* B :=
    { toFun := fun a => ⟨algebraMap A F a, hmem a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  letI : Algebra A B := f.toAlgebra
  have hf : ∀ a : A, ((algebraMap A B a : B) : F) = algebraMap A F a := fun a => rfl
  have hfinj : Function.Injective (algebraMap A B) := by
    intro a b h
    apply FaithfulSMul.algebraMap_injective A F
    rw [← hf a, ← hf b, h]

  have hpB : algebraMap A B (algebraMap R A p) = algebraMap O B ϖ := by
    apply Subtype.ext
    rw [hf, ← IsScalarTower.algebraMap_apply R A F, IsScalarTower.algebraMap_apply R O F]
    rfl

  haveI : IsReduced (B ⧸ Ideal.span {algebraMap A B (algebraMap R A p)}) := by
    rw [hpB]
    exact IsDiscreteValuationRing.isReduced_adjoin_singleton_quotient_of_squarefree hpO hα hsq

  let S : Set A := {s | ∃ r : R, r ∉ Ideal.span {p} ∧ s = algebraMap R A r}
  refine IsReduced.quotient_span_singleton_of_injective_of_forall_exists_mul_mem hfinj
    (algebraMap R A p) S ?_ ?_
  ·
    intro b
    suffices h : ∀ x ∈ Algebra.adjoin O {α}, ∃ r : R, r ∉ Ideal.span {p} ∧ ∃ a : A,
        algebraMap A F a = algebraMap R F r * x by
      obtain ⟨r, hr, a, ha⟩ := h b.1 b.2
      refine ⟨algebraMap R A r, ⟨r, hr, rfl⟩, a, Subtype.ext ?_⟩
      rw [hf, ha, Subalgebra.coe_mul, hf, ← IsScalarTower.algebraMap_apply]
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      obtain ⟨s, hs, a, ha⟩ := hαA
      exact ⟨s, hs, a, ha⟩
    | algebraMap c =>
      obtain ⟨s, hs, r, hr⟩ := hO c
      refine ⟨s, hs, algebraMap R A r, ?_⟩
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R O F r, hr, map_mul,
        ← IsScalarTower.algebraMap_apply]
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, a, ha⟩ := hy
      obtain ⟨t, ht, b, hb⟩ := hz
      refine ⟨s * t, ?_, algebraMap R A t * a + algebraMap R A s * b, ?_⟩
      · intro hst
        rcases hp.mem_or_mem hst with h | h
        · exact hs h
        · exact ht h
      · simp only [map_add, map_mul, ← IsScalarTower.algebraMap_apply, ha, hb]
        ring
    | mul y z _ _ hy hz =>
      obtain ⟨s, hs, a, ha⟩ := hy
      obtain ⟨t, ht, b, hb⟩ := hz
      refine ⟨s * t, ?_, a * b, ?_⟩
      · intro hst
        rcases hp.mem_or_mem hst with h | h
        · exact hs h
        · exact ht h
      · simp only [map_mul, ha, hb]
        ring
  ·
    rintro _ ⟨r, hr, rfl⟩ a h
    exact IsIntegrallyClosed.mem_span_singleton_of_mul_mem_of_isIntegral hp hp0 hr h

end S_IsIntegrallyClosed_isReduced_quotient_span_singleton_of_squarefree_minpoly
end P2MW
export P2MW.S_IsIntegrallyClosed_isReduced_quotient_span_singleton_of_squarefree_minpoly (solution)
