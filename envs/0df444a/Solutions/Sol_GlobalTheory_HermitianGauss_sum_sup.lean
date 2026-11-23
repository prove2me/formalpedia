-- Prove2me | solution 1 for GlobalTheory.HermitianGauss.sum_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:51.139074+00:00
-- url     : https://prove2.me/submissions/3e58db0f-759c-49f0-8f36-3c3b34810788

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
import Theorems.Thm_GlobalTheory_HermitianGauss_mem_pts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermitianGauss.mem_pts

set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
namespace GlobalTheory.HermitianGauss
theorem _root_.solution {D : Submodule R M} {x : M} {P : Ideal R} [Fintype (R ⧸ P)] (hP : ∀ r, r • x ∈ D ↔ r ∈ P)
    {A : Type} [AddCommMonoid A] (f : M → A) :
    ∑ y ∈ pts (D ⊔ Submodule.span R {x}), f y = ∑ q : R ⧸ P, ∑ d ∈ pts D, f (d + (Quotient.out q : R) • x) := by
  have hout : ∀ a : R ⧸ P, Ideal.Quotient.mk P (Quotient.out a) = a := fun a => Quotient.out_eq a
  calc ∑ y ∈ pts (D ⊔ Submodule.span R {x}), f y
      = ∑ p ∈ (Finset.univ : Finset (R ⧸ P)) ×ˢ pts D, f (p.2 + (Quotient.out p.1 : R) • x) := by
        symm
        apply Finset.sum_nbij (fun p => p.2 + (Quotient.out p.1 : R) • x)
        · rintro ⟨q, d⟩ hp
          simp only [Finset.mem_product, Finset.mem_univ, true_and, mem_pts] at hp
          exact mem_pts.mpr (Submodule.add_mem_sup hp
            (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
        · rintro ⟨q1, d1⟩ h1 ⟨q2, d2⟩ h2 heq
          simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, true_and,
            Finset.mem_coe, mem_pts] at h1 h2
          have heq' : d1 + (Quotient.out q1 : R) • x = d2 + (Quotient.out q2 : R) • x := heq
          have hq : q1 = q2 := by
            have hm : (Quotient.out q1 - Quotient.out q2 : R) • x ∈ D := by
              have e : (Quotient.out q1 : R) • x - (Quotient.out q2 : R) • x = d2 - d1 := by
                rw [sub_eq_sub_iff_add_eq_add, add_comm]
                exact heq'
              rw [sub_smul, e]
              exact D.sub_mem h2 h1
            rw [← hout q1, ← hout q2]
            exact Ideal.Quotient.eq.mpr ((hP _).mp hm)
          subst hq
          have : d1 = d2 := add_right_cancel heq'
          rw [this]
        · intro y hy
          rw [Finset.mem_coe, mem_pts] at hy
          obtain ⟨d, hd, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
          have hmem : (Quotient.out (Ideal.Quotient.mk P a) - a : R) ∈ P := Ideal.Quotient.eq.mp (hout _)
          refine ⟨(Ideal.Quotient.mk P a, d - (Quotient.out (Ideal.Quotient.mk P a) - a : R) • x), ?_, ?_⟩
          · simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, true_and,
              Finset.mem_coe, mem_pts]
            exact D.sub_mem hd ((hP _).mpr hmem)
          · show d - (Quotient.out (Ideal.Quotient.mk P a) - a : R) • x
                + (Quotient.out (Ideal.Quotient.mk P a) : R) • x = d + a • x
            rw [sub_smul]
            abel
        · intro p _
          rfl
    _ = _ := Finset.sum_product' _ _ (fun q d => f (d + (Quotient.out q : R) • x))
end GlobalTheory.HermitianGauss
