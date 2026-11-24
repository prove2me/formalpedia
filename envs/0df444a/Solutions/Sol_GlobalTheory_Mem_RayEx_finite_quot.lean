-- Prove2me | solution 1 for GlobalTheory.Mem.RayEx.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:05:43.927769+00:00
-- url     : https://prove2.me/submissions/7cfca08f-7c76-49de-96f4-a09f66d95db4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty
import Theorems.Thm_GlobalTheory_Mem_RayEx_ne_bot_of_isCoprime
import Theorems.Thm_GlobalTheory_Mem_RayEx_exists_good
import Theorems.Thm_GlobalTheory_Mem_RayEx_rel_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayEx
open NumberField IsDedekindDomain
variable {R : Type} [CommRing R] [IsDedekindDomain R] (m : Ideal R)
variable {m}
namespace GlobalTheory.Mem.RayEx
theorem _root_.solution (hm : m ≠ ⊤) [Finite (R ⧸ m)] [Finite (ClassGroup R)] : Finite (con m).Quotient := by
  let cl : S m → ClassGroup R := fun I =>
    ClassGroup.mk0 ⟨I.1, mem_nonZeroDivisors_of_ne_zero (ne_bot_of_isCoprime hm I.2)⟩
  have key : ∀ I : S m, ∃ b : R, IsCoprime (Ideal.span {b}) m ∧
      Rel m I.1 (Ideal.span {b} * (Function.invFun cl (cl I)).1) := by
    intro I
    have h : cl I = cl (Function.invFun cl (cl I)) := (Function.invFun_eq ⟨I, rfl⟩).symm
    obtain ⟨x, y, -, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
    exact exists_good I.2 (Function.invFun cl (cl I)).2 hy hxy
  choose b hb hrel using key
  let F : (con m).Quotient → ClassGroup R × (R ⧸ m) := fun x =>
    (cl (Quotient.out x), Ideal.Quotient.mk m (b (Quotient.out x)))
  refine Finite.of_injective F ?_
  intro x y hxy
  obtain ⟨h1, h2⟩ := Prod.mk.inj hxy
  rw [Ideal.Quotient.eq] at h2
  refine Quotient.out_equiv_out.mp ?_
  have h3 := hrel (Quotient.out y)
  rw [← h1] at h3
  exact ((hrel _).trans ((rel_span (hb _) h2).mul (Rel.refl _))).trans h3.symm
end GlobalTheory.Mem.RayEx
