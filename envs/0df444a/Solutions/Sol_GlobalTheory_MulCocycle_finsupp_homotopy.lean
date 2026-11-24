-- Prove2me | solution 1 for GlobalTheory.MulCocycle.finsupp_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:59:25.85502+00:00
-- url     : https://prove2.me/submissions/df6a744a-d464-4cbd-bb2d-65f8f882288a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitCoboundaryOfMulCocycle
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.trivialCoaction_apply
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply
attribute [local simp] P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0



set_option autoImplicit false
set_option autoImplicit false
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.MulCocycle
namespace GlobalTheory.MulCocycle
theorem _root_.solution {X : Type*} [Zero X] {N : Type*} [AddCommGroup N] (f : X × X →₀ N)
    (g : X →₀ N) (hg : ∀ x, g x = f (0, x)) (q : X × X) :
    (f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
        f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) :
          X × X × X →₀ N) (0, q) =
      (f - (g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
        g.mapDomain (fun y => (y, (0 : X)))) : X × X →₀ N) q := by
  classical
  let s : (X × X →₀ N) →+ (X →₀ N) :=
    Finsupp.comapDomain.addMonoidHom (f := fun x => ((0 : X), x)) (Prod.mk_right_injective 0)
  have hs : ∀ f x, s f x = f (0, x) := fun _ _ => rfl
  obtain rfl : g = s f := Finsupp.ext hg
  clear hg
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
    rw [← sub_eq_zero] at hf hg ⊢
    rw [← add_zero (0 : N)]
    nth_rewrite 1 [← hf]
    rw [← hg]; abel
  | single p m =>
    obtain ⟨y, z⟩ := p
    by_cases h : y = 0
    · subst h
      have : s (Finsupp.single (0, z) m) = Finsupp.single z m := by
        ext x; simp [hs, Finsupp.single_apply]
      simp [this, Finsupp.single_apply]
      abel
    · have : s (Finsupp.single (y, z) m) = 0 := by
        ext x; simp [hs, h]
      simp [this, Finsupp.single_apply, h]
end GlobalTheory.MulCocycle
