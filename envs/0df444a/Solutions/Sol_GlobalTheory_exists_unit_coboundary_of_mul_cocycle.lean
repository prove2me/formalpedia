-- Prove2me | solution 1 for GlobalTheory.exists_unit_coboundary_of_mul_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:48:56.577097+00:00
-- url     : https://prove2.me/submissions/9628e990-8c6b-4daa-9129-ed89aed8e8c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitCoboundaryOfMulCocycle
import Theorems.Thm_GlobalTheory_MulCocycle_finsupp_homotopy
import Theorems.Thm_GlobalTheory_MulCocycle_mem_map_algebraMap_iff
import Theorems.Thm_GlobalTheory_MulCocycle_exists_unit_of_faces
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
open GlobalTheory
open MulCocycle
namespace GlobalTheory
theorem _root_.solution (B : Type) [CommRing B] (I : Ideal B)
    (hI : IsNilpotent I) (X : Type) [AddCommGroup X] (f : AddMonoidAlgebra B (X × X))
    (hf : ∀ p, (f - 1).coeff p ∈ I)
    (hc : AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.1, p.2)) f *
        AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, (0 : X))) f =
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, p.2)) f *
        AddMonoidAlgebra.mapDomain (fun p : X × X => ((0 : X), p.1, p.2)) f) :
    ∃ g : (AddMonoidAlgebra B X)ˣ, (∀ x, (g.val - 1).coeff x ∈ I) ∧
      f * AddMonoidAlgebra.mapDomain (fun x : X => (x, x)) g.val =
        AddMonoidAlgebra.mapDomain (fun x : X => (x, (0 : X))) g.val *
          AddMonoidAlgebra.mapDomain (fun x : X => ((0 : X), x)) g.val := by
  obtain ⟨n, hn⟩ := hI
  have hn' : I ^ 2 ^ n = ⊥ :=
    le_bot_iff.1 ((Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le).trans hn.le)
  have key : ∀ (a a' : X →+ X × X) (b b' : X × X →+ X × X × X), (∀ x, b (a x) = b' (a' x)) →
      ∀ w : B[X], mapDomainAlgHom B B b (mapDomainAlgHom B B a w) =
        mapDomainAlgHom B B b' (mapDomainAlgHom B B a' w) := by
    intro a a' b b' h w
    induction w using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single x r => simp [h]
  obtain ⟨g, hg, hg'⟩ := exists_unit_of_faces (B := B)
    (mapDomainAlgHom B B (AddMonoidHom.inr X X))
    (mapDomainAlgHom B B ((AddMonoidHom.id X).prod (AddMonoidHom.id X)))
    (mapDomainAlgHom B B (AddMonoidHom.inl X X))
    (mapDomainAlgHom B B (AddMonoidHom.inr X (X × X)))
    (mapDomainAlgHom B B ((AddMonoidHom.fst X X).prod (AddMonoidHom.id (X × X))))
    (mapDomainAlgHom B B ((AddMonoidHom.fst X X).prod
      ((AddMonoidHom.snd X X).prod (AddMonoidHom.snd X X))))
    (mapDomainAlgHom B B ((AddMonoidHom.id X).prodMap (AddMonoidHom.inl X X)))
    (key _ _ _ _ fun _ => rfl) (key _ _ _ _ fun _ => rfl) (key _ _ _ _ fun _ => rfl)
    (key _ _ _ _ fun _ => rfl) (key _ _ _ _ fun _ => rfl) (key _ _ _ _ fun _ => rfl)
    (fun K L φ hφ hd => by
      rw [mem_map_algebraMap_iff] at hφ hd
      refine ⟨ofCoeff (φ.coeff.comapDomain (fun x => ((0 : X), x))
        (Prod.mk_right_injective 0).injOn), (mem_map_algebraMap_iff _ _).2 fun x => hφ (0, x),
        (mem_map_algebraMap_iff _ _).2 fun q => ?_⟩
      have := finsupp_homotopy φ.coeff (φ.coeff.comapDomain (fun x => ((0 : X), x))
        (Prod.mk_right_injective 0).injOn) (fun _ => rfl) q
      exact (congrArg (· ∈ L) this).mp (hd (0, q)))
    n I hn' f ((mem_map_algebraMap_iff _ _).2 hf) hc
  exact ⟨g, (mem_map_algebraMap_iff _ _).1 hg, hg'⟩
end GlobalTheory
