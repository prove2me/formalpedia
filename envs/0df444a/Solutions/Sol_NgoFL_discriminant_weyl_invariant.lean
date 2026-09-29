-- Prove2me | solution 1 for NgoFL.discriminant_weyl_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T18:17:50.750131+00:00
-- url     : https://prove2.me/submissions/eff31d77-03ce-41bb-b282-f7131804ec4a

import Mathlib
import Definitions.Def_NgoEndoscopicDiscriminant

open NgoFL

namespace NgoFLDiscr

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- Evaluating a root at a coreflected vector is evaluating the reflected root. -/
lemma root'_coreflection (j i : ι) (y : N) :
    P.root' i (P.coreflection j y) = P.root' (P.reflectionPerm j i) y := by
  have h : P.root (P.reflectionPerm j i) = P.root i - P.pairing i j • P.root j := by
    rw [P.root_reflectionPerm, P.reflection_apply_root]
  show P.toLinearMap (P.root i) (P.coreflection j y)
      = P.toLinearMap (P.root (P.reflectionPerm j i)) y
  rw [h]
  simp [RootPairing.coreflection_apply, mul_comm]

/-- The discriminant is invariant under a single coreflection. -/
lemma discriminant_coreflection [Fintype ι] (j : ι) (y : N) :
    discriminant P (P.coreflection j y) = discriminant P y := by
  calc discriminant P (P.coreflection j y)
      = ∏ i, P.root' (P.reflectionPerm j i) y :=
        Finset.prod_congr rfl fun i _ => root'_coreflection P j i y
    _ = ∏ i, P.root' i y := Equiv.prod_comp (P.reflectionPerm j) (fun i => P.root' i y)
    _ = discriminant P y := rfl

end NgoFLDiscr

/-- **Ngô, Lemme 1.10.1**: the discriminant `D_G = ∏_{α ∈ Φ} dα` is invariant under the
Weyl group. -/
theorem solution {ι R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Fintype ι] (P : RootPairing ι R M N)
    (w : N ≃ₗ[R] N) (hw : w ∈ weylSubgroup P Set.univ) (x : N) :
    discriminant P (w x) = discriminant P x := by
  have hsub : weylSubgroup P Set.univ ≤
      { carrier := {f : N ≃ₗ[R] N | ∀ y, discriminant P (f y) = discriminant P y}
        one_mem' := fun y => rfl
        mul_mem' := by
          intro a b ha hb y
          simp only [Set.mem_ofPred_eq] at ha hb
          rw [LinearEquiv.mul_apply, ha, hb]
        inv_mem' := by
          intro a ha y
          simp only [Set.mem_ofPred_eq] at ha ⊢
          have h := ha (a⁻¹ y)
          rw [show a (a⁻¹ y) = y from by simp] at h
          exact h.symm } := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro f ⟨i, -, rfl⟩ y
    exact NgoFLDiscr.discriminant_coreflection P i y
  exact hsub hw x
