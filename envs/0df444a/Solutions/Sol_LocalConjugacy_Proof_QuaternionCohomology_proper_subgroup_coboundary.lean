-- Prove2me | solution 1 for LocalConjugacy.Proof.QuaternionCohomology.proper_subgroup_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:30:28.800887+00:00
-- url     : https://prove2.me/submissions/568cca99-d645-46ac-b0e8-681e1053b7c8

import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_CocycleZorn
import Definitions.Def_LocalConjugacy_Proof_CocycleProducts
import Definitions.Def_LocalConjugacy_Proof_FiniteCoefficientSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInvarianceSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInjectivity
import Definitions.Def_LocalConjugacy_Proof_CocycleRebase
import Definitions.Def_LocalConjugacy_Proof_FiniteHall
import Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure
import Definitions.Def_LocalConjugacy_Proof_ProfiniteHall
import Definitions.Def_LocalConjugacy_Proof_ActionProductTopology
import Definitions.Def_LocalConjugacy_Proof_HallCohomology
import Definitions.Def_LocalConjugacy_Proof_SupersolvableRestriction
import Definitions.Def_LocalConjugacy_Proof_NilpotentCoefficients
import Definitions.Def_LocalConjugacy_Proof_NonabelianComplement
import Definitions.Def_LocalConjugacy_Proof_ComplementSupersolvable
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Quaternion
import Definitions.Def_LocalConjugacy_Proof_QuaternionCohomology
import Definitions.Def_LocalConjugacy_Proof_QuaternionMatrices
import Definitions.Def_LocalConjugacy_Proof_QuaternionAction
import Definitions.Def_LocalConjugacy_Proof_QuaternionComplements

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

/-!
The `Q₈ ⋊ S₃` obstruction from the introduction. We use Mathlib's quaternion
and dihedral groups, with `S₃ = DihedralGroup 3`. The action rotates `i,j,k`
and sends `(i,j,k)` to `(-j,-i,-k)` under a reflection.
All finite checks use kernel-checked `decide`, never `native_decide`.
-/

namespace LocalConjugacy.QuaternionExample




open QuaternionGroup







set_option maxRecDepth 10000
set_option maxHeartbeats 0



































/-- Every cocycle on the cyclic Sylow 3-subgroup is a coboundary. -/
private theorem sylow_three_H1_trivial : ∀ f : ZMod 3 → Q,
    (∀ x y, f (x + y) = f x * act (.r x) (f y)) →
    ∃ n : Q, ∀ x, f x = n⁻¹ * act (.r x) n := by decide

end LocalConjugacy.QuaternionExample

end LocalConjugacy.Proof

end

section


/-!
The finite cohomology assertions for the quaternion counterexample. The original
cocycle calculation is promoted to the actual quotient H¹. A small subgroup
classification proves vanishing on every proper subgroup, hence every Sylow.
-/
namespace LocalConjugacy.Proof.QuaternionCohomology
open LocalConjugacy.QuaternionExample
set_option maxRecDepth 20000
set_option maxHeartbeats 0






/-- A 64-case Boolean certificate classifies all subgroups of the order-six
dihedral group. It quantifies over membership masks, not over cocycle tables. -/
private theorem subgroup_mask_shapes : ∀ m : S → Bool,
    m 1 = true → (∀ x y, m x = true → m y = true → m (x * y) = true) →
    (∀ x, m x = true) ∨
    (∀ x, m x = true ↔ ∃ i : ZMod 3, x = DihedralGroup.r i) ∨
    (∃ i : ZMod 3, ∀ x, m x = true ↔ x = 1 ∨ x = DihedralGroup.sr i) ∨
    (∀ x, m x = true ↔ x = 1) := by decide

/-- Each reflection acts on Q₈ with trivial first cohomology. The only free
cocycle value satisfies the displayed order-two cocycle equation. -/
private theorem reflection_coboundary : ∀ i : ZMod 3, ∀ q : Q,
    q * act (.sr i) q = 1 → ∃ n : Q, q = n⁻¹ * act (.sr i) n := by decide

/-- All cocycles on every proper subgroup are coboundaries. The rotation case
uses the existing C₃ calculation; the reflection case uses its single generator. -/
private theorem proper_subgroup_coboundary_preparedProof (L : Subgroup S) (hL : L ≠ ⊤)
    (f : FiniteCocycle (action.comp L.subtype)) :
    ∃ n : Q, ∀ x : L, f.val x = n⁻¹ * act x.val n := by
  classical
  have h1 : f.val 1 = 1 := by
    have h := f.property 1 1
    change f.val 1 = f.val 1 * act 1 (f.val 1) at h
    rw [act_one] at h
    exact mul_eq_left.mp h.symm
  have hs := subgroup_mask_shapes (fun x => decide (x ∈ L))
    (by simpa using L.one_mem)
    (by intro x y hx hy; simpa using L.mul_mem (of_decide_eq_true hx) (of_decide_eq_true hy))
  simp only [decide_eq_true_eq] at hs
  rcases hs with ht | hr | ⟨i, hi⟩ | hb
  · exact (hL (top_unique fun x _ => ht x)).elim
  · have hm (i : ZMod 3) : DihedralGroup.r i ∈ L := (hr _).mpr ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := sylow_three_H1_trivial (fun i => f.val ⟨.r i, hm i⟩)
      (fun x y => f.property ⟨.r x, hm x⟩ ⟨.r y, hm y⟩)
    refine ⟨n, ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨i, rfl⟩ := (hr x).mp hx
    exact hn i
  · have hm : DihedralGroup.sr i ∈ L := (hi _).mpr (Or.inr rfl)
    let t : L := ⟨.sr i, hm⟩
    have htt : t * t = 1 := by apply Subtype.ext; simp [t]
    have hsq : f.val t * act (.sr i) (f.val t) = 1 := by
      have h := f.property t t
      rw [htt, h1] at h
      exact h.symm
    obtain ⟨n, hn⟩ := reflection_coboundary i (f.val t) hsq
    refine ⟨n, ?_⟩
    rintro ⟨x, hx⟩
    rcases (hi x).mp hx with rfl | rfl
    · change f.val (1 : L) = n⁻¹ * act 1 n
      rw [h1, act_one, inv_mul_cancel]
    · exact hn
  · refine ⟨1, ?_⟩
    rintro ⟨x, hx⟩
    have hx1 := (hb x).mp hx
    subst x
    change f.val (1 : L) = (1 : Q)⁻¹ * act 1 1
    rw [h1, act_one, inv_one, one_mul]



end LocalConjugacy.Proof.QuaternionCohomology

end

theorem solution :
∀
  (L :
    @Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
  (hL :
    @Ne.{1}
      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      L
      (@Top.top.{0}
        (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@Subgroup.instTop.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
  (f :
    @LocalConjugacy.FiniteCocycle.{0, 0}
      (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
        fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
        @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@SetLike.instMembership.{0, 0}
            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
            (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          L x)
      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
      (@Subgroup.toGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) L)
      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@MonoidHom.comp.{0, 0, 0}
        (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
          @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (@SetLike.instMembership.{0, 0}
              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
            L x)
        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
        (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
          (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
            (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
              (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
        (@MulOneClass.toMulOne.{0}
          (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
            fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
            @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (@SetLike.instMembership.{0, 0}
                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
              L x)
          (@Monoid.toMulOneClass.{0}
            (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@SetLike.instMembership.{0, 0}
                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                L x)
            (@DivInvMonoid.toMonoid.{0}
              (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@SetLike.instMembership.{0, 0}
                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                  L x)
              (@Group.toDivInvMonoid.{0}
                (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                  @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@SetLike.instMembership.{0, 0}
                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    L x)
                (@Subgroup.toGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) L)))))
        (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
        (@MulOneClass.toMulOne.{0}
          (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
            (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
              (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
          (@Monoid.toMulOneClass.{0}
            (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
              (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
            (@DivInvMonoid.toMonoid.{0}
              (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@QuaternionGroup.instGroup
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
              (@Group.toDivInvMonoid.{0}
                (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                (@MulAut.instGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))))
        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.action
        (@Subgroup.subtype.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) L))),
  @Exists.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
    fun (n : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q) =>
    ∀
      (x :
        @Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
          @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (@SetLike.instMembership.{0, 0}
              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
            L x),
      @Eq.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
        (@Subtype.val.{1}
          ((@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@SetLike.instMembership.{0, 0}
                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                L x) →
            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q)
          (fun
              (f :
                (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                    @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (@SetLike.instMembership.{0, 0}
                        (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                      L x) →
                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q) =>
            ∀
              (x y :
                @Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                  @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@SetLike.instMembership.{0, 0}
                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    L x),
              @Eq.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (f
                  (@HMul.hMul.{0, 0, 0}
                    (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                      @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        L x)
                    (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                      @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        L x)
                    (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                      @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        L x)
                    (@instHMul.{0}
                      (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                        @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (@SetLike.instMembership.{0, 0}
                            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          L x)
                      (@MulOne.toMul.{0}
                        (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                          @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            L x)
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                            @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              L x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                L x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  L x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    L x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  L)))))))
                    x y))
                (@HMul.hMul.{0, 0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@instHMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@QuaternionGroup.instGroup
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                  (f x)
                  (@DFunLike.coe.{1, 1, 1}
                    (@MulEquiv.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@QuaternionGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                      (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@QuaternionGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q) =>
                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q)
                    (@EquivLike.toFunLike.{1, 1, 1}
                      (@MulEquiv.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                        (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@MulEquiv.instEquivLike.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                        (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
                    (@DFunLike.coe.{1, 1, 1}
                      (@MonoidHom.{0, 0}
                        (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                          @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            L x)
                        (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                            @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              L x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                L x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  L x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    L x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  L)))))
                        (@MulOneClass.toMulOne.{0}
                          (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@QuaternionGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                          (@Monoid.toMulOneClass.{0}
                            (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@QuaternionGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                            (@DivInvMonoid.toMonoid.{0}
                              (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@DivInvMonoid.toMonoid.{0}
                                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@Group.toDivInvMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@QuaternionGroup.instGroup
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                              (@Group.toDivInvMonoid.{0}
                                (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@DivInvMonoid.toMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@Group.toDivInvMonoid.{0}
                                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                                (@MulAut.instGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@DivInvMonoid.toMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@Group.toDivInvMonoid.{0}
                                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))
                      (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                        @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (@SetLike.instMembership.{0, 0}
                            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          L x)
                      (fun
                          (x :
                            @Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                L x) =>
                        @MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                      (@MonoidHom.instFunLike.{0, 0}
                        (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                          @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            L x)
                        (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                            @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              L x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                L x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  L x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    L x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  L)))))
                        (@MulOneClass.toMulOne.{0}
                          (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@QuaternionGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                          (@Monoid.toMulOneClass.{0}
                            (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@QuaternionGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                            (@DivInvMonoid.toMonoid.{0}
                              (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@DivInvMonoid.toMonoid.{0}
                                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@Group.toDivInvMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@QuaternionGroup.instGroup
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                              (@Group.toDivInvMonoid.{0}
                                (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@DivInvMonoid.toMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@Group.toDivInvMonoid.{0}
                                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                                (@MulAut.instGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@DivInvMonoid.toMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@Group.toDivInvMonoid.{0}
                                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))
                      (@MonoidHom.comp.{0, 0, 0}
                        (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                          @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            L x)
                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                            @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              L x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                L x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  L x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    L x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  L)))))
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@QuaternionGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                          (@Monoid.toMulOneClass.{0}
                            (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@QuaternionGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                            (@DivInvMonoid.toMonoid.{0}
                              (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@DivInvMonoid.toMonoid.{0}
                                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@Group.toDivInvMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@QuaternionGroup.instGroup
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                              (@Group.toDivInvMonoid.{0}
                                (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@DivInvMonoid.toMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@Group.toDivInvMonoid.{0}
                                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                                (@MulAut.instGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@DivInvMonoid.toMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@Group.toDivInvMonoid.{0}
                                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))))
                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.action
                        (@Subgroup.subtype.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) L))
                      x)
                    (f y))))
          f x)
        (@HMul.hMul.{0, 0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
          (@instHMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
            (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
              (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
          (@Inv.inv.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
            (@InvOneClass.toInv.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
              (@DivInvOneMonoid.toInvOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (@DivisionMonoid.toDivInvOneMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@Group.toDivisionMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            n)
          (LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.act
            (@Subtype.val.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@SetLike.instMembership.{0, 0}
                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                  L x)
              x)
            n)) :=
  @LocalConjugacy.Proof.QuaternionCohomology.proper_subgroup_coboundary_preparedProof
