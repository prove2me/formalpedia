-- Prove2me | solution 2 for LocalConjugacy.Proof.finiteH1_subsingleton_of_coboundaries
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:30:45.350982+00:00
-- url     : https://prove2.me/submissions/4dc137ea-39ae-4c47-a74c-405c4031d508

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


/-! Transport the explicit dihedral presentation to the draft's symmetric group.
The transport preserves the full cocycle quotient and all Sylow restrictions. -/
namespace LocalConjugacy.Proof

set_option maxRecDepth 20000
set_option maxHeartbeats 0















/-- Vanishing of cocycles modulo coboundaries gives a singleton quotient. -/
private theorem finiteH1_subsingleton_of_coboundaries_preparedProof {J N : Type*} [Group J] [Group N]
    (a : J →* MulAut N)
    (h : ∀ f : FiniteCocycle a, ∃ n : N, ∀ x, f.val x = n⁻¹ * a x n) :
    Subsingleton (FiniteH1 a) := by
  let z : FiniteCocycle a := ⟨fun _ => 1, by simp⟩
  have hz (f : FiniteCocycle a) : Quotient.mk (finiteCohomologySetoid a) z =
      Quotient.mk (finiteCohomologySetoid a) f := by
    obtain ⟨n, hn⟩ := h f
    apply Quotient.sound
    exact ⟨n, fun x => by simpa [z] using hn x⟩
  constructor
  intro x y
  induction x using Quotient.inductionOn with
  | h f =>
    induction y using Quotient.inductionOn with
    | h g => exact (hz f).symm.trans (hz g)



end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N]
  (a :
    @MonoidHom.{u_1, u_2} J
      (@MulAut.{u_2} N
        (@MulOne.toMul.{u_2} N
          (@MulOneClass.toMulOne.{u_2} N
            (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
      (@MulOneClass.toMulOne.{u_1} J
        (@Monoid.toMulOneClass.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
      (@MulOneClass.toMulOne.{u_2}
        (@MulAut.{u_2} N
          (@MulOne.toMul.{u_2} N
            (@MulOneClass.toMulOne.{u_2} N
              (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
        (@Monoid.toMulOneClass.{u_2}
          (@MulAut.{u_2} N
            (@MulOne.toMul.{u_2} N
              (@MulOneClass.toMulOne.{u_2} N
                (@Monoid.toMulOneClass.{u_2} N
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
          (@DivInvMonoid.toMonoid.{u_2}
            (@MulAut.{u_2} N
              (@MulOne.toMul.{u_2} N
                (@MulOneClass.toMulOne.{u_2} N
                  (@Monoid.toMulOneClass.{u_2} N
                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
            (@Group.toDivInvMonoid.{u_2}
              (@MulAut.{u_2} N
                (@MulOne.toMul.{u_2} N
                  (@MulOneClass.toMulOne.{u_2} N
                    (@Monoid.toMulOneClass.{u_2} N
                      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
              (@MulAut.instGroup.{u_2} N
                (@MulOne.toMul.{u_2} N
                  (@MulOneClass.toMulOne.{u_2} N
                    (@Monoid.toMulOneClass.{u_2} N
                      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))))))))
  (h :
    ∀ (f : @LocalConjugacy.FiniteCocycle.{u_1, u_2} J N inst inst_1 a),
      @Exists.{u_2 + 1} N fun (n : N) =>
        ∀ (x : J),
          @Eq.{u_2 + 1} N
            (@Subtype.val.{max (u_1 + 1) (u_2 + 1)} (J → N)
              (fun (f : J → N) =>
                ∀ (x y : J),
                  @Eq.{u_2 + 1} N
                    (f
                      (@HMul.hMul.{u_1, u_1, u_1} J J J
                        (@instHMul.{u_1} J
                          (@MulOne.toMul.{u_1} J
                            (@MulOneClass.toMulOne.{u_1} J
                              (@Monoid.toMulOneClass.{u_1} J
                                (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))))
                        x y))
                    (@HMul.hMul.{u_2, u_2, u_2} N N N
                      (@instHMul.{u_2} N
                        (@MulOne.toMul.{u_2} N
                          (@MulOneClass.toMulOne.{u_2} N
                            (@Monoid.toMulOneClass.{u_2} N
                              (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                      (f x)
                      (@DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1}
                        (@MulEquiv.{u_2, u_2} N N
                          (@MulOne.toMul.{u_2} N
                            (@MulOneClass.toMulOne.{u_2} N
                              (@Monoid.toMulOneClass.{u_2} N
                                (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
                          (@MulOne.toMul.{u_2} N
                            (@MulOneClass.toMulOne.{u_2} N
                              (@Monoid.toMulOneClass.{u_2} N
                                (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                        N (fun (x : N) => N)
                        (@EquivLike.toFunLike.{u_2 + 1, u_2 + 1, u_2 + 1}
                          (@MulEquiv.{u_2, u_2} N N
                            (@MulOne.toMul.{u_2} N
                              (@MulOneClass.toMulOne.{u_2} N
                                (@Monoid.toMulOneClass.{u_2} N
                                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
                            (@MulOne.toMul.{u_2} N
                              (@MulOneClass.toMulOne.{u_2} N
                                (@Monoid.toMulOneClass.{u_2} N
                                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                          N N
                          (@MulEquiv.instEquivLike.{u_2, u_2} N N
                            (@MulOne.toMul.{u_2} N
                              (@MulOneClass.toMulOne.{u_2} N
                                (@Monoid.toMulOneClass.{u_2} N
                                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
                            (@MulOne.toMul.{u_2} N
                              (@MulOneClass.toMulOne.{u_2} N
                                (@Monoid.toMulOneClass.{u_2} N
                                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))))
                        (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
                          (@MonoidHom.{u_1, u_2} J
                            (@MulAut.{u_2} N
                              (@MulOne.toMul.{u_2} N
                                (@MulOneClass.toMulOne.{u_2} N
                                  (@Monoid.toMulOneClass.{u_2} N
                                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                            (@MulOneClass.toMulOne.{u_1} J
                              (@Monoid.toMulOneClass.{u_1} J
                                (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
                            (@MulOneClass.toMulOne.{u_2}
                              (@MulAut.{u_2} N
                                (@MulOne.toMul.{u_2} N
                                  (@MulOneClass.toMulOne.{u_2} N
                                    (@Monoid.toMulOneClass.{u_2} N
                                      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                              (@Monoid.toMulOneClass.{u_2}
                                (@MulAut.{u_2} N
                                  (@MulOne.toMul.{u_2} N
                                    (@MulOneClass.toMulOne.{u_2} N
                                      (@Monoid.toMulOneClass.{u_2} N
                                        (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                                (@DivInvMonoid.toMonoid.{u_2}
                                  (@MulAut.{u_2} N
                                    (@MulOne.toMul.{u_2} N
                                      (@MulOneClass.toMulOne.{u_2} N
                                        (@Monoid.toMulOneClass.{u_2} N
                                          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                                  (@Group.toDivInvMonoid.{u_2}
                                    (@MulAut.{u_2} N
                                      (@MulOne.toMul.{u_2} N
                                        (@MulOneClass.toMulOne.{u_2} N
                                          (@Monoid.toMulOneClass.{u_2} N
                                            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                                    (@MulAut.instGroup.{u_2} N
                                      (@MulOne.toMul.{u_2} N
                                        (@MulOneClass.toMulOne.{u_2} N
                                          (@Monoid.toMulOneClass.{u_2} N
                                            (@DivInvMonoid.toMonoid.{u_2} N
                                              (@Group.toDivInvMonoid.{u_2} N inst_1)))))))))))
                          J
                          (fun (x : J) =>
                            @MulAut.{u_2} N
                              (@MulOne.toMul.{u_2} N
                                (@MulOneClass.toMulOne.{u_2} N
                                  (@Monoid.toMulOneClass.{u_2} N
                                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                          (@MonoidHom.instFunLike.{u_1, u_2} J
                            (@MulAut.{u_2} N
                              (@MulOne.toMul.{u_2} N
                                (@MulOneClass.toMulOne.{u_2} N
                                  (@Monoid.toMulOneClass.{u_2} N
                                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                            (@MulOneClass.toMulOne.{u_1} J
                              (@Monoid.toMulOneClass.{u_1} J
                                (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
                            (@MulOneClass.toMulOne.{u_2}
                              (@MulAut.{u_2} N
                                (@MulOne.toMul.{u_2} N
                                  (@MulOneClass.toMulOne.{u_2} N
                                    (@Monoid.toMulOneClass.{u_2} N
                                      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                              (@Monoid.toMulOneClass.{u_2}
                                (@MulAut.{u_2} N
                                  (@MulOne.toMul.{u_2} N
                                    (@MulOneClass.toMulOne.{u_2} N
                                      (@Monoid.toMulOneClass.{u_2} N
                                        (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                                (@DivInvMonoid.toMonoid.{u_2}
                                  (@MulAut.{u_2} N
                                    (@MulOne.toMul.{u_2} N
                                      (@MulOneClass.toMulOne.{u_2} N
                                        (@Monoid.toMulOneClass.{u_2} N
                                          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                                  (@Group.toDivInvMonoid.{u_2}
                                    (@MulAut.{u_2} N
                                      (@MulOne.toMul.{u_2} N
                                        (@MulOneClass.toMulOne.{u_2} N
                                          (@Monoid.toMulOneClass.{u_2} N
                                            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                                    (@MulAut.instGroup.{u_2} N
                                      (@MulOne.toMul.{u_2} N
                                        (@MulOneClass.toMulOne.{u_2} N
                                          (@Monoid.toMulOneClass.{u_2} N
                                            (@DivInvMonoid.toMonoid.{u_2} N
                                              (@Group.toDivInvMonoid.{u_2} N inst_1)))))))))))
                          a x)
                        (f y))))
              f x)
            (@HMul.hMul.{u_2, u_2, u_2} N N N
              (@instHMul.{u_2} N
                (@MulOne.toMul.{u_2} N
                  (@MulOneClass.toMulOne.{u_2} N
                    (@Monoid.toMulOneClass.{u_2} N
                      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
              (@Inv.inv.{u_2} N
                (@InvOneClass.toInv.{u_2} N
                  (@DivInvOneMonoid.toInvOneClass.{u_2} N
                    (@DivisionMonoid.toDivInvOneMonoid.{u_2} N (@Group.toDivisionMonoid.{u_2} N inst_1))))
                n)
              (@DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1}
                (@MulEquiv.{u_2, u_2} N N
                  (@MulOne.toMul.{u_2} N
                    (@MulOneClass.toMulOne.{u_2} N
                      (@Monoid.toMulOneClass.{u_2} N
                        (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
                  (@MulOne.toMul.{u_2} N
                    (@MulOneClass.toMulOne.{u_2} N
                      (@Monoid.toMulOneClass.{u_2} N
                        (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                N (fun (x : N) => N)
                (@EquivLike.toFunLike.{u_2 + 1, u_2 + 1, u_2 + 1}
                  (@MulEquiv.{u_2, u_2} N N
                    (@MulOne.toMul.{u_2} N
                      (@MulOneClass.toMulOne.{u_2} N
                        (@Monoid.toMulOneClass.{u_2} N
                          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
                    (@MulOne.toMul.{u_2} N
                      (@MulOneClass.toMulOne.{u_2} N
                        (@Monoid.toMulOneClass.{u_2} N
                          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                  N N
                  (@MulEquiv.instEquivLike.{u_2, u_2} N N
                    (@MulOne.toMul.{u_2} N
                      (@MulOneClass.toMulOne.{u_2} N
                        (@Monoid.toMulOneClass.{u_2} N
                          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
                    (@MulOne.toMul.{u_2} N
                      (@MulOneClass.toMulOne.{u_2} N
                        (@Monoid.toMulOneClass.{u_2} N
                          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))))
                (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
                  (@MonoidHom.{u_1, u_2} J
                    (@MulAut.{u_2} N
                      (@MulOne.toMul.{u_2} N
                        (@MulOneClass.toMulOne.{u_2} N
                          (@Monoid.toMulOneClass.{u_2} N
                            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                    (@MulOneClass.toMulOne.{u_1} J
                      (@Monoid.toMulOneClass.{u_1} J
                        (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
                    (@MulOneClass.toMulOne.{u_2}
                      (@MulAut.{u_2} N
                        (@MulOne.toMul.{u_2} N
                          (@MulOneClass.toMulOne.{u_2} N
                            (@Monoid.toMulOneClass.{u_2} N
                              (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                      (@Monoid.toMulOneClass.{u_2}
                        (@MulAut.{u_2} N
                          (@MulOne.toMul.{u_2} N
                            (@MulOneClass.toMulOne.{u_2} N
                              (@Monoid.toMulOneClass.{u_2} N
                                (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                        (@DivInvMonoid.toMonoid.{u_2}
                          (@MulAut.{u_2} N
                            (@MulOne.toMul.{u_2} N
                              (@MulOneClass.toMulOne.{u_2} N
                                (@Monoid.toMulOneClass.{u_2} N
                                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                          (@Group.toDivInvMonoid.{u_2}
                            (@MulAut.{u_2} N
                              (@MulOne.toMul.{u_2} N
                                (@MulOneClass.toMulOne.{u_2} N
                                  (@Monoid.toMulOneClass.{u_2} N
                                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                            (@MulAut.instGroup.{u_2} N
                              (@MulOne.toMul.{u_2} N
                                (@MulOneClass.toMulOne.{u_2} N
                                  (@Monoid.toMulOneClass.{u_2} N
                                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))))))))
                  J
                  (fun (x : J) =>
                    @MulAut.{u_2} N
                      (@MulOne.toMul.{u_2} N
                        (@MulOneClass.toMulOne.{u_2} N
                          (@Monoid.toMulOneClass.{u_2} N
                            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                  (@MonoidHom.instFunLike.{u_1, u_2} J
                    (@MulAut.{u_2} N
                      (@MulOne.toMul.{u_2} N
                        (@MulOneClass.toMulOne.{u_2} N
                          (@Monoid.toMulOneClass.{u_2} N
                            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                    (@MulOneClass.toMulOne.{u_1} J
                      (@Monoid.toMulOneClass.{u_1} J
                        (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
                    (@MulOneClass.toMulOne.{u_2}
                      (@MulAut.{u_2} N
                        (@MulOne.toMul.{u_2} N
                          (@MulOneClass.toMulOne.{u_2} N
                            (@Monoid.toMulOneClass.{u_2} N
                              (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                      (@Monoid.toMulOneClass.{u_2}
                        (@MulAut.{u_2} N
                          (@MulOne.toMul.{u_2} N
                            (@MulOneClass.toMulOne.{u_2} N
                              (@Monoid.toMulOneClass.{u_2} N
                                (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                        (@DivInvMonoid.toMonoid.{u_2}
                          (@MulAut.{u_2} N
                            (@MulOne.toMul.{u_2} N
                              (@MulOneClass.toMulOne.{u_2} N
                                (@Monoid.toMulOneClass.{u_2} N
                                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                          (@Group.toDivInvMonoid.{u_2}
                            (@MulAut.{u_2} N
                              (@MulOne.toMul.{u_2} N
                                (@MulOneClass.toMulOne.{u_2} N
                                  (@Monoid.toMulOneClass.{u_2} N
                                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
                            (@MulAut.instGroup.{u_2} N
                              (@MulOne.toMul.{u_2} N
                                (@MulOneClass.toMulOne.{u_2} N
                                  (@Monoid.toMulOneClass.{u_2} N
                                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))))))))
                  a x)
                n))),
  Subsingleton.{max (u_2 + 1) (u_1 + 1)} (@LocalConjugacy.FiniteH1.{u_1, u_2} J N inst inst_1 a) :=
  @LocalConjugacy.Proof.finiteH1_subsingleton_of_coboundaries_preparedProof
