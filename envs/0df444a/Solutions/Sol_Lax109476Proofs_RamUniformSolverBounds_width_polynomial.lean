-- Prove2me | solution 1 for Lax109476Proofs.RamUniformSolverBounds.width_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:40:01.706961+00:00
-- url     : https://prove2.me/submissions/958d7df3-9101-40ff-9130-e83841e1a2dc

import Definitions.Def_EdgeSublinearMWIS_Main_NativeNodeCaseInterfaces

section

namespace Lax109476Proofs.RamIntegerFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NormalizedFeasibility IntegerCertificates EllipsoidSequence EllipsoidSearch RamNormalizedBounds

def instructionBound (m n S:ℕ):ℕ:=RamFeasibilitySetup.instructionBound S +
  RamSearchBounds.instructionBound (m + n) n
    (thresholdSteps n (ballExponent m n (2 ^ (2 * S))) + 1) (coefficientBits S)

end Lax109476Proofs.RamIntegerFeasibility

end

section

namespace Lax109476Proofs.RamStoredFeasibilityBounds

theorem wordWidth_monotone {L S:ℕ} (h:L≤ S):
    RamStoredFeasibility.wordWidth L≤ RamStoredFeasibility.wordWidth S:=by
  unfold RamStoredFeasibility.wordWidth RamRationalFeasibility.wordWidth
    RamPaddedFeasibility.wordWidth RamIntegerFeasibility.wordWidth RamFeasibilitySetup.wordWidth
    RamFeasibilityScaleBounds.wordWidth RamSearchBounds.wordWidth RamEllipsoidBitBounds.wordWidth
    RamEllipsoidBitBounds.magnitudeExponent RamEllipsoidBitBounds.formExponent
    RamTrajectoryBounds.stateBits RamNormalizedBounds.coefficientBits
    RamIntegerFeasibility.iterationBound RamDecoder.wordWidth
  gcongr

set_option maxRecDepth 30000 in
theorem instructionBound_monotone {L S:ℕ} (h:L≤ S):
    RamStoredFeasibility.instructionBound L≤ RamStoredFeasibility.instructionBound S:=by
  unfold RamStoredFeasibility.instructionBound RamRationalFeasibility.instructionBound
    RamPaddedFeasibility.instructionBound RamIntegerFeasibility.uniformInstructionBound
    RamFeasibilitySetup.instructionBound RamFeasibilityParameters.instructionBound
    RamSearchBounds.instructionBound RamSearchBounds.stepBound RamSearchBounds.rowBound
    RamTrajectoryBounds.instructionBound RamTrajectoryBounds.stateBits
    RamEllipsoidBitBounds.magnitudeExponent RamEllipsoidBitBounds.formExponent
    RamNormalizedBounds.coefficientBits RamIntegerFeasibility.iterationBound
  dsimp only
  gcongr

end Lax109476Proofs.RamStoredFeasibilityBounds

end

section

namespace Lax109476Proofs.RamRecoveryResourceMonotonicity

attribute [gcongr] RamStoredFeasibilityBounds.wordWidth_monotone
attribute [gcongr] RamStoredFeasibilityBounds.instructionBound_monotone

@[gcongr] theorem reconstruction_width {S T:ℕ} (h:S≤ T):
    RamRationalReconstruction.wordWidth S≤ RamRationalReconstruction.wordWidth T:=by
  unfold RamRationalReconstruction.wordWidth RamRationalReconstruction.depthBound
    RamConvergentBounds.wordWidth RamConvergentBounds.exponent RamDecoder.wordWidth
  gcongr

@[gcongr] theorem point_query_size {m n S r s T:ℕ} (hm:m≤ r) (hn:n≤ s) (hS:S≤ T):
    RamPointRecoveryBounds.querySize m n S≤ RamPointRecoveryBounds.querySize r s T:=by
  unfold RamPointRecoveryBounds.querySize
  gcongr

@[gcongr] theorem point_width {m n S r s T:ℕ} (hm:m≤ r) (hn:n≤ s) (hS:S≤ T):
    RamPointRecoveryBounds.wordWidth m n S≤ RamPointRecoveryBounds.wordWidth r s T:=by
  unfold RamPointRecoveryBounds.wordWidth RamDecoder.wordWidth
  gcongr

@[gcongr] theorem cap_bits {S T:ℕ} (h:S≤ T):
    RamRecoverFeasibleSystem.capBits S≤ RamRecoverFeasibleSystem.capBits T:=by
  unfold RamRecoverFeasibleSystem.capBits
  gcongr

@[gcongr] theorem recovery_bits {S T:ℕ} (h:S≤ T):
    RamRecoverFeasibleSystem.recoveryBits S≤ RamRecoverFeasibleSystem.recoveryBits T:=by
  unfold RamRecoverFeasibleSystem.recoveryBits
  gcongr

@[gcongr] theorem recovery_width {m n S r s T:ℕ} (hm:m≤ r) (hn:n≤ s) (hS:S≤ T):
    RamRecoverFeasibleSystem.wordWidth m n S≤ RamRecoverFeasibleSystem.wordWidth r s T:=by
  unfold RamRecoverFeasibleSystem.wordWidth RamCoordinateCapBounds.wordWidth
  gcongr

end Lax109476Proofs.RamRecoveryResourceMonotonicity

end

section

namespace Lax109476Proofs.RamResourcePolynomial

theorem constant (k:ℕ):HasPolynomial (fun _ => k):=by
  unfold HasPolynomial at *
  exact ⟨Polynomial.C k,fun n => by simp⟩

theorem identity:HasPolynomial (fun n => n):=by
  unfold HasPolynomial at *
  exact ⟨Polynomial.X,fun n => by simp⟩

theorem add {f g:ℕ→ ℕ} (hf:HasPolynomial f) (hg:HasPolynomial g):
    HasPolynomial (fun n => f n + g n):=by
  unfold HasPolynomial at *
  obtain ⟨p,hp⟩:=hf
  obtain ⟨q,hq⟩:=hg
  exact ⟨p + q,fun n => by simp [hp,hq]⟩

theorem mul {f g:ℕ→ ℕ} (hf:HasPolynomial f) (hg:HasPolynomial g):
    HasPolynomial (fun n => f n * g n):=by
  unfold HasPolynomial at *
  obtain ⟨p,hp⟩:=hf
  obtain ⟨q,hq⟩:=hg
  exact ⟨p * q,fun n => by simp [hp,hq]⟩

theorem pow {f:ℕ→ ℕ} (hf:HasPolynomial f) (k:ℕ):
    HasPolynomial (fun n => (f n) ^ k):=by
  unfold HasPolynomial at *
  obtain ⟨p,hp⟩:=hf
  exact ⟨p ^ k,fun n => by simp [hp]⟩

theorem compose {f g:ℕ→ ℕ} (hf:HasPolynomial f) (hg:HasPolynomial g):
    HasPolynomial (fun n => f (g n)):=by
  unfold HasPolynomial at *
  obtain ⟨p,hp⟩:=hf
  obtain ⟨q,hq⟩:=hg
  exact ⟨p.comp q,fun n => by simp [Polynomial.eval_comp,hp,hq]⟩

noncomputable abbrev _root_.AXr5282_0:= @Lax109476Proofs.RamResourcePolynomial.HasPolynomial
noncomputable abbrev _root_.AXr5282_1:= @Lax109476Proofs.RamResourcePolynomial.constant
noncomputable abbrev _root_.AXr5282_2:= @Lax109476Proofs.RamResourcePolynomial.add
theorem decoded_size:AXr5282_0 Lax109476Proofs.RamDecodedProgram.canonicalBound:=
let c0:Nat→ Nat→ Nat:=Nat.add;
let c1:Nat→ Nat→ Nat:=Nat.mul;
let c2:Nat→ Nat:=c1 ((2:Nat));
let c3:Nat→ Nat:=fun (n:Nat) => c2 n;
let c4:
  ∀ {g:Nat→ Nat},
    (AXr5282_0 fun (x:Nat) =>
        (2:Nat))→
      AXr5282_0 g→
        AXr5282_0 fun (n:Nat) =>
          Nat.mul ((2:Nat))
            (g n):=
  @Lax109476Proofs.RamResourcePolynomial.mul fun (x:Nat) => (2:Nat);
let c5:
  AXr5282_0 fun (n:Nat) =>
    Nat.mul ((2:Nat)) n:=
  @c4 (fun (n:Nat) => n)
    (AXr5282_1 ((2:Nat)))
    Lax109476Proofs.RamResourcePolynomial.identity;
let c6:Nat→ Nat:=fun (n:Nat) => c0 n ((1:Nat));
let c7:
  AXr5282_0 fun (n:Nat) =>
    Nat.add n ((1:Nat)):=
  @AXr5282_2 (fun (n:Nat) => n)
    (fun (x:Nat) => (1:Nat))
    Lax109476Proofs.RamResourcePolynomial.identity
    (AXr5282_1 ((1:Nat)));
@AXr5282_2
  (fun (n:Nat) => c0 (c2 n) ((4:Nat)))
  (fun (n:Nat) =>
    let c0_1:Nat:=c0 n ((1:Nat));
    c1
      (c0
        (c0
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) c0_1
            ((2:Nat)))
          (c2 n))
        ((2:Nat)))
      (c0 ((4:Nat)) (c2 c0_1)))
  (@AXr5282_2 c3
    (fun (x:Nat) => (4:Nat)) c5
    (AXr5282_1 ((4:Nat))))
  (@Lax109476Proofs.RamResourcePolynomial.mul
    (fun (n:Nat) =>
      c0
        (c0
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (c0 n ((1:Nat)))
            ((2:Nat)))
          (c2 n))
        ((2:Nat)))
    (fun (n:Nat) =>
      c0 ((4:Nat))
        (c2 (c0 n ((1:Nat)))))
    (@AXr5282_2
      (fun (n:Nat) =>
        c0
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (c0 n ((1:Nat)))
            ((2:Nat)))
          (c2 n))
      (fun (x:Nat) => (2:Nat))
      (@AXr5282_2
        (fun (n:Nat) =>
          @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (c0 n ((1:Nat)))
            ((2:Nat)))
        c3 (@Lax109476Proofs.RamResourcePolynomial.pow c6 c7 ((2:Nat)))
        c5)
      (AXr5282_1 ((2:Nat))))
    (@AXr5282_2
      (fun (x:Nat) => (4:Nat))
      (fun (n:Nat) => c2 (c0 n ((1:Nat))))
      (AXr5282_1 ((4:Nat)))
      (@c4 c6 (AXr5282_1 ((2:Nat)))
        c7)))

theorem parameter:Lax109476Proofs.RamResourcePolynomial.HasPolynomial Lax109476Proofs.RamCertificateSetup.parameter:=
@Lax109476Proofs.RamResourcePolynomial.mul (fun (x:Nat) => (2:Nat))
  (fun (n:Nat) =>
    Nat.add n ((4:Nat)))
  (Lax109476Proofs.RamResourcePolynomial.constant ((2:Nat)))
  (@Lax109476Proofs.RamResourcePolynomial.add (fun (n:Nat) => n)
    (fun (x:Nat) => (4:Nat))
    Lax109476Proofs.RamResourcePolynomial.identity
    (Lax109476Proofs.RamResourcePolynomial.constant ((4:Nat))))

noncomputable abbrev _root_.AXr5284_0:= @Lax109476Proofs.RamResourcePolynomial.HasPolynomial
noncomputable abbrev _root_.AXr5284_1:= @Lax109476Proofs.RamResourcePolynomial.constant
noncomputable abbrev _root_.AXr5284_2:= @Lax109476Proofs.RamResourcePolynomial.identity
noncomputable abbrev _root_.AXr5284_3:= @Lax109476Proofs.RamResourcePolynomial.add
noncomputable abbrev _root_.AXr5284_4:= @Lax109476Proofs.RamResourcePolynomial.mul
theorem stored_width:AXr5284_0 Lax109476Proofs.RamStoredFeasibility.wordWidth:=
let c0:Nat→ Nat→ Nat:=Nat.mul;
let c1:Nat→ Nat:=c0 ((4:Nat));
let c2:Nat→ Nat→ Nat:=Nat.add;
let c3:Nat→ Nat→ Nat:=
  @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)));
let c4:Nat→ Nat:=c0 ((2:Nat));
let c5:
  ∀ {g:Nat→ Nat},
    (AXr5284_0 fun (x:Nat) =>
        (4:Nat))→
      AXr5284_0 g→
        AXr5284_0 fun (n:Nat) =>
          Nat.mul ((4:Nat))
            (g n):=
  @AXr5284_4 fun (x:Nat) => (4:Nat);
let c6:Nat→ Nat:=fun (n:Nat) => c1 (c2 (c4 n) ((2:Nat)));
let c7:Nat→ Nat:=fun (n:Nat) => c2 n ((4:Nat));
let c8:Nat→ Nat:=fun (n:Nat) =>
  c3
    (c2 (c2 n ((4:Nat)))
      ((1:Nat)))
    ((2:Nat));
let c9:Nat→ Nat:=fun (n:Nat) =>
  c3
    (c2 (c2 n ((4:Nat)))
      ((1:Nat)))
    ((4:Nat));
let c10:Nat→ Nat:=fun (n:Nat) =>
  c2 (c2 n ((4:Nat)))
    ((1:Nat));
let c11:
  AXr5284_0 fun (n:Nat) =>
    Nat.add n ((4:Nat)):=
  @AXr5284_3 (fun (n:Nat) => n)
    (fun (x:Nat) => (4:Nat))
    AXr5284_2
    (AXr5284_1 ((4:Nat)));
let c12:
  AXr5284_0 fun (n:Nat) =>
    Nat.add (c7 n)
      ((1:Nat)):=
  @AXr5284_3 c7
    (fun (x:Nat) => (1:Nat)) c11
    (AXr5284_1 ((1:Nat)));
let c13:
  ∀ (k:Nat),
    AXr5284_0 fun (n:Nat) =>
      @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) (c10 n) k:=
  @Lax109476Proofs.RamResourcePolynomial.pow c10 c12;
let c14:
  AXr5284_0 fun (n:Nat) =>
    @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) (c10 n)
      ((4:Nat)):=
  c13 ((4:Nat));
let c15:Nat→ Nat:=fun (n:Nat) =>
  let c0_1:Nat:=c2 n ((4:Nat));
  c2
    (c2
      (c0 ((128:Nat))
        (c3 (c2 c0_1 ((1:Nat)))
          ((2:Nat))))
      (c4 c0_1))
    ((2:Nat));
let c16:
  AXr5284_0 fun (n:Nat) =>
    @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) (c10 n)
      ((2:Nat)):=
  c13 ((2:Nat));
let c17:
  ∀ {g:Nat→ Nat},
    (AXr5284_0 fun (x:Nat) =>
        (2:Nat))→
      AXr5284_0 g→
        AXr5284_0 fun (n:Nat) =>
          Nat.mul ((2:Nat))
            (g n):=
  @AXr5284_4 fun (x:Nat) => (2:Nat);
let c18:
  AXr5284_0 fun (n:Nat) =>
    Nat.add
      (let c0_1:Nat:=c2 n ((4:Nat));
      c2
        (c0 ((128:Nat))
          (c3 (c2 c0_1 ((1:Nat)))
            ((2:Nat))))
        (c4 c0_1))
      ((2:Nat)):=
  @AXr5284_3
    (fun (n:Nat) =>
      let c0_1:Nat:=c2 n ((4:Nat));
      c2
        (c0 ((128:Nat))
          (c3 (c2 c0_1 ((1:Nat)))
            ((2:Nat))))
        (c4 c0_1))
    (fun (x:Nat) => (2:Nat))
    (@AXr5284_3
      (fun (n:Nat) =>
        c0 ((128:Nat))
          (c3
            (c2 (c2 n ((4:Nat)))
              ((1:Nat)))
            ((2:Nat))))
      (fun (n:Nat) => c4 (c2 n ((4:Nat))))
      (@AXr5284_4
        (fun (x:Nat) => (128:Nat)) c8
        (AXr5284_1 ((128:Nat)))
        c16)
      (@c17 c7
        (AXr5284_1 ((2:Nat))) c11))
    (AXr5284_1 ((2:Nat)));
let c19:Nat→ Nat:=fun (n:Nat) =>
  c2
    (c0 ((1024:Nat))
      (c3
        (c2 (c2 n ((4:Nat)))
          ((1:Nat)))
        ((4:Nat))))
    ((1:Nat));
let c20:Nat→ Nat:=fun (n:Nat) =>
  let c0_1:Nat:=c2 n ((4:Nat));
  c0 c0_1 c0_1;
let c21:
  AXr5284_0 fun (n:Nat) =>
    Nat.add
      (c0 ((1024:Nat))
        (c3
          (c2 (c2 n ((4:Nat)))
            ((1:Nat)))
          ((4:Nat))))
      ((1:Nat)):=
  @AXr5284_3
    (fun (n:Nat) =>
      c0 ((1024:Nat))
        (c3
          (c2 (c2 n ((4:Nat)))
            ((1:Nat)))
          ((4:Nat))))
    (fun (x:Nat) => (1:Nat))
    (@AXr5284_4
      (fun (x:Nat) => (1024:Nat)) c9
      (AXr5284_1 ((1024:Nat)))
      c14)
    (AXr5284_1 ((1:Nat)));
let c22:
  AXr5284_0 fun (n:Nat) =>
    Nat.mul (c7 n) (c7 n):=
  @AXr5284_4 c7 c7 c11 c11;
let c23:
  AXr5284_0 fun (n:Nat) =>
    Nat.mul ((4:Nat))
      (c2 (c4 n) ((2:Nat))):=
  @c5 (fun (n:Nat) => c2 (c4 n) ((2:Nat)))
    (AXr5284_1 ((4:Nat)))
    (@AXr5284_3 (fun (n:Nat) => c4 n)
      (fun (x:Nat) => (2:Nat))
      (@c17 (fun (n:Nat) => n)
        (AXr5284_1 ((2:Nat)))
        AXr5284_2)
      (AXr5284_1 ((2:Nat))));
@AXr5284_3
  (fun (n:Nat) => c1 (c2 n ((2:Nat))))
  (fun (n:Nat) =>
    let c0_1:Nat:=c2 n ((4:Nat));
    let c1_1:Nat:=c2 c0_1 ((1:Nat));
    let c2_1:Nat→ Nat:=c3 c1_1;
    let c3_1:Nat:=c2_1 ((4:Nat));
    let c4_1:Nat:=c2_1 ((2:Nat));
    let c5:Nat:=
      c2 (c2 (c0 ((128:Nat)) c4_1) (c4 c0_1))
        ((2:Nat));
    let c6:Nat:=
      c2 (c0 ((1024:Nat)) c3_1)
        ((1:Nat));
    let c7:Nat:=c0 c0_1 c0_1;
    let c8:Nat:=c1 (c2 (c4 n) ((2:Nat)));
    c2
      (c2
        (c2
          (c2
            (c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2 (c0 ((4096:Nat)) c3_1)
                        (c1 (c2 c5 ((2:Nat)))))
                      c4_1)
                    c0_1)
                  ((2:Nat)))
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c0 ((64:Nat))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c6))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    c5))
                                                ((1:Nat)))
                                              c1_1))
                                          ((1:Nat)))
                                        c1_1)
                                      c7)
                                    (c4 c6))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat))))
                            ((224:Nat)))
                          c0_1)
                        c0_1)
                      c7)
                    c6)
                  ((2:Nat))))
              c8)
            (c3 c0_1 ((2:Nat))))
          n)
        ((5:Nat)))
      c8)
  (@c5 (fun (n:Nat) => c2 n ((2:Nat)))
    (AXr5284_1 ((4:Nat)))
    (@AXr5284_3 (fun (n:Nat) => n)
      (fun (x:Nat) => (2:Nat))
      AXr5284_2
      (AXr5284_1 ((2:Nat)))))
  (@AXr5284_3
    (fun (n:Nat) =>
      let c0_1:Nat:=c2 n ((4:Nat));
      let c1_1:Nat:=c2 c0_1 ((1:Nat));
      let c2_1:Nat→ Nat:=c3 c1_1;
      let c3_1:Nat:=c2_1 ((4:Nat));
      let c4_1:Nat:=c2_1 ((2:Nat));
      let c5:Nat:=
        c2 (c2 (c0 ((128:Nat)) c4_1) (c4 c0_1))
          ((2:Nat));
      let c6:Nat:=
        c2 (c0 ((1024:Nat)) c3_1)
          ((1:Nat));
      let c7:Nat:=c0 c0_1 c0_1;
      c2
        (c2
          (c2
            (c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2 (c0 ((4096:Nat)) c3_1)
                        (c1 (c2 c5 ((2:Nat)))))
                      c4_1)
                    c0_1)
                  ((2:Nat)))
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c0 ((64:Nat))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c6))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    c5))
                                                ((1:Nat)))
                                              c1_1))
                                          ((1:Nat)))
                                        c1_1)
                                      c7)
                                    (c4 c6))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat))))
                            ((224:Nat)))
                          c0_1)
                        c0_1)
                      c7)
                    c6)
                  ((2:Nat))))
              (c1 (c2 (c4 n) ((2:Nat)))))
            (c3 c0_1 ((2:Nat))))
          n)
        ((5:Nat)))
    c6
    (@AXr5284_3
      (fun (n:Nat) =>
        let c0_1:Nat:=c2 n ((4:Nat));
        let c1_1:Nat:=c2 c0_1 ((1:Nat));
        let c2_1:Nat→ Nat:=c3 c1_1;
        let c3_1:Nat:=c2_1 ((4:Nat));
        let c4_1:Nat:=c2_1 ((2:Nat));
        let c5:Nat:=
          c2 (c2 (c0 ((128:Nat)) c4_1) (c4 c0_1))
            ((2:Nat));
        let c6:Nat:=
          c2 (c0 ((1024:Nat)) c3_1)
            ((1:Nat));
        let c7:Nat:=c0 c0_1 c0_1;
        c2
          (c2
            (c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2 (c0 ((4096:Nat)) c3_1)
                        (c1 (c2 c5 ((2:Nat)))))
                      c4_1)
                    c0_1)
                  ((2:Nat)))
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c0 ((64:Nat))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c6))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    c5))
                                                ((1:Nat)))
                                              c1_1))
                                          ((1:Nat)))
                                        c1_1)
                                      c7)
                                    (c4 c6))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat))))
                            ((224:Nat)))
                          c0_1)
                        c0_1)
                      c7)
                    c6)
                  ((2:Nat))))
              (c1 (c2 (c4 n) ((2:Nat)))))
            (c3 c0_1 ((2:Nat))))
          n)
      (fun (x:Nat) => (5:Nat))
      (@AXr5284_3
        (fun (n:Nat) =>
          let c0_1:Nat:=c2 n ((4:Nat));
          let c1_1:Nat:=c2 c0_1 ((1:Nat));
          let c2_1:Nat→ Nat:=c3 c1_1;
          let c3_1:Nat:=c2_1 ((4:Nat));
          let c4_1:Nat:=c2_1 ((2:Nat));
          let c5:Nat:=
            c2 (c2 (c0 ((128:Nat)) c4_1) (c4 c0_1))
              ((2:Nat));
          let c6:Nat:=
            c2 (c0 ((1024:Nat)) c3_1)
              ((1:Nat));
          let c7:Nat:=c0 c0_1 c0_1;
          c2
            (c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2 (c0 ((4096:Nat)) c3_1)
                        (c1 (c2 c5 ((2:Nat)))))
                      c4_1)
                    c0_1)
                  ((2:Nat)))
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c0 ((64:Nat))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c6))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    c5))
                                                ((1:Nat)))
                                              c1_1))
                                          ((1:Nat)))
                                        c1_1)
                                      c7)
                                    (c4 c6))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat))))
                            ((224:Nat)))
                          c0_1)
                        c0_1)
                      c7)
                    c6)
                  ((2:Nat))))
              (c1 (c2 (c4 n) ((2:Nat)))))
            (c3 c0_1 ((2:Nat))))
        (fun (n:Nat) => n)
        (@AXr5284_3
          (fun (n:Nat) =>
            let c0_1:Nat:=c2 n ((4:Nat));
            let c1_1:Nat:=c2 c0_1 ((1:Nat));
            let c2_1:Nat→ Nat:=c3 c1_1;
            let c3:Nat:=c2_1 ((4:Nat));
            let c4_1:Nat:=c2_1 ((2:Nat));
            let c5:Nat:=
              c2 (c2 (c0 ((128:Nat)) c4_1) (c4 c0_1))
                ((2:Nat));
            let c6:Nat:=
              c2 (c0 ((1024:Nat)) c3)
                ((1:Nat));
            let c7:Nat:=c0 c0_1 c0_1;
            c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2 (c0 ((4096:Nat)) c3)
                        (c1 (c2 c5 ((2:Nat)))))
                      c4_1)
                    c0_1)
                  ((2:Nat)))
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c0 ((64:Nat))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c6))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    c5))
                                                ((1:Nat)))
                                              c1_1))
                                          ((1:Nat)))
                                        c1_1)
                                      c7)
                                    (c4 c6))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat))))
                            ((224:Nat)))
                          c0_1)
                        c0_1)
                      c7)
                    c6)
                  ((2:Nat))))
              (c1 (c2 (c4 n) ((2:Nat)))))
          (fun (n:Nat) =>
            c3 (c2 n ((4:Nat)))
              ((2:Nat)))
          (@AXr5284_3
            (fun (n:Nat) =>
              let c0_1:Nat:=c2 n ((4:Nat));
              let c1_1:Nat:=c2 c0_1 ((1:Nat));
              let c2_1:Nat→ Nat:=c3 c1_1;
              let c3:Nat:=c2_1 ((4:Nat));
              let c4_1:Nat:=c2_1 ((2:Nat));
              let c5:Nat:=
                c2 (c2 (c0 ((128:Nat)) c4_1) (c4 c0_1))
                  ((2:Nat));
              let c6:Nat:=
                c2 (c0 ((1024:Nat)) c3)
                  ((1:Nat));
              let c7:Nat:=c0 c0_1 c0_1;
              c2
                (c2
                  (c2
                    (c2
                      (c2 (c0 ((4096:Nat)) c3)
                        (c1 (c2 c5 ((2:Nat)))))
                      c4_1)
                    c0_1)
                  ((2:Nat)))
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c0 ((64:Nat))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c6))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    c5))
                                                ((1:Nat)))
                                              c1_1))
                                          ((1:Nat)))
                                        c1_1)
                                      c7)
                                    (c4 c6))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat))))
                            ((224:Nat)))
                          c0_1)
                        c0_1)
                      c7)
                    c6)
                  ((2:Nat))))
            c6
            (@AXr5284_3
              (fun (n:Nat) =>
                let c0_1:Nat:=c2 n ((4:Nat));
                let c1_1:Nat→ Nat:=c3 (c2 c0_1 ((1:Nat)));
                let c2_1:Nat:=c1_1 ((2:Nat));
                c2
                  (c2
                    (c2
                      (c2
                        (c0 ((4096:Nat))
                          (c1_1 ((4:Nat))))
                        (c1
                          (c2
                            (c2 (c2 (c0 ((128:Nat)) c2_1) (c4 c0_1))
                              ((2:Nat)))
                            ((2:Nat)))))
                      c2_1)
                    c0_1)
                  ((2:Nat)))
              (fun (n:Nat) =>
                let c0_1:Nat:=c2 n ((4:Nat));
                let c1:Nat:=c2 c0_1 ((1:Nat));
                let c2_1:Nat→ Nat:=c3 c1;
                let c3:Nat:=
                  c2
                    (c0 ((1024:Nat))
                      (c2_1 ((4:Nat))))
                    ((1:Nat));
                let c4_1:Nat:=c0 c0_1 c0_1;
                c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c0 ((64:Nat))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c3))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                          ((1:Nat)))
                                        c1)
                                      c4_1)
                                    (c4 c3))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat))))
                            ((224:Nat)))
                          c0_1)
                        c0_1)
                      c4_1)
                    c3)
                  ((2:Nat)))
              (@AXr5284_3
                (fun (n:Nat) =>
                  let c0_1:Nat:=c2 n ((4:Nat));
                  let c1_1:Nat→ Nat:=c3 (c2 c0_1 ((1:Nat)));
                  let c2_1:Nat:=c1_1 ((2:Nat));
                  c2
                    (c2
                      (c2
                        (c0 ((4096:Nat))
                          (c1_1 ((4:Nat))))
                        (c1
                          (c2
                            (c2 (c2 (c0 ((128:Nat)) c2_1) (c4 c0_1))
                              ((2:Nat)))
                            ((2:Nat)))))
                      c2_1)
                    c0_1)
                (fun (x:Nat) => (2:Nat))
                (@AXr5284_3
                  (fun (n:Nat) =>
                    let c0_1:Nat:=c2 n ((4:Nat));
                    let c1_1:Nat→ Nat:=c3 (c2 c0_1 ((1:Nat)));
                    let c2_1:Nat:=c1_1 ((2:Nat));
                    c2
                      (c2
                        (c0 ((4096:Nat))
                          (c1_1 ((4:Nat))))
                        (c1
                          (c2
                            (c2 (c2 (c0 ((128:Nat)) c2_1) (c4 c0_1))
                              ((2:Nat)))
                            ((2:Nat)))))
                      c2_1)
                  c7
                  (@AXr5284_3
                    (fun (n:Nat) =>
                      let c0_1:Nat:=c2 n ((4:Nat));
                      let c1_1:Nat→ Nat:=c3 (c2 c0_1 ((1:Nat)));
                      c2
                        (c0 ((4096:Nat))
                          (c1_1 ((4:Nat))))
                        (c1
                          (c2
                            (c2
                              (c2
                                (c0 ((128:Nat))
                                  (c1_1 ((2:Nat))))
                                (c4 c0_1))
                              ((2:Nat)))
                            ((2:Nat)))))
                    c8
                    (@AXr5284_3
                      (fun (n:Nat) =>
                        c0 ((4096:Nat))
                          (c3
                            (c2 (c2 n ((4:Nat)))
                              ((1:Nat)))
                            ((4:Nat))))
                      (fun (n:Nat) =>
                        let c0_1:Nat:=c2 n ((4:Nat));
                        c1
                          (c2
                            (c2
                              (c2
                                (c0 ((128:Nat))
                                  (c3 (c2 c0_1 ((1:Nat)))
                                    ((2:Nat))))
                                (c4 c0_1))
                              ((2:Nat)))
                            ((2:Nat))))
                      (@AXr5284_4
                        (fun (x:Nat) => (4096:Nat)) c9
                        (AXr5284_1
                          ((4096:Nat)))
                        c14)
                      (@c5
                        (fun (n:Nat) =>
                          let c0_1:Nat:=c2 n ((4:Nat));
                          c2
                            (c2
                              (c2
                                (c0 ((128:Nat))
                                  (c3 (c2 c0_1 ((1:Nat)))
                                    ((2:Nat))))
                                (c4 c0_1))
                              ((2:Nat)))
                            ((2:Nat)))
                        (AXr5284_1
                          ((4:Nat)))
                        (@AXr5284_3 c15
                          (fun (x:Nat) => (2:Nat)) c18
                          (AXr5284_1
                            ((2:Nat))))))
                    c16)
                  c11)
                (AXr5284_1
                  ((2:Nat))))
              (@AXr5284_3
                (fun (n:Nat) =>
                  let c0_1:Nat:=c2 n ((4:Nat));
                  let c1:Nat:=c2 c0_1 ((1:Nat));
                  let c2_1:Nat→ Nat:=c3 c1;
                  let c3:Nat:=
                    c2
                      (c0 ((1024:Nat))
                        (c2_1 ((4:Nat))))
                      ((1:Nat));
                  let c4_1:Nat:=c0 c0_1 c0_1;
                  c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c0 ((64:Nat))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c3))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                          ((1:Nat)))
                                        c1)
                                      c4_1)
                                    (c4 c3))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat))))
                            ((224:Nat)))
                          c0_1)
                        c0_1)
                      c4_1)
                    c3)
                (fun (x:Nat) => (2:Nat))
                (@AXr5284_3
                  (fun (n:Nat) =>
                    let c0_1:Nat:=c2 n ((4:Nat));
                    let c1:Nat:=c2 c0_1 ((1:Nat));
                    let c2_1:Nat→ Nat:=c3 c1;
                    let c3:Nat:=
                      c2
                        (c0 ((1024:Nat))
                          (c2_1 ((4:Nat))))
                        ((1:Nat));
                    let c4_1:Nat:=c0 c0_1 c0_1;
                    c2
                      (c2
                        (c2
                          (c2
                            (c0 ((64:Nat))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c3))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                          ((1:Nat)))
                                        c1)
                                      c4_1)
                                    (c4 c3))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat))))
                            ((224:Nat)))
                          c0_1)
                        c0_1)
                      c4_1)
                  c19
                  (@AXr5284_3
                    (fun (n:Nat) =>
                      let c0_1:Nat:=c2 n ((4:Nat));
                      let c1:Nat:=c2 c0_1 ((1:Nat));
                      let c2_1:Nat→ Nat:=c3 c1;
                      let c3:Nat:=
                        c2
                          (c0 ((1024:Nat))
                            (c2_1 ((4:Nat))))
                          ((1:Nat));
                      c2
                        (c2
                          (c2
                            (c0 ((64:Nat))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c3))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                          ((1:Nat)))
                                        c1)
                                      (c0 c0_1 c0_1))
                                    (c4 c3))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat))))
                            ((224:Nat)))
                          c0_1)
                        c0_1)
                    c20
                    (@AXr5284_3
                      (fun (n:Nat) =>
                        let c0_1:Nat:=c2 n ((4:Nat));
                        let c1:Nat:=c2 c0_1 ((1:Nat));
                        let c2_1:Nat→ Nat:=c3 c1;
                        let c3:Nat:=
                          c2
                            (c0 ((1024:Nat))
                              (c2_1 ((4:Nat))))
                            ((1:Nat));
                        c2
                          (c2
                            (c0 ((64:Nat))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c3))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                          ((1:Nat)))
                                        c1)
                                      (c0 c0_1 c0_1))
                                    (c4 c3))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat))))
                            ((224:Nat)))
                          c0_1)
                      c7
                      (@AXr5284_3
                        (fun (n:Nat) =>
                          let c0_1:Nat:=c2 n ((4:Nat));
                          let c1:Nat:=c2 c0_1 ((1:Nat));
                          let c2_1:Nat→ Nat:=c3 c1;
                          let c3:Nat:=
                            c2
                              (c0 ((1024:Nat))
                                (c2_1 ((4:Nat))))
                              ((1:Nat));
                          c2
                            (c0 ((64:Nat))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c3))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                          ((1:Nat)))
                                        c1)
                                      (c0 c0_1 c0_1))
                                    (c4 c3))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat))))
                            ((224:Nat)))
                        c7
                        (@AXr5284_3
                          (fun (n:Nat) =>
                            let c0_1:Nat:=c2 n ((4:Nat));
                            let c1:Nat:=c2 c0_1 ((1:Nat));
                            let c2_1:Nat→ Nat:=c3 c1;
                            let c3:Nat:=
                              c2
                                (c0 ((1024:Nat))
                                  (c2_1 ((4:Nat))))
                                ((1:Nat));
                            c0 ((64:Nat))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c3))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                          ((1:Nat)))
                                        c1)
                                      (c0 c0_1 c0_1))
                                    (c4 c3))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat))))
                          (fun (x:Nat) => (224:Nat))
                          (@AXr5284_4
                            (fun (x:Nat) => (64:Nat))
                            (fun (n:Nat) =>
                              let c0_1:Nat:=c2 n ((4:Nat));
                              let c1:Nat:=c2 c0_1 ((1:Nat));
                              let c2_1:Nat→ Nat:=c3 c1;
                              let c3:Nat:=
                                c2
                                  (c0 ((1024:Nat))
                                    (c2_1 ((4:Nat))))
                                  ((1:Nat));
                              c2
                                (c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c3))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                          ((1:Nat)))
                                        c1)
                                      (c0 c0_1 c0_1))
                                    (c4 c3))
                                  (c0 ((5:Nat)) c0_1))
                                ((13:Nat)))
                            (AXr5284_1
                              ((64:Nat)))
                            (@AXr5284_3
                              (fun (n:Nat) =>
                                let c0_1:Nat:=c2 n ((4:Nat));
                                let c1:Nat:=c2 c0_1 ((1:Nat));
                                let c2_1:Nat→ Nat:=c3 c1;
                                let c3:Nat:=
                                  c2
                                    (c0 ((1024:Nat))
                                      (c2_1 ((4:Nat))))
                                    ((1:Nat));
                                c2
                                  (c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c3))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                          ((1:Nat)))
                                        c1)
                                      (c0 c0_1 c0_1))
                                    (c4 c3))
                                  (c0 ((5:Nat)) c0_1))
                              (fun (x:Nat) => (13:Nat))
                              (@AXr5284_3
                                (fun (n:Nat) =>
                                  let c0_1:Nat:=c2 n ((4:Nat));
                                  let c1:Nat:=c2 c0_1 ((1:Nat));
                                  let c2_1:Nat→ Nat:=c3 c1;
                                  let c3:Nat:=
                                    c2
                                      (c0 ((1024:Nat))
                                        (c2_1 ((4:Nat))))
                                      ((1:Nat));
                                  c2
                                    (c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          c3))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                          ((1:Nat)))
                                        c1)
                                      (c0 c0_1 c0_1))
                                    (c4 c3))
                                (fun (n:Nat) =>
                                  c0 ((5:Nat))
                                    (c2 n ((4:Nat))))
                                (@AXr5284_3
                                  (fun (n:Nat) =>
                                    let c0_1:Nat:=c2 n ((4:Nat));
                                    let c1:Nat:=c2 c0_1 ((1:Nat));
                                    let c2_1:Nat→ Nat:=c3 c1;
                                    c2
                                      (c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          (c2
                                                            (c0
                                                              ((1024:Nat))
                                                              (c2_1
                                                                ((4:Nat))))
                                                            ((1:Nat)))))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                          ((1:Nat)))
                                        c1)
                                      (c0 c0_1 c0_1))
                                  (fun (n:Nat) =>
                                    c4
                                      (c2
                                        (c0 ((1024:Nat))
                                          (c3
                                            (c2 (c2 n ((4:Nat)))
                                              ((1:Nat)))
                                            ((4:Nat))))
                                        ((1:Nat))))
                                  (@AXr5284_3
                                    (fun (n:Nat) =>
                                      let c0_1:Nat:=c2 n ((4:Nat));
                                      let c1:Nat:=c2 c0_1 ((1:Nat));
                                      let c2_1:Nat→ Nat:=c3 c1;
                                      c0
                                        (c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          (c2
                                                            (c0
                                                              ((1024:Nat))
                                                              (c2_1
                                                                ((4:Nat))))
                                                            ((1:Nat)))))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                          ((1:Nat)))
                                        c1)
                                    c20
                                    (@AXr5284_4
                                      (fun (n:Nat) =>
                                        let c0_1:Nat:=
                                          c2 n ((4:Nat));
                                        let c1:Nat:=
                                          c2 c0_1 ((1:Nat));
                                        let c2_1:Nat→ Nat:=c3 c1;
                                        c2
                                          (c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          (c2
                                                            (c0
                                                              ((1024:Nat))
                                                              (c2_1
                                                                ((4:Nat))))
                                                            ((1:Nat)))))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                          ((1:Nat)))
                                      c10
                                      (@AXr5284_3
                                        (fun (n:Nat) =>
                                          let c0_1:Nat:=
                                            c2 n ((4:Nat));
                                          let c1:Nat:=
                                            c2 c0_1 ((1:Nat));
                                          let c2_1:Nat→ Nat:=c3 c1;
                                          c4
                                            (c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          (c2
                                                            (c0
                                                              ((1024:Nat))
                                                              (c2_1
                                                                ((4:Nat))))
                                                            ((1:Nat)))))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1))
                                        (fun (x:Nat) => (1:Nat))
                                        (@c17
                                          (fun (n:Nat) =>
                                            let c0_1:Nat:=
                                              c2 n ((4:Nat));
                                            let c1:Nat:=
                                              c2 c0_1 ((1:Nat));
                                            let c2_1:Nat→ Nat:=c3 c1;
                                            c0
                                              (c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          (c2
                                                            (c0
                                                              ((1024:Nat))
                                                              (c2_1
                                                                ((4:Nat))))
                                                            ((1:Nat)))))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c2_1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                              c1)
                                          (AXr5284_1
                                            ((2:Nat)))
                                          (@AXr5284_4
                                            (fun (n:Nat) =>
                                              let c0_1:Nat:=
                                                c2 n ((4:Nat));
                                              let c1:Nat→ Nat:=
                                                c3 (c2 c0_1 ((1:Nat)));
                                              c2
                                                (c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          (c2
                                                            (c0
                                                              ((1024:Nat))
                                                              (c1
                                                                ((4:Nat))))
                                                            ((1:Nat)))))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                                ((1:Nat)))
                                            c10
                                            (@AXr5284_3
                                              (fun (n:Nat) =>
                                                let c0_1:Nat:=
                                                  c2 n ((4:Nat));
                                                let c1:Nat→ Nat:=
                                                  c3
                                                    (c2 c0_1 ((1:Nat)));
                                                c4
                                                  (c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          (c2
                                                            (c0
                                                              ((1024:Nat))
                                                              (c1
                                                                ((4:Nat))))
                                                            ((1:Nat)))))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat)))))
                                              (fun (x:Nat) => (1:Nat))
                                              (@c17
                                                (fun (n:Nat) =>
                                                  let c0_1:Nat:=
                                                    c2 n ((4:Nat));
                                                  let c1:Nat→ Nat:=
                                                    c3
                                                      (c2 c0_1
                                                        ((1:Nat)));
                                                  c2
                                                    (c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          (c2
                                                            (c0
                                                              ((1024:Nat))
                                                              (c1
                                                                ((4:Nat))))
                                                            ((1:Nat)))))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                    (c2
                                                      (c2
                                                        (c0
                                                          ((128:Nat))
                                                          (c1
                                                            ((2:Nat))))
                                                        (c4 c0_1))
                                                      ((2:Nat))))
                                                (AXr5284_1
                                                  ((2:Nat)))
                                                (@AXr5284_3
                                                  (fun (n:Nat) =>
                                                    let c0_1:Nat:=
                                                      c2 n ((4:Nat));
                                                    c2
                                                      (c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          (c2
                                                            (c0
                                                              ((1024:Nat))
                                                              (c3
                                                                (c2 c0_1
                                                                  ((1:Nat)))
                                                                ((4:Nat))))
                                                            ((1:Nat)))))
                                                      (c0 ((14:Nat))
                                                        c0_1))
                                                  c15
                                                  (@AXr5284_3
                                                    (fun (n:Nat) =>
                                                      c2 ((60:Nat))
                                                        (c0 ((6:Nat))
                                                          (c2
                                                            (c0
                                                              ((1024:Nat))
                                                              (c3
                                                                (c2
                                                                  (c2 n
                                                                    ((4:Nat)))
                                                                  ((1:Nat)))
                                                                ((4:Nat))))
                                                            ((1:Nat)))))
                                                    (fun (n:Nat) =>
                                                      c0 ((14:Nat))
                                                        (c2 n
                                                          ((4:Nat))))
                                                    (@AXr5284_3
                                                      (fun (x:Nat) =>
                                                        (60:Nat))
                                                      (fun (n:Nat) =>
                                                        c0 ((6:Nat))
                                                          (c2
                                                            (c0
                                                              ((1024:Nat))
                                                              (c3
                                                                (c2
                                                                  (c2 n
                                                                    ((4:Nat)))
                                                                  ((1:Nat)))
                                                                ((4:Nat))))
                                                            ((1:Nat))))
                                                      (AXr5284_1
                                                        ((60:Nat)))
                                                      (@AXr5284_4
                                                        (fun (x:Nat) =>
                                                          (6:Nat))
                                                        c19
                                                        (AXr5284_1
                                                          ((6:Nat)))
                                                        c21))
                                                    (@AXr5284_4
                                                      (fun (x:Nat) =>
                                                        (14:Nat))
                                                      c7
                                                      (AXr5284_1
                                                        ((14:Nat)))
                                                      c11))
                                                  c18))
                                              (AXr5284_1
                                                ((1:Nat))))
                                            c12))
                                        (AXr5284_1
                                          ((1:Nat))))
                                      c12)
                                    c22)
                                  (@c17 c19
                                    (AXr5284_1
                                      ((2:Nat)))
                                    c21))
                                (@AXr5284_4
                                  (fun (x:Nat) => (5:Nat)) c7
                                  (AXr5284_1
                                    ((5:Nat)))
                                  c11))
                              (AXr5284_1
                                ((13:Nat)))))
                          (AXr5284_1
                            ((224:Nat))))
                        c11)
                      c11)
                    c22)
                  c21)
                (AXr5284_1
                  ((2:Nat)))))
            c23)
          (@Lax109476Proofs.RamResourcePolynomial.pow c7 c11 ((2:Nat))))
        AXr5284_2)
      (AXr5284_1 ((5:Nat))))
    c23)

noncomputable abbrev _root_.AXr5286_0:= @Lax109476Proofs.RamResourcePolynomial.constant
noncomputable abbrev _root_.AXr5286_1:= @Lax109476Proofs.RamResourcePolynomial.add
theorem reconstruction_width:Lax109476Proofs.RamResourcePolynomial.HasPolynomial Lax109476Proofs.RamRationalReconstruction.wordWidth:=
let c0:Nat→ Nat→ Nat:=Nat.add;
let c1:Nat→ Nat→ Nat:=Nat.mul;
let c2:Nat→ Nat:=fun (n:Nat) =>
  c0
    (c1 ((2:Nat))
      (c0 n ((1:Nat))))
    ((1:Nat));
let c3:Nat→ Nat:=fun (n:Nat) => c0 n ((1:Nat));
let c4:
  Lax109476Proofs.RamResourcePolynomial.HasPolynomial fun (n:Nat) =>
    Nat.add n ((1:Nat)):=
  @AXr5286_1 (fun (n:Nat) => n)
    (fun (x:Nat) => (1:Nat))
    Lax109476Proofs.RamResourcePolynomial.identity
    (AXr5286_0 ((1:Nat)));
let c5:
  Lax109476Proofs.RamResourcePolynomial.HasPolynomial fun (n:Nat) =>
    Nat.add
      (c1 ((2:Nat))
        (c0 n ((1:Nat))))
      ((1:Nat)):=
  @AXr5286_1
    (fun (n:Nat) =>
      c1 ((2:Nat))
        (c0 n ((1:Nat))))
    (fun (x:Nat) => (1:Nat))
    (@Lax109476Proofs.RamResourcePolynomial.mul
      (fun (x:Nat) => (2:Nat)) c3
      (AXr5286_0 ((2:Nat))) c4)
    (AXr5286_0 ((1:Nat)));
@AXr5286_1
  (fun (n:Nat) =>
    let c0_1:Nat:=c0 n ((1:Nat));
    let c1_1:Nat:=
      c0 (c1 ((2:Nat)) c0_1)
        ((1:Nat));
    c0
      (c1 ((4:Nat))
        (c0 (c1 c0_1 (c0 c1_1 ((2:Nat))))
          ((2:Nat))))
      c1_1)
  (fun (x:Nat) => (2:Nat))
  (@AXr5286_1
    (fun (n:Nat) =>
      let c0_1:Nat:=c0 n ((1:Nat));
      c1 ((4:Nat))
        (c0
          (c1 c0_1
            (c0
              (c0 (c1 ((2:Nat)) c0_1)
                ((1:Nat)))
              ((2:Nat))))
          ((2:Nat))))
    c2
    (@Lax109476Proofs.RamResourcePolynomial.mul
      (fun (x:Nat) => (4:Nat))
      (fun (n:Nat) =>
        let c0_1:Nat:=c0 n ((1:Nat));
        c0
          (c1 c0_1
            (c0
              (c0 (c1 ((2:Nat)) c0_1)
                ((1:Nat)))
              ((2:Nat))))
          ((2:Nat)))
      (AXr5286_0 ((4:Nat)))
      (@AXr5286_1
        (fun (n:Nat) =>
          let c0_1:Nat:=c0 n ((1:Nat));
          c1 c0_1
            (c0
              (c0 (c1 ((2:Nat)) c0_1)
                ((1:Nat)))
              ((2:Nat))))
        (fun (x:Nat) => (2:Nat))
        (@Lax109476Proofs.RamResourcePolynomial.mul c3
          (fun (n:Nat) =>
            c0
              (c0
                (c1 ((2:Nat))
                  (c0 n ((1:Nat))))
                ((1:Nat)))
              ((2:Nat)))
          c4
          (@AXr5286_1 c2
            (fun (x:Nat) => (2:Nat)) c5
            (AXr5286_0 ((2:Nat)))))
        (AXr5286_0 ((2:Nat)))))
    c5)
  (AXr5286_0 ((2:Nat)))

noncomputable abbrev _root_.AXr5288_0:= @Lax109476Proofs.RamRationalReconstruction.wordWidth
noncomputable abbrev _root_.AXr5288_1:= @Lax109476Proofs.RamResourcePolynomial.HasPolynomial
noncomputable abbrev _root_.AXr5288_2:= @Lax109476Proofs.RamResourcePolynomial.constant
noncomputable abbrev _root_.AXr5288_3:= @Lax109476Proofs.RamResourcePolynomial.identity
noncomputable abbrev _root_.AXr5288_4:= @Lax109476Proofs.RamStoredFeasibility.wordWidth
noncomputable abbrev _root_.AXr5288_5:= @Lax109476Proofs.RamResourcePolynomial.add
noncomputable abbrev _root_.AXr5288_6:= @Lax109476Proofs.RamResourcePolynomial.mul
theorem recovery_width:AXr5288_1 fun (S:Nat) =>
  Lax109476Proofs.RamRecoverFeasibleSystem.wordWidth S S S:=
let c0:Nat→ Nat→ Nat:=Nat.add;
let c1:Nat→ Nat→ Nat:=Nat.mul;
let c2:Nat→ Nat:=c1 ((4:Nat));
let c3:Nat→ Nat:=c1 ((2:Nat));
let c4:Nat→ Nat:=fun (n:Nat) =>
  c0
    (c0
      (c2
        (c1 ((32:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (c0 n ((1:Nat)))
            ((2:Nat)))))
      (c3 n))
    ((2:Nat));
let c5:
  ∀ {g:Nat→ Nat},
    (AXr5288_1 fun (x:Nat) =>
        (4:Nat))→
      AXr5288_1 g→
        AXr5288_1 fun (n:Nat) =>
          Nat.mul ((4:Nat))
            (g n):=
  @AXr5288_6 fun (x:Nat) => (4:Nat);
let c6:Nat→ Nat:=fun (n:Nat) =>
  c1 ((32:Nat))
    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
      (c0 n ((1:Nat)))
      ((2:Nat)));
let c7:
  AXr5288_1 fun (n:Nat) =>
    Nat.mul ((32:Nat))
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        (c0 n ((1:Nat)))
        ((2:Nat))):=
  @AXr5288_6
    (fun (x:Nat) => (32:Nat))
    (fun (n:Nat) =>
      @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        (c0 n ((1:Nat)))
        ((2:Nat)))
    (AXr5288_2 ((32:Nat)))
    (@Lax109476Proofs.RamResourcePolynomial.pow
      (fun (n:Nat) => c0 n ((1:Nat)))
      (@AXr5288_5 (fun (n:Nat) => n)
        (fun (x:Nat) => (1:Nat))
        AXr5288_3
        (AXr5288_2 ((1:Nat))))
      ((2:Nat)));
let c8:
  ∀ {g:Nat→ Nat},
    (AXr5288_1 fun (x:Nat) =>
        (2:Nat))→
      AXr5288_1 g→
        AXr5288_1 fun (n:Nat) =>
          Nat.mul ((2:Nat))
            (g n):=
  @AXr5288_6 fun (x:Nat) => (2:Nat);
let c9:
  AXr5288_1 fun (n:Nat) =>
    Nat.add
      (c0
        (c2
          (c1 ((32:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (c0 n ((1:Nat)))
              ((2:Nat)))))
        (c3 n))
      ((2:Nat)):=
  @AXr5288_5
    (fun (n:Nat) =>
      c0
        (c2
          (c1 ((32:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (c0 n ((1:Nat)))
              ((2:Nat)))))
        (c3 n))
    (fun (x:Nat) => (2:Nat))
    (@AXr5288_5
      (fun (n:Nat) =>
        c2
          (c1 ((32:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (c0 n ((1:Nat)))
              ((2:Nat)))))
      (fun (n:Nat) => c3 n)
      (@c5 c6 (AXr5288_2 ((4:Nat)))
        c7)
      (@c8 (fun (n:Nat) => n)
        (AXr5288_2 ((2:Nat)))
        AXr5288_3))
    (AXr5288_2 ((2:Nat)));
let c10:Nat→ Nat:=fun (n:Nat) =>
  c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat));
let c11:Nat→ Nat:=fun (n:Nat) => c0 n n;
let c12:
  ∀ {g:Nat→ Nat},
    AXr5288_1 c11→
      AXr5288_1 g→
        AXr5288_1 fun (n:Nat) =>
          Nat.add (c11 n) (g n):=
  @AXr5288_5 c11;
let c13:Nat→ Nat:=fun (n:Nat) => c0 (c0 n n) (c0 n n);
let c14:
  AXr5288_1 fun (n:Nat) =>
    Nat.add n n:=
  @AXr5288_5 (fun (n:Nat) => n) (fun (n:Nat) => n)
    AXr5288_3 AXr5288_3;
let c15:
  AXr5288_1 fun (n:Nat) =>
    Nat.add (c11 n) (c11 n):=
  @c12 c11 c14 c14;
let c16:
  AXr5288_1 fun (n:Nat) =>
    Nat.add (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
      ((1:Nat)):=
  @AXr5288_5 (fun (n:Nat) => c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
    (fun (x:Nat) => (1:Nat)) (@c12 c13 c14 c15)
    (AXr5288_2 ((1:Nat)));
let c17:
  ∀ {g:Nat→ Nat},
    (AXr5288_1 fun (n:Nat) =>
        c1 (c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat)))
          (c0 n n))→
      AXr5288_1 g→
        AXr5288_1 fun (n:Nat) =>
          Nat.add
            (c1 (c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat)))
              (c0 n n))
            (g n):=
  @AXr5288_5 fun (n:Nat) =>
    c1 (c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat))) (c0 n n);
let c18:
  AXr5288_1 fun (n:Nat) =>
    Nat.mul (c10 n) (c11 n):=
  @AXr5288_6 c10 c11 c16 c14;
@AXr5288_5
  (fun (n:Nat) =>
    let c0_1:Nat:=
      c1 ((32:Nat))
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          (c0 n ((1:Nat)))
          ((2:Nat)));
    let c1_1:Nat:=c0 (c0 (c2 c0_1) (c3 n)) ((2:Nat));
    let c2_1:Nat:=c0 (c0 n n) (c0 n n);
    let c3_1:Nat:=c0 (c0 (c0 n n) c2_1) ((1:Nat));
    let c4:Nat→ Nat:=c0 (c1 c3_1 (c0 n n));
    c0
      (c0
        (c0
          (c0
            (c0
              (c0
                (c0
                  (c0
                    (c0
                      (c0
                        (c0
                          (c0
                            (c2
                              (c0 (c0 c1_1 ((1:Nat)))
                                ((2:Nat))))
                            (AXr5288_0 c1_1))
                          (AXr5288_4
                            (c0 (c0 (c0 c3_1 (c0 n n)) ((2:Nat)))
                              (c1 (c0 (c4 c3_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3 (c0 (c3 c1_1) ((3:Nat)))))))))
                        (c0 (c0 (c4 (c0 n n)) c2_1) ((4:Nat))))
                      c1_1)
                    ((4:Nat)))
                  (c0 (c0 c0_1 n) ((16:Nat))))
                (c1 (c0 n n) (c0 n n)))
              n)
            n)
          n)
        ((4:Nat)))
      n)
  (fun (x:Nat) => (8:Nat))
  (@AXr5288_5
    (fun (n:Nat) =>
      let c0_1:Nat:=
        c1 ((32:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (c0 n ((1:Nat)))
            ((2:Nat)));
      let c1_1:Nat:=c0 (c0 (c2 c0_1) (c3 n)) ((2:Nat));
      let c2_1:Nat:=c0 (c0 n n) (c0 n n);
      let c3_1:Nat:=c0 (c0 (c0 n n) c2_1) ((1:Nat));
      let c4:Nat→ Nat:=c0 (c1 c3_1 (c0 n n));
      c0
        (c0
          (c0
            (c0
              (c0
                (c0
                  (c0
                    (c0
                      (c0
                        (c0
                          (c0
                            (c2
                              (c0 (c0 c1_1 ((1:Nat)))
                                ((2:Nat))))
                            (AXr5288_0 c1_1))
                          (AXr5288_4
                            (c0 (c0 (c0 c3_1 (c0 n n)) ((2:Nat)))
                              (c1 (c0 (c4 c3_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3 (c0 (c3 c1_1) ((3:Nat)))))))))
                        (c0 (c0 (c4 (c0 n n)) c2_1) ((4:Nat))))
                      c1_1)
                    ((4:Nat)))
                  (c0 (c0 c0_1 n) ((16:Nat))))
                (c1 (c0 n n) (c0 n n)))
              n)
            n)
          n)
        ((4:Nat)))
    (fun (n:Nat) => n)
    (@AXr5288_5
      (fun (n:Nat) =>
        let c0_1:Nat:=
          c1 ((32:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (c0 n ((1:Nat)))
              ((2:Nat)));
        let c1_1:Nat:=c0 (c0 (c2 c0_1) (c3 n)) ((2:Nat));
        let c2_1:Nat:=c0 (c0 n n) (c0 n n);
        let c3_1:Nat:=c0 (c0 (c0 n n) c2_1) ((1:Nat));
        let c4:Nat→ Nat:=c0 (c1 c3_1 (c0 n n));
        c0
          (c0
            (c0
              (c0
                (c0
                  (c0
                    (c0
                      (c0
                        (c0
                          (c0
                            (c2
                              (c0 (c0 c1_1 ((1:Nat)))
                                ((2:Nat))))
                            (AXr5288_0 c1_1))
                          (AXr5288_4
                            (c0 (c0 (c0 c3_1 (c0 n n)) ((2:Nat)))
                              (c1 (c0 (c4 c3_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3 (c0 (c3 c1_1) ((3:Nat)))))))))
                        (c0 (c0 (c4 (c0 n n)) c2_1) ((4:Nat))))
                      c1_1)
                    ((4:Nat)))
                  (c0 (c0 c0_1 n) ((16:Nat))))
                (c1 (c0 n n) (c0 n n)))
              n)
            n)
          n)
      (fun (x:Nat) => (4:Nat))
      (@AXr5288_5
        (fun (n:Nat) =>
          let c0_1:Nat:=
            c1 ((32:Nat))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (c0 n ((1:Nat)))
                ((2:Nat)));
          let c1_1:Nat:=c0 (c0 (c2 c0_1) (c3 n)) ((2:Nat));
          let c2_1:Nat:=c0 (c0 n n) (c0 n n);
          let c3_1:Nat:=c0 (c0 (c0 n n) c2_1) ((1:Nat));
          let c4:Nat→ Nat:=c0 (c1 c3_1 (c0 n n));
          c0
            (c0
              (c0
                (c0
                  (c0
                    (c0
                      (c0
                        (c0
                          (c0
                            (c2
                              (c0 (c0 c1_1 ((1:Nat)))
                                ((2:Nat))))
                            (AXr5288_0 c1_1))
                          (AXr5288_4
                            (c0 (c0 (c0 c3_1 (c0 n n)) ((2:Nat)))
                              (c1 (c0 (c4 c3_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3 (c0 (c3 c1_1) ((3:Nat)))))))))
                        (c0 (c0 (c4 (c0 n n)) c2_1) ((4:Nat))))
                      c1_1)
                    ((4:Nat)))
                  (c0 (c0 c0_1 n) ((16:Nat))))
                (c1 (c0 n n) (c0 n n)))
              n)
            n)
        (fun (n:Nat) => n)
        (@AXr5288_5
          (fun (n:Nat) =>
            let c0_1:Nat:=
              c1 ((32:Nat))
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (c0 n ((1:Nat)))
                  ((2:Nat)));
            let c1_1:Nat:=c0 (c0 (c2 c0_1) (c3 n)) ((2:Nat));
            let c2_1:Nat:=c0 (c0 n n) (c0 n n);
            let c3_1:Nat:=c0 (c0 (c0 n n) c2_1) ((1:Nat));
            let c4:Nat→ Nat:=c0 (c1 c3_1 (c0 n n));
            c0
              (c0
                (c0
                  (c0
                    (c0
                      (c0
                        (c0
                          (c0
                            (c2
                              (c0 (c0 c1_1 ((1:Nat)))
                                ((2:Nat))))
                            (AXr5288_0 c1_1))
                          (AXr5288_4
                            (c0 (c0 (c0 c3_1 (c0 n n)) ((2:Nat)))
                              (c1 (c0 (c4 c3_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3 (c0 (c3 c1_1) ((3:Nat)))))))))
                        (c0 (c0 (c4 (c0 n n)) c2_1) ((4:Nat))))
                      c1_1)
                    ((4:Nat)))
                  (c0 (c0 c0_1 n) ((16:Nat))))
                (c1 (c0 n n) (c0 n n)))
              n)
          (fun (n:Nat) => n)
          (@AXr5288_5
            (fun (n:Nat) =>
              let c0_1:Nat:=
                c1 ((32:Nat))
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (c0 n ((1:Nat)))
                    ((2:Nat)));
              let c1_1:Nat:=c0 (c0 (c2 c0_1) (c3 n)) ((2:Nat));
              let c2_1:Nat:=c0 (c0 n n) (c0 n n);
              let c3_1:Nat:=c0 (c0 (c0 n n) c2_1) ((1:Nat));
              let c4:Nat→ Nat:=c0 (c1 c3_1 (c0 n n));
              c0
                (c0
                  (c0
                    (c0
                      (c0
                        (c0
                          (c0
                            (c2
                              (c0 (c0 c1_1 ((1:Nat)))
                                ((2:Nat))))
                            (AXr5288_0 c1_1))
                          (AXr5288_4
                            (c0 (c0 (c0 c3_1 (c0 n n)) ((2:Nat)))
                              (c1 (c0 (c4 c3_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3 (c0 (c3 c1_1) ((3:Nat)))))))))
                        (c0 (c0 (c4 (c0 n n)) c2_1) ((4:Nat))))
                      c1_1)
                    ((4:Nat)))
                  (c0 (c0 c0_1 n) ((16:Nat))))
                (c1 (c0 n n) (c0 n n)))
            (fun (n:Nat) => n)
            (@AXr5288_5
              (fun (n:Nat) =>
                let c0_1:Nat:=
                  c1 ((32:Nat))
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      (c0 n ((1:Nat)))
                      ((2:Nat)));
                let c1_1:Nat:=c0 (c0 (c2 c0_1) (c3 n)) ((2:Nat));
                let c2_1:Nat:=c0 (c0 n n) (c0 n n);
                let c3_1:Nat:=c0 (c0 (c0 n n) c2_1) ((1:Nat));
                let c4:Nat→ Nat:=c0 (c1 c3_1 (c0 n n));
                c0
                  (c0
                    (c0
                      (c0
                        (c0
                          (c0
                            (c2
                              (c0 (c0 c1_1 ((1:Nat)))
                                ((2:Nat))))
                            (AXr5288_0 c1_1))
                          (AXr5288_4
                            (c0 (c0 (c0 c3_1 (c0 n n)) ((2:Nat)))
                              (c1 (c0 (c4 c3_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3 (c0 (c3 c1_1) ((3:Nat)))))))))
                        (c0 (c0 (c4 (c0 n n)) c2_1) ((4:Nat))))
                      c1_1)
                    ((4:Nat)))
                  (c0 (c0 c0_1 n) ((16:Nat))))
              (fun (n:Nat) => c1 (c0 n n) (c0 n n))
              (@AXr5288_5
                (fun (n:Nat) =>
                  let c0_1:Nat:=
                    c0
                      (c0
                        (c2
                          (c1 ((32:Nat))
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                              (c0 n ((1:Nat)))
                              ((2:Nat)))))
                        (c3 n))
                      ((2:Nat));
                  let c1_1:Nat:=c0 (c0 n n) (c0 n n);
                  let c2_1:Nat:=c0 (c0 (c0 n n) c1_1) ((1:Nat));
                  let c3_1:Nat→ Nat:=c0 (c1 c2_1 (c0 n n));
                  c0
                    (c0
                      (c0
                        (c0
                          (c0
                            (c2
                              (c0 (c0 c0_1 ((1:Nat)))
                                ((2:Nat))))
                            (AXr5288_0 c0_1))
                          (AXr5288_4
                            (c0 (c0 (c0 c2_1 (c0 n n)) ((2:Nat)))
                              (c1 (c0 (c3_1 c2_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3 (c0 (c3 c0_1) ((3:Nat)))))))))
                        (c0 (c0 (c3_1 (c0 n n)) c1_1) ((4:Nat))))
                      c0_1)
                    ((4:Nat)))
                (fun (n:Nat) =>
                  c0
                    (c0
                      (c1 ((32:Nat))
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          (c0 n ((1:Nat)))
                          ((2:Nat))))
                      n)
                    ((16:Nat)))
                (@AXr5288_5
                  (fun (n:Nat) =>
                    let c0_1:Nat:=
                      c0
                        (c0
                          (c2
                            (c1 ((32:Nat))
                              (@HPow.hPow Nat Nat Nat
                                (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                (c0 n ((1:Nat)))
                                ((2:Nat)))))
                          (c3 n))
                        ((2:Nat));
                    let c1_1:Nat:=c0 (c0 n n) (c0 n n);
                    let c2_1:Nat:=c0 (c0 (c0 n n) c1_1) ((1:Nat));
                    let c3_1:Nat→ Nat:=c0 (c1 c2_1 (c0 n n));
                    c0
                      (c0
                        (c0
                          (c0
                            (c2
                              (c0 (c0 c0_1 ((1:Nat)))
                                ((2:Nat))))
                            (AXr5288_0 c0_1))
                          (AXr5288_4
                            (c0 (c0 (c0 c2_1 (c0 n n)) ((2:Nat)))
                              (c1 (c0 (c3_1 c2_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3 (c0 (c3 c0_1) ((3:Nat)))))))))
                        (c0 (c0 (c3_1 (c0 n n)) c1_1) ((4:Nat))))
                      c0_1)
                  (fun (x:Nat) => (4:Nat))
                  (@AXr5288_5
                    (fun (n:Nat) =>
                      let c0_1:Nat:=
                        c0
                          (c0
                            (c2
                              (c1 ((32:Nat))
                                (@HPow.hPow Nat Nat Nat
                                  (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                  (c0 n ((1:Nat)))
                                  ((2:Nat)))))
                            (c3 n))
                          ((2:Nat));
                      let c1_1:Nat:=c0 (c0 n n) (c0 n n);
                      let c2_1:Nat:=c0 (c0 (c0 n n) c1_1) ((1:Nat));
                      let c3_1:Nat→ Nat:=c0 (c1 c2_1 (c0 n n));
                      c0
                        (c0
                          (c0
                            (c2
                              (c0 (c0 c0_1 ((1:Nat)))
                                ((2:Nat))))
                            (AXr5288_0 c0_1))
                          (AXr5288_4
                            (c0 (c0 (c0 c2_1 (c0 n n)) ((2:Nat)))
                              (c1 (c0 (c3_1 c2_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3 (c0 (c3 c0_1) ((3:Nat)))))))))
                        (c0 (c0 (c3_1 (c0 n n)) c1_1) ((4:Nat))))
                    c4
                    (@AXr5288_5
                      (fun (n:Nat) =>
                        let c0_1:Nat:=
                          c0
                            (c0
                              (c2
                                (c1 ((32:Nat))
                                  (@HPow.hPow Nat Nat Nat
                                    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                    (c0 n ((1:Nat)))
                                    ((2:Nat)))))
                              (c3 n))
                            ((2:Nat));
                        let c1_1:Nat:=
                          c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                            ((1:Nat));
                        c0
                          (c0
                            (c2
                              (c0 (c0 c0_1 ((1:Nat)))
                                ((2:Nat))))
                            (AXr5288_0 c0_1))
                          (AXr5288_4
                            (c0 (c0 (c0 c1_1 (c0 n n)) ((2:Nat)))
                              (c1 (c0 (c0 (c1 c1_1 (c0 n n)) c1_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3 (c0 (c3 c0_1) ((3:Nat)))))))))
                      (fun (n:Nat) =>
                        let c0_1:Nat:=c0 (c0 n n) (c0 n n);
                        c0
                          (c0
                            (c0
                              (c1 (c0 (c0 (c0 n n) c0_1) ((1:Nat)))
                                (c0 n n))
                              (c0 n n))
                            c0_1)
                          ((4:Nat)))
                      (@AXr5288_5
                        (fun (n:Nat) =>
                          let c0_1:Nat:=
                            c0
                              (c0
                                (c2
                                  (c1 ((32:Nat))
                                    (@HPow.hPow Nat Nat Nat
                                      (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                      (c0 n ((1:Nat)))
                                      ((2:Nat)))))
                                (c3 n))
                              ((2:Nat));
                          c0
                            (c2
                              (c0 (c0 c0_1 ((1:Nat)))
                                ((2:Nat))))
                            (AXr5288_0 c0_1))
                        (fun (n:Nat) =>
                          let c0_1:Nat:=
                            c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                              ((1:Nat));
                          AXr5288_4
                            (c0 (c0 (c0 c0_1 (c0 n n)) ((2:Nat)))
                              (c1 (c0 (c0 (c1 c0_1 (c0 n n)) c0_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3
                                    (c0
                                      (c3
                                        (c0
                                          (c0
                                            (c2
                                              (c1 ((32:Nat))
                                                (@HPow.hPow Nat Nat Nat
                                                  (@instHPow Nat Nat
                                                    (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                  (c0 n ((1:Nat)))
                                                  ((2:Nat)))))
                                            (c3 n))
                                          ((2:Nat))))
                                      ((3:Nat))))))))
                        (@AXr5288_5
                          (fun (n:Nat) =>
                            c2
                              (c0
                                (c0
                                  (c0
                                    (c0
                                      (c2
                                        (c1 ((32:Nat))
                                          (@HPow.hPow Nat Nat Nat
                                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                            (c0 n ((1:Nat)))
                                            ((2:Nat)))))
                                      (c3 n))
                                    ((2:Nat)))
                                  ((1:Nat)))
                                ((2:Nat))))
                          (fun (n:Nat) =>
                            AXr5288_0
                              (c0
                                (c0
                                  (c2
                                    (c1 ((32:Nat))
                                      (@HPow.hPow Nat Nat Nat
                                        (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                        (c0 n ((1:Nat)))
                                        ((2:Nat)))))
                                  (c3 n))
                                ((2:Nat))))
                          (@c5
                            (fun (n:Nat) =>
                              c0
                                (c0
                                  (c0
                                    (c0
                                      (c2
                                        (c1 ((32:Nat))
                                          (@HPow.hPow Nat Nat Nat
                                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                            (c0 n ((1:Nat)))
                                            ((2:Nat)))))
                                      (c3 n))
                                    ((2:Nat)))
                                  ((1:Nat)))
                                ((2:Nat)))
                            (AXr5288_2
                              ((4:Nat)))
                            (@AXr5288_5
                              (fun (n:Nat) =>
                                c0
                                  (c0
                                    (c0
                                      (c2
                                        (c1 ((32:Nat))
                                          (@HPow.hPow Nat Nat Nat
                                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                            (c0 n ((1:Nat)))
                                            ((2:Nat)))))
                                      (c3 n))
                                    ((2:Nat)))
                                  ((1:Nat)))
                              (fun (x:Nat) => (2:Nat))
                              (@AXr5288_5 c4
                                (fun (x:Nat) => (1:Nat)) c9
                                (AXr5288_2
                                  ((1:Nat))))
                              (AXr5288_2
                                ((2:Nat)))))
                          (@Lax109476Proofs.RamResourcePolynomial.compose
                            AXr5288_0 c4
                            Lax109476Proofs.RamResourcePolynomial.reconstruction_width c9))
                        (@Lax109476Proofs.RamResourcePolynomial.compose AXr5288_4
                          (fun (n:Nat) =>
                            let c0_1:Nat:=
                              c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                                ((1:Nat));
                            c0 (c0 (c0 c0_1 (c0 n n)) ((2:Nat)))
                              (c1 (c0 (c0 (c1 c0_1 (c0 n n)) c0_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3
                                    (c0
                                      (c3
                                        (c0
                                          (c0
                                            (c2
                                              (c1 ((32:Nat))
                                                (@HPow.hPow Nat Nat Nat
                                                  (@instHPow Nat Nat
                                                    (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                  (c0 n ((1:Nat)))
                                                  ((2:Nat)))))
                                            (c3 n))
                                          ((2:Nat))))
                                      ((3:Nat)))))))
                          Lax109476Proofs.RamResourcePolynomial.stored_width
                          (@AXr5288_5
                            (fun (n:Nat) =>
                              c0
                                (c0
                                  (c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                                    ((1:Nat)))
                                  (c0 n n))
                                ((2:Nat)))
                            (fun (n:Nat) =>
                              let c0_1:Nat:=
                                c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                                  ((1:Nat));
                              c1 (c0 (c0 (c1 c0_1 (c0 n n)) c0_1) (c0 n n))
                                (c0 ((4:Nat))
                                  (c3
                                    (c0
                                      (c3
                                        (c0
                                          (c0
                                            (c2
                                              (c1 ((32:Nat))
                                                (@HPow.hPow Nat Nat Nat
                                                  (@instHPow Nat Nat
                                                    (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                  (c0 n ((1:Nat)))
                                                  ((2:Nat)))))
                                            (c3 n))
                                          ((2:Nat))))
                                      ((3:Nat))))))
                            (@AXr5288_5
                              (fun (n:Nat) =>
                                c0
                                  (c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                                    ((1:Nat)))
                                  (c0 n n))
                              (fun (x:Nat) => (2:Nat))
                              (@AXr5288_5 c10 c11 c16 c14)
                              (AXr5288_2
                                ((2:Nat))))
                            (@AXr5288_6
                              (fun (n:Nat) =>
                                let c0_1:Nat:=
                                  c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                                    ((1:Nat));
                                c0 (c0 (c1 c0_1 (c0 n n)) c0_1) (c0 n n))
                              (fun (n:Nat) =>
                                c0 ((4:Nat))
                                  (c3
                                    (c0
                                      (c3
                                        (c0
                                          (c0
                                            (c2
                                              (c1 ((32:Nat))
                                                (@HPow.hPow Nat Nat Nat
                                                  (@instHPow Nat Nat
                                                    (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                  (c0 n ((1:Nat)))
                                                  ((2:Nat)))))
                                            (c3 n))
                                          ((2:Nat))))
                                      ((3:Nat)))))
                              (@AXr5288_5
                                (fun (n:Nat) =>
                                  let c0_1:Nat:=
                                    c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                                      ((1:Nat));
                                  c0 (c1 c0_1 (c0 n n)) c0_1)
                                c11 (@c17 c10 c18 c16) c14)
                              (@AXr5288_5
                                (fun (x:Nat) => (4:Nat))
                                (fun (n:Nat) =>
                                  c3
                                    (c0
                                      (c3
                                        (c0
                                          (c0
                                            (c2
                                              (c1 ((32:Nat))
                                                (@HPow.hPow Nat Nat Nat
                                                  (@instHPow Nat Nat
                                                    (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                  (c0 n ((1:Nat)))
                                                  ((2:Nat)))))
                                            (c3 n))
                                          ((2:Nat))))
                                      ((3:Nat))))
                                (AXr5288_2
                                  ((4:Nat)))
                                (@c8
                                  (fun (n:Nat) =>
                                    c0
                                      (c3
                                        (c0
                                          (c0
                                            (c2
                                              (c1 ((32:Nat))
                                                (@HPow.hPow Nat Nat Nat
                                                  (@instHPow Nat Nat
                                                    (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                  (c0 n ((1:Nat)))
                                                  ((2:Nat)))))
                                            (c3 n))
                                          ((2:Nat))))
                                      ((3:Nat)))
                                  (AXr5288_2
                                    ((2:Nat)))
                                  (@AXr5288_5
                                    (fun (n:Nat) =>
                                      c3
                                        (c0
                                          (c0
                                            (c2
                                              (c1 ((32:Nat))
                                                (@HPow.hPow Nat Nat Nat
                                                  (@instHPow Nat Nat
                                                    (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                  (c0 n ((1:Nat)))
                                                  ((2:Nat)))))
                                            (c3 n))
                                          ((2:Nat))))
                                    (fun (x:Nat) => (3:Nat))
                                    (@c8 c4
                                      (AXr5288_2
                                        ((2:Nat)))
                                      c9)
                                    (AXr5288_2
                                      ((3:Nat))))))))))
                      (@AXr5288_5
                        (fun (n:Nat) =>
                          let c0_1:Nat:=c0 (c0 n n) (c0 n n);
                          c0
                            (c0
                              (c1 (c0 (c0 (c0 n n) c0_1) ((1:Nat)))
                                (c0 n n))
                              (c0 n n))
                            c0_1)
                        (fun (x:Nat) => (4:Nat))
                        (@AXr5288_5
                          (fun (n:Nat) =>
                            c0
                              (c1
                                (c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                                  ((1:Nat)))
                                (c0 n n))
                              (c0 n n))
                          c13 (@c17 c11 c18 c14) c15)
                        (AXr5288_2
                          ((4:Nat)))))
                    c9)
                  (AXr5288_2
                    ((4:Nat))))
                (@AXr5288_5
                  (fun (n:Nat) =>
                    c0
                      (c1 ((32:Nat))
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          (c0 n ((1:Nat)))
                          ((2:Nat))))
                      n)
                  (fun (x:Nat) => (16:Nat))
                  (@AXr5288_5 c6 (fun (n:Nat) => n) c7
                    AXr5288_3)
                  (AXr5288_2
                    ((16:Nat)))))
              (@AXr5288_6 c11 c11 c14 c14))
            AXr5288_3)
          AXr5288_3)
        AXr5288_3)
      (AXr5288_2 ((4:Nat))))
    AXr5288_3)
  (AXr5288_2 ((8:Nat)))

noncomputable abbrev _root_.AXr5290_0:= @Lax109476Proofs.RamResourcePolynomial.HasPolynomial
noncomputable abbrev _root_.AXr5290_1:= @Lax109476Proofs.RamResourcePolynomial.constant
noncomputable abbrev _root_.AXr5290_2:= @Lax109476Proofs.RamResourcePolynomial.identity
noncomputable abbrev _root_.AXr5290_3:= @Lax109476Proofs.RamResourcePolynomial.add
theorem decision_width:AXr5290_0 fun (S:Nat) =>
  Lax109476Proofs.RamStoredFeasibility.wordWidth (Lax109476Proofs.RamCertificateDecision.sizeBound S S S):=
let c0:Nat→ Nat→ Nat:=Nat.add;
let c1:Nat→ Nat→ Nat:=Nat.mul;
let c2:Nat→ Nat:=c1 ((2:Nat));
let c3:
  ∀ {g:Nat→ Nat},
    (AXr5290_0 fun (x:Nat) =>
        (2:Nat))→
      AXr5290_0 g→
        AXr5290_0 fun (n:Nat) =>
          Nat.mul ((2:Nat))
            (g n):=
  @Lax109476Proofs.RamResourcePolynomial.mul fun (x:Nat) => (2:Nat);
@Lax109476Proofs.RamResourcePolynomial.compose Lax109476Proofs.RamStoredFeasibility.wordWidth
  (fun (n:Nat) => Lax109476Proofs.RamCertificateDecision.sizeBound n n n)
  Lax109476Proofs.RamResourcePolynomial.stored_width
  (@id
    (AXr5290_0 fun (n:Nat) =>
      Lax109476Proofs.RamCertificateDecision.sizeBound n n n)
    (@AXr5290_3
      (fun (n:Nat) => c0 (c0 n n) ((2:Nat)))
      (fun (n:Nat) =>
        c1 (c0 (c0 (c1 n n) n) n)
          (c0 ((4:Nat))
            (c2 (c0 (c2 n) ((1:Nat))))))
      (@AXr5290_3 (fun (n:Nat) => c0 n n)
        (fun (x:Nat) => (2:Nat))
        (@AXr5290_3 (fun (n:Nat) => n) (fun (n:Nat) => n)
          AXr5290_2 AXr5290_2)
        (AXr5290_1 ((2:Nat))))
      (@Lax109476Proofs.RamResourcePolynomial.mul (fun (n:Nat) => c0 (c0 (c1 n n) n) n)
        (fun (n:Nat) =>
          c0 ((4:Nat))
            (c2 (c0 (c2 n) ((1:Nat)))))
        (@AXr5290_3 (fun (n:Nat) => c0 (c1 n n) n) (fun (n:Nat) => n)
          (@AXr5290_3 (fun (n:Nat) => c1 n n) (fun (n:Nat) => n)
            (@Lax109476Proofs.RamResourcePolynomial.mul (fun (n:Nat) => n) (fun (n:Nat) => n)
              AXr5290_2 AXr5290_2)
            AXr5290_2)
          AXr5290_2)
        (@AXr5290_3
          (fun (x:Nat) => (4:Nat))
          (fun (n:Nat) => c2 (c0 (c2 n) ((1:Nat))))
          (AXr5290_1 ((4:Nat)))
          (@c3 (fun (n:Nat) => c0 (c2 n) ((1:Nat)))
            (AXr5290_1 ((2:Nat)))
            (@AXr5290_3 (fun (n:Nat) => c2 n)
              (fun (x:Nat) => (1:Nat))
              (@c3 (fun (n:Nat) => n)
                (AXr5290_1
                  ((2:Nat)))
                AXr5290_2)
              (AXr5290_1
                ((1:Nat)))))))))

end Lax109476Proofs.RamResourcePolynomial

end

section

namespace Lax109476Proofs.RamSolverBranchBounds

theorem recovery_width {r s S w:ℕ} (hr:r≤ S) (hs:s≤ S) (hw:wordWidth S≤ w):
    RamRecoverFeasibleSystem.wordWidth r s S≤ w:=
  (RamRecoveryResourceMonotonicity.recovery_width hr hs le_rfl).trans (by unfold wordWidth at hw; omega)

theorem decision_width {r s S w:ℕ} (hr:r≤ S) (hs:s≤ S) (hw:wordWidth S≤ w):
    RamStoredFeasibility.wordWidth (RamCertificateDecision.sizeBound r s S)≤ w:=by
  have hsize:RamCertificateDecision.sizeBound r s S≤ RamCertificateDecision.sizeBound S S S:=by
    unfold RamCertificateDecision.sizeBound
    gcongr
  exact (RamStoredFeasibilityBounds.wordWidth_monotone hsize).trans (by unfold wordWidth at hw; omega)

theorem width_polynomial:RamResourcePolynomial.HasPolynomial wordWidth:=by
  unfold wordWidth
  apply RamResourcePolynomial.add RamResourcePolynomial.recovery_width RamResourcePolynomial.decision_width

end Lax109476Proofs.RamSolverBranchBounds

end

section

namespace Lax109476Proofs.RamUniformSolverBounds

open RamResourcePolynomial

theorem canonical_polynomial:HasPolynomial canonicalSize:=decoded_size
theorem parameter_polynomial:HasPolynomial parameter:=
  compose (f:=RamCertificateSetup.parameter) (g:=canonicalSize)
    RamResourcePolynomial.parameter canonical_polynomial

theorem front_width_polynomial:Lax109476Proofs.RamResourcePolynomial.HasPolynomial Lax109476Proofs.RamFrontEndTotal.wordWidth:=
@Lax109476Proofs.RamResourcePolynomial.compose Lax109476Proofs.RamDecoder.wordWidth
  Lax109476Proofs.RamUniformSolverBounds.canonicalSize
  (@id (Lax109476Proofs.RamResourcePolynomial.HasPolynomial Lax109476Proofs.RamDecoder.wordWidth)
    (@Lax109476Proofs.RamResourcePolynomial.mul
      (fun (x:Nat) => (4:Nat))
      (fun (n:Nat) =>
        Nat.add n ((2:Nat)))
      (Lax109476Proofs.RamResourcePolynomial.constant ((4:Nat)))
      (@Lax109476Proofs.RamResourcePolynomial.add (fun (n:Nat) => n)
        (fun (x:Nat) => (2:Nat))
        Lax109476Proofs.RamResourcePolynomial.identity
        (Lax109476Proofs.RamResourcePolynomial.constant ((2:Nat))))))
  Lax109476Proofs.RamUniformSolverBounds.canonical_polynomial

theorem width_polynomial:HasPolynomial wordWidth:=by
  unfold wordWidth
  apply add
  · apply add
    · exact add front_width_polynomial (compose RamSolverBranchBounds.width_polynomial parameter_polynomial)
    · exact compose (f:=fun S => 32 * (S + 1) ^ 2) (g:=parameter)
        (mul (constant 32) (pow (add identity (constant 1)) 2)) parameter_polynomial
  · exact constant 32

end Lax109476Proofs.RamUniformSolverBounds

end

theorem solution:Lax109476Proofs.RamResourcePolynomial.HasPolynomial Lax109476Proofs.RamUniformSolverBounds.wordWidth:= @Lax109476Proofs.RamUniformSolverBounds.width_polynomial
