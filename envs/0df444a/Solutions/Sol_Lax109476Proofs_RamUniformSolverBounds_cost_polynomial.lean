-- Prove2me | solution 1 for Lax109476Proofs.RamUniformSolverBounds.cost_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:39:40.498399+00:00
-- url     : https://prove2.me/submissions/0f5c06e0-6b1e-481c-a3b9-79539920069f

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

namespace Lax109476Proofs.RamRecoveryThreshold

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRationalScalars RamEllipsoidStep RationalArithmeticBounds

def sizeBound (m n M:ℕ):ℕ:=
  ((m + (n + n)) + 1) + n + 2 +
    ((((m + (n + n)) + 1) * n) + ((m + (n + n)) + 1) + n) * (4 + 2 * M.size)

def instructionBound (m n M:ℕ):ℕ:=
  142 * (((m + (n + n)) + 1) * n) + 138 * ((m + (n + n)) + 1) + 33 * n + 106 +
    RamStoredFeasibility.instructionBound (sizeBound m n M)

end Lax109476Proofs.RamRecoveryThreshold

end

section

namespace Lax109476Proofs.RamRecoveryResourceMonotonicity

attribute [gcongr] RamStoredFeasibilityBounds.wordWidth_monotone
attribute [gcongr] RamStoredFeasibilityBounds.instructionBound_monotone

@[gcongr] theorem reconstruction_cost {S T:ℕ} (h:S≤ T):
    RamRationalReconstruction.instructionBound S≤ RamRationalReconstruction.instructionBound T:=by
  unfold RamRationalReconstruction.instructionBound RamRationalReconstruction.depthBound
    RamConvergentBounds.instructionBound RamConvergentBounds.exponent
  gcongr

@[gcongr] theorem point_query_size {m n S r s T:ℕ} (hm:m≤ r) (hn:n≤ s) (hS:S≤ T):
    RamPointRecoveryBounds.querySize m n S≤ RamPointRecoveryBounds.querySize r s T:=by
  unfold RamPointRecoveryBounds.querySize
  gcongr

@[gcongr] theorem point_query_cost {m n S r s T:ℕ} (hm:m≤ r) (hn:n≤ s) (hS:S≤ T):
    RamPointRecoveryBounds.queryCost m n S≤ RamPointRecoveryBounds.queryCost r s T:=by
  unfold RamPointRecoveryBounds.queryCost
  gcongr

@[gcongr] theorem point_cost {m n S C r s T D:ℕ}
    (hm:m≤ r) (hn:n≤ s) (hS:S≤ T) (hC:C≤ D):
    RamPointRecoveryBounds.instructionBound m n S C≤ RamPointRecoveryBounds.instructionBound r s T D:=by
  unfold RamPointRecoveryBounds.instructionBound
  gcongr

@[gcongr] theorem cap_bits {S T:ℕ} (h:S≤ T):
    RamRecoverFeasibleSystem.capBits S≤ RamRecoverFeasibleSystem.capBits T:=by
  unfold RamRecoverFeasibleSystem.capBits
  gcongr

@[gcongr] theorem recovery_bits {S T:ℕ} (h:S≤ T):
    RamRecoverFeasibleSystem.recoveryBits S≤ RamRecoverFeasibleSystem.recoveryBits T:=by
  unfold RamRecoverFeasibleSystem.recoveryBits
  gcongr

@[gcongr] theorem recovery_cost {m n S r s T:ℕ} (hm:m≤ r) (hn:n≤ s) (hS:S≤ T):
    RamRecoverFeasibleSystem.instructionBound m n S≤ RamRecoverFeasibleSystem.instructionBound r s T:=by
  unfold RamRecoverFeasibleSystem.instructionBound
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

set_option maxRecDepth 30000 in
noncomputable abbrev _root_.AXr5285_0:= @Lax109476Proofs.RamResourcePolynomial.HasPolynomial
noncomputable abbrev _root_.AXr5285_1:= @Lax109476Proofs.RamResourcePolynomial.constant
noncomputable abbrev _root_.AXr5285_2:= @Lax109476Proofs.RamResourcePolynomial.identity
noncomputable abbrev _root_.AXr5285_3:= @Lax109476Proofs.RamResourcePolynomial.add
noncomputable abbrev _root_.AXr5285_4:= @Lax109476Proofs.RamResourcePolynomial.mul
theorem stored_cost:AXr5285_0 Lax109476Proofs.RamStoredFeasibility.instructionBound:=
let c0:Nat→ Nat→ Nat:=Nat.add;
let c1:Nat→ Nat→ Nat:=Nat.mul;
let c2:Nat→ Nat:=c1 ((72:Nat));
let c3:Nat→ Nat:=c1 ((71:Nat));
let c4:Nat→ Nat→ Nat:=
  @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)));
let c5:Nat→ Nat:=c1 ((2:Nat));
let c6:Nat→ Nat:=c1 ((144:Nat));
let c7:Nat→ Nat:=fun (n:Nat) => c0 n ((1:Nat));
let c8:
  AXr5285_0 fun (n:Nat) =>
    Nat.add n ((1:Nat)):=
  @AXr5285_3 (fun (n:Nat) => n)
    (fun (x:Nat) => (1:Nat))
    AXr5285_2
    (AXr5285_1 ((1:Nat)));
let c9:
  ∀ {g:Nat→ Nat},
    (AXr5285_0 fun (x:Nat) =>
        (72:Nat))→
      AXr5285_0 g→
        AXr5285_0 fun (n:Nat) =>
          Nat.mul ((72:Nat))
            (g n):=
  @AXr5285_4 fun (x:Nat) => (72:Nat);
let c10:
  ∀ {g:Nat→ Nat},
    (AXr5285_0 fun (x:Nat) =>
        (71:Nat))→
      AXr5285_0 g→
        AXr5285_0 fun (n:Nat) =>
          Nat.mul ((71:Nat))
            (g n):=
  @AXr5285_4 fun (x:Nat) => (71:Nat);
let c11:Nat→ Nat:=fun (n:Nat) =>
  c4 (c0 n ((4:Nat)))
    ((2:Nat));
let c12:Nat→ Nat:=fun (n:Nat) => c0 n ((4:Nat));
let c13:
  AXr5285_0 fun (n:Nat) =>
    Nat.add n ((4:Nat)):=
  @AXr5285_3 (fun (n:Nat) => n)
    (fun (x:Nat) => (4:Nat))
    AXr5285_2
    (AXr5285_1 ((4:Nat)));
let c14:
  AXr5285_0 fun (n:Nat) =>
    @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) (c12 n)
      ((2:Nat)):=
  @Lax109476Proofs.RamResourcePolynomial.pow c12 c13 ((2:Nat));
let c15:Nat→ Nat:=fun (n:Nat) =>
  c4
    (c0 (c0 n ((4:Nat)))
      ((1:Nat)))
    ((2:Nat));
let c16:Nat→ Nat:=fun (n:Nat) =>
  c0 (c0 n ((4:Nat)))
    ((1:Nat));
let c17:
  AXr5285_0 fun (n:Nat) =>
    Nat.add (c12 n)
      ((1:Nat)):=
  @AXr5285_3 c12
    (fun (x:Nat) => (1:Nat)) c13
    (AXr5285_1 ((1:Nat)));
let c18:
  ∀ (k:Nat),
    AXr5285_0 fun (n:Nat) =>
      @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) (c16 n) k:=
  @Lax109476Proofs.RamResourcePolynomial.pow c16 c17;
let c19:
  AXr5285_0 fun (n:Nat) =>
    @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) (c16 n)
      ((2:Nat)):=
  c18 ((2:Nat));
let c20:Nat→ Nat:=fun (n:Nat) =>
  let c0:Nat:=c0 n ((4:Nat));
  c1 c0 c0;
let c21:
  ∀ {g:Nat→ Nat},
    (AXr5285_0 fun (n:Nat) =>
        let c0_1:Nat:=c0 n ((4:Nat));
        c2
          (c0
            (c0
              (c0
                (c1 ((128:Nat))
                  (c4 (c0 c0_1 ((1:Nat)))
                    ((2:Nat))))
                (c5 c0_1))
              ((2:Nat)))
            ((1:Nat))))→
      AXr5285_0 g→
        AXr5285_0 fun (n:Nat) =>
          Nat.add
            (let c0_1:Nat:=c0 n ((4:Nat));
            c2
              (c0
                (c0
                  (c0
                    (c1 ((128:Nat))
                      (c4 (c0 c0_1 ((1:Nat)))
                        ((2:Nat))))
                    (c5 c0_1))
                  ((2:Nat)))
                ((1:Nat))))
            (g n):=
  @AXr5285_3 fun (n:Nat) =>
    let c0_1:Nat:=c0 n ((4:Nat));
    c2
      (c0
        (c0
          (c0
            (c1 ((128:Nat))
              (c4 (c0 c0_1 ((1:Nat)))
                ((2:Nat))))
            (c5 c0_1))
          ((2:Nat)))
        ((1:Nat)));
let c22:Nat→ Nat:=fun (n:Nat) =>
  let c0_1:Nat:=c0 n ((4:Nat));
  c0
    (c0
      (c1 ((128:Nat))
        (c4 (c0 c0_1 ((1:Nat)))
          ((2:Nat))))
      (c5 c0_1))
    ((2:Nat));
let c23:
  ∀ {g:Nat→ Nat},
    (AXr5285_0 fun (x:Nat) =>
        (2:Nat))→
      AXr5285_0 g→
        AXr5285_0 fun (n:Nat) =>
          Nat.mul ((2:Nat))
            (g n):=
  @AXr5285_4 fun (x:Nat) => (2:Nat);
let c24:
  AXr5285_0 fun (n:Nat) =>
    Nat.add
      (let c0_1:Nat:=c0 n ((4:Nat));
      c0
        (c1 ((128:Nat))
          (c4 (c0 c0_1 ((1:Nat)))
            ((2:Nat))))
        (c5 c0_1))
      ((2:Nat)):=
  @AXr5285_3
    (fun (n:Nat) =>
      let c0_1:Nat:=c0 n ((4:Nat));
      c0
        (c1 ((128:Nat))
          (c4 (c0 c0_1 ((1:Nat)))
            ((2:Nat))))
        (c5 c0_1))
    (fun (x:Nat) => (2:Nat))
    (@AXr5285_3
      (fun (n:Nat) =>
        c1 ((128:Nat))
          (c4
            (c0 (c0 n ((4:Nat)))
              ((1:Nat)))
            ((2:Nat))))
      (fun (n:Nat) => c5 (c0 n ((4:Nat))))
      (@AXr5285_4
        (fun (x:Nat) => (128:Nat)) c15
        (AXr5285_1 ((128:Nat)))
        c19)
      (@c23 c12
        (AXr5285_1 ((2:Nat))) c13))
    (AXr5285_1 ((2:Nat)));
let c25:
  AXr5285_0 fun (n:Nat) =>
    Nat.mul ((72:Nat))
      (let c0_1:Nat:=c0 n ((4:Nat));
      c0
        (c0
          (c0
            (c1 ((128:Nat))
              (c4 (c0 c0_1 ((1:Nat)))
                ((2:Nat))))
            (c5 c0_1))
          ((2:Nat)))
        ((1:Nat))):=
  @c9
    (fun (n:Nat) =>
      let c0_1:Nat:=c0 n ((4:Nat));
      c0
        (c0
          (c0
            (c1 ((128:Nat))
              (c4 (c0 c0_1 ((1:Nat)))
                ((2:Nat))))
            (c5 c0_1))
          ((2:Nat)))
        ((1:Nat)))
    (AXr5285_1 ((72:Nat)))
    (@AXr5285_3 c22
      (fun (x:Nat) => (1:Nat)) c24
      (AXr5285_1 ((1:Nat))));
let c26:
  AXr5285_0 fun (n:Nat) =>
    Nat.mul (c12 n) (c12 n):=
  @AXr5285_4 c12 c12 c13 c13;
let c27:Nat→ Nat:=fun (n:Nat) =>
  c0
    (c1 ((1024:Nat))
      (c4
        (c0 (c0 n ((4:Nat)))
          ((1:Nat)))
        ((4:Nat))))
    ((1:Nat));
let c28:
  ∀ {g:Nat→ Nat},
    (AXr5285_0 fun (n:Nat) =>
        let c0_1:Nat:=c0 n ((4:Nat));
        let c1_1:Nat:=c0 c0_1 ((1:Nat));
        let c2:Nat→ Nat:=c4 c1_1;
        c0
          (c6
            (c0
              (c1 c1_1
                (c0
                  (c5
                    (c0
                      (c0
                        (c0
                          (c0 ((60:Nat))
                            (c1 ((6:Nat))
                              (c0
                                (c1 ((1024:Nat))
                                  (c2 ((4:Nat))))
                                ((1:Nat)))))
                          (c1 ((14:Nat)) c0_1))
                        (c0
                          (c0
                            (c1 ((128:Nat))
                              (c2 ((2:Nat))))
                            (c5 c0_1))
                          ((2:Nat))))
                      ((1:Nat))))
                  ((3:Nat))))
              ((1:Nat))))
          ((220:Nat)))→
      AXr5285_0 g→
        AXr5285_0 fun (n:Nat) =>
          Nat.mul
            (let c0_1:Nat:=c0 n ((4:Nat));
            let c1_1:Nat:=c0 c0_1 ((1:Nat));
            let c2:Nat→ Nat:=c4 c1_1;
            c0
              (c6
                (c0
                  (c1 c1_1
                    (c0
                      (c5
                        (c0
                          (c0
                            (c0
                              (c0 ((60:Nat))
                                (c1 ((6:Nat))
                                  (c0
                                    (c1 ((1024:Nat))
                                      (c2 ((4:Nat))))
                                    ((1:Nat)))))
                              (c1 ((14:Nat)) c0_1))
                            (c0
                              (c0
                                (c1 ((128:Nat))
                                  (c2 ((2:Nat))))
                                (c5 c0_1))
                              ((2:Nat))))
                          ((1:Nat))))
                      ((3:Nat))))
                  ((1:Nat))))
              ((220:Nat)))
            (g n):=
  @AXr5285_4 fun (n:Nat) =>
    let c0_1:Nat:=c0 n ((4:Nat));
    let c1_1:Nat:=c0 c0_1 ((1:Nat));
    let c2:Nat→ Nat:=c4 c1_1;
    c0
      (c6
        (c0
          (c1 c1_1
            (c0
              (c5
                (c0
                  (c0
                    (c0
                      (c0 ((60:Nat))
                        (c1 ((6:Nat))
                          (c0
                            (c1 ((1024:Nat))
                              (c2 ((4:Nat))))
                            ((1:Nat)))))
                      (c1 ((14:Nat)) c0_1))
                    (c0
                      (c0
                        (c1 ((128:Nat))
                          (c2 ((2:Nat))))
                        (c5 c0_1))
                      ((2:Nat))))
                  ((1:Nat))))
              ((3:Nat))))
          ((1:Nat))))
      ((220:Nat));
let c29:
  ∀ {g:Nat→ Nat},
    (AXr5285_0 fun (x:Nat) =>
        (144:Nat))→
      AXr5285_0 g→
        AXr5285_0 fun (n:Nat) =>
          Nat.mul
            ((144:Nat)) (g n):=
  @AXr5285_4 fun (x:Nat) =>
    (144:Nat);
let c30:Nat→ Nat:=fun (n:Nat) =>
  let c0_1:Nat:=c0 n ((4:Nat));
  let c1_1:Nat:=c0 c0_1 ((1:Nat));
  let c2:Nat→ Nat:=c4 c1_1;
  c0
    (c1 c1_1
      (c0
        (c5
          (c0
            (c0
              (c0
                (c0 ((60:Nat))
                  (c1 ((6:Nat))
                    (c0
                      (c1 ((1024:Nat))
                        (c2 ((4:Nat))))
                      ((1:Nat)))))
                (c1 ((14:Nat)) c0_1))
              (c0
                (c0
                  (c1 ((128:Nat))
                    (c2 ((2:Nat))))
                  (c5 c0_1))
                ((2:Nat))))
            ((1:Nat))))
        ((3:Nat))))
    ((1:Nat));
let c31:
  ∀ {g:Nat→ Nat},
    AXr5285_0 c16→
      AXr5285_0 g→
        AXr5285_0 fun (n:Nat) =>
          Nat.mul (c16 n) (g n):=
  @AXr5285_4 c16;
let c32:Nat→ Nat:=fun (n:Nat) =>
  let c0_1:Nat:=c0 n ((4:Nat));
  let c1_1:Nat→ Nat:=c4 (c0 c0_1 ((1:Nat)));
  c0
    (c0
      (c0 ((60:Nat))
        (c1 ((6:Nat))
          (c0
            (c1 ((1024:Nat))
              (c1_1 ((4:Nat))))
            ((1:Nat)))))
      (c1 ((14:Nat)) c0_1))
    (c0
      (c0
        (c1 ((128:Nat))
          (c1_1 ((2:Nat))))
        (c5 c0_1))
      ((2:Nat)));
let c33:
  AXr5285_0 fun (n:Nat) =>
    Nat.add
      (c1 ((1024:Nat))
        (c4
          (c0 (c0 n ((4:Nat)))
            ((1:Nat)))
          ((4:Nat))))
      ((1:Nat)):=
  @AXr5285_3
    (fun (n:Nat) =>
      c1 ((1024:Nat))
        (c4
          (c0 (c0 n ((4:Nat)))
            ((1:Nat)))
          ((4:Nat))))
    (fun (x:Nat) => (1:Nat))
    (@AXr5285_4
      (fun (x:Nat) => (1024:Nat))
      (fun (n:Nat) =>
        c4
          (c0 (c0 n ((4:Nat)))
            ((1:Nat)))
          ((4:Nat)))
      (AXr5285_1 ((1024:Nat)))
      (c18 ((4:Nat))))
    (AXr5285_1 ((1:Nat)));
let c34:
  AXr5285_0 fun (n:Nat) =>
    Nat.add
      (let c0_1:Nat:=c0 n ((4:Nat));
      c0
        (c0 ((60:Nat))
          (c1 ((6:Nat))
            (c0
              (c1 ((1024:Nat))
                (c4 (c0 c0_1 ((1:Nat)))
                  ((4:Nat))))
              ((1:Nat)))))
        (c1 ((14:Nat)) c0_1))
      (c22 n):=
  @AXr5285_3
    (fun (n:Nat) =>
      let c0_1:Nat:=c0 n ((4:Nat));
      c0
        (c0 ((60:Nat))
          (c1 ((6:Nat))
            (c0
              (c1 ((1024:Nat))
                (c4 (c0 c0_1 ((1:Nat)))
                  ((4:Nat))))
              ((1:Nat)))))
        (c1 ((14:Nat)) c0_1))
    c22
    (@AXr5285_3
      (fun (n:Nat) =>
        c0 ((60:Nat))
          (c1 ((6:Nat))
            (c0
              (c1 ((1024:Nat))
                (c4
                  (c0 (c0 n ((4:Nat)))
                    ((1:Nat)))
                  ((4:Nat))))
              ((1:Nat)))))
      (fun (n:Nat) =>
        c1 ((14:Nat))
          (c0 n ((4:Nat))))
      (@AXr5285_3
        (fun (x:Nat) => (60:Nat))
        (fun (n:Nat) =>
          c1 ((6:Nat))
            (c0
              (c1 ((1024:Nat))
                (c4
                  (c0 (c0 n ((4:Nat)))
                    ((1:Nat)))
                  ((4:Nat))))
              ((1:Nat))))
        (AXr5285_1 ((60:Nat)))
        (@AXr5285_4
          (fun (x:Nat) => (6:Nat)) c27
          (AXr5285_1 ((6:Nat)))
          c33))
      (@AXr5285_4
        (fun (x:Nat) => (14:Nat)) c12
        (AXr5285_1 ((14:Nat)))
        c13))
    c24;
let c35:
  AXr5285_0 fun (n:Nat) =>
    Nat.add
      (let c0_1:Nat:=c0 n ((4:Nat));
      let c1_1:Nat:=c0 c0_1 ((1:Nat));
      let c2:Nat→ Nat:=c4 c1_1;
      c1 c1_1
        (c0
          (c5
            (c0
              (c0
                (c0
                  (c0 ((60:Nat))
                    (c1 ((6:Nat))
                      (c0
                        (c1 ((1024:Nat))
                          (c2 ((4:Nat))))
                        ((1:Nat)))))
                  (c1 ((14:Nat)) c0_1))
                (c0
                  (c0
                    (c1 ((128:Nat))
                      (c2 ((2:Nat))))
                    (c5 c0_1))
                  ((2:Nat))))
              ((1:Nat))))
          ((3:Nat))))
      ((1:Nat)):=
  @AXr5285_3
    (fun (n:Nat) =>
      let c0_1:Nat:=c0 n ((4:Nat));
      let c1_1:Nat:=c0 c0_1 ((1:Nat));
      let c2:Nat→ Nat:=c4 c1_1;
      c1 c1_1
        (c0
          (c5
            (c0
              (c0
                (c0
                  (c0 ((60:Nat))
                    (c1 ((6:Nat))
                      (c0
                        (c1 ((1024:Nat))
                          (c2 ((4:Nat))))
                        ((1:Nat)))))
                  (c1 ((14:Nat)) c0_1))
                (c0
                  (c0
                    (c1 ((128:Nat))
                      (c2 ((2:Nat))))
                    (c5 c0_1))
                  ((2:Nat))))
              ((1:Nat))))
          ((3:Nat))))
    (fun (x:Nat) => (1:Nat))
    (@c31
      (fun (n:Nat) =>
        let c0_1:Nat:=c0 n ((4:Nat));
        let c1_1:Nat→ Nat:=c4 (c0 c0_1 ((1:Nat)));
        c0
          (c5
            (c0
              (c0
                (c0
                  (c0 ((60:Nat))
                    (c1 ((6:Nat))
                      (c0
                        (c1 ((1024:Nat))
                          (c1_1 ((4:Nat))))
                        ((1:Nat)))))
                  (c1 ((14:Nat)) c0_1))
                (c0
                  (c0
                    (c1 ((128:Nat))
                      (c1_1 ((2:Nat))))
                    (c5 c0_1))
                  ((2:Nat))))
              ((1:Nat))))
          ((3:Nat)))
      c17
      (@AXr5285_3
        (fun (n:Nat) =>
          let c0_1:Nat:=c0 n ((4:Nat));
          let c1_1:Nat→ Nat:=c4 (c0 c0_1 ((1:Nat)));
          c5
            (c0
              (c0
                (c0
                  (c0 ((60:Nat))
                    (c1 ((6:Nat))
                      (c0
                        (c1 ((1024:Nat))
                          (c1_1 ((4:Nat))))
                        ((1:Nat)))))
                  (c1 ((14:Nat)) c0_1))
                (c0
                  (c0
                    (c1 ((128:Nat))
                      (c1_1 ((2:Nat))))
                    (c5 c0_1))
                  ((2:Nat))))
              ((1:Nat))))
        (fun (x:Nat) => (3:Nat))
        (@c23
          (fun (n:Nat) =>
            let c0_1:Nat:=c0 n ((4:Nat));
            let c1_1:Nat→ Nat:=c4 (c0 c0_1 ((1:Nat)));
            c0
              (c0
                (c0
                  (c0 ((60:Nat))
                    (c1 ((6:Nat))
                      (c0
                        (c1 ((1024:Nat))
                          (c1_1 ((4:Nat))))
                        ((1:Nat)))))
                  (c1 ((14:Nat)) c0_1))
                (c0
                  (c0
                    (c1 ((128:Nat))
                      (c1_1 ((2:Nat))))
                    (c5 c0_1))
                  ((2:Nat))))
              ((1:Nat)))
          (AXr5285_1 ((2:Nat)))
          (@AXr5285_3 c32
            (fun (x:Nat) => (1:Nat)) c34
            (AXr5285_1 ((1:Nat)))))
        (AXr5285_1 ((3:Nat)))))
    (AXr5285_1 ((1:Nat)));
let c36:
  AXr5285_0 fun (n:Nat) =>
    Nat.add
      (let c0_1:Nat:=c0 n ((4:Nat));
      let c1_1:Nat:=c0 c0_1 ((1:Nat));
      let c2:Nat→ Nat:=c4 c1_1;
      c6
        (c0
          (c1 c1_1
            (c0
              (c5
                (c0
                  (c0
                    (c0
                      (c0 ((60:Nat))
                        (c1 ((6:Nat))
                          (c0
                            (c1 ((1024:Nat))
                              (c2 ((4:Nat))))
                            ((1:Nat)))))
                      (c1 ((14:Nat)) c0_1))
                    (c0
                      (c0
                        (c1 ((128:Nat))
                          (c2 ((2:Nat))))
                        (c5 c0_1))
                      ((2:Nat))))
                  ((1:Nat))))
              ((3:Nat))))
          ((1:Nat))))
      ((220:Nat)):=
  @AXr5285_3
    (fun (n:Nat) =>
      let c0_1:Nat:=c0 n ((4:Nat));
      let c1_1:Nat:=c0 c0_1 ((1:Nat));
      let c2:Nat→ Nat:=c4 c1_1;
      c6
        (c0
          (c1 c1_1
            (c0
              (c5
                (c0
                  (c0
                    (c0
                      (c0 ((60:Nat))
                        (c1 ((6:Nat))
                          (c0
                            (c1 ((1024:Nat))
                              (c2 ((4:Nat))))
                            ((1:Nat)))))
                      (c1 ((14:Nat)) c0_1))
                    (c0
                      (c0
                        (c1 ((128:Nat))
                          (c2 ((2:Nat))))
                        (c5 c0_1))
                      ((2:Nat))))
                  ((1:Nat))))
              ((3:Nat))))
          ((1:Nat))))
    (fun (x:Nat) => (220:Nat))
    (@c29 c30
      (AXr5285_1 ((144:Nat)))
      c35)
    (AXr5285_1 ((220:Nat)));
let c37:Nat→ Nat:=fun (n:Nat) =>
  let c0_1:Nat:=c0 n ((4:Nat));
  let c1_1:Nat:=c0 c0_1 ((1:Nat));
  let c2:Nat→ Nat:=c4 c1_1;
  let c3:Nat:=
    c0
      (c1 ((1024:Nat))
        (c2 ((4:Nat))))
      ((1:Nat));
  c0
    (c0
      (c0
        (c0
          (c0
            (c1
              (c0
                (c5
                  (c1
                    (c0
                      (c5
                        (c0
                          (c0
                            (c0 ((60:Nat))
                              (c1 ((6:Nat)) c3))
                            (c1 ((14:Nat)) c0_1))
                          (c0
                            (c0
                              (c1 ((128:Nat))
                                (c2 ((2:Nat))))
                              (c5 c0_1))
                            ((2:Nat)))))
                      ((1:Nat)))
                    c1_1))
                ((1:Nat)))
              c1_1)
            (c1 c0_1 c0_1))
          (c5 c3))
        (c1 ((5:Nat)) c0_1))
      ((13:Nat)))
    ((1:Nat));
let c38:
  AXr5285_0 fun (n:Nat) =>
    Nat.add
      (let c0_1:Nat:=c0 n ((4:Nat));
      let c1_1:Nat:=c0 c0_1 ((1:Nat));
      let c2:Nat→ Nat:=c4 c1_1;
      let c3:Nat:=
        c0
          (c1 ((1024:Nat))
            (c2 ((4:Nat))))
          ((1:Nat));
      c0
        (c0
          (c0
            (c0
              (c1
                (c0
                  (c5
                    (c1
                      (c0
                        (c5
                          (c0
                            (c0
                              (c0 ((60:Nat))
                                (c1 ((6:Nat)) c3))
                              (c1 ((14:Nat)) c0_1))
                            (c0
                              (c0
                                (c1 ((128:Nat))
                                  (c2 ((2:Nat))))
                                (c5 c0_1))
                              ((2:Nat)))))
                        ((1:Nat)))
                      c1_1))
                  ((1:Nat)))
                c1_1)
              (c1 c0_1 c0_1))
            (c5 c3))
          (c1 ((5:Nat)) c0_1))
        ((13:Nat)))
      ((1:Nat)):=
  @AXr5285_3
    (fun (n:Nat) =>
      let c0_1:Nat:=c0 n ((4:Nat));
      let c1_1:Nat:=c0 c0_1 ((1:Nat));
      let c2:Nat→ Nat:=c4 c1_1;
      let c3:Nat:=
        c0
          (c1 ((1024:Nat))
            (c2 ((4:Nat))))
          ((1:Nat));
      c0
        (c0
          (c0
            (c0
              (c1
                (c0
                  (c5
                    (c1
                      (c0
                        (c5
                          (c0
                            (c0
                              (c0 ((60:Nat))
                                (c1 ((6:Nat)) c3))
                              (c1 ((14:Nat)) c0_1))
                            (c0
                              (c0
                                (c1 ((128:Nat))
                                  (c2 ((2:Nat))))
                                (c5 c0_1))
                              ((2:Nat)))))
                        ((1:Nat)))
                      c1_1))
                  ((1:Nat)))
                c1_1)
              (c1 c0_1 c0_1))
            (c5 c3))
          (c1 ((5:Nat)) c0_1))
        ((13:Nat)))
    (fun (x:Nat) => (1:Nat))
    (@AXr5285_3
      (fun (n:Nat) =>
        let c0_1:Nat:=c0 n ((4:Nat));
        let c1_1:Nat:=c0 c0_1 ((1:Nat));
        let c2:Nat→ Nat:=c4 c1_1;
        let c3:Nat:=
          c0
            (c1 ((1024:Nat))
              (c2 ((4:Nat))))
            ((1:Nat));
        c0
          (c0
            (c0
              (c1
                (c0
                  (c5
                    (c1
                      (c0
                        (c5
                          (c0
                            (c0
                              (c0 ((60:Nat))
                                (c1 ((6:Nat)) c3))
                              (c1 ((14:Nat)) c0_1))
                            (c0
                              (c0
                                (c1 ((128:Nat))
                                  (c2 ((2:Nat))))
                                (c5 c0_1))
                              ((2:Nat)))))
                        ((1:Nat)))
                      c1_1))
                  ((1:Nat)))
                c1_1)
              (c1 c0_1 c0_1))
            (c5 c3))
          (c1 ((5:Nat)) c0_1))
      (fun (x:Nat) => (13:Nat))
      (@AXr5285_3
        (fun (n:Nat) =>
          let c0_1:Nat:=c0 n ((4:Nat));
          let c1_1:Nat:=c0 c0_1 ((1:Nat));
          let c2:Nat→ Nat:=c4 c1_1;
          let c3:Nat:=
            c0
              (c1 ((1024:Nat))
                (c2 ((4:Nat))))
              ((1:Nat));
          c0
            (c0
              (c1
                (c0
                  (c5
                    (c1
                      (c0
                        (c5
                          (c0
                            (c0
                              (c0 ((60:Nat))
                                (c1 ((6:Nat)) c3))
                              (c1 ((14:Nat)) c0_1))
                            (c0
                              (c0
                                (c1 ((128:Nat))
                                  (c2 ((2:Nat))))
                                (c5 c0_1))
                              ((2:Nat)))))
                        ((1:Nat)))
                      c1_1))
                  ((1:Nat)))
                c1_1)
              (c1 c0_1 c0_1))
            (c5 c3))
        (fun (n:Nat) =>
          c1 ((5:Nat))
            (c0 n ((4:Nat))))
        (@AXr5285_3
          (fun (n:Nat) =>
            let c0_1:Nat:=c0 n ((4:Nat));
            let c1_1:Nat:=c0 c0_1 ((1:Nat));
            let c2:Nat→ Nat:=c4 c1_1;
            c0
              (c1
                (c0
                  (c5
                    (c1
                      (c0
                        (c5
                          (c0
                            (c0
                              (c0 ((60:Nat))
                                (c1 ((6:Nat))
                                  (c0
                                    (c1 ((1024:Nat))
                                      (c2 ((4:Nat))))
                                    ((1:Nat)))))
                              (c1 ((14:Nat)) c0_1))
                            (c0
                              (c0
                                (c1 ((128:Nat))
                                  (c2 ((2:Nat))))
                                (c5 c0_1))
                              ((2:Nat)))))
                        ((1:Nat)))
                      c1_1))
                  ((1:Nat)))
                c1_1)
              (c1 c0_1 c0_1))
          (fun (n:Nat) =>
            c5
              (c0
                (c1 ((1024:Nat))
                  (c4
                    (c0 (c0 n ((4:Nat)))
                      ((1:Nat)))
                    ((4:Nat))))
                ((1:Nat))))
          (@AXr5285_3
            (fun (n:Nat) =>
              let c0_1:Nat:=c0 n ((4:Nat));
              let c1_1:Nat:=c0 c0_1 ((1:Nat));
              let c2:Nat→ Nat:=c4 c1_1;
              c1
                (c0
                  (c5
                    (c1
                      (c0
                        (c5
                          (c0
                            (c0
                              (c0 ((60:Nat))
                                (c1 ((6:Nat))
                                  (c0
                                    (c1 ((1024:Nat))
                                      (c2 ((4:Nat))))
                                    ((1:Nat)))))
                              (c1 ((14:Nat)) c0_1))
                            (c0
                              (c0
                                (c1 ((128:Nat))
                                  (c2 ((2:Nat))))
                                (c5 c0_1))
                              ((2:Nat)))))
                        ((1:Nat)))
                      c1_1))
                  ((1:Nat)))
                c1_1)
            c20
            (@AXr5285_4
              (fun (n:Nat) =>
                let c0_1:Nat:=c0 n ((4:Nat));
                let c1_1:Nat:=c0 c0_1 ((1:Nat));
                let c2:Nat→ Nat:=c4 c1_1;
                c0
                  (c5
                    (c1
                      (c0
                        (c5
                          (c0
                            (c0
                              (c0 ((60:Nat))
                                (c1 ((6:Nat))
                                  (c0
                                    (c1 ((1024:Nat))
                                      (c2 ((4:Nat))))
                                    ((1:Nat)))))
                              (c1 ((14:Nat)) c0_1))
                            (c0
                              (c0
                                (c1 ((128:Nat))
                                  (c2 ((2:Nat))))
                                (c5 c0_1))
                              ((2:Nat)))))
                        ((1:Nat)))
                      c1_1))
                  ((1:Nat)))
              c16
              (@AXr5285_3
                (fun (n:Nat) =>
                  let c0_1:Nat:=c0 n ((4:Nat));
                  let c1_1:Nat:=c0 c0_1 ((1:Nat));
                  let c2:Nat→ Nat:=c4 c1_1;
                  c5
                    (c1
                      (c0
                        (c5
                          (c0
                            (c0
                              (c0 ((60:Nat))
                                (c1 ((6:Nat))
                                  (c0
                                    (c1 ((1024:Nat))
                                      (c2 ((4:Nat))))
                                    ((1:Nat)))))
                              (c1 ((14:Nat)) c0_1))
                            (c0
                              (c0
                                (c1 ((128:Nat))
                                  (c2 ((2:Nat))))
                                (c5 c0_1))
                              ((2:Nat)))))
                        ((1:Nat)))
                      c1_1))
                (fun (x:Nat) => (1:Nat))
                (@c23
                  (fun (n:Nat) =>
                    let c0_1:Nat:=c0 n ((4:Nat));
                    let c1_1:Nat:=c0 c0_1 ((1:Nat));
                    let c2:Nat→ Nat:=c4 c1_1;
                    c1
                      (c0
                        (c5
                          (c0
                            (c0
                              (c0 ((60:Nat))
                                (c1 ((6:Nat))
                                  (c0
                                    (c1 ((1024:Nat))
                                      (c2 ((4:Nat))))
                                    ((1:Nat)))))
                              (c1 ((14:Nat)) c0_1))
                            (c0
                              (c0
                                (c1 ((128:Nat))
                                  (c2 ((2:Nat))))
                                (c5 c0_1))
                              ((2:Nat)))))
                        ((1:Nat)))
                      c1_1)
                  (AXr5285_1
                    ((2:Nat)))
                  (@AXr5285_4
                    (fun (n:Nat) =>
                      let c0_1:Nat:=c0 n ((4:Nat));
                      let c1_1:Nat→ Nat:=c4 (c0 c0_1 ((1:Nat)));
                      c0
                        (c5
                          (c0
                            (c0
                              (c0 ((60:Nat))
                                (c1 ((6:Nat))
                                  (c0
                                    (c1 ((1024:Nat))
                                      (c1_1 ((4:Nat))))
                                    ((1:Nat)))))
                              (c1 ((14:Nat)) c0_1))
                            (c0
                              (c0
                                (c1 ((128:Nat))
                                  (c1_1 ((2:Nat))))
                                (c5 c0_1))
                              ((2:Nat)))))
                        ((1:Nat)))
                    c16
                    (@AXr5285_3
                      (fun (n:Nat) =>
                        let c0_1:Nat:=c0 n ((4:Nat));
                        let c1_1:Nat→ Nat:=c4 (c0 c0_1 ((1:Nat)));
                        c5
                          (c0
                            (c0
                              (c0 ((60:Nat))
                                (c1 ((6:Nat))
                                  (c0
                                    (c1 ((1024:Nat))
                                      (c1_1 ((4:Nat))))
                                    ((1:Nat)))))
                              (c1 ((14:Nat)) c0_1))
                            (c0
                              (c0
                                (c1 ((128:Nat))
                                  (c1_1 ((2:Nat))))
                                (c5 c0_1))
                              ((2:Nat)))))
                      (fun (x:Nat) => (1:Nat))
                      (@c23 c32
                        (AXr5285_1
                          ((2:Nat)))
                        c34)
                      (AXr5285_1
                        ((1:Nat))))
                    c17))
                (AXr5285_1
                  ((1:Nat))))
              c17)
            c26)
          (@c23 c27
            (AXr5285_1 ((2:Nat)))
            c33))
        (@AXr5285_4
          (fun (x:Nat) => (5:Nat)) c12
          (AXr5285_1 ((5:Nat)))
          c13))
      (AXr5285_1 ((13:Nat))))
    (AXr5285_1 ((1:Nat)));
@AXr5285_3
  (fun (n:Nat) =>
    let c0_1:Nat:=c0 n ((1:Nat));
    c0
      (c0
        (c0
          (c0
            (c0
              (c0
                (c1
                  (c0 (c1 ((36:Nat)) c0_1)
                    ((61:Nat)))
                  n)
                (c1 ((24:Nat)) n))
              ((56:Nat)))
            (c1 ((13:Nat)) n))
          ((26:Nat)))
        (c1 (c0 (c2 c0_1) ((135:Nat))) n))
      ((80:Nat)))
  (fun (n:Nat) =>
    let c0_1:Nat:=c0 n ((4:Nat));
    let c1_1:Nat:=c4 c0_1 ((2:Nat));
    let c2_1:Nat:=c0 c0_1 ((1:Nat));
    let c3_1:Nat→ Nat:=c4 c2_1;
    let c4:Nat:=c3_1 ((2:Nat));
    let c5_1:Nat:=
      c0 (c0 (c1 ((128:Nat)) c4) (c5 c0_1))
        ((2:Nat));
    let c6_1:Nat→ Nat:=c0 (c2 (c0 c5_1 ((1:Nat))));
    let c7:Nat:=c1 c0_1 c0_1;
    let c8:Nat→ Nat:=c1 c2_1;
    let c9:Nat:=
      c0
        (c1 ((1024:Nat))
          (c3_1 ((4:Nat))))
        ((1:Nat));
    let c10:Nat:=
      c0
        (c0
          (c0 ((60:Nat))
            (c1 ((6:Nat)) c9))
          (c1 ((14:Nat)) c0_1))
        c5_1;
    let c11:Nat:=
      c0
        (c8
          (c0 (c5 (c0 c10 ((1:Nat))))
            ((3:Nat))))
        ((1:Nat));
    let c12:Nat→ Nat:=c1 (c0 (c6 c11) ((220:Nat)));
    let c13:Nat:=
      c0
        (c0
          (c0
            (c0
              (c0
                (c1
                  (c0 (c5 (c1 (c0 (c5 c10) ((1:Nat))) c2_1))
                    ((1:Nat)))
                  c2_1)
                c7)
              (c5 c9))
            (c1 ((5:Nat)) c0_1))
          ((13:Nat)))
        ((1:Nat));
    c0 (c0 (c3 n) ((58:Nat)))
      (c0
        (c0
          (c0 (c1 ((111:Nat)) c1_1)
            (c1 ((77:Nat)) c0_1))
          ((78:Nat)))
        (c0
          (c0
            (c0
              (c0
                (c0
                  (c0 (c1 ((1536:Nat)) c4)
                    (c1 ((48:Nat)) c0_1))
                  ((158:Nat)))
                (c1 (c6_1 ((181:Nat))) c7))
              (c1 (c6_1 ((189:Nat))) c0_1))
            ((78:Nat)))
          (c0
            (c0
              (c0 (c1 ((33:Nat)) c0_1)
                (c1 ((76:Nat)) c7))
              (c1
                (c0
                  (c0
                    (c0
                      (c0 (c1 (c0 (c12 c0_1) ((95:Nat))) c0_1)
                        (c1 ((126:Nat)) c0_1))
                      (c0
                        (c0
                          (c0
                            (c0
                              (c0
                                (c0
                                  (c0 (c12 c1_1)
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c8 (c0 (c5 c11) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c13)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c13)
                                    ((36767:Nat)))
                                  c7))
                              (c1 ((582:Nat)) c13))
                            ((1060:Nat)))
                          (c3 c0_1))
                        (c3 c7)))
                    ((103:Nat)))
                  ((4:Nat)))
                c9))
            ((64:Nat))))))
  (@AXr5285_3
    (fun (n:Nat) =>
      let c0_1:Nat:=c0 n ((1:Nat));
      c0
        (c0
          (c0
            (c0
              (c0
                (c1
                  (c0 (c1 ((36:Nat)) c0_1)
                    ((61:Nat)))
                  n)
                (c1 ((24:Nat)) n))
              ((56:Nat)))
            (c1 ((13:Nat)) n))
          ((26:Nat)))
        (c1 (c0 (c2 c0_1) ((135:Nat))) n))
    (fun (x:Nat) => (80:Nat))
    (@AXr5285_3
      (fun (n:Nat) =>
        c0
          (c0
            (c0
              (c0
                (c1
                  (c0
                    (c1 ((36:Nat))
                      (c0 n ((1:Nat))))
                    ((61:Nat)))
                  n)
                (c1 ((24:Nat)) n))
              ((56:Nat)))
            (c1 ((13:Nat)) n))
          ((26:Nat)))
      (fun (n:Nat) =>
        c1
          (c0 (c2 (c0 n ((1:Nat))))
            ((135:Nat)))
          n)
      (@AXr5285_3
        (fun (n:Nat) =>
          c0
            (c0
              (c0
                (c1
                  (c0
                    (c1 ((36:Nat))
                      (c0 n ((1:Nat))))
                    ((61:Nat)))
                  n)
                (c1 ((24:Nat)) n))
              ((56:Nat)))
            (c1 ((13:Nat)) n))
        (fun (x:Nat) => (26:Nat))
        (@AXr5285_3
          (fun (n:Nat) =>
            c0
              (c0
                (c1
                  (c0
                    (c1 ((36:Nat))
                      (c0 n ((1:Nat))))
                    ((61:Nat)))
                  n)
                (c1 ((24:Nat)) n))
              ((56:Nat)))
          (fun (n:Nat) => c1 ((13:Nat)) n)
          (@AXr5285_3
            (fun (n:Nat) =>
              c0
                (c1
                  (c0
                    (c1 ((36:Nat))
                      (c0 n ((1:Nat))))
                    ((61:Nat)))
                  n)
                (c1 ((24:Nat)) n))
            (fun (x:Nat) => (56:Nat))
            (@AXr5285_3
              (fun (n:Nat) =>
                c1
                  (c0
                    (c1 ((36:Nat))
                      (c0 n ((1:Nat))))
                    ((61:Nat)))
                  n)
              (fun (n:Nat) => c1 ((24:Nat)) n)
              (@AXr5285_4
                (fun (n:Nat) =>
                  c0
                    (c1 ((36:Nat))
                      (c0 n ((1:Nat))))
                    ((61:Nat)))
                (fun (n:Nat) => n)
                (@AXr5285_3
                  (fun (n:Nat) =>
                    c1 ((36:Nat))
                      (c0 n ((1:Nat))))
                  (fun (x:Nat) => (61:Nat))
                  (@AXr5285_4
                    (fun (x:Nat) => (36:Nat)) c7
                    (AXr5285_1
                      ((36:Nat)))
                    c8)
                  (AXr5285_1
                    ((61:Nat))))
                AXr5285_2)
              (@AXr5285_4
                (fun (x:Nat) => (24:Nat)) (fun (n:Nat) => n)
                (AXr5285_1
                  ((24:Nat)))
                AXr5285_2))
            (AXr5285_1
              ((56:Nat))))
          (@AXr5285_4
            (fun (x:Nat) => (13:Nat)) (fun (n:Nat) => n)
            (AXr5285_1 ((13:Nat)))
            AXr5285_2))
        (AXr5285_1 ((26:Nat))))
      (@AXr5285_4
        (fun (n:Nat) =>
          c0 (c2 (c0 n ((1:Nat))))
            ((135:Nat)))
        (fun (n:Nat) => n)
        (@AXr5285_3
          (fun (n:Nat) => c2 (c0 n ((1:Nat))))
          (fun (x:Nat) => (135:Nat))
          (@c9 c7
            (AXr5285_1 ((72:Nat)))
            c8)
          (AXr5285_1
            ((135:Nat))))
        AXr5285_2))
    (AXr5285_1 ((80:Nat))))
  (@AXr5285_3
    (fun (n:Nat) => c0 (c3 n) ((58:Nat)))
    (fun (n:Nat) =>
      let c0_1:Nat:=c0 n ((4:Nat));
      let c1_1:Nat:=c4 c0_1 ((2:Nat));
      let c2_1:Nat:=c0 c0_1 ((1:Nat));
      let c3_1:Nat→ Nat:=c4 c2_1;
      let c4:Nat:=c3_1 ((2:Nat));
      let c5_1:Nat:=
        c0 (c0 (c1 ((128:Nat)) c4) (c5 c0_1))
          ((2:Nat));
      let c6_1:Nat→ Nat:=c0 (c2 (c0 c5_1 ((1:Nat))));
      let c7:Nat:=c1 c0_1 c0_1;
      let c8:Nat→ Nat:=c1 c2_1;
      let c9:Nat:=
        c0
          (c1 ((1024:Nat))
            (c3_1 ((4:Nat))))
          ((1:Nat));
      let c10:Nat:=
        c0
          (c0
            (c0 ((60:Nat))
              (c1 ((6:Nat)) c9))
            (c1 ((14:Nat)) c0_1))
          c5_1;
      let c11:Nat:=
        c0
          (c8
            (c0 (c5 (c0 c10 ((1:Nat))))
              ((3:Nat))))
          ((1:Nat));
      let c12:Nat→ Nat:=c1 (c0 (c6 c11) ((220:Nat)));
      let c13:Nat:=
        c0
          (c0
            (c0
              (c0
                (c0
                  (c1
                    (c0 (c5 (c1 (c0 (c5 c10) ((1:Nat))) c2_1))
                      ((1:Nat)))
                    c2_1)
                  c7)
                (c5 c9))
              (c1 ((5:Nat)) c0_1))
            ((13:Nat)))
          ((1:Nat));
      c0
        (c0
          (c0 (c1 ((111:Nat)) c1_1)
            (c1 ((77:Nat)) c0_1))
          ((78:Nat)))
        (c0
          (c0
            (c0
              (c0
                (c0
                  (c0 (c1 ((1536:Nat)) c4)
                    (c1 ((48:Nat)) c0_1))
                  ((158:Nat)))
                (c1 (c6_1 ((181:Nat))) c7))
              (c1 (c6_1 ((189:Nat))) c0_1))
            ((78:Nat)))
          (c0
            (c0
              (c0 (c1 ((33:Nat)) c0_1)
                (c1 ((76:Nat)) c7))
              (c1
                (c0
                  (c0
                    (c0
                      (c0 (c1 (c0 (c12 c0_1) ((95:Nat))) c0_1)
                        (c1 ((126:Nat)) c0_1))
                      (c0
                        (c0
                          (c0
                            (c0
                              (c0
                                (c0
                                  (c0 (c12 c1_1)
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c8 (c0 (c5 c11) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c13)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c13)
                                    ((36767:Nat)))
                                  c7))
                              (c1 ((582:Nat)) c13))
                            ((1060:Nat)))
                          (c3 c0_1))
                        (c3 c7)))
                    ((103:Nat)))
                  ((4:Nat)))
                c9))
            ((64:Nat)))))
    (@AXr5285_3 (fun (n:Nat) => c3 n)
      (fun (x:Nat) => (58:Nat))
      (@c10 (fun (n:Nat) => n)
        (AXr5285_1 ((71:Nat)))
        AXr5285_2)
      (AXr5285_1 ((58:Nat))))
    (@AXr5285_3
      (fun (n:Nat) =>
        let c0_1:Nat:=c0 n ((4:Nat));
        c0
          (c0
            (c1 ((111:Nat))
              (c4 c0_1 ((2:Nat))))
            (c1 ((77:Nat)) c0_1))
          ((78:Nat)))
      (fun (n:Nat) =>
        let c0_1:Nat:=c0 n ((4:Nat));
        let c1_1:Nat:=c0 c0_1 ((1:Nat));
        let c2_1:Nat→ Nat:=c4 c1_1;
        let c3_1:Nat:=c2_1 ((2:Nat));
        let c4_1:Nat:=
          c0 (c0 (c1 ((128:Nat)) c3_1) (c5 c0_1))
            ((2:Nat));
        let c5_1:Nat→ Nat:=c0 (c2 (c0 c4_1 ((1:Nat))));
        let c6_1:Nat:=c1 c0_1 c0_1;
        let c7:Nat→ Nat:=c1 c1_1;
        let c8:Nat:=
          c0
            (c1 ((1024:Nat))
              (c2_1 ((4:Nat))))
            ((1:Nat));
        let c9:Nat:=
          c0
            (c0
              (c0 ((60:Nat))
                (c1 ((6:Nat)) c8))
              (c1 ((14:Nat)) c0_1))
            c4_1;
        let c10:Nat:=
          c0
            (c7
              (c0 (c5 (c0 c9 ((1:Nat))))
                ((3:Nat))))
            ((1:Nat));
        let c11:Nat→ Nat:=c1 (c0 (c6 c10) ((220:Nat)));
        let c12:Nat:=
          c0
            (c0
              (c0
                (c0
                  (c0
                    (c1
                      (c0 (c5 (c1 (c0 (c5 c9) ((1:Nat))) c1_1))
                        ((1:Nat)))
                      c1_1)
                    c6_1)
                  (c5 c8))
                (c1 ((5:Nat)) c0_1))
              ((13:Nat)))
            ((1:Nat));
        c0
          (c0
            (c0
              (c0
                (c0
                  (c0 (c1 ((1536:Nat)) c3_1)
                    (c1 ((48:Nat)) c0_1))
                  ((158:Nat)))
                (c1 (c5_1 ((181:Nat))) c6_1))
              (c1 (c5_1 ((189:Nat))) c0_1))
            ((78:Nat)))
          (c0
            (c0
              (c0 (c1 ((33:Nat)) c0_1)
                (c1 ((76:Nat)) c6_1))
              (c1
                (c0
                  (c0
                    (c0
                      (c0 (c1 (c0 (c11 c0_1) ((95:Nat))) c0_1)
                        (c1 ((126:Nat)) c0_1))
                      (c0
                        (c0
                          (c0
                            (c0
                              (c0
                                (c0
                                  (c0 (c11 (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c7 (c0 (c5 c10) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c12)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c12)
                                    ((36767:Nat)))
                                  c6_1))
                              (c1 ((582:Nat)) c12))
                            ((1060:Nat)))
                          (c3 c0_1))
                        (c3 c6_1)))
                    ((103:Nat)))
                  ((4:Nat)))
                c8))
            ((64:Nat))))
      (@AXr5285_3
        (fun (n:Nat) =>
          let c0_1:Nat:=c0 n ((4:Nat));
          c0
            (c1 ((111:Nat))
              (c4 c0_1 ((2:Nat))))
            (c1 ((77:Nat)) c0_1))
        (fun (x:Nat) => (78:Nat))
        (@AXr5285_3
          (fun (n:Nat) =>
            c1 ((111:Nat))
              (c4 (c0 n ((4:Nat)))
                ((2:Nat))))
          (fun (n:Nat) =>
            c1 ((77:Nat))
              (c0 n ((4:Nat))))
          (@AXr5285_4
            (fun (x:Nat) => (111:Nat)) c11
            (AXr5285_1
              ((111:Nat)))
            c14)
          (@AXr5285_4
            (fun (x:Nat) => (77:Nat)) c12
            (AXr5285_1 ((77:Nat)))
            c13))
        (AXr5285_1 ((78:Nat))))
      (@AXr5285_3
        (fun (n:Nat) =>
          let c0_1:Nat:=c0 n ((4:Nat));
          let c1_1:Nat:=
            c4 (c0 c0_1 ((1:Nat)))
              ((2:Nat));
          let c2:Nat→ Nat:=
            c0
              (c2
                (c0
                  (c0 (c0 (c1 ((128:Nat)) c1_1) (c5 c0_1))
                    ((2:Nat)))
                  ((1:Nat))));
          c0
            (c0
              (c0
                (c0
                  (c0 (c1 ((1536:Nat)) c1_1)
                    (c1 ((48:Nat)) c0_1))
                  ((158:Nat)))
                (c1 (c2 ((181:Nat))) (c1 c0_1 c0_1)))
              (c1 (c2 ((189:Nat))) c0_1))
            ((78:Nat)))
        (fun (n:Nat) =>
          let c0_1:Nat:=c0 n ((4:Nat));
          let c1_1:Nat:=c1 c0_1 c0_1;
          let c2:Nat:=c0 c0_1 ((1:Nat));
          let c3_1:Nat→ Nat:=c1 c2;
          let c4_1:Nat→ Nat:=c4 c2;
          let c5_1:Nat:=
            c0
              (c1 ((1024:Nat))
                (c4_1 ((4:Nat))))
              ((1:Nat));
          let c6_1:Nat:=
            c0
              (c0
                (c0 ((60:Nat))
                  (c1 ((6:Nat)) c5_1))
                (c1 ((14:Nat)) c0_1))
              (c0
                (c0
                  (c1 ((128:Nat))
                    (c4_1 ((2:Nat))))
                  (c5 c0_1))
                ((2:Nat)));
          let c7:Nat:=
            c0
              (c3_1
                (c0 (c5 (c0 c6_1 ((1:Nat))))
                  ((3:Nat))))
              ((1:Nat));
          let c8:Nat→ Nat:=c1 (c0 (c6 c7) ((220:Nat)));
          let c9:Nat:=
            c0
              (c0
                (c0
                  (c0
                    (c0
                      (c1
                        (c0 (c5 (c1 (c0 (c5 c6_1) ((1:Nat))) c2))
                          ((1:Nat)))
                        c2)
                      c1_1)
                    (c5 c5_1))
                  (c1 ((5:Nat)) c0_1))
                ((13:Nat)))
              ((1:Nat));
          c0
            (c0
              (c0 (c1 ((33:Nat)) c0_1)
                (c1 ((76:Nat)) c1_1))
              (c1
                (c0
                  (c0
                    (c0
                      (c0 (c1 (c0 (c8 c0_1) ((95:Nat))) c0_1)
                        (c1 ((126:Nat)) c0_1))
                      (c0
                        (c0
                          (c0
                            (c0
                              (c0
                                (c0
                                  (c0 (c8 (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c3_1
                                              (c0 (c5 c7) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c9)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c9)
                                    ((36767:Nat)))
                                  c1_1))
                              (c1 ((582:Nat)) c9))
                            ((1060:Nat)))
                          (c3 c0_1))
                        (c3 c1_1)))
                    ((103:Nat)))
                  ((4:Nat)))
                c5_1))
            ((64:Nat)))
        (@AXr5285_3
          (fun (n:Nat) =>
            let c0_1:Nat:=c0 n ((4:Nat));
            let c1_1:Nat:=
              c4 (c0 c0_1 ((1:Nat)))
                ((2:Nat));
            let c2:Nat→ Nat:=
              c0
                (c2
                  (c0
                    (c0 (c0 (c1 ((128:Nat)) c1_1) (c5 c0_1))
                      ((2:Nat)))
                    ((1:Nat))));
            c0
              (c0
                (c0
                  (c0 (c1 ((1536:Nat)) c1_1)
                    (c1 ((48:Nat)) c0_1))
                  ((158:Nat)))
                (c1 (c2 ((181:Nat))) (c1 c0_1 c0_1)))
              (c1 (c2 ((189:Nat))) c0_1))
          (fun (x:Nat) => (78:Nat))
          (@AXr5285_3
            (fun (n:Nat) =>
              let c0_1:Nat:=c0 n ((4:Nat));
              let c1_1:Nat:=
                c4 (c0 c0_1 ((1:Nat)))
                  ((2:Nat));
              c0
                (c0
                  (c0 (c1 ((1536:Nat)) c1_1)
                    (c1 ((48:Nat)) c0_1))
                  ((158:Nat)))
                (c1
                  (c0
                    (c2
                      (c0
                        (c0 (c0 (c1 ((128:Nat)) c1_1) (c5 c0_1))
                          ((2:Nat)))
                        ((1:Nat))))
                    ((181:Nat)))
                  (c1 c0_1 c0_1)))
            (fun (n:Nat) =>
              let c0_1:Nat:=c0 n ((4:Nat));
              c1
                (c0
                  (c2
                    (c0
                      (c0
                        (c0
                          (c1 ((128:Nat))
                            (c4 (c0 c0_1 ((1:Nat)))
                              ((2:Nat))))
                          (c5 c0_1))
                        ((2:Nat)))
                      ((1:Nat))))
                  ((189:Nat)))
                c0_1)
            (@AXr5285_3
              (fun (n:Nat) =>
                let c0_1:Nat:=c0 n ((4:Nat));
                c0
                  (c0
                    (c1 ((1536:Nat))
                      (c4 (c0 c0_1 ((1:Nat)))
                        ((2:Nat))))
                    (c1 ((48:Nat)) c0_1))
                  ((158:Nat)))
              (fun (n:Nat) =>
                let c0_1:Nat:=c0 n ((4:Nat));
                c1
                  (c0
                    (c2
                      (c0
                        (c0
                          (c0
                            (c1 ((128:Nat))
                              (c4 (c0 c0_1 ((1:Nat)))
                                ((2:Nat))))
                            (c5 c0_1))
                          ((2:Nat)))
                        ((1:Nat))))
                    ((181:Nat)))
                  (c1 c0_1 c0_1))
              (@AXr5285_3
                (fun (n:Nat) =>
                  let c0_1:Nat:=c0 n ((4:Nat));
                  c0
                    (c1 ((1536:Nat))
                      (c4 (c0 c0_1 ((1:Nat)))
                        ((2:Nat))))
                    (c1 ((48:Nat)) c0_1))
                (fun (x:Nat) => (158:Nat))
                (@AXr5285_3
                  (fun (n:Nat) =>
                    c1 ((1536:Nat))
                      (c4
                        (c0 (c0 n ((4:Nat)))
                          ((1:Nat)))
                        ((2:Nat))))
                  (fun (n:Nat) =>
                    c1 ((48:Nat))
                      (c0 n ((4:Nat))))
                  (@AXr5285_4
                    (fun (x:Nat) => (1536:Nat)) c15
                    (AXr5285_1
                      ((1536:Nat)))
                    c19)
                  (@AXr5285_4
                    (fun (x:Nat) => (48:Nat)) c12
                    (AXr5285_1
                      ((48:Nat)))
                    c13))
                (AXr5285_1
                  ((158:Nat))))
              (@AXr5285_4
                (fun (n:Nat) =>
                  let c0_1:Nat:=c0 n ((4:Nat));
                  c0
                    (c2
                      (c0
                        (c0
                          (c0
                            (c1 ((128:Nat))
                              (c4 (c0 c0_1 ((1:Nat)))
                                ((2:Nat))))
                            (c5 c0_1))
                          ((2:Nat)))
                        ((1:Nat))))
                    ((181:Nat)))
                c20
                (@c21 (fun (x:Nat) => (181:Nat)) c25
                  (AXr5285_1
                    ((181:Nat))))
                c26))
            (@AXr5285_4
              (fun (n:Nat) =>
                let c0_1:Nat:=c0 n ((4:Nat));
                c0
                  (c2
                    (c0
                      (c0
                        (c0
                          (c1 ((128:Nat))
                            (c4 (c0 c0_1 ((1:Nat)))
                              ((2:Nat))))
                          (c5 c0_1))
                        ((2:Nat)))
                      ((1:Nat))))
                  ((189:Nat)))
              c12
              (@c21 (fun (x:Nat) => (189:Nat)) c25
                (AXr5285_1
                  ((189:Nat))))
              c13))
          (AXr5285_1 ((78:Nat))))
        (@AXr5285_3
          (fun (n:Nat) =>
            let c0_1:Nat:=c0 n ((4:Nat));
            let c1_1:Nat:=c1 c0_1 c0_1;
            let c2:Nat:=c0 c0_1 ((1:Nat));
            let c3_1:Nat→ Nat:=c1 c2;
            let c4_1:Nat→ Nat:=c4 c2;
            let c5_1:Nat:=
              c0
                (c1 ((1024:Nat))
                  (c4_1 ((4:Nat))))
                ((1:Nat));
            let c6_1:Nat:=
              c0
                (c0
                  (c0 ((60:Nat))
                    (c1 ((6:Nat)) c5_1))
                  (c1 ((14:Nat)) c0_1))
                (c0
                  (c0
                    (c1 ((128:Nat))
                      (c4_1 ((2:Nat))))
                    (c5 c0_1))
                  ((2:Nat)));
            let c7:Nat:=
              c0
                (c3_1
                  (c0 (c5 (c0 c6_1 ((1:Nat))))
                    ((3:Nat))))
                ((1:Nat));
            let c8:Nat→ Nat:=c1 (c0 (c6 c7) ((220:Nat)));
            let c9:Nat:=
              c0
                (c0
                  (c0
                    (c0
                      (c0
                        (c1
                          (c0 (c5 (c1 (c0 (c5 c6_1) ((1:Nat))) c2))
                            ((1:Nat)))
                          c2)
                        c1_1)
                      (c5 c5_1))
                    (c1 ((5:Nat)) c0_1))
                  ((13:Nat)))
                ((1:Nat));
            c0
              (c0 (c1 ((33:Nat)) c0_1)
                (c1 ((76:Nat)) c1_1))
              (c1
                (c0
                  (c0
                    (c0
                      (c0 (c1 (c0 (c8 c0_1) ((95:Nat))) c0_1)
                        (c1 ((126:Nat)) c0_1))
                      (c0
                        (c0
                          (c0
                            (c0
                              (c0
                                (c0
                                  (c0 (c8 (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c3_1
                                              (c0 (c5 c7) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c9)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c9)
                                    ((36767:Nat)))
                                  c1_1))
                              (c1 ((582:Nat)) c9))
                            ((1060:Nat)))
                          (c3 c0_1))
                        (c3 c1_1)))
                    ((103:Nat)))
                  ((4:Nat)))
                c5_1))
          (fun (x:Nat) => (64:Nat))
          (@AXr5285_3
            (fun (n:Nat) =>
              let c0_1:Nat:=c0 n ((4:Nat));
              c0 (c1 ((33:Nat)) c0_1)
                (c1 ((76:Nat)) (c1 c0_1 c0_1)))
            (fun (n:Nat) =>
              let c0_1:Nat:=c0 n ((4:Nat));
              let c1_1:Nat:=c0 c0_1 ((1:Nat));
              let c2:Nat→ Nat:=c1 c1_1;
              let c3_1:Nat→ Nat:=c4 c1_1;
              let c4_1:Nat:=
                c0
                  (c1 ((1024:Nat))
                    (c3_1 ((4:Nat))))
                  ((1:Nat));
              let c5_1:Nat:=
                c0
                  (c0
                    (c0 ((60:Nat))
                      (c1 ((6:Nat)) c4_1))
                    (c1 ((14:Nat)) c0_1))
                  (c0
                    (c0
                      (c1 ((128:Nat))
                        (c3_1 ((2:Nat))))
                      (c5 c0_1))
                    ((2:Nat)));
              let c6_1:Nat:=
                c0
                  (c2
                    (c0 (c5 (c0 c5_1 ((1:Nat))))
                      ((3:Nat))))
                  ((1:Nat));
              let c7:Nat→ Nat:=c1 (c0 (c6 c6_1) ((220:Nat)));
              let c8:Nat:=c1 c0_1 c0_1;
              let c9:Nat:=
                c0
                  (c0
                    (c0
                      (c0
                        (c0
                          (c1
                            (c0 (c5 (c1 (c0 (c5 c5_1) ((1:Nat))) c1_1))
                              ((1:Nat)))
                            c1_1)
                          c8)
                        (c5 c4_1))
                      (c1 ((5:Nat)) c0_1))
                    ((13:Nat)))
                  ((1:Nat));
              c1
                (c0
                  (c0
                    (c0
                      (c0 (c1 (c0 (c7 c0_1) ((95:Nat))) c0_1)
                        (c1 ((126:Nat)) c0_1))
                      (c0
                        (c0
                          (c0
                            (c0
                              (c0
                                (c0
                                  (c0 (c7 (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c2
                                              (c0 (c5 c6_1) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c9)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c9)
                                    ((36767:Nat)))
                                  c8))
                              (c1 ((582:Nat)) c9))
                            ((1060:Nat)))
                          (c3 c0_1))
                        (c3 c8)))
                    ((103:Nat)))
                  ((4:Nat)))
                c4_1)
            (@AXr5285_3
              (fun (n:Nat) =>
                c1 ((33:Nat))
                  (c0 n ((4:Nat))))
              (fun (n:Nat) =>
                let c0:Nat:=c0 n ((4:Nat));
                c1 ((76:Nat)) (c1 c0 c0))
              (@AXr5285_4
                (fun (x:Nat) => (33:Nat)) c12
                (AXr5285_1
                  ((33:Nat)))
                c13)
              (@AXr5285_4
                (fun (x:Nat) => (76:Nat)) c20
                (AXr5285_1
                  ((76:Nat)))
                c26))
            (@AXr5285_4
              (fun (n:Nat) =>
                let c0_1:Nat:=c0 n ((4:Nat));
                let c1_1:Nat:=c0 c0_1 ((1:Nat));
                let c2:Nat→ Nat:=c1 c1_1;
                let c3_1:Nat→ Nat:=c4 c1_1;
                let c4_1:Nat:=
                  c0
                    (c1 ((1024:Nat))
                      (c3_1 ((4:Nat))))
                    ((1:Nat));
                let c5_1:Nat:=
                  c0
                    (c0
                      (c0 ((60:Nat))
                        (c1 ((6:Nat)) c4_1))
                      (c1 ((14:Nat)) c0_1))
                    (c0
                      (c0
                        (c1 ((128:Nat))
                          (c3_1 ((2:Nat))))
                        (c5 c0_1))
                      ((2:Nat)));
                let c6_1:Nat:=
                  c0
                    (c2
                      (c0 (c5 (c0 c5_1 ((1:Nat))))
                        ((3:Nat))))
                    ((1:Nat));
                let c7:Nat→ Nat:=c1 (c0 (c6 c6_1) ((220:Nat)));
                let c8:Nat:=c1 c0_1 c0_1;
                let c9:Nat:=
                  c0
                    (c0
                      (c0
                        (c0
                          (c0
                            (c1
                              (c0
                                (c5 (c1 (c0 (c5 c5_1) ((1:Nat))) c1_1))
                                ((1:Nat)))
                              c1_1)
                            c8)
                          (c5 c4_1))
                        (c1 ((5:Nat)) c0_1))
                      ((13:Nat)))
                    ((1:Nat));
                c0
                  (c0
                    (c0
                      (c0 (c1 (c0 (c7 c0_1) ((95:Nat))) c0_1)
                        (c1 ((126:Nat)) c0_1))
                      (c0
                        (c0
                          (c0
                            (c0
                              (c0
                                (c0
                                  (c0 (c7 (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c2
                                              (c0 (c5 c6_1) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c9)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c9)
                                    ((36767:Nat)))
                                  c8))
                              (c1 ((582:Nat)) c9))
                            ((1060:Nat)))
                          (c3 c0_1))
                        (c3 c8)))
                    ((103:Nat)))
                  ((4:Nat)))
              c27
              (@AXr5285_3
                (fun (n:Nat) =>
                  let c0_1:Nat:=c0 n ((4:Nat));
                  let c1_1:Nat:=c0 c0_1 ((1:Nat));
                  let c2:Nat→ Nat:=c1 c1_1;
                  let c3_1:Nat→ Nat:=c4 c1_1;
                  let c4_1:Nat:=
                    c0
                      (c1 ((1024:Nat))
                        (c3_1 ((4:Nat))))
                      ((1:Nat));
                  let c5_1:Nat:=
                    c0
                      (c0
                        (c0 ((60:Nat))
                          (c1 ((6:Nat)) c4_1))
                        (c1 ((14:Nat)) c0_1))
                      (c0
                        (c0
                          (c1 ((128:Nat))
                            (c3_1 ((2:Nat))))
                          (c5 c0_1))
                        ((2:Nat)));
                  let c6_1:Nat:=
                    c0
                      (c2
                        (c0 (c5 (c0 c5_1 ((1:Nat))))
                          ((3:Nat))))
                      ((1:Nat));
                  let c7:Nat→ Nat:=c1 (c0 (c6 c6_1) ((220:Nat)));
                  let c8:Nat:=c1 c0_1 c0_1;
                  let c9:Nat:=
                    c0
                      (c0
                        (c0
                          (c0
                            (c0
                              (c1
                                (c0
                                  (c5
                                    (c1 (c0 (c5 c5_1) ((1:Nat))) c1_1))
                                  ((1:Nat)))
                                c1_1)
                              c8)
                            (c5 c4_1))
                          (c1 ((5:Nat)) c0_1))
                        ((13:Nat)))
                      ((1:Nat));
                  c0
                    (c0
                      (c0 (c1 (c0 (c7 c0_1) ((95:Nat))) c0_1)
                        (c1 ((126:Nat)) c0_1))
                      (c0
                        (c0
                          (c0
                            (c0
                              (c0
                                (c0
                                  (c0 (c7 (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c2
                                              (c0 (c5 c6_1) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c9)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c9)
                                    ((36767:Nat)))
                                  c8))
                              (c1 ((582:Nat)) c9))
                            ((1060:Nat)))
                          (c3 c0_1))
                        (c3 c8)))
                    ((103:Nat)))
                (fun (x:Nat) => (4:Nat))
                (@AXr5285_3
                  (fun (n:Nat) =>
                    let c0_1:Nat:=c0 n ((4:Nat));
                    let c1_1:Nat:=c0 c0_1 ((1:Nat));
                    let c2:Nat→ Nat:=c1 c1_1;
                    let c3_1:Nat→ Nat:=c4 c1_1;
                    let c4_1:Nat:=
                      c0
                        (c1 ((1024:Nat))
                          (c3_1 ((4:Nat))))
                        ((1:Nat));
                    let c5_1:Nat:=
                      c0
                        (c0
                          (c0 ((60:Nat))
                            (c1 ((6:Nat)) c4_1))
                          (c1 ((14:Nat)) c0_1))
                        (c0
                          (c0
                            (c1 ((128:Nat))
                              (c3_1 ((2:Nat))))
                            (c5 c0_1))
                          ((2:Nat)));
                    let c6_1:Nat:=
                      c0
                        (c2
                          (c0 (c5 (c0 c5_1 ((1:Nat))))
                            ((3:Nat))))
                        ((1:Nat));
                    let c7:Nat→ Nat:=
                      c1 (c0 (c6 c6_1) ((220:Nat)));
                    let c8:Nat:=c1 c0_1 c0_1;
                    let c9:Nat:=
                      c0
                        (c0
                          (c0
                            (c0
                              (c0
                                (c1
                                  (c0
                                    (c5
                                      (c1 (c0 (c5 c5_1) ((1:Nat)))
                                        c1_1))
                                    ((1:Nat)))
                                  c1_1)
                                c8)
                              (c5 c4_1))
                            (c1 ((5:Nat)) c0_1))
                          ((13:Nat)))
                        ((1:Nat));
                    c0
                      (c0 (c1 (c0 (c7 c0_1) ((95:Nat))) c0_1)
                        (c1 ((126:Nat)) c0_1))
                      (c0
                        (c0
                          (c0
                            (c0
                              (c0
                                (c0
                                  (c0 (c7 (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c2
                                              (c0 (c5 c6_1) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c9)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c9)
                                    ((36767:Nat)))
                                  c8))
                              (c1 ((582:Nat)) c9))
                            ((1060:Nat)))
                          (c3 c0_1))
                        (c3 c8)))
                  (fun (x:Nat) => (103:Nat))
                  (@AXr5285_3
                    (fun (n:Nat) =>
                      let c0_1:Nat:=c0 n ((4:Nat));
                      let c1_1:Nat:=c0 c0_1 ((1:Nat));
                      let c2:Nat→ Nat:=c4 c1_1;
                      c0
                        (c1
                          (c0
                            (c1
                              (c0
                                (c6
                                  (c0
                                    (c1 c1_1
                                      (c0
                                        (c5
                                          (c0
                                            (c0
                                              (c0
                                                (c0 ((60:Nat))
                                                  (c1 ((6:Nat))
                                                    (c0
                                                      (c1
                                                        ((1024:Nat))
                                                        (c2 ((4:Nat))))
                                                      ((1:Nat)))))
                                                (c1 ((14:Nat)) c0_1))
                                              (c0
                                                (c0
                                                  (c1 ((128:Nat))
                                                    (c2 ((2:Nat))))
                                                  (c5 c0_1))
                                                ((2:Nat))))
                                            ((1:Nat))))
                                        ((3:Nat))))
                                    ((1:Nat))))
                                ((220:Nat)))
                              c0_1)
                            ((95:Nat)))
                          c0_1)
                        (c1 ((126:Nat)) c0_1))
                    (fun (n:Nat) =>
                      let c0_1:Nat:=c0 n ((4:Nat));
                      let c1_1:Nat:=c0 c0_1 ((1:Nat));
                      let c2:Nat→ Nat:=c1 c1_1;
                      let c3_1:Nat→ Nat:=c4 c1_1;
                      let c4_1:Nat:=
                        c0
                          (c1 ((1024:Nat))
                            (c3_1 ((4:Nat))))
                          ((1:Nat));
                      let c5_1:Nat:=
                        c0
                          (c0
                            (c0 ((60:Nat))
                              (c1 ((6:Nat)) c4_1))
                            (c1 ((14:Nat)) c0_1))
                          (c0
                            (c0
                              (c1 ((128:Nat))
                                (c3_1 ((2:Nat))))
                              (c5 c0_1))
                            ((2:Nat)));
                      let c6_1:Nat:=
                        c0
                          (c2
                            (c0 (c5 (c0 c5_1 ((1:Nat))))
                              ((3:Nat))))
                          ((1:Nat));
                      let c7:Nat:=c1 c0_1 c0_1;
                      let c8:Nat:=
                        c0
                          (c0
                            (c0
                              (c0
                                (c0
                                  (c1
                                    (c0
                                      (c5
                                        (c1 (c0 (c5 c5_1) ((1:Nat)))
                                          c1_1))
                                      ((1:Nat)))
                                    c1_1)
                                  c7)
                                (c5 c4_1))
                              (c1 ((5:Nat)) c0_1))
                            ((13:Nat)))
                          ((1:Nat));
                      c0
                        (c0
                          (c0
                            (c0
                              (c0
                                (c0
                                  (c0
                                    (c1 (c0 (c6 c6_1) ((220:Nat)))
                                      (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c2
                                              (c0 (c5 c6_1) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c8)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c8)
                                    ((36767:Nat)))
                                  c7))
                              (c1 ((582:Nat)) c8))
                            ((1060:Nat)))
                          (c3 c0_1))
                        (c3 c7))
                    (@AXr5285_3
                      (fun (n:Nat) =>
                        let c0_1:Nat:=c0 n ((4:Nat));
                        let c1_1:Nat:=c0 c0_1 ((1:Nat));
                        let c2:Nat→ Nat:=c4 c1_1;
                        c1
                          (c0
                            (c1
                              (c0
                                (c6
                                  (c0
                                    (c1 c1_1
                                      (c0
                                        (c5
                                          (c0
                                            (c0
                                              (c0
                                                (c0 ((60:Nat))
                                                  (c1 ((6:Nat))
                                                    (c0
                                                      (c1
                                                        ((1024:Nat))
                                                        (c2 ((4:Nat))))
                                                      ((1:Nat)))))
                                                (c1 ((14:Nat)) c0_1))
                                              (c0
                                                (c0
                                                  (c1 ((128:Nat))
                                                    (c2 ((2:Nat))))
                                                  (c5 c0_1))
                                                ((2:Nat))))
                                            ((1:Nat))))
                                        ((3:Nat))))
                                    ((1:Nat))))
                                ((220:Nat)))
                              c0_1)
                            ((95:Nat)))
                          c0_1)
                      (fun (n:Nat) =>
                        c1 ((126:Nat))
                          (c0 n ((4:Nat))))
                      (@AXr5285_4
                        (fun (n:Nat) =>
                          let c0_1:Nat:=c0 n ((4:Nat));
                          let c1_1:Nat:=c0 c0_1 ((1:Nat));
                          let c2:Nat→ Nat:=c4 c1_1;
                          c0
                            (c1
                              (c0
                                (c6
                                  (c0
                                    (c1 c1_1
                                      (c0
                                        (c5
                                          (c0
                                            (c0
                                              (c0
                                                (c0 ((60:Nat))
                                                  (c1 ((6:Nat))
                                                    (c0
                                                      (c1
                                                        ((1024:Nat))
                                                        (c2 ((4:Nat))))
                                                      ((1:Nat)))))
                                                (c1 ((14:Nat)) c0_1))
                                              (c0
                                                (c0
                                                  (c1 ((128:Nat))
                                                    (c2 ((2:Nat))))
                                                  (c5 c0_1))
                                                ((2:Nat))))
                                            ((1:Nat))))
                                        ((3:Nat))))
                                    ((1:Nat))))
                                ((220:Nat)))
                              c0_1)
                            ((95:Nat)))
                        c12
                        (@AXr5285_3
                          (fun (n:Nat) =>
                            let c0_1:Nat:=c0 n ((4:Nat));
                            let c1_1:Nat:=c0 c0_1 ((1:Nat));
                            let c2:Nat→ Nat:=c4 c1_1;
                            c1
                              (c0
                                (c6
                                  (c0
                                    (c1 c1_1
                                      (c0
                                        (c5
                                          (c0
                                            (c0
                                              (c0
                                                (c0 ((60:Nat))
                                                  (c1 ((6:Nat))
                                                    (c0
                                                      (c1
                                                        ((1024:Nat))
                                                        (c2 ((4:Nat))))
                                                      ((1:Nat)))))
                                                (c1 ((14:Nat)) c0_1))
                                              (c0
                                                (c0
                                                  (c1 ((128:Nat))
                                                    (c2 ((2:Nat))))
                                                  (c5 c0_1))
                                                ((2:Nat))))
                                            ((1:Nat))))
                                        ((3:Nat))))
                                    ((1:Nat))))
                                ((220:Nat)))
                              c0_1)
                          (fun (x:Nat) => (95:Nat))
                          (@c28 c12 c36 c13)
                          (AXr5285_1
                            ((95:Nat))))
                        c13)
                      (@AXr5285_4
                        (fun (x:Nat) => (126:Nat)) c12
                        (AXr5285_1
                          ((126:Nat)))
                        c13))
                    (@AXr5285_3
                      (fun (n:Nat) =>
                        let c0_1:Nat:=c0 n ((4:Nat));
                        let c1_1:Nat:=c0 c0_1 ((1:Nat));
                        let c2:Nat→ Nat:=c1 c1_1;
                        let c3_1:Nat→ Nat:=c4 c1_1;
                        let c4_1:Nat:=
                          c0
                            (c1 ((1024:Nat))
                              (c3_1 ((4:Nat))))
                            ((1:Nat));
                        let c5_1:Nat:=
                          c0
                            (c0
                              (c0 ((60:Nat))
                                (c1 ((6:Nat)) c4_1))
                              (c1 ((14:Nat)) c0_1))
                            (c0
                              (c0
                                (c1 ((128:Nat))
                                  (c3_1 ((2:Nat))))
                                (c5 c0_1))
                              ((2:Nat)));
                        let c6_1:Nat:=
                          c0
                            (c2
                              (c0 (c5 (c0 c5_1 ((1:Nat))))
                                ((3:Nat))))
                            ((1:Nat));
                        let c7:Nat:=c1 c0_1 c0_1;
                        let c8:Nat:=
                          c0
                            (c0
                              (c0
                                (c0
                                  (c0
                                    (c1
                                      (c0
                                        (c5
                                          (c1 (c0 (c5 c5_1) ((1:Nat)))
                                            c1_1))
                                        ((1:Nat)))
                                      c1_1)
                                    c7)
                                  (c5 c4_1))
                                (c1 ((5:Nat)) c0_1))
                              ((13:Nat)))
                            ((1:Nat));
                        c0
                          (c0
                            (c0
                              (c0
                                (c0
                                  (c0
                                    (c1 (c0 (c6 c6_1) ((220:Nat)))
                                      (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c2
                                              (c0 (c5 c6_1) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c8)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c8)
                                    ((36767:Nat)))
                                  c7))
                              (c1 ((582:Nat)) c8))
                            ((1060:Nat)))
                          (c3 c0_1))
                      (fun (n:Nat) =>
                        let c0:Nat:=c0 n ((4:Nat));
                        c3 (c1 c0 c0))
                      (@AXr5285_3
                        (fun (n:Nat) =>
                          let c0_1:Nat:=c0 n ((4:Nat));
                          let c1_1:Nat:=c0 c0_1 ((1:Nat));
                          let c2:Nat→ Nat:=c1 c1_1;
                          let c3:Nat→ Nat:=c4 c1_1;
                          let c4_1:Nat:=
                            c0
                              (c1 ((1024:Nat))
                                (c3 ((4:Nat))))
                              ((1:Nat));
                          let c5_1:Nat:=
                            c0
                              (c0
                                (c0 ((60:Nat))
                                  (c1 ((6:Nat)) c4_1))
                                (c1 ((14:Nat)) c0_1))
                              (c0
                                (c0
                                  (c1 ((128:Nat))
                                    (c3 ((2:Nat))))
                                  (c5 c0_1))
                                ((2:Nat)));
                          let c6_1:Nat:=
                            c0
                              (c2
                                (c0 (c5 (c0 c5_1 ((1:Nat))))
                                  ((3:Nat))))
                              ((1:Nat));
                          let c7:Nat:=c1 c0_1 c0_1;
                          let c8:Nat:=
                            c0
                              (c0
                                (c0
                                  (c0
                                    (c0
                                      (c1
                                        (c0
                                          (c5
                                            (c1 (c0 (c5 c5_1) ((1:Nat)))
                                              c1_1))
                                          ((1:Nat)))
                                        c1_1)
                                      c7)
                                    (c5 c4_1))
                                  (c1 ((5:Nat)) c0_1))
                                ((13:Nat)))
                              ((1:Nat));
                          c0
                            (c0
                              (c0
                                (c0
                                  (c0
                                    (c1 (c0 (c6 c6_1) ((220:Nat)))
                                      (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c2
                                              (c0 (c5 c6_1) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c8)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c8)
                                    ((36767:Nat)))
                                  c7))
                              (c1 ((582:Nat)) c8))
                            ((1060:Nat)))
                        (fun (n:Nat) => c3 (c0 n ((4:Nat))))
                        (@AXr5285_3
                          (fun (n:Nat) =>
                            let c0_1:Nat:=c0 n ((4:Nat));
                            let c1_1:Nat:=c0 c0_1 ((1:Nat));
                            let c2:Nat→ Nat:=c1 c1_1;
                            let c3:Nat→ Nat:=c4 c1_1;
                            let c4_1:Nat:=
                              c0
                                (c1 ((1024:Nat))
                                  (c3 ((4:Nat))))
                                ((1:Nat));
                            let c5_1:Nat:=
                              c0
                                (c0
                                  (c0 ((60:Nat))
                                    (c1 ((6:Nat)) c4_1))
                                  (c1 ((14:Nat)) c0_1))
                                (c0
                                  (c0
                                    (c1 ((128:Nat))
                                      (c3 ((2:Nat))))
                                    (c5 c0_1))
                                  ((2:Nat)));
                            let c6_1:Nat:=
                              c0
                                (c2
                                  (c0 (c5 (c0 c5_1 ((1:Nat))))
                                    ((3:Nat))))
                                ((1:Nat));
                            let c7:Nat:=c1 c0_1 c0_1;
                            let c8:Nat:=
                              c0
                                (c0
                                  (c0
                                    (c0
                                      (c0
                                        (c1
                                          (c0
                                            (c5
                                              (c1
                                                (c0 (c5 c5_1) ((1:Nat)))
                                                c1_1))
                                            ((1:Nat)))
                                          c1_1)
                                        c7)
                                      (c5 c4_1))
                                    (c1 ((5:Nat)) c0_1))
                                  ((13:Nat)))
                                ((1:Nat));
                            c0
                              (c0
                                (c0
                                  (c0
                                    (c1 (c0 (c6 c6_1) ((220:Nat)))
                                      (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c2
                                              (c0 (c5 c6_1) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c8)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c8)
                                    ((36767:Nat)))
                                  c7))
                              (c1 ((582:Nat)) c8))
                          (fun (x:Nat) => (1060:Nat))
                          (@AXr5285_3
                            (fun (n:Nat) =>
                              let c0_1:Nat:=c0 n ((4:Nat));
                              let c1_1:Nat:=c0 c0_1 ((1:Nat));
                              let c2:Nat→ Nat:=c1 c1_1;
                              let c3:Nat→ Nat:=c4 c1_1;
                              let c4_1:Nat:=
                                c0
                                  (c1 ((1024:Nat))
                                    (c3 ((4:Nat))))
                                  ((1:Nat));
                              let c5_1:Nat:=
                                c0
                                  (c0
                                    (c0 ((60:Nat))
                                      (c1 ((6:Nat)) c4_1))
                                    (c1 ((14:Nat)) c0_1))
                                  (c0
                                    (c0
                                      (c1 ((128:Nat))
                                        (c3 ((2:Nat))))
                                      (c5 c0_1))
                                    ((2:Nat)));
                              let c6_1:Nat:=
                                c0
                                  (c2
                                    (c0 (c5 (c0 c5_1 ((1:Nat))))
                                      ((3:Nat))))
                                  ((1:Nat));
                              let c7:Nat:=c1 c0_1 c0_1;
                              let c8:Nat:=
                                c0
                                  (c0
                                    (c0
                                      (c0
                                        (c0
                                          (c1
                                            (c0
                                              (c5
                                                (c1
                                                  (c0 (c5 c5_1)
                                                    ((1:Nat)))
                                                  c1_1))
                                              ((1:Nat)))
                                            c1_1)
                                          c7)
                                        (c5 c4_1))
                                      (c1 ((5:Nat)) c0_1))
                                    ((13:Nat)))
                                  ((1:Nat));
                              c0
                                (c0
                                  (c0
                                    (c1 (c0 (c6 c6_1) ((220:Nat)))
                                      (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c2
                                              (c0 (c5 c6_1) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0 (c1 ((2880:Nat)) c8)
                                      ((7559:Nat)))
                                    c0_1))
                                (c1
                                  (c0 (c1 ((14976:Nat)) c8)
                                    ((36767:Nat)))
                                  c7))
                            (fun (n:Nat) =>
                              let c0_1:Nat:=c0 n ((4:Nat));
                              let c1_1:Nat:=c0 c0_1 ((1:Nat));
                              let c2:Nat→ Nat:=c4 c1_1;
                              let c3:Nat:=
                                c0
                                  (c1 ((1024:Nat))
                                    (c2 ((4:Nat))))
                                  ((1:Nat));
                              c1 ((582:Nat))
                                (c0
                                  (c0
                                    (c0
                                      (c0
                                        (c0
                                          (c1
                                            (c0
                                              (c5
                                                (c1
                                                  (c0
                                                    (c5
                                                      (c0
                                                        (c0
                                                          (c0
                                                            ((60:Nat))
                                                            (c1
                                                              ((6:Nat))
                                                              c3))
                                                          (c1
                                                            ((14:Nat))
                                                            c0_1))
                                                        (c0
                                                          (c0
                                                            (c1
                                                              ((128:Nat))
                                                              (c2
                                                                ((2:Nat))))
                                                            (c5 c0_1))
                                                          ((2:Nat)))))
                                                    ((1:Nat)))
                                                  c1_1))
                                              ((1:Nat)))
                                            c1_1)
                                          (c1 c0_1 c0_1))
                                        (c5 c3))
                                      (c1 ((5:Nat)) c0_1))
                                    ((13:Nat)))
                                  ((1:Nat))))
                            (@AXr5285_3
                              (fun (n:Nat) =>
                                let c0_1:Nat:=c0 n ((4:Nat));
                                let c1_1:Nat:=c0 c0_1 ((1:Nat));
                                let c2:Nat→ Nat:=c1 c1_1;
                                let c3:Nat→ Nat:=c4 c1_1;
                                let c4_1:Nat:=
                                  c0
                                    (c1 ((1024:Nat))
                                      (c3 ((4:Nat))))
                                    ((1:Nat));
                                let c5_1:Nat:=
                                  c0
                                    (c0
                                      (c0 ((60:Nat))
                                        (c1 ((6:Nat)) c4_1))
                                      (c1 ((14:Nat)) c0_1))
                                    (c0
                                      (c0
                                        (c1 ((128:Nat))
                                          (c3 ((2:Nat))))
                                        (c5 c0_1))
                                      ((2:Nat)));
                                let c6_1:Nat:=
                                  c0
                                    (c2
                                      (c0 (c5 (c0 c5_1 ((1:Nat))))
                                        ((3:Nat))))
                                    ((1:Nat));
                                c0
                                  (c0
                                    (c1 (c0 (c6 c6_1) ((220:Nat)))
                                      (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c2
                                              (c0 (c5 c6_1) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                  (c1
                                    (c0
                                      (c1 ((2880:Nat))
                                        (c0
                                          (c0
                                            (c0
                                              (c0
                                                (c0
                                                  (c1
                                                    (c0
                                                      (c5
                                                        (c1
                                                          (c0 (c5 c5_1)
                                                            ((1:Nat)))
                                                          c1_1))
                                                      ((1:Nat)))
                                                    c1_1)
                                                  (c1 c0_1 c0_1))
                                                (c5 c4_1))
                                              (c1 ((5:Nat)) c0_1))
                                            ((13:Nat)))
                                          ((1:Nat))))
                                      ((7559:Nat)))
                                    c0_1))
                              (fun (n:Nat) =>
                                let c0_1:Nat:=c0 n ((4:Nat));
                                let c1_1:Nat:=c0 c0_1 ((1:Nat));
                                let c2:Nat→ Nat:=c4 c1_1;
                                let c3:Nat:=
                                  c0
                                    (c1 ((1024:Nat))
                                      (c2 ((4:Nat))))
                                    ((1:Nat));
                                let c4:Nat:=c1 c0_1 c0_1;
                                c1
                                  (c0
                                    (c1 ((14976:Nat))
                                      (c0
                                        (c0
                                          (c0
                                            (c0
                                              (c0
                                                (c1
                                                  (c0
                                                    (c5
                                                      (c1
                                                        (c0
                                                          (c5
                                                            (c0
                                                              (c0
                                                                (c0
                                                                  ((60:Nat))
                                                                  (c1
                                                                    ((6:Nat))
                                                                    c3))
                                                                (c1
                                                                  ((14:Nat))
                                                                  c0_1))
                                                              (c0
                                                                (c0
                                                                  (c1
                                                                    ((128:Nat))
                                                                    (c2
                                                                      ((2:Nat))))
                                                                  (c5 c0_1))
                                                                ((2:Nat)))))
                                                          ((1:Nat)))
                                                        c1_1))
                                                    ((1:Nat)))
                                                  c1_1)
                                                c4)
                                              (c5 c3))
                                            (c1 ((5:Nat)) c0_1))
                                          ((13:Nat)))
                                        ((1:Nat))))
                                    ((36767:Nat)))
                                  c4)
                              (@AXr5285_3
                                (fun (n:Nat) =>
                                  let c0_1:Nat:=c0 n ((4:Nat));
                                  let c1_1:Nat:=c0 c0_1 ((1:Nat));
                                  let c2:Nat→ Nat:=c1 c1_1;
                                  let c3:Nat→ Nat:=c4 c1_1;
                                  let c4_1:Nat:=
                                    c0
                                      (c2
                                        (c0
                                          (c5
                                            (c0
                                              (c0
                                                (c0
                                                  (c0 ((60:Nat))
                                                    (c1 ((6:Nat))
                                                      (c0
                                                        (c1
                                                          ((1024:Nat))
                                                          (c3
                                                            ((4:Nat))))
                                                        ((1:Nat)))))
                                                  (c1 ((14:Nat)) c0_1))
                                                (c0
                                                  (c0
                                                    (c1 ((128:Nat))
                                                      (c3 ((2:Nat))))
                                                    (c5 c0_1))
                                                  ((2:Nat))))
                                              ((1:Nat))))
                                          ((3:Nat))))
                                      ((1:Nat));
                                  c0
                                    (c1 (c0 (c6 c4_1) ((220:Nat)))
                                      (c4 c0_1 ((2:Nat))))
                                    (c1
                                      (c0
                                        (c6
                                          (c0
                                            (c2
                                              (c0 (c5 c4_1) ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1))
                                (fun (n:Nat) =>
                                  let c0_1:Nat:=c0 n ((4:Nat));
                                  let c1_1:Nat:=c0 c0_1 ((1:Nat));
                                  let c2:Nat→ Nat:=c4 c1_1;
                                  let c3:Nat:=
                                    c0
                                      (c1 ((1024:Nat))
                                        (c2 ((4:Nat))))
                                      ((1:Nat));
                                  c1
                                    (c0
                                      (c1 ((2880:Nat))
                                        (c0
                                          (c0
                                            (c0
                                              (c0
                                                (c0
                                                  (c1
                                                    (c0
                                                      (c5
                                                        (c1
                                                          (c0
                                                            (c5
                                                              (c0
                                                                (c0
                                                                  (c0
                                                                    ((60:Nat))
                                                                    (c1
                                                                      ((6:Nat))
                                                                      c3))
                                                                  (c1
                                                                    ((14:Nat))
                                                                    c0_1))
                                                                (c0
                                                                  (c0
                                                                    (c1
                                                                      ((128:Nat))
                                                                      (c2
                                                                        ((2:Nat))))
                                                                    (c5 c0_1))
                                                                  ((2:Nat)))))
                                                            ((1:Nat)))
                                                          c1_1))
                                                      ((1:Nat)))
                                                    c1_1)
                                                  (c1 c0_1 c0_1))
                                                (c5 c3))
                                              (c1 ((5:Nat)) c0_1))
                                            ((13:Nat)))
                                          ((1:Nat))))
                                      ((7559:Nat)))
                                    c0_1)
                                (@AXr5285_3
                                  (fun (n:Nat) =>
                                    let c0_1:Nat:=c0 n ((4:Nat));
                                    let c1_1:Nat:=c0 c0_1 ((1:Nat));
                                    let c2:Nat→ Nat:=c4 c1_1;
                                    c1
                                      (c0
                                        (c6
                                          (c0
                                            (c1 c1_1
                                              (c0
                                                (c5
                                                  (c0
                                                    (c0
                                                      (c0
                                                        (c0 ((60:Nat))
                                                          (c1 ((6:Nat))
                                                            (c0
                                                              (c1
                                                                ((1024:Nat))
                                                                (c2
                                                                  ((4:Nat))))
                                                              ((1:Nat)))))
                                                        (c1 ((14:Nat))
                                                          c0_1))
                                                      (c0
                                                        (c0
                                                          (c1
                                                            ((128:Nat))
                                                            (c2
                                                              ((2:Nat))))
                                                          (c5 c0_1))
                                                        ((2:Nat))))
                                                    ((1:Nat))))
                                                ((3:Nat))))
                                            ((1:Nat))))
                                        ((220:Nat)))
                                      (c4 c0_1 ((2:Nat))))
                                  (fun (n:Nat) =>
                                    let c0_1:Nat:=c0 n ((4:Nat));
                                    let c1_1:Nat:=c0 c0_1 ((1:Nat));
                                    let c2:Nat→ Nat:=c1 c1_1;
                                    let c3:Nat→ Nat:=c4 c1_1;
                                    c1
                                      (c0
                                        (c6
                                          (c0
                                            (c2
                                              (c0
                                                (c5
                                                  (c0
                                                    (c2
                                                      (c0
                                                        (c5
                                                          (c0
                                                            (c0
                                                              (c0
                                                                (c0
                                                                  ((60:Nat))
                                                                  (c1
                                                                    ((6:Nat))
                                                                    (c0
                                                                      (c1
                                                                        ((1024:Nat))
                                                                        (c3
                                                                          ((4:Nat))))
                                                                      ((1:Nat)))))
                                                                (c1
                                                                  ((14:Nat))
                                                                  c0_1))
                                                              (c0
                                                                (c0
                                                                  (c1
                                                                    ((128:Nat))
                                                                    (c3
                                                                      ((2:Nat))))
                                                                  (c5 c0_1))
                                                                ((2:Nat))))
                                                            ((1:Nat))))
                                                        ((3:Nat))))
                                                    ((1:Nat))))
                                                ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                      c0_1)
                                  (@c28 c11 c36 c14)
                                  (@AXr5285_4
                                    (fun (n:Nat) =>
                                      let c0_1:Nat:=c0 n ((4:Nat));
                                      let c1_1:Nat:=
                                        c0 c0_1 ((1:Nat));
                                      let c2:Nat→ Nat:=c1 c1_1;
                                      let c3:Nat→ Nat:=c4 c1_1;
                                      c0
                                        (c6
                                          (c0
                                            (c2
                                              (c0
                                                (c5
                                                  (c0
                                                    (c2
                                                      (c0
                                                        (c5
                                                          (c0
                                                            (c0
                                                              (c0
                                                                (c0
                                                                  ((60:Nat))
                                                                  (c1
                                                                    ((6:Nat))
                                                                    (c0
                                                                      (c1
                                                                        ((1024:Nat))
                                                                        (c3
                                                                          ((4:Nat))))
                                                                      ((1:Nat)))))
                                                                (c1
                                                                  ((14:Nat))
                                                                  c0_1))
                                                              (c0
                                                                (c0
                                                                  (c1
                                                                    ((128:Nat))
                                                                    (c3
                                                                      ((2:Nat))))
                                                                  (c5 c0_1))
                                                                ((2:Nat))))
                                                            ((1:Nat))))
                                                        ((3:Nat))))
                                                    ((1:Nat))))
                                                ((3:Nat))))
                                            ((1:Nat))))
                                        ((292:Nat)))
                                    c12
                                    (@AXr5285_3
                                      (fun (n:Nat) =>
                                        let c0_1:Nat:=
                                          c0 n ((4:Nat));
                                        let c1_1:Nat:=
                                          c0 c0_1 ((1:Nat));
                                        let c2:Nat→ Nat:=c1 c1_1;
                                        let c3:Nat→ Nat:=c4 c1_1;
                                        c6
                                          (c0
                                            (c2
                                              (c0
                                                (c5
                                                  (c0
                                                    (c2
                                                      (c0
                                                        (c5
                                                          (c0
                                                            (c0
                                                              (c0
                                                                (c0
                                                                  ((60:Nat))
                                                                  (c1
                                                                    ((6:Nat))
                                                                    (c0
                                                                      (c1
                                                                        ((1024:Nat))
                                                                        (c3
                                                                          ((4:Nat))))
                                                                      ((1:Nat)))))
                                                                (c1
                                                                  ((14:Nat))
                                                                  c0_1))
                                                              (c0
                                                                (c0
                                                                  (c1
                                                                    ((128:Nat))
                                                                    (c3
                                                                      ((2:Nat))))
                                                                  (c5 c0_1))
                                                                ((2:Nat))))
                                                            ((1:Nat))))
                                                        ((3:Nat))))
                                                    ((1:Nat))))
                                                ((3:Nat))))
                                            ((1:Nat))))
                                      (fun (x:Nat) => (292:Nat))
                                      (@c29
                                        (fun (n:Nat) =>
                                          let c0_1:Nat:=
                                            c0 n ((4:Nat));
                                          let c1_1:Nat:=
                                            c0 c0_1 ((1:Nat));
                                          let c2:Nat→ Nat:=c1 c1_1;
                                          let c3:Nat→ Nat:=c4 c1_1;
                                          c0
                                            (c2
                                              (c0
                                                (c5
                                                  (c0
                                                    (c2
                                                      (c0
                                                        (c5
                                                          (c0
                                                            (c0
                                                              (c0
                                                                (c0
                                                                  ((60:Nat))
                                                                  (c1
                                                                    ((6:Nat))
                                                                    (c0
                                                                      (c1
                                                                        ((1024:Nat))
                                                                        (c3
                                                                          ((4:Nat))))
                                                                      ((1:Nat)))))
                                                                (c1
                                                                  ((14:Nat))
                                                                  c0_1))
                                                              (c0
                                                                (c0
                                                                  (c1
                                                                    ((128:Nat))
                                                                    (c3
                                                                      ((2:Nat))))
                                                                  (c5 c0_1))
                                                                ((2:Nat))))
                                                            ((1:Nat))))
                                                        ((3:Nat))))
                                                    ((1:Nat))))
                                                ((3:Nat))))
                                            ((1:Nat)))
                                        (AXr5285_1
                                          ((144:Nat)))
                                        (@AXr5285_3
                                          (fun (n:Nat) =>
                                            let c0_1:Nat:=
                                              c0 n ((4:Nat));
                                            let c1_1:Nat:=
                                              c0 c0_1 ((1:Nat));
                                            let c2:Nat→ Nat:=c1 c1_1;
                                            let c3:Nat→ Nat:=c4 c1_1;
                                            c2
                                              (c0
                                                (c5
                                                  (c0
                                                    (c2
                                                      (c0
                                                        (c5
                                                          (c0
                                                            (c0
                                                              (c0
                                                                (c0
                                                                  ((60:Nat))
                                                                  (c1
                                                                    ((6:Nat))
                                                                    (c0
                                                                      (c1
                                                                        ((1024:Nat))
                                                                        (c3
                                                                          ((4:Nat))))
                                                                      ((1:Nat)))))
                                                                (c1
                                                                  ((14:Nat))
                                                                  c0_1))
                                                              (c0
                                                                (c0
                                                                  (c1
                                                                    ((128:Nat))
                                                                    (c3
                                                                      ((2:Nat))))
                                                                  (c5 c0_1))
                                                                ((2:Nat))))
                                                            ((1:Nat))))
                                                        ((3:Nat))))
                                                    ((1:Nat))))
                                                ((3:Nat))))
                                          (fun (x:Nat) => (1:Nat))
                                          (@c31
                                            (fun (n:Nat) =>
                                              let c0_1:Nat:=
                                                c0 n ((4:Nat));
                                              let c1_1:Nat:=
                                                c0 c0_1 ((1:Nat));
                                              let c2:Nat→ Nat:=c4 c1_1;
                                              c0
                                                (c5
                                                  (c0
                                                    (c1 c1_1
                                                      (c0
                                                        (c5
                                                          (c0
                                                            (c0
                                                              (c0
                                                                (c0
                                                                  ((60:Nat))
                                                                  (c1
                                                                    ((6:Nat))
                                                                    (c0
                                                                      (c1
                                                                        ((1024:Nat))
                                                                        (c2
                                                                          ((4:Nat))))
                                                                      ((1:Nat)))))
                                                                (c1
                                                                  ((14:Nat))
                                                                  c0_1))
                                                              (c0
                                                                (c0
                                                                  (c1
                                                                    ((128:Nat))
                                                                    (c2
                                                                      ((2:Nat))))
                                                                  (c5 c0_1))
                                                                ((2:Nat))))
                                                            ((1:Nat))))
                                                        ((3:Nat))))
                                                    ((1:Nat))))
                                                ((3:Nat)))
                                            c17
                                            (@AXr5285_3
                                              (fun (n:Nat) =>
                                                let c0_1:Nat:=
                                                  c0 n ((4:Nat));
                                                let c1_1:Nat:=
                                                  c0 c0_1 ((1:Nat));
                                                let c2:Nat→ Nat:=c4 c1_1;
                                                c5
                                                  (c0
                                                    (c1 c1_1
                                                      (c0
                                                        (c5
                                                          (c0
                                                            (c0
                                                              (c0
                                                                (c0
                                                                  ((60:Nat))
                                                                  (c1
                                                                    ((6:Nat))
                                                                    (c0
                                                                      (c1
                                                                        ((1024:Nat))
                                                                        (c2
                                                                          ((4:Nat))))
                                                                      ((1:Nat)))))
                                                                (c1
                                                                  ((14:Nat))
                                                                  c0_1))
                                                              (c0
                                                                (c0
                                                                  (c1
                                                                    ((128:Nat))
                                                                    (c2
                                                                      ((2:Nat))))
                                                                  (c5 c0_1))
                                                                ((2:Nat))))
                                                            ((1:Nat))))
                                                        ((3:Nat))))
                                                    ((1:Nat))))
                                              (fun (x:Nat) => (3:Nat))
                                              (@c23 c30
                                                (AXr5285_1
                                                  ((2:Nat)))
                                                c35)
                                              (AXr5285_1
                                                ((3:Nat)))))
                                          (AXr5285_1
                                            ((1:Nat)))))
                                      (AXr5285_1
                                        ((292:Nat))))
                                    c13))
                                (@AXr5285_4
                                  (fun (n:Nat) =>
                                    let c0_1:Nat:=c0 n ((4:Nat));
                                    let c1_1:Nat:=c0 c0_1 ((1:Nat));
                                    let c2:Nat→ Nat:=c4 c1_1;
                                    let c3:Nat:=
                                      c0
                                        (c1 ((1024:Nat))
                                          (c2 ((4:Nat))))
                                        ((1:Nat));
                                    c0
                                      (c1 ((2880:Nat))
                                        (c0
                                          (c0
                                            (c0
                                              (c0
                                                (c0
                                                  (c1
                                                    (c0
                                                      (c5
                                                        (c1
                                                          (c0
                                                            (c5
                                                              (c0
                                                                (c0
                                                                  (c0
                                                                    ((60:Nat))
                                                                    (c1
                                                                      ((6:Nat))
                                                                      c3))
                                                                  (c1
                                                                    ((14:Nat))
                                                                    c0_1))
                                                                (c0
                                                                  (c0
                                                                    (c1
                                                                      ((128:Nat))
                                                                      (c2
                                                                        ((2:Nat))))
                                                                    (c5 c0_1))
                                                                  ((2:Nat)))))
                                                            ((1:Nat)))
                                                          c1_1))
                                                      ((1:Nat)))
                                                    c1_1)
                                                  (c1 c0_1 c0_1))
                                                (c5 c3))
                                              (c1 ((5:Nat)) c0_1))
                                            ((13:Nat)))
                                          ((1:Nat))))
                                      ((7559:Nat)))
                                  c12
                                  (@AXr5285_3
                                    (fun (n:Nat) =>
                                      let c0_1:Nat:=c0 n ((4:Nat));
                                      let c1_1:Nat:=
                                        c0 c0_1 ((1:Nat));
                                      let c2:Nat→ Nat:=c4 c1_1;
                                      let c3:Nat:=
                                        c0
                                          (c1 ((1024:Nat))
                                            (c2 ((4:Nat))))
                                          ((1:Nat));
                                      c1 ((2880:Nat))
                                        (c0
                                          (c0
                                            (c0
                                              (c0
                                                (c0
                                                  (c1
                                                    (c0
                                                      (c5
                                                        (c1
                                                          (c0
                                                            (c5
                                                              (c0
                                                                (c0
                                                                  (c0
                                                                    ((60:Nat))
                                                                    (c1
                                                                      ((6:Nat))
                                                                      c3))
                                                                  (c1
                                                                    ((14:Nat))
                                                                    c0_1))
                                                                (c0
                                                                  (c0
                                                                    (c1
                                                                      ((128:Nat))
                                                                      (c2
                                                                        ((2:Nat))))
                                                                    (c5 c0_1))
                                                                  ((2:Nat)))))
                                                            ((1:Nat)))
                                                          c1_1))
                                                      ((1:Nat)))
                                                    c1_1)
                                                  (c1 c0_1 c0_1))
                                                (c5 c3))
                                              (c1 ((5:Nat)) c0_1))
                                            ((13:Nat)))
                                          ((1:Nat))))
                                    (fun (x:Nat) => (7559:Nat))
                                    (@AXr5285_4
                                      (fun (x:Nat) => (2880:Nat))
                                      c37
                                      (AXr5285_1
                                        ((2880:Nat)))
                                      c38)
                                    (AXr5285_1
                                      ((7559:Nat))))
                                  c13))
                              (@AXr5285_4
                                (fun (n:Nat) =>
                                  let c0_1:Nat:=c0 n ((4:Nat));
                                  let c1_1:Nat:=c0 c0_1 ((1:Nat));
                                  let c2:Nat→ Nat:=c4 c1_1;
                                  let c3:Nat:=
                                    c0
                                      (c1 ((1024:Nat))
                                        (c2 ((4:Nat))))
                                      ((1:Nat));
                                  c0
                                    (c1 ((14976:Nat))
                                      (c0
                                        (c0
                                          (c0
                                            (c0
                                              (c0
                                                (c1
                                                  (c0
                                                    (c5
                                                      (c1
                                                        (c0
                                                          (c5
                                                            (c0
                                                              (c0
                                                                (c0
                                                                  ((60:Nat))
                                                                  (c1
                                                                    ((6:Nat))
                                                                    c3))
                                                                (c1
                                                                  ((14:Nat))
                                                                  c0_1))
                                                              (c0
                                                                (c0
                                                                  (c1
                                                                    ((128:Nat))
                                                                    (c2
                                                                      ((2:Nat))))
                                                                  (c5 c0_1))
                                                                ((2:Nat)))))
                                                          ((1:Nat)))
                                                        c1_1))
                                                    ((1:Nat)))
                                                  c1_1)
                                                (c1 c0_1 c0_1))
                                              (c5 c3))
                                            (c1 ((5:Nat)) c0_1))
                                          ((13:Nat)))
                                        ((1:Nat))))
                                    ((36767:Nat)))
                                c20
                                (@AXr5285_3
                                  (fun (n:Nat) =>
                                    let c0_1:Nat:=c0 n ((4:Nat));
                                    let c1_1:Nat:=c0 c0_1 ((1:Nat));
                                    let c2:Nat→ Nat:=c4 c1_1;
                                    let c3:Nat:=
                                      c0
                                        (c1 ((1024:Nat))
                                          (c2 ((4:Nat))))
                                        ((1:Nat));
                                    c1 ((14976:Nat))
                                      (c0
                                        (c0
                                          (c0
                                            (c0
                                              (c0
                                                (c1
                                                  (c0
                                                    (c5
                                                      (c1
                                                        (c0
                                                          (c5
                                                            (c0
                                                              (c0
                                                                (c0
                                                                  ((60:Nat))
                                                                  (c1
                                                                    ((6:Nat))
                                                                    c3))
                                                                (c1
                                                                  ((14:Nat))
                                                                  c0_1))
                                                              (c0
                                                                (c0
                                                                  (c1
                                                                    ((128:Nat))
                                                                    (c2
                                                                      ((2:Nat))))
                                                                  (c5 c0_1))
                                                                ((2:Nat)))))
                                                          ((1:Nat)))
                                                        c1_1))
                                                    ((1:Nat)))
                                                  c1_1)
                                                (c1 c0_1 c0_1))
                                              (c5 c3))
                                            (c1 ((5:Nat)) c0_1))
                                          ((13:Nat)))
                                        ((1:Nat))))
                                  (fun (x:Nat) => (36767:Nat))
                                  (@AXr5285_4
                                    (fun (x:Nat) => (14976:Nat))
                                    c37
                                    (AXr5285_1
                                      ((14976:Nat)))
                                    c38)
                                  (AXr5285_1
                                    ((36767:Nat))))
                                c26))
                            (@AXr5285_4
                              (fun (x:Nat) => (582:Nat)) c37
                              (AXr5285_1
                                ((582:Nat)))
                              c38))
                          (AXr5285_1
                            ((1060:Nat))))
                        (@c10 c12
                          (AXr5285_1
                            ((71:Nat)))
                          c13))
                      (@c10 c20
                        (AXr5285_1
                          ((71:Nat)))
                        c26)))
                  (AXr5285_1
                    ((103:Nat))))
                (AXr5285_1
                  ((4:Nat))))
              c33))
          (AXr5285_1
            ((64:Nat)))))))

noncomputable abbrev _root_.AXr5287_0:= @Lax109476Proofs.RamResourcePolynomial.HasPolynomial
noncomputable abbrev _root_.AXr5287_1:= @Lax109476Proofs.RamResourcePolynomial.constant
noncomputable abbrev _root_.AXr5287_2:= @Lax109476Proofs.RamResourcePolynomial.add
noncomputable abbrev _root_.AXr5287_3:= @Lax109476Proofs.RamResourcePolynomial.mul
theorem reconstruction_cost:AXr5287_0 Lax109476Proofs.RamRationalReconstruction.instructionBound:=
let c0:Nat→ Nat→ Nat:=Nat.add;
let c1:Nat→ Nat→ Nat:=Nat.mul;
let c2:Nat→ Nat:=fun (n:Nat) =>
  c0
    (c1 ((2:Nat))
      (c0 n ((1:Nat))))
    ((1:Nat));
let c3:Nat→ Nat:=fun (n:Nat) => c0 n ((1:Nat));
let c4:
  AXr5287_0 fun (n:Nat) =>
    Nat.add n ((1:Nat)):=
  @AXr5287_2 (fun (n:Nat) => n)
    (fun (x:Nat) => (1:Nat))
    Lax109476Proofs.RamResourcePolynomial.identity
    (AXr5287_1 ((1:Nat)));
let c5:
  ∀ {g:Nat→ Nat},
    AXr5287_0 c2→
      AXr5287_0 g→
        AXr5287_0 fun (n:Nat) =>
          Nat.add (c2 n) (g n):=
  @AXr5287_2 c2;
let c6:
  AXr5287_0 fun (n:Nat) =>
    Nat.add
      (c1 ((2:Nat))
        (c0 n ((1:Nat))))
      ((1:Nat)):=
  @AXr5287_2
    (fun (n:Nat) =>
      c1 ((2:Nat))
        (c0 n ((1:Nat))))
    (fun (x:Nat) => (1:Nat))
    (@AXr5287_3
      (fun (x:Nat) => (2:Nat)) c3
      (AXr5287_1 ((2:Nat))) c4)
    (AXr5287_1 ((1:Nat)));
@AXr5287_2
  (fun (n:Nat) =>
    let c0_1:Nat:=c0 n ((1:Nat));
    let c1_1:Nat:=
      c0 (c1 ((2:Nat)) c0_1)
        ((1:Nat));
    let c2:Nat→ Nat:=c0 c1_1;
    c0
      (c1
        (c0
          (c0
            (c1
              (c0
                (c0 (c1 ((36:Nat)) c0_1)
                  ((113:Nat)))
                (c0
                  (c1 ((108:Nat))
                    (c0 (c1 c0_1 (c2 ((2:Nat))))
                      ((1:Nat))))
                  ((208:Nat))))
              (c2 ((1:Nat))))
            ((22:Nat)))
          ((156:Nat)))
        c1_1)
      (c1 ((12:Nat)) c0_1))
  (fun (x:Nat) => (22:Nat))
  (@AXr5287_2
    (fun (n:Nat) =>
      let c0_1:Nat:=c0 n ((1:Nat));
      let c1_1:Nat:=
        c0 (c1 ((2:Nat)) c0_1)
          ((1:Nat));
      let c2:Nat→ Nat:=c0 c1_1;
      c1
        (c0
          (c0
            (c1
              (c0
                (c0 (c1 ((36:Nat)) c0_1)
                  ((113:Nat)))
                (c0
                  (c1 ((108:Nat))
                    (c0 (c1 c0_1 (c2 ((2:Nat))))
                      ((1:Nat))))
                  ((208:Nat))))
              (c2 ((1:Nat))))
            ((22:Nat)))
          ((156:Nat)))
        c1_1)
    (fun (n:Nat) =>
      c1 ((12:Nat))
        (c0 n ((1:Nat))))
    (@AXr5287_3
      (fun (n:Nat) =>
        let c0_1:Nat:=c0 n ((1:Nat));
        let c1_1:Nat→ Nat:=
          c0
            (c0 (c1 ((2:Nat)) c0_1)
              ((1:Nat)));
        c0
          (c0
            (c1
              (c0
                (c0 (c1 ((36:Nat)) c0_1)
                  ((113:Nat)))
                (c0
                  (c1 ((108:Nat))
                    (c0 (c1 c0_1 (c1_1 ((2:Nat))))
                      ((1:Nat))))
                  ((208:Nat))))
              (c1_1 ((1:Nat))))
            ((22:Nat)))
          ((156:Nat)))
      c2
      (@AXr5287_2
        (fun (n:Nat) =>
          let c0_1:Nat:=c0 n ((1:Nat));
          let c1_1:Nat→ Nat:=
            c0
              (c0 (c1 ((2:Nat)) c0_1)
                ((1:Nat)));
          c0
            (c1
              (c0
                (c0 (c1 ((36:Nat)) c0_1)
                  ((113:Nat)))
                (c0
                  (c1 ((108:Nat))
                    (c0 (c1 c0_1 (c1_1 ((2:Nat))))
                      ((1:Nat))))
                  ((208:Nat))))
              (c1_1 ((1:Nat))))
            ((22:Nat)))
        (fun (x:Nat) => (156:Nat))
        (@AXr5287_2
          (fun (n:Nat) =>
            let c0_1:Nat:=c0 n ((1:Nat));
            let c1_1:Nat→ Nat:=
              c0
                (c0 (c1 ((2:Nat)) c0_1)
                  ((1:Nat)));
            c1
              (c0
                (c0 (c1 ((36:Nat)) c0_1)
                  ((113:Nat)))
                (c0
                  (c1 ((108:Nat))
                    (c0 (c1 c0_1 (c1_1 ((2:Nat))))
                      ((1:Nat))))
                  ((208:Nat))))
              (c1_1 ((1:Nat))))
          (fun (x:Nat) => (22:Nat))
          (@AXr5287_3
            (fun (n:Nat) =>
              let c0_1:Nat:=c0 n ((1:Nat));
              c0
                (c0 (c1 ((36:Nat)) c0_1)
                  ((113:Nat)))
                (c0
                  (c1 ((108:Nat))
                    (c0
                      (c1 c0_1
                        (c0
                          (c0 (c1 ((2:Nat)) c0_1)
                            ((1:Nat)))
                          ((2:Nat))))
                      ((1:Nat))))
                  ((208:Nat))))
            (fun (n:Nat) =>
              c0
                (c0
                  (c1 ((2:Nat))
                    (c0 n ((1:Nat))))
                  ((1:Nat)))
                ((1:Nat)))
            (@AXr5287_2
              (fun (n:Nat) =>
                c0
                  (c1 ((36:Nat))
                    (c0 n ((1:Nat))))
                  ((113:Nat)))
              (fun (n:Nat) =>
                let c0_1:Nat:=c0 n ((1:Nat));
                c0
                  (c1 ((108:Nat))
                    (c0
                      (c1 c0_1
                        (c0
                          (c0 (c1 ((2:Nat)) c0_1)
                            ((1:Nat)))
                          ((2:Nat))))
                      ((1:Nat))))
                  ((208:Nat)))
              (@AXr5287_2
                (fun (n:Nat) =>
                  c1 ((36:Nat))
                    (c0 n ((1:Nat))))
                (fun (x:Nat) => (113:Nat))
                (@AXr5287_3
                  (fun (x:Nat) => (36:Nat)) c3
                  (AXr5287_1
                    ((36:Nat)))
                  c4)
                (AXr5287_1
                  ((113:Nat))))
              (@AXr5287_2
                (fun (n:Nat) =>
                  let c0_1:Nat:=c0 n ((1:Nat));
                  c1 ((108:Nat))
                    (c0
                      (c1 c0_1
                        (c0
                          (c0 (c1 ((2:Nat)) c0_1)
                            ((1:Nat)))
                          ((2:Nat))))
                      ((1:Nat))))
                (fun (x:Nat) => (208:Nat))
                (@AXr5287_3
                  (fun (x:Nat) => (108:Nat))
                  (fun (n:Nat) =>
                    let c0_1:Nat:=c0 n ((1:Nat));
                    c0
                      (c1 c0_1
                        (c0
                          (c0 (c1 ((2:Nat)) c0_1)
                            ((1:Nat)))
                          ((2:Nat))))
                      ((1:Nat)))
                  (AXr5287_1
                    ((108:Nat)))
                  (@AXr5287_2
                    (fun (n:Nat) =>
                      let c0_1:Nat:=c0 n ((1:Nat));
                      c1 c0_1
                        (c0
                          (c0 (c1 ((2:Nat)) c0_1)
                            ((1:Nat)))
                          ((2:Nat))))
                    (fun (x:Nat) => (1:Nat))
                    (@AXr5287_3 c3
                      (fun (n:Nat) =>
                        c0
                          (c0
                            (c1 ((2:Nat))
                              (c0 n ((1:Nat))))
                            ((1:Nat)))
                          ((2:Nat)))
                      c4
                      (@c5 (fun (x:Nat) => (2:Nat)) c6
                        (AXr5287_1
                          ((2:Nat)))))
                    (AXr5287_1
                      ((1:Nat)))))
                (AXr5287_1
                  ((208:Nat)))))
            (@c5 (fun (x:Nat) => (1:Nat)) c6
              (AXr5287_1
                ((1:Nat)))))
          (AXr5287_1 ((22:Nat))))
        (AXr5287_1 ((156:Nat))))
      c6)
    (@AXr5287_3
      (fun (x:Nat) => (12:Nat)) c3
      (AXr5287_1 ((12:Nat))) c4))
  (AXr5287_1 ((22:Nat)))

noncomputable abbrev _root_.AXr5289_0:= @Lax109476Proofs.RamRationalReconstruction.instructionBound
noncomputable abbrev _root_.AXr5289_1:= @Lax109476Proofs.RamStoredFeasibility.instructionBound
noncomputable abbrev _root_.AXr5289_2:= @Lax109476Proofs.RamResourcePolynomial.HasPolynomial
noncomputable abbrev _root_.AXr5289_3:= @Lax109476Proofs.RamResourcePolynomial.constant
noncomputable abbrev _root_.AXr5289_4:= @Lax109476Proofs.RamResourcePolynomial.identity
noncomputable abbrev _root_.AXr5289_5:= @Lax109476Proofs.RamResourcePolynomial.add
noncomputable abbrev _root_.AXr5289_6:= @Lax109476Proofs.RamResourcePolynomial.mul
theorem recovery_cost:AXr5289_2 fun (S:Nat) =>
  Lax109476Proofs.RamRecoverFeasibleSystem.instructionBound S S S:=
let c0:Nat→ Nat→ Nat:=Nat.add;
let c1:Nat→ Nat→ Nat:=Nat.mul;
let c2:Nat→ Nat:=c1 ((2:Nat));
let c3:Nat→ Nat:=fun (n:Nat) => c1 ((33:Nat)) (c0 n n);
let c4:Nat→ Nat:=fun (n:Nat) => c0 n n;
let c5:
  AXr5289_2 fun (n:Nat) =>
    Nat.add n n:=
  @AXr5289_5 (fun (n:Nat) => n) (fun (n:Nat) => n)
    AXr5289_4 AXr5289_4;
let c6:
  AXr5289_2 fun (n:Nat) =>
    Nat.mul ((33:Nat))
      (c4 n):=
  @AXr5289_6
    (fun (x:Nat) => (33:Nat)) c4
    (AXr5289_3 ((33:Nat))) c5;
let c7:Nat→ Nat:=fun (n:Nat) =>
  c0
    (c0
      (c1 ((4:Nat))
        (c1 ((32:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (c0 n ((1:Nat)))
            ((2:Nat)))))
      (c2 n))
    ((2:Nat));
let c8:Nat→ Nat:=fun (n:Nat) =>
  c1 ((32:Nat))
    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
      (c0 n ((1:Nat)))
      ((2:Nat)));
let c9:
  AXr5289_2 fun (n:Nat) =>
    Nat.mul ((32:Nat))
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        (c0 n ((1:Nat)))
        ((2:Nat))):=
  @AXr5289_6
    (fun (x:Nat) => (32:Nat))
    (fun (n:Nat) =>
      @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        (c0 n ((1:Nat)))
        ((2:Nat)))
    (AXr5289_3 ((32:Nat)))
    (@Lax109476Proofs.RamResourcePolynomial.pow
      (fun (n:Nat) => c0 n ((1:Nat)))
      (@AXr5289_5 (fun (n:Nat) => n)
        (fun (x:Nat) => (1:Nat))
        AXr5289_4
        (AXr5289_3 ((1:Nat))))
      ((2:Nat)));
let c10:
  ∀ {g:Nat→ Nat},
    (AXr5289_2 fun (x:Nat) =>
        (2:Nat))→
      AXr5289_2 g→
        AXr5289_2 fun (n:Nat) =>
          Nat.mul ((2:Nat))
            (g n):=
  @AXr5289_6 fun (x:Nat) => (2:Nat);
let c11:
  AXr5289_2 fun (n:Nat) =>
    Nat.add
      (c0
        (c1 ((4:Nat))
          (c1 ((32:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (c0 n ((1:Nat)))
              ((2:Nat)))))
        (c2 n))
      ((2:Nat)):=
  @AXr5289_5
    (fun (n:Nat) =>
      c0
        (c1 ((4:Nat))
          (c1 ((32:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (c0 n ((1:Nat)))
              ((2:Nat)))))
        (c2 n))
    (fun (x:Nat) => (2:Nat))
    (@AXr5289_5
      (fun (n:Nat) =>
        c1 ((4:Nat))
          (c1 ((32:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (c0 n ((1:Nat)))
              ((2:Nat)))))
      (fun (n:Nat) => c2 n)
      (@AXr5289_6
        (fun (x:Nat) => (4:Nat)) c8
        (AXr5289_3 ((4:Nat))) c9)
      (@c10 (fun (n:Nat) => n)
        (AXr5289_3 ((2:Nat)))
        AXr5289_4))
    (AXr5289_3 ((2:Nat)));
let c12:Nat→ Nat:=fun (n:Nat) =>
  c1 (c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat))) (c0 n n);
let c13:Nat→ Nat:=fun (n:Nat) =>
  c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat));
let c14:
  ∀ {g:Nat→ Nat},
    AXr5289_2 c4→
      AXr5289_2 g→
        AXr5289_2 fun (n:Nat) =>
          Nat.add (c4 n) (g n):=
  @AXr5289_5 c4;
let c15:
  AXr5289_2 fun (n:Nat) =>
    Nat.add (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
      ((1:Nat)):=
  @AXr5289_5 (fun (n:Nat) => c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
    (fun (x:Nat) => (1:Nat))
    (@c14 (fun (n:Nat) => c0 (c0 n n) (c0 n n)) c5 (@c14 c4 c5 c5))
    (AXr5289_3 ((1:Nat)));
let c16:
  AXr5289_2 fun (n:Nat) =>
    Nat.mul (c13 n) (c4 n):=
  @AXr5289_6 c13 c4 c15 c5;
@AXr5289_5
  (fun (n:Nat) =>
    c0
      (c0
        (c0
          (c0 (c1 ((118:Nat)) (c1 (c0 n n) (c0 n n)))
            (c1 ((91:Nat)) (c0 n n)))
          (c1 ((33:Nat)) (c0 n n)))
        (c1 ((48:Nat)) n))
      ((192:Nat)))
  (fun (n:Nat) =>
    let c0_1:Nat:=
      c1 ((32:Nat))
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          (c0 n ((1:Nat)))
          ((2:Nat)));
    let c1_1:Nat:=
      c0 (c0 (c1 ((4:Nat)) c0_1) (c2 n))
        ((2:Nat));
    let c2_1:Nat:=c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat));
    let c3:Nat:=c1 c2_1 (c0 n n);
    c0
      (c1
        (c0
          (c0
            (c0
              (c1
                (c0
                  (c0
                    (c1 ((144:Nat))
                      (c0 c1_1 ((1:Nat))))
                    ((342:Nat)))
                  (c0
                    (c0
                      (c0
                        (c0 (c1 ((142:Nat)) c3)
                          (c1 ((138:Nat)) c2_1))
                        (c1 ((33:Nat)) (c0 n n)))
                      ((106:Nat)))
                    (AXr5289_1
                      (c0 (c0 (c0 c2_1 (c0 n n)) ((2:Nat)))
                        (c1 (c0 (c0 c3 c2_1) (c0 n n))
                          (c0 ((4:Nat))
                            (c2 (c0 (c2 c1_1) ((3:Nat))))))))))
                (c0 (c1 ((3:Nat)) c0_1)
                  ((2:Nat))))
              (c1 ((12:Nat)) c0_1))
            (AXr5289_0 c1_1))
          ((77:Nat)))
        (c0 n n))
      ((6:Nat)))
  (@AXr5289_5
    (fun (n:Nat) =>
      c0
        (c0
          (c0 (c1 ((118:Nat)) (c1 (c0 n n) (c0 n n)))
            (c1 ((91:Nat)) (c0 n n)))
          (c1 ((33:Nat)) (c0 n n)))
        (c1 ((48:Nat)) n))
    (fun (x:Nat) => (192:Nat))
    (@AXr5289_5
      (fun (n:Nat) =>
        c0
          (c0 (c1 ((118:Nat)) (c1 (c0 n n) (c0 n n)))
            (c1 ((91:Nat)) (c0 n n)))
          (c1 ((33:Nat)) (c0 n n)))
      (fun (n:Nat) => c1 ((48:Nat)) n)
      (@AXr5289_5
        (fun (n:Nat) =>
          c0 (c1 ((118:Nat)) (c1 (c0 n n) (c0 n n)))
            (c1 ((91:Nat)) (c0 n n)))
        c3
        (@AXr5289_5
          (fun (n:Nat) => c1 ((118:Nat)) (c1 (c0 n n) (c0 n n)))
          (fun (n:Nat) => c1 ((91:Nat)) (c0 n n))
          (@AXr5289_6
            (fun (x:Nat) => (118:Nat))
            (fun (n:Nat) => c1 (c0 n n) (c0 n n))
            (AXr5289_3
              ((118:Nat)))
            (@AXr5289_6 c4 c4 c5 c5))
          (@AXr5289_6
            (fun (x:Nat) => (91:Nat)) c4
            (AXr5289_3 ((91:Nat)))
            c5))
        c6)
      (@AXr5289_6
        (fun (x:Nat) => (48:Nat)) (fun (n:Nat) => n)
        (AXr5289_3 ((48:Nat)))
        AXr5289_4))
    (AXr5289_3 ((192:Nat))))
  (@AXr5289_5
    (fun (n:Nat) =>
      let c0_1:Nat:=
        c1 ((32:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (c0 n ((1:Nat)))
            ((2:Nat)));
      let c1_1:Nat:=
        c0 (c0 (c1 ((4:Nat)) c0_1) (c2 n))
          ((2:Nat));
      let c2_1:Nat:=
        c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat));
      let c3:Nat:=c1 c2_1 (c0 n n);
      c1
        (c0
          (c0
            (c0
              (c1
                (c0
                  (c0
                    (c1 ((144:Nat))
                      (c0 c1_1 ((1:Nat))))
                    ((342:Nat)))
                  (c0
                    (c0
                      (c0
                        (c0 (c1 ((142:Nat)) c3)
                          (c1 ((138:Nat)) c2_1))
                        (c1 ((33:Nat)) (c0 n n)))
                      ((106:Nat)))
                    (AXr5289_1
                      (c0 (c0 (c0 c2_1 (c0 n n)) ((2:Nat)))
                        (c1 (c0 (c0 c3 c2_1) (c0 n n))
                          (c0 ((4:Nat))
                            (c2 (c0 (c2 c1_1) ((3:Nat))))))))))
                (c0 (c1 ((3:Nat)) c0_1)
                  ((2:Nat))))
              (c1 ((12:Nat)) c0_1))
            (AXr5289_0 c1_1))
          ((77:Nat)))
        (c0 n n))
    (fun (x:Nat) => (6:Nat))
    (@AXr5289_6
      (fun (n:Nat) =>
        let c0_1:Nat:=
          c1 ((32:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (c0 n ((1:Nat)))
              ((2:Nat)));
        let c1_1:Nat:=
          c0 (c0 (c1 ((4:Nat)) c0_1) (c2 n))
            ((2:Nat));
        let c2_1:Nat:=
          c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat));
        let c3:Nat:=c1 c2_1 (c0 n n);
        c0
          (c0
            (c0
              (c1
                (c0
                  (c0
                    (c1 ((144:Nat))
                      (c0 c1_1 ((1:Nat))))
                    ((342:Nat)))
                  (c0
                    (c0
                      (c0
                        (c0 (c1 ((142:Nat)) c3)
                          (c1 ((138:Nat)) c2_1))
                        (c1 ((33:Nat)) (c0 n n)))
                      ((106:Nat)))
                    (AXr5289_1
                      (c0 (c0 (c0 c2_1 (c0 n n)) ((2:Nat)))
                        (c1 (c0 (c0 c3 c2_1) (c0 n n))
                          (c0 ((4:Nat))
                            (c2 (c0 (c2 c1_1) ((3:Nat))))))))))
                (c0 (c1 ((3:Nat)) c0_1)
                  ((2:Nat))))
              (c1 ((12:Nat)) c0_1))
            (AXr5289_0 c1_1))
          ((77:Nat)))
      c4
      (@AXr5289_5
        (fun (n:Nat) =>
          let c0_1:Nat:=
            c1 ((32:Nat))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (c0 n ((1:Nat)))
                ((2:Nat)));
          let c1_1:Nat:=
            c0 (c0 (c1 ((4:Nat)) c0_1) (c2 n))
              ((2:Nat));
          let c2_1:Nat:=
            c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat));
          let c3:Nat:=c1 c2_1 (c0 n n);
          c0
            (c0
              (c1
                (c0
                  (c0
                    (c1 ((144:Nat))
                      (c0 c1_1 ((1:Nat))))
                    ((342:Nat)))
                  (c0
                    (c0
                      (c0
                        (c0 (c1 ((142:Nat)) c3)
                          (c1 ((138:Nat)) c2_1))
                        (c1 ((33:Nat)) (c0 n n)))
                      ((106:Nat)))
                    (AXr5289_1
                      (c0 (c0 (c0 c2_1 (c0 n n)) ((2:Nat)))
                        (c1 (c0 (c0 c3 c2_1) (c0 n n))
                          (c0 ((4:Nat))
                            (c2 (c0 (c2 c1_1) ((3:Nat))))))))))
                (c0 (c1 ((3:Nat)) c0_1)
                  ((2:Nat))))
              (c1 ((12:Nat)) c0_1))
            (AXr5289_0 c1_1))
        (fun (x:Nat) => (77:Nat))
        (@AXr5289_5
          (fun (n:Nat) =>
            let c0_1:Nat:=
              c1 ((32:Nat))
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (c0 n ((1:Nat)))
                  ((2:Nat)));
            let c1_1:Nat:=
              c0 (c0 (c1 ((4:Nat)) c0_1) (c2 n))
                ((2:Nat));
            let c2_1:Nat:=
              c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat));
            let c3:Nat:=c1 c2_1 (c0 n n);
            c0
              (c1
                (c0
                  (c0
                    (c1 ((144:Nat))
                      (c0 c1_1 ((1:Nat))))
                    ((342:Nat)))
                  (c0
                    (c0
                      (c0
                        (c0 (c1 ((142:Nat)) c3)
                          (c1 ((138:Nat)) c2_1))
                        (c1 ((33:Nat)) (c0 n n)))
                      ((106:Nat)))
                    (AXr5289_1
                      (c0 (c0 (c0 c2_1 (c0 n n)) ((2:Nat)))
                        (c1 (c0 (c0 c3 c2_1) (c0 n n))
                          (c0 ((4:Nat))
                            (c2 (c0 (c2 c1_1) ((3:Nat))))))))))
                (c0 (c1 ((3:Nat)) c0_1)
                  ((2:Nat))))
              (c1 ((12:Nat)) c0_1))
          (fun (n:Nat) =>
            AXr5289_0
              (c0
                (c0
                  (c1 ((4:Nat))
                    (c1 ((32:Nat))
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        (c0 n ((1:Nat)))
                        ((2:Nat)))))
                  (c2 n))
                ((2:Nat))))
          (@AXr5289_5
            (fun (n:Nat) =>
              let c0_1:Nat:=
                c1 ((32:Nat))
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (c0 n ((1:Nat)))
                    ((2:Nat)));
              let c1_1:Nat:=
                c0 (c0 (c1 ((4:Nat)) c0_1) (c2 n))
                  ((2:Nat));
              let c2_1:Nat:=
                c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat));
              let c3:Nat:=c1 c2_1 (c0 n n);
              c1
                (c0
                  (c0
                    (c1 ((144:Nat))
                      (c0 c1_1 ((1:Nat))))
                    ((342:Nat)))
                  (c0
                    (c0
                      (c0
                        (c0 (c1 ((142:Nat)) c3)
                          (c1 ((138:Nat)) c2_1))
                        (c1 ((33:Nat)) (c0 n n)))
                      ((106:Nat)))
                    (AXr5289_1
                      (c0 (c0 (c0 c2_1 (c0 n n)) ((2:Nat)))
                        (c1 (c0 (c0 c3 c2_1) (c0 n n))
                          (c0 ((4:Nat))
                            (c2 (c0 (c2 c1_1) ((3:Nat))))))))))
                (c0 (c1 ((3:Nat)) c0_1)
                  ((2:Nat))))
            (fun (n:Nat) =>
              c1 ((12:Nat))
                (c1 ((32:Nat))
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (c0 n ((1:Nat)))
                    ((2:Nat)))))
            (@AXr5289_6
              (fun (n:Nat) =>
                let c0_1:Nat:=
                  c0
                    (c0
                      (c1 ((4:Nat))
                        (c1 ((32:Nat))
                          (@HPow.hPow Nat Nat Nat
                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            (c0 n ((1:Nat)))
                            ((2:Nat)))))
                      (c2 n))
                    ((2:Nat));
                let c1_1:Nat:=
                  c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat));
                let c2_1:Nat:=c1 c1_1 (c0 n n);
                c0
                  (c0
                    (c1 ((144:Nat))
                      (c0 c0_1 ((1:Nat))))
                    ((342:Nat)))
                  (c0
                    (c0
                      (c0
                        (c0 (c1 ((142:Nat)) c2_1)
                          (c1 ((138:Nat)) c1_1))
                        (c1 ((33:Nat)) (c0 n n)))
                      ((106:Nat)))
                    (AXr5289_1
                      (c0 (c0 (c0 c1_1 (c0 n n)) ((2:Nat)))
                        (c1 (c0 (c0 c2_1 c1_1) (c0 n n))
                          (c0 ((4:Nat))
                            (c2 (c0 (c2 c0_1) ((3:Nat))))))))))
              (fun (n:Nat) =>
                c0
                  (c1 ((3:Nat))
                    (c1 ((32:Nat))
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        (c0 n ((1:Nat)))
                        ((2:Nat)))))
                  ((2:Nat)))
              (@AXr5289_5
                (fun (n:Nat) =>
                  c0
                    (c1 ((144:Nat))
                      (c0
                        (c0
                          (c0
                            (c1 ((4:Nat))
                              (c1 ((32:Nat))
                                (@HPow.hPow Nat Nat Nat
                                  (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                  (c0 n ((1:Nat)))
                                  ((2:Nat)))))
                            (c2 n))
                          ((2:Nat)))
                        ((1:Nat))))
                    ((342:Nat)))
                (fun (n:Nat) =>
                  let c0_1:Nat:=
                    c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat));
                  let c1_1:Nat:=c1 c0_1 (c0 n n);
                  c0
                    (c0
                      (c0
                        (c0 (c1 ((142:Nat)) c1_1)
                          (c1 ((138:Nat)) c0_1))
                        (c1 ((33:Nat)) (c0 n n)))
                      ((106:Nat)))
                    (AXr5289_1
                      (c0 (c0 (c0 c0_1 (c0 n n)) ((2:Nat)))
                        (c1 (c0 (c0 c1_1 c0_1) (c0 n n))
                          (c0 ((4:Nat))
                            (c2
                              (c0
                                (c2
                                  (c0
                                    (c0
                                      (c1 ((4:Nat))
                                        (c1 ((32:Nat))
                                          (@HPow.hPow Nat Nat Nat
                                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                            (c0 n ((1:Nat)))
                                            ((2:Nat)))))
                                      (c2 n))
                                    ((2:Nat))))
                                ((3:Nat)))))))))
                (@AXr5289_5
                  (fun (n:Nat) =>
                    c1 ((144:Nat))
                      (c0
                        (c0
                          (c0
                            (c1 ((4:Nat))
                              (c1 ((32:Nat))
                                (@HPow.hPow Nat Nat Nat
                                  (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                  (c0 n ((1:Nat)))
                                  ((2:Nat)))))
                            (c2 n))
                          ((2:Nat)))
                        ((1:Nat))))
                  (fun (x:Nat) => (342:Nat))
                  (@AXr5289_6
                    (fun (x:Nat) => (144:Nat))
                    (fun (n:Nat) =>
                      c0
                        (c0
                          (c0
                            (c1 ((4:Nat))
                              (c1 ((32:Nat))
                                (@HPow.hPow Nat Nat Nat
                                  (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                  (c0 n ((1:Nat)))
                                  ((2:Nat)))))
                            (c2 n))
                          ((2:Nat)))
                        ((1:Nat)))
                    (AXr5289_3
                      ((144:Nat)))
                    (@AXr5289_5 c7
                      (fun (x:Nat) => (1:Nat)) c11
                      (AXr5289_3
                        ((1:Nat)))))
                  (AXr5289_3
                    ((342:Nat))))
                (@AXr5289_5
                  (fun (n:Nat) =>
                    let c0_1:Nat:=
                      c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat));
                    c0
                      (c0
                        (c0 (c1 ((142:Nat)) (c1 c0_1 (c0 n n)))
                          (c1 ((138:Nat)) c0_1))
                        (c1 ((33:Nat)) (c0 n n)))
                      ((106:Nat)))
                  (fun (n:Nat) =>
                    let c0_1:Nat:=
                      c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n))) ((1:Nat));
                    AXr5289_1
                      (c0 (c0 (c0 c0_1 (c0 n n)) ((2:Nat)))
                        (c1 (c0 (c0 (c1 c0_1 (c0 n n)) c0_1) (c0 n n))
                          (c0 ((4:Nat))
                            (c2
                              (c0
                                (c2
                                  (c0
                                    (c0
                                      (c1 ((4:Nat))
                                        (c1 ((32:Nat))
                                          (@HPow.hPow Nat Nat Nat
                                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                            (c0 n ((1:Nat)))
                                            ((2:Nat)))))
                                      (c2 n))
                                    ((2:Nat))))
                                ((3:Nat))))))))
                  (@AXr5289_5
                    (fun (n:Nat) =>
                      let c0_1:Nat:=
                        c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                          ((1:Nat));
                      c0
                        (c0 (c1 ((142:Nat)) (c1 c0_1 (c0 n n)))
                          (c1 ((138:Nat)) c0_1))
                        (c1 ((33:Nat)) (c0 n n)))
                    (fun (x:Nat) => (106:Nat))
                    (@AXr5289_5
                      (fun (n:Nat) =>
                        let c0_1:Nat:=
                          c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                            ((1:Nat));
                        c0 (c1 ((142:Nat)) (c1 c0_1 (c0 n n)))
                          (c1 ((138:Nat)) c0_1))
                      c3
                      (@AXr5289_5
                        (fun (n:Nat) =>
                          c1 ((142:Nat))
                            (c1
                              (c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                                ((1:Nat)))
                              (c0 n n)))
                        (fun (n:Nat) =>
                          c1 ((138:Nat))
                            (c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                              ((1:Nat))))
                        (@AXr5289_6
                          (fun (x:Nat) => (142:Nat)) c12
                          (AXr5289_3
                            ((142:Nat)))
                          c16)
                        (@AXr5289_6
                          (fun (x:Nat) => (138:Nat)) c13
                          (AXr5289_3
                            ((138:Nat)))
                          c15))
                      c6)
                    (AXr5289_3
                      ((106:Nat))))
                  (@Lax109476Proofs.RamResourcePolynomial.compose AXr5289_1
                    (fun (n:Nat) =>
                      let c0_1:Nat:=
                        c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                          ((1:Nat));
                      c0 (c0 (c0 c0_1 (c0 n n)) ((2:Nat)))
                        (c1 (c0 (c0 (c1 c0_1 (c0 n n)) c0_1) (c0 n n))
                          (c0 ((4:Nat))
                            (c2
                              (c0
                                (c2
                                  (c0
                                    (c0
                                      (c1 ((4:Nat))
                                        (c1 ((32:Nat))
                                          (@HPow.hPow Nat Nat Nat
                                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                            (c0 n ((1:Nat)))
                                            ((2:Nat)))))
                                      (c2 n))
                                    ((2:Nat))))
                                ((3:Nat)))))))
                    Lax109476Proofs.RamResourcePolynomial.stored_cost
                    (@AXr5289_5
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
                            (c2
                              (c0
                                (c2
                                  (c0
                                    (c0
                                      (c1 ((4:Nat))
                                        (c1 ((32:Nat))
                                          (@HPow.hPow Nat Nat Nat
                                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                            (c0 n ((1:Nat)))
                                            ((2:Nat)))))
                                      (c2 n))
                                    ((2:Nat))))
                                ((3:Nat))))))
                      (@AXr5289_5
                        (fun (n:Nat) =>
                          c0
                            (c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                              ((1:Nat)))
                            (c0 n n))
                        (fun (x:Nat) => (2:Nat))
                        (@AXr5289_5 c13 c4 c15 c5)
                        (AXr5289_3
                          ((2:Nat))))
                      (@AXr5289_6
                        (fun (n:Nat) =>
                          let c0_1:Nat:=
                            c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                              ((1:Nat));
                          c0 (c0 (c1 c0_1 (c0 n n)) c0_1) (c0 n n))
                        (fun (n:Nat) =>
                          c0 ((4:Nat))
                            (c2
                              (c0
                                (c2
                                  (c0
                                    (c0
                                      (c1 ((4:Nat))
                                        (c1 ((32:Nat))
                                          (@HPow.hPow Nat Nat Nat
                                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                            (c0 n ((1:Nat)))
                                            ((2:Nat)))))
                                      (c2 n))
                                    ((2:Nat))))
                                ((3:Nat)))))
                        (@AXr5289_5
                          (fun (n:Nat) =>
                            let c0_1:Nat:=
                              c0 (c0 (c0 n n) (c0 (c0 n n) (c0 n n)))
                                ((1:Nat));
                            c0 (c1 c0_1 (c0 n n)) c0_1)
                          c4 (@AXr5289_5 c12 c13 c16 c15) c5)
                        (@AXr5289_5
                          (fun (x:Nat) => (4:Nat))
                          (fun (n:Nat) =>
                            c2
                              (c0
                                (c2
                                  (c0
                                    (c0
                                      (c1 ((4:Nat))
                                        (c1 ((32:Nat))
                                          (@HPow.hPow Nat Nat Nat
                                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                            (c0 n ((1:Nat)))
                                            ((2:Nat)))))
                                      (c2 n))
                                    ((2:Nat))))
                                ((3:Nat))))
                          (AXr5289_3
                            ((4:Nat)))
                          (@c10
                            (fun (n:Nat) =>
                              c0
                                (c2
                                  (c0
                                    (c0
                                      (c1 ((4:Nat))
                                        (c1 ((32:Nat))
                                          (@HPow.hPow Nat Nat Nat
                                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                            (c0 n ((1:Nat)))
                                            ((2:Nat)))))
                                      (c2 n))
                                    ((2:Nat))))
                                ((3:Nat)))
                            (AXr5289_3
                              ((2:Nat)))
                            (@AXr5289_5
                              (fun (n:Nat) =>
                                c2
                                  (c0
                                    (c0
                                      (c1 ((4:Nat))
                                        (c1 ((32:Nat))
                                          (@HPow.hPow Nat Nat Nat
                                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                            (c0 n ((1:Nat)))
                                            ((2:Nat)))))
                                      (c2 n))
                                    ((2:Nat))))
                              (fun (x:Nat) => (3:Nat))
                              (@c10 c7
                                (AXr5289_3
                                  ((2:Nat)))
                                c11)
                              (AXr5289_3
                                ((3:Nat)))))))))))
              (@AXr5289_5
                (fun (n:Nat) =>
                  c1 ((3:Nat))
                    (c1 ((32:Nat))
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        (c0 n ((1:Nat)))
                        ((2:Nat)))))
                (fun (x:Nat) => (2:Nat))
                (@AXr5289_6
                  (fun (x:Nat) => (3:Nat)) c8
                  (AXr5289_3
                    ((3:Nat)))
                  c9)
                (AXr5289_3
                  ((2:Nat)))))
            (@AXr5289_6
              (fun (x:Nat) => (12:Nat)) c8
              (AXr5289_3
                ((12:Nat)))
              c9))
          (@Lax109476Proofs.RamResourcePolynomial.compose AXr5289_0 c7
            Lax109476Proofs.RamResourcePolynomial.reconstruction_cost c11))
        (AXr5289_3 ((77:Nat))))
      c5)
    (AXr5289_3 ((6:Nat))))

noncomputable abbrev _root_.AXr5291_0:= @Lax109476Proofs.RamResourcePolynomial.HasPolynomial
noncomputable abbrev _root_.AXr5291_1:= @Lax109476Proofs.RamResourcePolynomial.constant
noncomputable abbrev _root_.AXr5291_2:= @Lax109476Proofs.RamResourcePolynomial.identity
noncomputable abbrev _root_.AXr5291_3:= @Lax109476Proofs.RamResourcePolynomial.add
noncomputable abbrev _root_.AXr5291_4:= @Lax109476Proofs.RamResourcePolynomial.mul
theorem decision_cost:AXr5291_0 fun (S:Nat) =>
  Lax109476Proofs.RamCertificateDecision.instructionBound S S S:=
let c0:Nat→ Nat→ Nat:=Nat.add;
let c1:Nat→ Nat→ Nat:=Nat.mul;
let c2:Nat→ Nat:=c1 ((2:Nat));
let c3:Nat→ Nat:=fun (n:Nat) => c0 (c1 n n) n;
let c4:
  AXr5291_0 fun (n:Nat) =>
    Nat.add (c1 n n) n:=
  @AXr5291_3 (fun (n:Nat) => c1 n n) (fun (n:Nat) => n)
    (@AXr5291_4 (fun (n:Nat) => n) (fun (n:Nat) => n)
      AXr5291_2 AXr5291_2)
    AXr5291_2;
let c5:
  ∀ {g:Nat→ Nat},
    (AXr5291_0 fun (x:Nat) =>
        (2:Nat))→
      AXr5291_0 g→
        AXr5291_0 fun (n:Nat) =>
          Nat.mul ((2:Nat))
            (g n):=
  @AXr5291_4 fun (x:Nat) => (2:Nat);
@AXr5291_3
  (fun (n:Nat) =>
    c0
      (c0 (c1 ((71:Nat)) (c0 (c1 n n) n))
        (c1 ((33:Nat)) n))
      ((80:Nat)))
  (fun (n:Nat) =>
    Lax109476Proofs.RamStoredFeasibility.instructionBound
      (c0 (c0 (c0 n n) ((2:Nat)))
        (c1 (c0 (c0 (c1 n n) n) n)
          (c0 ((4:Nat))
            (c2 (c0 (c2 n) ((1:Nat))))))))
  (@AXr5291_3
    (fun (n:Nat) =>
      c0 (c1 ((71:Nat)) (c0 (c1 n n) n))
        (c1 ((33:Nat)) n))
    (fun (x:Nat) => (80:Nat))
    (@AXr5291_3
      (fun (n:Nat) => c1 ((71:Nat)) (c0 (c1 n n) n))
      (fun (n:Nat) => c1 ((33:Nat)) n)
      (@AXr5291_4
        (fun (x:Nat) => (71:Nat)) c3
        (AXr5291_1 ((71:Nat))) c4)
      (@AXr5291_4
        (fun (x:Nat) => (33:Nat)) (fun (n:Nat) => n)
        (AXr5291_1 ((33:Nat)))
        AXr5291_2))
    (AXr5291_1 ((80:Nat))))
  (@Lax109476Proofs.RamResourcePolynomial.compose Lax109476Proofs.RamStoredFeasibility.instructionBound
    (fun (n:Nat) =>
      c0 (c0 (c0 n n) ((2:Nat)))
        (c1 (c0 (c0 (c1 n n) n) n)
          (c0 ((4:Nat))
            (c2 (c0 (c2 n) ((1:Nat)))))))
    Lax109476Proofs.RamResourcePolynomial.stored_cost
    (@AXr5291_3
      (fun (n:Nat) => c0 (c0 n n) ((2:Nat)))
      (fun (n:Nat) =>
        c1 (c0 (c0 (c1 n n) n) n)
          (c0 ((4:Nat))
            (c2 (c0 (c2 n) ((1:Nat))))))
      (@AXr5291_3 (fun (n:Nat) => c0 n n)
        (fun (x:Nat) => (2:Nat))
        (@AXr5291_3 (fun (n:Nat) => n) (fun (n:Nat) => n)
          AXr5291_2 AXr5291_2)
        (AXr5291_1 ((2:Nat))))
      (@AXr5291_4 (fun (n:Nat) => c0 (c0 (c1 n n) n) n)
        (fun (n:Nat) =>
          c0 ((4:Nat))
            (c2 (c0 (c2 n) ((1:Nat)))))
        (@AXr5291_3 c3 (fun (n:Nat) => n) c4
          AXr5291_2)
        (@AXr5291_3
          (fun (x:Nat) => (4:Nat))
          (fun (n:Nat) => c2 (c0 (c2 n) ((1:Nat))))
          (AXr5291_1 ((4:Nat)))
          (@c5 (fun (n:Nat) => c0 (c2 n) ((1:Nat)))
            (AXr5291_1 ((2:Nat)))
            (@AXr5291_3 (fun (n:Nat) => c2 n)
              (fun (x:Nat) => (1:Nat))
              (@c5 (fun (n:Nat) => n)
                (AXr5291_1
                  ((2:Nat)))
                AXr5291_2)
              (AXr5291_1
                ((1:Nat)))))))))

end Lax109476Proofs.RamResourcePolynomial

end

section

namespace Lax109476Proofs.RamSolverBranchBounds

theorem recovery_cost {r s S:ℕ} (hr:r≤ S) (hs:s≤ S):
    RamRecoverFeasibleSystem.instructionBound r s S + 35 * s + 10≤ recoveryCost S:=by
  have h:=RamRecoveryResourceMonotonicity.recovery_cost hr hs (show S≤ S from le_rfl)
  unfold recoveryCost
  omega

theorem decision_cost {r s S:ℕ} (hr:r≤ S) (hs:s≤ S):
    RamCertificateDecision.instructionBound r s S≤ decisionCost S:=by
  unfold decisionCost RamCertificateDecision.instructionBound
  have hsize:RamCertificateDecision.sizeBound r s S≤ RamCertificateDecision.sizeBound S S S:=by
    unfold RamCertificateDecision.sizeBound
    gcongr
  have hstored:=RamStoredFeasibilityBounds.instructionBound_monotone hsize
  have hp:=Nat.mul_le_mul hr hs
  omega

theorem cost_polynomial:RamResourcePolynomial.HasPolynomial instructionBound:=by
  unfold instructionBound recoveryCost buildCost decisionCost
  apply RamResourcePolynomial.add
  · apply RamResourcePolynomial.add
    · apply RamResourcePolynomial.add
      · apply RamResourcePolynomial.mul (RamResourcePolynomial.constant 3)
        exact RamResourcePolynomial.add
          (RamResourcePolynomial.add
            (RamResourcePolynomial.mul (RamResourcePolynomial.constant 142)
              (RamResourcePolynomial.mul RamResourcePolynomial.identity RamResourcePolynomial.identity))
            (RamResourcePolynomial.mul (RamResourcePolynomial.constant 98) RamResourcePolynomial.identity))
          (RamResourcePolynomial.constant 74)
      · exact RamResourcePolynomial.mul (RamResourcePolynomial.constant 2) RamResourcePolynomial.decision_cost
    · apply RamResourcePolynomial.add
      · exact RamResourcePolynomial.add RamResourcePolynomial.recovery_cost
          (RamResourcePolynomial.mul (RamResourcePolynomial.constant 35) RamResourcePolynomial.identity)
      · exact RamResourcePolynomial.constant 10
  · exact RamResourcePolynomial.constant 32

end Lax109476Proofs.RamSolverBranchBounds

end

section

namespace Lax109476Proofs.RamUniformSolverBounds

open RamResourcePolynomial

theorem canonical_polynomial:HasPolynomial canonicalSize:=decoded_size
theorem parameter_polynomial:HasPolynomial parameter:=
  compose (f:=RamCertificateSetup.parameter) (g:=canonicalSize)
    RamResourcePolynomial.parameter canonical_polynomial

noncomputable abbrev _root_.AXr5336_0:= @Lax109476Proofs.RamResourcePolynomial.HasPolynomial
noncomputable abbrev _root_.AXr5336_1:= @Lax109476Proofs.RamResourcePolynomial.constant
noncomputable abbrev _root_.AXr5336_2:= @Lax109476Proofs.RamResourcePolynomial.identity
noncomputable abbrev _root_.AXr5336_3:= @Lax109476Proofs.RamResourcePolynomial.add
noncomputable abbrev _root_.AXr5336_4:= @Lax109476Proofs.RamResourcePolynomial.mul
theorem front_cost_polynomial:AXr5336_0 Lax109476Proofs.RamFrontEndTotal.instructionBound:=
let c0:Nat→ Nat→ Nat:=Nat.add;
let c1:Nat→ Nat→ Nat:=Nat.mul;
let c2:
  ∀ {g:Nat→ Nat},
    (AXr5336_0 fun (n:Nat) =>
        c1 ((36:Nat))
          (c0 n ((1:Nat))))→
      AXr5336_0 g→
        AXr5336_0 fun (n:Nat) =>
          Nat.add
            (c1 ((36:Nat))
              (c0 n ((1:Nat))))
            (g n):=
  @AXr5336_3 fun (n:Nat) =>
    c1 ((36:Nat))
      (c0 n ((1:Nat)));
let c3:Nat→ Nat:=fun (n:Nat) => c0 n ((1:Nat));
let c4:
  AXr5336_0 fun (n:Nat) =>
    Nat.add n ((1:Nat)):=
  @AXr5336_3 (fun (n:Nat) => n)
    (fun (x:Nat) => (1:Nat))
    AXr5336_2
    (AXr5336_1 ((1:Nat)));
let c5:
  AXr5336_0 fun (n:Nat) =>
    Nat.mul ((36:Nat))
      (c3 n):=
  @AXr5336_4
    (fun (x:Nat) => (36:Nat)) c3
    (AXr5336_1 ((36:Nat))) c4;
@Lax109476Proofs.RamResourcePolynomial.compose Lax109476Proofs.RamSolverFrontEnd.instructionBound
  Lax109476Proofs.RamUniformSolverBounds.canonicalSize
  (@id (AXr5336_0 Lax109476Proofs.RamSolverFrontEnd.instructionBound)
    (@id
      (AXr5336_0 fun (L:Nat) =>
        c0
          (c0 (Lax109476Proofs.RamSolverInitialization.instructionBound L)
            (c1
              (c0
                (c1 ((72:Nat))
                  (c0 L ((1:Nat))))
                ((135:Nat)))
              L))
          ((86:Nat)))
      (@id
        (AXr5336_0 fun (L:Nat) =>
          let c0_1:Nat:=c0 L ((1:Nat));
          c0
            (c0
              (c0
                (c0
                  (c0 (Lax109476Proofs.RamDecoder.instructionBound L c0_1)
                    (c1
                      (c0 (c1 ((36:Nat)) c0_1)
                        ((61:Nat)))
                      L))
                  (c1 ((37:Nat)) L))
                ((86:Nat)))
              (c1
                (c0 (c1 ((72:Nat)) c0_1)
                  ((135:Nat)))
                L))
            ((86:Nat)))
        (@AXr5336_3
          (fun (n:Nat) =>
            let c0_1:Nat:=c0 n ((1:Nat));
            let c1_1:Nat→ Nat:=c0 (c1 ((36:Nat)) c0_1);
            c0
              (c0
                (c0
                  (c0
                    (c0
                      (c1 (c1_1 ((115:Nat)))
                        (c0
                          (c0
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) n
                              ((2:Nat)))
                            (c1 ((4:Nat)) n))
                          ((3:Nat))))
                      ((127:Nat)))
                    (c1 (c1_1 ((61:Nat))) n))
                  (c1 ((37:Nat)) n))
                ((86:Nat)))
              (c1
                (c0 (c1 ((72:Nat)) c0_1)
                  ((135:Nat)))
                n))
          (fun (x:Nat) => (86:Nat))
          (@AXr5336_3
            (fun (n:Nat) =>
              let c0_1:Nat→ Nat:=
                c0
                  (c1 ((36:Nat))
                    (c0 n ((1:Nat))));
              c0
                (c0
                  (c0
                    (c0
                      (c1 (c0_1 ((115:Nat)))
                        (c0
                          (c0
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) n
                              ((2:Nat)))
                            (c1 ((4:Nat)) n))
                          ((3:Nat))))
                      ((127:Nat)))
                    (c1 (c0_1 ((61:Nat))) n))
                  (c1 ((37:Nat)) n))
                ((86:Nat)))
            (fun (n:Nat) =>
              c1
                (c0
                  (c1 ((72:Nat))
                    (c0 n ((1:Nat))))
                  ((135:Nat)))
                n)
            (@AXr5336_3
              (fun (n:Nat) =>
                let c0_1:Nat→ Nat:=
                  c0
                    (c1 ((36:Nat))
                      (c0 n ((1:Nat))));
                c0
                  (c0
                    (c0
                      (c1 (c0_1 ((115:Nat)))
                        (c0
                          (c0
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) n
                              ((2:Nat)))
                            (c1 ((4:Nat)) n))
                          ((3:Nat))))
                      ((127:Nat)))
                    (c1 (c0_1 ((61:Nat))) n))
                  (c1 ((37:Nat)) n))
              (fun (x:Nat) => (86:Nat))
              (@AXr5336_3
                (fun (n:Nat) =>
                  let c0_1:Nat→ Nat:=
                    c0
                      (c1 ((36:Nat))
                        (c0 n ((1:Nat))));
                  c0
                    (c0
                      (c1 (c0_1 ((115:Nat)))
                        (c0
                          (c0
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) n
                              ((2:Nat)))
                            (c1 ((4:Nat)) n))
                          ((3:Nat))))
                      ((127:Nat)))
                    (c1 (c0_1 ((61:Nat))) n))
                (fun (n:Nat) => c1 ((37:Nat)) n)
                (@AXr5336_3
                  (fun (n:Nat) =>
                    c0
                      (c1
                        (c0
                          (c1 ((36:Nat))
                            (c0 n ((1:Nat))))
                          ((115:Nat)))
                        (c0
                          (c0
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) n
                              ((2:Nat)))
                            (c1 ((4:Nat)) n))
                          ((3:Nat))))
                      ((127:Nat)))
                  (fun (n:Nat) =>
                    c1
                      (c0
                        (c1 ((36:Nat))
                          (c0 n ((1:Nat))))
                        ((61:Nat)))
                      n)
                  (@AXr5336_3
                    (fun (n:Nat) =>
                      c1
                        (c0
                          (c1 ((36:Nat))
                            (c0 n ((1:Nat))))
                          ((115:Nat)))
                        (c0
                          (c0
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) n
                              ((2:Nat)))
                            (c1 ((4:Nat)) n))
                          ((3:Nat))))
                    (fun (x:Nat) => (127:Nat))
                    (@AXr5336_4
                      (fun (n:Nat) =>
                        c0
                          (c1 ((36:Nat))
                            (c0 n ((1:Nat))))
                          ((115:Nat)))
                      (fun (n:Nat) =>
                        c0
                          (c0
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) n
                              ((2:Nat)))
                            (c1 ((4:Nat)) n))
                          ((3:Nat)))
                      (@c2 (fun (x:Nat) => (115:Nat)) c5
                        (AXr5336_1
                          ((115:Nat))))
                      (@AXr5336_3
                        (fun (n:Nat) =>
                          c0
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) n
                              ((2:Nat)))
                            (c1 ((4:Nat)) n))
                        (fun (x:Nat) => (3:Nat))
                        (@AXr5336_3
                          (fun (n:Nat) =>
                            @HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) n
                              ((2:Nat)))
                          (fun (n:Nat) => c1 ((4:Nat)) n)
                          (@Lax109476Proofs.RamResourcePolynomial.pow (fun (n:Nat) => n)
                            AXr5336_2
                            ((2:Nat)))
                          (@AXr5336_4
                            (fun (x:Nat) => (4:Nat))
                            (fun (n:Nat) => n)
                            (AXr5336_1
                              ((4:Nat)))
                            AXr5336_2))
                        (AXr5336_1
                          ((3:Nat)))))
                    (AXr5336_1
                      ((127:Nat))))
                  (@AXr5336_4
                    (fun (n:Nat) =>
                      c0
                        (c1 ((36:Nat))
                          (c0 n ((1:Nat))))
                        ((61:Nat)))
                    (fun (n:Nat) => n)
                    (@c2 (fun (x:Nat) => (61:Nat)) c5
                      (AXr5336_1
                        ((61:Nat))))
                    AXr5336_2))
                (@AXr5336_4
                  (fun (x:Nat) => (37:Nat)) (fun (n:Nat) => n)
                  (AXr5336_1
                    ((37:Nat)))
                  AXr5336_2))
              (AXr5336_1
                ((86:Nat))))
            (@AXr5336_4
              (fun (n:Nat) =>
                c0
                  (c1 ((72:Nat))
                    (c0 n ((1:Nat))))
                  ((135:Nat)))
              (fun (n:Nat) => n)
              (@AXr5336_3
                (fun (n:Nat) =>
                  c1 ((72:Nat))
                    (c0 n ((1:Nat))))
                (fun (x:Nat) => (135:Nat))
                (@AXr5336_4
                  (fun (x:Nat) => (72:Nat)) c3
                  (AXr5336_1
                    ((72:Nat)))
                  c4)
                (AXr5336_1
                  ((135:Nat))))
              AXr5336_2))
          (AXr5336_1
            ((86:Nat)))))))
  Lax109476Proofs.RamUniformSolverBounds.canonical_polynomial

theorem cost_polynomial:HasPolynomial instructionBound:=by
  unfold instructionBound
  exact add (add (add (add front_cost_polynomial (mul (constant 71) canonical_polynomial))
    (constant 100)) (compose RamSolverBranchBounds.cost_polynomial parameter_polynomial)) (constant 16)

end Lax109476Proofs.RamUniformSolverBounds

end

theorem solution:Lax109476Proofs.RamResourcePolynomial.HasPolynomial Lax109476Proofs.RamUniformSolverBounds.instructionBound:= @Lax109476Proofs.RamUniformSolverBounds.cost_polynomial
