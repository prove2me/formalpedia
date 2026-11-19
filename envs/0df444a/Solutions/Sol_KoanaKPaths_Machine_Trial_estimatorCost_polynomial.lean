-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.estimatorCost_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:37.685778+00:00
-- url     : https://prove2.me/submissions/72f8d12a-3f72-4110-a71d-3ab4feeac5b3

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_MedianOfMeans
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_Trial_nativeTrialCost_polynomial
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Main











lemma accuracy_square_bound (a : ℕ) : (a+1)^2≤4^a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    calc
      (a+1+1)^2≤4*(a+1)^2 := by nlinarith [Nat.zero_le (a*a)]
      _ ≤ 4*4^a := Nat.mul_le_mul_left 4 ih
      _ = 4^(a+1) := by rw [pow_succ]; ring

lemma medianWidth_cost (n k a : ℕ) :
    (medianWidth n k a+1)^2≤11000*(1+n+k)^4*4^a := by
  have ha := accuracy_square_bound a
  have hp : 1≤(1+n+k)^2 := by nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]
  have hlin : medianWidth n k a+1≤103*(1+n+k)^2*(a+1) := by
    unfold medianWidth
    nlinarith
  have hs := Nat.pow_le_pow_left hlin 2
  calc
    _ ≤ (103*(1+n+k)^2*(a+1))^2 := hs
    _ = 10609*(1+n+k)^4*(a+1)^2 := by ring
    _ ≤ 11000*(1+n+k)^4*4^a := by nlinarith [Nat.mul_le_mul_left (10609*(1+n+k)^4) ha]

end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main



lemma costEnvelope_mono {C W M Q L2 K C' W' M' L2' K' : ℕ}
    (hC : C≤ C') (hW : W≤ W') (hM : M≤ M') (hL : L2≤ L2') (hK : K≤ K') :
    costEnvelope C W M Q L2 K≤ costEnvelope C' W' M' Q L2' K' := by
  unfold costEnvelope
  gcongr

lemma costEnvelope_bound (E H F Q : ℕ) (hE : 1≤ E) (hH : 1≤ H) (hF : 1≤ F) (hQ : 1≤ Q) :
    costEnvelope (1000000000000000*E*H^10) (100*H^2) (1024*H^3*F) Q (11000*H^4*F) H≤
      10000000000000000000000000*E*H^14*F*Q := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le hE
  obtain ⟨h,rfl⟩ := Nat.exists_eq_add_of_le hH
  obtain ⟨f,rfl⟩ := Nat.exists_eq_add_of_le hF
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le hQ
  unfold costEnvelope
  ring_nf
  omega

lemma estimatorCost_polynomial (n k a b m : ℕ) (hk : 1≤ k) :
    estimatorCost n k a b m≤
      10000000000000000000000000*2^k*(1+n+k+m)^14*4^a*(b+1) := by
  let H := 1+n+k+m
  have hCost := nativeTrialCost_polynomial n k m hk
  have hbase : 1+n+k≤ H := by dsimp [H]; omega
  have hkp : k≤ H := by dsimp [H]; omega
  have hW : wordWidth n k≤100*H^2 :=
    Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hbase 2)
  have hM : groupTrials k a≤1024*H^3*4^a :=
    Nat.mul_le_mul_right (4^a) (Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left hkp 3))
  have hL : (medianWidth n k a+1)^2≤11000*H^4*4^a :=
    (medianWidth_cost n k a).trans (Nat.mul_le_mul_right (4^a)
      (Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left hbase 4)))
  have hK : k+1≤ H := by dsimp [H]; omega
  have heq : estimatorCost n k a b m=costEnvelope (nativeTrialCost n k m) (wordWidth n k)
      (groupTrials k a) (b+1) ((medianWidth n k a+1)^2) (k+1) := by
    unfold estimatorCost numeratorCost groupDriverCost groupNativeCost trialFoldBaseCost Denominator.driverCost costEnvelope
    ring
  rw [heq]
  exact (costEnvelope_mono hCost hW hM hL hK).trans
    (costEnvelope_bound (2^k) H (4^a) (b+1) (Nat.one_le_pow k 2 (by omega))
      (by dsimp [H]; omega) (Nat.one_le_pow a 4 (by omega)) (by omega))

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (n k a b m : Nat) (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k),
  @LE.le.{0} Nat instLENat (KoanaKPaths.Machine.Trial.estimatorCost n k a b m)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 10000000000000000000000000)
              (instOfNatNat (nat_lit 10000000000000000000000000)))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
                k)
              m)
            (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @KoanaKPaths.Machine.Trial.estimatorCost_polynomial
