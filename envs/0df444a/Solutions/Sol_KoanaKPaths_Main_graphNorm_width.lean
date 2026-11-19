-- Prove2me | solution 1 for KoanaKPaths.Main.graphNorm_width
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.374588+00:00
-- url     : https://prove2.me/submissions/17b9ed41-2a3e-4569-8de8-1ab641ead173

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Main_graphLayer_natAbs
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S P : ℕ}



































lemma nbits_eq_bits (n : ℕ) : nbits n = Nat.bits n := by
  induction n using Nat.binaryRec' with
  | zero => simp [nbits]
  | bit b n hn ih =>
    have hne : Nat.bit b n ≠ 0 := by
      intro hz
      cases b <;> simp_all [Nat.bit]
    rw [nbits,dif_neg hne,Nat.bit_mod_two,Nat.bit_div_two,ih,Nat.bits_append_bit n b hn]
    cases b <;> rfl

















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]

lemma zsz_le_iff (z : ℤ) (w : ℕ) : zsz z ≤ w ↔ z.natAbs<2^w := by
  rw [zsz_eq_size,Nat.size_le]



































end KoanaKPaths.Machine.Wedge

end

section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates

lemma natAbs_sum_le {α : Type} (s : Finset α) (f : α→ℤ) :
    (∑ x∈s, f x).natAbs ≤ ∑ x∈s, (f x).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)









lemma graphOutput_natAbs {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) (a : Fin ℓ) (S : Finset (Fin k)) :
    (graphOutput arcs σ R a S).natAbs≤n*(layerRadius n k ℓ)^k := by
  unfold graphOutput
  simp only [Finset.sum_apply]
  calc
    _ ≤ ∑ v : Fin n, (graphLayer arcs σ R k v a S).natAbs := natAbs_sum_le Finset.univ _
    _ ≤ ∑ _v : Fin n, (layerRadius n k ℓ)^k := Finset.sum_le_sum (fun v _ => graphLayer_natAbs arcs σ R k v a S)
    _ = _ := by simp


lemma layerRadius_le_exp (n k ℓ : ℕ) : layerRadius n k ℓ≤2^(n+k+ℓ+3) := by
  have hp : layerRadius n k ℓ≤(n+1)*(k+1)*(ℓ+1) := by
    unfold layerRadius
    nlinarith [Nat.zero_le (n*k),Nat.zero_le (n*ℓ),Nat.zero_le (k*ℓ)]
  have hn : n+1≤2^(n+1) := Nat.le_of_lt Nat.lt_two_pow_self
  have hk : k+1≤2^(k+1) := Nat.le_of_lt Nat.lt_two_pow_self
  have hl : ℓ+1≤2^(ℓ+1) := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    _ ≤ (n+1)*(k+1)*(ℓ+1) := hp
    _ ≤ 2^(n+1)*2^(k+1)*2^(ℓ+1) := Nat.mul_le_mul (Nat.mul_le_mul hn hk) hl
    _ = _ := by rw [← pow_add,← pow_add]; congr 1; omega





end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Main







lemma graphNorm_width {n k ℓ : ℕ} (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    zsz (∑ a : Fin ℓ, (graphOutput arcs σ R a Finset.univ)^2)≤ trialWidth n k ℓ := by
  have hr := Nat.pow_le_pow_left (layerRadius_le_exp n k ℓ) k
  rw [← pow_mul] at hr
  have hn : n≤2^n := Nat.le_of_lt Nat.lt_two_pow_self
  have hv : ∀ a : Fin ℓ, (graphOutput arcs σ R a Finset.univ).natAbs≤2^(outputExponent n k ℓ) := by
    intro a
    have hh := (graphOutput_natAbs arcs σ R a Finset.univ).trans (Nat.mul_le_mul hn hr)
    simpa only [← pow_add,outputExponent] using hh
  have hsq : ∀ a : Fin ℓ, ((graphOutput arcs σ R a Finset.univ)^2).natAbs≤2^(2*outputExponent n k ℓ) := by
    intro a
    rw [Int.natAbs_pow]
    have h := Nat.pow_le_pow_left (hv a) 2
    simpa only [← pow_mul,Nat.mul_comm] using h
  have hnorm : (∑ a : Fin ℓ, (graphOutput arcs σ R a Finset.univ)^2).natAbs≤
      ℓ*2^(2*outputExponent n k ℓ) := by
    calc
      _ ≤ ∑ a : Fin ℓ, ((graphOutput arcs σ R a Finset.univ)^2).natAbs :=
        natAbs_sum_le Finset.univ _
      _ ≤ ∑ _a : Fin ℓ, 2^(2*outputExponent n k ℓ) := Finset.sum_le_sum (fun a _ => hsq a)
      _ = _ := by simp
  have hl : ℓ≤2^ℓ := Nat.le_of_lt Nat.lt_two_pow_self
  have hh := hnorm.trans (Nat.mul_le_mul_right (2^(2*outputExponent n k ℓ)) hl)
  rw [← pow_add] at hh
  apply (Machine.Wedge.zsz_le_iff _ _).mpr
  unfold trialWidth
  rw [pow_succ]
  have hp : 0<2^(ℓ+2*outputExponent n k ℓ) := by positivity
  omega







end KoanaKPaths.Main

namespace KoanaKPaths.Machine.Norm




end KoanaKPaths.Machine.Norm

end

theorem solution :
∀ {n k ℓ : Nat} (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (σ : KoanaKPaths.Main.Labels n k)
  (R : KoanaKPaths.Main.SketchSigns n k ℓ),
  @LE.le.{0} Nat instLENat
    (NLogN.zsz
      (@Finset.sum.{0, 0} (Fin ℓ) Int Int.instAddCommMonoid (@Finset.univ.{0} (Fin ℓ) (Fin.fintype ℓ))
        fun (a : Fin ℓ) =>
        @HPow.hPow.{0, 0, 0} Int Nat Int
          (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
          (@KoanaKPaths.Main.graphOutput n k ℓ arcs σ R a (@Finset.univ.{0} (Fin k) (Fin.fintype k)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (KoanaKPaths.Main.trialWidth n k ℓ) := by
  exact @KoanaKPaths.Main.graphNorm_width
