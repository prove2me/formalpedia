-- Prove2me | solution 1 for GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:42:47.574568+00:00
-- url     : https://prove2.me/submissions/33f9e385-960a-4580-a3f0-ca39075aa433

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatDegreeMulEsymmRootsPow
import Theorems.Thm_GlobalTheory_CuspGL_roots_pow_eq_map_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X]) (m k s : ℕ), f.Monic → Irreducible f → ((f ^ m).natDegree : ℂ) * (((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).esymm s = ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s, rootSum θ (k * ∑ i ∈ I, Nat.card F ^ i) (f ^ m) := by
  intro F _ _ θ f m k s hf hi
  set R := ((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots with hR
  have hcard : R.card = (f ^ m).natDegree := by
    rw [hR, IsAlgClosed.card_roots_eq_natDegree, natDegree_map]
  have key : ∀ α ∈ R, (R.map fun α => θ α ^ k).esymm s =
      ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s,
        θ α ^ (k * ∑ i ∈ I, Nat.card F ^ i) := by
    intro α hα
    have h := roots_pow_eq_map_range f m hf hi α hα
    rw [← hR] at h
    conv_lhs => rw [h]
    rw [Multiset.map_map, ← Finset.range_val, Finset.esymm_map_val]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp, map_pow, ← pow_mul, mul_comm]
  have h2 : (R.map fun _ => (R.map fun α => θ α ^ k).esymm s).sum =
      (R.map fun α => ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s,
        θ α ^ (k * ∑ i ∈ I, Nat.card F ^ i)).sum := by
    rw [Multiset.map_congr rfl key]
  rw [Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul] at h2
  rw [h2, Multiset.sum_map_sum]
  rfl
end GlobalTheory.CuspGL
