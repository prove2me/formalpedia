-- Prove2me | solution 1 for GlobalTheory.TargetLemmaCollection.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:12:29.940814+00:00
-- url     : https://prove2.me/submissions/bba682f7-97bf-46df-be56-a9131745a193

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsExtraAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TargetLemmaCollection
open NumberField
namespace GlobalTheory.TargetLemmaCollection
theorem _root_.solution {K : Type} [Field K] [NumberField K] {Z : Type} [AddCommGroup Z] [Module K Z]
    [Module (RingOfIntegers K) Z] [IsScalarTower (RingOfIntegers K) K Z]
    {A : Submodule (RingOfIntegers K) Z} {x : Z} (hx : x ∈ Submodule.span K (A : Set Z)) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    have e1 : (d₁ * d₂) • y = d₂ • (d₁ • y) := by rw [mul_comm, mul_smul]
    have e2 : (d₁ * d₂) • z = d₁ • (d₂ • z) := by rw [mul_smul]
    rw [e1, e2]
    exact A.add_mem (A.smul_mem _ h₁) (A.smul_mem _ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) c
    simp only at hab
    have hb : (b : RingOfIntegers K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨(b : RingOfIntegers K) * d, mul_ne_zero hb hd, ?_⟩
    have key : ((b : RingOfIntegers K) * d) • (c • y) = a • (d • y) := by
      rw [← smul_assoc, Algebra.smul_def, map_mul, mul_comm (algebraMap _ K (b : RingOfIntegers K)),
        mul_assoc, mul_comm _ c, hab, ← map_mul, algebraMap_smul, mul_comm, mul_smul]
    rw [key]
    exact A.smul_mem _ h
end GlobalTheory.TargetLemmaCollection
