-- Prove2me | solution 1 for GlobalTheory.CoordinateBasisBounds.coord_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:58:36.325058+00:00
-- url     : https://prove2.me/submissions/2166fcd1-f2ca-4bbd-9d4b-940b39208be0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatMulIntegral
import Theorems.Thm_GlobalTheory_CoordinateBasisBounds_nat_mul_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoordinateBasisBounds
open NumberField
namespace GlobalTheory.CoordinateBasisBounds
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, ∀ i : Fin n, ∃ o : 𝓞 E, (N : E) * x i = algebraMap (𝓞 E) E o := by
  obtain ⟨S, hS⟩ := hL
  have key : ∀ v ∈ S, ∃ m : ℕ, 0 < m ∧ ∀ i : Fin n, ∃ o : 𝓞 E, (m : E) * v i = algebraMap (𝓞 E) E o := by
    intro v _
    choose m hm o ho using fun i : Fin n => nat_mul_integral (v i)
    refine ⟨∏ i, m i, Finset.prod_pos (fun i _ => hm i), fun i => ?_⟩
    have hd : m i ∣ ∏ j, m j := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := hd
    refine ⟨(k : 𝓞 E) * o i, ?_⟩
    rw [hk, map_mul, ← ho i, map_natCast]; push_cast; ring
  classical
  choose! m hm hv using key
  refine ⟨∏ v ∈ S, m v, Finset.prod_pos (fun v hv' => hm v hv'), ?_⟩
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem v hvS =>
    intro i
    obtain ⟨o, ho⟩ := hv v hvS i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hvS
    refine ⟨(k : 𝓞 E) * o, ?_⟩
    rw [hk, map_mul, ← ho, map_natCast]; push_cast; ring
  | zero => intro i; exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨a, ha⟩ := hx i
    obtain ⟨b, hb⟩ := hy i
    exact ⟨a + b, by rw [map_add, ← ha, ← hb, Pi.add_apply]; ring⟩
  | smul c x _ hx =>
    intro i
    obtain ⟨a, ha⟩ := hx i
    refine ⟨c * a, ?_⟩
    rw [map_mul, ← ha, Pi.smul_apply, Algebra.smul_def]; ring
end GlobalTheory.CoordinateBasisBounds
