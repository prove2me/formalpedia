-- Prove2me | solution 1 for GlobalTheory.bilinForm_bijective_of_nondegenerate_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:24:31.853719+00:00
-- url     : https://prove2.me/submissions/196beeba-c81c-4553-9196-41f55fe4d7d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_BilinFormBijectiveOfNondegenerateMod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (E : LinearMap.BilinForm ℤ X)
    (h : ∀ (k : ℕ) (a : X), 0 < k → (∀ b, (k : ℤ) ∣ E a b) → ∃ a', a = (k : ℤ) • a') :
    Function.Bijective E := by
  classical
  set b := Module.Free.chooseBasis ℤ X
  have hinj : Function.Injective E := by
    refine (injective_iff_map_eq_zero E).2 fun a ha => ?_
    refine b.ext_elem fun i => ?_
    obtain ⟨n, hn⟩ : ∃ n, (b.repr a i).natAbs = n := ⟨_, rfl⟩
    obtain ⟨a', ha'⟩ := h (n + 1) a (Nat.succ_pos n) (fun y => by rw [ha]; simp)
    have hdvd : ((n + 1 : ℕ) : ℤ) ∣ b.repr a i := ⟨b.repr a' i, by rw [ha']; simp⟩
    rw [map_zero, Finsupp.zero_apply]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd ?_
    rw [Int.natAbs_natCast, hn]
    exact Nat.lt_succ_self n
  have hrank : Module.rank ℤ (Module.Dual ℤ X ⧸ LinearMap.range E) = 0 := by
    have h1 := rank_quotient_add_rank_of_isDomain (LinearMap.range E)
    rw [← (LinearEquiv.ofInjective E hinj).rank_eq, ← b.toDualEquiv.rank_eq] at h1
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 (Module.rank_lt_aleph0 ℤ X)
    have hq : Module.rank ℤ (Module.Dual ℤ X ⧸ LinearMap.range E) < Cardinal.aleph0 :=
      lt_of_le_of_lt (le_self_add) (h1 ▸ Module.rank_lt_aleph0 ℤ X)
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hq
    rw [hm, hn] at h1
    rw [hm]
    have : m + n = n := by exact_mod_cast h1
    exact_mod_cast (by omega : m = 0)
  refine ⟨hinj, fun f => ?_⟩
  obtain ⟨c, hc0, hcf⟩ := rank_eq_zero_iff.1 hrank (Submodule.Quotient.mk f)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcf
  obtain ⟨x, hx⟩ := hcf
  have hk : 0 < c.natAbs * c.natAbs := Nat.mul_pos (Int.natAbs_pos.2 hc0) (Int.natAbs_pos.2 hc0)
  obtain ⟨a', ha'⟩ := h (c.natAbs * c.natAbs) (c • x) hk (fun y => by
    rw [Int.natAbs_mul_self, map_smul, hx, smul_smul]
    simp)
  refine ⟨a', ?_⟩
  have hEq : E (c • x) = ((c.natAbs * c.natAbs : ℕ) : ℤ) • f := by
    rw [Int.natAbs_mul_self, map_smul, hx, smul_smul]
  rw [ha', map_smul] at hEq
  ext y
  have hy := LinearMap.congr_fun hEq y
  simp only [LinearMap.smul_apply, smul_eq_mul] at hy
  exact mul_left_cancel₀ (by exact_mod_cast hk.ne') hy
end GlobalTheory
