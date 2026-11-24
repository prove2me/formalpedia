-- Prove2me | solution 1 for GlobalTheory.LatticeDatum.exists_nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:52.025385+00:00
-- url     : https://prove2.me/submissions/9d147e70-98f0-4d1e-b39b-33a28e689b6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeDatumOfSelfDualLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix nonZeroDivisors TensorProduct
open GlobalTheory GlobalTheory.LatticeDatum
namespace GlobalTheory.LatticeDatum
theorem _root_.solution {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module (𝓞 E) V] [Module E V]
    [IsScalarTower (𝓞 E) E V] (A B : Submodule (𝓞 E) V) (hA : A.FG)
    (hB : Submodule.span E (B : Set V) = ⊤) : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ A, N • x ∈ B := by
  have h1 : ∀ v : V, ∃ N : ℕ, 0 < N ∧ N • v ∈ B := fun v => by
    have hv : v ∈ Submodule.span E (B : Set V) := by rw [hB]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv
    rw [Submodule.span_eq] at ht
    have ht0 : (t : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero t
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {(t : 𝓞 E)}))
    refine ⟨Ideal.absNorm (Ideal.span {(t : 𝓞 E)}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ht0
    · rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hs, mul_smul]
      exact B.smul_mem s ht
  obtain ⟨S, rfl⟩ := hA
  choose n hn0 hn using h1
  refine ⟨∏ s ∈ S, n s, Finset.prod_pos fun s _ => hn0 s, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_coe.mp hx)
    rw [hk, mul_comm, mul_smul]
    exact B.toAddSubmonoid.nsmul_mem (hn x) k
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact B.smul_mem c hx
end GlobalTheory.LatticeDatum
