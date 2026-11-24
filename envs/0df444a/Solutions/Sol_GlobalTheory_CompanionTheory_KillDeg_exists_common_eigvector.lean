-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KillDeg.exists_common_eigvector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:40:50.280516+00:00
-- url     : https://prove2.me/submissions/c11cd6be-6e1b-47bb-9778-64847fe86304

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsRecurrencePolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KillDeg
namespace GlobalTheory.CompanionTheory.KillDeg
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ι : Type*} (f : ι → Module.End ℂ V) (hc : ∀ i j, Commute (f i) (f j))
    (W : Submodule ℂ V) (hW : W ≠ ⊥) (hinv : ∀ i, ∀ w ∈ W, f i w ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ μ : ℂ, f i v = μ • v := by
  classical
  let P : ℕ → Prop := fun n => ∃ U : Submodule ℂ V, U ≤ W ∧ U ≠ ⊥ ∧
    (∀ i, ∀ w ∈ U, f i w ∈ U) ∧ Module.finrank ℂ U = n
  have hP : ∃ n, P n := ⟨_, W, le_rfl, hW, hinv, rfl⟩
  obtain ⟨U, hUW, hU, hUinv, hUn⟩ := Nat.find_spec hP
  have hmin : ∀ U' : Submodule ℂ V, U' ≤ U → U' ≠ ⊥ → (∀ i, ∀ w ∈ U', f i w ∈ U') → U' = U := by
    intro U' hle hne hinv'
    have h1 : Nat.find hP ≤ Module.finrank ℂ U' :=
      Nat.find_min' hP ⟨U', hle.trans hUW, hne, hinv', rfl⟩
    exact Submodule.eq_of_le_of_finrank_le hle (by omega)
  obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  refine ⟨v, hUW hvU, hv0, fun i => ?_⟩
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU
  let r : Module.End ℂ U := (f i).restrict (hUinv i)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue r
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hxe : f i (x : V) = μ • (x : V) := by
    have := congrArg Subtype.val hx.apply_eq_smul
    simpa [r] using this
  have hx0 : (x : V) ≠ 0 := by
    intro h
    exact hx.2 (Subtype.ext h)
  let U' : Submodule ℂ V := U ⊓ Module.End.eigenspace (f i) μ
  have hU' : U' = U := by
    refine hmin U' inf_le_left ?_ ?_
    · intro hb
      have hxm : (x : V) ∈ U' := ⟨x.2, Module.End.mem_eigenspace_iff.2 hxe⟩
      rw [hb] at hxm
      exact hx0 (by simpa using hxm)
    · intro j w hw
      refine ⟨hUinv j w hw.1, Module.End.mem_eigenspace_iff.2 ?_⟩
      have hwe : f i w = μ • w := Module.End.mem_eigenspace_iff.1 hw.2
      have hcomm : f i (f j w) = f j (f i w) := by
        have := congrArg (fun e : Module.End ℂ V => e w) (hc i j).eq
        simpa using this
      rw [hcomm, hwe, map_smul]
  have hvm : v ∈ U' := by rw [hU']; exact hvU
  exact ⟨μ, Module.End.mem_eigenspace_iff.1 hvm.2⟩
end GlobalTheory.CompanionTheory.KillDeg
