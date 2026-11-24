-- Prove2me | solution 1 for GlobalTheory.TargetStatementSixOneNinetySeven.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:27:46.233787+00:00
-- url     : https://prove2.me/submissions/be3f6421-b53a-472b-a729-b9f4e9b1b698

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ImportsMore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TargetStatementSixOneNinetySeven
open Module
namespace GlobalTheory.TargetStatementSixOneNinetySeven
theorem _root_.solution {ι E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    (f : ι → Module.End ℂ E) (hc : ∀ i j, Commute (f i) (f j)) :
    ∃ x : E, x ≠ (0 : E) ∧ ∀ i, ∃ μ : ℂ, (f i : E → E) x = μ • x := by
  classical
  let P : Submodule ℂ E → Prop := fun p => p ≠ ⊥ ∧ ∀ i, ∀ x ∈ p, f i x ∈ p
  have hex : ∃ n, ∃ p : Submodule ℂ E, finrank ℂ p = n ∧ P p :=
    ⟨_, ⊤, rfl, top_ne_bot, fun i x _ => Submodule.mem_top⟩
  obtain ⟨p, hpn, hpb, hpi⟩ := Nat.find_spec hex
  have hmin : ∀ q : Submodule ℂ E, P q → finrank ℂ p ≤ finrank ℂ q := by
    intro q hq
    rw [hpn]
    exact Nat.find_min' hex ⟨q, rfl, hq⟩
  have hscal : ∀ i, ∃ μ : ℂ, ∀ x ∈ p, f i x = μ • x := by
    intro i
    haveI : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hpb
    let g : Module.End ℂ p := (f i).restrict (hpi i)
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue g
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    refine ⟨μ, ?_⟩
    let q : Submodule ℂ E := p ⊓ Module.End.eigenspace (f i) μ
    have hvq : (v : E) ∈ q := by
      refine Submodule.mem_inf.mpr ⟨v.2, ?_⟩
      rw [Module.End.mem_eigenspace_iff]
      have h1 := Module.End.mem_eigenspace_iff.mp hv.1
      have h2 := congrArg Subtype.val h1
      simpa [g] using h2
    have hqb : q ≠ ⊥ := by
      intro h
      have h0 : (v : E) = 0 := by rw [h] at hvq; exact (Submodule.mem_bot ℂ).mp hvq
      exact hv.2 (Subtype.ext h0)
    have hqi : ∀ j, ∀ x ∈ q, f j x ∈ q := by
      intro j x hx
      refine Submodule.mem_inf.mpr ⟨hpi j x (Submodule.mem_inf.mp hx).1, ?_⟩
      rw [Module.End.mem_eigenspace_iff]
      have hx2 := Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp hx).2
      have hcomm : f i (f j x) = f j (f i x) := by
        have h3 := (hc i j).eq
        exact congrArg (fun T : Module.End ℂ E => T x) h3
      rw [hcomm, hx2, map_smul]
    have hle : q ≤ p := inf_le_left
    have heq : q = p := Submodule.eq_of_le_of_finrank_le hle (hmin q ⟨hqb, hqi⟩)
    intro x hx
    rw [← heq] at hx
    exact Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp hx).2
  obtain ⟨x, hxp, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpb
  refine ⟨x, hx0, fun i => ?_⟩
  obtain ⟨μ, hμ⟩ := hscal i
  exact ⟨μ, hμ x hxp⟩
end GlobalTheory.TargetStatementSixOneNinetySeven
