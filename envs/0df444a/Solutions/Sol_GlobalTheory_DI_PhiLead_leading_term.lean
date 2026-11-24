-- Prove2me | solution 1 for GlobalTheory.DI.PhiLead.leading_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:22.561798+00:00
-- url     : https://prove2.me/submissions/cc6c7112-479c-4109-9d68-b31b7c0889a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAntisymmetrizedCupProductLeadingTerm
import Theorems.Thm_GlobalTheory_DI_PhiLead_alt_single
import Theorems.Thm_GlobalTheory_DI_PhiLead_gamma_iMulti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.PhiLead
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]
namespace GlobalTheory.DI.PhiLead
theorem _root_.solution : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (j : ι), alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k))) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (j : ι) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V), IsPhi p f h Φ → IsGamma p (f j) γ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, Φ x {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x := by
  intro K _ V _ _ ι _ p f h
  refine ⟨fun a v j => alt_single f h a v j, ?_⟩
  intro Φ j γ hΦ hγ a x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, -, v, -, rfl⟩ := hx
    have hg : γ (b • ExteriorAlgebra.ιMulti K a v) = b ^ p • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
      rw [Algebra.smul_def, map_mul, hγ.1, gamma_iMulti p (f j) γ hγ, ← Algebra.smul_def]
    rw [hΦ, Pi.smul_apply, alt_single, hg, smul_comm]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy, smul_add]
  | neg x _ hx => simp [hx, smul_neg]
end GlobalTheory.DI.PhiLead
