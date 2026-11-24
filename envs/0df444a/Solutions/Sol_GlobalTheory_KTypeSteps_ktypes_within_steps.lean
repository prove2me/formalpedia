-- Prove2me | solution 1 for GlobalTheory.KTypeSteps.ktypes_within_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:02:46.157546+00:00
-- url     : https://prove2.me/submissions/fd9f2532-0000-4e6c-b140-dc3b9ee15845

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_KtypesWithinSteps
import Theorems.Thm_GlobalTheory_KTypeSteps_sqrt_nsq_add_le
import Theorems.Thm_GlobalTheory_KTypeSteps_nsq_root
import Theorems.Thm_GlobalTheory_KTypeSteps_pfil_one_le_ker
import Theorems.Thm_GlobalTheory_KTypeSteps_ew_mem_pfil
import Theorems.Thm_Formalism_REAL_compact_highest_weight_unique
import Theorems.Thm_Formalism_REAL_compact_span_le_of_stable
import Theorems.Thm_Formalism_REAL_glRel_kRel
import Theorems.Thm_Formalism_REAL_isUnitary_kUnit
import Theorems.Thm_Formalism_REAL_kDecomp
import Theorems.Thm_Formalism_REAL_kLow
import Theorems.Thm_Formalism_REAL_kWtOrth
import Theorems.Thm_Formalism_REAL_pfilFacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.KTypeSteps
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace GlobalTheory.KTypeSteps
theorem _root_.solution :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E →
      KHighest ε E Λ u → FiniteDimensional ℂ (kSpan ε E u) →
      ∀ (j : ℕ) (μ : Fin n → ℝ), ∀ x ∈ pfil ε E u j, x ≠ 0 → KHighest ε E μ x →
        Real.sqrt (nsq (μ - Λ)) ≤ Real.sqrt 2 * j := by
  intro V _ _ n ε E Λ u hg hu hΛ hfd j
  obtain ⟨h0, -, hst, -, -, -, hfin⟩ := pfilFacts V n ε E u hg
  induction j with
  | zero =>
    intro μ x hx hx0 hhi
    rw [h0] at hx
    have := compact_highest_weight_unique kLow kWtOrth hg hu hΛ hx hhi hx0
    subst this
    simp [nsq, dot]
  | succ j ih =>
    intro μ x hx hx0 hhi
    by_contra hlt
    rw [not_le] at hlt
    push_cast at hlt
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have := hfin hfd j
    obtain ⟨m, y, lam, hy, -, hsup⟩ := kDecomp V n ε E (pfil ε E u j) inferInstance
      (glRel_kRel ε E hg) (isUnitary_kUnit ε E hu) (hst j)
    have hone : ∀ i, pfil ε E (y i) 1 ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      intro i
      obtain ⟨hmem, hy0, hyh⟩ := hy i
      have hb := ih (lam i) (y i) hmem hy0 hyh
      refine pfil_one_le_ker hg hu hhi hyh
        (Submodule.finiteDimensional_of_le (compact_span_le_of_stable (hst j) hmem)) ?_ ?_
      · intro h
        rw [h] at hlt
        nlinarith
      · intro a b hab h
        have hab' : a ≠ b := fun h => hab (h ▸ rfl)
        have ht := sqrt_nsq_add_le (lam i - Λ) (root a b)
        rw [nsq_root hab'] at ht
        have he : μ - Λ = lam i - Λ + root a b := by rw [h]; abel
        rw [he] at hlt
        nlinarith
    have hA : pfil ε E u j ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      rw [← hsup]
      refine iSup_le fun i => le_trans ?_ (hone i)
      obtain ⟨g0, g1, -⟩ := pfilFacts V n ε E (y i) hg
      rw [← g0]
      exact g1 0
    have hB : ∀ a b, pfil ε E u j ≤ (LinearMap.ker (innerₛₗ ℂ x)).comap (E a b) := by
      intro a b
      rw [← hsup]
      refine iSup_le fun i z hz => hone i ?_
      obtain ⟨g0, -, -, g3, -⟩ := pfilFacts V n ε E (y i) hg
      rw [← g0] at hz
      exact g3 0 a b z hz
    have hC : pfil ε E u (j + 1) ≤ LinearMap.ker (innerₛₗ ℂ x) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, hw, hp, z, hz, rfl⟩
      cases w with
      | nil => exact hA (ew_mem_pfil (Nat.zero_le j) hp hz)
      | cons p w =>
        have hw' : w.length ≤ j := by simpa using hw
        exact hB p.1 p.2 (ew_mem_pfil hw' (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hz)
    have := hC hx
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply] at this
    exact hx0 (inner_self_eq_zero.mp this)
end GlobalTheory.KTypeSteps
