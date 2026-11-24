-- Prove2me | solution 1 for MomentComparison.cstar_le_inf_of_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:38.615372+00:00
-- url     : https://prove2.me/submissions/62d0856c-1c07-4eec-be5b-d0f5f5ef695a

module
public import Definitions.Def_MomentComparison_Pairing
public import Definitions.Def_MomentComparison_Conformal
public import Definitions.Def_MomentComparison_Hypercontractivity
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Real.ConjExponents
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Upper
public import Theorems.Thm_MomentComparison_moment_comparison_of_conjugate

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution {L : ℝ → ℝ}
    (hL : ∀ p, 2 < p → 0 < L p)
    (hReverse : ∀ p, 2 < p → ∀ {n d : ℕ} (f : Cube n → ℝ), HasDegreeLE f d →
      complexMomentNorm p (fun x => (f x : ℂ)) ≤
        L p ^ d * complexMomentNorm (p / (p - 1)) (fun x => (f x : ℂ))) :
    Cstar ≤ sInf ((fun p => L p ^ (p / (2 * (p - 2)))) '' Set.Ioi 2) := by
  refine le_csInf ⟨L 3 ^ ((3 : ℝ) / (2 * (3 - 2))), 3, by norm_num, rfl⟩ ?_
  rintro _ ⟨p, hp, rfl⟩
  have hp' : 2 < p := hp
  have hLp := hL p hp'
  apply csInf_le ⟨0, fun _ h => h.1.le⟩
  refine ⟨Real.rpow_pos_of_pos hLp _, ?_⟩
  intro n d hn hd f hf
  exact moment_comparison_of_conjugate hp' hLp f (hReverse p hp' f hf)
end MomentComparison
