-- Prove2me | solution 1 for OAI.MatchingEntropy.second_deriv_quadratic_adjustment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:42:49.332957+00:00
-- url     : https://prove2.me/submissions/7eddc01f-262c-4c35-885f-8b8d719b6a01

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Calculus.lean:L149-L168
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.second_deriv_quadratic_adjustment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus

-- ---- from OAI.Combinatorics.PerfectMatching.Calculus ----
namespace OAI

/-!
Derivatives of entropy and log-partition, and the nonlinear entropy barrier.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

/-- A direct second-derivative calculation for the affine-law comparison
path used below. -/
theorem second_deriv_quadratic_adjustment {f fD g gD : ℝ → ℝ} {fDD gDD c₀ c₁ v : ℝ}
    (hf : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (fD t) t)
    (hg : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt g (gD t) t)
    (hfD : HasDerivAt fD fDD 0) (hgD : HasDerivAt gD gDD 0) :
    HasDerivAt (deriv (fun t => f t+c₀+t*c₁+t^2*v-g t))
      (fDD+2*v-gDD) 0 := by
  have hfirst : deriv (fun t => f t+c₀+t*c₁+t^2*v-g t) =ᶠ[𝓝 (0:ℝ)]
      (fun t => fD t+c₁+2*t*v-gD t) := by
    filter_upwards [hf, hg] with t hft hgt
    have hd := (((hft.add_const c₀).fun_add ((hasDerivAt_id t).mul_const c₁)).fun_add
      (((hasDerivAt_id t).fun_pow 2).mul_const v)).fun_sub hgt
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq, one_mul,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using hd.deriv
  have hd := ((hfD.add_const c₁).fun_add
    (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const v)).fun_sub hgD
  have hd' : HasDerivAt (fun t => fD t+c₁+2*t*v-gD t) (fDD+2*v-gDD) 0 := by
    simpa only [Pi.add_apply, Pi.sub_apply, id_eq, mul_one] using hd
  exact hd'.congr_of_eventuallyEq hfirst

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter

theorem solution {f fD g gD : ℝ → ℝ} {fDD gDD c₀ c₁ v : ℝ}
    (hf : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (fD t) t)
    (hg : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt g (gD t) t)
    (hfD : HasDerivAt fD fDD 0) (hgD : HasDerivAt gD gDD 0) :
    HasDerivAt (deriv (fun t => f t+c₀+t*c₁+t^2*v-g t))
      (fDD+2*v-gDD) 0 := by
  first
    | exact OAI.MatchingEntropy.second_deriv_quadratic_adjustment hf hg hfD hgD
    | exact OAI.MatchingEntropy.second_deriv_quadratic_adjustment
    | (apply OAI.MatchingEntropy.second_deriv_quadratic_adjustment <;> assumption)
    | (intros; apply OAI.MatchingEntropy.second_deriv_quadratic_adjustment <;> assumption)
