-- Prove2me | solution 1 for GlobalTheory.Reg.exists_prime_natCast_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:55:19.284795+00:00
-- url     : https://prove2.me/submissions/d5cb48e7-e020-4b4e-8176-e3c59368b955

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringComapEqNonunits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.Reg
namespace GlobalTheory.Reg
theorem _root_.solution {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
  classical
  have hbot : la.asIdeal ≠ ⊥ := la.ne_bot
  have hprime : la.asIdeal.IsPrime := la.isPrime
  have main : ∀ n : ℕ, (n : 𝓞 K) ∈ la.asIdeal → n ≠ 0 → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hn0
      have hn1 : n ≠ 1 := by
        rintro rfl
        exact hprime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hn))
      obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
      rw [Nat.cast_mul] at hn
      rcases hprime.mem_or_mem hn with h | h
      · exact ⟨p, hp, h⟩
      · have hm0 : m ≠ 0 := by rintro rfl; simp at hn0
        refine ih m ?_ h hm0
        calc m = 1 * m := (_root_.one_mul m).symm
          _ < p * m := Nat.mul_lt_mul_of_pos_right hp.one_lt (Nat.pos_of_ne_zero hm0)
  exact main _ (Ideal.absNorm_mem la.asIdeal) (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
end GlobalTheory.Reg
