-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.card_le_finrank_jacSpanAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:42:22.537817+00:00
-- url     : https://prove2.me/submissions/ec54896d-1156-442c-8861-c812bd1c3c54

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_ker_le_chart
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_card_le_of_kaehler

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
theorem _root_.solution (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)) (hsnc : IsSncModel y e J)
    (p : (k : K) → ι k) (hp : ∀ k, y ⟨k, p k⟩ ≠ 0) (w : (Σ k, ι k) → ℂ)
    (hw : ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p, eval w h = 0) :
    Fintype.card (Σ k, ι k) ≤
      Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p) w) + e := by
  classical
  have hkerC := ker_le_chart K ι Ω y p hp
  have hkerw : ∀ g : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) g = 0 →
      eval w (map (algebraMap ℚ ℂ) g) = 0 :=
    fun g hg => hw _ (hkerC g hg)
  obtain ⟨m, f, a, hf, ha, hsum, hS⟩ := hsnc p hp
  have hadj : ∀ s ∈ Algebra.adjoin ℚ (Set.range fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩),
      ∃ F : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F = s := by
    intro s hs
    rw [Algebra.adjoin_range_eq_range_aeval] at hs
    exact hs
  choose F hF using fun l => hadj (f l) (hf l)
  choose A hA using fun l => hadj (a l) (ha l)
  obtain ⟨l, hl⟩ : ∃ l, eval w (map (algebraMap ℚ ℂ) (F l)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := hkerw (∑ l, A l * F l - 1) (by
      simp only [map_sub, map_sum, map_mul, map_one, hF, hA]
      rw [hsum, sub_self])
    simp [hcon] at h0
  have hfl : f l ≠ 0 := fun h0 => hl (hkerw _ (by rw [hF, h0]))
  obtain ⟨-, z, n, -, -, hspan, -⟩ := hS l hfl _ rfl
  refine card_le_of_kaehler (Σ k, ι k) Ω _ (ReciprocityTheory.AnForm.R.jacSpanAt _ w) w (F l) (by rw [hF]; exact hfl) hl hkerw
    (fun g hg => Submodule.subset_span ⟨_, hkerC g hg, rfl⟩) _ (by rw [hF]) e z hspan
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
