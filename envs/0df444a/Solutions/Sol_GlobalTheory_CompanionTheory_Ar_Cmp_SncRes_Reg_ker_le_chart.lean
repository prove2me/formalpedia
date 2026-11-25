-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.ker_le_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:04:29.079318+00:00
-- url     : https://prove2.me/submissions/292e5995-667e-4d7d-b8fe-692fb0af4f41

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_exists_homogenised

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
theorem _root_.solution (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (g : MvPolynomial (Σ k, ι k) ℚ)
    (hg : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) g = 0) :
    map (algebraMap ℚ ℂ) g ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
  obtain ⟨d, H, E, hd, ha, hb, -⟩ := exists_homogenised K ι Ω y c hc
    (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c)
    (fun k => Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)) g
  have hH : H ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker]
    rw [ha, hg]
    simp
  have hHC : map (Int.castRingHom ℂ) H ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c :=
    Ideal.mem_sup_left (Ideal.subset_span ⟨H, hH, rfl⟩)
  have h2 : MvPolynomial.C (d : ℂ) * map (algebraMap ℚ ℂ) g ∈
      ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
    have := Ideal.sub_mem _ hHC hb
    simpa using this
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have h3 := Ideal.mul_mem_left _ (MvPolynomial.C (d : ℂ)⁻¹) h2
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hd', map_one, one_mul] at h3
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
