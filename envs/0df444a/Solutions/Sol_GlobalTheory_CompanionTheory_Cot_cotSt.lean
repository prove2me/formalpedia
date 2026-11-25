-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Cot.cotSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:54.248175+00:00
-- url     : https://prove2.me/submissions/cf9f960f-d1f0-411d-b112-23de534c8619

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodAffineStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodProductZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdealSquareLeKernelOfSquareZeroMapStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VectorBundleOfLocalFreenessStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExistsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLocalChartAtPrimeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsNbhd
import Theorems.Thm_GlobalTheory_CompanionTheory_Cot_exists_nbhd
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_T_closed_immersion_universal_square_zero
import Theorems.Thm_GlobalTheory_T_cotangent_local_open_chart_exists
import Theorems.Thm_GlobalTheory_T_exists_local_chart_at_prime
import Theorems.Thm_GlobalTheory_T_vector_bundle_of_local_freeness
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Cot
namespace GlobalTheory.CompanionTheory.Cot
theorem _root_.solution : CotSt := by
  intro R _ X s e g he hs
  obtain ⟨P, _, α, ε, j, h1, h2, h3, h4, h5, h6⟩ := exists_nbhd R X s e he
  obtain ⟨W, i1, i2, i3, i4, y₀, hy⟩ := GlobalTheory.T.closed_immersion_universal_square_zero R X s e P α ε j h1 h2 h3 h4 h5 h6
  refine ⟨W, i1, i2, i3, i4, y₀, GlobalTheory.T.vector_bundle_of_local_freeness R W g fun p ↦ ?_, hy⟩
  obtain ⟨r, A, C, _, _, _, _, j, k, hr, _, _, hjs, hε, f1, f2, f3⟩ := GlobalTheory.T.exists_local_chart_at_prime R X s e g he hs p
  obtain ⟨E⟩ := GlobalTheory.T.cotangent_local_open_chart_exists R X s e he W y₀ hy r A C j k hjs hε
  have : Nontrivial (Localization.Away r) := by
    refine ⟨⟨algebraMap R _ 1, algebraMap R _ 0, fun h ↦ ?_⟩⟩
    obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers r) _).1 h
    have h0 : r ^ n ∈ p.asIdeal := by
      have : r ^ n = 0 := by simpa using hc
      rw [this]; exact zero_mem _
    exact hr (p.2.mem_of_pow_mem n h0)
  have : Nontrivial A := (algebraMap A (Localization.Away r)).domain_nontrivial
  have hf : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W) := Module.Free.of_equiv E.symm
  have hn : Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W) := Module.Finite.equiv E.symm
  exact ⟨r, hr, hf, hn, by rw [E.finrank_eq, Module.finrank_baseChange, f3]⟩
end GlobalTheory.CompanionTheory.Cot
