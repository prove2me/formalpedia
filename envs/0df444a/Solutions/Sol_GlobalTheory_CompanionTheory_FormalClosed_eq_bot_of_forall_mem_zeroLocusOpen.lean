-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FormalClosed.eq_bot_of_forall_mem_zeroLocusOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:58:38.382973+00:00
-- url     : https://prove2.me/submissions/9d2831c5-9a98-47d7-887e-ce6bb93204e4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_FormalAlgebraisation_GEClosedProj
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsIsoOfIsClosedImmersionOfThickenings
import Theorems.Thm_GlobalTheory_ThickeningClosed_exists_mul_eq_zero_of_mem
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FormalClosed
open GlobalTheory.ThickeningClosed
namespace GlobalTheory.CompanionTheory.FormalClosed
theorem _root_.solution {X : Scheme.{0}} (K : X.IdealSheafData)
    (h : ∀ x, x ∈ zeroLocusOpen K) : K = ⊥ := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_bot]
  apply le_antisymm _ bot_le
  intro a ha
  rw [Ideal.mem_bot]
  by_contra ha0
  let J : Ideal Γ(X, U) := LinearMap.ker (LinearMap.toSpanSingleton Γ(X, U) Γ(X, U) a)
  have hJ : J ≠ ⊤ := by
    intro hJ
    apply ha0
    have h1 : (1 : Γ(X, U)) ∈ J := by rw [hJ]; exact Submodule.mem_top
    simpa [J] using h1
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨s, hs, hsa⟩ := exists_mul_eq_zero_of_mem K U ⟨m, hm.isPrime⟩ (h _) ha
  apply hs
  apply hJm
  simpa [J] using hsa
end GlobalTheory.CompanionTheory.FormalClosed
