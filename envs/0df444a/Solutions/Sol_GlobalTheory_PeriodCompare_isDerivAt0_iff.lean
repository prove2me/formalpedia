-- Prove2me | solution 1 for GlobalTheory.PeriodCompare.isDerivAt0_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:36.203677+00:00
-- url     : https://prove2.me/submissions/d27e014d-3039-4bd2-92c1-67ffecc00f2f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PeriodMapPresentation_Presents_unique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
namespace GlobalTheory.PeriodCompare
theorem _root_.solution {g : ℕ} {F : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {B : Set (Fin g → ℂ)} (hB : B ∈ 𝓝 0) (hF : HolOn B F)
    (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 F w v ↔ IsDerivAlong F w v := by
  refine and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => ?_
  have hU0 : ⊤ ≤ F 0 ⁻¹ᵁ U := by
    rw [← h0]
    exact fun x _ => hU (x := _) trivial
  obtain ⟨h1, h2⟩ := hF U 0 (mem_of_mem_nhds hB) hU0
  rw [nhdsWithin_eq_nhds.2 hB] at h1
  have hl : HasDerivAt (fun t : ℂ => t • w) w 0 := by simpa using (hasDerivAt_id (0 : ℂ)).smul_const w
  have hd : ∀ f : Γ(X, U), HasDerivAt (fun t : ℂ => valAt' (F (t • w)) U f)
      (fderiv ℂ (fun z => valAt' (F z) U f) 0 w) 0 := fun f =>
    HasFDerivAt.comp_hasDerivAt_of_eq (l := fun z => valAt' (F z) U f) (f := fun t : ℂ => t • w) 0
      ((h2 f).differentiableAt hB).hasFDerivAt hl (zero_smul ℂ w).symm
  constructor
  · intro h
    refine ⟨Filter.Tendsto.eventually (f := fun t : ℂ => t • w) (by simpa using hl.continuousAt.tendsto) h1,
      fun f => ?_⟩
    have := hd f
    rwa [← h f] at this
  · exact fun h f => (h.2 f).unique (hd f)
end GlobalTheory.PeriodCompare
