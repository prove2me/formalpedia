-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.ae_continuousAt_hardKernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:01:05.850492+00:00
-- url     : https://prove2.me/submissions/d62d43d0-8085-47ea-94d8-0581837d2b56

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_HardPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridCell
import Definitions.Def_OAI_Analysis_TriangularHilbert_Quantization
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridLine
import Definitions.Def_OAI_Analysis_TriangularHilbert_BoundedBox
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledOutput
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicSlice
import Definitions.Def_OAI_Analysis_TriangularHilbert_RationalSup

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
lemma h43_ind_contAt (r x : ℝ) (hx : |x| ≠ r) :
    ContinuousAt (fun t : ℝ => if r < |t| then (1:ℝ) else 0) x := by
  rcases lt_or_gt_of_ne hx with h | h
  · have hev : ∀ᶠ t in nhds x, |t| < r :=
      (continuous_abs.continuousAt).eventually (gt_mem_nhds h)
    refine (continuousAt_const (y := (0:ℝ))).congr ?_
    filter_upwards [hev] with t ht
    simp [not_lt.mpr ht.le]
  · have hev : ∀ᶠ t in nhds x, r < |t| :=
      (continuous_abs.continuousAt).eventually (lt_mem_nhds h)
    refine (continuousAt_const (y := (1:ℝ))).congr ?_
    filter_upwards [hev] with t ht
    simp [ht]

theorem solution (r R a : ℝ) : ∀ᵐ c : ℝ, ContinuousAt (hardKernel r R) (a+c) := by
  have hfin : ({-a, r-a, -r-a, R-a, -R-a} : Set ℝ).Countable := (Set.toFinite _).countable
  filter_upwards [hfin.ae_notMem volume] with c hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hc
  obtain ⟨h0, h1, h2, h3, h4⟩ := hc
  set x := a + c with hx
  have hx0 : x ≠ 0 := by intro h; apply h0; linarith
  have habs : ∀ s : ℝ, s - a ≠ c → -s - a ≠ c → |x| ≠ s := by
    intro s hs1 hs2 h
    rcases abs_choice x with h' | h'
    · exact hs1 (by linarith)
    · exact hs2 (by linarith)
  have hr : |x| ≠ r := habs r (fun h => h1 h.symm) (fun h => h2 h.symm)
  have hR : |x| ≠ R := habs R (fun h => h3 h.symm) (fun h => h4 h.symm)
  unfold hardKernel
  exact ((h43_ind_contAt r x hr).sub (h43_ind_contAt R x hR)).div continuousAt_id hx0

