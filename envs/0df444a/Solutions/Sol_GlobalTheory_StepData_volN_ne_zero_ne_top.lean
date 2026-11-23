-- Prove2me | solution 1 for GlobalTheory.StepData.volN_ne_zero_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:02.262557+00:00
-- url     : https://prove2.me/submissions/8c509513-6ca0-4faa-b440-4fdac8c615a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_RootEx_Model_coord_embedding
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.StepData
theorem _root_.solution [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {c : ℕ} (p : ℕ)
    {H : Subgroup (GL (n ⊕ Fin c) k)} (ho : IsOpen (H : Set (GL (n ⊕ Fin c) k)))
    (hc : IsCompact (H : Set (GL (n ⊕ Fin c) k))) :
    RootEx.volN ν n c p (H.subgroupOf (RootEx.N k n c p)) ≠ 0 ∧
      RootEx.volN ν n c p (H.subgroupOf (RootEx.N k n c p)) ≠ ⊤ := by
  classical
  haveI := secondCountable k
  haveI := t2Space k
  unfold RootEx.volN
  rw [(RootEx.Model.coord_embedding (k := k) (n := n) (c := c) p).1.comap_apply]
  constructor
  · have hcont : Continuous fun e => (RootEx.Model.mkNel (k := k) (n := n) (c := c) p e : GL (n ⊕ Fin c) k) := by
      rw [SplitFlip.isEmbedding_val_GL.continuous_iff]
      refine continuous_pi fun r => continuous_pi fun s => ?_
      change Continuous fun e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // RootEx.lev p rs.1 < RootEx.lev p rs.2} → k =>
        RootEx.Model.mkN (k := k) p e r s
      by_cases h : RootEx.lev p r < RootEx.lev p s
      · simp only [RootEx.Model.mkN, Matrix.of_apply, dif_pos h]; exact continuous_apply _
      · simp only [RootEx.Model.mkN, Matrix.of_apply, dif_neg h]; exact continuous_const
    refine (lt_of_lt_of_le ((ho.preimage hcont).measure_pos _ ⟨0, ?_⟩) (measure_mono fun e he => ?_)).ne'
    · have : (RootEx.Model.mkNel (k := k) (n := n) (c := c) p 0 : GL (n ⊕ Fin c) k) = 1 := by
        ext r s
        change RootEx.Model.mkN (k := k) p 0 r s = (1 : Matrix _ _ k) r s
        by_cases h : RootEx.lev p r < RootEx.lev p s
        · have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
          simp [RootEx.Model.mkN, this]
        · simp [RootEx.Model.mkN, h]
      simp [this]
    · refine ⟨RootEx.Model.mkNel p e, he, funext fun rs => ?_⟩
      change RootEx.Model.mkN p e _ _ = _
      simp [RootEx.Model.mkN, rs.2]
  · have hcont : Continuous fun (g : GL (n ⊕ Fin c) k)
        (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // RootEx.lev p rs.1 < RootEx.lev p rs.2}) => g.val rs.1.1 rs.1.2 := by
      have := Units.continuous_val (M := Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
      fun_prop
    refine (lt_of_le_of_lt (measure_mono ?_) (hc.image hcont).measure_lt_top).ne
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
end GlobalTheory.StepData
