-- Prove2me | solution 1 for GlobalTheory.FinEt.IsSplitOfRank.etale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:50.757662+00:00
-- url     : https://prove2.me/submissions/b32ad8c3-f5f6-42c0-b504-c418ac7d4531

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_iff_exists_iso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}
namespace GlobalTheory.FinEt
namespace IsSplitOfRank
theorem _root_.solution {X S : Scheme.{u}} {p : X ⟶ S} {n : ℕ} (h : IsSplitOfRank p n) :
    Etale p := by
  obtain ⟨e, he⟩ := (isSplitOfRank_iff_exists_iso p n).mp h
  have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  have : Etale (Sigma.desc fun _ : Fin n ↦ 𝟙 S) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ ↦ inferInstance
  rw [← e.inv_hom_id_assoc p, he]
  infer_instance
end IsSplitOfRank
end GlobalTheory.FinEt
