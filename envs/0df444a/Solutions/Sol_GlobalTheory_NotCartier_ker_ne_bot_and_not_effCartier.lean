-- Prove2me | solution 1 for GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:24:40.861312+00:00
-- url     : https://prove2.me/submissions/09d50454-82cc-4b0b-a102-3fe819499811

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerNeBotAndNotEffCartier
import Theorems.Thm_GlobalTheory_NotCartier_ringKrullDim_stalk_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
noncomputable section
open GlobalTheory GlobalTheory.NotCartier
namespace GlobalTheory.NotCartier
theorem _root_.solution : ∀ {W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian Y] (i : W ⟶ Y)
    [IsClosedImmersion i], 2 ≤ ringKrullDim (Y.presheaf.stalk (i (genericPoint W))) →
    i.ker ≠ ⊥ ∧ ∀ U : Y.Opens, i (genericPoint W) ∈ U → ¬ FinalTheorems.EffCartier (i.ker.comap U.ι) := by
  intro W Y _ _ i _ hdim
  set y := i (genericPoint W) with hy
  have hsub : (i.ker.support : Set Y) ⊆ closure {y} := by
    rw [Scheme.Hom.support_ker]
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ closure {genericPoint W} := by
      rw [(genericPoint_spec W).def]; trivial
    exact specializes_iff_mem_closure.1 ((specializes_iff_mem_closure.2 hw).map i.continuous)
  have hyS : y ∈ i.ker.support := by
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker]; exact subset_closure ⟨_, rfl⟩
  have hmin : ∀ z ∈ i.ker.support, z ⤳ y → z = y := fun z hz hzy =>
    (hzy.antisymm (specializes_iff_mem_closure.2 (hsub hz))).eq
  have hlt : ¬ ringKrullDim (Y.presheaf.stalk y) ≤ 1 := fun h => by
    have := hdim.trans h
    exact absurd this (by decide)
  refine ⟨fun hbot => ?_, fun U hyU hC => ?_⟩
  · obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    refine hlt (ringKrullDim_stalk_le_one i.ker y hyS hmin ⟨V, hV⟩ hyV ?_)
    rw [hbot, Scheme.IdealSheafData.ideal_bot]
    exact bot_isPrincipal
  · let x : U.toScheme := ⟨y, hyU⟩
    obtain ⟨V, f, hxV, -, hf⟩ := hC x
    have hxS : x ∈ (i.ker.comap U.ι).support := by
      rw [Scheme.IdealSheafData.support_comap]; exact hyS
    have hminU : ∀ z ∈ (i.ker.comap U.ι).support, z ⤳ x → z = x := by
      intro z hz hzx
      rw [Scheme.IdealSheafData.support_comap] at hz
      exact Subtype.ext (hmin _ hz (hzx.map U.ι.continuous))
    have h1 := ringKrullDim_stalk_le_one _ x hxS hminU V hxV ⟨⟨f, hf⟩⟩
    rw [← ringKrullDim_eq_of_ringEquiv (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv] at h1
    exact hlt h1
end GlobalTheory.NotCartier
