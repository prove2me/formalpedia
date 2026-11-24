-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Principalise.dense_range_restrict_of_blowup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:22:54.750809+00:00
-- url     : https://prove2.me/submissions/a5ae097c-f211-4f1e-b0e3-df3ebc0cd945

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIsoRestrictOfBlowupComp
import Theorems.Thm_GlobalTheory_CompanionTheory_Principalise_isEmpty_of_effCartier_bot
import Theorems.Thm_GlobalTheory_IsSmoothBlowupSeq_mono
import Theorems.Thm_GlobalTheory_Principalise_isIso_restrict_of_blowup
import Theorems.Thm_GlobalTheory_Principalise_nonempty_compl_support


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Principalise
namespace GlobalTheory.CompanionTheory.Principalise
theorem _root_.solution {X₁ X₂ : Scheme.{0}} [IsIntegral X₁] [Nonempty X₂] {π : X₂ ⟶ X₁}
    {Z : X₁.IdealSheafData} (hB : FinalTheorems.Blowup π Z) (U : X₁.Opens) : Dense (Set.range (π ∣_ U)) := by
  have hZ : Z ≠ ⊥ := by
    rintro rfl
    have h := hB.1
    rw [Scheme.IdealSheafData.comap_bot] at h
    exact (isEmpty_of_effCartier_bot h).false (Nonempty.some inferInstance)
  have hO := GlobalTheory.Principalise.nonempty_compl_support hZ
  have hiso : IsIso (π ∣_ Z.support.compl) :=
    GlobalTheory.Principalise.isIso_restrict_of_blowup hB _ fun x hx => hx
  have hdO : Dense (Z.support.compl : Set X₁) := Z.support.compl.isOpen.dense hO
  have hdU : Dense (U.ι ⁻¹' (Z.support.compl : Set X₁)) := hdO.preimage U.ι.isOpenMap
  refine hdU.mono fun x hx => ?_
  obtain ⟨y, hy⟩ := (π ∣_ Z.support.compl).surjective ⟨x.1, hx⟩
  have hw : π y.1 = x.1 := by
    have := morphismRestrict_base_coe π Z.support.compl y
    rw [hy] at this
    exact this.symm
  refine ⟨⟨y.1, show π y.1 ∈ U by rw [hw]; exact x.2⟩, Subtype.ext ?_⟩
  exact (morphismRestrict_base_coe π U ⟨y.1, _⟩).trans hw
end GlobalTheory.CompanionTheory.Principalise
