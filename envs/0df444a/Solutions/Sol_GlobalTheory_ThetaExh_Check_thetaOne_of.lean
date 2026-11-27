-- Prove2me | solution 1 for GlobalTheory.ThetaExh.Check.thetaOne_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:33:39.929956+00:00
-- url     : https://prove2.me/submissions/5c6585b2-1d48-4262-b709-6581a6d28692

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace GlobalTheory.ThetaExh.Check
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
private theorem pairs_of_starProjection_ne_zero (i : N.Loc) (σ : what₂.FT) (P : A.AV i) (f : what₂.Mj (N.j i))
    (hf : f ∈ what₂.isot (N.j i) σ)
    (hne : (A.typeV i P).starProjection (what₂.thetaT (N.mu i) (N.j i) f) ≠ 0) :
    Pairs N A i σ P := by
  refine ⟨f, hf, (A.typeV i P).starProjection (what₂.thetaT (N.mu i) (N.j i) f),
    Submodule.starProjection_apply_mem _ _, ?_⟩
  have e1 := Submodule.starProjection_inner_eq_zero (K := A.typeV i P)
    (what₂.thetaT (N.mu i) (N.j i) f) _
    (Submodule.starProjection_apply_mem (A.typeV i P) (what₂.thetaT (N.mu i) (N.j i) f))
  rw [inner_sub_left, sub_eq_zero] at e1
  rw [Submodule.inner_starProjection_left_eq_right, e1]
  exact inner_self_ne_zero.2 hne
end GlobalTheory.ThetaExh.Check
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaExh GlobalTheory.ThetaExh.Check
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.ThetaExh.Check
theorem _root_.solution (h1 : ∀ i, UpInj N i) (h2 : ∀ i, HoweUp N A i) (h3 : ∀ i, TypeOrth N A i) :
    ThetaOne N A := by
  intro i σ hσ
  classical
  letI : Fintype (A.AV i) := Fintype.ofFinite _
  have hO : OrthogonalFamily ℂ (fun P => A.typeV i P) (fun P => (A.typeV i P).subtypeₗᵢ) :=
    orthogonalFamily_iff_pairwise.2 (by intro P P' hP; exact h3 i P P' hP)
  have hsum : ∀ u, (∑ Q, (A.typeV i Q).starProjection u) = u := fun u =>
    hO.sum_projection_of_mem_iSup u (by rw [A.typeV_top i]; exact Submodule.mem_top)
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have hu0 : what₂.thetaT (N.mu i) (N.j i) f ≠ 0 := fun h => hf0 (h1 i σ f hf h)
  obtain ⟨P, hP⟩ : ∃ P, (A.typeV i P).starProjection (what₂.thetaT (N.mu i) (N.j i) f) ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    apply hu0
    rw [← hsum (what₂.thetaT (N.mu i) (N.j i) f)]
    exact Finset.sum_eq_zero (fun Q _ => hc Q)
  have hPair := pairs_of_starProjection_ne_zero N A i σ P f hf hP
  refine ⟨P, ?_, ?_⟩
  · intro hbot
    apply hu0
    have hm : what₂.thetaT (N.mu i) (N.j i) f ∈
        (what₂.isot (N.j i) σ).map (what₂.thetaT (N.mu i) (N.j i)) := Submodule.mem_map_of_mem hf
    rw [hbot] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · intro u hu
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hu
    have hz : ∀ Q, Q ≠ P → (A.typeV i Q).starProjection (what₂.thetaT (N.mu i) (N.j i) g) = 0 := by
      intro Q hQ
      by_contra hc
      exact hQ (h2 i σ Q P (pairs_of_starProjection_ne_zero N A i σ Q g hg hc) hPair)
    rw [← hsum (what₂.thetaT (N.mu i) (N.j i) g),
      Finset.sum_eq_single P (fun Q _ hQ => hz Q hQ) (by simp)]
    exact Submodule.starProjection_apply_mem _ _
end GlobalTheory.ThetaExh.Check
