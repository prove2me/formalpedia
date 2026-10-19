-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.separated_rays_contract
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:32:48.492356+00:00
-- url     : https://prove2.me/submissions/f69c72f1-ed3e-4dad-9d78-9733dc3ce809

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/RaySeparation.lean:L55-L112
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.separated_rays_contract. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PolygonGeometry
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Traversals
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ReturnCycles
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionStems
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Convexity
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_FaceBoundary
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryContainment
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryArcs
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexDomains
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_VisitRecursion
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryFlux
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexCuts
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RaySeparation

-- ---- from OAI.Combinatorics.HoneycombCorridor.RaySeparation ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem phase_add (a b : ℝ) : phase (a+b) = phase a * phase b := by
  simp only [phase,Complex.ofReal_add,add_mul,Complex.exp_add]

theorem phasedWordMass_norm_le (S : Finset (List Bool)) :
    ‖phasedWordMass S‖ ≤ positiveWordMass S := by
  simpa only [phasedWordMass,positiveWordMass,wordWeight_norm] using norm_sum_le S wordWeight

theorem separated_rays_contract (S T : Finset (List Bool)) (hTS : T ⊆ S)
    (hlower : Real.cos (3*Real.pi/8) * positiveWordMass T ≤ (phasedWordMass T).re)
    (a b : ℝ) (hb : 0 ≤ b)
    (hS : phasedWordMass S = (a : ℂ) * phase (-Real.pi/8))
    (hT : phasedWordMass T = (b : ℂ) * phase (-Real.pi/4)) :
    positiveWordMass T ≤ rayContraction * positiveWordMass S := by
  have halpha : Real.pi/8 + -Real.pi/4 = -Real.pi/8 := by ring
  have hzero : Real.pi/8 + -Real.pi/8 = 0 := by ring
  have hrotate : phase (Real.pi/8) * (phasedWordMass S - phasedWordMass T) =
      (a : ℂ) - (b : ℂ) * phase (-Real.pi/8) := by
    rw [hS,hT,mul_sub]
    have h1 := phase_add (Real.pi/8) (-Real.pi/8)
    have h2 := phase_add (Real.pi/8) (-Real.pi/4)
    rw [hzero,phase_zero] at h1
    rw [halpha] at h2
    calc
      _ = (a : ℂ) * (phase (Real.pi/8)*phase (-Real.pi/8)) -
          (b : ℂ) * (phase (Real.pi/8)*phase (-Real.pi/4)) := by ring
      _ = _ := by rw [← h1,← h2,mul_one]
  have him : (phase (Real.pi/8) * (phasedWordMass S - phasedWordMass T)).im =
      b * Real.sin (Real.pi/8) := by
    rw [hrotate]
    have hp : (phase (-Real.pi/8)).im = -Real.sin (Real.pi/8) := by
      unfold phase
      rw [Complex.exp_ofReal_mul_I_im,neg_div,Real.sin_neg]
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,hp,zero_sub,zero_mul,add_zero,mul_neg,neg_neg]
  have hnorm : b * Real.sin (Real.pi/8) ≤ ‖phasedWordMass S - phasedWordMass T‖ := by
    calc
      _ ≤ |(phase (Real.pi/8) * (phasedWordMass S - phasedWordMass T)).im| := by
        rw [him]; exact le_abs_self _
      _ ≤ ‖phase (Real.pi/8) * (phasedWordMass S - phasedWordMass T)‖ :=
        Complex.abs_im_le_norm _
      _ = _ := by rw [norm_mul,phase_norm,one_mul]
  have hbnd : Real.cos (3*Real.pi/8) * positiveWordMass T ≤ b := by
    calc
      _ ≤ (phasedWordMass T).re := hlower
      _ ≤ ‖phasedWordMass T‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ = b := by rw [hT,norm_mul,phase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb]
  have hmass : positiveWordMass (S \ T) + positiveWordMass T = positiveWordMass S :=
    Finset.sum_sdiff hTS
  have hdiff : phasedWordMass S - phasedWordMass T = phasedWordMass (S \ T) :=
    (Finset.sum_sdiff_eq_sub hTS).symm
  rw [hdiff] at hnorm
  have hnorm' := phasedWordMass_norm_le (S \ T)
  have hs : 0 ≤ Real.sin (Real.pi/8) := (Real.sin_pos_of_pos_of_lt_pi
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).le
  have hprod := mul_le_mul_of_nonneg_right hbnd hs
  have hfinal : (1+Real.cos (3*Real.pi/8)*Real.sin (Real.pi/8))*positiveWordMass T ≤
      positiveWordMass S := by nlinarith
  change _ ≤ (1+Real.cos (3*Real.pi/8)*Real.sin (Real.pi/8))⁻¹ * _
  have hd : 0 < 1+Real.cos (3*Real.pi/8)*Real.sin (Real.pi/8) := by
    have hc : 0 ≤ Real.cos (3*Real.pi/8) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> linarith [Real.pi_pos]
    nlinarith [mul_nonneg hc hs]
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hfinal)

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.separated_rays_contract := @_root_.OAI.PolynomialVacuumBridge.Corridor.separated_rays_contract
