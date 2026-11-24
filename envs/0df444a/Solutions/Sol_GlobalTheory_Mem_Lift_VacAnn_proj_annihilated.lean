-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.VacAnn.proj_annihilated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:10.41085+00:00
-- url     : https://prove2.me/submissions/f238ff94-47e9-4e20-a722-f1b9dc95285c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FderivCompress
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VacuumProjectorRangeAnnihilated
import Theorems.Thm_GlobalTheory_Mem_Lift_VacAnn_fderiv_gau_apply
import Theorems.Thm_GlobalTheory_Mem_Lift_VacBd_fderiv_compress
import Theorems.Thm_GlobalTheory_Mem_Lift_VacBd_heis_dH
import Theorems.Thm_GlobalTheory_Mem_Lift_VacBd_sm_dH
import Theorems.Thm_GlobalTheory_RealWeil_Good_inversion
import Theorems.Thm_GlobalTheory_RealWeil_Good_sm
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_of_sm
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_sm_add
import Theorems.Thm_GlobalTheory_RealWeil_Osc_sm_smul
import Theorems.Thm_GlobalTheory_RealWeil_contDiff_gau
import Theorems.Thm_GlobalTheory_RealWeil_proj_heis_proj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.VacAnn
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
namespace GlobalTheory.Mem.Lift.VacAnn
namespace _root_.GlobalTheory.Mem.Lift.VacAnn
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type)
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V)
    (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) →
    ∀ (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ) (x : B) (z : V),
      _root_.GlobalTheory.Mem.Lift.dH ρ z (_root_.GlobalTheory.RealWeil.proj h x) +
        I • _root_.GlobalTheory.Mem.Lift.dH ρ (J z) (_root_.GlobalTheory.RealWeil.proj h x) = 0 := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h x z
  set P := _root_.GlobalTheory.RealWeil.proj h
  set f := P x with hf_def
  have hf : _root_.GlobalTheory.RealWeil.Sm ρ f :=
    _root_.GlobalTheory.RealWeil.Good.sm hJ
      (_root_.GlobalTheory.RealWeil.Osc.good_proj hJ h x)
  have hsand : ∀ w : V, P (ρ w f) = _root_.GlobalTheory.RealWeil.gau w • f := fun w =>
    _root_.GlobalTheory.RealWeil.proj_heis_proj hJ h w x
  have hcomp : ∀ w v : V, P (ρ w (_root_.GlobalTheory.Mem.Lift.dH ρ v f)) =
      ((Real.pi : ℂ) * I * (⟪w, J v⟫ : ℝ) * _root_.GlobalTheory.RealWeil.gau w
        - (Real.pi : ℂ) * (⟪w, v⟫ : ℝ) * _root_.GlobalTheory.RealWeil.gau w) • f := by
    intro w v
    rw [_root_.GlobalTheory.Mem.Lift.VacBd.heis_dH h hf v w, map_add, map_smul, hsand w,
      _root_.GlobalTheory.Mem.Lift.VacBd.fderiv_compress P hf _root_.GlobalTheory.RealWeil.contDiff_gau hsand w v,
      _root_.GlobalTheory.Mem.Lift.VacAnn.fderiv_gau_apply, smul_smul, ← add_smul]
    congr 1
    show (Real.pi : ℂ) * I * ((⟪w, J v⟫ : ℝ) : ℂ) * _root_.GlobalTheory.RealWeil.gau w
        + -(Real.pi : ℂ) * ((⟪w, v⟫ : ℝ) : ℂ) * _root_.GlobalTheory.RealWeil.gau w = _
    ring
  set G := _root_.GlobalTheory.Mem.Lift.dH ρ z f + I • _root_.GlobalTheory.Mem.Lift.dH ρ (J z) f
  have hG : _root_.GlobalTheory.RealWeil.Sm ρ G :=
    _root_.GlobalTheory.RealWeil.Osc.sm_add (_root_.GlobalTheory.Mem.Lift.VacBd.sm_dH h hf z)
      (_root_.GlobalTheory.RealWeil.Osc.sm_smul I (_root_.GlobalTheory.Mem.Lift.VacBd.sm_dH h hf (J z)))
  have hzero : ∀ w : V, P (ρ w G) = 0 := by
    intro w
    simp only [G, map_add, map_smul, hcomp, smul_smul, ← add_smul, hJ z, inner_neg_right]
    apply smul_eq_zero_of_left
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [← (_root_.GlobalTheory.RealWeil.Osc.good_of_sm hJ h hG).inversion hJ]
  have hzero' : ∀ w : V, _root_.GlobalTheory.RealWeil.proj h (ρ (-w) G) = 0 := fun w => hzero (-w)
  simp only [hzero', map_zero, integral_zero]
end _root_.GlobalTheory.Mem.Lift.VacAnn
end GlobalTheory.Mem.Lift.VacAnn
