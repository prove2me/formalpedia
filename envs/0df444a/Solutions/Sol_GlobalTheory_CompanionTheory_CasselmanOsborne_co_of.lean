-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.co_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:29:24.179049+00:00
-- url     : https://prove2.me/submissions/1039e66b-5d4d-4962-b022-897d5dc99b70

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_deg_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_bd_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_deg_bd
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_lift_bd
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_lift_qdet
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_lift_zeta
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_deg_zeta
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_zeta_deg_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_bd_zeta
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_bd_qdet
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
namespace GlobalTheory.CompanionTheory.CasselmanOsborne
theorem _root_.solution (hB : BdFacts) (hG : GFacts) (hC : Cover) (h0 : CapelliDeterminantBlockProduct) : CO := by
  intro n ε V _ _ E hE u j
  induction j generalizing V with
  | zero =>
    intro x hx _
    obtain ⟨w, hw⟩ := h0 n ε V E hE u (x ∅)
    classical
    let w' : Ch ε V := fun A => ∑ i : NC ε, if A = {i} then w i else 0
    have hw' : Deg (0 + 1) w' := by
      intro A hA
      refine Finset.sum_eq_zero fun i _ => if_neg ?_
      rintro rfl
      simp at hA
    refine ⟨w', hw', ?_⟩
    funext A
    by_cases hA : A = ∅
    · subst hA
      rw [Pi.sub_apply, lift_apply, zeta_deg_zero E u hx, hw, bd_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [sg, w']
    · have hc : A.card ≠ 0 := by simpa using hA
      rw [Pi.sub_apply, deg_lift _ hx A hc, deg_zeta hG E u hx A hc, deg_bd E hw' A hc, sub_zero]
  | succ j ih =>
    intro x hx hbx
    obtain ⟨Y, _, _, EY, π, hY, hs, hπ, hac⟩ := hC n ε V E hE
    classical
    have hK : ∀ a b, ∀ y ∈ LinearMap.ker π, EY a b y ∈ LinearMap.ker π := by
      intro a b y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [hπ, hy, map_zero]
    let EK : Fin n → Fin n → Module.End ℂ (LinearMap.ker π) := fun a b => (EY a b).restrict (hK a b)
    have hι : ∀ a b y, (LinearMap.ker π).subtype (EK a b y) = EY a b ((LinearMap.ker π).subtype y) :=
      fun _ _ _ => rfl
    have hEK : GlRel EK := by
      intro a b c d
      ext y
      have := LinearMap.congr_fun (hY a b c d) (y : Y)
      split_ifs at this ⊢ <;> simpa [EK] using this
    let x' : Ch ε Y := fun A => if A.card = j + 1 then (hs (x A)).choose else 0
    have hx' : Deg (j + 1) x' := fun A hA => if_neg hA
    have hπx : lift ε π x' = x := by
      funext A
      by_cases hA : A.card = j + 1
      · simp only [lift_apply, x', if_pos hA]
        exact (hs (x A)).choose_spec
      · simp [x', hA, hx A hA]
    have hy : ∀ A, bd ε EY x' A ∈ LinearMap.ker π := by
      intro A
      have := congrFun (lift_bd π EY E hπ x') A
      rw [hπx, hbx] at this
      exact this
    let y : Ch ε (LinearMap.ker π) := fun A => ⟨_, hy A⟩
    have hιy : lift ε (LinearMap.ker π).subtype y = bd ε EY x' := rfl
    have hyd : Deg j y := fun A hA => Subtype.ext (deg_bd EY hx' A hA)
    have hyb : bd ε EK y = 0 := by
      have := lift_bd _ EK EY hι y
      rw [hιy, show bd ε EY (bd ε EY x') = 0 from LinearMap.congr_fun (hB n ε Y EY hY).1 x'] at this
      funext A
      exact Subtype.ext (congrFun this A)
    obtain ⟨w, hw, hDw⟩ := ih _ EK hEK y hyd hyb
    have hpush := congrArg (lift ε (LinearMap.ker π).subtype) hDw
    rw [map_sub, lift_qdet _ EK EY hι, lift_zeta hG _ EK EY hι, lift_bd _ EK EY hι, hιy] at hpush
    obtain ⟨t, ht, hbt⟩ := hac j
      (lift ε (qdet EY u) x' - zeta ε (Fop ε EY) u x' - lift ε (LinearMap.ker π).subtype w)
      ((degSub ε Y (j + 1)).sub_mem ((degSub ε Y (j + 1)).sub_mem (deg_lift _ hx') (deg_zeta hG EY u hx'))
        (deg_lift _ hw))
      (by rw [map_sub, map_sub, bd_qdet EY hY, bd_zeta hB EY hY, hpush, sub_self])
    refine ⟨lift ε π t, deg_lift _ ht, ?_⟩
    have h2 : lift ε π (lift ε (LinearMap.ker π).subtype w) = 0 := by
      funext A
      exact (w A).2
    rw [← lift_bd π EY E hπ, hbt, map_sub, map_sub, h2, lift_qdet π EY E hπ, lift_zeta hG π EY E hπ, hπx, sub_zero]
end GlobalTheory.CompanionTheory.CasselmanOsborne
