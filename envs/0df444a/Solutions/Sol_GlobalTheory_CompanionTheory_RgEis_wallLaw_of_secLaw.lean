-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.wallLaw_of_secLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:49.42054+00:00
-- url     : https://prove2.me/submissions/01498590-7173-4896-976b-bf5e5891dade

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_norm_le_of_strip
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_entire_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bound_left
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bound_right
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_eis_mul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_norm_eis_le
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_pos_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_eis_mul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution : SecLaw → WallLaw := by
  intro hS
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ P P' c η η' β L R D Op H hP hP' hη hη' hβ hW
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨h1, -, Ms, hb⟩ := hS G W K ρ hK hρ Γ P c hP
  obtain ⟨-, -, Ms', hb'⟩ := hS G W K ρ hK hρ Γ P' c hP'
  have hdiff : ∀ (g : G) (w : L), Differentiable ℂ fun z => H z g w := fun g w =>
    (hW.hol g).clm_apply (differentiable_const _)
  refine ⟨?_, ?_, ?_⟩
  · intro z γ hγ g
    refine ContinuousLinearMap.ext fun w => ?_
    have e : (fun z => H z (γ * g) w) = fun z => H z g w := by
      refine entire_eq (hdiff _ w) (hdiff _ w) R fun z hz => ?_
      rw [hW.eqR z hz, hW.eqR z hz, eis_mul_left hP h1 hη (hW.le w.2) z hγ g]
    exact congrFun e z
  · intro z g k w
    have e : (fun z => H z (g * k) w) = fun z => ρ k⁻¹ (H z g w) := by
      refine entire_eq (hdiff _ w) ((ρ k⁻¹).differentiable.comp (hdiff g w)) R fun z hz => ?_
      rw [hW.eqR z hz, hW.eqR z hz, eis_mul_right hP h1 hb hη (hW.le w.2) z (hW.convR _ hz) g k, map_smul]
    exact congrFun e z
  · intro a b ha hb₀
    obtain ⟨MD, hD⟩ := hW.dEnt.2 a a
    obtain ⟨MO, hO⟩ := hW.op.2 b b hb₀
    refine ⟨|MD| * |Ms| + |Ms'| * |MO|, ?_⟩
    intro z hz1 hz2 g
    have hab : b < a := by linarith [hW.pos]
    obtain ⟨U, hU, B, hB⟩ := hW.bdd b a g
    have hg : g ∈ U := mem_of_mem_nhds hU
    have hp := pos_nonneg (Γ := Γ) (P := P) (fun x => a * η x) g
    have hq := pos_nonneg (Γ := Γ) (P := P') (fun x => β x - b * η' x) g
    have hA : 0 ≤ |MD| * |Ms| := by positivity
    have hB' : 0 ≤ |Ms'| * |MO| := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    refine norm_le_of_strip (f := fun z => H z g w) (B := B * ‖w‖) (hdiff g w) hab ?_ ?_ ?_ hz1 hz2
    · intro u hu1 hu2
      exact ((H u g).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hB u hu1 hu2 g hg) (norm_nonneg _))
    · intro u hu
      have hO' := hO u hu.ge hu.le
      have hu' : u.re < -R := by rw [hu]; exact hb₀
      have e2 := norm_eis_le (Γ := Γ) hb' (l := fun x => β x - b * η' x) (hW.convL b hb₀)
        (Λ := fun x => (β x : ℂ) - u * η' x) (by intro x; simp [hu]) g (Op u w : W)
      have e3 : ‖(Op u w : W)‖ ≤ |MO| * ‖w‖ := by
        have : ‖(Op u w : W)‖ = ‖Op u w‖ := rfl
        rw [this]
        exact ((Op u).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (hO'.trans (le_abs_self _)) (norm_nonneg _))
      show ‖H u g w‖ ≤ _
      rw [hW.eqL u hu' g w]
      calc _ ≤ Ms' * ‖(Op u w : W)‖ * _ := e2
        _ ≤ |Ms'| * (|MO| * ‖w‖) * _ := by
            refine mul_le_mul_of_nonneg_right ?_ hq
            exact mul_le_mul (le_abs_self _) e3 (norm_nonneg _) (abs_nonneg _)
        _ = |Ms'| * |MO| * _ * ‖w‖ := by ring
        _ ≤ _ := bound_right hA hB' hp hq (norm_nonneg _)
    · intro u hu
      have hD' := hD u hu.ge hu.le
      have hu' : R < u.re := by rw [hu]; exact ha
      have e2 := norm_eis_le (Γ := Γ) hb (l := fun x => a * η x) (hW.convR a ha)
        (Λ := fun x => u * η x) (by intro x; simp [hu]) g (w : W)
      show ‖H u g w‖ ≤ _
      rw [hW.eqR u hu' g w, norm_smul]
      calc _ ≤ |MD| * (|Ms| * ‖w‖ * _) := by
            refine mul_le_mul (hD'.trans (le_abs_self _)) (e2.trans ?_) (norm_nonneg _) (abs_nonneg _)
            refine mul_le_mul_of_nonneg_right ?_ hp
            exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        _ = |MD| * |Ms| * _ * ‖w‖ := by
            have : ‖w‖ = ‖(w : W)‖ := rfl
            ring
        _ ≤ _ := bound_left hA hB' hp hq (norm_nonneg _)
end GlobalTheory.CompanionTheory.RgEis
