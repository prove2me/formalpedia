-- Prove2me | solution 1 for GlobalTheory.IntegralFrameCheck.nval_map_of_overLa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:53.235046+00:00
-- url     : https://prove2.me/submissions/ea4c7ccc-4093-47e6-b707-def28e0e8c5b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_VVAlgebraMapNonneg
import Theorems.Thm_GlobalTheory_IntegralFrameCheck_exists_vV_map
import Theorems.Thm_Formalism_L2_Pj_nval_bc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameCheck
open Formalism.L2.Pj NumberField IsDedekindDomain
open scoped WithZero
namespace GlobalTheory.IntegralFrameCheck
theorem _root_.solution {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)}
    {T T' : CDVR} {io : K →+* T.Fr} {io' : K →+* T'.Fr} {e e' : ℕ}
    (ho : OverLa la T.V io e) (ho' : OverLa la T'.V io' e') (i : T.Fr →+* T'.Fr)
    (hc : ∀ a, i (io a) = io' a)
    (hi : ∀ a : T.V, i (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) :
    ∃ r : ℕ, 0 < r ∧ e' = r * e ∧ (∀ x, vV T'.V (i x) = (r : ℤ) * vV T.V x) ∧
      ∀ x, nval T'.V e' (i x) = nval T.V e x := by
  obtain ⟨r, hr⟩ := exists_vV_map i hi
  obtain ⟨a, ha⟩ := la.valuation_exists_uniformizer K
  have h1 : vLa la a = 1 := by simp [vLa, ha]
  have h2 := hr (io a)
  rw [hc, ho'.2, ho.2, h1] at h2
  have he : e' = r * e := by
    have : (e' : ℤ) = (r * e : ℕ) := by push_cast; linarith
    exact_mod_cast this
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · have := ho'.1; rw [he, h] at this; simp at this
    · exact h
  exact ⟨r, hr0, he, hr, fun x => he ▸ nval_bc i hr0 hr e x⟩
end GlobalTheory.IntegralFrameCheck
