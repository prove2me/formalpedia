-- Prove2me | solution 1 for GlobalTheory.IntegralFrameCheck.exists_vV_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:27:15.02731+00:00
-- url     : https://prove2.me/submissions/0cc83a52-b9d8-4d5f-8e98-b95a8fbc3800

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_VVAlgebraMapNonneg
import Theorems.Thm_GlobalTheory_IntegralFrameCheck_vV_algebraMap_nonneg
import Theorems.Thm_GlobalTheory_IntegralFrameCheck_vV_pow
import Theorems.Thm_GlobalTheory_IntegralFrameCheck_vV_map_unit
import Theorems.Thm_Formalism_L2_Pj_vV_mul


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
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']
variable {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K''] [Algebra V' K'']
  [IsFractionRing V' K'']
namespace GlobalTheory.IntegralFrameCheck
theorem _root_.solution (i : K' →+* K'') (hi : ∀ a : V, i (algebraMap V K' a) ∈ Set.range (algebraMap V' K'')) :
    ∃ r : ℕ, ∀ x, vV V' (i x) = (r : ℤ) * vV V x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hp0 : algebraMap V K' p ≠ 0 := by
    simpa using hp.ne_zero
  have hr : 0 ≤ vV V' (i (algebraMap V K' p)) := by
    obtain ⟨b, hb⟩ := hi p
    rw [← hb]; exact vV_algebraMap_nonneg b
  have hp1 : vV V (algebraMap V K' p) = 1 := by
    have h : valV V (algebraMap V K' p) = WithZero.exp (-1 : ℤ) := by
      unfold valV
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      refine HeightOneSpectrum.intValuation_singleton _ hp.ne_zero ?_
      exact hp.maximalIdeal_eq
    simp [vV, h]
  refine ⟨(vV V' (i (algebraMap V K' p))).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hr]
  have key : ∀ a : V, a ≠ 0 → vV V' (i (algebraMap V K' a)) =
      vV V' (i (algebraMap V K' p)) * vV V (algebraMap V K' a) := by
    intro a ha
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hp
    have hu : algebraMap V K' u ≠ 0 := (u.isUnit.map (algebraMap V K')).ne_zero
    have hu0 : vV V (algebraMap V K' u) = 0 :=
      vV_map_unit (V' := V) (RingHom.id K') (fun a => ⟨a, rfl⟩) u
    rw [map_mul, map_pow, map_mul, map_pow,
      vV_mul ((map_ne_zero i).2 hu) (pow_ne_zero n ((map_ne_zero i).2 hp0)),
      vV_mul hu (pow_ne_zero n hp0), vV_pow ((map_ne_zero i).2 hp0), vV_pow hp0, vV_map_unit i hi u, hu0, hp1]
    ring
  intro x
  by_cases hx : x = 0
  · subst hx; simp [vV]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap V K' b ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have e : algebraMap V K' a / algebraMap V K' b * algebraMap V K' b = algebraMap V K' a :=
    div_mul_cancel₀ _ hb'
  have h1 := vV_mul (V := V) hx hb'
  have h2 := vV_mul (V := V') ((map_ne_zero i).2 hx) ((map_ne_zero i).2 hb')
  rw [← map_mul, e, key a ha0, key b hb0] at h2
  rw [e] at h1
  rw [h1] at h2
  linarith
end GlobalTheory.IntegralFrameCheck
