-- Prove2me | solution 1 for GlobalTheory.GramCount.exists_isPrimitive_invol_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:31:43.475543+00:00
-- url     : https://prove2.me/submissions/2910dce1-de31-4c58-8203-8f2f4bf04859

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimitiveAddCharInvolutionInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
namespace GlobalTheory.GramCount
theorem _root_.solution {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (ω : B) (hω : IsUnit (ω - c ω))
    (hfix : ∀ t, c t = t → t ≠ 0 → IsUnit t) :
    ∃ χ : AddChar B ℂ, χ.IsPrimitive ∧ ∀ u, χ (c u) = χ u := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · refine ⟨1, fun a ha => absurd (Subsingleton.elim a 0) ha, fun u => by simp⟩
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := (1 : B))).2 one_ne_zero
  let T : B →+ B := AddMonoidHom.id B + c.toAddMonoidHom
  have hT : ∀ u, T u = u + c u := fun u => rfl
  refine ⟨ψ.compAddMonoidHom T, ?_, ?_⟩
  · intro a ha h
    have hex : ∃ u, a * u + c (a * u) ≠ 0 := by
      by_contra hne
      push_neg at hne
      have h1 := hne 1
      have h2 := hne ω
      rw [mul_one] at h1
      rw [map_mul] at h2
      have h3 : a * (ω - c ω) = 0 := by linear_combination h2 - c ω * h1
      exact ha ((hω.mul_left_eq_zero).1 h3)
    obtain ⟨u, hu⟩ := hex
    have hs : c (a * u + c (a * u)) = a * u + c (a * u) := by
      rw [map_add, hc, add_comm]
    obtain ⟨s', hs'⟩ := (hfix _ hs hu).exists_right_inv
    have hcs : c s' = s' := by
      have h4 := congrArg c hs'
      rw [map_mul, hs, map_one] at h4
      linear_combination s' * h4 - c s' * hs'
    have h5 : T (a * (u * s')) = 1 := by
      rw [hT, ← mul_assoc, map_mul c (a * u), hcs, ← hs']
      ring
    have h6 := DFunLike.congr_fun h (u * s')
    rw [AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply, h5] at h6
    exact hψ (by simpa using h6)
  · intro u
    simp only [AddChar.compAddMonoidHom_apply, hT, hc, add_comm]
end GlobalTheory.GramCount
