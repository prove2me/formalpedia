-- Prove2me | solution 1 for GlobalTheory.algebraicIndependent_update_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:22:14.43894+00:00
-- url     : https://prove2.me/submissions/0a25e78d-bec8-41de-beda-c76c5a2f011f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAlgHomInjectiveApplyOfTranscendental

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    [DecidableEq ι] {x : ι → A} (hx : AlgebraicIndependent R x) (i₀ : ι) {n : ℕ} (hn : 0 < n) :
    AlgebraicIndependent R (Function.update x i₀ (x i₀ ^ n)) := by
  let e := Equiv.optionSubtypeNe i₀
  have key : ∀ y : ι → A, y ∘ e = fun o => o.elim (y i₀) (fun b => y b.1) := by
    intro y; funext o; cases o <;> rfl
  rw [← algebraicIndependent_equiv e, key] at hx
  rw [← algebraicIndependent_equiv e, key]
  obtain ⟨h1, h2⟩ := AlgebraicIndependent.option_iff.1 hx
  have hrest : (fun b : {b // b ≠ i₀} => Function.update x i₀ (x i₀ ^ n) b.1) =
      fun b => x b.1 := by
    funext b; exact Function.update_of_ne b.2 _ _
  rw [hrest, Function.update_self]
  exact AlgebraicIndependent.option_iff.2 ⟨h1, h2.pow hn⟩
end GlobalTheory
