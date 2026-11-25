-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeClosed.closedSt_of_twoFormCohSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:42:38.399907+00:00
-- url     : https://prove2.me/submissions/63a944fc-be95-4736-a80d-0633d26f8d6a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedStOfTwoFormCohSt
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeClosed_eq_zero_of_additive
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeClosed_nu_natural

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeClosed
namespace GlobalTheory.CompanionTheory.HodgeClosed
theorem _root_.solution : TwoFormCohSt → ClosedSt := by
  intro h2 R _ C _ F hF hBi
  obtain ⟨D, _, G, m, p, q, hS, hP, -, hb, -, hm, -⟩ := hBi
  have hG : Framed G := by
    obtain ⟨-, -, h1, h3⟩ := hF
    let e : (Glob1 F × Glob1 F) ≃ₗ[R] Glob1 G := LinearEquiv.ofBijective ((pullGlob1 p).coprod (pullGlob1 q))
      ((funext fun x ↦ LinearMap.coprod_apply (pullGlob1 p) (pullGlob1 q) x :
        ⇑((pullGlob1 p).coprod (pullGlob1 q)) = _) ▸ hb)
    exact ⟨hS, hP, Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  obtain ⟨ν, hν, -, hsurj⟩ := h2 R C F hF
  obtain ⟨ν', hν', hinj, -⟩ := h2 R D G hG
  obtain ⟨-, -, hfin, hproj⟩ := hF
  refine eq_top_iff.2 fun ω₀ _ T ↦ ?_
  obtain ⟨t, ht⟩ := hsurj (fun T ↦ dOne R _ (ω₀.1 T)) fun T T' φ ↦ by
    rw [pOm_dOne, ω₀.2 φ]
  have step : ∀ (c : CoefMap (RingHom.id R) F G),
      ν' (exteriorPower.map 2 (pullGlob1 c) t) = fun T ↦ dOne R _ ((pullGlob1 c ω₀).1 T) := by
    intro c
    funext T
    rw [← nu_natural c ν ν' hν hν' t T, ht]
    exact qOm_dOne c (ω₀.1 (c.G.obj T))
  have hadd : exteriorPower.map 2 (pullGlob1 p + pullGlob1 q) t =
      exteriorPower.map 2 (pullGlob1 p) t + exteriorPower.map 2 (pullGlob1 q) t := by
    have h1 : pullGlob1 p + pullGlob1 q = pullGlob1 m := LinearMap.ext fun ω ↦ (hm ω).symm
    apply hinj
    rw [h1, step m, map_add, step p, step q]
    funext T'
    change dOne R _ ((pullGlob1 m ω₀).1 T') = dOne R _ ((pullGlob1 p ω₀).1 T') + dOne R _ ((pullGlob1 q ω₀).1 T')
    rw [hm, ← map_add]
    rfl
  have ht0 : t = 0 := eq_zero_of_additive _ _ hb t hadd
  have := congrFun ht T
  rw [ht0, map_zero] at this
  exact this.symm
end GlobalTheory.CompanionTheory.HodgeClosed
