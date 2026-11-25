-- Prove2me | solution 1 for GlobalTheory.LevelPairing.levelFourierDatum_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:04:22.256021+00:00
-- url     : https://prove2.me/submissions/28c0a7f4-3075-4baf-800d-03be9dfbb14d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Theorems.Thm_GlobalTheory_LevelPairing_pairL_congr
import Theorems.Thm_GlobalTheory_LevelPairing_zetaM_prim
import Theorems.Thm_GlobalTheory_LevelPairing_zpow_congr
import Theorems.Thm_GlobalTheory_LevelPairing_levelFourierDatum_mk
import Theorems.Thm_GlobalTheory_LevelPairing_mem_of_dvd

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
open GlobalTheory GlobalTheory.LevelPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.LevelPairing
theorem _root_.solution (c : Coeff l) {n : ℕ} (x0 x0' : Fin n → Dw.La) :
    x0Dat c x0 = x0Dat c x0' ↔ ∀ b, x0 b - x0' b ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  constructor
  · intro h b
    refine mem_of_dvd fun y => ?_
    have h1 := congrFun h (fun i => (Submodule.Quotient.mk ((Pi.single b y : Fin n → Dw.La) i) : LevQ Dw l))
    rw [levelFourierDatum_mk, levelFourierDatum_mk] at h1
    have h0 : zetaM c ≠ 0 := (zetaM_prim c).ne_zero hM
    have h2 : (l.M : ℤ) ∣ pairL (l := l) x0 (Pi.single b y) - pairL (l := l) x0' (Pi.single b y) := by
      rw [← (zetaM_prim c).zpow_eq_one_iff_dvd, zpow_sub₀ h0, h1, div_self (zpow_ne_zero _ h0)]
    have h3 : ∀ u : Fin n → Dw.La, pairL (l := l) u (Pi.single b y) = Dw.EF (u b) (cSep l • y) := by
      intro u
      unfold pairL
      rw [Finset.sum_eq_single b]
      · simp
      · intro i _ hi; simp [Pi.single_eq_of_ne hi]
      · simp
    rw [h3, h3] at h2
    simpa using h2
  · intro h
    funext q
    exact zpow_congr c (pairL_congr _ _ _ _ h (fun b => by simp))
end GlobalTheory.LevelPairing
