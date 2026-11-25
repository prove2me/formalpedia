-- Prove2me | solution 1 for GlobalTheory.Survey.BaseClassMove.shortValAt_beta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:46.039568+00:00
-- url     : https://prove2.me/submissions/88c3c0bd-2f00-4178-b164-705f5d9c62bd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove

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
open GlobalTheory GlobalTheory.Survey GlobalTheory.Survey.BaseClassMove
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
namespace GlobalTheory.Survey.BaseClassMove
theorem _root_.solution (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F)
    (hβ : β ≠ 0) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (v : S) :
    ShortValAt Xo c nab w Λ β N P y v ↔ ShortValAt Xo c nab w Λ 1 N P y (algebraMap c.F S β * v) := by
  have key : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (a b d : c.F) (T : S'),
      φ v = algebraMap c.F S' (β⁻¹ * a * b * d) * T ↔
        φ (algebraMap c.F S β * v) = algebraMap c.F S' (1⁻¹ * a * b * d) * T := by
    intro S' _ _ φ a b d T
    have hu : algebraMap c.F S' β * algebraMap c.F S' β⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hβ, map_one]
    simp only [map_mul, AlgHom.commutes, inv_one, map_one]
    constructor
    · intro h; rw [h]; linear_combination (algebraMap c.F S' a * algebraMap c.F S' b * algebraMap c.F S' d * T) * hu
    · intro h; linear_combination (algebraMap c.F S' β⁻¹) * h - φ v * hu
  constructor
  · rintro ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).1 h7⟩
  · rintro ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).2 h7⟩
end GlobalTheory.Survey.BaseClassMove
