-- Prove2me | solution 1 for GlobalTheory.ShortLawsCompare.shortValAt_beta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:10:41.416784+00:00
-- url     : https://prove2.me/submissions/0f1edd87-2770-4aa2-a03b-493726d61953

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm

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
open GlobalTheory GlobalTheory.ShortLawsCompare
open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
namespace GlobalTheory.ShortLawsCompare
theorem _root_.solution (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) {β : c.F}
    (hβ : β ≠ 0) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (v : S) :
    ShortValAt Xo c nab w Λ β N P y v ↔ ShortValAt Xo c nab w Λ 1 N P y (algebraMap c.F S β * v) := by
  have key : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (a b d : c.F) (Z : S'),
      φ v = algebraMap c.F S' (β⁻¹ * a * b * d) * Z ↔
        φ (algebraMap c.F S β * v) = algebraMap c.F S' (1⁻¹ * a * b * d) * Z := by
    intro S' _ _ φ a b d Z
    have hu : IsUnit (algebraMap c.F S' β) := (IsUnit.mk0 β hβ).map _
    rw [map_mul φ, φ.commutes, ← hu.mul_right_inj, ← _root_.mul_assoc, ← map_mul]
    have : β * (β⁻¹ * a * b * d) = 1⁻¹ * a * b * d := by field_simp
    rw [this]
  constructor
  · rintro ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).1 h7⟩
  · rintro ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨S', i1, i2, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).2 h7⟩
end GlobalTheory.ShortLawsCompare
