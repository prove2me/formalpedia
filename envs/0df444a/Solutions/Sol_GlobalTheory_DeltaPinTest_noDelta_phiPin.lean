-- Prove2me | solution 1 for GlobalTheory.DeltaPinTest.noDelta_phiPin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:44:35.475581+00:00
-- url     : https://prove2.me/submissions/37df0e0c-1b41-417a-9b72-32987a0d250c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_InducedEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DeltaPinTest
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}
namespace GlobalTheory.DeltaPinTest
theorem _root_.solution (nab : NabV Xo c) (m : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) :
    (noDelta Xo c nab m n).PhiPin (fun _ => 1) 1 (fun _ => 0) := by
  haveI hs : Subsingleton (LaJ Xo c (noDelta Xo c nab m n)) := by
    apply Submodule.Quotient.subsingleton_iff.2
    show Ideal.map _ ⊤ • ⊤ = ⊤
    rw [Ideal.map_top, Submodule.top_smul]
  refine ⟨fun _ _ _ => rfl, fun _ _ => Subsingleton.elim _ _, fun _ _ _ _ => by simp, rfl,
    Subsingleton.elim _ _, fun q => ?_⟩
  haveI : Unique (Fin n → LaJ Xo c (noDelta Xo c nab m n)) := uniqueOfSubsingleton (fun _ => 0)
  rw [finsum_unique]
  have hz : ((⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ (l.M' / 1)) = 1 := by
    have h0 : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    apply Subtype.ext
    rw [Nat.div_one]
    exact (Complex.isPrimitiveRoot_exp _ h0).pow_eq_one
  show (noDelta Xo c nab m n).eF 1 = (noDelta Xo c nab m n).eF 1 * ((⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ (l.M' / 1)) ^ _
  rw [hz]
  exact ((congrArg _ (one_zpow _)).trans (mul_one _)).symm
end GlobalTheory.DeltaPinTest
