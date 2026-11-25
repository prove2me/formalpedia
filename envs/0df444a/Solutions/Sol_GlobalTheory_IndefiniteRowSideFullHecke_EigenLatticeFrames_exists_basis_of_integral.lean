-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames.exists_basis_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:55:46.775459+00:00
-- url     : https://prove2.me/submissions/ed0206b4-f41d-443f-b49e-82e4f284af33

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_EigenLatticeFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames
theorem _root_.solution {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr}
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (h : Integral T io y) :
    letI := io.toAlgebra
    ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t y.x)
      (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))), ∀ τ, ∃ ub, IsEigenLatticeBasis Dw c T io G τ ub ∧
        ∀ i, IsGenericFibre m₁ m₂ (ub i) (y.u τ i) := by
  obtain ⟨G, t', m₁, m₂, ⟨ub, h1, h2, h3, h4⟩, -⟩ := h
  exact ⟨G, t', m₁, m₂, fun τ => ⟨ub τ, ⟨h1 τ, h2 τ, h3 τ⟩, h4 τ⟩⟩
end GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames
