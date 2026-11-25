-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.pushLet_letB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:17.947777+00:00
-- url     : https://prove2.me/submissions/b8e1794e-386e-4163-9f5e-f2feb5c1903f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ThetaSpanAdjoint

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
set_option autoImplicit false
open NumberField MvPolynomial
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
variable (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l)
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
theorem _root_.solution {n : ℕ} (γ : Matrix (Fin n) (Fin n) E)
    (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (b : Fin n → E) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.pushLet c γ (_root_.Formalism.L2.Pj.letB c σ i b) = _root_.Formalism.L2.Pj.letB c σ i (γ.mulVec b) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.pushLet _root_.Formalism.L2.Pj.letB
  simp only [map_sum, map_mul, aeval_C, aeval_X, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Finset.sum_mul, MvPolynomial.algebraMap_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
