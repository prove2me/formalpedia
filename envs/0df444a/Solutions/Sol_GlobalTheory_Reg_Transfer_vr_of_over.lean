-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.vr_of_over
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:58.731193+00:00
-- url     : https://prove2.me/submissions/d9f4585b-8084-49fd-a800-b38b9ba26125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentreChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing NumberField IsDedekindDomain Formalism.L2.Pj Formalism.L2.PjFree ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Reg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
namespace GlobalTheory.Reg.Transfer
theorem _root_.solution {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (eO e : ℕ) (heO : 0 < eO)
    (he : 0 < e) (y : V) (hy : vV (K' := FractionRing V) V (algebraMap V (FractionRing V) y) * (eO : ℤ) = e) :
    vr e y = 1 / eO := by
  unfold vr
  have hv : ((vV (K' := FractionRing V) V (algebraMap V (FractionRing V) y) : ℤ) : ℝ) * eO = e := by exact_mod_cast hy
  have heOr : (0 : ℝ) < eO := by exact_mod_cast heO
  have her : (0 : ℝ) < e := by exact_mod_cast he
  field_simp
  linarith
end GlobalTheory.Reg.Transfer
