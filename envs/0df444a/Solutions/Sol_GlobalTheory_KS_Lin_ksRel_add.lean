-- Prove2me | solution 1 for GlobalTheory.KS.Lin.ksRel_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:18:19.975255+00:00
-- url     : https://prove2.me/submissions/7e955a86-5067-4f97-a779-413c08a95227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAnalyticKodairaSpencerClassStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FderivFnAddLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerMatrixLinearInDerivation
import Theorems.Thm_GlobalTheory_TorusElliptic_Rapid_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Lin
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} {u : HolUnif A₀ L₀ g} {X : Scheme.{0}}
  {R : Type} [CommRing R] {p : X ⟶ Sp R} {m : A₀.left ⟶ X}
namespace GlobalTheory.KS.Lin
theorem _root_.solution {D D' : R → ℂ} {Θ Θ' : Matrix (Fin g) (Fin g) ℂ}
    {s s' : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ}
    (h : KSRel u p m D Θ s) (h' : KSRel u p m D' Θ' s') :
    KSRel u p m (fun r => D r + D' r) (Θ + Θ') (fun z W f => s z W f + s' z W f) where
  der z :=
    { add := fun W hW f f' => by
        simp only [(h.der z).add W hW, (h'.der z).add W hW]
        ring
      mul := fun W hW f f' => by
        simp only [(h.der z).mul W hW, (h'.der z).mul W hW]
        ring
      res := fun W W' hle hW' f => by
        simp only [(h.der z).res W W' hle hW', (h'.der z).res W W' hle hW'] }
  base z r := by simp only [h.base, h'.base]
  hol W f := (h.hol W f).add (h'.hol W f)
  per l W f z hz := by
    simp only [h.per l W f z hz, h'.per l W f z hz, Matrix.add_mulVec, map_add]
    ring
end GlobalTheory.KS.Lin
