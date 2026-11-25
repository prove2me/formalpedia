-- Prove2me | solution 1 for GlobalTheory.SecSpread.res_mem_secOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:02:53.56818+00:00
-- url     : https://prove2.me/submissions/9b53250f-c482-4a82-bf6d-2ed764f9224c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsDenomOfIsAffineOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
open GlobalTheory GlobalTheory.SecSpread
variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}
namespace GlobalTheory.SecSpread
theorem _root_.solution {L : LB X} (θ : L.Sec) (V : X.Opens) :
    (fun i => resG X (inf_le_right : V ⊓ L.U i ≤ L.U i) (θ.f i)) ∈ secOn L V := by
  intro i j
  refine fn_ext fun x hx => ?_
  have hx' : (𝟙 X : X ⟶ X) x ∈ V ⊓ L.U i ⊓ L.U j := hx
  have hm : (𝟙 X : X ⟶ X) x ∈ L.U i ⊓ L.U j := ⟨hx.1.2, hx.2⟩
  have e := congrArg (gs (𝟙 X) x _) (θ.compat i j)
  rw [gs_mul _ x _ hm, gs_res _ x _ hm, gs_res _ x _ hm] at e
  rw [gs_mul _ x _ hx', gs_res _ x _ hx', gs_res _ x _ hx', gs_res _ x _ hx', gs_res _ x _ hx'.1,
    gs_res _ x (V := V ⊓ L.U j) _ ⟨hx.1.1, hx.2⟩]
  exact e
end GlobalTheory.SecSpread
