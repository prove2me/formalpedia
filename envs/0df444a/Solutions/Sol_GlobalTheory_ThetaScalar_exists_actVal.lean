-- Prove2me | solution 1 for GlobalTheory.ThetaScalar.exists_actVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:49:35.822372+00:00
-- url     : https://prove2.me/submissions/12754cb6-4fb3-48cf-86f7-a95dada5618c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Theorems.Thm_GlobalTheory_ThetaScalar_translT_snd_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_formEq_of_add


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaScalar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
namespace GlobalTheory.ThetaScalar
theorem _root_.solution (hL : L.IsLB) (θ : ThetaGrp A L k T) (s : LB.Sec (LPow A L k T)) : ∃ s', ActVal θ s s' := by
  obtain ⟨s', hs'⟩ := exists_sec hL (K' := Fin 1) (φ' := fun _ => (snd T A).left) (ε' := fun _ => k)
    (formEq_of_add fun U _ h => by
      simp [Fintype.sum_sum_type, Fin.sum_univ_succ, ← translT_snd_left])
    (pullMulSec (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => k) s (translT A θ.pt).left
      (φ₃ := ![(snd T A).left, (translPt A θ.pt).left]) (ε₃ := ![k, -k]) θ.φ θ.isGen)
  exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans (mul_comm _ _))⟩
end GlobalTheory.ThetaScalar
