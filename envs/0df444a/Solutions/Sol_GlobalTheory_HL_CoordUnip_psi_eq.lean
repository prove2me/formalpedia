-- Prove2me | solution 1 for GlobalTheory.HL.CoordUnip.psi_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:46.686617+00:00
-- url     : https://prove2.me/submissions/85a7d0b6-9a92-42b4-92db-1beec7a9c559

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Theorems.Thm_GlobalTheory_HL_CoordUnip_grp_apply
import Theorems.Thm_GlobalTheory_HL_CoordUnip_theta_eq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordUnip
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
namespace GlobalTheory.HL.CoordUnip
theorem _root_.solution (Fr : LocNG.FrameD H r) (f : Fin (r + 1) → S.V) (es : Fin r → S.V)
    (hf : ∀ a, f a = c.e (Fr.f a)) (hes : ∀ a, es a = c.e (Fr.es a)) (g : V ≃ₗ[E] V) :
    Fr.psiN (LocNG.theta M) g = S.psiOf f es (c.grp g) := by
  unfold LocNG.FrameD.psiN LocNG.FrameD.psiOf LocNG.FrameD.coefSum Frames.psiOf Frames.coef
  simp only [hf, hes, grp_apply, c.h_eq, theta_eq c]
end GlobalTheory.HL.CoordUnip
