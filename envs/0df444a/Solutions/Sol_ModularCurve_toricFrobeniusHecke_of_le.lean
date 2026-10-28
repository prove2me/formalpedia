-- Prove2me | solution 1 for ModularCurve.toricFrobeniusHecke_of_le
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:58:32.486127+00:00
-- url     : https://prove2.me/submissions/d1bad2d0-172f-4c7d-8950-a981e5dcef46

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_DeligneRapoport
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_MazurPrincipleCore
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_X0
import Definitions.Def_WeierstrassCurve_GenusOnePic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem solution (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime)
    (frob : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    [Module ModularCurve.HeckeAlg (ModularCurve.JZero (N * q))]
    (𝒯 U : Submodule ModularCurve.HeckeAlg (ModularCurve.JZero (N * q)))
    (hhecke : ModularCurve.ToricFrobeniusHecke ⟨q, hq⟩ frob 𝒯) (hle : U ≤ 𝒯) :
    ModularCurve.ToricFrobeniusHecke ⟨q, hq⟩ frob U := by
  intro x hx
  exact hhecke x (hle hx)
