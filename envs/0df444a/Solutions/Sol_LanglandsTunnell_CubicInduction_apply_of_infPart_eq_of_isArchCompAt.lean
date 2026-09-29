-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.apply_of_infPart_eq_of_isArchCompAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f2d2a213-e803-5908-baa3-91d64b2f16d7

import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_apply_of_infPart_eq_of_isArchCompAt

set_option autoImplicit false

open NumberField LanglandsTunnell.Converse

open LanglandsTunnell.CubicInduction in

theorem solution
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (t : ℂ) (e : ℤ) (hχ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ χ v t e)
    (z : (InfiniteAdeleRing ℚ)ˣ) (v : InfinitePlace ℚ) (hv : v.IsReal) :
    ((χ (E z) : ℂˣ) : ℂ) =
      ((‖(z : InfiniteAdeleRing ℚ) v‖ : ℂ) ^ ((v.mult : ℂ) * t)) *
        (NumberField.InfinitePlace.Completion.extensionEmbedding v ((z : InfiniteAdeleRing ℚ) v) /
            (‖(z : InfiniteAdeleRing ℚ) v‖ : ℂ)) ^ e := by

  let zv : (v.Completion)ˣ :=
    ⟨(z : InfiniteAdeleRing ℚ) v, ((z⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) v,
      congrFun z.mul_inv v, congrFun z.inv_mul v⟩
  have hEz : E z = TateGlobal.archUnitHom v zv := by
    apply Units.ext
    show ((E z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)
      = ((AdelicVolume.archCentralUnit ℚ v zv : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)
    have h1 : ((E z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = (z : InfiniteAdeleRing ℚ) :=
      congrArg Units.val (hE z).1
    have h2 : ((E z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := congrArg Units.val (hE z).2
    refine Prod.ext ?_ ?_
    · rw [h1]
      funext w
      have hw : w = v := Subsingleton.elim w v
      subst hw
      exact (AdelicVolume.archCentralUnit_fst_self (F := ℚ) w zv).symm
    · rw [h2]
      exact (AdelicVolume.archCentralUnit_snd (F := ℚ) v zv).symm
  rw [hEz]
  exact hχ v hv zv

end S_LanglandsTunnell_CubicInduction_apply_of_infPart_eq_of_isArchCompAt
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_apply_of_infPart_eq_of_isArchCompAt (solution)
