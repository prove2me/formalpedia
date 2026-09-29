-- Prove2me | solution 1 for NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/dde32d61-7777-5bc6-abdc-1666f63c441a

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isComplex

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace PsiLine40

open scoped Classical in
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.StandardAddChar in

theorem infTraceSum_single_of_isComplex (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (z : ℂ) : infTraceSum F (Pi.single w ((ringEquivComplexOfIsComplex hw).symm z)) = 2 * z.re := by
  unfold infTraceSum
  rw [Finset.sum_eq_single w]
  · rw [Pi.single_eq_same, mult_isComplex ⟨w, hw⟩]
    have hre : (extensionEmbedding w ((ringEquivComplexOfIsComplex hw).symm z)).re = z.re := by
      rw [← ringEquivComplexOfIsComplex_apply hw, RingEquiv.apply_symm_apply]
    rw [hre]
    push_cast
    ring
  · intro w' _ hw'
    rw [Pi.single_eq_of_ne hw', map_zero, Complex.zero_re, mul_zero]
  · intro h; exact absurd (Finset.mem_univ w) h

open NumberField.StandardAddChar in

theorem psiArch_ratArchLine (t : ℝ) :
    psiArch (ratArchLine t) = Complex.exp (2 * Real.pi * Complex.I * t) := by
  have h1 : psiArch (ratArchLine t) = psiArchPlace default (ratArchLine t default) := by
    rw [psiArch_apply]
    exact finprod_unique _
  rw [h1, psiArchPlace_apply, ratArchLine_apply, ← NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    RingEquiv.apply_symm_apply]

end PsiLine40

open scoped Classical in
open PsiLine40 NumberField.StandardAddChar in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂ) :
    NumberField.StandardAddChar.stdAddChar K
        (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z), 0)) =
      Complex.exp (2 * Real.pi * Complex.I * ((2 * z.re : ℝ) : ℂ)) := by
  show (adelicTraceData K).psiK _ = _
  rw [AdelicTraceData.psiK_apply, AdelicTraceData.adelicTrace_apply, psiQ_apply]
  have hfin : (adelicTraceData K).traceFin
      ((show (AdeleRing (𝓞 K) K) from
        (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z), 0))).2 = 0 := by
    show (adelicTraceData K).traceFin 0 = 0
    exact map_zero _
  have hinf : (adelicTraceData K).traceInf
      ((show (AdeleRing (𝓞 K) K) from
        (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z), 0))).1 = ratArchLine (2 * z.re) := by
    show traceInfHom K (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z)) = _
    rw [traceInfHom_apply, infTraceSum_single_of_isComplex K w hw z]
  rw [hfin, AddChar.map_zero_eq_one, mul_one, hinf, psiArch_ratArchLine]

end S_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isComplex
end P2MW
export P2MW.S_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isComplex (solution)
