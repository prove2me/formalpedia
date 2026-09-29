-- Prove2me | solution 1 for LanglandsTunnell.Converse.prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_one_real_one_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a2a72ffb-8ce0-56d3-b237-9a6af564052c

import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_one_real_one_complex

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse

namespace Ws14Press11

open scoped Classical in
theorem univ_isReal_eq_singleton (K : Type) [Field K] [NumberField K]
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal) (wC : InfinitePlace K) (hC : wC.IsComplex)
    (hall : ∀ w : InfinitePlace K, w = wC ∨ w = w₀) :
    (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}) = {⟨w₀, h₀⟩} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, ?_⟩
  rintro ⟨w, hw⟩ -
  rcases hall w with h | h
  · exact absurd hw (h ▸ (InfinitePlace.not_isReal_iff_isComplex.mpr hC))
  · exact Subtype.ext h

open scoped Classical in
theorem univ_isComplex_eq_singleton (K : Type) [Field K] [NumberField K]
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal) (wC : InfinitePlace K) (hC : wC.IsComplex)
    (hall : ∀ w : InfinitePlace K, w = wC ∨ w = w₀) :
    (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}) = {⟨wC, hC⟩} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, ?_⟩
  rintro ⟨w, hw⟩ -
  rcases hall w with h | h
  · exact Subtype.ext h
  · exact absurd hw (h ▸ (InfinitePlace.not_isComplex_iff_isReal.mpr h₀))

open scoped Classical in
theorem twistedGammaR_sig11 (K : Type) [Field K] [NumberField K]
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal) (wC : InfinitePlace K) (hC : wC.IsComplex)
    (hall : ∀ w : InfinitePlace K, w = wC ∨ w = w₀) :
    twistedGammaR K archR uR aR = ((archR w₀ h₀).twist (uR w₀ h₀) (aR w₀ h₀)).gammaR := by
  rw [twistedGammaR, univ_isReal_eq_singleton K w₀ h₀ wC hC hall, Finset.sum_singleton]

open scoped Classical in
theorem twistedGammaC_sig11 (K : Type) [Field K] [NumberField K]
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal) (wC : InfinitePlace K) (hC : wC.IsComplex)
    (hall : ∀ w : InfinitePlace K, w = wC ∨ w = w₀) :
    twistedGammaC K archR archC uR aR uC kC =
      ((archR w₀ h₀).twist (uR w₀ h₀) (aR w₀ h₀)).gammaC + ((archC wC hC).twist (uC wC hC) (kC wC hC)).gammaC := by
  rw [twistedGammaC, univ_isReal_eq_singleton K w₀ h₀ wC hC hall, univ_isComplex_eq_singleton K w₀ h₀ wC hC hall,
    Finset.sum_singleton, Finset.sum_singleton]

open scoped Classical in
theorem archRootNumber_sig11 (K : Type) [Field K] [NumberField K]
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal) (wC : InfinitePlace K) (hC : wC.IsComplex)
    (hall : ∀ w : InfinitePlace K, w = wC ∨ w = w₀) :
    archRootNumber K archR archC uR aR uC kC =
      ((archR w₀ h₀).twist (uR w₀ h₀) (aR w₀ h₀)).epsilonFactor * ((archC wC hC).twist (uC wC hC) (kC wC hC)).epsilonFactor := by
  rw [archRootNumber, univ_isReal_eq_singleton K w₀ h₀ wC hC hall, univ_isComplex_eq_singleton K w₀ h₀ wC hC hall,
    Finset.prod_singleton, Finset.prod_singleton]

end Ws14Press11

open Ws14Press11 in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (w₀ wC : NumberField.InfinitePlace K) (h₀ : w₀.IsReal) (hC : wC.IsComplex)
    (hall : ∀ w : NumberField.InfinitePlace K, w = wC ∨ w = w₀)
    (uR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℤ)
    (P : RealArchParam) (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2) (hP : P = RealArchParam.principal ν₁ a₁ ν₂ a₂)
    (s : ℂ) :
    (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
          fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod =
        Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -uR w₀ h₀) + signShift (a₁ + aR w₀ h₀))) *
        Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -uR w₀ h₀) + signShift (a₂ + aR w₀ h₀)))) ∧
    (((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
          fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod =
        Complex.Gammaℂ (s + 1 / 2 + ((-ν₁ + -uC wC hC) + ((kC wC hC).natAbs : ℂ) / 2)) *
        Complex.Gammaℂ (s + 1 / 2 + ((-ν₂ + -uC wC hC) + ((kC wC hC).natAbs : ℂ) / 2))) ∧
    (archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val *
          (-1 : ℂ) ^ (Finset.univ : Finset {w : NumberField.InfinitePlace K // w.IsComplex}).card =
        (signEpsilon (a₁ + aR w₀ h₀) * signEpsilon (a₂ + aR w₀ h₀)) *
          (Complex.I ^ (kC wC hC).natAbs * Complex.I ^ (kC wC hC).natAbs) *
          (-1 : ℂ) ^ (a₁ + a₂).val * (-1 : ℂ) ^ 1) := by
  subst hP
  refine ⟨?_, ?_, ?_⟩
  · rw [twistedGammaR_sig11 K _ _ aR w₀ h₀ wC hC hall]
    simp [archOfParamR, RealArchParam.twist, RealArchParam.gammaR, RealArchParam.dual]
  · rw [twistedGammaC_sig11 K _ _ _ aR _ _ w₀ h₀ wC hC hall]
    simp [archOfParamR, archOfParamC, RealArchParam.twist, RealArchParam.gammaC, RealArchParam.baseChange, RealArchParam.dual,
      ComplexArchParam.dual, ComplexArchParam.twist, ComplexArchParam.gammaC, Int.natAbs_neg]
  · rw [archRootNumber_sig11 K _ _ uR aR uC kC w₀ h₀ wC hC hall, univ_isComplex_eq_singleton K w₀ h₀ wC hC hall,
      Finset.card_singleton]
    simp only [archOfParamR, archOfParamC, RealArchParam.twist, RealArchParam.epsilonFactor_principal, RealArchParam.baseChange,
      ComplexArchParam.twist, ComplexArchParam.epsilonFactor, zero_add, RealArchParam.centralSign]

end S_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_one_real_one_complex
end P2MW
export P2MW.S_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_one_real_one_complex (solution)
