-- Prove2me | solution 1 for LanglandsTunnell.Converse.prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_one_real_one_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/9043d568-7ef6-57e0-9a72-5b45e6cde4a4

import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_one_real_one_complex

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse

namespace PressDisc11

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

theorem neg_one_pow_val_natCast_add_one (n : ℕ) :
    (-1 : ℂ) ^ (((n : ZMod 2) + 1).val) = (-1 : ℂ) ^ (n + 1) := by
  have h : ((n : ZMod 2) + 1) = ((n + 1 : ℕ) : ZMod 2) := by push_cast; rfl
  rw [h, ZMod.val_natCast, ← neg_one_pow_eq_pow_mod_two]

theorem natAbs_neg_add_neg (a b : ℤ) : (-a + -b).natAbs = (a + b).natAbs := by
  rw [← neg_add, Int.natAbs_neg]

theorem natAbs_add_neg (a b : ℤ) : (a + -b).natAbs = (-a + b).natAbs := by
  rw [← Int.natAbs_neg, neg_add, neg_neg]

end PressDisc11

open PressDisc11 in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (w₀ wC : NumberField.InfinitePlace K) (h₀ : w₀.IsReal) (hC : wC.IsComplex)
    (hall : ∀ w : NumberField.InfinitePlace K, w = wC ∨ w = w₀)
    (uR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℤ)
    (P : RealArchParam) (uP : ℂ) (nP : ℕ) (hnP : 1 ≤ nP) (hP : P = RealArchParam.discrete uP nP hnP)
    (s : ℂ) :
    (((twistedGammaR K (archOfParamR K P) uR aR).map fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod = 1) ∧
    (((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod =
        Complex.Gammaℂ (s + 1 / 2 + ((uP + uR w₀ h₀) + (nP : ℂ) / 2)) *
        (Complex.Gammaℂ (s + 1 / 2 + ((uP + uC wC hC) + ((((nP : ℤ) + kC wC hC).natAbs : ℕ) : ℂ) / 2)) *
        Complex.Gammaℂ (s + 1 / 2 + ((uP + uC wC hC) + (((-(nP : ℤ) + kC wC hC).natAbs : ℕ) : ℂ) / 2)))) ∧
    (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
          fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod = 1) ∧
    (((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
          fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod =
        Complex.Gammaℂ (s + 1 / 2 + ((-uP + -uR w₀ h₀) + (nP : ℂ) / 2)) *
        (Complex.Gammaℂ (s + 1 / 2 + ((-uP + -uC wC hC) + ((((nP : ℤ) + kC wC hC).natAbs : ℕ) : ℂ) / 2)) *
        Complex.Gammaℂ (s + 1 / 2 + ((-uP + -uC wC hC) + (((-(nP : ℤ) + kC wC hC).natAbs : ℕ) : ℂ) / 2)))) ∧
    (archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val *
          (-1 : ℂ) ^ (Finset.univ : Finset {w : NumberField.InfinitePlace K // w.IsComplex}).card =
        Complex.I ^ (nP + 1) *
          (Complex.I ^ ((nP : ℤ) + kC wC hC).natAbs * Complex.I ^ (-(nP : ℤ) + kC wC hC).natAbs) *
          (-1 : ℂ) ^ (nP + 1) * (-1 : ℂ) ^ 1) := by
  subst hP
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [twistedGammaR_sig11 K _ _ aR w₀ h₀ wC hC hall]
    simp only [archOfParamR, RealArchParam.twist, RealArchParam.gammaR, Multiset.map_zero, Multiset.prod_zero]
  · rw [twistedGammaC_sig11 K _ _ _ aR _ _ w₀ h₀ wC hC hall]
    simp only [archOfParamR, archOfParamC, RealArchParam.twist, RealArchParam.gammaC, RealArchParam.baseChange,
      ComplexArchParam.twist, ComplexArchParam.gammaC, Multiset.map_add, Multiset.prod_add, Multiset.map_singleton,
      Multiset.prod_singleton, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons]
  · rw [twistedGammaR_sig11 K _ _ aR w₀ h₀ wC hC hall]
    simp only [archOfParamR, RealArchParam.dual, RealArchParam.twist, RealArchParam.gammaR, Multiset.map_zero,
      Multiset.prod_zero]
  · rw [twistedGammaC_sig11 K _ _ _ aR _ _ w₀ h₀ wC hC hall]
    simp only [archOfParamR, archOfParamC, RealArchParam.dual, RealArchParam.twist, RealArchParam.gammaC,
      RealArchParam.baseChange, ComplexArchParam.dual, ComplexArchParam.twist, ComplexArchParam.gammaC, neg_neg,
      natAbs_add_neg, Multiset.map_add, Multiset.prod_add, Multiset.map_singleton,
      Multiset.prod_singleton, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons]
  · rw [archRootNumber_sig11 K _ _ uR aR uC kC w₀ h₀ wC hC hall, univ_isComplex_eq_singleton K w₀ h₀ wC hC hall,
      Finset.card_singleton]
    simp only [archOfParamR, archOfParamC, RealArchParam.twist, RealArchParam.epsilonFactor_discrete,
      RealArchParam.baseChange, ComplexArchParam.twist, ComplexArchParam.epsilonFactor, RealArchParam.centralSign,
      neg_one_pow_val_natCast_add_one]

#print axioms solution

end S_LanglandsTunnell_Converse_prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_one_real_one_complex
end P2MW
export P2MW.S_LanglandsTunnell_Converse_prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_one_real_one_complex (solution)
