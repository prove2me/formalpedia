-- Prove2me | solution 1 for GlobalTheory.associated_of_v_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:21:50.829699+00:00
-- url     : https://prove2.me/submissions/65d331c7-1146-48fd-9aca-78a418e56a53

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapPadicIntFinExtInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
namespace GlobalTheory
private theorem associated_prime_of_valuation_eq_one {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (c : ℤ_[l]) (hc : P.v LL (algebraMap ℤ_[l] ↥LL.1 c) = 1) : Associated c (l : ℤ_[l]) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, AddValuation.map_zero] at hc
    exact WithTop.top_ne_one hc
  have hspec := PadicInt.unitCoeff_spec hc0
  set u := PadicInt.unitCoeff hc0
  have hnn : ∀ w : ℤ_[l], 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 w) := fun w =>
    (P.v_O LL _).mpr (Subalgebra.algebraMap_mem _ w)
  have hu0 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) = 0 := by
    have h1 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) +
        P.v LL (algebraMap ℤ_[l] ↥LL.1 ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
    exact ((add_eq_zero_iff_of_nonneg (hnn _) (hnn _)).mp h1).1
  have hval : c.valuation = 1 := by
    rw [hspec, map_mul, AddValuation.map_mul, hu0, zero_add, map_pow, AddValuation.map_pow,
      map_natCast, P.v_l LL, nsmul_one] at hc
    exact_mod_cast hc
  refine ⟨u⁻¹, ?_⟩
  conv_lhs => rw [hspec]
  rw [hval, pow_one, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
end GlobalTheory
end

set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (y : ℤ_[l]) (x : ↥(OL LL)) (hy : algebraMap ℤ_[l] ↥(OL LL) y = x)
    (h : P.v LL (algebraMap ↥(OL LL) ↥LL.1 x - 1) = 1) : Associated (y - 1) (l : ℤ_[l]) := by
  apply associated_prime_of_valuation_eq_one P LL
  have hx : algebraMap ↥(OL LL) ↥LL.1 x = algebraMap ℤ_[l] ↥LL.1 y := by
    rw [← hy]
    rfl
  rw [map_sub, map_one, ← hx]
  exact h
end GlobalTheory
