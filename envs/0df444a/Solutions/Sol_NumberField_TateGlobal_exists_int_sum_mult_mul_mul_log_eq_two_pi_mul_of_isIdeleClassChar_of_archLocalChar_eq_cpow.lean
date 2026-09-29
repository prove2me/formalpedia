-- Prove2me | solution 1 for NumberField.TateGlobal.exists_int_sum_mult_mul_mul_log_eq_two_pi_mul_of_isIdeleClassChar_of_archLocalChar_eq_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/89081dac-ea4c-5e0f-9a2e-954e8b7d8ef5

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_eq_one_of_forall_isUnramifiedCharAt_of_fst_eq_one_of_mem_adicCompletionIntegers
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_NumberField_TateGlobal_exists_int_sum_mult_mul_mul_log_eq_two_pi_mul_of_isIdeleClassChar_of_archLocalChar_eq_cpow
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped Classical

noncomputable section

namespace C3b1Proof

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.TateGlobal

variable {K : Type} [Field K] [NumberField K]

theorem archUnitHom_coe {w : InfinitePlace K} (u : (w.Completion)ˣ) :
    ((archUnitHom w u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
      (Function.update (1 : Π v : InfinitePlace K, v.Completion) w (u : w.Completion), 1) := rfl

theorem ideleNorm_archUnitHom {w : InfinitePlace K} (u : (w.Completion)ˣ) :
    ideleNorm K (archUnitHom w u) = ‖(u : w.Completion)‖ ^ w.mult := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K (archUnitHom w u) rfl,
    archUnitHom_coe]
  rw [Finset.prod_eq_single w]
  · simp
  · intro v _ hv
    simp [Function.update_of_ne hv]
  · intro h
    exact absurd (Finset.mem_univ w) h

variable (K) in

def evalArchRing (w : InfinitePlace K) : AdeleRing (𝓞 K) K →+* w.Completion where
  toFun a := a.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable (K) in

def evalFinRing : AdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 K) K where
  toFun a := a.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable (K) in

def Uarch (w : InfinitePlace K) : (AdeleRing (𝓞 K) K)ˣ →* (w.Completion)ˣ := Units.map (evalArchRing K w).toMonoidHom

variable (K) in

def Ufin : (AdeleRing (𝓞 K) K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ := Units.map (evalFinRing K).toMonoidHom

theorem Uarch_coe (w : InfinitePlace K) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((Uarch K w z : (w.Completion)ˣ) : w.Completion) = ((z : AdeleRing (𝓞 K) K)).1 w := rfl

theorem Ufin_coe (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((Ufin K z : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) = ((z : AdeleRing (𝓞 K) K)).2 := rfl

theorem Uarch_archUnitHom_self (w : InfinitePlace K) (u : (w.Completion)ˣ) : Uarch K w (archUnitHom w u) = u := by
  ext
  show Function.update (1 : Π v : InfinitePlace K, v.Completion) w (u : w.Completion) w = u
  rw [Function.update_self]

theorem Uarch_archUnitHom_of_ne {w v : InfinitePlace K} (h : w ≠ v) (u : (v.Completion)ˣ) :
    Uarch K w (archUnitHom v u) = 1 := by
  ext
  show Function.update (1 : Π v : InfinitePlace K, v.Completion) v (u : v.Completion) w = (1 : w.Completion)
  rw [Function.update_of_ne h, Pi.one_apply]

theorem Ufin_archUnitHom (v : InfinitePlace K) (u : (v.Completion)ˣ) : Ufin K (archUnitHom v u) = 1 := by
  ext; rfl

variable (K) in

def unitAt (ε : (𝓞 K)ˣ) (v : InfinitePlace K) : (v.Completion)ˣ :=
  Units.map (algebraMap K v.Completion : K →* v.Completion) (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) ε)

theorem unitAt_coe (ε : (𝓞 K)ˣ) (v : InfinitePlace K) :
    ((unitAt K ε v : (v.Completion)ˣ) : v.Completion) = algebraMap K v.Completion (((ε : 𝓞 K)) : K) := rfl

theorem norm_unitAt (ε : (𝓞 K)ˣ) (v : InfinitePlace K) :
    ‖((unitAt K ε v : (v.Completion)ˣ) : v.Completion)‖ = v (((ε : 𝓞 K)) : K) := by
  rw [unitAt_coe]
  exact InfinitePlace.Completion.norm_coe v _

variable (K) in

def archPart (ε : (𝓞 K)ˣ) : (AdeleRing (𝓞 K) K)ˣ := ∏ v : InfinitePlace K, archUnitHom v (unitAt K ε v)

theorem Uarch_archPart (ε : (𝓞 K)ˣ) (w : InfinitePlace K) : Uarch K w (archPart K ε) = unitAt K ε w := by
  rw [archPart, map_prod, Finset.prod_eq_single w]
  · exact Uarch_archUnitHom_self w _
  · intro v _ hv
    exact Uarch_archUnitHom_of_ne hv.symm _
  · intro h; exact absurd (Finset.mem_univ w) h

theorem Ufin_archPart (ε : (𝓞 K)ˣ) : Ufin K (archPart K ε) = 1 := by
  rw [archPart, map_prod]
  exact Finset.prod_eq_one fun v _ => Ufin_archUnitHom v _

variable (K) in

def princ (ε : (𝓞 K)ˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) ε)

theorem princ_coe (ε : (𝓞 K)ˣ) :
    ((princ K ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = algebraMap K (AdeleRing (𝓞 K) K) (((ε : 𝓞 K)) : K) := rfl

theorem princ_inv (ε : (𝓞 K)ˣ) : (princ K ε)⁻¹ = princ K ε⁻¹ := by
  rw [princ, princ, ← map_inv, ← map_inv]

theorem Uarch_princ (ε : (𝓞 K)ˣ) (w : InfinitePlace K) : Uarch K w (princ K ε) = unitAt K ε w := by
  ext; rfl

theorem Ufin_princ_coe (ε : (𝓞 K)ˣ) :
    ((Ufin K (princ K ε) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) =
      algebraMap K (FiniteAdeleRing (𝓞 K) K) (((ε : 𝓞 K)) : K) := rfl

variable (K) in

def finPart (ε : (𝓞 K)ˣ) : (AdeleRing (𝓞 K) K)ˣ := princ K ε * (archPart K ε)⁻¹

theorem finPart_fst (ε : (𝓞 K)ˣ) : (((finPart K ε : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).1 = 1 := by
  funext w
  show ((Uarch K w (finPart K ε) : (w.Completion)ˣ) : w.Completion) = 1
  rw [finPart, map_mul, map_inv, Uarch_princ, Uarch_archPart, mul_inv_cancel, Units.val_one]

theorem Ufin_finPart (ε : (𝓞 K)ˣ) : Ufin K (finPart K ε) = Ufin K (princ K ε) := by
  rw [finPart, map_mul, map_inv, Ufin_archPart, inv_one, mul_one]

theorem finPart_snd_apply_mem (ε : (𝓞 K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((finPart K ε : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K := by
  show ((Ufin K (finPart K ε) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈ _
  rw [Ufin_finPart, Ufin_princ_coe, IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]
  exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v (ε : 𝓞 K)

theorem finPart_inv_snd_apply_mem (ε : (𝓞 K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((((finPart K ε)⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K := by
  show ((Ufin K (finPart K ε)⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈ _
  rw [map_inv, Ufin_finPart, ← map_inv, princ_inv, Ufin_princ_coe, IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]
  exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K)

theorem main
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (hχic : IsIdeleClassChar (𝓞 K) K χ)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), NumberField.TateGlobal.IsUnramifiedCharAt χ v)
    (σ : InfinitePlace K → ℝ)
    (hσ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ((NumberField.TateGlobal.archLocalChar χ v x : ℂˣ) : ℂ) =
        (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
          (((σ v : ℝ) : ℂ) * Complex.I))
    (ε : (𝓞 K)ˣ) :
    ∃ n : ℤ, ∑ v : InfinitePlace K, (v.mult : ℝ) * σ v * Real.log (v (((ε : 𝓞 K)) : K)) = 2 * Real.pi * n := by

  have hprinc : χ (princ K ε) = 1 := hχic _
  have hfin : χ (finPart K ε) = 1 :=
    NumberField.TateGlobal.eq_one_of_forall_isUnramifiedCharAt_of_fst_eq_one_of_mem_adicCompletionIntegers K χ hχc
      hram _ (finPart_fst ε) fun v => ⟨finPart_snd_apply_mem ε v, finPart_inv_snd_apply_mem ε v⟩

  have harch : χ (archPart K ε) = 1 := by
    have : princ K ε = finPart K ε * archPart K ε := by rw [finPart, inv_mul_cancel_right]
    rw [this, map_mul, hfin, one_mul] at hprinc
    exact hprinc

  have hpos : ∀ v : InfinitePlace K, 0 < v (((ε : 𝓞 K)) : K) := fun v =>
    AbsoluteValue.pos v.1 (by exact_mod_cast ε.ne_zero)
  set a : InfinitePlace K → ℝ := fun v => (v.mult : ℝ) * σ v * Real.log (v (((ε : 𝓞 K)) : K)) with ha
  have hval : ∀ v : InfinitePlace K, ((χ (archUnitHom v (unitAt K ε v)) : ℂˣ) : ℂ) = Complex.exp ((a v : ℂ) * Complex.I) := by
    intro v
    have h := hσ v (unitAt K ε v)
    change ((χ (archUnitHom v (unitAt K ε v)) : ℂˣ) : ℂ) = _ at h
    have hN : 0 < v (((ε : 𝓞 K)) : K) ^ v.mult := pow_pos (hpos v) _
    rw [h, ideleNorm_archUnitHom, norm_unitAt, Complex.cpow_def_of_ne_zero (by exact_mod_cast hN.ne'),
      ← Complex.ofReal_log hN.le, Real.log_pow]
    congr 1
    rw [ha]
    push_cast
    ring

  have hprod : ((χ (archPart K ε) : ℂˣ) : ℂ) = Complex.exp ((∑ v : InfinitePlace K, (a v : ℂ)) * Complex.I) := by
    rw [archPart, map_prod, Units.coe_prod, Finset.sum_mul, Complex.exp_sum]
    exact Finset.prod_congr rfl fun v _ => hval v
  rw [harch, Units.val_one] at hprod
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hprod.symm
  refine ⟨n, ?_⟩
  have hI : (∑ v : InfinitePlace K, (a v : ℂ)) = ((2 * Real.pi * n : ℝ) : ℂ) := by
    have : (∑ v : InfinitePlace K, (a v : ℂ)) * Complex.I = ((2 * Real.pi * n : ℝ) : ℂ) * Complex.I := by
      rw [hn]; push_cast; ring
    exact mul_right_cancel₀ Complex.I_ne_zero this
  have h2 : ((∑ v : InfinitePlace K, a v : ℝ) : ℂ) = ((2 * Real.pi * n : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]; exact hI
  exact Complex.ofReal_injective h2

end C3b1Proof

theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (hχic : IsIdeleClassChar (𝓞 K) K χ)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), NumberField.TateGlobal.IsUnramifiedCharAt χ v)
    (σ : InfinitePlace K → ℝ)
    (hσ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ((NumberField.TateGlobal.archLocalChar χ v x : ℂˣ) : ℂ) =
        (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
          (((σ v : ℝ) : ℂ) * Complex.I))
    (ε : (𝓞 K)ˣ) :
    ∃ n : ℤ, ∑ v : InfinitePlace K, (v.mult : ℝ) * σ v * Real.log (v (((ε : 𝓞 K)) : K)) = 2 * Real.pi * n :=
  C3b1Proof.main χ hχc hχic hram σ hσ ε

end
end S_NumberField_TateGlobal_exists_int_sum_mult_mul_mul_log_eq_two_pi_mul_of_isIdeleClassChar_of_archLocalChar_eq_cpow
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_int_sum_mult_mul_mul_log_eq_two_pi_mul_of_isIdeleClassChar_of_archLocalChar_eq_cpow (solution)
