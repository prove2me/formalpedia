-- Prove2me | solution 1 for ModularCurve.Period.finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e8a15ddc-6513-5410-9aca-ec001d8484c8

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix MatrixGroups Subgroup MulAction ModularCurve.Period

noncomputable section

namespace BassSerreCuspDim

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (K : Type) [Field K]

abbrev Cu : Type := orbitRel.Quotient (zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Γ)

def cusp (x : SL(2, ℤ) ⧸ Γ) : Cu Γ := Quotient.mk (orbitRel (zpowers ModularGroup.T) _) x

theorem cusp_surjective : Function.Surjective (cusp Γ) := Quotient.mk_surjective

def wd (x : SL(2, ℤ) ⧸ Γ) : ℕ := Function.minimalPeriod (fun y => ModularGroup.T • y) x

theorem gen_mem (g : SL(2, ℤ)) : g⁻¹ * ModularGroup.T ^ wd Γ (g : SL(2, ℤ) ⧸ Γ) * g ∈ Γ := by
  have h0 : ModularGroup.T ^ wd Γ (g : SL(2, ℤ) ⧸ Γ) • (g : SL(2, ℤ) ⧸ Γ) = (g : SL(2, ℤ) ⧸ Γ) :=
    (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl
  have h1 : ((ModularGroup.T ^ wd Γ (g : SL(2, ℤ) ⧸ Γ) * g : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ)
      = (g : SL(2, ℤ) ⧸ Γ) := h0
  rw [QuotientGroup.eq] at h1
  have h2 := Γ.inv_mem h1
  simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc] using h2

def rep (c : Cu Γ) : SL(2, ℤ) := Quotient.out (Quotient.out c)

theorem cusp_rep (c : Cu Γ) : cusp Γ (rep Γ c : SL(2, ℤ) ⧸ Γ) = c := by
  rw [rep, QuotientGroup.out_eq', cusp]; exact Quotient.out_eq c

def genOf (c : Cu Γ) : Γ := ⟨_, gen_mem Γ (rep Γ c)⟩

theorem trace_genOf (c : Cu Γ) :
    ((genOf Γ c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  show (((rep Γ c)⁻¹ * ModularGroup.T ^ wd Γ (rep Γ c : SL(2, ℤ) ⧸ Γ) * rep Γ c : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ).trace = 2
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, ← zpow_natCast, ModularGroup.coe_T_zpow]
  simp [Matrix.trace_fin_two]

def ev : (Additive Γ →+ K) →ₗ[K] (Cu Γ → K) where
  toFun φ c := φ (Additive.ofMul (genOf Γ c))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem parabolicHoms_le_ker : parabolicHoms K Γ K ≤ LinearMap.ker (ev Γ K) := by
  intro φ hφ
  rw [LinearMap.mem_ker]
  funext c
  exact hφ (genOf Γ c) (by rw [trace_genOf]; norm_num)

def sumL [Fintype (Cu Γ)] : (Cu Γ → K) →ₗ[K] K where
  toFun v := ∑ c, v c
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum]

theorem ker_sumL_le_range (hneg : (-1 : SL(2, ℤ)) ∈ Γ) [Fintype (Cu Γ)] :
    LinearMap.ker (sumL Γ K) ≤ LinearMap.range (ev Γ K) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv
  have hv' : ∑ᶠ c, v c = 0 := by rw [finsum_eq_sum_of_fintype]; exact hv
  obtain ⟨φ, hφ⟩ :=
    Matrix.SpecialLinearGroup.exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero
      Γ hneg K v hv'
  refine ⟨φ, funext fun c => ?_⟩
  show φ (Additive.ofMul (genOf Γ c)) = v c
  have key := hφ (rep Γ c) (gen_mem Γ (rep Γ c))
  exact key.trans (congrArg v (cusp_rep Γ c))

theorem finrank_ker_sumL_add_one [Fintype (Cu Γ)] :
    Module.finrank K (LinearMap.ker (sumL Γ K)) + 1 = Fintype.card (Cu Γ) := by
  classical
  have c₀ : Cu Γ := cusp Γ ((1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ)
  have hsurj : Function.Surjective (sumL Γ K) := fun r =>
    ⟨Pi.single c₀ r, by simp [sumL]⟩
  have h1 : Module.finrank K (LinearMap.range (sumL Γ K)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have h2 := LinearMap.finrank_range_add_finrank_ker (sumL Γ K)
  rw [h1, Module.finrank_fintype_fun_eq_card] at h2
  omega

theorem moduleFinite_hom : Module.Finite K (Additive Γ →+ K) := by
  classical
  haveI : Group.FG SL(2, ℤ) := ⟨⟨{ModularGroup.S, ModularGroup.T}, by
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact SpecialLinearGroup.SL2Z_generators⟩⟩
  haveI hΓ : Group.FG Γ := Subgroup.fg_of_index_ne_zero _
  obtain ⟨s, hs⟩ := hΓ.out
  let e : (Additive Γ →+ K) →ₗ[K] (s → K) :=
    { toFun := fun φ i => φ (Additive.ofMul (i : Γ))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective e ?_
  intro φ ψ h
  have key : ∀ γ : Γ, φ (Additive.ofMul γ) = ψ (Additive.ofMul γ) := by
    intro γ
    have hγ : γ ∈ Subgroup.closure (s : Set Γ) := by rw [hs]; exact Subgroup.mem_top γ
    induction hγ using Subgroup.closure_induction with
    | mem x hx => exact congrFun h ⟨x, hx⟩
    | one => rw [ofMul_one, map_zero, map_zero]
    | mul x y _ _ hx hy => rw [ofMul_mul, map_add, map_add, hx, hy]
    | inv x _ hx => rw [ofMul_inv, map_neg, map_neg, hx]
  exact AddMonoidHom.ext fun x => key (Additive.toMul x)

theorem main (hneg : (-1 : SL(2, ℤ)) ∈ Γ) :
    Module.finrank K (parabolicHoms K Γ K) + Nat.card (Cu Γ)
      ≤ Module.finrank K (Additive Γ →+ K) + 1 := by
  classical
  haveI : Fintype (Cu Γ) := Fintype.ofFinite _
  haveI := moduleFinite_hom Γ K
  have h1 : Module.finrank K (parabolicHoms K Γ K) ≤ Module.finrank K (LinearMap.ker (ev Γ K)) :=
    Submodule.finrank_mono (parabolicHoms_le_ker Γ K)
  have h2 : Module.finrank K (LinearMap.ker (sumL Γ K))
      ≤ Module.finrank K (LinearMap.range (ev Γ K)) :=
    Submodule.finrank_mono (ker_sumL_le_range Γ K hneg)
  have h3 := finrank_ker_sumL_add_one Γ K
  have h4 := LinearMap.finrank_range_add_finrank_ker (ev Γ K)
  rw [Nat.card_eq_fintype_card]
  omega

end BassSerreCuspDim

theorem solution (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (K : Type) [Field K] :
    Module.finrank K (ModularCurve.Period.parabolicHoms K Γ K)
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      ≤ Module.finrank K (Additive Γ →+ K) + 1 :=
  BassSerreCuspDim.main Γ K hneg

#print axioms solution

end
end S_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one
end P2MW
export P2MW.S_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one (solution)
