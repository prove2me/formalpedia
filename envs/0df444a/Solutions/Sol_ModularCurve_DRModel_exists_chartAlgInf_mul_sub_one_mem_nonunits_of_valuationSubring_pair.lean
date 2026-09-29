-- Prove2me | solution 1 for ModularCurve.DRModel.exists_chartAlgInf_mul_sub_one_mem_nonunits_of_valuationSubring_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/489ff05a-4926-546b-9d8a-ca780b963c2d

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Theorems.Thm_ModularCurve_forall_mem_chartAlgInf_jFull_exists_mul_mem_and_symm_of_coe_eq_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModel_exists_chartAlgInf_mul_sub_one_mem_nonunits_of_valuationSubring_pair
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option Elab.async false

open scoped Polynomial

noncomputable section

open AlgebraicCurve

namespace TensorAdapt

section ChartRing

variable (κ : Type) [Field κ]

theorem aeval_X_eq_algebraMap (f : κ[X]) :
    Polynomial.aeval (RatFunc.X : RatFunc κ) f = algebraMap κ[X] (RatFunc κ) f := by
  rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left, AlgHom.coe_id, id]

theorem aeval_X_injective :
    Function.Injective (Polynomial.aeval (RatFunc.X : RatFunc κ) : κ[X] →ₐ[κ] RatFunc κ) := by
  intro f g h
  apply RatFunc.algebraMap_injective (K := κ)
  rwa [← aeval_X_eq_algebraMap, ← aeval_X_eq_algebraMap]

end ChartRing

section MidLift

open AlgebraicCurve.TwoChartIntegralModel

variable (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (j : F) [Fact (j ≠ 0)]
  (𝔭 : Ideal ↥(chartAlgFin ℤ F j)) (e : (↥(chartAlgFin ℤ F j) ⧸ 𝔭) ≃+* (ZMod p)[X]) (m : ℕ)

def ρ₀ : ↥(chartAlgFin ℤ F j) →+* RatFunc (ZMod p) :=
  (Polynomial.aeval (RatFunc.X : RatFunc (ZMod p)) : (ZMod p)[X] →ₐ[ZMod p] RatFunc (ZMod p)).toRingHom.comp
    (e.toRingHom.comp (Ideal.Quotient.mk 𝔭))

theorem ρ₀_apply (b : ↥(chartAlgFin ℤ F j)) :
    ρ₀ p j 𝔭 e b = Polynomial.aeval (RatFunc.X : RatFunc (ZMod p)) (e (Ideal.Quotient.mk 𝔭 b)) := rfl

variable (hej : e (Ideal.Quotient.mk 𝔭 (jChartFin ℤ F j)) = Polynomial.X ^ m)

include hej in
theorem ρ₀_j : ρ₀ p j 𝔭 e (jChartFin ℤ F j) = RatFunc.X ^ m := by
  rw [ρ₀_apply, hej, map_pow, Polynomial.aeval_X]

include hej in
theorem isUnit_ρ₀_j : IsUnit (ρ₀ p j 𝔭 e (jChartFin ℤ F j)) := by
  rw [ρ₀_j p j 𝔭 e m hej]
  exact (isUnit_iff_ne_zero.mpr RatFunc.X_ne_zero).pow m

def ρ₀M : ↥(chartAlgMid ℤ F j) →+* RatFunc (ZMod p) :=
  letI := (TwoChartIntegralModel.inclFin ℤ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin ℤ F j
  IsLocalization.Away.lift (jChartFin ℤ F j) (g := ρ₀ p j 𝔭 e) (isUnit_ρ₀_j p j 𝔭 e m hej)

theorem ρ₀M_inclFin (b : ↥(chartAlgFin ℤ F j)) : ρ₀M p j 𝔭 e m hej (TwoChartIntegralModel.inclFin ℤ F j b) = ρ₀ p j 𝔭 e b := by
  letI := (TwoChartIntegralModel.inclFin ℤ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin ℤ F j
  exact IsLocalization.Away.lift_eq (jChartFin ℤ F j) (isUnit_ρ₀_j p j 𝔭 e m hej) b

def ρ₀' : ↥(chartAlgInf ℤ F j) →+* RatFunc (ZMod p) :=
  (ρ₀M p j 𝔭 e m hej).comp (TwoChartIntegralModel.inclInf ℤ F j).toRingHom

theorem ρ₀'_mul_pow (b : ↥(chartAlgFin ℤ F j)) (b' : ↥(chartAlgInf ℤ F j)) (n : ℕ)
    (h : (b : F) = (b' : F) * j ^ n) :
    ρ₀' p j 𝔭 e m hej b' * RatFunc.X ^ (m * n) = ρ₀ p j 𝔭 e b := by
  have hmid : TwoChartIntegralModel.inclInf ℤ F j b' * TwoChartIntegralModel.inclFin ℤ F j (jChartFin ℤ F j) ^ n =
      TwoChartIntegralModel.inclFin ℤ F j b := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, TwoChartIntegralModel.coe_chartIncl, coe_jChartFin]
    exact h.symm
  have := congrArg (ρ₀M p j 𝔭 e m hej) hmid
  rw [map_mul, map_pow, ρ₀M_inclFin, ρ₀M_inclFin, ρ₀_j p j 𝔭 e m hej, ← pow_mul] at this
  exact this

theorem ρ₀'_jInv (hm : 0 < m ∨ True) : ρ₀' p j 𝔭 e m hej (jInvChartInf ℤ F j) = (RatFunc.X ^ m)⁻¹ := by
  have h := ρ₀'_mul_pow p j 𝔭 e m hej 1 (jInvChartInf ℤ F j) 1
    (by rw [coe_jInvChartInf, pow_one, inv_mul_cancel₀ (Fact.out : j ≠ 0)]; rfl)
  rw [mul_one, map_one] at h
  exact eq_inv_of_mul_eq_one_left h

end MidLift

end TensorAdapt

end

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel ModularCurve Polynomial

noncomputable section

namespace S2a

theorem Subring.mem_of_unit_mul_mem_of_pow_mul_mem {K : Type*} [CommRing K] (B : Subring K)
    {y t g u : K} (ht : t ∈ B) (hg : g ∈ B) (hu : u = 1 + t * g) (huy : u * y ∈ B)
    {k : ℕ} (hk : t ^ k * y ∈ B) : y ∈ B := by

  let I : Ideal B :=
    { carrier := {b : B | (b : K) * y ∈ B}
      add_mem' := fun {a b} ha hb => by
        change ((a + b : B) : K) * y ∈ B
        rw [Subring.coe_add, add_mul]
        exact B.add_mem ha hb
      zero_mem' := by
        change ((0 : B) : K) * y ∈ B
        rw [Subring.coe_zero, zero_mul]
        exact B.zero_mem
      smul_mem' := fun c {b} hb => by
        change ((c * b : B) : K) * y ∈ B
        rw [Subring.coe_mul, mul_assoc]
        exact B.mul_mem c.2 hb }
  have huB : u ∈ B := by rw [hu]; exact B.add_mem B.one_mem (B.mul_mem ht hg)
  have huI : (⟨u, huB⟩ : B) ∈ I := huy
  have htI : (⟨t, ht⟩ : B) ^ k ∈ I := by
    change (((⟨t, ht⟩ : B) ^ k : B) : K) * y ∈ B
    rwa [Subring.coe_pow]
  have htr : (⟨t, ht⟩ : B) ∈ I.radical := ⟨k, htI⟩
  have hone : (1 : B) ∈ I.radical := by
    have : (1 : B) = ⟨u, huB⟩ - ⟨t, ht⟩ * ⟨g, hg⟩ := by
      apply Subtype.ext
      change (1 : K) = u - t * g
      rw [hu, add_sub_cancel_right]
    rw [this]
    exact I.radical.sub_mem (Ideal.le_radical huI) (I.radical.mul_mem_right _ htr)
  have hI : I = ⊤ := by
    rw [← Ideal.radical_eq_top, Ideal.eq_top_iff_one]
    exact hone
  have h1 : (1 : B) ∈ I := by rw [hI]; trivial
  have : ((1 : B) : K) * y ∈ B := h1
  rwa [Subring.coe_one, one_mul] at this

section Modular

variable (p : ℕ) [Fact p.Prime] [NeZero p]

variable (jp : ↥(chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
  (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
  (𝔭₁ : Ideal ↥(chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (e₁ : (↥(chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⧸ 𝔭₁) ≃+* (ZMod p)[X])
  (he₁jp : e₁ (Ideal.Quotient.mk 𝔭₁ jp) = Polynomial.X)
  (he₁j : e₁ (Ideal.Quotient.mk 𝔭₁ (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = Polynomial.X ^ p)

abbrev ρ : ↥(chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* RatFunc (ZMod p) := TensorAdapt.ρ₀' p (IgusaScheme.jFull p) 𝔭₁ e₁ p he₁j

include he₁jp in

theorem jp_ne_zero' : (jp : ↥(modularFunctionFieldFull p)) ≠ 0 := by
  intro h0
  have hjp0 : jp = 0 := Subtype.ext h0
  rw [hjp0, map_zero, map_zero] at he₁jp
  exact Polynomial.X_ne_zero he₁jp.symm

include he₁jp in

theorem ρ₀_jp : TensorAdapt.ρ₀ p (IgusaScheme.jFull p) 𝔭₁ e₁ jp = (RatFunc.X : RatFunc (ZMod p)) := by
  rw [TensorAdapt.ρ₀_apply, he₁jp, Polynomial.aeval_X]

include hjp he₁jp in

theorem exists_ρ_mul_X_eq :
    ∃ a h : ↥(chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), ρ p 𝔭₁ e₁ he₁j h * (RatFunc.X : RatFunc (ZMod p)) = 1 + ρ p 𝔭₁ e₁ he₁j (jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) * ρ p 𝔭₁ e₁ he₁j a := by
  haveI : Fact ((jp : ↥(modularFunctionFieldFull p)) ≠ 0) := ⟨jp_ne_zero' p jp 𝔭₁ e₁ he₁jp⟩
  obtain ⟨hvis, -⟩ :=
    ModularCurve.forall_mem_chartAlgInf_jFull_exists_mul_mem_and_symm_of_coe_eq_qExpand p p (jp : ↥(modularFunctionFieldFull p)) hjp
  obtain ⟨s, hs, ⟨a, ha, hsa⟩, hsy⟩ := hvis ((jp : ↥(modularFunctionFieldFull p))⁻¹) (subset_chartAlg ℤ ↥(modularFunctionFieldFull p) _ rfl)
  refine ⟨⟨a, ha⟩, ⟨s * (jp : ↥(modularFunctionFieldFull p))⁻¹, hsy⟩, ?_⟩

  have hmid : TwoChartIntegralModel.inclInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ⟨s * (jp : ↥(modularFunctionFieldFull p))⁻¹, hsy⟩ *
      TwoChartIntegralModel.inclFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) jp =
      1 + TwoChartIntegralModel.inclInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) (jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) *
        TwoChartIntegralModel.inclInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ⟨a, ha⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one,
      TwoChartIntegralModel.coe_chartIncl, coe_jInvChartInf]
    rw [inv_mul_cancel_right₀ (jp_ne_zero' p jp 𝔭₁ e₁ he₁jp)]
    exact hsa
  have h := congrArg (TensorAdapt.ρ₀M p (IgusaScheme.jFull p) 𝔭₁ e₁ p he₁j) hmid
  rw [map_mul, map_add, map_one, map_mul, TensorAdapt.ρ₀M_inclFin, ρ₀_jp p jp 𝔭₁ e₁ he₁jp] at h
  exact h

omit [Fact p.Prime] in

theorem exists_coe_eq_mul_pow (b₀ : ↥(chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : ∃ (b' : ↥(chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (k : ℕ), (b₀ : ↥(modularFunctionFieldFull p)) = (b' : ↥(modularFunctionFieldFull p)) * ((IgusaScheme.jFull p) : ↥(modularFunctionFieldFull p)) ^ k := by
  letI := (TwoChartIntegralModel.inclInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
  obtain ⟨⟨b', ⟨_, ⟨k, rfl⟩⟩⟩, hb⟩ :=
    IsLocalization.surj (Submonoid.powers (jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (TwoChartIntegralModel.inclFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) b₀)
  refine ⟨b', k, ?_⟩
  have hb' := congrArg (fun x : ↥(chartAlgMid ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) => (x : ↥(modularFunctionFieldFull p))) hb
  simp only [Subalgebra.coe_mul, TwoChartIntegralModel.coe_chartIncl] at hb'

  change (b₀ : ↥(modularFunctionFieldFull p)) * ((TwoChartIntegralModel.inclInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) (jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ^ k) : ↥(chartAlgMid ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : ↥(modularFunctionFieldFull p)) =
    ((TwoChartIntegralModel.inclInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) b' : ↥(chartAlgMid ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : ↥(modularFunctionFieldFull p)) at hb'
  rw [map_pow, Subalgebra.coe_pow, TwoChartIntegralModel.coe_chartIncl, TwoChartIntegralModel.coe_chartIncl,
    coe_jInvChartInf] at hb'
  have hj : ((IgusaScheme.jFull p) : ↥(modularFunctionFieldFull p)) ≠ 0 := Fact.out
  rw [← hb', mul_assoc, ← mul_pow, inv_mul_cancel₀ hj, one_pow, mul_one]

include hjp he₁jp in

theorem exists_ρ_eq_Xinv : ∃ b' : ↥(chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), ρ p 𝔭₁ e₁ he₁j b' = (RatFunc.X : RatFunc (ZMod p))⁻¹ := by
  have hX : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 := RatFunc.X_ne_zero
  have hp : 0 < p := (Fact.out : p.Prime).pos

  have ht : ρ p 𝔭₁ e₁ he₁j (jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) = (RatFunc.X ^ p)⁻¹ :=
    TensorAdapt.ρ₀'_jInv p (IgusaScheme.jFull p) 𝔭₁ e₁ p he₁j (Or.inr trivial)

  obtain ⟨a, h, hh⟩ := exists_ρ_mul_X_eq p jp hjp 𝔭₁ e₁ he₁jp he₁j

  obtain ⟨q₀, hq₀⟩ := Ideal.Quotient.mk_surjective (e₁.symm (Polynomial.X ^ (p - 1)))
  obtain ⟨b', k, hb'⟩ := exists_coe_eq_mul_pow p q₀
  have hρb' : ρ p 𝔭₁ e₁ he₁j b' * RatFunc.X ^ (p * k) = RatFunc.X ^ (p - 1) := by
    have h1 := TensorAdapt.ρ₀'_mul_pow p (IgusaScheme.jFull p) 𝔭₁ e₁ p he₁j q₀ b' k hb'
    rw [TensorAdapt.ρ₀_apply, hq₀, RingEquiv.apply_symm_apply, map_pow, Polynomial.aeval_X] at h1
    exact h1

  refine (Subring.mem_of_unit_mul_mem_of_pow_mul_mem (ρ p 𝔭₁ e₁ he₁j).range
    (y := (RatFunc.X : RatFunc (ZMod p))⁻¹) (t := (RatFunc.X ^ p)⁻¹)
    (g := ρ p 𝔭₁ e₁ he₁j a) (u := 1 + (RatFunc.X ^ p)⁻¹ * ρ p 𝔭₁ e₁ he₁j a) (k := k)
    ?_ ⟨a, rfl⟩ rfl ?_ ?_).imp fun b hb => hb
  · exact ⟨_, ht⟩
  ·
    refine ⟨h, ?_⟩
    rw [← ht, ← hh, mul_assoc, mul_inv_cancel₀ hX, mul_one]
  ·
    refine ⟨jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) * b', ?_⟩
    rw [map_mul, ht]
    have hXpk : (RatFunc.X : RatFunc (ZMod p)) ^ (p * k) ≠ 0 := pow_ne_zero _ hX

    have e1 : ρ p 𝔭₁ e₁ he₁j b' = RatFunc.X ^ (p - 1) * (RatFunc.X ^ (p * k))⁻¹ :=
      (eq_mul_inv_iff_mul_eq₀ hXpk).mpr hρb'
    rw [e1]

    have hp1 : RatFunc.X ^ p = RatFunc.X ^ (p - 1) * (RatFunc.X : RatFunc (ZMod p)) := by
      rw [← pow_succ, Nat.sub_add_cancel hp]
    rw [inv_pow, ← pow_mul, hp1, mul_inv, mul_comm (RatFunc.X ^ (p * k))⁻¹]

    field_simp

include he₁jp in

theorem mul_sub_one_mem_nonunits_of_ρ_eq_Xinv
    (W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hjW : ((IgusaScheme.jFull p) : ↥(modularFunctionFieldFull p))⁻¹ ∈ W₁)
    (h𝔭₁ : ∀ a : ↥(chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), a ∈ 𝔭₁ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits))
    (b' : ↥(chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (hb' : ρ p 𝔭₁ e₁ he₁j b' = (RatFunc.X : RatFunc (ZMod p))⁻¹) :
    (b' : ↥(modularFunctionFieldFull p)) * (jp : ↥(modularFunctionFieldFull p)) - 1 ∈ W₁.nonunits := by
  have hX : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 := RatFunc.X_ne_zero
  have hj : ((IgusaScheme.jFull p) : ↥(modularFunctionFieldFull p)) ≠ 0 := Fact.out

  letI := (TwoChartIntegralModel.inclFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
  obtain ⟨⟨c, ⟨_, ⟨n, rfl⟩⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (TwoChartIntegralModel.inclInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) b' * TwoChartIntegralModel.inclFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) jp - 1)
  change (TwoChartIntegralModel.inclInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) b' * TwoChartIntegralModel.inclFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) jp - 1) *
      TwoChartIntegralModel.inclFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) (jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ^ n) =
    TwoChartIntegralModel.inclFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) c at hc

  have hρc : TensorAdapt.ρ₀ p (IgusaScheme.jFull p) 𝔭₁ e₁ c = 0 := by
    have h := congrArg (TensorAdapt.ρ₀M p (IgusaScheme.jFull p) 𝔭₁ e₁ p he₁j) hc
    simp only [map_mul, map_sub, map_one, map_pow, TensorAdapt.ρ₀M_inclFin, ρ₀_jp p jp 𝔭₁ e₁ he₁jp] at h
    change ((ρ p 𝔭₁ e₁ he₁j b') * RatFunc.X - 1) * _ = _ at h
    rw [hb', inv_mul_cancel₀ hX, sub_self, zero_mul] at h
    exact h.symm
  have hc𝔭 : c ∈ 𝔭₁ := by
    rw [TensorAdapt.ρ₀_apply, map_eq_zero_iff _ (TensorAdapt.aeval_X_injective (ZMod p)),
      map_eq_zero_iff _ e₁.injective, Ideal.Quotient.eq_zero_iff_mem] at hρc
    exact hρc
  have hcW : (c : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits := (h𝔭₁ c).mp hc𝔭

  have hcF : ((b' : ↥(modularFunctionFieldFull p)) * (jp : ↥(modularFunctionFieldFull p)) - 1) * ((IgusaScheme.jFull p) : ↥(modularFunctionFieldFull p)) ^ n = (c : ↥(modularFunctionFieldFull p)) := by
    have h := congrArg (fun z : ↥(chartAlgMid ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) => (z : ↥(modularFunctionFieldFull p))) hc
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, map_pow, Subalgebra.coe_pow,
      TwoChartIntegralModel.coe_chartIncl, coe_jChartFin] at h
    exact h
  have hx : (b' : ↥(modularFunctionFieldFull p)) * (jp : ↥(modularFunctionFieldFull p)) - 1 = (c : ↥(modularFunctionFieldFull p)) * (((IgusaScheme.jFull p) : ↥(modularFunctionFieldFull p))⁻¹) ^ n := by
    rw [← hcF, mul_assoc, ← mul_pow, mul_inv_cancel₀ hj, one_pow, mul_one]
  rw [hx]

  have hcW' : (⟨(c : ↥(modularFunctionFieldFull p)), W₁.nonunits_subset hcW⟩ : W₁) ∈ IsLocalRing.maximalIdeal W₁ :=
    ValuationSubring.coe_mem_nonunits_iff.mp hcW
  have hprod : (⟨(c : ↥(modularFunctionFieldFull p)), W₁.nonunits_subset hcW⟩ * ⟨((IgusaScheme.jFull p) : ↥(modularFunctionFieldFull p))⁻¹, hjW⟩ ^ n : W₁) ∈
      IsLocalRing.maximalIdeal W₁ := Ideal.mul_mem_right _ _ hcW'
  exact ValuationSubring.coe_mem_nonunits_iff.mpr hprod

end Modular

theorem exists_chartAlgInf_mul_sub_one_mem_nonunits
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)
    (hne : W₀ ≠ W₁)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹
            ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull p),
        ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : ↥(modularFunctionFieldFull p)) - (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p) ∈ W₀.nonunits)
    (hres₀ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₀ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ W₀.nonunits)
    (hres₁ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₁ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) P
            ∈ W₁.nonunits)
    (𝔭₁ : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (h𝔭₁ : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
        a ∈ 𝔭₁ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits))
    (e₁ : (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⧸ 𝔭₁) ≃+* Polynomial (ZMod p))
    (he₁jp : e₁ (Ideal.Quotient.mk 𝔭₁ jp) = X)
    (he₁j : e₁ (Ideal.Quotient.mk 𝔭₁ (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = X ^ p) :
    ∃ b' : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      (b' : ↥(modularFunctionFieldFull p)) * (jp : ↥(modularFunctionFieldFull p)) - 1 ∈ W₁.nonunits := by
  obtain ⟨b', hb'⟩ := exists_ρ_eq_Xinv p jp hjp 𝔭₁ e₁ he₁jp he₁j
  have hXmap : (Polynomial.X : Polynomial ℤ).map (Int.castRingHom (ZMod p)) ≠ 0 := by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero
  have hjW : ((IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)))⁻¹ ∈ W₁ := by
    have h := (hgen 1 Polynomial.X hXmap).2
    rwa [Polynomial.eval₂_X] at h
  exact ⟨b', mul_sub_one_mem_nonunits_of_ρ_eq_Xinv p jp 𝔭₁ e₁ he₁jp he₁j W₁ hjW h𝔭₁ b' hb'⟩

end S2a

end

open ModularCurve AlgebraicCurve Polynomial

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)
    (hne : W₀ ≠ W₁)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹
            ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull p),
        ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : ↥(modularFunctionFieldFull p)) - (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p) ∈ W₀.nonunits)
    (hres₀ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₀ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ W₀.nonunits)
    (hres₁ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₁ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) P
            ∈ W₁.nonunits)
    (𝔭₁ : Ideal ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (h𝔭₁ : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
        a ∈ 𝔭₁ ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits))
    (e₁ : (↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ⧸ 𝔭₁) ≃+* Polynomial (ZMod p))
    (he₁jp : e₁ (Ideal.Quotient.mk 𝔭₁ jp) = X)
    (he₁j : e₁ (Ideal.Quotient.mk 𝔭₁ (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) = X ^ p) :
    ∃ b' : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), (b' : ↥(modularFunctionFieldFull p)) * (jp : ↥(modularFunctionFieldFull p)) - 1 ∈ W₁.nonunits :=
  S2a.exists_chartAlgInf_mul_sub_one_mem_nonunits p jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁ 𝔭₁ h𝔭₁ e₁ he₁jp he₁j

end S_ModularCurve_DRModel_exists_chartAlgInf_mul_sub_one_mem_nonunits_of_valuationSubring_pair
end P2MW
export P2MW.S_ModularCurve_DRModel_exists_chartAlgInf_mul_sub_one_mem_nonunits_of_valuationSubring_pair (solution)
