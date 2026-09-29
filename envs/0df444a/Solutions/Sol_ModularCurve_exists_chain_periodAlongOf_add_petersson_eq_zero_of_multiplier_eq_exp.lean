-- Prove2me | solution 1 for ModularCurve.exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/53bf2366-d866-5d60-9aa9-5e8a3c7e9121

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Theorems.Thm_ModularCurve_exists_meromorphicOrderAt_eq_coe_of_tendsto_atImInfty
import Theorems.Thm_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf
import Theorems.Thm_ModularCurve_exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex
import Theorems.Thm_ModularCurve_sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp_periodOf
import Theorems.Thm_ModularCurve_exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_exp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp
p2m_attr_erase "instance" "FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero"

set_option autoImplicit false

open UpperHalfPlane MeasureTheory Filter Topology
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "periodAlongOf periodOf period exists_meromorphicOrderAt_eq_coe_of_tendsto_atImInfty meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp_periodOf exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_exp"
namespace ChainReciprocityAssemblyOf
p2m_open "ModularCurve"

theorem finite_setOf_smul_eq (τ : ℍ) : {g : SL(2, ℤ) | g • τ = τ}.Finite := by
  have h := ProperlyDiscontinuousSMul.finite_stabilizer' (↥𝒮ℒ) τ
  let φ : SL(2, ℤ) → ↥𝒮ℒ := (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
  have hφ : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    simpa [φ] using this
  have hset : {g : SL(2, ℤ) | g • τ = τ} = φ ⁻¹' {s : ↥𝒮ℒ | s • τ = τ} := by
    ext g
    rfl
  rw [hset]
  exact h.preimage hφ.injOn

variable {Γ : Subgroup SL(2, ℤ)}

scoped instance finite_stabilizer (τ : ℍ) :
    Finite (MulAction.stabilizer (Γ) τ) := by
  have h := finite_setOf_smul_eq τ
  have : Set.Finite ((MulAction.stabilizer (Γ) τ :
      Set (Γ))) := by
    have hsub : (MulAction.stabilizer (Γ) τ :
        Set (Γ)) = Subtype.val ⁻¹' {g : SL(2, ℤ) | g • τ = τ} := by
      ext γ
      simp [MulAction.mem_stabilizer_iff]
      rfl
    rw [hsub]
    exact h.preimage Subtype.val_injective.injOn
  exact this.to_subtype

theorem card_stabilizer_pos (τ : ℍ) :
    0 < Nat.card (MulAction.stabilizer (Γ) τ) :=
  Nat.card_pos

theorem card_stabilizer_smul (γ : Γ) (τ : ℍ) :
    Nat.card (MulAction.stabilizer (Γ) ((γ : SL(2, ℤ)) • τ)) =
      Nat.card (MulAction.stabilizer (Γ) τ) := by
  have h : ((γ : SL(2, ℤ)) • τ) = γ • τ := rfl
  rw [h, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Nat.card_congr
    ((MulAction.stabilizer (Γ) τ).equivMapOfInjective
      (MulEquiv.toMonoidHom (MulAut.conj γ)) (MulAut.conj γ).injective).toEquiv.symm

def Rel (Γ : Subgroup SL(2, ℤ)) (a τ : ℍ) : Prop :=
  ∃ γ : Γ, (γ : SL(2, ℤ)) • a = τ

theorem rel_smul_left_iff (γ₀ : Γ) (a τ : ℍ) :
    Rel Γ ((γ₀ : SL(2, ℤ)) • a) τ ↔ Rel Γ a τ := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ * γ₀, ?_⟩
    rw [← hγ, Subgroup.coe_mul, mul_smul]
  · rintro ⟨γ, hγ⟩
    refine ⟨γ * γ₀⁻¹, ?_⟩
    rw [← hγ, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_smul]

theorem rel_trans_symm {a b τ : ℍ} (ha : Rel Γ a τ) (hb : Rel Γ b τ) : Rel Γ a b := by
  obtain ⟨γ, hγ⟩ := ha
  obtain ⟨δ, hδ⟩ := hb
  refine ⟨δ⁻¹ * γ, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hγ, ← hδ, inv_smul_smul]

section SumLemmas

variable {A : Type*} [AddCommGroup A]

theorem sum_chain (S : Finset ℍ) (m : ℍ → ℤ) (c : Γ →₀ ℤ)
    (φ : ℍ × ℍ → ℤ → A) (h0 : ∀ e, φ e 0 = 0) (hadd : ∀ e a b, φ e (a + b) = φ e a + φ e b) :
    ((∑ s ∈ S, Finsupp.single (UpperHalfPlane.I, s) (m s)) +
        c.sum (fun γ a => Finsupp.single (UpperHalfPlane.I, (γ : SL(2, ℤ)) • UpperHalfPlane.I) a)).sum φ
      = ∑ s ∈ S, φ (UpperHalfPlane.I, s) (m s) +
        c.sum (fun γ a => φ (UpperHalfPlane.I, (γ : SL(2, ℤ)) • UpperHalfPlane.I) a) := by
  rw [Finsupp.sum_add_index' (fun e => h0 e) (fun e a b => hadd e a b)]
  congr 1
  · rw [← Finsupp.sum_finsetSum_index (fun e => h0 e) (fun e a b => hadd e a b)]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact Finsupp.sum_single_index (h0 _)
  · rw [Finsupp.sum_sum_index (fun e => h0 e) (fun e a b => hadd e a b)]
    refine Finsupp.sum_congr fun γ _ => ?_
    exact Finsupp.sum_single_index (h0 _)

end SumLemmas

section Boundary

open Classical in
theorem sum_ite_rel_eq_of_rel (S : Finset ℍ) (m : ℍ → ℤ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    {s₀ : ℍ} (hs₀ : s₀ ∈ S) {τ : ℍ} (hτ : Rel Γ s₀ τ) :
    (∑ s ∈ S, if ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ then m s else 0)
      = m s₀ := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have : S.filter (fun s => ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ) = {s₀} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hs, hrel⟩
      exact hinj s hs s₀ hs₀ (rel_trans_symm hrel hτ)
    · rintro rfl
      exact ⟨hs₀, hτ⟩
  rw [this, Finset.sum_singleton]

open Classical in
theorem sum_ite_rel_eq_zero (S : Finset ℍ) (m : ℍ → ℤ) {τ : ℍ}
    (hτ : ∀ s ∈ S, ¬ ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ) :
    (∑ s ∈ S, if ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ then m s else 0)
      = 0 := by
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [if_neg (hτ s hs)]

end Boundary

open Classical in
theorem main [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ Z : (ℍ × ℍ) →₀ ℤ,
      (∀ τ : ℍ, ∃ n : ℤ,
        meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
          2 * n = (Nat.card (MulAction.stabilizer (Γ) τ) : ℤ) *
            Z.sum (fun e m =>
              (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.2 = τ then m else 0) -
              (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.1 = τ then m else 0))) ∧
      ∀ g : CuspForm (Γ) 2,
        (Z.sum fun e m => m • ModularCurve.periodAlongOf Γ e.1 e.2) g +
          Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
            (Γ), UpperHalfPlane.petersson 2 k g τ) = 0 := by

  choose n hn using
    ModularCurve.exists_meromorphicOrderAt_eq_coe_of_tendsto_atImInfty F hF hcusp
  obtain ⟨hinv, hdvd⟩ :=
    ModularCurve.meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf
      Γ hneg F k hF hχ
  obtain ⟨S, hinj, hcov⟩ :=
    ModularCurve.exists_finset_orbitReps_of_meromorphicOrderAt_ne_zero_of_finiteIndex Γ F k hF hχ hcusp
  have hdeg := ModularCurve.sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp_periodOf
    Γ hneg F k hF hχ hcusp S n (fun s _ => hn s) hinj hcov
  obtain ⟨Λ, hΛ, hrec⟩ :=
    ModularCurve.exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_exp
      Γ hneg F k hF hχ hcusp S n (fun s _ => hn s) hinj hcov

  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hΛ
  have hcp : (c.sum fun γ a => a • ModularCurve.periodAlongOf Γ UpperHalfPlane.I
      ((γ : SL(2, ℤ)) • UpperHalfPlane.I)) = Λ := hc

  have hcard : ∀ τ : ℍ,
      (Nat.card (MulAction.stabilizer (Γ) τ) : ℂ) ≠ 0 := fun τ => by
    exact_mod_cast (card_stabilizer_pos τ).ne'
  obtain ⟨m, hm⟩ : ∃ m : ℍ → ℤ, ∀ s,
      (Nat.card (MulAction.stabilizer (Γ) s) : ℤ) * m s = 2 * n s :=
    ⟨fun s => 2 * n s / (Nat.card (MulAction.stabilizer (Γ) s) : ℤ),
      fun s => Int.mul_ediv_cancel' (hdvd s (n s) (hn s))⟩
  have hm_cast : ∀ s, (m s : ℂ) = 2 * (n s : ℂ) /
      (Nat.card (MulAction.stabilizer (Γ) s) : ℂ) := fun s => by
    rw [eq_div_iff (hcard s)]
    have := congrArg (fun z : ℤ => (z : ℂ)) (hm s)
    push_cast at this
    linear_combination this
  have hsum_m : ∑ s ∈ S, m s = 0 := by
    have h : ((∑ s ∈ S, m s : ℤ) : ℂ) = 2 * ∑ s ∈ S, (n s : ℂ) /
        (Nat.card (MulAction.stabilizer (Γ) s) : ℂ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hm_cast s]
      ring
    rw [hdeg, mul_zero] at h
    exact_mod_cast h

  refine ⟨(∑ s ∈ S, Finsupp.single (UpperHalfPlane.I, s) (m s)) +
      c.sum (fun γ a => Finsupp.single (UpperHalfPlane.I, (γ : SL(2, ℤ)) • UpperHalfPlane.I) a),
    fun τ => ⟨n τ, hn τ, ?_⟩, fun g => ?_⟩
  ·
    rw [sum_chain S m c _ (fun e => by simp) (fun e a b => by split_ifs <;> ring)]
    dsimp only
    have hc0 : (c.sum fun γ a =>
        ((if ∃ γ' : Γ,
            (γ' : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • UpperHalfPlane.I) = τ then a else 0) -
         (if ∃ γ' : Γ,
            (γ' : SL(2, ℤ)) • UpperHalfPlane.I = τ then a else 0))) = 0 := by
      simp only [Finsupp.sum]
      refine Finset.sum_eq_zero fun γ _ => ?_
      have hPQ : (∃ γ' : Γ,
            (γ' : SL(2, ℤ)) • ((γ : SL(2, ℤ)) • UpperHalfPlane.I) = τ) ↔
          ∃ γ' : Γ, (γ' : SL(2, ℤ)) • UpperHalfPlane.I = τ :=
        rel_smul_left_iff γ UpperHalfPlane.I τ
      by_cases hI : ∃ γ' : Γ, (γ' : SL(2, ℤ)) • UpperHalfPlane.I = τ
      · rw [if_pos (hPQ.mpr hI), if_pos hI, sub_self]
      · rw [if_neg (mt hPQ.mp hI), if_neg hI, sub_self]
    have hIsum : (∑ s ∈ S, if ∃ γ' : Γ,
        (γ' : SL(2, ℤ)) • UpperHalfPlane.I = τ then m s else 0) = 0 := by
      by_cases hI : ∃ γ' : Γ, (γ' : SL(2, ℤ)) • UpperHalfPlane.I = τ
      · simp only [if_pos hI]
        exact hsum_m
      · simp only [if_neg hI, Finset.sum_const_zero]
    rw [hc0, add_zero, Finset.sum_sub_distrib, hIsum, sub_zero]
    by_cases hτS : ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ
    · obtain ⟨s₀, hs₀, hrel⟩ := hτS
      rw [sum_ite_rel_eq_of_rel S m hinj hs₀ hrel]
      obtain ⟨γ, rfl⟩ := hrel
      have h := hinv γ s₀
      rw [hn, hn] at h
      rw [WithTop.coe_inj.mp h, card_stabilizer_smul γ s₀, hm s₀]
    · have hτ0 : ∀ s ∈ S, ¬ ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ :=
        fun s hs h => hτS ⟨s, hs, h⟩
      have h0 : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = 0 := by
        by_contra h
        exact hτS (hcov τ h)
      rw [hn τ] at h0
      rw [sum_ite_rel_eq_zero S m hτ0, WithTop.coe_eq_zero.mp h0, mul_zero, mul_zero]
  ·
    rw [sum_chain S m c _ (fun e => by simp) (fun e a b => by rw [add_smul])]
    dsimp only
    have hS : (∑ s ∈ S, m s • ModularCurve.periodAlongOf Γ UpperHalfPlane.I s) g =
        ∑ s ∈ S, (2 * (n s : ℂ) /
          (Nat.card (MulAction.stabilizer (Γ) s) : ℂ)) *
            ModularCurve.periodAlongOf Γ UpperHalfPlane.I s g := by
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [LinearMap.smul_apply, zsmul_eq_mul, hm_cast]
    rw [hcp, LinearMap.add_apply, hS]
    linear_combination hrec g

end ModularCurve.ChainReciprocityAssemblyOf
p2m_reactivate "P2MW.S_ModularCurve_exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp.ModularCurve P2MW.S_ModularCurve_exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp.ModularCurve.ChainReciprocityAssemblyOf"
p2m_reactivate "P2MW.S_ModularCurve_exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp.ModularCurve"

open Classical in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ Z : (ℍ × ℍ) →₀ ℤ,
      (∀ τ : ℍ, ∃ n : ℤ,
        meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
          2 * n = (Nat.card (MulAction.stabilizer (Γ) τ) : ℤ) *
            Z.sum (fun e m =>
              (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.2 = τ then m else 0) -
              (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.1 = τ then m else 0))) ∧
      ∀ g : CuspForm (Γ) 2,
        (Z.sum fun e m => m • ModularCurve.periodAlongOf Γ e.1 e.2) g +
          Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
            (Γ), UpperHalfPlane.petersson 2 k g τ) = 0 :=
  ModularCurve.ChainReciprocityAssemblyOf.main hneg F k hF hχ hcusp

end S_ModularCurve_exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp
end P2MW
export P2MW.S_ModularCurve_exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp (solution)
