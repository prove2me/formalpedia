-- Prove2me | solution 1 for ModularCurve.periodAlong_add_petersson_mem_periodLattice_of_multiplier_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/120adf15-9314-56a9-8753-619722899679

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Theorems.Thm_ModularCurve_exists_chain_periodAlong_add_petersson_eq_zero_of_multiplier_eq_exp
import Theorems.Thm_ModularCurve_sum_periodAlong_mem_periodLattice_of_boundary_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodAlong_add_petersson_mem_periodLattice_of_multiplier_eq_exp
p2m_attr_erase "instance" "FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero"

noncomputable section

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

namespace ModularCurve
p2m_export "ModularCurve" "periodAlong period periodLattice exists_chain_periodAlong_add_petersson_eq_zero_of_multiplier_eq_exp sum_periodAlong_mem_periodLattice_of_boundary_eq_zero"
namespace PeriodExpAbelNecessity
p2m_open "ModularCurve"

variable {N : ℕ}

local notation "Γ₀" => CongruenceSubgroup.Gamma0

open Classical in

def orbInd (N : ℕ) (τ x : ℍ) : ℤ := if ∃ γ : Γ₀ N, (γ : SL(2, ℤ)) • x = τ then 1 else 0

open Classical in
theorem ite_eq_mul_orbInd (τ x : ℍ) (m : ℤ) :
    (if ∃ γ : Γ₀ N, (γ : SL(2, ℤ)) • x = τ then m else 0) = m * orbInd N τ x := by
  unfold orbInd; split_ifs <;> simp

def bdry (N : ℕ) (Z : (ℍ × ℍ) →₀ ℤ) (τ : ℍ) : ℤ :=
  Z.sum fun e m => m * orbInd N τ e.2 - m * orbInd N τ e.1

def ocount (N : ℕ) (c : ℍ →₀ ℤ) (τ : ℍ) : ℤ := c.sum fun x m => m * orbInd N τ x

open Classical in
theorem bdry_eq (Z : (ℍ × ℍ) →₀ ℤ) (τ : ℍ) :
    Z.sum (fun e m =>
      (if ∃ γ : Γ₀ N, (γ : SL(2, ℤ)) • e.2 = τ then m else 0) -
      (if ∃ γ : Γ₀ N, (γ : SL(2, ℤ)) • e.1 = τ then m else 0)) = bdry N Z τ := by
  unfold bdry
  refine Finsupp.sum_congr fun e _ => ?_
  rw [ite_eq_mul_orbInd, ite_eq_mul_orbInd]

open Classical in
theorem ocount_eq (c : ℍ →₀ ℤ) (τ : ℍ) :
    c.sum (fun x m => if ∃ γ : Γ₀ N, (γ : SL(2, ℤ)) • x = τ then m else 0) = ocount N c τ := by
  unfold ocount
  exact Finsupp.sum_congr fun x _ => ite_eq_mul_orbInd _ _ _

def cone (c : ℍ →₀ ℤ) : (ℍ × ℍ) →₀ ℤ := Finsupp.mapDomain (fun τ => (UpperHalfPlane.I, τ)) c

theorem cone_sum_periodAlong (N : ℕ) (c : ℍ →₀ ℤ) :
    ((cone c).sum fun e m => m • ModularCurve.periodAlong N e.1 e.2) =
      c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ := by
  unfold cone
  exact Finsupp.sum_mapDomain_index (h := fun (e : ℍ × ℍ) (m : ℤ) =>
    m • ModularCurve.periodAlong N e.1 e.2) (fun _ => zero_smul _ _)
    (fun _ _ _ => add_smul _ _ _)

theorem bdry_add (Z W : (ℍ × ℍ) →₀ ℤ) (τ : ℍ) : bdry N (Z + W) τ = bdry N Z τ + bdry N W τ := by
  unfold bdry
  rw [Finsupp.sum_add_index' (fun _ => by ring) (fun _ _ _ => by ring)]

theorem bdry_neg (Z : (ℍ × ℍ) →₀ ℤ) (τ : ℍ) : bdry N (-Z) τ = -bdry N Z τ := by
  unfold bdry
  rw [Finsupp.sum_neg_index (fun _ => by ring)]
  simp only [neg_mul, Finsupp.sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => by ring

theorem bdry_sub (Z W : (ℍ × ℍ) →₀ ℤ) (τ : ℍ) : bdry N (Z - W) τ = bdry N Z τ - bdry N W τ := by
  rw [sub_eq_add_neg, bdry_add, bdry_neg, ← sub_eq_add_neg]

theorem bdry_cone (c : ℍ →₀ ℤ) (τ : ℍ) :
    bdry N (cone c) τ = ocount N c τ - (c.sum fun _ m => m) * orbInd N τ UpperHalfPlane.I := by
  unfold bdry cone ocount
  rw [Finsupp.sum_mapDomain_index (fun _ => by ring) (fun _ _ _ => by ring)]
  simp only [Finsupp.sum, Finset.sum_sub_distrib, Finset.sum_mul]

theorem sum_periodAlong_sub (N : ℕ) (Z W : (ℍ × ℍ) →₀ ℤ) :
    ((Z - W).sum fun e m => m • ModularCurve.periodAlong N e.1 e.2) =
      (Z.sum fun e m => m • ModularCurve.periodAlong N e.1 e.2) -
        W.sum fun e m => m • ModularCurve.periodAlong N e.1 e.2 := by
  rw [Finsupp.sum_sub_index (fun _ _ _ => sub_smul _ _ _)]

section Reps

open Classical

def qo (N : ℕ) (x : ℍ) : Quotient (MulAction.orbitRel (Γ₀ N) ℍ) :=
  Quotient.mk (MulAction.orbitRel (Γ₀ N) ℍ) x

theorem orbInd_eq_one_iff (τ x : ℍ) : orbInd N τ x = 1 ↔ qo N τ = qo N x := by
  unfold orbInd qo
  rw [Quotient.eq]
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · intro h
    by_contra hne
    rw [if_neg] at h
    · exact zero_ne_one h
    · rintro ⟨γ, hγ⟩
      exact hne ⟨γ, hγ⟩
  · rintro ⟨γ, hγ⟩
    rw [if_pos ⟨γ, hγ⟩]

theorem orbInd_eq_ite (τ x : ℍ) : orbInd N τ x = if qo N τ = qo N x then 1 else 0 := by
  by_cases h : qo N τ = qo N x
  · rw [if_pos h]; exact (orbInd_eq_one_iff τ x).2 h
  · rw [if_neg h]
    unfold orbInd
    split_ifs with h'
    · exact absurd ((orbInd_eq_one_iff (N := N) τ x).1 (by unfold orbInd; rw [if_pos h'])) h
    · rfl

def reps (N : ℕ) (S : Finset ℍ) : Finset ℍ := (S.image (qo N)).image Quotient.out

theorem qo_out (s : Quotient (MulAction.orbitRel (Γ₀ N) ℍ)) : qo N s.out = s :=
  Quotient.out_eq s

theorem sum_reps_orbInd {S : Finset ℍ} {x : ℍ} (hx : x ∈ S) :
    ∑ r ∈ reps N S, orbInd N r x = 1 := by
  unfold reps
  rw [Finset.sum_image]
  · simp_rw [orbInd_eq_ite, qo_out]
    rw [Finset.sum_ite_eq' (S.image (qo N)) (qo N x) (fun _ => (1 : ℤ))]
    rw [if_pos (Finset.mem_image_of_mem _ hx)]
  · intro a _ b _ hab
    rw [← qo_out (N := N) a, ← qo_out (N := N) b, hab]

theorem sum_reps_ocount {S : Finset ℍ} (c : ℍ →₀ ℤ) (hS : c.support ⊆ S) :
    ∑ r ∈ reps N S, ocount N c r = c.sum fun _ m => m := by
  unfold ocount
  simp only [Finsupp.sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finset.mul_sum, sum_reps_orbInd (hS hx), mul_one]

theorem sum_reps_bdry {S : Finset ℍ} (Z : (ℍ × ℍ) →₀ ℤ)
    (h1 : Z.support.image Prod.fst ⊆ S) (h2 : Z.support.image Prod.snd ⊆ S) :
    ∑ r ∈ reps N S, bdry N Z r = 0 := by
  unfold bdry
  simp only [Finsupp.sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e he => ?_
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_reps_orbInd (h2 (Finset.mem_image_of_mem _ he)),
    sum_reps_orbInd (h1 (Finset.mem_image_of_mem _ he)), sub_self]

theorem deg_eq_zero (c : ℍ →₀ ℤ) (Z : (ℍ × ℍ) →₀ ℤ)
    (h : ∀ τ : ℍ, ocount N c τ = bdry N Z τ) : (c.sum fun _ m => m) = 0 := by
  classical
  set S : Finset ℍ := c.support ∪ (Z.support.image Prod.fst ∪ Z.support.image Prod.snd)
  rw [← sum_reps_ocount (N := N) (S := S) c Finset.subset_union_left]
  simp_rw [h]
  exact sum_reps_bdry Z (Finset.subset_union_left.trans Finset.subset_union_right)
    (Finset.subset_union_right.trans Finset.subset_union_right)

end Reps

theorem orbInd_self (τ : ℍ) : orbInd N τ τ = 1 := by
  classical
  unfold orbInd
  rw [if_pos ⟨1, by simp⟩]

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

scoped instance finite_stabilizer (τ : ℍ) :
    Finite (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) := by
  have h := finite_setOf_smul_eq τ
  have : Set.Finite ((MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ :
      Set (CongruenceSubgroup.Gamma0 N))) := by
    have hsub : (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ :
        Set (CongruenceSubgroup.Gamma0 N)) = Subtype.val ⁻¹' {g : SL(2, ℤ) | g • τ = τ} := by
      ext γ
      simp [MulAction.mem_stabilizer_iff]
      rfl
    rw [hsub]
    exact h.preimage Subtype.val_injective.injOn
  exact this.to_subtype

end ModularCurve.PeriodExpAbelNecessity
p2m_reactivate "P2MW.S_ModularCurve_periodAlong_add_petersson_mem_periodLattice_of_multiplier_eq_exp.ModularCurve P2MW.S_ModularCurve_periodAlong_add_petersson_mem_periodLattice_of_multiplier_eq_exp.ModularCurve.PeriodExpAbelNecessity"
p2m_reactivate "P2MW.S_ModularCurve_periodAlong_add_petersson_mem_periodLattice_of_multiplier_eq_exp.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_periodAlong_add_petersson_mem_periodLattice_of_multiplier_eq_exp.ModularCurve P2MW.S_ModularCurve_periodAlong_add_petersson_mem_periodLattice_of_multiplier_eq_exp.ModularCurve.PeriodExpAbelNecessity"

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

open ModularCurve.PeriodExpAbelNecessity in
open Classical in
theorem solution
    {N : ℕ} [NeZero N] (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (k : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, ∃ n : ℤ,
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
        2 * n = (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) : ℤ) *
          c.sum (fun τ' m =>
            if ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ' = τ then m else 0)) :
    ∃ Λ ∈ ModularCurve.periodLattice N, ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) g +
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 k g τ) = Λ g := by

  obtain ⟨Z, hZb, hZ⟩ :=
    ModularCurve.exists_chain_periodAlong_add_petersson_eq_zero_of_multiplier_eq_exp
      F k hF hχ hcusp

  have hcount : ∀ τ : ℍ, ocount N c τ = bdry N Z τ := by
    intro τ
    obtain ⟨n, hn, hcn⟩ := hord τ
    obtain ⟨n', hn', hZn⟩ := hZb τ
    rw [ocount_eq] at hcn
    rw [bdry_eq] at hZn
    have hnn : n = n' := by
      have := hn.symm.trans hn'
      exact_mod_cast this
    subst hnn

    have hfin : Finite (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) :=
      finite_stabilizer τ
    have hpos : (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) : ℤ) ≠ 0 := by
      have : 0 < Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) := Nat.card_pos
      exact_mod_cast this.ne'
    exact mul_left_cancel₀ hpos (hcn.symm.trans hZn)

  have hdeg : (c.sum fun _ m => m) = 0 := deg_eq_zero c Z hcount
  have hclosed : ∀ τ : ℍ, bdry N (cone c - Z) τ = 0 := by
    intro τ
    rw [bdry_sub, bdry_cone, hdeg, zero_mul, sub_zero, hcount, sub_self]
  have hmem := ModularCurve.sum_periodAlong_mem_periodLattice_of_boundary_eq_zero
    (N := N) (cone c - Z) (fun τ => by rw [bdry_eq]; exact hclosed τ)
  refine ⟨_, hmem, fun g => ?_⟩
  rw [sum_periodAlong_sub, cone_sum_periodAlong, LinearMap.sub_apply]
  have := hZ g
  linear_combination this

end S_ModularCurve_periodAlong_add_petersson_mem_periodLattice_of_multiplier_eq_exp
end P2MW
export P2MW.S_ModularCurve_periodAlong_add_petersson_mem_periodLattice_of_multiplier_eq_exp (solution)
