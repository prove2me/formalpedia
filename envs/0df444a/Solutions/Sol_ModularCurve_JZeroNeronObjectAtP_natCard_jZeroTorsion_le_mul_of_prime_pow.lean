-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.natCard_jZeroTorsion_le_mul_of_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6fc1af8f-05f2-5a7c-afc2-414e69dc4b9b

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Theorems.Thm_ValuationSubring_exists_tame_generator_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_exists_apply_eq_pow_and_apply_eq_self_of_mem_inertiaSubgroupIn_and_exists_mem_inertiaSubgroupIn_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_natCard_jZeroTorsion_le_mul_of_prime_pow
p2m_attr_erase "instance" "GaloisRep.DeformationRingData.instIsLocalHom GaloisRep.DeformationRingData.instCommRing GaloisRep.DeformationRingData.instIsLocalRing GaloisRep.DeformationRingData.instIsNoetherianRing GaloisRep.DeformationRingData.instIsAdicComplete GaloisRep.DeformationRingData.instAlgebra"
p2m_attr_erase "simp" "GaloisRep.DeformationRingData.mk.injEq GaloisRep.DeformationRingData.mk.sizeOf_spec"

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

namespace BridgeMonoF3b

theorem card_le_of_generator {G V : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]
    (I : Subgroup G) (J T Jinv : AddSubgroup V) (n : ℕ)
    (hT : ∀ σ ∈ I, ∀ y ∈ T, σ • y = y)
    (hdisp : ∀ σ ∈ I, ∀ x ∈ J, σ • x - x ∈ T)
    (hstab : ∀ σ ∈ I, ∀ x ∈ J, σ • x ∈ J)
    (htors : ∀ x ∈ J, n • x = 0)
    (hJinv : ∀ x : V, (∀ τ ∈ I, τ • x = x) → x ∈ Jinv)
    (γ : G) (hγ : γ ∈ I)
    (hgen : ∀ τ ∈ I, ∃ (j : ℕ) (y w : G), y ∈ I ∧ w ∈ I ∧ τ = γ ^ j * y ^ n * w ^ n) :
    Nat.card ↥J ≤
      Nat.card ↥(AddSubgroup.closure {y : V | ∃ σ ∈ I, ∃ x ∈ J, y = σ • x - x}) * Nat.card ↥(J ⊓ Jinv) := by
  classical

  have hmul : ∀ x ∈ J, ∀ σ ∈ I, ∀ τ ∈ I, (σ * τ) • x - x = (σ • x - x) + (τ • x - x) := by
    intro x hx σ hσ τ hτ
    have h1 : σ • (τ • x - x) = τ • x - x := hT σ hσ _ (hdisp τ hτ x hx)
    rw [smul_sub] at h1
    rw [mul_smul]
    calc σ • τ • x - x = (σ • τ • x - σ • x) + (σ • x - x) := by abel
      _ = (τ • x - x) + (σ • x - x) := by rw [h1]
      _ = (σ • x - x) + (τ • x - x) := add_comm _ _
  have hpow : ∀ x ∈ J, ∀ σ ∈ I, ∀ j : ℕ, σ ^ j • x - x = j • (σ • x - x) := by
    intro x hx σ hσ j
    induction j with
    | zero => rw [pow_zero, one_smul, sub_self, zero_nsmul]
    | succ j ih => rw [pow_succ, hmul x hx _ (I.pow_mem hσ j) σ hσ, ih, add_nsmul, one_nsmul]
  have hkill : ∀ x ∈ J, ∀ σ ∈ I, σ ^ n • x - x = 0 := by
    intro x hx σ hσ
    rw [hpow x hx σ hσ n]
    exact htors _ (J.sub_mem (hstab σ hσ x hx) hx)

  have hker : ∀ x ∈ J, γ • x = x → ∀ τ ∈ I, τ • x = x := by
    intro x hx hγx τ hτ
    obtain ⟨j, y, w, hy, hw, hτeq⟩ := hgen τ hτ
    have hIγ : γ ^ j ∈ I := I.pow_mem hγ j
    have hIy : y ^ n ∈ I := I.pow_mem hy n
    have hIw : w ^ n ∈ I := I.pow_mem hw n
    have e1 : τ • x - x = 0 := by
      rw [hτeq, hmul x hx _ (I.mul_mem hIγ hIy) _ hIw, hmul x hx _ hIγ _ hIy,
        hkill x hx y hy, hkill x hx w hw, hpow x hx γ hγ j, hγx, sub_self, nsmul_zero, add_zero, add_zero]
    exact sub_eq_zero.mp e1

  obtain ⟨f, hf⟩ : ∃ f : ↥J →+ V, ∀ x, f x = γ • (x : V) - x :=
    ⟨AddMonoidHom.mk' (fun x => γ • (x : V) - x) (fun x y => by
      show γ • ((x + y : ↥J) : V) - (x + y : ↥J) = (γ • (x : V) - x) + (γ • (y : V) - y)
      rw [AddSubgroup.coe_add, smul_add]
      exact (sub_add_sub_comm _ _ _ _).symm), fun _ => rfl⟩

  by_cases hfin : Finite ↥J
  swap
  · calc Nat.card ↥J = 0 := @Nat.card_eq_zero_of_infinite _ (not_finite_iff_infinite.mp hfin)
      _ ≤ _ := Nat.zero_le _

  have e1 : Nat.card ↥J = Nat.card (↥J ⧸ f.ker) * Nat.card ↥f.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  have e2 : Nat.card (↥J ⧸ f.ker) = Nat.card ↥f.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv

  have hrangeS : f.range ≤ AddSubgroup.closure {y : V | ∃ σ ∈ I, ∃ x ∈ J, y = σ • x - x} := by
    intro y hy
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hy
    have hy' : y = γ • (x : V) - x := hx.symm.trans (hf x)
    rw [hy']
    exact AddSubgroup.subset_closure ⟨γ, hγ, x, x.2, rfl⟩
  have hSJ : AddSubgroup.closure {y : V | ∃ σ ∈ I, ∃ x ∈ J, y = σ • x - x} ≤ J := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨σ, hσ, x, hx, rfl⟩
    exact J.sub_mem (hstab σ hσ x hx) hx
  haveI hSfin : Finite ↥(AddSubgroup.closure {y : V | ∃ σ ∈ I, ∃ x ∈ J, y = σ • x - x}) :=
    Finite.of_injective _ (AddSubgroup.inclusion_injective hSJ)
  haveI hHfin : Finite ↥(J ⊓ Jinv) :=
    Finite.of_injective _ (AddSubgroup.inclusion_injective (inf_le_left : J ⊓ Jinv ≤ J))
  have h1 : Nat.card ↥f.range ≤ Nat.card ↥(AddSubgroup.closure {y : V | ∃ σ ∈ I, ∃ x ∈ J, y = σ • x - x}) :=
    Nat.card_le_card_of_injective _ (AddSubgroup.inclusion_injective hrangeS)

  have hkermem : ∀ x : ↥J, x ∈ f.ker → (x : V) ∈ J ⊓ Jinv := by
    intro x hx
    rw [AddMonoidHom.mem_ker, hf, sub_eq_zero] at hx
    exact AddSubgroup.mem_inf.mpr ⟨x.2, hJinv x (hker x x.2 hx)⟩
  have h2 : Nat.card ↥f.ker ≤ Nat.card ↥(J ⊓ Jinv) := by
    refine Nat.card_le_card_of_injective (fun x => (⟨((x : ↥J) : V), hkermem x x.2⟩ : ↥(J ⊓ Jinv))) ?_
    intro a b h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  have h12 : Nat.card ↥f.range * Nat.card ↥f.ker ≤
      Nat.card ↥(AddSubgroup.closure {y : V | ∃ σ ∈ I, ∃ x ∈ J, y = σ • x - x}) * Nat.card ↥(J ⊓ Jinv) :=
    Nat.mul_le_mul h1 h2
  calc Nat.card ↥J = Nat.card (↥J ⧸ f.ker) * Nat.card ↥f.ker := e1
    _ = Nat.card ↥f.range * Nat.card ↥f.ker := congrArg (fun t => t * Nat.card ↥f.ker) e2
    _ ≤ _ := h12

end BridgeMonoF3b

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (ℓ k : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (hdisp : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) (ℓ ^ k), σ • x - x ∈ O.toricPts (ℓ ^ k)) :
    Nat.card ↥(jZeroTorsion (N₀ * p) (ℓ ^ k)) ≤
      Nat.card ↥(AddSubgroup.closure {y : JZero (N₀ * p) | ∃ σ ∈ A.inertiaSubgroupIn ℚ,
          ∃ x ∈ jZeroTorsion (N₀ * p) (ℓ ^ k), y = σ • x - x}) *
        Nat.card ↥(jZeroTorsion (N₀ * p) (ℓ ^ k) ⊓ inertiaInvariants A (N₀ * p)) := by
  have hp : p.Prime := Fact.out
  have hn0 : 0 < ℓ ^ k := pow_pos hℓ.pos k
  have hpn : ¬ p ∣ ℓ ^ k := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h)).symm

  have hmemJ : ∀ x : JZero (N₀ * p), x ∈ jZeroTorsion (N₀ * p) (ℓ ^ k) ↔ ((ℓ ^ k : ℕ) : ℤ) • x = 0 := fun x =>
    Submodule.mem_torsionBy_iff _ _

  have hroots : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ (ℓ ^ k) = 1 → σ μ = μ := by
    intro σ hσ
    obtain ⟨_, _, h⟩ :=
      (ValuationSubring.exists_apply_eq_pow_and_apply_eq_self_of_mem_inertiaSubgroupIn_and_exists_mem_inertiaSubgroupIn_of_not_dvd
        p hp 0 (ℓ ^ k) hpn A hA).1 σ hσ
    exact h

  have hfixT : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ y ∈ O.toricPts (ℓ ^ k), σ • y = y := by
    intro σ hσ y hy
    rw [toricPts, dif_pos hn0] at hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨χ, rfl⟩ := hz
      have h1 := O.toricLift_inertia (ℓ ^ k) hn0 σ hσ 1
        (fun ζ hζ => by rw [pow_one]; exact hroots σ hσ ζ hζ) χ
      simpa only [toricPoint, one_smul] using h1
    | zero => exact smul_zero (A := JZero (N₀ * p)) σ
    | add a b _ _ ha hb => rw [smul_add, ha, hb]
    | neg a _ ha => rw [smul_neg, ha]

  have hstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) (ℓ ^ k),
      σ • x ∈ jZeroTorsion (N₀ * p) (ℓ ^ k) := by
    intro σ _ x hx
    rw [hmemJ] at hx ⊢
    rw [smul_comm (((ℓ ^ k : ℕ) : ℤ)) σ x, hx, smul_zero]
  have htors : ∀ x ∈ jZeroTorsion (N₀ * p) (ℓ ^ k), (ℓ ^ k) • x = 0 := by
    intro x hx
    rw [← natCast_zsmul]
    exact (hmemJ x).mp hx

  obtain ⟨γ, hγ, hgen⟩ :=
    ValuationSubring.exists_tame_generator_inertiaSubgroupIn (p := ℓ) (q := p) hℓ hp hℓp A hA k
  exact BridgeMonoF3b.card_le_of_generator (A.inertiaSubgroupIn ℚ) (jZeroTorsion (N₀ * p) (ℓ ^ k))
    (O.toricPts (ℓ ^ k)) (inertiaInvariants A (N₀ * p)) (ℓ ^ k) hfixT hdisp hstab htors
    (fun x h => ModularCurve.mem_inertiaInvariants.mpr h) γ hγ hgen

end S_ModularCurve_JZeroNeronObjectAtP_natCard_jZeroTorsion_le_mul_of_prime_pow
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_natCard_jZeroTorsion_le_mul_of_prime_pow (solution)
