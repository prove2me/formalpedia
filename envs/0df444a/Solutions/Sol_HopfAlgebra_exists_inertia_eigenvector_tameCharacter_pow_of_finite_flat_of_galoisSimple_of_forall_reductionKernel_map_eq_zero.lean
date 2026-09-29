-- Prove2me | solution 1 for HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple_of_forall_reductionKernel_map_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0d958dca-8ba8-5519-b600-2f935c2f34e3

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Theorems.Thm_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple_of_forall_reductionKernel_map_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 4800000

open GaloisRep in
theorem solution
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (N : Type) [AddCommGroup N] [Module (IsLocalRing.ResidueField P) N]
    (act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N →ₗ[IsLocalRing.ResidueField P] N)
    (F : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N)
    (hFmul : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      F (f * g) = F f + F g)
    (hFequiv : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → F g = act σ (F f))
    (hFne : ∃ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), F f ≠ 0)
    (hSimple : ∀ S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ f ∈ S,
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (hFker : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      (∀ h : H, P.valuation (f h -
        algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) →
      F f = 0) :
    ∃ s : ℕ, 1 ≤ s ∧ ∀ π' : AlgebraicClosure ℚ, π' ^ (p ^ s - 1) = p →
      ∃ D : Finset ℕ, (∀ j ∈ D, j < s) ∧ ∃ w : N, w ≠ 0 ∧
        ∀ σ ∈ P.inertiaSubgroupIn ℚ,
          act σ w = P.tameCharacter π' σ ^ (∑ j ∈ D, p ^ j) • w := by
  haveI hpF : Fact p.Prime := ⟨hp⟩
  obtain ⟨f₀, hf₀⟩ := hFne
  refine ⟨1, le_refl 1, fun π' _ => ⟨∅, fun j hj => absurd hj (Finset.notMem_empty j),
    F f₀, hf₀, ?_⟩⟩
  intro σ hσ
  rw [Finset.sum_empty, pow_zero, one_smul]
  have hσ0 := hσ

  have hZpP : ∀ r : ratLocalizedAt p, (↑↑r : AlgebraicClosure ℚ) ∈ P := by
    intro r
    rw [show (↑↑r : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) (↑r : ℚ) from rfl]
    rw [ValuationSubring.algebraMap_rat_mem_iff_of_liesOverPrime P hP,
       Valuation.mem_valuationSubring_iff]
    unfold Rat.padicValuation
    simp only [Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    split
    · exact zero_le_one
    · have hden : padicValNat p (↑r:ℚ).den = 0 :=
        padicValNat.eq_zero_of_not_dvd fun hd =>
          absurd r.2 (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hd, dvd_refl p⟩)
      have hvr : 0 ≤ padicValRat p (↑r:ℚ) := by
        rw [padicValRat, hden, Nat.cast_zero, sub_zero]; exact Int.natCast_nonneg _
      calc WithZero.exp (-padicValRat p ↑r)
          ≤ WithZero.exp 0 := WithZero.exp_le_exp.mpr (neg_nonpos_of_nonneg hvr)
        _ = 1 := WithZero.exp_zero
  let ψ : ratLocalizedAt p →+* ↥P := {
    toFun := fun r => ⟨↑↑r, hZpP r⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := fun a b => Subtype.ext (by push_cast; ring)
    map_zero' := Subtype.ext (by simp)
    map_add' := fun a b => Subtype.ext (by push_cast; ring) }
  have hψcomp : (algebraMap ↥P (AlgebraicClosure ℚ)).comp ψ
      = algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) := by ext r; rfl
  have hIntP : ∀ x : AlgebraicClosure ℚ, IsIntegral (ratLocalizedAt p) x → x ∈ P := by
    intro x ⟨q, hqm, hqe⟩
    have hxP : IsIntegral (↥P) x := ⟨q.map ψ, hqm.map ψ, by
      rw [Polynomial.eval₂_map, hψcomp]; exact hqe⟩
    obtain ⟨⟨y, hy⟩, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxP
    exact hy
  have hfP : ∀ (f : WithConv (H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ)) (h : H),
      f.ofConv h ∈ P := fun f h =>
    hIntP _ (((Algebra.IsIntegral.of_finite (ratLocalizedAt p) H).isIntegral h).map f.ofConv)

  unfold ValuationSubring.inertiaSubgroupIn at hσ
  obtain ⟨σ', hσ'mem, hσ'eq⟩ := Subgroup.mem_map.mp hσ
  have hker : MulSemiringAction.toRingAut _ (IsLocalRing.ResidueField ↥P) σ' = 1 :=
    MonoidHom.mem_ker.mp hσ'mem
  have hfix : ∀ y : IsLocalRing.ResidueField ↥P, σ' • y = y := fun y => by
    simpa [MulSemiringAction.toRingAut_apply] using RingEquiv.congr_fun hker y
  have hmove : ∀ x : AlgebraicClosure ℚ, x ∈ P → P.valuation (σ x - x) < 1 := by
    intro x hx
    have hcoe : σ x - x = ((σ' • (⟨x, hx⟩ : ↥P) - ⟨x, hx⟩ : ↥P) : AlgebraicClosure ℚ) := by
      rw [← hσ'eq]; rfl
    rw [hcoe]
    apply (ValuationSubring.valuation_lt_one_iff P _).mp
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, sub_eq_zero]
    have hres : IsLocalRing.residue ↥P (σ' • (⟨x, hx⟩ : ↥P))
        = σ' • IsLocalRing.residue ↥P ⟨x, hx⟩ := rfl
    rw [hres, hfix]

  obtain ⟨g, hg⟩ : ∃ g : WithConv (H →ₐ[ratLocalizedAt p] AlgebraicClosure ℚ),
      ∀ h : H, g h = σ (f₀ h) :=
    ⟨WithConv.toConv ((σ.toAlgHom.restrictScalars (ratLocalizedAt p)).comp f₀.ofConv),
      fun h => by first | rfl | simp [WithConv.ofConv_toConv]⟩
  have hFg : F g = act σ (F f₀) := hFequiv σ hσ0 f₀ g hg

  have hu : f₀ ^ (p - 1) * f₀ = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hp.one_le, hMp]
  have hfu : f₀ * f₀ ^ (p - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le, hMp]
  have hK : ∀ h : H, P.valuation ((g * f₀ ^ (p - 1)).ofConv h -
      algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1 := by
    intro h
    have h1 : (f₀ * f₀ ^ (p - 1)).ofConv h
        = algebraMap (ratLocalizedAt p) (AlgebraicClosure ℚ) (Coalgebra.counit h) := by
      rw [hfu, AlgHom.convOne_apply]
    rw [← h1, AlgHom.convMul_apply, AlgHom.convMul_apply]
    generalize (Coalgebra.comul (R := ratLocalizedAt p) h) = z
    induction z with
    | zero => simpa using hmove 0 (zero_mem P)
    | add x y hx hy =>
        rw [map_add, map_add, add_sub_add_comm]
        exact Valuation.map_add_lt _ hx hy
    | tmul a b =>
        simp only [Algebra.TensorProduct.lift_tmul]
        rw [hg a, ← sub_mul, map_mul]
        refine lt_of_le_of_lt (mul_le_mul_right
          ((ValuationSubring.valuation_le_one_iff P _).mpr (hfP (f₀ ^ (p - 1)) b)) _) ?_
        rw [mul_one]
        exact hmove _ (hfP f₀ a)
  have hFgu : F (g * f₀ ^ (p - 1)) = 0 := hFker _ hK

  have hgk : g = g * f₀ ^ (p - 1) * f₀ := by rw [mul_assoc, hu, mul_one]
  have hFgf : F g = F f₀ := by rw [hgk, hFmul, hFgu, zero_add]
  rw [← hFg, hFgf]

end S_HopfAlgebra_exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple_of_forall_reductionKernel_map_eq_zero
end P2MW
export P2MW.S_HopfAlgebra_exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple_of_forall_reductionKernel_map_eq_zero (solution)
