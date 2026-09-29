-- Prove2me | solution 1 for IharaLemma.map_codRestrict_eq_of_residual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a92304d3-b6bc-59ba-8ed6-eaa040a21321

import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.FreeModule.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaLemma_map_codRestrict_eq_of_residual

set_option autoImplicit false

namespace IharaLemmaSol

variable {R : Type} [CommRing R]

private def Saturated {M : Type} [AddCommGroup M] [Module R M] (P : Submodule R M) : Prop :=
  ∀ (c : R) (x : M), c ≠ 0 → c • x ∈ P → x ∈ P

private theorem Saturated.eq_of_le_of_finrank_le [IsDomain R]
    {M : Type} [AddCommGroup M] [Module R M] [IsNoetherian R M]
    {P Q : Submodule R M} (hPQ : P ≤ Q) (hP : Saturated P)
    (hrank : Module.finrank R Q ≤ Module.finrank R P) : P = Q := by
  refine le_antisymm hPQ ?_
  intro q hq
  set P' : Submodule R Q := Submodule.comap Q.subtype P with hP'
  have hfin : Module.finrank R P' = Module.finrank R P :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hPQ)
  have hrn := Submodule.finrank_quotient_add_finrank P'
  have hzero : Module.finrank R (Q ⧸ P') = 0 := by omega
  have htors : Module.IsTorsion R (Q ⧸ P') :=
    (Module.finrank_eq_zero_iff_isTorsion).mp hzero
  obtain ⟨⟨a, ha⟩, hax⟩ := @htors (Submodule.Quotient.mk ⟨q, hq⟩)
  have ha0 : (a : R) ≠ 0 := nonZeroDivisors.ne_zero ha
  have hax' : (Submodule.Quotient.mk (p := P') (a • (⟨q, hq⟩ : Q))) = 0 := by
    rw [Submodule.Quotient.mk_smul]
    exact hax
  have hmem : a • (⟨q, hq⟩ : Q) ∈ P' := (Submodule.Quotient.mk_eq_zero P').mp hax'
  have hmem' : a • q ∈ P := by
    simpa [hP', Submodule.mem_comap] using hmem
  exact hP a q ha0 hmem'

private theorem saturated_range_of_residual [IsDomain R] [IsDiscreteValuationRing R]
    {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [Module.IsTorsionFree R M']
    (i : M →ₗ[R] M') {ϖ : R} (hϖ : Irreducible ϖ)
    (hres : ∀ (m : M) (x' : M'), i m = ϖ • x' → ∃ m₁ : M, m = ϖ • m₁) :
    Saturated (LinearMap.range i) := by
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hstep : ∀ x' : M', ϖ • x' ∈ LinearMap.range i → x' ∈ LinearMap.range i := by
    intro x' hx
    obtain ⟨m, hm⟩ := hx
    obtain ⟨m₁, rfl⟩ := hres m x' hm
    refine ⟨m₁, ?_⟩
    have h : ϖ • (i m₁ - x') = 0 := by
      rw [smul_sub, ← map_smul, hm, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_left hϖ0)
  have hpow : ∀ (n : ℕ) (x' : M'), ϖ ^ n • x' ∈ LinearMap.range i → x' ∈ LinearMap.range i := by
    intro n
    induction n with
    | zero => intro x' hx; simpa using hx
    | succ n ih =>
      intro x' hx
      apply ih
      apply hstep
      rw [← mul_smul, ← pow_succ']
      exact hx
  intro c x' hc hcx
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  apply hpow n x'
  have : ϖ ^ n • x' = ((u⁻¹ : Rˣ) : R) • (((u : R) * ϖ ^ n) • x') := by
    rw [← mul_smul, ← mul_assoc, Units.inv_mul, one_mul]
  rw [this]
  exact Submodule.smul_mem _ _ hcx

private theorem Saturated.map {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] {i : M →ₗ[R] M'} (hi : Function.Injective i)
    (hrange : Saturated (LinearMap.range i)) {A : Submodule R M} (hA : Saturated A) :
    Saturated (Submodule.map i A) := by
  intro c x' hc hcx
  have hx'range : x' ∈ LinearMap.range i := by
    apply hrange c x' hc
    exact LinearMap.map_le_range hcx
  obtain ⟨m, rfl⟩ := hx'range
  obtain ⟨a, haA, ha⟩ := hcx
  have hcm : c • m = a := by
    apply hi
    rw [map_smul, ha]
  have hm : m ∈ A := hA c m hc (hcm ▸ haA)
  exact Submodule.mem_map_of_mem hm

private theorem map_eq_of_saturated_residual [IsDomain R] [IsDiscreteValuationRing R]
    {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [IsNoetherian R M'] [Module.IsTorsionFree R M']
    (i : M →ₗ[R] M') (hi : Function.Injective i) {ϖ : R} (hϖ : Irreducible ϖ)
    (hres : ∀ (m : M) (x' : M'), i m = ϖ • x' → ∃ m₁ : M, m = ϖ • m₁)
    {A : Submodule R M} (hA : Saturated A) {B : Submodule R M'}
    (hle : Submodule.map i A ≤ B) (hrank : Module.finrank R B ≤ Module.finrank R A) :
    Submodule.map i A = B := by
  have hsat : Saturated (Submodule.map i A) :=
    (saturated_range_of_residual i hϖ hres).map hi hA
  refine hsat.eq_of_le_of_finrank_le hle ?_
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective i hi A).symm]
  exact hrank

end IharaLemmaSol

open IharaLemma

theorem solution {𝒪 : Type} [CommRing 𝒪] {B : Type}
    [CommRing B] [Algebra 𝒪 B] {W : Type} [AddCommGroup W] [Module B W] [Module 𝒪 W]
    [IsScalarTower 𝒪 B W] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [Module.Finite 𝒪 W] [Module.Free 𝒪 W] {V : Type} [AddCommGroup V] [Module 𝒪 V]
    (i : V →ₗ[𝒪] W) (e : B)
    (hmem : ∀ v : V, i v ∈ (cornerSubmodule (M := W) e).restrictScalars 𝒪)
    (hi : Function.Injective i) {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : V) (x : W), i v = ϖ • x → ∃ v₁ : V, v = ϖ • v₁)
    {A : Submodule 𝒪 V} (hA : ∀ (c : 𝒪) (x : V), c ≠ 0 → c • x ∈ A → x ∈ A)
    {Bc : Submodule 𝒪 ((cornerSubmodule (M := W) e).restrictScalars 𝒪)}
    (hle : Submodule.map (LinearMap.codRestrict
      ((cornerSubmodule (M := W) e).restrictScalars 𝒪) i hmem) A ≤ Bc)
    (hrank : Module.finrank 𝒪 Bc ≤ Module.finrank 𝒪 A) :
    Submodule.map (LinearMap.codRestrict
      ((cornerSubmodule (M := W) e).restrictScalars 𝒪) i hmem) A = Bc := by
  haveI : IsNoetherian 𝒪 W := isNoetherian_of_isNoetherianRing_of_finite 𝒪 W
  haveI : Module.IsTorsionFree 𝒪 ((cornerSubmodule (M := W) e).restrictScalars 𝒪) :=
    Function.Injective.moduleIsTorsionFree (fun z => (z : W)) Subtype.val_injective
      (fun _ _ => rfl)
  refine IharaLemmaSol.map_eq_of_saturated_residual _ ?_ hϖ ?_ hA hle hrank
  · intro a b h
    exact hi (congrArg Subtype.val h)
  · intro v z h
    refine hres v (z : W) ?_
    have := congrArg Subtype.val h
    simpa using this

end S_IharaLemma_map_codRestrict_eq_of_residual
end P2MW
export P2MW.S_IharaLemma_map_codRestrict_eq_of_residual (solution)
