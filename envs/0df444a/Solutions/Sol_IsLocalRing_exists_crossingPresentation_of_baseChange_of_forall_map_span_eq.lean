-- Prove2me | solution 1 for IsLocalRing.exists_crossingPresentation_of_baseChange_of_forall_map_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b3dd0df8-4d47-5d32-8348-29c98fcdedbb

import Mathlib
import Theorems.Thm_Ideal_eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq
import Theorems.Thm_Algebra_Etale_exists_sum_mul_smul_eq_ite_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_crossingPresentation_of_baseChange_of_forall_map_span_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct
open IsLocalRing

namespace C2Aux

theorem isLocalHom_of_finite {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : IsLocalHom (algebraMap R S) := by
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  refine ⟨fun r hr => ?_⟩
  by_contra hnu
  have hmem : r ∈ maximalIdeal R := hnu
  have hcomap : (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal S))
  rw [← hcomap, Ideal.mem_comap] at hmem
  exact hmem hr

theorem comap_maximalIdeal {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] : (maximalIdeal S).comap f = maximalIdeal R := by
  ext r
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

theorem exists_unit_mul_eq_of_span_eq {T : Type*} [CommRing T] {a b : T} (hb : b ∈ nonZeroDivisors T)
    (h : Ideal.span {a} = Ideal.span {b}) : ∃ v : Tˣ, a = v * b := by
  have ha : a ∈ Ideal.span {b} := h ▸ Ideal.mem_span_singleton_self a
  have hb' : b ∈ Ideal.span {a} := h.symm ▸ Ideal.mem_span_singleton_self b
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hb'

  have h1 : (1 - d * c) * b = 0 := by linear_combination -hd
  have hdc : d * c = 1 := by
    have := (mul_right_mem_nonZeroDivisors_eq_zero_iff hb).mp h1
    linear_combination -this
  exact ⟨⟨c, d, by rw [mul_comm, hdc], hdc⟩, rfl⟩

theorem exists_eq_span_singleton_of_map_eq_span {S T : Type*} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [CommRing T] [Nontrivial T] [Algebra S T] [Module.Free S T] [Module.Finite S T]
    (J : Ideal S) (x' : T) (hx' : x' ∈ nonZeroDivisors T) (hJ : J.map (algebraMap S T) = Ideal.span {x'}) :
    ∃ x : S, J = Ideal.span {x} := by
  classical

  let b := Module.finBasis S T
  set k := Module.finrank S T with hk
  have hkpos : 0 < k := Fin.pos_iff_nonempty.mpr b.index_nonempty

  let Φ : (Fin k → J) →ₗ[S] T :=
    { toFun := fun j => ∑ i, ((j i : J) : S) • b i
      map_add' := fun j j' => by
        simp only [Pi.add_apply, Submodule.coe_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c j => by
        simp only [Pi.smul_apply, SetLike.val_smul, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul] }
  have hΦ_apply : ∀ j : Fin k → J, Φ j = ∑ i, ((j i : J) : S) • b i := fun j => rfl
  have hΦinj : Function.Injective Φ := by
    intro j j' hjj
    have hrepr : ∀ i, ((j i : J) : S) = ((j' i : J) : S) := by
      intro i
      have h1 := congrArg (fun t => b.repr t i) hjj
      simpa [hΦ_apply, map_sum, map_smul, Finsupp.single_apply, b.repr_self] using h1
    exact funext fun i => Subtype.ext (hrepr i)

  have hrange : LinearMap.range Φ = (J.map (algebraMap S T)).restrictScalars S := by
    apply le_antisymm
    · rintro t ⟨j, rfl⟩
      rw [Submodule.restrictScalars_mem, hΦ_apply]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (j i).2)
    ·
      have hmul : ∀ (t y : T), y ∈ LinearMap.range Φ → t * y ∈ LinearMap.range Φ := by
        rintro t y ⟨j, rfl⟩
        refine ⟨fun l => ⟨∑ i, b.repr (t * b i) l * ((j i : J) : S),
          Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (j i).2⟩, ?_⟩
        rw [hΦ_apply, hΦ_apply, Finset.mul_sum]
        simp only [Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        symm
        calc t * (((j i : J) : S) • b i) = ((j i : J) : S) • (t * b i) := (mul_smul_comm _ _ _)
          _ = ((j i : J) : S) • ∑ l, b.repr (t * b i) l • b l := by rw [b.sum_repr]
          _ = ∑ l, (b.repr (t * b i) l * ((j i : J) : S)) • b l := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [smul_smul, mul_comm]
      intro t ht
      rw [Submodule.restrictScalars_mem] at ht
      refine Submodule.span_induction (p := fun t _ => t ∈ LinearMap.range Φ) ?_ ?_ ?_ ?_ ht
      · rintro _ ⟨s, hs, rfl⟩
        refine ⟨fun l => ⟨b.repr 1 l * s, Ideal.mul_mem_left _ _ hs⟩, ?_⟩
        rw [hΦ_apply]
        show ∑ i, (b.repr 1 i * s) • b i = algebraMap S T s
        symm
        calc algebraMap S T s = s • (1 : T) := Algebra.algebraMap_eq_smul_one s
          _ = s • ∑ i, b.repr 1 i • b i := by rw [b.sum_repr]
          _ = ∑ i, (b.repr 1 i * s) • b i := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [smul_smul, mul_comm]
      · exact zero_mem _
      · intro _ _ _ _ h₁ h₂
        exact add_mem h₁ h₂
      · intro t _ _ hy
        exact hmul t _ hy

  let e₁ : (Fin k → J) ≃ₗ[S] LinearMap.range Φ := LinearEquiv.ofInjective Φ hΦinj
  have hx'eq : (LinearMap.range Φ) = (Ideal.span {x'}).restrictScalars S := by rw [hrange, hJ]
  let e₂ : LinearMap.range Φ ≃ₗ[S] (Ideal.span {x'}).restrictScalars S := LinearEquiv.ofEq _ _ hx'eq
  let mulx : T →ₗ[S] (Ideal.span {x'}).restrictScalars S :=
    { toFun := fun t => ⟨t * x', Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x')⟩
      map_add' := fun t t' => Subtype.ext (add_mul t t' x')
      map_smul' := fun c t => Subtype.ext (by simp [Algebra.smul_def, mul_assoc]) }
  have hmulx : Function.Bijective mulx := by
    constructor
    · intro t t' htt
      have : t * x' = t' * x' := congrArg Subtype.val htt
      exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hx').mp (by linear_combination this) |> sub_eq_zero.mp
    · rintro ⟨z, hz⟩
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      exact ⟨t, rfl⟩
  let e₃ : T ≃ₗ[S] (Ideal.span {x'}).restrictScalars S := LinearEquiv.ofBijective mulx hmulx
  let E : (Fin k → J) ≃ₗ[S] (Fin k → S) := (e₁.trans e₂).trans (e₃.symm.trans b.equivFun)

  haveI : Module.Projective S J := Module.Projective.of_split
    (E.toLinearMap.comp (LinearMap.single S (fun _ : Fin k => (J : Type _)) ⟨0, hkpos⟩))
    ((LinearMap.proj ⟨0, hkpos⟩).comp E.symm.toLinearMap)
    (by ext j; simp)
  haveI : Module.Finite S J := Module.IsNoetherian.finite S J
  haveI : Module.Free S J := Module.free_of_flat_of_isLocalRing

  have hrank : Module.finrank S J = 1 := by
    have h1 : Module.finrank S (Fin k → J) = Module.finrank S (Fin k → S) := E.finrank_eq
    rw [Module.finrank_pi_fintype, Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h1
    exact Nat.eq_of_mul_eq_mul_left hkpos (by rw [h1, mul_one])

  let β : Module.Basis (Fin 1) S J := Module.finBasisOfFinrankEq S J hrank
  refine ⟨(β 0 : J), le_antisymm ?_ ?_⟩
  · intro j hj
    have hsum := β.sum_repr ⟨j, hj⟩
    rw [Fin.sum_univ_one] at hsum
    have : j = β.repr ⟨j, hj⟩ 0 * ((β 0 : J) : S) := by
      have := congrArg Subtype.val hsum
      simpa [smul_eq_mul] using this.symm
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_singleton_le_iff_mem]
    exact (β 0).2

end C2Aux

open C2Aux in
theorem solution
    {W W' S : Type*} [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
    [Algebra W W'] [Module.Finite W W'] [Module.Flat W W'] [FaithfulSMul W W'] [Algebra.Etale W W']
    {Γ : Type*} [Group Γ] [Fintype Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
    (hinv : ∀ w' : W', (∀ γ : Γ, γ • w' = w') ↔ w' ∈ Set.range (algebraMap W W'))
    (hcard : Fintype.card Γ = Module.finrank W W')
    [CommRing S] [IsNoetherianRing S] [IsLocalRing S] [Algebra W S]
    [IsLocalRing (S ⊗[W] W')]
    (π : W) (m : ℕ)
    (hπ : IsSMulRegular (S ⊗[W] W') (algebraMap W (S ⊗[W] W') π))
    (x' y' : S ⊗[W] W') (u' : (S ⊗[W] W')ˣ)
    (hxy : x' * y' = algebraMap W (S ⊗[W] W') π ^ m * ↑u')
    (hmax : IsLocalRing.maximalIdeal (S ⊗[W] W') =
      Ideal.span {algebraMap W (S ⊗[W] W') π, x', y'})
    (hstabx : ∀ γ : Γ, Ideal.map (Algebra.TensorProduct.map (AlgHom.id S S)
        (MulSemiringAction.toAlgHom W W' γ)) (Ideal.span {x'}) = Ideal.span {x'})
    (hstaby : ∀ γ : Γ, Ideal.map (Algebra.TensorProduct.map (AlgHom.id S S)
        (MulSemiringAction.toAlgHom W W' γ)) (Ideal.span {y'}) = Ideal.span {y'}) :
    ∃ (x y : S) (u : Sˣ),
      x * y = algebraMap W S π ^ m * ↑u ∧
      IsLocalRing.maximalIdeal S = Ideal.span {algebraMap W S π, x, y} ∧
      Ideal.span {(x ⊗ₜ[W] (1 : W'))} = Ideal.span {x'} ∧
      Ideal.span {(y ⊗ₜ[W] (1 : W'))} = Ideal.span {y'} := by
  classical

  haveI : Module.Free W W' := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free S (S ⊗[W] W') := inferInstance
  haveI : Module.Finite S (S ⊗[W] W') := inferInstance
  haveI : Module.FaithfullyFlat S (S ⊗[W] W') := inferInstance
  haveI hloc : IsLocalHom (algebraMap S (S ⊗[W] W')) := isLocalHom_of_finite
  have hι : (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[W] W') = algebraMap S (S ⊗[W] W') :=
    RingHom.ext fun s => rfl
  have hιapply : ∀ s : S, algebraMap S (S ⊗[W] W') s = s ⊗ₜ[W] (1 : W') := fun s => rfl
  have hπS : algebraMap W (S ⊗[W] W') π = algebraMap S (S ⊗[W] W') (algebraMap W S π) :=
    IsScalarTower.algebraMap_apply W S (S ⊗[W] W') π

  have hπm : (algebraMap W (S ⊗[W] W') π) ^ m ∈ nonZeroDivisors (S ⊗[W] W') := by
    apply pow_mem
    rw [mem_nonZeroDivisors_iff_right]
    intro t ht
    exact hπ (by simpa [smul_eq_mul, mul_comm] using ht)
  have hx'reg : x' ∈ nonZeroDivisors (S ⊗[W] W') := by
    rw [mem_nonZeroDivisors_iff_right]
    intro t ht
    have : t * (algebraMap W (S ⊗[W] W') π ^ m * ↑u') = 0 := by
      rw [← hxy, ← mul_assoc, ht, zero_mul]
    rw [← mul_assoc] at this
    have h2 := (mul_right_mem_nonZeroDivisors_eq_zero_iff (Units.isUnit u').mem_nonZeroDivisors).mp this
    exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hπm).mp h2
  have hy'reg : y' ∈ nonZeroDivisors (S ⊗[W] W') := by
    rw [mem_nonZeroDivisors_iff_right]
    intro t ht
    have : t * (algebraMap W (S ⊗[W] W') π ^ m * ↑u') = 0 := by
      rw [← hxy, mul_comm x' y', ← mul_assoc, ht, zero_mul]
    rw [← mul_assoc] at this
    have h2 := (mul_right_mem_nonZeroDivisors_eq_zero_iff (Units.isUnit u').mem_nonZeroDivisors).mp this
    exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hπm).mp h2

  obtain ⟨n, cx, cy, hchr⟩ := Algebra.Etale.exists_sum_mul_smul_eq_ite_of_isLocalRing (Γ := Γ) hinv hcard
  have hGx := Ideal.eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq
    (fun w' hw' => (hinv w').mp hw') cx cy hchr S (Ideal.span {x'}) hstabx
  have hGy := Ideal.eq_map_comap_includeLeft_of_forall_map_eq_of_sum_mul_smul_eq
    (fun w' hw' => (hinv w').mp hw') cx cy hchr S (Ideal.span {y'}) hstaby
  rw [hι] at hGx hGy

  obtain ⟨x, hx⟩ := exists_eq_span_singleton_of_map_eq_span
    ((Ideal.span {x'}).comap (algebraMap S (S ⊗[W] W'))) x' hx'reg hGx.symm
  obtain ⟨y, hy⟩ := exists_eq_span_singleton_of_map_eq_span
    ((Ideal.span {y'}).comap (algebraMap S (S ⊗[W] W'))) y' hy'reg hGy.symm
  have hspanx : Ideal.span {algebraMap S (S ⊗[W] W') x} = Ideal.span {x'} := by
    rw [hGx, hx, Ideal.map_span, Set.image_singleton]
  have hspany : Ideal.span {algebraMap S (S ⊗[W] W') y} = Ideal.span {y'} := by
    rw [hGy, hy, Ideal.map_span, Set.image_singleton]
  obtain ⟨vx, hvx⟩ := exists_unit_mul_eq_of_span_eq hx'reg hspanx
  obtain ⟨vy, hvy⟩ := exists_unit_mul_eq_of_span_eq hy'reg hspany

  have hprod : algebraMap S (S ⊗[W] W') (x * y) =
      algebraMap W (S ⊗[W] W') π ^ m * ↑(vx * vy * u') := by
    rw [map_mul, hvx, hvy, Units.val_mul, Units.val_mul]
    linear_combination (↑vx * ↑vy : S ⊗[W] W') * hxy
  have hmemS : x * y ∈ Ideal.span {algebraMap W S π ^ m} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S ⊗[W] W') (Ideal.span {algebraMap W S π ^ m}),
      Ideal.mem_comap, Ideal.map_span, Set.image_singleton, map_pow, ← hπS, hprod]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmemS
  have hcunit : IsUnit c := by
    have h1 : algebraMap S (S ⊗[W] W') c * algebraMap W (S ⊗[W] W') π ^ m =
        ↑(vx * vy * u') * algebraMap W (S ⊗[W] W') π ^ m := by
      rw [mul_comm (↑(vx * vy * u') : S ⊗[W] W'), ← hprod, ← hc, map_mul, map_pow, ← hπS]
    have h2 : algebraMap S (S ⊗[W] W') c = ↑(vx * vy * u') := by
      have : (algebraMap S (S ⊗[W] W') c - ↑(vx * vy * u')) * algebraMap W (S ⊗[W] W') π ^ m = 0 := by
        rw [sub_mul, h1, sub_self]
      exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hπm).mp this)
    exact (isUnit_map_iff (algebraMap S (S ⊗[W] W')) c).mp (h2 ▸ Units.isUnit _)

  have hmaxS : maximalIdeal S = Ideal.span {algebraMap W S π, x, y} := by
    have hmapI : (Ideal.span {algebraMap W S π, x, y}).map (algebraMap S (S ⊗[W] W')) =
        maximalIdeal (S ⊗[W] W') := by
      rw [Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, ← hπS, hvx, hvy, hmax,
        Ideal.span_insert, Ideal.span_insert, Ideal.span_insert, Ideal.span_insert,
        Ideal.span_singleton_mul_left_unit (Units.isUnit vx), Ideal.span_singleton_mul_left_unit (Units.isUnit vy)]
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S ⊗[W] W') (Ideal.span {algebraMap W S π, x, y}),
      hmapI, comap_maximalIdeal]

  refine ⟨x, y, hcunit.unit, ?_, hmaxS, ?_, ?_⟩
  · rw [IsUnit.unit_spec, mul_comm _ c]
    exact hc.symm
  · rw [← hιapply]; exact hspanx
  · rw [← hιapply]; exact hspany

end S_IsLocalRing_exists_crossingPresentation_of_baseChange_of_forall_map_span_eq
end P2MW
export P2MW.S_IsLocalRing_exists_crossingPresentation_of_baseChange_of_forall_map_span_eq (solution)
