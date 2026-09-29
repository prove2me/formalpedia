-- Prove2me | solution 1 for NumberField.natCard_sUnit_quotient_range_powMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/32a7099d-06b6-5ff6-951c-79554970f14b

import Mathlib
import Theorems.Thm_M4aHerbrand_finrank_sUnit_eq_univ
import Theorems.Thm_MonoidHom_index_range_powMonoidHom_eq_mul_of_exact
import Theorems.Thm_CommGroup_index_range_powMonoidHom_eq_pow_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_natCard_sUnit_quotient_range_powMonoidHom

set_option autoImplicit false

namespace P2mS26B1

theorem eq_one_of_pow_eq_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a : Γ₀} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = 1) : a = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rcases lt_trichotomy a 1 with ha | ha | ha
  · exfalso
    have h1 : a ^ m ≤ 1 := pow_le_one' ha.le m
    have h2 : a ^ (m + 1) ≤ a := by
      rw [pow_succ']
      exact mul_le_of_le_one_right' h1
    rw [h] at h2
    exact absurd h2 (not_le.2 ha)
  · exact ha
  · exfalso
    have h1 : 1 ≤ a ^ m := one_le_pow_of_one_le' ha.le m
    have h2 : a ≤ a ^ (m + 1) := by
      rw [pow_succ']
      exact le_mul_of_one_le_right' h1
    rw [h] at h2
    exact absurd h2 (not_le.2 ha)

end P2mS26B1

theorem solution (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [Finite S]
    {n : ℕ} (hμ : (primitiveRoots n K).Nonempty) :
    Nat.card (↥(S.unit K) ⧸ (powMonoidHom n : ↥(S.unit K) →* ↥(S.unit K)).range)
      = n ^ (Nat.card S + NumberField.Units.rank K + 1) := by
  classical
  obtain ⟨ζ, hζmem⟩ := hμ
  have hnpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hζmem)
  have hζ : IsPrimitiveRoot ζ n := (mem_primitiveRoots hnpos).1 hζmem
  haveI : NeZero n := ⟨hnpos.ne'⟩
  obtain ⟨hfin, hrank⟩ := M4aHerbrand.finrank_sUnit_eq_univ K S
  haveI := hfin

  haveI hfgA : AddGroup.FG (Additive ↥(S.unit K)) := Module.Finite.iff_addGroup_fg.1 hfin
  haveI hfg : Group.FG ↥(S.unit K) :=
    (inferInstance : Group.FG (Multiplicative (Additive ↥(S.unit K))))

  set T : Subgroup ↥(S.unit K) := CommGroup.torsion ↥(S.unit K) with hT
  have hmemT : ∀ g : ↥(S.unit K), g ∈ T ↔ IsOfFinOrder g := fun g => CommGroup.mem_torsion g
  have htf : ∀ (x : ↥(S.unit K) ⧸ T) (m : ℕ), 0 < m → x ^ m = 1 → x = 1 := by
    intro x m hm hx
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hmemT] at hx
      rw [QuotientGroup.eq_one_iff, hmemT]
      exact hx.of_pow hm.ne'

  have hsplit := MonoidHom.index_range_powMonoidHom_eq_mul_of_exact T.subtype (QuotientGroup.mk' T)
    T.subtype_injective (QuotientGroup.mk'_surjective T)
    (by rw [Subgroup.range_subtype, QuotientGroup.ker_mk']) (n := n) (fun x hx => htf x n hnpos hx)

  have hfree := CommGroup.index_range_powMonoidHom_eq_pow_finrank (F := ↥(S.unit K) ⧸ T) htf hnpos

  have hrk : Module.finrank ℤ (Additive (↥(S.unit K) ⧸ T)) = Module.finrank ℤ (Additive ↥(S.unit K)) := by
    let f : Additive ↥(S.unit K) →ₗ[ℤ] Additive (↥(S.unit K) ⧸ T) :=
      (MonoidHom.toAdditive (QuotientGroup.mk' T)).toIntLinearMap
    have hf : ∀ x, f x = Additive.ofMul (QuotientGroup.mk' T (Additive.toMul x)) := fun x => rfl
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective T (Additive.toMul y)
      exact ⟨Additive.ofMul g, by rw [hf, toMul_ofMul, hg, ofMul_toMul]⟩
    have hker : Module.rank ℤ ↥(LinearMap.ker f) = 0 := by
      rw [rank_eq_zero_iff]
      intro x
      have hx : QuotientGroup.mk' T (Additive.toMul (x : Additive ↥(S.unit K))) = 1 := by
        have h0 := x.2
        rw [LinearMap.mem_ker, hf] at h0
        exact congrArg Additive.toMul h0
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmemT] at hx
      obtain ⟨m, hm, hxm⟩ := hx.exists_pow_eq_one
      refine ⟨(m : ℤ), by exact_mod_cast hm.ne', Subtype.ext ?_⟩
      show ((m : ℤ) • (x : Additive ↥(S.unit K))) = 0
      rw [natCast_zsmul]
      show Additive.ofMul (Additive.toMul (x : Additive ↥(S.unit K)) ^ m) = Additive.ofMul 1
      rw [hxm]
    have hrn := LinearMap.rank_range_add_rank_ker f
    rw [hker, add_zero, LinearMap.range_eq_top.2 hsurj, rank_top] at hrn
    apply Module.finrank_eq_of_rank_eq
    rw [hrn]
    exact (Module.finrank_eq_rank ℤ (Additive ↥(S.unit K))).symm

  haveI : IsNoetherian ℤ (Additive ↥(S.unit K)) := isNoetherian_of_isNoetherianRing_of_finite ℤ _
  let TA : Submodule ℤ (Additive ↥(S.unit K)) := AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup T)
  have hmemTA : ∀ x : Additive ↥(S.unit K), x ∈ TA ↔ Additive.toMul x ∈ T := fun x => Iff.rfl
  haveI : Module.Finite ℤ ↥TA := Module.IsNoetherian.finite ℤ ↥TA
  haveI : AddGroup.FG ↥TA := Module.Finite.iff_addGroup_fg.1 inferInstance
  have hTA : AddMonoid.IsTorsion ↥TA := by
    intro x
    have hx : Additive.toMul (x : Additive ↥(S.unit K)) ∈ T := (hmemTA _).1 x.2
    rw [hmemT] at hx
    obtain ⟨m, hm, hxm⟩ := hx.exists_pow_eq_one
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨m, hm, Subtype.ext ?_⟩
    show Additive.ofMul (Additive.toMul (x : Additive ↥(S.unit K)) ^ m) = Additive.ofMul 1
    rw [hxm]
  haveI : Finite ↥TA := AddCommGroup.finite_of_fg_torsion _ hTA
  haveI : Finite ↥T := Finite.of_equiv ↥TA
    ⟨fun x => ⟨Additive.toMul x.1, (hmemTA _).1 x.2⟩, fun x => ⟨Additive.ofMul x.1, (hmemTA _).2 x.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  haveI : IsCyclic ↥T :=
    isCyclic_of_injective_ringHom ((Units.coeHom K).comp ((S.unit K).subtype.comp T.subtype))
      (Units.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective))

  have hζ0 : ζ ≠ 0 := hζ.ne_zero hnpos.ne'
  have hζS : Units.mk0 ζ hζ0 ∈ S.unit K := by
    intro v _
    apply P2mS26B1.eq_one_of_pow_eq_one hnpos.ne'
    rw [Units.val_mk0, ← map_pow, hζ.pow_eq_one, map_one]
  have hg : IsPrimitiveRoot (⟨Units.mk0 ζ hζ0, hζS⟩ : ↥(S.unit K)) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (Units.coeHom K).comp (S.unit K).subtype)
      (by simpa using hζ) (Units.val_injective.comp Subtype.val_injective)
  have hgT : (⟨Units.mk0 ζ hζ0, hζS⟩ : ↥(S.unit K)) ∈ T :=
    (hmemT _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hnpos, hg.pow_eq_one⟩)
  have hdvd : n ∣ Nat.card ↥T := by
    have h1 : orderOf (⟨_, hgT⟩ : ↥T) = n := by
      rw [← orderOf_injective T.subtype T.subtype_injective, Subgroup.subtype_apply, ← hg.eq_orderOf]
    rw [← h1]
    exact orderOf_dvd_natCard _
  have htors : (powMonoidHom n : ↥T →* ↥T).range.index = n := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right hdvd]

  show (powMonoidHom n : ↥(S.unit K) →* ↥(S.unit K)).range.index = _
  rw [hsplit, hfree, hrk, hrank, htors, pow_succ]

end S_NumberField_natCard_sUnit_quotient_range_powMonoidHom
end P2MW
export P2MW.S_NumberField_natCard_sUnit_quotient_range_powMonoidHom (solution)
