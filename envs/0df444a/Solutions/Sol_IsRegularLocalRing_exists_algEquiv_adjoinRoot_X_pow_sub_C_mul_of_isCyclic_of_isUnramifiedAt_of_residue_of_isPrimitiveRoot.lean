-- Prove2me | solution 1 for IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c08ac042-3d77-5e54-af9c-aecb2c1a5169

import Mathlib
import Theorems.Thm_UniqueFactorizationMonoid_dvd_multiplicity_of_pow_eq_algebraMap_of_forall_isUnramifiedAt
import Theorems.Thm_IsAdicComplete_mem_range_algebraMap_of_pow_eq_unit_of_forall_sub_mem_maximalIdeal
import Theorems.Thm_UniqueFactorizationMonoid_exists_eq_unit_mul_pow_mul_pow_of_forall_dvd_multiplicity
import Theorems.Thm_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_apply_root_eq_of_isIntegrallyClosed_of_finrank_eq
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open IsLocalRing Polynomial

namespace IsRegularLocalRing
p2m_export "IsRegularLocalRing" "spanFinrank_maximalIdeal exists_algEquiv_adjoinRoot_X_pow_sub_C_apply_root_eq_of_isIntegrallyClosed_of_finrank_eq uniqueFactorizationMonoid_of_ringKrullDim_le_two"
namespace RungZ
p2m_open "IsRegularLocalRing"

theorem notMem_sq_of_maximalIdeal_eq_span_pair {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (ϖ s : R) (hmax : maximalIdeal R = Ideal.span {ϖ, s}) (hdim : ringKrullDim R = 2) :
    s ∉ maximalIdeal R ^ 2 := by
  intro hs2

  have hle : maximalIdeal R ≤ Ideal.span {ϖ} := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R) (IsNoetherian.noetherian _)
      (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    conv_lhs => rw [hmax]
    rw [Ideal.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Submodule.mem_sup_left (Ideal.mem_span_singleton_self _)
    · apply Submodule.mem_sup_right
      rw [Ideal.smul_eq_mul, ← pow_two]
      exact hs2
  have hϖ : ϖ ∈ maximalIdeal R := by rw [hmax]; exact Ideal.subset_span (by simp)
  have heq : maximalIdeal R = Ideal.span {ϖ} := le_antisymm hle ((Ideal.span_singleton_le_iff_mem _).mpr hϖ)
  have h1 : (maximalIdeal R).spanFinrank ≤ 1 := by
    rw [heq, ← Set.ncard_singleton ϖ]
    exact Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton ϖ)
  have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [hdim] at h2
  have : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ (1 : ℕ) := by exact_mod_cast h1
  rw [h2] at this
  exact absurd this (by decide)

theorem irreducible_of_notMem_sq {R : Type*} [CommRing R] [IsLocalRing R] {s : R}
    (hs : s ∈ maximalIdeal R) (hs2 : s ∉ maximalIdeal R ^ 2) : Irreducible s := by
  refine ⟨fun hu => (IsLocalRing.mem_maximalIdeal _).mp hs hu, fun a b hab => ?_⟩
  by_contra h
  push_neg at h
  apply hs2
  rw [hab, pow_two]
  exact Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).mpr h.1) ((IsLocalRing.mem_maximalIdeal _).mpr h.2)

theorem height_span_singleton_eq_one {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {p : R}
    (hp : Prime p) : (Ideal.span {p}).height = 1 := by
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  apply le_antisymm
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {p}) (Ideal.span {p})
      (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton _)
  · exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hp.ne_zero)

theorem exists_algebraMap_eq_of_isIntegral {R B F : Type*} [CommRing R] [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Field F] [Algebra R B] [Algebra R F] [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    (x : F) (hx : IsIntegral R x) : ∃ y : B, algebraMap B F y = x :=
  IsIntegrallyClosed.isIntegral_iff.mp hx.tower_top

theorem finrank_le_of_pow_mem_of_adjoin_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (α : L) (m : ℕ) (hm : 0 < m) (c : K) (hα : α ^ m = algebraMap K L c)
    (htop : IntermediateField.adjoin K {α} = ⊤) : Module.finrank K L ≤ m := by
  have hint : IsIntegral K α := IsIntegral.of_finite K α
  have h1 : Module.finrank K L = (minpoly K α).natDegree := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top']
  rw [h1]
  have hdvd : minpoly K α ∣ X ^ m - C c :=
    minpoly.dvd K α (by rw [map_sub, map_pow, aeval_X, aeval_C, hα, sub_self])
  have hne : (X ^ m - C c : K[X]) ≠ 0 := X_pow_sub_C_ne_zero hm c
  calc (minpoly K α).natDegree ≤ (X ^ m - C c : K[X]).natDegree := natDegree_le_of_dvd hdvd hne
    _ = m := natDegree_X_pow_sub_C

theorem adjoin_simple_eq_top_of_eq_mul {K L : Type*} [Field K] [Field L] [Algebra K L]
    (α β : L) (c : K) (hc : c ≠ 0) (hβ : β = algebraMap K L c * α)
    (h : IntermediateField.adjoin K {α} = ⊤) : IntermediateField.adjoin K {β} = ⊤ := by
  rw [eq_top_iff, ← h, IntermediateField.adjoin_simple_le_iff]
  have : α = algebraMap K L c⁻¹ * β := by
    rw [hβ, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  rw [this]
  exact mul_mem (algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self K β)

end IsRegularLocalRing.RungZ

theorem solution
    {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [IsAdicComplete (maximalIdeal R) R]
    (ϖ s : R) (hmax : maximalIdeal R = Ideal.span {ϖ, s}) (hdim : ringKrullDim R = 2)
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R)) (ζ : R) (hζ : IsPrimitiveRoot ζ e)
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (K₀ : Type*) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra R F] [IsScalarTower R K₀ F]
    [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F)) (hdeg : Module.finrank K₀ F = e)
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (𝔭.comap (algebraMap R B)).height = 1 →
      s ∉ 𝔭.comap (algebraMap R B) → Algebra.IsUnramifiedAt R 𝔭)
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B) :
    ∃ u : Rˣ, Nonempty (B ≃ₐ[R] AdjoinRoot (X ^ e - C ((u : R) * s) : R[X])) := by
  classical

  have hinjRB : Function.Injective (algebraMap R B) := FaithfulSMul.algebraMap_injective R B
  haveI hUFD : UniqueFactorizationMonoid R :=
    IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two R hdim.le
  have hinjRK : Function.Injective (algebraMap R K₀) := IsFractionRing.injective R K₀
  have hinjRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]; exact (algebraMap K₀ F).injective.comp hinjRK
  have hinjBF : Function.Injective (algebraMap B F) := IsFractionRing.injective B F

  have hs𝔪 : s ∈ maximalIdeal R := by rw [hmax]; exact Ideal.subset_span (by simp)
  have hs2 : s ∉ maximalIdeal R ^ 2 := IsRegularLocalRing.RungZ.notMem_sq_of_maximalIdeal_eq_span_pair ϖ s hmax hdim
  have hs0 : s ≠ 0 := fun h => hs2 (by rw [h]; exact zero_mem _)
  have hsprime : Prime s :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (IsRegularLocalRing.RungZ.irreducible_of_notMem_sq hs𝔪 hs2)
  have hsF0 : algebraMap R F s ≠ 0 := (map_ne_zero_iff _ hinjRF).mpr hs0

  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  haveI : IsLocalHom (algebraMap R B) := by
    constructor
    intro a ha
    by_contra hna
    have hmax' : ((maximalIdeal B).comap (algebraMap R B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    have hle : maximalIdeal R ≤ (maximalIdeal B).comap (algebraMap R B) := by
      rw [IsLocalRing.eq_maximalIdeal hmax']
    have : algebraMap R B a ∈ maximalIdeal B := hle ((IsLocalRing.mem_maximalIdeal _).mpr hna)
    exact (IsLocalRing.mem_maximalIdeal _).mp this ha

  by_cases he1 : e = 1
  · subst he1
    obtain ⟨φ, -⟩ := IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_apply_root_eq_of_isIntegrallyClosed_of_finrank_eq
      hdim.le (t := (((1 : Rˣ) : R) * s)) (by rw [Units.val_one, one_mul]; exact hs𝔪)
      (by rw [Units.val_one, one_mul]; exact hs2) Nat.one_pos B K₀ F hdeg (algebraMap R B (((1 : Rˣ) : R) * s)) (by rw [pow_one])
    exact ⟨1, ⟨φ.symm⟩⟩
  have he2 : 2 ≤ e := by omega

  have hζK : IsPrimitiveRoot (algebraMap R K₀ ζ) e := hζ.map_of_injective hinjRK
  have hK : (primitiveRoots (Module.finrank K₀ F) K₀).Nonempty :=
    ⟨algebraMap R K₀ ζ, by rw [hdeg, mem_primitiveRoots he]; exact hζK⟩
  haveI : IsCyclic (F ≃ₐ[K₀] F) := hcyc
  obtain ⟨α, ⟨c, hc⟩, hαtop⟩ := exists_root_adjoin_eq_top_of_isCyclic K₀ F hK
  rw [hdeg] at hc

  obtain ⟨a, b, hb, hcab⟩ := IsFractionRing.div_surjective (A := R) c
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero hb
  set f : R := b ^ (e - 1) * a with hf
  set α₁ : F := algebraMap R F b * α with hα₁def
  have hα₁ : α₁ ^ e = algebraMap R F f := by
    rw [hα₁def, mul_pow, ← hc, ← hcab, hf, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      map_mul, map_pow]
    have hbF : algebraMap R F b ≠ 0 := (map_ne_zero_iff _ hinjRF).mpr hb0
    have : e = (e - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    field_simp
  have hα₁top : IntermediateField.adjoin K₀ {α₁} = ⊤ :=
    IsRegularLocalRing.RungZ.adjoin_simple_eq_top_of_eq_mul α α₁ (algebraMap R K₀ b)
      ((map_ne_zero_iff _ hinjRK).mpr hb0) (by rw [hα₁def, ← IsScalarTower.algebraMap_apply]) hαtop

  have hf0 : f ≠ 0 := by
    intro hf0
    apply he1
    have hα₁0 : α₁ = 0 := by
      have : α₁ ^ e = 0 := by rw [hα₁, hf0, map_zero]
      exact pow_eq_zero_iff he.ne' |>.mp this
    have htb : (⊤ : IntermediateField K₀ F) = ⊥ := by
      rw [← hα₁top, IntermediateField.adjoin_simple_eq_bot_iff, hα₁0]; exact zero_mem _
    rw [← hdeg, ← IntermediateField.finrank_top', htb, IntermediateField.finrank_bot]

  have hdiv : ∀ p : R, Prime p → ¬ Associated p s → e ∣ multiplicity p f := by
    intro p hp hps
    refine UniqueFactorizationMonoid.dvd_multiplicity_of_pow_eq_algebraMap_of_forall_isUnramifiedAt p hp e he f hf0 B K₀ F α₁ hα₁ ?_
    intro 𝔓 _ h𝔓
    refine hunr 𝔓 ?_ ?_
    · rw [h𝔓]; exact IsRegularLocalRing.RungZ.height_span_singleton_eq_one hp
    · rw [h𝔓, Ideal.mem_span_singleton]
      intro hdvd
      exact hps (hp.associated_of_dvd hsprime hdvd)
  obtain ⟨w, k, g, hfac⟩ :=
    UniqueFactorizationMonoid.exists_eq_unit_mul_pow_mul_pow_of_forall_dvd_multiplicity s hsprime e he f hf0 hdiv
  have hg0 : g ≠ 0 := by
    rintro rfl; apply hf0; rw [hfac, zero_pow he.ne', mul_zero]
  have hgF : algebraMap R F g ≠ 0 := (map_ne_zero_iff _ hinjRF).mpr hg0

  set α₂ : F := α₁ / algebraMap R F g with hα₂def
  have hα₂ : α₂ ^ e = algebraMap R F (w : R) * algebraMap R F s ^ k := by
    rw [hα₂def, div_pow, hα₁, hfac, map_mul, map_mul, map_pow, map_pow, mul_div_assoc, div_self (pow_ne_zero _ hgF), mul_one]
  have hα₂top : IntermediateField.adjoin K₀ {α₂} = ⊤ :=
    IsRegularLocalRing.RungZ.adjoin_simple_eq_top_of_eq_mul α₁ α₂ (algebraMap R K₀ g)⁻¹
      (inv_ne_zero ((map_ne_zero_iff _ hinjRK).mpr hg0))
      (by rw [hα₂def, map_inv₀, ← IsScalarTower.algebraMap_apply, div_eq_inv_mul]) hα₁top
  have hα₂0 : α₂ ≠ 0 := by
    intro h0
    have : α₂ ^ e = 0 := by rw [h0, zero_pow he.ne']
    rw [hα₂] at this
    exact (mul_ne_zero ((map_ne_zero_iff _ hinjRF).mpr w.ne_zero) (pow_ne_zero _ hsF0)) this

  have hcop : Nat.Coprime k e := by
    by_contra hd
    set d := Nat.gcd k e with hddef
    obtain ⟨k', hk'⟩ : d ∣ k := Nat.gcd_dvd_left k e
    obtain ⟨e', he'⟩ : d ∣ e := Nat.gcd_dvd_right k e
    have hd0 : 0 < d := Nat.gcd_pos_of_pos_right _ he
    have hd1 : d ≠ 1 := fun h => hd (show Nat.gcd k e = 1 by rw [← hddef]; exact h)
    have hd2 : 2 ≤ d := by omega
    have he'0 : 0 < e' := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at he'; omega)

    set β : F := α₂ ^ e' / algebraMap R F s ^ k' with hβdef
    have hβd : β ^ d = algebraMap R F (w : R) := by
      rw [hβdef, div_pow, ← pow_mul, ← pow_mul, mul_comm e' d, mul_comm k' d, ← he', ← hk', hα₂,
        mul_div_assoc, div_self (pow_ne_zero _ hsF0), mul_one]
    have hβint : IsIntegral R β := by
      refine ⟨X ^ d - C (w : R), monic_X_pow_sub_C _ hd0.ne', ?_⟩
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, hβd, sub_self]
    obtain ⟨βB, hβB⟩ := IsRegularLocalRing.RungZ.exists_algebraMap_eq_of_isIntegral (R := R) (B := B) β hβint
    have hβBd : βB ^ d = algebraMap R B (w : R) := by
      apply hinjBF; rw [map_pow, hβB, hβd, ← IsScalarTower.algebraMap_apply]
    have hdR : IsUnit (d : R) := by
      apply isUnit_of_mul_isUnit_left (y := (e' : R))
      rw [← Nat.cast_mul, ← he']; exact heR
    obtain ⟨r, hr⟩ := IsAdicComplete.mem_range_algebraMap_of_pow_eq_unit_of_forall_sub_mem_maximalIdeal
      d hd0 hdR w hres βB hβBd

    have hαe' : α₂ ^ e' = algebraMap K₀ F (algebraMap R K₀ r * algebraMap R K₀ s ^ k') := by
      rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        show algebraMap R F r = β by rw [← hβB, ← hr, ← IsScalarTower.algebraMap_apply], hβdef,
        div_mul_cancel₀ _ (pow_ne_zero _ hsF0)]
    have hle := IsRegularLocalRing.RungZ.finrank_le_of_pow_mem_of_adjoin_eq_top α₂ e' he'0 _ hαe' hα₂top
    rw [hdeg, he'] at hle
    have : d * e' ≤ 1 * e' := by rw [one_mul]; exact hle
    have := Nat.le_of_mul_le_mul_right this he'0
    omega

  obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, (k : ℤ) * x + (e : ℤ) * y = 1 := by
    refine ⟨Nat.gcdA k e, Nat.gcdB k e, ?_⟩
    have := Nat.gcd_eq_gcd_ab k e
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    exact_mod_cast this.symm
  set θF : F := α₂ ^ x * algebraMap R F s ^ y with hθF
  have hθFe : θF ^ e = algebraMap R F (((w ^ x : Rˣ) : R) * s) := by
    have hwF : algebraMap R F ((w ^ x : Rˣ) : R) = (algebraMap R F (w : R)) ^ x := by
      have hu : ∀ u : Rˣ, algebraMap R F (u : R) = ((Units.map (algebraMap R F : R →* F) u : Fˣ) : F) :=
        fun u => rfl
      rw [hu, hu, map_zpow, Units.val_zpow_eq_zpow_val]
    have hW0 : algebraMap R F (w : R) ≠ 0 := (map_ne_zero_iff _ hinjRF).mpr w.ne_zero
    rw [map_mul, hwF, hθF, mul_pow, ← zpow_natCast, ← zpow_natCast (algebraMap R F s ^ y), ← zpow_mul, ← zpow_mul,
      mul_comm x (e : ℤ), zpow_mul, zpow_natCast, hα₂, mul_zpow, ← zpow_natCast (algebraMap R F s), ← zpow_mul,
      mul_assoc, ← zpow_add₀ hsF0]
    congr 1
    rw [show (k : ℤ) * x + y * (e : ℤ) = 1 by linarith, zpow_one]

  have hθint : IsIntegral R θF := by
    refine ⟨X ^ e - C (((w ^ x : Rˣ) : R) * s), monic_X_pow_sub_C _ he.ne', ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hθFe, sub_self]
  obtain ⟨θ, hθ⟩ := IsRegularLocalRing.RungZ.exists_algebraMap_eq_of_isIntegral (R := R) (B := B) θF hθint
  have hθe : θ ^ e = algebraMap R B (((w ^ x : Rˣ) : R) * s) := by
    apply hinjBF
    rw [map_pow, hθ, hθFe, ← IsScalarTower.algebraMap_apply]

  have ht𝔪 : ((w ^ x : Rˣ) : R) * s ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hs𝔪
  have ht2 : ((w ^ x : Rˣ) : R) * s ∉ maximalIdeal R ^ 2 := by
    intro h
    apply hs2
    have := Ideal.mul_mem_left _ (((w ^ x)⁻¹ : Rˣ) : R) h
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  obtain ⟨φ, -⟩ := IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_apply_root_eq_of_isIntegrallyClosed_of_finrank_eq
    hdim.le ht𝔪 ht2 he B K₀ F hdeg θ hθe
  exact ⟨w ^ x, ⟨φ.symm⟩⟩

end S_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot
end P2MW
export P2MW.S_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot (solution)
