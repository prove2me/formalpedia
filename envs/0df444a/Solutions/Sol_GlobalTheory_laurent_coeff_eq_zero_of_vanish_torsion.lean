-- Prove2me | solution 1 for GlobalTheory.laurent_coeff_eq_zero_of_vanish_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:53.333799+00:00
-- url     : https://prove2.me/submissions/39705af1-d8b0-457b-8f95-3a9e7ee7809f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CoeffEqZeroOfSumSmulEqZeroOfSeparating
import Theorems.Thm_GlobalTheory_coeff_eq_zero_of_sum_smul_eq_zero_of_separating
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (n : ℕ), n.Prime →
    ∀ s : Finset Y, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (A : Type) [CommRing A] [IsLocalRing A] (ζ : A),
    IsUnit (n : A) → ζ ^ (n ^ j) = 1 → IsPrimitiveRoot (IsLocalRing.residue A ζ) (n ^ j) →
    ∀ (M : Type) [AddCommGroup M] [Module A M] (a : Y → M),
    (∀ t : Multiplicative Y →* Aˣ, (∀ y, t y ^ (n ^ j) = 1) →
      ∑ y ∈ s, (t (Multiplicative.ofAdd y) : A) • a y = 0) → ∀ y ∈ s, a y = 0 := by
  intro Y _ _ _ n hn s
  let b := Module.Free.chooseBasis ℤ Y

  refine ⟨∑ p ∈ s ×ˢ s, ∑ i, (b.repr (p.1 - p.2) i).natAbs, ?_⟩
  intro j hj A _ _ ζ _ hζ hprim M _ _ a ha
  have hN : n ^ j ≠ 0 := pow_ne_zero _ hn.ne_zero
  let u : Aˣ := Units.ofPowEqOne ζ (n ^ j) hζ hN
  have hu : u ^ (n ^ j) = 1 := Units.pow_ofPowEqOne hζ hN

  let χ : _ → Multiplicative Y →* Aˣ := fun i =>
    (zpowersHom Aˣ u).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
  have hχ : ∀ i y, χ i (Multiplicative.ofAdd y) = u ^ (b.repr y i) := by
    intro i y
    simp [χ, zpowersHom]
  have hχord : ∀ i y, χ i y ^ (n ^ j) = 1 := by
    intro i y
    rw [show y = Multiplicative.ofAdd (Multiplicative.toAdd y) from rfl, hχ, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  let P : (Y → A) → Prop := fun f =>
    ∃ t : Multiplicative Y →* Aˣ, (∀ y, t y ^ (n ^ j) = 1) ∧ f = fun y => (t (Multiplicative.ofAdd y) : A)
  refine coeff_eq_zero_of_sum_smul_eq_zero_of_separating P ⟨1, fun _ => one_pow _, by funext; simp⟩
    ?_ s ?_ a ?_
  · rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
    exact ⟨t * t', fun y => by rw [MonoidHom.mul_apply, mul_pow, ht, ht', one_mul],
      by funext y; simp⟩
  · intro y hy z hz hyz
    have hw : b.repr (y - z) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]
      exact sub_ne_zero.mpr hyz
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hw
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
    refine ⟨_, ⟨χ i, hχord i, rfl⟩, ?_⟩
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hχ, hχ, map_sub]
    let v : (IsLocalRing.ResidueField A)ˣ := Units.map (IsLocalRing.residue A).toMonoidHom u
    have hv : IsPrimitiveRoot v (n ^ j) := IsPrimitiveRoot.coe_units_iff.mp (by simpa [v, u] using hprim)
    have hres : ∀ k : ℤ, IsLocalRing.residue A ((u ^ k : Aˣ) : A) = ((v ^ k : _ˣ) : _) := by
      intro k
      rw [show v ^ k = Units.map (IsLocalRing.residue A).toMonoidHom (u ^ k) from (map_zpow _ u k).symm]
      rfl
    rw [hres, hres, sub_ne_zero, Ne, Units.val_inj, ← div_eq_one, div_eq_mul_inv, ← zpow_sub, ← Finsupp.sub_apply,
      ← map_sub, hv.zpow_eq_one_iff_dvd]
    intro hdvd
    apply hi
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    have h1 : (b.repr (y - z) i).natAbs ≤ ∑ p ∈ s ×ˢ s, ∑ i, (b.repr (p.1 - p.2) i).natAbs := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun p : Y × Y => ∑ i, (b.repr (p.1 - p.2) i).natAbs)
        (fun _ _ => Nat.zero_le _) (show (y, z) ∈ s ×ˢ s from Finset.mem_product.mpr ⟨hy, hz⟩))
      exact Finset.single_le_sum (f := fun i => (b.repr (y - z) i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : j < n ^ j := Nat.lt_pow_self hn.one_lt
    simp only [Int.natAbs_natCast]
    omega
  · rintro _ ⟨t, ht, rfl⟩
    exact ha t ht
end GlobalTheory
