-- Prove2me | solution 1 for GlobalTheory.ZM.CycBase.exists_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:17:53.846262+00:00
-- url     : https://prove2.me/submissions/1425f447-e0b1-4d18-a5a0-eaef929f7edc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCyclotomicBaseRingInvertingPrime
import Theorems.Thm_GlobalTheory_ZM_CycBase_zF_prim
import Theorems.Thm_GlobalTheory_ZM_CycBase_cyc
import Theorems.Thm_GlobalTheory_ZM_CycBase_mem_ZP
import Theorems.Thm_GlobalTheory_ZM_exists_arBase_away

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.ZM.CycBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma zeta_isPrimitiveRoot' {k : ℕ} (hk : k ≠ 0) : IsPrimitiveRoot (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta k) k := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta; exact Complex.isPrimitiveRoot_exp k hk
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma inv_natCast_mem_ZP_of_coprime {p M m : ℕ} (hm : m.Coprime p) :
    ((m : ℂ)⁻¹) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP
  exact Subring.subset_closure (Or.inr ⟨m, hm, rfl⟩)
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma snd_eq_zero_of_natCast_mul_eq_one {K : Type} [Field K] {m : ℕ} {v : DualNumber K}
    (h : (m : DualNumber K) * v = 1) : v.snd = 0 ∧ (m : K) ≠ 0 := by
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp at h1 h2
  have hm : (m : K) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact ⟨by simpa [hm] using h2, hm⟩
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma zeta_mem_ZP (p M : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta M ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP
  exact Subring.subset_closure (Or.inl rfl)
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma ringHom_ZP_pow_dualNumber_snd_eq_zero {K : Type} [Field K] {p n e : ℕ}
    (hn : n.Coprime p) (hn0 : n ≠ 0) (f : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e) →+* DualNumber K)
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) : (f x).snd = 0 := by
  have hnK : (n : K) ≠ 0 := by
    have hmul : ((n : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) * ⟨(n : ℂ)⁻¹, inv_natCast_mem_ZP_of_coprime hn⟩ = 1 := by
      apply Subtype.ext; simp [hn0]
    have := congrArg f hmul
    rw [map_mul, map_natCast, map_one] at this
    exact (snd_eq_zero_of_natCast_mul_eq_one this).2
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with hy | ⟨m, hm, rfl⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      set z := f ⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n ^ e), zeta_mem_ZP p _⟩ with hz
      have hN : n ^ e ≠ 0 := pow_ne_zero _ hn0
      have hpow : z ^ (n ^ e) = 1 := by
        rw [hz, ← map_pow]
        have : (⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n ^ e), zeta_mem_ZP p _⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) ^ (n ^ e) = 1 :=
          Subtype.ext (by simpa using (zeta_isPrimitiveRoot' hN).pow_eq_one)
        rw [this, map_one]
      have h1 := congrArg TrivSqZeroExt.fst hpow
      have h2 := congrArg TrivSqZeroExt.snd hpow
      simp only [TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_one] at h1
      rw [TrivSqZeroExt.snd_pow, TrivSqZeroExt.snd_one] at h2
      have hz0 : z.fst ≠ 0 := by
        intro h0; rw [h0, zero_pow hN] at h1; exact zero_ne_one h1
      simp only [nsmul_eq_mul, smul_eq_mul] at h2
      have hNK : ((n ^ e : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hnK
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hNK
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd (pow_eq_zero_iff'.mp h).1 hz0
        · exact h
    · by_cases hm0 : m = 0
      · subst hm0
        have : (⟨((0 : ℕ) : ℂ)⁻¹, Subring.subset_closure (Or.inr ⟨0, hm, rfl⟩)⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = 0 :=
          Subtype.ext (by simp)
        rw [this, map_zero]; rfl
      · have hmul : ((m : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) *
            ⟨(m : ℂ)⁻¹, Subring.subset_closure (Or.inr ⟨m, hm, rfl⟩)⟩ = 1 := by
          apply Subtype.ext; simp [hm0]
        have := congrArg f hmul
        rw [map_mul, map_natCast, map_one] at this
        exact (snd_eq_zero_of_natCast_mul_eq_one this).1
  | zero => rw [show (⟨0, _⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = 0 from rfl, map_zero]; rfl
  | one => rw [show (⟨1, _⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = 1 from rfl, map_one]; rfl
  | add y z hy hz ihy ihz =>
    rw [show (⟨y + z, add_mem hy hz⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = ⟨y, hy⟩ + ⟨z, hz⟩ from rfl, map_add,
      TrivSqZeroExt.snd_add, ihy, ihz, add_zero]
  | neg y hy ihy =>
    rw [show (⟨-y, neg_mem hy⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = -⟨y, hy⟩ from rfl, map_neg,
      TrivSqZeroExt.snd_neg, ihy, neg_zero]
  | mul y z hy hz ihy ihz =>
    rw [show (⟨y * z, mul_mem hy hz⟩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) = ⟨y, hy⟩ * ⟨z, hz⟩ from rfl, map_mul,
      TrivSqZeroExt.snd_mul, ihy, ihz, smul_zero, smul_zero, add_zero]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma spec_dualNumber_hom_ZP_eq_constPt {K : Type} [Field K] {p n e : ℕ}
    (hn : n.Coprime p) (hn0 : n ≠ 0)
    (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e))) : y = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
  conv_lhs => rw [← Spec.map_preimage y]
  conv_rhs => rw [← Spec.map_preimage y]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, ringHom_ZP_pow_dualNumber_snd_eq_zero hn hn0]
end GlobalTheory.ZM.CycBase
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.CycBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.ZM.CycBase
namespace _root_.GlobalTheory.ZM.CycBase
theorem _root_.solution : ∀ (n e p k : ℕ), n.Prime → p.Prime → n ≠ p → 1 ≤ e →
    k = n ^ e → ∃ (o : Type) (_ : CommRing o) (b : _root_.GlobalTheory.ZM.TBase o k) (em : o →+* ℂ)
      (j : o →+* _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p k), _root_.GlobalTheory.ZM.ArBase em ∧ j (b.ζ : o) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zetaZP p k ∧
      (∀ x, ((j x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p k) : ℂ) = em x) ∧
      ∀ (K : Type) [Field K] (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p k)), y = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt y := by
  intro n e p k hn hp hnp _ hk
  subst hk
  have hN : n ^ e ≠ 0 := pow_ne_zero _ hn.ne_zero
  haveI : NeZero (n ^ e) := ⟨hN⟩
  haveI := _root_.GlobalTheory.ZM.CycBase.cyc (k := n ^ e)
  haveI : NumberField (_root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) :=
    IsCyclotomicExtension.numberField {n ^ e} ℚ _
  have hcop : n.Coprime p := (Nat.coprime_primes hn hp).mpr hnp
  set F := _root_.GlobalTheory.ZM.CycBase.CF (n ^ e) with hF
  obtain ⟨em, har, hcomp⟩ :=
    _root_.GlobalTheory.ZM.exists_arBase_away (F := F) F.val.toRingHom hn.ne_zero
  have hζ := _root_.GlobalTheory.ZM.CycBase.zF_prim hN
  have hζi := hζ.toInteger_isPrimitiveRoot
  have hpos : 0 < n ^ e := Nat.pos_of_ne_zero hN
  let u : (𝓞 F)ˣ := (hζi.isUnit hN).unit
  let ζo : (Localization.Away (n : 𝓞 F))ˣ := Units.map (algebraMap (𝓞 F) _).toMonoidHom u
  have hkunit : IsUnit ((n ^ e : ℕ) : Localization.Away (n : 𝓞 F)) := by
    have := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (n : 𝓞 F))
      (n : 𝓞 F)).pow e
    simpa using this
  have hprim : ∀ (K : Type) [Field K] (β : Localization.Away (n : 𝓞 F) →+* K),
      IsPrimitiveRoot (β ζo) (n ^ e) := by
    intro K _ β
    have hroot := (hζi.isRoot_cyclotomic hpos).map (f := β.comp (algebraMap (𝓞 F) _))
    rw [Polynomial.map_cyclotomic] at hroot
    haveI : NeZero ((n ^ e : ℕ) : K) := ⟨by simpa using (hkunit.map β).ne_zero⟩
    exact Polynomial.isRoot_cyclotomic_iff.mp hroot
  let b : _root_.GlobalTheory.ZM.TBase (Localization.Away (n : 𝓞 F)) (n ^ e) := ⟨ζo, hkunit, hprim⟩
  have hcompx : ∀ a : 𝓞 F, em (algebraMap _ _ a) = ((a : F) : ℂ) := fun a =>
    RingHom.congr_fun hcomp a
  have hmemZ : ∀ x, em x ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e) := by
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (n : 𝓞 F)) x
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hspec := congrArg em (IsLocalization.mk'_spec (Localization.Away (n : 𝓞 F)) a s)
    rw [map_mul, hcompx, hcompx, ← hm] at hspec
    have hnm : (((((n : 𝓞 F) ^ m : 𝓞 F)) : F) : ℂ) = (n : ℂ) ^ m := by simp
    rw [hnm] at hspec
    have hn0 : (n : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne_zero)
    rw [eq_div_of_mul_eq hn0 hspec, div_eq_mul_inv, ← inv_pow]
    exact mul_mem (_root_.GlobalTheory.ZM.CycBase.mem_ZP p n e hn a)
      (pow_mem (inv_natCast_mem_ZP_of_coprime hcop) m)
  refine ⟨Localization.Away (n : 𝓞 F), inferInstance, b, em, em.codRestrict _ hmemZ, har, ?_,
    fun x => rfl, ?_⟩
  · apply Subtype.ext
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zetaZP
    change em (algebraMap (𝓞 F) _ hζ.toInteger) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n ^ e)
    rw [hcompx]
    exact congrArg Subtype.val hζ.coe_toInteger
  · intro K _ y
    exact spec_dualNumber_hom_ZP_eq_constPt hcop hn.ne_zero y
end _root_.GlobalTheory.ZM.CycBase
end GlobalTheory.ZM.CycBase
