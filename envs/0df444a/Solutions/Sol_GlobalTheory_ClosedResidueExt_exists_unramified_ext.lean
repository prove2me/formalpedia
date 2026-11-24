-- Prove2me | solution 1 for GlobalTheory.ClosedResidueExt.exists_unramified_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:32.229889+00:00
-- url     : https://prove2.me/submissions/efe36663-a9fe-4059-8b9e-3bdc0b754b48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.ClosedResidueExt
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]
open Polynomial IsLocalRing in
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω] in
private lemma exists_maximal_unram_subalgebra (π : W) (h0 : _root_.GlobalTheory.ClosedResidueExt.Unram π (⊥ : Subalgebra W Ω)) :
    ∃ M : Subalgebra W Ω, _root_.GlobalTheory.ClosedResidueExt.Unram π M ∧
      ∀ N, _root_.GlobalTheory.ClosedResidueExt.Unram π N → M ≤ N → N = M := by
  obtain ⟨M, -, hM⟩ := zorn_le_nonempty₀ {R : Subalgebra W Ω | _root_.GlobalTheory.ClosedResidueExt.Unram π R}
    (fun c hc hchain y hy => by
    have hne : Nonempty c := ⟨⟨y, hy⟩⟩
    have hd : Directed (· ≤ ·) (fun R : c => (R : Subalgebra W Ω)) := hchain.directed
    have hmem : ∀ x ∈ ⨆ R : c, (R : Subalgebra W Ω), ∃ R : c, x ∈ (R : Subalgebra W Ω) := fun x hx => by
      have : x ∈ (↑(⨆ R : c, (R : Subalgebra W Ω)) : Set Ω) := hx
      rw [Subalgebra.coe_iSup_of_directed hd, Set.mem_iUnion] at this
      exact this
    refine ⟨⨆ R : c, (R : Subalgebra W Ω), ⟨fun x hx => ?_, fun hx => ?_, fun x hx hx0 => ?_⟩,
      fun R hR => le_iSup (fun R : c => (R : Subalgebra W Ω)) ⟨R, hR⟩⟩
    · obtain ⟨R, hR⟩ := hmem x hx
      exact (hc R.2).1 x hR
    · obtain ⟨R, hR⟩ := hmem _ hx
      exact (hc R.2).2.1 hR
    · obtain ⟨R, hR⟩ := hmem x hx
      obtain ⟨n, u, hu, hu', e⟩ := (hc R.2).2.2 x hR hx0
      exact ⟨n, u, le_iSup (fun R : c => (R : Subalgebra W Ω)) R hu,
        le_iSup (fun R : c => (R : Subalgebra W Ω)) R hu', e⟩) ⊥ h0
  exact ⟨M, hM.prop, fun N hN hle => (hM.eq_of_le hN hle).symm⟩
open Polynomial IsLocalRing in
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω] in
private lemma isUnit_of_inv_mem_of_ne_zero {M : Subalgebra W Ω}
    (a : M) (ha : (a : Ω)⁻¹ ∈ M) (ha0 : (a : Ω) ≠ 0) : IsUnit a :=
  have h : a * ⟨_, ha⟩ = 1 := Subtype.ext (by simp [mul_inv_cancel₀ ha0])
  ⟨⟨a, ⟨_, ha⟩, h, by rw [mul_comm]; exact h⟩, rfl⟩
open Polynomial IsLocalRing in
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω] in
private lemma irreducible_and_associated_pow_of_unram {π : W}
    (M : Subalgebra W Ω) (hM : _root_.GlobalTheory.ClosedResidueExt.Unram π M) :
    Irreducible (algebraMap W M π) ∧ ∀ x : M, x ≠ 0 → ∃ n : ℕ, Associated (algebraMap W M π ^ n) x := by
  obtain ⟨-, hinv, hfac⟩ := hM
  have hp0 : algebraMap W Ω π ≠ 0 := by
    intro h
    rw [h, inv_zero] at hinv
    exact hinv M.zero_mem
  have hcoe : ((algebraMap W M π : M) : Ω) = algebraMap W Ω π := rfl
  have unit_of : ∀ (a : M) (u : Ω), u⁻¹ ∈ M → (a : Ω) = u → u ≠ 0 → IsUnit a := fun a u hu' e hu0 =>
    isUnit_of_inv_mem_of_ne_zero a (e ▸ hu') (e ▸ hu0)
  refine ⟨⟨fun hu => ?_, fun a b hab => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := hu.exists_right_inv
    have hy' : (y : Ω) = (algebraMap W Ω π)⁻¹ := by
      have := congrArg Subtype.val hy
      simp only [MulMemClass.coe_mul, hcoe, OneMemClass.coe_one] at this
      exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact this)
    exact hinv (hy' ▸ y.2)
  · have hab' : algebraMap W Ω π = (a : Ω) * b := by
      have := congrArg Subtype.val hab
      simpa using this
    have ha0 : (a : Ω) ≠ 0 := fun h => hp0 (by rw [hab', h, zero_mul])
    have hb0 : (b : Ω) ≠ 0 := fun h => hp0 (by rw [hab', h, mul_zero])
    obtain ⟨i, u, hu, hu', ea⟩ := hfac a a.2 ha0
    obtain ⟨j, v, hv, hv', eb⟩ := hfac b b.2 hb0
    have hu0 : u ≠ 0 := fun h => ha0 (by rw [ea, h, mul_zero])
    have hv0 : v ≠ 0 := fun h => hb0 (by rw [eb, h, mul_zero])
    rcases i with _ | i
    · exact Or.inl (unit_of a u hu' (by rw [ea, pow_zero, one_mul]) hu0)
    rcases j with _ | j
    · exact Or.inr (unit_of b v hv' (by rw [eb, pow_zero, one_mul]) hv0)
    exfalso
    apply hinv
    have key : (algebraMap W Ω π)⁻¹ = algebraMap W Ω π ^ (i + j) * u * v := by
      apply inv_eq_of_mul_eq_one_right
      apply mul_left_cancel₀ hp0
      rw [mul_one]
      calc algebraMap W Ω π * (algebraMap W Ω π * (algebraMap W Ω π ^ (i + j) * u * v))
          = algebraMap W Ω π ^ (i + 1) * u * (algebraMap W Ω π ^ (j + 1) * v) := by ring
        _ = algebraMap W Ω π := by rw [← ea, ← eb, hab']
    rw [key]
    exact M.mul_mem (M.mul_mem (M.pow_mem (M.algebraMap_mem π) _) hu) hv
  · have hx0 : (x : Ω) ≠ 0 := fun h => hx (Subtype.ext h)
    obtain ⟨n, u, hu, hu', e⟩ := hfac x x.2 hx0
    have hu0 : u ≠ 0 := fun h => hx0 (by rw [e, h, mul_zero])
    obtain ⟨U, hU⟩ := unit_of ⟨u, hu⟩ u hu' rfl hu0
    refine ⟨n, ⟨U, Subtype.ext ?_⟩⟩
    simp [hU, e]
open Polynomial IsLocalRing in
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω] in
private lemma isUnit_one_add_algebraMap_mul_of_not_isUnit [IsLocalRing W] {π : W} (hπ : ¬ IsUnit π)
    (N : Subalgebra W Ω) (hN : ∀ x ∈ N, IsIntegral W x) (h : N) : IsUnit (1 + algebraMap W N π * h) := by
  by_contra hu
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {1 + algebraMap W N π * h})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  haveI : Algebra.IsIntegral W N :=
    ⟨fun x => (isIntegral_algHom_iff N.val Subtype.val_injective).1 (hN x x.2)⟩
  have hmax : (m.comap (algebraMap W N)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  have hc : m.comap (algebraMap W N) = IsLocalRing.maximalIdeal W := IsLocalRing.eq_maximalIdeal hmax
  have hπm : algebraMap W N π ∈ m := by
    rw [← Ideal.mem_comap, hc]; exact hπ
  have h1 : 1 + algebraMap W N π * h ∈ m := hle (Ideal.subset_span rfl)
  exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem h1 (m.mul_mem_right h hπm)))
open Polynomial IsLocalRing in
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω] in
private lemma eq_pow_mul_unit_of_mem_adjoin [IsLocalRing W] {π : W}
    (hπ : ¬ IsUnit π) (M : Subalgebra W Ω) [WfDvdMonoid M] {k : Type} [Field k] (φ : M →+* k)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span {algebraMap W M π}) (f : M[X])
    (hf : f.Monic) (hirr : Irreducible (f.map φ)) (α : Ω) (hα : aeval α f = 0)
    (hN : ∀ x ∈ (Algebra.adjoin M {α}).restrictScalars W, IsIntegral W x) :
    ∀ x ∈ (Algebra.adjoin M {α}).restrictScalars W, x ≠ 0 → ∃ (n : ℕ) (u : Ω),
      u ∈ (Algebra.adjoin M {α}).restrictScalars W ∧ u⁻¹ ∈ (Algebra.adjoin M {α}).restrictScalars W ∧
      x = algebraMap W Ω π ^ n * u := by
  set N := (Algebra.adjoin M {α}).restrictScalars W with hNdef
  have memN : ∀ g : M[X], aeval α g ∈ N := fun g => by
    show aeval α g ∈ Algebra.adjoin M {α}
    rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨g, rfl⟩
  intro x hx hx0
  have hx' : x ∈ Algebra.adjoin M {α} := hx
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨g0, rfl⟩ := hx'
  change aeval α g0 ≠ 0 at hx0
  show ∃ (n : ℕ) (u : Ω), u ∈ N ∧ u⁻¹ ∈ N ∧ aeval α g0 = algebraMap W Ω π ^ n * u
  have hf1 : f ≠ 1 := by
    rintro rfl
    exact hirr.not_isUnit (by simp)
  set g := g0 %ₘ f with hgdef
  have hg : aeval α g = aeval α g0 := by
    conv_rhs => rw [← modByMonic_add_div g0 f]
    simp [hgdef, hα]
  have hgdeg : g.natDegree < f.natDegree := natDegree_modByMonic_lt g0 hf hf1
  have hg0 : g ≠ 0 := by
    intro h
    apply hx0
    rw [← hg, h, map_zero]
  have hπM : algebraMap W M π ∈ RingHom.ker φ := hker ▸ Ideal.subset_span rfl
  have hπC : ¬ IsUnit (C (algebraMap W M π)) := by
    rw [Polynomial.isUnit_C]
    intro hu
    exact (RingHom.ker_ne_top φ) (Ideal.eq_top_of_isUnit_mem _ hπM hu)
  obtain ⟨n, g1, hndvd, hgeq⟩ := WfDvdMonoid.max_power_factor' hg0 hπC
  have hmap1 : g1.map φ ≠ 0 := by
    intro h0
    apply hndvd
    have : g1 ∈ RingHom.ker (mapRingHom φ) := h0
    rw [Polynomial.ker_mapRingHom, hker, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at this
    exact this
  have hg1ne : g1 ≠ 0 := by
    rintro rfl
    exact hg0 (by rw [hgeq, mul_zero])
  have hpne : (C (algebraMap W M π)) ^ n ≠ 0 := by
    intro h
    exact hg0 (by rw [hgeq, h, zero_mul])
  have hdeg1 : g1.natDegree ≤ g.natDegree := by
    rw [hgeq, natDegree_mul hpne hg1ne]; omega
  have hndvdp : ¬ f.map φ ∣ g1.map φ := by
    intro hd
    have h1 := natDegree_le_of_dvd hd hmap1
    rw [hf.natDegree_map] at h1
    have h2 := natDegree_map_le (f := φ) (p := g1)
    omega
  obtain ⟨a, b, hab⟩ := (hirr.coprime_iff_not_dvd).2 hndvdp
  obtain ⟨A, rfl⟩ := Polynomial.map_surjective φ hφ a
  obtain ⟨B, rfl⟩ := Polynomial.map_surjective φ hφ b
  have hker2 : A * f + B * g1 - 1 ∈ RingHom.ker (mapRingHom φ) := by
    rw [RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_one, hab, sub_self]
  rw [Polynomial.ker_mapRingHom, hker, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hker2
  obtain ⟨H, hH⟩ := hker2
  have hev : aeval α B * aeval α g1 = 1 + algebraMap W Ω π * aeval α H := by
    have h := congrArg (aeval α) hH
    simp only [map_sub, map_add, map_mul, map_one, hα, mul_zero, zero_add, aeval_C] at h
    rw [IsScalarTower.algebraMap_apply W M Ω]
    linear_combination h
  obtain ⟨v, hvN, hv⟩ : ∃ v ∈ N, v * (1 + algebraMap W Ω π * aeval α H) = 1 := by
    obtain ⟨w, hw⟩ := (isUnit_one_add_algebraMap_mul_of_not_isUnit hπ N hN ⟨aeval α H, memN H⟩).exists_left_inv
    refine ⟨w, w.2, ?_⟩
    have := congrArg Subtype.val hw
    simpa using this
  refine ⟨n, aeval α g1, memN g1, ?_, ?_⟩
  · have hinv : (aeval α g1)⁻¹ = v * aeval α B := by
      apply inv_eq_of_mul_eq_one_right
      linear_combination v * hev + hv
    rw [hinv]
    exact N.mul_mem hvN (memN B)
  · rw [← hg, hgeq, map_mul, map_pow, aeval_C, IsScalarTower.algebraMap_apply W M Ω]
end GlobalTheory.ClosedResidueExt
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedResidueExt
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]
namespace GlobalTheory.ClosedResidueExt
namespace _root_.GlobalTheory.ClosedResidueExt
theorem _root_.solution (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : Algebra W R), Function.Injective (algebraMap W R) ∧ Algebra.IsIntegral W R ∧
        Irreducible (algebraMap W R π) ∧ IsAlgClosed (ResidueField R) := by
  let Ω := AlgebraicClosure (FractionRing W)
  have hinj : Function.Injective (algebraMap W Ω) := by
    rw [IsScalarTower.algebraMap_eq W (FractionRing W) Ω]
    exact (algebraMap (FractionRing W) Ω).injective.comp (IsFractionRing.injective W (FractionRing W))
  have hπu : ¬ IsUnit π := hπ.not_isUnit
  have h0 : _root_.GlobalTheory.ClosedResidueExt.Unram π (⊥ : Subalgebra W Ω) := by
    refine ⟨fun x hx => ?_, fun hx => ?_, fun x hx hx0 => ?_⟩
    · obtain ⟨w, rfl⟩ := Algebra.mem_bot.1 hx
      exact isIntegral_algebraMap
    · obtain ⟨w, hw⟩ := Algebra.mem_bot.1 hx
      apply hπu
      have hp0 : algebraMap W Ω π ≠ 0 := fun h => hπ.ne_zero (hinj (by rw [h, map_zero]))
      have h1 : π * w = 1 := hinj (by rw [map_mul, hw, map_one, mul_inv_cancel₀ hp0])
      exact ⟨⟨π, w, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
    · obtain ⟨w, rfl⟩ := Algebra.mem_bot.1 hx
      have hw0 : w ≠ 0 := fun h => hx0 (by rw [h, map_zero])
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hπ
      have hinv : (algebraMap W Ω (u : W))⁻¹ = algebraMap W Ω ((u⁻¹ : Wˣ) : W) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← map_mul, Units.mul_inv, map_one]
      refine ⟨n, algebraMap W Ω u, Subalgebra.algebraMap_mem _ _, ?_, ?_⟩
      · rw [hinv]; exact Subalgebra.algebraMap_mem _ _
      · rw [hu, map_mul, map_pow, mul_comm]
  obtain ⟨M, hM, hmax⟩ := exists_maximal_unram_subalgebra π h0
  obtain ⟨hirrM, hfacM⟩ := irreducible_and_associated_pow_of_unram M hM
  haveI : IsDiscreteValuationRing M :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirrM, fun {x} hx => hfacM x hx⟩
  haveI hint : Algebra.IsIntegral W M :=
    ⟨fun x => (isIntegral_algHom_iff M.val Subtype.val_injective).1 (hM.1 x x.2)⟩
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, ?_, hint, hirrM, ?_⟩
  · intro a b hab
    exact hinj (congrArg Subtype.val hab)
  refine IsAlgClosed.of_exists_root _ fun p hpm hpirr => ?_
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (IsLocalRing.residue M) IsLocalRing.residue_surjective p
  obtain ⟨f, hfp, hfnat, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts p).2 ⟨q, hq⟩) hpm
  have hfdeg : f.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hfm.ne_zero, hfnat]
    exact_mod_cast (Polynomial.natDegree_pos_iff_degree_pos.2
      (Polynomial.degree_pos_of_irreducible hpirr)).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero Ω f hfdeg
  have hαi : IsIntegral M α := ⟨f, hfm, hα⟩
  have hNint : ∀ x ∈ (Algebra.adjoin M {α}).restrictScalars W, IsIntegral W x := fun x hx =>
    isIntegral_trans x (by
      have := adjoin_le_integralClosure hαi hx
      exact this)
  have hker : RingHom.ker (IsLocalRing.residue M) = Ideal.span {algebraMap W M π} := by
    rw [IsLocalRing.ker_residue]
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirrM
  have hirr' : Irreducible (f.map (IsLocalRing.residue M)) := hfp ▸ hpirr
  have hp0 : algebraMap W Ω π ≠ 0 := by
    intro h
    apply hM.2.1
    rw [h, inv_zero]
    exact M.zero_mem
  have hNU : _root_.GlobalTheory.ClosedResidueExt.Unram π ((Algebra.adjoin M {α}).restrictScalars W) := by
    refine ⟨hNint, fun hx => ?_, eq_pow_mul_unit_of_mem_adjoin hπu M (IsLocalRing.residue M)
      IsLocalRing.residue_surjective hker f hfm hirr' α hα hNint⟩
    have hu := isUnit_one_add_algebraMap_mul_of_not_isUnit hπu _ hNint ⟨-(algebraMap W Ω π)⁻¹, Subalgebra.neg_mem _ hx⟩
    have hz : (1 + algebraMap W ((Algebra.adjoin M {α}).restrictScalars W) π *
        ⟨-(algebraMap W Ω π)⁻¹, Subalgebra.neg_mem _ hx⟩ : (Algebra.adjoin M {α}).restrictScalars W) = 0 :=
      Subtype.ext (by
        show (1 : Ω) + algebraMap W Ω π * -(algebraMap W Ω π)⁻¹ = 0
        rw [mul_neg, mul_inv_cancel₀ hp0, add_neg_cancel])
    rw [hz] at hu
    exact not_isUnit_zero hu
  have hle : M ≤ (Algebra.adjoin M {α}).restrictScalars W := fun x hx =>
    Subalgebra.algebraMap_mem (Algebra.adjoin M {α}) (⟨x, hx⟩ : M)
  have hNM := hmax _ hNU hle
  have hαM : α ∈ M := hNM ▸ (Algebra.self_mem_adjoin_singleton M α : α ∈ Algebra.adjoin M {α})
  refine ⟨IsLocalRing.residue M ⟨α, hαM⟩, ?_⟩
  have hev : Polynomial.eval (⟨α, hαM⟩ : M) f = 0 := by
    have h := hα
    rw [show α = algebraMap M Ω ⟨α, hαM⟩ from rfl, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at h
    exact Subtype.ext h
  rw [← hfp, Polynomial.eval_map, Polynomial.eval₂_hom, hev, map_zero]
end _root_.GlobalTheory.ClosedResidueExt
end GlobalTheory.ClosedResidueExt
