-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:38.400251+00:00
-- url     : https://prove2.me/submissions/f6cc7f7d-8592-4fb2-a87e-a98426da9253

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Theorems.Thm_GlobalTheory_UnitLemma_UnramNorm_cO_spec
import Theorems.Thm_GlobalTheory_UnitLemma_UnramNorm_val_c
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.UnitLemma.UnramNorm
open IsLocalRing Polynomial
variable (K : UQ)
open IsLocalRing Polynomial in
variable (K : _root_.GlobalTheory.UnitLemma.UQ) in
private theorem cO_cO' (x : K.O) :
    _root_.GlobalTheory.UnitLemma.UnramNorm.cO K (_root_.GlobalTheory.UnitLemma.UnramNorm.cO K x) = x :=
  _root_.GlobalTheory.UnitLemma.UnramNorm.alg_inj K (by
    rw [_root_.GlobalTheory.UnitLemma.UnramNorm.cO_spec, _root_.GlobalTheory.UnitLemma.UnramNorm.cO_spec, K.c_c])
open IsLocalRing Polynomial in
variable (K : _root_.GlobalTheory.UnitLemma.UQ) in
private theorem isUnit_iff_notMem_maximalIdeal {x : K.O} : IsUnit x ↔ x ∉ maximalIdeal K.O := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
open IsLocalRing Polynomial in
variable (K : _root_.GlobalTheory.UnitLemma.UQ) in
private theorem exists_mul_apply_eq_of_fixed_involution {F : Type} [Field F] [Finite F] (σ : F ≃+* F)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (u : F) (hu : u ≠ 0) (hfix : σ u = u) :
    ∃ z, z * σ z = u := by
  classical
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  have hcomm : ∀ r : ZMod (ringChar F), σ (algebraMap (ZMod (ringChar F)) F r) =
      algebraMap (ZMod (ringChar F)) F r := fun r =>
    congrArg (· r) (RingHom.ext_zmod ((σ : F →+* F).comp (algebraMap _ _)) (algebraMap _ _))
  let τ : F ≃ₐ[ZMod (ringChar F)] F := AlgEquiv.ofRingEquiv (f := σ) hcomm
  have hτ : τ ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    intro h
    exact hx (by simpa [τ] using congrArg (fun g : F ≃ₐ[ZMod (ringChar F)] F => g x) h)
  have hτ2 : τ ^ 2 = 1 := by
    ext x
    simp [τ, pow_two, hσ]
  have hord : orderOf τ = 2 := orderOf_eq_prime hτ2 hτ
  let k0 := IntermediateField.fixedField (Subgroup.zpowers τ)
  haveI : FiniteDimensional (ZMod (ringChar F)) F := Module.Finite.of_finite
  have hrank : Module.finrank k0 F = 2 := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hord]
  have hmem : ∀ x : F, σ x = x → x ∈ k0 := by
    intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have : Subgroup.zpowers τ ≤ MulAction.stabilizer (F ≃ₐ[ZMod (ringChar F)] F) x :=
      Subgroup.zpowers_le.mpr (by simpa [MulAction.mem_stabilizer_iff, τ] using hx)
    exact this hg
  let τ0 : F ≃ₐ[k0] F := AlgEquiv.ofRingEquiv (f := σ) (fun x => by
    have := (IntermediateField.mem_fixedField_iff _ _).mp x.2 τ (Subgroup.mem_zpowers τ)
    simpa [τ] using this)
  have hτ0 : (1 : F ≃ₐ[k0] F) ≠ τ0 := by
    obtain ⟨x, hx⟩ := hne
    intro h
    exact hx (by simpa [τ0] using (congrArg (fun g : F ≃ₐ[k0] F => g x) h).symm)
  have huniv : (Finset.univ : Finset (F ≃ₐ[k0] F)) = {1, τ0} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, Finset.card_pair hτ0, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank, hrank]
  obtain ⟨z, hz⟩ := FiniteField.norm_surjective (K := k0) (K' := F) ⟨u, hmem u hfix⟩
  refine ⟨z, ?_⟩
  have := Algebra.norm_eq_prod_automorphisms k0 z
  rw [huniv, Finset.prod_pair hτ0, hz] at this
  simpa [τ0] using this.symm
open IsLocalRing Polynomial in
variable (K : _root_.GlobalTheory.UnitLemma.UQ) in
private theorem exists_add_mul_cO_notMem_maximalIdeal (e : K.O) :
    ∃ t : K.O, t + e * _root_.GlobalTheory.UnitLemma.UnramNorm.cO K t ∉ maximalIdeal K.O := by
  by_contra h
  push_neg at h
  obtain ⟨x, y, hxy, hm⟩ := K.c_res
  have hy : _root_.GlobalTheory.UnitLemma.UnramNorm.cO K x = y := _root_.GlobalTheory.UnitLemma.UnramNorm.alg_inj K
    (by rw [_root_.GlobalTheory.UnitLemma.UnramNorm.cO_spec, hxy])
  have h1 := h 1
  have hx := h x
  rw [map_one, mul_one] at h1
  rw [hy] at hx
  apply hm
  have : x - y = (x + e * y) - (1 + e) * y := by ring
  rw [this]
  exact Ideal.sub_mem _ hx (Ideal.mul_mem_right _ _ h1)
end GlobalTheory.UnitLemma.UnramNorm
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnramNorm
open IsLocalRing Polynomial
variable (K : UQ)
open IsLocalRing Polynomial
variable (K : _root_.GlobalTheory.UnitLemma.UQ)
namespace GlobalTheory.UnitLemma.UnramNorm
namespace _root_.GlobalTheory.UnitLemma.UnramNorm
theorem _root_.solution :
    ∀ (K : _root_.GlobalTheory.UnitLemma.UQ), (∀ u : K.Oˣ, K.c (algebraMap K.O K.E u) = algebraMap K.O K.E u →
    ∃ z : K.Oˣ, algebraMap K.O K.E u = algebraMap K.O K.E z * K.c (algebraMap K.O K.E z)) ∧
    (∃ z : K.O, algebraMap K.O K.E z + K.c (algebraMap K.O K.E z) = 1) ∧
    (∃ ϖ : K.O, Irreducible ϖ ∧ K.c (algebraMap K.O K.E ϖ) = algebraMap K.O K.E ϖ) ∧
    ∀ x : K.E, _root_.GlobalTheory.UnitLemma.val K.O (K.c x) = _root_.GlobalTheory.UnitLemma.val K.O x := by
  intro K
  set σ := _root_.GlobalTheory.UnitLemma.UnramNorm.cO K
  have hσσ : ∀ x, σ (σ x) = x := cO_cO' K
  have hspec : ∀ x, K.c (algebraMap K.O K.E x) = algebraMap K.O K.E (σ x) := fun x =>
    (_root_.GlobalTheory.UnitLemma.UnramNorm.cO_spec K x).symm
  have hσm : ∀ x, x ∈ maximalIdeal K.O → σ x ∈ maximalIdeal K.O := by
    intro x hx
    rw [← not_not (a := σ x ∈ _), ← isUnit_iff_notMem_maximalIdeal, isUnit_map_iff σ, isUnit_iff_notMem_maximalIdeal, not_not]
    exact hx
  refine ⟨?_, ?_, ?_, _root_.GlobalTheory.UnitLemma.UnramNorm.val_c K⟩
  · intro u hu
    have hσu : σ u = u := _root_.GlobalTheory.UnitLemma.UnramNorm.alg_inj K (by rw [← hspec, hu])
    have hres : ∀ x, ResidueField.mapEquiv σ (residue K.O x) = residue K.O (σ x) := fun x => rfl
    have hσb : ∀ x, ResidueField.mapEquiv σ (ResidueField.mapEquiv σ x) = x := by
      intro x
      obtain ⟨y, rfl⟩ := residue_surjective x
      rw [hres, hres, hσσ]
    have hne : ∃ x, ResidueField.mapEquiv σ x ≠ x := by
      obtain ⟨x, y, hxy, hm⟩ := K.c_res
      have hy : σ x = y := _root_.GlobalTheory.UnitLemma.UnramNorm.alg_inj K (by rw [← hspec, hxy])
      refine ⟨residue K.O x, ?_⟩
      rw [hres, hy]
      intro h
      apply hm
      rw [← residue_eq_zero_iff, map_sub, h, sub_self]
    have hu0 : residue K.O (u : K.O) ≠ 0 := by
      rw [ne_eq, residue_eq_zero_iff, ← isUnit_iff_notMem_maximalIdeal K] at *
      simp [u.isUnit]
    obtain ⟨zb, hzb⟩ := exists_mul_apply_eq_of_fixed_involution (ResidueField.mapEquiv σ) hσb hne _ hu0
      (by rw [hres, hσu])
    obtain ⟨z0, rfl⟩ := residue_surjective zb
    rw [hres, ← map_mul] at hzb
    have hN : z0 * σ z0 - u ∈ maximalIdeal K.O := by
      rw [← residue_eq_zero_iff, map_sub, hzb, sub_self]
    have hz0 : IsUnit z0 := by
      rw [isUnit_iff_notMem_maximalIdeal K, ← residue_eq_zero_iff]
      intro h
      rw [map_mul, h, zero_mul] at hzb
      exact hu0 hzb.symm
    obtain ⟨t, ht⟩ := exists_add_mul_cO_notMem_maximalIdeal K 1
    rw [one_mul] at ht
    have ha1 := (isUnit_iff_notMem_maximalIdeal K).mpr ht
    have htu : IsUnit t := by
      rw [isUnit_iff_notMem_maximalIdeal K]
      intro h
      exact ht (Ideal.add_mem _ h (hσm t h))
    obtain ⟨w0, hw0⟩ : ∃ w, z0 * w = 1 := ⟨↑hz0.unit⁻¹, hz0.mul_val_inv⟩
    set e0 := σ t * σ w0 with he0
    have hz0e0 : z0 * σ e0 = t := by
      rw [he0, map_mul, hσσ, hσσ, mul_left_comm, hw0, mul_one]
    have he0z0 : e0 * σ z0 = σ t := by
      rw [he0, mul_assoc, ← map_mul, mul_comm w0, hw0, map_one, mul_one]
    have he0u : IsUnit e0 := by
      rw [he0]
      refine (htu.map σ).mul (IsUnit.map σ (⟨⟨w0, z0, by rw [mul_comm]; exact hw0, hw0⟩, rfl⟩ : IsUnit w0))
    have ha2 : IsUnit (e0 * σ e0) := he0u.mul (he0u.map σ)
    obtain ⟨i2, hi2⟩ : ∃ i, e0 * σ e0 * i = 1 := ⟨↑ha2.unit⁻¹, ha2.mul_val_inv⟩
    have hi2u : IsUnit i2 := ⟨⟨i2, e0 * σ e0, by rw [mul_comm]; exact hi2, hi2⟩, rfl⟩
    set f : K.O[X] := X ^ 2 + C ((t + σ t) * i2) * X + C ((z0 * σ z0 - u) * i2) with hf
    have hfm : f.Monic := by rw [hf]; monicity!
    obtain ⟨X0, hroot, hX0⟩ := HenselianRing.is_henselian (I := maximalIdeal K.O) f hfm 0
      (by simpa [hf] using Ideal.mul_mem_right _ _ hN)
      (by
        have hd : (derivative f).eval 0 = (t + σ t) * i2 := by
          rw [hf]; simp; first | done | rfl | ring
        rw [hd]; exact (ha1.mul hi2u).map _)
    rw [sub_zero] at hX0
    have hE : e0 * σ e0 * X0 ^ 2 + (t + σ t) * X0 + (z0 * σ z0 - u) = 0 := by
      have h := hroot
      simp only [IsRoot, hf, eval_add, eval_mul, eval_C, eval_X, eval_pow] at h
      linear_combination e0 * σ e0 * h - ((t + σ t) * X0 + (z0 * σ z0 - u)) * hi2
    have hE' : e0 * σ e0 * σ X0 ^ 2 + (t + σ t) * σ X0 + (z0 * σ z0 - u) = 0 := by
      have h := congrArg σ hE
      simp only [map_add, map_mul, map_pow, map_zero, map_sub, hσσ, hσu] at h
      linear_combination h
    have hfix : σ X0 = X0 := by
      have hprod : (X0 - σ X0) * (e0 * σ e0 * (X0 + σ X0) + (t + σ t)) = 0 := by
        linear_combination hE - hE'
      have hunit : IsUnit (e0 * σ e0 * (X0 + σ X0) + (t + σ t)) := by
        rw [isUnit_iff_notMem_maximalIdeal K]
        intro h
        apply ht
        have : t + σ t = (e0 * σ e0 * (X0 + σ X0) + (t + σ t)) - e0 * σ e0 * (X0 + σ X0) := by ring
        rw [this]
        exact Ideal.sub_mem _ h (Ideal.mul_mem_left _ _ (Ideal.add_mem _ hX0 (hσm _ hX0)))
      have := (mul_eq_zero.mp hprod).resolve_right hunit.ne_zero
      exact (sub_eq_zero.mp this).symm
    have hnorm : (z0 + X0 * e0) * σ (z0 + X0 * e0) = u := by
      rw [map_add, map_mul, hfix]
      linear_combination hE + X0 * hz0e0 + X0 * he0z0
    have hzu : IsUnit (z0 + X0 * e0) := isUnit_of_mul_isUnit_left (hnorm ▸ u.isUnit)
    refine ⟨hzu.unit, ?_⟩
    rw [IsUnit.unit_spec, hspec, ← map_mul, hnorm]
  · obtain ⟨t, ht⟩ := exists_add_mul_cO_notMem_maximalIdeal K 1
    rw [one_mul] at ht
    have hs := (isUnit_iff_notMem_maximalIdeal K).mpr ht
    set s := t + σ t
    have hσs : σ s = s := by simp only [s, map_add, hσσ, add_comm]
    obtain ⟨w, hws⟩ : ∃ w, w * s = 1 := ⟨↑hs.unit⁻¹, hs.val_inv_mul⟩
    refine ⟨t * w, ?_⟩
    rw [hspec, ← map_add, ← map_one (algebraMap K.O K.E)]
    congr 1
    have hz : t * w * s = t := by rw [mul_assoc, hws, mul_one]
    have hz' : σ (t * w) * s = σ t := by
      rw [← hσs, ← map_mul, hz]
    have : (t * w + σ (t * w)) * s = 1 * s := by
      rw [add_mul, hz, hz', one_mul]
    exact hs.mul_left_injective this
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
    have hcϖ : Irreducible (σ ϖ) := (MulEquiv.irreducible_iff σ.toMulEquiv).mpr hϖ
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_of_irreducible K.O hϖ hcϖ
    obtain ⟨t, ht⟩ := exists_add_mul_cO_notMem_maximalIdeal K (e : K.O)
    have hw := (isUnit_iff_notMem_maximalIdeal K).mpr ht
    refine ⟨ϖ * t + σ (ϖ * t), ?_, ?_⟩
    · have : ϖ * t + σ (ϖ * t) = ϖ * (t + ↑e * σ t) := by
        rw [map_mul, ← he]; ring
      rw [this]
      exact (irreducible_mul_isUnit hw).mpr hϖ
    · rw [hspec]
      congr 1
      rw [map_add, hσσ, add_comm]
end _root_.GlobalTheory.UnitLemma.UnramNorm
end GlobalTheory.UnitLemma.UnramNorm
