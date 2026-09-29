-- Prove2me | solution 1 for IsLocalRing.ringHom_eq_of_forall_sub_mem_maximalIdeal_of_maximalIdeal_eq_map_of_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e85faaf4-5d3e-5aa2-a987-bbb299a27e25

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_ringHom_eq_of_forall_sub_mem_maximalIdeal_of_maximalIdeal_eq_map_of_isSeparable

set_option autoImplicit false

universe u v w

open IsLocalRing Polynomial

namespace UnramifiedRigidity

variable {A₀ : Type u} {W₀ : Type v} {C : Type w}
  [CommRing A₀] [IsLocalRing A₀] [CommRing W₀] [HenselianLocalRing W₀]
  [Algebra A₀ W₀] [IsLocalHom (algebraMap A₀ W₀)]
  [CommRing C] [IsLocalRing C]

lemma root_eq_of_sub_mem (f : C[X]) (b₁ b₂ : C) (h₁ : f.eval b₁ = 0) (h₂ : f.eval b₂ = 0)
    (hu : IsUnit (f.derivative.eval b₁)) (hδ : b₂ - b₁ ∈ maximalIdeal C) : b₁ = b₂ := by
  obtain ⟨k, hk⟩ := f.binomExpansion b₁ (b₂ - b₁)
  have hb : b₁ + (b₂ - b₁) = b₂ := by ring
  rw [hb, h₂, h₁, zero_add] at hk

  have hfac : (f.derivative.eval b₁ + k * (b₂ - b₁)) * (b₂ - b₁) = 0 := by
    have := hk.symm
    linear_combination this
  have hunit : IsUnit (f.derivative.eval b₁ + k * (b₂ - b₁)) := by

    have hm : k * (b₂ - b₁) ∈ maximalIdeal C := Ideal.mul_mem_left _ _ hδ
    by_contra hnu
    have hmem : f.derivative.eval b₁ + k * (b₂ - b₁) ∈ maximalIdeal C :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have : f.derivative.eval b₁ ∈ maximalIdeal C := by
      have := Ideal.sub_mem _ hmem hm
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).mp this hu
  have : b₂ - b₁ = 0 := by
    have := congrArg (fun z => (hunit.unit⁻¹ : Cˣ).val * z) hfac
    simpa [← mul_assoc, Units.inv_mul, mul_zero] using this
  linear_combination -this

omit [IsLocalHom (algebraMap A₀ W₀)] in

lemma top_le_adjoin_sup_pow_smul
    (hW₀ : maximalIdeal W₀ = (maximalIdeal A₀).map (algebraMap A₀ W₀))
    (α : W₀)
    (hgen : ∀ w : W₀, ∃ p : A₀[X], w - aeval α p ∈ maximalIdeal W₀) (N : ℕ) :
    ∀ w : W₀, ∃ p : A₀[X], w - aeval α p ∈ (maximalIdeal A₀ ^ N).map (algebraMap A₀ W₀) := by

  let E : Submodule A₀ W₀ := (Algebra.adjoin A₀ ({α} : Set W₀)).toSubmodule
  have hE : ∀ w : W₀, w ∈ E ↔ ∃ p : A₀[X], aeval α p = w := by
    intro w
    change w ∈ Algebra.adjoin A₀ ({α} : Set W₀) ↔ _
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    simp [AlgHom.mem_range]

  have hbase : (⊤ : Submodule A₀ W₀) ≤ E ⊔ (maximalIdeal A₀) • ⊤ := by
    intro w _
    obtain ⟨p, hp⟩ := hgen w
    rw [hW₀] at hp
    have hmem : w - aeval α p ∈ (maximalIdeal A₀ • ⊤ : Submodule A₀ W₀) := by
      rw [Ideal.smul_top_eq_map]; exact hp
    have hE' : aeval α p ∈ E := (hE _).mpr ⟨p, rfl⟩
    have : w = aeval α p + (w - aeval α p) := by ring
    rw [this]
    exact Submodule.add_mem_sup hE' hmem

  have hind : ∀ n : ℕ, (⊤ : Submodule A₀ W₀) ≤ E ⊔ (maximalIdeal A₀ ^ n) • ⊤ := by
    intro n
    induction n with
    | zero =>
        exact le_sup_of_le_right (by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul])
    | succ n ih =>
      calc (⊤ : Submodule A₀ W₀) ≤ E ⊔ (maximalIdeal A₀ ^ n) • ⊤ := ih
        _ ≤ E ⊔ (maximalIdeal A₀ ^ n) • (E ⊔ (maximalIdeal A₀) • ⊤) := by
            gcongr
        _ = E ⊔ ((maximalIdeal A₀ ^ n) • E ⊔ (maximalIdeal A₀ ^ (n + 1)) • ⊤) := by
            rw [Submodule.smul_sup, pow_succ, ← Submodule.smul_assoc, smul_eq_mul, mul_comm]
        _ ≤ E ⊔ (maximalIdeal A₀ ^ (n + 1)) • ⊤ := by
            apply sup_le
            · exact le_sup_left
            · apply sup_le
              · exact le_trans (Submodule.smul_le_right) le_sup_left
              · exact le_sup_right
  intro w
  have hw : w ∈ E ⊔ (maximalIdeal A₀ ^ N) • (⊤ : Submodule A₀ W₀) := hind N Submodule.mem_top
  obtain ⟨e, he, r, hr, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨p, rfl⟩ := (hE e).mp he
  refine ⟨p, ?_⟩
  rw [Ideal.smul_top_eq_map] at hr
  simpa using hr

end UnramifiedRigidity

open UnramifiedRigidity in
theorem solution
    (A₀ : Type u) (W₀ : Type v) (C : Type w)
    [CommRing A₀] [IsLocalRing A₀] [CommRing W₀] [HenselianLocalRing W₀]
    [Algebra A₀ W₀] [IsLocalHom (algebraMap A₀ W₀)]
    (hW₀ : IsLocalRing.maximalIdeal W₀ = (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ W₀))
    [FiniteDimensional (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField W₀)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField W₀)]
    [CommRing C] [IsLocalRing C] [IsHausdorff (IsLocalRing.maximalIdeal C) C]
    (u₁ u₂ : W₀ →+* C) [IsLocalHom u₁]
    (hA₀ : u₁.comp (algebraMap A₀ W₀) = u₂.comp (algebraMap A₀ W₀))
    (h : ∀ w : W₀, u₁ w - u₂ w ∈ IsLocalRing.maximalIdeal C) :
    u₁ = u₂ := by
  classical

  set κ₀ := ResidueField A₀
  set k := ResidueField W₀

  have hu₁ : ∀ w ∈ maximalIdeal W₀, u₁ w ∈ maximalIdeal C := by
    intro w hw
    exact map_nonunit u₁ w hw
  have hu₂ : ∀ w ∈ maximalIdeal W₀, u₂ w ∈ maximalIdeal C := by
    intro w hw
    have : u₂ w = u₁ w - (u₁ w - u₂ w) := by ring
    rw [this]
    exact Ideal.sub_mem _ (hu₁ w hw) (h w)
  have hpow : ∀ (u : W₀ →+* C), (∀ w ∈ maximalIdeal W₀, u w ∈ maximalIdeal C) →
      ∀ (n : ℕ) (w : W₀), w ∈ (maximalIdeal A₀ ^ n).map (algebraMap A₀ W₀) → u w ∈ maximalIdeal C ^ n := by
    intro u hu n w hw
    have hle : (maximalIdeal A₀ ^ n).map (algebraMap A₀ W₀) ≤ (maximalIdeal C ^ n).comap u := by
      rw [Ideal.map_pow, ← hW₀]
      have h1 : maximalIdeal W₀ ≤ (maximalIdeal C).comap u := fun w hw => hu w hw
      calc maximalIdeal W₀ ^ n ≤ ((maximalIdeal C).comap u) ^ n := Ideal.pow_right_mono h1 n
        _ ≤ (maximalIdeal C ^ n).comap u := Ideal.le_comap_pow u n
    exact hle hw

  obtain ⟨ᾱ, hᾱ⟩ := Field.exists_primitive_element κ₀ k
  have hint : IsIntegral κ₀ ᾱ := IsIntegral.of_finite κ₀ ᾱ
  set f₀ : κ₀[X] := minpoly κ₀ ᾱ with hf₀
  have hf₀m : f₀.Monic := minpoly.monic hint
  have hf₀sep : f₀.Separable := Algebra.IsSeparable.isSeparable κ₀ ᾱ
  have hf₀root : aeval ᾱ f₀ = 0 := minpoly.aeval κ₀ ᾱ

  obtain ⟨f, hfmap, -, hfmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective IsLocalRing.residue_surjective f₀) hf₀m

  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective ᾱ
  set fW : W₀[X] := f.map (algebraMap A₀ W₀) with hfW
  have hfWm : fW.Monic := hfmonic.map _

  have hres_eval : ∀ (g : A₀[X]) (x : W₀),
      residue W₀ ((g.map (algebraMap A₀ W₀)).eval x) = aeval (residue W₀ x) (g.map (residue A₀)) := by
    intro g x
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
    congr 1
  have h1 : fW.eval a₀ ∈ maximalIdeal W₀ := by
    rw [← IsLocalRing.residue_eq_zero_iff, hres_eval, hfmap, ha₀, hf₀root]
  have hunit_of_res : ∀ x : W₀, residue W₀ x = ᾱ → IsUnit (fW.derivative.eval x) := by
    intro x hx
    rw [hfW, Polynomial.derivative_map]
    by_contra hnu
    have hmem : (f.derivative.map (algebraMap A₀ W₀)).eval x ∈ maximalIdeal W₀ :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← IsLocalRing.residue_eq_zero_iff, hres_eval, ← Polynomial.derivative_map, hfmap, hx] at hmem
    exact hf₀sep.aeval_derivative_ne_zero hf₀root hmem
  have h2 : IsUnit (fW.derivative.eval a₀) := hunit_of_res a₀ ha₀
  obtain ⟨α, hαroot, hαa₀⟩ := HenselianLocalRing.is_henselian fW hfWm a₀ h1 h2
  have hαres : residue W₀ α = ᾱ := by
    rw [← ha₀, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hαa₀

  set fC : C[X] := fW.map u₁ with hfC
  have hfC₂ : fC = fW.map u₂ := by
    rw [hfC, hfW, Polynomial.map_map, Polynomial.map_map, hA₀]
  have hrootC : ∀ (u : W₀ →+* C), fC = fW.map u → fC.eval (u α) = 0 := by
    intro u hu
    rw [hu, Polynomial.eval_map, Polynomial.eval₂_hom, hαroot.eq_zero, map_zero]
  have hderC : IsUnit (fC.derivative.eval (u₁ α)) := by
    rw [hfC, Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_hom]
    exact (hunit_of_res α hαres).map u₁
  have hα : u₁ α = u₂ α :=
    root_eq_of_sub_mem fC (u₁ α) (u₂ α) (hrootC u₁ rfl) (hrootC u₂ hfC₂) hderC
      (by have := h α; rwa [← Ideal.neg_mem_iff, neg_sub] at this)

  have hadj : ∀ p : A₀[X], u₁ (aeval α p) = u₂ (aeval α p) := by
    intro p
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.hom_eval₂, hA₀, hα]

  have hgen : ∀ w : W₀, ∃ p : A₀[X], w - aeval α p ∈ maximalIdeal W₀ := by
    intro w

    have hmem : residue W₀ w ∈ (IntermediateField.adjoin κ₀ {ᾱ}).toSubalgebra := by
      rw [hᾱ]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨p₀, hp₀⟩ := hmem
    obtain ⟨p, rfl⟩ := Polynomial.map_surjective (residue A₀) IsLocalRing.residue_surjective p₀
    refine ⟨p, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    have haev : aeval α p = (p.map (algebraMap A₀ W₀)).eval α := by
      rw [Polynomial.eval_map, Polynomial.aeval_def]
    rw [haev, hres_eval, hαres]
    exact hp₀.symm

  refine RingHom.ext fun w => ?_
  rw [← sub_eq_zero]
  refine IsHausdorff.haus ‹IsHausdorff (maximalIdeal C) C› _ fun N => ?_
  obtain ⟨p, hp⟩ := top_le_adjoin_sup_pow_smul hW₀ α hgen N w
  have hdecomp : u₁ w - u₂ w = u₁ (w - aeval α p) - u₂ (w - aeval α p) := by
    rw [map_sub, map_sub, hadj p]; ring
  rw [SModEq.zero, hdecomp, smul_eq_mul, Ideal.mul_top]
  exact Ideal.sub_mem _ (hpow u₁ hu₁ N _ hp) (hpow u₂ hu₂ N _ hp)

end S_IsLocalRing_ringHom_eq_of_forall_sub_mem_maximalIdeal_of_maximalIdeal_eq_map_of_isSeparable
end P2MW
export P2MW.S_IsLocalRing_ringHom_eq_of_forall_sub_mem_maximalIdeal_of_maximalIdeal_eq_map_of_isSeparable (solution)
