-- Prove2me | solution 1 for GlobalTheory.SS.dilatation_lowers_defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:09:39.171802+00:00
-- url     : https://prove2.me/submissions/c210a4b9-571a-42b9-a9fa-789a07956ff0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
import Theorems.Thm_GlobalTheory_SS_Dil_factA
import Theorems.Thm_GlobalTheory_SS_Dil_factB
import Theorems.Thm_GlobalTheory_SS_Dil_core
import Theorems.Thm_GlobalTheory_SS_Dil_tors
import Theorems.Thm_GlobalTheory_SS_Dil_exists_dil
import Theorems.Thm_GlobalTheory_SS_Dil_exists_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS
open Dil
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B] (E : ∀ (R' : Type) [CommRing R'] [Algebra R R'], (B →ₐ[R] R') → Prop), (∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Unr π R') → ∀ (I : Ideal B), (∀ b, b ∈ I ↔ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → algebraMap R R' π ∣ a b) → ∀ (k : Type) [Field k] [Algebra R k] [Algebra k (B ⧸ I)] [IsScalarTower R k (B ⧸ I)], Function.Surjective (algebraMap R k) → Algebra.Smooth k (B ⧸ I) → Module.Free (B ⧸ I) (TensorProduct B (B ⧸ I) (KaehlerDifferential R B)) → ∃ (B' : Type) (_ : CommRing B') (_ : Algebra R B') (φ : B →ₐ[R] B'), Algebra.FiniteType R B' ∧ Module.Flat R B' ∧ Function.Injective φ ∧ (∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R') (c : ℕ), E R' a → Defect a π (c + 1) → ∃ a' : B' →ₐ[R] R', a'.comp φ = a ∧ Defect a' π c := by
  intro R _ _ _ π hπ B _ _ _ _ E hE I hI k _ _ _ _ hk hsm hfree
  obtain ⟨B', _, _, φ, hft, hfl, hinj, hden, hreg', hβ, hgen⟩ := exists_dil R π hπ B I
  refine ⟨B', inferInstance, inferInstance, φ, hft, hfl, hinj, hden, ?_⟩
  obtain ⟨n, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R B)
  let σ₀ : MvPolynomial (Fin n) R →ₐ[R] B ⧸ I := (Ideal.Quotient.mkₐ R I).comp q
  have hσ₀ : Function.Surjective σ₀ := (Ideal.Quotient.mkₐ_surjective R I).comp hq
  let I₀ : Ideal (MvPolynomial (Fin n) R) := I.comap q
  have hI₀ : ∀ p, p ∈ I₀ ↔ σ₀ p = 0 := fun p => (Ideal.Quotient.eq_zero_iff_mem (I := I) (a := q p)).symm
  have hker : ∀ r, algebraMap R k r = 0 ↔ π ∣ r := fun r => by
    have h1 : RingHom.ker (algebraMap R k) = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hk)
    rw [← RingHom.mem_ker, h1, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  obtain ⟨h, hh, hA⟩ := factA π hk hker σ₀ hσ₀ I₀ hI₀
  obtain ⟨h', hh', hB⟩ := factB q hq σ₀.toRingHom (fun _ => rfl) hσ₀
  have hJ : ∀ f, q f = 0 → f ∈ I₀ := fun f hf => by
    show q f ∈ I
    rw [hf]; exact I.zero_mem
  have hCπ : q (C π) = algebraMap R B π := by rw [← algebraMap_eq, q.commutes]
  have hπI : C π ∈ I₀ := by
    show q (C π) ∈ I
    rw [hCπ, hI]
    intro R' _ _ a _
    rw [a.commutes]
  have hB' : ∀ f, q f = 0 → f - ∑ j, pderiv j f * h' j ∈ I₀ * I₀ := by
    intro f hf
    have h0 := hB f hf
    have h1 : q (f - ∑ j, pderiv j f * h' j) = 0 := by simp [hf, hh']
    generalize f - ∑ j, pderiv j f * h' j = g at h0 h1 ⊢
    obtain ⟨p, hp⟩ := hA g (hJ g h1)
    have h2 : ∑ j, pderiv j g * h j ∈ I₀ * I₀ :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_mul ((hI₀ _).2 (congrFun h0 j)) (hh j)
    have h3 : g - C π * p ∈ I₀ * I₀ := by
      have := Ideal.add_mem _ hp h2
      convert this using 1; ring
    have h4 : p ∈ I₀ := by
      show q p ∈ I
      rw [hI]
      intro R' _ _ a ha
      obtain ⟨_, _, hirr⟩ := hE R' a ha
      have h5 : ∀ e ∈ I₀ * I₀, algebraMap R R' π * algebraMap R R' π ∣ a (q e) := fun e he =>
        Submodule.mul_induction_on he
          (fun x hx y hy => by
            rw [map_mul, map_mul]
            exact mul_dvd_mul ((hI _).1 hx R' a ha) ((hI _).1 hy R' a ha))
          (fun x y hx hy => by rw [map_add, map_add]; exact dvd_add hx hy)
      have h6 := h5 _ h3
      rw [map_sub, h1, zero_sub, map_neg, dvd_neg, map_mul, map_mul, hCπ, a.commutes] at h6
      exact (mul_dvd_mul_iff_left hirr.ne_zero).1 h6
    have := Ideal.add_mem _ h3 (Ideal.mul_mem_mul hπI h4)
    rwa [sub_add_cancel] at this
  intro R' _ _ a c ha hdef
  obtain ⟨_, _, hirr⟩ := hE R' a ha
  have hreg : algebraMap R R' π ∈ nonZeroDivisors R' := mem_nonZeroDivisors_of_ne_zero hirr.ne_zero
  obtain ⟨a', ha'⟩ := exists_ext φ π I hinj hden hgen a hreg (fun g hg => (hI g).1 hg R' a ha)
  refine ⟨a', ha', ?_⟩
  letI := a.toRingHom.toAlgebra
  letI := a'.toRingHom.toAlgebra
  have hφ : ∀ b, algebraMap B' R' (φ b) = algebraMap B R' b := fun b => AlgHom.congr_fun ha' b
  have hϖ : algebraMap B' R' (algebraMap R B' π) = algebraMap R R' π := a'.commutes π
  intro m hm
  obtain ⟨u, hu, hc⟩ := core q hq (a.comp q).toRingHom (fun _ => rfl) φ hφ π _ hϖ
    (fun x hx => (mul_eq_zero.1 hx).resolve_left hirr.ne_zero) hreg' I₀ (fun g hg => hβ _ hg) hJ
    (fun Q h1 h2 => hgen Q h1 (fun g hg b' hb' => by
      obtain ⟨p, rfl⟩ := hq g
      exact h2 p hg b' hb')) h hh hA h' hh' hB' m
  exact hc c (hdef _ (tors φ hφ π _ hϖ hreg hinj hden u _ (hu ▸ Submodule.smul_mem _ _ hm)))
end GlobalTheory.SS
