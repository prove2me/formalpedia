-- Prove2me | solution 1 for GlobalTheory.EisConstTerm.hasSum_constTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:36.377733+00:00
-- url     : https://prove2.me/submissions/df3c2d35-22d3-4bbe-8464-de788bb61c27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinConstantTermPartialZeta
import Theorems.Thm_GlobalTheory_EisConstTerm_eisTerm_pair_zero
import Theorems.Thm_GlobalTheory_EisConstTerm_spanSingleton_mul_le_one
import Theorems.Thm_GlobalTheory_EisConstTerm_mem_latM_of_le_one
import Theorems.Thm_GlobalTheory_EisConstTerm_absNorm_of_spanSingleton
import Theorems.Thm_GlobalTheory_EisConstTerm_mk0_eq_of_spanSingleton
import Theorems.Thm_GlobalTheory_EisConstTerm_exists_spanSingleton_of_mk0_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open GlobalTheory GlobalTheory.EisConstTerm
namespace GlobalTheory.EisConstTerm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (s : ℕ), 1 ≤ s →
  ∀ (D : (Ideal (NumberField.RingOfIntegers F))⁰), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) →
  ∀ Z : ℂ → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) Z →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 = 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 (2 * s) 0 z c)
      (((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F * GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℝ) : ℂ) ^ (2 * s) * Z ((2 * s : ℕ) : ℂ)) := by
  intro F _ _ _ 𝔞 𝔟 s hs D hD Z hZ z hz
  classical
  set C := ClassGroup.mk0 D * ClassGroup.mk F 𝔞 with hC
  let S := {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 = 0}
  let T := {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C}
  let cD : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  let Jf : F → FractionalIdeal (𝓞 F)⁰ F := fun a => FractionalIdeal.spanSingleton (𝓞 F)⁰ a * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)
  have hcD : cD ≠ 0 := by
    simp only [cD, ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have hX : cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := mul_ne_zero hcD (Units.ne_zero 𝔞)
  have hne : ∀ c : S, c.1.out.1.1 ≠ 0 := fun c h => c.1.out.2.2.2 (Prod.ext h c.2)
  have hle : ∀ c : S, Jf c.1.out.1.1 ≤ 1 := fun c => spanSingleton_mul_le_one F 𝔞 _ c.1.out.2.1
  let Jof : S → Ideal (𝓞 F) := fun c => Classical.choose (FractionalIdeal.le_one_iff_exists_coeIdeal.1 (hle c))
  have hJof : ∀ c : S, ((Jof c : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = Jf c.1.out.1.1 := fun c =>
    Classical.choose_spec (FractionalIdeal.le_one_iff_exists_coeIdeal.1 (hle c))
  have hJnz : ∀ c : S, Jof c ∈ (Ideal (𝓞 F))⁰ := by
    intro c
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    have := hJof c
    rw [h0, Submodule.zero_eq_bot, FractionalIdeal.coeIdeal_bot] at this
    simp only [Jf, mul_assoc] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact hne c (FractionalIdeal.spanSingleton_eq_zero_iff.1 h)
    · exact hX h
  have hDc : ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = cD := by simp only [cD, hD]
  let f : S → T := fun c => ⟨⟨Jof c, hJnz c⟩, mk0_eq_of_spanSingleton F 𝔞 D _ (hne c) _ (by rw [hDc]; exact hJof c)⟩
  have hsp : ∀ (a : F) (ε : (𝓞 F)ˣ), FractionalIdeal.spanSingleton (𝓞 F)⁰ (((ε : 𝓞 F) : F) * a) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a := by
    intro a ε
    refine (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨ε, ?_⟩).symm
    rw [Units.smul_def, Algebra.smul_def]
  have hf : Function.Bijective f := by
    constructor
    · intro c c' h
      have h1 : Jof c = Jof c' := congrArg (fun J : T => (J.1 : Ideal (𝓞 F))) h
      have h2 : Jf c.1.out.1.1 = Jf c'.1.out.1.1 := by rw [← hJof, ← hJof, h1]
      have h3 : FractionalIdeal.spanSingleton (𝓞 F)⁰ c.1.out.1.1 = FractionalIdeal.spanSingleton (𝓞 F)⁰ c'.1.out.1.1 := by
        simp only [Jf, mul_assoc] at h2
        exact mul_right_cancel₀ hX h2
      obtain ⟨ε, hε⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h3
      apply Subtype.ext
      rw [← Quotient.out_eq c.1, ← Quotient.out_eq c'.1]
      apply Quotient.sound
      refine ⟨ε, ?_, ?_⟩
      · rw [← hε, Units.smul_def, Algebra.smul_def]
      · rw [c.2, c'.2, mul_zero]
    · rintro ⟨J, hJ⟩
      obtain ⟨a, ha, hJa⟩ := exists_spanSingleton_of_mk0_eq F 𝔞 D J hJ
      have hJle : Jf a ≤ 1 := by
        have h := FractionalIdeal.coeIdeal_le_one (I := (J : Ideal (𝓞 F))) (S := (𝓞 F)⁰) (P := F)
        rwa [hJa, hDc] at h
      let p : LatPair 𝔞 𝔟 := ⟨(a, 0), mem_latM_of_le_one F 𝔞 a hJle, Submodule.zero_mem _, fun h => ha (congrArg Prod.fst h)⟩
      obtain ⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r p (Quotient.mk (latRel 𝔞 𝔟) p).out := Quotient.exact (Quotient.out_eq _).symm
      have h2' : (Quotient.mk (latRel 𝔞 𝔟) p).out.1.2 = 0 := by rw [h2]; simp [p]
      refine ⟨⟨Quotient.mk _ p, h2'⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show Jof _ = (J : Ideal (𝓞 F))
      refine FractionalIdeal.coeIdeal_injective (K := F) ?_
      show ((Jof _ : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
      rw [hJof, hJa, hDc]
      show Jf (Quotient.mk (latRel 𝔞 𝔟) p).out.1.1 = Jf a
      rw [h1]
      simp only [Jf, hsp]
      rfl
  let e : S ≃ T := Equiv.ofBijective f hf
  have hZ2 := hZ.2 ((2 * s : ℕ) : ℂ) (by simp; norm_cast; omega)
  rw [← e.hasSum_iff] at hZ2
  have key : (fun c : S => eisClass 𝔞 𝔟 (2 * s) 0 z c.1) = fun c => (((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
        ((dF F * nrm 𝔞 : ℝ) : ℂ) ^ (2 * s)) * ((fun J : T => ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-((2 * s : ℕ) : ℂ))) ∘ e) c := by
    funext c
    have hN := absNorm_of_spanSingleton F 𝔞 c.1.out.1.1 (Jof c) (hJof c)
    simp only [Function.comp_apply, e, Equiv.ofBijective_apply, f]
    unfold eisClass
    rw [← Prod.mk.eta (p := c.1.out.1), c.2, eisTerm_pair_zero, Complex.cpow_neg, Complex.cpow_natCast]
    have hX0 : ((dF F * nrm 𝔞 : ℝ) : ℂ) ≠ 0 := by
      have h1 : dF F ≠ 0 := by
        unfold dF; rw [abs_ne_zero]; exact_mod_cast NumberField.discr_ne_zero F
      have h2 : nrm 𝔞 ≠ 0 := by
        unfold nrm; rw [Rat.cast_ne_zero, ne_eq, FractionalIdeal.absNorm_eq_zero_iff]; exact Units.ne_zero 𝔞
      exact_mod_cast mul_ne_zero h1 h2
    rw [← Complex.ofReal_natCast, hN, Complex.ofReal_mul (|_|)]
    have gen : ∀ (K y X : ℂ) (n : ℕ), X ≠ 0 → K * y⁻¹ ^ n = K * X ^ n * ((y * X) ^ n)⁻¹ := by
      intro K y X n hX
      rw [mul_pow, mul_inv, inv_pow, mul_assoc K, mul_comm ((y ^ n)⁻¹), ← mul_assoc (X ^ n), mul_inv_cancel₀ (pow_ne_zero _ hX), one_mul]
    exact gen _ _ _ _ hX0
  rw [key]
  exact hZ2.mul_left _
end GlobalTheory.EisConstTerm
