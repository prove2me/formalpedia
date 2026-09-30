-- Prove2me | solution 1 for MTT.Eigenform.quadratic_centralValue_eq_eulerFactors_mul_of_hasMinimalLevel
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T14:27:20.986873+00:00
-- url     : https://prove2.me/submissions/b0db2d1c-f9f8-47a0-ad7b-477c741fb5eb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_KN_HorizontalPadicL
import Mathlib.GroupTheory.Exponent
import Theorems.Thm_MTT_criticalLValue_sum_dilate
import Theorems.Thm_MTT_Eigenform_exists_oldform_dilation_expansion
import Theorems.Thm_MTT_Eigenform_norm_localParameter_le_of_hasMinimalLevel

set_option autoImplicit false
noncomputable section

open HorizontalPadicL

namespace MTT

/-- Embedded quadratic character values are fixed by inversion, including at nonunits. -/
lemma quadratic_character_inv_eq (ι : Qbar →+* ℂ)
    (η : DirichletCharacterWithLevel) (horder : orderOf η.2 = 2) (n : ℕ) :
    (ι (η.2 n))⁻¹ = ι (η.2 n) := by
  rw [← map_inv₀]
  congr 1
  rw [← MulChar.inv_apply_eq_inv', inv_eq_self_of_orderOf_eq_two horder]

/-- Primitivity turns conductor coprimality into coprimality with the character modulus. -/
lemma coprime_character_level_of_dvd {N M q : ℕ}
    (η : DirichletCharacterWithLevel) (hη : η.2.IsPrimitive)
    (hcop : Nat.Coprime (N * M) η.2.conductor) (hq : q ∣ N) :
    Nat.Coprime q η.1.1 := by
  rw [← hη]
  exact hcop.of_dvd_left (hq.trans (Nat.dvd_mul_right N M))

end MTT

open scoped BigOperators

namespace MTT

lemma sum_finset_euler_coefficients {m r : ℕ} [NeZero m]
    (ι : Qbar →+* ℂ) (χ : DirichletCharacter Qbar m) (j : ℕ)
    (q : Fin r → ℕ) (a : Fin r → ℂ) :
    (∑ S : Finset (Fin r), (∏ i ∈ S, -a i) *
      (ι (χ ((∏ i ∈ S, q i : ℕ) : ZMod m)))⁻¹ /
        ((∏ i ∈ S, q i : ℕ) : ℂ) ^ (j + 1)) =
    ∏ i, (1 - a i * (ι (χ (q i)))⁻¹ / (q i : ℂ) ^ (j + 1)) := by
  classical
  have hterm (S : Finset (Fin r)) :
      (∏ i ∈ S, -a i) * (ι (χ ((∏ i ∈ S, q i : ℕ) : ZMod m)))⁻¹ /
        ((∏ i ∈ S, q i : ℕ) : ℂ) ^ (j + 1) =
      ∏ i ∈ S, (-a i * (ι (χ (q i)))⁻¹ / (q i : ℂ) ^ (j + 1)) := by
    simp only [Nat.cast_prod, map_prod, Finset.prod_inv_distrib,
      Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_div_distrib]
  simp_rw [hterm, sub_eq_add_neg, neg_mul, neg_div]
  simpa only [Finset.powerset_univ] using
    (Finset.prod_one_add (f := fun i : Fin r ↦
      -(a i * (ι (χ (q i)))⁻¹ / (q i : ℂ) ^ (j + 1))) Finset.univ).symm

lemma criticalLValue_eq_prod_of_finset_dilation {M k m r : ℕ} [NeZero m]
    (hM : 0 < M) (hk : 2 ≤ k) (ι : Qbar →+* ℂ)
    (g : CuspForm (GammaOne M) (k : ℤ)) (f : UpperHalfPlane → ℂ)
    (χ : DirichletCharacter Qbar m) (j : ℕ) (q : Fin r → ℕ) (a : Fin r → ℂ)
    (hq : ∀ i, 0 < q i ∧ Nat.Coprime (q i) m)
    (hf : ∀ z, f z = ∑ S : Finset (Fin r), (∏ i ∈ S, -a i) *
      g (UpperHalfPlane.ofComplex ((∏ i ∈ S, (q i : ℂ)) * (z : ℂ)))) :
    criticalLValue ι f m χ j =
      (∏ i, (1 - a i * (ι (χ (q i)))⁻¹ / (q i : ℂ) ^ (j + 1))) *
        criticalLValue ι g m χ j := by
  classical
  have hd (S : Finset (Fin r)) :
      0 < ∏ i ∈ S, q i ∧ Nat.Coprime (∏ i ∈ S, q i) m := by
    exact ⟨Finset.prod_pos (fun i _ ↦ (hq i).1),
      Nat.coprime_prod_left_iff.mpr (fun i _ ↦ (hq i).2)⟩
  have hfun : f = fun z : UpperHalfPlane ↦ ∑ S : Finset (Fin r), (∏ i ∈ S, -a i) *
      g (UpperHalfPlane.ofComplex (((∏ i ∈ S, q i : ℕ) : ℂ) * (z : ℂ))) := by
    funext z
    simpa only [Nat.cast_prod] using hf z
  rw [hfun, criticalLValue_sum_dilate hM hk ι g χ j
    (fun S : Finset (Fin r) ↦ ∏ i ∈ S, q i) (fun S ↦ ∏ i ∈ S, -a i) hd]
  rw [sum_finset_euler_coefficients]

end MTT

open HorizontalPadicL
open scoped BigOperators

theorem solution
    {N M k : ℕ} (hN : 0 < N) (hM : 0 < M) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (g : MTT.Eigenform M k ι)
    (hfg : f.SameHeckeSystem g) (hg : g.HasMinimalLevel)
    (η : DirichletCharacterWithLevel) (hη : η.2.IsPrimitive)
    (horder : orderOf η.2 = 2) (hcop : Nat.Coprime (N * M) η.2.conductor) :
    ∃ (r : ℕ) (q : Fin r → ℕ) (a : Fin r → ℂ),
      (∀ i, (q i).Prime ∧ q i ∣ N ∧ ‖a i‖ ≤ (q i : ℝ) ^ (((k : ℝ) - 1) / 2)) ∧
      @MTT.criticalLValue ι f.form η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) =
        (∏ i, (1 - a i * ι (η.2 (q i)) / (q i : ℂ) ^ (k / 2))) *
          @MTT.criticalLValue ι g.form η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) := by
  classical
  have : NeZero η.1.1 := ⟨Nat.ne_of_gt η.1.2⟩
  obtain ⟨r, q, a, hqa, hexpansion⟩ :=
    f.exists_oldform_dilation_expansion hN hM hk ι g hfg hg
  refine ⟨r, q, a, ?_, ?_⟩
  · intro i
    exact ⟨(hqa i).1, (hqa i).2.1,
      g.norm_localParameter_le_of_hasMinimalLevel hM hk ι hg (q i) (hqa i).1
        (a i) (hqa i).2.2⟩
  · have hq : ∀ i, 0 < q i ∧ Nat.Coprime (q i) η.1.1 := fun i ↦
      ⟨(hqa i).1.pos, MTT.coprime_character_level_of_dvd η hη hcop (hqa i).2.1⟩
    have hindex : k / 2 - 1 + 1 = k / 2 := by omega
    simpa only [hindex, MTT.quadratic_character_inv_eq ι η horder] using
      MTT.criticalLValue_eq_prod_of_finset_dilation hM hk ι g.form f.form η.2
        (k / 2 - 1) q a hq hexpansion
