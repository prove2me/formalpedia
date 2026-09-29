-- Prove2me | solution 1 for ModularCurve.exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/ea86d594-53e5-55b9-9637-7b7f8c74a4bd

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_qExpansion_coeff_atkinLehnerSlash_eq_and_slash_mul_eq_apply_gamma1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul

set_option autoImplicit false

namespace GalConjWL

noncomputable def zetaC (p : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))

noncomputable def kC (p : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaC p}

theorem zetaC_mem (p : ℕ) : zetaC p ∈ kC p := IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)

theorem exists_bridge (p : ℕ) [hp : Fact p.Prime]
    (L : Type) [Field L] [CharZero L] (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (ι : L →+* ℂ) (s : L ≃ₐ[ℚ] L) (b : ℕ) (hs : s ζ = ζ ^ b) :
    ∃ j : ↥(kC p) →ₐ[ℚ] L, (∀ z : ↥(kC p), ι (j z) = (z : ℂ)) ∧
      ∀ z : ↥(kC p), (z : ℂ) = zetaC p → ι (s (j z)) = zetaC p ^ b := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hζC : IsPrimitiveRoot (zetaC p) p := Complex.isPrimitiveRoot_exp p (NeZero.ne p)

  have hιζ : IsPrimitiveRoot (ι ζ) p := hζ.map_of_injective ι.injective
  obtain ⟨i, -, hi⟩ := hιζ.eq_pow_of_pow_eq_one hζC.pow_eq_one

  set ζ' : L := ζ ^ i with hζ'def
  have hιζ' : ι ζ' = zetaC p := by rw [hζ'def, map_pow, hi]
  have hζ' : IsPrimitiveRoot ζ' p := by
    have : IsPrimitiveRoot (ι ζ') p := by rw [hιζ']; exact hζC
    exact this.of_map_of_injective ι.injective
  have hsζ' : s ζ' = ζ' ^ b := by
    rw [hζ'def, map_pow, hs, ← pow_mul, mul_comm, pow_mul]

  have hint : IsIntegral ℚ (zetaC p) := (hζC.isIntegral (NeZero.pos p)).tower_top
  have hroot : ζ' ∈ (minpoly ℚ (zetaC p)).aroots L := by
    rw [Polynomial.mem_aroots, ← Polynomial.cyclotomic_eq_minpoly_rat hζC (NeZero.pos p)]
    refine ⟨Polynomial.cyclotomic_ne_zero p ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr hζ').eq_zero
  let j : ↥(kC p) →ₐ[ℚ] L := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hint).symm ⟨ζ', hroot⟩
  have hjgen : j ⟨zetaC p, zetaC_mem p⟩ = ζ' :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hint ⟨ζ', hroot⟩

  have hιj : (ι.toRatAlgHom.comp j) = (kC p).val := by
    apply IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := kC p) (s := {zetaC p}) rfl
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change ι (j ⟨zetaC p, _⟩) = zetaC p
    rw [hjgen, hιζ']
  refine ⟨j, fun z => ?_, fun z hz => ?_⟩
  · have := congrArg (fun f : ↥(kC p) →ₐ[ℚ] ℂ => f z) hιj
    exact this
  · have hz' : z = ⟨zetaC p, zetaC_mem p⟩ := Subtype.ext hz
    rw [hz', hjgen, hsζ', map_pow, hιζ']

end GalConjWL

open scoped MatrixGroups ModularForm in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ} (hk : Even k)
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    {p₀ : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp f p₀)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (ι : L →+* ℂ) (s : L ≃ₐ[ℚ] L) (b : ℕ) (hb : Nat.Coprime b p) (hs : s ζ = ζ ^ b)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 (M * p))
    (hδp : ((δ 0 0 : ℤ) : ZMod p) = (b : ZMod p)) (hδM : ((δ 0 0 : ℤ) : ZMod M) = 1) (n : ℕ) :
    ∃ z : L, ι z = (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n ∧
      (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        (((⇑f : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n = ι (s z) := by
  obtain ⟨j, hιj, hφ⟩ := GalConjWL.exists_bridge p L ζ hζ ι s b hs
  let φ : ↥(GalConjWL.kC p) →+* ℂ := (ι.comp s.toRingEquiv.toRingHom).comp j.toRingHom
  have hφ' : ∀ z : ↥(GalConjWL.kC p), (z : ℂ) = GalConjWL.zetaC p → φ z = GalConjWL.zetaC p ^ b := by
    intro z hz
    have := hφ z hz
    simpa [φ] using this
  obtain ⟨z, hz, hz'⟩ :=
    ModularCurve.exists_qExpansion_coeff_atkinLehnerSlash_eq_and_slash_mul_eq_apply_gamma1_mul p M hpM hk f hf γ hγ hγp
      (GalConjWL.kC p) rfl b hb φ hφ' δ hδ hδp hδM n
  refine ⟨j z, ?_, ?_⟩
  · rw [hιj z]; exact hz
  · rw [hz']
    simp [φ]

end S_ModularCurve_exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul
end P2MW
export P2MW.S_ModularCurve_exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul (solution)
