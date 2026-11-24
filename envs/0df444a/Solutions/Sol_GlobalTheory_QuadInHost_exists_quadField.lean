-- Prove2me | solution 1 for GlobalTheory.QuadInHost.exists_quadField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:44.790019+00:00
-- url     : https://prove2.me/submissions/206ce59a-cee6-4470-98a0-0cc94aa59a84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_VpBounds
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImagQuadraticSubfieldOfToricCMFieldData
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ClassZetaValuationBounds_ToricDenominatorLevel_exact
import Theorems.Thm_GlobalTheory_discr_eq_neg_of_sq_eq
import Theorems.Thm_GlobalTheory_exists_integer_generator_of_sq_eq_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped IntermediateField
open GlobalTheory GlobalTheory.QuadInHost
namespace GlobalTheory.QuadInHost
theorem _root_.solution : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → d % 4 = 3 → ∀ (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ K : IntermediateField ℚ E, Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ ∃ φK : K →+* ℂ, (∀ i, (φ i).comp (algebraMap K E) = φK) ∧ (starRingEnd ℂ).comp φK ≠ φK ∧ IsLatOf φK 1 Λ := by
  intro E _ _ I _ d φ hF hd4 Λ hΛ
  obtain ⟨hp, hd, -, -, -, hI, -, w, hw, hφw⟩ := hF
  have hd0 : (0 : ℚ) < d := by exact_mod_cast hp.pos
  obtain ⟨i₀⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  have hm : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ) : Polynomial ℚ).Monic := by monicity!
  have he : Polynomial.aeval w (Polynomial.X ^ 2 + Polynomial.C (d : ℚ) : Polynomial ℚ) = 0 := by
    simp [hw]
  have hi : IsIntegral ℚ w := ⟨_, hm, he⟩
  have h2 : Module.finrank ℚ ℚ⟮w⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank hi]
    refine le_antisymm ((Polynomial.natDegree_le_natDegree (minpoly.min ℚ w hm he)).trans
      (by compute_degree)) ((minpoly.two_le_natDegree_iff hi).2 ?_)
    rintro ⟨q, hq⟩
    have h1 : (algebraMap ℚ E q) ^ 2 = -(d : E) := by rw [hq]; exact hw
    have h3 : q ^ 2 = -(d : ℚ) := (algebraMap ℚ E).injective (by simpa using h1)
    nlinarith [sq_nonneg q]
  let r : ℚ⟮w⟯ := IntermediateField.AdjoinSimple.gen ℚ w
  have hr : r ^ 2 = -(d : ℚ⟮w⟯) := Subtype.ext (by simpa [r] using hw)
  let φK : ℚ⟮w⟯ →+* ℂ := (φ i₀).comp (algebraMap ℚ⟮w⟯ E)
  have hφr : ∀ i, (φ i).comp (algebraMap ℚ⟮w⟯ E) r = Complex.I * (Real.sqrt d : ℂ) := fun i => hφw i
  have hsq : (Real.sqrt d : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hp.pos)
    exact_mod_cast this.ne'
  refine ⟨ℚ⟮w⟯, h2, GlobalTheory.discr_eq_neg_of_sq_eq h2 hp.squarefree hd4 hr, φK, ?_, ?_, ?_⟩
  · intro i
    have := (IntermediateField.adjoin.powerBasis hi).algHom_ext
      (f := ((φ i).comp (algebraMap ℚ⟮w⟯ E)).toRatAlgHom) (g := φK.toRatAlgHom)
      (by simp only [IntermediateField.adjoin.powerBasis_gen]; exact (hφr i).trans (hφr i₀).symm)
    exact congrArg AlgHom.toRingHom this
  · intro h
    have := congrArg (fun f => f r) h
    simp only [RingHom.comp_apply] at this
    change starRingEnd ℂ (φK r) = φK r at this
    rw [show φK r = _ from hφr i₀] at this
    simp [Complex.conj_ofReal] at this
    have h0 : (2 * Complex.I) * (Real.sqrt d : ℂ) = 0 := by linear_combination -this
    rcases mul_eq_zero.1 h0 with h0 | h0
    · simp at h0
    · exact hsq h0
  · obtain ⟨ω, hω2, hgen⟩ := GlobalTheory.exists_integer_generator_of_sq_eq_neg h2 hp.squarefree hd4 hr
    have hφω : φK ω = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 := by
      have := congrArg φK hω2
      rw [map_mul, map_add, map_one, map_ofNat, show φK r = _ from hφr i₀] at this
      linear_combination this / 2
    unfold IsLatOf
    ext x
    rw [SetLike.mem_coe, hΛ x]
    constructor
    · rintro ⟨hx, a, b, rfl⟩
      let y : ℚ⟮w⟯ := a + b * r
      have hy : φK y = a + b * (Complex.I * (Real.sqrt d : ℂ)) := by
        simp only [y, map_add, map_mul, map_ratCast, show φK r = _ from hφr i₀]
      have hint : IsIntegral ℤ y := by
        rw [← hy] at hx
        exact (isIntegral_algHom_iff φK.toIntAlgHom φK.injective).1 hx
      refine ⟨y, ?_, hy⟩
      rw [SetLike.mem_coe, FractionalIdeal.mem_one_iff]
      exact ⟨⟨y, hint⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, FractionalIdeal.mem_one_iff] at hy
      obtain ⟨c, rfl⟩ := hy
      refine ⟨(RingOfIntegers.isIntegral_coe c).map φK.toIntAlgHom, ?_⟩
      obtain ⟨m, n, rfl⟩ := hgen c
      refine ⟨m + n / 2, n / 2, ?_⟩
      change φK ((m + n * ω : 𝓞 ℚ⟮w⟯) : ℚ⟮w⟯) = _
      push_cast
      simp only [map_add, map_mul, hφω]
      simp
      ring
end GlobalTheory.QuadInHost
