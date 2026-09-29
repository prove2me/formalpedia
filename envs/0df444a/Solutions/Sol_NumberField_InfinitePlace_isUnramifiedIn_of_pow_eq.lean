-- Prove2me | solution 1 for NumberField.InfinitePlace.isUnramifiedIn_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8f33d596-dfde-5ece-a9e5-2d68efad294f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfinitePlace_isUnramifiedIn_of_pow_eq

set_option autoImplicit false

theorem solution
    (E M : Type*) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    {p : ℕ} (hp : p.Prime) (hζ : (primitiveRoots p E).Nonempty) (u : E) (α : M) (hα : α ^ p = algebraMap E M u)
    (hgen : IntermediateField.adjoin E {α} = ⊤)
    (w : NumberField.InfinitePlace E)
    (hb : w.IsReal → ∃ b : w.Completion, algebraMap E w.Completion u = b ^ p) :
    w.IsUnramifiedIn M := by
  classical
  intro w' hw'
  rw [NumberField.InfinitePlace.isUnramified_iff]
  by_cases hwc : w.IsComplex
  · right
    rw [hw']
    exact hwc
  left
  have hw : w.IsReal := NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hwc

  obtain ⟨ζ, hζ⟩ := hζ
  have hprim : IsPrimitiveRoot ζ p := (mem_primitiveRoots hp.pos).mp hζ
  have hp2 : p = 2 := by
    by_contra hne
    have hlt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hne)
    have h0 := NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hlt hprim
    have hpos : 0 < NumberField.InfinitePlace.nrRealPlaces E := Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
    omega
  subst hp2
  obtain ⟨b, hb⟩ := hb hw

  set φ : M →+* ℂ := w'.embedding with hφ
  set ψ : E →+* ℂ := φ.comp (algebraMap E M) with hψ
  have hψw : NumberField.InfinitePlace.mk ψ = NumberField.InfinitePlace.mk w.embedding := by
    rw [NumberField.InfinitePlace.mk_embedding, hψ, ← NumberField.InfinitePlace.comap_mk, hφ,
      NumberField.InfinitePlace.mk_embedding, hw']
  have hwr : NumberField.ComplexEmbedding.IsReal w.embedding := NumberField.InfinitePlace.isReal_iff.mp hw
  have hcases := NumberField.InfinitePlace.mk_eq_iff.mp hψw
  have hψreal : NumberField.ComplexEmbedding.IsReal ψ := by
    rcases hcases with h | h
    · rw [h]; exact hwr
    · rw [← NumberField.ComplexEmbedding.isReal_conjugate_iff, h]; exact hwr

  have hwu : ∃ r : ℝ, w.embedding u = (r : ℂ) ^ 2 := by
    have h1 : NumberField.InfinitePlace.Completion.extensionEmbedding w (algebraMap E w.Completion u)
        = (NumberField.InfinitePlace.Completion.extensionEmbedding w b) ^ 2 := by
      rw [hb, map_pow]
    rw [show algebraMap E w.Completion u = (((WithAbs.equiv w.1).symm u : WithAbs w.1) : w.Completion) from rfl,
      NumberField.InfinitePlace.Completion.extensionEmbedding_coe] at h1
    simp only [RingEquiv.apply_symm_apply] at h1
    refine ⟨NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw b, ?_⟩
    rw [h1, NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  obtain ⟨r, hr⟩ := hwu
  have hψu : ψ u = (r : ℂ) ^ 2 := by
    rcases hcases with h | h
    · rw [h, hr]
    · have h2 : starRingEnd ℂ (ψ u) = (r : ℂ) ^ 2 := by
        rw [← NumberField.ComplexEmbedding.conjugate_coe_eq, h, hr]
      have h3 := congrArg (starRingEnd ℂ) h2
      rwa [Complex.conj_conj, map_pow, Complex.conj_ofReal] at h3

  have hφα : starRingEnd ℂ (φ α) = φ α := by
    have hsq : (φ α) ^ 2 = (r : ℂ) ^ 2 := by rw [← map_pow, hα, ← hψu]; rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · rw [h, Complex.conj_ofReal]
    · rw [h, map_neg, Complex.conj_ofReal]

  letI : Algebra E ℂ := ψ.toAlgebra
  let φ₁ : M →ₐ[E] ℂ := { φ with commutes' := fun e => rfl }
  let φ₂ : M →ₐ[E] ℂ :=
    { (starRingEnd ℂ).comp φ with
      commutes' := fun e => by
        show starRingEnd ℂ (ψ e) = ψ e
        exact RingHom.congr_fun hψreal e }
  have halg : IsAlgebraic E α := Algebra.IsAlgebraic.isAlgebraic α
  have hadj : Algebra.adjoin E {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg, hgen]
    rfl
  have heq : φ₂ = φ₁ :=
    AlgHom.ext_of_adjoin_eq_top hadj fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hφα

  rw [NumberField.InfinitePlace.isReal_iff]
  show NumberField.ComplexEmbedding.IsReal φ
  ext x
  exact AlgHom.congr_fun heq x

end S_NumberField_InfinitePlace_isUnramifiedIn_of_pow_eq
end P2MW
export P2MW.S_NumberField_InfinitePlace_isUnramifiedIn_of_pow_eq (solution)
