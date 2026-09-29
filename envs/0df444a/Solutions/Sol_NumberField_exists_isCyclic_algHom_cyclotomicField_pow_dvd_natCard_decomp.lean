-- Prove2me | solution 1 for NumberField.exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3e75749d-e004-55b3-83dd-c2083fdac917

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Theorems.Thm_IsGalois_exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units
import Theorems.Thm_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_fixedField_of_forall_isConj_mem
import Theorems.Thm_NumberField_exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp
set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain

namespace C7pProof

theorem pow_dvd_of_pow_succ_dvd_mul {p : ℕ} (hp : p.Prime) {a x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : p ^ (a + 1) ∣ x * y) (hy2 : ¬ p ^ 2 ∣ y) : p ^ a ∣ x := by
  rw [hp.pow_dvd_iff_le_factorization hx.ne']
  have h1 := (hp.pow_dvd_iff_le_factorization (Nat.mul_pos hx hy).ne').1 h
  rw [Nat.factorization_mul hx.ne' hy.ne', Finsupp.add_apply] at h1
  have h2 : y.factorization p < 2 := by
    by_contra h2
    push Not at h2
    exact hy2 ((hp.pow_dvd_iff_le_factorization hy.ne').2 h2)
  omega

theorem not_sq_dvd_of_le {p : ℕ} (hp : p.Prime) {y : ℕ} (hy : 0 < y) (hle : y ≤ 2 * (p - 1)) : ¬ p ^ 2 ∣ y := by
  intro h
  have h1 := Nat.le_of_dvd hy h
  have h2 := hp.two_le
  have h3 : 2 * p ≤ p ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right p h2
  omega

variable {E : Type} [Field E] [NumberField E]

private theorem _root_.C7pProof.under_under (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra E K] [Algebra K L] [Algebra E L]
    [IsScalarTower E K L] (w : HeightOneSpectrum (𝓞 L)) : (w.under (𝓞 K)).under (𝓞 E) = w.under (𝓞 E) := by
  apply HeightOneSpectrum.ext
  change (w.asIdeal.under (𝓞 K)).under (𝓞 E) = w.asIdeal.under (𝓞 E)
  rw [Ideal.under_under]

p2m_export "C7pProof" "under_under"

theorem autToPow_eq_neg_one_of_isConj (n : ℕ) [NeZero n] (L : Type) [Field L] [NumberField L] [Algebra E L]
    [IsCyclotomicExtension {n} E L] (φ : L →+* ℂ) (σ : L ≃ₐ[E] L) (hσ : NumberField.ComplexEmbedding.IsConj φ σ) :
    (IsCyclotomicExtension.zeta_spec n E L).autToPow E σ = -1 := by
  set hz := IsCyclotomicExtension.zeta_spec n E L with hhz
  set ζ := IsCyclotomicExtension.zeta n E L with hζ

  have hnorm : ‖φ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hz.pow_eq_one, map_one]) (NeZero.ne n)
  have hσζ : σ ζ = ζ⁻¹ := by
    apply φ.injective
    rw [hσ.eq, map_inv₀, Complex.inv_eq_conj hnorm]
    rfl

  have h1 := hz.autToPow_spec E σ
  rw [hσζ] at h1

  have h2 : ζ ^ (((hz.autToPow E σ : (ZMod n)ˣ) : ZMod n).val + 1) = 1 := by
    rw [pow_succ, h1, inv_mul_cancel₀ (hz.ne_zero (NeZero.ne n))]
  have h3 : (n : ℕ) ∣ ((hz.autToPow E σ : (ZMod n)ˣ) : ZMod n).val + 1 := (hz.pow_eq_one_iff_dvd _).1 h2
  apply Units.ext
  rw [Units.val_neg, Units.val_one, ← ZMod.natCast_zmod_val ((hz.autToPow E σ : (ZMod n)ˣ) : ZMod n), eq_neg_iff_add_eq_zero,
    ← Nat.cast_one, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  exact h3

end C7pProof

theorem solution
    (E : Type) [Field E] [NumberField E] (T : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ) [Fact p.Prime] (a : ℕ) :
    ∃ (k : ℕ) (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra E F') (_ : IsGalois E F')
      (_ : IsCyclic (F' ≃ₐ[E] F')),
      Nonempty (F' →ₐ[E] CyclotomicField (p ^ k) E) ∧
      (∀ (w : InfinitePlace F') (g : (F' ≃ₐ[E] F')), g ∈ NumberField.InfPlaceDecomp.decomp E F' w → g = 1) ∧
      p ^ a ∣ Nat.card (F' ≃ₐ[E] F') ∧
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 F'), w.under (𝓞 E) = v →
        p ^ a ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)) ∧

      IsPGroup p (F' ≃ₐ[E] F') := by
  classical

  obtain ⟨k₀, hk₀⟩ := NumberField.exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv E T p (a + 1)
  obtain ⟨hdeg, hloc⟩ := hk₀ k₀ le_rfl
  set k := k₀ with hk
  let C := CyclotomicField (p ^ k) E
  haveI : IsGalois E C := IsCyclotomicExtension.isGalois {p ^ k} E C
  have hz := IsCyclotomicExtension.zeta_spec (p ^ k) E C
  let χ : (C ≃ₐ[E] C) →* (ZMod (p ^ k))ˣ := hz.autToPow E
  have hχ : Function.Injective χ := hz.autToPow_injective E

  obtain ⟨M, hMn, hneg, hMcard, hgal, hcyc, hpg, hmul⟩ :=
    IsGalois.exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units E C p k χ hχ
  haveI := hMn
  haveI : IsGalois E (IntermediateField.fixedField M) := hgal
  let F' : Type := ↥(IntermediateField.fixedField M)
  have hp := (Fact.out : p.Prime)
  have hM0 : 0 < Nat.card M := Nat.card_pos
  have hMsq : ¬ p ^ 2 ∣ Nat.card M := C7pProof.not_sq_dvd_of_le hp hM0 hMcard
  refine ⟨k, F', inferInstance, inferInstance, inferInstance, hgal, hcyc, ⟨(IntermediateField.fixedField M).val⟩, ?_, ?_, ?_, hpg⟩
  ·
    have hM : ∀ (φ : C →+* ℂ) (σ : C ≃ₐ[E] C), NumberField.ComplexEmbedding.IsConj φ σ → σ ∈ M := fun φ σ hσ =>
      hneg σ (C7pProof.autToPow_eq_neg_one_of_isConj (p ^ k) C φ σ hσ)
    exact NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_fixedField_of_forall_isConj_mem E C M hM
  ·
    exact C7pProof.pow_dvd_of_pow_succ_dvd_mul hp Nat.card_pos hM0 (hmul ▸ hdeg) hMsq
  ·
    intro v hvT w' hw'

    obtain ⟨W, hWF⟩ : ∃ W : HeightOneSpectrum (𝓞 C), W.under (𝓞 F') = w' :=
      ⟨NumberField.PlaceAbove.above F' C w', HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above F' C w')⟩
    subst hWF
    have hWE : W.under (𝓞 E) = v := by rw [← C7pProof.under_under F' C W, hw']
    have hDC := hloc v hvT W hWE

    obtain ⟨r, hrs, -, hrker, -, -⟩ := NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower E F' C W
    have hcardD : Nat.card ↥(NumberField.PlaceDecomp.decomp E C W) =
        Nat.card ↥(NumberField.PlaceDecomp.decomp E F' (W.under (𝓞 F'))) * Nat.card r.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup r.ker, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective r hrs).toEquiv]

    have hker : Nat.card r.ker ≤ Nat.card M := by
      refine Nat.card_le_card_of_injective (fun σ : r.ker => (⟨((σ : ↥(NumberField.PlaceDecomp.decomp E C W)) : C ≃ₐ[E] C), ?_⟩ : M)) ?_
      · have h1 : r σ = 1 := σ.2
        rw [hrker] at h1
        exact (IntermediateField.fixingSubgroup_fixedField M).le
          ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => h1 ⟨x, hx⟩)
      · intro σ τ h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h')
    have hker0 : 0 < Nat.card r.ker := Nat.card_pos
    rw [hcardD] at hDC
    exact C7pProof.pow_dvd_of_pow_succ_dvd_mul hp Nat.card_pos hker0 hDC (C7pProof.not_sq_dvd_of_le hp hker0 (hker.trans hMcard))

end S_NumberField_exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp
end P2MW
export P2MW.S_NumberField_exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp (solution)
