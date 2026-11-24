-- Prove2me | solution 1 for GlobalTheory.UnramConjUnit.exists_sub_conj_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:19:10.46087+00:00
-- url     : https://prove2.me/submissions/2dc55892-a299-4dfa-8d63-202906cb593a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
import Theorems.Thm_GlobalTheory_UnramConjUnit_conj_ne_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal GlobalTheory.SelfDualLatticeCompare
open GlobalTheory GlobalTheory.UnramConjUnit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
namespace GlobalTheory.UnramConjUnit
namespace _root_.GlobalTheory.UnramConjUnit
theorem _root_.solution (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v) :
    ∃ (t d : 𝓞 E) (s : 𝓞 F), (d : E) = (t : E) - σ t ∧
      algebraMap F E (s : F) = (d : E) * d ∧ s ∉ v.asIdeal := by
  classical
  have hne := _root_.GlobalTheory.UnramConjUnit.conj_ne_id h
  obtain ⟨-, -, hrank, -⟩ := h
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ σ.bijective
  have hτ : ∀ x, τ x = σ x := fun _ => rfl
  have hτ1 : τ ≠ 1 := fun h1 => hne fun e => by rw [← hτ, h1]; rfl
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    refine le_antisymm (hrank ▸ AlgEquiv.card_le) ?_
    have h2 : ({1, τ} : Finset (E ≃ₐ[F] E)).card = 2 := Finset.card_pair (Ne.symm hτ1)
    exact h2 ▸ Finset.card_le_univ _
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E
    (by rw [Nat.card_eq_fintype_card, hcard, hrank])
  have hG : ∀ g : E ≃ₐ[F] E, g = 1 ∨ g = τ := by
    intro g
    by_contra hg
    push_neg at hg
    have h3 : ({g, 1, τ} : Finset (E ≃ₐ[F] E)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hg.1, hg.2]), Finset.card_pair (Ne.symm hτ1)]
    have := h3 ▸ Finset.card_le_univ ({g, 1, τ} : Finset (E ≃ₐ[F] E))
    omega
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    rcases hG (τ * τ) with h2 | h2
    · exact congrArg (fun g : E ≃ₐ[F] E => g x) h2
    · exact absurd (mul_eq_right.mp h2) hτ1
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := 𝓞 E) v.asIdeal
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [hPv.over, Ideal.under, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
  have he := hv ⟨P, hP, hPbot⟩ hPv
  have hin : τ ∉ Ideal.inertia (E ≃ₐ[F] E) P := by
    intro hmem
    have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) v.asIdeal P
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P (E ≃ₐ[F] E)] at h1
    have h1' : Nat.card (Ideal.inertia (E ≃ₐ[F] E) P) = 1 := h1.trans he
    rw [Subgroup.card_eq_one] at h1'
    rw [h1', Subgroup.mem_bot] at hmem
    exact hτ1 hmem
  have hin' : ¬ ∀ x : 𝓞 E, τ • x - x ∈ P := fun hall => hin (AddSubgroup.mem_inertia.mpr hall)
  push_neg at hin'
  obtain ⟨x, hx⟩ := hin'
  set d : 𝓞 E := x - τ • x with hd_def
  have hd : d ∉ P := fun hd => hx (by rw [← neg_sub]; exact P.neg_mem hd)
  have hdE : (d : E) = x - σ x := rfl
  have hfix : ∀ g : E ≃ₐ[F] E, g ((d : E) * d) = (d : E) * d := by
    intro g
    rcases hG g with rfl | rfl
    · rfl
    · have : τ (d : E) = -(d : E) := by
        rw [hdE, map_sub, ← hτ, hττ, neg_sub]
      rw [map_mul, this, neg_mul_neg]
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix
  have hcint : IsIntegral ℤ c := by
    have hi : IsIntegral ℤ (algebraMap F E c) := by
      rw [hc]
      exact ((d * d : 𝓞 E)).isIntegral_coe
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E)
      (algebraMap F E).injective).mp hi
  refine ⟨x, d, ⟨c, hcint⟩, hdE, hc, ?_⟩
  intro hs
  have hmem : algebraMap (𝓞 F) (𝓞 E) ⟨c, hcint⟩ ∈ P := by
    rw [hPv.over] at hs
    exact hs
  have heq : algebraMap (𝓞 F) (𝓞 E) ⟨c, hcint⟩ = d * d := by
    apply RingOfIntegers.ext
    change _ = (d : E) * d
    rw [← hc]
    rfl
  rw [heq] at hmem
  exact hd ((hP.mem_or_mem hmem).elim id id)
end _root_.GlobalTheory.UnramConjUnit
end GlobalTheory.UnramConjUnit
