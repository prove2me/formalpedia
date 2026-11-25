-- Prove2me | solution 1 for GlobalTheory.LatticeCovolumeL2.exists_line_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:17.990806+00:00
-- url     : https://prove2.me/submissions/cff6c4e4-5abf-4b5f-b1fb-6920ed70adec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsLineBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LatticeCovolumeL2
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.LatticeCovolumeL2
theorem _root_.solution {La ι V : Type} [AddCommGroup La] [Module (𝓞 E) La] [Fintype ι]
    [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (ψ : La →ₗ[𝓞 E] V) (hψ : Function.Injective ψ) (T : La → Prop) (b : ι → La)
    (hT : ∀ (c : 𝓞 E) v, T v → T (c • v)) (hsat : ∀ (m : ℤ) v, m ≠ 0 → T (m • v) → T v)
    (hb : ∀ v, T v → v ∈ Submodule.span ℤ (Set.range b)) (hι : Fintype.card ι ≤ Module.finrank ℚ E)
    (t : La) (ht : T t) (h0 : ψ t ≠ 0) :
    Fintype.card ι = Module.finrank ℚ E ∧ ∃ a : ι → E, (∀ k, ψ (b k) = a k • ψ t) ∧
      ∀ e : E, e • ψ t ∈ LinearMap.range ψ ↔ e ∈ Submodule.span ℤ (Set.range a) := by
  have hinj : ∀ c : 𝓞 E, c • t = 0 → c = 0 := by
    intro c hc
    have h1 := congrArg ψ hc
    rw [map_smul, map_zero, ← algebraMap_smul E c (ψ t)] at h1
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).1 h2
    · exact absurd h2 h0
  let S : Submodule ℤ La := Submodule.span ℤ (Set.range b)
  have hSfin : Module.Finite ℤ S := Module.Finite.span_of_finite ℤ (Set.finite_range b)
  have hS : ∀ {κ : Type} [Fintype κ] (w : κ → La), (∀ i, w i ∈ S) → LinearIndependent ℤ w →
      Fintype.card κ ≤ Fintype.card ι := by
    intro κ _ w hw hli
    let w' : κ → S := fun i => ⟨w i, hw i⟩
    have hli' : LinearIndependent ℤ w' := LinearIndependent.of_comp S.subtype hli
    exact hli'.fintype_card_le_finrank.trans (finrank_range_le_card b)
  obtain ⟨β, hβ⟩ := exists_linearIndependent_of_le_finrank (R := ℤ) (M := 𝓞 E)
    (le_of_eq (NumberField.RingOfIntegers.rank E).symm)
  let φ : 𝓞 E →ₗ[ℤ] La := (LinearMap.toSpanSingleton (𝓞 E) La t).restrictScalars ℤ
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    exact fun c hc => hinj c hc
  have hβt : LinearIndependent ℤ (φ ∘ β) := hβ.map' φ hφ
  have hβS : ∀ j, (φ ∘ β) j ∈ S := fun j => hb _ (hT _ _ ht)
  have hcard : Fintype.card ι = Module.finrank ℚ E := by
    refine le_antisymm hι ?_
    simpa using hS (φ ∘ β) hβS hβt
  have hline : ∀ k, ∃ e : E, ψ (b k) = e • ψ t := by
    intro k
    let w : Option (Fin (Module.finrank ℚ E)) → La := fun o => Option.elim o (b k) (φ ∘ β)
    have hw : ∀ o, w o ∈ S := by
      intro o
      cases o with
      | none => exact Submodule.subset_span ⟨k, rfl⟩
      | some j => exact hβS j
    have hnd : ¬ LinearIndependent ℤ w := by
      intro hli
      have := hS w hw hli
      simp [hcard] at this
    obtain ⟨g, hg, o, ho⟩ := Fintype.not_linearIndependent_iff.1 hnd
    rw [Fintype.sum_option] at hg
    have hgn : g none ≠ 0 := by
      intro hz
      rw [hz, zero_smul, zero_add] at hg
      have := Fintype.linearIndependent_iff.1 hβt (fun j => g (some j)) hg
      cases o with
      | none => exact ho hz
      | some j => exact ho (this j)
    let γ : 𝓞 E := -∑ j, (g (some j) : 𝓞 E) * β j
    have hmb : g none • b k = γ • t := by
      have h1 : g none • b k = -∑ j, g (some j) • φ (β j) := eq_neg_of_add_eq_zero_left hg
      rw [h1]
      simp only [γ, φ, LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply, neg_smul,
        Finset.sum_smul, mul_smul, Int.cast_smul_eq_zsmul]
    refine ⟨((g none : ℤ) : E)⁻¹ * algebraMap (𝓞 E) E γ, ?_⟩
    have h2 := congrArg ψ hmb
    rw [map_zsmul, map_smul, ← algebraMap_smul E γ (ψ t), ← Int.cast_smul_eq_zsmul E] at h2
    have hne : ((g none : ℤ) : E) ≠ 0 := by exact_mod_cast hgn
    rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hne, one_smul]
  choose a ha using hline
  refine ⟨hcard, a, ha, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨v, hv⟩
    obtain ⟨α, β', hβ'⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
    have hβ0 : β' ≠ 0 := nonZeroDivisors.ne_zero hβ'.1
    have hβE : algebraMap (𝓞 E) E β' ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hβ0
    have h1 : β' • v = α • t := by
      apply hψ
      rw [map_smul, map_smul, hv, ← algebraMap_smul E β', ← algebraMap_smul E α, smul_smul, ← hβ'.2]
      congr 1
      field_simp
    have hI := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := Ideal.span {β'}) hβ0
      (Ideal.mem_span_singleton_self β') (NumberField.RingOfIntegers.isIntegral β')
    obtain ⟨N, hN, hN0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hN
    obtain ⟨c, hc⟩ := hN
    have hTv : T v := by
      apply hsat N v hN0
      rw [← algebraMap_smul (𝓞 E) N v, hc, mul_comm β' c, mul_smul, h1, smul_smul]
      exact hT _ _ ht
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).1 (hb v hTv)
    have h2 : e • ψ t = (∑ k, g k • a k) • ψ t := by
      rw [← hv, ← hg, map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, ha k, smul_assoc]
    have h3 : e = ∑ k, g k • a k := smul_left_injective E h0 h2
    rw [h3]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · intro he
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).1 he
    refine ⟨∑ k, c k • b k, ?_⟩
    rw [map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, ha k, smul_assoc]
end GlobalTheory.LatticeCovolumeL2
