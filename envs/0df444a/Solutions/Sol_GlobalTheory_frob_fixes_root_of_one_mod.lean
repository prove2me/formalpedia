-- Prove2me | solution 1 for GlobalTheory.frob_fixes_root_of_one_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:59:12.403024+00:00
-- url     : https://prove2.me/submissions/ae65f736-2c25-46a6-8052-b373a5e59877

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFrobFixesRootOfOneModPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (M : ℕ) (ζ : F) (hζ : IsPrimitiveRoot ζ M) (v : HeightOneSpectrum (𝓞 F))
    (hMv : ((M : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (A : ValuationSubring Ω) (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v) (σ : Formalism.ConjugateSelfDual.G F Ω)
    (hσ : Formalism.ConjugateSelfDual.IsFrob A (Formalism.ConjugateSelfDual.normV v) σ)
    (x : 𝓞 F) (hx : x - 1 ∈ v.asIdeal) (w : Ω) (hw : w ^ M = algebraMap F Ω (x : F)) :
    σ w = w := by
  set q := Formalism.ConjugateSelfDual.normV v
  set x' := algebraMap F Ω (x : F) with hx'
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hMv
    · exact h
  haveI : NeZero M := ⟨hM0.ne'⟩
  have hx1 : A.valuation (x' - 1) < 1 := by
    have := (hA (x - 1)).2 hx
    simpa [hx'] using this
  have hMk : ¬ A.valuation (M : Ω) < 1 := by
    intro h; apply hMv; apply (hA (M : 𝓞 F)).1; simpa using h
  have hpow : ∀ y : Ω, y ^ M ∈ A → y ∈ A := by
    intro y hy
    rw [← A.valuation_le_one_iff] at hy ⊢
    rwa [map_pow, pow_le_one_iff hM0.ne'] at hy
  have hx'A : x' ∈ A := by
    have h1 : x' - 1 ∈ A := (A.valuation_le_one_iff _).1 hx1.le
    simpa using add_mem h1 A.one_mem
  have hwA : w ∈ A := hpow w (hw ▸ hx'A)
  set ζ' := algebraMap F Ω ζ with hζ'
  have hζ'p : IsPrimitiveRoot ζ' M := hζ.map_of_injective (algebraMap F Ω).injective
  have hσζ : ∀ n : ℕ, σ (ζ' ^ n) = ζ' ^ n := by
    intro n; rw [map_pow, hζ', AlgEquiv.commutes]
  have hσx : σ x' = x' := AlgEquiv.commutes σ _
  have hroot : ∀ μ : Ω, μ ^ M = 1 → μ ∈ A := fun μ h => hpow μ (h ▸ A.one_mem)
  let res := IsLocalRing.residue A
  have key : ∀ a b : A, res a = res b ↔ A.valuation ((a : Ω) - b) < 1 := by
    intro a b
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simp
  have hfrob : ∀ a : A, ∃ b : A, (b : Ω) = σ a ∧ res b = res a ^ q := by
    intro a
    have h := hσ.2 a ((A.valuation_le_one_iff _).2 a.2)
    have hb : σ (a : Ω) ∈ A := by
      have h1 : σ (a:Ω) - (a:Ω) ^ q ∈ A := (A.valuation_le_one_iff _).1 h.le
      have h2 : (a : Ω) ^ q ∈ A := A.pow_mem a.2 q
      simpa using add_mem h1 h2
    refine ⟨⟨_, hb⟩, rfl, ?_⟩
    rw [← map_pow, key]; simpa using h

  obtain ⟨μ, hμM, hμ⟩ : ∃ μ : Ω, μ ^ M = 1 ∧ A.valuation (w - μ) < 1 := by
    have hprod := congrArg (Polynomial.eval w) (X_pow_sub_one_eq_prod hM0 hζ'p)
    simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at hprod
    by_contra hcon
    push_neg at hcon
    have h1 : A.valuation (w ^ M - 1) = 1 := by
      rw [hprod, map_prod]
      apply Finset.prod_eq_one
      intro μ hμ
      have hμM : μ ^ M = 1 := (mem_nthRootsFinset hM0 (1 : Ω)).1 hμ
      apply le_antisymm
      · exact (A.valuation_le_one_iff _).2 (A.sub_mem hwA (hroot μ hμM))
      · exact hcon μ hμM
    rw [hw] at h1
    rw [h1] at hx1
    exact lt_irrefl _ hx1
  obtain ⟨j, -, hj⟩ := hζ'p.eq_pow_of_pow_eq_one hμM

  let aw : A := ⟨w, hwA⟩
  let aμ : A := ⟨μ, hroot μ hμM⟩
  have hwμ : res aw = res aμ := (key aw aμ).2 hμ
  obtain ⟨bw, hbw, hbw'⟩ := hfrob aw
  obtain ⟨bμ, hbμ, hbμ'⟩ := hfrob aμ
  have hbμe : bμ = aμ := by
    apply Subtype.ext
    rw [hbμ]; show σ μ = μ
    rw [← hj, hσζ]
  rw [hbμe] at hbμ'
  have hB : res bw = res aw := by
    rw [hbw', hwμ, ← hbμ']

  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0.ne'] at hw
    rw [← hw] at hx1
    simp at hx1
  have hx'0 : x' ≠ 0 := by rw [← hw]; exact pow_ne_zero _ hw0
  set ξ := σ w / w with hξ
  have hξM : ξ ^ M = 1 := by
    rw [hξ, div_pow, ← map_pow, hw, hσx, div_self hx'0]
  let aξ : A := ⟨ξ, hroot ξ hξM⟩
  have hbw_eq : bw = aξ * aw := by
    apply Subtype.ext
    show (bw : Ω) = ξ * w
    rw [hbw, hξ, div_mul_cancel₀ _ hw0]
  have hresw : res aw ≠ 0 := by
    intro h0
    have h1 : res (aw ^ M) = 0 := by rw [map_pow, h0, zero_pow hM0.ne']
    have h2 : res (aw ^ M) = res 1 := by
      rw [key]
      have : ((aw ^ M : A) : Ω) = x' := by simp [aw, hw]
      rw [this]; simpa using hx1
    rw [h1, map_one] at h2
    exact zero_ne_one h2
  have hresξ : res aξ = 1 := by
    have h := hB
    rw [hbw_eq, map_mul] at h
    exact mul_right_cancel₀ hresw (h.trans (one_mul _).symm)
  by_contra hne
  have hξ1 : ξ ≠ 1 := by
    intro h; apply hne
    rw [hξ] at h
    exact (div_eq_one_iff_eq hw0).1 h
  have hsum : ∑ l ∈ Finset.range M, ξ ^ l = 0 := by
    rw [geom_sum_eq hξ1, hξM, sub_self, zero_div]
  have hsumA : ∑ l ∈ Finset.range M, aξ ^ l = 0 := by
    apply Subtype.ext
    simpa [aξ] using hsum
  have hres : res ((M : ℕ) : A) = res 0 := by
    have := congrArg res hsumA
    rw [map_sum] at this
    simp only [map_pow, hresξ, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at this
    rw [map_natCast, this]
  rw [key] at hres
  apply hMk
  simpa using hres
end GlobalTheory
