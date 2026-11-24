-- Prove2me | solution 1 for GlobalTheory.CMFormBound.formClaims
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:20:34.054466+00:00
-- url     : https://prove2.me/submissions/83ce2e07-e784-4607-8eeb-e257e5179d7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral
import Theorems.Thm_GlobalTheory_CMFormBound_ord_mul
import Theorems.Thm_GlobalTheory_CMFormBound_ord_of_not_mem
import Theorems.Thm_GlobalTheory_CMFormBound_ord_natCast_ne
import Theorems.Thm_GlobalTheory_CMFormBound_val_of_ne
import Theorems.Thm_GlobalTheory_CMFormBound_val_mul
import Theorems.Thm_GlobalTheory_CMFormBound_conj_sqrt
import Theorems.Thm_GlobalTheory_CMFormBound_eig_ext
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CMFormBound
namespace GlobalTheory.CMFormBound
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → (∀ i, 0 ≤ val_vp O l (algebraMap O K (B (e i) (f i))) ∧ val_vp O l (algebraMap O K (B (e i) (f i))) ≤ val_vp O l (algebraMap O K D)) → (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) → FormClaims l φ ρ B D e f := by
  intro E _ _ _ c hc l hl O _ _ _ _ K _ _ _ hlm hcard D hD hCl I _ φ hφ H _ _ ρ Fil B hLat hEig e f hgens hB hρE
  refine ⟨hρE, ?_⟩
  intro ρE hρE' d r ξ hd hr hξ hξ0 hval
  have hconjr := conj_sqrt E d hd r hr
  have ha_real : IsCMField.complexConj E (ξ * r) = ξ * r := by
    rw [map_mul, hξ, hconjr, neg_mul_neg]
  have hr0 : r ≠ 0 := by
    rintro rfl
    have h0 : (d : E) = 0 := by
      rw [zero_pow two_ne_zero] at hr
      exact neg_eq_zero.1 hr.symm
    exact hd.ne_zero (by exact_mod_cast h0)
  have ha0 : ξ * r ≠ 0 := mul_ne_zero hξ0 hr0
  have hinv : ρE (ξ * r) * ρE (ξ * r)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha0, map_one]
  have hinv' : ρE (ξ * r)⁻¹ * ρE (ξ * r) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha0, map_one]
  refine ⟨⟨(IsCMField.complexConj_eq_self_iff E (ξ * r)).1 ha_real, ha0⟩, ?_, ?_⟩
  · refine ⟨(B.baseChange K).compl₂ (ρE (ξ * r)), ?_, ?_⟩
    · intro x y
      rw [LinearMap.compl₂_apply, ← Module.End.mul_apply, hinv, Module.End.one_apply]
    · intro BF' hBF'
      refine LinearMap.ext₂ fun x y => ?_
      rw [LinearMap.compl₂_apply, hBF' x (ρE (ξ * r) y), ← Module.End.mul_apply, hinv', Module.End.one_apply]
  · intro BF hBF i
    have hBFxy : ∀ x y, BF x y = B.baseChange K x (ρE (ξ * r) y) := by
      intro x y
      rw [hBF x (ρE (ξ * r) y), ← Module.End.mul_apply, hinv', Module.End.one_apply]
    have hfmem : inK K H (f i) ∈ eigK ρ (bar (φ i)) := by
      have : f i ∈ eigLat ρ (bar (φ i)) := by
        rw [(hgens i).2]
        exact Submodule.mem_span_singleton_self _
      exact this
    have heig := eig_ext hc ρ ρE hρE' (bar (φ i)) _ hfmem (ξ * r)
    have hbar : bar (φ i) (ξ * r) = φ i (ξ * r) := by
      show φ i (IsCMField.complexConj E (ξ * r)) = _
      rw [ha_real]
    have hK : B.baseChange K (inK K H (e i)) (inK K H (f i)) = algebraMap O K (B (e i) (f i)) := by
      simp [inK, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]
    have hval1 : BF (inK K H (e i)) (inK K H (f i)) = φ i (ξ * r) * algebraMap O K (B (e i) (f i)) := by
      rw [hBFxy, heig, hbar, LinearMap.map_smul, smul_eq_mul, hK]
    have hD0 : algebraMap O K D ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hD
    have hB0 : algebraMap O K (B (e i) (f i)) ≠ 0 := by
      intro h0
      have h1 := (hB i).2
      rw [h0, val_vp, if_pos rfl, val_of_ne O l hD0, top_le_iff] at h1
      exact WithTop.coe_ne_top h1
    have hφξ : φ i ξ ≠ 0 := (map_ne_zero _).2 hξ0
    have hφr : φ i r ≠ 0 := (map_ne_zero _).2 hr0
    have hF0 : BF (inK K H (e i)) (inK K H (f i)) ≠ 0 := by
      rw [hval1]
      exact mul_ne_zero ((map_ne_zero _).2 ha0) hB0
    have hlne : ord_vw O (l : K) ≠ 0 := ord_natCast_ne O l hl.ne_zero hlm
    have hvr : val_vp O l (φ i r) = (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) := by
      have hsq : φ i r * φ i r = -1 * (d : K) := by
        rw [← map_mul, ← sq, hr, map_neg, map_natCast]; ring
      have hdK : (d : K) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hsq
        exact hφr (mul_self_eq_zero.1 hsq)
      have hm1 : ord_vw O ((-1 : K)) = 0 := by
        have := ord_of_not_mem O (K := K) (-1 : O) (by
          intro h; exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
            ((Ideal.eq_top_iff_one _).2 (by simpa using (IsLocalRing.maximalIdeal O).neg_mem h)))
        simpa using this
      have hord := congrArg (ord_vw O) hsq
      rw [ord_mul O hφr hφr, ord_mul O (by norm_num) hdK, hm1, zero_add] at hord
      rw [val_of_ne O l hφr]
      by_cases hld : l = d
      · subst hld
        rw [if_pos rfl]
        congr 1
        have : (ord_vw O (φ i r) : ℚ) * 2 = ord_vw O ((l : ℕ) : K) := by exact_mod_cast (by linarith : ord_vw O (φ i r) * 2 = ord_vw O ((l : ℕ) : K))
        have hq : (ord_vw O ((l : ℕ) : K) : ℚ) ≠ 0 := by exact_mod_cast hlne
        field_simp
        linarith
      · rw [if_neg hld]
        have hdu : (d : O) ∉ IsLocalRing.maximalIdeal O := by
          intro hdm
          have hcop : IsCoprime (d : ℤ) (l : ℤ) :=
            Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hd hl).2 (Ne.symm hld))
          obtain ⟨u, w, huw⟩ := hcop
          have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
            have := congrArg (Int.cast : ℤ → O) huw
            push_cast at this
            rw [← this]
            exact add_mem (Ideal.mul_mem_left _ _ hdm) (Ideal.mul_mem_left _ _ hlm)
          exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
        have hd0 : ord_vw O ((d : ℕ) : K) = 0 := by
          have := ord_of_not_mem O (K := K) (d : O) hdu
          simpa using this
        rw [hd0] at hord
        have : ord_vw O (φ i r) = 0 := by linarith
        rw [this]
        simp
    have hvF : val_vp O l (BF (inK K H (e i)) (inK K H (f i))) =
        val_vp O l (algebraMap O K (B (e i) (f i))) + val_vp O l (φ i ξ) + val_vp O l (φ i r) := by
      rw [hval1, map_mul, val_mul O l (mul_ne_zero hφξ hφr) hB0, val_mul O l hφξ hφr]
      rw [add_comm, add_assoc]
    refine ⟨hval1, hF0, hvF, hvr, ?_⟩
    rw [hvF, hvr]
    calc val_vp O l (algebraMap O K (B (e i) (f i))) + val_vp O l (φ i ξ) + (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ)
        ≤ val_vp O l (algebraMap O K D) + 0 + (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) := by
          gcongr
          · exact (hB i).2
          · exact hval (φ i)
      _ = _ := by rw [add_zero]
end GlobalTheory.CMFormBound
