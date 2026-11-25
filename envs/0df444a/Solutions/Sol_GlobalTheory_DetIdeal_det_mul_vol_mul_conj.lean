-- Prove2me | solution 1 for GlobalTheory.DetIdeal.det_mul_vol_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:39:29.292461+00:00
-- url     : https://prove2.me/submissions/c6365a49-71f2-4120-a6ec-c1726bec4574

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
import Theorems.Thm_GlobalTheory_DetIdeal_det_mem_vol
import Theorems.Thm_GlobalTheory_DetIdeal_map_vol
import Theorems.Thm_GlobalTheory_DetIdeal_det_mul_vol_eq
import Theorems.Thm_GlobalTheory_DetIdeal_exists_det_ne_zero
import Theorems.Thm_GlobalTheory_DetIdeal_herm_eq
import Theorems.Thm_GlobalTheory_HermModel_herm_smul_right
import Theorems.Thm_GlobalTheory_HermModel_rank_integral_selfDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DetIdeal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.DetIdeal
theorem _root_.solution (H : Host E) (D : Datum H) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (hξ : FD.cc ξ = -ξ) (hξ0 : ξ ≠ 0)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
      (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)))
    (n : 𝓞 E) (hn : n ≠ 0)
    (hint : ∀ z, ∃ x : Fin r → 𝓞 E, algebraMap (𝓞 E) E ∘ x = algebraMap (𝓞 E) E n • φ z) :
    ∃ I : Ideal (𝓞 E), I ≠ ⊥ ∧
      FractionalIdeal.spanSingleton (𝓞 E)⁰ ((ξ / ((n : E) * FD.cc (n : E))) ^ r * Gm.det) *
        ((I * I.map (H.bar : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ^ r := by
  obtain ⟨-, -, -, hdual⟩ := HermModel.rank_integral_selfDual E H D r ξ Gm φ hξ h
  obtain ⟨-, hspan, -, hdet, -⟩ := h
  have hsm : ∀ (a : 𝓞 E) (x : D.La), φ (a • x) = (a : E) • φ x := fun a x => by
    rw [map_smul]; rfl
  have hnE : (n : E) ≠ 0 := by exact_mod_cast hn
  have hcn : FD.cc (n : E) ≠ 0 := by simpa [FD.cc] using hn
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  set L : Set (Fin r → 𝓞 E) := {x | ∃ z, algebraMap (𝓞 E) E ∘ x = (n : E) • φ z} with hL
  have hvol : vol L ≠ ⊥ := by
    obtain ⟨Y, hY, hYd⟩ := exists_det_ne_zero _ hspan
    choose z hz using hY
    choose x hx using hint
    intro hb
    have hm : (Matrix.of fun i => x (z i)).det ∈ vol L := det_mem_vol fun i => ⟨z i, hx _⟩
    rw [hb, Ideal.mem_bot] at hm
    have : (Matrix.of fun i => x (z i)).map (algebraMap (𝓞 E) E) = (n : E) • Y := by
      ext i j
      have := congrFun (hx (z i)) j
      rw [hz] at this
      exact this
    have h2 := RingHom.map_det (algebraMap (𝓞 E) E) (Matrix.of fun i => x (z i))
    rw [hm, map_zero, RingHom.mapMatrix_apply, this, Matrix.det_smul] at h2
    exact mul_ne_zero (pow_ne_zero _ hnE) hYd h2.symm
  refine ⟨vol L, hvol, ?_⟩
  have hvol' : (vol L).map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    rwa [Ne, Ideal.map_eq_bot_iff_of_injective (f := (H.bar : 𝓞 E →+* 𝓞 E)) H.bar.injective]
  have hd : (ξ / ((n : E) * FD.cc (n : E))) ^ r * Gm.det = ((ξ / ((n : E) * FD.cc (n : E))) • Gm).det := by
    rw [Matrix.det_smul, Fintype.card_fin]
  rw [map_vol] at hvol' ⊢
  rw [hd]
  refine det_mul_vol_eq _ (FractionalIdeal.dual_ne_zero ℤ ℚ h1) _ _ _ ?_ hvol' ?_
  · rw [← hd]
    exact mul_ne_zero (pow_ne_zero _ (div_ne_zero hξ0 (mul_ne_zero hnE hcn))) hdet
  intro v
  have hpair : ∀ (x : Fin r → 𝓞 E) (z : D.La), algebraMap (𝓞 E) E ∘ x = (n : E) • φ z →
      v ⬝ᵥ ((ξ / ((n : E) * FD.cc (n : E))) • Gm) *ᵥ
          (algebraMap (𝓞 E) E ∘ ((H.bar : 𝓞 E →+* 𝓞 E) ∘ x)) =
        ξ * FD.herm Gm ((n : E)⁻¹ • v) (φ z) := fun x z hx => by
    have e : algebraMap (𝓞 E) E ∘ ((H.bar : 𝓞 E →+* 𝓞 E) ∘ x) =
        FD.cc (n : E) • fun b => FD.cc (φ z b) := by
      funext b
      have := congrFun hx b
      simp only [Function.comp, Pi.smul_apply, smul_eq_mul] at this ⊢
      have h3 : algebraMap (𝓞 E) E ((H.bar : 𝓞 E →+* 𝓞 E) (x b)) = FD.cc (algebraMap (𝓞 E) E (x b)) :=
        H.bar_eq (x b)
      rw [h3, this]
      simp [FD.cc]
    rw [e, herm_eq, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, smul_dotProduct]
    simp only [smul_eq_mul]
    field_simp
  have hiff : (∃ x ∈ L, algebraMap (𝓞 E) E ∘ x = v) ↔ (n : E)⁻¹ • v ∈ LinearMap.range φ := by
    constructor
    · rintro ⟨x, ⟨z, hz⟩, rfl⟩
      exact ⟨z, by rw [hz, smul_smul, inv_mul_cancel₀ hnE, one_smul]⟩
    · rintro ⟨z, hz⟩
      obtain ⟨x, hx⟩ := hint z
      refine ⟨x, ⟨z, hx⟩, ?_⟩
      rw [hx, hz, smul_smul]
      change ((n : E) * (n : E)⁻¹) • v = v
      rw [mul_inv_cancel₀ hnE, one_smul]
  rw [hiff, ← hdual]
  constructor
  · intro hv z
    obtain ⟨x, hx⟩ := hint z
    have h4 := hv _ ⟨x, ⟨z, hx⟩, rfl⟩
    rw [hpair x z hx, FractionalIdeal.mem_dual h1] at h4
    obtain ⟨k, hk⟩ := h4 1 (FractionalIdeal.one_mem_one _)
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, mul_one] at hk
    simpa using hk.symm
  · rintro hv _ ⟨x, ⟨z, hx⟩, rfl⟩
    rw [hpair x z hx, FractionalIdeal.mem_dual h1]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨k, hk⟩ := hv (H.bar.symm b • z)
    have hc : FD.cc ((H.bar.symm b : 𝓞 E) : E) = b := by
      rw [FD.cc, ← H.bar_eq, RingEquiv.apply_symm_apply]
    rw [hsm, HermModel.herm_smul_right, hc, ← mul_assoc] at hk
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hk.symm
end GlobalTheory.DetIdeal
