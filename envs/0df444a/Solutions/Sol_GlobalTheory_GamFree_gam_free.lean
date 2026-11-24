-- Prove2me | solution 1 for GlobalTheory.GamFree.gam_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:39:50.760859+00:00
-- url     : https://prove2.me/submissions/ec7e4e97-afa0-477b-bf0e-d954d59c79cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BoundedPowOfTriangularIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
import Theorems.Thm_GlobalTheory_GamFree_pow_bounded
import Theorems.Thm_GlobalTheory_GamFree_gram_unitary
import Theorems.Thm_GlobalTheory_GamFree_isOfFinOrder_of_bounded
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_gram_isHermitian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GamFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.GamFree
theorem _root_.solution : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 M : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ a b, FD.cc (Gm a b) = Gm b a) → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → 3 ≤ M → FD.IsUStab Gm Λ γ → (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w) → ∀ x ∈ FD.GG Ψ Gm p0, ∀ b ∈ FD.Bor Ψ r, FD.lact γ x = FD.rmul x b → γ = 1 := by
  intro hMink E _ _ _ r p0 M Ψ Gm Λ γ hΨ hG hfg hsp hM hγ hcong x hx b hb hxb
  have hbd : ∀ τ : Ψ, ∃ R : ℝ, ∀ (k : ℕ) (i j : Fin r),
      ‖((((γ : Matrix (Fin r) (Fin r) E)).map τ.1) ^ k) i j‖ ≤ R := by
    intro τ
    have hg : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * FD.mat x τ = FD.mat x τ * FD.mat b τ :=
      congrFun hxb τ
    refine pow_bounded _ (FD.mat x τ) (FD.mat b τ) (FD.gram τ.1 Gm (FD.mat x τ)) (hx τ).1
      (fun a c h => (hb τ).2 a c h) (FD.gram_isHermitian τ.1 hG _) (fun i h0 => ?_) hg ?_
    · have h := (hx τ).2 i
      have : FD.dmin Gm x τ i = 0 := h0
      rw [this] at h
      simp at h
    · rw [← FD.FrameDegreeData.gram_mul, ← hg, gram_unitary Gm _ hγ.1]
  choose R hR using hbd
  have hfo : IsOfFinOrder γ := by
    refine isOfFinOrder_of_bounded Ψ hΨ Λ hfg hsp γ (fun v hv => (hγ.2 v).1 hv) (∑ τ, |R τ|)
      fun τ k a c => ?_
    have h1 := hR τ k a c
    rw [← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)))
  obtain ⟨n, hn, hγn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfo
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  have : Module.Free ℤ Λ := inferInstance
  have hpow : ∀ (k : ℕ) (v : Λ), (((restrict Λ γ hγ.2) ^ k) v : Fin r → E) =
      ((γ : Matrix (Fin r) (Fin r) E) ^ k) *ᵥ v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec]
      rfl
  have hσ := hMink Λ (restrict Λ γ hγ.2) n M hn (by
    ext v : 1
    apply Subtype.ext
    rw [hpow, ← Units.val_pow_eq_pow_val, hγn]
    simp) hM (fun y => by
      obtain ⟨w, hw, h⟩ := hcong y y.2
      exact ⟨⟨w, hw⟩, Subtype.ext h⟩)
  have hfix : ∀ v ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v hv => by
    have := hpow 1 ⟨v, hv⟩
    rw [hσ] at this
    simpa using this.symm
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext_on hsp
  intro v hv
  simpa using hfix v hv
end GlobalTheory.GamFree
