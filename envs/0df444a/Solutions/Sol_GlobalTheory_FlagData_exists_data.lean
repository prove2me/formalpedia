-- Prove2me | solution 1 for GlobalTheory.FlagData.exists_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:50:03.818251+00:00
-- url     : https://prove2.me/submissions/e026f4ae-5b20-49ee-a81d-7211ce7e5946

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CongruenceFiniteIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmulMemOfIsIntegral
import Theorems.Thm_GlobalTheory_FlagData_herm_transvMat
import Theorems.Thm_GlobalTheory_FlagData_smul_mem_of_isIntegral
import Theorems.Thm_GlobalTheory_CongruenceIndex_congruence_finiteIndex
import Theorems.Thm_GlobalTheory_GamFree_gam_free


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
open GlobalTheory GlobalTheory.FlagData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FlagData
theorem _root_.solution : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 M m : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (ξ0 κ0 : E), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ a b, FD.cc (Gm a b) = Gm b a) → Gm.det ≠ 0 → p0 ≤ r → (∀ τ ∈ Ψ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → 3 ≤ M → FD.cc ξ0 = -ξ0 → ξ0 ≠ 0 → (κ0 = 2 * ξ0 ∨ κ0 = -(2 * ξ0)) → (∀ τ ∈ Ψ, (τ κ0).im < 0) → 0 < m → (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((m : E) / (M : E) * κ0 * FD.herm Gm x y)) → ∃ X : FD.Data E r, X.Ψ = Ψ ∧ X.Gm = Gm ∧ X.p0 = p0 ∧ X.Λ = Λ ∧ X.ξ0 = ξ0 ∧ X.κ0 = κ0 ∧ X.m = m ∧ (∀ γ, γ ∈ X.Γ ↔ FD.IsUStab Gm Λ γ ∧ (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)) ∧ ∀ la γ, X.χ la γ = 1 := by
  intro hMink E _ _ _ r p0 M m Ψ Gm Λ ξ0 κ0 hΨ hG hdet hp hsig hfg hsp hM hξ hξ0 hκ hκs hm hint
  obtain ⟨Γ, hΓ, hidx⟩ :=
    GlobalTheory.CongruenceIndex.congruence_finiteIndex E r M Gm Λ hfg (by omega)
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hκ0 : κ0 ≠ 0 := by rcases hκ with h | h <;> simp [h, hξ0]
  have hξ' : IsCMField.complexConj E ξ0 = -ξ0 := hξ
  have hκc : IsCMField.complexConj E κ0 = -κ0 := by
    rcases hκ with h | h <;> simp [h, hξ', map_ofNat]
  have halg : IsAlgebraic ℤ (((m : E) / (M : E) * κ0)⁻¹) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
  refine ⟨{
    Ψ := Ψ, cmType := hΨ, Gm := Gm, Gm_herm := hG, Gm_det := hdet, p0 := p0, p0_le := hp
    signature := fun τ => hsig τ.1 τ.2
    Λ := Λ, Λ_fg := hfg, Λ_span := hsp
    den := (k : 𝓞 E), den_ne := Int.cast_ne_zero.2 hk
    Λ_int := fun x hx y hy => ?_
    Γ := Γ, Γ_stab := fun γ h => ((hΓ γ).1 h).1, Γ_index := hidx
    Γ_free := fun γ h => GlobalTheory.GamFree.gam_free hMink E r p0 M Ψ Gm Λ γ hΨ hG hfg hsp hM
      ((hΓ γ).1 h).1 ((hΓ γ).1 h).2
    χ := fun _ _ => 1
    χ_mul := fun _ _ _ _ _ => (mul_one _).symm
    χ_add := fun _ _ _ _ => (mul_one _).symm
    χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow _⟩
    ξ0 := ξ0, ξ0_im := hξ, ξ0_ne := hξ0, κ0 := κ0, κ0_xi := hκ
    κ0_sign := fun τ => hκs τ.1 τ.2
    m := m, m_pos := hm
    transv := fun ξ hξΛ hiso s hs hsi => ?_ },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, hΓ, fun _ _ => rfl⟩
  · have h := hki.mul (hint x hx y hy)
    have e : k • ((m : E) / (M : E) * κ0)⁻¹ * ((m : E) / (M : E) * κ0 * FD.herm Gm x y) =
        (((k : 𝓞 E) : 𝓞 E) : E) * FD.herm Gm x y := by
      rw [zsmul_eq_mul]
      simp only [map_intCast]
      field_simp
    rwa [e] at h
  · have hs' : IsCMField.complexConj E s = s := hs
    have hα : FD.cc ((m : E) * s * κ0) = -((m : E) * s * κ0) := by
      simp [FD.cc, hs', hκc]
    have hMi : IsIntegral ℤ (M : E) := isIntegral_natCast M
    have key : ∀ v ∈ Λ, (s * ((m : E) / (M : E) * κ0 * FD.herm Gm v ξ)) • ξ ∈ Λ := fun v hv =>
      smul_mem_of_isIntegral Λ (hsi.mul (hint v hv ξ hξΛ)) hξΛ
    have e : ∀ v, ((m : E) * s * κ0 * FD.herm Gm v ξ) • ξ =
        M • ((s * ((m : E) / (M : E) * κ0 * FD.herm Gm v ξ)) • ξ) := by
      intro v
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul]
      congr 1
      field_simp
    refine ⟨transv Gm hiso ((m : E) * s * κ0), (hΓ _).2 ⟨⟨herm_transvMat hG hiso hα, fun x => ?_⟩,
      fun v hv => ⟨_, key v hv, ?_⟩⟩, rfl⟩
    · change x ∈ Λ ↔ FD.transvMat Gm ξ ((m : E) * s * κ0) *ᵥ x ∈ Λ
      rw [transvMat_mulVec]
      refine ⟨fun hx => Λ.add_mem hx (by rw [e]; exact nsmul_mem (key x hx) M), fun hx => ?_⟩
      have h := nsmul_mem (key _ hx) M
      rw [← e, herm_add_smul_left, hiso, mul_zero, add_zero] at h
      simpa using Λ.sub_mem hx h
    · change FD.transvMat Gm ξ ((m : E) * s * κ0) *ᵥ v = _
      rw [transvMat_mulVec, e]
end GlobalTheory.FlagData
