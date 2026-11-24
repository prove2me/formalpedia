-- Prove2me | solution 1 for GlobalTheory.KeyPow.value_at_normalForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:18:58.074852+00:00
-- url     : https://prove2.me/submissions/0ed0c04f-c39d-48b5-90e9-2d2fb52a57bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ValueAtNormalForm
import Theorems.Thm_GlobalTheory_KeyPow_exists_sec_div
import Theorems.Thm_GlobalTheory_KeyPow_smul_one_row
import Theorems.Thm_GlobalTheory_LieComb_lieComb_algebra
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_UnifDifferential_isDiff_of_isLieComb
import Theorems.Thm_P2M_GlobalTheory_valAt__constFn_1b31686fad50
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyPow
namespace GlobalTheory.KeyPow
theorem _root_.solution :
    ∀ (N : ℕ → ℕ) (g₀ : ℕ) (κ : KeyIn ℂ → ℂˣ) (g : ℕ) (a b : Fin g → ℂ), g₀ ≤ g → GlobalTheory.KeyPow.ClauseH ℂ N g₀ κ → (∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 → κ x = 1) → ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c : ℂ), c ≠ 0 → M.det ≠ 0 → GlobalTheory.KeyPow.NormalAt x τ M (fun i => a (i.cast h)) (fun i => b (i.cast h)) c → (κ x : ℂ) = (M.det ^ 4 / c ^ 8) ^ N g := by
  intro N g₀ κ g a b hg₀ hH hN x h τ M c hc hM hx
  obtain ⟨P, hg, rig, hr, th, hth, v, hv⟩ := x
  dsimp only at h τ M
  subst h
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hx
  haveI := P.isAb.comm
  obtain ⟨ex, tan, comp, sgl, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v hv.1
  choose v₀ hv₀ using fun i => (ex (M⁻¹ i)).exists
  have hb₀ : IsLieBasis v₀ := (bas M⁻¹ v₀ hv hv₀).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit)
  obtain ⟨ex₀, -, -, -, -⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v₀ hb₀.1
  have hMv : ∀ i, IsLieComb (M i) v₀ (v i) := fun i => by
    obtain ⟨w, hw⟩ := (ex₀ (M i)).exists
    have h1 := comp _ (fun i => M⁻¹ i) v₀ (M i) w hv₀ hw
    have e : ∑ j, M i j • M⁻¹ j = Pi.single i 1 := by
      rw [← Matrix.vecMul_eq_sum]
      refine (congrFun (Matrix.mul_nonsing_inv M hM.isUnit) i).trans ?_
      simpa using smul_one_row (1 : ℂ) i
    rw [e] at h1
    rwa [(ex _).unique (sgl i) h1]
  obtain ⟨th₀, e₀, e₁, hle⟩ := exists_sec_div P.A.hom (mul_inv_cancel₀ hc) th
  have hth₀ : ∀ s : Sp ℂ, ∃ y : P.A.left, P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th₀ :=
    fun s => (hth s).imp fun y hy => ⟨hy.1, hle hy.2⟩
  have h0 : κ ⟨P, hg, rig, hr, th₀, hth₀, v₀, hb₀⟩ = 1 := by
    refine hN ⟨P, hg, rig, hr, th₀, hth₀, v₀, hb₀⟩ rfl τ ⟨u, h₁, h₂, h₃, h₄, ?_, ?_⟩
    · intro i z hz
      have e := h₅ i z hz
      refine ((congrArg (valAt' _ _) (e₀ i)).trans (valAt'_mul _ _ _ _)).trans ?_
      rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
      refine (congrArg (c⁻¹ * ·) e).trans ?_
      beta_reduce
      rw [_root_.one_mul, ← _root_.mul_assoc, inv_mul_cancel_left₀ hc]
    · intro i
      have h1 := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 h₆ (hv₀ i)
      have e : ∑ j, M⁻¹ i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
          (2 * Real.pi * Complex.I : ℂ)⁻¹ • (1 : Matrix (Fin P.g) (Fin P.g) ℂ) i := by
        simp only [smul_comm (M⁻¹ i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
        rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum, ← Matrix.nonsing_inv_mul M hM.isUnit]
        rfl
      rwa [e] at h1
  have h1 := hH P hg rig hr _ hth₀ v₀ hb₀ th hth v hv c M hg₀ e₁ hMv
  rw [h0, Units.val_one, _root_.mul_one] at h1
  rw [div_pow, ← pow_mul, ← pow_mul, eq_div_iff (pow_ne_zero _ hc), mul_comm]
  exact h1
end GlobalTheory.KeyPow
