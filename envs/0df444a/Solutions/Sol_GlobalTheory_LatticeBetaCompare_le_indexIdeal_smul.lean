-- Prove2me | solution 1 for GlobalTheory.LatticeBetaCompare.le_indexIdeal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:32:00.203145+00:00
-- url     : https://prove2.me/submissions/4976925a-5561-46df-85ba-c641f2b3f57f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
import Theorems.Thm_GlobalTheory_exists_pseudoCoords
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBetaCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace GlobalTheory.LatticeBetaCompare
theorem _root_.solution {L' L : Submodule (𝓞 E) (Fin n → E)} (hle : L ≤ L') (hfg : L'.FG)
    (hsp : Submodule.span E (L' : Set (Fin n → E)) = ⊤) : detSpan L ≤ indexIdeal L' L • detSpan L' := by
  classical
  obtain ⟨-, f, c, hf, hc, hΛ, -⟩ :=
    exists_pseudoCoords (R := 𝓞 E) (K := E) n (Fin n → E) (by simp) L' ⊤ hfg hsp
  set F : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' (LinearMap.pi f) with hF
  have hFv : ∀ v, F.mulVec v = fun a => f a v := fun v => by rw [hF, LinearMap.toMatrix'_mulVec]; rfl
  have hF0 : F.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    rw [hFv] at hv
    exact hv0 (hf v fun a => congrFun hv a)
  have hint : ∀ a, ∀ y ∈ (c a)⁻¹, ∀ z ∈ c a, ∃ b : 𝓞 E, (b : E) = y * z := fun a y hy z hz =>
    (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff (hc a)).1 hy z hz)
  rw [detSpan, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  set W : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => w j i with hW
  have h1 : (1 : E) ∈ Submodule.span (𝓞 E)
      (∏ a, ((((c a)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) * (c a : Set E))) := by
    rw [← Submodule.prod_span]
    have : ∀ a, Submodule.span (𝓞 E) ((((c a)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) * (c a : Set E)) = 1 := by
      intro a
      rw [← Submodule.span_mul_span, ← FractionalIdeal.coe_one (S := (𝓞 E)⁰), ← inv_mul_cancel₀ (hc a),
        FractionalIdeal.coe_mul]
      congr 1 <;> exact Submodule.span_eq _
    simp only [this, Finset.prod_const_one]
    exact Submodule.mem_one.2 ⟨1, map_one _⟩
  have key : ∀ z ∈ Submodule.span (𝓞 E)
      (∏ a, ((((c a)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) * (c a : Set E))),
      z * W.det ∈ indexIdeal L' L • detSpan L' := by
    intro z hz
    induction hz using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := (Set.mem_fintype_prod _ _).1 hz
      choose y hy t ht hyt using hu
      obtain rfl : u = fun a => y a * t a := funext fun a => (hyt a).symm
      choose b hb using fun a i => hint a _ (hy a) _ ((hΛ _).1 (hle (hw i)) a)
      have hB : (((Matrix.of b).det : 𝓞 E) : E) = W.det * ((∏ a, y a) * F.det) := by
        have : (algebraMap (𝓞 E) E).mapMatrix (Matrix.of b) = Matrix.diagonal y * F * W := by
          ext a i
          rw [Matrix.mul_assoc, Matrix.diagonal_mul]
          exact (hb a i).trans (congrArg _ (congrFun (hFv (w i)) a).symm)
        change algebraMap (𝓞 E) E _ = _
        rw [RingHom.map_det, this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_comm]
      have hI : (Matrix.of b).det ∈ indexIdeal L' L := by
        refine Ideal.subset_span ⟨Matrix.toLin' (W * (Matrix.diagonal y * F)), fun x hx => ?_, ?_⟩
        · choose b' hb' using fun a => hint a _ (hy a) _ ((hΛ _).1 hx a)
          have : Matrix.toLin' (W * (Matrix.diagonal y * F)) x = ∑ a, b' a • w a := by
            rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hFv]
            ext i
            simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
            change ∑ a, W i a * (Matrix.diagonal y).mulVec (fun a => f a x) a = _
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Matrix.mulVec_diagonal, ← hb', mul_comm]
            rfl
          rw [this]
          exact Submodule.sum_mem _ fun a _ => L.smul_mem _ (hw a)
        · rw [LinearMap.det_toLin', Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hB]
      have hV : (F.det)⁻¹ * ∏ a, t a ∈ detSpan L' := by
        refine Submodule.subset_span ⟨fun i => F⁻¹.mulVec (Pi.single i (t i)), fun i => (hΛ _).2 fun a => ?_, ?_⟩
        · have := congrFun (hFv (F⁻¹.mulVec (Pi.single i (t i)))) a
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hF0.isUnit, Matrix.one_mulVec] at this
          rw [← this]
          by_cases h : a = i
          · subst h; simpa using ht a
          · rw [Pi.single_eq_of_ne h]; exact (c a).zero_mem
        · have : (Matrix.of fun i j => F⁻¹.mulVec (Pi.single j (t j)) i) = F⁻¹ * Matrix.diagonal t := by
            ext i j
            simp [Matrix.mul_diagonal]
          rw [this, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      have := Submodule.smul_mem_smul hI hV
      convert this using 1
      rw [Algebra.smul_def, Finset.prod_mul_distrib]
      change _ = (((Matrix.of b).det : 𝓞 E) : E) * _
      rw [hB]
      field_simp
  simpa using key 1 h1
end GlobalTheory.LatticeBetaCompare
