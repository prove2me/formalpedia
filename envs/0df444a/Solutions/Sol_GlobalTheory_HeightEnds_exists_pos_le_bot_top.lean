-- Prove2me | solution 1 for GlobalTheory.HeightEnds.exists_pos_le_bot_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:43:47.654814+00:00
-- url     : https://prove2.me/submissions/374a0b11-8da6-4f9a-98aa-881a42f13e76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightBotTop
import Theorems.Thm_GlobalTheory_HeightEnds_norm_det_orth
import Theorems.Thm_GlobalTheory_HeightEnds_gramDet_square
import Theorems.Thm_GlobalTheory_LatBasis_exists_basis_mem
import Theorems.Thm_GlobalTheory_SpanIndex_relIndex_span_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.HeightEnds
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HeightEnds
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∃ m : ℝ, 0 < m ∧ ∀ x, IsOrth X x → m ≤ d x ⊥ ∧ m ≤ d x ⊤) := by
  intro r X d hd
  obtain ⟨w0, hw0, hΛ0, hsp0⟩ := GlobalTheory.LatBasis.exists_basis_mem r X ⊤
  have hr : r = Module.finrank E (⊤ : Submodule E (Fin r → E)) := by simp
  let w : Fin r → Fin r → E := w0 ∘ finCongr hr
  have hw : LinearIndependent E w := hw0.comp _ (finCongr hr).injective
  have hΛ : ∀ a, w a ∈ X.Λ := fun a => hΛ0 _
  have hsp : Submodule.span E (Set.range w) = ⊤ := by
    rw [(finCongr hr).surjective.range_comp]; exact hsp0
  have hdet : (Matrix.of w).det ≠ 0 := by
    have : IsUnit (Matrix.of w) := Matrix.linearIndependent_rows_iff_isUnit.1 hw
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hind := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X (Fin r) w hw hΛ
  set n : ℕ := (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup) with hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hind)
  let c : ℝ := (∏ τ : X.Ψ, ‖τ.1 X.Gm.det‖ * ‖τ.1 (Matrix.of w).det‖ ^ 2) / n
  have hc : 0 < c := by
    refine div_pos (Finset.prod_pos fun τ _ => mul_pos ?_ (pow_pos ?_ 2)) hnpos
    · exact norm_pos_iff.2 ((map_ne_zero τ.1).2 X.Gm_det)
    · exact norm_pos_iff.2 ((map_ne_zero τ.1).2 hdet)
  refine ⟨min 1 c, lt_min one_pos hc, fun x hx => ?_⟩
  have hxd : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := by
    intro τ h0
    have := norm_det_orth X x hx τ
    simp [h0] at this
  constructor
  · have h := hd x hxd Empty (fun a => a.elim) linearIndependent_empty_type (fun a => a.elim)
    have hre : Set.range (fun a : Empty => (a.elim : Fin r → E)) = ∅ := Set.range_eq_empty _
    rw [hre] at h
    simp only [Submodule.span_empty, Matrix.det_isEmpty, Complex.one_re, Finset.prod_const_one,
      Submodule.bot_toAddSubgroup, inf_bot_eq, AddSubgroup.relIndex_self, Nat.cast_one,
      div_one] at h
    rw [h]
    exact min_le_left _ _
  · have h := hd x hxd (Fin r) w hw hΛ
    rw [← hn, hsp] at h
    rw [h]
    refine (min_le_right _ _).trans (le_of_eq ?_)
    refine congrArg (· / (n : ℝ)) (Finset.prod_congr rfl fun τ _ => ?_)
    have h1 : (Matrix.of fun k a => τ.1 (w a k)).det = τ.1 (Matrix.of w).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_transpose]
      rfl
    have h2 := norm_det_orth X x hx τ
    have h3 : ‖(mat x τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hxd τ)
    rw [gramDet_square, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h1, norm_mul,
      norm_inv, mul_pow, inv_pow]
    congr 1
    exact eq_inv_of_mul_eq_one_right h2
end GlobalTheory.HeightEnds
