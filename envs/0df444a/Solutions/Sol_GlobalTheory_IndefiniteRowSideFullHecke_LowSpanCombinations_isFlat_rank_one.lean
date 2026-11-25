-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations.isFlat_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:53:08.063789+00:00
-- url     : https://prove2.me/submissions/30e3f760-a9a2-476c-a9ba-4d3e61f03a9a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_LowSpanCombinations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
theorem _root_.solution (X : Data E 1) (x0 : Frame X.Ψ 1) (h0 : x0 ∈ X.dom) :
    IsFlat X 0 (fun _ : Fin 1 => fun _ => 1) (fun _ => 1) (fun _ _ => 0) (fun _ : Fin 1 => x0) := by
  have hE : IsEmpty (Ent X) := ⟨fun p => absurd p.2.2 (by rw [Subsingleton.elim p.2.1.2 p.2.1.1]; exact lt_irrefl _)⟩
  have hnd : nd X = 0 := Fintype.card_eq_zero
  have hF : IsEmpty (Fin (nd X)) := by rw [hnd]; infer_instance
  have hV : Subsingleton (V (nd X)) := ⟨fun u v => by ext i; exact hF.elim i⟩
  have hsame : ∀ x ∈ X.dom, SamePt X x0 x := by
    intro x hx
    have ha : ∀ τ, x0 τ 0 0 ≠ 0 := fun τ => by simpa [mat] using (h0 τ).1
    have hb : ∀ τ, x τ 0 0 ≠ 0 := fun τ => by simpa [mat] using (hx τ).1
    refine ⟨1, X.Γ.one_mem, fun τ _ _ => x τ 0 0 / x0 τ 0 0, fun τ => ⟨?_, fun a c h => ?_⟩, ?_⟩
    · simpa [mat] using ⟨hb τ, ha τ⟩
    · exact absurd h (by rw [Subsingleton.elim c a]; exact lt_irrefl _)
    · funext τ a c
      rw [Subsingleton.elim a 0, Subsingleton.elim c 0]
      have := ha τ
      simp [lact, rmul, mat, Matrix.mul_apply]
      change x τ 0 0 = ∑ j : Fin 1, x0 τ 0 j * (x τ 0 0 / x0 τ 0 0)
      simp only [Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero]
      field_simp
  have hχ : ∀ γ ∈ X.Γ, X.χ 0 γ = 1 := by
    intro γ hγ
    obtain ⟨n, hn, h⟩ := X.χ_fin 0
    have hne : X.χ 0 γ ≠ 0 := fun e => by
      have := h γ hγ
      rw [e, zero_pow hn.ne'] at this
      exact zero_ne_one this
    have h2 := X.χ_add 0 0 γ hγ
    rw [add_zero] at h2
    exact (mul_right_eq_self₀.1 h2.symm).resolve_right hne
  have hp : ∀ x, X.pnorm 0 (fun _ => 1) x = 1 := fun x => by simp [Data.pnorm]
  refine ⟨fun _ => ⟨differentiableOn_const _, fun x _ b _ => by simp [bchar],
      fun γ hγ x _ => by simp [hχ γ hγ]⟩, ⟨fun _ => 1, fun _ _ => by simp⟩,
    fun _ => ⟨fun _ => 0, fun _ _ => by simp⟩, fun x _ => by simp [famNorm, hp], Nat.one_pos,
    fun _ => h0, fun _ _ _ => Subsingleton.elim _ _,
    fun x hx => ⟨fun _ => ⟨0, hsame x hx⟩, fun _ _ => rfl⟩, fun _ => one_ne_zero,
    fun _ => ⟨ContinuousLinearEquiv.refl ℂ _, ?_⟩,
    fun U _ hU => ⟨0, fun x hx h => absurd (hsame x hx) (h x0 (hU 0) h0)⟩,
    1, fun x _ => ?_⟩
  · have := hasFDerivAt_of_subsingleton (𝕜 := ℂ) (zMap X (fun _ => 1) (fun _ _ => 0) x0) 0
    convert this using 1
    ext v i
    exact hF.elim i
  · unfold famNorm
    rw [Fintype.sum_option]
    simp [hp]
end GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
