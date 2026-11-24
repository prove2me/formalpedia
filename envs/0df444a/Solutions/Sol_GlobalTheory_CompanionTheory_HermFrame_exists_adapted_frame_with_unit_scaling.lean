-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermFrame.exists_adapted_frame_with_unit_scaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:12:14.011824+00:00
-- url     : https://prove2.me/submissions/5531862b-50cf-4841-a794-33ed19cdc4c2

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FrameOfAnisotropicPlaneSplitting
import Theorems.Thm_GlobalTheory_CompanionTheory_HermFrame_herm_smul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_HermFrame_frame_cons
import Theorems.Thm_GlobalTheory_CompanionTheory_HermFrame_adapted_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermFrame
namespace GlobalTheory.CompanionTheory.HermFrame
theorem _root_.solution (hA : StAniso) (hP : StPlane) (hS : StSplit)
    (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] [CharZero L]
    (s : L →+* L) (hs : IsInv s) (δ : L) (hδ : IsDelta s δ) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (h : V → V → L),
      Module.finrank L V = n → IsHerm s h → ∀ Λ Λ' : AddSubgroup V, IsMax h Λ → IsMax h Λ' →
      ∃ (l : ℕ) (e f : Fin l → V) (W : Submodule L V) (u : Fin l → L), (∀ i, u i ≠ 0) ∧
        IsFrame h δ e f W ∧ IsAdapted h e f W (fun _ => 1) Λ ∧ IsAdapted h e f W u Λ' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ h hn hh Λ Λ' hΛ hΛ'
  by_cases hiso : ∃ x, x ≠ 0 ∧ h x x = 0
  · obtain ⟨e, f, u, hu, hee, hff, hef, he, hf, hue, hvf⟩ :=
      hP L s hs δ hδ V h hh hiso Λ Λ' hΛ hΛ'
    have hUm : ∀ x, x ∈ orthPair hh e f ↔ h e x = 0 ∧ h f x = 0 := fun x => Iff.rfl
    obtain ⟨hUh, hdec, hUtop, hmax⟩ := hS L s hs δ hδ V h hh e f (orthPair hh e f) hee hff hef hUm
    have hsu : s u ≠ 0 := (map_ne_zero s).2 hu
    have hee' : h (u • e) (u • e) = 0 := by
      rw [herm_smul_left hh, hh.2.1, hee, mul_zero, mul_zero]
    have hff' : h ((s u)⁻¹ • f) ((s u)⁻¹ • f) = 0 := by
      rw [herm_smul_left hh, hh.2.1, hff, mul_zero, mul_zero]
    have hef' : h (u • e) ((s u)⁻¹ • f) = δ := by
      rw [herm_smul_left hh, hh.2.1, hef, ← mul_assoc, mul_inv_cancel₀ hsu, one_mul]
    have hUm' : ∀ x, x ∈ orthPair hh e f ↔ h (u • e) x = 0 ∧ h ((s u)⁻¹ • f) x = 0 := by
      intro x
      rw [hUm, herm_smul_left hh, herm_smul_left hh]
      have hsi' : s ((s u)⁻¹) ≠ 0 := (map_ne_zero s).2 (inv_ne_zero hsu)
      simp [hsu, hsi']
    obtain ⟨-, -, -, hmax'⟩ :=
      hS L s hs δ hδ V h hh (u • e) ((s u)⁻¹ • f) (orthPair hh e f) hee' hff' hef' hUm'
    obtain ⟨m1, p1⟩ := hmax Λ hΛ he hf
    obtain ⟨m2, p2⟩ := hmax' Λ' hΛ' hue hvf
    have hlt : Module.finrank L (orthPair hh e f) < n := hn ▸ Submodule.finrank_lt hUtop
    obtain ⟨l, e', f', W', u', hu', hfr, ad1, ad2⟩ :=
      ih _ hlt (orthPair hh e f) (fun x y => h x y) rfl hUh _ _ m1 m2
    have hsp1 : ∀ (a b : L), ∀ w ∈ orthPair hh e f,
        (a • e + b • f + w ∈ Λ ↔ ‖a‖ ≤ ‖(1 : L)‖ ∧ ‖b‖ ≤ ‖(1 : L)‖⁻¹ ∧ w ∈ Λ) := by
      intro a b w hw
      simp only [norm_one, inv_one]
      exact p1 a b w hw
    have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu
    have hsp2 : ∀ (a b : L), ∀ w ∈ orthPair hh e f,
        (a • e + b • f + w ∈ Λ' ↔ ‖a‖ ≤ ‖u‖ ∧ ‖b‖ ≤ ‖u‖⁻¹ ∧ w ∈ Λ') := by
      intro a b w hw
      have key := p2 (a * u⁻¹) (b * s u) w hw
      have e1 : (a * u⁻¹) • (u • e) + (b * s u) • ((s u)⁻¹ • f) + w = a • e + b • f + w := by
        rw [smul_smul, smul_smul, mul_assoc, mul_assoc, inv_mul_cancel₀ hu,
          mul_inv_cancel₀ hsu, mul_one, mul_one]
      rw [e1] at key
      rw [key, norm_mul, norm_mul, norm_inv, hs.2.1 u, ← div_eq_mul_inv, div_le_one hpos,
        ← one_div, le_div_iff₀ hpos]
    have h1 : (fun _ : Fin (l + 1) => (1 : L)) = Fin.cons 1 (fun _ : Fin l => (1 : L)) := by
      funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ i => rfl
    refine ⟨l + 1, Fin.cons e fun i => (e' i : V), Fin.cons f fun i => (f' i : V),
      W'.map (orthPair hh e f).subtype, Fin.cons u u', ?_,
      frame_cons hh hUm hee hff hef hdec hfr, ?_, adapted_cons hsp2 ad2⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hu
      | succ i => simpa using hu' i
    · rw [h1]
      exact adapted_cons hsp1 ad1
  · have hiso' : ∀ x, h x x = 0 → x = 0 := by
      intro x hx
      by_contra hne
      exact hiso ⟨x, hne, hx⟩
    have hm : ∀ M : AddSubgroup V, IsMax h M → ∀ x, x ∈ M ↔ ‖h x x‖ ≤ 1 :=
      fun M hM => hA L s hs δ hδ V h hh hiso' M hM
    refine ⟨0, Fin.elim0, Fin.elim0, ⊤, Fin.elim0, fun i => i.elim0,
      ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun _ _ i => i.elim0,
        fun w _ hw => hiso' w hw, fun x => ⟨Fin.elim0, Fin.elim0, x, trivial, by simp⟩⟩, ?_, ?_⟩
    · intro a b w _
      simp [hm Λ hΛ]
    · intro a b w _
      simp [hm Λ' hΛ']
end GlobalTheory.CompanionTheory.HermFrame
