-- Prove2me | solution 1 for OAI.FiniteCircle.mask_inactive_average_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:56:59.573315+00:00
-- url     : https://prove2.me/submissions/666c8f37-ae65-454b-b32b-5c218f2e19a2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/MaskSeparation.lean:L141-L189
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.mask_inactive_average_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation

-- ---- from OAI.Combinatorics.FiniteCircle.MaskSeparation ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem card_maskTag (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) :
    Fintype.card (MaskTag h p l) = ∑ k : Fin h, p l k := by
  simp only [MaskTag, Fintype.card_sigma, Fintype.card_fin]

 theorem mask_average_formula {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ k : Fin h, p l k ∣ M) (hn : ∀ k : Fin h, 0 < p l k)
    (f : PhaseCost (ZMod M)) (x : ZMod M) (z : MaskResidues h p l) :
    f.average (maskPhaseHom h p M l hd) x z =
      (∑ k : Fin h, ∑ b : Fin (p l k),
        f (x+(∑ k,subcircle (hd k) (z k))+b.val • subcircle (hd k) (z k))) /
          (∑ k : Fin h, (p l k : ℝ)) := by
  let : ∀ k : Fin h, NeZero (p l k) := fun k => ⟨(hn k).ne'⟩
  simp only [PhaseCost.average, card_maskTag, Nat.cast_sum, Fintype.sum_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  change x+((∑ k,subcircle (hd k) (z k))+b.val • subcircle (hd k) (z k)) = _
  abel

theorem mask_inactive_average_lower {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hh : 0 < h) (hd : ∀ k : Fin h, p l k ∣ M)
    (hp : ∀ k : Fin h, (p l k).Prime)
    (hlo : ∀ k : Fin h, h^3 ≤ p l k) (hhi : ∀ k : Fin h, p l k ≤ 2*h^3)
    (f : PhaseCost (ZMod M)) (x : ZMod M) (z : MaskResidues h p l)
    (hs : 2*(Finset.univ.filter (fun k : Fin h => z k ≠ 0)).card ≤ h) :
    (1/4:ℝ)*f (x+∑ k,subcircle (hd k) (z k)) ≤
      f.average (maskPhaseHom h p M l hd) x z := by
  classical
  let N := Finset.univ.filter (fun k : Fin h => z k = 0)
  let T : ℝ := ∑ k : Fin h, (p l k : ℝ)
  let B (k : Fin h) : ℝ := ∑ b : Fin (p l k),
    f (x+(∑ j,subcircle (hd j) (z j))+b.val • subcircle (hd k) (z k))
  let Q := f (x+∑ k,subcircle (hd k) (z k))
  have hQ : 0 ≤ Q := f.nonneg _
  have hB (k : Fin h) : 0 ≤ B k := Finset.sum_nonneg (fun _ _ => f.nonneg _)
  have hT : 0 < T := by
    apply Finset.sum_pos
    · intro k _; exact_mod_cast (hp k).pos
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0,hh⟩⟩
  have hTu : T ≤ 2*(h:ℝ)^4 := by
    calc
      T ≤ ∑ _k : Fin h, (2:ℝ)*h^3 := Finset.sum_le_sum (fun k _ => by exact_mod_cast hhi k)
      _ = _ := by simp; ring
  have hN : (h:ℝ) ≤ 2*N.card := by
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun k : Fin h => z k = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    change N.card + (Finset.univ.filter (fun k : Fin h => z k ≠ 0)).card = h at hc
    exact_mod_cast (show h ≤ 2*N.card by omega)
  have hkb (k : Fin h) (hk : k ∈ N) : (h:ℝ)^3*Q ≤ B k := by
    have hz := (Finset.mem_filter.mp hk).2
    have he : B k = (p l k : ℝ)*Q := by
      simp [B, Q, hz]
    rw [he]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlo k) hQ
  have hsum : (N.card : ℝ)*(h:ℝ)^3*Q ≤ ∑ k : Fin h, B k := by
    calc
      _ = ∑ _k ∈ N, (h:ℝ)^3*Q := by simp; ring
      _ ≤ ∑ k ∈ N, B k := Finset.sum_le_sum hkb
      _ ≤ ∑ k : Fin h, B k := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun k _ _ => hB k)
  rw [mask_average_formula hd (fun k => (hp k).pos)]
  change (1/4:ℝ)*Q ≤ (∑ k : Fin h, B k)/T
  rw [le_div_iff₀ hT]
  calc
    _ ≤ ((1/4:ℝ)*Q)*(2*(h:ℝ)^4) := mul_le_mul_of_nonneg_left hTu (by positivity)
    _ = ((h:ℝ)/2)*h^3*Q := by ring
    _ ≤ (N.card : ℝ)*h^3*Q := by gcongr; linarith
    _ ≤ _ := hsum

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.mask_inactive_average_lower := @_root_.OAI.FiniteCircle.mask_inactive_average_lower
