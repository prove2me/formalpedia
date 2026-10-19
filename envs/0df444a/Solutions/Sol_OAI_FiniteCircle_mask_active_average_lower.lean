-- Prove2me | solution 1 for OAI.FiniteCircle.mask_active_average_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:54:25.024384+00:00
-- url     : https://prove2.me/submissions/29dce4a3-49d2-4d19-8e23-060eafd6c136

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/MaskSeparation.lean:L85-L139
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.mask_active_average_lower. The node keeps its source
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

-- ---- from OAI.Combinatorics.FiniteCircle.CircleWords ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

theorem sub_le (f : PhaseCost G) (x y : G) : f (x-y) ≤ f x+f y := by
  simpa only [sub_eq_add_neg, f.neg] using f.add_le x (-y)

theorem le_pair (f : PhaseCost G) (x d : G) : f d ≤ f x+f (x+d) := by
  have h := f.sub_le (x+d) x
  simpa only [add_sub_cancel_left, add_comm] using h

theorem grid_pair_bound (f : PhaseCost G) {p : ℕ} [NeZero p]
    (φ : ZMod p →+ G) (x : G) :
    (p : ℝ)*f (φ 1) ≤ 2*∑ b : ZMod p, f (x+φ b) := by
  have hpairs := Finset.sum_le_sum (s := Finset.univ)
    (fun (b : ZMod p) _ => f.le_pair (x+φ b) (φ 1))
  have hs : ∑ b : ZMod p, f (x+φ b+φ 1) = ∑ b : ZMod p, f (x+φ b) := by
    simpa only [Equiv.coe_addRight, map_add, add_assoc] using
      Equiv.sum_comp (Equiv.addRight (1 : ZMod p)) (fun b => f (x+φ b))
  simpa only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    Finset.sum_add_distrib, hs, two_mul] using hpairs

theorem prime_grid_bound (f : PhaseCost G) {p : ℕ} [NeZero p] (hp : p.Prime)
    (φ : ZMod p →+ G) (x : G) (z : ZMod p) (hz : z ≠ 0) :
    (p : ℝ)*f (φ 1) ≤ 2*∑ b : ZMod p, f (x+b.val • φ z) := by
  let : Fact p.Prime := ⟨hp⟩
  have hs : ∑ b : ZMod p, f (x+b.val • φ z) = ∑ b : ZMod p, f (x+φ b) := by
    have he (b : ZMod p) : b.val • φ z = φ (b*z) := by
      rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    simp_rw [he]
    exact Equiv.sum_comp (Equiv.mulRight₀ z hz) (fun b => f (x+φ b))
  rw [hs]
  exact f.grid_pair_bound φ x

end PhaseCost

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.MaskSeparation ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem sum_fin_zmod {p : ℕ} [NeZero p] (g : ZMod p → ℝ) :
    ∑ b : Fin p, g (b.val : ZMod p) = ∑ b : ZMod p, g b := by
  refine Fintype.sum_equiv (ZMod.finEquiv p).toEquiv _ _ ?_
  intro b
  congr 1
  cases p with
  | zero => exact Fin.elim0 b
  | succ p =>
    change (b.val : ZMod (p+1)) = b
    exact ZMod.natCast_zmod_val (show ZMod (p+1) from b)

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

theorem mask_active_average_lower {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hh : 0 < h) (hd : ∀ k : Fin h, p l k ∣ M)
    (hp : ∀ k : Fin h, (p l k).Prime)
    (hlo : ∀ k : Fin h, h^3 ≤ p l k) (hhi : ∀ k : Fin h, p l k ≤ 2*h^3)
    (f : PhaseCost (ZMod M)) (x : ZMod M) (z : MaskResidues h p l)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hq : ∀ k : Fin h, z k ≠ 0 → Q ≤ f (subcircle (hd k) 1)) :
    (((Finset.univ.filter (fun k : Fin h => z k ≠ 0)).card : ℝ)/(4*h))*Q ≤
      f.average (maskPhaseHom h p M l hd) x z := by
  classical
  let : ∀ k : Fin h, NeZero (p l k) := fun k => ⟨(hp k).ne_zero⟩
  let S := Finset.univ.filter (fun k : Fin h => z k ≠ 0)
  let T : ℝ := ∑ k : Fin h, (p l k : ℝ)
  let B (k : Fin h) : ℝ := ∑ b : Fin (p l k),
    f (x+(∑ j,subcircle (hd j) (z j))+b.val • subcircle (hd k) (z k))
  have hB (k : Fin h) : 0 ≤ B k := Finset.sum_nonneg (fun _ _ => f.nonneg _)
  have hT : 0 < T := by
    apply Finset.sum_pos
    · intro k _; exact_mod_cast (hp k).pos
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0,hh⟩⟩
  have hTu : T ≤ 2*(h:ℝ)^4 := by
    calc
      T ≤ ∑ _k : Fin h, (2:ℝ)*h^3 := Finset.sum_le_sum (fun k _ => by exact_mod_cast hhi k)
      _ = _ := by simp; ring
  have hkb (k : Fin h) (hk : k ∈ S) : (h:ℝ)^3*Q ≤ 2*B k := by
    have ha := f.prime_grid_bound (hp k) (subcircle (hd k))
      (x+∑ j,subcircle (hd j) (z j)) (z k) ((Finset.mem_filter.mp hk).2)
    have he : B k = ∑ b : ZMod (p l k),
        f (x+(∑ j,subcircle (hd j) (z j))+b.val • subcircle (hd k) (z k)) := by
      symm
      rw [← sum_fin_zmod]
      apply Finset.sum_congr rfl
      intro b _
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt b.isLt]
    rw [← he] at ha
    calc
      (h:ℝ)^3*Q ≤ (p l k : ℝ)*Q := mul_le_mul_of_nonneg_right (by exact_mod_cast hlo k) hQ
      _ ≤ (p l k : ℝ)*f (subcircle (hd k) 1) := mul_le_mul_of_nonneg_left (hq k ((Finset.mem_filter.mp hk).2)) (by positivity)
      _ ≤ _ := ha
  have hsum : (S.card : ℝ)*(h:ℝ)^3*Q ≤ 2*∑ k : Fin h, B k := by
    calc
      _ = ∑ _k ∈ S, (h:ℝ)^3*Q := by simp; ring
      _ ≤ ∑ k ∈ S, 2*B k := Finset.sum_le_sum hkb
      _ ≤ ∑ k : Fin h, 2*B k := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun k _ _ => mul_nonneg (by norm_num) (hB k))
      _ = _ := (Finset.mul_sum ..).symm
  rw [mask_average_formula hd (fun k => (hp k).pos)]
  change (S.card : ℝ)/(4*h)*Q ≤ (∑ k : Fin h, B k)/T
  rw [le_div_iff₀ hT]
  have hh' : (0:ℝ) < h := by exact_mod_cast hh
  have hb : 0 ≤ (S.card : ℝ)/(4*h)*Q := by positivity
  calc
    _ ≤ ((S.card : ℝ)/(4*h)*Q)*(2*(h:ℝ)^4) := mul_le_mul_of_nonneg_left hTu hb
    _ = ((S.card : ℝ)*(h:ℝ)^3*Q)/2 := by field_simp; ring
    _ ≤ _ := by linarith

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.mask_active_average_lower := @_root_.OAI.FiniteCircle.mask_active_average_lower
