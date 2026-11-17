-- Prove2me | solution 1 for N25.level25_cusp_width
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:44.431143+00:00
-- url     : https://prove2.me/submissions/ce9ad36d-9a89-4149-b153-7456771431ee

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_primitive_rows
import Theorems.Thm_N25_level25_gammaH_rightRel
import Theorems.Thm_N25_level25_subgroup_membership
import Theorems.Thm_N25_level25_row_scaling_iff
import Theorems.Thm_N25_level25_cusp_width_census

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

namespace N25

/-- The exact positive cusp width is determined by the reduced lower-left entry. -/
theorem _root_.solution (A : SL(2, ℤ)) :
    let c := (A 1 0 : ZMod 25).val
    let w := if c=0 then 1 else if c%5=0 then 5 else 25
    0 < w ∧ A*ModularGroup.T^w*A⁻¹ ∈ CohCarrier.GammaH 25 H25 ∧
      ∀ n : ℕ, 0 < n → A*ModularGroup.T^n*A⁻¹ ∈ CohCarrier.GammaH 25 H25 → w ≤ n := by
  classical
  let R := Fin 25 × Fin 25
  let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
  let scale : ℕ → R → R := fun h r =>
    (⟨h*r.1.val%25, Nat.mod_lt _ (by decide)⟩,
     ⟨h*r.2.val%25, Nat.mod_lt _ (by decide)⟩)
  let labels : Fin 4 → ℕ := ![1,7,18,24]
  let code : R → ℕ := fun r => r.1.val + 25*r.2.val
  let normcode : R → ℕ := fun r =>
    min (min (code r) (code (scale 7 r))) (min (code (scale 18 r)) (code (scale 24 r)))
  let translate : ℕ → R → R := fun n r => (r.1, ⟨(r.2.val+n*r.1.val)%25, Nat.mod_lt _ (by decide)⟩)
  let row : SL(2, ℤ) → R := fun A => ((A 1 0 : ZMod 25), (A 1 1 : ZMod 25))
  have hp : ∀ A, primitive (row A) := level25_primitive_rows.1
  let width : R → ℕ := fun r => if r.1.val=0 then 1 else if r.1.val%5=0 then 5 else 25
  have hmul (A B : SL(2, ℤ)) (i j : Fin 2) :
      ((A*B) i j : ZMod 25) = (A i 0 : ZMod 25)*(B 0 j : ZMod 25) +
        (A i 1 : ZMod 25)*(B 1 j : ZMod 25) := by
    change (((A : Matrix (Fin 2) (Fin 2) ℤ)*(B : Matrix (Fin 2) (Fin 2) ℤ)) i j : ZMod 25) = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have htranslate1 (r : R) : translate 1 r =
      (r.1, (fun x y : ZMod 25 => x+y) r.2 r.1) := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change (r.2.val+1*r.1.val)%25 = (r.2.val+r.1.val)%25
      rw [one_mul]
  have hrowT (A : SL(2, ℤ)) : row (A*ModularGroup.T) = translate 1 (row A) := by
    rw [htranslate1]
    apply Prod.ext
    · change ((A*ModularGroup.T) 1 0 : ZMod 25) = (A 1 0 : ZMod 25)
      rw [hmul]
      simp [ModularGroup.T]
    · change ((A*ModularGroup.T) 1 1 : ZMod 25) = (A 1 1 : ZMod 25) + (A 1 0 : ZMod 25)
      rw [hmul]
      simp [ModularGroup.T, add_comm]
  have htranslate (n : ℕ) (r : R) : translate 1 (translate n r) = translate (n+1) r := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change ((r.2.val+n*r.1.val)%25 + 1*r.1.val)%25 = (r.2.val+(n+1)*r.1.val)%25
      simp only [one_mul, Nat.mod_add_mod, Nat.add_mul, one_mul]
      congr 1
      ring
  have htranslate0 (r : R) : translate 0 r = r := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [translate, Nat.mod_eq_of_lt r.2.isLt]
  have hrowTpow (A : SL(2, ℤ)) (n : ℕ) : row (A*ModularGroup.T^n) = translate n (row A) := by
    induction n with
    | zero => simpa only [pow_zero, mul_one, htranslate0]
    | succ n ih => rw [pow_succ, ← mul_assoc, hrowT, ih, htranslate]
  have hscale (i : Fin 4) (r : R) :
      (scale (labels i) r).1 = ((fun x y : ZMod 25 => x*y) ((labels i : ℕ) : ZMod 25) r.1) ∧
      (scale (labels i) r).2 = ((fun x y : ZMod 25 => x*y) ((labels i : ℕ) : ZMod 25) r.2) := by
    fin_cases i <;> constructor <;> apply Fin.ext <;> rfl
  have huclass (u : (ZMod 25)ˣ) (hu : u ∈ H25) :
      ∃ i : Fin 4, (u : ZMod 25) = ((labels i : ℕ) : ZMod 25) := by
    rcases (level25_subgroup_membership u).mp hu with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  have hulabel (i : Fin 4) : ∃ u : (ZMod 25)ˣ,
      u ∈ H25 ∧ (u : ZMod 25) = ((labels i : ℕ) : ZMod 25) := by
    have hc : ∀ i : Fin 4, Nat.Coprime (labels i) 25 := by decide +kernel
    refine ⟨ZMod.unitOfCoprime (labels i) (hc i), ?_, rfl⟩
    rw [level25_subgroup_membership]
    change ((labels i : ℕ) : ZMod 25) = 1 ∨ ((labels i : ℕ) : ZMod 25) = 7 ∨
      ((labels i : ℕ) : ZMod 25) = 18 ∨ ((labels i : ℕ) : ZMod 25) = 24
    fin_cases i <;> norm_num [labels]
  let Γ := CohCarrier.GammaH 25 H25
  have hnormrel (B C : SL(2, ℤ)) : QuotientGroup.rightRel Γ B C ↔
      normcode (row B) = normcode (row C) := by
    constructor
    · intro h
      obtain ⟨u, hu, hc, hd⟩ := (level25_gammaH_rightRel H25 B C).mp h
      obtain ⟨i, hi⟩ := huclass u hu
      apply (level25_row_scaling_iff (row B) (row C)).mpr
      refine ⟨i, ?_⟩
      apply Prod.ext
      · change (scale (labels i) (row B)).1 = (C 1 0 : ZMod 25)
        rw [(hscale i (row B)).1, ← hi]
        exact hc.symm
      · change (scale (labels i) (row B)).2 = (C 1 1 : ZMod 25)
        rw [(hscale i (row B)).2, ← hi]
        exact hd.symm
    · intro h
      obtain ⟨i, hi⟩ := (level25_row_scaling_iff (row B) (row C)).mp h
      obtain ⟨u, hu, hval⟩ := hulabel i
      apply (level25_gammaH_rightRel H25 B C).mpr
      refine ⟨u, hu, ?_, ?_⟩
      · have hc := congrArg Prod.fst hi.symm
        change (C 1 0 : ZMod 25) = (scale (labels i) (row B)).1 at hc
        rw [hc, (hscale i (row B)).1, hval]
      · have hd := congrArg Prod.snd hi.symm
        change (C 1 1 : ZMod 25) = (scale (labels i) (row B)).2 at hd
        rw [hd, (hscale i (row B)).2, hval]
  have hconj (n : ℕ) : A*ModularGroup.T^n*A⁻¹ ∈ Γ ↔
      normcode (translate n (row A)) = normcode (row A) := by
    constructor
    · intro h
      have hr : QuotientGroup.rightRel Γ A (A*ModularGroup.T^n) :=
        (QuotientGroup.rightRel_apply).mpr h
      have hn := (hnormrel A (A*ModularGroup.T^n)).mp hr
      rw [hrowTpow] at hn
      exact hn.symm
    · intro h
      apply (QuotientGroup.rightRel_apply).mp
      apply (hnormrel A (A*ModularGroup.T^n)).mpr
      rw [hrowTpow]
      exact h.symm
  have hw : normcode (translate (width (row A)) (row A)) = normcode (row A) ∧
      ∀ n : Fin 25, 0 < n.val → n.val < width (row A) →
        normcode (translate n.val (row A)) ≠ normcode (row A) :=
    level25_cusp_width_census.2.2.2.2.2 (row A) (hp A)
  have hwpos : 0 < width (row A) := by
    dsimp only [width]
    split_ifs <;> norm_num
  have hwle : width (row A) ≤ 25 := by
    dsimp only [width]
    split_ifs <;> norm_num
  change 0 < width (row A) ∧ A*ModularGroup.T^(width (row A))*A⁻¹ ∈ Γ ∧
    ∀ n : ℕ, 0 < n → A*ModularGroup.T^n*A⁻¹ ∈ Γ → width (row A) ≤ n
  refine ⟨hwpos, (hconj _).mpr hw.1, ?_⟩
  intro n hn hmem
  by_contra! hlt
  have hn25 : n < 25 := lt_of_lt_of_le hlt hwle
  exact hw.2 ⟨n, hn25⟩ hn hlt ((hconj n).mp hmem)

end N25
