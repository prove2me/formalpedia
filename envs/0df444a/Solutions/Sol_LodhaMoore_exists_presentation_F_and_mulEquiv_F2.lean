-- Prove2me | solution 1 for LodhaMoore.exists_presentation_F_and_mulEquiv_F2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:29.357794+00:00
-- url     : https://prove2.me/submissions/e635e670-b83b-48cb-a2bb-5ecb63edc6de

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_CannonFloydParry_Presentations
import Theorems.Thm_CannonFloydParry_exists_mulEquiv_F1_F
import Theorems.Thm_CannonFloydParry_Y_conj_eq_Y_succ
import Theorems.Thm_LodhaMoore_bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R

section
/-! Development: `a`, `b`, `c` are the homeomorphisms the bundle names (`ofReal` returns the
extension of `aFun`, `bFun`, `cFun`), and their values on `ℝ`. -/

namespace LodhaMoore

end LodhaMoore
end

section
/-! # Lodha–Moore §3 (group S3a): Proposition 3.1, the identification `G₀ ≅ ⟨X ∪ Y₀⟩`, the
relations (1)–(5), the presentation of `F`, and the conjugacy classes of the `y_s`. -/

namespace LodhaMoore.Dev.S3a

open LodhaMoore

/-! ## Infinite binary sequences -/

abbrev Str := Stream' Bool

theorem cons_zero (d : Bool) (s : Str) : (Stream'.cons d s) 0 = d := rfl

theorem eq_cons (ξ : Str) : ξ = Stream'.cons (ξ 0) ξ.tail := (Stream'.eta ξ).symm

theorem exists_cons (ξ : Str) : ∃ d ζ, ξ = Stream'.cons d ζ := ⟨_, _, eq_cons ξ⟩

theorem cases_x (ξ : Str) :
    (∃ ζ, ξ = Stream'.cons false (Stream'.cons false ζ)) ∨
    (∃ ζ, ξ = Stream'.cons false (Stream'.cons true ζ)) ∨ (∃ ζ, ξ = Stream'.cons true ζ) := by
  obtain ⟨d, ζ, rfl⟩ := exists_cons ξ
  obtain ⟨e, η, rfl⟩ := exists_cons ζ
  cases d <;> cases e <;>
    first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl⟩) | exact Or.inr (Or.inr ⟨_, rfl⟩)

/-! ## `localize` -/

theorem localize_nil (f : Str → Str) (ξ : Str) : localize [] f ξ = f ξ := by
  simp [localize, Stream'.take_zero]

theorem localize_cons_same (d : Bool) (t : Seq) (f : Str → Str) (ζ : Str) :
    localize (d :: t) f (Stream'.cons d ζ) = Stream'.cons d (localize t f ζ) := by
  unfold localize
  simp only [List.length_cons, Stream'.take_succ_cons, List.cons.injEq, true_and]
  split_ifs
  · rfl
  · rfl

theorem localize_cons_diff {d e : Bool} (h : d ≠ e) (t : Seq) (f : Str → Str) (ζ : Str) :
    localize (d :: t) f (Stream'.cons e ζ) = Stream'.cons e ζ := by
  unfold localize
  simp only [List.length_cons, Stream'.take_succ_cons, List.cons.injEq]
  rw [if_neg (fun h' => h h'.1.symm)]

/-! ## `x` and `x⁻¹` -/

theorem xFun_00 (ζ : Str) : xFun (Stream'.cons false (Stream'.cons false ζ)) =
    Stream'.cons false ζ := rfl
theorem xFun_01 (ζ : Str) : xFun (Stream'.cons false (Stream'.cons true ζ)) =
    Stream'.cons true (Stream'.cons false ζ) := rfl
theorem xFun_1 (ζ : Str) : xFun (Stream'.cons true ζ) = Stream'.cons true (Stream'.cons true ζ) :=
  rfl

/-! ## `y` and `y⁻¹` -/

theorem localize_tf (t : Seq) (f : Str → Str) (ζ : Str) :
    localize (true :: t) f (Stream'.cons false ζ) = Stream'.cons false ζ :=
  localize_cons_diff (by decide) t f ζ

/-! ## The relations (1)–(5) as identities of functions -/

/-- `(xr r)`: the tail action of `x` on finite sequences, as in `xFin`. -/
def xr : List Bool → Option (List Bool)
  | false :: false :: r => some (false :: r)
  | false :: true :: r => some (true :: false :: r)
  | true :: r => some (true :: true :: r)
  | _ => none

theorem xFin_append (s r : Seq) : xFin s (s ++ r) = (xr r).map (s ++ ·) := by
  unfold xFin
  rw [if_pos (List.prefix_append _ _)]
  simp only [List.drop_left]
  rcases r with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;> rfl

/-! ## `SeqGroup` -/

theorem unop_mul_apply (g h : SeqGroup) (ξ : Str) :
    MulOpposite.unop (g * h) ξ = MulOpposite.unop h (MulOpposite.unop g ξ) := rfl

theorem unop_one_apply (ξ : Str) : MulOpposite.unop (1 : SeqGroup) ξ = ξ := rfl

theorem unop_toSeqGroup {f : Str → Str} (hf : Function.Bijective f) (ξ : Str) :
    MulOpposite.unop (toSeqGroup f) ξ = f ξ := by
  simp [toSeqGroup, hf]

/-- Every `x_s` and `y_s` is a bijection. -/
def HB : Prop := ∀ s, Function.Bijective (xSeq s) ∧ Function.Bijective (ySeq s)

/-- Every relation of `R` holds. -/
def HR : Prop := ∀ r ∈ R, FreeGroup.lift Gen.val r = 1

section
variable (hb : HB)
include hb

theorem unop_xs (s : Seq) (ξ : Str) : MulOpposite.unop (xs s) ξ = xSeq s ξ :=
  unop_toSeqGroup (hb s).1 ξ

end

/-! ## `phi`: the recursion, and the nested intervals -/

/-! ## Proposition 3.1, first part: `phi(ξ.y) = 2 phi(ξ)` -/

/-! ## Proposition 3.1, second part: `Phi` carries `x`, `x₁`, `y₁₀` to `a`, `b`, `c` -/

/-! ## Generation and conjugacy, from the relations alone (in any group) -/

/-- `s` is `1ⁿ`, or `s` is `1ⁿ0r` (and likewise with the digits swapped). -/
theorem decomp (d : Bool) : ∀ s : Seq,
    s = List.replicate s.length d ∨ ∃ n r, s = List.replicate n d ++ (!d) :: r
  | [] => Or.inl rfl
  | e :: s => by
    by_cases he : e = d
    · subst he
      rcases decomp e s with h | ⟨n, r, h⟩
      · left; rw [List.length_cons, List.replicate_succ, ← h]
      · right; exact ⟨n + 1, r, by rw [h, List.replicate_succ, List.cons_append]⟩
    · right
      refine ⟨0, s, ?_⟩
      have : e = !d := by cases e <;> cases d <;> simp_all
      rw [this]; rfl

section GroupGen

variable {Γ : Type*} [Group Γ]

theorem gen_x (X : Seq → Γ)
    (h1 : ∀ s, X s * X s = X (s ++ [false]) * X s * X (s ++ [true]))
    (h2 : ∀ s t t', xFin s t = some t' → X t * X s = X s * X t')
    (H : Subgroup Γ) (hH : ∀ n, X (List.replicate n true) ∈ H) : ∀ s, X s ∈ H := by
  have aux : ∀ r n, X (List.replicate n true ++ false :: r) ∈ H := by
    intro r
    induction r with
    | nil =>
      intro n
      have key := h1 (List.replicate n true)
      rw [← List.replicate_succ'] at key
      have : X (List.replicate n true ++ [false]) = X (List.replicate n true) *
          X (List.replicate n true) * (X (List.replicate (n + 1) true))⁻¹ *
            (X (List.replicate n true))⁻¹ := by
        rw [key]; group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.mul_mem (hH n) (hH n)) (H.inv_mem (hH _)))
        (H.inv_mem (hH n))
    | cons d r ih =>
      intro n
      cases d
      · have key := h2 (List.replicate n true) (List.replicate n true ++ false :: false :: r)
          (List.replicate n true ++ false :: r) (by rw [xFin_append]; rfl)
        have : X (List.replicate n true ++ false :: false :: r) = X (List.replicate n true) *
            X (List.replicate n true ++ false :: r) * (X (List.replicate n true))⁻¹ := by
          rw [← key]; group
        rw [this]
        exact H.mul_mem (H.mul_mem (hH n) (ih n)) (H.inv_mem (hH n))
      · have key := h2 (List.replicate n true) (List.replicate n true ++ false :: true :: r)
          (List.replicate n true ++ true :: false :: r) (by rw [xFin_append]; rfl)
        have e : List.replicate n true ++ true :: false :: r =
            List.replicate (n + 1) true ++ false :: r := by
          rw [List.replicate_succ', List.append_assoc]; rfl
        rw [e] at key
        have : X (List.replicate n true ++ false :: true :: r) = X (List.replicate n true) *
            X (List.replicate (n + 1) true ++ false :: r) * (X (List.replicate n true))⁻¹ := by
          rw [← key]; group
        rw [this]
        exact H.mul_mem (H.mul_mem (hH n) (ih (n + 1))) (H.inv_mem (hH n))
  intro s
  rcases decomp true s with h | ⟨n, r, h⟩
  · rw [h]; exact hH _
  · rw [h]; exact aux r n

variable {Y : Seq → Γ} {K : Subgroup Γ}

section moves
variable (X : Seq → Γ) (h3 : ∀ s t t', xFin s t = some t' → Y t * X s = X s * Y t')
  (hK : ∀ s, X s ∈ K)
include h3 hK

end moves

end GroupGen

/-! ## The relations in `SeqGroup`, from `HR` -/

section
variable (hr : HR)
include hr

theorem rel1_grp (s : Seq) : xs s * xs s = xs (s ++ [false]) * xs s * xs (s ++ [true]) := by
  have := hr _ ⟨Rel.one s, rfl⟩
  simp only [Rel.lhs, Rel.rhs, map_mul, map_inv, FreeGroup.lift_apply_of, Gen.val] at this
  exact mul_inv_eq_one.mp this

theorem rel2_grp {s t t' : Seq} (h : xFin s t = some t') : xs t * xs s = xs s * xs t' := by
  have := hr _ ⟨Rel.two s t t' h, rfl⟩
  simp only [Rel.lhs, Rel.rhs, map_mul, map_inv, FreeGroup.lift_apply_of, Gen.val] at this
  exact mul_inv_eq_one.mp this

end

/-! ## Every element of `G` is locally determined -/

/-! ## `Phi` is onto -/

/-! ## The identification `G₀ ≅ ⟨X ∪ Y₀⟩` induced by `Phi` -/

/-! ## Binary expansions: `F` on sequences and `F` on the unit interval -/

noncomputable def beta (ξ : Str) : ℝ := ∑' i, if ξ i then (1 / 2 : ℝ) ^ (i + 1) else 0

theorem geom_summable : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1)) :=
  (summable_geometric_two.mul_left (1 / 2 : ℝ)).congr fun i => by ring

theorem geom_tsum : ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) = 1 := by
  have : (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) = fun n => 1 / 2 / 2 ^ n := by
    funext n; rw [pow_succ, div_pow, one_pow]; ring
  rw [this, tsum_geometric_two']

theorem beta_summable (ξ : Str) : Summable (fun i => if ξ i then (1 / 2 : ℝ) ^ (i + 1) else 0) :=
  Summable.of_nonneg_of_le (fun i => by split_ifs <;> positivity)
    (fun i => by split_ifs <;> [exact le_rfl; positivity]) geom_summable

theorem beta_cons (d : Bool) (ζ : Str) :
    beta (Stream'.cons d ζ) = (if d then 1 / 2 else 0) + beta ζ / 2 := by
  have hs := beta_summable (Stream'.cons d ζ)
  have e2 : ∑' (b : ℕ), (fun i => if (Stream'.cons d ζ) i = true then (1 / 2 : ℝ) ^ (i + 1)
      else 0) (b + 1) = beta ζ / 2 := by
    rw [beta, ← tsum_div_const]
    congr 1
    funext i
    change (if ζ i = true then (1 / 2 : ℝ) ^ (i + 1 + 1) else 0) = _
    split_ifs <;> ring
  unfold beta at e2 ⊢
  rw [hs.tsum_eq_zero_add, e2]
  cases d <;> simp [cons_zero]

theorem beta_nonneg (ξ : Str) : 0 ≤ beta ξ := tsum_nonneg fun i => by split_ifs <;> positivity

theorem beta_le_one (ξ : Str) : beta ξ ≤ 1 := by
  rw [← geom_tsum]
  exact Summable.tsum_le_tsum (fun i => by split_ifs <;> [exact le_rfl; positivity])
    (beta_summable ξ) geom_summable

theorem beta_const_false : beta (Stream'.const false) = 0 := by
  simp [beta, Stream'.const]

theorem beta_const_true : beta (Stream'.const true) = 1 := by
  rw [← geom_tsum]; simp [beta, Stream'.const]

theorem beta_dyadic (n : ℕ) : ∀ k : ℕ, k ≤ 2 ^ n → ∃ ξ, beta ξ = k / 2 ^ n := by
  induction n with
  | zero =>
    intro k hk
    interval_cases k
    · exact ⟨_, by rw [beta_const_false]; simp⟩
    · exact ⟨_, by rw [beta_const_true]; simp⟩
  | succ n ih =>
    intro k hk
    by_cases hk' : k ≤ 2 ^ n
    · obtain ⟨ξ, hξ⟩ := ih k hk'
      refine ⟨Stream'.cons false ξ, ?_⟩
      rw [beta_cons, hξ, pow_succ]; simp; ring
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.mp hk'))
      obtain ⟨ξ, hξ⟩ := ih k' (by rw [pow_succ] at hk; omega)
      refine ⟨Stream'.cons true ξ, ?_⟩
      rw [beta_cons, hξ]
      simp only [if_true]
      push_cast
      field_simp
      ring

theorem beta_between {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 1) :
    ∃ ξ, x < beta ξ ∧ beta ξ < y := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hxy) (by norm_num : (1 / 2 : ℝ) < 1)
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  set k := ⌊x * 2 ^ n⌋₊ + 1 with hk
  have hk1 : x * 2 ^ n < k := by rw [hk]; push_cast; exact Nat.lt_floor_add_one _
  have hk2 : (k : ℝ) ≤ x * 2 ^ n + 1 := by
    rw [hk]; push_cast; linarith [Nat.floor_le (mul_nonneg hx h2.le)]
  have hn' : (1 / 2 : ℝ) ^ n = 1 / 2 ^ n := by rw [div_pow, one_pow]
  have hlt : (k : ℝ) / 2 ^ n < y := by
    rw [div_lt_iff₀ h2]
    rw [hn', div_lt_iff₀ h2, sub_mul] at hn
    linarith
  have hkn : k ≤ 2 ^ n := by
    have : (k : ℝ) < 2 ^ n := by
      have := (div_lt_iff₀ h2).mp (lt_of_lt_of_le hlt hy); linarith
    exact_mod_cast this.le
  obtain ⟨ξ, hξ⟩ := beta_dyadic n k hkn
  refine ⟨ξ, ?_, ?_⟩ <;> rw [hξ]
  · rw [lt_div_iff₀ h2]; exact hk1
  · exact hlt

noncomputable def betaUI (ξ : Str) : CannonFloydParry.UI := ⟨beta ξ, beta_nonneg ξ, beta_le_one ξ⟩

theorem eq_one_of_fix_beta (f : CannonFloydParry.UI ≃o CannonFloydParry.UI)
    (hf : ∀ ξ, f (betaUI ξ) = betaUI ξ) : f = 1 := by
  apply RelIso.ext
  intro z
  change f z = z
  by_contra hne
  rcases lt_trichotomy (f z : ℝ) (z : ℝ) with h | h | h
  · obtain ⟨ξ, h1, h2⟩ := beta_between (f z).2.1 h z.2.2
    have hw : betaUI ξ < z := h2
    have := f.lt_iff_lt.mpr hw
    rw [hf] at this
    exact absurd (lt_trans h1 this) (lt_irrefl _)
  · exact hne (Subtype.ext h)
  · obtain ⟨ξ, h1, h2⟩ := beta_between z.2.1 h (f z).2.2
    have hw : z < betaUI ξ := h1
    have := f.lt_iff_lt.mpr hw
    rw [hf] at this
    exact absurd (lt_trans h2 this) (lt_irrefl _)

/-- `g` on sequences corresponds to `f⁻¹` on the interval. -/
def SemiB (g : SeqGroup) (f : CannonFloydParry.UI ≃o CannonFloydParry.UI) : Prop :=
  ∀ ξ, f (betaUI (MulOpposite.unop g ξ)) = betaUI ξ

theorem SemiB_one : SemiB 1 1 := fun _ => rfl

theorem SemiB_mul {g h : SeqGroup} {f f' : CannonFloydParry.UI ≃o CannonFloydParry.UI}
    (H : SemiB g f) (H' : SemiB h f') : SemiB (g * h) (f * f') := fun ξ => by
  rw [RelIso.mul_apply, unop_mul_apply, H', H]

theorem SemiB_inv {g : SeqGroup} {f : CannonFloydParry.UI ≃o CannonFloydParry.UI}
    (H : SemiB g f) : SemiB g⁻¹ f⁻¹ := fun ξ => by
  apply f.injective
  rw [RelIso.apply_inv_self]
  have := H (MulOpposite.unop g⁻¹ ξ)
  rw [← unop_mul_apply, inv_mul_cancel, unop_one_apply] at this
  exact this.symm

theorem mapA_coe (z : CannonFloydParry.UI) :
    ((CannonFloydParry.mapA z : CannonFloydParry.UI) : ℝ) = CannonFloydParry.aFun z := rfl
theorem mapB_coe (z : CannonFloydParry.UI) :
    ((CannonFloydParry.mapB z : CannonFloydParry.UI) : ℝ) = CannonFloydParry.bFun z := rfl

theorem SemiB_A (hb : HB) : SemiB (xs []) CannonFloydParry.mapA := fun ξ => by
  apply Subtype.ext
  rw [mapA_coe, unop_xs hb, xSeq, localize_nil]
  change CannonFloydParry.aFun (beta _) = beta ξ
  rcases cases_x ξ with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
  · rw [xFun_00]
    simp only [beta_cons, Bool.false_eq_true, if_false]
    have h0 := beta_nonneg ζ; have h1 := beta_le_one ζ
    rw [CannonFloydParry.aFun_of_mem1 (by linarith only [h0, h1]) (by linarith only [h0, h1])]; ring
  · rw [xFun_01]
    simp only [beta_cons, Bool.false_eq_true, if_false, if_true]
    have h0 := beta_nonneg ζ; have h1 := beta_le_one ζ
    rw [CannonFloydParry.aFun_of_mem2 (by linarith only [h0, h1]) (by linarith only [h0, h1])]; ring
  · rw [xFun_1]
    simp only [beta_cons, if_true]
    have h0 := beta_nonneg ζ; have h1 := beta_le_one ζ
    rw [CannonFloydParry.aFun_of_mem3 (by linarith only [h0, h1]) (by linarith only [h0, h1])]; ring

theorem SemiB_B (hb : HB) : SemiB (xs [true]) CannonFloydParry.mapB := fun ξ => by
  apply Subtype.ext
  rw [mapB_coe, unop_xs hb]
  change CannonFloydParry.bFun (beta _) = beta ξ
  obtain ⟨d, η, rfl⟩ := exists_cons ξ
  cases d
  · rw [xSeq, localize_tf]
    simp only [beta_cons, Bool.false_eq_true, if_false]
    have h0 := beta_nonneg η; have h1 := beta_le_one η
    rw [CannonFloydParry.bFun_of_le_half (by linarith only [h0, h1])]
  · rw [xSeq, localize_cons_same, localize_nil]
    rcases cases_x η with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
    · rw [xFun_00]
      simp only [beta_cons, Bool.false_eq_true, if_false, if_true]
      have h0 := beta_nonneg ζ; have h1 := beta_le_one ζ
      rw [CannonFloydParry.bFun_of_mem1 (by linarith only [h0, h1]) (by linarith only [h0, h1])]; ring
    · rw [xFun_01]
      simp only [beta_cons, Bool.false_eq_true, if_false, if_true]
      have h0 := beta_nonneg ζ; have h1 := beta_le_one ζ
      rw [CannonFloydParry.bFun_of_mem2 (by linarith only [h0, h1]) (by linarith only [h0, h1])]; ring
    · rw [xFun_1]
      simp only [beta_cons, if_true]
      have h0 := beta_nonneg ζ; have h1 := beta_le_one ζ
      rw [CannonFloydParry.bFun_of_mem3 (by linarith only [h0, h1]) (by linarith only [h0, h1])]; ring

/-! ## The presentations of Cannon–Floyd–Parry: `F₂ → F₁` is injective -/

section CFP
open PresentedGroup

theorem F2_rel (k n : ℕ) (hkn : k < n) :
    (of k : CannonFloydParry.F2)⁻¹ * of n * of k = of (n + 1) := by
  have h := one_of_mem (rels := CannonFloydParry.relsF2)
    (x := (FreeGroup.of k)⁻¹ * FreeGroup.of n * FreeGroup.of k * (FreeGroup.of (n + 1))⁻¹)
    ⟨k, n, hkn, rfl⟩
  simp only [map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

theorem F2_of_succ (n : ℕ) :
    (of (n + 1) : CannonFloydParry.F2) = (of 0 ^ n)⁻¹ * of 1 * of 0 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← F2_rel 0 (n + 1) (by omega), ih, pow_succ, mul_inv_rev]; group

theorem comm_relator_of_conj_eq {Γ : Type*} [Group Γ] (a b y : Γ)
    (h : b⁻¹ * y * b = a⁻¹ * y * a) : (a * b⁻¹) * y * (a * b⁻¹)⁻¹ * y⁻¹ = 1 := by
  calc (a * b⁻¹) * y * (a * b⁻¹)⁻¹ * y⁻¹ = a * (b⁻¹ * y * b) * a⁻¹ * y⁻¹ := by group
    _ = a * (a⁻¹ * y * a) * a⁻¹ * y⁻¹ := by rw [h]
    _ = 1 := by group

theorem relsF1_F2 : ∀ r ∈ CannonFloydParry.relsF1, FreeGroup.lift CannonFloydParry.symF2 r = 1 := by
  intro r hr
  simp only [CannonFloydParry.relsF1, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  have h2 : ((of 0 : CannonFloydParry.F2)⁻¹ * of 1 * of 0) = of 2 := by
    have := F2_of_succ 1; rw [pow_one] at this; exact this.symm
  have h3 : ((of 0 : CannonFloydParry.F2)⁻¹ ^ 2 * of 1 * of 0 ^ 2) = of 3 := by
    rw [inv_pow]; exact (F2_of_succ 2).symm
  rcases hr with rfl | rfl
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, CannonFloydParry.symF2]
    rw [h2]
    exact comm_relator_of_conj_eq _ _ _ (by rw [F2_rel 1 2 (by norm_num), F2_rel 0 2 (by norm_num)])
  · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, CannonFloydParry.symF2]
    rw [h3]
    exact comm_relator_of_conj_eq _ _ _ (by rw [F2_rel 1 3 (by norm_num), F2_rel 0 3 (by norm_num)])

theorem relsF2_Y : ∀ r ∈ CannonFloydParry.relsF2, FreeGroup.lift CannonFloydParry.Y r = 1 := by
  rintro r ⟨k, n, hkn, rfl⟩
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
  rw [CannonFloydParry.Y_conj_eq_Y_succ k n hkn, mul_inv_cancel]

noncomputable def psi12 : CannonFloydParry.F1 →* CannonFloydParry.F2 := toGroup relsF1_F2
noncomputable def psi21 : CannonFloydParry.F2 →* CannonFloydParry.F1 := toGroup relsF2_Y

theorem psi12_Y (n : ℕ) : psi12 (CannonFloydParry.Y n) = of n := by
  cases n with
  | zero => exact toGroup.of _
  | succ n =>
    show psi12 ((of CannonFloydParry.FormalAB.A ^ n)⁻¹ * of CannonFloydParry.FormalAB.B *
      of CannonFloydParry.FormalAB.A ^ n) = _
    rw [map_mul, map_mul, map_inv, map_pow, psi12, toGroup.of, toGroup.of]
    exact (F2_of_succ n).symm

theorem psi21_injective : Function.Injective psi21 := by
  have : psi12.comp psi21 = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro n
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, psi21, toGroup.of]
    exact psi12_Y n
  exact Function.LeftInverse.injective (g := psi12) (fun x => by
    rw [← MonoidHom.comp_apply, this, MonoidHom.id_apply])

end CFP

/-! ## Statement 14: relations (1), (2) present `F`, and `F₂ ≅ F` -/

section PresF
open PresentedGroup

theorem xFin_rep {k n : ℕ} (h : k < n) :
    xFin (List.replicate k true) (List.replicate n true) = some (List.replicate (n + 1) true) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [show k + j + 1 = k + (j + 1) by ring, List.replicate_add, xFin_append, List.replicate_succ]
  simp only [xr, Option.map_some]
  congr 1
  rw [show k + (j + 1) + 1 = k + (j + 2) by ring, List.replicate_add]
  rfl

theorem RX_rel1 (s : Seq) : (of s : PresentedGroup RX) * of s =
    of (s ++ [false]) * of s * of (s ++ [true]) := by
  have h := one_of_mem (rels := RX) (x := FreeGroup.of s * FreeGroup.of s *
    (FreeGroup.of (s ++ [false]) * FreeGroup.of s * FreeGroup.of (s ++ [true]))⁻¹) (Or.inl ⟨s, rfl⟩)
  simp only [map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

theorem RX_rel2 {s t t' : Seq} (ht : xFin s t = some t') :
    (of t : PresentedGroup RX) * of s = of s * of t' := by
  have h := one_of_mem (rels := RX) (x := FreeGroup.of t * FreeGroup.of s *
    (FreeGroup.of s * FreeGroup.of t')⁻¹) (Or.inr ⟨s, t, t', ht, rfl⟩)
  simp only [map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

theorem pres_F (hb : HB) (hr : HR) :
    (∃ phi : PresentedGroup RX →* SeqGroup,
      (∀ s, phi (PresentedGroup.of s) = xs s) ∧ Function.Injective phi ∧ phi.range = F) ∧
    ∃ e : CannonFloydParry.F2 ≃* ↥F,
      ∀ n : ℕ, (e (PresentedGroup.of n) : SeqGroup) = xs (List.replicate n true) := by
  -- the presented group maps onto `F`
  have hRX : ∀ r ∈ RX, FreeGroup.lift xs r = 1 := by
    rintro r (⟨s, rfl⟩ | ⟨s, t, t', h, rfl⟩)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      exact mul_inv_eq_one.mpr (rel1_grp hr s)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      exact mul_inv_eq_one.mpr (rel2_grp hr h)
  let P : PresentedGroup RX →* SeqGroup := toGroup hRX
  have hP : ∀ s, P (of s) = xs s := fun s => toGroup.of hRX
  have hPrange : P.range = F := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure, F]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩; exact ⟨s, (hP s).symm⟩
    · rintro ⟨s, rfl⟩; exact ⟨_, ⟨s, rfl⟩, hP s⟩
  -- `F₂` maps onto the presented group, `Xₙ ↦ x_{1ⁿ}`
  have hF2 : ∀ r ∈ CannonFloydParry.relsF2,
      FreeGroup.lift (fun n => (of (List.replicate n true) : PresentedGroup RX)) r = 1 := by
    rintro r ⟨k, n, hkn, rfl⟩
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    have key : ∀ x y w : PresentedGroup RX, y * x = x * w → x⁻¹ * y * x * w⁻¹ = 1 :=
      fun x y w h => by rw [mul_assoc x⁻¹, h]; group
    exact key _ _ _ (RX_rel2 (xFin_rep hkn))
  let ψ : CannonFloydParry.F2 →* PresentedGroup RX := toGroup hF2
  have hψ : ∀ n, ψ (of n) = of (List.replicate n true) := fun n => toGroup.of hF2
  have hψsurj : Function.Surjective ψ := by
    have hall : ∀ s, (of s : PresentedGroup RX) ∈ ψ.range :=
      gen_x of RX_rel1 (fun _ _ _ h => RX_rel2 h) ψ.range (fun n => ⟨of n, hψ n⟩)
    have htop : ψ.range = ⊤ := by
      rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
      rintro _ ⟨s, rfl⟩; exact hall s
    intro w
    have : w ∈ ψ.range := by rw [htop]; trivial
    exact this
  -- the composite `F₂ → SeqGroup` is injective, by comparison with the interval model
  let ρ : CannonFloydParry.F2 →* SeqGroup := P.comp ψ
  have hρ : ∀ n, ρ (of n) = xs (List.replicate n true) := fun n => by
    simp only [ρ, MonoidHom.comp_apply, hψ, hP]
  obtain ⟨e1, he1A, he1B⟩ := CannonFloydParry.exists_mulEquiv_F1_F
  let σ : CannonFloydParry.F2 →* (CannonFloydParry.UI ≃o CannonFloydParry.UI) :=
    (CannonFloydParry.F.subtype.comp e1.toMonoidHom).comp psi21
  have hσinj : Function.Injective σ :=
    (Subtype.val_injective.comp e1.injective).comp psi21_injective
  have hσ0 : σ (of 0) = CannonFloydParry.mapA := by
    simp only [σ, MonoidHom.comp_apply, psi21, toGroup.of]
    exact he1A
  have hσ1 : σ (of 1) = CannonFloydParry.mapB := by
    simp only [σ, MonoidHom.comp_apply, psi21, toGroup.of]
    have hY1 : CannonFloydParry.Y 1 = of CannonFloydParry.FormalAB.B := by
      simp [CannonFloydParry.Y]
    rw [hY1]
    exact he1B
  let S : Subgroup CannonFloydParry.F2 :=
    { carrier := {v | SemiB (ρ v) (σ v)}
      mul_mem' := fun {v w} hv hw => by
        change SemiB (ρ (v * w)) (σ (v * w))
        rw [map_mul, map_mul]
        exact SemiB_mul hv hw
      one_mem' := by
        change SemiB (ρ 1) (σ 1)
        rw [map_one, map_one]; exact SemiB_one
      inv_mem' := fun {v} hv => by
        change SemiB (ρ v⁻¹) (σ v⁻¹)
        rw [map_inv, map_inv]
        exact SemiB_inv hv }
  have hS0 : (of 0 : CannonFloydParry.F2) ∈ S := by
    change SemiB (ρ (of 0)) (σ (of 0))
    rw [hρ, hσ0]; exact SemiB_A hb
  have hS1 : (of 1 : CannonFloydParry.F2) ∈ S := by
    change SemiB (ρ (of 1)) (σ (of 1))
    rw [hρ, hσ1]; exact SemiB_B hb
  have hStop : S = ⊤ := by
    rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => exact hS0
    | succ n =>
      rw [SetLike.mem_coe, F2_of_succ]
      exact S.mul_mem (S.mul_mem (S.inv_mem (S.pow_mem hS0 n)) hS1) (S.pow_mem hS0 n)
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hvS : v ∈ S := by rw [hStop]; trivial
    have hsem : SemiB (ρ v) (σ v) := hvS
    rw [hv] at hsem
    have : σ v = 1 := eq_one_of_fix_beta (σ v) hsem
    exact hσinj (by rw [this, map_one])
  have hPinj : Function.Injective P := by
    rw [injective_iff_map_eq_one]
    intro w hw
    obtain ⟨v, rfl⟩ := hψsurj w
    have : v = 1 := hρinj (by simpa [ρ] using hw)
    rw [this, map_one]
  refine ⟨⟨P, hP, hPinj, hPrange⟩, ?_⟩
  have hρF : ∀ v, ρ v ∈ F := fun v => hPrange ▸ ⟨ψ v, rfl⟩
  let ρF : CannonFloydParry.F2 →* ↥F := ρ.codRestrict F hρF
  have hbij : Function.Bijective ρF := by
    refine ⟨fun v w h => hρinj (congrArg Subtype.val h), fun y => ?_⟩
    have : (y : SeqGroup) ∈ P.range := by rw [hPrange]; exact y.2
    obtain ⟨w, hw⟩ := this
    obtain ⟨v, rfl⟩ := hψsurj w
    exact ⟨v, Subtype.ext hw⟩
  exact ⟨MulEquiv.ofBijective ρF hbij, fun n => hρ n⟩

end PresF

/-! ## Statement 15: the `F`-conjugacy classes of the `y_s` -/

section Conj


end Conj

end LodhaMoore.Dev.S3a

namespace LodhaMoore

open LodhaMoore.Dev.S3a

end LodhaMoore
end

section
open LodhaMoore
open LodhaMoore.Dev.S3a
theorem solution :
    (∃ phi : PresentedGroup RX →* SeqGroup,
      (∀ s, phi (PresentedGroup.of s) = xs s) ∧ Function.Injective phi ∧ phi.range = F) ∧
    ∃ e : CannonFloydParry.F2 ≃* ↥F, ∀ n : ℕ, (e (PresentedGroup.of n) : SeqGroup) = xs (List.replicate n true) :=
  pres_F bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R.1
    bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R.2
end
