-- Prove2me | solution 1 for LodhaMoore.bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.993817+00:00
-- url     : https://prove2.me/submissions/f530f2fc-a166-4b66-9acf-2e7364636fb8

import Mathlib
import Definitions.Def_LodhaMoore
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

theorem eq_cons (ξ : Str) : ξ = Stream'.cons (ξ 0) ξ.tail := (Stream'.eta ξ).symm

theorem exists_cons (ξ : Str) : ∃ d ζ, ξ = Stream'.cons d ζ := ⟨_, _, eq_cons ξ⟩

theorem cases_x (ξ : Str) :
    (∃ ζ, ξ = Stream'.cons false (Stream'.cons false ζ)) ∨
    (∃ ζ, ξ = Stream'.cons false (Stream'.cons true ζ)) ∨ (∃ ζ, ξ = Stream'.cons true ζ) := by
  obtain ⟨d, ζ, rfl⟩ := exists_cons ξ
  obtain ⟨e, η, rfl⟩ := exists_cons ζ
  cases d <;> cases e <;>
    first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl⟩) | exact Or.inr (Or.inr ⟨_, rfl⟩)

theorem cases_xinv (ξ : Str) :
    (∃ ζ, ξ = Stream'.cons false ζ) ∨
    (∃ ζ, ξ = Stream'.cons true (Stream'.cons false ζ)) ∨
    (∃ ζ, ξ = Stream'.cons true (Stream'.cons true ζ)) := by
  obtain ⟨d, ζ, rfl⟩ := exists_cons ξ
  obtain ⟨e, η, rfl⟩ := exists_cons ζ
  cases d <;> cases e <;>
    first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl⟩) | exact Or.inr (Or.inr ⟨_, rfl⟩)

theorem append_cons (d : Bool) (l : Seq) (s : Str) :
    (d :: l) ++ₛ s = Stream'.cons d (l ++ₛ s) := rfl

theorem take_length_append (s : Seq) (η : Str) : (s ++ₛ η).take s.length = s := by
  have := Stream'.append_take 0 s η
  simpa [Stream'.take_zero] using this.symm

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

theorem localize_append_self (s : Seq) (f : Str → Str) (η : Str) :
    localize s f (s ++ₛ η) = s ++ₛ f η := by
  induction s with
  | nil => simp [localize_nil]
  | cons d s ih => rw [append_cons, localize_cons_same, ih]; rfl

theorem localize_append (s t : Seq) (f : Str → Str) (η : Str) :
    localize (s ++ t) f (s ++ₛ η) = s ++ₛ localize t f η := by
  induction s with
  | nil => simp
  | cons d s ih => rw [List.cons_append, append_cons, localize_cons_same, ih]; rfl

theorem localize_of_not {s : Seq} {ξ : Str} (h : ∀ η, ξ ≠ s ++ₛ η) (f : Str → Str) :
    localize s f ξ = ξ := by
  unfold localize
  rw [if_neg]
  intro h'
  apply h (ξ.drop s.length)
  conv_lhs => rw [← Stream'.append_take_drop s.length ξ]
  rw [h']

/-- The cylinder of `s`. -/
def Cyl (s : Seq) (ξ : Str) : Prop := ∃ η, ξ = s ++ₛ η

theorem localize_of_not_cyl {s : Seq} {ξ : Str} (h : ¬ Cyl s ξ) (f : Str → Str) :
    localize s f ξ = ξ :=
  localize_of_not (fun η hη => h ⟨η, hη⟩) f

theorem cyl_append_self (s : Seq) (η : Str) : Cyl s (s ++ₛ η) := ⟨η, rfl⟩

theorem cyl_mono {s t : Seq} {ξ : Str} (h : Cyl (s ++ t) ξ) : Cyl s ξ := by
  obtain ⟨η, rfl⟩ := h
  exact ⟨t ++ₛ η, by rw [Stream'.append_append_stream]⟩

theorem prefix_of_cyl_cyl {s t : Seq} {ξ : Str} (hs : Cyl s ξ) (ht : Cyl t ξ) :
    s <+: t ∨ t <+: s := by
  obtain ⟨η, rfl⟩ := hs
  obtain ⟨ζ, hζ⟩ := ht
  have h1 : (s ++ₛ η).take s.length = s := take_length_append s η
  have h2 : (s ++ₛ η).take t.length = t := by rw [hζ]; exact take_length_append t ζ
  rcases le_total s.length t.length with h | h
  · left; rw [← h1, ← h2]; exact Stream'.take_prefix_take_left _ _ _ h
  · right; rw [← h1, ← h2]; exact Stream'.take_prefix_take_left _ _ _ h

theorem not_cyl_of_incompatible {s t : Seq} (h : Incompatible s t) {ξ : Str} (hs : Cyl s ξ) :
    ¬ Cyl t ξ := fun ht => by
  rcases prefix_of_cyl_cyl hs ht with h' | h'
  · exact h.1 h'
  · exact h.2 h'

theorem cyl_localize_iff (s : Seq) (f : Str → Str) (ξ : Str) :
    Cyl s (localize s f ξ) ↔ Cyl s ξ := by
  by_cases h : Cyl s ξ
  · obtain ⟨η, rfl⟩ := h
    rw [localize_append_self]
    exact ⟨fun _ => cyl_append_self _ _, fun _ => cyl_append_self _ _⟩
  · rw [localize_of_not_cyl h]

theorem localize_comp (s : Seq) (f g : Str → Str) (ξ : Str) :
    localize s f (localize s g ξ) = localize s (f ∘ g) ξ := by
  by_cases h : Cyl s ξ
  · obtain ⟨η, rfl⟩ := h
    simp [localize_append_self]
  · rw [localize_of_not_cyl h, localize_of_not_cyl h, localize_of_not_cyl h]

theorem localize_inv {s : Seq} {f g : Str → Str} (h : ∀ ξ, g (f ξ) = ξ) (ξ : Str) :
    localize s g (localize s f ξ) = ξ := by
  rw [localize_comp]
  by_cases hc : Cyl s ξ
  · obtain ⟨η, rfl⟩ := hc
    rw [localize_append_self, Function.comp_apply, h]
  · rw [localize_of_not_cyl hc]

theorem localize_bijective {s : Seq} {f g : Str → Str} (h1 : ∀ ξ, g (f ξ) = ξ)
    (h2 : ∀ ξ, f (g ξ) = ξ) : Function.Bijective (localize s f) :=
  ⟨Function.LeftInverse.injective (g := localize s g) (localize_inv h1),
    Function.RightInverse.surjective (g := localize s g) (localize_inv h2)⟩

/-- Localizations to incompatible sequences commute. -/
theorem localize_comm {s t : Seq} (h : Incompatible s t) (f g : Str → Str) (ξ : Str) :
    localize s f (localize t g ξ) = localize t g (localize s f ξ) := by
  by_cases hs : Cyl s ξ
  · have ht : ¬ Cyl t ξ := not_cyl_of_incompatible h hs
    have hs' : Cyl s (localize s f ξ) := (cyl_localize_iff s f ξ).2 hs
    rw [localize_of_not_cyl ht, localize_of_not_cyl (not_cyl_of_incompatible h hs')]
  · by_cases ht : Cyl t ξ
    · have ht' : Cyl t (localize t g ξ) := (cyl_localize_iff t g ξ).2 ht
      rw [localize_of_not_cyl hs,
        localize_of_not_cyl (not_cyl_of_incompatible ⟨h.2, h.1⟩ ht')]
    · rw [localize_of_not_cyl hs, localize_of_not_cyl ht, localize_of_not_cyl hs]

/-- If `k` maps `t⌢η` to `t'⌢η` and nothing else into the cylinder of `t'`, then
`k ∘ localize t g = localize t' g ∘ k`. -/
theorem comp_localize {t t' : Seq} {k : Str → Str} (h1 : ∀ η, k (t ++ₛ η) = t' ++ₛ η)
    (h2 : ∀ ξ, Cyl t' (k ξ) → Cyl t ξ) (g : Str → Str) (ξ : Str) :
    k (localize t g ξ) = localize t' g (k ξ) := by
  by_cases h : Cyl t ξ
  · obtain ⟨η, rfl⟩ := h
    rw [localize_append_self, h1, h1, localize_append_self]
  · rw [localize_of_not_cyl h, localize_of_not_cyl (fun h' => h (h2 ξ h'))]

/-! ## `x` and `x⁻¹` -/

/-- `x⁻¹`: `0η ↦ 00η`, `10η ↦ 01η`, `11η ↦ 1η`. -/
def xInvFun (ξ : Str) : Str :=
  match ξ 0, ξ 1 with
  | false, _ => Stream'.cons false ξ
  | true, false => Stream'.cons false (Stream'.cons true (ξ.drop 2))
  | true, true => ξ.tail

theorem xFun_00 (ζ : Str) : xFun (Stream'.cons false (Stream'.cons false ζ)) =
    Stream'.cons false ζ := rfl
theorem xFun_01 (ζ : Str) : xFun (Stream'.cons false (Stream'.cons true ζ)) =
    Stream'.cons true (Stream'.cons false ζ) := rfl
theorem xFun_1 (ζ : Str) : xFun (Stream'.cons true ζ) = Stream'.cons true (Stream'.cons true ζ) :=
  rfl

theorem xInvFun_xFun (ξ : Str) : xInvFun (xFun ξ) = ξ := by
  rcases cases_x ξ with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
  · rfl
  · rfl
  · rfl

theorem xFun_xInvFun (ξ : Str) : xFun (xInvFun ξ) = ξ := by
  rcases cases_xinv ξ with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
  · rfl
  · rfl
  · rfl

/-! ## `y` and `y⁻¹` -/

theorem yStep_ne_nil (σ : Bool) (ξ : Str) : (yStep σ ξ).1 ≠ [] := by
  cases σ <;> simp only [yStep] <;> split <;> simp

theorem yOut_length (k : ℕ) (σ : Bool) (ξ : Str) : k ≤ (yOut k σ ξ).length := by
  induction k generalizing σ ξ with
  | zero => simp
  | succ k ih =>
    simp only [yOut, List.length_append]
    have := ih (yStep σ ξ).2.1 (yStep σ ξ).2.2
    have := List.length_pos_of_ne_nil (yStep_ne_nil σ ξ)
    omega

theorem yOut_prefix_succ (k : ℕ) (σ : Bool) (ξ : Str) : yOut k σ ξ <+: yOut (k + 1) σ ξ := by
  induction k generalizing σ ξ with
  | zero => simp [yOut]
  | succ k ih =>
    simp only [yOut] at ih ⊢
    exact (List.prefix_append_right_inj _).mpr (ih _ _)

theorem yOut_prefix {k m : ℕ} (h : k ≤ m) (σ : Bool) (ξ : Str) : yOut k σ ξ <+: yOut m σ ξ := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih => exact ih.trans (yOut_prefix_succ m σ ξ)

theorem getD_of_prefix {l₁ l₂ : Seq} (h : l₁ <+: l₂) {n : ℕ} (hn : n < l₁.length) :
    l₁.getD n false = l₂.getD n false := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hn]

theorem yFun_eq_getD {n m : ℕ} (h : n + 1 ≤ m) (σ : Bool) (ξ : Str) :
    yFun σ ξ n = (yOut m σ ξ).getD n false := by
  unfold yFun
  exact getD_of_prefix (yOut_prefix h σ ξ) (by have := yOut_length (n + 1) σ ξ; omega)

theorem yFun_rec (σ : Bool) (ξ : Str) :
    yFun σ ξ = (yStep σ ξ).1 ++ₛ yFun (yStep σ ξ).2.1 (yStep σ ξ).2.2 := by
  funext n
  have hne := List.length_pos_of_ne_nil (yStep_ne_nil σ ξ)
  change yFun σ ξ n = Stream'.get _ n
  rw [yFun_eq_getD (le_refl _), yOut]
  by_cases hn : n < (yStep σ ξ).1.length
  · rw [List.getD_append _ _ _ _ hn, Stream'.get_append_left n _ _ hn, List.getD_eq_getElem _ _ hn]
  · push Not at hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [List.getD_append_right _ _ _ _ hn, Stream'.get_append_right, Nat.add_sub_cancel_left]
    change _ = yFun (yStep σ ξ).2.1 (yStep σ ξ).2.2 j
    rw [yFun_eq_getD (m := (yStep σ ξ).1.length + j) (by omega)]

theorem yT_00 (ζ : Str) : yFun true (Stream'.cons false (Stream'.cons false ζ)) =
    Stream'.cons false (yFun true ζ) := by rw [yFun_rec]; rfl
theorem yT_01 (ζ : Str) : yFun true (Stream'.cons false (Stream'.cons true ζ)) =
    Stream'.cons true (Stream'.cons false (yFun false ζ)) := by rw [yFun_rec]; rfl
theorem yT_1 (ζ : Str) : yFun true (Stream'.cons true ζ) =
    Stream'.cons true (Stream'.cons true (yFun true ζ)) := by rw [yFun_rec]; rfl
theorem yF_0 (ζ : Str) : yFun false (Stream'.cons false ζ) =
    Stream'.cons false (Stream'.cons false (yFun false ζ)) := by rw [yFun_rec]; rfl
theorem yF_10 (ζ : Str) : yFun false (Stream'.cons true (Stream'.cons false ζ)) =
    Stream'.cons false (Stream'.cons true (yFun true ζ)) := by rw [yFun_rec]; rfl
theorem yF_11 (ζ : Str) : yFun false (Stream'.cons true (Stream'.cons true ζ)) =
    Stream'.cons true (yFun false ζ) := by rw [yFun_rec]; rfl

theorem yFun_inv_aux (n : ℕ) : ∀ (σ : Bool) (ξ : Str), yFun (!σ) (yFun σ ξ) n = ξ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro σ ξ
  cases σ
  · rcases cases_xinv ξ with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
    · rw [yF_0, Bool.not_false, yT_00]
      match n with
      | 0 => rfl
      | k + 1 => exact ih k (by omega) false ζ
    · rw [yF_10, Bool.not_false, yT_01]
      match n with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => exact ih k (by omega) true ζ
    · rw [yF_11, Bool.not_false, yT_1]
      match n with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => exact ih k (by omega) false ζ
  · rcases cases_x ξ with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
    · rw [yT_00, Bool.not_true, yF_0]
      match n with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => exact ih k (by omega) true ζ
    · rw [yT_01, Bool.not_true, yF_10]
      match n with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => exact ih k (by omega) false ζ
    · rw [yT_1, Bool.not_true, yF_11]
      match n with
      | 0 => rfl
      | k + 1 => exact ih k (by omega) true ζ

theorem yFun_inv (σ : Bool) (ξ : Str) : yFun (!σ) (yFun σ ξ) = ξ :=
  funext fun n => yFun_inv_aux n σ ξ

theorem yF_yT (ξ : Str) : yFun false (yFun true ξ) = ξ := yFun_inv true ξ
theorem yT_yF (ξ : Str) : yFun true (yFun false ξ) = ξ := yFun_inv false ξ

theorem xSeq_bijective (s : Seq) : Function.Bijective (xSeq s) :=
  localize_bijective xInvFun_xFun xFun_xInvFun

theorem ySeq_bijective (s : Seq) : Function.Bijective (ySeq s) :=
  localize_bijective yF_yT yT_yF

theorem localize_tf (t : Seq) (f : Str → Str) (ζ : Str) :
    localize (true :: t) f (Stream'.cons false ζ) = Stream'.cons false ζ :=
  localize_cons_diff (by decide) t f ζ
theorem localize_ft (t : Seq) (f : Str → Str) (ζ : Str) :
    localize (false :: t) f (Stream'.cons true ζ) = Stream'.cons true ζ :=
  localize_cons_diff (by decide) t f ζ

/-! ## The relations (1)–(5) as identities of functions -/

theorem not_cyl_append {s t : Seq} {ξ : Str} (h : ¬ Cyl s ξ) : ¬ Cyl (s ++ t) ξ :=
  fun h' => h (cyl_mono h')

theorem rel1_fun (s : Seq) (ξ : Str) :
    xSeq s (xSeq s ξ) = xSeq (s ++ [true]) (xSeq s (xSeq (s ++ [false]) ξ)) := by
  unfold xSeq
  by_cases h : Cyl s ξ
  · obtain ⟨η, rfl⟩ := h
    rw [localize_append_self, localize_append_self, localize_append, localize_append_self,
      localize_append]
    congr 1
    obtain ⟨d1, η, rfl⟩ := exists_cons η
    obtain ⟨d2, η, rfl⟩ := exists_cons η
    obtain ⟨d3, η, rfl⟩ := exists_cons η
    cases d1 <;> cases d2 <;> cases d3 <;>
      simp only [localize_cons_same, localize_tf, localize_ft, localize_nil, xFun_00, xFun_01,
        xFun_1]
  · rw [localize_of_not_cyl (not_cyl_append h), localize_of_not_cyl h, localize_of_not_cyl h,
      localize_of_not_cyl (not_cyl_append h)]

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

theorem incompatible_of_xFin {s t t' : Seq} (h : xFin s t = some t') (hst : ¬ s <+: t) :
    Incompatible s t ∧ t' = t := by
  unfold xFin at h
  rw [if_neg hst] at h
  split_ifs at h with hts
  exact ⟨⟨hst, hts⟩, (Option.some.inj h).symm⟩

theorem xSeq_append_of_xFin {s t t' : Seq} (h : xFin s t = some t') (η : Str) :
    xSeq s (t ++ₛ η) = t' ++ₛ η := by
  by_cases hst : s <+: t
  · obtain ⟨r, rfl⟩ := hst
    rw [xFin_append] at h
    unfold xSeq
    rw [Stream'.append_append_stream, localize_append_self]
    rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp [xr] at h <;> subst h <;>
      (rw [Stream'.append_append_stream]; rfl)
  · obtain ⟨hinc, rfl⟩ := incompatible_of_xFin h hst
    unfold xSeq
    rw [localize_of_not_cyl]
    intro hc
    exact not_cyl_of_incompatible hinc hc (cyl_append_self _ _)

theorem cyl_of_cyl_xSeq {s t t' : Seq} (h : xFin s t = some t') {ξ : Str}
    (hc : Cyl t' (xSeq s ξ)) : Cyl t ξ := by
  obtain ⟨η, hη⟩ := hc
  refine ⟨η, ?_⟩
  have h1 : localize s xInvFun (xSeq s ξ) = ξ := localize_inv xInvFun_xFun ξ
  have h2 : localize s xInvFun (xSeq s (t ++ₛ η)) = t ++ₛ η := localize_inv xInvFun_xFun _
  rw [← h1, hη, ← h2, xSeq_append_of_xFin h]

theorem rel23_fun {s t t' : Seq} (h : xFin s t = some t') (g : Str → Str) (ξ : Str) :
    xSeq s (localize t g ξ) = localize t' g (xSeq s ξ) :=
  comp_localize (xSeq_append_of_xFin h) (fun _ hc => cyl_of_cyl_xSeq h hc) g ξ

theorem rel4_fun {s t : Seq} (h : Incompatible s t) (ξ : Str) :
    ySeq t (ySeq s ξ) = ySeq s (ySeq t ξ) :=
  (localize_comm h (yFun true) (yFun true) ξ).symm

theorem rel5_fun (s : Seq) (ξ : Str) :
    ySeq s ξ = ySeq (s ++ [true, true]) (localize (s ++ [true, false]) (yFun false)
      (ySeq (s ++ [false]) (xSeq s ξ))) := by
  unfold xSeq ySeq
  by_cases h : Cyl s ξ
  · obtain ⟨η, rfl⟩ := h
    rw [localize_append_self, localize_append_self, localize_append, localize_append,
      localize_append]
    congr 1
    rcases cases_x η with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
    · simp only [xFun_00, yT_00, localize_cons_same, localize_tf, localize_nil]
    · simp only [xFun_01, yT_01, localize_cons_same, localize_tf, localize_ft, localize_nil]
    · simp only [xFun_1, yT_1, localize_cons_same, localize_ft, localize_nil]
  · rw [localize_of_not_cyl h, localize_of_not_cyl h, localize_of_not_cyl (not_cyl_append h),
      localize_of_not_cyl (not_cyl_append h), localize_of_not_cyl (not_cyl_append h)]

/-! ## `SeqGroup` -/

theorem seq_ext {g h : SeqGroup} (H : ∀ ξ, MulOpposite.unop g ξ = MulOpposite.unop h ξ) :
    g = h :=
  MulOpposite.unop_injective (Equiv.ext H)

theorem unop_mul_apply (g h : SeqGroup) (ξ : Str) :
    MulOpposite.unop (g * h) ξ = MulOpposite.unop h (MulOpposite.unop g ξ) := rfl

theorem unop_toSeqGroup {f : Str → Str} (hf : Function.Bijective f) (ξ : Str) :
    MulOpposite.unop (toSeqGroup f) ξ = f ξ := by
  simp [toSeqGroup, hf]

theorem unop_toSeqGroup_inv {f g : Str → Str} (hf : Function.Bijective f)
    (hfg : ∀ ξ, f (g ξ) = ξ) (ξ : Str) : MulOpposite.unop (toSeqGroup f)⁻¹ ξ = g ξ := by
  simp only [toSeqGroup, hf, dif_pos, MulOpposite.unop_inv, MulOpposite.unop_op,
    Equiv.Perm.inv_def]
  rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, hfg]

/-- Every `x_s` and `y_s` is a bijection. -/
def HB : Prop := ∀ s, Function.Bijective (xSeq s) ∧ Function.Bijective (ySeq s)

/-- Every relation of `R` holds. -/
def HR : Prop := ∀ r ∈ R, FreeGroup.lift Gen.val r = 1

theorem hB : HB := fun s => ⟨xSeq_bijective s, ySeq_bijective s⟩

section
variable (hb : HB)
include hb

theorem unop_xs (s : Seq) (ξ : Str) : MulOpposite.unop (xs s) ξ = xSeq s ξ :=
  unop_toSeqGroup (hb s).1 ξ

theorem unop_ys (s : Seq) (ξ : Str) : MulOpposite.unop (ys s) ξ = ySeq s ξ :=
  unop_toSeqGroup (hb s).2 ξ

theorem unop_ys_inv (s : Seq) (ξ : Str) :
    MulOpposite.unop (ys s)⁻¹ ξ = localize s (yFun false) ξ :=
  unop_toSeqGroup_inv (hb s).2 (localize_inv yT_yF) ξ

end

theorem hR : HR := by
  rintro r ⟨rel, rfl⟩
  rw [map_mul, map_inv, mul_inv_eq_one]
  cases rel with
  | one s =>
    simp only [Rel.lhs, Rel.rhs, map_mul, FreeGroup.lift_apply_of, Gen.val]
    refine seq_ext fun ξ => ?_
    simp only [unop_mul_apply, unop_xs hB]
    exact rel1_fun s ξ
  | two s t t' h =>
    simp only [Rel.lhs, Rel.rhs, map_mul, FreeGroup.lift_apply_of, Gen.val]
    refine seq_ext fun ξ => ?_
    simp only [unop_mul_apply, unop_xs hB]
    exact rel23_fun h xFun ξ
  | three s t t' h =>
    simp only [Rel.lhs, Rel.rhs, map_mul, FreeGroup.lift_apply_of, Gen.val]
    refine seq_ext fun ξ => ?_
    simp only [unop_mul_apply, unop_xs hB, unop_ys hB]
    exact rel23_fun h (yFun true) ξ
  | four s t h =>
    simp only [Rel.lhs, Rel.rhs, map_mul, FreeGroup.lift_apply_of, Gen.val]
    refine seq_ext fun ξ => ?_
    simp only [unop_mul_apply, unop_ys hB]
    exact rel4_fun h ξ
  | five s =>
    simp only [Rel.lhs, Rel.rhs, map_mul, map_inv, FreeGroup.lift_apply_of, Gen.val]
    refine seq_ext fun ξ => ?_
    simp only [unop_mul_apply, unop_xs hB, unop_ys hB, unop_ys_inv hB]
    exact rel5_fun s ξ

/-! ## `phi`: the recursion, and the nested intervals -/

/-! ## Proposition 3.1, first part: `phi(ξ.y) = 2 phi(ξ)` -/

/-! ## Proposition 3.1, second part: `Phi` carries `x`, `x₁`, `y₁₀` to `a`, `b`, `c` -/

/-! ## Generation and conjugacy, from the relations alone (in any group) -/

section GroupGen

variable {Γ : Type*} [Group Γ]

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

end

/-! ## Every element of `G` is locally determined -/

/-! ## `Phi` is onto -/

/-! ## The identification `G₀ ≅ ⟨X ∪ Y₀⟩` induced by `Phi` -/

/-! ## Binary expansions: `F` on sequences and `F` on the unit interval -/

/-! ## The presentations of Cannon–Floyd–Parry: `F₂ → F₁` is injective -/

section CFP
open PresentedGroup

end CFP

/-! ## Statement 14: relations (1), (2) present `F`, and `F₂ ≅ F` -/

section PresF
open PresentedGroup

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
    (∀ s, Function.Bijective (xSeq s) ∧ Function.Bijective (ySeq s)) ∧
      ∀ r ∈ R, FreeGroup.lift Gen.val r = 1 :=
  ⟨hB, hR⟩
end
