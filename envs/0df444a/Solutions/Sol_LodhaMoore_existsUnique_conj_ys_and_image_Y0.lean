-- Prove2me | solution 1 for LodhaMoore.existsUnique_conj_ys_and_image_Y0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.947351+00:00
-- url     : https://prove2.me/submissions/a13cf23e-2287-4dc7-a781-fd31640b41f9

import Mathlib
import Definitions.Def_LodhaMoore
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

theorem localize_append_self (s : Seq) (f : Str → Str) (η : Str) :
    localize s f (s ++ₛ η) = s ++ₛ f η := by
  induction s with
  | nil => simp [localize_nil]
  | cons d s ih => rw [append_cons, localize_cons_same, ih]; rfl

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

/-! ## `x` and `x⁻¹` -/

theorem xFun_00 (ζ : Str) : xFun (Stream'.cons false (Stream'.cons false ζ)) =
    Stream'.cons false ζ := rfl
theorem xFun_1 (ζ : Str) : xFun (Stream'.cons true ζ) = Stream'.cons true (Stream'.cons true ζ) :=
  rfl

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

theorem unop_ys (s : Seq) (ξ : Str) : MulOpposite.unop (ys s) ξ = ySeq s ξ :=
  unop_toSeqGroup (hb s).2 ξ

end

/-! ## `phi`: the recursion, and the nested intervals -/

/-! ## Proposition 3.1, first part: `phi(ξ.y) = 2 phi(ξ)` -/

/-! ## Proposition 3.1, second part: `Phi` carries `x`, `x₁`, `y₁₀` to `a`, `b`, `c` -/

/-! ## Generation and conjugacy, from the relations alone (in any group) -/

theorem xFin_nil (r : Seq) : xFin [] r = xr r := by
  have := xFin_append [] r
  simp only [List.nil_append] at this
  rw [this]
  cases xr r <;> rfl

theorem xFin_one (r : Seq) : xFin [true] (true :: r) = (xr r).map (true :: ·) :=
  xFin_append [true] r

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

theorem isConst_replicate (k : ℕ) (d : Bool) : IsConst (List.replicate k d) := by
  intro i hi j hj
  simp only [List.length_replicate] at hi hj
  simp [hi, hj]

theorem nonconst_decomp {s : Seq} (h : ¬ IsConst s) :
    ∃ n r, s = List.replicate (n + 1) true ++ false :: r ∨
      s = List.replicate (n + 1) false ++ true :: r := by
  rcases s with _ | ⟨d, s⟩
  · exact absurd (fun i hi => absurd hi (by simp)) h
  · rcases decomp d s with h' | ⟨n, r, h'⟩
    · exact absurd (by rw [h', ← List.replicate_succ]; exact isConst_replicate _ _) h
    · refine ⟨n, r, ?_⟩
      rw [h', ← List.cons_append, ← List.replicate_succ]
      cases d
      · right; rfl
      · left; rfl

section GroupGen

variable {Γ : Type*} [Group Γ]

/-- `y_v` is a `K`-conjugate of `y_u`. -/
def CJ (Y : Seq → Γ) (K : Subgroup Γ) (u v : Seq) : Prop := ∃ g ∈ K, Y v = g⁻¹ * Y u * g

variable {Y : Seq → Γ} {K : Subgroup Γ}

theorem CJ.refl (u : Seq) : CJ Y K u u := ⟨1, K.one_mem, by group⟩

theorem CJ.symm {u v : Seq} (h : CJ Y K u v) : CJ Y K v u := by
  obtain ⟨g, hg, h⟩ := h
  exact ⟨g⁻¹, K.inv_mem hg, by rw [h]; group⟩

theorem CJ.trans {u v w : Seq} (h : CJ Y K u v) (h' : CJ Y K v w) : CJ Y K u w := by
  obtain ⟨g, hg, h⟩ := h
  obtain ⟨g', hg', h'⟩ := h'
  exact ⟨g * g', K.mul_mem hg hg', by rw [h', h]; group⟩

theorem CJ.move (X : Seq → Γ) (h3 : ∀ s t t', xFin s t = some t' → Y t * X s = X s * Y t')
    (hK : ∀ s, X s ∈ K) {s t t' : Seq} (h : xFin s t = some t') : CJ Y K t t' :=
  ⟨X s, hK s, by rw [mul_assoc, h3 s t t' h]; group⟩

section moves
variable (X : Seq → Γ) (h3 : ∀ s t t', xFin s t = some t' → Y t * X s = X s * Y t')
  (hK : ∀ s, X s ∈ K)
include h3 hK

theorem cj_10 (r : Seq) : CJ Y K [true, false] (true :: false :: r) := by
  induction r with
  | nil => exact CJ.refl _
  | cons d r ih =>
    cases d
    · refine ih.trans (CJ.move X h3 hK (s := [true]) ?_).symm
      rw [xFin_one]; rfl
    · refine (ih.trans (CJ.move X h3 hK (s := []) (t := true :: false :: r)
        (t' := true :: true :: false :: r) ?_)).trans
        (CJ.move X h3 hK (s := [true]) (t := true :: false :: true :: r)
          (t' := true :: true :: false :: r) ?_).symm
      · rw [xFin_nil]; rfl
      · rw [xFin_one]; rfl

theorem cj_1n0 (n : ℕ) (r : Seq) :
    CJ Y K [true, false] (List.replicate (n + 1) true ++ false :: r) := by
  induction n with
  | zero => exact cj_10 X h3 hK r
  | succ n ih =>
    refine ih.trans (CJ.move X h3 hK (s := []) ?_)
    rw [xFin_nil, List.replicate_succ, List.cons_append]; rfl

theorem cj_0n1 (n : ℕ) (r : Seq) :
    CJ Y K [true, false] (List.replicate (n + 1) false ++ true :: r) := by
  induction n with
  | zero =>
    refine (cj_10 X h3 hK r).trans (CJ.move X h3 hK (s := []) ?_).symm
    rw [xFin_nil]; rfl
  | succ n ih =>
    refine ih.trans (CJ.move X h3 hK (s := []) ?_).symm
    rw [xFin_nil, List.replicate_succ, List.replicate_succ, List.cons_append, List.cons_append]
    rfl

theorem cj_nonconst {s : Seq} (h : ¬ IsConst s) : CJ Y K [true, false] s := by
  obtain ⟨n, r, h | h⟩ := nonconst_decomp h <;> rw [h]
  · exact cj_1n0 X h3 hK n r
  · exact cj_0n1 X h3 hK n r

theorem cj_0n (n : ℕ) : CJ Y K [false] (List.replicate (n + 1) false) := by
  induction n with
  | zero => exact CJ.refl _
  | succ n ih =>
    refine ih.trans (CJ.move X h3 hK (s := []) ?_).symm
    rw [xFin_nil, List.replicate_succ, List.replicate_succ]; rfl

theorem cj_1n (n : ℕ) : CJ Y K [true] (List.replicate (n + 1) true) := by
  induction n with
  | zero => exact CJ.refl _
  | succ n ih =>
    refine ih.trans (CJ.move X h3 hK (s := []) ?_)
    rw [xFin_nil, List.replicate_succ]; rfl

end moves

end GroupGen

/-! ## The relations in `SeqGroup`, from `HR` -/

section
variable (hr : HR)
include hr

theorem rel3_grp {s t t' : Seq} (h : xFin s t = some t') : ys t * xs s = xs s * ys t' := by
  have := hr _ ⟨Rel.three s t t' h, rfl⟩
  simp only [Rel.lhs, Rel.rhs, map_mul, map_inv, FreeGroup.lift_apply_of, Gen.val] at this
  exact mul_inv_eq_one.mp this

end

theorem xs_mem_F (s : Seq) : xs s ∈ F := Subgroup.subset_closure ⟨s, rfl⟩

/-! ## Every element of `G` is locally determined -/

theorem cyl_iff_take (s : Seq) (ξ : Str) : Cyl s ξ ↔ ξ.take s.length = s := by
  constructor
  · rintro ⟨η, rfl⟩; exact take_length_append s η
  · intro h
    refine ⟨ξ.drop s.length, ?_⟩
    conv_lhs => rw [← Stream'.append_take_drop s.length ξ]
    rw [h]

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


theorem rep_append_stream (m n : ℕ) (d : Bool) (η : Str) :
    List.replicate m d ++ₛ (List.replicate n d ++ₛ η) = List.replicate (m + n) d ++ₛ η := by
  rw [← Stream'.append_append_stream, List.replicate_add]

theorem rep_comm_stream (m n : ℕ) (d : Bool) (η : Str) :
    List.replicate m d ++ₛ (List.replicate n d ++ₛ η) = List.replicate n d ++ₛ (List.replicate m d ++ₛ η) := by
  rw [rep_append_stream, rep_append_stream, Nat.add_comm]

theorem rep_succ_stream (n : ℕ) (d : Bool) (η : Str) :
    List.replicate (n + 1) d ++ₛ η = Stream'.cons d (List.replicate n d ++ₛ η) := rfl

theorem rep_cons_stream (n : ℕ) (d : Bool) (η : Str) :
    List.replicate n d ++ₛ Stream'.cons d η = List.replicate (n + 1) d ++ₛ η := by
  rw [show Stream'.cons d η = List.replicate 1 d ++ₛ η from rfl, rep_append_stream]

theorem rep_get_lt {n i : ℕ} (h : i < n) (d : Bool) (η : Str) : (List.replicate n d ++ₛ η) i = d := by
  change (List.replicate n d ++ₛ η).get i = d
  rw [Stream'.get_append_left i _ _ (by simpa using h)]
  simp

theorem rep_get_eq (n : ℕ) (d : Bool) (η : Str) : (List.replicate n d ++ₛ η) n = η 0 := by
  change (List.replicate n d ++ₛ η).get n = η.get 0
  have := Stream'.get_append_length (List.replicate n d) η
  rwa [List.length_replicate] at this

/-- Near the constant sequence `d̄`, `g` deletes or inserts digits `d`. -/
def GermD (d : Bool) : Subgroup SeqGroup where
  carrier := {g | ∃ A B, ∀ η, MulOpposite.unop g (List.replicate A d ++ₛ η) = List.replicate B d ++ₛ η}
  one_mem' := ⟨0, 0, fun _ => rfl⟩
  mul_mem' := by
    rintro g h ⟨A, B, hg⟩ ⟨C, D, hh⟩
    refine ⟨A + C, D + B, fun η => ?_⟩
    rw [unop_mul_apply, ← rep_append_stream, hg, rep_comm_stream, hh, rep_append_stream]
  inv_mem' := by
    rintro g ⟨A, B, hg⟩
    refine ⟨B, A, fun η => ?_⟩
    rw [← hg, ← unop_mul_apply, mul_inv_cancel, unop_one_apply]

theorem xs_mem_GermD (hb : HB) (d : Bool) (s : Seq) : xs s ∈ GermD d := by
  by_cases hs : s = List.replicate s.length d
  · set k := s.length
    rw [hs]
    cases d
    · refine ⟨k + 2, k + 1, fun η => ?_⟩
      rw [unop_xs hb, ← rep_append_stream, xSeq, localize_append_self]
      change List.replicate k false ++ₛ xFun (Stream'.cons false (Stream'.cons false η)) = _
      rw [xFun_00, rep_cons_stream]
    · refine ⟨k + 1, k + 2, fun η => ?_⟩
      rw [unop_xs hb, ← rep_append_stream, xSeq, localize_append_self]
      change List.replicate k true ++ₛ xFun (Stream'.cons true η) = _
      rw [xFun_1, rep_cons_stream, rep_cons_stream]
  · refine ⟨s.length, s.length, fun η => ?_⟩
    rw [unop_xs hb, xSeq, localize_of_not_cyl]
    rw [cyl_iff_take]
    intro h
    have := take_length_append (List.replicate s.length d) η
    rw [List.length_replicate] at this
    exact hs (h.symm.trans this)

theorem F_le_GermD (hb : HB) (d : Bool) : F ≤ GermD d := by
  rw [F, Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  exact xs_mem_GermD hb d s

/-- `h` fixes a neighbourhood of `d̄` pointwise. -/
def Pd (d : Bool) (h : SeqGroup) : Prop :=
  ∃ N, ∀ η, MulOpposite.unop h (List.replicate N d ++ₛ η) = List.replicate N d ++ₛ η

theorem Pd_mono {d : Bool} {h : SeqGroup} {N : ℕ}
    (hN : ∀ η, MulOpposite.unop h (List.replicate N d ++ₛ η) = List.replicate N d ++ₛ η) (j : ℕ) (η : Str) :
    MulOpposite.unop h (List.replicate (N + j) d ++ₛ η) = List.replicate (N + j) d ++ₛ η := by
  rw [← rep_append_stream, hN]

theorem Pd_conj {d : Bool} {g h : SeqGroup} (hg : g ∈ GermD d) (hP : Pd d h) :
    Pd d (g⁻¹ * h * g) := by
  obtain ⟨A, B, hgi⟩ := (GermD d).inv_mem hg
  obtain ⟨N, hN⟩ := hP
  refine ⟨A + N, fun η => ?_⟩
  have hback : ∀ X, MulOpposite.unop g (List.replicate B d ++ₛ X) = List.replicate A d ++ₛ X := fun X => by
    rw [← hgi, ← unop_mul_apply, inv_mul_cancel, unop_one_apply]
  rw [unop_mul_apply, unop_mul_apply, ← rep_append_stream, hgi, rep_comm_stream, hN,
    rep_comm_stream, hback, rep_append_stream]

theorem Pd_conj_iff (hb : HB) (d : Bool) {g h : SeqGroup} (hg : g ∈ F) :
    Pd d h ↔ Pd d (g⁻¹ * h * g) := by
  refine ⟨Pd_conj (F_le_GermD hb d hg), fun hP => ?_⟩
  have := Pd_conj (F_le_GermD hb d (F.inv_mem hg)) hP
  rwa [inv_inv, show g * (g⁻¹ * h * g) * g⁻¹ = h by group] at this

theorem Pd_ys (hb : HB) {d : Bool} {u : Seq} (hu : u ≠ List.replicate u.length d) : Pd d (ys u) := by
  refine ⟨u.length, fun η => ?_⟩
  rw [unop_ys hb, ySeq, localize_of_not_cyl]
  rw [cyl_iff_take]
  intro h
  have := take_length_append (List.replicate u.length d) η
  rw [List.length_replicate] at this
  exact hu (h.symm.trans this)

theorem claimA (N : ℕ) :
    (yFun true (List.replicate (2 * N + 1) false ++ₛ Stream'.const true)) N = true := by
  induction N with
  | zero =>
    change yFun true (Stream'.cons false (Stream'.cons true (Stream'.const true))) 0 = true
    rw [yT_01]; rfl
  | succ N ih =>
    rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, rep_succ_stream, rep_succ_stream, yT_00]
    exact ih

theorem claimB (N : ℕ) : ∀ i ≤ 2 * N,
    (yFun true (List.replicate N true ++ₛ Stream'.cons false (Stream'.const true))) i = true := by
  induction N with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := by omega
    change yFun true (Stream'.cons false (Stream'.cons true (Stream'.const true))) 0 = true
    rw [yT_01]; rfl
  | succ N ih =>
    intro i hi
    rw [rep_succ_stream, yT_1]
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | j + 2, hj => exact ih j (by omega)

theorem not_P0_y (hb : HB) : ¬ Pd false (ys []) := by
  rintro ⟨N, hN⟩
  have h := hN (List.replicate (N + 1) false ++ₛ Stream'.const true)
  rw [unop_ys hb, ySeq, localize_nil, rep_append_stream, show N + (N + 1) = 2 * N + 1 by ring] at h
  have := congrFun h N
  rw [claimA, rep_get_lt (n := 2 * N + 1) (i := N) (by omega)] at this
  exact Bool.noConfusion this

theorem not_P0_y0 (hb : HB) : ¬ Pd false (ys [false]) := by
  rintro ⟨N, hN⟩
  have h := Pd_mono hN 1 (List.replicate (N + 1) false ++ₛ Stream'.const true)
  rw [unop_ys hb, ySeq, rep_succ_stream, localize_cons_same, localize_nil, rep_append_stream,
    show N + (N + 1) = 2 * N + 1 by ring] at h
  have := congrFun h (N + 1)
  change yFun true (List.replicate (2 * N + 1) false ++ₛ Stream'.const true) N =
    (List.replicate (2 * N + 1) false ++ₛ Stream'.const true) N at this
  rw [claimA, rep_get_lt (n := 2 * N + 1) (i := N) (by omega)] at this
  exact Bool.noConfusion this

theorem not_P1_y (hb : HB) : ¬ Pd true (ys []) := by
  rintro ⟨N, hN⟩
  have h := hN (Stream'.cons false (Stream'.const true))
  rw [unop_ys hb, ySeq, localize_nil] at h
  have := congrFun h N
  rw [claimB N N (by omega), rep_get_eq] at this
  exact Bool.noConfusion this

theorem not_P1_y1 (hb : HB) : ¬ Pd true (ys [true]) := by
  rintro ⟨N, hN⟩
  have h := Pd_mono hN 1 (Stream'.cons false (Stream'.const true))
  rw [unop_ys hb, ySeq, rep_succ_stream, localize_cons_same, localize_nil] at h
  have := congrFun h (N + 1)
  rw [← rep_succ_stream, rep_get_eq] at this
  change (yFun true (List.replicate N true ++ₛ Stream'.cons false (Stream'.const true))) N = false at this
  rw [claimB N N (by omega)] at this
  exact Bool.noConfusion this

/-- The four representatives. -/
def Reps : Set Seq := {[], [false], [true], [true, false]}

theorem Pd_reps (hb : HB) {w : Seq} (hw : w ∈ Reps) :
    (Pd false (ys w) ↔ (w = [true] ∨ w = [true, false])) ∧
      (Pd true (ys w) ↔ (w = [false] ∨ w = [true, false])) := by
  simp only [Reps, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · refine ⟨iff_of_false (not_P0_y hb) (by simp), iff_of_false (not_P1_y hb) (by simp)⟩
  · refine ⟨iff_of_false (not_P0_y0 hb) (by simp),
      iff_of_true (Pd_ys hb (by decide)) (Or.inl rfl)⟩
  · refine ⟨iff_of_true (Pd_ys hb (by decide)) (Or.inl rfl),
      iff_of_false (not_P1_y1 hb) (by simp)⟩
  · exact ⟨iff_of_true (Pd_ys hb (by decide)) (Or.inr rfl),
      iff_of_true (Pd_ys hb (by decide)) (Or.inr rfl)⟩

theorem reps_eq {u v : Seq} (hu : u ∈ Reps) (hv : v ∈ Reps)
    (h0 : (u = [true] ∨ u = [true, false]) ↔ (v = [true] ∨ v = [true, false]))
    (h1 : (u = [false] ∨ u = [true, false]) ↔ (v = [false] ∨ v = [true, false])) : u = v := by
  simp only [Reps, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;> simp_all

theorem uniq_rep (hb : HB) {u v : Seq} (hu : u ∈ Reps) (hv : v ∈ Reps)
    (h : CJ ys F u v) : u = v := by
  obtain ⟨g, hg, e⟩ := h
  have P : ∀ d, Pd d (ys u) ↔ Pd d (ys v) := fun d => by rw [e]; exact Pd_conj_iff hb d hg
  obtain ⟨u0, u1⟩ := Pd_reps hb hu
  obtain ⟨v0, v1⟩ := Pd_reps hb hv
  exact reps_eq hu hv (u0.symm.trans ((P false).trans v0)) (u1.symm.trans ((P true).trans v1))

theorem const_cases {s : Seq} (h : IsConst s) :
    s = [] ∨ ∃ n, s = List.replicate (n + 1) false ∨ s = List.replicate (n + 1) true := by
  rcases s with _ | ⟨d, s⟩
  · exact Or.inl rfl
  · right
    rcases decomp d s with h' | ⟨n, r, h'⟩
    · refine ⟨s.length, ?_⟩
      rw [h', List.length_replicate]
      cases d
      · left; rfl
      · right; rfl
    · exfalso
      have := h 0 (by simp) (n + 1) (by rw [h']; simp)
      rw [h'] at this
      simp at this

theorem existsUnique_conj (hb : HB) (hr : HR) :
    (∀ s : Seq, ∃! u : Seq, u ∈ ({[], [false], [true], [true, false]} : Set Seq) ∧
      ∃ g ∈ F, ys s = g⁻¹ * ys u * g) ∧
    ys '' {s | ¬ IsConst s} = {h | h ∈ Set.range ys ∧ ∃ g ∈ F, h = g⁻¹ * ys [true, false] * g} := by
  have h3 : ∀ s t t', xFin s t = some t' → ys t * xs s = xs s * ys t' :=
    fun _ _ _ h => rel3_grp hr h
  -- every `y_s` is conjugate to one of the four
  have hex : ∀ s, ∃ u ∈ Reps, CJ ys F u s ∧ (IsConst s → u ≠ [true, false]) := by
    intro s
    by_cases hs : IsConst s
    · rcases const_cases hs with rfl | ⟨n, rfl | rfl⟩
      · exact ⟨[], by simp [Reps], CJ.refl _, by simp⟩
      · exact ⟨[false], by simp [Reps], cj_0n xs h3 xs_mem_F n, by simp⟩
      · exact ⟨[true], by simp [Reps], cj_1n xs h3 xs_mem_F n, by simp⟩
    · exact ⟨[true, false], by simp [Reps], cj_nonconst xs h3 xs_mem_F hs, fun h => absurd h hs⟩
  refine ⟨fun s => ?_, ?_⟩
  · obtain ⟨u, hu, hcj, -⟩ := hex s
    refine ⟨u, ⟨hu, hcj⟩, fun v ⟨hv, hcjv⟩ => ?_⟩
    exact (uniq_rep hb hu hv (CJ.trans hcj (CJ.symm hcjv))).symm
  · ext h
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, rfl⟩, cj_nonconst xs h3 xs_mem_F hs⟩
    · rintro ⟨⟨s, rfl⟩, g, hg, e⟩
      refine ⟨s, fun hs => ?_, rfl⟩
      obtain ⟨u, hu, hcj, hne⟩ := hex s
      exact hne hs (uniq_rep hb hu (by simp [Reps]) (CJ.trans hcj (CJ.symm ⟨g, hg, e⟩)))

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
    (∀ s : Seq, ∃! u : Seq, u ∈ ({[], [false], [true], [true, false]} : Set Seq) ∧
      ∃ g ∈ F, ys s = g⁻¹ * ys u * g) ∧
    ys '' {s | ¬ IsConst s} = {h | h ∈ Set.range ys ∧ ∃ g ∈ F, h = g⁻¹ * ys [true, false] * g} :=
  existsUnique_conj bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R.1
    bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R.2
end
