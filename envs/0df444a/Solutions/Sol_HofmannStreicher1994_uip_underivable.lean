-- Prove2me | solution 1 for HofmannStreicher1994.uip_underivable
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T21:03:56.178384+00:00
-- url     : https://prove2.me/submissions/8baf09e6-49d4-4800-82c1-20119033ae7b

import Definitions.Def_HofmannStreicher1994_Syntax



set_option autoImplicit false



/-! ## ValTest.lean -/

open Classical

namespace HofmannStreicher1994

set_option genSizeOf false in
inductive Tree (D : Nat → Type) : Type where
  | dflt : Tree D
  | nat : Nat → Tree D
  | uCode : Tree D
  | elObj : Tree D
  | elMor : Bool → Tree D
  | idObj : Tree D → Tree D
  | pairObj : Tree D → Tree D → Tree D
  | pairMor : Tree D → Tree D → Tree D → Tree D → Tree D
  | piObj (k : Nat) : (D k → Tree D) → (D k → D k → D k → Tree D) → Tree D
  | piMor (k : Nat) : (D k → D k → D k → Tree D) → Tree D

def DFam : Nat → (Nat → Type)
  | 0 => fun _ => PEmpty
  | n + 1 => fun k => if k = n then Tree (DFam n) else DFam n k

abbrev D (n : Nat) : Type := Tree (DFam n)

abbrev Val : Type := Tree D

theorem dFam_eq_D : ∀ (n k : Nat), k < n → DFam n k = D k
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
    unfold DFam
    by_cases heq : k = n
    · subst heq; simp [D]
    · simp [heq]
      exact dFam_eq_D n k (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) heq)

def ofD (n : Nat) : D n → Val
  | .dflt => .dflt
  | .nat m => .nat m
  | .uCode => .uCode
  | .elObj => .elObj
  | .elMor b => .elMor b
  | .idObj p => .idObj (ofD n p)
  | .pairObj x y => .pairObj (ofD n x) (ofD n y)
  | .pairMor x₁ x₂ p q =>
    .pairMor (ofD n x₁) (ofD n x₂) (ofD n p) (ofD n q)
  | .piObj k fo fm =>
    let rfo := fun x => ofD n (fo x)
    let rfm := fun x y p => ofD n (fm x y p)
    if h : k < n then
      .piObj k
        (fun w => rfo (cast (dFam_eq_D n k h).symm w))
        (fun wx wy wp => rfm (cast (dFam_eq_D n k h).symm wx)
          (cast (dFam_eq_D n k h).symm wy) (cast (dFam_eq_D n k h).symm wp))
    else
      .dflt
  | .piMor k η =>
    let rη := fun x y p => ofD n (η x y p)
    if h : k < n then
      .piMor k (fun wx wy wp => rη (cast (dFam_eq_D n k h).symm wx)
        (cast (dFam_eq_D n k h).symm wy) (cast (dFam_eq_D n k h).symm wp))
    else
      .dflt

def toD (n : Nat) : Val → D n
  | .dflt => .dflt
  | .nat m => .nat m
  | .uCode => .uCode
  | .elObj => .elObj
  | .elMor b => .elMor b
  | .idObj p => .idObj (toD n p)
  | .pairObj x y => .pairObj (toD n x) (toD n y)
  | .pairMor x₁ x₂ p q =>
    .pairMor (toD n x₁) (toD n x₂) (toD n p) (toD n q)
  | .piObj k fo fm =>
    let rfo := fun x => toD n (fo x)
    let rfm := fun x y p => toD n (fm x y p)
    if h : k < n then
      .piObj k
        (fun w => rfo (cast (dFam_eq_D n k h) w))
        (fun wx wy wp => rfm (cast (dFam_eq_D n k h) wx)
          (cast (dFam_eq_D n k h) wy) (cast (dFam_eq_D n k h) wp))
    else
      .dflt
  | .piMor k η =>
    let rη := fun x y p => toD n (η x y p)
    if h : k < n then
      .piMor k (fun wx wy wp => rη (cast (dFam_eq_D n k h) wx)
        (cast (dFam_eq_D n k h) wy) (cast (dFam_eq_D n k h) wp))
    else
      .dflt

def RankLt (n : Nat) : Val → Prop
  | .dflt => True
  | .nat _ => True
  | .uCode => True
  | .elObj => True
  | .elMor _ => True
  | .idObj p => RankLt n p
  | .pairObj x y => RankLt n x ∧ RankLt n y
  | .pairMor x₁ x₂ p q => RankLt n x₁ ∧ RankLt n x₂ ∧ RankLt n p ∧ RankLt n q
  | .piObj k fo fm =>
    k < n ∧ (∀ w, RankLt n (fo w)) ∧ (∀ wx wy wp, RankLt n (fm wx wy wp))
  | .piMor k η =>
    k < n ∧ (∀ wx wy wp, RankLt n (η wx wy wp))

theorem RankLt_mono {m n : Nat} (hmn : m ≤ n) (v : Val) (h : RankLt m v) : RankLt n v := by
  induction v with
  | dflt => trivial
  | nat _ => trivial
  | uCode => trivial
  | elObj => trivial
  | elMor _ => trivial
  | idObj p ih => exact ih h
  | pairObj x y ihx ihy => exact ⟨ihx h.1, ihy h.2⟩
  | pairMor x₁ x₂ p q ih1 ih2 ihp ihq =>
    exact ⟨ih1 h.1, ih2 h.2.1, ihp h.2.2.1, ihq h.2.2.2⟩
  | piObj k fo fm ihfo ihfm =>
    rcases h with ⟨hk, hfo, hfm⟩
    exact ⟨Nat.lt_of_lt_of_le hk hmn, fun w => ihfo w (hfo w),
      fun wx wy wp => ihfm wx wy wp (hfm wx wy wp)⟩
  | piMor k η ihη =>
    rcases h with ⟨hk, hη⟩
    exact ⟨Nat.lt_of_lt_of_le hk hmn, fun wx wy wp => ihη wx wy wp (hη wx wy wp)⟩

theorem ofD_toD (n : Nat) (v : Val) (h : RankLt n v) :
    ofD n (toD n v) = v := by
  induction v with
  | dflt => rfl
  | nat _ => rfl
  | uCode => rfl
  | elObj => rfl
  | elMor _ => rfl
  | idObj p ih =>
    simp [toD, ofD, ih h]
  | pairObj x y ihx ihy =>
    simp [toD, ofD, ihx h.1, ihy h.2]
  | pairMor x₁ x₂ p q ih1 ih2 ihp ihq =>
    simp [toD, ofD, ih1 h.1, ih2 h.2.1, ihp h.2.2.1, ihq h.2.2.2]
  | piObj k fo fm ihfo ihfm =>
    rcases h with ⟨hk, hfo, hfm⟩
    simp [toD, ofD, hk]
    constructor
    · funext w
      simpa using ihfo w (hfo w)
    · funext wx wy wp
      simpa using ihfm wx wy wp (hfm wx wy wp)
  | piMor k η ihη =>
    rcases h with ⟨hk, hη⟩
    simp [toD, ofD, hk]
    funext wx wy wp
    simpa using ihη wx wy wp (hη wx wy wp)

attribute [irreducible] ofD toD

def idVal : Val → Val
  | .dflt => .dflt
  | .nat m => .nat m
  | .uCode => .uCode
  | .elObj => .elMor false
  | .elMor b => .elMor b
  | .idObj p => .idObj p
  | .pairObj x y => .pairMor x x (idVal x) (idVal y)
  | .pairMor x₁ x₂ p q => .pairMor x₁ x₂ p q
  | .piObj k _ fm => .piMor k fm
  | .piMor k η => .piMor k η

theorem RankLt_idVal {n : Nat} (v : Val) (h : RankLt n v) : RankLt n (idVal v) := by
  induction v with
  | dflt => trivial
  | nat _ => trivial
  | uCode => trivial
  | elObj => trivial
  | elMor _ => trivial
  | idObj p _ => exact h
  | pairObj x y ihx ihy => exact ⟨h.1, h.1, ihx h.1, ihy h.2⟩
  | pairMor x₁ x₂ p q _ _ _ _ => exact h
  | piObj k fo fm _ _ =>
    rcases h with ⟨hk, _, hfm⟩
    exact ⟨hk, hfm⟩
  | piMor k η _ => exact h

-- Id helpers
def unId : Val → Val
  | .idObj p => p
  | _ => .dflt

@[simp] theorem unId_idObj (p : Val) : unId (.idObj p) = p := rfl

-- Sigma helpers
def sigFst : Val → Val
  | .pairObj x _ => x
  | _ => .dflt

def sigSnd : Val → Val
  | .pairObj _ y => y
  | _ => .dflt

def sigMorX1 : Val → Val
  | .pairMor x₁ _ _ _ => x₁
  | _ => .dflt

def sigMorX2 : Val → Val
  | .pairMor _ x₂ _ _ => x₂
  | _ => .dflt

def sigMorP : Val → Val
  | .pairMor _ _ p _ => p
  | _ => .dflt

def sigMorQ : Val → Val
  | .pairMor _ _ _ q => q
  | _ => .dflt

@[simp] theorem sigFst_pairObj (x y : Val) : sigFst (.pairObj x y) = x := rfl
@[simp] theorem sigSnd_pairObj (x y : Val) : sigSnd (.pairObj x y) = y := rfl
@[simp] theorem sigMorX1_pairMor (x₁ x₂ p q : Val) : sigMorX1 (.pairMor x₁ x₂ p q) = x₁ := rfl
@[simp] theorem sigMorX2_pairMor (x₁ x₂ p q : Val) : sigMorX2 (.pairMor x₁ x₂ p q) = x₂ := rfl
@[simp] theorem sigMorP_pairMor (x₁ x₂ p q : Val) : sigMorP (.pairMor x₁ x₂ p q) = p := rfl
@[simp] theorem sigMorQ_pairMor (x₁ x₂ p q : Val) : sigMorQ (.pairMor x₁ x₂ p q) = q := rfl

-- Pi helpers
noncomputable def mkPiObj (k : Nat) (P_obj : Val → Prop) (P_mor : Val → Val → Val → Prop)
    (fo : Val → Val) (fm : Val → Val → Val → Val) : Val :=
  .piObj k
    (fun w => if P_obj (ofD k w) then fo (ofD k w) else .dflt)
    (fun wx wy wp => if P_mor (ofD k wx) (ofD k wy) (ofD k wp) then
      fm (ofD k wx) (ofD k wy) (ofD k wp) else .dflt)

def piAppObj : Val → Val → Val
  | .piObj k fo _, x => fo (toD k x)
  | _, _ => .dflt

def piAppMor : Val → Val → Val → Val → Val
  | .piObj k _ fm, x, y, p => fm (toD k x) (toD k y) (toD k p)
  | _, _, _, _ => .dflt

noncomputable def mkPiMor (k : Nat) (P_mor : Val → Val → Val → Prop) (η : Val → Val → Val → Val) : Val :=
  .piMor k (fun wx wy wp => if P_mor (ofD k wx) (ofD k wy) (ofD k wp) then
    η (ofD k wx) (ofD k wy) (ofD k wp) else .dflt)

def piMorAt : Val → Val → Val → Val → Val
  | .piMor k η, x, y, p => η (toD k x) (toD k y) (toD k p)
  | _, _, _, _ => .dflt

theorem piAppObj_mkPiObj {k : Nat} {P_obj : Val → Prop} {P_mor : Val → Val → Val → Prop}
    {fo : Val → Val} {fm : Val → Val → Val → Val} {x : Val}
    (hx_rk : RankLt k x) (hx : P_obj x) :
    piAppObj (mkPiObj k P_obj P_mor fo fm) x = fo x := by
  simp [mkPiObj, piAppObj, ofD_toD k x hx_rk, hx]

theorem piAppMor_mkPiObj {k : Nat} {P_obj : Val → Prop} {P_mor : Val → Val → Val → Prop}
    {fo : Val → Val} {fm : Val → Val → Val → Val} {x y p : Val}
    (hx_rk : RankLt k x) (hy_rk : RankLt k y) (hp_rk : RankLt k p) (hp : P_mor x y p) :
    piAppMor (mkPiObj k P_obj P_mor fo fm) x y p = fm x y p := by
  simp [mkPiObj, piAppMor, ofD_toD k x hx_rk, ofD_toD k y hy_rk, ofD_toD k p hp_rk, hp]

theorem piMorAt_mkPiMor {k : Nat} {P_mor : Val → Val → Val → Prop} {η : Val → Val → Val → Val}
    {x y p : Val}
    (hx_rk : RankLt k x) (hy_rk : RankLt k y) (hp_rk : RankLt k p) (hp : P_mor x y p) :
    piMorAt (mkPiMor k P_mor η) x y p = η x y p := by
  simp [mkPiMor, piMorAt, ofD_toD k x hx_rk, ofD_toD k y hy_rk, ofD_toD k p hp_rk, hp]

@[simp] theorem idVal_mkPiObj (k : Nat) (P_obj : Val → Prop) (P_mor : Val → Val → Val → Prop)
    (fo : Val → Val) (fm : Val → Val → Val → Val) :
    idVal (mkPiObj k P_obj P_mor fo fm) = mkPiMor k P_mor fm := rfl

@[simp] theorem piMorAt_idVal (f x y p : Val) :
    (∀ k fo fm, f = .piObj k fo fm → piMorAt (idVal f) x y p = piAppMor f x y p) := by
  intro k fo fm hf; subst hf; rfl

theorem RankLt_mkPiObj {k n : Nat} {P_obj : Val → Prop} {P_mor : Val → Val → Val → Prop}
    {fo : Val → Val} {fm : Val → Val → Val → Val}
    (hk : k < n)
    (hfo : ∀ x, P_obj x → RankLt n (fo x))
    (hfm : ∀ x y p, P_mor x y p → RankLt n (fm x y p)) :
    RankLt n (mkPiObj k P_obj P_mor fo fm) := by
  refine ⟨hk, fun w => ?_, fun wx wy wp => ?_⟩
  · by_cases h : P_obj (ofD k w)
    · simp [h, hfo _ h]
    · simp [h, RankLt]
  · by_cases h : P_mor (ofD k wx) (ofD k wy) (ofD k wp)
    · simp [h, hfm _ _ _ h]
    · simp [h, RankLt]

theorem RankLt_mkPiMor {k n : Nat} {P_mor : Val → Val → Val → Prop} {η : Val → Val → Val → Val}
    (hk : k < n) (hη : ∀ x y p, P_mor x y p → RankLt n (η x y p)) :
    RankLt n (mkPiMor k P_mor η) := by
  refine ⟨hk, fun wx wy wp => ?_⟩
  by_cases h : P_mor (ofD k wx) (ofD k wy) (ofD k wp)
  · simp [h, hη _ _ _ h]
  · simp [h, RankLt]

theorem mkPiObj_ext {k : Nat} {P_obj P_obj' : Val → Prop} {P_mor P_mor' : Val → Val → Val → Prop}
    {fo fo' : Val → Val} {fm fm' : Val → Val → Val → Val}
    (hPo : ∀ x, (P_obj x ↔ P_obj' x))
    (hPm : ∀ x y p, (P_mor x y p ↔ P_mor' x y p))
    (hfo : ∀ x, P_obj x → fo x = fo' x)
    (hfm : ∀ x y p, P_mor x y p → fm x y p = fm' x y p) :
    mkPiObj k P_obj P_mor fo fm = mkPiObj k P_obj' P_mor' fo' fm' := by
  unfold mkPiObj
  congr 1
  · funext w
    by_cases h : P_obj (ofD k w)
    · have h' : P_obj' (ofD k w) := (hPo _).mp h
      simp [h, h', hfo _ h]
    · have h' : ¬ P_obj' (ofD k w) := fun hc => h ((hPo _).mpr hc)
      simp [h, h']
  · funext wx wy wp
    by_cases h : P_mor (ofD k wx) (ofD k wy) (ofD k wp)
    · have h' : P_mor' (ofD k wx) (ofD k wy) (ofD k wp) := (hPm _ _ _).mp h
      simp [h, h', hfm _ _ _ h]
    · have h' : ¬ P_mor' (ofD k wx) (ofD k wy) (ofD k wp) := fun hc => h ((hPm _ _ _).mpr hc)
      simp [h, h']

theorem mkPiMor_ext {k : Nat} {P_mor P_mor' : Val → Val → Val → Prop}
    {η η' : Val → Val → Val → Val}
    (hPm : ∀ x y p, (P_mor x y p ↔ P_mor' x y p))
    (hη : ∀ x y p, P_mor x y p → η x y p = η' x y p) :
    mkPiMor k P_mor η = mkPiMor k P_mor' η' := by
  unfold mkPiMor
  congr 1
  funext wx wy wp
  by_cases h : P_mor (ofD k wx) (ofD k wy) (ofD k wp)
  · have h' : P_mor' (ofD k wx) (ofD k wy) (ofD k wp) := (hPm _ _ _).mp h
    simp [h, h', hη _ _ _ h]
  · have h' : ¬ P_mor' (ofD k wx) (ofD k wy) (ofD k wp) := fun hc => h ((hPm _ _ _).mpr hc)
    simp [h, h']

end HofmannStreicher1994

/-! ## SyntaxScope.lean -/

namespace HofmannStreicher1994

def Scoped (k : Nat) : Expr → Prop
  | .var n => n < k
  | .pi A B | .sigma A B | .lam A B => Scoped k A ∧ Scoped (k + 1) B
  | .identity A a b => Scoped k A ∧ Scoped k a ∧ Scoped k b
  | .nat | .universe | .zero => True
  | .el a | .succ a => Scoped k a
  | .app A B f a => Scoped k A ∧ Scoped (k + 1) B ∧ Scoped k f ∧ Scoped k a
  | .pair A B a b => Scoped k A ∧ Scoped (k + 1) B ∧ Scoped k a ∧ Scoped k b
  | .sigmaRec A B C d p =>
      Scoped k A ∧ Scoped (k + 1) B ∧ Scoped (k + 1) C ∧ Scoped (k + 2) d ∧ Scoped k p
  | .refl A a => Scoped k A ∧ Scoped k a
  | .idRec A C d a b p =>
      Scoped k A ∧ Scoped (k + 3) C ∧ Scoped (k + 1) d ∧
      Scoped k a ∧ Scoped k b ∧ Scoped k p
  | .natRec C z s n => Scoped (k + 1) C ∧ Scoped k z ∧ Scoped (k + 2) s ∧ Scoped k n

def IsTm : Expr → Prop
  | .var _ | .lam _ _ | .app _ _ _ _ | .pair _ _ _ _ | .sigmaRec _ _ _ _ _
    | .refl _ _ | .idRec _ _ _ _ _ _ | .zero | .succ _ | .natRec _ _ _ _ => True
  | _ => False

def IsTy : Expr → Prop
  | .pi _ _ | .sigma _ _ | .identity _ _ _ | .nat | .universe | .el _ => True
  | _ => False

def RenScope (k l : Nat) (ρ : Nat → Nat) : Prop := ∀ n, n < k → ρ n < l

theorem RenScope.lift {k l : Nat} {ρ : Nat → Nat} (h : RenScope k l ρ) :
    RenScope (k + 1) (l + 1) (liftRenaming ρ) := by
  intro n hn
  cases n with
  | zero => exact Nat.zero_lt_succ _
  | succ n => exact Nat.succ_lt_succ (h n (Nat.lt_of_succ_lt_succ hn))

theorem Scoped.rename {e : Expr} {k l : Nat} {ρ : Nat → Nat}
    (he : Scoped k e) (hρ : RenScope k l ρ) : Scoped l (rename ρ e) := by
  induction e generalizing k l ρ <;> simp_all [Scoped, HofmannStreicher1994.rename]
  all_goals grind only [→ RenScope.lift, RenScope]

theorem Scoped.weaken {e : Expr} {k : Nat} (h : Scoped k e) :
    Scoped (k + 1) (weaken e) := h.rename (fun _ hn => Nat.succ_lt_succ hn)

theorem IsTm.rename {e : Expr} {ρ : Nat → Nat} (h : IsTm e) :
    IsTm (rename ρ e) := by
  cases e <;> simp_all [IsTm, HofmannStreicher1994.rename]

theorem IsTy.rename {e : Expr} {ρ : Nat → Nat} (h : IsTy e) :
    IsTy (rename ρ e) := by
  cases e <;> simp_all [IsTy, HofmannStreicher1994.rename]

theorem IsTy.substitute {e : Expr} {σ : Nat → Expr} (h : IsTy e) :
    IsTy (substitute σ e) := by
  cases e <;> simp_all [IsTy, HofmannStreicher1994.substitute]

def SubScope (k l : Nat) (σ : Nat → Expr) : Prop :=
  ∀ n, n < k → Scoped l (σ n)

theorem SubScope.lift {k l : Nat} {σ : Nat → Expr} (h : SubScope k l σ) :
    SubScope (k + 1) (l + 1) (liftSubstitution σ) := by
  intro n hn
  cases n with
  | zero => exact Nat.zero_lt_succ _
  | succ n => exact (h n (Nat.lt_of_succ_lt_succ hn)).weaken

theorem Scoped.substitute {e : Expr} {k l : Nat} {σ : Nat → Expr}
    (he : Scoped k e) (hσ : SubScope k l σ) : Scoped l (substitute σ e) := by
  induction e generalizing k l σ <;> simp_all [Scoped, HofmannStreicher1994.substitute]
  all_goals grind only [→ SubScope.lift, SubScope]

def SubAgree (k : Nat) (σ τ : Nat → Expr) : Prop := ∀ n, n < k → σ n = τ n

theorem SubAgree.lift {k : Nat} {σ τ : Nat → Expr} (h : SubAgree k σ τ) :
    SubAgree (k + 1) (liftSubstitution σ) (liftSubstitution τ) := by
  intro n hn
  cases n with
  | zero => rfl
  | succ n => exact congrArg weaken (h n (Nat.lt_of_succ_lt_succ hn))

theorem Scoped.substitute_congr {e : Expr} {k : Nat} {σ τ : Nat → Expr}
    (he : Scoped k e) (hστ : SubAgree k σ τ) :
    HofmannStreicher1994.substitute σ e = HofmannStreicher1994.substitute τ e := by
  induction e generalizing k σ τ <;> simp_all [Scoped, HofmannStreicher1994.substitute]
  all_goals grind only [→ SubAgree.lift, SubAgree]

def truncSub (k : Nat) (σ : Nat → Expr) : Nat → Expr :=
  fun n => if n < k then σ n else .zero

theorem Scoped.truncSub {e : Expr} {k : Nat} {σ : Nat → Expr} (he : Scoped k e) :
    HofmannStreicher1994.substitute (truncSub k σ) e =
      HofmannStreicher1994.substitute σ e :=
  he.substitute_congr (fun _ hn => if_pos hn)

theorem IsTm.substitute {e : Expr} {k : Nat} {σ : Nat → Expr}
    (he : IsTm e) (hs : Scoped k e) (hσ : ∀ n, n < k → IsTm (σ n)) :
    IsTm (substitute σ e) := by
  cases e <;> simp_all [IsTm, Scoped, HofmannStreicher1994.substitute]

theorem truncSub_isTm {k : Nat} {σ : Nat → Expr} (hσ : ∀ n, n < k → IsTm (σ n)) :
    ∀ n, IsTm (truncSub k σ n) := by
  intro n
  by_cases hn : n < k
  · simpa only [truncSub, if_pos hn] using hσ n hn
  · simp [truncSub, hn, IsTm]

end HofmannStreicher1994

/-! ## JudgmentScope.lean -/

namespace HofmannStreicher1994

theorem scoped_instantiate {B a : Expr} {k : Nat}
    (hB : Scoped (k + 1) B) (ha : Scoped k a) : Scoped k (instantiate B a) := by
  apply hB.substitute
  intro n hn
  match n with
  | 0 => exact ha
  | n + 1 => exact Nat.lt_of_succ_lt_succ hn

theorem scoped_instantiate₂ {C a b : Expr} {k : Nat}
    (hC : Scoped (k + 2) C) (ha : Scoped k a) (hb : Scoped k b) :
    Scoped k (instantiate₂ C a b) := by
  apply hC.substitute
  intro n hn
  match n with
  | 0 => exact hb
  | 1 => exact ha
  | n + 2 => exact Nat.lt_of_add_lt_add_right hn

theorem scoped_instantiate₃ {C a b p : Expr} {k : Nat}
    (hC : Scoped (k + 3) C) (ha : Scoped k a) (hb : Scoped k b) (hp : Scoped k p) :
    Scoped k (instantiate₃ C a b p) := by
  apply hC.substitute
  intro n hn
  match n with
  | 0 => exact hp
  | 1 => exact hb
  | 2 => exact ha
  | n + 3 => exact Nat.lt_of_add_lt_add_right hn

def CtxScoped : Context → Prop
  | [] => True
  | A :: Γ => CtxScoped Γ ∧ Scoped Γ.length A

def GoodType (k : Nat) (A : Expr) : Prop := Scoped k A ∧ IsTy A
def GoodTerm (k : Nat) (t : Expr) : Prop := Scoped k t ∧ IsTm t
def GoodSub (k l : Nat) (σ : Nat → Expr) : Prop :=
  ∀ n, n < k → GoodTerm l (σ n)

theorem GoodType.subst {k l : Nat} {A : Expr} {σ : Nat → Expr}
    (hA : GoodType k A) (hσ : GoodSub k l σ) : GoodType l (substitute σ A) :=
  ⟨hA.1.substitute (fun n hn => (hσ n hn).1), hA.2.substitute⟩

theorem GoodTerm.subst {k l : Nat} {t : Expr} {σ : Nat → Expr}
    (ht : GoodTerm k t) (hσ : GoodSub k l σ) : GoodTerm l (substitute σ t) :=
  ⟨ht.1.substitute (fun n hn => (hσ n hn).1),
    ht.2.substitute ht.1 (fun n hn => (hσ n hn).2)⟩

theorem GoodTerm.instantiate {k : Nat} {t a : Expr}
    (ht : GoodTerm (k + 1) t) (ha : GoodTerm k a) : GoodTerm k (instantiate t a) := by
  apply ht.subst
  intro n hn
  match n with
  | 0 => exact ha
  | n + 1 => exact ⟨Nat.lt_of_succ_lt_succ hn, trivial⟩

theorem GoodTerm.instantiate₂ {k : Nat} {t a b : Expr}
    (ht : GoodTerm (k + 2) t) (ha : GoodTerm k a) (hb : GoodTerm k b) :
    GoodTerm k (instantiate₂ t a b) := by
  apply ht.subst
  intro n hn
  match n with
  | 0 => exact hb
  | 1 => exact ha
  | n + 2 => exact ⟨Nat.lt_of_add_lt_add_right hn, trivial⟩

theorem ContextEq.length_eq {Γ Δ : Context} : ContextEq Γ Δ → Γ.length = Δ.length
  | .nil => rfl
  | .cons h _ => congrArg Nat.succ (ContextEq.length_eq h)

mutual
  theorem TypeWf.metadata {Γ : Context} {A : Expr} : TypeWf Γ A → GoodType Γ.length A
    | .pi hA hB => ⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1⟩, trivial⟩
    | .sigma hA hB => ⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1⟩, trivial⟩
    | .identity hA ha hb =>
      ⟨⟨(TypeWf.metadata hA).1, (TermWf.metadata ha).1, (TermWf.metadata hb).1⟩, trivial⟩
    | .nat _ => ⟨trivial, trivial⟩
    | .universe _ => ⟨trivial, trivial⟩
    | .el ha => ⟨(TermWf.metadata ha).1, trivial⟩
    | .subst hA hσ => (TypeWf.metadata hA).subst (SubstitutionWf.metadata hσ)
    | .context hA hΓ => hΓ.length_eq ▸ TypeWf.metadata hA

  theorem TermWf.metadata {Γ : Context} {t A : Expr} : TermWf Γ t A → GoodTerm Γ.length t
    | .var _ hn => ⟨(List.getElem?_eq_some_iff.mp hn).1, trivial⟩
    | .lam hA _ hb => ⟨⟨(TypeWf.metadata hA).1, (TermWf.metadata hb).1⟩, trivial⟩
    | .app hA hB hf ha =>
      ⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1,
        (TermWf.metadata hf).1, (TermWf.metadata ha).1⟩, trivial⟩
    | .pair hA hB ha hb =>
      ⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1,
        (TermWf.metadata ha).1, (TermWf.metadata hb).1⟩, trivial⟩
    | .sigmaRec hA hB hC hd hp =>
      ⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1, (TypeWf.metadata hC).1,
        (TermWf.metadata hd).1, (TermWf.metadata hp).1⟩, trivial⟩
    | .refl hA ha => ⟨⟨(TypeWf.metadata hA).1, (TermWf.metadata ha).1⟩, trivial⟩
    | .idRec hA hC hd ha hb hp =>
      ⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hC).1, (TermWf.metadata hd).1,
        (TermWf.metadata ha).1, (TermWf.metadata hb).1, (TermWf.metadata hp).1⟩, trivial⟩
    | .zero _ => ⟨trivial, trivial⟩
    | .succ hn => ⟨(TermWf.metadata hn).1, trivial⟩
    | .natRec hC hz hs hn =>
      ⟨⟨(TypeWf.metadata hC).1, (TermWf.metadata hz).1,
        (TermWf.metadata hs).1, (TermWf.metadata hn).1⟩, trivial⟩
    | .conv ha _ => TermWf.metadata ha
    | .subst ha hσ => (TermWf.metadata ha).subst (SubstitutionWf.metadata hσ)
    | .context ha hΓ => hΓ.length_eq ▸ TermWf.metadata ha

  theorem TypeEq.metadata {Γ : Context} {A B : Expr} :
      TypeEq Γ A B → GoodType Γ.length A ∧ GoodType Γ.length B
    | .refl hA => ⟨TypeWf.metadata hA, TypeWf.metadata hA⟩
    | .symm h => ⟨(TypeEq.metadata h).2, (TypeEq.metadata h).1⟩
    | .trans h₁ h₂ => ⟨(TypeEq.metadata h₁).1, (TypeEq.metadata h₂).2⟩
    | .pi hA hB =>
      ⟨⟨⟨(TypeEq.metadata hA).1.1, (TypeEq.metadata hB).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TypeEq.metadata hB).2.1⟩, trivial⟩⟩
    | .sigma hA hB =>
      ⟨⟨⟨(TypeEq.metadata hA).1.1, (TypeEq.metadata hB).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TypeEq.metadata hB).2.1⟩, trivial⟩⟩
    | .identity hA ha hb =>
      ⟨⟨⟨(TypeEq.metadata hA).1.1, (TermEq.metadata ha).1.1, (TermEq.metadata hb).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TermEq.metadata ha).2.1, (TermEq.metadata hb).2.1⟩, trivial⟩⟩
    | .el h => ⟨⟨(TermEq.metadata h).1.1, trivial⟩, ⟨(TermEq.metadata h).2.1, trivial⟩⟩
    | .subst h hσ => ⟨(TypeEq.metadata h).1.subst (SubstitutionWf.metadata hσ),
        (TypeEq.metadata h).2.subst (SubstitutionWf.metadata hσ)⟩
    | .substEq hA (.mk hσ hτ _) =>
      ⟨(TypeWf.metadata hA).subst (SubstitutionWf.metadata hσ),
        (TypeWf.metadata hA).subst (SubstitutionWf.metadata hτ)⟩
    | .context h hΓ => hΓ.length_eq ▸ TypeEq.metadata h

  theorem TermEq.metadata {Γ : Context} {a b A : Expr} :
      TermEq Γ a b A → GoodTerm Γ.length a ∧ GoodTerm Γ.length b
    | @TermEq.etaPi Γ A B f hA hB hf => by
      have hρ : RenScope Γ.length (Γ.length + 1) Nat.succ := fun _ hn => Nat.succ_lt_succ hn
      exact ⟨⟨⟨(TypeWf.metadata hA).1,
        (TypeWf.metadata hA).1.weaken, (TypeWf.metadata hB).1.rename hρ.lift,
        (TermWf.metadata hf).1.weaken, Nat.zero_lt_succ _⟩, trivial⟩, TermWf.metadata hf⟩
    | .refl h => by exact ⟨TermWf.metadata h, TermWf.metadata h⟩
    | .symm h => by exact ⟨(TermEq.metadata h).2, (TermEq.metadata h).1⟩
    | .trans h₁ h₂ => by exact ⟨(TermEq.metadata h₁).1, (TermEq.metadata h₂).2⟩
    | .conv h _ => by exact TermEq.metadata h
    | .lam hA _ hb => by
      exact ⟨⟨⟨(TypeEq.metadata hA).1.1, (TermEq.metadata hb).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TermEq.metadata hb).2.1⟩, trivial⟩⟩
    | .app hA hB hf ha => by
      exact ⟨⟨⟨(TypeEq.metadata hA).1.1, (TypeEq.metadata hB).1.1,
        (TermEq.metadata hf).1.1, (TermEq.metadata ha).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TypeEq.metadata hB).2.1,
        (TermEq.metadata hf).2.1, (TermEq.metadata ha).2.1⟩, trivial⟩⟩
    | .pair hA hB ha hb => by
      exact ⟨⟨⟨(TypeEq.metadata hA).1.1, (TypeEq.metadata hB).1.1,
        (TermEq.metadata ha).1.1, (TermEq.metadata hb).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TypeEq.metadata hB).2.1,
        (TermEq.metadata ha).2.1, (TermEq.metadata hb).2.1⟩, trivial⟩⟩
    | .sigmaRec hA hB hC hd hp => by
      exact ⟨⟨⟨(TypeEq.metadata hA).1.1, (TypeEq.metadata hB).1.1,
        (TypeEq.metadata hC).1.1, (TermEq.metadata hd).1.1, (TermEq.metadata hp).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TypeEq.metadata hB).2.1,
        (TypeEq.metadata hC).2.1, (TermEq.metadata hd).2.1, (TermEq.metadata hp).2.1⟩, trivial⟩⟩
    | .reflCongr hA ha => by
      exact ⟨⟨⟨(TypeEq.metadata hA).1.1, (TermEq.metadata ha).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TermEq.metadata ha).2.1⟩, trivial⟩⟩
    | .idRec hA hC hd ha hb hp => by
      exact ⟨⟨⟨(TypeEq.metadata hA).1.1, (TypeEq.metadata hC).1.1,
        (TermEq.metadata hd).1.1, (TermEq.metadata ha).1.1, (TermEq.metadata hb).1.1,
        (TermEq.metadata hp).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TypeEq.metadata hC).2.1,
        (TermEq.metadata hd).2.1, (TermEq.metadata ha).2.1, (TermEq.metadata hb).2.1,
        (TermEq.metadata hp).2.1⟩, trivial⟩⟩
    | .succ h => by exact ⟨⟨(TermEq.metadata h).1.1, trivial⟩, ⟨(TermEq.metadata h).2.1, trivial⟩⟩
    | .natRec hC hz hs hn => by
      exact ⟨⟨⟨(TypeEq.metadata hC).1.1, (TermEq.metadata hz).1.1,
        (TermEq.metadata hs).1.1, (TermEq.metadata hn).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hC).2.1, (TermEq.metadata hz).2.1,
        (TermEq.metadata hs).2.1, (TermEq.metadata hn).2.1⟩, trivial⟩⟩
    | .betaPi hA hB hb ha => by
      exact ⟨⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1,
        ⟨(TypeWf.metadata hA).1, (TermWf.metadata hb).1⟩, (TermWf.metadata ha).1⟩, trivial⟩,
        (TermWf.metadata hb).instantiate (TermWf.metadata ha)⟩
    | .betaSigma hA hB hC hd ha hb => by
      exact ⟨⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1, (TypeWf.metadata hC).1,
        (TermWf.metadata hd).1, (TypeWf.metadata hA).1, (TypeWf.metadata hB).1,
        (TermWf.metadata ha).1, (TermWf.metadata hb).1⟩, trivial⟩,
        (TermWf.metadata hd).instantiate₂ (TermWf.metadata ha) (TermWf.metadata hb)⟩
    | .betaId hA hC hd ha => by
      exact ⟨⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hC).1, (TermWf.metadata hd).1,
        (TermWf.metadata ha).1, (TermWf.metadata ha).1,
        (TypeWf.metadata hA).1, (TermWf.metadata ha).1⟩, trivial⟩,
        (TermWf.metadata hd).instantiate (TermWf.metadata ha)⟩
    | .betaNatZero hC hz hs => by
      exact ⟨⟨⟨(TypeWf.metadata hC).1, (TermWf.metadata hz).1,
        (TermWf.metadata hs).1, trivial⟩, trivial⟩, TermWf.metadata hz⟩
    | .betaNatSucc hC hz hs hn => by
      exact ⟨⟨⟨(TypeWf.metadata hC).1, (TermWf.metadata hz).1,
        (TermWf.metadata hs).1, (TermWf.metadata hn).1⟩, trivial⟩,
        (TermWf.metadata hs).instantiate₂ (TermWf.metadata hn)
          ⟨⟨(TypeWf.metadata hC).1, (TermWf.metadata hz).1,
            (TermWf.metadata hs).1, (TermWf.metadata hn).1⟩, trivial⟩⟩
    | .subst h hσ => by exact ⟨(TermEq.metadata h).1.subst (SubstitutionWf.metadata hσ),
        (TermEq.metadata h).2.subst (SubstitutionWf.metadata hσ)⟩
    | .substEq h hστ => by
      cases hστ with
      | mk hσ hτ _ => exact ⟨(TermWf.metadata h).subst (SubstitutionWf.metadata hσ),
          (TermWf.metadata h).subst (SubstitutionWf.metadata hτ)⟩
    | .context h hΓ => by exact hΓ.length_eq ▸ TermEq.metadata h


  theorem SubstitutionWf.metadata {Γ Δ : Context} {σ : Nat → Expr} :
      SubstitutionWf Γ Δ σ → GoodSub Γ.length Δ.length σ
    | .mk _ _ h => fun n hn => TermWf.metadata (h n (Γ[n]) (List.getElem?_eq_getElem hn))
end

theorem ContextWf.scoped {Γ : Context} : ContextWf Γ → CtxScoped Γ
  | .nil => trivial
  | .cons hΓ hA => ⟨ContextWf.scoped hΓ, (TypeWf.metadata hA).1⟩

theorem SubstitutionEq.metadata {Γ Δ : Context} {σ τ : Nat → Expr} :
    SubstitutionEq Γ Δ σ τ → GoodSub Γ.length Δ.length σ ∧ GoodSub Γ.length Δ.length τ
  | .mk hσ hτ _ => ⟨SubstitutionWf.metadata hσ, SubstitutionWf.metadata hτ⟩

end HofmannStreicher1994

/-! ## SemModelRepaired.lean -/

/-!
Experimental raw interpretation for the remaining soundness proof.

This module proves renaming and substitution equations. It does not yet prove
preservation of the typing judgments or all groupoid/functor laws. Compared with
the inherited evaluator, dependent functions carry identity/composition laws,
function morphisms carry naturality laws, and all morphisms are represented in
their target fibers. The original evaluator is retained in SemModel.lean and its
identity-law counterexample is checked in ModelAudit.lean.
-/

open Classical

namespace HofmannStreicher1994.Repaired

abbrev Env : Type := Nat → Val

def consEnv (x : Val) (γ : Env) : Env
  | 0 => x
  | n + 1 => γ n

def idEnv (γ : Env) : Env :=
  fun n => idVal (γ n)

def renEnv (ρ : Nat → Nat) (γ : Env) : Env :=
  fun n => γ (ρ n)

@[simp] theorem consEnv_zero (x : Val) (γ : Env) : consEnv x γ 0 = x := rfl
@[simp] theorem consEnv_succ (x : Val) (γ : Env) (n : Nat) : consEnv x γ (n + 1) = γ n := rfl

@[simp] theorem idEnv_consEnv (x : Val) (γ : Env) :
    idEnv (consEnv x γ) = consEnv (idVal x) (idEnv γ) := by
  funext n; cases n <;> rfl

@[simp] theorem renEnv_consEnv_lift (ρ : Nat → Nat) (x : Val) (γ : Env) :
    renEnv (liftRenaming ρ) (consEnv x γ) = consEnv x (renEnv ρ γ) := by
  funext n; cases n <;> rfl

@[simp] theorem idEnv_renEnv (ρ : Nat → Nat) (γ : Env) :
    idEnv (renEnv ρ γ) = renEnv ρ (idEnv γ) := rfl

@[simp] theorem renEnv_succ_consEnv (x : Val) (γ : Env) :
    renEnv Nat.succ (consEnv x γ) = γ := rfl

structure SemFam where
  lvl : Nat
  Obj : Env → Val → Prop
  Hom : Env → Env → Env → Val → Val → Val → Prop
  comp : Env → Val → Val → Val
  inv : Env → Val → Val
  reindexObj : Env → Env → Env → Val → Val
  reindexMor : Env → Env → Env → Val → Val
  unreindexObj : Env → Env → Env → Val → Val
  unreindexMor : Env → Env → Env → Val → Val

structure SemTm where
  obj : Env → Val
  mor : Env → Env → Env → Val

def dfltFam : SemFam where
  lvl := 0
  Obj _ _ := False
  Hom _ _ _ _ _ _ := False
  comp _ _ _ := .dflt
  inv _ _ := .dflt
  reindexObj _ _ _ _ := .dflt
  reindexMor _ _ _ _ := .dflt
  unreindexObj _ _ _ _ := .dflt
  unreindexMor _ _ _ _ := .dflt

def dfltTm : SemTm where
  obj _ := .dflt
  mor _ _ _ := .dflt

def semUniverse : SemFam where
  lvl := 0
  Obj _ x := x = .uCode
  Hom _ _ _ x y p := x = .uCode ∧ y = .uCode ∧ p = .uCode
  comp _ _ _ := .uCode
  inv _ _ := .uCode
  reindexObj _ _ _ _ := .uCode
  reindexMor _ _ _ _ := .uCode
  unreindexObj _ _ _ _ := .uCode
  unreindexMor _ _ _ _ := .uCode

def elCompVal : Val → Val → Val
  | .elMor b₁, .elMor b₂ => .elMor (xor b₁ b₂)
  | _, _ => .dflt

def semEl : SemFam where
  lvl := 0
  Obj _ x := x = .elObj
  Hom _ _ _ x y p := x = .elObj ∧ y = .elObj ∧ ∃ b : Bool, p = .elMor b
  comp _ p q := elCompVal p q
  inv _ p := p
  reindexObj _ _ _ _ := .elObj
  reindexMor _ _ _ p := p
  unreindexObj _ _ _ _ := .elObj
  unreindexMor _ _ _ p := p

def semNat : SemFam where
  lvl := 0
  Obj _ x := ∃ k : Nat, x = .nat k
  Hom _ _ _ x y p := ∃ k : Nat, x = .nat k ∧ y = .nat k ∧ p = .nat k
  comp _ p _ := p
  inv _ p := p
  reindexObj _ _ _ x := x
  reindexMor _ _ _ p := p
  unreindexObj _ _ _ x := x
  unreindexMor _ _ _ p := p

def semId (A : SemFam) (a b : SemTm) : SemFam where
  lvl := A.lvl
  Obj γ x := ∃ p, x = .idObj p ∧ A.Hom γ γ (idEnv γ) (a.obj γ) (b.obj γ) p
  Hom γ₁ γ₂ δ x y q :=
    y = .idObj (A.comp γ₂ (A.inv γ₂ (a.mor γ₁ γ₂ δ))
      (A.comp γ₂ (A.reindexMor γ₁ γ₂ δ (unId x)) (b.mor γ₁ γ₂ δ))) ∧
    q = y ∧ (∃ p, x = .idObj p ∧ A.Hom γ₁ γ₁ (idEnv γ₁) (a.obj γ₁) (b.obj γ₁) p)
  comp _ p _ := p
  inv _ p := p
  reindexObj γ₁ γ₂ δ x :=
    .idObj (A.comp γ₂ (A.inv γ₂ (a.mor γ₁ γ₂ δ))
      (A.comp γ₂ (A.reindexMor γ₁ γ₂ δ (unId x)) (b.mor γ₁ γ₂ δ)))
  reindexMor γ₁ γ₂ δ q :=
    .idObj (A.comp γ₂ (A.inv γ₂ (a.mor γ₁ γ₂ δ))
      (A.comp γ₂ (A.reindexMor γ₁ γ₂ δ (unId q)) (b.mor γ₁ γ₂ δ)))
  unreindexObj γ₁ γ₂ δ x' :=
    .idObj (A.unreindexMor γ₁ γ₂ δ
      (A.comp γ₂ (a.mor γ₁ γ₂ δ) (A.comp γ₂ (unId x') (A.inv γ₂ (b.mor γ₁ γ₂ δ)))))
  unreindexMor γ₁ γ₂ δ q' :=
    .idObj (A.unreindexMor γ₁ γ₂ δ
      (A.comp γ₂ (a.mor γ₁ γ₂ δ) (A.comp γ₂ (unId q') (A.inv γ₂ (b.mor γ₁ γ₂ δ)))))

def semSigma (A B : SemFam) : SemFam where
  lvl := Nat.max A.lvl B.lvl
  Obj γ z := ∃ x y, z = .pairObj x y ∧ A.Obj γ x ∧ B.Obj (consEnv x γ) y
  Hom γ₁ γ₂ δ z₁ z₂ m :=
    ∃ x₁ y₁ x₂ y₂ p q,
      z₁ = .pairObj x₁ y₁ ∧ z₂ = .pairObj x₂ y₂ ∧
      m = .pairMor (A.reindexObj γ₁ γ₂ δ x₁) x₂ p q ∧
      A.Obj γ₁ x₁ ∧ A.Obj γ₂ x₂ ∧ B.Obj (consEnv x₁ γ₁) y₁ ∧ B.Obj (consEnv x₂ γ₂) y₂ ∧
      A.Hom γ₁ γ₂ δ x₁ x₂ p ∧
      B.Hom (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) y₁ y₂ q
  comp γ m₁ m₂ :=
    let x₁ := sigMorX1 m₁
    let x₂ := sigMorX2 m₁
    let x₃ := sigMorX2 m₂
    let p₁ := sigMorP m₁
    let q₁ := sigMorQ m₁
    let p₂ := sigMorP m₂
    let q₂ := sigMorQ m₂
    .pairMor x₁ x₃ (A.comp γ p₁ p₂)
      (B.comp (consEnv x₃ γ)
        (B.reindexMor (consEnv x₂ γ) (consEnv x₃ γ) (consEnv p₂ (idEnv γ)) q₁) q₂)
  inv γ m :=
    let x₁ := sigMorX1 m
    let x₂ := sigMorX2 m
    let p := sigMorP m
    let q := sigMorQ m
    let pinv := A.inv γ p
    .pairMor x₂ x₁ pinv
      (B.reindexMor (consEnv x₂ γ) (consEnv x₁ γ) (consEnv pinv (idEnv γ))
        (B.inv (consEnv x₂ γ) q))
  reindexObj γ₁ γ₂ δ z :=
    let x := sigFst z
    let y := sigSnd z
    let x' := A.reindexObj γ₁ γ₂ δ x
    .pairObj x' (B.reindexObj (consEnv x γ₁) (consEnv x' γ₂) (consEnv (idVal x') δ) y)
  reindexMor γ₁ γ₂ δ m :=
    let x₁ := sigMorX1 m
    let x₂ := sigMorX2 m
    let p := sigMorP m
    let q := sigMorQ m
    let x₁' := A.reindexObj γ₁ γ₂ δ x₁
    let x₂' := A.reindexObj γ₁ γ₂ δ x₂
    let p' := A.reindexMor γ₁ γ₂ δ p
    .pairMor x₁' x₂' p'
      (B.reindexMor (consEnv x₂ γ₁) (consEnv x₂' γ₂) (consEnv (idVal x₂') δ) q)
  unreindexObj γ₁ γ₂ δ z' :=
    let x' := sigFst z'
    let y' := sigSnd z'
    let x := A.unreindexObj γ₁ γ₂ δ x'
    .pairObj x (B.unreindexObj (consEnv x γ₁) (consEnv x' γ₂) (consEnv (idVal x') δ) y')
  unreindexMor γ₁ γ₂ δ m' :=
    let x₁' := sigMorX1 m'
    let x₂' := sigMorX2 m'
    let p' := sigMorP m'
    let q' := sigMorQ m'
    let x₁ := A.unreindexObj γ₁ γ₂ δ x₁'
    let x₂ := A.unreindexObj γ₁ γ₂ δ x₂'
    let p := A.unreindexMor γ₁ γ₂ δ p'
    .pairMor x₁ x₂ p
      (B.unreindexMor (consEnv x₂ γ₁) (consEnv x₂' γ₂) (consEnv (idVal x₂') δ) q')

abbrev piHetMor (A : SemFam) (γ₁ γ₂ δ : Env) : Val → Val → Val → Prop :=
  fun x y p => A.Obj γ₁ x ∧ A.Obj γ₂ y ∧ A.Hom γ₁ γ₂ δ x y p

abbrev piDomMor (A : SemFam) (γ : Env) : Val → Val → Val → Prop :=
  piHetMor A γ γ (idEnv γ)

@[simp] theorem piHetMor_eq (A : SemFam) (γ₁ γ₂ δ : Env) :
    piHetMor A γ₁ γ₂ δ = (fun x y p => A.Obj γ₁ x ∧ A.Obj γ₂ y ∧ A.Hom γ₁ γ₂ δ x y p) := rfl

@[simp] theorem piHetMor_apply (A : SemFam) (γ₁ γ₂ δ : Env) (x y p : Val) :
    piHetMor A γ₁ γ₂ δ x y p = (A.Obj γ₁ x ∧ A.Obj γ₂ y ∧ A.Hom γ₁ γ₂ δ x y p) := rfl

-- A dependent function is a section functor, so its action preserves
-- identities and composition. Pointwise typing alone does not imply either.
def PiFunctorLaws (A B : SemFam) (γ : Env) (f : Val) : Prop :=
  (∀ x, A.Obj γ x →
    piAppMor f x x (idVal x) = idVal (piAppObj f x)) ∧
  (∀ x y z p q, piDomMor A γ x y p → piDomMor A γ y z q →
    piAppMor f x z (A.comp γ p q) =
      B.comp (consEnv z γ)
        (B.reindexMor (consEnv y γ) (consEnv z γ)
          (consEnv q (idEnv γ)) (piAppMor f x y p))
        (piAppMor f y z q))

-- The mixed components of a dependent natural transformation must commute
-- with vertical arrows on both ends of the base arrow.
def PiNaturalLaws (A B : SemFam) (γ₁ γ₂ δ : Env) (f g η : Val) : Prop :=
  (∀ w x y u p, piDomMor A γ₁ w x u → piHetMor A γ₁ γ₂ δ x y p →
    piMorAt η w y (A.comp γ₂ (A.reindexMor γ₁ γ₂ δ u) p) =
      B.comp (consEnv y γ₂)
        (B.reindexMor (consEnv x γ₁) (consEnv y γ₂)
          (consEnv p δ) (piAppMor f w x u))
        (piMorAt η x y p)) ∧
  (∀ x y z p v, piHetMor A γ₁ γ₂ δ x y p → piDomMor A γ₂ y z v →
    piMorAt η x z (A.comp γ₂ p v) =
      B.comp (consEnv z γ₂)
        (B.reindexMor (consEnv y γ₂) (consEnv z γ₂)
          (consEnv v (idEnv γ₂)) (piMorAt η x y p))
        (piAppMor g y z v))

-- Morphisms are represented in their target fiber throughout the model.
-- This makes the same value usable by composition, inverse and transport.
noncomputable def piTransportObj (A B : SemFam) (γ₁ γ₂ δ : Env) (f : Val) : Val :=
  mkPiObj A.lvl (A.Obj γ₂) (piDomMor A γ₂)
    (fun x' =>
      let x := A.unreindexObj γ₁ γ₂ δ x'
      B.reindexObj (consEnv x γ₁) (consEnv x' γ₂) (consEnv (idVal x') δ) (piAppObj f x))
    (fun x' y' p' =>
      let x := A.unreindexObj γ₁ γ₂ δ x'
      let y := A.unreindexObj γ₁ γ₂ δ y'
      let p := A.unreindexMor γ₁ γ₂ δ p'
      B.reindexMor (consEnv y γ₁) (consEnv y' γ₂) (consEnv (idVal y') δ) (piAppMor f x y p))

def PiHom (A B : SemFam) (γ : Env) (f g η : Val) : Prop :=
  η = mkPiMor A.lvl (piDomMor A γ) (piMorAt η) ∧
  (∀ x y p, piDomMor A γ x y p →
    B.Hom (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
      (piAppObj f x) (piAppObj g y) (piMorAt η x y p)) ∧
  PiNaturalLaws A B γ γ (idEnv γ) f g η

noncomputable def semPi (A B : SemFam) : SemFam where
  lvl := Nat.max (A.lvl + 1) B.lvl
  Obj γ f :=
    f = mkPiObj A.lvl (A.Obj γ) (piDomMor A γ) (piAppObj f) (piAppMor f) ∧
    (∀ x, A.Obj γ x → B.Obj (consEnv x γ) (piAppObj f x)) ∧
    (∀ x y p, piDomMor A γ x y p →
      B.Hom (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
        (piAppObj f x) (piAppObj f y) (piAppMor f x y p)) ∧
    PiFunctorLaws A B γ f
  Hom γ₁ γ₂ δ f g η :=
    PiHom A B γ₂ (piTransportObj A B γ₁ γ₂ δ f) g η
  comp γ η₁ η₂ :=
    mkPiMor A.lvl (piDomMor A γ) (fun x y p =>
      B.comp (consEnv y γ)
        (B.reindexMor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
          (piMorAt η₁ x x (idVal x)))
        (piMorAt η₂ x y p))
  inv γ η :=
    mkPiMor A.lvl (piDomMor A γ) (fun x y p =>
      B.reindexMor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
        (B.inv (consEnv x γ) (piMorAt η y x (A.inv γ p))))
  reindexObj γ₁ γ₂ δ f :=
    mkPiObj A.lvl (A.Obj γ₂) (piDomMor A γ₂)
      (fun x' =>
        let x := A.unreindexObj γ₁ γ₂ δ x'
        B.reindexObj (consEnv x γ₁) (consEnv x' γ₂) (consEnv (idVal x') δ) (piAppObj f x))
      (fun x' y' p' =>
        let x := A.unreindexObj γ₁ γ₂ δ x'
        let y := A.unreindexObj γ₁ γ₂ δ y'
        let p := A.unreindexMor γ₁ γ₂ δ p'
        B.reindexMor (consEnv y γ₁) (consEnv y' γ₂) (consEnv (idVal y') δ) (piAppMor f x y p))
  reindexMor γ₁ γ₂ δ η :=
    mkPiMor A.lvl (piDomMor A γ₂) (fun x' y' p' =>
      let x := A.unreindexObj γ₁ γ₂ δ x'
      let y := A.unreindexObj γ₁ γ₂ δ y'
      let p := A.unreindexMor γ₁ γ₂ δ p'
      B.reindexMor (consEnv y γ₁) (consEnv y' γ₂) (consEnv (idVal y') δ) (piMorAt η x y p))
  unreindexObj γ₁ γ₂ δ f' :=
    mkPiObj A.lvl (A.Obj γ₁) (piDomMor A γ₁)
      (fun x =>
        let x' := A.reindexObj γ₁ γ₂ δ x
        B.unreindexObj (consEnv x γ₁) (consEnv x' γ₂) (consEnv (idVal x') δ) (piAppObj f' x'))
      (fun x y p =>
        let x' := A.reindexObj γ₁ γ₂ δ x
        let y' := A.reindexObj γ₁ γ₂ δ y
        let p' := A.reindexMor γ₁ γ₂ δ p
        B.unreindexMor (consEnv y γ₁) (consEnv y' γ₂) (consEnv (idVal y') δ) (piAppMor f' x' y' p'))
  unreindexMor γ₁ γ₂ δ η' :=
    mkPiMor A.lvl (piDomMor A γ₁) (fun x y p =>
      let x' := A.reindexObj γ₁ γ₂ δ x
      let y' := A.reindexObj γ₁ γ₂ δ y
      let p' := A.reindexMor γ₁ γ₂ δ p
      B.unreindexMor (consEnv y γ₁) (consEnv y' γ₂) (consEnv (idVal y') δ) (piMorAt η' x' y' p'))

def unNat : Val → Nat
  | .nat k => k
  | _ => 0

def natRecObj (z s : SemTm) (γ : Env) : Nat → Val
  | 0 => z.obj γ
  | k + 1 => s.obj (consEnv (natRecObj z s γ k) (consEnv (.nat k) γ))

def natRecMor (z s : SemTm) (γ₁ γ₂ δ : Env) : Nat → Val
  | 0 => z.mor γ₁ γ₂ δ
  | k + 1 =>
    s.mor
      (consEnv (natRecObj z s γ₁ k) (consEnv (.nat k) γ₁))
      (consEnv (natRecObj z s γ₂ k) (consEnv (.nat k) γ₂))
      (consEnv (natRecMor z s γ₁ γ₂ δ k) (consEnv (.nat k) δ))

noncomputable def eval : Expr → SemFam × SemTm
  | .var n =>
    (dfltFam, { obj := fun γ => γ n, mor := fun _ _ δ => δ n })
  | .pi A B =>
    let eA := (eval A).1
    let eB := (eval B).1
    (semPi eA eB, dfltTm)
  | .sigma A B =>
    let eA := (eval A).1
    let eB := (eval B).1
    (semSigma eA eB, dfltTm)
  | .identity A a b =>
    let eA := (eval A).1
    let ea := (eval a).2
    let eb := (eval b).2
    (semId eA ea eb, dfltTm)
  | .nat => (semNat, dfltTm)
  | .universe => (semUniverse, dfltTm)
  | .el a =>
    let _ := eval a
    (semEl, dfltTm)
  | .lam A b =>
    let eA := (eval A).1
    let eb := (eval b).2
    (dfltFam, {
      obj := fun γ =>
        mkPiObj eA.lvl (eA.Obj γ) (piDomMor eA γ)
          (fun x => eb.obj (consEnv x γ))
          (fun x y p => eb.mor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
      mor := fun γ₁ γ₂ δ =>
        mkPiMor eA.lvl (piDomMor eA γ₂) (fun x' y p =>
          let x := eA.unreindexObj γ₁ γ₂ δ x'
          eb.mor (consEnv x γ₁) (consEnv y γ₂) (consEnv p δ))
    })
  | .app A B f a =>
    let eA := (eval A).1
    let _ := eval B
    let ef := (eval f).2
    let ea := (eval a).2
    (dfltFam, {
      obj := fun γ => piAppObj (ef.obj γ) (ea.obj γ)
      mor := fun γ₁ γ₂ δ =>
        piMorAt (ef.mor γ₁ γ₂ δ)
          (eA.reindexObj γ₁ γ₂ δ (ea.obj γ₁)) (ea.obj γ₂) (ea.mor γ₁ γ₂ δ)
    })
  | .pair A B a b =>
    let eA := (eval A).1
    let _ := eval B
    let ea := (eval a).2
    let eb := (eval b).2
    (dfltFam, {
      obj := fun γ => .pairObj (ea.obj γ) (eb.obj γ)
      mor := fun γ₁ γ₂ δ =>
        .pairMor (eA.reindexObj γ₁ γ₂ δ (ea.obj γ₁)) (ea.obj γ₂)
          (ea.mor γ₁ γ₂ δ) (eb.mor γ₁ γ₂ δ)
    })
  | .sigmaRec A B C d p =>
    let _ := eval A
    let _ := eval B
    let _ := eval C
    let ed := (eval d).2
    let ep := (eval p).2
    (dfltFam, {
      obj := fun γ =>
        ed.obj (consEnv (sigSnd (ep.obj γ)) (consEnv (sigFst (ep.obj γ)) γ))
      mor := fun γ₁ γ₂ δ =>
        ed.mor
          (consEnv (sigSnd (ep.obj γ₁)) (consEnv (sigFst (ep.obj γ₁)) γ₁))
          (consEnv (sigSnd (ep.obj γ₂)) (consEnv (sigFst (ep.obj γ₂)) γ₂))
          (consEnv (sigMorQ (ep.mor γ₁ γ₂ δ)) (consEnv (sigMorP (ep.mor γ₁ γ₂ δ)) δ))
    })
  | .refl A a =>
    let _ := eval A
    let ea := (eval a).2
    (dfltFam, {
      obj := fun γ => .idObj (idVal (ea.obj γ))
      mor := fun _ γ₂ _ => .idObj (idVal (ea.obj γ₂))
    })
  | .idRec A C d a b p =>
    let _ := eval A
    let eC := (eval C).1
    let ed := (eval d).2
    let ea := (eval a).2
    let eb := (eval b).2
    let ep := (eval p).2
    (dfltFam, {
      obj := fun γ =>
        let a₀ := ea.obj γ
        let b₀ := eb.obj γ
        let p₀ := ep.obj γ
        let γ₀ := consEnv (.idObj (idVal a₀)) (consEnv a₀ (consEnv a₀ γ))
        let γ₁ := consEnv p₀ (consEnv b₀ (consEnv a₀ γ))
        let δ_J := consEnv p₀ (consEnv (unId p₀) (consEnv (idVal a₀) (idEnv γ)))
        eC.reindexObj γ₀ γ₁ δ_J (ed.obj (consEnv a₀ γ))
      mor := fun γ₁ γ₂ δ =>
        let a₂ := ea.obj γ₂
        let b₂ := eb.obj γ₂
        let p₂ := ep.obj γ₂
        let γ₀ := consEnv (.idObj (idVal a₂)) (consEnv a₂ (consEnv a₂ γ₂))
        let γ_t := consEnv p₂ (consEnv b₂ (consEnv a₂ γ₂))
        let δ_J := consEnv p₂ (consEnv (unId p₂) (consEnv (idVal a₂) (idEnv γ₂)))
        eC.reindexMor γ₀ γ_t δ_J
          (ed.mor (consEnv (ea.obj γ₁) γ₁) (consEnv a₂ γ₂) (consEnv (ea.mor γ₁ γ₂ δ) δ))
    })
  | .zero =>
    (dfltFam, { obj := fun _ => .nat 0, mor := fun _ _ _ => .nat 0 })
  | .succ n =>
    let en := (eval n).2
    (dfltFam, {
      obj := fun γ => .nat (unNat (en.obj γ) + 1)
      mor := fun _ γ₂ _ => .nat (unNat (en.obj γ₂) + 1)
    })
  | .natRec C z s n =>
    let _ := eval C
    let ez := (eval z).2
    let es := (eval s).2
    let en := (eval n).2
    (dfltFam, {
      obj := fun γ => natRecObj ez es γ (unNat (en.obj γ))
      mor := fun γ₁ γ₂ δ => natRecMor ez es γ₁ γ₂ δ (unNat (en.obj γ₂))
    })

noncomputable abbrev evalTy (e : Expr) : SemFam := (eval e).1
noncomputable abbrev evalTm (e : Expr) : SemTm := (eval e).2

def renameFam (ρ : Nat → Nat) (A : SemFam) : SemFam where
  lvl := A.lvl
  Obj γ x := A.Obj (renEnv ρ γ) x
  Hom γ₁ γ₂ δ x y p := A.Hom (renEnv ρ γ₁) (renEnv ρ γ₂) (renEnv ρ δ) x y p
  comp γ p q := A.comp (renEnv ρ γ) p q
  inv γ p := A.inv (renEnv ρ γ) p
  reindexObj γ₁ γ₂ δ x := A.reindexObj (renEnv ρ γ₁) (renEnv ρ γ₂) (renEnv ρ δ) x
  reindexMor γ₁ γ₂ δ p := A.reindexMor (renEnv ρ γ₁) (renEnv ρ γ₂) (renEnv ρ δ) p
  unreindexObj γ₁ γ₂ δ x := A.unreindexObj (renEnv ρ γ₁) (renEnv ρ γ₂) (renEnv ρ δ) x
  unreindexMor γ₁ γ₂ δ p := A.unreindexMor (renEnv ρ γ₁) (renEnv ρ γ₂) (renEnv ρ δ) p

def renameTm (ρ : Nat → Nat) (t : SemTm) : SemTm where
  obj γ := t.obj (renEnv ρ γ)
  mor γ₁ γ₂ δ := t.mor (renEnv ρ γ₁) (renEnv ρ γ₂) (renEnv ρ δ)

@[simp] theorem natRecObj_rename (ρ : Nat → Nat) (z s : SemTm) (γ : Env) :
    ∀ k, natRecObj (renameTm ρ z) (renameTm (liftRenaming (liftRenaming ρ)) s) γ k =
      natRecObj z s (renEnv ρ γ) k
  | 0 => rfl
  | k + 1 => by
    unfold natRecObj
    rw [natRecObj_rename ρ z s γ k]
    simp only [renameTm, renEnv_consEnv_lift]

@[simp] theorem natRecMor_rename (ρ : Nat → Nat) (z s : SemTm) (γ₁ γ₂ δ : Env) :
    ∀ k, natRecMor (renameTm ρ z) (renameTm (liftRenaming (liftRenaming ρ)) s) γ₁ γ₂ δ k =
      natRecMor z s (renEnv ρ γ₁) (renEnv ρ γ₂) (renEnv ρ δ) k
  | 0 => rfl
  | k + 1 => by
    unfold natRecMor
    rw [natRecObj_rename, natRecObj_rename, natRecMor_rename ρ z s γ₁ γ₂ δ k]
    simp only [renameTm, renEnv_consEnv_lift]

theorem semId_rename (ρ : Nat → Nat) (A : SemFam) (a b : SemTm) :
    semId (renameFam ρ A) (renameTm ρ a) (renameTm ρ b) = renameFam ρ (semId A a b) := rfl

theorem semSigma_rename (ρ : Nat → Nat) (A B : SemFam) :
    semSigma (renameFam ρ A) (renameFam (liftRenaming ρ) B) = renameFam ρ (semSigma A B) := by
  simp only [semSigma, renameFam, renEnv_consEnv_lift, idEnv_renEnv]

theorem semPi_rename (ρ : Nat → Nat) (A B : SemFam) :
    semPi (renameFam ρ A) (renameFam (liftRenaming ρ) B) = renameFam ρ (semPi A B) := by
  simp only [semPi, PiHom, piTransportObj, PiFunctorLaws, PiNaturalLaws, renameFam,
    piDomMor, piHetMor_eq, piHetMor_apply, renEnv_consEnv_lift, idEnv_renEnv]

theorem eval_rename : ∀ (e : Expr) (ρ : Nat → Nat),
    eval (rename ρ e) = (renameFam ρ (eval e).1, renameTm ρ (eval e).2)
  | .var _, _ => rfl
  | .pi A B, ρ => by
    unfold rename eval
    rw [eval_rename A ρ, eval_rename B (liftRenaming ρ)]
    dsimp only
    rw [semPi_rename]
    rfl
  | .sigma A B, ρ => by
    unfold rename eval
    rw [eval_rename A ρ, eval_rename B (liftRenaming ρ)]
    dsimp only
    rw [semSigma_rename]
    rfl
  | .identity A a b, ρ => by
    unfold rename eval
    rw [eval_rename A ρ, eval_rename a ρ, eval_rename b ρ]
    rfl
  | .nat, _ => rfl
  | .universe, _ => rfl
  | .el _, _ => rfl
  | .lam A b, ρ => by
    unfold rename eval
    rw [eval_rename A ρ, eval_rename b (liftRenaming ρ)]
    simp only [renameFam, renameTm, dfltFam, piDomMor, renEnv_consEnv_lift, idEnv_renEnv]
  | .app A B f a, ρ => by
    unfold rename eval
    rw [eval_rename A ρ, eval_rename f ρ, eval_rename a ρ]
    rfl
  | .pair A B a b, ρ => by
    unfold rename eval
    rw [eval_rename A ρ, eval_rename a ρ, eval_rename b ρ]
    rfl
  | .sigmaRec A B C d p, ρ => by
    unfold rename eval
    rw [eval_rename d (liftRenaming (liftRenaming ρ)), eval_rename p ρ]
    simp only [renameFam, renameTm, dfltFam, renEnv_consEnv_lift]
  | .refl A a, ρ => by
    unfold rename eval
    rw [eval_rename a ρ]
    rfl
  | .idRec A C d a b p, ρ => by
    unfold rename eval
    rw [eval_rename C (liftRenaming (liftRenaming (liftRenaming ρ))),
      eval_rename d (liftRenaming ρ), eval_rename a ρ, eval_rename b ρ, eval_rename p ρ]
    simp only [renameFam, renameTm, dfltFam, renEnv_consEnv_lift, idEnv_renEnv]
  | .zero, _ => rfl
  | .succ n, ρ => by
    unfold rename eval
    rw [eval_rename n ρ]
    rfl
  | .natRec C z s n, ρ => by
    unfold rename eval
    rw [eval_rename z ρ, eval_rename s (liftRenaming (liftRenaming ρ)), eval_rename n ρ]
    dsimp only
    simp only [natRecObj_rename, natRecMor_rename]
    rfl

theorem evalTy_rename (e : Expr) (ρ : Nat → Nat) :
    evalTy (rename ρ e) = renameFam ρ (evalTy e) :=
  congrArg Prod.fst (eval_rename e ρ)

theorem evalTm_rename (e : Expr) (ρ : Nat → Nat) :
    evalTm (rename ρ e) = renameTm ρ (evalTm e) :=
  congrArg Prod.snd (eval_rename e ρ)

-- Substitution
noncomputable def subObj (σ : Nat → Expr) (γ : Env) : Env :=
  fun n => (evalTm (σ n)).obj γ

noncomputable def subMor (σ : Nat → Expr) (γ₁ γ₂ δ : Env) : Env :=
  fun n => (evalTm (σ n)).mor γ₁ γ₂ δ

def EnvOn (σ : Nat → Expr) (γ : Env) : Prop :=
  ∀ n, (evalTm (σ n)).mor γ γ (idEnv γ) = idVal ((evalTm (σ n)).obj γ)

@[simp] theorem subObj_consEnv_lift (σ : Nat → Expr) (x : Val) (γ : Env) :
    subObj (liftSubstitution σ) (consEnv x γ) = consEnv x (subObj σ γ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [subObj, liftSubstitution, weaken, evalTm_rename, renameTm, renEnv_succ_consEnv, consEnv_succ]

@[simp] theorem subMor_consEnv_lift (σ : Nat → Expr) (x₁ x₂ p : Val) (γ₁ γ₂ δ : Env) :
    subMor (liftSubstitution σ) (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) =
      consEnv p (subMor σ γ₁ γ₂ δ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [subMor, liftSubstitution, weaken, evalTm_rename, renameTm, renEnv_succ_consEnv, consEnv_succ]

theorem subMor_idEnv {σ : Nat → Expr} {γ : Env} (h : EnvOn σ γ) :
    subMor σ γ γ (idEnv γ) = idEnv (subObj σ γ) :=
  funext (h ·)

theorem EnvOn.lift {σ : Nat → Expr} {γ : Env} (h : EnvOn σ γ) (x : Val) :
    EnvOn (liftSubstitution σ) (consEnv x γ) := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [liftSubstitution, weaken, evalTm_rename, renameTm, idEnv_consEnv, renEnv_succ_consEnv]
    exact h n

def FamSubstAt (A' A : SemFam) (σ : Nat → Expr) : Prop :=
  A'.lvl = A.lvl ∧
  (∀ γ, EnvOn σ γ →
    A'.Obj γ = A.Obj (subObj σ γ) ∧
    A'.comp γ = A.comp (subObj σ γ) ∧
    A'.inv γ = A.inv (subObj σ γ)) ∧
  (∀ γ₁ γ₂ δ, EnvOn σ γ₁ → EnvOn σ γ₂ →
    A'.Hom γ₁ γ₂ δ = A.Hom (subObj σ γ₁) (subObj σ γ₂) (subMor σ γ₁ γ₂ δ) ∧
    A'.reindexObj γ₁ γ₂ δ = A.reindexObj (subObj σ γ₁) (subObj σ γ₂) (subMor σ γ₁ γ₂ δ) ∧
    A'.reindexMor γ₁ γ₂ δ = A.reindexMor (subObj σ γ₁) (subObj σ γ₂) (subMor σ γ₁ γ₂ δ) ∧
    A'.unreindexObj γ₁ γ₂ δ = A.unreindexObj (subObj σ γ₁) (subObj σ γ₂) (subMor σ γ₁ γ₂ δ) ∧
    A'.unreindexMor γ₁ γ₂ δ = A.unreindexMor (subObj σ γ₁) (subObj σ γ₂) (subMor σ γ₁ γ₂ δ))

def TmSubstAt (t' t : SemTm) (σ : Nat → Expr) : Prop :=
  (∀ γ, EnvOn σ γ → t'.obj γ = t.obj (subObj σ γ)) ∧
  (∀ γ₁ γ₂ δ, EnvOn σ γ₁ → EnvOn σ γ₂ →
    t'.mor γ₁ γ₂ δ = t.mor (subObj σ γ₁) (subObj σ γ₂) (subMor σ γ₁ γ₂ δ))

theorem FamSubstAt.dflt (σ : Nat → Expr) : FamSubstAt dfltFam dfltFam σ :=
  ⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem TmSubstAt.dflt (σ : Nat → Expr) : TmSubstAt dfltTm dfltTm σ :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩

theorem FamSubstAt.semId {A' A : SemFam} {a' a b' b : SemTm} {σ : Nat → Expr}
    (hA : FamSubstAt A' A σ) (ha : TmSubstAt a' a σ) (hb : TmSubstAt b' b σ) :
    FamSubstAt (semId A' a' b') (semId A a b) σ := by
  refine ⟨hA.1, fun γ hγ => ?_, fun γ₁ γ₂ δ hγ₁ hγ₂ => ?_⟩
  · have hAh := (hA.2.2 γ γ (idEnv γ) hγ hγ).1
    have hao := ha.1 γ hγ
    have hbo := hb.1 γ hγ
    dsimp only [HofmannStreicher1994.Repaired.semId]
    simp only [hAh, hao, hbo, subMor_idEnv hγ, and_self]
  · have ⟨_, hAc, hAi⟩ := hA.2.1 γ₂ hγ₂
    have hAh₁ := (hA.2.2 γ₁ γ₁ (idEnv γ₁) hγ₁ hγ₁).1
    have ⟨_, _, hArm, _, hAurm⟩ := hA.2.2 γ₁ γ₂ δ hγ₁ hγ₂
    have hao₁ := ha.1 γ₁ hγ₁
    have hbo₁ := hb.1 γ₁ hγ₁
    have ham := ha.2 γ₁ γ₂ δ hγ₁ hγ₂
    have hbm := hb.2 γ₁ γ₂ δ hγ₁ hγ₂
    dsimp only [HofmannStreicher1994.Repaired.semId]
    simp only [hAh₁, hAc, hAi, hArm, hAurm, hao₁, hbo₁, ham, hbm, subMor_idEnv hγ₁, and_self]

theorem FamSubstAt.semSigma {A' A B' B : SemFam} {σ : Nat → Expr}
    (hA : FamSubstAt A' A σ) (hB : FamSubstAt B' B (liftSubstitution σ)) :
    FamSubstAt (semSigma A' B') (semSigma A B) σ := by
  refine ⟨by dsimp [HofmannStreicher1994.Repaired.semSigma]; rw [hA.1, hB.1],
    fun γ hγ => ?_, fun γ₁ γ₂ δ hγ₁ hγ₂ => ?_⟩
  · have ⟨hAo, hAc, hAi⟩ := hA.2.1 γ hγ
    have hBo := fun x => (hB.2.1 (consEnv x γ) (hγ.lift x)).1
    have hBc := fun x => (hB.2.1 (consEnv x γ) (hγ.lift x)).2.1
    have hBi := fun x => (hB.2.1 (consEnv x γ) (hγ.lift x)).2.2
    have hBrm := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ) (consEnv x₂ γ) (consEnv p (idEnv γ)) (hγ.lift x₁) (hγ.lift x₂)).2.2.1
    dsimp only [HofmannStreicher1994.Repaired.semSigma]
    simp only [hAo, hAc, hAi, hBo, hBc, hBi, hBrm,
      subObj_consEnv_lift, subMor_consEnv_lift, subMor_idEnv hγ, and_self]
  · have hAo₁ := (hA.2.1 γ₁ hγ₁).1
    have hAo₂ := (hA.2.1 γ₂ hγ₂).1
    have ⟨hAh, hAro, hArm, hAuro, hAurm⟩ := hA.2.2 γ₁ γ₂ δ hγ₁ hγ₂
    have hBo₁ := fun x => (hB.2.1 (consEnv x γ₁) (hγ₁.lift x)).1
    have hBo₂ := fun x => (hB.2.1 (consEnv x γ₂) (hγ₂.lift x)).1
    have hBh := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) (hγ₁.lift x₁) (hγ₂.lift x₂)).1
    have hBro := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) (hγ₁.lift x₁) (hγ₂.lift x₂)).2.1
    have hBrm := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) (hγ₁.lift x₁) (hγ₂.lift x₂)).2.2.1
    have hBuro := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) (hγ₁.lift x₁) (hγ₂.lift x₂)).2.2.2.1
    have hBurm := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) (hγ₁.lift x₁) (hγ₂.lift x₂)).2.2.2.2
    dsimp only [HofmannStreicher1994.Repaired.semSigma]
    simp only [hAo₁, hAo₂, hAh, hAro, hArm, hAuro, hAurm, hBo₁, hBo₂, hBh, hBro, hBrm, hBuro, hBurm,
      subObj_consEnv_lift, subMor_consEnv_lift, and_self]

theorem FamSubstAt.semPi {A' A B' B : SemFam} {σ : Nat → Expr}
    (hA : FamSubstAt A' A σ) (hB : FamSubstAt B' B (liftSubstitution σ)) :
    FamSubstAt (semPi A' B') (semPi A B) σ := by
  refine ⟨by dsimp [HofmannStreicher1994.Repaired.semPi]; rw [hA.1, hB.1],
    fun γ hγ => ?_, fun γ₁ γ₂ δ hγ₁ hγ₂ => ?_⟩
  · have hAl := hA.1
    have ⟨hAo, hAc, hAi⟩ := hA.2.1 γ hγ
    have hAh := (hA.2.2 γ γ (idEnv γ) hγ hγ).1
    have hBo := fun x => (hB.2.1 (consEnv x γ) (hγ.lift x)).1
    have hBc := fun x => (hB.2.1 (consEnv x γ) (hγ.lift x)).2.1
    have hBi := fun x => (hB.2.1 (consEnv x γ) (hγ.lift x)).2.2
    have hBh := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ) (consEnv x₂ γ) (consEnv p (idEnv γ)) (hγ.lift x₁) (hγ.lift x₂)).1
    have hBrm := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ) (consEnv x₂ γ) (consEnv p (idEnv γ)) (hγ.lift x₁) (hγ.lift x₂)).2.2.1
    dsimp only [HofmannStreicher1994.Repaired.semPi, PiHom, piTransportObj]
    simp only [PiFunctorLaws, piDomMor, piHetMor_eq, piHetMor_apply, hAl, hAo, hAh, hAc, hAi, hBo, hBh, hBc, hBi, hBrm,
      subObj_consEnv_lift, subMor_consEnv_lift, subMor_idEnv hγ, and_self]
  · have hAl := hA.1
    have hAo₁ := (hA.2.1 γ₁ hγ₁).1
    have hAo₂ := (hA.2.1 γ₂ hγ₂).1
    have hAc₂ := (hA.2.1 γ₂ hγ₂).2.1
    have hAh₁ := (hA.2.2 γ₁ γ₁ (idEnv γ₁) hγ₁ hγ₁).1
    have hAh₂ := (hA.2.2 γ₂ γ₂ (idEnv γ₂) hγ₂ hγ₂).1
    have ⟨hAh, hAro, hArm, hAuro, hAurm⟩ := hA.2.2 γ₁ γ₂ δ hγ₁ hγ₂
    have hBh := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) (hγ₁.lift x₁) (hγ₂.lift x₂)).1
    have hBro := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) (hγ₁.lift x₁) (hγ₂.lift x₂)).2.1
    have hBrm := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) (hγ₁.lift x₁) (hγ₂.lift x₂)).2.2.1
    have hBuro := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) (hγ₁.lift x₁) (hγ₂.lift x₂)).2.2.2.1
    have hBurm := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) (hγ₁.lift x₁) (hγ₂.lift x₂)).2.2.2.2
    have hBc₂ := fun x => (hB.2.1 (consEnv x γ₂) (hγ₂.lift x)).2.1
    have hBrm₂ := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ₂) (consEnv x₂ γ₂) (consEnv p (idEnv γ₂)) (hγ₂.lift x₁) (hγ₂.lift x₂)).2.2.1
    have hBh₂ := fun x₁ x₂ p => (hB.2.2 (consEnv x₁ γ₂) (consEnv x₂ γ₂) (consEnv p (idEnv γ₂)) (hγ₂.lift x₁) (hγ₂.lift x₂)).1
    have hArm₂ := (hA.2.2 γ₂ γ₂ (idEnv γ₂) hγ₂ hγ₂).2.2.1
    dsimp only [HofmannStreicher1994.Repaired.semPi, PiHom, piTransportObj]
    simp only [PiNaturalLaws, piDomMor, piHetMor_eq, piHetMor_apply, hAl, hAo₁, hAo₂, hAh₁, hAh₂, hAc₂, hBc₂, hBrm₂, hBh₂, hArm₂,
      hAro, hArm, hAuro, hAurm, hBro, hBrm, hBuro, hBurm,
      subObj_consEnv_lift, subMor_consEnv_lift, subMor_idEnv hγ₁, subMor_idEnv hγ₂, and_self]

def SubstTmOnly (σ : Nat → Expr) : Prop :=
  ∀ n, evalTy (σ n) = dfltFam

theorem SubstTmOnly.lift {σ : Nat → Expr} (h : SubstTmOnly σ) :
    SubstTmOnly (liftSubstitution σ) := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [liftSubstitution, weaken, evalTy_rename, h n]
    rfl

theorem natRecObj_subst {z' z s' s : SemTm} {σ : Nat → Expr}
    (hz : TmSubstAt z' z σ) (hs : TmSubstAt s' s (liftSubstitution (liftSubstitution σ)))
    {γ : Env} (hγ : EnvOn σ γ) :
    ∀ k, natRecObj z' s' γ k = natRecObj z s (subObj σ γ) k
  | 0 => hz.1 γ hγ
  | k + 1 => by
    unfold natRecObj
    rw [natRecObj_subst hz hs hγ k]
    have h1 := hs.1 (consEnv (natRecObj z s (subObj σ γ) k) (consEnv (.nat k) γ))
      ((hγ.lift (.nat k)).lift (natRecObj z s (subObj σ γ) k))
    simp only [subObj_consEnv_lift] at h1
    exact h1

theorem natRecMor_subst {z' z s' s : SemTm} {σ : Nat → Expr}
    (hz : TmSubstAt z' z σ) (hs : TmSubstAt s' s (liftSubstitution (liftSubstitution σ)))
    {γ₁ γ₂ δ : Env} (hγ₁ : EnvOn σ γ₁) (hγ₂ : EnvOn σ γ₂) :
    ∀ k, natRecMor z' s' γ₁ γ₂ δ k = natRecMor z s (subObj σ γ₁) (subObj σ γ₂) (subMor σ γ₁ γ₂ δ) k
  | 0 => hz.2 γ₁ γ₂ δ hγ₁ hγ₂
  | k + 1 => by
    unfold natRecMor
    rw [natRecObj_subst hz hs hγ₁ k, natRecObj_subst hz hs hγ₂ k, natRecMor_subst hz hs hγ₁ hγ₂ k]
    have h2 := hs.2
      (consEnv (natRecObj z s (subObj σ γ₁) k) (consEnv (.nat k) γ₁))
      (consEnv (natRecObj z s (subObj σ γ₂) k) (consEnv (.nat k) γ₂))
      (consEnv (natRecMor z s (subObj σ γ₁) (subObj σ γ₂) (subMor σ γ₁ γ₂ δ) k) (consEnv (.nat k) δ))
      ((hγ₁.lift (.nat k)).lift (natRecObj z s (subObj σ γ₁) k))
      ((hγ₂.lift (.nat k)).lift (natRecObj z s (subObj σ γ₂) k))
    simp only [subObj_consEnv_lift, subMor_consEnv_lift] at h2
    exact h2

theorem eval_substitute : ∀ (e : Expr) {σ : Nat → Expr}, SubstTmOnly σ →
    FamSubstAt (evalTy (substitute σ e)) (evalTy e) σ ∧
    TmSubstAt (evalTm (substitute σ e)) (evalTm e) σ
  | .var n, σ, hσ => by
    refine ⟨?_, ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩
    change FamSubstAt (evalTy (σ n)) dfltFam σ
    rw [hσ n]
    exact FamSubstAt.dflt σ
  | .pi A B, σ, hσ =>
    ⟨FamSubstAt.semPi (eval_substitute A hσ).1 (eval_substitute B hσ.lift).1, TmSubstAt.dflt σ⟩
  | .sigma A B, σ, hσ =>
    ⟨FamSubstAt.semSigma (eval_substitute A hσ).1 (eval_substitute B hσ.lift).1, TmSubstAt.dflt σ⟩
  | .identity A a b, σ, hσ =>
    ⟨FamSubstAt.semId (eval_substitute A hσ).1 (eval_substitute a hσ).2 (eval_substitute b hσ).2,
      TmSubstAt.dflt σ⟩
  | .nat, σ, _ =>
    ⟨⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩, TmSubstAt.dflt σ⟩
  | .universe, σ, _ =>
    ⟨⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩, TmSubstAt.dflt σ⟩
  | .el _, σ, _ =>
    ⟨⟨rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩, TmSubstAt.dflt σ⟩
  | .lam A b, σ, hσ => by
    have hA := (eval_substitute A hσ).1
    have hb := (eval_substitute b hσ.lift).2
    refine ⟨FamSubstAt.dflt σ, ⟨fun γ hγ => ?_, fun γ₁ γ₂ δ hγ₁ hγ₂ => ?_⟩⟩
    · have hAl := hA.1
      have hAo := (hA.2.1 γ hγ).1
      have hAh := (hA.2.2 γ γ (idEnv γ) hγ hγ).1
      have hbo := fun x => hb.1 (consEnv x γ) (hγ.lift x)
      have hbm := fun x y p => hb.2 (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)) (hγ.lift x) (hγ.lift y)
      dsimp only [substitute, evalTm, eval]
      simp only [piDomMor, piHetMor_eq, hAl, hAo, hAh, hbo, hbm, subObj_consEnv_lift, subMor_consEnv_lift, subMor_idEnv hγ]
    · have hAl := hA.1
      have hAo₁ := (hA.2.1 γ₁ hγ₁).1
      have hAo₂ := (hA.2.1 γ₂ hγ₂).1
      have hAh := (hA.2.2 γ₁ γ₂ δ hγ₁ hγ₂).1
      have hAh₂ := (hA.2.2 γ₂ γ₂ (idEnv γ₂) hγ₂ hγ₂).1
      have hAuo := (hA.2.2 γ₁ γ₂ δ hγ₁ hγ₂).2.2.2.1
      have hbm := fun x y p => hb.2 (consEnv x γ₁) (consEnv y γ₂) (consEnv p δ) (hγ₁.lift x) (hγ₂.lift y)
      dsimp only [substitute, evalTm, eval]
      simp only [piDomMor, piHetMor_eq, hAl, hAo₂, hAh₂, hAuo, hbm,
        subObj_consEnv_lift, subMor_consEnv_lift, subMor_idEnv hγ₂]
  | .app A B f a, σ, hσ => by
    have hA := (eval_substitute A hσ).1
    have hf := (eval_substitute f hσ).2
    have ha := (eval_substitute a hσ).2
    refine ⟨FamSubstAt.dflt σ, ⟨fun γ hγ => ?_, fun γ₁ γ₂ δ hγ₁ hγ₂ => ?_⟩⟩
    · dsimp only [substitute, evalTm, eval]
      rw [hf.1 γ hγ, ha.1 γ hγ]
    · dsimp only [substitute, evalTm, eval]
      rw [hf.2 γ₁ γ₂ δ hγ₁ hγ₂, ha.1 γ₁ hγ₁, ha.1 γ₂ hγ₂, ha.2 γ₁ γ₂ δ hγ₁ hγ₂]
      rw [(hA.2.2 γ₁ γ₂ δ hγ₁ hγ₂).2.1]
  | .pair A B a b, σ, hσ => by
    have hA := (eval_substitute A hσ).1
    have ha := (eval_substitute a hσ).2
    have hb := (eval_substitute b hσ).2
    refine ⟨FamSubstAt.dflt σ, ⟨fun γ hγ => ?_, fun γ₁ γ₂ δ hγ₁ hγ₂ => ?_⟩⟩
    · dsimp only [substitute, evalTm, eval]
      rw [ha.1 γ hγ, hb.1 γ hγ]
    · dsimp only [substitute, evalTm, eval]
      rw [ha.1 γ₁ hγ₁, ha.1 γ₂ hγ₂, ha.2 γ₁ γ₂ δ hγ₁ hγ₂, hb.2 γ₁ γ₂ δ hγ₁ hγ₂]
      rw [(hA.2.2 γ₁ γ₂ δ hγ₁ hγ₂).2.1]
  | .sigmaRec A B C d p, σ, hσ => by
    have hd := (eval_substitute d hσ.lift.lift).2
    have hp := (eval_substitute p hσ).2
    refine ⟨FamSubstAt.dflt σ, ⟨fun γ hγ => ?_, fun γ₁ γ₂ δ hγ₁ hγ₂ => ?_⟩⟩
    · dsimp only [substitute, evalTm, eval]
      rw [hp.1 γ hγ]
      have hdo := hd.1 (consEnv (sigSnd ((eval p).2.obj (subObj σ γ))) (consEnv (sigFst ((eval p).2.obj (subObj σ γ))) γ))
        ((hγ.lift _).lift _)
      simp only [subObj_consEnv_lift] at hdo
      exact hdo
    · dsimp only [substitute, evalTm, eval]
      rw [hp.1 γ₁ hγ₁, hp.1 γ₂ hγ₂, hp.2 γ₁ γ₂ δ hγ₁ hγ₂]
      have hdm := hd.2
        (consEnv (sigSnd ((eval p).2.obj (subObj σ γ₁))) (consEnv (sigFst ((eval p).2.obj (subObj σ γ₁))) γ₁))
        (consEnv (sigSnd ((eval p).2.obj (subObj σ γ₂))) (consEnv (sigFst ((eval p).2.obj (subObj σ γ₂))) γ₂))
        (consEnv (sigMorQ ((eval p).2.mor (subObj σ γ₁) (subObj σ γ₂) (subMor σ γ₁ γ₂ δ)))
          (consEnv (sigMorP ((eval p).2.mor (subObj σ γ₁) (subObj σ γ₂) (subMor σ γ₁ γ₂ δ))) δ))
        ((hγ₁.lift _).lift _) ((hγ₂.lift _).lift _)
      simp only [subObj_consEnv_lift, subMor_consEnv_lift] at hdm
      exact hdm
  | .refl A a, σ, hσ => by
    have ha := (eval_substitute a hσ).2
    refine ⟨FamSubstAt.dflt σ, ⟨fun γ hγ => ?_, fun γ₁ γ₂ δ _ hγ₂ => ?_⟩⟩
    · dsimp only [substitute, evalTm, eval]
      rw [ha.1 γ hγ]
    · dsimp only [substitute, evalTm, eval]
      rw [ha.1 γ₂ hγ₂]
  | .idRec A C d a b p, σ, hσ => by
    have hC := (eval_substitute C hσ.lift.lift.lift).1
    have hd := (eval_substitute d hσ.lift).2
    have ha := (eval_substitute a hσ).2
    have hb := (eval_substitute b hσ).2
    have hp := (eval_substitute p hσ).2
    refine ⟨FamSubstAt.dflt σ, ⟨fun γ hγ => ?_, fun γ₁ γ₂ δ hγ₁ hγ₂ => ?_⟩⟩
    · dsimp only [substitute, evalTm, eval]
      dsimp only [evalTy, evalTm] at hC hd ha hb hp
      rw [ha.1 γ hγ, hb.1 γ hγ, hp.1 γ hγ]
      have hdo := hd.1 (consEnv ((eval a).2.obj (subObj σ γ)) γ) (hγ.lift _)
      simp only [subObj_consEnv_lift] at hdo
      have hCro := (hC.2.2
        (consEnv (.idObj (idVal ((eval a).2.obj (subObj σ γ)))) (consEnv ((eval a).2.obj (subObj σ γ)) (consEnv ((eval a).2.obj (subObj σ γ)) γ)))
        (consEnv ((eval p).2.obj (subObj σ γ)) (consEnv ((eval b).2.obj (subObj σ γ)) (consEnv ((eval a).2.obj (subObj σ γ)) γ)))
        (consEnv ((eval p).2.obj (subObj σ γ)) (consEnv (unId ((eval p).2.obj (subObj σ γ))) (consEnv (idVal ((eval a).2.obj (subObj σ γ))) (idEnv γ))))
        (((hγ.lift _).lift _).lift _) (((hγ.lift _).lift _).lift _)).2.1
      simp only [subObj_consEnv_lift, subMor_consEnv_lift, subMor_idEnv hγ] at hCro
      rw [hdo, hCro]
    · dsimp only [substitute, evalTm, eval]
      dsimp only [evalTy, evalTm] at hC hd ha hb hp
      rw [ha.1 γ₁ hγ₁, ha.1 γ₂ hγ₂, ha.2 γ₁ γ₂ δ hγ₁ hγ₂, hb.1 γ₂ hγ₂, hp.1 γ₂ hγ₂]
      have hdm := hd.2
        (consEnv ((eval a).2.obj (subObj σ γ₁)) γ₁)
        (consEnv ((eval a).2.obj (subObj σ γ₂)) γ₂)
        (consEnv ((eval a).2.mor (subObj σ γ₁) (subObj σ γ₂) (subMor σ γ₁ γ₂ δ)) δ)
        (hγ₁.lift _) (hγ₂.lift _)
      simp only [subObj_consEnv_lift, subMor_consEnv_lift] at hdm
      have hCrm := (hC.2.2
        (consEnv (.idObj (idVal ((eval a).2.obj (subObj σ γ₂)))) (consEnv ((eval a).2.obj (subObj σ γ₂)) (consEnv ((eval a).2.obj (subObj σ γ₂)) γ₂)))
        (consEnv ((eval p).2.obj (subObj σ γ₂)) (consEnv ((eval b).2.obj (subObj σ γ₂)) (consEnv ((eval a).2.obj (subObj σ γ₂)) γ₂)))
        (consEnv ((eval p).2.obj (subObj σ γ₂)) (consEnv (unId ((eval p).2.obj (subObj σ γ₂))) (consEnv (idVal ((eval a).2.obj (subObj σ γ₂))) (idEnv γ₂))))
        (((hγ₂.lift _).lift _).lift _) (((hγ₂.lift _).lift _).lift _)).2.2.1
      simp only [subObj_consEnv_lift, subMor_consEnv_lift, subMor_idEnv hγ₂] at hCrm
      rw [hdm, hCrm]
  | .zero, σ, _ =>
    ⟨FamSubstAt.dflt σ, ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩
  | .succ n, σ, hσ => by
    have hn := (eval_substitute n hσ).2
    refine ⟨FamSubstAt.dflt σ, ⟨fun γ hγ => ?_, fun γ₁ γ₂ δ _ hγ₂ => ?_⟩⟩
    · dsimp only [substitute, evalTm, eval]
      rw [hn.1 γ hγ]
    · dsimp only [substitute, evalTm, eval]
      rw [hn.1 γ₂ hγ₂]
  | .natRec C z s n, σ, hσ => by
    have hz := (eval_substitute z hσ).2
    have hs := (eval_substitute s hσ.lift.lift).2
    have hn := (eval_substitute n hσ).2
    refine ⟨FamSubstAt.dflt σ, ⟨fun γ hγ => ?_, fun γ₁ γ₂ δ hγ₁ hγ₂ => ?_⟩⟩
    · dsimp only [substitute, evalTm, eval]
      rw [hn.1 γ hγ, natRecObj_subst hz hs hγ]
    · dsimp only [substitute, evalTm, eval]
      rw [hn.1 γ₂ hγ₂, natRecMor_subst hz hs hγ₁ hγ₂]

end HofmannStreicher1994.Repaired

/-! ## SemScope.lean -/

namespace HofmannStreicher1994.Repaired

theorem evalTy_of_isTm {e : Expr} (h : IsTm e) : evalTy e = dfltFam := by
  cases e <;> simp_all [IsTm, evalTy, eval]

theorem truncSub_tmOnly {k : Nat} {σ : Nat → Expr}
    (hσ : ∀ n, n < k → IsTm (σ n)) : SubstTmOnly (truncSub k σ) :=
  fun n => evalTy_of_isTm (truncSub_isTm hσ n)

theorem substitutionWf_truncSub_tmOnly {Γ Δ : Context} {σ : Nat → Expr}
    (hσ : SubstitutionWf Γ Δ σ) : SubstTmOnly (truncSub Γ.length σ) :=
  truncSub_tmOnly (fun n hn => (hσ.metadata n hn).2)

theorem truncSub_envOn {k : Nat} {σ : Nat → Expr} {γ : Env}
    (hσ : ∀ n, n < k →
      (evalTm (σ n)).mor γ γ (idEnv γ) = idVal ((evalTm (σ n)).obj γ)) :
    EnvOn (truncSub k σ) γ := by
  intro n
  by_cases hn : n < k
  · simpa only [truncSub, if_pos hn] using hσ n hn
  · simp [truncSub, hn, evalTm, eval, idVal]

theorem eval_substitute_scoped {e : Expr} {k : Nat} {σ : Nat → Expr}
    (he : Scoped k e) (hσ : ∀ n, n < k → IsTm (σ n)) :
    FamSubstAt (evalTy (substitute σ e)) (evalTy e) (truncSub k σ) ∧
    TmSubstAt (evalTm (substitute σ e)) (evalTm e) (truncSub k σ) := by
  rw [← he.truncSub]
  exact eval_substitute e (truncSub_tmOnly hσ)

end HofmannStreicher1994.Repaired

/-! ## SemCounterexample.lean -/

namespace HofmannStreicher1994.Repaired

noncomputable def CtxObj : Context → Env → Prop
  | [], _ => True
  | A :: Γ, γ => CtxObj Γ (renEnv Nat.succ γ) ∧
      (evalTy A).Obj (renEnv Nat.succ γ) (γ 0)

def witnessObj : Val := .pairObj .uCode .elObj
def witnessLoop (b : Bool) : Val := .idObj (.pairMor .uCode .uCode .uCode (.elMor b))

def diagonalEnv : Env :=
  consEnv (witnessLoop false) (consEnv (witnessLoop true)
    (consEnv witnessObj (fun _ => .dflt)))

def uipEnv : Env :=
  consEnv (witnessLoop false) (consEnv (witnessLoop true)
    (consEnv witnessObj (consEnv witnessObj (fun _ => .dflt))))

theorem counterexampleType_wf : TypeWf [] counterexampleType :=
  .sigma (.universe .nil) (.el (.var (n := 0) (A := .universe)
    (.cons .nil (.universe .nil)) rfl))

theorem diagonalEnv_valid : CtxObj (diagonalContext counterexampleType) diagonalEnv := by
  simp [CtxObj, diagonalContext, counterexampleType, diagonalEnv, witnessObj, witnessLoop,
    evalTy, eval, semSigma, semUniverse, semEl, semId, weaken, rename,
    consEnv, renEnv, idVal, eq_comm, and_assoc, exists_and_left]
  done

theorem diagonalConclusion_empty (v : Val) :
    ¬ (evalTy (diagonalConclusion counterexampleType)).Obj diagonalEnv v := by
  simp [diagonalConclusion, counterexampleType, diagonalEnv, witnessObj, witnessLoop,
    evalTy, eval, semSigma, semUniverse, semEl, semId, rename,
    consEnv, idEnv, idVal, sigMorX1, sigMorX2, sigMorP, sigMorQ, elCompVal]
  done

theorem uipEnv_valid : CtxObj (uipContext counterexampleType) uipEnv := by
  simp [CtxObj, uipContext, counterexampleType, uipEnv, witnessObj, witnessLoop,
    evalTy, eval, semSigma, semUniverse, semEl, semId, weaken, rename,
    consEnv, renEnv, idVal, eq_comm, and_assoc, exists_and_left]

theorem uipConclusion_empty (v : Val) :
    ¬ (evalTy (uipConclusion counterexampleType)).Obj uipEnv v := by
  simp [uipConclusion, counterexampleType, uipEnv, witnessObj, witnessLoop,
    evalTy, eval, semSigma, semUniverse, semEl, semId, rename,
    consEnv, idEnv, idVal, sigMorX1, sigMorX2, sigMorP, sigMorQ, elCompVal]

/-- The remaining semantic bridge, stated explicitly rather than assumed as an axiom. -/
def ObjectSoundness : Prop :=
  ∀ {Γ t A}, TermWf Γ t A → ∀ γ, CtxObj Γ γ → (evalTy A).Obj γ ((evalTm t).obj γ)

theorem uip_underivable_of_soundness (sound : ObjectSoundness) :
    TypeWf [] counterexampleType ∧
      (¬ ∃ t, TermWf (diagonalContext counterexampleType) t
        (diagonalConclusion counterexampleType)) ∧
      (¬ ∃ t, TermWf (uipContext counterexampleType) t
        (uipConclusion counterexampleType)) := by
  refine ⟨counterexampleType_wf, ?_, ?_⟩
  · exact fun ⟨t, ht⟩ => diagonalConclusion_empty _ (sound ht diagonalEnv diagonalEnv_valid)
  · exact fun ⟨t, ht⟩ => uipConclusion_empty _ (sound ht uipEnv uipEnv_valid)

end HofmannStreicher1994.Repaired

/-! ## SemLaws.lean -/

namespace HofmannStreicher1994.Repaired

/-- A vertical arrow, including the well-formedness of both endpoints. -/
abbrev FiberHom (A : SemFam) (γ : Env) (x y p : Val) : Prop := piDomMor A γ x y p

/-- The groupoid laws in one fiber. These are obligations, not assumed axioms. -/
structure FiberLaws (A : SemFam) (γ : Env) : Prop where
  id_hom {x} : A.Obj γ x → FiberHom A γ x x (idVal x)
  comp_hom {x y z p q} : FiberHom A γ x y p → FiberHom A γ y z q →
    FiberHom A γ x z (A.comp γ p q)
  inv_hom {x y p} : FiberHom A γ x y p → FiberHom A γ y x (A.inv γ p)
  id_comp {x y p} : FiberHom A γ x y p → A.comp γ (idVal x) p = p
  comp_id {x y p} : FiberHom A γ x y p → A.comp γ p (idVal y) = p
  assoc {w x y z p q r} : FiberHom A γ w x p → FiberHom A γ x y q →
    FiberHom A γ y z r → A.comp γ (A.comp γ p q) r = A.comp γ p (A.comp γ q r)
  inv_comp {x y p} : FiberHom A γ x y p → A.comp γ (A.inv γ p) p = idVal y
  comp_inv {x y p} : FiberHom A γ x y p → A.comp γ p (A.inv γ p) = idVal x

def conjugate (A : SemFam) (γ : Env) (a p b : Val) : Val :=
  A.comp γ (A.inv γ a) (A.comp γ p b)

theorem FiberLaws.conjugate_hom {A : SemFam} {γ : Env} (h : FiberLaws A γ)
    {x x' y y' a p b : Val} (ha : FiberHom A γ x x' a)
    (hp : FiberHom A γ x y p) (hb : FiberHom A γ y y' b) :
    FiberHom A γ x' y' (conjugate A γ a p b) :=
  h.comp_hom (h.inv_hom ha) (h.comp_hom hp hb)

theorem FiberLaws.conjugate_refl {A : SemFam} {γ : Env} (h : FiberLaws A γ)
    {x y a : Val} (ha : FiberHom A γ x y a) :
    conjugate A γ a (idVal x) a = idVal y := by
  unfold conjugate
  rw [h.id_comp ha, h.inv_comp ha]

theorem FiberLaws.unconjugate_conjugate {A : SemFam} {γ : Env} (h : FiberLaws A γ)
    {x x' y y' a p b : Val} (ha : FiberHom A γ x x' a)
    (hp : FiberHom A γ x y p) (hb : FiberHom A γ y y' b) :
    A.comp γ a (A.comp γ (conjugate A γ a p b) (A.inv γ b)) = p := by
  unfold conjugate
  rw [h.assoc (h.inv_hom ha) (h.comp_hom hp hb) (h.inv_hom hb),
    h.assoc hp hb (h.inv_hom hb), h.comp_inv hb, h.comp_id hp,
    ← h.assoc ha (h.inv_hom ha) hp, h.comp_inv ha, h.id_comp hp]

theorem FiberLaws.conjugate_unconjugate {A : SemFam} {γ : Env} (h : FiberLaws A γ)
    {x x' y y' a p b : Val} (ha : FiberHom A γ x x' a)
    (hp : FiberHom A γ x' y' p) (hb : FiberHom A γ y y' b) :
    conjugate A γ a (A.comp γ a (A.comp γ p (A.inv γ b))) b = p := by
  rw [conjugate, h.assoc ha (h.comp_hom hp (h.inv_hom hb)) hb,
    h.assoc hp (h.inv_hom hb) hb, h.inv_comp hb, h.comp_id hp,
    ← h.assoc (h.inv_hom ha) ha hp, h.inv_comp ha, h.id_comp hp]

theorem FiberLaws.inv_id {A : SemFam} {γ : Env} (h : FiberLaws A γ)
    {x : Val} (hx : A.Obj γ x) : A.inv γ (idVal x) = idVal x :=
  (h.comp_id (h.inv_hom (h.id_hom hx))).symm.trans (h.inv_comp (h.id_hom hx))

/-- Strict invertible transport between two fibers, including its relation to
the heterogeneous arrow predicate. The interpretation must establish these laws. -/
structure TransportLaws (A : SemFam) (γ₁ γ₂ δ : Env) : Prop where
  map_obj {x} : A.Obj γ₁ x → A.Obj γ₂ (A.reindexObj γ₁ γ₂ δ x)
  unmap_obj {x} : A.Obj γ₂ x → A.Obj γ₁ (A.unreindexObj γ₁ γ₂ δ x)
  map_hom {x y p} : FiberHom A γ₁ x y p →
    FiberHom A γ₂ (A.reindexObj γ₁ γ₂ δ x) (A.reindexObj γ₁ γ₂ δ y)
      (A.reindexMor γ₁ γ₂ δ p)
  unmap_hom {x y p} : FiberHom A γ₂ x y p →
    FiberHom A γ₁ (A.unreindexObj γ₁ γ₂ δ x) (A.unreindexObj γ₁ γ₂ δ y)
      (A.unreindexMor γ₁ γ₂ δ p)
  unmap_map_obj {x} : A.Obj γ₁ x →
    A.unreindexObj γ₁ γ₂ δ (A.reindexObj γ₁ γ₂ δ x) = x
  map_unmap_obj {x} : A.Obj γ₂ x →
    A.reindexObj γ₁ γ₂ δ (A.unreindexObj γ₁ γ₂ δ x) = x
  unmap_map_mor {x y p} : FiberHom A γ₁ x y p →
    A.unreindexMor γ₁ γ₂ δ (A.reindexMor γ₁ γ₂ δ p) = p
  map_unmap_mor {x y p} : FiberHom A γ₂ x y p →
    A.reindexMor γ₁ γ₂ δ (A.unreindexMor γ₁ γ₂ δ p) = p
  map_id {x} : A.Obj γ₁ x →
    A.reindexMor γ₁ γ₂ δ (idVal x) = idVal (A.reindexObj γ₁ γ₂ δ x)
  map_comp {x y z p q} : FiberHom A γ₁ x y p → FiberHom A γ₁ y z q →
    A.reindexMor γ₁ γ₂ δ (A.comp γ₁ p q) =
      A.comp γ₂ (A.reindexMor γ₁ γ₂ δ p) (A.reindexMor γ₁ γ₂ δ q)
  hom_iff {x y p} : A.Obj γ₁ x → A.Obj γ₂ y →
    (A.Hom γ₁ γ₂ δ x y p ↔
      A.Hom γ₂ γ₂ (idEnv γ₂) (A.reindexObj γ₁ γ₂ δ x) y p)

structure IdentityTransport (A : SemFam) (γ : Env) : Prop where
  obj {x} : A.Obj γ x → A.reindexObj γ γ (idEnv γ) x = x
  mor {x y p} : FiberHom A γ x y p → A.reindexMor γ γ (idEnv γ) p = p

theorem TransportLaws.unmap_hom_between {A : SemFam} {γ₁ γ₂ δ : Env}
    (tr : TransportLaws A γ₁ γ₂ δ) {x y p : Val}
    (hx : A.Obj γ₁ x) (hy : A.Obj γ₁ y)
    (hp : FiberHom A γ₂ (A.reindexObj γ₁ γ₂ δ x) (A.reindexObj γ₁ γ₂ δ y) p) :
    FiberHom A γ₁ x y (A.unreindexMor γ₁ γ₂ δ p) := by
  simpa only [tr.unmap_map_obj hx, tr.unmap_map_obj hy] using tr.unmap_hom hp

theorem TransportLaws.vertical {A : SemFam} {γ₁ γ₂ δ : Env}
    (tr : TransportLaws A γ₁ γ₂ δ) {x y p : Val} (hp : piHetMor A γ₁ γ₂ δ x y p) :
    FiberHom A γ₂ (A.reindexObj γ₁ γ₂ δ x) y p :=
  ⟨tr.map_obj hp.1, hp.2.1, (tr.hom_iff hp.1 hp.2.1).mp hp.2.2⟩

theorem TransportLaws.unmap_identity_obj {A : SemFam} {γ : Env}
    (tr : TransportLaws A γ γ (idEnv γ)) (hi : IdentityTransport A γ)
    {x : Val} (hx : A.Obj γ x) : A.unreindexObj γ γ (idEnv γ) x = x :=
  (congrArg (A.unreindexObj γ γ (idEnv γ)) (hi.obj hx)).symm.trans (tr.unmap_map_obj hx)

theorem TransportLaws.unmap_identity_mor {A : SemFam} {γ : Env}
    (tr : TransportLaws A γ γ (idEnv γ)) (hi : IdentityTransport A γ)
    {x y p : Val} (hp : FiberHom A γ x y p) : A.unreindexMor γ γ (idEnv γ) p = p :=
  (congrArg (A.unreindexMor γ γ (idEnv γ)) (hi.mor hp)).symm.trans (tr.unmap_map_mor hp)

theorem FiberLaws.inv_inv {A : SemFam} {γ : Env} (h : FiberLaws A γ)
    {x y p : Val} (hp : FiberHom A γ x y p) : A.inv γ (A.inv γ p) = p := by
  have hi := h.inv_hom hp
  have hii := h.inv_hom hi
  calc A.inv γ (A.inv γ p)
    _ = A.comp γ (A.inv γ (A.inv γ p)) (idVal y) := (h.comp_id hii).symm
    _ = A.comp γ (A.inv γ (A.inv γ p)) (A.comp γ (A.inv γ p) p) := by rw [h.inv_comp hp]
    _ = A.comp γ (A.comp γ (A.inv γ (A.inv γ p)) (A.inv γ p)) p := (h.assoc hii hi hp).symm
    _ = A.comp γ (idVal x) p := by rw [h.inv_comp hi]
    _ = p := h.id_comp hp

theorem FiberLaws.inv_eq_of_comp_eq_id {A : SemFam} {γ : Env} (h : FiberLaws A γ)
    {x y u v : Val} (hu : FiberHom A γ x y u) (hv : FiberHom A γ y x v)
    (huv : A.comp γ u v = idVal x) : A.inv γ u = v := by
  have hiu := h.inv_hom hu
  calc A.inv γ u
    _ = A.comp γ (A.inv γ u) (idVal x) := (h.comp_id hiu).symm
    _ = A.comp γ (A.inv γ u) (A.comp γ u v) := by rw [huv]
    _ = A.comp γ (A.comp γ (A.inv γ u) u) v := (h.assoc hiu hu hv).symm
    _ = A.comp γ (idVal y) v := by rw [h.inv_comp hu]
    _ = v := h.id_comp hv

theorem FiberLaws.inv_comp_rev {A : SemFam} {γ : Env} (h : FiberLaws A γ)
    {x y z p q : Val} (hp : FiberHom A γ x y p) (hq : FiberHom A γ y z q) :
    A.inv γ (A.comp γ p q) = A.comp γ (A.inv γ q) (A.inv γ p) := by
  have hpq := h.comp_hom hp hq
  have hipq := h.inv_hom hpq
  have hiq := h.inv_hom hq
  have hip := h.inv_hom hp
  have h1 : A.comp γ (A.comp γ p q) (A.comp γ (A.inv γ q) (A.inv γ p)) = idVal x := by
    rw [← h.assoc hpq hiq hip, h.assoc hp hq hiq, h.comp_inv hq, h.comp_id hp, h.comp_inv hp]
  calc A.inv γ (A.comp γ p q)
    _ = A.comp γ (A.inv γ (A.comp γ p q)) (idVal x) := (h.comp_id hipq).symm
    _ = A.comp γ (A.inv γ (A.comp γ p q))
          (A.comp γ (A.comp γ p q) (A.comp γ (A.inv γ q) (A.inv γ p))) := by rw [h1]
    _ = A.comp γ (A.comp γ (A.inv γ (A.comp γ p q)) (A.comp γ p q))
          (A.comp γ (A.inv γ q) (A.inv γ p)) := (h.assoc hipq hpq (h.comp_hom hiq hip)).symm
    _ = A.comp γ (idVal z) (A.comp γ (A.inv γ q) (A.inv γ p)) := by rw [h.inv_comp hpq]
    _ = A.comp γ (A.inv γ q) (A.inv γ p) := h.id_comp (h.comp_hom hiq hip)

theorem FiberLaws.conjugate_conjugate {A : SemFam} {γ : Env} (h : FiberLaws A γ)
    {x₀ x₁ x₂ y₀ y₁ y₂ a₁ a₂ p b₁ b₂ : Val}
    (ha₁ : FiberHom A γ x₀ x₁ a₁) (ha₂ : FiberHom A γ x₁ x₂ a₂)
    (hp : FiberHom A γ x₀ y₀ p)
    (hb₁ : FiberHom A γ y₀ y₁ b₁) (hb₂ : FiberHom A γ y₁ y₂ b₂) :
    conjugate A γ a₂ (conjugate A γ a₁ p b₁) b₂ =
      conjugate A γ (A.comp γ a₁ a₂) p (A.comp γ b₁ b₂) := by
  unfold conjugate
  rw [h.inv_comp_rev ha₁ ha₂,
    h.assoc (h.inv_hom ha₁) (h.comp_hom hp hb₁) hb₂,
    h.assoc hp hb₁ hb₂,
    h.assoc (h.inv_hom ha₂) (h.inv_hom ha₁) (h.comp_hom hp (h.comp_hom hb₁ hb₂))]

theorem TransportLaws.map_inv {A : SemFam} {γ₁ γ₂ δ : Env}
    (h₁ : FiberLaws A γ₁) (h₂ : FiberLaws A γ₂) (tr : TransportLaws A γ₁ γ₂ δ)
    {x y p : Val} (hp : FiberHom A γ₁ x y p) :
    A.reindexMor γ₁ γ₂ δ (A.inv γ₁ p) = A.inv γ₂ (A.reindexMor γ₁ γ₂ δ p) := by
  have hp' := tr.map_hom hp
  have hip' := tr.map_hom (h₁.inv_hom hp)
  have hcomp : A.comp γ₂ (A.reindexMor γ₁ γ₂ δ p) (A.reindexMor γ₁ γ₂ δ (A.inv γ₁ p)) =
      idVal (A.reindexObj γ₁ γ₂ δ x) := by
    rw [← tr.map_comp hp (h₁.inv_hom hp), h₁.comp_inv hp, tr.map_id hp.1]
  calc A.reindexMor γ₁ γ₂ δ (A.inv γ₁ p)
    _ = A.comp γ₂ (idVal (A.reindexObj γ₁ γ₂ δ y)) (A.reindexMor γ₁ γ₂ δ (A.inv γ₁ p)) :=
        (h₂.id_comp hip').symm
    _ = A.comp γ₂ (A.comp γ₂ (A.inv γ₂ (A.reindexMor γ₁ γ₂ δ p)) (A.reindexMor γ₁ γ₂ δ p))
          (A.reindexMor γ₁ γ₂ δ (A.inv γ₁ p)) := by rw [h₂.inv_comp hp']
    _ = A.comp γ₂ (A.inv γ₂ (A.reindexMor γ₁ γ₂ δ p))
          (A.comp γ₂ (A.reindexMor γ₁ γ₂ δ p) (A.reindexMor γ₁ γ₂ δ (A.inv γ₁ p))) :=
        h₂.assoc (h₂.inv_hom hp') hp' hip'
    _ = A.comp γ₂ (A.inv γ₂ (A.reindexMor γ₁ γ₂ δ p)) (idVal (A.reindexObj γ₁ γ₂ δ x)) := by
        rw [hcomp]
    _ = A.inv γ₂ (A.reindexMor γ₁ γ₂ δ p) := h₂.comp_id (h₂.inv_hom hp')

theorem TransportLaws.map_conjugate {A : SemFam} {γ₁ γ₂ δ : Env}
    (h₁ : FiberLaws A γ₁) (h₂ : FiberLaws A γ₂) (tr : TransportLaws A γ₁ γ₂ δ)
    {x x' y y' a p b : Val}
    (ha : FiberHom A γ₁ x x' a) (hp : FiberHom A γ₁ x y p) (hb : FiberHom A γ₁ y y' b) :
    A.reindexMor γ₁ γ₂ δ (conjugate A γ₁ a p b) =
      conjugate A γ₂ (A.reindexMor γ₁ γ₂ δ a) (A.reindexMor γ₁ γ₂ δ p)
        (A.reindexMor γ₁ γ₂ δ b) := by
  unfold conjugate
  rw [tr.map_comp (h₁.inv_hom ha) (h₁.comp_hom hp hb),
    tr.map_inv h₁ h₂ ha, tr.map_comp hp hb]

theorem TransportLaws.unmap_id {A : SemFam} {γ₁ γ₂ δ : Env}
    (h₁ : FiberLaws A γ₁) (tr : TransportLaws A γ₁ γ₂ δ)
    {x : Val} (hx : A.Obj γ₂ x) :
    A.unreindexMor γ₁ γ₂ δ (idVal x) = idVal (A.unreindexObj γ₁ γ₂ δ x) := by
  have hx₁ := tr.unmap_obj hx
  have h1 := tr.map_id hx₁
  rw [tr.map_unmap_obj hx] at h1
  exact (congrArg (A.unreindexMor γ₁ γ₂ δ) h1).symm.trans (tr.unmap_map_mor (h₁.id_hom hx₁))

theorem TransportLaws.unmap_comp {A : SemFam} {γ₁ γ₂ δ : Env}
    (h₁ : FiberLaws A γ₁) (tr : TransportLaws A γ₁ γ₂ δ)
    {x y z p q : Val} (hp : FiberHom A γ₂ x y p) (hq : FiberHom A γ₂ y z q) :
    A.unreindexMor γ₁ γ₂ δ (A.comp γ₂ p q) =
      A.comp γ₁ (A.unreindexMor γ₁ γ₂ δ p) (A.unreindexMor γ₁ γ₂ δ q) := by
  have hp₁ := tr.unmap_hom hp
  have hq₁ := tr.unmap_hom hq
  have h1 := tr.map_comp hp₁ hq₁
  rw [tr.map_unmap_mor hp, tr.map_unmap_mor hq] at h1
  exact (congrArg (A.unreindexMor γ₁ γ₂ δ) h1).symm.trans
    (tr.unmap_map_mor (h₁.comp_hom hp₁ hq₁))

theorem TransportLaws.unmap_inv {A : SemFam} {γ₁ γ₂ δ : Env}
    (h₁ : FiberLaws A γ₁) (h₂ : FiberLaws A γ₂) (tr : TransportLaws A γ₁ γ₂ δ)
    {x y p : Val} (hp : FiberHom A γ₂ x y p) :
    A.unreindexMor γ₁ γ₂ δ (A.inv γ₂ p) = A.inv γ₁ (A.unreindexMor γ₁ γ₂ δ p) := by
  have hp₁ := tr.unmap_hom hp
  have h1 := tr.map_inv h₁ h₂ hp₁
  rw [tr.map_unmap_mor hp] at h1
  exact (congrArg (A.unreindexMor γ₁ γ₂ δ) h1).symm.trans
    (tr.unmap_map_mor (h₁.inv_hom hp₁))

structure RankLaws (A : SemFam) (γ : Env) : Prop where
  obj_rank {x} : A.Obj γ x → RankLt A.lvl x
  hom_rank {x y p} : FiberHom A γ x y p → RankLt A.lvl p

theorem RankLaws.het_hom_rank {A : SemFam} {γ₁ γ₂ δ : Env}
    (rk₂ : RankLaws A γ₂) (tr : TransportLaws A γ₁ γ₂ δ)
    {x y p : Val} (hp : piHetMor A γ₁ γ₂ δ x y p) : RankLt A.lvl p :=
  rk₂.hom_rank (tr.vertical hp)

structure CompTransport (A : SemFam) (γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ : Env) : Prop where
  comp_obj {x} : A.Obj γ₁ x →
    A.reindexObj γ₂ γ₃ δ₂₃ (A.reindexObj γ₁ γ₂ δ₁₂ x) = A.reindexObj γ₁ γ₃ δ₁₃ x
  comp_mor {x y p} : FiberHom A γ₁ x y p →
    A.reindexMor γ₂ γ₃ δ₂₃ (A.reindexMor γ₁ γ₂ δ₁₂ p) = A.reindexMor γ₁ γ₃ δ₁₃ p

theorem CompTransport.uncomp_obj {A : SemFam} {γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ : Env}
    (tr₁₂ : TransportLaws A γ₁ γ₂ δ₁₂) (tr₂₃ : TransportLaws A γ₂ γ₃ δ₂₃)
    (tr₁₃ : TransportLaws A γ₁ γ₃ δ₁₃)
    (ct : CompTransport A γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃)
    {z : Val} (hz : A.Obj γ₃ z) :
    A.unreindexObj γ₁ γ₂ δ₁₂ (A.unreindexObj γ₂ γ₃ δ₂₃ z) =
      A.unreindexObj γ₁ γ₃ δ₁₃ z := by
  have hy := tr₂₃.unmap_obj hz
  have hx := tr₁₂.unmap_obj hy
  have h1 : A.reindexObj γ₁ γ₃ δ₁₃ (A.unreindexObj γ₁ γ₂ δ₁₂ (A.unreindexObj γ₂ γ₃ δ₂₃ z)) = z := by
    rw [← ct.comp_obj hx, tr₁₂.map_unmap_obj hy, tr₂₃.map_unmap_obj hz]
  exact (tr₁₃.unmap_map_obj hx).symm.trans (congrArg (A.unreindexObj γ₁ γ₃ δ₁₃) h1)

theorem CompTransport.uncomp_mor {A : SemFam} {γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ : Env}
    (tr₁₂ : TransportLaws A γ₁ γ₂ δ₁₂) (tr₂₃ : TransportLaws A γ₂ γ₃ δ₂₃)
    (tr₁₃ : TransportLaws A γ₁ γ₃ δ₁₃)
    (ct : CompTransport A γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃)
    {x y p : Val} (hp : FiberHom A γ₃ x y p) :
    A.unreindexMor γ₁ γ₂ δ₁₂ (A.unreindexMor γ₂ γ₃ δ₂₃ p) =
      A.unreindexMor γ₁ γ₃ δ₁₃ p := by
  have hp₂ := tr₂₃.unmap_hom hp
  have hp₁ := tr₁₂.unmap_hom hp₂
  have h1 : A.reindexMor γ₁ γ₃ δ₁₃ (A.unreindexMor γ₁ γ₂ δ₁₂ (A.unreindexMor γ₂ γ₃ δ₂₃ p)) = p := by
    rw [← ct.comp_mor hp₁, tr₁₂.map_unmap_mor hp₂, tr₂₃.map_unmap_mor hp]
  exact (tr₁₃.unmap_map_mor hp₁).symm.trans (congrArg (A.unreindexMor γ₁ γ₃ δ₁₃) h1)

end HofmannStreicher1994.Repaired

/-! ## SemBaseLaws.lean -/

namespace HofmannStreicher1994.Repaired

theorem semEl_fiber_laws (γ : Env) : FiberLaws semEl γ := by
  constructor
  all_goals simp [FiberHom, piDomMor, piHetMor, semEl, idVal, elCompVal]
  all_goals grind only [idVal]

theorem semUniverse_fiber_laws (γ : Env) : FiberLaws semUniverse γ := by
  constructor
  all_goals grind only [semUniverse, idVal]

theorem semNat_fiber_laws (γ : Env) : FiberLaws semNat γ := by
  constructor
  all_goals grind only [semNat, idVal]

theorem semUniverse_identity_transport (γ : Env) : IdentityTransport semUniverse γ where
  obj hx := hx.symm
  mor hp := hp.2.2.2.2.symm

theorem semEl_identity_transport (γ : Env) : IdentityTransport semEl γ where
  obj hx := hx.symm
  mor _ := rfl

theorem semNat_identity_transport (γ : Env) : IdentityTransport semNat γ where
  obj _ := rfl
  mor _ := rfl

theorem semUniverse_transport_laws (γ₁ γ₂ δ : Env) : TransportLaws semUniverse γ₁ γ₂ δ where
  map_obj _ := rfl
  unmap_obj _ := rfl
  map_hom _ := ⟨rfl, rfl, rfl, rfl, rfl⟩
  unmap_hom _ := ⟨rfl, rfl, rfl, rfl, rfl⟩
  unmap_map_obj hx := hx.symm
  map_unmap_obj hx := hx.symm
  unmap_map_mor hp := hp.2.2.2.2.symm
  map_unmap_mor hp := hp.2.2.2.2.symm
  map_id _ := rfl
  map_comp _ _ := rfl
  hom_iff hx _ := ⟨fun hp => ⟨rfl, hp.2⟩, fun hp => ⟨hx, hp.2⟩⟩

theorem semEl_transport_laws (γ₁ γ₂ δ : Env) : TransportLaws semEl γ₁ γ₂ δ where
  map_obj _ := rfl
  unmap_obj _ := rfl
  map_hom hp := ⟨rfl, rfl, rfl, rfl, hp.2.2.2.2⟩
  unmap_hom hp := ⟨rfl, rfl, rfl, rfl, hp.2.2.2.2⟩
  unmap_map_obj hx := hx.symm
  map_unmap_obj hx := hx.symm
  unmap_map_mor _ := rfl
  map_unmap_mor _ := rfl
  map_id hx := congrArg idVal hx
  map_comp _ _ := rfl
  hom_iff hx _ := ⟨fun hp => ⟨rfl, hp.2⟩, fun hp => ⟨hx, hp.2⟩⟩

theorem semNat_transport_laws (γ₁ γ₂ δ : Env) : TransportLaws semNat γ₁ γ₂ δ where
  map_obj hx := hx
  unmap_obj hx := hx
  map_hom hp := hp
  unmap_hom hp := hp
  unmap_map_obj _ := rfl
  map_unmap_obj _ := rfl
  unmap_map_mor _ := rfl
  map_unmap_mor _ := rfl
  map_id _ := rfl
  map_comp _ _ := rfl
  hom_iff _ _ := Iff.rfl

theorem semUniverse_rank_laws (γ : Env) : RankLaws semUniverse γ where
  obj_rank hx := hx ▸ trivial
  hom_rank hp := hp.2.2.2.2 ▸ trivial

theorem semEl_rank_laws (γ : Env) : RankLaws semEl γ where
  obj_rank hx := hx ▸ trivial
  hom_rank hp := by
    rcases hp.2.2.2.2 with ⟨b, rfl⟩
    trivial

theorem semNat_rank_laws (γ : Env) : RankLaws semNat γ where
  obj_rank hx := by
    rcases hx with ⟨k, rfl⟩
    trivial
  hom_rank hp := by
    rcases hp.2.2 with ⟨k, _, _, rfl⟩
    trivial

theorem semUniverse_comp_transport (γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ : Env) :
    CompTransport semUniverse γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ where
  comp_obj _ := rfl
  comp_mor _ := rfl

theorem semEl_comp_transport (γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ : Env) :
    CompTransport semEl γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ where
  comp_obj _ := rfl
  comp_mor _ := rfl

theorem semNat_comp_transport (γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ : Env) :
    CompTransport semNat γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ where
  comp_obj _ := rfl
  comp_mor _ := rfl

end HofmannStreicher1994.Repaired

/-! ## SemIdLaws.lean -/

namespace HofmannStreicher1994.Repaired

/-- Object typing and the identity equation for a semantic term at one environment. -/
structure TermAt (A : SemFam) (a : SemTm) (γ : Env) : Prop where
  obj : A.Obj γ (a.obj γ)
  id : a.mor γ γ (idEnv γ) = idVal (a.obj γ)

/-- Typed endpoints and action of a semantic term along one environment arrow. -/
abbrev TermAlong (A : SemFam) (a : SemTm) (γ₁ γ₂ δ : Env) : Prop :=
  piHetMor A γ₁ γ₂ δ (a.obj γ₁) (a.obj γ₂) (a.mor γ₁ γ₂ δ)

theorem TermAlong.vertical {A : SemFam} {a : SemTm} {γ₁ γ₂ δ : Env}
    (tr : TransportLaws A γ₁ γ₂ δ) (ha : TermAlong A a γ₁ γ₂ δ) :
    FiberHom A γ₂ (A.reindexObj γ₁ γ₂ δ (a.obj γ₁)) (a.obj γ₂)
      (a.mor γ₁ γ₂ δ) :=
  ⟨tr.map_obj ha.1, ha.2.1, (tr.hom_iff ha.1 ha.2.1).mp ha.2.2⟩

theorem semId_identity_obj {A : SemFam} {a b : SemTm} {γ : Env}
    (h : FiberLaws A γ) (hi : IdentityTransport A γ)
    (ha : TermAt A a γ) (hb : TermAt A b γ)
    {x : Val} (hx : (semId A a b).Obj γ x) :
    (semId A a b).reindexObj γ γ (idEnv γ) x = x := by
  rcases hx with ⟨p, rfl, hp⟩
  simp only [semId, unId, ha.id, hb.id, hi.mor ⟨ha.obj, hb.obj, hp⟩,
    h.inv_id ha.obj, h.comp_id ⟨ha.obj, hb.obj, hp⟩, h.id_comp ⟨ha.obj, hb.obj, hp⟩]

theorem semId_hom_iff {A : SemFam} {a b : SemTm} {γ : Env}
    (h : FiberLaws A γ) (hi : IdentityTransport A γ)
    (ha : TermAt A a γ) (hb : TermAt A b γ)
    {x y q : Val} (hx : (semId A a b).Obj γ x) :
    (semId A a b).Hom γ γ (idEnv γ) x y q ↔ y = x ∧ q = y := by
  change (y = (semId A a b).reindexObj γ γ (idEnv γ) x ∧
    q = y ∧ (semId A a b).Obj γ x) ↔ _
  rw [semId_identity_obj h hi ha hb hx, and_iff_left hx]

theorem semId_idVal {A : SemFam} {a b : SemTm} {γ : Env} {x : Val}
    (hx : (semId A a b).Obj γ x) : idVal x = x := by
  rcases hx with ⟨p, rfl, _⟩
  rfl

theorem semId_fiber_hom_iff {A : SemFam} {a b : SemTm} {γ : Env}
    (h : FiberLaws A γ) (hi : IdentityTransport A γ)
    (ha : TermAt A a γ) (hb : TermAt A b γ) {x y q : Val} :
    FiberHom (semId A a b) γ x y q ↔ (semId A a b).Obj γ x ∧ y = x ∧ q = x :=
  ⟨fun hp =>
    let hh := (semId_hom_iff h hi ha hb hp.1).mp hp.2.2
    ⟨hp.1, hh.1, hh.2.trans hh.1⟩,
   fun hp => ⟨hp.1, hp.2.1.symm ▸ hp.1,
     (semId_hom_iff h hi ha hb hp.1).mpr
       ⟨hp.2.1, hp.2.2.trans hp.2.1.symm⟩⟩⟩

theorem semId_fiber_laws {A : SemFam} {a b : SemTm} {γ : Env}
    (h : FiberLaws A γ) (hi : IdentityTransport A γ)
    (ha : TermAt A a γ) (hb : TermAt A b γ) :
    FiberLaws (semId A a b) γ := by
  constructor
  all_goals simp only [semId_fiber_hom_iff h hi ha hb]
  all_goals grind only [semId_idVal, semId]

theorem semId_identity_transport {A : SemFam} {a b : SemTm} {γ : Env}
    (h : FiberLaws A γ) (hi : IdentityTransport A γ)
    (ha : TermAt A a γ) (hb : TermAt A b γ) :
    IdentityTransport (semId A a b) γ where
  obj := semId_identity_obj h hi ha hb
  mor hp :=
    let hq := (semId_fiber_hom_iff h hi ha hb).mp hp
    semId_identity_obj h hi ha hb (hq.2.2.symm ▸ hq.1)

theorem semId_map_obj {A : SemFam} {a b : SemTm} {γ₁ γ₂ δ : Env}
    (h : FiberLaws A γ₂) (tr : TransportLaws A γ₁ γ₂ δ)
    (ha : TermAlong A a γ₁ γ₂ δ) (hb : TermAlong A b γ₁ γ₂ δ)
    {x : Val} (hx : (semId A a b).Obj γ₁ x) :
    (semId A a b).Obj γ₂ ((semId A a b).reindexObj γ₁ γ₂ δ x) := by
  rcases hx with ⟨p, rfl, hp⟩
  exact ⟨_, rfl, (h.conjugate_hom (ha.vertical tr)
    (tr.map_hom ⟨ha.1, hb.1, hp⟩) (hb.vertical tr)).2.2⟩

theorem semId_unmap_obj {A : SemFam} {a b : SemTm} {γ₁ γ₂ δ : Env}
    (h : FiberLaws A γ₂) (tr : TransportLaws A γ₁ γ₂ δ)
    (ha : TermAlong A a γ₁ γ₂ δ) (hb : TermAlong A b γ₁ γ₂ δ)
    {x : Val} (hx : (semId A a b).Obj γ₂ x) :
    (semId A a b).Obj γ₁ ((semId A a b).unreindexObj γ₁ γ₂ δ x) := by
  rcases hx with ⟨p, rfl, hp⟩
  exact ⟨_, rfl, (tr.unmap_hom_between ha.1 hb.1
    (h.comp_hom (ha.vertical tr)
      (h.comp_hom ⟨ha.2.1, hb.2.1, hp⟩ (h.inv_hom (hb.vertical tr))))).2.2⟩

theorem semId_unmap_map_obj {A : SemFam} {a b : SemTm} {γ₁ γ₂ δ : Env}
    (h : FiberLaws A γ₂) (tr : TransportLaws A γ₁ γ₂ δ)
    (ha : TermAlong A a γ₁ γ₂ δ) (hb : TermAlong A b γ₁ γ₂ δ)
    {x : Val} (hx : (semId A a b).Obj γ₁ x) :
    (semId A a b).unreindexObj γ₁ γ₂ δ
      ((semId A a b).reindexObj γ₁ γ₂ δ x) = x := by
  rcases hx with ⟨p, rfl, hp⟩
  exact congrArg Tree.idObj
    ((congrArg (A.unreindexMor γ₁ γ₂ δ)
      (h.unconjugate_conjugate (ha.vertical tr)
        (tr.map_hom ⟨ha.1, hb.1, hp⟩) (hb.vertical tr))).trans
      (tr.unmap_map_mor ⟨ha.1, hb.1, hp⟩))

theorem semId_map_unmap_obj {A : SemFam} {a b : SemTm} {γ₁ γ₂ δ : Env}
    (h : FiberLaws A γ₂) (tr : TransportLaws A γ₁ γ₂ δ)
    (ha : TermAlong A a γ₁ γ₂ δ) (hb : TermAlong A b γ₁ γ₂ δ)
    {x : Val} (hx : (semId A a b).Obj γ₂ x) :
    (semId A a b).reindexObj γ₁ γ₂ δ
      ((semId A a b).unreindexObj γ₁ γ₂ δ x) = x := by
  rcases hx with ⟨p, rfl, hp⟩
  exact congrArg Tree.idObj
    ((congrArg (fun q => conjugate A γ₂ (a.mor γ₁ γ₂ δ) q (b.mor γ₁ γ₂ δ))
      (tr.map_unmap_mor (h.comp_hom (ha.vertical tr)
        (h.comp_hom ⟨ha.2.1, hb.2.1, hp⟩ (h.inv_hom (hb.vertical tr)))))).trans
      (h.conjugate_unconjugate (ha.vertical tr) ⟨ha.2.1, hb.2.1, hp⟩ (hb.vertical tr)))

theorem semId_het_hom_iff {A : SemFam} {a b : SemTm} {γ₁ γ₂ δ : Env}
    {x y q : Val} (hx : (semId A a b).Obj γ₁ x) :
    (semId A a b).Hom γ₁ γ₂ δ x y q ↔
      y = (semId A a b).reindexObj γ₁ γ₂ δ x ∧ q = y :=
  ⟨fun hp => ⟨hp.1, hp.2.1⟩, fun hp => ⟨hp.1, hp.2, hx⟩⟩

theorem semId_transport_laws {A : SemFam} {a b : SemTm} {γ₁ γ₂ δ : Env}
    (h₁ : FiberLaws A γ₁) (h₂ : FiberLaws A γ₂)
    (hi₁ : IdentityTransport A γ₁) (hi₂ : IdentityTransport A γ₂)
    (ha₁ : TermAt A a γ₁) (hb₁ : TermAt A b γ₁)
    (ha₂ : TermAt A a γ₂) (hb₂ : TermAt A b γ₂)
    (tr : TransportLaws A γ₁ γ₂ δ)
    (ha : TermAlong A a γ₁ γ₂ δ) (hb : TermAlong A b γ₁ γ₂ δ) :
    TransportLaws (semId A a b) γ₁ γ₂ δ where
  map_obj := semId_map_obj h₂ tr ha hb
  unmap_obj := semId_unmap_obj h₂ tr ha hb
  map_hom hp :=
    let hq := (semId_fiber_hom_iff h₁ hi₁ ha₁ hb₁).mp hp
    (semId_fiber_hom_iff h₂ hi₂ ha₂ hb₂).mpr
      ⟨semId_map_obj h₂ tr ha hb hq.1,
        congrArg ((semId A a b).reindexObj γ₁ γ₂ δ) hq.2.1,
        congrArg ((semId A a b).reindexObj γ₁ γ₂ δ) hq.2.2⟩
  unmap_hom hp :=
    let hq := (semId_fiber_hom_iff h₂ hi₂ ha₂ hb₂).mp hp
    (semId_fiber_hom_iff h₁ hi₁ ha₁ hb₁).mpr
      ⟨semId_unmap_obj h₂ tr ha hb hq.1,
        congrArg ((semId A a b).unreindexObj γ₁ γ₂ δ) hq.2.1,
        congrArg ((semId A a b).unreindexObj γ₁ γ₂ δ) hq.2.2⟩
  unmap_map_obj := semId_unmap_map_obj h₂ tr ha hb
  map_unmap_obj := semId_map_unmap_obj h₂ tr ha hb
  unmap_map_mor hp :=
    let hq := (semId_fiber_hom_iff h₁ hi₁ ha₁ hb₁).mp hp
    semId_unmap_map_obj h₂ tr ha hb (hq.2.2.symm ▸ hq.1)
  map_unmap_mor hp :=
    let hq := (semId_fiber_hom_iff h₂ hi₂ ha₂ hb₂).mp hp
    semId_map_unmap_obj h₂ tr ha hb (hq.2.2.symm ▸ hq.1)
  map_id hx :=
    (congrArg ((semId A a b).reindexMor γ₁ γ₂ δ) (semId_idVal hx)).trans
      (semId_idVal (semId_map_obj h₂ tr ha hb hx)).symm
  map_comp _ _ := rfl
  hom_iff hx _ :=
    (semId_het_hom_iff hx).trans
      (semId_hom_iff h₂ hi₂ ha₂ hb₂ (semId_map_obj h₂ tr ha hb hx)).symm

theorem semId_rank_laws {A : SemFam} {a b : SemTm} {γ : Env}
    (h : FiberLaws A γ) (hi : IdentityTransport A γ) (rk : RankLaws A γ)
    (ha : TermAt A a γ) (hb : TermAt A b γ) :
    RankLaws (semId A a b) γ where
  obj_rank hx := by
    rcases hx with ⟨p, rfl, hp⟩
    change RankLt A.lvl p
    exact rk.hom_rank ⟨ha.obj, hb.obj, hp⟩
  hom_rank hp := by
    have hq := (semId_fiber_hom_iff h hi ha hb).mp hp
    rcases hq.1 with ⟨p, hxp, hpA⟩
    rw [hq.2.2, hxp]
    change RankLt A.lvl p
    exact rk.hom_rank ⟨ha.obj, hb.obj, hpA⟩

theorem semId_comp_obj {A : SemFam} {a b : SemTm} {γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ : Env}
    (h₂ : FiberLaws A γ₂) (h₃ : FiberLaws A γ₃)
    (tr₁₂ : TransportLaws A γ₁ γ₂ δ₁₂) (tr₂₃ : TransportLaws A γ₂ γ₃ δ₂₃)
    (ctA : CompTransport A γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃)
    (ha₁₂ : TermAlong A a γ₁ γ₂ δ₁₂) (ha₂₃ : TermAlong A a γ₂ γ₃ δ₂₃)
    (hb₁₂ : TermAlong A b γ₁ γ₂ δ₁₂) (hb₂₃ : TermAlong A b γ₂ γ₃ δ₂₃)
    (ha_comp : a.mor γ₁ γ₃ δ₁₃ =
      A.comp γ₃ (A.reindexMor γ₂ γ₃ δ₂₃ (a.mor γ₁ γ₂ δ₁₂)) (a.mor γ₂ γ₃ δ₂₃))
    (hb_comp : b.mor γ₁ γ₃ δ₁₃ =
      A.comp γ₃ (A.reindexMor γ₂ γ₃ δ₂₃ (b.mor γ₁ γ₂ δ₁₂)) (b.mor γ₂ γ₃ δ₂₃))
    {x : Val} (hx : (semId A a b).Obj γ₁ x) :
    (semId A a b).reindexObj γ₂ γ₃ δ₂₃ ((semId A a b).reindexObj γ₁ γ₂ δ₁₂ x) =
      (semId A a b).reindexObj γ₁ γ₃ δ₁₃ x := by
  rcases hx with ⟨p, rfl, hp⟩
  have hp₁ : FiberHom A γ₁ (a.obj γ₁) (b.obj γ₁) p := ⟨ha₁₂.1, hb₁₂.1, hp⟩
  have ha₁₂v := ha₁₂.vertical tr₁₂
  have hb₁₂v := hb₁₂.vertical tr₁₂
  have ha₂₃v := ha₂₃.vertical tr₂₃
  have hb₂₃v := hb₂₃.vertical tr₂₃
  have hp₂ := tr₁₂.map_hom hp₁
  have ha₁₂v' : FiberHom A γ₃ (A.reindexObj γ₁ γ₃ δ₁₃ (a.obj γ₁))
      (A.reindexObj γ₂ γ₃ δ₂₃ (a.obj γ₂)) (A.reindexMor γ₂ γ₃ δ₂₃ (a.mor γ₁ γ₂ δ₁₂)) := by
    simpa only [ctA.comp_obj ha₁₂.1] using tr₂₃.map_hom ha₁₂v
  have hb₁₂v' : FiberHom A γ₃ (A.reindexObj γ₁ γ₃ δ₁₃ (b.obj γ₁))
      (A.reindexObj γ₂ γ₃ δ₂₃ (b.obj γ₂)) (A.reindexMor γ₂ γ₃ δ₂₃ (b.mor γ₁ γ₂ δ₁₂)) := by
    simpa only [ctA.comp_obj hb₁₂.1] using tr₂₃.map_hom hb₁₂v
  have hp₃ : FiberHom A γ₃ (A.reindexObj γ₁ γ₃ δ₁₃ (a.obj γ₁))
      (A.reindexObj γ₁ γ₃ δ₁₃ (b.obj γ₁)) (A.reindexMor γ₁ γ₃ δ₁₃ p) := by
    simpa only [ctA.comp_obj ha₁₂.1, ctA.comp_obj hb₁₂.1, ctA.comp_mor hp₁] using tr₂₃.map_hom hp₂
  dsimp only [semId, unId]
  apply congrArg Tree.idObj
  change conjugate A γ₃ (a.mor γ₂ γ₃ δ₂₃)
      (A.reindexMor γ₂ γ₃ δ₂₃ (conjugate A γ₂ (a.mor γ₁ γ₂ δ₁₂) (A.reindexMor γ₁ γ₂ δ₁₂ p) (b.mor γ₁ γ₂ δ₁₂)))
      (b.mor γ₂ γ₃ δ₂₃) =
    conjugate A γ₃ (a.mor γ₁ γ₃ δ₁₃) (A.reindexMor γ₁ γ₃ δ₁₃ p) (b.mor γ₁ γ₃ δ₁₃)
  rw [tr₂₃.map_conjugate h₂ h₃ ha₁₂v hp₂ hb₁₂v, ctA.comp_mor hp₁,
    h₃.conjugate_conjugate ha₁₂v' ha₂₃v hp₃ hb₁₂v' hb₂₃v, ← ha_comp, ← hb_comp]

theorem semId_comp_transport {A : SemFam} {a b : SemTm} {γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ : Env}
    (h₁ : FiberLaws A γ₁) (h₂ : FiberLaws A γ₂) (h₃ : FiberLaws A γ₃)
    (hi₁ : IdentityTransport A γ₁)
    (ha₁ : TermAt A a γ₁) (hb₁ : TermAt A b γ₁)
    (tr₁₂ : TransportLaws A γ₁ γ₂ δ₁₂) (tr₂₃ : TransportLaws A γ₂ γ₃ δ₂₃)
    (ctA : CompTransport A γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃)
    (ha₁₂ : TermAlong A a γ₁ γ₂ δ₁₂) (ha₂₃ : TermAlong A a γ₂ γ₃ δ₂₃)
    (hb₁₂ : TermAlong A b γ₁ γ₂ δ₁₂) (hb₂₃ : TermAlong A b γ₂ γ₃ δ₂₃)
    (ha_comp : a.mor γ₁ γ₃ δ₁₃ =
      A.comp γ₃ (A.reindexMor γ₂ γ₃ δ₂₃ (a.mor γ₁ γ₂ δ₁₂)) (a.mor γ₂ γ₃ δ₂₃))
    (hb_comp : b.mor γ₁ γ₃ δ₁₃ =
      A.comp γ₃ (A.reindexMor γ₂ γ₃ δ₂₃ (b.mor γ₁ γ₂ δ₁₂)) (b.mor γ₂ γ₃ δ₂₃)) :
    CompTransport (semId A a b) γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ where
  comp_obj := semId_comp_obj h₂ h₃ tr₁₂ tr₂₃ ctA ha₁₂ ha₂₃ hb₁₂ hb₂₃ ha_comp hb_comp
  comp_mor hp :=
    let hq := (semId_fiber_hom_iff h₁ hi₁ ha₁ hb₁).mp hp
    semId_comp_obj h₂ h₃ tr₁₂ tr₂₃ ctA ha₁₂ ha₂₃ hb₁₂ hb₂₃ ha_comp hb_comp (hq.2.2.symm ▸ hq.1)

end HofmannStreicher1994.Repaired

/-! ## SemSigmaLaws.lean -/

namespace HofmannStreicher1994.Repaired

theorem semSigma_het_hom_iff {A B : SemFam} {γ₁ γ₂ δ : Env} {z₁ z₂ m : Val} :
    piHetMor (semSigma A B) γ₁ γ₂ δ z₁ z₂ m ↔
      ∃ x₁ y₁ x₂ y₂ p q,
        z₁ = .pairObj x₁ y₁ ∧ z₂ = .pairObj x₂ y₂ ∧
        m = .pairMor (A.reindexObj γ₁ γ₂ δ x₁) x₂ p q ∧
        piHetMor A γ₁ γ₂ δ x₁ x₂ p ∧
        piHetMor B (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) y₁ y₂ q := by
  constructor
  · rintro ⟨_, _, x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hx₁, hx₂, hy₁, hy₂, hp, hq⟩
    exact ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, ⟨hx₁, hx₂, hp⟩, ⟨hy₁, hy₂, hq⟩⟩
  · rintro ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, ⟨hx₁, hx₂, hp⟩, ⟨hy₁, hy₂, hq⟩⟩
    exact ⟨⟨x₁, y₁, rfl, hx₁, hy₁⟩, ⟨x₂, y₂, rfl, hx₂, hy₂⟩,
      x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hx₁, hx₂, hy₁, hy₂, hp, hq⟩

theorem semSigma_fiber_hom_iff {A B : SemFam} {γ : Env}
    (hiA : IdentityTransport A γ) {z₁ z₂ m : Val} :
    FiberHom (semSigma A B) γ z₁ z₂ m ↔
      ∃ x₁ y₁ x₂ y₂ p q,
        z₁ = .pairObj x₁ y₁ ∧ z₂ = .pairObj x₂ y₂ ∧
        m = .pairMor x₁ x₂ p q ∧
        FiberHom A γ x₁ x₂ p ∧
        piHetMor B (consEnv x₁ γ) (consEnv x₂ γ) (consEnv p (idEnv γ)) y₁ y₂ q := by
  unfold FiberHom piDomMor
  rw [semSigma_het_hom_iff]
  constructor
  · rintro ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
    rw [hiA.obj hp.1]
    exact ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
  · rintro ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
    refine ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, ?_, hp, hq⟩
    rw [hiA.obj hp.1]

theorem semSigma_identity_transport {A B : SemFam} {γ : Env}
    (hiA : IdentityTransport A γ)
    (hiB : ∀ {x}, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ {x₁ x₂ p}, FiberHom A γ x₁ x₂ p →
      TransportLaws B (consEnv x₁ γ) (consEnv x₂ γ) (consEnv p (idEnv γ))) :
    IdentityTransport (semSigma A B) γ where
  obj hz := by
    rcases hz with ⟨x, y, rfl, hx, hy⟩
    dsimp only [semSigma, sigFst, sigSnd]
    rw [hiA.obj hx, ← idEnv_consEnv, (hiB hx).obj hy]
  mor hm := by
    rcases (semSigma_fiber_hom_iff hiA).mp hm with
      ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
    have hqv := (trB hp).vertical hq
    dsimp only [semSigma, sigMorX1, sigMorX2, sigMorP, sigMorQ]
    rw [hiA.obj hp.1, hiA.obj hp.2.1, hiA.mor hp,
      ← idEnv_consEnv, (hiB hp.2.1).mor hqv]

theorem semSigma_rank_laws {A B : SemFam} {γ : Env}
    (hiA : IdentityTransport A γ) (rkA : RankLaws A γ)
    (rkB : ∀ {x}, A.Obj γ x → RankLaws B (consEnv x γ))
    (trB : ∀ {x₁ x₂ p}, FiberHom A γ x₁ x₂ p →
      TransportLaws B (consEnv x₁ γ) (consEnv x₂ γ) (consEnv p (idEnv γ))) :
    RankLaws (semSigma A B) γ where
  obj_rank hz := by
    rcases hz with ⟨x, y, rfl, hx, hy⟩
    exact ⟨RankLt_mono (Nat.le_max_left _ _) x (rkA.obj_rank hx),
      RankLt_mono (Nat.le_max_right _ _) y ((rkB hx).obj_rank hy)⟩
  hom_rank hm := by
    rcases (semSigma_fiber_hom_iff hiA).mp hm with
      ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
    exact ⟨RankLt_mono (Nat.le_max_left _ _) x₁ (rkA.obj_rank hp.1),
      RankLt_mono (Nat.le_max_left _ _) x₂ (rkA.obj_rank hp.2.1),
      RankLt_mono (Nat.le_max_left _ _) p (rkA.hom_rank hp),
      RankLt_mono (Nat.le_max_right _ _) q ((rkB hp.2.1).het_hom_rank (trB hp) hq)⟩

theorem semSigma_fiber_laws {A B : SemFam} {γ : Env}
    (hA : FiberLaws A γ) (hiA : IdentityTransport A γ)
    (hB : ∀ {x}, A.Obj γ x → FiberLaws B (consEnv x γ))
    (hiB : ∀ {x}, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ {x₁ x₂ p}, FiberHom A γ x₁ x₂ p →
      TransportLaws B (consEnv x₁ γ) (consEnv x₂ γ) (consEnv p (idEnv γ)))
    (ctB : ∀ {x₁ x₂ x₃ p₁ p₂}, FiberHom A γ x₁ x₂ p₁ → FiberHom A γ x₂ x₃ p₂ →
      CompTransport B (consEnv x₁ γ) (consEnv x₂ γ) (consEnv x₃ γ)
        (consEnv p₁ (idEnv γ)) (consEnv p₂ (idEnv γ)) (consEnv (A.comp γ p₁ p₂) (idEnv γ))) :
    FiberLaws (semSigma A B) γ where
  id_hom hz := by
    rcases hz with ⟨x, y, rfl, hx, hy⟩
    refine (semSigma_fiber_hom_iff hiA).mpr ⟨x, y, x, y, idVal x, idVal y, rfl, rfl, rfl,
      hA.id_hom hx, ?_⟩
    rw [← idEnv_consEnv]
    exact (hB hx).id_hom hy
  comp_hom hm₁ hm₂ := by
    rcases (semSigma_fiber_hom_iff hiA).mp hm₁ with
      ⟨x₁, y₁, x₂, y₂, p₁, q₁, rfl, rfl, rfl, hp₁, hq₁⟩
    rcases (semSigma_fiber_hom_iff hiA).mp hm₂ with
      ⟨x₂', y₂', x₃, y₃, p₂, q₂, hpair, rfl, rfl, hp₂, hq₂⟩
    cases hpair
    have hq₁v := (trB hp₁).vertical hq₁
    have hq₂v := (trB hp₂).vertical hq₂
    have hq₁_tr : FiberHom B (consEnv x₃ γ)
        (B.reindexObj (consEnv x₁ γ) (consEnv x₃ γ) (consEnv (A.comp γ p₁ p₂) (idEnv γ)) y₁)
        (B.reindexObj (consEnv x₂ γ) (consEnv x₃ γ) (consEnv p₂ (idEnv γ)) y₂)
        (B.reindexMor (consEnv x₂ γ) (consEnv x₃ γ) (consEnv p₂ (idEnv γ)) q₁) := by
      simpa only [(ctB hp₁ hp₂).comp_obj hq₁.1] using (trB hp₂).map_hom hq₁v
    have hq₁₂v := (hB hp₂.2.1).comp_hom hq₁_tr hq₂v
    have hq₁₂ : piHetMor B (consEnv x₁ γ) (consEnv x₃ γ) (consEnv (A.comp γ p₁ p₂) (idEnv γ))
        y₁ y₃
        (B.comp (consEnv x₃ γ)
          (B.reindexMor (consEnv x₂ γ) (consEnv x₃ γ) (consEnv p₂ (idEnv γ)) q₁) q₂) :=
      ⟨hq₁.1, hq₂.2.1, ((trB (hA.comp_hom hp₁ hp₂)).hom_iff hq₁.1 hq₂.2.1).mpr hq₁₂v.2.2⟩
    exact (semSigma_fiber_hom_iff hiA).mpr
      ⟨x₁, y₁, x₃, y₃, A.comp γ p₁ p₂, _, rfl, rfl, rfl, hA.comp_hom hp₁ hp₂, hq₁₂⟩
  inv_hom hm := by
    rcases (semSigma_fiber_hom_iff hiA).mp hm with
      ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
    have hpinv := hA.inv_hom hp
    have hqv := (trB hp).vertical hq
    have hqinv := (hB hp.2.1).inv_hom hqv
    have hdom : B.reindexObj (consEnv x₂ γ) (consEnv x₁ γ) (consEnv (A.inv γ p) (idEnv γ))
        (B.reindexObj (consEnv x₁ γ) (consEnv x₂ γ) (consEnv p (idEnv γ)) y₁) = y₁ := by
      rw [(ctB hp hpinv).comp_obj hq.1, hA.comp_inv hp, ← idEnv_consEnv, (hiB hp.1).obj hq.1]
    have hqinv_tr : FiberHom B (consEnv x₁ γ)
        (B.reindexObj (consEnv x₂ γ) (consEnv x₁ γ) (consEnv (A.inv γ p) (idEnv γ)) y₂)
        y₁
        (B.reindexMor (consEnv x₂ γ) (consEnv x₁ γ) (consEnv (A.inv γ p) (idEnv γ))
          (B.inv (consEnv x₂ γ) q)) := by
      simpa only [hdom] using (trB hpinv).map_hom hqinv
    have hqinv_het : piHetMor B (consEnv x₂ γ) (consEnv x₁ γ) (consEnv (A.inv γ p) (idEnv γ))
        y₂ y₁
        (B.reindexMor (consEnv x₂ γ) (consEnv x₁ γ) (consEnv (A.inv γ p) (idEnv γ))
          (B.inv (consEnv x₂ γ) q)) :=
      ⟨hq.2.1, hq.1, ((trB hpinv).hom_iff hq.2.1 hq.1).mpr hqinv_tr.2.2⟩
    exact (semSigma_fiber_hom_iff hiA).mpr
      ⟨x₂, y₂, x₁, y₁, A.inv γ p, _, rfl, rfl, rfl, hpinv, hqinv_het⟩
  id_comp hm := by
    rcases (semSigma_fiber_hom_iff hiA).mp hm with
      ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
    have hqv := (trB hp).vertical hq
    dsimp only [semSigma, idVal, sigMorX1, sigMorX2, sigMorP, sigMorQ]
    rw [hA.id_comp hp, (trB hp).map_id hq.1, (hB hp.2.1).id_comp hqv]
  comp_id hm := by
    rcases (semSigma_fiber_hom_iff hiA).mp hm with
      ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
    have hqv := (trB hp).vertical hq
    dsimp only [semSigma, idVal, sigMorX1, sigMorX2, sigMorP, sigMorQ]
    rw [hA.comp_id hp, ← idEnv_consEnv, (hiB hp.2.1).mor hqv, (hB hp.2.1).comp_id hqv]
  assoc hm₁ hm₂ hm₃ := by
    rcases (semSigma_fiber_hom_iff hiA).mp hm₁ with
      ⟨x₁, y₁, x₂, y₂, p₁, q₁, rfl, rfl, rfl, hp₁, hq₁⟩
    rcases (semSigma_fiber_hom_iff hiA).mp hm₂ with
      ⟨x₂', y₂', x₃, y₃, p₂, q₂, hpair₁, rfl, rfl, hp₂, hq₂⟩
    cases hpair₁
    rcases (semSigma_fiber_hom_iff hiA).mp hm₃ with
      ⟨x₃', y₃', x₄, y₄, p₃, q₃, hpair₂, rfl, rfl, hp₃, hq₃⟩
    cases hpair₂
    have hq₁v := (trB hp₁).vertical hq₁
    have hq₂v := (trB hp₂).vertical hq₂
    have hq₃v := (trB hp₃).vertical hq₃
    have hq₁_tr₂ : FiberHom B (consEnv x₃ γ)
        (B.reindexObj (consEnv x₁ γ) (consEnv x₃ γ) (consEnv (A.comp γ p₁ p₂) (idEnv γ)) y₁)
        (B.reindexObj (consEnv x₂ γ) (consEnv x₃ γ) (consEnv p₂ (idEnv γ)) y₂)
        (B.reindexMor (consEnv x₂ γ) (consEnv x₃ γ) (consEnv p₂ (idEnv γ)) q₁) := by
      simpa only [(ctB hp₁ hp₂).comp_obj hq₁.1] using (trB hp₂).map_hom hq₁v
    have hq₁_tr₃ : FiberHom B (consEnv x₄ γ)
        (B.reindexObj (consEnv x₁ γ) (consEnv x₄ γ) (consEnv (A.comp γ (A.comp γ p₁ p₂) p₃) (idEnv γ)) y₁)
        (B.reindexObj (consEnv x₂ γ) (consEnv x₄ γ) (consEnv (A.comp γ p₂ p₃) (idEnv γ)) y₂)
        (B.reindexMor (consEnv x₂ γ) (consEnv x₄ γ) (consEnv (A.comp γ p₂ p₃) (idEnv γ)) q₁) := by
      simpa only [(ctB (hA.comp_hom hp₁ hp₂) hp₃).comp_obj hq₁.1,
        (ctB hp₂ hp₃).comp_obj hq₁.2.1, (ctB hp₂ hp₃).comp_mor hq₁v] using (trB hp₃).map_hom hq₁_tr₂
    have hq₂_tr₃ : FiberHom B (consEnv x₄ γ)
        (B.reindexObj (consEnv x₂ γ) (consEnv x₄ γ) (consEnv (A.comp γ p₂ p₃) (idEnv γ)) y₂)
        (B.reindexObj (consEnv x₃ γ) (consEnv x₄ γ) (consEnv p₃ (idEnv γ)) y₃)
        (B.reindexMor (consEnv x₃ γ) (consEnv x₄ γ) (consEnv p₃ (idEnv γ)) q₂) := by
      simpa only [(ctB hp₂ hp₃).comp_obj hq₂.1] using (trB hp₃).map_hom hq₂v
    dsimp only [semSigma, sigMorX1, sigMorX2, sigMorP, sigMorQ]
    rw [hA.assoc hp₁ hp₂ hp₃, (trB hp₃).map_comp hq₁_tr₂ hq₂v,
      (ctB hp₂ hp₃).comp_mor hq₁v, (hB hp₃.2.1).assoc hq₁_tr₃ hq₂_tr₃ hq₃v]
  inv_comp hm := by
    rcases (semSigma_fiber_hom_iff hiA).mp hm with
      ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
    have hpinv := hA.inv_hom hp
    have hqv := (trB hp).vertical hq
    have hqinv := (hB hp.2.1).inv_hom hqv
    dsimp only [semSigma, idVal, sigMorX1, sigMorX2, sigMorP, sigMorQ]
    rw [hA.inv_comp hp, (ctB hpinv hp).comp_mor hqinv, hA.inv_comp hp,
      ← idEnv_consEnv, (hiB hp.2.1).mor hqinv, (hB hp.2.1).inv_comp hqv]
  comp_inv hm := by
    rcases (semSigma_fiber_hom_iff hiA).mp hm with
      ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
    have hpinv := hA.inv_hom hp
    have hqv := (trB hp).vertical hq
    have hqinv := (hB hp.2.1).inv_hom hqv
    have hdom : B.reindexObj (consEnv x₂ γ) (consEnv x₁ γ) (consEnv (A.inv γ p) (idEnv γ))
        (B.reindexObj (consEnv x₁ γ) (consEnv x₂ γ) (consEnv p (idEnv γ)) y₁) = y₁ := by
      rw [(ctB hp hpinv).comp_obj hq.1, hA.comp_inv hp, ← idEnv_consEnv, (hiB hp.1).obj hq.1]
    dsimp only [semSigma, idVal, sigMorX1, sigMorX2, sigMorP, sigMorQ]
    rw [hA.comp_inv hp, ← (trB hpinv).map_comp hqv hqinv, (hB hp.2.1).comp_inv hqv,
      (trB hpinv).map_id ((trB hp).map_obj hq.1), hdom]

theorem semSigma_transport_laws {A B : SemFam} {γ₁ γ₂ δ : Env}
    (hA₂ : FiberLaws A γ₂)
    (hiA₁ : IdentityTransport A γ₁) (hiA₂ : IdentityTransport A γ₂)
    (trA : TransportLaws A γ₁ γ₂ δ)
    (trB₁ : ∀ {x₁ x₂ p}, FiberHom A γ₁ x₁ x₂ p →
      TransportLaws B (consEnv x₁ γ₁) (consEnv x₂ γ₁) (consEnv p (idEnv γ₁)))
    (trB₂ : ∀ {x₁ x₂ p}, FiberHom A γ₂ x₁ x₂ p →
      TransportLaws B (consEnv x₁ γ₂) (consEnv x₂ γ₂) (consEnv p (idEnv γ₂)))
    (trB_het : ∀ {x₁ x₂ p}, piHetMor A γ₁ γ₂ δ x₁ x₂ p →
      TransportLaws B (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ))
    (ctB_left : ∀ {x₁ x₂ p}, FiberHom A γ₁ x₁ x₂ p →
      CompTransport B (consEnv x₁ γ₁) (consEnv x₂ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₂) γ₂)
        (consEnv p (idEnv γ₁)) (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₂)) δ)
        (consEnv (A.reindexMor γ₁ γ₂ δ p) δ))
    (ctB_right : ∀ {x₁ x₂ p}, piHetMor A γ₁ γ₂ δ x₁ x₂ p →
      CompTransport B (consEnv x₁ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₁) γ₂) (consEnv x₂ γ₂)
        (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₁)) δ) (consEnv p (idEnv γ₂))
        (consEnv p δ)) :
    TransportLaws (semSigma A B) γ₁ γ₂ δ where
  map_obj hz := by
    rcases hz with ⟨x, y, rfl, hx, hy⟩
    have hx' := trA.map_obj hx
    have h_id : piHetMor A γ₁ γ₂ δ x (A.reindexObj γ₁ γ₂ δ x) (idVal (A.reindexObj γ₁ γ₂ δ x)) :=
      ⟨hx, hx', (trA.hom_iff hx hx').mpr (hA₂.id_hom hx').2.2⟩
    exact ⟨_, _, rfl, hx', (trB_het h_id).map_obj hy⟩
  unmap_obj hz' := by
    rcases hz' with ⟨x', y', rfl, hx', hy'⟩
    let x := A.unreindexObj γ₁ γ₂ δ x'
    have hx : A.Obj γ₁ x := trA.unmap_obj hx'
    have h_id : piHetMor A γ₁ γ₂ δ x x' (idVal x') := by
      refine ⟨hx, hx', (trA.hom_iff hx hx').mpr ?_⟩
      dsimp only [x]
      rw [trA.map_unmap_obj hx']
      exact (hA₂.id_hom hx').2.2
    exact ⟨_, _, rfl, hx, (trB_het h_id).unmap_obj hy'⟩
  map_hom hm := by
    rcases (semSigma_fiber_hom_iff hiA₁).mp hm with
      ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
    have hp' := trA.map_hom hp
    have hx₁' := hp'.1
    have hx₂' := hp'.2.1
    have h_id₁ : piHetMor A γ₁ γ₂ δ x₁ (A.reindexObj γ₁ γ₂ δ x₁) (idVal (A.reindexObj γ₁ γ₂ δ x₁)) :=
      ⟨hp.1, hx₁', (trA.hom_iff hp.1 hx₁').mpr (hA₂.id_hom hx₁').2.2⟩
    have h_id₂ : piHetMor A γ₁ γ₂ δ x₂ (A.reindexObj γ₁ γ₂ δ x₂) (idVal (A.reindexObj γ₁ γ₂ δ x₂)) :=
      ⟨hp.2.1, hx₂', (trA.hom_iff hp.2.1 hx₂').mpr (hA₂.id_hom hx₂').2.2⟩
    have hp_het : piHetMor A γ₁ γ₂ δ x₁ (A.reindexObj γ₁ γ₂ δ x₂) (A.reindexMor γ₁ γ₂ δ p) :=
      ⟨hp.1, hx₂', (trA.hom_iff hp.1 hx₂').mpr hp'.2.2⟩
    have hqv := (trB₁ hp).vertical hq
    have hq'_raw := (trB_het h_id₂).map_hom hqv
    have hdom_eq : B.reindexObj (consEnv x₂ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₂) γ₂)
        (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₂)) δ)
        (B.reindexObj (consEnv x₁ γ₁) (consEnv x₂ γ₁) (consEnv p (idEnv γ₁)) y₁) =
      B.reindexObj (consEnv (A.reindexObj γ₁ γ₂ δ x₁) γ₂) (consEnv (A.reindexObj γ₁ γ₂ δ x₂) γ₂)
        (consEnv (A.reindexMor γ₁ γ₂ δ p) (idEnv γ₂))
        (B.reindexObj (consEnv x₁ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₁) γ₂)
          (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₁)) δ) y₁) := by
      rw [(ctB_left hp).comp_obj hq.1, (ctB_right hp_het).comp_obj hq.1]
    have hq'v : FiberHom B (consEnv (A.reindexObj γ₁ γ₂ δ x₂) γ₂)
        (B.reindexObj (consEnv (A.reindexObj γ₁ γ₂ δ x₁) γ₂) (consEnv (A.reindexObj γ₁ γ₂ δ x₂) γ₂)
          (consEnv (A.reindexMor γ₁ γ₂ δ p) (idEnv γ₂))
          (B.reindexObj (consEnv x₁ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₁) γ₂)
            (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₁)) δ) y₁))
        (B.reindexObj (consEnv x₂ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₂) γ₂)
          (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₂)) δ) y₂)
        (B.reindexMor (consEnv x₂ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₂) γ₂)
          (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₂)) δ) q) := by
      simpa only [hdom_eq] using hq'_raw
    have hq'_het : piHetMor B (consEnv (A.reindexObj γ₁ γ₂ δ x₁) γ₂)
        (consEnv (A.reindexObj γ₁ γ₂ δ x₂) γ₂)
        (consEnv (A.reindexMor γ₁ γ₂ δ p) (idEnv γ₂))
        (B.reindexObj (consEnv x₁ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₁) γ₂)
          (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₁)) δ) y₁)
        (B.reindexObj (consEnv x₂ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₂) γ₂)
          (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₂)) δ) y₂)
        (B.reindexMor (consEnv x₂ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₂) γ₂)
          (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₂)) δ) q) :=
      ⟨(trB_het h_id₁).map_obj hq.1, (trB_het h_id₂).map_obj hq.2.1,
        ((trB₂ hp').hom_iff ((trB_het h_id₁).map_obj hq.1) ((trB_het h_id₂).map_obj hq.2.1)).mpr
          hq'v.2.2⟩
    exact (semSigma_fiber_hom_iff hiA₂).mpr
      ⟨_, _, _, _, _, _, rfl, rfl, rfl, hp', hq'_het⟩
  unmap_hom hm' := by
    rcases (semSigma_fiber_hom_iff hiA₂).mp hm' with
      ⟨x₁', y₁', x₂', y₂', p', q', rfl, rfl, rfl, hp', hq'⟩
    have hp := trA.unmap_hom hp'
    let x₁ := A.unreindexObj γ₁ γ₂ δ x₁'
    let x₂ := A.unreindexObj γ₁ γ₂ δ x₂'
    have hx₁ : A.Obj γ₁ x₁ := hp.1
    have hx₂ : A.Obj γ₁ x₂ := hp.2.1
    have h_id₁ : piHetMor A γ₁ γ₂ δ x₁ x₁' (idVal x₁') := by
      refine ⟨hx₁, hp'.1, (trA.hom_iff hx₁ hp'.1).mpr ?_⟩
      dsimp only [x₁]
      rw [trA.map_unmap_obj hp'.1]
      exact (hA₂.id_hom hp'.1).2.2
    have h_id₂ : piHetMor A γ₁ γ₂ δ x₂ x₂' (idVal x₂') := by
      refine ⟨hx₂, hp'.2.1, (trA.hom_iff hx₂ hp'.2.1).mpr ?_⟩
      dsimp only [x₂]
      rw [trA.map_unmap_obj hp'.2.1]
      exact (hA₂.id_hom hp'.2.1).2.2
    have hp_het : piHetMor A γ₁ γ₂ δ x₁ x₂' p' := by
      refine ⟨hx₁, hp'.2.1, (trA.hom_iff hx₁ hp'.2.1).mpr ?_⟩
      dsimp only [x₁]
      rw [trA.map_unmap_obj hp'.1]
      exact hp'.2.2
    have hy₁ := (trB_het h_id₁).unmap_obj hq'.1
    have hy₂ := (trB_het h_id₂).unmap_obj hq'.2.1
    have hq'v := (trB₂ hp').vertical hq'
    have hdom_eq : B.reindexObj (consEnv x₁' γ₂) (consEnv x₂' γ₂) (consEnv p' (idEnv γ₂)) y₁' =
        B.reindexObj (consEnv x₂ γ₁) (consEnv x₂' γ₂) (consEnv (idVal x₂') δ)
          (B.reindexObj (consEnv x₁ γ₁) (consEnv x₂ γ₁) (consEnv (A.unreindexMor γ₁ γ₂ δ p') (idEnv γ₁))
            (B.unreindexObj (consEnv x₁ γ₁) (consEnv x₁' γ₂) (consEnv (idVal x₁') δ) y₁')) := by
      have h1 := (ctB_left hp).comp_obj hy₁
      have h2 := (ctB_right hp_het).comp_obj hy₁
      dsimp only [x₁, x₂] at h1 h2 ⊢
      rw [trA.map_unmap_obj hp'.2.1, trA.map_unmap_mor hp'] at h1
      rw [trA.map_unmap_obj hp'.1, (trB_het h_id₁).map_unmap_obj hq'.1] at h2
      exact h2.trans h1.symm
    have hq'v_rew : FiberHom B (consEnv x₂' γ₂)
        (B.reindexObj (consEnv x₂ γ₁) (consEnv x₂' γ₂) (consEnv (idVal x₂') δ)
          (B.reindexObj (consEnv x₁ γ₁) (consEnv x₂ γ₁) (consEnv (A.unreindexMor γ₁ γ₂ δ p') (idEnv γ₁))
            (B.unreindexObj (consEnv x₁ γ₁) (consEnv x₁' γ₂) (consEnv (idVal x₁') δ) y₁')))
        y₂' q' := by
      simpa only [← hdom_eq] using hq'v
    have hqv_raw := (trB_het h_id₂).unmap_hom hq'v_rew
    rw [(trB_het h_id₂).unmap_map_obj ((trB₁ hp).map_obj hy₁)] at hqv_raw
    have hq_het : piHetMor B (consEnv x₁ γ₁) (consEnv x₂ γ₁)
        (consEnv (A.unreindexMor γ₁ γ₂ δ p') (idEnv γ₁))
        (B.unreindexObj (consEnv x₁ γ₁) (consEnv x₁' γ₂) (consEnv (idVal x₁') δ) y₁')
        (B.unreindexObj (consEnv x₂ γ₁) (consEnv x₂' γ₂) (consEnv (idVal x₂') δ) y₂')
        (B.unreindexMor (consEnv x₂ γ₁) (consEnv x₂' γ₂) (consEnv (idVal x₂') δ) q') :=
      ⟨hy₁, hy₂, ((trB₁ hp).hom_iff hy₁ hy₂).mpr hqv_raw.2.2⟩
    exact (semSigma_fiber_hom_iff hiA₁).mpr
      ⟨_, _, _, _, _, _, rfl, rfl, rfl, hp, hq_het⟩
  unmap_map_obj hz := by
    rcases hz with ⟨x, y, rfl, hx, hy⟩
    have hx' := trA.map_obj hx
    have h_id : piHetMor A γ₁ γ₂ δ x (A.reindexObj γ₁ γ₂ δ x) (idVal (A.reindexObj γ₁ γ₂ δ x)) :=
      ⟨hx, hx', (trA.hom_iff hx hx').mpr (hA₂.id_hom hx').2.2⟩
    dsimp only [semSigma, sigFst, sigSnd]
    rw [trA.unmap_map_obj hx, (trB_het h_id).unmap_map_obj hy]
  map_unmap_obj hz' := by
    rcases hz' with ⟨x', y', rfl, hx', hy'⟩
    let x := A.unreindexObj γ₁ γ₂ δ x'
    have hx : A.Obj γ₁ x := trA.unmap_obj hx'
    have h_id : piHetMor A γ₁ γ₂ δ x x' (idVal x') := by
      refine ⟨hx, hx', (trA.hom_iff hx hx').mpr ?_⟩
      dsimp only [x]
      rw [trA.map_unmap_obj hx']
      exact (hA₂.id_hom hx').2.2
    dsimp only [semSigma, sigFst, sigSnd]
    rw [trA.map_unmap_obj hx', (trB_het h_id).map_unmap_obj hy']
  unmap_map_mor hm := by
    rcases (semSigma_fiber_hom_iff hiA₁).mp hm with
      ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
    have hx₂' := trA.map_obj hp.2.1
    have h_id₂ : piHetMor A γ₁ γ₂ δ x₂ (A.reindexObj γ₁ γ₂ δ x₂) (idVal (A.reindexObj γ₁ γ₂ δ x₂)) :=
      ⟨hp.2.1, hx₂', (trA.hom_iff hp.2.1 hx₂').mpr (hA₂.id_hom hx₂').2.2⟩
    have hqv := (trB₁ hp).vertical hq
    dsimp only [semSigma, sigMorX1, sigMorX2, sigMorP, sigMorQ]
    rw [trA.unmap_map_obj hp.1, trA.unmap_map_obj hp.2.1, trA.unmap_map_mor hp,
      (trB_het h_id₂).unmap_map_mor hqv]
  map_unmap_mor hm' := by
    rcases (semSigma_fiber_hom_iff hiA₂).mp hm' with
      ⟨x₁', y₁', x₂', y₂', p', q', rfl, rfl, rfl, hp', hq'⟩
    let x₂ := A.unreindexObj γ₁ γ₂ δ x₂'
    have hx₂ : A.Obj γ₁ x₂ := trA.unmap_obj hp'.2.1
    have h_id₂ : piHetMor A γ₁ γ₂ δ x₂ x₂' (idVal x₂') := by
      refine ⟨hx₂, hp'.2.1, (trA.hom_iff hx₂ hp'.2.1).mpr ?_⟩
      dsimp only [x₂]
      rw [trA.map_unmap_obj hp'.2.1]
      exact (hA₂.id_hom hp'.2.1).2.2
    have hq'v := (trB₂ hp').vertical hq'
    dsimp only [semSigma, sigMorX1, sigMorX2, sigMorP, sigMorQ]
    rw [trA.map_unmap_obj hp'.1, trA.map_unmap_obj hp'.2.1, trA.map_unmap_mor hp',
      (trB_het h_id₂).map_unmap_mor hq'v]
  map_id hz := by
    rcases hz with ⟨x, y, rfl, hx, hy⟩
    have hx' := trA.map_obj hx
    have h_id : piHetMor A γ₁ γ₂ δ x (A.reindexObj γ₁ γ₂ δ x) (idVal (A.reindexObj γ₁ γ₂ δ x)) :=
      ⟨hx, hx', (trA.hom_iff hx hx').mpr (hA₂.id_hom hx').2.2⟩
    dsimp only [semSigma, idVal, sigFst, sigSnd, sigMorX1, sigMorX2, sigMorP, sigMorQ]
    rw [trA.map_id hx, (trB_het h_id).map_id hy]
  map_comp hm₁ hm₂ := by
    rcases (semSigma_fiber_hom_iff hiA₁).mp hm₁ with
      ⟨x₁, y₁, x₂, y₂, p₁, q₁, rfl, rfl, rfl, hp₁, hq₁⟩
    rcases (semSigma_fiber_hom_iff hiA₁).mp hm₂ with
      ⟨x₂', y₂', x₃, y₃, p₂, q₂, hpair, rfl, rfl, hp₂, hq₂⟩
    cases hpair
    have hx₂' := trA.map_obj hp₂.1
    have hx₃' := trA.map_obj hp₂.2.1
    have h_id₃ : piHetMor A γ₁ γ₂ δ x₃ (A.reindexObj γ₁ γ₂ δ x₃) (idVal (A.reindexObj γ₁ γ₂ δ x₃)) :=
      ⟨hp₂.2.1, hx₃', (trA.hom_iff hp₂.2.1 hx₃').mpr (hA₂.id_hom hx₃').2.2⟩
    have hp₂' := trA.map_hom hp₂
    have hp₂_het : piHetMor A γ₁ γ₂ δ x₂ (A.reindexObj γ₁ γ₂ δ x₃) (A.reindexMor γ₁ γ₂ δ p₂) :=
      ⟨hp₂.1, hx₃', (trA.hom_iff hp₂.1 hx₃').mpr hp₂'.2.2⟩
    have hq₁v := (trB₁ hp₁).vertical hq₁
    have hq₂v := (trB₁ hp₂).vertical hq₂
    have hq₁_tr := (trB₁ hp₂).map_hom hq₁v
    dsimp only [semSigma, sigMorX1, sigMorX2, sigMorP, sigMorQ]
    rw [trA.map_comp hp₁ hp₂, (trB_het h_id₃).map_comp hq₁_tr hq₂v,
      (ctB_left hp₂).comp_mor hq₁v, (ctB_right hp₂_het).comp_mor hq₁v]
  hom_iff hz₁ hz₂ := by
    rcases hz₁ with ⟨x₁, y₁, rfl, hx₁, hy₁⟩
    rcases hz₂ with ⟨x₂, y₂, rfl, hx₂, hy₂⟩
    dsimp only [semSigma, sigFst, sigSnd]
    constructor
    · rintro ⟨x₁a, y₁a, x₂a, y₂a, p, q, hpair₁, hpair₂, rfl, _, _, _, _, hp, hq⟩
      cases hpair₁; cases hpair₂
      have hp_het : piHetMor A γ₁ γ₂ δ x₁ x₂ p := ⟨hx₁, hx₂, hp⟩
      have hp' : FiberHom A γ₂ (A.reindexObj γ₁ γ₂ δ x₁) x₂ p := trA.vertical hp_het
      have hx₁' := hp'.1
      have h_id₁ : piHetMor A γ₁ γ₂ δ x₁ (A.reindexObj γ₁ γ₂ δ x₁) (idVal (A.reindexObj γ₁ γ₂ δ x₁)) :=
        ⟨hx₁, hx₁', (trA.hom_iff hx₁ hx₁').mpr (hA₂.id_hom hx₁').2.2⟩
      have hy₁' := (trB_het h_id₁).map_obj hy₁
      have hqv := (trB_het hp_het).vertical ⟨hy₁, hy₂, hq⟩
      have hqv' : FiberHom B (consEnv x₂ γ₂)
          (B.reindexObj (consEnv (A.reindexObj γ₁ γ₂ δ x₁) γ₂) (consEnv x₂ γ₂) (consEnv p (idEnv γ₂))
            (B.reindexObj (consEnv x₁ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₁) γ₂)
              (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₁)) δ) y₁))
          y₂ q := by
        simpa only [← (ctB_right hp_het).comp_obj hy₁] using hqv
      refine ⟨_, _, _, _, p, q, rfl, rfl, ?_, hx₁', hx₂, hy₁', hy₂, hp'.2.2,
        ((trB₂ hp').hom_iff hy₁' hy₂).mpr hqv'.2.2⟩
      rw [hiA₂.obj hx₁']
    · rintro ⟨x₁a, y₁a, x₂a, y₂a, p, q, hpair₁, hpair₂, rfl, hx₁', _, hy₁', _, hp', hq'⟩
      cases hpair₁; cases hpair₂
      have hp_v : FiberHom A γ₂ (A.reindexObj γ₁ γ₂ δ x₁) x₂ p := ⟨hx₁', hx₂, hp'⟩
      have hp : A.Hom γ₁ γ₂ δ x₁ x₂ p := (trA.hom_iff hx₁ hx₂).mpr hp'
      have hp_het : piHetMor A γ₁ γ₂ δ x₁ x₂ p := ⟨hx₁, hx₂, hp⟩
      have hqv' := (trB₂ hp_v).vertical ⟨hy₁', hy₂, hq'⟩
      have hqv : FiberHom B (consEnv x₂ γ₂)
          (B.reindexObj (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) y₁) y₂ q := by
        simpa only [(ctB_right hp_het).comp_obj hy₁] using hqv'
      refine ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, ?_, hx₁, hx₂, hy₁, hy₂, hp,
        ((trB_het hp_het).hom_iff hy₁ hy₂).mpr hqv.2.2⟩
      rw [hiA₂.obj hx₁']

theorem semSigma_comp_transport {A B : SemFam} {γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ : Env}
    (hiA₁ : IdentityTransport A γ₁)
    (ctA : CompTransport A γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃)
    (trB₁ : ∀ {x₁ x₂ p}, FiberHom A γ₁ x₁ x₂ p →
      TransportLaws B (consEnv x₁ γ₁) (consEnv x₂ γ₁) (consEnv p (idEnv γ₁)))
    (ctB_id : ∀ {x}, A.Obj γ₁ x →
      CompTransport B (consEnv x γ₁)
        (consEnv (A.reindexObj γ₁ γ₂ δ₁₂ x) γ₂)
        (consEnv (A.reindexObj γ₁ γ₃ δ₁₃ x) γ₃)
        (consEnv (idVal (A.reindexObj γ₁ γ₂ δ₁₂ x)) δ₁₂)
        (consEnv (idVal (A.reindexObj γ₁ γ₃ δ₁₃ x)) δ₂₃)
        (consEnv (idVal (A.reindexObj γ₁ γ₃ δ₁₃ x)) δ₁₃)) :
    CompTransport (semSigma A B) γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ where
  comp_obj hz := by
    rcases hz with ⟨x, y, rfl, hx, hy⟩
    dsimp only [semSigma, sigFst, sigSnd]
    rw [ctA.comp_obj hx, (ctB_id hx).comp_obj hy]
  comp_mor hm := by
    rcases (semSigma_fiber_hom_iff hiA₁).mp hm with
      ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
    have hqv := (trB₁ hp).vertical hq
    dsimp only [semSigma, sigMorX1, sigMorX2, sigMorP, sigMorQ]
    rw [ctA.comp_obj hp.1, ctA.comp_obj hp.2.1, ctA.comp_mor hp,
      (ctB_id hp.2.1).comp_mor hqv]

end HofmannStreicher1994.Repaired

/-! ## SemPiLaws.lean -/

namespace HofmannStreicher1994.Repaired

theorem piAppObj_mkPiObj_of_rk {A : SemFam} {γ : Env} (rkA : RankLaws A γ)
    {fo : Val → Val} {fm : Val → Val → Val → Val} {x : Val} (hx : A.Obj γ x) :
    piAppObj (mkPiObj A.lvl (A.Obj γ) (piDomMor A γ) fo fm) x = fo x :=
  piAppObj_mkPiObj (rkA.obj_rank hx) hx

theorem piAppMor_mkPiObj_of_rk {A : SemFam} {γ : Env} (rkA : RankLaws A γ)
    {fo : Val → Val} {fm : Val → Val → Val → Val} {x y p : Val} (hp : FiberHom A γ x y p) :
    piAppMor (mkPiObj A.lvl (A.Obj γ) (piDomMor A γ) fo fm) x y p = fm x y p :=
  piAppMor_mkPiObj (rkA.obj_rank hp.1) (rkA.obj_rank hp.2.1) (rkA.hom_rank hp) hp

theorem piMorAt_mkPiMor_of_rk {A : SemFam} {γ : Env} (rkA : RankLaws A γ)
    {η : Val → Val → Val → Val} {x y p : Val} (hp : FiberHom A γ x y p) :
    piMorAt (mkPiMor A.lvl (piDomMor A γ) η) x y p = η x y p :=
  piMorAt_mkPiMor (rkA.obj_rank hp.1) (rkA.obj_rank hp.2.1) (rkA.hom_rank hp) hp

theorem semPi_id_components {A B : SemFam} {γ : Env} {f : Val}
    (hf : (semPi A B).Obj γ f) (x y p : Val) :
    piMorAt (idVal f) x y p = piAppMor f x y p :=
  piMorAt_idVal f x y p A.lvl _ _ hf.1

theorem semPi_identity_obj {A B : SemFam} {γ : Env}
    (hiA : IdentityTransport A γ) (trA : TransportLaws A γ γ (idEnv γ))
    (hiB : ∀ x, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
    {f : Val} (hf : (semPi A B).Obj γ f) :
    (semPi A B).reindexObj γ γ (idEnv γ) f = f := by
  dsimp only [semPi]
  refine (mkPiObj_ext (fun _ => Iff.rfl) (fun _ _ _ => Iff.rfl) ?_ ?_).trans hf.1.symm
  case refine_2 =>
    intro x y p hp
    simpa only [trA.unmap_identity_obj hiA hp.1, trA.unmap_identity_obj hiA hp.2.1,
      trA.unmap_identity_mor hiA hp, ← idEnv_consEnv] using
      (hiB y hp.2.1).mor ((trB x y p hp).vertical
        ⟨hf.2.1 x hp.1, hf.2.1 y hp.2.1, hf.2.2.1 x y p hp⟩)
  case refine_1 =>
    intro x hx
    simpa only [trA.unmap_identity_obj hiA hx, ← idEnv_consEnv] using
      (hiB x hx).obj (hf.2.1 x hx)

theorem semPi_identity_piHom {A B : SemFam} {γ : Env}
    (hiA : IdentityTransport A γ) {f : Val} (hf : (semPi A B).Obj γ f) :
    PiHom A B γ f f (idVal f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  case refine_3 =>
    intro w x y u p hu hp
    simpa only [semPi_id_components hf, hiA.mor hu] using hf.2.2.2.2 w x y u p hu hp
  case refine_4 =>
    simpa only [semPi_id_components hf] using hf.2.2.2.2
  case refine_2 =>
    simpa only [semPi_id_components hf] using hf.2.2.1
  case refine_1 =>
    exact (congrArg idVal hf.1).trans
      (congrArg (mkPiMor A.lvl (piDomMor A γ)) (funext fun x => funext fun y =>
        funext fun p => (semPi_id_components hf x y p).symm))

theorem semPi_hom_iff {A B : SemFam} {γ : Env}
    (hiA : IdentityTransport A γ) (trA : TransportLaws A γ γ (idEnv γ))
    (hiB : ∀ x, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
    {f g η : Val} (hf : (semPi A B).Obj γ f) :
    (semPi A B).Hom γ γ (idEnv γ) f g η ↔ PiHom A B γ f g η :=
  Iff.of_eq (congrArg (fun f' => PiHom A B γ f' g η) (semPi_identity_obj hiA trA hiB trB hf))

theorem semPi_id_hom {A B : SemFam} {γ : Env}
    (hiA : IdentityTransport A γ) (trA : TransportLaws A γ γ (idEnv γ))
    (hiB : ∀ x, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
    {f : Val} (hf : (semPi A B).Obj γ f) :
    FiberHom (semPi A B) γ f f (idVal f) :=
  ⟨hf, hf, (semPi_hom_iff hiA trA hiB trB hf).mpr (semPi_identity_piHom hiA hf)⟩

theorem semPi_identity_mor {A B : SemFam} {γ : Env}
    (hiA : IdentityTransport A γ) (trA : TransportLaws A γ γ (idEnv γ))
    (hiB : ∀ x, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
    {f g η : Val} (hη : FiberHom (semPi A B) γ f g η) :
    (semPi A B).reindexMor γ γ (idEnv γ) η = η := by
  have hh := (semPi_hom_iff hiA trA hiB trB hη.1).mp hη.2.2
  dsimp only [semPi]
  refine (mkPiMor_ext (fun _ _ _ => Iff.rfl) ?_).trans hh.1.symm
  intro x y p hp
  simpa only [trA.unmap_identity_obj hiA hp.1, trA.unmap_identity_obj hiA hp.2.1,
    trA.unmap_identity_mor hiA hp, ← idEnv_consEnv] using
    (hiB y hp.2.1).mor ((trB x y p hp).vertical
      ⟨hη.1.2.1 x hp.1, hη.2.1.2.1 y hp.2.1, hh.2.1 x y p hp⟩)

theorem semPi_identity_transport {A B : SemFam} {γ : Env}
    (hiA : IdentityTransport A γ) (trA : TransportLaws A γ γ (idEnv γ))
    (hiB : ∀ x, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))) :
    IdentityTransport (semPi A B) γ where
  obj := semPi_identity_obj hiA trA hiB trB
  mor := semPi_identity_mor hiA trA hiB trB

theorem semPi_rank_laws {A B : SemFam} {γ : Env}
    (hiA : IdentityTransport A γ) (trA : TransportLaws A γ γ (idEnv γ))
    (hiB : ∀ x, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (rkB : ∀ x, A.Obj γ x → RankLaws B (consEnv x γ))
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))) :
    RankLaws (semPi A B) γ where
  obj_rank hf := by
    rw [hf.1]
    refine RankLt_mkPiObj
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _))
      (fun x hx => RankLt_mono (Nat.le_max_right _ _) _ ((rkB x hx).obj_rank (hf.2.1 x hx)))
      (fun x y p hp => RankLt_mono (Nat.le_max_right _ _) _
        ((rkB y hp.2.1).het_hom_rank (trB x y p hp) ⟨hf.2.1 x hp.1, hf.2.1 y hp.2.1, hf.2.2.1 x y p hp⟩))
  hom_rank hη := by
    have hh := (semPi_hom_iff hiA trA hiB trB hη.1).mp hη.2.2
    rw [hh.1]
    refine RankLt_mkPiMor
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _))
      (fun x y p hp => RankLt_mono (Nat.le_max_right _ _) _
        ((rkB y hp.2.1).het_hom_rank (trB x y p hp) ⟨hη.1.2.1 x hp.1, hη.2.1.2.1 y hp.2.1, hh.2.1 x y p hp⟩))

theorem semPi_obj_mor_vertical {A B : SemFam} {γ : Env}
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
    {f : Val} (hf : (semPi A B).Obj γ f) {x y p : Val} (hp : FiberHom A γ x y p) :
    FiberHom B (consEnv y γ)
      (B.reindexObj (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)) (piAppObj f x))
      (piAppObj f y)
      (piAppMor f x y p) :=
  (trB x y p hp).vertical ⟨hf.2.1 x hp.1, hf.2.1 y hp.2.1, hf.2.2.1 x y p hp⟩

theorem semPi_hom_mor_vertical {A B : SemFam} {γ : Env}
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
    {f g η : Val} (hf : (semPi A B).Obj γ f) (hg : (semPi A B).Obj γ g)
    (hh : PiHom A B γ f g η) {x y p : Val} (hp : FiberHom A γ x y p) :
    FiberHom B (consEnv y γ)
      (B.reindexObj (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)) (piAppObj f x))
      (piAppObj g y)
      (piMorAt η x y p) :=
  (trB x y p hp).vertical ⟨hf.2.1 x hp.1, hg.2.1 y hp.2.1, hh.2.1 x y p hp⟩

theorem semPi_hom_diag_vertical {A B : SemFam} {γ : Env}
    (hA : FiberLaws A γ)
    (hiB : ∀ x, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
    {f g η : Val} (hf : (semPi A B).Obj γ f) (hg : (semPi A B).Obj γ g)
    (hh : PiHom A B γ f g η) {x : Val} (hx : A.Obj γ x) :
    FiberHom B (consEnv x γ) (piAppObj f x) (piAppObj g x) (piMorAt η x x (idVal x)) := by
  have hv := semPi_hom_mor_vertical trB hf hg hh (hA.id_hom hx)
  rwa [← idEnv_consEnv, (hiB x hx).obj (hf.2.1 x hx)] at hv

theorem piMorAt_decomp_left {A B : SemFam} {γ : Env}
    (hA : FiberLaws A γ) {f g η : Val} (hh : PiHom A B γ f g η)
    {x y p : Val} (hp : FiberHom A γ x y p) :
    piMorAt η x y p =
      B.comp (consEnv y γ)
        (B.reindexMor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
          (piMorAt η x x (idVal x)))
        (piAppMor g x y p) := by
  have hnat := hh.2.2.2 x x y (idVal x) p (hA.id_hom hp.1) hp
  rwa [hA.id_comp hp] at hnat

theorem piMorAt_decomp_right {A B : SemFam} {γ : Env}
    (hA : FiberLaws A γ) (hiA : IdentityTransport A γ)
    (hiB : ∀ x, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
    {f g η : Val} (hf : (semPi A B).Obj γ f) (hh : PiHom A B γ f g η)
    {x y p : Val} (hp : FiberHom A γ x y p) :
    piMorAt η x y p =
      B.comp (consEnv y γ)
        (piAppMor f x y p)
        (piMorAt η y y (idVal y)) := by
  have hnat := hh.2.2.1 x y y p (idVal y) hp (hA.id_hom hp.2.1)
  have hfv := semPi_obj_mor_vertical trB hf hp
  rwa [hiA.mor hp, hA.comp_id hp, ← idEnv_consEnv, (hiB y hp.2.1).mor hfv] at hnat

theorem semPi_comp_alt {A B : SemFam} {γ : Env}
    (hA : FiberLaws A γ) (hiA : IdentityTransport A γ)
    (hB : ∀ x, A.Obj γ x → FiberLaws B (consEnv x γ))
    (hiB : ∀ x, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
    {f g h η₁ η₂ : Val}
    (hf : (semPi A B).Obj γ f) (hg : (semPi A B).Obj γ g) (hh : (semPi A B).Obj γ h)
    (hη₁ : PiHom A B γ f g η₁) (hη₂ : PiHom A B γ g h η₂)
    {x y p : Val} (hp : FiberHom A γ x y p) :
    B.comp (consEnv y γ)
      (B.reindexMor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
        (piMorAt η₁ x x (idVal x)))
      (piMorAt η₂ x y p) =
    B.comp (consEnv y γ)
      (piMorAt η₁ x y p)
      (piMorAt η₂ y y (idVal y)) := by
  have hd₁ := (trB x y p hp).map_hom (semPi_hom_diag_vertical hA hiB trB hf hg hη₁ hp.1)
  have hgv := semPi_obj_mor_vertical trB hg hp
  have hd₂ := semPi_hom_diag_vertical hA hiB trB hg hh hη₂ hp.2.1
  rw [piMorAt_decomp_right hA hiA hiB trB hg hη₂ hp,
    ← (hB y hp.2.1).assoc hd₁ hgv hd₂, ← piMorAt_decomp_left hA hη₁ hp]

theorem semPi_obj_mor_inv {A B : SemFam} {γ : Env}
    (hA : FiberLaws A γ)
    (hB : ∀ x, A.Obj γ x → FiberLaws B (consEnv x γ))
    (hiB : ∀ x, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
    (ctB : ∀ x y z p q, FiberHom A γ x y p → FiberHom A γ y z q →
      CompTransport B (consEnv x γ) (consEnv y γ) (consEnv z γ)
        (consEnv p (idEnv γ)) (consEnv q (idEnv γ)) (consEnv (A.comp γ p q) (idEnv γ)))
    {f : Val} (hf : (semPi A B).Obj γ f) {x y p : Val} (hp : FiberHom A γ x y p) :
    B.reindexMor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
      (B.inv (consEnv x γ) (piAppMor f y x (A.inv γ p))) =
    piAppMor f x y p := by
  have hpinv := hA.inv_hom hp
  have hf_pinv := semPi_obj_mor_vertical trB hf hpinv
  have hf_p := semPi_obj_mor_vertical trB hf hp
  have hdom : B.reindexObj (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
      (B.reindexObj (consEnv y γ) (consEnv x γ) (consEnv (A.inv γ p) (idEnv γ)) (piAppObj f y)) =
      piAppObj f y := by
    rw [(ctB y x y (A.inv γ p) p hpinv hp).comp_obj (hf.2.1 y hp.2.1),
      hA.inv_comp hp, ← idEnv_consEnv, (hiB y hp.2.1).obj (hf.2.1 y hp.2.1)]
  have hu : FiberHom B (consEnv y γ) (piAppObj f y)
      (B.reindexObj (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)) (piAppObj f x))
      (B.reindexMor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
        (piAppMor f y x (A.inv γ p))) := by
    simpa only [hdom] using (trB x y p hp).map_hom hf_pinv
  have huv : B.comp (consEnv y γ)
      (B.reindexMor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
        (piAppMor f y x (A.inv γ p)))
      (piAppMor f x y p) = idVal (piAppObj f y) := by
    rw [← hf.2.2.2.2 y x y (A.inv γ p) p hpinv hp, hA.inv_comp hp, hf.2.2.2.1 y hp.2.1]
  rw [(trB x y p hp).map_inv (hB x hp.1) (hB y hp.2.1) hf_pinv]
  exact (hB y hp.2.1).inv_eq_of_comp_eq_id hu hf_p huv

theorem semPi_inv_val_left {A B : SemFam} {γ : Env}
    (hA : FiberLaws A γ) (hiA : IdentityTransport A γ)
    (hB : ∀ x, A.Obj γ x → FiberLaws B (consEnv x γ))
    (hiB : ∀ x, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
    (ctB : ∀ x y z p q, FiberHom A γ x y p → FiberHom A γ y z q →
      CompTransport B (consEnv x γ) (consEnv y γ) (consEnv z γ)
        (consEnv p (idEnv γ)) (consEnv q (idEnv γ)) (consEnv (A.comp γ p q) (idEnv γ)))
    {f g η : Val} (hf : (semPi A B).Obj γ f) (hg : (semPi A B).Obj γ g)
    (hh : PiHom A B γ f g η) {x y p : Val} (hp : FiberHom A γ x y p) :
    B.reindexMor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
      (B.inv (consEnv x γ) (piMorAt η y x (A.inv γ p))) =
    B.comp (consEnv y γ)
      (B.reindexMor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
        (B.inv (consEnv x γ) (piMorAt η x x (idVal x))))
      (piAppMor f x y p) := by
  have hpinv := hA.inv_hom hp
  have hf_pinv := semPi_obj_mor_vertical trB hf hpinv
  have hd_x := semPi_hom_diag_vertical hA hiB trB hf hg hh hp.1
  rw [piMorAt_decomp_right hA hiA hiB trB hf hh hpinv,
    (hB x hp.1).inv_comp_rev hf_pinv hd_x,
    (trB x y p hp).map_comp ((hB x hp.1).inv_hom hd_x) ((hB x hp.1).inv_hom hf_pinv),
    semPi_obj_mor_inv hA hB hiB trB ctB hf hp]

theorem semPi_inv_val_right {A B : SemFam} {γ : Env}
    (hA : FiberLaws A γ)
    (hB : ∀ x, A.Obj γ x → FiberLaws B (consEnv x γ))
    (hiB : ∀ x, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
    (ctB : ∀ x y z p q, FiberHom A γ x y p → FiberHom A γ y z q →
      CompTransport B (consEnv x γ) (consEnv y γ) (consEnv z γ)
        (consEnv p (idEnv γ)) (consEnv q (idEnv γ)) (consEnv (A.comp γ p q) (idEnv γ)))
    {f g η : Val} (hf : (semPi A B).Obj γ f) (hg : (semPi A B).Obj γ g)
    (hh : PiHom A B γ f g η) {x y p : Val} (hp : FiberHom A γ x y p) :
    B.reindexMor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
      (B.inv (consEnv x γ) (piMorAt η y x (A.inv γ p))) =
    B.comp (consEnv y γ)
      (piAppMor g x y p)
      (B.inv (consEnv y γ) (piMorAt η y y (idVal y))) := by
  have hpinv := hA.inv_hom hp
  have hg_pinv := semPi_obj_mor_vertical trB hg hpinv
  have hd_y := semPi_hom_diag_vertical hA hiB trB hf hg hh hp.2.1
  have hd_y_tr := (trB y x (A.inv γ p) hpinv).map_hom hd_y
  have hd_y_inv := (hB y hp.2.1).inv_hom hd_y
  rw [piMorAt_decomp_left hA hh hpinv,
    (hB x hp.1).inv_comp_rev hd_y_tr hg_pinv,
    (trB x y p hp).map_comp ((hB x hp.1).inv_hom hg_pinv) ((hB x hp.1).inv_hom hd_y_tr),
    semPi_obj_mor_inv hA hB hiB trB ctB hg hp,
    ← (trB y x (A.inv γ p) hpinv).map_inv (hB y hp.2.1) (hB x hp.1) hd_y,
    (ctB y x y (A.inv γ p) p hpinv hp).comp_mor hd_y_inv,
    hA.inv_comp hp, ← idEnv_consEnv, (hiB y hp.2.1).mor hd_y_inv]

theorem semPi_fiber_laws {A B : SemFam} {γ : Env}
    (hA : FiberLaws A γ) (hiA : IdentityTransport A γ)
    (trA : TransportLaws A γ γ (idEnv γ)) (rkA : RankLaws A γ)
    (hB : ∀ x, A.Obj γ x → FiberLaws B (consEnv x γ))
    (hiB : ∀ x, A.Obj γ x → IdentityTransport B (consEnv x γ))
    (trB : ∀ x y p, FiberHom A γ x y p →
      TransportLaws B (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)))
    (ctB : ∀ x y z p q, FiberHom A γ x y p → FiberHom A γ y z q →
      CompTransport B (consEnv x γ) (consEnv y γ) (consEnv z γ)
        (consEnv p (idEnv γ)) (consEnv q (idEnv γ)) (consEnv (A.comp γ p q) (idEnv γ))) :
    FiberLaws (semPi A B) γ where
  id_hom := semPi_id_hom hiA trA hiB trB
  comp_hom {f g h η₁ η₂} hη₁ hη₂ := by
    have hf := hη₁.1
    have hg := hη₁.2.1
    have hh := hη₂.2.1
    have hh₁ := (semPi_hom_iff hiA trA hiB trB hf).mp hη₁.2.2
    have hh₂ := (semPi_hom_iff hiA trA hiB trB hg).mp hη₂.2.2
    refine ⟨hf, hh, (semPi_hom_iff hiA trA hiB trB hf).mpr ⟨?_, ?_, ?_, ?_⟩⟩
    · dsimp only [semPi]
      exact mkPiMor_ext (fun _ _ _ => Iff.rfl) (fun x y p hp => by
        rw [piMorAt_mkPiMor_of_rk rkA hp])
    · intro x y p hp
      dsimp only [semPi]
      rw [piMorAt_mkPiMor_of_rk rkA hp]
      have hd₁ := (trB x y p hp).map_hom (semPi_hom_diag_vertical hA hiB trB hf hg hh₁ hp.1)
      have hv₂ := semPi_hom_mor_vertical trB hg hh hh₂ hp
      exact ((trB x y p hp).hom_iff (hf.2.1 x hp.1) (hh.2.1 y hp.2.1)).mpr
        ((hB y hp.2.1).comp_hom hd₁ hv₂).2.2
    · intro w x y u p hu hp
      have hup : FiberHom A γ w y (A.comp γ (A.reindexMor γ γ (idEnv γ) u) p) := by
        rw [hiA.mor hu]
        exact hA.comp_hom hu hp
      dsimp only [semPi]
      rw [piMorAt_mkPiMor_of_rk rkA hup, piMorAt_mkPiMor_of_rk rkA hp,
        semPi_comp_alt hA hiA hB hiB trB hf hg hh hh₁ hh₂ hup,
        semPi_comp_alt hA hiA hB hiB trB hf hg hh hh₁ hh₂ hp,
        hh₁.2.2.1 w x y u p hu hp]
      have hfu := (trB x y p hp).map_hom (semPi_obj_mor_vertical trB hf hu)
      have hfu' : FiberHom B (consEnv y γ)
          (B.reindexObj (consEnv w γ) (consEnv y γ) (consEnv (A.comp γ u p) (idEnv γ)) (piAppObj f w))
          (B.reindexObj (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)) (piAppObj f x))
          (B.reindexMor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)) (piAppMor f w x u)) := by
        simpa only [(ctB w x y u p hu hp).comp_obj (hf.2.1 w hu.1)] using hfu
      have hv₁ := semPi_hom_mor_vertical trB hf hg hh₁ hp
      have hd₂ := semPi_hom_diag_vertical hA hiB trB hg hh hh₂ hp.2.1
      exact (hB y hp.2.1).assoc hfu' hv₁ hd₂
    · intro x y z p v hp hv
      have hpv := hA.comp_hom hp hv
      dsimp only [semPi]
      rw [piMorAt_mkPiMor_of_rk rkA hpv, piMorAt_mkPiMor_of_rk rkA hp,
        hh₂.2.2.2 x y z p v hp hv]
      have hd₁_x := semPi_hom_diag_vertical hA hiB trB hf hg hh₁ hp.1
      have hd₁_y := (trB x y p hp).map_hom hd₁_x
      have hv₂_y := semPi_hom_mor_vertical trB hg hh hh₂ hp
      have hhv := semPi_obj_mor_vertical trB hh hv
      rw [← (ctB x y z p v hp hv).comp_mor hd₁_x,
        ← (hB z hv.2.1).assoc ((trB y z v hv).map_hom hd₁_y) ((trB y z v hv).map_hom hv₂_y) hhv,
        ← (trB y z v hv).map_comp hd₁_y hv₂_y]
  inv_hom {f g η} hη := by
    have hf := hη.1
    have hg := hη.2.1
    have hh := (semPi_hom_iff hiA trA hiB trB hf).mp hη.2.2
    refine ⟨hg, hf, (semPi_hom_iff hiA trA hiB trB hg).mpr ⟨?_, ?_, ?_, ?_⟩⟩
    · dsimp only [semPi]
      exact mkPiMor_ext (fun _ _ _ => Iff.rfl) (fun x y p hp => by
        rw [piMorAt_mkPiMor_of_rk rkA hp])
    · intro x y p hp
      dsimp only [semPi]
      rw [piMorAt_mkPiMor_of_rk rkA hp,
        semPi_inv_val_left hA hiA hB hiB trB ctB hf hg hh hp]
      have hd_inv := (trB x y p hp).map_hom
        ((hB x hp.1).inv_hom (semPi_hom_diag_vertical hA hiB trB hf hg hh hp.1))
      have hfv := semPi_obj_mor_vertical trB hf hp
      exact ((trB x y p hp).hom_iff (hg.2.1 x hp.1) (hf.2.1 y hp.2.1)).mpr
        ((hB y hp.2.1).comp_hom hd_inv hfv).2.2
    · intro w x y u p hu hp
      have hup : FiberHom A γ w y (A.comp γ (A.reindexMor γ γ (idEnv γ) u) p) := by
        rw [hiA.mor hu]
        exact hA.comp_hom hu hp
      dsimp only [semPi]
      rw [piMorAt_mkPiMor_of_rk rkA hup, piMorAt_mkPiMor_of_rk rkA hp,
        semPi_inv_val_right hA hB hiB trB ctB hf hg hh hup,
        semPi_inv_val_right hA hB hiB trB ctB hf hg hh hp]
      have hgu : piAppMor g w y (A.comp γ (A.reindexMor γ γ (idEnv γ) u) p) =
          B.comp (consEnv y γ)
            (B.reindexMor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)) (piAppMor g w x u))
            (piAppMor g x y p) := by
        rw [hiA.mor hu]
        exact hg.2.2.2.2 w x y u p hu hp
      have hgu_tr : FiberHom B (consEnv y γ)
          (B.reindexObj (consEnv w γ) (consEnv y γ) (consEnv (A.comp γ u p) (idEnv γ)) (piAppObj g w))
          (B.reindexObj (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)) (piAppObj g x))
          (B.reindexMor (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ)) (piAppMor g w x u)) := by
        simpa only [(ctB w x y u p hu hp).comp_obj (hg.2.1 w hu.1)] using
          (trB x y p hp).map_hom (semPi_obj_mor_vertical trB hg hu)
      have hgp := semPi_obj_mor_vertical trB hg hp
      have hd_inv := (hB y hp.2.1).inv_hom (semPi_hom_diag_vertical hA hiB trB hf hg hh hp.2.1)
      rw [hgu, (hB y hp.2.1).assoc hgu_tr hgp hd_inv]
    · intro x y z p v hp hv
      have hpv := hA.comp_hom hp hv
      dsimp only [semPi]
      rw [piMorAt_mkPiMor_of_rk rkA hpv, piMorAt_mkPiMor_of_rk rkA hp,
        semPi_inv_val_left hA hiA hB hiB trB ctB hf hg hh hpv,
        semPi_inv_val_left hA hiA hB hiB trB ctB hf hg hh hp,
        hf.2.2.2.2 x y z p v hp hv]
      have hd_x := (hB x hp.1).inv_hom (semPi_hom_diag_vertical hA hiB trB hf hg hh hp.1)
      have hd_y := (trB x y p hp).map_hom hd_x
      have hfp_y := semPi_obj_mor_vertical trB hf hp
      have hfv := semPi_obj_mor_vertical trB hf hv
      rw [← (ctB x y z p v hp hv).comp_mor hd_x,
        ← (hB z hv.2.1).assoc ((trB y z v hv).map_hom hd_y) ((trB y z v hv).map_hom hfp_y) hfv,
        ← (trB y z v hv).map_comp hd_y hfp_y]
  id_comp hη := by
    have hf := hη.1
    have hg := hη.2.1
    have hh := (semPi_hom_iff hiA trA hiB trB hf).mp hη.2.2
    dsimp only [semPi]
    refine (mkPiMor_ext (fun _ _ _ => Iff.rfl) ?_).trans hh.1.symm
    intro x y p hp
    have hv := semPi_hom_mor_vertical trB hf hg hh hp
    rw [semPi_id_components hf x x (idVal x), hf.2.2.2.1 x hp.1,
      (trB x y p hp).map_id (hf.2.1 x hp.1), (hB y hp.2.1).id_comp hv]
  comp_id hη := by
    have hf := hη.1
    have hg := hη.2.1
    have hh := (semPi_hom_iff hiA trA hiB trB hf).mp hη.2.2
    dsimp only [semPi]
    refine (mkPiMor_ext (fun _ _ _ => Iff.rfl) ?_).trans hh.1.symm
    intro x y p hp
    rw [semPi_id_components hg x y p, ← piMorAt_decomp_left hA hh hp]
  assoc hη₁ hη₂ hη₃ := by
    have hf₁ := hη₁.1
    have hf₂ := hη₁.2.1
    have hf₃ := hη₂.2.1
    have hf₄ := hη₃.2.1
    have hh₁ := (semPi_hom_iff hiA trA hiB trB hf₁).mp hη₁.2.2
    have hh₂ := (semPi_hom_iff hiA trA hiB trB hf₂).mp hη₂.2.2
    have hh₃ := (semPi_hom_iff hiA trA hiB trB hf₃).mp hη₃.2.2
    dsimp only [semPi]
    refine mkPiMor_ext (fun _ _ _ => Iff.rfl) ?_
    intro x y p hp
    have h_id_x := hA.id_hom hp.1
    rw [piMorAt_mkPiMor_of_rk rkA h_id_x, piMorAt_mkPiMor_of_rk rkA hp]
    have hd₁_x := semPi_hom_diag_vertical hA hiB trB hf₁ hf₂ hh₁ hp.1
    have hd₂_x := semPi_hom_diag_vertical hA hiB trB hf₂ hf₃ hh₂ hp.1
    have hd₁_y := (trB x y p hp).map_hom hd₁_x
    have hd₂_y := (trB x y p hp).map_hom hd₂_x
    have hv₃ := semPi_hom_mor_vertical trB hf₃ hf₄ hh₃ hp
    rw [← idEnv_consEnv, (hiB x hp.1).mor hd₁_x,
      (trB x y p hp).map_comp hd₁_x hd₂_x,
      (hB y hp.2.1).assoc hd₁_y hd₂_y hv₃]
  inv_comp hη := by
    have hf := hη.1
    have hg := hη.2.1
    have hh := (semPi_hom_iff hiA trA hiB trB hf).mp hη.2.2
    have h_id_g := semPi_identity_piHom hiA hg
    dsimp only [semPi]
    refine (mkPiMor_ext (fun _ _ _ => Iff.rfl) ?_).trans h_id_g.1.symm
    intro x y p hp
    have h_id_x := hA.id_hom hp.1
    have hd_x := semPi_hom_diag_vertical hA hiB trB hf hg hh hp.1
    have hd_x_inv := (hB x hp.1).inv_hom hd_x
    have hd_y := (trB x y p hp).map_hom hd_x
    have hd_y_inv := (trB x y p hp).map_hom hd_x_inv
    have hgv := semPi_obj_mor_vertical trB hg hp
    rw [piMorAt_mkPiMor_of_rk rkA h_id_x, hA.inv_id hp.1,
      ← idEnv_consEnv, (hiB x hp.1).mor hd_x_inv,
      piMorAt_decomp_left hA hh hp,
      ← (hB y hp.2.1).assoc hd_y_inv hd_y hgv,
      ← (trB x y p hp).map_comp hd_x_inv hd_x,
      (hB x hp.1).inv_comp hd_x,
      (trB x y p hp).map_id (hg.2.1 x hp.1),
      (hB y hp.2.1).id_comp hgv,
      semPi_id_components hg x y p]
  comp_inv hη := by
    have hf := hη.1
    have hg := hη.2.1
    have hh := (semPi_hom_iff hiA trA hiB trB hf).mp hη.2.2
    have h_id_f := semPi_identity_piHom hiA hf
    dsimp only [semPi]
    refine (mkPiMor_ext (fun _ _ _ => Iff.rfl) ?_).trans h_id_f.1.symm
    intro x y p hp
    have hd_x := semPi_hom_diag_vertical hA hiB trB hf hg hh hp.1
    have hd_x_inv := (hB x hp.1).inv_hom hd_x
    have hd_y := (trB x y p hp).map_hom hd_x
    have hd_y_inv := (trB x y p hp).map_hom hd_x_inv
    have hfv := semPi_obj_mor_vertical trB hf hp
    rw [piMorAt_mkPiMor_of_rk rkA hp,
      semPi_inv_val_left hA hiA hB hiB trB ctB hf hg hh hp,
      ← (hB y hp.2.1).assoc hd_y hd_y_inv hfv,
      ← (trB x y p hp).map_comp hd_x hd_x_inv,
      (hB x hp.1).comp_inv hd_x,
      (trB x y p hp).map_id (hf.2.1 x hp.1),
      (hB y hp.2.1).id_comp hfv,
      semPi_id_components hf x y p]

theorem trB_map_id {A B : SemFam} {γ₁ γ₂ δ : Env}
    (hA₂ : FiberLaws A γ₂) (trA : TransportLaws A γ₁ γ₂ δ)
    (trB_het : ∀ x₁ x₂ p, piHetMor A γ₁ γ₂ δ x₁ x₂ p →
      TransportLaws B (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ))
    {x : Val} (hx : A.Obj γ₁ x) :
    TransportLaws B (consEnv x γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x) γ₂)
      (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x)) δ) := by
  have hx' := trA.map_obj hx
  exact trB_het x (A.reindexObj γ₁ γ₂ δ x) (idVal (A.reindexObj γ₁ γ₂ δ x))
    ⟨hx, hx', (trA.hom_iff hx hx').mpr (hA₂.id_hom hx').2.2⟩

theorem trB_unmap_id {A B : SemFam} {γ₁ γ₂ δ : Env}
    (hA₂ : FiberLaws A γ₂) (trA : TransportLaws A γ₁ γ₂ δ)
    (trB_het : ∀ x₁ x₂ p, piHetMor A γ₁ γ₂ δ x₁ x₂ p →
      TransportLaws B (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ))
    {x' : Val} (hx' : A.Obj γ₂ x') :
    TransportLaws B (consEnv (A.unreindexObj γ₁ γ₂ δ x') γ₁) (consEnv x' γ₂)
      (consEnv (idVal x') δ) := by
  have hx := trA.unmap_obj hx'
  refine trB_het (A.unreindexObj γ₁ γ₂ δ x') x' (idVal x') ⟨hx, hx', (trA.hom_iff hx hx').mpr ?_⟩
  rw [trA.map_unmap_obj hx']
  exact (hA₂.id_hom hx').2.2

theorem trB_map_het {A B : SemFam} {γ₁ γ₂ δ : Env}
    (trA : TransportLaws A γ₁ γ₂ δ)
    (trB_het : ∀ x₁ x₂ p, piHetMor A γ₁ γ₂ δ x₁ x₂ p →
      TransportLaws B (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ))
    {x y p : Val} (hp : FiberHom A γ₁ x y p) :
    TransportLaws B (consEnv x γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂)
      (consEnv (A.reindexMor γ₁ γ₂ δ p) δ) := by
  have hp' := trA.map_hom hp
  exact trB_het x (A.reindexObj γ₁ γ₂ δ y) (A.reindexMor γ₁ γ₂ δ p)
    ⟨hp.1, hp'.2.1, (trA.hom_iff hp.1 hp'.2.1).mpr hp'.2.2⟩

theorem trB_unmap_het {A B : SemFam} {γ₁ γ₂ δ : Env}
    (trA : TransportLaws A γ₁ γ₂ δ)
    (trB_het : ∀ x₁ x₂ p, piHetMor A γ₁ γ₂ δ x₁ x₂ p →
      TransportLaws B (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ))
    {x' y' p' : Val} (hp' : FiberHom A γ₂ x' y' p') :
    TransportLaws B (consEnv (A.unreindexObj γ₁ γ₂ δ x') γ₁) (consEnv y' γ₂)
      (consEnv p' δ) := by
  have hx := trA.unmap_obj hp'.1
  refine trB_het (A.unreindexObj γ₁ γ₂ δ x') y' p' ⟨hx, hp'.2.1, (trA.hom_iff hx hp'.2.1).mpr ?_⟩
  rw [trA.map_unmap_obj hp'.1]
  exact hp'.2.2

theorem ctB_unmap_left {A B : SemFam} {γ₁ γ₂ δ : Env}
    (trA : TransportLaws A γ₁ γ₂ δ)
    (ctB_left : ∀ x₁ x₂ p, FiberHom A γ₁ x₁ x₂ p →
      CompTransport B (consEnv x₁ γ₁) (consEnv x₂ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₂) γ₂)
        (consEnv p (idEnv γ₁)) (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₂)) δ)
        (consEnv (A.reindexMor γ₁ γ₂ δ p) δ))
    {x' y' p' : Val} (hp' : FiberHom A γ₂ x' y' p') :
    CompTransport B (consEnv (A.unreindexObj γ₁ γ₂ δ x') γ₁)
      (consEnv (A.unreindexObj γ₁ γ₂ δ y') γ₁)
      (consEnv y' γ₂)
      (consEnv (A.unreindexMor γ₁ γ₂ δ p') (idEnv γ₁))
      (consEnv (idVal y') δ)
      (consEnv p' δ) := by
  have h := ctB_left _ _ _ (trA.unmap_hom hp')
  rwa [trA.map_unmap_obj hp'.2.1, trA.map_unmap_mor hp'] at h

theorem ctB_unmap_right {A B : SemFam} {γ₁ γ₂ δ : Env}
    (trA : TransportLaws A γ₁ γ₂ δ)
    (ctB_right : ∀ x₁ x₂ p, piHetMor A γ₁ γ₂ δ x₁ x₂ p →
      CompTransport B (consEnv x₁ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₁) γ₂) (consEnv x₂ γ₂)
        (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₁)) δ) (consEnv p (idEnv γ₂))
        (consEnv p δ))
    {x' y' p' : Val} (hp' : FiberHom A γ₂ x' y' p') :
    CompTransport B (consEnv (A.unreindexObj γ₁ γ₂ δ x') γ₁)
      (consEnv x' γ₂)
      (consEnv y' γ₂)
      (consEnv (idVal x') δ)
      (consEnv p' (idEnv γ₂))
      (consEnv p' δ) := by
  have hx := trA.unmap_obj hp'.1
  have hp_het : piHetMor A γ₁ γ₂ δ (A.unreindexObj γ₁ γ₂ δ x') y' p' := by
    refine ⟨hx, hp'.2.1, (trA.hom_iff hx hp'.2.1).mpr ?_⟩
    rw [trA.map_unmap_obj hp'.1]
    exact hp'.2.2
  have h := ctB_right _ _ _ hp_het
  rwa [trA.map_unmap_obj hp'.1] at h

theorem unmap_reindex_comm {A B : SemFam} {γ₁ γ₂ δ : Env}
    (hA₂ : FiberLaws A γ₂) (trA : TransportLaws A γ₁ γ₂ δ)
    (trB₁ : ∀ x y p, FiberHom A γ₁ x y p →
      TransportLaws B (consEnv x γ₁) (consEnv y γ₁) (consEnv p (idEnv γ₁)))
    (trB_het : ∀ x₁ x₂ p, piHetMor A γ₁ γ₂ δ x₁ x₂ p →
      TransportLaws B (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ))
    (ctB_left : ∀ x₁ x₂ p, FiberHom A γ₁ x₁ x₂ p →
      CompTransport B (consEnv x₁ γ₁) (consEnv x₂ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₂) γ₂)
        (consEnv p (idEnv γ₁)) (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₂)) δ)
        (consEnv (A.reindexMor γ₁ γ₂ δ p) δ))
    (ctB_right : ∀ x₁ x₂ p, piHetMor A γ₁ γ₂ δ x₁ x₂ p →
      CompTransport B (consEnv x₁ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₁) γ₂) (consEnv x₂ γ₂)
        (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₁)) δ) (consEnv p (idEnv γ₂))
        (consEnv p δ))
    {y z q : Val} (hq : FiberHom A γ₁ y z q)
    {u' v' m' : Val} (hm' : FiberHom B (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂) u' v' m') :
    B.unreindexMor (consEnv z γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ z) γ₂)
      (consEnv (idVal (A.reindexObj γ₁ γ₂ δ z)) δ)
      (B.reindexMor (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂) (consEnv (A.reindexObj γ₁ γ₂ δ z) γ₂)
        (consEnv (A.reindexMor γ₁ γ₂ δ q) (idEnv γ₂)) m') =
    B.reindexMor (consEnv y γ₁) (consEnv z γ₁) (consEnv q (idEnv γ₁))
      (B.unreindexMor (consEnv y γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂)
        (consEnv (idVal (A.reindexObj γ₁ γ₂ δ y)) δ) m') := by
  have hq' := trA.map_hom hq
  have hq_het : piHetMor A γ₁ γ₂ δ y (A.reindexObj γ₁ γ₂ δ z) (A.reindexMor γ₁ γ₂ δ q) :=
    ⟨hq.1, hq'.2.1, (trA.hom_iff hq.1 hq'.2.1).mpr hq'.2.2⟩
  have hm := (trB_map_id hA₂ trA trB_het hq.1).unmap_hom hm'
  have hm_q := (trB₁ y z q hq).map_hom hm
  have h1 := (ctB_right _ _ _ hq_het).comp_mor hm
  rw [(trB_map_id hA₂ trA trB_het hq.1).map_unmap_mor hm'] at h1
  rw [h1, ← (ctB_left y z q hq).comp_mor hm,
    (trB_map_id hA₂ trA trB_het hq.2.1).unmap_map_mor hm_q]

theorem semPi_transport_laws {A B : SemFam} {γ₁ γ₂ δ : Env}
    (hA₁ : FiberLaws A γ₁) (hA₂ : FiberLaws A γ₂)
    (hiA₁ : IdentityTransport A γ₁) (hiA₂ : IdentityTransport A γ₂)
    (trA₁ : TransportLaws A γ₁ γ₁ (idEnv γ₁)) (trA₂ : TransportLaws A γ₂ γ₂ (idEnv γ₂))
    (rkA₁ : RankLaws A γ₁) (rkA₂ : RankLaws A γ₂)
    (trA : TransportLaws A γ₁ γ₂ δ)
    (hB₁ : ∀ x, A.Obj γ₁ x → FiberLaws B (consEnv x γ₁))
    (hiB₁ : ∀ x, A.Obj γ₁ x → IdentityTransport B (consEnv x γ₁))
    (hiB₂ : ∀ x, A.Obj γ₂ x → IdentityTransport B (consEnv x γ₂))
    (trB₁ : ∀ x y p, FiberHom A γ₁ x y p →
      TransportLaws B (consEnv x γ₁) (consEnv y γ₁) (consEnv p (idEnv γ₁)))
    (trB₂ : ∀ x y p, FiberHom A γ₂ x y p →
      TransportLaws B (consEnv x γ₂) (consEnv y γ₂) (consEnv p (idEnv γ₂)))
    (trB_het : ∀ x₁ x₂ p, piHetMor A γ₁ γ₂ δ x₁ x₂ p →
      TransportLaws B (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ))
    (ctB_left : ∀ x₁ x₂ p, FiberHom A γ₁ x₁ x₂ p →
      CompTransport B (consEnv x₁ γ₁) (consEnv x₂ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₂) γ₂)
        (consEnv p (idEnv γ₁)) (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₂)) δ)
        (consEnv (A.reindexMor γ₁ γ₂ δ p) δ))
    (ctB_right : ∀ x₁ x₂ p, piHetMor A γ₁ γ₂ δ x₁ x₂ p →
      CompTransport B (consEnv x₁ γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x₁) γ₂) (consEnv x₂ γ₂)
        (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x₁)) δ) (consEnv p (idEnv γ₂))
        (consEnv p δ)) :
    TransportLaws (semPi A B) γ₁ γ₂ δ := by
  have h_map_obj : ∀ {f}, (semPi A B).Obj γ₁ f → (semPi A B).Obj γ₂ ((semPi A B).reindexObj γ₁ γ₂ δ f) := by
    intro f hf
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [semPi]
      exact mkPiObj_ext (fun _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
        (fun x' hx' => by rw [piAppObj_mkPiObj_of_rk rkA₂ hx'])
        (fun x' y' p' hp' => by rw [piAppMor_mkPiObj_of_rk rkA₂ hp'])
    · intro x' hx'
      dsimp only [semPi]
      rw [piAppObj_mkPiObj_of_rk rkA₂ hx']
      exact (trB_unmap_id hA₂ trA trB_het hx').map_obj (hf.2.1 _ (trA.unmap_obj hx'))
    · intro x' y' p' hp'
      have hp := trA.unmap_hom hp'
      have hfv := semPi_obj_mor_vertical trB₁ hf hp
      have hfv' := (trB_unmap_id hA₂ trA trB_het hp'.2.1).map_hom hfv
      have hdom : B.reindexObj (consEnv (A.unreindexObj γ₁ γ₂ δ y') γ₁) (consEnv y' γ₂)
          (consEnv (idVal y') δ)
          (B.reindexObj (consEnv (A.unreindexObj γ₁ γ₂ δ x') γ₁)
            (consEnv (A.unreindexObj γ₁ γ₂ δ y') γ₁)
            (consEnv (A.unreindexMor γ₁ γ₂ δ p') (idEnv γ₁))
            (piAppObj f (A.unreindexObj γ₁ γ₂ δ x'))) =
        B.reindexObj (consEnv x' γ₂) (consEnv y' γ₂) (consEnv p' (idEnv γ₂))
          (B.reindexObj (consEnv (A.unreindexObj γ₁ γ₂ δ x') γ₁) (consEnv x' γ₂)
            (consEnv (idVal x') δ)
            (piAppObj f (A.unreindexObj γ₁ γ₂ δ x'))) := by
        rw [(ctB_unmap_left trA ctB_left hp').comp_obj (hf.2.1 _ hp.1),
          (ctB_unmap_right trA ctB_right hp').comp_obj (hf.2.1 _ hp.1)]
      dsimp only [semPi]
      rw [piAppObj_mkPiObj_of_rk rkA₂ hp'.1, piAppObj_mkPiObj_of_rk rkA₂ hp'.2.1,
        piAppMor_mkPiObj_of_rk rkA₂ hp']
      have hfv'' : FiberHom B (consEnv y' γ₂)
          (B.reindexObj (consEnv x' γ₂) (consEnv y' γ₂) (consEnv p' (idEnv γ₂))
            (B.reindexObj (consEnv (A.unreindexObj γ₁ γ₂ δ x') γ₁) (consEnv x' γ₂)
              (consEnv (idVal x') δ)
              (piAppObj f (A.unreindexObj γ₁ γ₂ δ x'))))
          (B.reindexObj (consEnv (A.unreindexObj γ₁ γ₂ δ y') γ₁) (consEnv y' γ₂)
            (consEnv (idVal y') δ)
            (piAppObj f (A.unreindexObj γ₁ γ₂ δ y')))
          (B.reindexMor (consEnv (A.unreindexObj γ₁ γ₂ δ y') γ₁) (consEnv y' γ₂)
            (consEnv (idVal y') δ)
            (piAppMor f (A.unreindexObj γ₁ γ₂ δ x') (A.unreindexObj γ₁ γ₂ δ y')
              (A.unreindexMor γ₁ γ₂ δ p'))) := by
        simpa only [hdom] using hfv'
      exact ((trB₂ x' y' p' hp').hom_iff
        ((trB_unmap_id hA₂ trA trB_het hp'.1).map_obj (hf.2.1 _ hp.1)) hfv''.2.1).mpr hfv''.2.2
    · intro x' hx'
      have hx := trA.unmap_obj hx'
      dsimp only [semPi]
      rw [piAppObj_mkPiObj_of_rk rkA₂ hx', piAppMor_mkPiObj_of_rk rkA₂ (hA₂.id_hom hx'),
        trA.unmap_id hA₁ hx', hf.2.2.2.1 _ hx,
        (trB_unmap_id hA₂ trA trB_het hx').map_id (hf.2.1 _ hx)]
    · intro x' y' z' p' q' hp' hq'
      have hp := trA.unmap_hom hp'
      have hq := trA.unmap_hom hq'
      have hpq' := hA₂.comp_hom hp' hq'
      have hfp := semPi_obj_mor_vertical trB₁ hf hp
      have hfq := semPi_obj_mor_vertical trB₁ hf hq
      have hfp_q := (trB₁ _ _ _ hq).map_hom hfp
      dsimp only [semPi]
      rw [piAppMor_mkPiObj_of_rk rkA₂ hpq', piAppMor_mkPiObj_of_rk rkA₂ hp',
        piAppMor_mkPiObj_of_rk rkA₂ hq',
        trA.unmap_comp hA₁ hp' hq', hf.2.2.2.2 _ _ _ _ _ hp hq,
        (trB_unmap_id hA₂ trA trB_het hq'.2.1).map_comp hfp_q hfq,
        (ctB_unmap_left trA ctB_left hq').comp_mor hfp,
        (ctB_unmap_right trA ctB_right hq').comp_mor hfp]
  have h_unmap_obj : ∀ {f'}, (semPi A B).Obj γ₂ f' → (semPi A B).Obj γ₁ ((semPi A B).unreindexObj γ₁ γ₂ δ f') := by
    intro f' hf'
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [semPi]
      exact mkPiObj_ext (fun _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
        (fun x hx => by rw [piAppObj_mkPiObj_of_rk rkA₁ hx])
        (fun x y p hp => by rw [piAppMor_mkPiObj_of_rk rkA₁ hp])
    · intro x hx
      dsimp only [semPi]
      rw [piAppObj_mkPiObj_of_rk rkA₁ hx]
      exact (trB_map_id hA₂ trA trB_het hx).unmap_obj (hf'.2.1 _ (trA.map_obj hx))
    · intro x y p hp
      have hp' := trA.map_hom hp
      have hf'v := semPi_obj_mor_vertical trB₂ hf' hp'
      have hy₁ := (trB_map_id hA₂ trA trB_het hp.1).unmap_obj (hf'.2.1 _ hp'.1)
      have hy₂ := (trB_map_id hA₂ trA trB_het hp.2.1).unmap_obj (hf'.2.1 _ hp'.2.1)
      have hp_het : piHetMor A γ₁ γ₂ δ x (A.reindexObj γ₁ γ₂ δ y) (A.reindexMor γ₁ γ₂ δ p) :=
        ⟨hp.1, hp'.2.1, (trA.hom_iff hp.1 hp'.2.1).mpr hp'.2.2⟩
      have hdom : B.reindexObj (consEnv (A.reindexObj γ₁ γ₂ δ x) γ₂)
          (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂)
          (consEnv (A.reindexMor γ₁ γ₂ δ p) (idEnv γ₂))
          (piAppObj f' (A.reindexObj γ₁ γ₂ δ x)) =
        B.reindexObj (consEnv y γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂)
          (consEnv (idVal (A.reindexObj γ₁ γ₂ δ y)) δ)
          (B.reindexObj (consEnv x γ₁) (consEnv y γ₁) (consEnv p (idEnv γ₁))
            (B.unreindexObj (consEnv x γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x) γ₂)
              (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x)) δ)
              (piAppObj f' (A.reindexObj γ₁ γ₂ δ x)))) := by
        have h1 := (ctB_left x y p hp).comp_obj hy₁
        have h2 := (ctB_right x _ _ hp_het).comp_obj hy₁
        rw [(trB_map_id hA₂ trA trB_het hp.1).map_unmap_obj (hf'.2.1 _ hp'.1)] at h2
        exact h2.trans h1.symm
      have hf'v_rew : FiberHom B (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂)
          (B.reindexObj (consEnv y γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂)
            (consEnv (idVal (A.reindexObj γ₁ γ₂ δ y)) δ)
            (B.reindexObj (consEnv x γ₁) (consEnv y γ₁) (consEnv p (idEnv γ₁))
              (B.unreindexObj (consEnv x γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x) γ₂)
                (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x)) δ)
                (piAppObj f' (A.reindexObj γ₁ γ₂ δ x)))))
          (piAppObj f' (A.reindexObj γ₁ γ₂ δ y))
          (piAppMor f' (A.reindexObj γ₁ γ₂ δ x) (A.reindexObj γ₁ γ₂ δ y)
            (A.reindexMor γ₁ γ₂ δ p)) := by
        simpa only [← hdom] using hf'v
      have hfv := (trB_map_id hA₂ trA trB_het hp.2.1).unmap_hom hf'v_rew
      rw [(trB_map_id hA₂ trA trB_het hp.2.1).unmap_map_obj ((trB₁ x y p hp).map_obj hy₁)] at hfv
      dsimp only [semPi]
      rw [piAppObj_mkPiObj_of_rk rkA₁ hp.1, piAppObj_mkPiObj_of_rk rkA₁ hp.2.1,
        piAppMor_mkPiObj_of_rk rkA₁ hp]
      exact ((trB₁ x y p hp).hom_iff hy₁ hy₂).mpr hfv.2.2
    · intro x hx
      have hx' := trA.map_obj hx
      dsimp only [semPi]
      rw [piAppObj_mkPiObj_of_rk rkA₁ hx, piAppMor_mkPiObj_of_rk rkA₁ (hA₁.id_hom hx),
        trA.map_id hx, hf'.2.2.2.1 _ hx',
        (trB_map_id hA₂ trA trB_het hx).unmap_id (hB₁ x hx) (hf'.2.1 _ hx')]
    · intro x y z p q hp hq
      have hp' := trA.map_hom hp
      have hq' := trA.map_hom hq
      have hpq := hA₁.comp_hom hp hq
      have hf'p := semPi_obj_mor_vertical trB₂ hf' hp'
      have hf'q := semPi_obj_mor_vertical trB₂ hf' hq'
      have hf'p_q := (trB₂ _ _ _ hq').map_hom hf'p
      dsimp only [semPi]
      rw [piAppMor_mkPiObj_of_rk rkA₁ hpq, piAppMor_mkPiObj_of_rk rkA₁ hp,
        piAppMor_mkPiObj_of_rk rkA₁ hq,
        trA.map_comp hp hq, hf'.2.2.2.2 _ _ _ _ _ hp' hq',
        (trB_map_id hA₂ trA trB_het hq.2.1).unmap_comp (hB₁ z hq.2.1) hf'p_q hf'q,
        unmap_reindex_comm hA₂ trA trB₁ trB_het ctB_left ctB_right hq hf'p]
  refine
    { map_obj := h_map_obj
      unmap_obj := h_unmap_obj
      map_hom := ?_
      unmap_hom := ?_
      unmap_map_obj := ?_
      map_unmap_obj := ?_
      unmap_map_mor := ?_
      map_unmap_mor := ?_
      map_id := ?_
      map_comp := ?_
      hom_iff := fun hf _ => (semPi_hom_iff hiA₂ trA₂ hiB₂ trB₂ (h_map_obj hf)).symm }
  · intro f g η hη
    have hf := hη.1
    have hg := hη.2.1
    have hh := (semPi_hom_iff hiA₁ trA₁ hiB₁ trB₁ hf).mp hη.2.2
    have hf' := h_map_obj hf
    have hg' := h_map_obj hg
    refine ⟨hf', hg', (semPi_hom_iff hiA₂ trA₂ hiB₂ trB₂ hf').mpr ⟨?_, ?_, ?_, ?_⟩⟩
    · dsimp only [semPi]
      exact mkPiMor_ext (fun _ _ _ => Iff.rfl) (fun x' y' p' hp' => by
        rw [piMorAt_mkPiMor_of_rk rkA₂ hp'])
    · intro x' y' p' hp'
      have hp := trA.unmap_hom hp'
      have hv := semPi_hom_mor_vertical trB₁ hf hg hh hp
      have hv' := (trB_unmap_id hA₂ trA trB_het hp'.2.1).map_hom hv
      have hdom : B.reindexObj (consEnv (A.unreindexObj γ₁ γ₂ δ y') γ₁) (consEnv y' γ₂)
          (consEnv (idVal y') δ)
          (B.reindexObj (consEnv (A.unreindexObj γ₁ γ₂ δ x') γ₁)
            (consEnv (A.unreindexObj γ₁ γ₂ δ y') γ₁)
            (consEnv (A.unreindexMor γ₁ γ₂ δ p') (idEnv γ₁))
            (piAppObj f (A.unreindexObj γ₁ γ₂ δ x'))) =
        B.reindexObj (consEnv x' γ₂) (consEnv y' γ₂) (consEnv p' (idEnv γ₂))
          (B.reindexObj (consEnv (A.unreindexObj γ₁ γ₂ δ x') γ₁) (consEnv x' γ₂)
            (consEnv (idVal x') δ)
            (piAppObj f (A.unreindexObj γ₁ γ₂ δ x'))) := by
        rw [(ctB_unmap_left trA ctB_left hp').comp_obj (hf.2.1 _ hp.1),
          (ctB_unmap_right trA ctB_right hp').comp_obj (hf.2.1 _ hp.1)]
      dsimp only [semPi]
      rw [piAppObj_mkPiObj_of_rk rkA₂ hp'.1, piAppObj_mkPiObj_of_rk rkA₂ hp'.2.1,
        piMorAt_mkPiMor_of_rk rkA₂ hp']
      have hv'' : FiberHom B (consEnv y' γ₂)
          (B.reindexObj (consEnv x' γ₂) (consEnv y' γ₂) (consEnv p' (idEnv γ₂))
            (B.reindexObj (consEnv (A.unreindexObj γ₁ γ₂ δ x') γ₁) (consEnv x' γ₂)
              (consEnv (idVal x') δ)
              (piAppObj f (A.unreindexObj γ₁ γ₂ δ x'))))
          (B.reindexObj (consEnv (A.unreindexObj γ₁ γ₂ δ y') γ₁) (consEnv y' γ₂)
            (consEnv (idVal y') δ)
            (piAppObj g (A.unreindexObj γ₁ γ₂ δ y')))
          (B.reindexMor (consEnv (A.unreindexObj γ₁ γ₂ δ y') γ₁) (consEnv y' γ₂)
            (consEnv (idVal y') δ)
            (piMorAt η (A.unreindexObj γ₁ γ₂ δ x') (A.unreindexObj γ₁ γ₂ δ y')
              (A.unreindexMor γ₁ γ₂ δ p'))) := by
        simpa only [hdom] using hv'
      exact ((trB₂ x' y' p' hp').hom_iff
        ((trB_unmap_id hA₂ trA trB_het hp'.1).map_obj (hf.2.1 _ hp.1)) hv''.2.1).mpr hv''.2.2
    · intro w' x' y' u' p' hu' hp'
      have hu := trA.unmap_hom hu'
      have hp := trA.unmap_hom hp'
      have hup' : FiberHom A γ₂ w' y' (A.comp γ₂ (A.reindexMor γ₂ γ₂ (idEnv γ₂) u') p') := by
        rw [hiA₂.mor hu']
        exact hA₂.comp_hom hu' hp'
      have hfu := semPi_obj_mor_vertical trB₁ hf hu
      have hfu_p := (trB₁ _ _ _ hp).map_hom hfu
      have hv := semPi_hom_mor_vertical trB₁ hf hg hh hp
      have hnat : piMorAt η (A.unreindexObj γ₁ γ₂ δ w') (A.unreindexObj γ₁ γ₂ δ y')
          (A.comp γ₁ (A.unreindexMor γ₁ γ₂ δ u') (A.unreindexMor γ₁ γ₂ δ p')) =
        B.comp (consEnv (A.unreindexObj γ₁ γ₂ δ y') γ₁)
          (B.reindexMor (consEnv (A.unreindexObj γ₁ γ₂ δ x') γ₁)
            (consEnv (A.unreindexObj γ₁ γ₂ δ y') γ₁)
            (consEnv (A.unreindexMor γ₁ γ₂ δ p') (idEnv γ₁))
            (piAppMor f (A.unreindexObj γ₁ γ₂ δ w') (A.unreindexObj γ₁ γ₂ δ x')
              (A.unreindexMor γ₁ γ₂ δ u')))
          (piMorAt η (A.unreindexObj γ₁ γ₂ δ x') (A.unreindexObj γ₁ γ₂ δ y')
            (A.unreindexMor γ₁ γ₂ δ p')) := by
        have h := hh.2.2.1 _ _ _ _ _ hu hp
        rwa [hiA₁.mor hu] at h
      dsimp only [semPi]
      rw [piMorAt_mkPiMor_of_rk rkA₂ hup', piMorAt_mkPiMor_of_rk rkA₂ hp',
        piAppMor_mkPiObj_of_rk rkA₂ hu', hiA₂.mor hu',
        trA.unmap_comp hA₁ hu' hp', hnat,
        (trB_unmap_id hA₂ trA trB_het hp'.2.1).map_comp hfu_p hv,
        (ctB_unmap_left trA ctB_left hp').comp_mor hfu,
        (ctB_unmap_right trA ctB_right hp').comp_mor hfu]
    · intro x' y' z' p' v' hp' hv'
      have hp := trA.unmap_hom hp'
      have hv := trA.unmap_hom hv'
      have hpv' := hA₂.comp_hom hp' hv'
      have hηp := semPi_hom_mor_vertical trB₁ hf hg hh hp
      have hηp_v := (trB₁ _ _ _ hv).map_hom hηp
      have hgv := semPi_obj_mor_vertical trB₁ hg hv
      dsimp only [semPi]
      rw [piMorAt_mkPiMor_of_rk rkA₂ hpv', piMorAt_mkPiMor_of_rk rkA₂ hp',
        piAppMor_mkPiObj_of_rk rkA₂ hv',
        trA.unmap_comp hA₁ hp' hv', hh.2.2.2 _ _ _ _ _ hp hv,
        (trB_unmap_id hA₂ trA trB_het hv'.2.1).map_comp hηp_v hgv,
        (ctB_unmap_left trA ctB_left hv').comp_mor hηp,
        (ctB_unmap_right trA ctB_right hv').comp_mor hηp]
  · intro f' g' η' hη'
    have hf' := hη'.1
    have hg' := hη'.2.1
    have hh' := (semPi_hom_iff hiA₂ trA₂ hiB₂ trB₂ hf').mp hη'.2.2
    have hf := h_unmap_obj hf'
    have hg := h_unmap_obj hg'
    refine ⟨hf, hg, (semPi_hom_iff hiA₁ trA₁ hiB₁ trB₁ hf).mpr ⟨?_, ?_, ?_, ?_⟩⟩
    · dsimp only [semPi]
      exact mkPiMor_ext (fun _ _ _ => Iff.rfl) (fun x y p hp => by
        rw [piMorAt_mkPiMor_of_rk rkA₁ hp])
    · intro x y p hp
      have hp' := trA.map_hom hp
      have hv' := semPi_hom_mor_vertical trB₂ hf' hg' hh' hp'
      have hy₁ := (trB_map_id hA₂ trA trB_het hp.1).unmap_obj (hf'.2.1 _ hp'.1)
      have hy₂ := (trB_map_id hA₂ trA trB_het hp.2.1).unmap_obj (hg'.2.1 _ hp'.2.1)
      have hp_het : piHetMor A γ₁ γ₂ δ x (A.reindexObj γ₁ γ₂ δ y) (A.reindexMor γ₁ γ₂ δ p) :=
        ⟨hp.1, hp'.2.1, (trA.hom_iff hp.1 hp'.2.1).mpr hp'.2.2⟩
      have hdom : B.reindexObj (consEnv (A.reindexObj γ₁ γ₂ δ x) γ₂)
          (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂)
          (consEnv (A.reindexMor γ₁ γ₂ δ p) (idEnv γ₂))
          (piAppObj f' (A.reindexObj γ₁ γ₂ δ x)) =
        B.reindexObj (consEnv y γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂)
          (consEnv (idVal (A.reindexObj γ₁ γ₂ δ y)) δ)
          (B.reindexObj (consEnv x γ₁) (consEnv y γ₁) (consEnv p (idEnv γ₁))
            (B.unreindexObj (consEnv x γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x) γ₂)
              (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x)) δ)
              (piAppObj f' (A.reindexObj γ₁ γ₂ δ x)))) := by
        have h1 := (ctB_left x y p hp).comp_obj hy₁
        have h2 := (ctB_right x _ _ hp_het).comp_obj hy₁
        rw [(trB_map_id hA₂ trA trB_het hp.1).map_unmap_obj (hf'.2.1 _ hp'.1)] at h2
        exact h2.trans h1.symm
      have hv'_rew : FiberHom B (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂)
          (B.reindexObj (consEnv y γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂)
            (consEnv (idVal (A.reindexObj γ₁ γ₂ δ y)) δ)
            (B.reindexObj (consEnv x γ₁) (consEnv y γ₁) (consEnv p (idEnv γ₁))
              (B.unreindexObj (consEnv x γ₁) (consEnv (A.reindexObj γ₁ γ₂ δ x) γ₂)
                (consEnv (idVal (A.reindexObj γ₁ γ₂ δ x)) δ)
                (piAppObj f' (A.reindexObj γ₁ γ₂ δ x)))))
          (piAppObj g' (A.reindexObj γ₁ γ₂ δ y))
          (piMorAt η' (A.reindexObj γ₁ γ₂ δ x) (A.reindexObj γ₁ γ₂ δ y)
            (A.reindexMor γ₁ γ₂ δ p)) := by
        simpa only [← hdom] using hv'
      have hv := (trB_map_id hA₂ trA trB_het hp.2.1).unmap_hom hv'_rew
      rw [(trB_map_id hA₂ trA trB_het hp.2.1).unmap_map_obj ((trB₁ x y p hp).map_obj hy₁)] at hv
      dsimp only [semPi]
      rw [piAppObj_mkPiObj_of_rk rkA₁ hp.1, piAppObj_mkPiObj_of_rk rkA₁ hp.2.1,
        piMorAt_mkPiMor_of_rk rkA₁ hp]
      exact ((trB₁ x y p hp).hom_iff hy₁ hy₂).mpr hv.2.2
    · intro w x y u p hu hp
      have hu' := trA.map_hom hu
      have hp' := trA.map_hom hp
      have hup : FiberHom A γ₁ w y (A.comp γ₁ (A.reindexMor γ₁ γ₁ (idEnv γ₁) u) p) := by
        rw [hiA₁.mor hu]
        exact hA₁.comp_hom hu hp
      have hf'u := semPi_obj_mor_vertical trB₂ hf' hu'
      have hf'u_p := (trB₂ _ _ _ hp').map_hom hf'u
      have hv' := semPi_hom_mor_vertical trB₂ hf' hg' hh' hp'
      have hnat' : piMorAt η' (A.reindexObj γ₁ γ₂ δ w) (A.reindexObj γ₁ γ₂ δ y)
          (A.comp γ₂ (A.reindexMor γ₁ γ₂ δ u) (A.reindexMor γ₁ γ₂ δ p)) =
        B.comp (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂)
          (B.reindexMor (consEnv (A.reindexObj γ₁ γ₂ δ x) γ₂)
            (consEnv (A.reindexObj γ₁ γ₂ δ y) γ₂)
            (consEnv (A.reindexMor γ₁ γ₂ δ p) (idEnv γ₂))
            (piAppMor f' (A.reindexObj γ₁ γ₂ δ w) (A.reindexObj γ₁ γ₂ δ x)
              (A.reindexMor γ₁ γ₂ δ u)))
          (piMorAt η' (A.reindexObj γ₁ γ₂ δ x) (A.reindexObj γ₁ γ₂ δ y)
            (A.reindexMor γ₁ γ₂ δ p)) := by
        have h := hh'.2.2.1 _ _ _ _ _ hu' hp'
        rwa [hiA₂.mor hu'] at h
      dsimp only [semPi]
      rw [piMorAt_mkPiMor_of_rk rkA₁ hup, piMorAt_mkPiMor_of_rk rkA₁ hp,
        piAppMor_mkPiObj_of_rk rkA₁ hu, hiA₁.mor hu,
        trA.map_comp hu hp, hnat',
        (trB_map_id hA₂ trA trB_het hp.2.1).unmap_comp (hB₁ y hp.2.1) hf'u_p hv',
        unmap_reindex_comm hA₂ trA trB₁ trB_het ctB_left ctB_right hp hf'u]
    · intro x y z p v hp hv
      have hp' := trA.map_hom hp
      have hv' := trA.map_hom hv
      have hpv := hA₁.comp_hom hp hv
      have hη'p := semPi_hom_mor_vertical trB₂ hf' hg' hh' hp'
      have hη'p_v := (trB₂ _ _ _ hv').map_hom hη'p
      have hg'v := semPi_obj_mor_vertical trB₂ hg' hv'
      dsimp only [semPi]
      rw [piMorAt_mkPiMor_of_rk rkA₁ hpv, piMorAt_mkPiMor_of_rk rkA₁ hp,
        piAppMor_mkPiObj_of_rk rkA₁ hv,
        trA.map_comp hp hv, hh'.2.2.2 _ _ _ _ _ hp' hv',
        (trB_map_id hA₂ trA trB_het hv.2.1).unmap_comp (hB₁ z hv.2.1) hη'p_v hg'v,
        unmap_reindex_comm hA₂ trA trB₁ trB_het ctB_left ctB_right hv hη'p]
  · intro f hf
    dsimp only [semPi]
    refine (mkPiObj_ext (fun _ => Iff.rfl) (fun _ _ _ => Iff.rfl) ?_ ?_).trans hf.1.symm
    · intro x hx
      rw [piAppObj_mkPiObj_of_rk rkA₂ (trA.map_obj hx),
        trA.unmap_map_obj hx,
        (trB_map_id hA₂ trA trB_het hx).unmap_map_obj (hf.2.1 x hx)]
    · intro x y p hp
      rw [piAppMor_mkPiObj_of_rk rkA₂ (trA.map_hom hp),
        trA.unmap_map_obj hp.1, trA.unmap_map_obj hp.2.1, trA.unmap_map_mor hp,
        (trB_map_id hA₂ trA trB_het hp.2.1).unmap_map_mor (semPi_obj_mor_vertical trB₁ hf hp)]
  · intro f' hf'
    dsimp only [semPi]
    refine (mkPiObj_ext (fun _ => Iff.rfl) (fun _ _ _ => Iff.rfl) ?_ ?_).trans hf'.1.symm
    · intro x' hx'
      rw [piAppObj_mkPiObj_of_rk rkA₁ (trA.unmap_obj hx'),
        trA.map_unmap_obj hx',
        (trB_unmap_id hA₂ trA trB_het hx').map_unmap_obj (hf'.2.1 x' hx')]
    · intro x' y' p' hp'
      rw [piAppMor_mkPiObj_of_rk rkA₁ (trA.unmap_hom hp'),
        trA.map_unmap_obj hp'.1, trA.map_unmap_obj hp'.2.1, trA.map_unmap_mor hp',
        (trB_unmap_id hA₂ trA trB_het hp'.2.1).map_unmap_mor (semPi_obj_mor_vertical trB₂ hf' hp')]
  · intro f g η hη
    have hh := (semPi_hom_iff hiA₁ trA₁ hiB₁ trB₁ hη.1).mp hη.2.2
    dsimp only [semPi]
    refine (mkPiMor_ext (fun _ _ _ => Iff.rfl) ?_).trans hh.1.symm
    intro x y p hp
    rw [piMorAt_mkPiMor_of_rk rkA₂ (trA.map_hom hp),
      trA.unmap_map_obj hp.1, trA.unmap_map_obj hp.2.1, trA.unmap_map_mor hp,
      (trB_map_id hA₂ trA trB_het hp.2.1).unmap_map_mor
        (semPi_hom_mor_vertical trB₁ hη.1 hη.2.1 hh hp)]
  · intro f' g' η' hη'
    have hh' := (semPi_hom_iff hiA₂ trA₂ hiB₂ trB₂ hη'.1).mp hη'.2.2
    dsimp only [semPi]
    refine (mkPiMor_ext (fun _ _ _ => Iff.rfl) ?_).trans hh'.1.symm
    intro x' y' p' hp'
    rw [piMorAt_mkPiMor_of_rk rkA₁ (trA.unmap_hom hp'),
      trA.map_unmap_obj hp'.1, trA.map_unmap_obj hp'.2.1, trA.map_unmap_mor hp',
      (trB_unmap_id hA₂ trA trB_het hp'.2.1).map_unmap_mor
        (semPi_hom_mor_vertical trB₂ hη'.1 hη'.2.1 hh' hp')]
  · intro f hf
    dsimp only [semPi, idVal_mkPiObj]
    refine mkPiMor_ext (fun _ _ _ => Iff.rfl) ?_
    intro x' y' p' hp'
    rw [semPi_id_components hf]
  · intro f g h η₁ η₂ hη₁ hη₂
    have hf := hη₁.1
    have hg := hη₁.2.1
    have hh := hη₂.2.1
    have hh₁ := (semPi_hom_iff hiA₁ trA₁ hiB₁ trB₁ hf).mp hη₁.2.2
    have hh₂ := (semPi_hom_iff hiA₁ trA₁ hiB₁ trB₁ hg).mp hη₂.2.2
    dsimp only [semPi]
    refine mkPiMor_ext (fun _ _ _ => Iff.rfl) ?_
    intro x' y' p' hp'
    have hp := trA.unmap_hom hp'
    have hd₁_x := semPi_hom_diag_vertical hA₁ hiB₁ trB₁ hf hg hh₁ hp.1
    have hd₁_y := (trB₁ _ _ _ hp).map_hom hd₁_x
    have hv₂ := semPi_hom_mor_vertical trB₁ hg hh hh₂ hp
    rw [piMorAt_mkPiMor_of_rk rkA₁ hp,
      piMorAt_mkPiMor_of_rk rkA₂ (hA₂.id_hom hp'.1),
      piMorAt_mkPiMor_of_rk rkA₂ hp',
      trA.unmap_id hA₁ hp'.1,
      (trB_unmap_id hA₂ trA trB_het hp'.2.1).map_comp hd₁_y hv₂,
      (ctB_unmap_left trA ctB_left hp').comp_mor hd₁_x,
      (ctB_unmap_right trA ctB_right hp').comp_mor hd₁_x]

theorem semPi_comp_transport {A B : SemFam} {γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ : Env}
    (hiA₁ : IdentityTransport A γ₁) (trA₁ : TransportLaws A γ₁ γ₁ (idEnv γ₁))
    (rkA₂ : RankLaws A γ₂)
    (trA₁₂ : TransportLaws A γ₁ γ₂ δ₁₂) (trA₂₃ : TransportLaws A γ₂ γ₃ δ₂₃)
    (trA₁₃ : TransportLaws A γ₁ γ₃ δ₁₃)
    (ctA : CompTransport A γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃)
    (hiB₁ : ∀ x, A.Obj γ₁ x → IdentityTransport B (consEnv x γ₁))
    (trB₁ : ∀ x y p, FiberHom A γ₁ x y p →
      TransportLaws B (consEnv x γ₁) (consEnv y γ₁) (consEnv p (idEnv γ₁)))
    (ctB_unmap : ∀ x₃, A.Obj γ₃ x₃ →
      CompTransport B (consEnv (A.unreindexObj γ₁ γ₃ δ₁₃ x₃) γ₁)
        (consEnv (A.unreindexObj γ₂ γ₃ δ₂₃ x₃) γ₂)
        (consEnv x₃ γ₃)
        (consEnv (idVal (A.unreindexObj γ₂ γ₃ δ₂₃ x₃)) δ₁₂)
        (consEnv (idVal x₃) δ₂₃)
        (consEnv (idVal x₃) δ₁₃)) :
    CompTransport (semPi A B) γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ where
  comp_obj {f} hf := by
    dsimp only [semPi]
    refine mkPiObj_ext (fun _ => Iff.rfl) (fun _ _ _ => Iff.rfl) ?_ ?_
    · intro x₃ hx₃
      have hx₂ := trA₂₃.unmap_obj hx₃
      have hx_eq := ctA.uncomp_obj trA₁₂ trA₂₃ trA₁₃ hx₃
      rw [piAppObj_mkPiObj_of_rk rkA₂ hx₂, hx_eq]
      have hx₁ : A.Obj γ₁ (A.unreindexObj γ₁ γ₃ δ₁₃ x₃) := trA₁₃.unmap_obj hx₃
      exact (ctB_unmap x₃ hx₃).comp_obj (hf.2.1 _ hx₁)
    · intro x₃ y₃ p₃ hp₃
      have hp₂ := trA₂₃.unmap_hom hp₃
      have hx_eq := ctA.uncomp_obj trA₁₂ trA₂₃ trA₁₃ hp₃.1
      have hy_eq := ctA.uncomp_obj trA₁₂ trA₂₃ trA₁₃ hp₃.2.1
      have hp_eq := ctA.uncomp_mor trA₁₂ trA₂₃ trA₁₃ hp₃
      rw [piAppMor_mkPiObj_of_rk rkA₂ hp₂, hx_eq, hy_eq, hp_eq]
      have hp₁ := trA₁₃.unmap_hom hp₃
      exact (ctB_unmap y₃ hp₃.2.1).comp_mor (semPi_obj_mor_vertical trB₁ hf hp₁)
  comp_mor {f g η} hη := by
    have hh := (semPi_hom_iff hiA₁ trA₁ hiB₁ trB₁ hη.1).mp hη.2.2
    dsimp only [semPi]
    refine mkPiMor_ext (fun _ _ _ => Iff.rfl) ?_
    intro x₃ y₃ p₃ hp₃
    have hp₂ := trA₂₃.unmap_hom hp₃
    have hx_eq := ctA.uncomp_obj trA₁₂ trA₂₃ trA₁₃ hp₃.1
    have hy_eq := ctA.uncomp_obj trA₁₂ trA₂₃ trA₁₃ hp₃.2.1
    have hp_eq := ctA.uncomp_mor trA₁₂ trA₂₃ trA₁₃ hp₃
    rw [piMorAt_mkPiMor_of_rk rkA₂ hp₂, hx_eq, hy_eq, hp_eq]
    have hp₁ := trA₁₃.unmap_hom hp₃
    exact (ctB_unmap y₃ hp₃.2.1).comp_mor (semPi_hom_mor_vertical trB₁ hη.1 hη.2.1 hh hp₁)

end HofmannStreicher1994.Repaired

/-! ## SemContexts.lean -/

namespace HofmannStreicher1994.Repaired

@[simp] theorem consEnv_head_tail (γ : Env) :
    consEnv (γ 0) (renEnv Nat.succ γ) = γ := by
  funext n; cases n <;> rfl

/-- Context arrows have typed components. The unused environment tail is discrete. -/
noncomputable def CtxHom : Context → Env → Env → Env → Prop
  | [], γ₁, γ₂, δ => γ₁ = γ₂ ∧ δ = idEnv γ₁
  | A :: Γ, γ₁, γ₂, δ =>
      CtxHom Γ (renEnv Nat.succ γ₁) (renEnv Nat.succ γ₂) (renEnv Nat.succ δ) ∧
      piHetMor (evalTy A) (renEnv Nat.succ γ₁) (renEnv Nat.succ γ₂)
        (renEnv Nat.succ δ) (γ₁ 0) (γ₂ 0) (δ 0)

noncomputable def compCtx : Context → Env → Env → Env → Env → Env → Env
  | [], _, _, _, _, δ₂₃ => δ₂₃
  | A :: Γ, γ₁, γ₂, γ₃, δ₁₂, δ₂₃ =>
    consEnv
      ((evalTy A).comp (renEnv Nat.succ γ₃)
        ((evalTy A).reindexMor (renEnv Nat.succ γ₂) (renEnv Nat.succ γ₃)
          (renEnv Nat.succ δ₂₃) (δ₁₂ 0))
        (δ₂₃ 0))
      (compCtx Γ (renEnv Nat.succ γ₁) (renEnv Nat.succ γ₂) (renEnv Nat.succ γ₃)
        (renEnv Nat.succ δ₁₂) (renEnv Nat.succ δ₂₃))

@[simp] theorem compCtx_nil (γ₁ γ₂ γ₃ δ₁₂ δ₂₃ : Env) :
    compCtx [] γ₁ γ₂ γ₃ δ₁₂ δ₂₃ = δ₂₃ := rfl

@[simp] theorem compCtx_consEnv (A : Expr) (Γ : Context)
    (x₁ x₂ x₃ p₁₂ p₂₃ : Val) (γ₁ γ₂ γ₃ δ₁₂ δ₂₃ : Env) :
    compCtx (A :: Γ) (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv x₃ γ₃)
      (consEnv p₁₂ δ₁₂) (consEnv p₂₃ δ₂₃) =
    consEnv
      ((evalTy A).comp γ₃ ((evalTy A).reindexMor γ₂ γ₃ δ₂₃ p₁₂) p₂₃)
      (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃) := rfl

theorem CtxObj.cons {Γ : Context} {A : Expr} {γ : Env} {x : Val}
    (hγ : CtxObj Γ γ) (hx : (evalTy A).Obj γ x) :
    CtxObj (A :: Γ) (consEnv x γ) := ⟨hγ, hx⟩

theorem CtxHom.source : ∀ {Γ : Context} {γ₁ γ₂ δ : Env},
    CtxHom Γ γ₁ γ₂ δ → CtxObj Γ γ₁
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, _, h => ⟨h.1.source, h.2.1⟩

theorem CtxHom.target : ∀ {Γ : Context} {γ₁ γ₂ δ : Env},
    CtxHom Γ γ₁ γ₂ δ → CtxObj Γ γ₂
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, _, h => ⟨h.1.target, h.2.2.1⟩

theorem CtxHom.cons {Γ : Context} {A : Expr} {γ₁ γ₂ δ : Env} {x y p : Val}
    (hγ : CtxHom Γ γ₁ γ₂ δ) (hp : piHetMor (evalTy A) γ₁ γ₂ δ x y p) :
    CtxHom (A :: Γ) (consEnv x γ₁) (consEnv y γ₂) (consEnv p δ) := ⟨hγ, hp⟩

structure SemTypeWf (Γ : Context) (A : Expr) : Prop where
  good : GoodType Γ.length A
  fiber {γ} : CtxObj Γ γ → FiberLaws (evalTy A) γ
  id_tr {γ} : CtxObj Γ γ → IdentityTransport (evalTy A) γ
  rank {γ} : CtxObj Γ γ → RankLaws (evalTy A) γ
  tr {γ₁ γ₂ δ} : CtxHom Γ γ₁ γ₂ δ → TransportLaws (evalTy A) γ₁ γ₂ δ
  comp_tr {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} : CtxHom Γ γ₁ γ₂ δ₁₂ → CtxHom Γ γ₂ γ₃ δ₂₃ →
    CompTransport (evalTy A) γ₁ γ₂ γ₃ δ₁₂ δ₂₃ (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃)

def SemCtxWf : Context → Prop
  | [] => True
  | A :: Γ => SemCtxWf Γ ∧ SemTypeWf Γ A

theorem SemCtxWf.id_hom : ∀ {Γ : Context}, SemCtxWf Γ →
    ∀ {γ : Env}, CtxObj Γ γ → CtxHom Γ γ γ (idEnv γ)
  | [], _, _, _ => ⟨rfl, rfl⟩
  | _ :: _, ⟨hΓ, hA⟩, _, ⟨hγ, hx⟩ =>
    ⟨hΓ.id_hom hγ, (hA.fiber hγ).id_hom hx⟩

theorem SemCtxWf.comp_hom : ∀ {Γ : Context}, SemCtxWf Γ →
    ∀ {γ₁ γ₂ γ₃ δ₁₂ δ₂₃ : Env}, CtxHom Γ γ₁ γ₂ δ₁₂ → CtxHom Γ γ₂ γ₃ δ₂₃ →
      CtxHom Γ γ₁ γ₃ (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃)
  | [], _, _, _, _, _, _, ⟨hγ₁₂, _⟩, ⟨hγ₂₃, hδ₂₃⟩ => by
    subst hγ₁₂; subst hγ₂₃; exact ⟨rfl, hδ₂₃⟩
  | A :: Γ, ⟨hΓ, hA⟩, γ₁, γ₂, γ₃, δ₁₂, δ₂₃, ⟨h₁₂, hp₁₂⟩, ⟨h₂₃, hp₂₃⟩ => by
    have h₁₃ := hΓ.comp_hom h₁₂ h₂₃
    have hp₁₂v := (hA.tr h₁₂).vertical hp₁₂
    have hp₂₃v := (hA.tr h₂₃).vertical hp₂₃
    have hp₁₂_tr : FiberHom (evalTy A) (renEnv Nat.succ γ₃)
        ((evalTy A).reindexObj (renEnv Nat.succ γ₁) (renEnv Nat.succ γ₃)
          (compCtx Γ (renEnv Nat.succ γ₁) (renEnv Nat.succ γ₂) (renEnv Nat.succ γ₃)
            (renEnv Nat.succ δ₁₂) (renEnv Nat.succ δ₂₃)) (γ₁ 0))
        ((evalTy A).reindexObj (renEnv Nat.succ γ₂) (renEnv Nat.succ γ₃)
          (renEnv Nat.succ δ₂₃) (γ₂ 0))
        ((evalTy A).reindexMor (renEnv Nat.succ γ₂) (renEnv Nat.succ γ₃)
          (renEnv Nat.succ δ₂₃) (δ₁₂ 0)) := by
      simpa only [(hA.comp_tr h₁₂ h₂₃).comp_obj hp₁₂.1] using (hA.tr h₂₃).map_hom hp₁₂v
    have hp₁₃v := (hA.fiber h₂₃.target).comp_hom hp₁₂_tr hp₂₃v
    exact ⟨h₁₃, hp₁₂.1, hp₂₃.2.1, ((hA.tr h₁₃).hom_iff hp₁₂.1 hp₂₃.2.1).mpr hp₁₃v.2.2⟩

theorem SemCtxWf.id_comp : ∀ {Γ : Context}, SemCtxWf Γ →
    ∀ {γ₁ γ₂ δ : Env}, CtxHom Γ γ₁ γ₂ δ → compCtx Γ γ₁ γ₁ γ₂ (idEnv γ₁) δ = δ
  | [], _, _, _, _, _ => rfl
  | A :: Γ, ⟨hΓ, hA⟩, γ₁, γ₂, δ, ⟨hδ, hp⟩ => by
    have h_tail := hΓ.id_comp hδ
    have hpv := (hA.tr hδ).vertical hp
    have h_head : (evalTy A).comp (renEnv Nat.succ γ₂)
        ((evalTy A).reindexMor (renEnv Nat.succ γ₁) (renEnv Nat.succ γ₂)
          (renEnv Nat.succ δ) (idVal (γ₁ 0))) (δ 0) = δ 0 := by
      rw [(hA.tr hδ).map_id hp.1, (hA.fiber hδ.target).id_comp hpv]
    dsimp only [compCtx]
    change consEnv
      ((evalTy A).comp (renEnv Nat.succ γ₂)
        ((evalTy A).reindexMor (renEnv Nat.succ γ₁) (renEnv Nat.succ γ₂)
          (renEnv Nat.succ δ) (idVal (γ₁ 0))) (δ 0))
      (compCtx Γ (renEnv Nat.succ γ₁) (renEnv Nat.succ γ₁) (renEnv Nat.succ γ₂)
        (idEnv (renEnv Nat.succ γ₁)) (renEnv Nat.succ δ)) = δ
    rw [h_head, h_tail, consEnv_head_tail]

theorem SemCtxWf.comp_id : ∀ {Γ : Context}, SemCtxWf Γ →
    ∀ {γ₁ γ₂ δ : Env}, CtxHom Γ γ₁ γ₂ δ → compCtx Γ γ₁ γ₂ γ₂ δ (idEnv γ₂) = δ
  | [], _, _, _, _, ⟨hγ, hδ⟩ => by subst hγ; exact hδ.symm
  | A :: Γ, ⟨hΓ, hA⟩, γ₁, γ₂, δ, ⟨hδ, hp⟩ => by
    have h_tail := hΓ.comp_id hδ
    have hpv := (hA.tr hδ).vertical hp
    have h_head : (evalTy A).comp (renEnv Nat.succ γ₂)
        ((evalTy A).reindexMor (renEnv Nat.succ γ₂) (renEnv Nat.succ γ₂)
          (idEnv (renEnv Nat.succ γ₂)) (δ 0)) (idVal (γ₂ 0)) = δ 0 := by
      rw [(hA.id_tr hδ.target).mor hpv, (hA.fiber hδ.target).comp_id hpv]
    dsimp only [compCtx]
    change consEnv
      ((evalTy A).comp (renEnv Nat.succ γ₂)
        ((evalTy A).reindexMor (renEnv Nat.succ γ₂) (renEnv Nat.succ γ₂)
          (idEnv (renEnv Nat.succ γ₂)) (δ 0)) (idVal (γ₂ 0)))
      (compCtx Γ (renEnv Nat.succ γ₁) (renEnv Nat.succ γ₂) (renEnv Nat.succ γ₂)
        (renEnv Nat.succ δ) (idEnv (renEnv Nat.succ γ₂))) = δ
    rw [h_head, h_tail, consEnv_head_tail]

theorem SemTypeWf.ctB_vert {Γ : Context} {A B : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B)
    {γ : Env} (hγ : CtxObj Γ γ) {x₁ x₂ x₃ p₁ p₂ : Val}
    (hp₁ : FiberHom (evalTy A) γ x₁ x₂ p₁) (hp₂ : FiberHom (evalTy A) γ x₂ x₃ p₂) :
    CompTransport (evalTy B) (consEnv x₁ γ) (consEnv x₂ γ) (consEnv x₃ γ)
      (consEnv p₁ (idEnv γ)) (consEnv p₂ (idEnv γ))
      (consEnv ((evalTy A).comp γ p₁ p₂) (idEnv γ)) := by
  have h₁₂ : CtxHom (A :: Γ) (consEnv x₁ γ) (consEnv x₂ γ) (consEnv p₁ (idEnv γ)) :=
    ⟨hΓ.id_hom hγ, hp₁⟩
  have h₂₃ : CtxHom (A :: Γ) (consEnv x₂ γ) (consEnv x₃ γ) (consEnv p₂ (idEnv γ)) :=
    ⟨hΓ.id_hom hγ, hp₂⟩
  have h := hB.comp_tr h₁₂ h₂₃
  rwa [compCtx_consEnv, (hA.id_tr hγ).mor hp₁, hΓ.id_comp (hΓ.id_hom hγ)] at h

theorem SemTypeWf.ctB_left {Γ : Context} {A B : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B)
    {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ) {x₁ x₂ p : Val}
    (hp : FiberHom (evalTy A) γ₁ x₁ x₂ p) :
    CompTransport (evalTy B) (consEnv x₁ γ₁) (consEnv x₂ γ₁)
      (consEnv ((evalTy A).reindexObj γ₁ γ₂ δ x₂) γ₂)
      (consEnv p (idEnv γ₁)) (consEnv (idVal ((evalTy A).reindexObj γ₁ γ₂ δ x₂)) δ)
      (consEnv ((evalTy A).reindexMor γ₁ γ₂ δ p) δ) := by
  have hx₂' := (hA.tr hδ).map_obj hp.2.1
  have h_id₂ : piHetMor (evalTy A) γ₁ γ₂ δ x₂ ((evalTy A).reindexObj γ₁ γ₂ δ x₂)
      (idVal ((evalTy A).reindexObj γ₁ γ₂ δ x₂)) :=
    ⟨hp.2.1, hx₂', ((hA.tr hδ).hom_iff hp.2.1 hx₂').mpr ((hA.fiber hδ.target).id_hom hx₂').2.2⟩
  have h₁₂ : CtxHom (A :: Γ) (consEnv x₁ γ₁) (consEnv x₂ γ₁) (consEnv p (idEnv γ₁)) :=
    ⟨hΓ.id_hom hδ.source, hp⟩
  have h₂₃ : CtxHom (A :: Γ) (consEnv x₂ γ₁) (consEnv ((evalTy A).reindexObj γ₁ γ₂ δ x₂) γ₂)
      (consEnv (idVal ((evalTy A).reindexObj γ₁ γ₂ δ x₂)) δ) :=
    ⟨hδ, h_id₂⟩
  have h := hB.comp_tr h₁₂ h₂₃
  rwa [compCtx_consEnv, (hA.fiber hδ.target).comp_id ((hA.tr hδ).map_hom hp), hΓ.id_comp hδ] at h

theorem SemTypeWf.ctB_right {Γ : Context} {A B : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B)
    {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ) {x₁ x₂ p : Val}
    (hp : piHetMor (evalTy A) γ₁ γ₂ δ x₁ x₂ p) :
    CompTransport (evalTy B) (consEnv x₁ γ₁)
      (consEnv ((evalTy A).reindexObj γ₁ γ₂ δ x₁) γ₂) (consEnv x₂ γ₂)
      (consEnv (idVal ((evalTy A).reindexObj γ₁ γ₂ δ x₁)) δ) (consEnv p (idEnv γ₂))
      (consEnv p δ) := by
  have hx₁' := (hA.tr hδ).map_obj hp.1
  have h_id₁ : piHetMor (evalTy A) γ₁ γ₂ δ x₁ ((evalTy A).reindexObj γ₁ γ₂ δ x₁)
      (idVal ((evalTy A).reindexObj γ₁ γ₂ δ x₁)) :=
    ⟨hp.1, hx₁', ((hA.tr hδ).hom_iff hp.1 hx₁').mpr ((hA.fiber hδ.target).id_hom hx₁').2.2⟩
  have hpv := (hA.tr hδ).vertical hp
  have h₁₂ : CtxHom (A :: Γ) (consEnv x₁ γ₁) (consEnv ((evalTy A).reindexObj γ₁ γ₂ δ x₁) γ₂)
      (consEnv (idVal ((evalTy A).reindexObj γ₁ γ₂ δ x₁)) δ) :=
    ⟨hδ, h_id₁⟩
  have h₂₃ : CtxHom (A :: Γ) (consEnv ((evalTy A).reindexObj γ₁ γ₂ δ x₁) γ₂) (consEnv x₂ γ₂)
      (consEnv p (idEnv γ₂)) :=
    ⟨hΓ.id_hom hδ.target, hpv⟩
  have h := hB.comp_tr h₁₂ h₂₃
  rwa [compCtx_consEnv, (hA.id_tr hδ.target).mor ((hA.fiber hδ.target).id_hom hx₁'),
    (hA.fiber hδ.target).id_comp hpv, hΓ.comp_id hδ] at h

theorem SemTypeWf.ctB_id {Γ : Context} {A B : Expr}
    (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B)
    {γ₁ γ₂ γ₃ δ₁₂ δ₂₃ : Env} (h₁₂ : CtxHom Γ γ₁ γ₂ δ₁₂) (h₂₃ : CtxHom Γ γ₂ γ₃ δ₂₃)
    {x : Val} (hx : (evalTy A).Obj γ₁ x) :
    let δ₁₃ := compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃
    CompTransport (evalTy B) (consEnv x γ₁)
      (consEnv ((evalTy A).reindexObj γ₁ γ₂ δ₁₂ x) γ₂)
      (consEnv ((evalTy A).reindexObj γ₁ γ₃ δ₁₃ x) γ₃)
      (consEnv (idVal ((evalTy A).reindexObj γ₁ γ₂ δ₁₂ x)) δ₁₂)
      (consEnv (idVal ((evalTy A).reindexObj γ₁ γ₃ δ₁₃ x)) δ₂₃)
      (consEnv (idVal ((evalTy A).reindexObj γ₁ γ₃ δ₁₃ x)) δ₁₃) := by
  intro δ₁₃
  have hx₂ := (hA.tr h₁₂).map_obj hx
  have hx₃ := (hA.tr h₂₃).map_obj hx₂
  have hx_eq : (evalTy A).reindexObj γ₂ γ₃ δ₂₃ ((evalTy A).reindexObj γ₁ γ₂ δ₁₂ x) =
      (evalTy A).reindexObj γ₁ γ₃ δ₁₃ x :=
    (hA.comp_tr h₁₂ h₂₃).comp_obj hx
  have h_id₁₂ : piHetMor (evalTy A) γ₁ γ₂ δ₁₂ x ((evalTy A).reindexObj γ₁ γ₂ δ₁₂ x)
      (idVal ((evalTy A).reindexObj γ₁ γ₂ δ₁₂ x)) :=
    ⟨hx, hx₂, ((hA.tr h₁₂).hom_iff hx hx₂).mpr ((hA.fiber h₁₂.target).id_hom hx₂).2.2⟩
  have h_id₂₃ : piHetMor (evalTy A) γ₂ γ₃ δ₂₃ ((evalTy A).reindexObj γ₁ γ₂ δ₁₂ x)
      ((evalTy A).reindexObj γ₁ γ₃ δ₁₃ x) (idVal ((evalTy A).reindexObj γ₁ γ₃ δ₁₃ x)) := by
    rw [← hx_eq]
    exact ⟨hx₂, hx₃, ((hA.tr h₂₃).hom_iff hx₂ hx₃).mpr ((hA.fiber h₂₃.target).id_hom hx₃).2.2⟩
  have h := hB.comp_tr (CtxHom.cons h₁₂ h_id₁₂) (CtxHom.cons h₂₃ h_id₂₃)
  have h_head : (evalTy A).comp γ₃
      ((evalTy A).reindexMor γ₂ γ₃ δ₂₃ (idVal ((evalTy A).reindexObj γ₁ γ₂ δ₁₂ x)))
      (idVal ((evalTy A).reindexObj γ₁ γ₃ δ₁₃ x)) =
      idVal ((evalTy A).reindexObj γ₁ γ₃ δ₁₃ x) := by
    rw [(hA.tr h₂₃).map_id hx₂, hx_eq,
      (hA.fiber h₂₃.target).id_comp ((hA.fiber h₂₃.target).id_hom (hx_eq ▸ hx₃))]
  simpa only [compCtx_consEnv, h_head] using h

theorem SemTypeWf.ctB_unmap {Γ : Context} {A B : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B)
    {γ₁ γ₂ γ₃ δ₁₂ δ₂₃ : Env} (h₁₂ : CtxHom Γ γ₁ γ₂ δ₁₂) (h₂₃ : CtxHom Γ γ₂ γ₃ δ₂₃)
    {x₃ : Val} (hx₃ : (evalTy A).Obj γ₃ x₃) :
    let δ₁₃ := compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃
    CompTransport (evalTy B)
      (consEnv ((evalTy A).unreindexObj γ₁ γ₃ δ₁₃ x₃) γ₁)
      (consEnv ((evalTy A).unreindexObj γ₂ γ₃ δ₂₃ x₃) γ₂)
      (consEnv x₃ γ₃)
      (consEnv (idVal ((evalTy A).unreindexObj γ₂ γ₃ δ₂₃ x₃)) δ₁₂)
      (consEnv (idVal x₃) δ₂₃)
      (consEnv (idVal x₃) δ₁₃) := by
  intro δ₁₃
  have h₁₃ := hΓ.comp_hom h₁₂ h₂₃
  have hx₁ := (hA.tr h₁₃).unmap_obj hx₃
  have h := hA.ctB_id hB h₁₂ h₂₃ hx₁
  have hx₂_eq : (evalTy A).reindexObj γ₁ γ₂ δ₁₂ ((evalTy A).unreindexObj γ₁ γ₃ δ₁₃ x₃) =
      (evalTy A).unreindexObj γ₂ γ₃ δ₂₃ x₃ := by
    rw [← (hA.comp_tr h₁₂ h₂₃).uncomp_obj (hA.tr h₁₂) (hA.tr h₂₃) (hA.tr h₁₃) hx₃,
      (hA.tr h₁₂).map_unmap_obj ((hA.tr h₂₃).unmap_obj hx₃)]
  have hx₃_eq : (evalTy A).reindexObj γ₁ γ₃ δ₁₃ ((evalTy A).unreindexObj γ₁ γ₃ δ₁₃ x₃) = x₃ :=
    (hA.tr h₁₃).map_unmap_obj hx₃
  dsimp only [δ₁₃] at h hx₂_eq hx₃_eq ⊢
  rw [hx₂_eq, hx₃_eq] at h
  exact h

/-- The context arrow used by J, from the reflexive diagonal to an arbitrary path. -/
theorem j_context_arrow {Γ : Context} {A : Expr} {γ : Env}
    (hγ : CtxHom Γ γ γ (idEnv γ))
    (hA : FiberLaws (evalTy A) γ) (hiA : IdentityTransport (evalTy A) γ)
    {x y p : Val} (hp : FiberHom (evalTy A) γ x y p) :
    CtxHom (identityContext Γ A)
      (consEnv (.idObj (idVal x)) (consEnv x (consEnv x γ)))
      (consEnv (.idObj p) (consEnv y (consEnv x γ)))
      (consEnv (.idObj p) (consEnv p (consEnv (idVal x) (idEnv γ)))) := by
  refine CtxHom.cons (CtxHom.cons (CtxHom.cons hγ (hA.id_hom hp.1)) ?_) ?_
  case refine_2 =>
    simp only [piHetMor, evalTy, eval, semId, weaken, eval_rename, renameFam,
      idEnv_consEnv, renEnv_succ_consEnv, consEnv_zero, consEnv_succ, unId]
    simp [hiA.mor (hA.id_hom hp.1), hA.inv_id hp.1, hA.id_comp hp,
      (hA.id_hom hp.1).2.2, hp.2.2]
  case refine_1 =>
    simpa only [weaken, evalTy_rename, piHetMor, renameFam, renEnv_succ_consEnv] using hp

end HofmannStreicher1994.Repaired

/-! ## SemMotives.lean -/

namespace HofmannStreicher1994.Repaired

/-- A finite list of replacement terms, followed by a renaming of the remaining variables. -/
def prefixSub : List Expr → (Nat → Nat) → Nat → Expr
  | [], ρ, n => .var (ρ n)
  | e :: _, _, 0 => e
  | _ :: es, ρ, n + 1 => prefixSub es ρ n

theorem prefixSub_tmOnly : ∀ (es : List Expr) (ρ : Nat → Nat),
    (∀ e ∈ es, evalTy e = dfltFam) → SubstTmOnly (prefixSub es ρ)
  | [], _, _ => fun _ => rfl
  | e :: es, ρ, h => fun
      | 0 => h e (List.mem_cons_self ..)
      | n + 1 => prefixSub_tmOnly es ρ (fun e he => h e (List.mem_cons_of_mem _ he)) n

theorem prefixSub_envOn : ∀ (es : List Expr) (ρ : Nat → Nat) (γ : Env),
    (∀ e ∈ es, (evalTm e).mor γ γ (idEnv γ) = idVal ((evalTm e).obj γ)) →
    EnvOn (prefixSub es ρ) γ
  | [], _, _, _ => fun _ => rfl
  | e :: es, ρ, γ, h => fun
      | 0 => h e (List.mem_cons_self ..)
      | n + 1 => prefixSub_envOn es ρ γ
          (fun e he => h e (List.mem_cons_of_mem _ he)) n

theorem subObj_prefixSub : ∀ (es : List Expr) (ρ : Nat → Nat) (γ : Env),
    subObj (prefixSub es ρ) γ =
      es.foldr (fun e γ' => consEnv ((evalTm e).obj γ) γ') (renEnv ρ γ)
  | [], _, _ => rfl
  | _ :: es, ρ, γ => funext fun
      | 0 => rfl
      | n + 1 => congrFun (subObj_prefixSub es ρ γ) n

theorem subMor_prefixSub : ∀ (es : List Expr) (ρ : Nat → Nat) (γ₁ γ₂ δ : Env),
    subMor (prefixSub es ρ) γ₁ γ₂ δ =
      es.foldr (fun e δ' => consEnv ((evalTm e).mor γ₁ γ₂ δ) δ') (renEnv ρ δ)
  | [], _, _, _, _ => rfl
  | _ :: es, ρ, γ₁, γ₂, δ => funext fun
      | 0 => rfl
      | n + 1 => congrFun (subMor_prefixSub es ρ γ₁ γ₂ δ) n

theorem evalTy_prefixSub_obj (C : Expr) (es : List Expr) (ρ : Nat → Nat) (γ : Env)
    (ht : ∀ e ∈ es, evalTy e = dfltFam)
    (hi : ∀ e ∈ es, (evalTm e).mor γ γ (idEnv γ) = idVal ((evalTm e).obj γ)) :
    (evalTy (substitute (prefixSub es ρ) C)).Obj γ =
      (evalTy C).Obj
        (es.foldr (fun e γ' => consEnv ((evalTm e).obj γ) γ') (renEnv ρ γ)) := by
  simpa only [subObj_prefixSub] using
    ((eval_substitute C (prefixSub_tmOnly es ρ ht)).1.2.1 γ (prefixSub_envOn es ρ γ hi)).1

theorem evalTm_prefixSub_obj (t : Expr) (es : List Expr) (ρ : Nat → Nat) (γ : Env)
    (ht : ∀ e ∈ es, evalTy e = dfltFam)
    (hi : ∀ e ∈ es, (evalTm e).mor γ γ (idEnv γ) = idVal ((evalTm e).obj γ)) :
    (evalTm (substitute (prefixSub es ρ) t)).obj γ =
      (evalTm t).obj
        (es.foldr (fun e γ' => consEnv ((evalTm e).obj γ) γ') (renEnv ρ γ)) := by
  simpa only [subObj_prefixSub] using
    (eval_substitute t (prefixSub_tmOnly es ρ ht)).2.1 γ (prefixSub_envOn es ρ γ hi)

theorem reflexivityMotive_eq_prefixSub (A C : Expr) :
    reflexivityMotive A C = substitute
      (prefixSub [.refl (weaken A) (.var 0), .var 0, .var 0] Nat.succ) C :=
  congrArg (fun σ => substitute σ C) (funext fun
    | 0 => rfl | 1 => rfl | 2 => rfl | _ + 3 => rfl)

theorem evalTy_reflexivityMotive_obj (A C : Expr) (γ : Env) (x : Val) :
    (evalTy (reflexivityMotive A C)).Obj (consEnv x γ) =
      (evalTy C).Obj (consEnv (.idObj (idVal x)) (consEnv x (consEnv x γ))) := by
  rw [reflexivityMotive_eq_prefixSub]
  refine evalTy_prefixSub_obj C [.refl (weaken A) (.var 0), .var 0, .var 0]
    Nat.succ (consEnv x γ) ?_ ?_
  all_goals simp [evalTy, evalTm, eval, idVal]

theorem instantiate_eq_prefixSub (C a : Expr) :
    instantiate C a = substitute (prefixSub [a] id) C :=
  congrArg (fun σ => substitute σ C) (funext fun | 0 => rfl | _ + 1 => rfl)

theorem instantiate₂_eq_prefixSub (C a b : Expr) :
    instantiate₂ C a b = substitute (prefixSub [b, a] id) C :=
  congrArg (fun σ => substitute σ C) (funext fun | 0 => rfl | 1 => rfl | _ + 2 => rfl)

theorem instantiate₃_eq_prefixSub (C a b p : Expr) :
    instantiate₃ C a b p = substitute (prefixSub [p, b, a] id) C :=
  congrArg (fun σ => substitute σ C) (funext fun
    | 0 => rfl | 1 => rfl | 2 => rfl | _ + 3 => rfl)

theorem evalTy_instantiate_obj (C a : Expr) (γ : Env)
    (ht : evalTy a = dfltFam)
    (hi : (evalTm a).mor γ γ (idEnv γ) = idVal ((evalTm a).obj γ)) :
    (evalTy (instantiate C a)).Obj γ =
      (evalTy C).Obj (consEnv ((evalTm a).obj γ) γ) :=
  (congrArg (fun e => (evalTy e).Obj γ) (instantiate_eq_prefixSub C a)).trans
    (evalTy_prefixSub_obj C [a] id γ
      (List.forall_mem_singleton.mpr ht) (List.forall_mem_singleton.mpr hi))

theorem evalTm_instantiate_obj (t a : Expr) (γ : Env)
    (ht : evalTy a = dfltFam)
    (hi : (evalTm a).mor γ γ (idEnv γ) = idVal ((evalTm a).obj γ)) :
    (evalTm (instantiate t a)).obj γ =
      (evalTm t).obj (consEnv ((evalTm a).obj γ) γ) :=
  (congrArg (fun e => (evalTm e).obj γ) (instantiate_eq_prefixSub t a)).trans
    (evalTm_prefixSub_obj t [a] id γ
      (List.forall_mem_singleton.mpr ht) (List.forall_mem_singleton.mpr hi))

theorem evalTy_instantiate₂_obj (C a b : Expr) (γ : Env)
    (hta : evalTy a = dfltFam) (htb : evalTy b = dfltFam)
    (hia : (evalTm a).mor γ γ (idEnv γ) = idVal ((evalTm a).obj γ))
    (hib : (evalTm b).mor γ γ (idEnv γ) = idVal ((evalTm b).obj γ)) :
    (evalTy (instantiate₂ C a b)).Obj γ =
      (evalTy C).Obj (consEnv ((evalTm b).obj γ) (consEnv ((evalTm a).obj γ) γ)) :=
  (congrArg (fun e => (evalTy e).Obj γ) (instantiate₂_eq_prefixSub C a b)).trans
    (evalTy_prefixSub_obj C [b, a] id γ
      (List.forall_mem_cons.mpr ⟨htb, List.forall_mem_singleton.mpr hta⟩)
      (List.forall_mem_cons.mpr ⟨hib, List.forall_mem_singleton.mpr hia⟩))

theorem evalTm_instantiate₂_obj (t a b : Expr) (γ : Env)
    (hta : evalTy a = dfltFam) (htb : evalTy b = dfltFam)
    (hia : (evalTm a).mor γ γ (idEnv γ) = idVal ((evalTm a).obj γ))
    (hib : (evalTm b).mor γ γ (idEnv γ) = idVal ((evalTm b).obj γ)) :
    (evalTm (instantiate₂ t a b)).obj γ =
      (evalTm t).obj (consEnv ((evalTm b).obj γ) (consEnv ((evalTm a).obj γ) γ)) :=
  (congrArg (fun e => (evalTm e).obj γ) (instantiate₂_eq_prefixSub t a b)).trans
    (evalTm_prefixSub_obj t [b, a] id γ
      (List.forall_mem_cons.mpr ⟨htb, List.forall_mem_singleton.mpr hta⟩)
      (List.forall_mem_cons.mpr ⟨hib, List.forall_mem_singleton.mpr hia⟩))

theorem evalTy_instantiate₃_obj (C a b p : Expr) (γ : Env)
    (hta : evalTy a = dfltFam) (htb : evalTy b = dfltFam) (htp : evalTy p = dfltFam)
    (hia : (evalTm a).mor γ γ (idEnv γ) = idVal ((evalTm a).obj γ))
    (hib : (evalTm b).mor γ γ (idEnv γ) = idVal ((evalTm b).obj γ))
    (hip : (evalTm p).mor γ γ (idEnv γ) = idVal ((evalTm p).obj γ)) :
    (evalTy (instantiate₃ C a b p)).Obj γ = (evalTy C).Obj
      (consEnv ((evalTm p).obj γ) (consEnv ((evalTm b).obj γ) (consEnv ((evalTm a).obj γ) γ))) :=
  (congrArg (fun e => (evalTy e).Obj γ) (instantiate₃_eq_prefixSub C a b p)).trans
    (evalTy_prefixSub_obj C [p, b, a] id γ
      (List.forall_mem_cons.mpr ⟨htp,
        List.forall_mem_cons.mpr ⟨htb, List.forall_mem_singleton.mpr hta⟩⟩)
      (List.forall_mem_cons.mpr ⟨hip,
        List.forall_mem_cons.mpr ⟨hib, List.forall_mem_singleton.mpr hia⟩⟩))

end HofmannStreicher1994.Repaired

/-! ## SemJ.lean -/

namespace HofmannStreicher1994.Repaired

def jDiagonal (γ : Env) (x : Val) : Env :=
  consEnv (.idObj (idVal x)) (consEnv x (consEnv x γ))

def jTarget (γ : Env) (x y p : Val) : Env :=
  consEnv p (consEnv y (consEnv x γ))

def jArrow (γ : Env) (x p : Val) : Env :=
  consEnv p (consEnv (unId p) (consEnv (idVal x) (idEnv γ)))

/-- The object part of J preserves typing whenever its motive and premises do.
This is one constructor of soundness; it does not assume general term soundness. -/
theorem eval_idRec_obj {Γ : Context} {A C d a b p : Expr} {γ : Env}
    (hγ : CtxHom Γ γ γ (idEnv γ))
    (hA : FiberLaws (evalTy A) γ) (hiA : IdentityTransport (evalTy A) γ)
    (hC : ∀ γ₁ γ₂ δ, CtxHom (identityContext Γ A) γ₁ γ₂ δ → ∀ v,
      (evalTy C).Obj γ₁ v → (evalTy C).Obj γ₂ ((evalTy C).reindexObj γ₁ γ₂ δ v))
    (hd : ∀ x, (evalTy A).Obj γ x →
      (evalTy (reflexivityMotive A C)).Obj (consEnv x γ) ((evalTm d).obj (consEnv x γ)))
    (ha : TermAt (evalTy A) (evalTm a) γ) (hb : TermAt (evalTy A) (evalTm b) γ)
    (hp : TermAt (semId (evalTy A) (evalTm a) (evalTm b)) (evalTm p) γ)
    (hta : IsTm a) (htb : IsTm b) (htp : IsTm p) :
    (evalTy (instantiate₃ C a b p)).Obj γ ((evalTm (.idRec A C d a b p)).obj γ) := by
  rw [evalTy_instantiate₃_obj C a b p γ (evalTy_of_isTm hta)
    (evalTy_of_isTm htb) (evalTy_of_isTm htp) ha.id hb.id hp.id]
  rcases hp.obj with ⟨q, hq, hpq⟩
  have hdiag := Eq.mp (congrFun (evalTy_reflexivityMotive_obj A C γ ((evalTm a).obj γ))
    ((evalTm d).obj (consEnv ((evalTm a).obj γ) γ))) (hd _ ha.obj)
  simpa only [evalTm, eval, hq, unId] using
    hC _ _ _ (j_context_arrow hγ hA hiA ⟨ha.obj, hb.obj, hpq⟩) _ hdiag

theorem eval_idRec_identity {A C d a b p : Expr} {γ : Env}
    (hia : (evalTm a).mor γ γ (idEnv γ) = idVal ((evalTm a).obj γ))
    (hid : (evalTm d).mor (consEnv ((evalTm a).obj γ) γ)
        (consEnv ((evalTm a).obj γ) γ) (idEnv (consEnv ((evalTm a).obj γ) γ)) =
      idVal ((evalTm d).obj (consEnv ((evalTm a).obj γ) γ)))
    (hd : (evalTy C).Obj (jDiagonal γ ((evalTm a).obj γ))
      ((evalTm d).obj (consEnv ((evalTm a).obj γ) γ)))
    (hC : TransportLaws (evalTy C) (jDiagonal γ ((evalTm a).obj γ))
      (jTarget γ ((evalTm a).obj γ) ((evalTm b).obj γ) ((evalTm p).obj γ))
      (jArrow γ ((evalTm a).obj γ) ((evalTm p).obj γ))) :
    (evalTm (.idRec A C d a b p)).mor γ γ (idEnv γ) =
      idVal ((evalTm (.idRec A C d a b p)).obj γ) := by
  simpa only [evalTm, eval, hia, ← idEnv_consEnv, hid, jDiagonal, jTarget, jArrow] using
    hC.map_id hd

theorem eval_betaId_obj {A C d a : Expr} {γ : Env}
    (hta : IsTm a)
    (hia : (evalTm a).mor γ γ (idEnv γ) = idVal ((evalTm a).obj γ))
    (hd : (evalTy C).Obj (jDiagonal γ ((evalTm a).obj γ))
      ((evalTm d).obj (consEnv ((evalTm a).obj γ) γ)))
    (hC : IdentityTransport (evalTy C) (jDiagonal γ ((evalTm a).obj γ))) :
    (evalTm (.idRec A C d a a (.refl A a))).obj γ =
      (evalTm (instantiate d a)).obj γ := by
  rw [evalTm_instantiate_obj d a γ (evalTy_of_isTm hta) hia]
  simpa only [evalTm, eval, jDiagonal, unId, idEnv_consEnv, idVal] using hC.obj hd

end HofmannStreicher1994.Repaired

/-! ## SemEquiv.lean -/

namespace HofmannStreicher1994.Repaired

structure FamAtEq (A' A : SemFam) (γ' γ : Env) : Prop where
  lvl : A'.lvl = A.lvl
  obj {x} : A'.Obj γ' x ↔ A.Obj γ x
  hom_id {x y p} : A.Obj γ x → A.Obj γ y →
    (A'.Hom γ' γ' (idEnv γ') x y p ↔ A.Hom γ γ (idEnv γ) x y p)
  comp {x y z p q} : FiberHom A γ x y p → FiberHom A γ y z q →
    A'.comp γ' p q = A.comp γ p q
  inv {x y p} : FiberHom A γ x y p → A'.inv γ' p = A.inv γ p
  ro_id {x} : A.Obj γ x → A'.reindexObj γ' γ' (idEnv γ') x = A.reindexObj γ γ (idEnv γ) x
  rm_id {x y p} : FiberHom A γ x y p →
    A'.reindexMor γ' γ' (idEnv γ') p = A.reindexMor γ γ (idEnv γ) p

structure FamAlongEq (A' A : SemFam) (γ₁' γ₂' δ' γ₁ γ₂ δ : Env) : Prop where
  hom {x y p} : A.Obj γ₁ x → A.Obj γ₂ y →
    (A'.Hom γ₁' γ₂' δ' x y p ↔ A.Hom γ₁ γ₂ δ x y p)
  reindexObj {x} : A.Obj γ₁ x →
    A'.reindexObj γ₁' γ₂' δ' x = A.reindexObj γ₁ γ₂ δ x
  reindexMor {x y p} : FiberHom A γ₁ x y p →
    A'.reindexMor γ₁' γ₂' δ' p = A.reindexMor γ₁ γ₂ δ p
  unreindexObj {x'} : A.Obj γ₂ x' →
    A'.unreindexObj γ₁' γ₂' δ' x' = A.unreindexObj γ₁ γ₂ δ x'
  unreindexMor {x' y' p'} : FiberHom A γ₂ x' y' p' →
    A'.unreindexMor γ₁' γ₂' δ' p' = A.unreindexMor γ₁ γ₂ δ p'

theorem FamAtEq.refl (A : SemFam) (γ : Env) : FamAtEq A A γ γ where
  lvl := rfl
  obj := Iff.rfl
  hom_id _ _ := Iff.rfl
  comp _ _ := rfl
  inv _ := rfl
  ro_id _ := rfl
  rm_id _ := rfl

theorem FamAlongEq.refl (A : SemFam) (γ₁ γ₂ δ : Env) : FamAlongEq A A γ₁ γ₂ δ γ₁ γ₂ δ where
  hom _ _ := Iff.rfl
  reindexObj _ := rfl
  reindexMor _ := rfl
  unreindexObj _ := rfl
  unreindexMor _ := rfl

theorem FamAtEq.fiberHom_iff {A' A : SemFam} {γ' γ : Env}
    (h : FamAtEq A' A γ' γ) {x y p : Val} :
    FiberHom A' γ' x y p ↔ FiberHom A γ x y p := by
  refine ⟨fun ⟨hx, hy, hp⟩ => ⟨h.obj.mp hx, h.obj.mp hy, (h.hom_id (h.obj.mp hx) (h.obj.mp hy)).mp hp⟩,
    fun ⟨hx, hy, hp⟩ => ⟨h.obj.mpr hx, h.obj.mpr hy, (h.hom_id hx hy).mpr hp⟩⟩

theorem FamAlongEq.hetHom_iff {A' A : SemFam} {γ₁' γ₂' δ' γ₁ γ₂ δ : Env}
    (h₁ : FamAtEq A' A γ₁' γ₁) (h₂ : FamAtEq A' A γ₂' γ₂)
    (hδ : FamAlongEq A' A γ₁' γ₂' δ' γ₁ γ₂ δ) {x y p : Val} :
    piHetMor A' γ₁' γ₂' δ' x y p ↔ piHetMor A γ₁ γ₂ δ x y p := by
  refine ⟨fun ⟨hx, hy, hp⟩ => ⟨h₁.obj.mp hx, h₂.obj.mp hy, (hδ.hom (h₁.obj.mp hx) (h₂.obj.mp hy)).mp hp⟩,
    fun ⟨hx, hy, hp⟩ => ⟨h₁.obj.mpr hx, h₂.obj.mpr hy, (hδ.hom hx hy).mpr hp⟩⟩

theorem FamAtEq.symm {A' A : SemFam} {γ' γ : Env} (h : FamAtEq A' A γ' γ) :
    FamAtEq A A' γ γ' where
  lvl := h.lvl.symm
  obj := h.obj.symm
  hom_id hx' hy' := (h.hom_id (h.obj.mp hx') (h.obj.mp hy')).symm
  comp hp' hq' := (h.comp (h.fiberHom_iff.mp hp') (h.fiberHom_iff.mp hq')).symm
  inv hp' := (h.inv (h.fiberHom_iff.mp hp')).symm
  ro_id hx' := (h.ro_id (h.obj.mp hx')).symm
  rm_id hp' := (h.rm_id (h.fiberHom_iff.mp hp')).symm

theorem FamAtEq.trans {A₁ A₂ A₃ : SemFam} {γ₁ γ₂ γ₃ : Env}
    (h₁₂ : FamAtEq A₁ A₂ γ₁ γ₂) (h₂₃ : FamAtEq A₂ A₃ γ₂ γ₃) :
    FamAtEq A₁ A₃ γ₁ γ₃ where
  lvl := h₁₂.lvl.trans h₂₃.lvl
  obj := h₁₂.obj.trans h₂₃.obj
  hom_id hx₃ hy₃ := (h₁₂.hom_id (h₂₃.obj.mpr hx₃) (h₂₃.obj.mpr hy₃)).trans (h₂₃.hom_id hx₃ hy₃)
  comp hp₃ hq₃ := (h₁₂.comp (h₂₃.fiberHom_iff.mpr hp₃) (h₂₃.fiberHom_iff.mpr hq₃)).trans (h₂₃.comp hp₃ hq₃)
  inv hp₃ := (h₁₂.inv (h₂₃.fiberHom_iff.mpr hp₃)).trans (h₂₃.inv hp₃)
  ro_id hx₃ := (h₁₂.ro_id (h₂₃.obj.mpr hx₃)).trans (h₂₃.ro_id hx₃)
  rm_id hp₃ := (h₁₂.rm_id (h₂₃.fiberHom_iff.mpr hp₃)).trans (h₂₃.rm_id hp₃)

theorem FamAlongEq.symm {A' A : SemFam} {γ₁' γ₂' δ' γ₁ γ₂ δ : Env}
    (h₁ : FamAtEq A' A γ₁' γ₁) (h₂ : FamAtEq A' A γ₂' γ₂)
    (hδ : FamAlongEq A' A γ₁' γ₂' δ' γ₁ γ₂ δ) :
    FamAlongEq A A' γ₁ γ₂ δ γ₁' γ₂' δ' where
  hom hx' hy' := (hδ.hom (h₁.obj.mp hx') (h₂.obj.mp hy')).symm
  reindexObj hx' := (hδ.reindexObj (h₁.obj.mp hx')).symm
  reindexMor hp' := (hδ.reindexMor (h₁.fiberHom_iff.mp hp')).symm
  unreindexObj hx' := (hδ.unreindexObj (h₂.obj.mp hx')).symm
  unreindexMor hp' := (hδ.unreindexMor (h₂.fiberHom_iff.mp hp')).symm

theorem FamAlongEq.trans {A₁ A₂ A₃ : SemFam} {γ₁a γ₂a δa γ₁b γ₂b δb γ₁c γ₂c δc : Env}
    (h₁_bc : FamAtEq A₂ A₃ γ₁b γ₁c) (h₂_bc : FamAtEq A₂ A₃ γ₂b γ₂c)
    (hab : FamAlongEq A₁ A₂ γ₁a γ₂a δa γ₁b γ₂b δb)
    (hbc : FamAlongEq A₂ A₃ γ₁b γ₂b δb γ₁c γ₂c δc) :
    FamAlongEq A₁ A₃ γ₁a γ₂a δa γ₁c γ₂c δc where
  hom hx hy := (hab.hom (h₁_bc.obj.mpr hx) (h₂_bc.obj.mpr hy)).trans (hbc.hom hx hy)
  reindexObj hx := (hab.reindexObj (h₁_bc.obj.mpr hx)).trans (hbc.reindexObj hx)
  reindexMor hp := (hab.reindexMor (h₁_bc.fiberHom_iff.mpr hp)).trans (hbc.reindexMor hp)
  unreindexObj hx := (hab.unreindexObj (h₂_bc.obj.mpr hx)).trans (hbc.unreindexObj hx)
  unreindexMor hp := (hab.unreindexMor (h₂_bc.fiberHom_iff.mpr hp)).trans (hbc.unreindexMor hp)

theorem FiberLaws.of_famAtEq {A' A : SemFam} {γ' γ : Env}
    (h : FamAtEq A' A γ' γ) (fl : FiberLaws A γ) : FiberLaws A' γ' where
  id_hom hx' := h.fiberHom_iff.mpr (fl.id_hom (h.obj.mp hx'))
  comp_hom hp' hq' := by
    have hp := h.fiberHom_iff.mp hp'
    have hq := h.fiberHom_iff.mp hq'
    rw [h.comp hp hq]
    exact h.fiberHom_iff.mpr (fl.comp_hom hp hq)
  inv_hom hp' := by
    have hp := h.fiberHom_iff.mp hp'
    rw [h.inv hp]
    exact h.fiberHom_iff.mpr (fl.inv_hom hp)
  id_comp hp' := by
    have hp := h.fiberHom_iff.mp hp'
    rw [h.comp (fl.id_hom hp.1) hp]
    exact fl.id_comp hp
  comp_id hp' := by
    have hp := h.fiberHom_iff.mp hp'
    rw [h.comp hp (fl.id_hom hp.2.1)]
    exact fl.comp_id hp
  assoc hp' hq' hr' := by
    have hp := h.fiberHom_iff.mp hp'
    have hq := h.fiberHom_iff.mp hq'
    have hr := h.fiberHom_iff.mp hr'
    rw [h.comp hp hq, h.comp (fl.comp_hom hp hq) hr, h.comp hq hr, h.comp hp (fl.comp_hom hq hr)]
    exact fl.assoc hp hq hr
  inv_comp hp' := by
    have hp := h.fiberHom_iff.mp hp'
    rw [h.inv hp, h.comp (fl.inv_hom hp) hp]
    exact fl.inv_comp hp
  comp_inv hp' := by
    have hp := h.fiberHom_iff.mp hp'
    rw [h.inv hp, h.comp hp (fl.inv_hom hp)]
    exact fl.comp_inv hp

theorem IdentityTransport.of_famAtEq {A' A : SemFam} {γ' γ : Env}
    (h : FamAtEq A' A γ' γ) (it : IdentityTransport A γ) : IdentityTransport A' γ' where
  obj hx' := (h.ro_id (h.obj.mp hx')).trans (it.obj (h.obj.mp hx'))
  mor hp' := (h.rm_id (h.fiberHom_iff.mp hp')).trans (it.mor (h.fiberHom_iff.mp hp'))

theorem RankLaws.of_famAtEq {A' A : SemFam} {γ' γ : Env}
    (h : FamAtEq A' A γ' γ) (rk : RankLaws A γ) : RankLaws A' γ' where
  obj_rank hx' := h.lvl ▸ rk.obj_rank (h.obj.mp hx')
  hom_rank hp' := h.lvl ▸ rk.hom_rank (h.fiberHom_iff.mp hp')

theorem TransportLaws.of_famAlongEq {A' A : SemFam} {γ₁' γ₂' δ' γ₁ γ₂ δ : Env}
    (h₁ : FamAtEq A' A γ₁' γ₁) (h₂ : FamAtEq A' A γ₂' γ₂)
    (hδ : FamAlongEq A' A γ₁' γ₂' δ' γ₁ γ₂ δ)
    (fl₁ : FiberLaws A γ₁) (tr : TransportLaws A γ₁ γ₂ δ) :
    TransportLaws A' γ₁' γ₂' δ' where
  map_obj hx' := by
    have hx := h₁.obj.mp hx'
    rw [hδ.reindexObj hx]
    exact h₂.obj.mpr (tr.map_obj hx)
  unmap_obj hx' := by
    have hx := h₂.obj.mp hx'
    rw [hδ.unreindexObj hx]
    exact h₁.obj.mpr (tr.unmap_obj hx)
  map_hom hp' := by
    have hp := h₁.fiberHom_iff.mp hp'
    rw [hδ.reindexObj hp.1, hδ.reindexObj hp.2.1, hδ.reindexMor hp]
    exact h₂.fiberHom_iff.mpr (tr.map_hom hp)
  unmap_hom hp' := by
    have hp := h₂.fiberHom_iff.mp hp'
    rw [hδ.unreindexObj hp.1, hδ.unreindexObj hp.2.1, hδ.unreindexMor hp]
    exact h₁.fiberHom_iff.mpr (tr.unmap_hom hp)
  unmap_map_obj hx' := by
    have hx := h₁.obj.mp hx'
    rw [hδ.reindexObj hx, hδ.unreindexObj (tr.map_obj hx)]
    exact tr.unmap_map_obj hx
  map_unmap_obj hx' := by
    have hx := h₂.obj.mp hx'
    rw [hδ.unreindexObj hx, hδ.reindexObj (tr.unmap_obj hx)]
    exact tr.map_unmap_obj hx
  unmap_map_mor hp' := by
    have hp := h₁.fiberHom_iff.mp hp'
    rw [hδ.reindexMor hp, hδ.unreindexMor (tr.map_hom hp)]
    exact tr.unmap_map_mor hp
  map_unmap_mor hp' := by
    have hp := h₂.fiberHom_iff.mp hp'
    rw [hδ.unreindexMor hp, hδ.reindexMor (tr.unmap_hom hp)]
    exact tr.map_unmap_mor hp
  map_id hx' := by
    have hx := h₁.obj.mp hx'
    rw [hδ.reindexMor (fl₁.id_hom hx), hδ.reindexObj hx]
    exact tr.map_id hx
  map_comp hp' hq' := by
    have hp := h₁.fiberHom_iff.mp hp'
    have hq := h₁.fiberHom_iff.mp hq'
    rw [h₁.comp hp hq, hδ.reindexMor (fl₁.comp_hom hp hq), hδ.reindexMor hp, hδ.reindexMor hq,
      h₂.comp (tr.map_hom hp) (tr.map_hom hq)]
    exact tr.map_comp hp hq
  hom_iff hx' hy' := by
    have hx := h₁.obj.mp hx'
    have hy := h₂.obj.mp hy'
    rw [hδ.reindexObj hx]
    exact (hδ.hom hx hy).trans ((tr.hom_iff hx hy).trans (h₂.hom_id (tr.map_obj hx) hy).symm)

theorem CompTransport.of_famAlongEq {A' A : SemFam}
    {γ₁' γ₂' γ₃' δ₁₂' δ₂₃' δ₁₃' γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃ : Env}
    (h₁ : FamAtEq A' A γ₁' γ₁)
    (h₁₂ : FamAlongEq A' A γ₁' γ₂' δ₁₂' γ₁ γ₂ δ₁₂)
    (h₂₃ : FamAlongEq A' A γ₂' γ₃' δ₂₃' γ₂ γ₃ δ₂₃)
    (h₁₃ : FamAlongEq A' A γ₁' γ₃' δ₁₃' γ₁ γ₃ δ₁₃)
    (tr₁₂ : TransportLaws A γ₁ γ₂ δ₁₂)
    (ct : CompTransport A γ₁ γ₂ γ₃ δ₁₂ δ₂₃ δ₁₃) :
    CompTransport A' γ₁' γ₂' γ₃' δ₁₂' δ₂₃' δ₁₃' where
  comp_obj hx' := by
    have hx := h₁.obj.mp hx'
    rw [h₁₂.reindexObj hx, h₂₃.reindexObj (tr₁₂.map_obj hx), h₁₃.reindexObj hx]
    exact ct.comp_obj hx
  comp_mor hp' := by
    have hp := h₁.fiberHom_iff.mp hp'
    rw [h₁₂.reindexMor hp, h₂₃.reindexMor (tr₁₂.map_hom hp), h₁₃.reindexMor hp]
    exact ct.comp_mor hp

theorem FamSubstAt.atEq {A' A : SemFam} {σ : Nat → Expr}
    (h : FamSubstAt A' A σ) {γ : Env} (hγ : EnvOn σ γ) :
    FamAtEq A' A γ (subObj σ γ) where
  lvl := h.1
  obj := by rw [(h.2.1 γ hγ).1]
  hom_id _ _ := by rw [(h.2.2 γ γ (idEnv γ) hγ hγ).1, subMor_idEnv hγ]
  comp _ _ := by rw [(h.2.1 γ hγ).2.1]
  inv _ := by rw [(h.2.1 γ hγ).2.2]
  ro_id _ := by rw [(h.2.2 γ γ (idEnv γ) hγ hγ).2.1, subMor_idEnv hγ]
  rm_id _ := by rw [(h.2.2 γ γ (idEnv γ) hγ hγ).2.2.1, subMor_idEnv hγ]

theorem FamSubstAt.alongEq {A' A : SemFam} {σ : Nat → Expr}
    (h : FamSubstAt A' A σ) {γ₁ γ₂ : Env} (δ : Env)
    (hγ₁ : EnvOn σ γ₁) (hγ₂ : EnvOn σ γ₂) :
    FamAlongEq A' A γ₁ γ₂ δ (subObj σ γ₁) (subObj σ γ₂) (subMor σ γ₁ γ₂ δ) where
  hom _ _ := by rw [(h.2.2 γ₁ γ₂ δ hγ₁ hγ₂).1]
  reindexObj _ := by rw [(h.2.2 γ₁ γ₂ δ hγ₁ hγ₂).2.1]
  reindexMor _ := by rw [(h.2.2 γ₁ γ₂ δ hγ₁ hγ₂).2.2.1]
  unreindexObj _ := by rw [(h.2.2 γ₁ γ₂ δ hγ₁ hγ₂).2.2.2.1]
  unreindexMor _ := by rw [(h.2.2 γ₁ γ₂ δ hγ₁ hγ₂).2.2.2.2]

theorem evalTy_rename_atEq (ρ : Nat → Nat) (A : Expr) (γ : Env) :
    FamAtEq (evalTy (rename ρ A)) (evalTy A) γ (renEnv ρ γ) := by
  rw [evalTy_rename]
  exact ⟨rfl, Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem evalTy_rename_alongEq (ρ : Nat → Nat) (A : Expr) (γ₁ γ₂ δ : Env) :
    FamAlongEq (evalTy (rename ρ A)) (evalTy A) γ₁ γ₂ δ
      (renEnv ρ γ₁) (renEnv ρ γ₂) (renEnv ρ δ) := by
  rw [evalTy_rename]
  exact ⟨fun _ _ => Iff.rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem SemTypeWf.pullback {Γ Δ : Context} {A' A : Expr}
    (hΔ : SemCtxWf Δ) (hgood : GoodType Δ.length A') (hA : SemTypeWf Γ A)
    (f_obj : Env → Env) (f_mor : Env → Env → Env → Env)
    (h_obj : ∀ {γ}, CtxObj Δ γ → CtxObj Γ (f_obj γ))
    (h_mor : ∀ {γ₁ γ₂ δ}, CtxHom Δ γ₁ γ₂ δ → CtxHom Γ (f_obj γ₁) (f_obj γ₂) (f_mor γ₁ γ₂ δ))
    (h_comp : ∀ {γ₁ γ₂ γ₃ δ₁₂ δ₂₃}, CtxHom Δ γ₁ γ₂ δ₁₂ → CtxHom Δ γ₂ γ₃ δ₂₃ →
      f_mor γ₁ γ₃ (compCtx Δ γ₁ γ₂ γ₃ δ₁₂ δ₂₃) =
        compCtx Γ (f_obj γ₁) (f_obj γ₂) (f_obj γ₃) (f_mor γ₁ γ₂ δ₁₂) (f_mor γ₂ γ₃ δ₂₃))
    (hat : ∀ {γ}, CtxObj Δ γ → FamAtEq (evalTy A') (evalTy A) γ (f_obj γ))
    (halong : ∀ {γ₁ γ₂ δ}, CtxHom Δ γ₁ γ₂ δ →
      FamAlongEq (evalTy A') (evalTy A) γ₁ γ₂ δ (f_obj γ₁) (f_obj γ₂) (f_mor γ₁ γ₂ δ)) :
    SemTypeWf Δ A' where
  good := hgood
  fiber hγ := FiberLaws.of_famAtEq (hat hγ) (hA.fiber (h_obj hγ))
  id_tr hγ := IdentityTransport.of_famAtEq (hat hγ) (hA.id_tr (h_obj hγ))
  rank hγ := RankLaws.of_famAtEq (hat hγ) (hA.rank (h_obj hγ))
  tr hδ := TransportLaws.of_famAlongEq (hat hδ.source) (hat hδ.target) (halong hδ)
    (hA.fiber (h_obj hδ.source)) (hA.tr (h_mor hδ))
  comp_tr h₁₂ h₂₃ := by
    have h₁₃ := hΔ.comp_hom h₁₂ h₂₃
    have hal₁₃ := halong h₁₃
    rw [h_comp h₁₂ h₂₃] at hal₁₃
    exact CompTransport.of_famAlongEq (hat h₁₂.source) (halong h₁₂) (halong h₂₃) hal₁₃
      (hA.tr (h_mor h₁₂)) (hA.comp_tr (h_mor h₁₂) (h_mor h₂₃))

theorem SemTypeWf.of_eq {Γ : Context} {A' A : Expr}
    (hΓ : SemCtxWf Γ) (hgood : GoodType Γ.length A') (hA : SemTypeWf Γ A)
    (hat : ∀ {γ}, CtxObj Γ γ → FamAtEq (evalTy A') (evalTy A) γ γ)
    (halong : ∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ →
      FamAlongEq (evalTy A') (evalTy A) γ₁ γ₂ δ γ₁ γ₂ δ) :
    SemTypeWf Γ A' :=
  SemTypeWf.pullback hΓ hgood hA id (fun _ _ δ => δ)
    id id (fun _ _ => rfl) hat halong

theorem SemTypeWf.weaken {Γ : Context} {A B : Expr}
    (hΓ : SemCtxWf Γ) (hB : SemTypeWf Γ B) (hA : SemTypeWf Γ A) :
    SemTypeWf (B :: Γ) (HofmannStreicher1994.weaken A) :=
  SemTypeWf.pullback ⟨hΓ, hB⟩ ⟨hA.good.1.weaken, hA.good.2.rename⟩ hA
    (renEnv Nat.succ) (fun _ _ δ => renEnv Nat.succ δ)
    (fun h => h.1) (fun h => h.1) (fun _ _ => rfl)
    (fun _ => evalTy_rename_atEq Nat.succ A _)
    (fun _ => evalTy_rename_alongEq Nat.succ A _ _ _)

structure SemTermWf (Γ : Context) (t A : Expr) : Prop where
  good : GoodTerm Γ.length t
  at_obj {γ} : CtxObj Γ γ → TermAt (evalTy A) (evalTm t) γ
  along {γ₁ γ₂ δ} : CtxHom Γ γ₁ γ₂ δ → TermAlong (evalTy A) (evalTm t) γ₁ γ₂ δ
  comp_mor {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} : CtxHom Γ γ₁ γ₂ δ₁₂ → CtxHom Γ γ₂ γ₃ δ₂₃ →
    (evalTm t).mor γ₁ γ₃ (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃) =
      (evalTy A).comp γ₃
        ((evalTy A).reindexMor γ₂ γ₃ δ₂₃ ((evalTm t).mor γ₁ γ₂ δ₁₂))
        ((evalTm t).mor γ₂ γ₃ δ₂₃)

theorem SemTermWf.pullback {Γ Δ : Context} {t' t A' A : Expr}
    (hΔ : SemCtxWf Δ) (hgood : GoodTerm Δ.length t') (hA : SemTypeWf Γ A) (ht : SemTermWf Γ t A)
    (f_obj : Env → Env) (f_mor : Env → Env → Env → Env)
    (h_obj : ∀ {γ}, CtxObj Δ γ → CtxObj Γ (f_obj γ))
    (h_mor : ∀ {γ₁ γ₂ δ}, CtxHom Δ γ₁ γ₂ δ → CtxHom Γ (f_obj γ₁) (f_obj γ₂) (f_mor γ₁ γ₂ δ))
    (h_id : ∀ {γ}, CtxObj Δ γ → f_mor γ γ (idEnv γ) = idEnv (f_obj γ))
    (h_comp : ∀ {γ₁ γ₂ γ₃ δ₁₂ δ₂₃}, CtxHom Δ γ₁ γ₂ δ₁₂ → CtxHom Δ γ₂ γ₃ δ₂₃ →
      f_mor γ₁ γ₃ (compCtx Δ γ₁ γ₂ γ₃ δ₁₂ δ₂₃) =
        compCtx Γ (f_obj γ₁) (f_obj γ₂) (f_obj γ₃) (f_mor γ₁ γ₂ δ₁₂) (f_mor γ₂ γ₃ δ₂₃))
    (hat : ∀ {γ}, CtxObj Δ γ → FamAtEq (evalTy A') (evalTy A) γ (f_obj γ))
    (halong : ∀ {γ₁ γ₂ δ}, CtxHom Δ γ₁ γ₂ δ →
      FamAlongEq (evalTy A') (evalTy A) γ₁ γ₂ δ (f_obj γ₁) (f_obj γ₂) (f_mor γ₁ γ₂ δ))
    (ht_obj : ∀ {γ}, CtxObj Δ γ → (evalTm t').obj γ = (evalTm t).obj (f_obj γ))
    (ht_mor : ∀ {γ₁ γ₂ δ}, CtxHom Δ γ₁ γ₂ δ →
      (evalTm t').mor γ₁ γ₂ δ = (evalTm t).mor (f_obj γ₁) (f_obj γ₂) (f_mor γ₁ γ₂ δ)) :
    SemTermWf Δ t' A' where
  good := hgood
  at_obj hγ := by
    have hto := ht.at_obj (h_obj hγ)
    refine ⟨?_, ?_⟩
    · rw [ht_obj hγ]
      exact (hat hγ).obj.mpr hto.obj
    · rw [ht_mor (hΔ.id_hom hγ), h_id hγ, ht_obj hγ]
      exact hto.id
  along hδ := by
    unfold TermAlong
    rw [ht_obj hδ.source, ht_obj hδ.target, ht_mor hδ]
    exact (halong hδ).hetHom_iff (hat hδ.source) (hat hδ.target) |>.mpr (ht.along (h_mor hδ))
  comp_mor h₁₂ h₂₃ := by
    have h₁₃ := hΔ.comp_hom h₁₂ h₂₃
    have hm₁₂ := (hA.tr (h_mor h₁₂)).vertical (ht.along (h_mor h₁₂))
    have hm₂₃ := (hA.tr (h_mor h₂₃)).vertical (ht.along (h_mor h₂₃))
    have hm₁₂_tr := (hA.tr (h_mor h₂₃)).map_hom hm₁₂
    rw [ht_mor h₁₃, h_comp h₁₂ h₂₃, ht_mor h₁₂, ht_mor h₂₃,
      (halong h₂₃).reindexMor hm₁₂, (hat h₂₃.target).comp hm₁₂_tr hm₂₃]
    exact ht.comp_mor (h_mor h₁₂) (h_mor h₂₃)

theorem SemTermWf.conv_eq {Γ : Context} {t A A' : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (ht : SemTermWf Γ t A)
    (hat : ∀ {γ}, CtxObj Γ γ → FamAtEq (evalTy A') (evalTy A) γ γ)
    (halong : ∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ →
      FamAlongEq (evalTy A') (evalTy A) γ₁ γ₂ δ γ₁ γ₂ δ) :
    SemTermWf Γ t A' :=
  SemTermWf.pullback hΓ ht.good hA ht id (fun _ _ δ => δ)
    id id (fun _ => rfl) (fun _ _ => rfl) hat halong (fun _ => rfl) (fun _ => rfl)

theorem SemTermWf.of_eq {Γ : Context} {t t' A : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (ht : SemTermWf Γ t A) (hgood : GoodTerm Γ.length t')
    (hobj : ∀ {γ}, CtxObj Γ γ → (evalTm t').obj γ = (evalTm t).obj γ)
    (hmor : ∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ → (evalTm t').mor γ₁ γ₂ δ = (evalTm t).mor γ₁ γ₂ δ) :
    SemTermWf Γ t' A :=
  SemTermWf.pullback hΓ hgood hA ht id (fun _ _ δ => δ)
    id id (fun _ => rfl) (fun _ _ => rfl)
    (fun _ => FamAtEq.refl _ _) (fun _ => FamAlongEq.refl _ _ _ _) hobj hmor

structure SemTypeEq (Γ : Context) (A' A : Expr) : Prop where
  ctx : SemCtxWf Γ
  wf_left : SemTypeWf Γ A'
  wf_right : SemTypeWf Γ A
  lvl_eq : (evalTy A').lvl = (evalTy A).lvl
  at_eq {γ} : CtxObj Γ γ → FamAtEq (evalTy A') (evalTy A) γ γ
  along_eq {γ₁ γ₂ δ} : CtxHom Γ γ₁ γ₂ δ → FamAlongEq (evalTy A') (evalTy A) γ₁ γ₂ δ γ₁ γ₂ δ

theorem SemTypeEq.of_left {Γ : Context} {A' A : Expr}
    (hΓ : SemCtxWf Γ) (wf_left : SemTypeWf Γ A') (hgood_right : GoodType Γ.length A)
    (lvl_eq : (evalTy A').lvl = (evalTy A).lvl)
    (at_eq : ∀ {γ}, CtxObj Γ γ → FamAtEq (evalTy A') (evalTy A) γ γ)
    (along_eq : ∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ →
      FamAlongEq (evalTy A') (evalTy A) γ₁ γ₂ δ γ₁ γ₂ δ) :
    SemTypeEq Γ A' A where
  ctx := hΓ
  wf_left := wf_left
  wf_right := SemTypeWf.of_eq hΓ hgood_right wf_left
    (fun hγ => (at_eq hγ).symm)
    (fun hδ => (along_eq hδ).symm (at_eq hδ.source) (at_eq hδ.target))
  lvl_eq := lvl_eq
  at_eq := at_eq
  along_eq := along_eq

theorem SemTypeEq.symm {Γ : Context} {A' A : Expr} (h : SemTypeEq Γ A' A) :
    SemTypeEq Γ A A' where
  ctx := h.ctx
  wf_left := h.wf_right
  wf_right := h.wf_left
  lvl_eq := h.lvl_eq.symm
  at_eq hγ := (h.at_eq hγ).symm
  along_eq hδ := (h.along_eq hδ).symm (h.at_eq hδ.source) (h.at_eq hδ.target)

theorem SemTypeEq.trans {Γ : Context} {A₁ A₂ A₃ : Expr}
    (h₁₂ : SemTypeEq Γ A₁ A₂) (h₂₃ : SemTypeEq Γ A₂ A₃) :
    SemTypeEq Γ A₁ A₃ where
  ctx := h₁₂.ctx
  wf_left := h₁₂.wf_left
  wf_right := h₂₃.wf_right
  lvl_eq := h₁₂.lvl_eq.trans h₂₃.lvl_eq
  at_eq hγ := (h₁₂.at_eq hγ).trans (h₂₃.at_eq hγ)
  along_eq hδ := (h₁₂.along_eq hδ).trans (h₂₃.at_eq hδ.source) (h₂₃.at_eq hδ.target) (h₂₃.along_eq hδ)

structure SemTermEq (Γ : Context) (t' t A : Expr) : Prop where
  ctx : SemCtxWf Γ
  wf_A : SemTypeWf Γ A
  wf_left : SemTermWf Γ t' A
  wf_right : SemTermWf Γ t A
  obj_eq {γ} : CtxObj Γ γ → (evalTm t').obj γ = (evalTm t).obj γ
  mor_eq {γ₁ γ₂ δ} : CtxHom Γ γ₁ γ₂ δ → (evalTm t').mor γ₁ γ₂ δ = (evalTm t).mor γ₁ γ₂ δ

theorem SemTermEq.of_left {Γ : Context} {t' t A : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (wf_left : SemTermWf Γ t' A)
    (hgood_right : GoodTerm Γ.length t)
    (obj_eq : ∀ {γ}, CtxObj Γ γ → (evalTm t').obj γ = (evalTm t).obj γ)
    (mor_eq : ∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ → (evalTm t').mor γ₁ γ₂ δ = (evalTm t).mor γ₁ γ₂ δ) :
    SemTermEq Γ t' t A where
  ctx := hΓ
  wf_A := hA
  wf_left := wf_left
  wf_right := SemTermWf.of_eq hΓ hA wf_left hgood_right
    (fun hγ => (obj_eq hγ).symm) (fun hδ => (mor_eq hδ).symm)
  obj_eq := obj_eq
  mor_eq := mor_eq

theorem SemTermEq.symm {Γ : Context} {t' t A : Expr} (h : SemTermEq Γ t' t A) :
    SemTermEq Γ t t' A where
  ctx := h.ctx
  wf_A := h.wf_A
  wf_left := h.wf_right
  wf_right := h.wf_left
  obj_eq hγ := (h.obj_eq hγ).symm
  mor_eq hδ := (h.mor_eq hδ).symm

theorem SemTermEq.trans {Γ : Context} {t₁ t₂ t₃ A : Expr}
    (h₁₂ : SemTermEq Γ t₁ t₂ A) (h₂₃ : SemTermEq Γ t₂ t₃ A) :
    SemTermEq Γ t₁ t₃ A where
  ctx := h₁₂.ctx
  wf_A := h₁₂.wf_A
  wf_left := h₁₂.wf_left
  wf_right := h₂₃.wf_right
  obj_eq hγ := (h₁₂.obj_eq hγ).trans (h₂₃.obj_eq hγ)
  mor_eq hδ := (h₁₂.mor_eq hδ).trans (h₂₃.mor_eq hδ)

end HofmannStreicher1994.Repaired

/-! ## SemSubst.lean -/

namespace HofmannStreicher1994.Repaired

theorem CtxObj_iff_getElem? : ∀ {Γ : Context} {γ : Env},
    CtxObj Γ γ ↔ ∀ n A, Γ[n]? = some A → (evalTy A).Obj (renEnv (fun k => k + n + 1) γ) (γ n)
  | [], _ => ⟨fun _ _ _ h => by simp at h, fun _ => trivial⟩
  | B :: Γ, γ => by
    refine ⟨fun ⟨hΓ, hB⟩ n A hn => ?_, fun h => ⟨?_, ?_⟩⟩
    · cases n with
      | zero =>
        cases hn
        exact hB
      | succ n =>
        exact CtxObj_iff_getElem?.mp hΓ n A hn
    · exact CtxObj_iff_getElem?.mpr (fun n A hn => h (n + 1) A hn)
    · exact h 0 B rfl

theorem CtxHom_iff_getElem? : ∀ {Γ : Context} {γ₁ γ₂ δ : Env},
    CtxHom Γ γ₁ γ₂ δ ↔
      (∀ n, Γ.length ≤ n → γ₁ n = γ₂ n ∧ δ n = idVal (γ₁ n)) ∧
      (∀ n A, Γ[n]? = some A →
        piHetMor (evalTy A) (renEnv (fun k => k + n + 1) γ₁)
          (renEnv (fun k => k + n + 1) γ₂) (renEnv (fun k => k + n + 1) δ)
          (γ₁ n) (γ₂ n) (δ n))
  | [], γ₁, γ₂, δ => by
    refine ⟨fun ⟨hγ, hδ⟩ => ⟨fun n _ => ⟨congrFun hγ n, congrFun hδ n⟩, fun _ _ h => by simp at h⟩,
      fun ⟨h, _⟩ => ⟨funext fun n => (h n (Nat.zero_le n)).1, funext fun n => (h n (Nat.zero_le n)).2⟩⟩
  | B :: Γ, γ₁, γ₂, δ => by
    refine ⟨fun ⟨hΓ, hB⟩ => ⟨fun n hn => ?_, fun n A hn => ?_⟩, fun ⟨htail, h⟩ => ⟨?_, ?_⟩⟩
    · cases n with
      | zero => cases hn
      | succ n =>
        exact (CtxHom_iff_getElem?.mp hΓ).1 n (Nat.le_of_succ_le_succ hn)
    · cases n with
      | zero =>
        cases hn
        exact hB
      | succ n =>
        exact (CtxHom_iff_getElem?.mp hΓ).2 n A hn
    · exact CtxHom_iff_getElem?.mpr
        ⟨fun n hn => htail (n + 1) (Nat.succ_le_succ hn), fun n A hn => h (n + 1) A hn⟩
    · exact h 0 B rfl

theorem compCtx_ge : ∀ {Γ : Context} {γ₁ γ₂ γ₃ δ₁₂ δ₂₃ : Env} {n : Nat},
    Γ.length ≤ n → compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃ n = δ₂₃ n
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: Γ, γ₁, γ₂, γ₃, δ₁₂, δ₂₃, _ + 1, hn =>
    compCtx_ge (Γ := Γ) (γ₁ := renEnv Nat.succ γ₁) (γ₂ := renEnv Nat.succ γ₂)
      (γ₃ := renEnv Nat.succ γ₃) (δ₁₂ := renEnv Nat.succ δ₁₂) (δ₂₃ := renEnv Nat.succ δ₂₃)
      (Nat.le_of_succ_le_succ hn)

theorem compCtx_getElem? : ∀ {Γ : Context} {γ₁ γ₂ γ₃ δ₁₂ δ₂₃ : Env} {n : Nat} {A : Expr},
    Γ[n]? = some A →
    compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃ n =
      (evalTy A).comp (renEnv (fun k => k + n + 1) γ₃)
        ((evalTy A).reindexMor (renEnv (fun k => k + n + 1) γ₂)
          (renEnv (fun k => k + n + 1) γ₃) (renEnv (fun k => k + n + 1) δ₂₃) (δ₁₂ n))
        (δ₂₃ n)
  | _ :: _, _, _, _, _, _, 0, _, hn => by cases hn; rfl
  | _ :: Γ, γ₁, γ₂, γ₃, δ₁₂, δ₂₃, _ + 1, _, hn =>
    compCtx_getElem? (Γ := Γ) (γ₁ := renEnv Nat.succ γ₁) (γ₂ := renEnv Nat.succ γ₂)
      (γ₃ := renEnv Nat.succ γ₃) (δ₁₂ := renEnv Nat.succ δ₁₂) (δ₂₃ := renEnv Nat.succ δ₂₃) hn

theorem SemCtxWf.lookup_good_base : ∀ {Γ : Context}, SemCtxWf Γ →
    ∀ {n : Nat} {A : Expr}, Γ[n]? = some A → GoodType (Γ.length - (n + 1)) A
  | _ :: _, ⟨_, hB⟩, 0, _, hn => by cases hn; exact hB.good
  | _ :: _, ⟨hΓ, _⟩, _ + 1, _, hn => by simpa using hΓ.lookup_good_base hn

theorem SemCtxWf.lookup_good {Γ : Context} (hΓ : SemCtxWf Γ)
    {n : Nat} {A : Expr} (hn : Γ[n]? = some A) :
    GoodType Γ.length (rename (fun k => k + n + 1) A) := by
  have h := hΓ.lookup_good_base hn
  exact ⟨h.1.rename (fun k hk => by omega), h.2.rename⟩

theorem SemCtxWf.lookup_type : ∀ {Γ : Context}, SemCtxWf Γ →
    ∀ {n : Nat} {A : Expr}, Γ[n]? = some A → SemTypeWf Γ (rename (fun k => k + n + 1) A)
  | _ :: _, ⟨hΓ, hB⟩, 0, _, hn => by
    cases hn
    exact hB.weaken hΓ hB
  | B :: Γ, ⟨hΓ, hB⟩, n + 1, A, hn => by
    have ih := hΓ.lookup_type hn
    refine SemTypeWf.pullback ⟨hΓ, hB⟩ (SemCtxWf.lookup_good (Γ := B :: Γ) ⟨hΓ, hB⟩ hn) ih
      (renEnv Nat.succ) (fun _ _ δ => renEnv Nat.succ δ)
      (fun h => h.1) (fun h => h.1) (fun _ _ => rfl)
      (fun _ => ?_) (fun _ => ?_)
    · rw [evalTy_rename, evalTy_rename]
      exact ⟨rfl, Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    · rw [evalTy_rename, evalTy_rename]
      exact ⟨fun _ _ => Iff.rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

structure SemCtxEq (Γ Δ : Context) : Prop where
  ctx_left : SemCtxWf Γ
  ctx_right : SemCtxWf Δ
  len_eq : Γ.length = Δ.length
  obj_iff {γ} : CtxObj Γ γ ↔ CtxObj Δ γ
  hom_iff {γ₁ γ₂ δ} : CtxHom Γ γ₁ γ₂ δ ↔ CtxHom Δ γ₁ γ₂ δ
  comp_eq {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} : CtxHom Γ γ₁ γ₂ δ₁₂ → CtxHom Γ γ₂ γ₃ δ₂₃ →
    compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃ = compCtx Δ γ₁ γ₂ γ₃ δ₁₂ δ₂₃

theorem SemCtxEq.nil : SemCtxEq [] [] where
  ctx_left := trivial
  ctx_right := trivial
  len_eq := rfl
  obj_iff := Iff.rfl
  hom_iff := Iff.rfl
  comp_eq _ _ := rfl

theorem SemTypeWf.context {Γ Δ : Context} {A : Expr}
    (hA : SemTypeWf Γ A) (hΓΔ : SemCtxEq Γ Δ) : SemTypeWf Δ A :=
  SemTypeWf.pullback hΓΔ.ctx_right (hΓΔ.len_eq ▸ hA.good) hA id (fun _ _ δ => δ)
    (fun h => hΓΔ.obj_iff.mpr h) (fun h => hΓΔ.hom_iff.mpr h)
    (fun h₁₂ h₂₃ => (hΓΔ.comp_eq (hΓΔ.hom_iff.mpr h₁₂) (hΓΔ.hom_iff.mpr h₂₃)).symm)
    (fun _ => FamAtEq.refl _ _) (fun _ => FamAlongEq.refl _ _ _ _)

theorem SemTermWf.context {Γ Δ : Context} {t A : Expr}
    (hA : SemTypeWf Γ A) (ht : SemTermWf Γ t A) (hΓΔ : SemCtxEq Γ Δ) : SemTermWf Δ t A :=
  SemTermWf.pullback hΓΔ.ctx_right (hΓΔ.len_eq ▸ ht.good) hA ht id (fun _ _ δ => δ)
    (fun h => hΓΔ.obj_iff.mpr h) (fun h => hΓΔ.hom_iff.mpr h) (fun _ => rfl)
    (fun h₁₂ h₂₃ => (hΓΔ.comp_eq (hΓΔ.hom_iff.mpr h₁₂) (hΓΔ.hom_iff.mpr h₂₃)).symm)
    (fun _ => FamAtEq.refl _ _) (fun _ => FamAlongEq.refl _ _ _ _)
    (fun _ => rfl) (fun _ => rfl)

theorem SemTypeEq.context {Γ Δ : Context} {A B : Expr}
    (hAB : SemTypeEq Γ A B) (hΓΔ : SemCtxEq Γ Δ) : SemTypeEq Δ A B where
  ctx := hΓΔ.ctx_right
  wf_left := hAB.wf_left.context hΓΔ
  wf_right := hAB.wf_right.context hΓΔ
  lvl_eq := hAB.lvl_eq
  at_eq hγ := hAB.at_eq (hΓΔ.obj_iff.mpr hγ)
  along_eq hδ := hAB.along_eq (hΓΔ.hom_iff.mpr hδ)

theorem SemTermEq.context {Γ Δ : Context} {a b A : Expr}
    (hab : SemTermEq Γ a b A) (hΓΔ : SemCtxEq Γ Δ) : SemTermEq Δ a b A where
  ctx := hΓΔ.ctx_right
  wf_A := hab.wf_A.context hΓΔ
  wf_left := hab.wf_left.context hab.wf_A hΓΔ
  wf_right := hab.wf_right.context hab.wf_A hΓΔ
  obj_eq hγ := hab.obj_eq (hΓΔ.obj_iff.mpr hγ)
  mor_eq hδ := hab.mor_eq (hΓΔ.hom_iff.mpr hδ)

theorem SemCtxEq.cons {Γ Δ : Context} {A B : Expr}
    (hΓΔ : SemCtxEq Γ Δ) (hAB : SemTypeEq Γ A B) : SemCtxEq (A :: Γ) (B :: Δ) where
  ctx_left := ⟨hΓΔ.ctx_left, hAB.wf_left⟩
  ctx_right := ⟨hΓΔ.ctx_right, hAB.wf_right.context hΓΔ⟩
  len_eq := congrArg Nat.succ hΓΔ.len_eq
  obj_iff := by
    intro γ
    refine ⟨fun ⟨hγ, hx⟩ => ⟨hΓΔ.obj_iff.mp hγ, (hAB.at_eq hγ).obj.mp hx⟩,
      fun ⟨hγ, hx⟩ => ⟨hΓΔ.obj_iff.mpr hγ, (hAB.at_eq (hΓΔ.obj_iff.mpr hγ)).obj.mpr hx⟩⟩
  hom_iff := by
    intro γ₁ γ₂ δ
    refine ⟨fun ⟨hδ, hp⟩ => ⟨hΓΔ.hom_iff.mp hδ,
        (hAB.along_eq hδ).hetHom_iff (hAB.at_eq hδ.source) (hAB.at_eq hδ.target) |>.mp hp⟩,
      fun ⟨hδ, hp⟩ =>
        have hδ' := hΓΔ.hom_iff.mpr hδ
        ⟨hδ', (hAB.along_eq hδ').hetHom_iff (hAB.at_eq hδ'.source) (hAB.at_eq hδ'.target) |>.mpr hp⟩⟩
  comp_eq := by
    intro γ₁ γ₂ γ₃ δ₁₂ δ₂₃ ⟨h₁₂, hp₁₂⟩ ⟨h₂₃, hp₂₃⟩
    dsimp only [compCtx]
    congr 1
    · have hp₁₂v := (hAB.wf_left.tr h₁₂).vertical hp₁₂
      have hp₂₃v := (hAB.wf_left.tr h₂₃).vertical hp₂₃
      have hp₁₂_tr := (hAB.wf_left.tr h₂₃).map_hom hp₁₂v
      have hp₁₂v' := (hAB.at_eq h₁₂.target).fiberHom_iff.mp hp₁₂v
      have hp₂₃v' := (hAB.at_eq h₂₃.target).fiberHom_iff.mp hp₂₃v
      have hp₁₂_tr' := (hAB.at_eq h₂₃.target).fiberHom_iff.mp hp₁₂_tr
      rw [(hAB.at_eq h₂₃.target).comp hp₁₂_tr' hp₂₃v', (hAB.along_eq h₂₃).reindexMor hp₁₂v']
    · exact hΓΔ.comp_eq h₁₂ h₂₃

structure SemSubstWf (Γ Δ : Context) (σ : Nat → Expr) : Prop where
  ctx_src : SemCtxWf Γ
  ctx_dst : SemCtxWf Δ
  good : GoodSub Γ.length Δ.length σ
  envOn {γ} : CtxObj Δ γ → EnvOn (truncSub Γ.length σ) γ
  sub_obj {γ} : CtxObj Δ γ → CtxObj Γ (subObj (truncSub Γ.length σ) γ)
  sub_hom {γ₁ γ₂ δ} : CtxHom Δ γ₁ γ₂ δ →
    CtxHom Γ (subObj (truncSub Γ.length σ) γ₁) (subObj (truncSub Γ.length σ) γ₂)
      (subMor (truncSub Γ.length σ) γ₁ γ₂ δ)
  sub_comp {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} : CtxHom Δ γ₁ γ₂ δ₁₂ → CtxHom Δ γ₂ γ₃ δ₂₃ →
    subMor (truncSub Γ.length σ) γ₁ γ₃ (compCtx Δ γ₁ γ₂ γ₃ δ₁₂ δ₂₃) =
      compCtx Γ (subObj (truncSub Γ.length σ) γ₁) (subObj (truncSub Γ.length σ) γ₂)
        (subObj (truncSub Γ.length σ) γ₃)
        (subMor (truncSub Γ.length σ) γ₁ γ₂ δ₁₂)
        (subMor (truncSub Γ.length σ) γ₂ γ₃ δ₂₃)

theorem SemTypeWf.subst {Γ Δ : Context} {A : Expr} {σ : Nat → Expr}
    (hA : SemTypeWf Γ A) (hσ : SemSubstWf Γ Δ σ) : SemTypeWf Δ (substitute σ A) := by
  have hsub := (eval_substitute_scoped hA.good.1 (fun n hn => (hσ.good n hn).2)).1
  exact SemTypeWf.pullback hσ.ctx_dst (hA.good.subst hσ.good) hA
    (subObj (truncSub Γ.length σ)) (subMor (truncSub Γ.length σ))
    hσ.sub_obj hσ.sub_hom hσ.sub_comp
    (fun hγ => hsub.atEq (hσ.envOn hγ))
    (fun hδ => hsub.alongEq _ (hσ.envOn hδ.source) (hσ.envOn hδ.target))

theorem SemTermWf.subst {Γ Δ : Context} {t A : Expr} {σ : Nat → Expr}
    (hA : SemTypeWf Γ A) (ht : SemTermWf Γ t A) (hσ : SemSubstWf Γ Δ σ) :
    SemTermWf Δ (substitute σ t) (substitute σ A) := by
  have hsubA := (eval_substitute_scoped hA.good.1 (fun n hn => (hσ.good n hn).2)).1
  have hsubt := (eval_substitute_scoped ht.good.1 (fun n hn => (hσ.good n hn).2)).2
  exact SemTermWf.pullback hσ.ctx_dst (ht.good.subst hσ.good) hA ht
    (subObj (truncSub Γ.length σ)) (subMor (truncSub Γ.length σ))
    hσ.sub_obj hσ.sub_hom (fun hγ => subMor_idEnv (hσ.envOn hγ)) hσ.sub_comp
    (fun hγ => hsubA.atEq (hσ.envOn hγ))
    (fun hδ => hsubA.alongEq _ (hσ.envOn hδ.source) (hσ.envOn hδ.target))
    (fun hγ => hsubt.1 _ (hσ.envOn hγ))
    (fun hδ => hsubt.2 _ _ _ (hσ.envOn hδ.source) (hσ.envOn hδ.target))

theorem SemTypeEq.subst {Γ Δ : Context} {A B : Expr} {σ : Nat → Expr}
    (hAB : SemTypeEq Γ A B) (hσ : SemSubstWf Γ Δ σ) :
    SemTypeEq Δ (substitute σ A) (substitute σ B) := by
  have hsubA := (eval_substitute_scoped hAB.wf_left.good.1 (fun n hn => (hσ.good n hn).2)).1
  have hsubB := (eval_substitute_scoped hAB.wf_right.good.1 (fun n hn => (hσ.good n hn).2)).1
  refine SemTypeEq.of_left hσ.ctx_dst (hAB.wf_left.subst hσ) (hAB.wf_right.good.subst hσ.good)
    (hsubA.1.trans (hAB.lvl_eq.trans hsubB.1.symm))
    (fun hγ => ?_) (fun hδ => ?_)
  · exact (hsubA.atEq (hσ.envOn hγ)).trans
      ((hAB.at_eq (hσ.sub_obj hγ)).trans (hsubB.atEq (hσ.envOn hγ)).symm)
  · have h₁ := hσ.envOn hδ.source
    have h₂ := hσ.envOn hδ.target
    have hAB_at₁ := hAB.at_eq (hσ.sub_obj hδ.source)
    have hAB_at₂ := hAB.at_eq (hσ.sub_obj hδ.target)
    have hal₁ := (hsubA.alongEq _ h₁ h₂).trans hAB_at₁ hAB_at₂ (hAB.along_eq (hσ.sub_hom hδ))
    exact hal₁.trans (hsubB.atEq h₁).symm (hsubB.atEq h₂).symm
      ((hsubB.alongEq _ h₁ h₂).symm (hsubB.atEq h₁) (hsubB.atEq h₂))

theorem SemTermEq.subst {Γ Δ : Context} {a b A : Expr} {σ : Nat → Expr}
    (hab : SemTermEq Γ a b A) (hσ : SemSubstWf Γ Δ σ) :
    SemTermEq Δ (substitute σ a) (substitute σ b) (substitute σ A) := by
  have hsuba := (eval_substitute_scoped hab.wf_left.good.1 (fun n hn => (hσ.good n hn).2)).2
  have hsubb := (eval_substitute_scoped hab.wf_right.good.1 (fun n hn => (hσ.good n hn).2)).2
  refine SemTermEq.of_left hσ.ctx_dst (hab.wf_A.subst hσ)
    (hab.wf_left.subst hab.wf_A hσ) (hab.wf_right.good.subst hσ.good)
    (fun hγ => ?_) (fun hδ => ?_)
  · rw [hsuba.1 _ (hσ.envOn hγ), hsubb.1 _ (hσ.envOn hγ), hab.obj_eq (hσ.sub_obj hγ)]
  · rw [hsuba.2 _ _ _ (hσ.envOn hδ.source) (hσ.envOn hδ.target),
      hsubb.2 _ _ _ (hσ.envOn hδ.source) (hσ.envOn hδ.target),
      hab.mor_eq (hσ.sub_hom hδ)]

theorem SemSubstWf.of_terms {Γ Δ : Context} {σ : Nat → Expr}
    (hΓ : SemCtxWf Γ) (hΔ : SemCtxWf Δ)
    (hσ : ∀ n A, Γ[n]? = some A →
      SemTermWf Δ (σ n) (substitute σ (rename (fun k => k + n + 1) A))) :
    SemSubstWf Γ Δ σ := by
  have hgood : GoodSub Γ.length Δ.length σ := fun n hn =>
    (hσ n Γ[n] (List.getElem?_eq_getElem hn)).good
  have henvOn : ∀ {γ}, CtxObj Δ γ → EnvOn (truncSub Γ.length σ) γ := fun hγ =>
    truncSub_envOn (fun n hn => ((hσ n Γ[n] (List.getElem?_eq_getElem hn)).at_obj hγ).id)
  have hA_sub : ∀ {n A}, Γ[n]? = some A →
      FamSubstAt (evalTy (substitute σ (rename (fun k => k + n + 1) A)))
        (evalTy (rename (fun k => k + n + 1) A)) (truncSub Γ.length σ) := fun hn =>
    (eval_substitute_scoped (hΓ.lookup_good hn).1 (fun m hm => (hgood m hm).2)).1
  refine ⟨hΓ, hΔ, hgood, henvOn, fun hγ => ?_, fun {γ₁ γ₂ δ} hδ => ?_,
    fun {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} h₁₂ h₂₃ => ?_⟩
  · refine CtxObj_iff_getElem?.mpr (fun n A hn => ?_)
    have hn_lt : n < Γ.length := (List.getElem?_eq_some_iff.mp hn).1
    have hto := ((hσ n A hn).at_obj hγ).obj
    have hAt := (hA_sub hn).atEq (henvOn hγ)
    have hto' := hAt.obj.mp hto
    rw [evalTy_rename] at hto'
    simpa only [subObj, truncSub, if_pos hn_lt, renameFam] using hto'
  · refine CtxHom_iff_getElem?.mpr ⟨fun n hn => ?_, fun n A hn => ?_⟩
    · have hn_not_lt : ¬ n < Γ.length := Nat.not_lt.mpr hn
      simp [subObj, subMor, truncSub, hn_not_lt, evalTm, eval, idVal]
    · have hn_lt : n < Γ.length := (List.getElem?_eq_some_iff.mp hn).1
      have hta := (hσ n A hn).along hδ
      have hAt₁ := (hA_sub hn).atEq (henvOn hδ.source)
      have hAt₂ := (hA_sub hn).atEq (henvOn hδ.target)
      have hAl := (hA_sub hn).alongEq δ (henvOn hδ.source) (henvOn hδ.target)
      have hta' := (hAl.hetHom_iff hAt₁ hAt₂).mp hta
      rw [evalTy_rename] at hta'
      simpa only [subObj, subMor, truncSub, if_pos hn_lt, renameFam] using hta'
  · funext n
    by_cases hn_lt : n < Γ.length
    · have hn : Γ[n]? = some Γ[n] := List.getElem?_eq_getElem hn_lt
      have hcm := (hσ n Γ[n] hn).comp_mor h₁₂ h₂₃
      have h_lhs : subMor (truncSub Γ.length σ) γ₁ γ₃ (compCtx Δ γ₁ γ₂ γ₃ δ₁₂ δ₂₃) n =
          (evalTm (σ n)).mor γ₁ γ₃ (compCtx Δ γ₁ γ₂ γ₃ δ₁₂ δ₂₃) := by
        simp [subMor, truncSub, if_pos hn_lt]
      rw [h_lhs, hcm, compCtx_getElem? hn]
      rw [((hA_sub hn).2.1 γ₃ (henvOn h₂₃.target)).2.1,
        ((hA_sub hn).2.2 γ₂ γ₃ δ₂₃ (henvOn h₂₃.source) (henvOn h₂₃.target)).2.2.1,
        evalTy_rename]
      simp [subMor, truncSub, if_pos hn_lt, renameFam]
    · have hn_ge : Γ.length ≤ n := Nat.le_of_not_lt hn_lt
      rw [compCtx_ge hn_ge]
      simp [subMor, truncSub, hn_lt, evalTm, eval]

structure SemSubstEq (Γ Δ : Context) (σ τ : Nat → Expr) : Prop where
  wf_left : SemSubstWf Γ Δ σ
  wf_right : SemSubstWf Γ Δ τ
  subObj_eq {γ} : CtxObj Δ γ →
    subObj (truncSub Γ.length σ) γ = subObj (truncSub Γ.length τ) γ
  subMor_eq {γ₁ γ₂ δ} : CtxHom Δ γ₁ γ₂ δ →
    subMor (truncSub Γ.length σ) γ₁ γ₂ δ = subMor (truncSub Γ.length τ) γ₁ γ₂ δ

theorem SemSubstEq.of_terms {Γ Δ : Context} {σ τ : Nat → Expr}
    (hσ : SemSubstWf Γ Δ σ) (hτ : SemSubstWf Γ Δ τ)
    (hστ : ∀ n A, Γ[n]? = some A →
      SemTermEq Δ (σ n) (τ n) (substitute σ (rename (fun k => k + n + 1) A))) :
    SemSubstEq Γ Δ σ τ where
  wf_left := hσ
  wf_right := hτ
  subObj_eq hγ := by
    funext n
    by_cases hn : n < Γ.length
    · simpa only [subObj, truncSub, if_pos hn] using
        (hστ n Γ[n] (List.getElem?_eq_getElem hn)).obj_eq hγ
    · simp [subObj, truncSub, hn]
  subMor_eq hδ := by
    funext n
    by_cases hn : n < Γ.length
    · simpa only [subMor, truncSub, if_pos hn] using
        (hστ n Γ[n] (List.getElem?_eq_getElem hn)).mor_eq hδ
    · simp [subMor, truncSub, hn]

theorem SemTypeEq.substEq {Γ Δ : Context} {A : Expr} {σ τ : Nat → Expr}
    (hA : SemTypeWf Γ A) (hστ : SemSubstEq Γ Δ σ τ) :
    SemTypeEq Δ (substitute σ A) (substitute τ A) := by
  have hsubσ := (eval_substitute_scoped hA.good.1 (fun n hn => (hστ.wf_left.good n hn).2)).1
  have hsubτ := (eval_substitute_scoped hA.good.1 (fun n hn => (hστ.wf_right.good n hn).2)).1
  refine SemTypeEq.of_left hστ.wf_left.ctx_dst (hA.subst hστ.wf_left)
    (hA.good.subst hστ.wf_right.good) (hsubσ.1.trans hsubτ.1.symm)
    (fun hγ => ?_) (fun {γ₁ γ₂ δ} hδ => ?_)
  · have h₁ := hsubσ.atEq (hστ.wf_left.envOn hγ)
    have h₂ := hsubτ.atEq (hστ.wf_right.envOn hγ)
    rw [← hστ.subObj_eq hγ] at h₂
    exact h₁.trans h₂.symm
  · have h₁_τ := hsubτ.atEq (hστ.wf_right.envOn hδ.source)
    have h₂_τ := hsubτ.atEq (hστ.wf_right.envOn hδ.target)
    have hal_σ := hsubσ.alongEq δ (hστ.wf_left.envOn hδ.source) (hστ.wf_left.envOn hδ.target)
    have hal_τ := hsubτ.alongEq δ (hστ.wf_right.envOn hδ.source) (hστ.wf_right.envOn hδ.target)
    rw [← hστ.subObj_eq hδ.source] at h₁_τ hal_τ
    rw [← hστ.subObj_eq hδ.target] at h₂_τ hal_τ
    rw [← hστ.subMor_eq hδ] at hal_τ
    exact hal_σ.trans h₁_τ.symm h₂_τ.symm (hal_τ.symm h₁_τ h₂_τ)

theorem SemTermEq.substEq {Γ Δ : Context} {a A : Expr} {σ τ : Nat → Expr}
    (hA : SemTypeWf Γ A) (ha : SemTermWf Γ a A) (hστ : SemSubstEq Γ Δ σ τ) :
    SemTermEq Δ (substitute σ a) (substitute τ a) (substitute σ A) := by
  have hsubσ := (eval_substitute_scoped ha.good.1 (fun n hn => (hστ.wf_left.good n hn).2)).2
  have hsubτ := (eval_substitute_scoped ha.good.1 (fun n hn => (hστ.wf_right.good n hn).2)).2
  refine SemTermEq.of_left hστ.wf_left.ctx_dst (hA.subst hστ.wf_left)
    (ha.subst hA hστ.wf_left) (ha.good.subst hστ.wf_right.good)
    (fun hγ => ?_) (fun hδ => ?_)
  · rw [hsubσ.1 _ (hστ.wf_left.envOn hγ), hsubτ.1 _ (hστ.wf_right.envOn hγ), hστ.subObj_eq hγ]
  · rw [hsubσ.2 _ _ _ (hστ.wf_left.envOn hδ.source) (hστ.wf_left.envOn hδ.target),
      hsubτ.2 _ _ _ (hστ.wf_right.envOn hδ.source) (hστ.wf_right.envOn hδ.target),
      hστ.subObj_eq hδ.source, hστ.subObj_eq hδ.target, hστ.subMor_eq hδ]

theorem evalTy_prefixSub_atEq (C : Expr) (es : List Expr) (ρ : Nat → Nat) (γ : Env)
    (ht : ∀ e ∈ es, evalTy e = dfltFam)
    (hi : ∀ e ∈ es, (evalTm e).mor γ γ (idEnv γ) = idVal ((evalTm e).obj γ)) :
    FamAtEq (evalTy (substitute (prefixSub es ρ) C)) (evalTy C) γ
      (es.foldr (fun e γ' => consEnv ((evalTm e).obj γ) γ') (renEnv ρ γ)) := by
  have h := (eval_substitute C (prefixSub_tmOnly es ρ ht)).1.atEq (prefixSub_envOn es ρ γ hi)
  rwa [subObj_prefixSub] at h

theorem evalTy_prefixSub_alongEq (C : Expr) (es : List Expr) (ρ : Nat → Nat) (γ₁ γ₂ δ : Env)
    (ht : ∀ e ∈ es, evalTy e = dfltFam)
    (hi₁ : ∀ e ∈ es, (evalTm e).mor γ₁ γ₁ (idEnv γ₁) = idVal ((evalTm e).obj γ₁))
    (hi₂ : ∀ e ∈ es, (evalTm e).mor γ₂ γ₂ (idEnv γ₂) = idVal ((evalTm e).obj γ₂)) :
    FamAlongEq (evalTy (substitute (prefixSub es ρ) C)) (evalTy C) γ₁ γ₂ δ
      (es.foldr (fun e γ' => consEnv ((evalTm e).obj γ₁) γ') (renEnv ρ γ₁))
      (es.foldr (fun e γ' => consEnv ((evalTm e).obj γ₂) γ') (renEnv ρ γ₂))
      (es.foldr (fun e δ' => consEnv ((evalTm e).mor γ₁ γ₂ δ) δ') (renEnv ρ δ)) := by
  have h := (eval_substitute C (prefixSub_tmOnly es ρ ht)).1.alongEq δ
    (prefixSub_envOn es ρ γ₁ hi₁) (prefixSub_envOn es ρ γ₂ hi₂)
  rwa [subObj_prefixSub, subObj_prefixSub, subMor_prefixSub] at h

theorem evalTm_prefixSub_mor (t : Expr) (es : List Expr) (ρ : Nat → Nat) (γ₁ γ₂ δ : Env)
    (ht : ∀ e ∈ es, evalTy e = dfltFam)
    (hi₁ : ∀ e ∈ es, (evalTm e).mor γ₁ γ₁ (idEnv γ₁) = idVal ((evalTm e).obj γ₁))
    (hi₂ : ∀ e ∈ es, (evalTm e).mor γ₂ γ₂ (idEnv γ₂) = idVal ((evalTm e).obj γ₂)) :
    (evalTm (substitute (prefixSub es ρ) t)).mor γ₁ γ₂ δ =
      (evalTm t).mor
        (es.foldr (fun e γ' => consEnv ((evalTm e).obj γ₁) γ') (renEnv ρ γ₁))
        (es.foldr (fun e γ' => consEnv ((evalTm e).obj γ₂) γ') (renEnv ρ γ₂))
        (es.foldr (fun e δ' => consEnv ((evalTm e).mor γ₁ γ₂ δ) δ') (renEnv ρ δ)) := by
  simpa only [subObj_prefixSub, subMor_prefixSub] using
    (eval_substitute t (prefixSub_tmOnly es ρ ht)).2.2 γ₁ γ₂ δ
      (prefixSub_envOn es ρ γ₁ hi₁) (prefixSub_envOn es ρ γ₂ hi₂)

theorem instantiate_atEq {Γ : Context} {A : Expr} (B : Expr) {a : Expr}
    (ha : SemTermWf Γ a A) {γ : Env} (hγ : CtxObj Γ γ) :
    FamAtEq (evalTy (instantiate B a)) (evalTy B) γ (consEnv ((evalTm a).obj γ) γ) := by
  rw [instantiate_eq_prefixSub]
  exact evalTy_prefixSub_atEq B [a] id γ
    (List.forall_mem_singleton.mpr (evalTy_of_isTm ha.good.2))
    (List.forall_mem_singleton.mpr (ha.at_obj hγ).id)

theorem instantiate_alongEq {Γ : Context} {A : Expr} (B : Expr) {a : Expr}
    (ha : SemTermWf Γ a A) {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ) :
    FamAlongEq (evalTy (instantiate B a)) (evalTy B) γ₁ γ₂ δ
      (consEnv ((evalTm a).obj γ₁) γ₁) (consEnv ((evalTm a).obj γ₂) γ₂)
      (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ) := by
  rw [instantiate_eq_prefixSub]
  exact evalTy_prefixSub_alongEq B [a] id γ₁ γ₂ δ
    (List.forall_mem_singleton.mpr (evalTy_of_isTm ha.good.2))
    (List.forall_mem_singleton.mpr (ha.at_obj hδ.source).id)
    (List.forall_mem_singleton.mpr (ha.at_obj hδ.target).id)

theorem evalTm_instantiate_mor {Γ : Context} {A : Expr} (t : Expr) {a : Expr}
    (ha : SemTermWf Γ a A) {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ) :
    (evalTm (instantiate t a)).mor γ₁ γ₂ δ =
      (evalTm t).mor (consEnv ((evalTm a).obj γ₁) γ₁) (consEnv ((evalTm a).obj γ₂) γ₂)
        (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ) := by
  rw [instantiate_eq_prefixSub]
  exact evalTm_prefixSub_mor t [a] id γ₁ γ₂ δ
    (List.forall_mem_singleton.mpr (evalTy_of_isTm ha.good.2))
    (List.forall_mem_singleton.mpr (ha.at_obj hδ.source).id)
    (List.forall_mem_singleton.mpr (ha.at_obj hδ.target).id)

theorem SemTypeWf.instantiate {Γ : Context} {A B a : Expr}
    (hΓ : SemCtxWf Γ) (hB : SemTypeWf (A :: Γ) B) (ha : SemTermWf Γ a A) :
    SemTypeWf Γ (HofmannStreicher1994.instantiate B a) :=
  SemTypeWf.pullback hΓ ⟨scoped_instantiate hB.good.1 ha.good.1, hB.good.2.substitute⟩ hB
    (fun γ => consEnv ((evalTm a).obj γ) γ)
    (fun γ₁ γ₂ δ => consEnv ((evalTm a).mor γ₁ γ₂ δ) δ)
    (fun hγ => ⟨hγ, (ha.at_obj hγ).obj⟩)
    (fun hδ => ⟨hδ, ha.along hδ⟩)
    (fun h₁₂ h₂₃ => by rw [compCtx_consEnv, ha.comp_mor h₁₂ h₂₃])
    (fun hγ => instantiate_atEq B ha hγ)
    (fun hδ => instantiate_alongEq B ha hδ)

theorem instantiate₂_atEq {Γ : Context} {A B : Expr} (C : Expr) {a b : Expr}
    (ha : SemTermWf Γ a A) (hb : SemTermWf Γ b B) {γ : Env} (hγ : CtxObj Γ γ) :
    FamAtEq (evalTy (instantiate₂ C a b)) (evalTy C) γ
      (consEnv ((evalTm b).obj γ) (consEnv ((evalTm a).obj γ) γ)) := by
  rw [instantiate₂_eq_prefixSub]
  exact evalTy_prefixSub_atEq C [b, a] id γ
    (List.forall_mem_cons.mpr ⟨evalTy_of_isTm hb.good.2, List.forall_mem_singleton.mpr (evalTy_of_isTm ha.good.2)⟩)
    (List.forall_mem_cons.mpr ⟨(hb.at_obj hγ).id, List.forall_mem_singleton.mpr (ha.at_obj hγ).id⟩)

theorem instantiate₂_alongEq {Γ : Context} {A B : Expr} (C : Expr) {a b : Expr}
    (ha : SemTermWf Γ a A) (hb : SemTermWf Γ b B) {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ) :
    FamAlongEq (evalTy (instantiate₂ C a b)) (evalTy C) γ₁ γ₂ δ
      (consEnv ((evalTm b).obj γ₁) (consEnv ((evalTm a).obj γ₁) γ₁))
      (consEnv ((evalTm b).obj γ₂) (consEnv ((evalTm a).obj γ₂) γ₂))
      (consEnv ((evalTm b).mor γ₁ γ₂ δ) (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ)) := by
  rw [instantiate₂_eq_prefixSub]
  exact evalTy_prefixSub_alongEq C [b, a] id γ₁ γ₂ δ
    (List.forall_mem_cons.mpr ⟨evalTy_of_isTm hb.good.2, List.forall_mem_singleton.mpr (evalTy_of_isTm ha.good.2)⟩)
    (List.forall_mem_cons.mpr ⟨(hb.at_obj hδ.source).id, List.forall_mem_singleton.mpr (ha.at_obj hδ.source).id⟩)
    (List.forall_mem_cons.mpr ⟨(hb.at_obj hδ.target).id, List.forall_mem_singleton.mpr (ha.at_obj hδ.target).id⟩)

theorem evalTm_instantiate₂_mor {Γ : Context} {A B : Expr} (t : Expr) {a b : Expr}
    (ha : SemTermWf Γ a A) (hb : SemTermWf Γ b B) {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ) :
    (evalTm (instantiate₂ t a b)).mor γ₁ γ₂ δ =
      (evalTm t).mor
        (consEnv ((evalTm b).obj γ₁) (consEnv ((evalTm a).obj γ₁) γ₁))
        (consEnv ((evalTm b).obj γ₂) (consEnv ((evalTm a).obj γ₂) γ₂))
        (consEnv ((evalTm b).mor γ₁ γ₂ δ) (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ)) := by
  rw [instantiate₂_eq_prefixSub]
  exact evalTm_prefixSub_mor t [b, a] id γ₁ γ₂ δ
    (List.forall_mem_cons.mpr ⟨evalTy_of_isTm hb.good.2, List.forall_mem_singleton.mpr (evalTy_of_isTm ha.good.2)⟩)
    (List.forall_mem_cons.mpr ⟨(hb.at_obj hδ.source).id, List.forall_mem_singleton.mpr (ha.at_obj hδ.source).id⟩)
    (List.forall_mem_cons.mpr ⟨(hb.at_obj hδ.target).id, List.forall_mem_singleton.mpr (ha.at_obj hδ.target).id⟩)

theorem instantiate₃_atEq {Γ : Context} {A B P : Expr} (C : Expr) {a b p : Expr}
    (ha : SemTermWf Γ a A) (hb : SemTermWf Γ b B) (hp : SemTermWf Γ p P)
    {γ : Env} (hγ : CtxObj Γ γ) :
    FamAtEq (evalTy (instantiate₃ C a b p)) (evalTy C) γ
      (consEnv ((evalTm p).obj γ) (consEnv ((evalTm b).obj γ) (consEnv ((evalTm a).obj γ) γ))) := by
  rw [instantiate₃_eq_prefixSub]
  exact evalTy_prefixSub_atEq C [p, b, a] id γ
    (List.forall_mem_cons.mpr ⟨evalTy_of_isTm hp.good.2,
      List.forall_mem_cons.mpr ⟨evalTy_of_isTm hb.good.2, List.forall_mem_singleton.mpr (evalTy_of_isTm ha.good.2)⟩⟩)
    (List.forall_mem_cons.mpr ⟨(hp.at_obj hγ).id,
      List.forall_mem_cons.mpr ⟨(hb.at_obj hγ).id, List.forall_mem_singleton.mpr (ha.at_obj hγ).id⟩⟩)

theorem instantiate₃_alongEq {Γ : Context} {A B P : Expr} (C : Expr) {a b p : Expr}
    (ha : SemTermWf Γ a A) (hb : SemTermWf Γ b B) (hp : SemTermWf Γ p P)
    {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ) :
    FamAlongEq (evalTy (instantiate₃ C a b p)) (evalTy C) γ₁ γ₂ δ
      (consEnv ((evalTm p).obj γ₁) (consEnv ((evalTm b).obj γ₁) (consEnv ((evalTm a).obj γ₁) γ₁)))
      (consEnv ((evalTm p).obj γ₂) (consEnv ((evalTm b).obj γ₂) (consEnv ((evalTm a).obj γ₂) γ₂)))
      (consEnv ((evalTm p).mor γ₁ γ₂ δ) (consEnv ((evalTm b).mor γ₁ γ₂ δ) (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ))) := by
  rw [instantiate₃_eq_prefixSub]
  exact evalTy_prefixSub_alongEq C [p, b, a] id γ₁ γ₂ δ
    (List.forall_mem_cons.mpr ⟨evalTy_of_isTm hp.good.2,
      List.forall_mem_cons.mpr ⟨evalTy_of_isTm hb.good.2, List.forall_mem_singleton.mpr (evalTy_of_isTm ha.good.2)⟩⟩)
    (List.forall_mem_cons.mpr ⟨(hp.at_obj hδ.source).id,
      List.forall_mem_cons.mpr ⟨(hb.at_obj hδ.source).id, List.forall_mem_singleton.mpr (ha.at_obj hδ.source).id⟩⟩)
    (List.forall_mem_cons.mpr ⟨(hp.at_obj hδ.target).id,
      List.forall_mem_cons.mpr ⟨(hb.at_obj hδ.target).id, List.forall_mem_singleton.mpr (ha.at_obj hδ.target).id⟩⟩)

theorem reflexivityMotive_atEq (A C : Expr) (γ : Env) :
    FamAtEq (evalTy (reflexivityMotive A C)) (evalTy C) γ
      (consEnv (.idObj (idVal (γ 0))) (consEnv (γ 0) (consEnv (γ 0) (renEnv Nat.succ γ)))) := by
  rw [reflexivityMotive_eq_prefixSub]
  refine evalTy_prefixSub_atEq C [.refl (weaken A) (.var 0), .var 0, .var 0] Nat.succ γ ?_ ?_
  all_goals simp [evalTy, evalTm, eval, idEnv, idVal]

theorem reflexivityMotive_alongEq (A C : Expr) (γ₁ γ₂ δ : Env) :
    FamAlongEq (evalTy (reflexivityMotive A C)) (evalTy C) γ₁ γ₂ δ
      (consEnv (.idObj (idVal (γ₁ 0))) (consEnv (γ₁ 0) (consEnv (γ₁ 0) (renEnv Nat.succ γ₁))))
      (consEnv (.idObj (idVal (γ₂ 0))) (consEnv (γ₂ 0) (consEnv (γ₂ 0) (renEnv Nat.succ γ₂))))
      (consEnv (.idObj (idVal (γ₂ 0))) (consEnv (δ 0) (consEnv (δ 0) (renEnv Nat.succ δ)))) := by
  rw [reflexivityMotive_eq_prefixSub]
  refine evalTy_prefixSub_alongEq C [.refl (weaken A) (.var 0), .var 0, .var 0] Nat.succ γ₁ γ₂ δ ?_ ?_ ?_
  all_goals simp [evalTy, evalTm, eval, idEnv, idVal]

theorem pairingMotive_eq_prefixSub (A B C : Expr) :
    pairingMotive A B C = substitute
      (prefixSub [.pair (rename (fun n => n + 2) A)
        (rename (liftRenaming (fun n => n + 2)) B) (.var 1) (.var 0)] (fun n => n + 2)) C :=
  congrArg (fun σ => substitute σ C) (funext fun | 0 => rfl | _ + 1 => rfl)

theorem pairingMotive_atEq (A B C : Expr) (γ : Env)
    (hiA : (evalTy A).reindexObj (renEnv (fun n => n + 2) γ) (renEnv (fun n => n + 2) γ)
      (idEnv (renEnv (fun n => n + 2) γ)) (γ 1) = γ 1) :
    FamAtEq (evalTy (pairingMotive A B C)) (evalTy C) γ
      (consEnv (.pairObj (γ 1) (γ 0)) (renEnv (fun n => n + 2) γ)) := by
  rw [pairingMotive_eq_prefixSub]
  refine evalTy_prefixSub_atEq C
    [.pair (rename (fun n => n + 2) A) (rename (liftRenaming (fun n => n + 2)) B) (.var 1) (.var 0)]
    (fun n => n + 2) γ ?_ ?_
  · simp [evalTy, eval]
  · simp [evalTm, eval, evalTy_rename, renameFam, ← idEnv_renEnv, idVal, hiA]; exact ⟨rfl, rfl⟩

theorem pairingMotive_alongEq (A B C : Expr) (γ₁ γ₂ δ : Env)
    (hi₁ : (evalTy A).reindexObj (renEnv (fun n => n + 2) γ₁) (renEnv (fun n => n + 2) γ₁)
      (idEnv (renEnv (fun n => n + 2) γ₁)) (γ₁ 1) = γ₁ 1)
    (hi₂ : (evalTy A).reindexObj (renEnv (fun n => n + 2) γ₂) (renEnv (fun n => n + 2) γ₂)
      (idEnv (renEnv (fun n => n + 2) γ₂)) (γ₂ 1) = γ₂ 1) :
    FamAlongEq (evalTy (pairingMotive A B C)) (evalTy C) γ₁ γ₂ δ
      (consEnv (.pairObj (γ₁ 1) (γ₁ 0)) (renEnv (fun n => n + 2) γ₁))
      (consEnv (.pairObj (γ₂ 1) (γ₂ 0)) (renEnv (fun n => n + 2) γ₂))
      (consEnv (.pairMor ((evalTy A).reindexObj (renEnv (fun n => n + 2) γ₁)
        (renEnv (fun n => n + 2) γ₂) (renEnv (fun n => n + 2) δ) (γ₁ 1)) (γ₂ 1) (δ 1) (δ 0))
        (renEnv (fun n => n + 2) δ)) := by
  rw [pairingMotive_eq_prefixSub]
  have h := evalTy_prefixSub_alongEq C
    [.pair (rename (fun n => n + 2) A) (rename (liftRenaming (fun n => n + 2)) B) (.var 1) (.var 0)]
    (fun n => n + 2) γ₁ γ₂ δ ?_ ?_ ?_
  · simpa only [List.foldr, evalTm, eval, evalTy_rename, renameFam] using h
  · simp [evalTy, eval]
  · simp [evalTm, eval, evalTy_rename, renameFam, ← idEnv_renEnv, idVal, hi₁]; exact ⟨rfl, rfl⟩
  · simp [evalTm, eval, evalTy_rename, renameFam, ← idEnv_renEnv, idVal, hi₂]; exact ⟨rfl, rfl⟩

theorem successorMotive_eq_prefixSub (C : Expr) :
    successorMotive C = substitute (prefixSub [.succ (.var 1)] (fun n => n + 2)) C :=
  congrArg (fun σ => substitute σ C) (funext fun | 0 => rfl | _ + 1 => rfl)

theorem successorMotive_atEq (C : Expr) (γ : Env) :
    FamAtEq (evalTy (successorMotive C)) (evalTy C) γ
      (consEnv (.nat (unNat (γ 1) + 1)) (renEnv (fun n => n + 2) γ)) := by
  rw [successorMotive_eq_prefixSub]
  refine evalTy_prefixSub_atEq C [.succ (.var 1)] (fun n => n + 2) γ ?_ ?_
  all_goals simp [evalTy, evalTm, eval, idVal]

theorem successorMotive_alongEq (C : Expr) (γ₁ γ₂ δ : Env) :
    FamAlongEq (evalTy (successorMotive C)) (evalTy C) γ₁ γ₂ δ
      (consEnv (.nat (unNat (γ₁ 1) + 1)) (renEnv (fun n => n + 2) γ₁))
      (consEnv (.nat (unNat (γ₂ 1) + 1)) (renEnv (fun n => n + 2) γ₂))
      (consEnv (.nat (unNat (γ₂ 1) + 1)) (renEnv (fun n => n + 2) δ)) := by
  rw [successorMotive_eq_prefixSub]
  refine evalTy_prefixSub_alongEq C [.succ (.var 1)] (fun n => n + 2) γ₁ γ₂ δ ?_ ?_ ?_
  all_goals simp [evalTy, evalTm, eval, idVal]

end HofmannStreicher1994.Repaired

/-! ## SemTypeConstructors.lean -/

namespace HofmannStreicher1994.Repaired

theorem SemTypeWf.nat {Γ : Context} : SemTypeWf Γ .nat where
  good := ⟨trivial, trivial⟩
  fiber _ := semNat_fiber_laws _
  id_tr _ := semNat_identity_transport _
  rank _ := semNat_rank_laws _
  tr _ := semNat_transport_laws _ _ _
  comp_tr _ _ := semNat_comp_transport _ _ _ _ _ _

theorem SemTypeWf.universe {Γ : Context} : SemTypeWf Γ .universe where
  good := ⟨trivial, trivial⟩
  fiber _ := semUniverse_fiber_laws _
  id_tr _ := semUniverse_identity_transport _
  rank _ := semUniverse_rank_laws _
  tr _ := semUniverse_transport_laws _ _ _
  comp_tr _ _ := semUniverse_comp_transport _ _ _ _ _ _

theorem SemTypeWf.el {Γ : Context} {a : Expr} (ha : SemTermWf Γ a .universe) :
    SemTypeWf Γ (.el a) where
  good := ⟨ha.good.1, trivial⟩
  fiber _ := semEl_fiber_laws _
  id_tr _ := semEl_identity_transport _
  rank _ := semEl_rank_laws _
  tr _ := semEl_transport_laws _ _ _
  comp_tr _ _ := semEl_comp_transport _ _ _ _ _ _

theorem SemTypeWf.identity {Γ : Context} {A a b : Expr}
    (hA : SemTypeWf Γ A) (ha : SemTermWf Γ a A) (hb : SemTermWf Γ b A) :
    SemTypeWf Γ (.identity A a b) where
  good := ⟨⟨hA.good.1, ha.good.1, hb.good.1⟩, trivial⟩
  fiber hγ := semId_fiber_laws (hA.fiber hγ) (hA.id_tr hγ) (ha.at_obj hγ) (hb.at_obj hγ)
  id_tr hγ := semId_identity_transport (hA.fiber hγ) (hA.id_tr hγ) (ha.at_obj hγ) (hb.at_obj hγ)
  rank hγ := semId_rank_laws (hA.fiber hγ) (hA.id_tr hγ) (hA.rank hγ) (ha.at_obj hγ) (hb.at_obj hγ)
  tr hδ := semId_transport_laws (hA.fiber hδ.source) (hA.fiber hδ.target)
    (hA.id_tr hδ.source) (hA.id_tr hδ.target)
    (ha.at_obj hδ.source) (hb.at_obj hδ.source)
    (ha.at_obj hδ.target) (hb.at_obj hδ.target)
    (hA.tr hδ) (ha.along hδ) (hb.along hδ)
  comp_tr h₁₂ h₂₃ := semId_comp_transport
    (hA.fiber h₁₂.source) (hA.fiber h₁₂.target) (hA.fiber h₂₃.target)
    (hA.id_tr h₁₂.source) (ha.at_obj h₁₂.source) (hb.at_obj h₁₂.source)
    (hA.tr h₁₂) (hA.tr h₂₃) (hA.comp_tr h₁₂ h₂₃)
    (ha.along h₁₂) (ha.along h₂₃) (hb.along h₁₂) (hb.along h₂₃)
    (ha.comp_mor h₁₂ h₂₃) (hb.comp_mor h₁₂ h₂₃)

theorem SemTypeWf.sigma {Γ : Context} {A B : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B) :
    SemTypeWf Γ (.sigma A B) where
  good := ⟨⟨hA.good.1, hB.good.1⟩, trivial⟩
  fiber hγ := semSigma_fiber_laws (hA.fiber hγ) (hA.id_tr hγ)
    (fun hx => hB.fiber ⟨hγ, hx⟩)
    (fun hx => hB.id_tr ⟨hγ, hx⟩)
    (fun hp => hB.tr ⟨hΓ.id_hom hγ, hp⟩)
    (fun hp₁ hp₂ => hA.ctB_vert hΓ hB hγ hp₁ hp₂)
  id_tr hγ := semSigma_identity_transport (hA.id_tr hγ)
    (fun hx => hB.id_tr ⟨hγ, hx⟩)
    (fun hp => hB.tr ⟨hΓ.id_hom hγ, hp⟩)
  rank hγ := semSigma_rank_laws (hA.id_tr hγ) (hA.rank hγ)
    (fun hx => hB.rank ⟨hγ, hx⟩)
    (fun hp => hB.tr ⟨hΓ.id_hom hγ, hp⟩)
  tr hδ := semSigma_transport_laws (hA.fiber hδ.target)
    (hA.id_tr hδ.source) (hA.id_tr hδ.target) (hA.tr hδ)
    (fun hp => hB.tr ⟨hΓ.id_hom hδ.source, hp⟩)
    (fun hp => hB.tr ⟨hΓ.id_hom hδ.target, hp⟩)
    (fun hp => hB.tr ⟨hδ, hp⟩)
    (fun hp => hA.ctB_left hΓ hB hδ hp)
    (fun hp => hA.ctB_right hΓ hB hδ hp)
  comp_tr h₁₂ h₂₃ := semSigma_comp_transport (hA.id_tr h₁₂.source) (hA.comp_tr h₁₂ h₂₃)
    (fun hp => hB.tr ⟨hΓ.id_hom h₁₂.source, hp⟩)
    (fun hx => hA.ctB_id hB h₁₂ h₂₃ hx)

theorem SemTypeWf.pi {Γ : Context} {A B : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B) :
    SemTypeWf Γ (.pi A B) where
  good := ⟨⟨hA.good.1, hB.good.1⟩, trivial⟩
  fiber hγ := semPi_fiber_laws (hA.fiber hγ) (hA.id_tr hγ)
    (hA.tr (hΓ.id_hom hγ)) (hA.rank hγ)
    (fun _ hx => hB.fiber ⟨hγ, hx⟩)
    (fun _ hx => hB.id_tr ⟨hγ, hx⟩)
    (fun _ _ _ hp => hB.tr ⟨hΓ.id_hom hγ, hp⟩)
    (fun _ _ _ _ _ hp₁ hp₂ => hA.ctB_vert hΓ hB hγ hp₁ hp₂)
  id_tr hγ := semPi_identity_transport (hA.id_tr hγ) (hA.tr (hΓ.id_hom hγ))
    (fun _ hx => hB.id_tr ⟨hγ, hx⟩)
    (fun _ _ _ hp => hB.tr ⟨hΓ.id_hom hγ, hp⟩)
  rank hγ := semPi_rank_laws (hA.id_tr hγ) (hA.tr (hΓ.id_hom hγ))
    (fun _ hx => hB.id_tr ⟨hγ, hx⟩)
    (fun _ hx => hB.rank ⟨hγ, hx⟩)
    (fun _ _ _ hp => hB.tr ⟨hΓ.id_hom hγ, hp⟩)
  tr hδ := semPi_transport_laws (hA.fiber hδ.source) (hA.fiber hδ.target)
    (hA.id_tr hδ.source) (hA.id_tr hδ.target)
    (hA.tr (hΓ.id_hom hδ.source)) (hA.tr (hΓ.id_hom hδ.target))
    (hA.rank hδ.source) (hA.rank hδ.target) (hA.tr hδ)
    (fun _ hx => hB.fiber ⟨hδ.source, hx⟩)
    (fun _ hx => hB.id_tr ⟨hδ.source, hx⟩)
    (fun _ hx => hB.id_tr ⟨hδ.target, hx⟩)
    (fun _ _ _ hp => hB.tr ⟨hΓ.id_hom hδ.source, hp⟩)
    (fun _ _ _ hp => hB.tr ⟨hΓ.id_hom hδ.target, hp⟩)
    (fun _ _ _ hp => hB.tr ⟨hδ, hp⟩)
    (fun _ _ _ hp => hA.ctB_left hΓ hB hδ hp)
    (fun _ _ _ hp => hA.ctB_right hΓ hB hδ hp)
  comp_tr h₁₂ h₂₃ := semPi_comp_transport
    (hA.id_tr h₁₂.source) (hA.tr (hΓ.id_hom h₁₂.source)) (hA.rank h₁₂.target)
    (hA.tr h₁₂) (hA.tr h₂₃) (hA.tr (hΓ.comp_hom h₁₂ h₂₃)) (hA.comp_tr h₁₂ h₂₃)
    (fun _ hx => hB.id_tr ⟨h₁₂.source, hx⟩)
    (fun _ _ _ hp => hB.tr ⟨hΓ.id_hom h₁₂.source, hp⟩)
    (fun _ hx₃ => hA.ctB_unmap hΓ hB h₁₂ h₂₃ hx₃)

theorem SemTypeWf.instantiate₃ {Γ : Context} {A C a b p : Expr}
    (hΓ : SemCtxWf Γ) (hC : SemTypeWf (identityContext Γ A) C)
    (ha : SemTermWf Γ a A) (hb : SemTermWf Γ b A) (hp : SemTermWf Γ p (.identity A a b)) :
    SemTypeWf Γ (HofmannStreicher1994.instantiate₃ C a b p) := by
  refine SemTypeWf.pullback hΓ
    ⟨scoped_instantiate₃ hC.good.1 ha.good.1 hb.good.1 hp.good.1, hC.good.2.substitute⟩ hC
    (fun γ => consEnv ((evalTm p).obj γ) (consEnv ((evalTm b).obj γ) (consEnv ((evalTm a).obj γ) γ)))
    (fun γ₁ γ₂ δ => consEnv ((evalTm p).mor γ₁ γ₂ δ) (consEnv ((evalTm b).mor γ₁ γ₂ δ) (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ)))
    (fun hγ => ?_) (fun hδ => ?_) (fun h₁₂ h₂₃ => ?_)
    (fun hγ => instantiate₃_atEq C ha hb hp hγ)
    (fun hδ => instantiate₃_alongEq C ha hb hp hδ)
  · refine ⟨⟨⟨hγ, (ha.at_obj hγ).obj⟩, ?_⟩, ?_⟩
    · rw [HofmannStreicher1994.weaken, evalTy_rename]
      exact (hb.at_obj hγ).obj
    · simp only [evalTy, eval, semId, HofmannStreicher1994.weaken, eval_rename, renameFam,
        renEnv_succ_consEnv, idEnv_consEnv, consEnv_zero, consEnv_succ]
      exact (hp.at_obj hγ).obj
  · refine ⟨⟨⟨hδ, ha.along hδ⟩, ?_⟩, ?_⟩
    · rw [HofmannStreicher1994.weaken, evalTy_rename]
      exact hb.along hδ
    · simp only [piHetMor, evalTy, eval, semId, HofmannStreicher1994.weaken, eval_rename, renameFam,
        renEnv_succ_consEnv, idEnv_consEnv, consEnv_zero, consEnv_succ]
      exact hp.along hδ
  · dsimp only [identityContext]
    rw [compCtx_consEnv, compCtx_consEnv, compCtx_consEnv,
      ha.comp_mor h₁₂ h₂₃, hb.comp_mor h₁₂ h₂₃, hp.comp_mor h₁₂ h₂₃]
    simp [evalTy, eval, semId, HofmannStreicher1994.weaken, evalTy_rename, renameFam]

theorem SemTypeEq.of_left_hyps {Γ : Context} {C C' : Expr}
    (hΓ : SemCtxWf Γ) (wf_left : SemTypeWf Γ C) (hgood_right : GoodType Γ.length C')
    (lvl_eq : (evalTy C').lvl = (evalTy C).lvl)
    (obj_eq : ∀ {γ x}, CtxObj Γ γ → ((evalTy C').Obj γ x ↔ (evalTy C).Obj γ x))
    (comp_eq : ∀ {γ x y z p q}, CtxObj Γ γ →
      FiberHom (evalTy C) γ x y p → FiberHom (evalTy C) γ y z q →
      (evalTy C').comp γ p q = (evalTy C).comp γ p q)
    (inv_eq : ∀ {γ x y p}, CtxObj Γ γ →
      FiberHom (evalTy C) γ x y p → (evalTy C').inv γ p = (evalTy C).inv γ p)
    (along_eq : ∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ →
      FamAlongEq (evalTy C') (evalTy C) γ₁ γ₂ δ γ₁ γ₂ δ) :
    SemTypeEq Γ C C' := by
  have at_eq : ∀ {γ}, CtxObj Γ γ → FamAtEq (evalTy C') (evalTy C) γ γ := fun hγ =>
    { lvl := lvl_eq
      obj := obj_eq hγ
      hom_id := (along_eq (hΓ.id_hom hγ)).hom
      comp := comp_eq hγ
      inv := inv_eq hγ
      ro_id := (along_eq (hΓ.id_hom hγ)).reindexObj
      rm_id := (along_eq (hΓ.id_hom hγ)).reindexMor }
  have wf_right := SemTypeWf.of_eq hΓ hgood_right wf_left at_eq along_eq
  exact ⟨hΓ, wf_left, wf_right, lvl_eq.symm, fun hγ => (at_eq hγ).symm,
    fun hδ => (along_eq hδ).symm (at_eq hδ.source) (at_eq hδ.target)⟩

theorem SemTypeEq.refl {Γ : Context} {A : Expr} (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) :
    SemTypeEq Γ A A :=
  ⟨hΓ, hA, hA, rfl, fun _ => FamAtEq.refl _ _, fun _ => FamAlongEq.refl _ _ _ _⟩

theorem SemTypeEq.el {Γ : Context} {a b : Expr} (hab : SemTermEq Γ a b .universe) :
    SemTypeEq Γ (.el a) (.el b) :=
  ⟨hab.ctx, SemTypeWf.el hab.wf_left, SemTypeWf.el hab.wf_right, rfl,
    fun _ => FamAtEq.refl _ _, fun _ => FamAlongEq.refl _ _ _ _⟩

theorem SemTypeEq.identity {Γ : Context} {A A' a a' b b' : Expr}
    (hA : SemTypeEq Γ A A') (ha : SemTermEq Γ a a' A) (hb : SemTermEq Γ b b' A) :
    SemTypeEq Γ (.identity A a b) (.identity A' a' b') := by
  refine SemTypeEq.of_left_hyps hA.ctx (SemTypeWf.identity hA.wf_left ha.wf_left hb.wf_left)
    ⟨⟨hA.wf_right.good.1, ha.wf_right.good.1, hb.wf_right.good.1⟩, trivial⟩
    hA.lvl_eq.symm
    (fun {γ x} hγ => ?_) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun {γ₁ γ₂ δ} hδ => ?_)
  · have hAt := (hA.at_eq hγ).symm
    dsimp only [evalTy, eval, semId]
    rw [← ha.obj_eq hγ, ← hb.obj_eq hγ]
    exact exists_congr (fun _ => and_congr_right (fun _ =>
      hAt.hom_id (ha.wf_left.at_obj hγ).obj (hb.wf_left.at_obj hγ).obj))
  · have hAt₁ := (hA.at_eq hδ.source).symm
    have hAt₂ := (hA.at_eq hδ.target).symm
    have hAl := (hA.along_eq hδ).symm (hA.at_eq hδ.source) (hA.at_eq hδ.target)
    have ha_al := ha.wf_left.along hδ
    have hb_al := hb.wf_left.along hδ
    have hav := (hA.wf_left.tr hδ).vertical ha_al
    have hbv := (hA.wf_left.tr hδ).vertical hb_al
    have h_re : ∀ p, FiberHom (evalTy A) γ₁ ((evalTm a).obj γ₁) ((evalTm b).obj γ₁) p →
        (evalTy A').comp γ₂ ((evalTy A').inv γ₂ ((evalTm a').mor γ₁ γ₂ δ))
          ((evalTy A').comp γ₂ ((evalTy A').reindexMor γ₁ γ₂ δ p) ((evalTm b').mor γ₁ γ₂ δ)) =
        (evalTy A).comp γ₂ ((evalTy A).inv γ₂ ((evalTm a).mor γ₁ γ₂ δ))
          ((evalTy A).comp γ₂ ((evalTy A).reindexMor γ₁ γ₂ δ p) ((evalTm b).mor γ₁ γ₂ δ)) := by
      intro p hpv
      have hp_tr := (hA.wf_left.tr hδ).map_hom hpv
      rw [← ha.mor_eq hδ, ← hb.mor_eq hδ, hAt₂.inv hav, hAl.reindexMor hpv, hAt₂.comp hp_tr hbv,
        hAt₂.comp ((hA.wf_left.fiber hδ.target).inv_hom hav)
          ((hA.wf_left.fiber hδ.target).comp_hom hp_tr hbv)]
    have h_unre : ∀ p', FiberHom (evalTy A) γ₂ ((evalTm a).obj γ₂) ((evalTm b).obj γ₂) p' →
        (evalTy A').unreindexMor γ₁ γ₂ δ
          ((evalTy A').comp γ₂ ((evalTm a').mor γ₁ γ₂ δ)
            ((evalTy A').comp γ₂ p' ((evalTy A').inv γ₂ ((evalTm b').mor γ₁ γ₂ δ)))) =
        (evalTy A).unreindexMor γ₁ γ₂ δ
          ((evalTy A).comp γ₂ ((evalTm a).mor γ₁ γ₂ δ)
            ((evalTy A).comp γ₂ p' ((evalTy A).inv γ₂ ((evalTm b).mor γ₁ γ₂ δ)))) := by
      intro p' hp'v
      have hbv_inv := (hA.wf_left.fiber hδ.target).inv_hom hbv
      have hp'_inv := (hA.wf_left.fiber hδ.target).comp_hom hp'v hbv_inv
      have hall := (hA.wf_left.fiber hδ.target).comp_hom hav hp'_inv
      rw [← ha.mor_eq hδ, ← hb.mor_eq hδ, hAt₂.inv hbv, hAt₂.comp hp'v hbv_inv,
        hAt₂.comp hav hp'_inv, hAl.unreindexMor hall]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro x y q ⟨p, rfl, hp⟩ _
      dsimp only [evalTy, eval, semId, unId]
      rw [h_re p ⟨ha_al.1, hb_al.1, hp⟩, ← ha.obj_eq hδ.source, ← hb.obj_eq hδ.source]
      exact and_congr_right (fun _ => and_congr_right (fun _ =>
        exists_congr (fun _ => and_congr_right (fun _ => hAt₁.hom_id ha_al.1 hb_al.1))))
    · rintro x ⟨p, rfl, hp⟩
      dsimp only [evalTy, eval, semId, unId]
      exact congrArg Tree.idObj (h_re p ⟨ha_al.1, hb_al.1, hp⟩)
    · intro x y q hq
      have hq' := (semId_fiber_hom_iff (hA.wf_left.fiber hδ.source) (hA.wf_left.id_tr hδ.source)
        (ha.wf_left.at_obj hδ.source) (hb.wf_left.at_obj hδ.source)).mp hq
      rcases hq'.1 with ⟨p, rfl, hp⟩
      rw [hq'.2.2]
      dsimp only [evalTy, eval, semId, unId]
      exact congrArg Tree.idObj (h_re p ⟨ha_al.1, hb_al.1, hp⟩)
    · rintro x' ⟨p', rfl, hp'⟩
      dsimp only [evalTy, eval, semId, unId]
      exact congrArg Tree.idObj (h_unre p' ⟨ha_al.2.1, hb_al.2.1, hp'⟩)
    · intro x' y' q' hq'
      have hq'' := (semId_fiber_hom_iff (hA.wf_left.fiber hδ.target) (hA.wf_left.id_tr hδ.target)
        (ha.wf_left.at_obj hδ.target) (hb.wf_left.at_obj hδ.target)).mp hq'
      rcases hq''.1 with ⟨p', rfl, hp'⟩
      rw [hq''.2.2]
      dsimp only [evalTy, eval, semId, unId]
      exact congrArg Tree.idObj (h_unre p' ⟨ha_al.2.1, hb_al.2.1, hp'⟩)

theorem SemTypeEq.cons_at {Γ : Context} {A B B' : Expr}
    (hB : SemTypeEq (A :: Γ) B B') {γ : Env} {x : Val}
    (hγ : CtxObj Γ γ) (hx : (evalTy A).Obj γ x) :
    FamAtEq (evalTy B') (evalTy B) (consEnv x γ) (consEnv x γ) :=
  (hB.at_eq (CtxObj.cons hγ hx)).symm

theorem SemTypeEq.cons_along {Γ : Context} {A B B' : Expr}
    (hB : SemTypeEq (A :: Γ) B B') {γ₁ γ₂ δ : Env} {x₁ x₂ p : Val}
    (hδ : CtxHom Γ γ₁ γ₂ δ) (hp : piHetMor (evalTy A) γ₁ γ₂ δ x₁ x₂ p) :
    FamAlongEq (evalTy B') (evalTy B)
      (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ)
      (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv p δ) :=
  (hB.along_eq (CtxHom.cons hδ hp)).symm
    (hB.at_eq (CtxObj.cons hδ.source hp.1)) (hB.at_eq (CtxObj.cons hδ.target hp.2.1))

theorem SemTypeEq.sigma {Γ : Context} {A A' B B' : Expr}
    (hA : SemTypeEq Γ A A') (hB : SemTypeEq (A :: Γ) B B') :
    SemTypeEq Γ (.sigma A B) (.sigma A' B') := by
  refine SemTypeEq.of_left_hyps hA.ctx (SemTypeWf.sigma hA.ctx hA.wf_left hB.wf_left)
    ⟨⟨hA.wf_right.good.1, hB.wf_right.good.1⟩, trivial⟩
    (by dsimp [evalTy, eval, semSigma]; rw [hA.lvl_eq, hB.lvl_eq])
    (fun {γ z} hγ => ?_) (fun {γ z₁ z₂ z₃ m₁ m₂} hγ hm₁ hm₂ => ?_)
    (fun {γ z₁ z₂ m} hγ hm => ?_) (fun {γ₁ γ₂ δ} hδ => ?_)
  · have hAt := (hA.at_eq hγ).symm
    dsimp only [evalTy, eval, semSigma]
    refine exists_congr (fun x => exists_congr (fun y => and_congr_right (fun _ => ?_)))
    exact ⟨fun ⟨hx', hy'⟩ =>
      have hx := hAt.obj.mp hx'
      ⟨hx, (hB.cons_at hγ hx).obj.mp hy'⟩,
      fun ⟨hx, hy⟩ => ⟨hAt.obj.mpr hx, (hB.cons_at hγ hx).obj.mpr hy⟩⟩
  · have hAt := (hA.at_eq hγ).symm
    rcases (semSigma_fiber_hom_iff (hA.wf_left.id_tr hγ)).mp hm₁ with
      ⟨x₁, y₁, x₂, y₂, p₁, q₁, rfl, rfl, rfl, hp₁, hq₁⟩
    rcases (semSigma_fiber_hom_iff (hA.wf_left.id_tr hγ)).mp hm₂ with
      ⟨x₂', y₂', x₃, y₃, p₂, q₂, hpair, rfl, rfl, hp₂, hq₂⟩
    cases hpair
    have hq₁v := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp₁)).vertical hq₁
    have hq₂v := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp₂)).vertical hq₂
    have hq₁_tr := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp₂)).map_hom hq₁v
    have hB_al₂ := hB.cons_along (hA.ctx.id_hom hγ) hp₂
    have hB_at₃ := hB.cons_at hγ hp₂.2.1
    dsimp only [evalTy, eval, semSigma, sigMorX1, sigMorX2, sigMorP, sigMorQ]
    rw [hAt.comp hp₁ hp₂, hB_al₂.reindexMor hq₁v, hB_at₃.comp hq₁_tr hq₂v]
  · have hAt := (hA.at_eq hγ).symm
    rcases (semSigma_fiber_hom_iff (hA.wf_left.id_tr hγ)).mp hm with
      ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
    have hpinv := (hA.wf_left.fiber hγ).inv_hom hp
    have hqv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)).vertical hq
    have hqinv := (hB.wf_left.fiber (CtxObj.cons hγ hp.2.1)).inv_hom hqv
    have hB_at₂ := hB.cons_at hγ hp.2.1
    have hB_al_inv := hB.cons_along (hA.ctx.id_hom hγ) hpinv
    dsimp only [evalTy, eval, semSigma, sigMorX1, sigMorX2, sigMorP, sigMorQ]
    rw [hAt.inv hp, hB_at₂.inv hqv, hB_al_inv.reindexMor hqinv]
  · have hAt₁ := (hA.at_eq hδ.source).symm
    have hAt₂ := (hA.at_eq hδ.target).symm
    have hAl := (hA.along_eq hδ).symm (hA.at_eq hδ.source) (hA.at_eq hδ.target)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro z₁ z₂ m ⟨x₁, y₁, rfl, hx₁, hy₁⟩ ⟨x₂, y₂, rfl, hx₂, hy₂⟩
      dsimp only [evalTy, eval, semSigma]
      constructor
      · rintro ⟨x₁a, y₁a, x₂a, y₂a, p, q, h₁, h₂, rfl, _, _, _, _, hp', hq'⟩
        cases h₁; cases h₂
        have hp := (hAl.hom hx₁ hx₂).mp hp'
        have hB_al := hB.cons_along hδ ⟨hx₁, hx₂, hp⟩
        rw [hAl.reindexObj hx₁]
        exact ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hx₁, hx₂, hy₁, hy₂, hp,
          (hB_al.hom hy₁ hy₂).mp hq'⟩
      · rintro ⟨x₁a, y₁a, x₂a, y₂a, p, q, h₁, h₂, rfl, _, _, _, _, hp, hq⟩
        cases h₁; cases h₂
        have hB_al := hB.cons_along hδ ⟨hx₁, hx₂, hp⟩
        rw [← hAl.reindexObj hx₁]
        exact ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl,
          hAt₁.obj.mpr hx₁, hAt₂.obj.mpr hx₂,
          (hB.cons_at hδ.source hx₁).obj.mpr hy₁,
          (hB.cons_at hδ.target hx₂).obj.mpr hy₂,
          (hAl.hom hx₁ hx₂).mpr hp, (hB_al.hom hy₁ hy₂).mpr hq⟩
    · rintro z ⟨x, y, rfl, hx, hy⟩
      have hx' := (hA.wf_left.tr hδ).map_obj hx
      have h_id : piHetMor (evalTy A) γ₁ γ₂ δ x ((evalTy A).reindexObj γ₁ γ₂ δ x)
          (idVal ((evalTy A).reindexObj γ₁ γ₂ δ x)) :=
        ⟨hx, hx', ((hA.wf_left.tr hδ).hom_iff hx hx').mpr
          ((hA.wf_left.fiber hδ.target).id_hom hx').2.2⟩
      have hB_al := hB.cons_along hδ h_id
      dsimp only [evalTy, eval, semSigma, sigFst, sigSnd]
      rw [hAl.reindexObj hx, hB_al.reindexObj hy]
    · intro z₁ z₂ m hm
      rcases (semSigma_fiber_hom_iff (hA.wf_left.id_tr hδ.source)).mp hm with
        ⟨x₁, y₁, x₂, y₂, p, q, rfl, rfl, rfl, hp, hq⟩
      have hx₂' := (hA.wf_left.tr hδ).map_obj hp.2.1
      have h_id₂ : piHetMor (evalTy A) γ₁ γ₂ δ x₂ ((evalTy A).reindexObj γ₁ γ₂ δ x₂)
          (idVal ((evalTy A).reindexObj γ₁ γ₂ δ x₂)) :=
        ⟨hp.2.1, hx₂', ((hA.wf_left.tr hδ).hom_iff hp.2.1 hx₂').mpr
          ((hA.wf_left.fiber hδ.target).id_hom hx₂').2.2⟩
      have hqv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hδ.source) hp)).vertical hq
      have hB_al := hB.cons_along hδ h_id₂
      dsimp only [evalTy, eval, semSigma, sigMorX1, sigMorX2, sigMorP, sigMorQ]
      rw [hAl.reindexObj hp.1, hAl.reindexObj hp.2.1, hAl.reindexMor hp, hB_al.reindexMor hqv]
    · rintro z' ⟨x', y', rfl, hx', hy'⟩
      have hx := (hA.wf_left.tr hδ).unmap_obj hx'
      have h_id : piHetMor (evalTy A) γ₁ γ₂ δ ((evalTy A).unreindexObj γ₁ γ₂ δ x') x' (idVal x') := by
        refine ⟨hx, hx', ((hA.wf_left.tr hδ).hom_iff hx hx').mpr ?_⟩
        rw [(hA.wf_left.tr hδ).map_unmap_obj hx']
        exact ((hA.wf_left.fiber hδ.target).id_hom hx').2.2
      have hB_al := hB.cons_along hδ h_id
      dsimp only [evalTy, eval, semSigma, sigFst, sigSnd]
      rw [hAl.unreindexObj hx', hB_al.unreindexObj hy']
    · intro z₁' z₂' m' hm'
      rcases (semSigma_fiber_hom_iff (hA.wf_left.id_tr hδ.target)).mp hm' with
        ⟨x₁', y₁', x₂', y₂', p', q', rfl, rfl, rfl, hp', hq'⟩
      have hx₂ := (hA.wf_left.tr hδ).unmap_obj hp'.2.1
      have h_id₂ : piHetMor (evalTy A) γ₁ γ₂ δ ((evalTy A).unreindexObj γ₁ γ₂ δ x₂') x₂' (idVal x₂') := by
        refine ⟨hx₂, hp'.2.1, ((hA.wf_left.tr hδ).hom_iff hx₂ hp'.2.1).mpr ?_⟩
        rw [(hA.wf_left.tr hδ).map_unmap_obj hp'.2.1]
        exact ((hA.wf_left.fiber hδ.target).id_hom hp'.2.1).2.2
      have hq'v := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hδ.target) hp')).vertical hq'
      have hB_al := hB.cons_along hδ h_id₂
      dsimp only [evalTy, eval, semSigma, sigMorX1, sigMorX2, sigMorP, sigMorQ]
      rw [hAl.unreindexObj hp'.1, hAl.unreindexObj hp'.2.1, hAl.unreindexMor hp',
        hB_al.unreindexMor hq'v]

theorem SemTypeEq.piHetMor_iff {Γ : Context} {A A' : Expr} (hA : SemTypeEq Γ A A')
    {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ) (x y p : Val) :
    piHetMor (evalTy A') γ₁ γ₂ δ x y p ↔ piHetMor (evalTy A) γ₁ γ₂ δ x y p := by
  have hAt₁ := (hA.at_eq hδ.source).symm
  have hAt₂ := (hA.at_eq hδ.target).symm
  have hAl := (hA.along_eq hδ).symm (hA.at_eq hδ.source) (hA.at_eq hδ.target)
  exact ⟨fun ⟨hx', hy', hp'⟩ =>
    have hx := hAt₁.obj.mp hx'; have hy := hAt₂.obj.mp hy'
    ⟨hx, hy, (hAl.hom hx hy).mp hp'⟩,
    fun ⟨hx, hy, hp⟩ => ⟨hAt₁.obj.mpr hx, hAt₂.obj.mpr hy, (hAl.hom hx hy).mpr hp⟩⟩

theorem SemTypeEq.piDomMor_iff {Γ : Context} {A A' : Expr} (hA : SemTypeEq Γ A A')
    {γ : Env} (hγ : CtxObj Γ γ) (x y p : Val) :
    piDomMor (evalTy A') γ x y p ↔ piDomMor (evalTy A) γ x y p :=
  hA.piHetMor_iff (hA.ctx.id_hom hγ) x y p

theorem SemTypeEq.piHom_iff {Γ : Context} {A A' B B' : Expr}
    (hA : SemTypeEq Γ A A') (hB : SemTypeEq (A :: Γ) B B')
    {γ : Env} (hγ : CtxObj Γ γ) {f g η : Val}
    (hf : (evalTy (.pi A B)).Obj γ f) (hg : (evalTy (.pi A B)).Obj γ g) :
    PiHom (evalTy A') (evalTy B') γ f g η ↔ PiHom (evalTy A) (evalTy B) γ f g η := by
  have hAt := (hA.at_eq hγ).symm
  have hAl := (hA.along_eq (hA.ctx.id_hom hγ)).symm (hA.at_eq hγ) (hA.at_eq hγ)
  have hmk : mkPiMor (evalTy A').lvl (piDomMor (evalTy A') γ) (piMorAt η) =
      mkPiMor (evalTy A).lvl (piDomMor (evalTy A) γ) (piMorAt η) := by
    rw [← hA.lvl_eq]
    exact mkPiMor_ext (hA.piDomMor_iff hγ) (fun _ _ _ _ => rfl)
  have hhom : (∀ x y p, piDomMor (evalTy A') γ x y p →
      (evalTy B').Hom (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
        (piAppObj f x) (piAppObj g y) (piMorAt η x y p)) ↔
      (∀ x y p, piDomMor (evalTy A) γ x y p →
      (evalTy B).Hom (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
        (piAppObj f x) (piAppObj g y) (piMorAt η x y p)) :=
    ⟨fun h x y p hp =>
      ((hB.cons_along (hA.ctx.id_hom hγ) hp).hom (hf.2.1 x hp.1) (hg.2.1 y hp.2.1)).mp
        (h x y p ((hA.piDomMor_iff hγ x y p).mpr hp)),
     fun h x y p hp' =>
      have hp := (hA.piDomMor_iff hγ x y p).mp hp'
      ((hB.cons_along (hA.ctx.id_hom hγ) hp).hom (hf.2.1 x hp.1) (hg.2.1 y hp.2.1)).mpr
        (h x y p hp)⟩
  refine ⟨fun ⟨h1, h2', h3', h4'⟩ => ?_, fun ⟨h1, h2, h3, h4⟩ => ?_⟩
  · have h2 := hhom.mp h2'
    refine ⟨h1.trans hmk, h2, fun w x y u p hu hp => ?_, fun x y z p v hp hv => ?_⟩
    · have h_lhs := h3' w x y u p ((hA.piDomMor_iff hγ w x u).mpr hu)
        ((hA.piDomMor_iff hγ x y p).mpr hp)
      have huv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hu)).vertical
        ⟨hf.2.1 w hu.1, hf.2.1 x hu.2.1, hf.2.2.1 w x u hu⟩
      have hu_btr := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)).map_hom huv
      have hpv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)).vertical
        ⟨hf.2.1 x hp.1, hg.2.1 y hp.2.1, h2 x y p hp⟩
      rw [hAl.reindexMor hu, (hA.wf_left.id_tr hγ).mor hu, hAt.comp hu hp,
        (hB.cons_along (hA.ctx.id_hom hγ) hp).reindexMor huv,
        (hB.cons_at hγ hp.2.1).comp hu_btr hpv] at h_lhs
      rw [(hA.wf_left.id_tr hγ).mor hu]
      exact h_lhs
    · have h_lhs := h4' x y z p v ((hA.piDomMor_iff hγ x y p).mpr hp)
        ((hA.piDomMor_iff hγ y z v).mpr hv)
      have hpv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)).vertical
        ⟨hf.2.1 x hp.1, hg.2.1 y hp.2.1, h2 x y p hp⟩
      have hp_btr := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hv)).map_hom hpv
      have hvv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hv)).vertical
        ⟨hg.2.1 y hv.1, hg.2.1 z hv.2.1, hg.2.2.1 y z v hv⟩
      rw [hAt.comp hp hv, (hB.cons_along (hA.ctx.id_hom hγ) hv).reindexMor hpv,
        (hB.cons_at hγ hv.2.1).comp hp_btr hvv] at h_lhs
      exact h_lhs
  · refine ⟨h1.trans hmk.symm, hhom.mpr h2, fun w x y u p hu' hp' => ?_, fun x y z p v hp' hv' => ?_⟩
    · have hu := (hA.piDomMor_iff hγ w x u).mp hu'
      have hp := (hA.piDomMor_iff hγ x y p).mp hp'
      have huv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hu)).vertical
        ⟨hf.2.1 w hu.1, hf.2.1 x hu.2.1, hf.2.2.1 w x u hu⟩
      have hu_btr := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)).map_hom huv
      have hpv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)).vertical
        ⟨hf.2.1 x hp.1, hg.2.1 y hp.2.1, h2 x y p hp⟩
      rw [hAl.reindexMor hu, (hA.wf_left.id_tr hγ).mor hu, hAt.comp hu hp,
        (hB.cons_along (hA.ctx.id_hom hγ) hp).reindexMor huv,
        (hB.cons_at hγ hp.2.1).comp hu_btr hpv]
      have h_rhs := h3 w x y u p hu hp
      rw [(hA.wf_left.id_tr hγ).mor hu] at h_rhs
      exact h_rhs
    · have hp := (hA.piDomMor_iff hγ x y p).mp hp'
      have hv := (hA.piDomMor_iff hγ y z v).mp hv'
      have hpv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)).vertical
        ⟨hf.2.1 x hp.1, hg.2.1 y hp.2.1, h2 x y p hp⟩
      have hp_btr := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hv)).map_hom hpv
      have hvv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hv)).vertical
        ⟨hg.2.1 y hv.1, hg.2.1 z hv.2.1, hg.2.2.1 y z v hv⟩
      rw [hAt.comp hp hv, (hB.cons_along (hA.ctx.id_hom hγ) hv).reindexMor hpv,
        (hB.cons_at hγ hv.2.1).comp hp_btr hvv]
      exact h4 x y z p v hp hv

theorem SemTypeEq.pi {Γ : Context} {A A' B B' : Expr}
    (hA : SemTypeEq Γ A A') (hB : SemTypeEq (A :: Γ) B B') :
    SemTypeEq Γ (.pi A B) (.pi A' B') := by
  have hPiWf := SemTypeWf.pi hA.ctx hA.wf_left hB.wf_left
  refine SemTypeEq.of_left_hyps hA.ctx hPiWf
    ⟨⟨hA.wf_right.good.1, hB.wf_right.good.1⟩, trivial⟩
    (by dsimp [evalTy, eval, semPi]; rw [hA.lvl_eq, hB.lvl_eq])
    (fun {γ f} hγ => ?_) (fun {γ f g h η₁ η₂} hγ hη₁ hη₂ => ?_)
    (fun {γ f g η} hγ hη => ?_) (fun {γ₁ γ₂ δ} hδ => ?_)
  · have hAt := (hA.at_eq hγ).symm
    have hmk : mkPiObj (evalTy A').lvl ((evalTy A').Obj γ) (piDomMor (evalTy A') γ) (piAppObj f) (piAppMor f) =
        mkPiObj (evalTy A).lvl ((evalTy A).Obj γ) (piDomMor (evalTy A) γ) (piAppObj f) (piAppMor f) := by
      rw [← hA.lvl_eq]
      exact mkPiObj_ext (fun _ => hAt.obj) (hA.piDomMor_iff hγ) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    refine ⟨fun ⟨h1', h2', h3', h4', h5'⟩ => ?_, fun ⟨h1, h2, h3, h4, h5⟩ => ?_⟩
    · have h2 : ∀ x, (evalTy A).Obj γ x → (evalTy B).Obj (consEnv x γ) (piAppObj f x) :=
        fun x hx => (hB.cons_at hγ hx).obj.mp (h2' x (hAt.obj.mpr hx))
      have h3 : ∀ x y p, piDomMor (evalTy A) γ x y p →
          (evalTy B).Hom (consEnv x γ) (consEnv y γ) (consEnv p (idEnv γ))
            (piAppObj f x) (piAppObj f y) (piAppMor f x y p) :=
        fun x y p hp => ((hB.cons_along (hA.ctx.id_hom hγ) hp).hom (h2 x hp.1) (h2 y hp.2.1)).mp
          (h3' x y p ((hA.piDomMor_iff hγ x y p).mpr hp))
      refine ⟨h1'.trans hmk, h2, h3, fun x hx => h4' x (hAt.obj.mpr hx), fun x y z p q hp hq => ?_⟩
      have h_lhs := h5' x y z p q ((hA.piDomMor_iff hγ x y p).mpr hp) ((hA.piDomMor_iff hγ y z q).mpr hq)
      have hpv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)).vertical ⟨h2 x hp.1, h2 y hp.2.1, h3 x y p hp⟩
      have hp_tr := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hq)).map_hom hpv
      have hqv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hq)).vertical ⟨h2 y hq.1, h2 z hq.2.1, h3 y z q hq⟩
      rw [hAt.comp hp hq, (hB.cons_along (hA.ctx.id_hom hγ) hq).reindexMor hpv,
        (hB.cons_at hγ hq.2.1).comp hp_tr hqv] at h_lhs
      exact h_lhs
    · refine ⟨h1.trans hmk.symm,
        fun x hx' => (hB.cons_at hγ (hAt.obj.mp hx')).obj.mpr (h2 x (hAt.obj.mp hx')),
        fun x y p hp' =>
          have hp := (hA.piDomMor_iff hγ x y p).mp hp'
          ((hB.cons_along (hA.ctx.id_hom hγ) hp).hom (h2 x hp.1) (h2 y hp.2.1)).mpr (h3 x y p hp),
        fun x hx' => h4 x (hAt.obj.mp hx'),
        fun x y z p q hp' hq' => ?_⟩
      have hp := (hA.piDomMor_iff hγ x y p).mp hp'
      have hq := (hA.piDomMor_iff hγ y z q).mp hq'
      have hpv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)).vertical ⟨h2 x hp.1, h2 y hp.2.1, h3 x y p hp⟩
      have hp_tr := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hq)).map_hom hpv
      have hqv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hq)).vertical ⟨h2 y hq.1, h2 z hq.2.1, h3 y z q hq⟩
      rw [hAt.comp hp hq, (hB.cons_along (hA.ctx.id_hom hγ) hq).reindexMor hpv,
        (hB.cons_at hγ hq.2.1).comp hp_tr hqv]
      exact h5 x y z p q hp hq
  · have hh₁ := (semPi_hom_iff (hA.wf_left.id_tr hγ) (hA.wf_left.tr (hA.ctx.id_hom hγ))
      (fun x hx => hB.wf_left.id_tr (CtxObj.cons hγ hx))
      (fun x y p hp => hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)) hη₁.1).mp hη₁.2.2
    have hh₂ := (semPi_hom_iff (hA.wf_left.id_tr hγ) (hA.wf_left.tr (hA.ctx.id_hom hγ))
      (fun x hx => hB.wf_left.id_tr (CtxObj.cons hγ hx))
      (fun x y p hp => hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)) hη₂.1).mp hη₂.2.2
    dsimp only [evalTy, eval, semPi]
    rw [← hA.lvl_eq]
    refine mkPiMor_ext (hA.piDomMor_iff hγ) (fun x y p hp' => ?_)
    have hp := (hA.piDomMor_iff hγ x y p).mp hp'
    have hidx := (hA.wf_left.fiber hγ).id_hom hp.1
    have hη₁v := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hidx)).vertical
      ⟨hη₁.1.2.1 x hp.1, hη₁.2.1.2.1 x hp.1, hh₁.2.1 x x (idVal x) hidx⟩
    have hη₁_tr := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)).map_hom hη₁v
    have hη₂v := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)).vertical
      ⟨hη₂.1.2.1 x hp.1, hη₂.2.1.2.1 y hp.2.1, hh₂.2.1 x y p hp⟩
    rw [(hB.cons_along (hA.ctx.id_hom hγ) hp).reindexMor hη₁v,
      (hB.cons_at hγ hp.2.1).comp hη₁_tr hη₂v]
  · have hAt := (hA.at_eq hγ).symm
    have hh := (semPi_hom_iff (hA.wf_left.id_tr hγ) (hA.wf_left.tr (hA.ctx.id_hom hγ))
      (fun x hx => hB.wf_left.id_tr (CtxObj.cons hγ hx))
      (fun x y p hp => hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hp)) hη.1).mp hη.2.2
    dsimp only [evalTy, eval, semPi]
    rw [← hA.lvl_eq]
    refine mkPiMor_ext (hA.piDomMor_iff hγ) (fun x y p hp' => ?_)
    have hp := (hA.piDomMor_iff hγ x y p).mp hp'
    have hpinv := (hA.wf_left.fiber hγ).inv_hom hp
    have hηv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hγ) hpinv)).vertical
      ⟨hη.1.2.1 y hp.2.1, hη.2.1.2.1 x hp.1, hh.2.1 y x _ hpinv⟩
    have hη_inv := (hB.wf_left.fiber (CtxObj.cons hγ hp.1)).inv_hom hηv
    rw [hAt.inv hp, (hB.cons_at hγ hp.1).inv hηv,
      (hB.cons_along (hA.ctx.id_hom hγ) hp).reindexMor hη_inv]
  · have hAt₁ := (hA.at_eq hδ.source).symm
    have hAt₂ := (hA.at_eq hδ.target).symm
    have hAl := (hA.along_eq hδ).symm (hA.at_eq hδ.source) (hA.at_eq hδ.target)
    have h_unmap_id : ∀ {x'}, (evalTy A).Obj γ₂ x' →
        piHetMor (evalTy A) γ₁ γ₂ δ ((evalTy A).unreindexObj γ₁ γ₂ δ x') x' (idVal x') := by
      intro x' hx'
      have hx := (hA.wf_left.tr hδ).unmap_obj hx'
      refine ⟨hx, hx', ((hA.wf_left.tr hδ).hom_iff hx hx').mpr ?_⟩
      rw [(hA.wf_left.tr hδ).map_unmap_obj hx']
      exact ((hA.wf_left.fiber hδ.target).id_hom hx').2.2
    have h_map_id : ∀ {x}, (evalTy A).Obj γ₁ x →
        piHetMor (evalTy A) γ₁ γ₂ δ x ((evalTy A).reindexObj γ₁ γ₂ δ x)
          (idVal ((evalTy A).reindexObj γ₁ γ₂ δ x)) := by
      intro x hx
      have hx' := (hA.wf_left.tr hδ).map_obj hx
      exact ⟨hx, hx', ((hA.wf_left.tr hδ).hom_iff hx hx').mpr
        ((hA.wf_left.fiber hδ.target).id_hom hx').2.2⟩
    have h_ro : ∀ {f}, (evalTy (.pi A B)).Obj γ₁ f →
        (evalTy (.pi A' B')).reindexObj γ₁ γ₂ δ f = (evalTy (.pi A B)).reindexObj γ₁ γ₂ δ f := by
      intro f hf
      dsimp only [evalTy, eval, semPi]
      rw [← hA.lvl_eq]
      refine mkPiObj_ext (fun _ => hAt₂.obj) (hA.piDomMor_iff hδ.target)
        (fun x' hx'' => ?_) (fun x' y' p' hp'' => ?_)
      · have hx' := hAt₂.obj.mp hx''
        have hx := (hA.wf_left.tr hδ).unmap_obj hx'
        rw [hAl.unreindexObj hx', (hB.cons_along hδ (h_unmap_id hx')).reindexObj (hf.2.1 _ hx)]
      · have hp' := (hA.piDomMor_iff hδ.target x' y' p').mp hp''
        have hp := (hA.wf_left.tr hδ).unmap_hom hp'
        have hfv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hδ.source) hp)).vertical
          ⟨hf.2.1 _ hp.1, hf.2.1 _ hp.2.1, hf.2.2.1 _ _ _ hp⟩
        rw [hAl.unreindexObj hp'.1, hAl.unreindexObj hp'.2.1, hAl.unreindexMor hp',
          (hB.cons_along hδ (h_unmap_id hp'.2.1)).reindexMor hfv]
    refine ⟨?_, h_ro, ?_, ?_, ?_⟩
    · intro f g η hf hg
      dsimp only [evalTy, eval, semPi]
      change PiHom (evalTy A') (evalTy B') γ₂ ((evalTy (.pi A' B')).reindexObj γ₁ γ₂ δ f) g η ↔
        PiHom (evalTy A) (evalTy B) γ₂ ((evalTy (.pi A B)).reindexObj γ₁ γ₂ δ f) g η
      rw [h_ro hf]
      exact hA.piHom_iff hB hδ.target ((hPiWf.tr hδ).map_obj hf) hg
    · intro f g η hη
      have hh := (semPi_hom_iff (hA.wf_left.id_tr hδ.source) (hA.wf_left.tr (hA.ctx.id_hom hδ.source))
        (fun x hx => hB.wf_left.id_tr (CtxObj.cons hδ.source hx))
        (fun x y p hp => hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hδ.source) hp)) hη.1).mp hη.2.2
      dsimp only [evalTy, eval, semPi]
      rw [← hA.lvl_eq]
      refine mkPiMor_ext (hA.piDomMor_iff hδ.target) (fun x' y' p' hp'' => ?_)
      have hp' := (hA.piDomMor_iff hδ.target x' y' p').mp hp''
      have hp := (hA.wf_left.tr hδ).unmap_hom hp'
      have hηv := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hδ.source) hp)).vertical
        ⟨hη.1.2.1 _ hp.1, hη.2.1.2.1 _ hp.2.1, hh.2.1 _ _ _ hp⟩
      rw [hAl.unreindexObj hp'.1, hAl.unreindexObj hp'.2.1, hAl.unreindexMor hp',
        (hB.cons_along hδ (h_unmap_id hp'.2.1)).reindexMor hηv]
    · intro f' hf'
      dsimp only [evalTy, eval, semPi]
      rw [← hA.lvl_eq]
      refine mkPiObj_ext (fun _ => hAt₁.obj) (hA.piDomMor_iff hδ.source)
        (fun x hx' => ?_) (fun x y p hp' => ?_)
      · have hx := hAt₁.obj.mp hx'
        have hx₂ := (hA.wf_left.tr hδ).map_obj hx
        rw [hAl.reindexObj hx, (hB.cons_along hδ (h_map_id hx)).unreindexObj (hf'.2.1 _ hx₂)]
      · have hp := (hA.piDomMor_iff hδ.source x y p).mp hp'
        have hp₂ := (hA.wf_left.tr hδ).map_hom hp
        have hf'v := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hδ.target) hp₂)).vertical
          ⟨hf'.2.1 _ hp₂.1, hf'.2.1 _ hp₂.2.1, hf'.2.2.1 _ _ _ hp₂⟩
        rw [hAl.reindexObj hp.1, hAl.reindexObj hp.2.1, hAl.reindexMor hp,
          (hB.cons_along hδ (h_map_id hp.2.1)).unreindexMor hf'v]
    · intro f' g' η' hη'
      have hh' := (semPi_hom_iff (hA.wf_left.id_tr hδ.target) (hA.wf_left.tr (hA.ctx.id_hom hδ.target))
        (fun x hx => hB.wf_left.id_tr (CtxObj.cons hδ.target hx))
        (fun x y p hp => hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hδ.target) hp)) hη'.1).mp hη'.2.2
      dsimp only [evalTy, eval, semPi]
      rw [← hA.lvl_eq]
      refine mkPiMor_ext (hA.piDomMor_iff hδ.source) (fun x y p hp' => ?_)
      have hp := (hA.piDomMor_iff hδ.source x y p).mp hp'
      have hp₂ := (hA.wf_left.tr hδ).map_hom hp
      have hη'v := (hB.wf_left.tr (CtxHom.cons (hA.ctx.id_hom hδ.target) hp₂)).vertical
        ⟨hη'.1.2.1 _ hp₂.1, hη'.2.1.2.1 _ hp₂.2.1, hh'.2.1 _ _ _ hp₂⟩
      rw [hAl.reindexObj hp.1, hAl.reindexObj hp.2.1, hAl.reindexMor hp,
        (hB.cons_along hδ (h_map_id hp.2.1)).unreindexMor hη'v]

end HofmannStreicher1994.Repaired

/-! ## SemTermWf1.lean -/

namespace HofmannStreicher1994.Repaired

theorem SemTermWf.mk_of {Γ : Context} {t A : Expr}
    (good : GoodTerm Γ.length t)
    (obj : ∀ {γ}, CtxObj Γ γ → (evalTy A).Obj γ ((evalTm t).obj γ))
    (id_mor : ∀ {γ}, CtxObj Γ γ → (evalTm t).mor γ γ (idEnv γ) = idVal ((evalTm t).obj γ))
    (hom : ∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ →
      (evalTy A).Hom γ₁ γ₂ δ ((evalTm t).obj γ₁) ((evalTm t).obj γ₂) ((evalTm t).mor γ₁ γ₂ δ))
    (comp_mor : ∀ {γ₁ γ₂ γ₃ δ₁₂ δ₂₃}, CtxHom Γ γ₁ γ₂ δ₁₂ → CtxHom Γ γ₂ γ₃ δ₂₃ →
      (evalTm t).mor γ₁ γ₃ (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃) =
        (evalTy A).comp γ₃
          ((evalTy A).reindexMor γ₂ γ₃ δ₂₃ ((evalTm t).mor γ₁ γ₂ δ₁₂))
          ((evalTm t).mor γ₂ γ₃ δ₂₃)) :
    SemTermWf Γ t A where
  good := good
  at_obj hγ := ⟨obj hγ, id_mor hγ⟩
  along hδ := ⟨obj hδ.source, obj hδ.target, hom hδ⟩
  comp_mor := comp_mor

theorem SemTermWf.vertical {Γ : Context} {t A : Expr} (hA : SemTypeWf Γ A) (ht : SemTermWf Γ t A)
    {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ) :
    FiberHom (evalTy A) γ₂
      ((evalTy A).reindexObj γ₁ γ₂ δ ((evalTm t).obj γ₁))
      ((evalTm t).obj γ₂)
      ((evalTm t).mor γ₁ γ₂ δ) :=
  (hA.tr hδ).vertical (ht.along hδ)

theorem SemTermWf.var {Γ : Context} {n : Nat} {A : Expr}
    (_hΓ : SemCtxWf Γ) (hget : Γ[n]? = some A) :
    SemTermWf Γ (.var n) (rename (fun k => k + n + 1) A) :=
  have ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hget
  SemTermWf.mk_of ⟨hlt, trivial⟩
    (fun hγ => by rw [evalTy_rename]; exact CtxObj_iff_getElem?.mp hγ n A hget)
    (fun _ => rfl)
    (fun hδ => by rw [evalTy_rename]; exact ((CtxHom_iff_getElem?.mp hδ).2 n A hget).2.2)
    (fun _ _ => by rw [evalTy_rename]; exact compCtx_getElem? hget)

theorem SemTermWf.zero {Γ : Context} (_hΓ : SemCtxWf Γ) :
    SemTermWf Γ .zero .nat :=
  SemTermWf.mk_of ⟨trivial, trivial⟩
    (fun _ => ⟨0, rfl⟩)
    (fun _ => rfl)
    (fun _ => ⟨0, rfl, rfl, rfl⟩)
    (fun _ _ => rfl)

theorem SemTermWf.succ {Γ : Context} {n : Expr} (hn : SemTermWf Γ n .nat) :
    SemTermWf Γ (.succ n) .nat :=
  SemTermWf.mk_of ⟨hn.good.1, trivial⟩
    (fun _ => ⟨_, rfl⟩)
    (fun _ => rfl)
    (fun hδ => by
      rcases (hn.along hδ).2.2 with ⟨k, h1, h2, _⟩
      exact ⟨k + 1, by simp [evalTm, eval, h1, h2, unNat]⟩)
    (fun _ h₂₃ => by
      rcases (hn.along h₂₃).2.2 with ⟨k, h2, h3, _⟩
      dsimp only [evalTm, eval, evalTy, semNat]
      rw [h2, h3])

theorem SemTermWf.refl {Γ : Context} {A a : Expr}
    (_hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (ha : SemTermWf Γ a A) :
    SemTermWf Γ (.refl A a) (.identity A a a) := by
  refine SemTermWf.mk_of ⟨⟨hA.good.1, ha.good.1⟩, trivial⟩
    (fun {γ} hγ => ⟨idVal ((evalTm a).obj γ), rfl, ((hA.fiber hγ).id_hom (ha.at_obj hγ).obj).2.2⟩)
    (fun _ => rfl)
    (fun {γ₁ γ₂ δ} hδ => ?_)
    (fun {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} _ h₂₃ => ?_)
  · have ha₁ := (ha.at_obj hδ.source).obj
    have hav := ha.vertical hA hδ
    dsimp only [evalTy, evalTm, eval, semId, unId]
    rw [(hA.tr hδ).map_id ha₁, (hA.fiber hδ.target).id_comp hav, (hA.fiber hδ.target).inv_comp hav]
    exact ⟨rfl, rfl, idVal ((evalTm a).obj γ₁), rfl, ((hA.fiber hδ.source).id_hom ha₁).2.2⟩
  · have ha₂ := (ha.at_obj h₂₃.source).obj
    have hav₂₃ := ha.vertical hA h₂₃
    dsimp only [evalTy, evalTm, eval, semId, unId]
    rw [(hA.tr h₂₃).map_id ha₂, (hA.fiber h₂₃.target).id_comp hav₂₃, (hA.fiber h₂₃.target).inv_comp hav₂₃]

theorem SemTermWf.pair {Γ : Context} {A B a b : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B)
    (ha : SemTermWf Γ a A) (hb : SemTermWf Γ b (instantiate B a)) :
    SemTermWf Γ (.pair A B a b) (.sigma A B) := by
  have hb_at : ∀ {γ} (hγ : CtxObj Γ γ),
      FamAtEq (evalTy (instantiate B a)) (evalTy B) γ (consEnv ((evalTm a).obj γ) γ) :=
    fun hγ => instantiate_atEq B ha hγ
  have hb_al : ∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ →
      FamAlongEq (evalTy (instantiate B a)) (evalTy B) γ₁ γ₂ δ
        (consEnv ((evalTm a).obj γ₁) γ₁) (consEnv ((evalTm a).obj γ₂) γ₂)
        (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ) :=
    fun hδ => instantiate_alongEq B ha hδ
  have hb_obj : ∀ {γ} (hγ : CtxObj Γ γ),
      (evalTy B).Obj (consEnv ((evalTm a).obj γ) γ) ((evalTm b).obj γ) :=
    fun hγ => (hb_at hγ).obj.mp (hb.at_obj hγ).obj
  have hb_hom : ∀ {γ₁ γ₂ δ} (hδ : CtxHom Γ γ₁ γ₂ δ),
      (evalTy B).Hom (consEnv ((evalTm a).obj γ₁) γ₁) (consEnv ((evalTm a).obj γ₂) γ₂)
        (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ) ((evalTm b).obj γ₁) ((evalTm b).obj γ₂)
        ((evalTm b).mor γ₁ γ₂ δ) :=
    fun hδ => ((hb_al hδ).hom (hb_obj hδ.source) (hb_obj hδ.target)).mp (hb.along hδ).2.2
  refine SemTermWf.mk_of ⟨⟨hA.good.1, hB.good.1, ha.good.1, hb.good.1⟩, trivial⟩
    (fun {γ} hγ => ⟨(evalTm a).obj γ, (evalTm b).obj γ, rfl, (ha.at_obj hγ).obj, hb_obj hγ⟩)
    (fun {γ} hγ => by
      dsimp only [evalTm, eval, idVal]
      rw [(hA.id_tr hγ).obj (ha.at_obj hγ).obj, (ha.at_obj hγ).id, (hb.at_obj hγ).id])
    (fun hδ => ⟨(evalTm a).obj _, (evalTm b).obj _, (evalTm a).obj _, (evalTm b).obj _,
      (evalTm a).mor _ _ _, (evalTm b).mor _ _ _, rfl, rfl, rfl,
      (ha.at_obj hδ.source).obj, (ha.at_obj hδ.target).obj,
      hb_obj hδ.source, hb_obj hδ.target, (ha.along hδ).2.2, hb_hom hδ⟩)
    (fun {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} h₁₂ h₂₃ => ?_)
  have hbv₁₂_B : FiberHom (evalTy B) (consEnv ((evalTm a).obj γ₂) γ₂)
      ((evalTy B).reindexObj (consEnv ((evalTm a).obj γ₁) γ₁)
        (consEnv ((evalTm a).obj γ₂) γ₂) (consEnv ((evalTm a).mor γ₁ γ₂ δ₁₂) δ₁₂)
        ((evalTm b).obj γ₁))
      ((evalTm b).obj γ₂) ((evalTm b).mor γ₁ γ₂ δ₁₂) :=
    (hB.tr (CtxHom.cons h₁₂ (ha.along h₁₂))).vertical ⟨hb_obj h₁₂.source, hb_obj h₁₂.target, hb_hom h₁₂⟩
  have hbv₁₂_B_tr := (hB.tr (CtxHom.cons h₂₃ (ha.along h₂₃))).map_hom hbv₁₂_B
  have hbv₂₃_B : FiberHom (evalTy B) (consEnv ((evalTm a).obj γ₃) γ₃)
      ((evalTy B).reindexObj (consEnv ((evalTm a).obj γ₂) γ₂)
        (consEnv ((evalTm a).obj γ₃) γ₃) (consEnv ((evalTm a).mor γ₂ γ₃ δ₂₃) δ₂₃)
        ((evalTm b).obj γ₂))
      ((evalTm b).obj γ₃) ((evalTm b).mor γ₂ γ₃ δ₂₃) :=
    (hB.tr (CtxHom.cons h₂₃ (ha.along h₂₃))).vertical ⟨hb_obj h₂₃.source, hb_obj h₂₃.target, hb_hom h₂₃⟩
  dsimp only [evalTm, eval, evalTy, semSigma, sigMorX1, sigMorX2, sigMorP, sigMorQ]
  rw [ha.comp_mor h₁₂ h₂₃, ← (hA.comp_tr h₁₂ h₂₃).comp_obj (ha.at_obj h₁₂.source).obj,
    hb.comp_mor h₁₂ h₂₃, (hb_al h₂₃).reindexMor hbv₁₂_B,
    (hb_at h₂₃.target).comp hbv₁₂_B_tr hbv₂₃_B,
    (SemTypeWf.ctB_right hΓ hA hB h₂₃ (ha.along h₂₃)).comp_mor hbv₁₂_B]

theorem SemTermWf.sigmaRec {Γ : Context} {A B C d p : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B)
    (hC : SemTypeWf (.sigma A B :: Γ) C)
    (hd : SemTermWf (B :: A :: Γ) d (pairingMotive A B C))
    (hp : SemTermWf Γ p (.sigma A B)) :
    SemTermWf Γ (.sigmaRec A B C d p) (instantiate C p) := by
  have hC_at : ∀ {γ} (hγ : CtxObj Γ γ),
      FamAtEq (evalTy (instantiate C p)) (evalTy C) γ (consEnv ((evalTm p).obj γ) γ) :=
    fun hγ => instantiate_atEq C hp hγ
  have hC_al : ∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ →
      FamAlongEq (evalTy (instantiate C p)) (evalTy C) γ₁ γ₂ δ
        (consEnv ((evalTm p).obj γ₁) γ₁) (consEnv ((evalTm p).obj γ₂) γ₂)
        (consEnv ((evalTm p).mor γ₁ γ₂ δ) δ) :=
    fun hδ => instantiate_alongEq C hp hδ
  have h_obj_C : ∀ {γ} (hγ : CtxObj Γ γ),
      (evalTy C).Obj (consEnv ((evalTm p).obj γ) γ) ((evalTm (.sigmaRec A B C d p)).obj γ) := by
    intro γ hγ
    rcases (hp.at_obj hγ).obj with ⟨x, y, hp_eq, hx, hy⟩
    have hd_at := pairingMotive_atEq A B C (consEnv y (consEnv x γ)) ((hA.id_tr hγ).obj hx)
    have hdo := hd_at.obj.mp (hd.at_obj (CtxObj.cons (CtxObj.cons hγ hx) hy)).obj
    dsimp only [evalTm, eval]
    rw [hp_eq]
    exact hdo
  have h_hom_C : ∀ {γ₁ γ₂ δ} (hδ : CtxHom Γ γ₁ γ₂ δ),
      (evalTy C).Hom (consEnv ((evalTm p).obj γ₁) γ₁) (consEnv ((evalTm p).obj γ₂) γ₂)
        (consEnv ((evalTm p).mor γ₁ γ₂ δ) δ)
        ((evalTm (.sigmaRec A B C d p)).obj γ₁) ((evalTm (.sigmaRec A B C d p)).obj γ₂)
        ((evalTm (.sigmaRec A B C d p)).mor γ₁ γ₂ δ) := by
    intro γ₁ γ₂ δ hδ
    rcases (hp.along hδ).2.2 with ⟨x₁, y₁, x₂, y₂, p₀, q₀, h₁, h₂, hm, hx₁, hx₂, hy₁, hy₂, hp₀, hq₀⟩
    have hd_al := pairingMotive_alongEq A B C
      (consEnv y₁ (consEnv x₁ γ₁)) (consEnv y₂ (consEnv x₂ γ₂)) (consEnv q₀ (consEnv p₀ δ))
      ((hA.id_tr hδ.source).obj hx₁) ((hA.id_tr hδ.target).obj hx₂)
    have hdh := (hd.along (CtxHom.cons (CtxHom.cons hδ ⟨hx₁, hx₂, hp₀⟩) ⟨hy₁, hy₂, hq₀⟩)).2.2
    have h1 := h_obj_C hδ.source
    have h2 := h_obj_C hδ.target
    dsimp only [evalTm, eval] at h1 h2 ⊢
    rw [h₁] at h1 ⊢; rw [h₂] at h2 ⊢; rw [hm]
    exact (hd_al.hom h1 h2).mp hdh
  refine SemTermWf.mk_of ⟨⟨hA.good.1, hB.good.1, hC.good.1, hd.good.1, hp.good.1⟩, trivial⟩
    (fun hγ => (hC_at hγ).obj.mpr (h_obj_C hγ))
    (fun {γ} hγ => by
      rcases (hp.at_obj hγ).obj with ⟨x, y, hp_eq, hx, hy⟩
      dsimp only [evalTm, eval]
      rw [(hp.at_obj hγ).id, hp_eq]
      dsimp only [idVal, sigFst_pairObj, sigSnd_pairObj, sigMorP_pairMor, sigMorQ_pairMor]
      rw [← idEnv_consEnv, ← idEnv_consEnv]
      exact (hd.at_obj (CtxObj.cons (CtxObj.cons hγ hx) hy)).id)
    (fun hδ => ((hC_al hδ).hom (h_obj_C hδ.source) (h_obj_C hδ.target)).mpr (h_hom_C hδ))
    (fun {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} h₁₂ h₂₃ => ?_)
  rcases (hp.along h₁₂).2.2 with ⟨x₁, y₁, x₂, y₂, p₁₂, q₁₂, h₁, h₂, hm₁₂, hx₁, hx₂, hy₁, hy₂, hp₁₂, hq₁₂⟩
  rcases (hp.along h₂₃).2.2 with ⟨x₂', y₂', x₃, y₃, p₂₃, q₂₃, h₂', h₃, hm₂₃, _, hx₃, _, hy₃, hp₂₃, hq₂₃⟩
  have hpair := h₂.symm.trans h₂'
  cases hpair
  have hδ₁₂_AB := CtxHom.cons (CtxHom.cons h₁₂ ⟨hx₁, hx₂, hp₁₂⟩) ⟨hy₁, hy₂, hq₁₂⟩
  have hδ₂₃_AB := CtxHom.cons (CtxHom.cons h₂₃ ⟨hx₂, hx₃, hp₂₃⟩) ⟨hy₂, hy₃, hq₂₃⟩
  have hq₁₂v := (hB.tr (CtxHom.cons h₁₂ ⟨hx₁, hx₂, hp₁₂⟩)).vertical ⟨hy₁, hy₂, hq₁₂⟩
  have h_comp_env : consEnv (sigMorQ ((evalTm p).mor γ₁ γ₃ (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃)))
      (consEnv (sigMorP ((evalTm p).mor γ₁ γ₃ (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃))) (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃)) =
    compCtx (B :: A :: Γ) (consEnv y₁ (consEnv x₁ γ₁)) (consEnv y₂ (consEnv x₂ γ₂))
      (consEnv y₃ (consEnv x₃ γ₃)) (consEnv q₁₂ (consEnv p₁₂ δ₁₂)) (consEnv q₂₃ (consEnv p₂₃ δ₂₃)) := by
    funext k; cases k with
    | zero =>
      dsimp only [consEnv, compCtx]
      rw [hp.comp_mor h₁₂ h₂₃, hm₁₂, hm₂₃]
      dsimp only [evalTy, eval, semSigma, sigMorX1, sigMorX2, sigMorP, sigMorQ, renEnv_succ_consEnv]
      rw [← (SemTypeWf.ctB_right hΓ hA hB h₂₃ ⟨hx₂, hx₃, hp₂₃⟩).comp_mor hq₁₂v]
    | succ k =>
      cases k with
      | zero =>
        dsimp only [consEnv, compCtx]
        rw [hp.comp_mor h₁₂ h₂₃, hm₁₂, hm₂₃]
        rfl
      | succ k => rfl
  have h_cv₁₂ := (hC.tr (CtxHom.cons h₁₂ (hp.along h₁₂))).vertical
    ⟨h_obj_C h₁₂.source, h_obj_C h₁₂.target, h_hom_C h₁₂⟩
  have h_cv₁₂_tr := (hC.tr (CtxHom.cons h₂₃ (hp.along h₂₃))).map_hom h_cv₁₂
  have h_cv₂₃ := (hC.tr (CtxHom.cons h₂₃ (hp.along h₂₃))).vertical
    ⟨h_obj_C h₂₃.source, h_obj_C h₂₃.target, h_hom_C h₂₃⟩
  have hd_at₃ : FamAtEq (evalTy (pairingMotive A B C)) (evalTy C)
      (consEnv y₃ (consEnv x₃ γ₃)) (consEnv (.pairObj x₃ y₃) γ₃) :=
    pairingMotive_atEq A B C (consEnv y₃ (consEnv x₃ γ₃)) ((hA.id_tr h₂₃.target).obj hx₃)
  have hd_al₂₃ : FamAlongEq (evalTy (pairingMotive A B C)) (evalTy C)
      (consEnv y₂ (consEnv x₂ γ₂)) (consEnv y₃ (consEnv x₃ γ₃)) (consEnv q₂₃ (consEnv p₂₃ δ₂₃))
      (consEnv (.pairObj x₂ y₂) γ₂) (consEnv (.pairObj x₃ y₃) γ₃)
      (consEnv (.pairMor ((evalTy A).reindexObj γ₂ γ₃ δ₂₃ x₂) x₃ p₂₃ q₂₃) δ₂₃) :=
    pairingMotive_alongEq A B C
      (consEnv y₂ (consEnv x₂ γ₂)) (consEnv y₃ (consEnv x₃ γ₃)) (consEnv q₂₃ (consEnv p₂₃ δ₂₃))
      ((hA.id_tr h₂₃.source).obj hx₂) ((hA.id_tr h₂₃.target).obj hx₃)
  have h_cv₁₂' : FiberHom (evalTy C) (consEnv (.pairObj x₂ y₂) γ₂)
      ((evalTy C).reindexObj (consEnv (.pairObj x₁ y₁) γ₁) (consEnv (.pairObj x₂ y₂) γ₂)
        (consEnv (.pairMor ((evalTy A).reindexObj γ₁ γ₂ δ₁₂ x₁) x₂ p₁₂ q₁₂) δ₁₂)
        ((evalTm d).obj (consEnv y₁ (consEnv x₁ γ₁))))
      ((evalTm d).obj (consEnv y₂ (consEnv x₂ γ₂)))
      ((evalTm d).mor (consEnv y₁ (consEnv x₁ γ₁)) (consEnv y₂ (consEnv x₂ γ₂))
        (consEnv q₁₂ (consEnv p₁₂ δ₁₂))) := by
    simpa only [evalTm, eval, h₁, h₂, hm₁₂, sigFst_pairObj, sigSnd_pairObj,
      sigMorP_pairMor, sigMorQ_pairMor] using h_cv₁₂
  have h_cv₁₂_tr' : FiberHom (evalTy C) (consEnv (.pairObj x₃ y₃) γ₃)
      ((evalTy C).reindexObj (consEnv (.pairObj x₂ y₂) γ₂) (consEnv (.pairObj x₃ y₃) γ₃)
        (consEnv (.pairMor ((evalTy A).reindexObj γ₂ γ₃ δ₂₃ x₂) x₃ p₂₃ q₂₃) δ₂₃)
        ((evalTy C).reindexObj (consEnv (.pairObj x₁ y₁) γ₁) (consEnv (.pairObj x₂ y₂) γ₂)
          (consEnv (.pairMor ((evalTy A).reindexObj γ₁ γ₂ δ₁₂ x₁) x₂ p₁₂ q₁₂) δ₁₂)
          ((evalTm d).obj (consEnv y₁ (consEnv x₁ γ₁)))))
      ((evalTy C).reindexObj (consEnv (.pairObj x₂ y₂) γ₂) (consEnv (.pairObj x₃ y₃) γ₃)
        (consEnv (.pairMor ((evalTy A).reindexObj γ₂ γ₃ δ₂₃ x₂) x₃ p₂₃ q₂₃) δ₂₃)
        ((evalTm d).obj (consEnv y₂ (consEnv x₂ γ₂))))
      ((evalTy C).reindexMor (consEnv (.pairObj x₂ y₂) γ₂) (consEnv (.pairObj x₃ y₃) γ₃)
        (consEnv (.pairMor ((evalTy A).reindexObj γ₂ γ₃ δ₂₃ x₂) x₃ p₂₃ q₂₃) δ₂₃)
        ((evalTm d).mor (consEnv y₁ (consEnv x₁ γ₁)) (consEnv y₂ (consEnv x₂ γ₂))
          (consEnv q₁₂ (consEnv p₁₂ δ₁₂)))) := by
    simpa only [evalTm, eval, h₁, h₂, h₃, hm₁₂, hm₂₃, sigFst_pairObj, sigSnd_pairObj,
      sigMorP_pairMor, sigMorQ_pairMor] using h_cv₁₂_tr
  have h_cv₂₃' : FiberHom (evalTy C) (consEnv (.pairObj x₃ y₃) γ₃)
      ((evalTy C).reindexObj (consEnv (.pairObj x₂ y₂) γ₂) (consEnv (.pairObj x₃ y₃) γ₃)
        (consEnv (.pairMor ((evalTy A).reindexObj γ₂ γ₃ δ₂₃ x₂) x₃ p₂₃ q₂₃) δ₂₃)
        ((evalTm d).obj (consEnv y₂ (consEnv x₂ γ₂))))
      ((evalTm d).obj (consEnv y₃ (consEnv x₃ γ₃)))
      ((evalTm d).mor (consEnv y₂ (consEnv x₂ γ₂)) (consEnv y₃ (consEnv x₃ γ₃))
        (consEnv q₂₃ (consEnv p₂₃ δ₂₃))) := by
    simpa only [evalTm, eval, h₂, h₃, hm₂₃, sigFst_pairObj, sigSnd_pairObj,
      sigMorP_pairMor, sigMorQ_pairMor] using h_cv₂₃
  rw [(hC_al h₂₃).reindexMor h_cv₁₂, (hC_at h₂₃.target).comp h_cv₁₂_tr h_cv₂₃]
  dsimp only [evalTm, eval]
  rw [h₁, h₂, h₃, hm₁₂, hm₂₃]
  dsimp only [sigFst_pairObj, sigSnd_pairObj, sigMorP_pairMor, sigMorQ_pairMor]
  rw [h_comp_env, hd.comp_mor hδ₁₂_AB hδ₂₃_AB, hd_al₂₃.reindexMor h_cv₁₂',
    hd_at₃.comp h_cv₁₂_tr' h_cv₂₃']

theorem compCtx_cons_vert {Γ : Context} {A : Expr} (hΓ : SemCtxWf Γ)
    {γ : Env} (hγ : CtxObj Γ γ) {x y z p q : Val} (hp : FiberHom (evalTy A) γ x y p)
    (hiA : IdentityTransport (evalTy A) γ) :
    compCtx (A :: Γ) (consEnv x γ) (consEnv y γ) (consEnv z γ)
      (consEnv p (idEnv γ)) (consEnv q (idEnv γ)) =
    consEnv ((evalTy A).comp γ p q) (idEnv γ) := by
  funext k; cases k with
  | zero =>
    dsimp only [compCtx, consEnv, renEnv_succ_consEnv]
    rw [hiA.mor hp]
  | succ k =>
    change compCtx Γ γ γ γ (idEnv γ) (idEnv γ) k = idEnv γ k
    rw [hΓ.id_comp (hΓ.id_hom hγ)]

theorem compCtx_cons_left {Γ : Context} (A : Expr) (hΓ : SemCtxWf Γ)
    {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ) (w x y u p : Val) :
    compCtx (A :: Γ) (consEnv w γ₁) (consEnv x γ₁) (consEnv y γ₂)
      (consEnv u (idEnv γ₁)) (consEnv p δ) =
    consEnv ((evalTy A).comp γ₂ ((evalTy A).reindexMor γ₁ γ₂ δ u) p) δ := by
  funext k; cases k with
  | zero => rfl
  | succ k =>
    change compCtx Γ γ₁ γ₁ γ₂ (idEnv γ₁) δ k = δ k
    rw [hΓ.id_comp hδ]

theorem compCtx_cons_right {Γ : Context} {A : Expr} (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A)
    {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ) {x y z p v : Val}
    (hp : piHetMor (evalTy A) γ₁ γ₂ δ x y p) :
    compCtx (A :: Γ) (consEnv x γ₁) (consEnv y γ₂) (consEnv z γ₂)
      (consEnv p δ) (consEnv v (idEnv γ₂)) =
    consEnv ((evalTy A).comp γ₂ p v) δ := by
  funext k; cases k with
  | zero =>
    dsimp only [compCtx, consEnv, renEnv_succ_consEnv]
    rw [(hA.id_tr hδ.target).mor ((hA.tr hδ).vertical hp)]
  | succ k =>
    change compCtx Γ γ₁ γ₂ γ₂ δ (idEnv γ₂) k = δ k
    rw [hΓ.comp_id hδ]

theorem compCtx_cons_map_id {Γ : Context} {A : Expr} (hA : SemTypeWf Γ A)
    {γ₁ γ₂ γ₃ δ₁₂ δ₂₃ : Env} (_h₁₂ : CtxHom Γ γ₁ γ₂ δ₁₂) (h₂₃ : CtxHom Γ γ₂ γ₃ δ₂₃)
    {x₁ x₂ y₃ p : Val} (hx₂ : (evalTy A).Obj γ₂ x₂)
    (hp : piHetMor (evalTy A) γ₂ γ₃ δ₂₃ x₂ y₃ p) :
    compCtx (A :: Γ) (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv y₃ γ₃)
      (consEnv (idVal x₂) δ₁₂) (consEnv p δ₂₃) =
    consEnv p (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃) := by
  funext k; cases k with
  | zero =>
    dsimp only [compCtx, consEnv, renEnv_succ_consEnv]
    rw [(hA.tr h₂₃).map_id hx₂, (hA.fiber h₂₃.target).id_comp ((hA.tr h₂₃).vertical hp)]
  | succ k => rfl

theorem SemTermWf.lam {Γ : Context} {A B b : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B)
    (hb : SemTermWf (A :: Γ) b B) :
    SemTermWf Γ (.lam A b) (.pi A B) := by
  have h_obj : ∀ {γ}, CtxObj Γ γ → (evalTy (.pi A B)).Obj γ ((evalTm (.lam A b)).obj γ) := by
    intro γ hγ
    have rkA := hA.rank hγ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [evalTm, eval]
      exact mkPiObj_ext (fun _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
        (fun x hx => by rw [piAppObj_mkPiObj_of_rk rkA hx])
        (fun x y p hp => by rw [piAppMor_mkPiObj_of_rk rkA hp])
    · intro x hx
      dsimp only [evalTm, eval]
      rw [piAppObj_mkPiObj_of_rk rkA hx]
      exact (hb.at_obj (CtxObj.cons hγ hx)).obj
    · intro x y p hp
      dsimp only [evalTm, eval]
      rw [piAppObj_mkPiObj_of_rk rkA hp.1, piAppObj_mkPiObj_of_rk rkA hp.2.1,
        piAppMor_mkPiObj_of_rk rkA hp]
      exact (hb.along (CtxHom.cons (hΓ.id_hom hγ) hp)).2.2
    · intro x hx
      dsimp only [evalTm, eval]
      rw [piAppObj_mkPiObj_of_rk rkA hx, piAppMor_mkPiObj_of_rk rkA ((hA.fiber hγ).id_hom hx)]
      rw [← idEnv_consEnv]
      exact (hb.at_obj (CtxObj.cons hγ hx)).id
    · intro x y z p q hp hq
      have hpq := (hA.fiber hγ).comp_hom hp hq
      dsimp only [evalTm, eval]
      rw [piAppMor_mkPiObj_of_rk rkA hpq, piAppMor_mkPiObj_of_rk rkA hp,
        piAppMor_mkPiObj_of_rk rkA hq,
        ← compCtx_cons_vert hΓ hγ hp (hA.id_tr hγ)]
      exact hb.comp_mor (CtxHom.cons (hΓ.id_hom hγ) hp) (CtxHom.cons (hΓ.id_hom hγ) hq)
  refine SemTermWf.mk_of ⟨⟨hA.good.1, hb.good.1⟩, trivial⟩ h_obj
    (fun {γ} hγ => ?_) (fun {γ₁ γ₂ δ} hδ => ?_) (fun {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} h₁₂ h₂₃ => ?_)
  · dsimp only [evalTm, eval, idVal_mkPiObj]
    refine mkPiMor_ext (fun _ _ _ => Iff.rfl) (fun x y p hp => ?_)
    rw [(hA.tr (hΓ.id_hom hγ)).unmap_identity_obj (hA.id_tr hγ) hp.1]
  · have rkA₁ := hA.rank hδ.source
    have rkA₂ := hA.rank hδ.target
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [evalTm, eval]
      exact mkPiMor_ext (fun _ _ _ => Iff.rfl) (fun x' y p hp' => by
        rw [piMorAt_mkPiMor_of_rk rkA₂ hp'])
    · intro x' y p hp'
      have hx := (hA.tr hδ).unmap_obj hp'.1
      have hp_het : piHetMor (evalTy A) γ₁ γ₂ δ ((evalTy A).unreindexObj γ₁ γ₂ δ x') y p := by
        refine ⟨hx, hp'.2.1, ((hA.tr hδ).hom_iff hx hp'.2.1).mpr ?_⟩
        rw [(hA.tr hδ).map_unmap_obj hp'.1]
        exact hp'.2.2
      have hbv := hb.vertical hB (CtxHom.cons hδ hp_het)
      have hdom : (evalTy B).reindexObj (consEnv x' γ₂) (consEnv y γ₂) (consEnv p (idEnv γ₂))
          (piAppObj (piTransportObj (evalTy A) (evalTy B) γ₁ γ₂ δ ((evalTm (.lam A b)).obj γ₁)) x') =
        (evalTy B).reindexObj (consEnv ((evalTy A).unreindexObj γ₁ γ₂ δ x') γ₁) (consEnv y γ₂)
          (consEnv p δ) ((evalTm b).obj (consEnv ((evalTy A).unreindexObj γ₁ γ₂ δ x') γ₁)) := by
        dsimp only [piTransportObj, evalTm, eval]
        rw [piAppObj_mkPiObj_of_rk rkA₂ hp'.1, piAppObj_mkPiObj_of_rk rkA₁ hx]
        exact (ctB_unmap_right (hA.tr hδ) (fun _ _ _ h => SemTypeWf.ctB_right hΓ hA hB hδ h) hp').comp_obj
          (hb.at_obj (CtxObj.cons hδ.source hx)).obj
      have hx'_obj : (evalTy B).Obj (consEnv x' γ₂)
          (piAppObj (piTransportObj (evalTy A) (evalTy B) γ₁ γ₂ δ ((evalTm (.lam A b)).obj γ₁)) x') := by
        dsimp only [piTransportObj, evalTm, eval]
        rw [piAppObj_mkPiObj_of_rk rkA₂ hp'.1, piAppObj_mkPiObj_of_rk rkA₁ hx]
        exact (trB_unmap_id (hA.fiber hδ.target) (hA.tr hδ)
          (fun _ _ _ h => hB.tr (CtxHom.cons hδ h)) hp'.1).map_obj
          (hb.at_obj (CtxObj.cons hδ.source hx)).obj
      have hbv' : (evalTy B).Hom (consEnv x' γ₂) (consEnv y γ₂) (consEnv p (idEnv γ₂))
          (piAppObj (piTransportObj (evalTy A) (evalTy B) γ₁ γ₂ δ ((evalTm (.lam A b)).obj γ₁)) x')
          ((evalTm b).obj (consEnv y γ₂))
          ((evalTm b).mor (consEnv ((evalTy A).unreindexObj γ₁ γ₂ δ x') γ₁) (consEnv y γ₂) (consEnv p δ)) := by
        refine ((hB.tr (CtxHom.cons (hΓ.id_hom hδ.target) hp')).hom_iff hx'_obj hbv.2.1).mpr ?_
        rw [hdom]
        exact hbv.2.2
      dsimp only [evalTm, eval]
      rw [piAppObj_mkPiObj_of_rk rkA₂ hp'.2.1, piMorAt_mkPiMor_of_rk rkA₂ hp']
      exact hbv'
    · intro w' x' y' u' p' hu' hp'
      have hup' : FiberHom (evalTy A) γ₂ w' y' ((evalTy A).comp γ₂ ((evalTy A).reindexMor γ₂ γ₂ (idEnv γ₂) u') p') := by
        rw [(hA.id_tr hδ.target).mor hu']
        exact (hA.fiber hδ.target).comp_hom hu' hp'
      have hu := (hA.tr hδ).unmap_hom hu'
      have hx₁ := hu.2.1
      have hp_het : piHetMor (evalTy A) γ₁ γ₂ δ ((evalTy A).unreindexObj γ₁ γ₂ δ x') y' p' := by
        refine ⟨hx₁, hp'.2.1, ((hA.tr hδ).hom_iff hx₁ hp'.2.1).mpr ?_⟩
        rw [(hA.tr hδ).map_unmap_obj hp'.1]
        exact hp'.2.2
      have hbu_v := hb.vertical hB (CtxHom.cons (hΓ.id_hom hδ.source) hu)
      have h_re_u : (evalTy B).reindexMor (consEnv x' γ₂) (consEnv y' γ₂) (consEnv p' (idEnv γ₂))
          (piAppMor (piTransportObj (evalTy A) (evalTy B) γ₁ γ₂ δ ((evalTm (.lam A b)).obj γ₁)) w' x' u') =
        (evalTy B).reindexMor (consEnv ((evalTy A).unreindexObj γ₁ γ₂ δ x') γ₁) (consEnv y' γ₂)
          (consEnv p' δ)
          ((evalTm b).mor (consEnv ((evalTy A).unreindexObj γ₁ γ₂ δ w') γ₁)
            (consEnv ((evalTy A).unreindexObj γ₁ γ₂ δ x') γ₁)
            (consEnv ((evalTy A).unreindexMor γ₁ γ₂ δ u') (idEnv γ₁))) := by
        dsimp only [piTransportObj, evalTm, eval]
        rw [piAppMor_mkPiObj_of_rk rkA₂ hu', piAppMor_mkPiObj_of_rk rkA₁ hu,
          (ctB_unmap_right (hA.tr hδ) (fun _ _ _ h => SemTypeWf.ctB_right hΓ hA hB hδ h) hp').comp_mor hbu_v]
      have h_comp_l := compCtx_cons_left A hΓ hδ
        ((evalTy A).unreindexObj γ₁ γ₂ δ w') ((evalTy A).unreindexObj γ₁ γ₂ δ x') y'
        ((evalTy A).unreindexMor γ₁ γ₂ δ u') p'
      rw [(hA.tr hδ).map_unmap_mor hu'] at h_comp_l
      rw [h_re_u]
      dsimp only [evalTm, eval]
      rw [piMorAt_mkPiMor_of_rk rkA₂ hup', piMorAt_mkPiMor_of_rk rkA₂ hp',
        (hA.id_tr hδ.target).mor hu', ← h_comp_l]
      exact hb.comp_mor (CtxHom.cons (hΓ.id_hom hδ.source) hu) (CtxHom.cons hδ hp_het)
    · intro x' y' z' p' v' hp' hv'
      have hpv' := (hA.fiber hδ.target).comp_hom hp' hv'
      have hx₁ := (hA.tr hδ).unmap_obj hp'.1
      have hp_het : piHetMor (evalTy A) γ₁ γ₂ δ ((evalTy A).unreindexObj γ₁ γ₂ δ x') y' p' := by
        refine ⟨hx₁, hp'.2.1, ((hA.tr hδ).hom_iff hx₁ hp'.2.1).mpr ?_⟩
        rw [(hA.tr hδ).map_unmap_obj hp'.1]
        exact hp'.2.2
      dsimp only [evalTm, eval]
      rw [piMorAt_mkPiMor_of_rk rkA₂ hpv', piMorAt_mkPiMor_of_rk rkA₂ hp',
        piAppMor_mkPiObj_of_rk rkA₂ hv',
        ← compCtx_cons_right hΓ hA hδ hp_het]
      exact hb.comp_mor (CtxHom.cons hδ hp_het) (CtxHom.cons (hΓ.id_hom hδ.target) hv')
  · have rkA₂ := hA.rank h₁₂.target
    have rkA₃ := hA.rank h₂₃.target
    dsimp only [evalTm, eval, evalTy, semPi]
    refine mkPiMor_ext (fun _ _ _ => Iff.rfl) (fun x₃ y₃ p₃ hp₃ => ?_)
    have hx₂ := (hA.tr h₂₃).unmap_obj hp₃.1
    have hx₁ := (hA.tr h₁₂).unmap_obj hx₂
    have h_id₂ : piHetMor (evalTy A) γ₁ γ₂ δ₁₂ ((evalTy A).unreindexObj γ₁ γ₂ δ₁₂ ((evalTy A).unreindexObj γ₂ γ₃ δ₂₃ x₃))
        ((evalTy A).unreindexObj γ₂ γ₃ δ₂₃ x₃) (idVal ((evalTy A).unreindexObj γ₂ γ₃ δ₂₃ x₃)) := by
      refine ⟨hx₁, hx₂, ((hA.tr h₁₂).hom_iff hx₁ hx₂).mpr ?_⟩
      rw [(hA.tr h₁₂).map_unmap_obj hx₂]
      exact ((hA.fiber h₁₂.target).id_hom hx₂).2.2
    have hp₂₃ : piHetMor (evalTy A) γ₂ γ₃ δ₂₃ ((evalTy A).unreindexObj γ₂ γ₃ δ₂₃ x₃) y₃ p₃ := by
      refine ⟨hx₂, hp₃.2.1, ((hA.tr h₂₃).hom_iff hx₂ hp₃.2.1).mpr ?_⟩
      rw [(hA.tr h₂₃).map_unmap_obj hp₃.1]
      exact hp₃.2.2
    have hbv₁₂ := hb.vertical hB (CtxHom.cons h₁₂ h_id₂)
    rw [piMorAt_mkPiMor_of_rk rkA₃ hp₃,
      piMorAt_mkPiMor_of_rk rkA₃ ((hA.fiber h₂₃.target).id_hom hp₃.1),
      (hA.tr h₂₃).unmap_id (hA.fiber h₁₂.target) hp₃.1,
      piMorAt_mkPiMor_of_rk rkA₂ ((hA.fiber h₁₂.target).id_hom hx₂),
      (ctB_unmap_right (hA.tr h₂₃) (fun _ _ _ h => SemTypeWf.ctB_right hΓ hA hB h₂₃ h) hp₃).comp_mor hbv₁₂,
      ← (hA.comp_tr h₁₂ h₂₃).uncomp_obj (hA.tr h₁₂) (hA.tr h₂₃) (hA.tr (hΓ.comp_hom h₁₂ h₂₃)) hp₃.1,
      ← compCtx_cons_map_id hA h₁₂ h₂₃ hx₂ hp₂₃]
    exact hb.comp_mor (CtxHom.cons h₁₂ h_id₂) (CtxHom.cons h₂₃ hp₂₃)

theorem SemTermWf.app {Γ : Context} {A B f a : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B)
    (hf : SemTermWf Γ f (.pi A B)) (ha : SemTermWf Γ a A) :
    SemTermWf Γ (.app A B f a) (instantiate B a) := by
  have hb_at : ∀ {γ} (hγ : CtxObj Γ γ),
      FamAtEq (evalTy (instantiate B a)) (evalTy B) γ (consEnv ((evalTm a).obj γ) γ) :=
    fun hγ => instantiate_atEq B ha hγ
  have hb_al : ∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ →
      FamAlongEq (evalTy (instantiate B a)) (evalTy B) γ₁ γ₂ δ
        (consEnv ((evalTm a).obj γ₁) γ₁) (consEnv ((evalTm a).obj γ₂) γ₂)
        (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ) :=
    fun hδ => instantiate_alongEq B ha hδ
  have h_obj_B : ∀ {γ} (hγ : CtxObj Γ γ),
      (evalTy B).Obj (consEnv ((evalTm a).obj γ) γ) (piAppObj ((evalTm f).obj γ) ((evalTm a).obj γ)) :=
    fun {γ} hγ => (hf.at_obj hγ).obj.2.1 ((evalTm a).obj γ) (ha.at_obj hγ).obj
  have h_hom_B : ∀ {γ₁ γ₂ δ} (hδ : CtxHom Γ γ₁ γ₂ δ),
      (evalTy B).Hom (consEnv ((evalTm a).obj γ₁) γ₁) (consEnv ((evalTm a).obj γ₂) γ₂)
        (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ)
        (piAppObj ((evalTm f).obj γ₁) ((evalTm a).obj γ₁))
        (piAppObj ((evalTm f).obj γ₂) ((evalTm a).obj γ₂))
        ((evalTm (.app A B f a)).mor γ₁ γ₂ δ) := by
    intro γ₁ γ₂ δ hδ
    have hf₁ := (hf.at_obj hδ.source).obj
    have hf₂ := (hf.at_obj hδ.target).obj
    have hh := (hf.along hδ).2.2
    have ha₁ := (ha.at_obj hδ.source).obj
    have hav := ha.vertical hA hδ
    have hPi := SemTypeWf.pi hΓ hA hB
    have hf₁_tr := (hPi.tr hδ).map_obj hf₁
    have hv := semPi_hom_mor_vertical (fun _ _ _ h => hB.tr (CtxHom.cons (hΓ.id_hom hδ.target) h))
      hf₁_tr hf₂ hh hav
    have hdom : (evalTy B).reindexObj (consEnv ((evalTy A).reindexObj γ₁ γ₂ δ ((evalTm a).obj γ₁)) γ₂)
        (consEnv ((evalTm a).obj γ₂) γ₂) (consEnv ((evalTm a).mor γ₁ γ₂ δ) (idEnv γ₂))
        (piAppObj ((evalTy (.pi A B)).reindexObj γ₁ γ₂ δ ((evalTm f).obj γ₁))
          ((evalTy A).reindexObj γ₁ γ₂ δ ((evalTm a).obj γ₁))) =
      (evalTy B).reindexObj (consEnv ((evalTm a).obj γ₁) γ₁) (consEnv ((evalTm a).obj γ₂) γ₂)
        (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ) (piAppObj ((evalTm f).obj γ₁) ((evalTm a).obj γ₁)) := by
      dsimp only [evalTy, eval, semPi]
      rw [piAppObj_mkPiObj_of_rk (hA.rank hδ.target) hav.1, (hA.tr hδ).unmap_map_obj ha₁]
      exact (SemTypeWf.ctB_right hΓ hA hB hδ (ha.along hδ)).comp_obj (h_obj_B hδ.source)
    have hv_hom := hv.2.2
    rw [hdom] at hv_hom
    exact ((hB.tr (CtxHom.cons hδ (ha.along hδ))).hom_iff (h_obj_B hδ.source) (h_obj_B hδ.target)).mpr hv_hom
  refine SemTermWf.mk_of ⟨⟨hA.good.1, hB.good.1, hf.good.1, ha.good.1⟩, trivial⟩
    (fun hγ => (hb_at hγ).obj.mpr (h_obj_B hγ))
    (fun hγ => by
      dsimp only [evalTm, eval]
      rw [(hf.at_obj hγ).id, (hA.id_tr hγ).obj (ha.at_obj hγ).obj, (ha.at_obj hγ).id,
        semPi_id_components (hf.at_obj hγ).obj, (hf.at_obj hγ).obj.2.2.2.1 _ (ha.at_obj hγ).obj])
    (fun hδ => ((hb_al hδ).hom (h_obj_B hδ.source) (h_obj_B hδ.target)).mpr (h_hom_B hδ))
    (fun {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} h₁₂ h₂₃ => ?_)
  have hPi := SemTypeWf.pi hΓ hA hB
  have hf₃ := (hf.at_obj h₂₃.target).obj
  have hh₂₃ := (hf.along h₂₃).2.2
  have hfv₁₂ := hf.vertical hPi h₁₂
  have hfv₁₂_tr := (hPi.tr h₂₃).map_hom hfv₁₂
  have hh₁₂_tr := (semPi_hom_iff (hA.id_tr h₂₃.target) (hA.tr (hΓ.id_hom h₂₃.target))
    (fun x hx => hB.id_tr (CtxObj.cons h₂₃.target hx))
    (fun x y p hp => hB.tr (CtxHom.cons (hΓ.id_hom h₂₃.target) hp)) hfv₁₂_tr.1).mp hfv₁₂_tr.2.2
  have hav₁₂ := ha.vertical hA h₁₂
  have hav₁₂_tr := (hA.tr h₂₃).map_hom hav₁₂
  have hav₂₃ := ha.vertical hA h₂₃
  have hav₁₃ := (hA.fiber h₂₃.target).comp_hom hav₁₂_tr hav₂₃
  have h_app_v₁₂_B : FiberHom (evalTy B) (consEnv ((evalTm a).obj γ₂) γ₂)
      ((evalTy B).reindexObj (consEnv ((evalTm a).obj γ₁) γ₁)
        (consEnv ((evalTm a).obj γ₂) γ₂) (consEnv ((evalTm a).mor γ₁ γ₂ δ₁₂) δ₁₂)
        (piAppObj ((evalTm f).obj γ₁) ((evalTm a).obj γ₁)))
      (piAppObj ((evalTm f).obj γ₂) ((evalTm a).obj γ₂))
      ((evalTm (.app A B f a)).mor γ₁ γ₂ δ₁₂) :=
    (hB.tr (CtxHom.cons h₁₂ (ha.along h₁₂))).vertical ⟨h_obj_B h₁₂.source, h_obj_B h₁₂.target, h_hom_B h₁₂⟩
  have h_app_v₂₃_B : FiberHom (evalTy B) (consEnv ((evalTm a).obj γ₃) γ₃)
      ((evalTy B).reindexObj (consEnv ((evalTm a).obj γ₂) γ₂)
        (consEnv ((evalTm a).obj γ₃) γ₃) (consEnv ((evalTm a).mor γ₂ γ₃ δ₂₃) δ₂₃)
        (piAppObj ((evalTm f).obj γ₂) ((evalTm a).obj γ₂)))
      (piAppObj ((evalTm f).obj γ₃) ((evalTm a).obj γ₃))
      ((evalTm (.app A B f a)).mor γ₂ γ₃ δ₂₃) :=
    (hB.tr (CtxHom.cons h₂₃ (ha.along h₂₃))).vertical ⟨h_obj_B h₂₃.source, h_obj_B h₂₃.target, h_hom_B h₂₃⟩
  have h_app_v₁₂_B_tr := (hB.tr (CtxHom.cons h₂₃ (ha.along h₂₃))).map_hom h_app_v₁₂_B
  have h_η₁_p₁₂ : piMorAt ((evalTy (.pi A B)).reindexMor γ₂ γ₃ δ₂₃ ((evalTm f).mor γ₁ γ₂ δ₁₂))
      ((evalTy A).reindexObj γ₂ γ₃ δ₂₃ ((evalTy A).reindexObj γ₁ γ₂ δ₁₂ ((evalTm a).obj γ₁)))
      ((evalTy A).reindexObj γ₂ γ₃ δ₂₃ ((evalTm a).obj γ₂))
      ((evalTy A).reindexMor γ₂ γ₃ δ₂₃ ((evalTm a).mor γ₁ γ₂ δ₁₂)) =
    (evalTy B).reindexMor (consEnv ((evalTm a).obj γ₂) γ₂)
      (consEnv ((evalTy A).reindexObj γ₂ γ₃ δ₂₃ ((evalTm a).obj γ₂)) γ₃)
      (consEnv (idVal ((evalTy A).reindexObj γ₂ γ₃ δ₂₃ ((evalTm a).obj γ₂))) δ₂₃)
      ((evalTm (.app A B f a)).mor γ₁ γ₂ δ₁₂) := by
    dsimp only [evalTy, eval, semPi, evalTm]
    rw [piMorAt_mkPiMor_of_rk (hA.rank h₂₃.target) hav₁₂_tr,
      (hA.tr h₂₃).unmap_map_obj hav₁₂.1, (hA.tr h₂₃).unmap_map_obj hav₁₂.2.1,
      (hA.tr h₂₃).unmap_map_mor hav₁₂]
  have h_re_η₁ : (evalTy B).reindexMor (consEnv ((evalTy A).reindexObj γ₂ γ₃ δ₂₃ ((evalTm a).obj γ₂)) γ₃)
      (consEnv ((evalTm a).obj γ₃) γ₃) (consEnv ((evalTm a).mor γ₂ γ₃ δ₂₃) (idEnv γ₃))
      (piMorAt ((evalTy (.pi A B)).reindexMor γ₂ γ₃ δ₂₃ ((evalTm f).mor γ₁ γ₂ δ₁₂))
        ((evalTy A).reindexObj γ₂ γ₃ δ₂₃ ((evalTy A).reindexObj γ₁ γ₂ δ₁₂ ((evalTm a).obj γ₁)))
        ((evalTy A).reindexObj γ₂ γ₃ δ₂₃ ((evalTm a).obj γ₂))
        ((evalTy A).reindexMor γ₂ γ₃ δ₂₃ ((evalTm a).mor γ₁ γ₂ δ₁₂))) =
    (evalTy B).reindexMor (consEnv ((evalTm a).obj γ₂) γ₂)
      (consEnv ((evalTm a).obj γ₃) γ₃) (consEnv ((evalTm a).mor γ₂ γ₃ δ₂₃) δ₂₃)
      ((evalTm (.app A B f a)).mor γ₁ γ₂ δ₁₂) := by
    rw [h_η₁_p₁₂, (SemTypeWf.ctB_right hΓ hA hB h₂₃ (ha.along h₂₃)).comp_mor h_app_v₁₂_B]
  have h_v₁ := (hB.tr (CtxHom.cons (hΓ.id_hom h₂₃.target) hav₂₃)).map_hom
    (semPi_hom_mor_vertical (fun x y p hp => hB.tr (CtxHom.cons (hΓ.id_hom h₂₃.target) hp))
      hfv₁₂_tr.1 hfv₁₂_tr.2.1 hh₁₂_tr hav₁₂_tr)
  have h_v₂ := semPi_obj_mor_vertical (fun x y p hp => hB.tr (CtxHom.cons (hΓ.id_hom h₂₃.target) hp))
    hfv₁₂_tr.2.1 hav₂₃
  have h_v₃ := semPi_hom_diag_vertical (hA.fiber h₂₃.target)
    (fun x hx => hB.id_tr (CtxObj.cons h₂₃.target hx))
    (fun x y p hp => hB.tr (CtxHom.cons (hΓ.id_hom h₂₃.target) hp))
    hfv₁₂_tr.2.1 hf₃ hh₂₃ hav₂₃.2.1
  change piMorAt ((evalTm f).mor γ₁ γ₃ (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃))
      ((evalTy A).reindexObj γ₁ γ₃ (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃) ((evalTm a).obj γ₁))
      ((evalTm a).obj γ₃) ((evalTm a).mor γ₁ γ₃ (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃)) =
    (evalTy (instantiate B a)).comp γ₃
      ((evalTy (instantiate B a)).reindexMor γ₂ γ₃ δ₂₃ ((evalTm (.app A B f a)).mor γ₁ γ₂ δ₁₂))
      ((evalTm (.app A B f a)).mor γ₂ γ₃ δ₂₃)
  rw [hf.comp_mor h₁₂ h₂₃, ha.comp_mor h₁₂ h₂₃,
    ← (hA.comp_tr h₁₂ h₂₃).comp_obj (ha.at_obj h₁₂.source).obj]
  change piMorAt (mkPiMor (evalTy A).lvl (piDomMor (evalTy A) γ₃) (fun x y p =>
      (evalTy B).comp (consEnv y γ₃)
        ((evalTy B).reindexMor (consEnv x γ₃) (consEnv y γ₃) (consEnv p (idEnv γ₃))
          (piMorAt ((evalTy (.pi A B)).reindexMor γ₂ γ₃ δ₂₃ ((evalTm f).mor γ₁ γ₂ δ₁₂)) x x (idVal x)))
        (piMorAt ((evalTm f).mor γ₂ γ₃ δ₂₃) x y p)))
      ((evalTy A).reindexObj γ₂ γ₃ δ₂₃ ((evalTy A).reindexObj γ₁ γ₂ δ₁₂ ((evalTm a).obj γ₁)))
      ((evalTm a).obj γ₃)
      ((evalTy A).comp γ₃ ((evalTy A).reindexMor γ₂ γ₃ δ₂₃ ((evalTm a).mor γ₁ γ₂ δ₁₂)) ((evalTm a).mor γ₂ γ₃ δ₂₃)) = _
  rw [piMorAt_mkPiMor_of_rk (hA.rank h₂₃.target) hav₁₃,
    semPi_comp_alt (hA.fiber h₂₃.target) (hA.id_tr h₂₃.target)
      (fun x hx => hB.fiber (CtxObj.cons h₂₃.target hx))
      (fun x hx => hB.id_tr (CtxObj.cons h₂₃.target hx))
      (fun x y p hp => hB.tr (CtxHom.cons (hΓ.id_hom h₂₃.target) hp))
      hfv₁₂_tr.1 hfv₁₂_tr.2.1 hf₃ hh₁₂_tr hh₂₃ hav₁₃,
    hh₁₂_tr.2.2.2 _ _ _ _ _ hav₁₂_tr hav₂₃,
    (hB.fiber (CtxObj.cons h₂₃.target (ha.at_obj h₂₃.target).obj)).assoc h_v₁ h_v₂ h_v₃,
    ← piMorAt_decomp_right (hA.fiber h₂₃.target) (hA.id_tr h₂₃.target)
      (fun x hx => hB.id_tr (CtxObj.cons h₂₃.target hx))
      (fun x y p hp => hB.tr (CtxHom.cons (hΓ.id_hom h₂₃.target) hp))
      hfv₁₂_tr.2.1 hh₂₃ hav₂₃,
    h_re_η₁,
    (hb_al h₂₃).reindexMor h_app_v₁₂_B,
    (hb_at h₂₃.target).comp h_app_v₁₂_B_tr h_app_v₂₃_B]
  rfl

end HofmannStreicher1994.Repaired

/-! ## SemTermWf2.lean -/

namespace HofmannStreicher1994.Repaired

def jDiagMor (γ₂ : Env) (a_mor : Val) (δ : Env) : Env :=
  consEnv (.idObj (idVal (γ₂ 0))) (consEnv a_mor (consEnv a_mor δ))

theorem eval_fst_weaken (A : Expr) :
    (eval (HofmannStreicher1994.weaken A)).1 = renameFam Nat.succ (evalTy A) :=
  evalTy_rename A Nat.succ

theorem eval_fst_weaken₂ (A : Expr) :
    (eval (HofmannStreicher1994.weaken (HofmannStreicher1994.weaken A))).1 =
      renameFam Nat.succ (renameFam Nat.succ (evalTy A)) := by
  rw [eval_fst_weaken, HofmannStreicher1994.weaken, evalTy_rename]

theorem j_diag_context_arrow {Γ : Context} {A : Expr}
    (hA : SemTypeWf Γ A) {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ)
    {a₁ a₂ a_mor : Val} (ha : piHetMor (evalTy A) γ₁ γ₂ δ a₁ a₂ a_mor) :
    CtxHom (identityContext Γ A) (jDiagonal γ₁ a₁) (jDiagonal γ₂ a₂)
      (consEnv (.idObj (idVal a₂)) (consEnv a_mor (consEnv a_mor δ))) := by
  have hδ₁ : CtxHom (A :: Γ) (consEnv a₁ γ₁) (consEnv a₂ γ₂) (consEnv a_mor δ) :=
    CtxHom.cons hδ ha
  have ha_w : piHetMor (evalTy (HofmannStreicher1994.weaken A))
      (consEnv a₁ γ₁) (consEnv a₂ γ₂) (consEnv a_mor δ) a₁ a₂ a_mor := by
    rw [HofmannStreicher1994.weaken, evalTy_rename]
    exact ha
  have hδ₂ : CtxHom (HofmannStreicher1994.weaken A :: A :: Γ)
      (consEnv a₁ (consEnv a₁ γ₁)) (consEnv a₂ (consEnv a₂ γ₂))
      (consEnv a_mor (consEnv a_mor δ)) :=
    CtxHom.cons hδ₁ ha_w
  refine CtxHom.cons hδ₂ ⟨?_, ?_, ?_⟩
  · dsimp only [evalTy, eval, semId, evalTm, consEnv]
    rw [eval_fst_weaken₂]
    dsimp only [renameFam]
    simp only [idEnv_consEnv, renEnv_succ_consEnv]
    exact ⟨idVal a₁, rfl, ((hA.fiber hδ.source).id_hom ha.1).2.2⟩
  · dsimp only [evalTy, eval, semId, evalTm, consEnv]
    rw [eval_fst_weaken₂]
    dsimp only [renameFam]
    simp only [idEnv_consEnv, renEnv_succ_consEnv]
    exact ⟨idVal a₂, rfl, ((hA.fiber hδ.target).id_hom ha.2.1).2.2⟩
  · have hav := (hA.tr hδ).vertical ha
    dsimp only [evalTy, eval, semId, evalTm, consEnv, unId]
    rw [eval_fst_weaken₂]
    dsimp only [renameFam]
    simp only [idEnv_consEnv, renEnv_succ_consEnv]
    rw [(hA.tr hδ).map_id ha.1, (hA.fiber hδ.target).id_comp hav, (hA.fiber hδ.target).inv_comp hav]
    exact ⟨rfl, trivial, idVal a₁, rfl, ((hA.fiber hδ.source).id_hom ha.1).2.2⟩

theorem j_targ_context_arrow {Γ : Context} {A : Expr}
    (_hA : SemTypeWf Γ A) {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ)
    {a₁ a₂ a_mor b₁ b₂ b_mor p₁ p₂ p_mor : Val}
    (ha : piHetMor (evalTy A) γ₁ γ₂ δ a₁ a₂ a_mor)
    (hb : piHetMor (evalTy A) γ₁ γ₂ δ b₁ b₂ b_mor)
    (hp₁ : (evalTy A).Hom γ₁ γ₁ (idEnv γ₁) a₁ b₁ (unId p₁))
    (hp₁_eq : p₁ = .idObj (unId p₁))
    (hp₂ : (evalTy A).Hom γ₂ γ₂ (idEnv γ₂) a₂ b₂ (unId p₂))
    (hp₂_eq : p₂ = .idObj (unId p₂))
    (hp_mor : p₂ = .idObj ((evalTy A).comp γ₂ ((evalTy A).inv γ₂ a_mor)
      ((evalTy A).comp γ₂ ((evalTy A).reindexMor γ₁ γ₂ δ (unId p₁)) b_mor)))
    (hp_mor_eq : p_mor = p₂) :
    CtxHom (identityContext Γ A) (jTarget γ₁ a₁ b₁ p₁) (jTarget γ₂ a₂ b₂ p₂)
      (consEnv p_mor (consEnv b_mor (consEnv a_mor δ))) := by
  have hδ₁ : CtxHom (A :: Γ) (consEnv a₁ γ₁) (consEnv a₂ γ₂) (consEnv a_mor δ) :=
    CtxHom.cons hδ ha
  have hb_w : piHetMor (evalTy (HofmannStreicher1994.weaken A))
      (consEnv a₁ γ₁) (consEnv a₂ γ₂) (consEnv a_mor δ) b₁ b₂ b_mor := by
    rw [HofmannStreicher1994.weaken, evalTy_rename]
    exact hb
  have hδ₂ : CtxHom (HofmannStreicher1994.weaken A :: A :: Γ)
      (consEnv b₁ (consEnv a₁ γ₁)) (consEnv b₂ (consEnv a₂ γ₂))
      (consEnv b_mor (consEnv a_mor δ)) :=
    CtxHom.cons hδ₁ hb_w
  refine CtxHom.cons hδ₂ ⟨?_, ?_, ?_⟩
  · dsimp only [evalTy, eval, semId, evalTm, consEnv]
    rw [eval_fst_weaken₂]
    dsimp only [renameFam]
    simp only [idEnv_consEnv, renEnv_succ_consEnv]
    exact ⟨unId p₁, hp₁_eq, hp₁⟩
  · dsimp only [evalTy, eval, semId, evalTm, consEnv]
    rw [eval_fst_weaken₂]
    dsimp only [renameFam]
    simp only [idEnv_consEnv, renEnv_succ_consEnv]
    exact ⟨unId p₂, hp₂_eq, hp₂⟩
  · dsimp only [evalTy, eval, semId, evalTm, consEnv]
    rw [eval_fst_weaken₂]
    dsimp only [renameFam]
    simp only [idEnv_consEnv, renEnv_succ_consEnv]
    exact ⟨hp_mor, hp_mor_eq, unId p₁, hp₁_eq, hp₁⟩

theorem j_comm_square {Γ : Context} {A : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) {γ₁ γ₂ δ : Env} (hδ : CtxHom Γ γ₁ γ₂ δ)
    {a₁ a₂ a_mor b₁ b₂ b_mor p₁ p₂ : Val}
    (ha : piHetMor (evalTy A) γ₁ γ₂ δ a₁ a₂ a_mor)
    (hb : piHetMor (evalTy A) γ₁ γ₂ δ b₁ b₂ b_mor)
    (hp₁ : (evalTy A).Hom γ₁ γ₁ (idEnv γ₁) a₁ b₁ (unId p₁))
    (hp₂ : (evalTy A).Hom γ₂ γ₂ (idEnv γ₂) a₂ b₂ (unId p₂))
    (hp₂_eq : p₂ = .idObj (unId p₂))
    (hp_mor : p₂ = .idObj ((evalTy A).comp γ₂ ((evalTy A).inv γ₂ a_mor)
      ((evalTy A).comp γ₂ ((evalTy A).reindexMor γ₁ γ₂ δ (unId p₁)) b_mor))) :
    compCtx (identityContext Γ A) (jDiagonal γ₁ a₁) (jDiagonal γ₂ a₂) (jTarget γ₂ a₂ b₂ p₂)
      (consEnv (.idObj (idVal a₂)) (consEnv a_mor (consEnv a_mor δ))) (jArrow γ₂ a₂ p₂) =
    compCtx (identityContext Γ A) (jDiagonal γ₁ a₁) (jTarget γ₁ a₁ b₁ p₁) (jTarget γ₂ a₂ b₂ p₂)
      (jArrow γ₁ a₁ p₁) (consEnv p₂ (consEnv b_mor (consEnv a_mor δ))) := by
  have hav := (hA.tr hδ).vertical ha
  have hbv := (hA.tr hδ).vertical hb
  have hq₁ : FiberHom (evalTy A) γ₁ a₁ b₁ (unId p₁) := ⟨ha.1, hb.1, hp₁⟩
  have hq₁_tr := (hA.tr hδ).map_hom hq₁
  have hq₂ : FiberHom (evalTy A) γ₂ a₂ b₂ (unId p₂) := ⟨ha.2.1, hb.2.1, hp₂⟩
  have hq₂_val : unId p₂ = (evalTy A).comp γ₂ ((evalTy A).inv γ₂ a_mor)
      ((evalTy A).comp γ₂ ((evalTy A).reindexMor γ₁ γ₂ δ (unId p₁)) b_mor) := by
    have := congrArg unId hp_mor
    simpa only [unId_idObj] using this
  funext k; cases k with
  | zero =>
    dsimp only [identityContext, compCtx, jDiagonal, jTarget, jArrow, consEnv]
    dsimp only [evalTy, eval, semId, evalTm]
    rw [eval_fst_weaken₂, unId_idObj]
    dsimp only [renameFam]
    simp only [renEnv_succ_consEnv, consEnv_zero, consEnv_succ]
    rw [(hA.fiber hδ.target).inv_id ha.2.1, (hA.id_tr hδ.target).mor ((hA.fiber hδ.target).id_hom ha.2.1),
      (hA.fiber hδ.target).id_comp hq₂, (hA.fiber hδ.target).id_comp hq₂,
      ← hp₂_eq, ← hp_mor]
  | succ k =>
    cases k with
    | zero =>
      dsimp only [identityContext, compCtx, jDiagonal, jTarget, jArrow, consEnv]
      rw [HofmannStreicher1994.weaken, evalTy_rename]
      dsimp only [renameFam]
      simp only [renEnv_succ_consEnv, consEnv_zero]
      rw [(hA.id_tr hδ.target).mor hav, hq₂_val,
        ← (hA.fiber hδ.target).assoc hav ((hA.fiber hδ.target).inv_hom hav)
          ((hA.fiber hδ.target).comp_hom hq₁_tr hbv),
        (hA.fiber hδ.target).comp_inv hav,
        (hA.fiber hδ.target).id_comp ((hA.fiber hδ.target).comp_hom hq₁_tr hbv)]
    | succ k =>
      cases k with
      | zero =>
        dsimp only [identityContext, compCtx, jDiagonal, jTarget, jArrow, consEnv]
        simp only [renEnv_succ_consEnv, consEnv_zero]
        rw [(hA.id_tr hδ.target).mor hav, (hA.fiber hδ.target).comp_id hav,
          (hA.tr hδ).map_id ha.1, (hA.fiber hδ.target).id_comp hav]
      | succ k =>
        change compCtx Γ γ₁ γ₂ γ₂ δ (idEnv γ₂) k = compCtx Γ γ₁ γ₁ γ₂ (idEnv γ₁) δ k
        rw [hΓ.comp_id hδ, hΓ.id_comp hδ]

theorem SemTermWf.idRec {Γ : Context} {A C d a b p : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hC : SemTypeWf (identityContext Γ A) C)
    (hd : SemTermWf (A :: Γ) d (reflexivityMotive A C))
    (ha : SemTermWf Γ a A) (hb : SemTermWf Γ b A)
    (hp : SemTermWf Γ p (.identity A a b)) :
    SemTermWf Γ (.idRec A C d a b p) (instantiate₃ C a b p) := by
  have hd_obj_C : ∀ {γ} (hγ : CtxObj Γ γ) {x} (hx : (evalTy A).Obj γ x),
      (evalTy C).Obj (jDiagonal γ x) ((evalTm d).obj (consEnv x γ)) :=
    fun {γ} hγ {x} hx => (reflexivityMotive_atEq A C (consEnv x γ)).obj.mp
      (hd.at_obj (CtxObj.cons hγ hx)).obj
  have hd_hom_C : ∀ {γ₁ γ₂ δ} (hδ : CtxHom Γ γ₁ γ₂ δ)
      {x₁ x₂ xm} (hx : piHetMor (evalTy A) γ₁ γ₂ δ x₁ x₂ xm),
      (evalTy C).Hom (jDiagonal γ₁ x₁) (jDiagonal γ₂ x₂)
        (consEnv (.idObj (idVal x₂)) (consEnv xm (consEnv xm δ)))
        ((evalTm d).obj (consEnv x₁ γ₁)) ((evalTm d).obj (consEnv x₂ γ₂))
        ((evalTm d).mor (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv xm δ)) :=
    fun {γ₁ γ₂ δ} hδ {x₁ x₂ xm} hx =>
      ((reflexivityMotive_alongEq A C (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv xm δ)).hom
        (hd_obj_C hδ.source hx.1) (hd_obj_C hδ.target hx.2.1)).mp
        (hd.along (CtxHom.cons hδ hx)).2.2
  have h_idRec_obj : ∀ {γ} (hγ : CtxObj Γ γ),
      (evalTy (instantiate₃ C a b p)).Obj γ ((evalTm (.idRec A C d a b p)).obj γ) := by
    intro γ hγ
    exact eval_idRec_obj (hΓ.id_hom hγ) (hA.fiber hγ) (hA.id_tr hγ)
      (fun _ _ _ hδ_J _ hv => (hC.tr hδ_J).map_obj hv)
      (fun _ hx => (hd.at_obj (CtxObj.cons hγ hx)).obj)
      (ha.at_obj hγ) (hb.at_obj hγ) (hp.at_obj hγ) ha.good.2 hb.good.2 hp.good.2
  have h_idRec_obj_C : ∀ {γ} (hγ : CtxObj Γ γ),
      (evalTy C).Obj (jTarget γ ((evalTm a).obj γ) ((evalTm b).obj γ) ((evalTm p).obj γ))
        ((evalTm (.idRec A C d a b p)).obj γ) :=
    fun hγ => (instantiate₃_atEq C ha hb hp hγ).obj.mp (h_idRec_obj hγ)
  have h_idRec_hom_C : ∀ {γ₁ γ₂ δ} (hδ : CtxHom Γ γ₁ γ₂ δ),
      (evalTy C).Hom
        (jTarget γ₁ ((evalTm a).obj γ₁) ((evalTm b).obj γ₁) ((evalTm p).obj γ₁))
        (jTarget γ₂ ((evalTm a).obj γ₂) ((evalTm b).obj γ₂) ((evalTm p).obj γ₂))
        (consEnv ((evalTm p).mor γ₁ γ₂ δ) (consEnv ((evalTm b).mor γ₁ γ₂ δ) (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ)))
        ((evalTm (.idRec A C d a b p)).obj γ₁)
        ((evalTm (.idRec A C d a b p)).obj γ₂)
        ((evalTm (.idRec A C d a b p)).mor γ₁ γ₂ δ) := by
    intro γ₁ γ₂ δ hδ
    rcases (hp.at_obj hδ.source).obj with ⟨q₁, hq₁_eq, hq₁_hom⟩
    rcases (hp.at_obj hδ.target).obj with ⟨q₂, hq₂_eq, hq₂_hom⟩
    rcases (hp.along hδ).2.2 with ⟨hp_mor, hp_mor_eq, _⟩
    have hp₁_un : unId ((evalTm p).obj γ₁) = q₁ := by rw [hq₁_eq, unId_idObj]
    have hp₂_un : unId ((evalTm p).obj γ₂) = q₂ := by rw [hq₂_eq, unId_idObj]
    have hδ_diag := j_diag_context_arrow hA hδ (ha.along hδ)
    have hδ_J₁ : CtxHom (identityContext Γ A) (jDiagonal γ₁ ((evalTm a).obj γ₁))
        (jTarget γ₁ ((evalTm a).obj γ₁) ((evalTm b).obj γ₁) ((evalTm p).obj γ₁))
        (jArrow γ₁ ((evalTm a).obj γ₁) ((evalTm p).obj γ₁)) := by
      rw [hq₁_eq]
      exact j_context_arrow (hΓ.id_hom hδ.source) (hA.fiber hδ.source) (hA.id_tr hδ.source)
        ⟨(ha.at_obj hδ.source).obj, (hb.at_obj hδ.source).obj, hq₁_hom⟩
    have hδ_J₂ : CtxHom (identityContext Γ A) (jDiagonal γ₂ ((evalTm a).obj γ₂))
        (jTarget γ₂ ((evalTm a).obj γ₂) ((evalTm b).obj γ₂) ((evalTm p).obj γ₂))
        (jArrow γ₂ ((evalTm a).obj γ₂) ((evalTm p).obj γ₂)) := by
      rw [hq₂_eq]
      exact j_context_arrow (hΓ.id_hom hδ.target) (hA.fiber hδ.target) (hA.id_tr hδ.target)
        ⟨(ha.at_obj hδ.target).obj, (hb.at_obj hδ.target).obj, hq₂_hom⟩
    have hδ_targ := j_targ_context_arrow hA hδ (ha.along hδ) (hb.along hδ)
      (hp₁_un.symm ▸ hq₁_hom) (hq₁_eq.trans (congrArg Tree.idObj hp₁_un.symm))
      (hp₂_un.symm ▸ hq₂_hom) (hq₂_eq.trans (congrArg Tree.idObj hp₂_un.symm))
      hp_mor hp_mor_eq
    have h_comm := j_comm_square hΓ hA hδ (ha.along hδ) (hb.along hδ)
      (hp₁_un.symm ▸ hq₁_hom) (hp₂_un.symm ▸ hq₂_hom)
      (hq₂_eq.trans (congrArg Tree.idObj hp₂_un.symm)) hp_mor
    have h_ct₁ := hC.comp_tr hδ_diag hδ_J₂
    have h_ct₂ := hC.comp_tr hδ_J₁ hδ_targ
    have hd₁_obj := hd_obj_C hδ.source (ha.at_obj hδ.source).obj
    have h_ro_eq : (evalTy C).reindexObj (jDiagonal γ₂ ((evalTm a).obj γ₂))
        (jTarget γ₂ ((evalTm a).obj γ₂) ((evalTm b).obj γ₂) ((evalTm p).obj γ₂))
        (jArrow γ₂ ((evalTm a).obj γ₂) ((evalTm p).obj γ₂))
        ((evalTy C).reindexObj (jDiagonal γ₁ ((evalTm a).obj γ₁)) (jDiagonal γ₂ ((evalTm a).obj γ₂))
          (consEnv (.idObj (idVal ((evalTm a).obj γ₂))) (consEnv ((evalTm a).mor γ₁ γ₂ δ) (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ)))
          ((evalTm d).obj (consEnv ((evalTm a).obj γ₁) γ₁))) =
      (evalTy C).reindexObj (jTarget γ₁ ((evalTm a).obj γ₁) ((evalTm b).obj γ₁) ((evalTm p).obj γ₁))
        (jTarget γ₂ ((evalTm a).obj γ₂) ((evalTm b).obj γ₂) ((evalTm p).obj γ₂))
        (consEnv ((evalTm p).mor γ₁ γ₂ δ) (consEnv ((evalTm b).mor γ₁ γ₂ δ) (consEnv ((evalTm a).mor γ₁ γ₂ δ) δ)))
        ((evalTm (.idRec A C d a b p)).obj γ₁) := by
      have h1 := h_ct₁.comp_obj hd₁_obj
      have h2 := h_ct₂.comp_obj hd₁_obj
      rw [hp_mor_eq] at h2 ⊢
      exact h1.trans (by rw [h_comm]; exact h2.symm)
    have hdv := (hC.tr hδ_diag).vertical ⟨hd₁_obj, hd_obj_C hδ.target (ha.at_obj hδ.target).obj, hd_hom_C hδ (ha.along hδ)⟩
    have hdv_tr := (hC.tr hδ_J₂).map_hom hdv
    have hdv_hom := hdv_tr.2.2
    rw [h_ro_eq] at hdv_hom
    exact ((hC.tr hδ_targ).hom_iff (h_idRec_obj_C hδ.source) (h_idRec_obj_C hδ.target)).mpr hdv_hom
  refine SemTermWf.mk_of ⟨⟨hA.good.1, hC.good.1, hd.good.1, ha.good.1, hb.good.1, hp.good.1⟩, trivial⟩
    h_idRec_obj
    (fun {γ} hγ => by
      rcases (hp.at_obj hγ).obj with ⟨q, hq_eq, hq_hom⟩
      have hδ_J : CtxHom (identityContext Γ A) (jDiagonal γ ((evalTm a).obj γ))
          (jTarget γ ((evalTm a).obj γ) ((evalTm b).obj γ) ((evalTm p).obj γ))
          (jArrow γ ((evalTm a).obj γ) ((evalTm p).obj γ)) := by
        rw [hq_eq]
        exact j_context_arrow (hΓ.id_hom hγ) (hA.fiber hγ) (hA.id_tr hγ)
          ⟨(ha.at_obj hγ).obj, (hb.at_obj hγ).obj, hq_hom⟩
      exact eval_idRec_identity (ha.at_obj hγ).id
        (hd.at_obj (CtxObj.cons hγ (ha.at_obj hγ).obj)).id
        (hd_obj_C hγ (ha.at_obj hγ).obj)
        (hC.tr hδ_J))
    (fun hδ => ((instantiate₃_alongEq C ha hb hp hδ).hom (h_idRec_obj_C hδ.source) (h_idRec_obj_C hδ.target)).mpr
      (h_idRec_hom_C hδ))
    (fun {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} h₁₂ h₂₃ => ?_)
  rcases (hp.at_obj h₁₂.target).obj with ⟨q₂, hq₂_eq, hq₂_hom⟩
  rcases (hp.at_obj h₂₃.target).obj with ⟨q₃, hq₃_eq, hq₃_hom⟩
  rcases (hp.along h₂₃).2.2 with ⟨hp₂₃_mor, hp₂₃_mor_eq, _⟩
  have hp₂_un : unId ((evalTm p).obj γ₂) = q₂ := by rw [hq₂_eq, unId_idObj]
  have hp₃_un : unId ((evalTm p).obj γ₃) = q₃ := by rw [hq₃_eq, unId_idObj]
  have hδ_diag₁₂ := j_diag_context_arrow hA h₁₂ (ha.along h₁₂)
  have hδ_diag₂₃ := j_diag_context_arrow hA h₂₃ (ha.along h₂₃)
  have hδ_J₂ : CtxHom (identityContext Γ A) (jDiagonal γ₂ ((evalTm a).obj γ₂))
      (jTarget γ₂ ((evalTm a).obj γ₂) ((evalTm b).obj γ₂) ((evalTm p).obj γ₂))
      (jArrow γ₂ ((evalTm a).obj γ₂) ((evalTm p).obj γ₂)) := by
    rw [hq₂_eq]
    exact j_context_arrow (hΓ.id_hom h₁₂.target) (hA.fiber h₁₂.target) (hA.id_tr h₁₂.target)
      ⟨(ha.at_obj h₁₂.target).obj, (hb.at_obj h₁₂.target).obj, hq₂_hom⟩
  have hδ_J₃ : CtxHom (identityContext Γ A) (jDiagonal γ₃ ((evalTm a).obj γ₃))
      (jTarget γ₃ ((evalTm a).obj γ₃) ((evalTm b).obj γ₃) ((evalTm p).obj γ₃))
      (jArrow γ₃ ((evalTm a).obj γ₃) ((evalTm p).obj γ₃)) := by
    rw [hq₃_eq]
    exact j_context_arrow (hΓ.id_hom h₂₃.target) (hA.fiber h₂₃.target) (hA.id_tr h₂₃.target)
      ⟨(ha.at_obj h₂₃.target).obj, (hb.at_obj h₂₃.target).obj, hq₃_hom⟩
  have hδ_targ₁₂ : CtxHom (identityContext Γ A)
      (jTarget γ₁ ((evalTm a).obj γ₁) ((evalTm b).obj γ₁) ((evalTm p).obj γ₁))
      (jTarget γ₂ ((evalTm a).obj γ₂) ((evalTm b).obj γ₂) ((evalTm p).obj γ₂))
      (consEnv ((evalTm p).mor γ₁ γ₂ δ₁₂) (consEnv ((evalTm b).mor γ₁ γ₂ δ₁₂) (consEnv ((evalTm a).mor γ₁ γ₂ δ₁₂) δ₁₂))) := by
    rcases (hp.at_obj h₁₂.source).obj with ⟨q₁, hq₁_eq, hq₁_hom⟩
    rcases (hp.along h₁₂).2.2 with ⟨hp₁₂_mor, hp₁₂_mor_eq, _⟩
    have hp₁_un : unId ((evalTm p).obj γ₁) = q₁ := by rw [hq₁_eq, unId_idObj]
    exact j_targ_context_arrow hA h₁₂ (ha.along h₁₂) (hb.along h₁₂)
      (hp₁_un.symm ▸ hq₁_hom) (hq₁_eq.trans (congrArg Tree.idObj hp₁_un.symm))
      (hp₂_un.symm ▸ hq₂_hom) (hq₂_eq.trans (congrArg Tree.idObj hp₂_un.symm))
      hp₁₂_mor hp₁₂_mor_eq
  have hδ_targ₂₃ := j_targ_context_arrow hA h₂₃ (ha.along h₂₃) (hb.along h₂₃)
    (hp₂_un.symm ▸ hq₂_hom) (hq₂_eq.trans (congrArg Tree.idObj hp₂_un.symm))
    (hp₃_un.symm ▸ hq₃_hom) (hq₃_eq.trans (congrArg Tree.idObj hp₃_un.symm))
    hp₂₃_mor hp₂₃_mor_eq
  have h_comm₂₃ := j_comm_square hΓ hA h₂₃ (ha.along h₂₃) (hb.along h₂₃)
    (hp₂_un.symm ▸ hq₂_hom) (hp₃_un.symm ▸ hq₃_hom)
    (hq₃_eq.trans (congrArg Tree.idObj hp₃_un.symm)) hp₂₃_mor
  have hdv₁₂ := (hC.tr hδ_diag₁₂).vertical
    ⟨hd_obj_C h₁₂.source (ha.at_obj h₁₂.source).obj, hd_obj_C h₁₂.target (ha.at_obj h₁₂.target).obj, hd_hom_C h₁₂ (ha.along h₁₂)⟩
  have hdv₁₂_tr := (hC.tr hδ_diag₂₃).map_hom hdv₁₂
  have hdv₂₃ := (hC.tr hδ_diag₂₃).vertical
    ⟨hd_obj_C h₂₃.source (ha.at_obj h₂₃.source).obj, hd_obj_C h₂₃.target (ha.at_obj h₂₃.target).obj, hd_hom_C h₂₃ (ha.along h₂₃)⟩
  have h_idv₁₂ := (hC.tr hδ_targ₁₂).vertical ⟨h_idRec_obj_C h₁₂.source, h_idRec_obj_C h₁₂.target, h_idRec_hom_C h₁₂⟩
  have h_idv₁₂_tr := (hC.tr hδ_targ₂₃).map_hom h_idv₁₂
  have h_idv₂₃ := (hC.tr hδ_targ₂₃).vertical ⟨h_idRec_obj_C h₂₃.source, h_idRec_obj_C h₂₃.target, h_idRec_hom_C h₂₃⟩
  have h_cons_comp : consEnv ((evalTm a).mor γ₁ γ₃ (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃)) (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃) =
      compCtx (A :: Γ) (consEnv ((evalTm a).obj γ₁) γ₁) (consEnv ((evalTm a).obj γ₂) γ₂)
        (consEnv ((evalTm a).obj γ₃) γ₃) (consEnv ((evalTm a).mor γ₁ γ₂ δ₁₂) δ₁₂)
        (consEnv ((evalTm a).mor γ₂ γ₃ δ₂₃) δ₂₃) := by
    rw [compCtx_consEnv, ha.comp_mor h₁₂ h₂₃]
  have hd_at₃ := reflexivityMotive_atEq A C (consEnv ((evalTm a).obj γ₃) γ₃)
  have hd_al₂₃ := reflexivityMotive_alongEq A C
    (consEnv ((evalTm a).obj γ₂) γ₂) (consEnv ((evalTm a).obj γ₃) γ₃) (consEnv ((evalTm a).mor γ₂ γ₃ δ₂₃) δ₂₃)
  simp only [consEnv_zero, renEnv_succ_consEnv] at hd_at₃ hd_al₂₃
  have h_re_comm : (evalTy C).reindexMor (jDiagonal γ₃ ((evalTm a).obj γ₃))
      (jTarget γ₃ ((evalTm a).obj γ₃) ((evalTm b).obj γ₃) ((evalTm p).obj γ₃))
      (jArrow γ₃ ((evalTm a).obj γ₃) ((evalTm p).obj γ₃))
      ((evalTy C).reindexMor (jDiagonal γ₂ ((evalTm a).obj γ₂)) (jDiagonal γ₃ ((evalTm a).obj γ₃))
        (consEnv (.idObj (idVal ((evalTm a).obj γ₃))) (consEnv ((evalTm a).mor γ₂ γ₃ δ₂₃) (consEnv ((evalTm a).mor γ₂ γ₃ δ₂₃) δ₂₃)))
        ((evalTm d).mor (consEnv ((evalTm a).obj γ₁) γ₁) (consEnv ((evalTm a).obj γ₂) γ₂)
          (consEnv ((evalTm a).mor γ₁ γ₂ δ₁₂) δ₁₂))) =
    (evalTy C).reindexMor
      (jTarget γ₂ ((evalTm a).obj γ₂) ((evalTm b).obj γ₂) ((evalTm p).obj γ₂))
      (jTarget γ₃ ((evalTm a).obj γ₃) ((evalTm b).obj γ₃) ((evalTm p).obj γ₃))
      (consEnv ((evalTm p).mor γ₂ γ₃ δ₂₃) (consEnv ((evalTm b).mor γ₂ γ₃ δ₂₃) (consEnv ((evalTm a).mor γ₂ γ₃ δ₂₃) δ₂₃)))
      ((evalTm (.idRec A C d a b p)).mor γ₁ γ₂ δ₁₂) := by
    have h1 := (hC.comp_tr hδ_diag₂₃ hδ_J₃).comp_mor hdv₁₂
    have h2 := (hC.comp_tr hδ_J₂ hδ_targ₂₃).comp_mor hdv₁₂
    rw [hp₂₃_mor_eq] at h2 ⊢
    exact h1.trans (by rw [h_comm₂₃]; exact h2.symm)
  dsimp only [jTarget, jDiagonal] at h_idv₁₂ h_idv₁₂_tr h_idv₂₃ hdv₁₂ hdv₁₂_tr hdv₂₃ hδ_J₃ h_re_comm
  rw [(instantiate₃_alongEq C ha hb hp h₂₃).reindexMor h_idv₁₂,
    (instantiate₃_atEq C ha hb hp h₂₃.target).comp h_idv₁₂_tr h_idv₂₃]
  change (evalTy C).reindexMor
      (consEnv (.idObj (idVal ((evalTm a).obj γ₃))) (consEnv ((evalTm a).obj γ₃) (consEnv ((evalTm a).obj γ₃) γ₃)))
      (consEnv ((evalTm p).obj γ₃) (consEnv ((evalTm b).obj γ₃) (consEnv ((evalTm a).obj γ₃) γ₃)))
      (jArrow γ₃ ((evalTm a).obj γ₃) ((evalTm p).obj γ₃))
      ((evalTm d).mor (consEnv ((evalTm a).obj γ₁) γ₁) (consEnv ((evalTm a).obj γ₃) γ₃)
        (consEnv ((evalTm a).mor γ₁ γ₃ (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃)) (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃))) = _
  rw [h_cons_comp, hd.comp_mor (CtxHom.cons h₁₂ (ha.along h₁₂)) (CtxHom.cons h₂₃ (ha.along h₂₃)),
    hd_al₂₃.reindexMor hdv₁₂, hd_at₃.comp hdv₁₂_tr hdv₂₃,
    (hC.tr hδ_J₃).map_comp hdv₁₂_tr hdv₂₃, h_re_comm]
  rfl

theorem SemTermWf.natRec {Γ : Context} {C z s n : Expr}
    (hΓ : SemCtxWf Γ) (hC : SemTypeWf (.nat :: Γ) C)
    (hz : SemTermWf Γ z (instantiate C .zero))
    (hs : SemTermWf (C :: .nat :: Γ) s (successorMotive C))
    (hn : SemTermWf Γ n .nat) :
    SemTermWf Γ (.natRec C z s n) (instantiate C n) := by
  have hz_at : ∀ {γ} (hγ : CtxObj Γ γ),
      FamAtEq (evalTy (instantiate C .zero)) (evalTy C) γ (consEnv (.nat 0) γ) :=
    fun hγ => instantiate_atEq C (SemTermWf.zero hΓ) hγ
  have hz_al : ∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ →
      FamAlongEq (evalTy (instantiate C .zero)) (evalTy C) γ₁ γ₂ δ
        (consEnv (.nat 0) γ₁) (consEnv (.nat 0) γ₂) (consEnv (.nat 0) δ) :=
    fun hδ => instantiate_alongEq C (SemTermWf.zero hΓ) hδ
  have h_step : ∀ k,
      (∀ {γ}, CtxObj Γ γ → (evalTy C).Obj (consEnv (.nat k) γ) (natRecObj (evalTm z) (evalTm s) γ k) ∧
        natRecMor (evalTm z) (evalTm s) γ γ (idEnv γ) k = idVal (natRecObj (evalTm z) (evalTm s) γ k)) ∧
      (∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ →
        (evalTy C).Hom (consEnv (.nat k) γ₁) (consEnv (.nat k) γ₂) (consEnv (.nat k) δ)
          (natRecObj (evalTm z) (evalTm s) γ₁ k) (natRecObj (evalTm z) (evalTm s) γ₂ k)
          (natRecMor (evalTm z) (evalTm s) γ₁ γ₂ δ k)) ∧
      (∀ {γ₁ γ₂ γ₃ δ₁₂ δ₂₃}, CtxHom Γ γ₁ γ₂ δ₁₂ → CtxHom Γ γ₂ γ₃ δ₂₃ →
        natRecMor (evalTm z) (evalTm s) γ₁ γ₃ (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃) k =
          (evalTy C).comp (consEnv (.nat k) γ₃)
            ((evalTy C).reindexMor (consEnv (.nat k) γ₂) (consEnv (.nat k) γ₃) (consEnv (.nat k) δ₂₃)
              (natRecMor (evalTm z) (evalTm s) γ₁ γ₂ δ₁₂ k))
            (natRecMor (evalTm z) (evalTm s) γ₂ γ₃ δ₂₃ k)) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun hγ => ⟨(hz_at hγ).obj.mp (hz.at_obj hγ).obj, (hz.at_obj hγ).id⟩,
        fun hδ => ((hz_al hδ).hom ((hz_at hδ.source).obj.mp (hz.at_obj hδ.source).obj)
          ((hz_at hδ.target).obj.mp (hz.at_obj hδ.target).obj)).mp (hz.along hδ).2.2,
        fun {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} h₁₂ h₂₃ => ?_⟩
      have hzv₁₂ := (hC.tr (CtxHom.cons h₁₂ ⟨⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl, rfl, rfl⟩⟩)).vertical
        ⟨(hz_at h₁₂.source).obj.mp (hz.at_obj h₁₂.source).obj,
         (hz_at h₁₂.target).obj.mp (hz.at_obj h₁₂.target).obj,
         ((hz_al h₁₂).hom ((hz_at h₁₂.source).obj.mp (hz.at_obj h₁₂.source).obj)
           ((hz_at h₁₂.target).obj.mp (hz.at_obj h₁₂.target).obj)).mp (hz.along h₁₂).2.2⟩
      have hzv₁₂_tr := (hC.tr (CtxHom.cons h₂₃ ⟨⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl, rfl, rfl⟩⟩)).map_hom hzv₁₂
      have hzv₂₃ := (hC.tr (CtxHom.cons h₂₃ ⟨⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl, rfl, rfl⟩⟩)).vertical
        ⟨(hz_at h₂₃.source).obj.mp (hz.at_obj h₂₃.source).obj,
         (hz_at h₂₃.target).obj.mp (hz.at_obj h₂₃.target).obj,
         ((hz_al h₂₃).hom ((hz_at h₂₃.source).obj.mp (hz.at_obj h₂₃.source).obj)
           ((hz_at h₂₃.target).obj.mp (hz.at_obj h₂₃.target).obj)).mp (hz.along h₂₃).2.2⟩
      dsimp only [natRecMor]
      rw [hz.comp_mor h₁₂ h₂₃, (hz_al h₂₃).reindexMor hzv₁₂, (hz_at h₂₃.target).comp hzv₁₂_tr hzv₂₃]
    | succ k ih =>
      have h_obj_k : ∀ {γ}, CtxObj Γ γ →
          (evalTy C).Obj (consEnv (.nat (k + 1)) γ) (natRecObj (evalTm z) (evalTm s) γ (k + 1)) := by
        intro γ hγ
        have hγ_s : CtxObj (C :: .nat :: Γ)
            (consEnv (natRecObj (evalTm z) (evalTm s) γ k) (consEnv (.nat k) γ)) :=
          CtxObj.cons (CtxObj.cons hγ ⟨k, rfl⟩) (ih.1 hγ).1
        exact (successorMotive_atEq C (consEnv (natRecObj (evalTm z) (evalTm s) γ k) (consEnv (.nat k) γ))).obj.mp
          (hs.at_obj hγ_s).obj
      have h_id_k : ∀ {γ}, CtxObj Γ γ →
          natRecMor (evalTm z) (evalTm s) γ γ (idEnv γ) (k + 1) =
            idVal (natRecObj (evalTm z) (evalTm s) γ (k + 1)) := by
        intro γ hγ
        have hγ_s : CtxObj (C :: .nat :: Γ)
            (consEnv (natRecObj (evalTm z) (evalTm s) γ k) (consEnv (.nat k) γ)) :=
          CtxObj.cons (CtxObj.cons hγ ⟨k, rfl⟩) (ih.1 hγ).1
        dsimp only [natRecMor, natRecObj]
        rw [(ih.1 hγ).2]
        change (evalTm s).mor _ _
          (consEnv (idVal (natRecObj (evalTm z) (evalTm s) γ k)) (consEnv (idVal (.nat k)) (idEnv γ))) = _
        rw [← idEnv_consEnv, ← idEnv_consEnv]
        exact (hs.at_obj hγ_s).id
      have h_hom_k : ∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ →
          (evalTy C).Hom (consEnv (.nat (k + 1)) γ₁) (consEnv (.nat (k + 1)) γ₂) (consEnv (.nat (k + 1)) δ)
            (natRecObj (evalTm z) (evalTm s) γ₁ (k + 1)) (natRecObj (evalTm z) (evalTm s) γ₂ (k + 1))
            (natRecMor (evalTm z) (evalTm s) γ₁ γ₂ δ (k + 1)) := by
        intro γ₁ γ₂ δ hδ
        have hδ_s : CtxHom (C :: .nat :: Γ)
            (consEnv (natRecObj (evalTm z) (evalTm s) γ₁ k) (consEnv (.nat k) γ₁))
            (consEnv (natRecObj (evalTm z) (evalTm s) γ₂ k) (consEnv (.nat k) γ₂))
            (consEnv (natRecMor (evalTm z) (evalTm s) γ₁ γ₂ δ k) (consEnv (.nat k) δ)) :=
          CtxHom.cons (CtxHom.cons hδ ⟨⟨k, rfl⟩, ⟨k, rfl⟩, ⟨k, rfl, rfl, rfl⟩⟩)
            ⟨(ih.1 hδ.source).1, (ih.1 hδ.target).1, ih.2.1 hδ⟩
        have hs_al : FamAlongEq (evalTy (successorMotive C)) (evalTy C)
            (consEnv (natRecObj (evalTm z) (evalTm s) γ₁ k) (consEnv (.nat k) γ₁))
            (consEnv (natRecObj (evalTm z) (evalTm s) γ₂ k) (consEnv (.nat k) γ₂))
            (consEnv (natRecMor (evalTm z) (evalTm s) γ₁ γ₂ δ k) (consEnv (.nat k) δ))
            (consEnv (.nat (k + 1)) γ₁) (consEnv (.nat (k + 1)) γ₂) (consEnv (.nat (k + 1)) δ) :=
          successorMotive_alongEq C _ _ _
        exact (hs_al.hom (h_obj_k hδ.source) (h_obj_k hδ.target)).mp (hs.along hδ_s).2.2
      refine ⟨fun hγ => ⟨h_obj_k hγ, h_id_k hγ⟩, h_hom_k, fun {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} h₁₂ h₂₃ => ?_⟩
      have hδ₁₂_s : CtxHom (C :: .nat :: Γ)
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₁ k) (consEnv (.nat k) γ₁))
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₂ k) (consEnv (.nat k) γ₂))
          (consEnv (natRecMor (evalTm z) (evalTm s) γ₁ γ₂ δ₁₂ k) (consEnv (.nat k) δ₁₂)) :=
        CtxHom.cons (CtxHom.cons h₁₂ ⟨⟨k, rfl⟩, ⟨k, rfl⟩, ⟨k, rfl, rfl, rfl⟩⟩)
          ⟨(ih.1 h₁₂.source).1, (ih.1 h₁₂.target).1, ih.2.1 h₁₂⟩
      have hδ₂₃_s : CtxHom (C :: .nat :: Γ)
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₂ k) (consEnv (.nat k) γ₂))
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₃ k) (consEnv (.nat k) γ₃))
          (consEnv (natRecMor (evalTm z) (evalTm s) γ₂ γ₃ δ₂₃ k) (consEnv (.nat k) δ₂₃)) :=
        CtxHom.cons (CtxHom.cons h₂₃ ⟨⟨k, rfl⟩, ⟨k, rfl⟩, ⟨k, rfl, rfl, rfl⟩⟩)
          ⟨(ih.1 h₂₃.source).1, (ih.1 h₂₃.target).1, ih.2.1 h₂₃⟩
      have h_comp_s : consEnv (natRecMor (evalTm z) (evalTm s) γ₁ γ₃ (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃) k)
          (consEnv (.nat k) (compCtx Γ γ₁ γ₂ γ₃ δ₁₂ δ₂₃)) =
        compCtx (C :: .nat :: Γ)
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₁ k) (consEnv (.nat k) γ₁))
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₂ k) (consEnv (.nat k) γ₂))
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₃ k) (consEnv (.nat k) γ₃))
          (consEnv (natRecMor (evalTm z) (evalTm s) γ₁ γ₂ δ₁₂ k) (consEnv (.nat k) δ₁₂))
          (consEnv (natRecMor (evalTm z) (evalTm s) γ₂ γ₃ δ₂₃ k) (consEnv (.nat k) δ₂₃)) := by
        funext m; cases m with
        | zero =>
          dsimp only [consEnv, compCtx, renEnv_succ_consEnv]
          exact ih.2.2 h₁₂ h₂₃
        | succ m =>
          cases m with
          | zero => rfl
          | succ m => rfl
      have hs_at₃ : FamAtEq (evalTy (successorMotive C)) (evalTy C)
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₃ k) (consEnv (.nat k) γ₃))
          (consEnv (.nat (k + 1)) γ₃) :=
        successorMotive_atEq C _
      have hs_al₂₃ : FamAlongEq (evalTy (successorMotive C)) (evalTy C)
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₂ k) (consEnv (.nat k) γ₂))
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₃ k) (consEnv (.nat k) γ₃))
          (consEnv (natRecMor (evalTm z) (evalTm s) γ₂ γ₃ δ₂₃ k) (consEnv (.nat k) δ₂₃))
          (consEnv (.nat (k + 1)) γ₂) (consEnv (.nat (k + 1)) γ₃) (consEnv (.nat (k + 1)) δ₂₃) :=
        successorMotive_alongEq C _ _ _
      have hsv₁₂ := (hC.tr (CtxHom.cons h₁₂ ⟨⟨k + 1, rfl⟩, ⟨k + 1, rfl⟩, ⟨k + 1, rfl, rfl, rfl⟩⟩)).vertical
        ⟨h_obj_k h₁₂.source, h_obj_k h₁₂.target, h_hom_k h₁₂⟩
      have hsv₁₂_tr := (hC.tr (CtxHom.cons h₂₃ ⟨⟨k + 1, rfl⟩, ⟨k + 1, rfl⟩, ⟨k + 1, rfl, rfl, rfl⟩⟩)).map_hom hsv₁₂
      have hsv₂₃ := (hC.tr (CtxHom.cons h₂₃ ⟨⟨k + 1, rfl⟩, ⟨k + 1, rfl⟩, ⟨k + 1, rfl, rfl, rfl⟩⟩)).vertical
        ⟨h_obj_k h₂₃.source, h_obj_k h₂₃.target, h_hom_k h₂₃⟩
      dsimp only [natRecMor] at hsv₁₂ hsv₁₂_tr hsv₂₃ ⊢
      rw [h_comp_s, hs.comp_mor hδ₁₂_s hδ₂₃_s, hs_al₂₃.reindexMor hsv₁₂, hs_at₃.comp hsv₁₂_tr hsv₂₃]
  refine SemTermWf.mk_of ⟨⟨hC.good.1, hz.good.1, hs.good.1, hn.good.1⟩, trivial⟩
    (fun {γ} hγ => by
      rcases (hn.at_obj hγ).obj with ⟨k, hk⟩
      have h_at := instantiate_atEq C hn hγ
      dsimp only [evalTm, eval]
      rw [hk] at h_at ⊢
      exact h_at.obj.mpr ((h_step k).1 hγ).1)
    (fun {γ} hγ => by
      rcases (hn.at_obj hγ).obj with ⟨k, hk⟩
      dsimp only [evalTm, eval]
      rw [hk]
      exact ((h_step k).1 hγ).2)
    (fun {γ₁ γ₂ δ} hδ => by
      rcases (hn.along hδ).2.2 with ⟨k, h1, h2, hm⟩
      have h_al := instantiate_alongEq C hn hδ
      have ho₁ := ((h_step k).1 hδ.source).1
      have ho₂ := ((h_step k).1 hδ.target).1
      dsimp only [evalTm, eval]
      rw [h1, h2, hm] at h_al
      rw [h1, h2]
      exact (h_al.hom ho₁ ho₂).mpr ((h_step k).2.1 hδ))
    (fun {γ₁ γ₂ γ₃ δ₁₂ δ₂₃} h₁₂ h₂₃ => ?_)
  rcases (hn.along h₁₂).2.2 with ⟨k, h1, h2, hm₁₂⟩
  rcases (hn.along h₂₃).2.2 with ⟨k', h2', h3, hm₂₃⟩
  have hk_eq := h2.symm.trans h2'
  cases hk_eq
  have h_al₂₃ := instantiate_alongEq C hn h₂₃
  have h_at₃ := instantiate_atEq C hn h₂₃.target
  have ho₁ := ((h_step k).1 h₁₂.source).1
  have ho₂ := ((h_step k).1 h₁₂.target).1
  have ho₃ := ((h_step k).1 h₂₃.target).1
  have hv₁₂ := (hC.tr (CtxHom.cons h₁₂ ⟨⟨k, rfl⟩, ⟨k, rfl⟩, ⟨k, rfl, rfl, rfl⟩⟩)).vertical
    ⟨ho₁, ho₂, (h_step k).2.1 h₁₂⟩
  have hv₁₂_tr := (hC.tr (CtxHom.cons h₂₃ ⟨⟨k, rfl⟩, ⟨k, rfl⟩, ⟨k, rfl, rfl, rfl⟩⟩)).map_hom hv₁₂
  have hv₂₃ := (hC.tr (CtxHom.cons h₂₃ ⟨⟨k, rfl⟩, ⟨k, rfl⟩, ⟨k, rfl, rfl, rfl⟩⟩)).vertical
    ⟨ho₂, ho₃, (h_step k).2.1 h₂₃⟩
  dsimp only [evalTm, eval]
  rw [h2, h3, hm₂₃] at h_al₂₃
  rw [h3] at h_at₃
  rw [h2, h3]
  dsimp only [unNat]
  rw [h_al₂₃.reindexMor hv₁₂, h_at₃.comp hv₁₂_tr hv₂₃]
  exact (h_step k).2.2 h₁₂ h₂₃

end HofmannStreicher1994.Repaired

/-! ## SemTermEqConstructors.lean -/

namespace HofmannStreicher1994.Repaired

theorem SemTermWf.conv {Γ : Context} {a A B : Expr}
    (ha : SemTermWf Γ a A) (hAB : SemTypeEq Γ A B) :
    SemTermWf Γ a B :=
  SemTermWf.conv_eq hAB.ctx hAB.wf_left ha
    (fun hγ => (hAB.at_eq hγ).symm)
    (fun hδ => (hAB.along_eq hδ).symm (hAB.at_eq hδ.source) (hAB.at_eq hδ.target))

theorem SemTermEq.refl {Γ : Context} {a A : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (ha : SemTermWf Γ a A) :
    SemTermEq Γ a a A where
  ctx := hΓ
  wf_A := hA
  wf_left := ha
  wf_right := ha
  obj_eq _ := rfl
  mor_eq _ := rfl

theorem SemTermEq.conv {Γ : Context} {a b A B : Expr}
    (hab : SemTermEq Γ a b A) (hAB : SemTypeEq Γ A B) :
    SemTermEq Γ a b B where
  ctx := hab.ctx
  wf_A := hAB.wf_right
  wf_left := SemTermWf.conv hab.wf_left hAB
  wf_right := SemTermWf.conv hab.wf_right hAB
  obj_eq := hab.obj_eq
  mor_eq := hab.mor_eq

theorem SemTermEq.succ {Γ : Context} {n n' : Expr}
    (hn : SemTermEq Γ n n' .nat) :
    SemTermEq Γ (.succ n) (.succ n') .nat :=
  SemTermEq.of_left hn.ctx hn.wf_A (SemTermWf.succ hn.wf_left)
    ⟨hn.wf_right.good.1, trivial⟩
    (fun hγ => by dsimp only [evalTm, eval]; rw [hn.obj_eq hγ])
    (fun hδ => by dsimp only [evalTm, eval]; rw [hn.obj_eq hδ.target])

theorem SemTermEq.reflCongr {Γ : Context} {A A' a a' : Expr}
    (hA : SemTypeEq Γ A A') (ha : SemTermEq Γ a a' A) :
    SemTermEq Γ (.refl A a) (.refl A' a') (.identity A a a) :=
  SemTermEq.of_left hA.ctx (SemTypeWf.identity hA.wf_left ha.wf_left ha.wf_left)
    (SemTermWf.refl hA.ctx hA.wf_left ha.wf_left)
    ⟨⟨hA.wf_right.good.1, ha.wf_right.good.1⟩, trivial⟩
    (fun hγ => by dsimp only [evalTm, eval]; rw [ha.obj_eq hγ])
    (fun hδ => by dsimp only [evalTm, eval]; rw [ha.obj_eq hδ.target])

theorem SemTermEq.pair {Γ : Context} {A A' B B' a a' b b' : Expr}
    (hA : SemTypeEq Γ A A') (hB : SemTypeEq (A :: Γ) B B')
    (ha : SemTermEq Γ a a' A) (hb : SemTermEq Γ b b' (instantiate B a)) :
    SemTermEq Γ (.pair A B a b) (.pair A' B' a' b') (.sigma A B) :=
  SemTermEq.of_left hA.ctx (SemTypeWf.sigma hA.ctx hA.wf_left hB.wf_left)
    (SemTermWf.pair hA.ctx hA.wf_left hB.wf_left ha.wf_left hb.wf_left)
    ⟨⟨hA.wf_right.good.1, hB.wf_right.good.1, ha.wf_right.good.1, hb.wf_right.good.1⟩, trivial⟩
    (fun hγ => by dsimp only [evalTm, eval]; rw [ha.obj_eq hγ, hb.obj_eq hγ])
    (fun hδ => by
      have ha₁' := (hA.at_eq hδ.source).obj.mp (ha.wf_left.at_obj hδ.source).obj
      have h_ro := (hA.along_eq hδ).reindexObj ha₁'
      dsimp only [evalTy, evalTm] at h_ro
      dsimp only [evalTm, eval]
      rw [h_ro, ha.obj_eq hδ.source, ha.obj_eq hδ.target, ha.mor_eq hδ, hb.mor_eq hδ])

theorem SemTermEq.sigmaRec {Γ : Context} {A A' B B' C C' d d' p p' : Expr}
    (hA : SemTypeEq Γ A A') (hB : SemTypeEq (A :: Γ) B B')
    (hC : SemTypeEq (.sigma A B :: Γ) C C')
    (hd : SemTermEq (B :: A :: Γ) d d' (pairingMotive A B C))
    (hp : SemTermEq Γ p p' (.sigma A B)) :
    SemTermEq Γ (.sigmaRec A B C d p) (.sigmaRec A' B' C' d' p') (instantiate C p) :=
  SemTermEq.of_left hA.ctx (SemTypeWf.instantiate hA.ctx hC.wf_left hp.wf_left)
    (SemTermWf.sigmaRec hA.ctx hA.wf_left hB.wf_left hC.wf_left hd.wf_left hp.wf_left)
    ⟨⟨hA.wf_right.good.1, hB.wf_right.good.1, hC.wf_right.good.1,
      hd.wf_right.good.1, hp.wf_right.good.1⟩, trivial⟩
    (fun hγ => by
      rcases (hp.wf_left.at_obj hγ).obj with ⟨x, y, hp_eq, hx, hy⟩
      dsimp only [evalTm, eval]
      rw [← hp.obj_eq hγ, hp_eq, sigFst_pairObj, sigSnd_pairObj]
      exact hd.obj_eq (CtxObj.cons (CtxObj.cons hγ hx) hy))
    (fun hδ => by
      rcases (hp.wf_left.along hδ).2.2 with ⟨x₁, y₁, x₂, y₂, pm, qm, hp₁_eq, hp₂_eq, hpm_eq,
        hx₁, hx₂, hy₁, hy₂, hpm, hqm⟩
      dsimp only [evalTm, eval]
      rw [← hp.obj_eq hδ.source, ← hp.obj_eq hδ.target, ← hp.mor_eq hδ,
        hp₁_eq, hp₂_eq, hpm_eq, sigFst_pairObj, sigSnd_pairObj,
        sigFst_pairObj, sigSnd_pairObj, sigMorP_pairMor, sigMorQ_pairMor]
      exact hd.mor_eq (CtxHom.cons (CtxHom.cons hδ ⟨hx₁, hx₂, hpm⟩) ⟨hy₁, hy₂, hqm⟩))

theorem SemTermEq.lam {Γ : Context} {A A' B b b' : Expr}
    (hA : SemTypeEq Γ A A') (hB : SemTypeWf (A :: Γ) B)
    (hb : SemTermEq (A :: Γ) b b' B) :
    SemTermEq Γ (.lam A b) (.lam A' b') (.pi A B) :=
  SemTermEq.of_left hA.ctx (SemTypeWf.pi hA.ctx hA.wf_left hB)
    (SemTermWf.lam hA.ctx hA.wf_left hB hb.wf_left)
    ⟨⟨hA.wf_right.good.1, hb.wf_right.good.1⟩, trivial⟩
    (fun hγ => by
      have h_lvl := hA.lvl_eq
      dsimp only [evalTy] at h_lvl
      dsimp only [evalTm, eval]
      rw [← h_lvl]
      exact mkPiObj_ext (fun _ => (hA.at_eq hγ).obj) (fun x y p => (hA.piDomMor_iff hγ x y p).symm)
        (fun x hx => hb.obj_eq (CtxObj.cons hγ hx))
        (fun x y p hp => hb.mor_eq (CtxHom.cons (hA.ctx.id_hom hγ) hp)))
    (fun {γ₁ γ₂ δ} hδ => by
      have h_lvl := hA.lvl_eq
      dsimp only [evalTy] at h_lvl
      dsimp only [evalTm, eval]
      rw [← h_lvl]
      refine mkPiMor_ext (fun x y p => (hA.piDomMor_iff hδ.target x y p).symm) (fun x' y p hp => ?_)
      have hx' := (hA.at_eq hδ.target).obj.mp hp.1
      have h_uro := (hA.along_eq hδ).unreindexObj hx'
      dsimp only [evalTy] at h_uro
      rw [← h_uro]
      have hx₁ := (hA.wf_left.tr hδ).unmap_obj hp.1
      have hp_hom : (evalTy A).Hom γ₁ γ₂ δ ((evalTy A).unreindexObj γ₁ γ₂ δ x') y p := by
        refine ((hA.wf_left.tr hδ).hom_iff hx₁ hp.2.1).mpr ?_
        rw [(hA.wf_left.tr hδ).map_unmap_obj hp.1]
        exact hp.2.2
      exact hb.mor_eq (CtxHom.cons hδ ⟨hx₁, hp.2.1, hp_hom⟩))

theorem SemTermEq.app {Γ : Context} {A A' B B' f f' a a' : Expr}
    (hA : SemTypeEq Γ A A') (hB : SemTypeEq (A :: Γ) B B')
    (hf : SemTermEq Γ f f' (.pi A B)) (ha : SemTermEq Γ a a' A) :
    SemTermEq Γ (.app A B f a) (.app A' B' f' a') (instantiate B a) :=
  SemTermEq.of_left hA.ctx (SemTypeWf.instantiate hA.ctx hB.wf_left ha.wf_left)
    (SemTermWf.app hA.ctx hA.wf_left hB.wf_left hf.wf_left ha.wf_left)
    ⟨⟨hA.wf_right.good.1, hB.wf_right.good.1, hf.wf_right.good.1, ha.wf_right.good.1⟩, trivial⟩
    (fun hγ => by dsimp only [evalTm, eval]; rw [hf.obj_eq hγ, ha.obj_eq hγ])
    (fun hδ => by
      have ha₁' := (hA.at_eq hδ.source).obj.mp (ha.wf_left.at_obj hδ.source).obj
      have h_ro := (hA.along_eq hδ).reindexObj ha₁'
      dsimp only [evalTy, evalTm] at h_ro
      dsimp only [evalTm, eval]
      rw [hf.mor_eq hδ, h_ro, ha.obj_eq hδ.source, ha.obj_eq hδ.target, ha.mor_eq hδ])

theorem SemTermEq.idRec {Γ : Context} {A A' C C' d d' a a' b b' p p' : Expr}
    (hA : SemTypeEq Γ A A') (hC : SemTypeEq (identityContext Γ A) C C')
    (hd : SemTermEq (A :: Γ) d d' (reflexivityMotive A C))
    (ha : SemTermEq Γ a a' A) (hb : SemTermEq Γ b b' A)
    (hp : SemTermEq Γ p p' (.identity A a b)) :
    SemTermEq Γ (.idRec A C d a b p) (.idRec A' C' d' a' b' p') (instantiate₃ C a b p) := by
  have hd_obj_C : ∀ {γ} (hγ : CtxObj Γ γ) {x} (hx : (evalTy A).Obj γ x),
      (evalTy C).Obj (jDiagonal γ x) ((evalTm d).obj (consEnv x γ)) :=
    fun {γ} hγ {x} hx => (reflexivityMotive_atEq A C (consEnv x γ)).obj.mp
      (hd.wf_left.at_obj (CtxObj.cons hγ hx)).obj
  have hd_hom_C : ∀ {γ₁ γ₂ δ} (hδ : CtxHom Γ γ₁ γ₂ δ)
      {x₁ x₂ xm} (hx : piHetMor (evalTy A) γ₁ γ₂ δ x₁ x₂ xm),
      (evalTy C).Hom (jDiagonal γ₁ x₁) (jDiagonal γ₂ x₂)
        (consEnv (.idObj (idVal x₂)) (consEnv xm (consEnv xm δ)))
        ((evalTm d).obj (consEnv x₁ γ₁)) ((evalTm d).obj (consEnv x₂ γ₂))
        ((evalTm d).mor (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv xm δ)) :=
    fun {γ₁ γ₂ δ} hδ {x₁ x₂ xm} hx =>
      ((reflexivityMotive_alongEq A C (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv xm δ)).hom
        (hd_obj_C hδ.source hx.1) (hd_obj_C hδ.target hx.2.1)).mp
        (hd.wf_left.along (CtxHom.cons hδ hx)).2.2
  refine SemTermEq.of_left hA.ctx
    (SemTypeWf.instantiate₃ hA.ctx hC.wf_left ha.wf_left hb.wf_left hp.wf_left)
    (SemTermWf.idRec hA.ctx hA.wf_left hC.wf_left hd.wf_left ha.wf_left hb.wf_left hp.wf_left)
    ⟨⟨hA.wf_right.good.1, hC.wf_right.good.1, hd.wf_right.good.1,
      ha.wf_right.good.1, hb.wf_right.good.1, hp.wf_right.good.1⟩, trivial⟩
    (fun {γ} hγ => ?_) (fun {γ₁ γ₂ δ} hδ => ?_)
  · rcases (hp.wf_left.at_obj hγ).obj with ⟨q, hq_eq, hq_hom⟩
    have hδ_J : CtxHom (identityContext Γ A) (jDiagonal γ ((evalTm a).obj γ))
        (jTarget γ ((evalTm a).obj γ) ((evalTm b).obj γ) ((evalTm p).obj γ))
        (jArrow γ ((evalTm a).obj γ) ((evalTm p).obj γ)) := by
      rw [hq_eq]
      exact j_context_arrow (hA.ctx.id_hom hγ) (hA.wf_left.fiber hγ) (hA.wf_left.id_tr hγ)
        ⟨(ha.wf_left.at_obj hγ).obj, (hb.wf_left.at_obj hγ).obj, hq_hom⟩
    have h_ro := (hC.along_eq hδ_J).reindexObj
      ((hC.at_eq hδ_J.source).obj.mp (hd_obj_C hγ (ha.wf_left.at_obj hγ).obj))
    dsimp only [jDiagonal, jTarget, jArrow, evalTy, evalTm] at h_ro
    dsimp only [evalTm, eval]
    rw [h_ro, ← ha.obj_eq hγ, ← hb.obj_eq hγ, ← hp.obj_eq hγ,
      hd.obj_eq (CtxObj.cons hγ (ha.wf_left.at_obj hγ).obj)]
  · rcases (hp.wf_left.at_obj hδ.target).obj with ⟨q₂, hq₂_eq, hq₂_hom⟩
    have hδ_J₂ : CtxHom (identityContext Γ A) (jDiagonal γ₂ ((evalTm a).obj γ₂))
        (jTarget γ₂ ((evalTm a).obj γ₂) ((evalTm b).obj γ₂) ((evalTm p).obj γ₂))
        (jArrow γ₂ ((evalTm a).obj γ₂) ((evalTm p).obj γ₂)) := by
      rw [hq₂_eq]
      exact j_context_arrow (hA.ctx.id_hom hδ.target) (hA.wf_left.fiber hδ.target) (hA.wf_left.id_tr hδ.target)
        ⟨(ha.wf_left.at_obj hδ.target).obj, (hb.wf_left.at_obj hδ.target).obj, hq₂_hom⟩
    have hδ_diag := j_diag_context_arrow hA.wf_left hδ (ha.wf_left.along hδ)
    have hdv := (hC.wf_left.tr hδ_diag).vertical
      ⟨hd_obj_C hδ.source (ha.wf_left.at_obj hδ.source).obj,
       hd_obj_C hδ.target (ha.wf_left.at_obj hδ.target).obj,
       hd_hom_C hδ (ha.wf_left.along hδ)⟩
    have h_rm := (hC.along_eq hδ_J₂).reindexMor ((hC.at_eq hδ_J₂.source).fiberHom_iff.mp hdv)
    dsimp only [jDiagonal, jTarget, jArrow, evalTy, evalTm] at h_rm
    dsimp only [evalTm, eval]
    rw [h_rm, ← ha.obj_eq hδ.source, ← ha.obj_eq hδ.target, ← hb.obj_eq hδ.target,
      ← hp.obj_eq hδ.target, ← ha.mor_eq hδ, hd.mor_eq (CtxHom.cons hδ (ha.wf_left.along hδ))]

theorem SemTermEq.natRec {Γ : Context} {C C' z z' s s' n n' : Expr}
    (hC : SemTypeEq (.nat :: Γ) C C')
    (hz : SemTermEq Γ z z' (instantiate C .zero))
    (hs : SemTermEq (C :: .nat :: Γ) s s' (successorMotive C))
    (hn : SemTermEq Γ n n' .nat) :
    SemTermEq Γ (.natRec C z s n) (.natRec C' z' s' n') (instantiate C n) := by
  have hΓ := hn.ctx
  have h_step : ∀ k,
      (∀ {γ}, CtxObj Γ γ →
        (evalTy C).Obj (consEnv (.nat k) γ) (natRecObj (evalTm z) (evalTm s) γ k) ∧
        natRecObj (evalTm z) (evalTm s) γ k = natRecObj (evalTm z') (evalTm s') γ k) ∧
      (∀ {γ₁ γ₂ δ}, CtxHom Γ γ₁ γ₂ δ →
        (evalTy C).Hom (consEnv (.nat k) γ₁) (consEnv (.nat k) γ₂) (consEnv (.nat k) δ)
          (natRecObj (evalTm z) (evalTm s) γ₁ k) (natRecObj (evalTm z) (evalTm s) γ₂ k)
          (natRecMor (evalTm z) (evalTm s) γ₁ γ₂ δ k) ∧
        natRecMor (evalTm z) (evalTm s) γ₁ γ₂ δ k = natRecMor (evalTm z') (evalTm s') γ₁ γ₂ δ k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun hγ => ⟨(instantiate_atEq C (SemTermWf.zero hΓ) hγ).obj.mp (hz.wf_left.at_obj hγ).obj, hz.obj_eq hγ⟩,
        fun hδ => ⟨((instantiate_alongEq C (SemTermWf.zero hΓ) hδ).hom
          ((instantiate_atEq C (SemTermWf.zero hΓ) hδ.source).obj.mp (hz.wf_left.at_obj hδ.source).obj)
          ((instantiate_atEq C (SemTermWf.zero hΓ) hδ.target).obj.mp (hz.wf_left.at_obj hδ.target).obj)).mp
          (hz.wf_left.along hδ).2.2, hz.mor_eq hδ⟩⟩
    | succ k ih =>
      have h_obj_k : ∀ {γ}, CtxObj Γ γ →
          (evalTy C).Obj (consEnv (.nat (k + 1)) γ) (natRecObj (evalTm z) (evalTm s) γ (k + 1)) ∧
          natRecObj (evalTm z) (evalTm s) γ (k + 1) = natRecObj (evalTm z') (evalTm s') γ (k + 1) := by
        intro γ hγ
        have hγ_s : CtxObj (C :: .nat :: Γ)
            (consEnv (natRecObj (evalTm z) (evalTm s) γ k) (consEnv (.nat k) γ)) :=
          CtxObj.cons (CtxObj.cons hγ ⟨k, rfl⟩) (ih.1 hγ).1
        refine ⟨(successorMotive_atEq C _).obj.mp (hs.wf_left.at_obj hγ_s).obj, ?_⟩
        dsimp only [natRecObj]
        rw [← (ih.1 hγ).2]
        exact hs.obj_eq hγ_s
      refine ⟨h_obj_k, fun {γ₁ γ₂ δ} hδ => ?_⟩
      have hδ_s : CtxHom (C :: .nat :: Γ)
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₁ k) (consEnv (.nat k) γ₁))
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₂ k) (consEnv (.nat k) γ₂))
          (consEnv (natRecMor (evalTm z) (evalTm s) γ₁ γ₂ δ k) (consEnv (.nat k) δ)) :=
        CtxHom.cons (CtxHom.cons hδ ⟨⟨k, rfl⟩, ⟨k, rfl⟩, ⟨k, rfl, rfl, rfl⟩⟩)
          ⟨(ih.1 hδ.source).1, (ih.1 hδ.target).1, (ih.2 hδ).1⟩
      have hs_al : FamAlongEq (evalTy (successorMotive C)) (evalTy C)
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₁ k) (consEnv (.nat k) γ₁))
          (consEnv (natRecObj (evalTm z) (evalTm s) γ₂ k) (consEnv (.nat k) γ₂))
          (consEnv (natRecMor (evalTm z) (evalTm s) γ₁ γ₂ δ k) (consEnv (.nat k) δ))
          (consEnv (.nat (k + 1)) γ₁) (consEnv (.nat (k + 1)) γ₂) (consEnv (.nat (k + 1)) δ) :=
        successorMotive_alongEq C _ _ _
      refine ⟨(hs_al.hom (h_obj_k hδ.source).1 (h_obj_k hδ.target).1).mp (hs.wf_left.along hδ_s).2.2, ?_⟩
      dsimp only [natRecMor]
      rw [← (ih.1 hδ.source).2, ← (ih.1 hδ.target).2, ← (ih.2 hδ).2]
      exact hs.mor_eq hδ_s
  refine SemTermEq.of_left hΓ (SemTypeWf.instantiate hΓ hC.wf_left hn.wf_left)
    (SemTermWf.natRec hΓ hC.wf_left hz.wf_left hs.wf_left hn.wf_left)
    ⟨⟨hC.wf_right.good.1, hz.wf_right.good.1, hs.wf_right.good.1, hn.wf_right.good.1⟩, trivial⟩
    (fun {γ} hγ => by
      rcases (hn.wf_left.at_obj hγ).obj with ⟨k, hk⟩
      dsimp only [evalTm, eval]
      rw [← hn.obj_eq hγ, hk]
      exact ((h_step k).1 hγ).2)
    (fun {γ₁ γ₂ δ} hδ => by
      rcases (hn.wf_left.at_obj hδ.target).obj with ⟨k, hk⟩
      dsimp only [evalTm, eval]
      rw [← hn.obj_eq hδ.target, hk]
      exact ((h_step k).2 hδ).2)

theorem SemTermEq.betaPi {Γ : Context} {A B b a : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B)
    (hb : SemTermWf (A :: Γ) b B) (ha : SemTermWf Γ a A) :
    SemTermEq Γ (.app A B (.lam A b) a) (instantiate b a) (instantiate B a) :=
  SemTermEq.of_left hΓ (SemTypeWf.instantiate hΓ hB ha)
    (SemTermWf.app hΓ hA hB (SemTermWf.lam hΓ hA hB hb) ha)
    (hb.good.instantiate ha.good)
    (fun {γ} hγ => by
      rw [evalTm_instantiate_obj b a γ (evalTy_of_isTm ha.good.2) (ha.at_obj hγ).id]
      dsimp only [evalTm, eval]
      exact piAppObj_mkPiObj_of_rk (hA.rank hγ) (ha.at_obj hγ).obj)
    (fun {γ₁ γ₂ δ} hδ => by
      rw [evalTm_instantiate_mor b ha hδ]
      have hav := (hA.tr hδ).vertical (ha.along hδ)
      dsimp only [evalTm, eval]
      rw [piMorAt_mkPiMor_of_rk (hA.rank hδ.target) hav,
        (hA.tr hδ).unmap_map_obj (ha.at_obj hδ.source).obj])

theorem SemTermEq.etaPi {Γ : Context} {A B f : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B)
    (hf : SemTermWf Γ f (.pi A B)) :
    SemTermEq Γ (.lam A (.app (HofmannStreicher1994.weaken A) (rename (liftRenaming Nat.succ) B)
      (HofmannStreicher1994.weaken f) (.var 0))) f (.pi A B) := by
  have hρ : RenScope Γ.length (Γ.length + 1) Nat.succ := fun _ hn => Nat.succ_lt_succ hn
  have hgood_lhs : GoodTerm Γ.length (.lam A (.app (HofmannStreicher1994.weaken A)
      (rename (liftRenaming Nat.succ) B) (HofmannStreicher1994.weaken f) (.var 0))) :=
    ⟨⟨hA.good.1, hA.good.1.weaken, hB.good.1.rename hρ.lift, hf.good.1.weaken, Nat.zero_lt_succ _⟩, trivial⟩
  refine (SemTermEq.of_left hΓ (SemTypeWf.pi hΓ hA hB) hf hgood_lhs
    (fun {γ} hγ => ?_) (fun {γ₁ γ₂ δ} hδ => ?_)).symm
  · have hfo := (hf.at_obj hγ).obj
    have hfi := (hf.at_obj hγ).id
    dsimp only [evalTm, eval]
    refine hfo.1.trans (mkPiObj_ext (fun _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
      (fun x _ => ?_) (fun x y p hp => ?_))
    · rw [show (eval (HofmannStreicher1994.weaken f)).2 = evalTm (HofmannStreicher1994.weaken f) from rfl,
        HofmannStreicher1994.weaken, evalTm_rename]
      rfl
    · rw [show (eval (HofmannStreicher1994.weaken f)).2 = evalTm (HofmannStreicher1994.weaken f) from rfl,
        eval_fst_weaken, HofmannStreicher1994.weaken, evalTm_rename]
      dsimp only [renameTm, renameFam, consEnv]
      rw [renEnv_succ_consEnv, renEnv_succ_consEnv, renEnv_succ_consEnv,
        (hA.id_tr hγ).obj hp.1, hfi, semPi_id_components hfo]
  · have hfm := (hf.along hδ).2.2
    dsimp only [evalTm, eval]
    refine hfm.1.trans (mkPiMor_ext (fun _ _ _ => Iff.rfl) (fun x' y p hp => ?_))
    rw [show (eval (HofmannStreicher1994.weaken f)).2 = evalTm (HofmannStreicher1994.weaken f) from rfl,
      eval_fst_weaken, HofmannStreicher1994.weaken, evalTm_rename]
    dsimp only [renameTm, renameFam, consEnv]
    rw [renEnv_succ_consEnv, renEnv_succ_consEnv, renEnv_succ_consEnv,
      (hA.tr hδ).map_unmap_obj hp.1]

theorem SemTermEq.betaSigma {Γ : Context} {A B C d a b : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hB : SemTypeWf (A :: Γ) B)
    (hC : SemTypeWf (.sigma A B :: Γ) C)
    (hd : SemTermWf (B :: A :: Γ) d (pairingMotive A B C))
    (ha : SemTermWf Γ a A) (hb : SemTermWf Γ b (instantiate B a)) :
    SemTermEq Γ (.sigmaRec A B C d (.pair A B a b)) (instantiate₂ d a b)
      (instantiate C (.pair A B a b)) :=
  SemTermEq.of_left hΓ (SemTypeWf.instantiate hΓ hC (SemTermWf.pair hΓ hA hB ha hb))
    (SemTermWf.sigmaRec hΓ hA hB hC hd (SemTermWf.pair hΓ hA hB ha hb))
    (hd.good.instantiate₂ ha.good hb.good)
    (fun {γ} hγ => by
      rw [evalTm_instantiate₂_obj d a b γ (evalTy_of_isTm ha.good.2) (evalTy_of_isTm hb.good.2)
        (ha.at_obj hγ).id (hb.at_obj hγ).id]
      rfl)
    (fun {γ₁ γ₂ δ} hδ => by
      rw [evalTm_instantiate₂_mor d ha hb hδ]
      rfl)

theorem SemTermEq.betaId {Γ : Context} {A C d a : Expr}
    (hΓ : SemCtxWf Γ) (hA : SemTypeWf Γ A) (hC : SemTypeWf (identityContext Γ A) C)
    (hd : SemTermWf (A :: Γ) d (reflexivityMotive A C)) (ha : SemTermWf Γ a A) :
    SemTermEq Γ (.idRec A C d a a (.refl A a)) (instantiate d a)
      (instantiate₃ C a a (.refl A a)) := by
  have hd_obj_C : ∀ {γ} (hγ : CtxObj Γ γ) {x} (hx : (evalTy A).Obj γ x),
      (evalTy C).Obj (jDiagonal γ x) ((evalTm d).obj (consEnv x γ)) :=
    fun {γ} hγ {x} hx => (reflexivityMotive_atEq A C (consEnv x γ)).obj.mp
      (hd.at_obj (CtxObj.cons hγ hx)).obj
  have hd_hom_C : ∀ {γ₁ γ₂ δ} (hδ : CtxHom Γ γ₁ γ₂ δ)
      {x₁ x₂ xm} (hx : piHetMor (evalTy A) γ₁ γ₂ δ x₁ x₂ xm),
      (evalTy C).Hom (jDiagonal γ₁ x₁) (jDiagonal γ₂ x₂)
        (consEnv (.idObj (idVal x₂)) (consEnv xm (consEnv xm δ)))
        ((evalTm d).obj (consEnv x₁ γ₁)) ((evalTm d).obj (consEnv x₂ γ₂))
        ((evalTm d).mor (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv xm δ)) :=
    fun {γ₁ γ₂ δ} hδ {x₁ x₂ xm} hx =>
      ((reflexivityMotive_alongEq A C (consEnv x₁ γ₁) (consEnv x₂ γ₂) (consEnv xm δ)).hom
        (hd_obj_C hδ.source hx.1) (hd_obj_C hδ.target hx.2.1)).mp
        (hd.along (CtxHom.cons hδ hx)).2.2
  refine SemTermEq.of_left hΓ
    (SemTypeWf.instantiate₃ hΓ hC ha ha (SemTermWf.refl hΓ hA ha))
    (SemTermWf.idRec hΓ hA hC hd ha ha (SemTermWf.refl hΓ hA ha))
    (hd.good.instantiate ha.good)
    (fun {γ} hγ => ?_) (fun {γ₁ γ₂ δ} hδ => ?_)
  · have hδ_diag := j_diag_context_arrow hA (hΓ.id_hom hγ) (ha.along (hΓ.id_hom hγ))
    exact eval_betaId_obj ha.good.2 (ha.at_obj hγ).id
      (hd_obj_C hγ (ha.at_obj hγ).obj) (hC.id_tr hδ_diag.source)
  · rw [evalTm_instantiate_mor d ha hδ]
    have hδ_diag := j_diag_context_arrow hA hδ (ha.along hδ)
    have hdv := (hC.tr hδ_diag).vertical
      ⟨hd_obj_C hδ.source (ha.at_obj hδ.source).obj,
       hd_obj_C hδ.target (ha.at_obj hδ.target).obj,
       hd_hom_C hδ (ha.along hδ)⟩
    have h_id_mor := (hC.id_tr hδ_diag.target).mor hdv
    dsimp only [jDiagonal, evalTy, evalTm] at h_id_mor
    rw [idEnv_consEnv, idEnv_consEnv, idEnv_consEnv] at h_id_mor
    exact h_id_mor

theorem SemTermEq.betaNatZero {Γ : Context} {C z s : Expr}
    (hΓ : SemCtxWf Γ) (hC : SemTypeWf (.nat :: Γ) C)
    (hz : SemTermWf Γ z (instantiate C .zero))
    (hs : SemTermWf (C :: .nat :: Γ) s (successorMotive C)) :
    SemTermEq Γ (.natRec C z s .zero) z (instantiate C .zero) :=
  SemTermEq.of_left hΓ (SemTypeWf.instantiate hΓ hC (SemTermWf.zero hΓ))
    (SemTermWf.natRec hΓ hC hz hs (SemTermWf.zero hΓ)) hz.good
    (fun _ => rfl) (fun _ => rfl)

theorem SemTermEq.betaNatSucc {Γ : Context} {C z s n : Expr}
    (hΓ : SemCtxWf Γ) (hC : SemTypeWf (.nat :: Γ) C)
    (hz : SemTermWf Γ z (instantiate C .zero))
    (hs : SemTermWf (C :: .nat :: Γ) s (successorMotive C))
    (hn : SemTermWf Γ n .nat) :
    SemTermEq Γ (.natRec C z s (.succ n)) (instantiate₂ s n (.natRec C z s n))
      (instantiate C (.succ n)) := by
  have hnr := SemTermWf.natRec hΓ hC hz hs hn
  refine SemTermEq.of_left hΓ (SemTypeWf.instantiate hΓ hC (SemTermWf.succ hn))
    (SemTermWf.natRec hΓ hC hz hs (SemTermWf.succ hn))
    (hs.good.instantiate₂ hn.good hnr.good)
    (fun {γ} hγ => ?_) (fun {γ₁ γ₂ δ} hδ => ?_)
  · rw [evalTm_instantiate₂_obj s n (.natRec C z s n) γ
      (evalTy_of_isTm hn.good.2) (evalTy_of_isTm hnr.good.2)
      (hn.at_obj hγ).id (hnr.at_obj hγ).id]
    rcases (hn.at_obj hγ).obj with ⟨k, hk⟩
    dsimp only [evalTm, eval]
    rw [hk]
    rfl
  · rw [evalTm_instantiate₂_mor s hn hnr hδ]
    rcases (hn.along hδ).2.2 with ⟨k, h1, h2, hm⟩
    dsimp only [evalTm, eval]
    rw [h1, h2, hm]
    rfl

end HofmannStreicher1994.Repaired

/-! ## SemSoundness.lean -/

namespace HofmannStreicher1994.Repaired

mutual
  theorem ContextWf.sound {Γ : Context} :
      ContextWf Γ → SemCtxWf Γ
    | .nil => trivial
    | .cons hΓ hA => ⟨ContextWf.sound hΓ, (TypeWf.sound hA).2⟩

  theorem TypeWf.sound {Γ : Context} {A : Expr} :
      TypeWf Γ A → SemCtxWf Γ ∧ SemTypeWf Γ A
    | .pi hA hB =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      ⟨sΓ, SemTypeWf.pi sΓ sA (TypeWf.sound hB).2⟩
    | .sigma hA hB =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      ⟨sΓ, SemTypeWf.sigma sΓ sA (TypeWf.sound hB).2⟩
    | .identity hA ha hb =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      ⟨sΓ, SemTypeWf.identity sA (TermWf.sound ha).2.2 (TermWf.sound hb).2.2⟩
    | .nat hΓ => ⟨ContextWf.sound hΓ, SemTypeWf.nat⟩
    | .universe hΓ => ⟨ContextWf.sound hΓ, SemTypeWf.universe⟩
    | .el ha =>
      let ⟨sΓ, _, sa⟩ := TermWf.sound ha
      ⟨sΓ, SemTypeWf.el sa⟩
    | .subst hA hσ =>
      let sσ := SubstitutionWf.sound hσ
      ⟨sσ.ctx_dst, (TypeWf.sound hA).2.subst sσ⟩
    | .context hA hΓΔ =>
      let sΓΔ := ContextEq.sound hΓΔ
      ⟨sΓΔ.ctx_right, (TypeWf.sound hA).2.context sΓΔ⟩

  theorem TermWf.sound {Γ : Context} {t A : Expr} :
      TermWf Γ t A → SemCtxWf Γ ∧ SemTypeWf Γ A ∧ SemTermWf Γ t A
    | .var hΓ hn =>
      let sΓ := ContextWf.sound hΓ
      ⟨sΓ, sΓ.lookup_type hn, SemTermWf.var sΓ hn⟩
    | .lam hA hB hb =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      let sB := (TypeWf.sound hB).2
      ⟨sΓ, SemTypeWf.pi sΓ sA sB, SemTermWf.lam sΓ sA sB (TermWf.sound hb).2.2⟩
    | .app hA hB hf ha =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      let sB := (TypeWf.sound hB).2
      let sa := (TermWf.sound ha).2.2
      ⟨sΓ, SemTypeWf.instantiate sΓ sB sa, SemTermWf.app sΓ sA sB (TermWf.sound hf).2.2 sa⟩
    | .pair hA hB ha hb =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      let sB := (TypeWf.sound hB).2
      ⟨sΓ, SemTypeWf.sigma sΓ sA sB,
        SemTermWf.pair sΓ sA sB (TermWf.sound ha).2.2 (TermWf.sound hb).2.2⟩
    | .sigmaRec hA hB hC hd hp =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      let sB := (TypeWf.sound hB).2
      let sC := (TypeWf.sound hC).2
      let sp := (TermWf.sound hp).2.2
      ⟨sΓ, SemTypeWf.instantiate sΓ sC sp,
        SemTermWf.sigmaRec sΓ sA sB sC (TermWf.sound hd).2.2 sp⟩
    | .refl hA ha =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      let sa := (TermWf.sound ha).2.2
      ⟨sΓ, SemTypeWf.identity sA sa sa, SemTermWf.refl sΓ sA sa⟩
    | .idRec hA hC hd ha hb hp =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      let sC := (TypeWf.sound hC).2
      let sa := (TermWf.sound ha).2.2
      let sb := (TermWf.sound hb).2.2
      let sp := (TermWf.sound hp).2.2
      ⟨sΓ, SemTypeWf.instantiate₃ sΓ sC sa sb sp,
        SemTermWf.idRec sΓ sA sC (TermWf.sound hd).2.2 sa sb sp⟩
    | .zero hΓ =>
      let sΓ := ContextWf.sound hΓ
      ⟨sΓ, SemTypeWf.nat, SemTermWf.zero sΓ⟩
    | .succ hn =>
      let ⟨sΓ, sNat, sn⟩ := TermWf.sound hn
      ⟨sΓ, sNat, SemTermWf.succ sn⟩
    | .natRec hC hz hs hn =>
      let ⟨sΓ, _, sn⟩ := TermWf.sound hn
      let sC := (TypeWf.sound hC).2
      ⟨sΓ, SemTypeWf.instantiate sΓ sC sn,
        SemTermWf.natRec sΓ sC (TermWf.sound hz).2.2 (TermWf.sound hs).2.2 sn⟩
    | .conv ha hAB =>
      let ⟨sΓ, _, sa⟩ := TermWf.sound ha
      let sAB := TypeEq.sound hAB
      ⟨sΓ, sAB.wf_right, SemTermWf.conv sa sAB⟩
    | .subst ha hσ =>
      let ⟨_, sA, sa⟩ := TermWf.sound ha
      let sσ := SubstitutionWf.sound hσ
      ⟨sσ.ctx_dst, sA.subst sσ, sa.subst sA sσ⟩
    | .context ha hΓΔ =>
      let ⟨_, sA, sa⟩ := TermWf.sound ha
      let sΓΔ := ContextEq.sound hΓΔ
      ⟨sΓΔ.ctx_right, sA.context sΓΔ, SemTermWf.context sA sa sΓΔ⟩

  theorem TypeEq.sound {Γ : Context} {A B : Expr} :
      TypeEq Γ A B → SemTypeEq Γ A B
    | .refl hA =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      SemTypeEq.refl sΓ sA
    | .symm h => (TypeEq.sound h).symm
    | .trans h₁ h₂ => (TypeEq.sound h₁).trans (TypeEq.sound h₂)
    | .pi hA hB => SemTypeEq.pi (TypeEq.sound hA) (TypeEq.sound hB)
    | .sigma hA hB => SemTypeEq.sigma (TypeEq.sound hA) (TypeEq.sound hB)
    | .identity hA ha hb =>
      SemTypeEq.identity (TypeEq.sound hA) (TermEq.sound ha) (TermEq.sound hb)
    | .el h => SemTypeEq.el (TermEq.sound h)
    | .subst h hσ => (TypeEq.sound h).subst (SubstitutionWf.sound hσ)
    | .substEq hA hστ => SemTypeEq.substEq (TypeWf.sound hA).2 (SubstitutionEq.sound hστ)
    | .context h hΓΔ => (TypeEq.sound h).context (ContextEq.sound hΓΔ)

  theorem TermEq.sound {Γ : Context} {a b A : Expr} :
      TermEq Γ a b A → SemTermEq Γ a b A
    | .refl ha =>
      let ⟨sΓ, sA, sa⟩ := TermWf.sound ha
      SemTermEq.refl sΓ sA sa
    | .symm h => (TermEq.sound h).symm
    | .trans h₁ h₂ => (TermEq.sound h₁).trans (TermEq.sound h₂)
    | .conv h hAB => SemTermEq.conv (TermEq.sound h) (TypeEq.sound hAB)
    | .lam hA hB hb =>
      SemTermEq.lam (TypeEq.sound hA) (TypeWf.sound hB).2 (TermEq.sound hb)
    | .app hA hB hf ha =>
      SemTermEq.app (TypeEq.sound hA) (TypeEq.sound hB) (TermEq.sound hf) (TermEq.sound ha)
    | .pair hA hB ha hb =>
      SemTermEq.pair (TypeEq.sound hA) (TypeEq.sound hB) (TermEq.sound ha) (TermEq.sound hb)
    | .sigmaRec hA hB hC hd hp =>
      SemTermEq.sigmaRec (TypeEq.sound hA) (TypeEq.sound hB) (TypeEq.sound hC)
        (TermEq.sound hd) (TermEq.sound hp)
    | .reflCongr hA ha => SemTermEq.reflCongr (TypeEq.sound hA) (TermEq.sound ha)
    | .idRec hA hC hd ha hb hp =>
      SemTermEq.idRec (TypeEq.sound hA) (TypeEq.sound hC) (TermEq.sound hd)
        (TermEq.sound ha) (TermEq.sound hb) (TermEq.sound hp)
    | .succ hn => SemTermEq.succ (TermEq.sound hn)
    | .natRec hC hz hs hn =>
      SemTermEq.natRec (TypeEq.sound hC) (TermEq.sound hz) (TermEq.sound hs) (TermEq.sound hn)
    | .betaPi hA hB hb ha =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      SemTermEq.betaPi sΓ sA (TypeWf.sound hB).2 (TermWf.sound hb).2.2 (TermWf.sound ha).2.2
    | .etaPi hA hB hf =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      SemTermEq.etaPi sΓ sA (TypeWf.sound hB).2 (TermWf.sound hf).2.2
    | .betaSigma hA hB hC hd ha hb =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      SemTermEq.betaSigma sΓ sA (TypeWf.sound hB).2 (TypeWf.sound hC).2
        (TermWf.sound hd).2.2 (TermWf.sound ha).2.2 (TermWf.sound hb).2.2
    | .betaId hA hC hd ha =>
      let ⟨sΓ, sA⟩ := TypeWf.sound hA
      SemTermEq.betaId sΓ sA (TypeWf.sound hC).2 (TermWf.sound hd).2.2 (TermWf.sound ha).2.2
    | .betaNatZero hC hz hs =>
      let ⟨sΓ, _, sz⟩ := TermWf.sound hz
      SemTermEq.betaNatZero sΓ (TypeWf.sound hC).2 sz (TermWf.sound hs).2.2
    | .betaNatSucc hC hz hs hn =>
      let ⟨sΓ, _, sn⟩ := TermWf.sound hn
      SemTermEq.betaNatSucc sΓ (TypeWf.sound hC).2
        (TermWf.sound hz).2.2 (TermWf.sound hs).2.2 sn
    | .subst h hσ => (TermEq.sound h).subst (SubstitutionWf.sound hσ)
    | .substEq ha hστ =>
      let ⟨_, sA, sa⟩ := TermWf.sound ha
      SemTermEq.substEq sA sa (SubstitutionEq.sound hστ)
    | .context h hΓΔ => (TermEq.sound h).context (ContextEq.sound hΓΔ)

  theorem SubstitutionWf.sound {Γ Δ : Context} {σ : Nat → Expr} :
      SubstitutionWf Γ Δ σ → SemSubstWf Γ Δ σ
    | .mk hΓ hΔ hσ =>
      SemSubstWf.of_terms (ContextWf.sound hΓ) (ContextWf.sound hΔ)
        (fun n A hn => (TermWf.sound (hσ n A hn)).2.2)

  theorem SubstitutionEq.sound {Γ Δ : Context} {σ τ : Nat → Expr} :
      SubstitutionEq Γ Δ σ τ → SemSubstEq Γ Δ σ τ
    | .mk hσ hτ hστ =>
      SemSubstEq.of_terms (SubstitutionWf.sound hσ) (SubstitutionWf.sound hτ)
        (fun n A hn => TermEq.sound (hστ n A hn))

  theorem ContextEq.sound {Γ Δ : Context} :
      ContextEq Γ Δ → SemCtxEq Γ Δ
    | .nil => SemCtxEq.nil
    | .cons hΓΔ hAB => SemCtxEq.cons (ContextEq.sound hΓΔ) (TypeEq.sound hAB)
end

end HofmannStreicher1994.Repaired

namespace HofmannStreicher1994

theorem uip_underivable :
    TypeWf [] counterexampleType ∧
      (¬ ∃ t, TermWf (diagonalContext counterexampleType) t
        (diagonalConclusion counterexampleType)) ∧
      (¬ ∃ t, TermWf (uipContext counterexampleType) t
        (uipConclusion counterexampleType)) := by
  refine ⟨Repaired.counterexampleType_wf, ?_, ?_⟩
  · exact fun ⟨t, ht⟩ =>
      Repaired.diagonalConclusion_empty _
        (((Repaired.TermWf.sound ht).2.2.at_obj Repaired.diagonalEnv_valid).obj)
  · exact fun ⟨t, ht⟩ =>
      Repaired.uipConclusion_empty _
        (((Repaired.TermWf.sound ht).2.2.at_obj Repaired.uipEnv_valid).obj)


end HofmannStreicher1994

open HofmannStreicher1994

theorem solution :
    TypeWf [] counterexampleType ∧
      (¬ ∃ t, TermWf (diagonalContext counterexampleType) t
        (diagonalConclusion counterexampleType)) ∧
      (¬ ∃ t, TermWf (uipContext counterexampleType) t
        (uipConclusion counterexampleType)) :=
  HofmannStreicher1994.uip_underivable
