-- Prove2me | solution 1 for MoritaEquiv.example4_morita
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-12T23:48:52.499257+00:00
-- url     : https://prove2.me/submissions/50d05fca-9d5f-4c07-ac9f-0816fa977e90

import Mathlib
import Definitions.Def_MoritaEquiv_defs
import Theorems.Thm_MoritaEquiv_MoritaData_isModel_ext_iff

open CategoryTheory

namespace MoritaEquiv
namespace E4

set_option allowUnsafeReducibility true
attribute [local reducible] MoritaData.sig Ctx.cons

/-! ### Realization lemmas -/

section Realize
variable {L : Sig} (M : Str L) {n : ℕ} {Γ : Fin n → L.Srt} (v : (i : Fin n) → M.carrier (Γ i))

theorem r_not (φ : Formula L Γ) : φ.not.Realize M v ↔ ¬ φ.Realize M v := Iff.rfl

theorem r_imp (φ ψ : Formula L Γ) :
    (Formula.imp φ ψ).Realize M v ↔ (φ.Realize M v → ψ.Realize M v) := Iff.rfl

theorem r_and (φ ψ : Formula L Γ) :
    (φ.and ψ).Realize M v ↔ φ.Realize M v ∧ ψ.Realize M v := by
  show ¬(φ.Realize M v → ¬ψ.Realize M v) ↔ _
  tauto

theorem r_or (φ ψ : Formula L Γ) :
    (φ.or ψ).Realize M v ↔ φ.Realize M v ∨ ψ.Realize M v := by
  show (¬φ.Realize M v → ψ.Realize M v) ↔ _
  tauto

theorem r_iff (φ ψ : Formula L Γ) :
    (φ.iff ψ).Realize M v ↔ (φ.Realize M v ↔ ψ.Realize M v) := by
  rw [Formula.iff, r_and]
  exact iff_def.symm

theorem r_allS (s : L.Srt) (φ : Formula L (Ctx.cons s Γ)) :
    (Formula.allS s φ).Realize M v ↔
      ∀ a : M.carrier s, φ.Realize M (Fin.cons (α := fun i => M.carrier (Ctx.cons s Γ i)) a v) :=
  Iff.rfl

theorem r_exS (s : L.Srt) (φ : Formula L (Ctx.cons s Γ)) :
    (Formula.exS s φ).Realize M v ↔
      ∃ a : M.carrier s, φ.Realize M (Fin.cons (α := fun i => M.carrier (Ctx.cons s Γ i)) a v) := by
  show ¬ (∀ a : M.carrier s, ¬ _) ↔ _
  exact not_forall_not

theorem r_equal {s : L.Srt} (t₁ t₂ : Term L Γ s) :
    (Formula.equal t₁ t₂).Realize M v ↔ t₁.realize M v = t₂.realize M v := Iff.rfl

/-- Apply a unary symbol to a value. -/
def ap {a b : L.Srt} (f : L.Func 1 ![a] b) (z : M.carrier a) : M.carrier b :=
  M.funMap f (Fin.cons (α := fun j => M.carrier (![a] j)) z finZeroElim)

theorem fin1_eq {α : Fin 1 → Type} (g : (j : Fin 1) → α j) :
    g = Fin.cons (α := α) (g 0) finZeroElim := by
  funext j; exact Fin.cases rfl (fun k => k.elim0) j

theorem fin2_eq {α : Fin 2 → Type} (g : (j : Fin 2) → α j) :
    g = Fin.cons (α := α) (g 0) (Fin.cons (α := fun j => α j.succ) (g 1) finZeroElim) := by
  funext j
  exact Fin.cases rfl (fun k => Fin.cases rfl (fun l => l.elim0) k) j

theorem consEta {m : ℕ} {α : Fin (m + 1) → Type} (g : (j : Fin (m + 1)) → α j) :
    Fin.cons (α := α) (g 0) (fun j => g j.succ) = g :=
  Fin.cons_self_tail g

theorem r_app1 {a b : L.Srt} (f : L.Func 1 ![a] b) (t : Term L Γ a) :
    (Term.app1 f t).realize M v = ap M f (t.realize M v) := by
  show M.funMap f _ = M.funMap f _
  congr 1
  funext j; exact Fin.cases rfl (fun k => k.elim0) j

theorem r_eqapp {a b : L.Srt} (f : L.Func 1 ![a] b) (t : Term L Γ a) (u : Term L Γ b) :
    (Formula.equal (Term.app1 f t) u).Realize M v ↔ ap M f (t.realize M v) = u.realize M v := by
  rw [r_equal, r_app1]

theorem r_eqapp2 {a a' b : L.Srt} (f : L.Func 1 ![a] b) (g : L.Func 1 ![a'] b) (t : Term L Γ a)
    (t' : Term L Γ a') :
    (Formula.equal (Term.app1 f t) (Term.app1 g t')).Realize M v ↔
      ap M f (t.realize M v) = ap M g (t'.realize M v) := by
  rw [r_equal, r_app1, r_app1]

theorem r_appeq {a a' b : L.Srt} (f : L.Func 1 ![a] b) (g : L.Func 1 ![a'] b) (t : Term L Γ a)
    (t' : Term L Γ a') :
    (Term.app1 f t).realize M v = (Term.app1 g t').realize M v ↔
      ap M f (t.realize M v) = ap M g (t'.realize M v) := by
  rw [r_app1, r_app1]

theorem funMap_unary {a b : L.Srt} (f : L.Func 1 ![a] b) (g : (j : Fin 1) → M.carrier (![a] j)) :
    M.funMap f g = ap M f (g 0) := by
  unfold ap; congr 1; exact fin1_eq g

theorem realize_fin1 {a : L.Srt} (φ : Formula L ![a]) (w : (j : Fin 1) → M.carrier (![a] j)) :
    φ.Realize M w ↔
      φ.Realize M (Fin.cons (α := fun j => M.carrier (![a] j)) (w 0) finZeroElim) := by
  rw [← fin1_eq w]

theorem realize_fin2 {a : L.Srt} (φ : Formula L ![a, a]) (w : (j : Fin 2) → M.carrier (![a, a] j)) :
    φ.Realize M w ↔ φ.Realize M (Fin.cons (α := fun j => M.carrier (![a, a] j)) (w 0)
      (Fin.cons (α := fun j => M.carrier (![a, a] j.succ)) (w 1) finZeroElim)) := by
  rw [← fin2_eq w]

theorem realize_consEta {m : ℕ} {s : L.Srt} {dom : Fin m → L.Srt} (φ : Formula L (Ctx.cons s dom))
    (w : (j : Fin (m + 1)) → M.carrier (Ctx.cons s dom j)) :
    φ.Realize M (Fin.cons (α := fun j => M.carrier (Ctx.cons s dom j)) (w 0) (fun j => w j.succ)) ↔
      φ.Realize M w := by
  rw [consEta w]

end Realize


/-! ### The concrete Morita extensions -/

open MoritaData Ex1

/-- `T₁ ⇝ T₁⁺`: subsorts `σ_b = {x | p x}` (`b = true`) and `{x | q x}` (`b = false`). -/
def D1 : MoritaData sig1 T1 where
  Prod := Empty
  prodFst := Empty.elim
  prodSnd := Empty.elim
  Coprod := Empty
  coprodFst := Empty.elim
  coprodSnd := Empty.elim
  Sub := Bool
  subBase _ := ()
  subDef b := if b then pAt else qAt
  Quot := Empty
  quotBase := Empty.elim
  quotDef σ := σ.elim
  NewFunc _ _ _ := Empty
  funcDef f := f.elim
  NewRel _ _ := Empty
  relDef r := r.elim
  sub_adm M hM b := by
    have h1 : (Formula.exS (L := sig1) (Γ := uctx 0) () pAt).Realize M finZeroElim :=
      hM _ (Or.inl rfl) finZeroElim
    have h2 : (Formula.exS (L := sig1) (Γ := uctx 0) () qAt).Realize M finZeroElim :=
      hM _ (Or.inr (Or.inl rfl)) finZeroElim
    cases b
    · obtain ⟨a, ha⟩ := (r_exS M finZeroElim () qAt).1 h2; exact ⟨a, ha⟩
    · obtain ⟨a, ha⟩ := (r_exS M finZeroElim () pAt).1 h1; exact ⟨a, ha⟩
  quot_adm _ _ σ := σ.elim
  func_adm _ _ _ _ _ f := f.elim

/-- `T₂ ⇝ T₂⁺`: the coproduct sort `σ₁ = σ₂ ⊔ σ₃`. -/
def D2a : MoritaData sig2 T2 where
  Prod := Empty
  prodFst := Empty.elim
  prodSnd := Empty.elim
  Coprod := Unit
  coprodFst _ := true
  coprodSnd _ := false
  Sub := Empty
  subBase := Empty.elim
  subDef σ := σ.elim
  Quot := Empty
  quotBase := Empty.elim
  quotDef σ := σ.elim
  NewFunc _ _ _ := Empty
  funcDef f := f.elim
  NewRel _ _ := Empty
  relDef r := r.elim
  sub_adm _ _ σ := σ.elim
  quot_adm _ _ σ := σ.elim
  func_adm _ _ _ _ _ f := f.elim

/-- The new predicates `p, q` on the coproduct sort. -/
inductive NR : (m : ℕ) → (Fin m → D2a.ExtSrt) → Type
  | p : NR 1 (fun _ => .coprod ())
  | q : NR 1 (fun _ => .coprod ())

/-- The two coproduct injections. -/
def inlb : (b : Bool) → D2a.sig.Func 1 ![.old b] (.coprod ())
  | true => ExtFunc.inl (D := D2a) ()
  | false => ExtFunc.inr (D := D2a) ()

def nrOf : Bool → NR 1 (fun _ => .coprod ())
  | true => .p
  | false => .q

/-- `p(x) ↔ ∃ y, ρ₁ y = x`, `q(x) ↔ ∃ y, ρ₂ y = x`. -/
def nrDef : {m : ℕ} → {dom : Fin m → D2a.ExtSrt} → NR m dom → Formula D2a.sig dom
  | _, _, .p => Formula.exS (L := D2a.sig) (.old true)
      (Formula.equal (Term.app1 (L := D2a.sig) (inlb true) (Term.var 0)) (Term.var 1))
  | _, _, .q => Formula.exS (L := D2a.sig) (.old false)
      (Formula.equal (Term.app1 (L := D2a.sig) (inlb false) (Term.var 0)) (Term.var 1))

/-- `T₂⁺ ⇝ T₂⁺⁺`: the predicates `p, q` on the coproduct sort. -/
def D2b : MoritaData D2a.sig D2a.ext where
  Prod := Empty
  prodFst := Empty.elim
  prodSnd := Empty.elim
  Coprod := Empty
  coprodFst := Empty.elim
  coprodSnd := Empty.elim
  Sub := Empty
  subBase := Empty.elim
  subDef σ := σ.elim
  Quot := Empty
  quotBase := Empty.elim
  quotDef σ := σ.elim
  NewFunc _ _ _ := Empty
  funcDef f := f.elim
  NewRel := NR
  relDef := nrDef
  sub_adm _ _ σ := σ.elim
  quot_adm _ _ σ := σ.elim
  func_adm _ _ _ _ _ f := f.elim

/-! ### The renaming `Σ₁⁺ ⟶ Σ₂⁺⁺` -/

def oS : D1.ExtSrt → D2b.ExtSrt
  | .old _ => .old (.coprod ())
  | .sub b => .old (.old b)
  | .prod σ => σ.elim
  | .coprod σ => σ.elim
  | .quot σ => σ.elim

theorem oS_inj : Function.Injective oS := by
  intro a b h
  rcases a with x | σ | σ | a | σ <;> rcases b with y | τ | τ | b | τ <;>
    first | exact σ.elim | exact τ.elim | skip
  · rfl
  · simp [oS] at h
  · simp [oS] at h
  · exact congrArg _ (ExtSrt.old.inj (ExtSrt.old.inj h))

theorem oS_surj : Function.Surjective oS := by
  intro y
  rcases y with x | σ | σ | σ | σ
  · rcases x with b | σ | u | σ | σ
    · exact ⟨.sub b, rfl⟩
    · exact σ.elim
    · exact ⟨.old (), rfl⟩
    · exact σ.elim
    · exact σ.elim
  all_goals exact σ.elim

def castD {L : Sig} {m : ℕ} {d d' : Fin m → L.Srt} {s : L.Srt} (h : d = d') (f : L.Func m d s) :
    L.Func m d' s := h ▸ f

theorem castD_heq {L : Sig} {m : ℕ} {d d' : Fin m → L.Srt} {s : L.Srt} (h : d = d')
    (f : L.Func m d s) : HEq (castD h f) f := by
  subst h; rfl

theorem funMap_castD {L : Sig} (M : Str L) {m : ℕ} {d d' : Fin m → L.Srt} {s : L.Srt} (h : d = d')
    (f : L.Func m d s) (xs : (j : Fin m) → M.carrier (d' j)) (ys : (j : Fin m) → M.carrier (d j))
    (hxy : HEq xs ys) : M.funMap (castD h f) xs = M.funMap f ys := by
  subst h; cases hxy; rfl

theorem hdom (b : Bool) :
    (ExtSrt.old ∘ ![ExtSrt.old b] : Fin 1 → D2b.ExtSrt) = oS ∘ ![ExtSrt.sub (D := D1) b] := by
  funext i; fin_cases i; rfl

def oF : {m : ℕ} → {dom : Fin m → D1.ExtSrt} → {s : D1.ExtSrt} → D1.ExtFunc m dom s →
    D2b.ExtFunc m (oS ∘ dom) (oS s)
  | _, _, _, .incl b => castD (L := D2b.sig) (hdom b) (ExtFunc.old (inlb b))
  | _, _, _, .old f => nomatch f
  | _, _, _, .new f => nomatch f
  | _, _, _, .fst σ => nomatch σ
  | _, _, _, .snd σ => nomatch σ
  | _, _, _, .inl σ => nomatch σ
  | _, _, _, .inr σ => nomatch σ
  | _, _, _, .proj σ => nomatch σ

def oR : {m : ℕ} → {dom : Fin m → D1.ExtSrt} → D1.ExtRel m dom → D2b.ExtRel m (oS ∘ dom)
  | _, _, .old .p => ExtRel.new NR.p
  | _, _, .old .q => ExtRel.new NR.q
  | _, _, .new r => nomatch r

def F : D1.sig.Hom D2b.sig := ⟨oS, oF, oR⟩

theorem oF_ss {m : ℕ} {dom : Fin m → D1.ExtSrt} {s : D1.ExtSrt} (f : D1.ExtFunc m dom s) :
    ∀ {m' : ℕ} {dom' : Fin m' → D1.ExtSrt} {s' : D1.ExtSrt} (g : D1.ExtFunc m' dom' s'),
      HEq dom dom' → HEq f g := by
  cases f with
  | incl b =>
    intro m' dom' s' g
    cases g with
    | incl b' =>
      intro h
      have : b = b' := by
        have := congrFun (eq_of_heq h) 0
        simpa using this
      subst this; rfl
    | old f => exact nomatch f
    | new f => exact nomatch f
    | fst σ => exact nomatch σ
    | snd σ => exact nomatch σ
    | inl σ => exact nomatch σ
    | inr σ => exact nomatch σ
    | proj σ => exact nomatch σ
  | old f => exact nomatch f
  | new f => exact nomatch f
  | fst σ => exact nomatch σ
  | snd σ => exact nomatch σ
  | inl σ => exact nomatch σ
  | inr σ => exact nomatch σ
  | proj σ => exact nomatch σ

theorem oF_surj' {m : ℕ} {dom' : Fin m → D2b.ExtSrt} {s' : D2b.ExtSrt} (g : D2b.ExtFunc m dom' s') :
    ∀ (dom : Fin m → D1.ExtSrt) (s : D1.ExtSrt), oS ∘ dom = dom' → oS s = s' →
      ∃ f : D1.ExtFunc m dom s, HEq (oF f) g := by
  cases g with
  | old g =>
    cases g with
    | inl u =>
      intro dom s hd hs
      have hd' : dom = ![ExtSrt.sub true] := by
        funext i; fin_cases i; exact oS_inj (congrFun hd 0)
      have hs' : s = .old () := oS_inj hs
      subst hd' hs'
      exact ⟨ExtFunc.incl (D := D1) true, castD_heq (L := D2b.sig) (hdom true) (ExtFunc.old (inlb true))⟩
    | inr u =>
      intro dom s hd hs
      have hd' : dom = ![ExtSrt.sub false] := by
        funext i; fin_cases i; exact oS_inj (congrFun hd 0)
      have hs' : s = .old () := oS_inj hs
      subst hd' hs'
      exact ⟨ExtFunc.incl (D := D1) false, castD_heq (L := D2b.sig) (hdom false) (ExtFunc.old (inlb false))⟩
    | old f => exact nomatch f
    | new f => exact nomatch f
    | fst σ => exact nomatch σ
    | snd σ => exact nomatch σ
    | incl σ => exact nomatch σ
    | proj σ => exact nomatch σ
  | new f => exact nomatch f
  | fst σ => exact nomatch σ
  | snd σ => exact nomatch σ
  | inl σ => exact nomatch σ
  | inr σ => exact nomatch σ
  | incl σ => exact nomatch σ
  | proj σ => exact nomatch σ

theorem oR_inj' {m : ℕ} {dom : Fin m → D1.ExtSrt} (f : D1.ExtRel m dom) :
    ∀ (g : D1.ExtRel m dom), oR f = oR g → f = g := by
  cases f with
  | old r =>
    cases r with
    | p =>
      intro g
      cases g with
      | old r' => cases r' with
        | p => intro; rfl
        | q => intro h; cases h
      | new r' => exact nomatch r'
    | q =>
      intro g
      cases g with
      | old r' => cases r' with
        | p => intro h; cases h
        | q => intro; rfl
      | new r' => exact nomatch r'
  | new r => exact nomatch r

theorem oR_surj' {m : ℕ} {dom' : Fin m → D2b.ExtSrt} (g : D2b.ExtRel m dom') :
    ∀ (dom : Fin m → D1.ExtSrt), oS ∘ dom = dom' → ∃ f : D1.ExtRel m dom, HEq (oR f) g := by
  cases g with
  | old g =>
    cases g with
    | old r => exact nomatch r
    | new r => exact nomatch r
  | new r =>
    cases r with
    | p =>
      intro dom hd
      have hd' : dom = ExtSrt.old ∘ uctx 1 := by
        funext i; exact oS_inj (congrFun hd i)
      subst hd'
      exact ⟨.old .p, HEq.rfl⟩
    | q =>
      intro dom hd
      have hd' : dom = ExtSrt.old ∘ uctx 1 := by
        funext i; exact oS_inj (congrFun hd i)
      subst hd'
      exact ⟨.old .q, HEq.rfl⟩

theorem F_isRenaming : F.IsRenaming where
  srt := ⟨oS_inj, oS_surj⟩
  func := fun {m dom s} => by
    refine ⟨fun f g _ => eq_of_heq (oF_ss f g HEq.rfl), fun g => ?_⟩
    obtain ⟨f, hf⟩ := oF_surj' g dom s rfl rfl
    exact ⟨f, eq_of_heq hf⟩
  rel := fun {m dom} => by
    refine ⟨fun f g h => oR_inj' f g h, fun g => ?_⟩
    obtain ⟨f, hf⟩ := oR_surj' g dom rfl
    exact ⟨f, eq_of_heq hf⟩


/-! ### Models on both sides -/

/-- The coproduct injections in a `Σ₂⁺⁺`-structure. -/
def ι (M : Str D2b.sig) (b : Bool) (a : M.carrier (.old (.old b))) : M.carrier (.old (.coprod ())) :=
  ap (M.reduct D2b.incl) (L := D2a.sig) (inlb b) a

/-- The predicates `p` (`b = true`) and `q` (`b = false`) in a `Σ₂⁺⁺`-structure. -/
def Pr (M : Str D2b.sig) (b : Bool) (c : M.carrier (.old (.coprod ()))) : Prop :=
  M.relMap (L := D2b.sig) (ExtRel.new (nrOf b)) (fun _ => c)

theorem incl_ap (M : Str D2b.sig) (b : Bool) (z : M.carrier (.old (.old b))) :
    ap (M.reduct F) (L := D1.sig) (ExtFunc.incl (D := D1) b) z = ι M b z := by
  unfold ap ι
  show M.funMap (castD (L := D2b.sig) (hdom b) (ExtFunc.old (inlb b))) _ =
    M.funMap (ExtFunc.old (inlb b)) _
  apply funMap_castD
  apply Function.hfunext rfl
  intro j j' hj
  cases hj
  fin_cases j
  exact HEq.rfl

theorem incl_iff (M : Str D2b.sig) (b : Bool) (z : M.carrier (.old (.old b)))
    (c : M.carrier (.old (.coprod ()))) :
    ap (M.reduct F) (L := D1.sig) (ExtFunc.incl (D := D1) b) z = c ↔ ι M b z = c :=
  ⟨fun h => (incl_ap M b z).symm.trans h, fun h => (incl_ap M b z).trans h⟩

theorem nr_realize (M : Str D2b.sig) (b : Bool) (c : M.carrier (.old (.coprod ()))) :
    (nrDef (nrOf b)).Realize (M.reduct D2b.incl) (fun _ => c) ↔ ∃ a, ι M b a = c := by
  cases b
  · refine (r_exS _ _ _ _).trans ?_
    exact exists_congr fun a => r_eqapp ..
  · refine (r_exS _ _ _ _).trans ?_
    exact exists_congr fun a => r_eqapp ..

theorem core {C : Type} {A : Bool → Type} (hA : ∀ b, Nonempty (A b)) (ι : ∀ b, A b → C)
    (P : Bool → C → Prop) :
    ((∀ c, (∃ a, ι true a = c ∧ ∀ a', ι true a' = c → a' = a) ∨
        (∃ a, ι false a = c ∧ ∀ a', ι false a' = c → a' = a)) ∧
      (∀ a a', ¬ ι true a = ι false a') ∧ (∀ b c, P b c ↔ ∃ a, ι b a = c)) ↔
    ((∃ c, P true c) ∧ (∃ c, P false c) ∧ (∀ c, P true c ∨ P false c) ∧
      (∀ c, ¬ (P true c ∧ P false c)) ∧
      ∀ b, (∀ c, P b c ↔ ∃ a, ι b a = c) ∧ Function.Injective (ι b)) := by
  constructor
  · rintro ⟨hco, hdis, hP⟩
    refine ⟨?_, ?_, fun c => ?_, fun c => ?_, fun b => ⟨hP b, ?_⟩⟩
    · obtain ⟨a⟩ := hA true; exact ⟨_, (hP true _).2 ⟨a, rfl⟩⟩
    · obtain ⟨a⟩ := hA false; exact ⟨_, (hP false _).2 ⟨a, rfl⟩⟩
    · rcases hco c with ⟨a, ha, -⟩ | ⟨a, ha, -⟩
      · exact Or.inl ((hP true c).2 ⟨a, ha⟩)
      · exact Or.inr ((hP false c).2 ⟨a, ha⟩)
    · rintro ⟨h1, h2⟩
      obtain ⟨a, rfl⟩ := (hP true c).1 h1
      obtain ⟨a', ha'⟩ := (hP false _).1 h2
      exact hdis a a' ha'.symm
    · intro a1 a2 h
      cases b
      · rcases hco (ι false a1) with ⟨a, ha, -⟩ | ⟨a, -, hu⟩
        · exact (hdis a a1 ha).elim
        · exact (hu a1 rfl).trans (hu a2 h.symm).symm
      · rcases hco (ι true a1) with ⟨a, -, hu⟩ | ⟨a, ha, -⟩
        · exact (hu a1 rfl).trans (hu a2 h.symm).symm
        · exact (hdis a1 a ha.symm).elim
  · rintro ⟨-, -, hor, hnot, hb⟩
    refine ⟨fun c => ?_, fun a a' h => hnot (ι true a)
      ⟨((hb true).1 _).2 ⟨a, rfl⟩, ((hb false).1 _).2 ⟨a', h.symm⟩⟩, fun b c => (hb b).1 c⟩
    rcases hor c with h | h
    · obtain ⟨a, ha⟩ := ((hb true).1 c).1 h
      exact Or.inl ⟨a, ha, fun a' h' => (hb true).2 (h'.trans ha.symm)⟩
    · obtain ⟨a, ha⟩ := ((hb false).1 c).1 h
      exact Or.inr ⟨a, ha, fun a' h' => (hb false).2 (h'.trans ha.symm)⟩

theorem T1_iff (N : Str sig1) : N.IsModel T1 ↔
    (∃ x : N.carrier (), N.relMap (L := sig1) Rel1.p (fun _ => x)) ∧ (∃ x : N.carrier (), N.relMap (L := sig1) Rel1.q (fun _ => x)) ∧
      (∀ x : N.carrier (), N.relMap (L := sig1) Rel1.p (fun _ => x) ∨ N.relMap (L := sig1) Rel1.q (fun _ => x)) ∧
      ∀ x : N.carrier (), ¬ (N.relMap (L := sig1) Rel1.p (fun _ => x) ∧ N.relMap (L := sig1) Rel1.q (fun _ => x)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, fun x => ?_, fun x hpq => ?_⟩
    · obtain ⟨a, ha⟩ := (r_exS N finZeroElim () pAt).1 (h _ (Or.inl rfl) finZeroElim)
      exact ⟨a, ha⟩
    · obtain ⟨a, ha⟩ := (r_exS N finZeroElim () qAt).1 (h _ (Or.inr (Or.inl rfl)) finZeroElim)
      exact ⟨a, ha⟩
    · exact (r_or N (fun _ => x) pAt qAt).1 (h _ (Or.inr (Or.inr (Or.inl rfl))) (fun _ => x))
    · exact (h _ (Or.inr (Or.inr (Or.inr rfl))) (fun _ => x)) ((r_and N (fun _ => x) pAt qAt).2 hpq)
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩, hor, hnot⟩ A hA
    rcases hA with rfl | rfl | rfl | rfl
    · intro v; exact (r_exS N v () pAt).2 ⟨x, hx⟩
    · intro v; exact (r_exS N v () qAt).2 ⟨y, hy⟩
    · intro v; exact (r_or N v pAt qAt).2 (hor (v 0))
    · intro v hv; exact hnot (v 0) ((r_and N v pAt qAt).1 hv)

theorem sem2 (M : Str D2b.sig) : M.IsModel D2b.ext ↔
    ((∀ c, (∃ a, ι M true a = c ∧ ∀ a', ι M true a' = c → a' = a) ∨
        (∃ a, ι M false a = c ∧ ∀ a', ι M false a' = c → a' = a)) ∧
      (∀ a a', ¬ ι M true a = ι M false a') ∧ (∀ b c, Pr M b c ↔ ∃ a, ι M b a = c)) := by
  constructor
  · intro h
    obtain ⟨h0, -, -, -, -, -, hr⟩ := (MoritaData.isModel_ext_iff D2b M).1 h
    obtain ⟨-, -, hc, -⟩ := (MoritaData.isModel_ext_iff D2a (M.reduct D2b.incl)).1 h0
    have hc' := hc ()
    refine ⟨fun c => (hc' (Fin.cons c finZeroElim)).1,
      fun a a' => (hc' (Fin.cons (ι M true a) finZeroElim)).2 a a', fun b c => ?_⟩
    exact (hr (nrOf b) (fun _ => c)).trans (nr_realize M b c)
  · rintro ⟨hco, hdis, hP⟩
    refine (MoritaData.isModel_ext_iff D2b M).2 ⟨?_, (Empty.elim ·), (Empty.elim ·), (Empty.elim ·),
      (Empty.elim ·), fun f => Empty.elim f, fun r => ?_⟩
    · refine (MoritaData.isModel_ext_iff D2a _).2 ⟨fun _ hA => False.elim hA, (Empty.elim ·),
        fun σ => ?_, (Empty.elim ·), (Empty.elim ·), fun f => Empty.elim f, fun r => Empty.elim r⟩
      cases σ
      exact fun v => ⟨hco (v 0), hdis⟩
    · cases r with
      | p =>
        refine fun v => ?_
        rw [show v = fun _ => v 0 from funext fun j => by fin_cases j; rfl]
        exact (hP true (v 0)).trans (nr_realize M true (v 0)).symm
      | q =>
        refine fun v => ?_
        rw [show v = fun _ => v 0 from funext fun j => by fin_cases j; rfl]
        exact (hP false (v 0)).trans (nr_realize M false (v 0)).symm

theorem sem1 (M : Str D2b.sig) : (M.reduct F).IsModel D1.ext ↔
    ((∃ c, Pr M true c) ∧ (∃ c, Pr M false c) ∧ (∀ c, Pr M true c ∨ Pr M false c) ∧
      (∀ c, ¬ (Pr M true c ∧ Pr M false c)) ∧
      ∀ b, (∀ c, Pr M b c ↔ ∃ a, ι M b a = c) ∧ Function.Injective (ι M b)) := by
  constructor
  · intro h
    obtain ⟨h0, -, -, hs, -, -, -⟩ := (MoritaData.isModel_ext_iff D1 (M.reduct F)).1 h
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hor, hnot⟩ := (T1_iff _).1 h0
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, hor, hnot, fun b => ⟨fun c => ?_, fun a1 a2 h12 => ?_⟩⟩
    · have := (hs b (fun _ => c)).1
      cases b
      · exact this.trans (exists_congr fun z => incl_iff M false z c)
      · exact this.trans (exists_congr fun z => incl_iff M true z c)
    · exact (hs b (fun _ => ι M b a1)).2 a2 a1
        ((incl_ap M b a1).trans (h12.trans (incl_ap M b a2).symm))
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩, hor, hnot, hb⟩
    refine (MoritaData.isModel_ext_iff D1 _).2 ⟨(T1_iff _).2 ⟨⟨x, hx⟩, ⟨y, hy⟩, hor, hnot⟩, (Empty.elim ·),
      (Empty.elim ·), fun b => ?_, (Empty.elim ·), fun f => Empty.elim f, fun r => Empty.elim r⟩
    refine fun v => ⟨?_, fun z1 z2 h => (hb b).2
      ((incl_ap M b z2).symm.trans (h.trans (incl_ap M b z1)))⟩
    rw [show v = fun _ => v 0 from funext fun j => by fin_cases j; rfl]
    cases b
    · exact ((hb false).1 (v 0)).trans (exists_congr fun z => (incl_iff M false z (v 0)).symm)
    · exact ((hb true).1 (v 0)).trans (exists_congr fun z => (incl_iff M true z (v 0)).symm)

theorem e4_main : MoritaEquivalent T1 T2 :=
  ⟨D1.sig, D2b.sig, D1.ext, D2b.ext, F, .step D1 (.refl _), .step D2a (.step D2b (.refl _)),
    F_isRenaming, fun M =>
      (sem2 M).trans ((core (fun b => M.nonempty _) (ι M) (Pr M)).trans (sem1 M).symm)⟩

end E4
end MoritaEquiv

open MoritaEquiv in
theorem solution : MoritaEquivalent Ex1.T1 Ex1.T2 := MoritaEquiv.E4.e4_main
