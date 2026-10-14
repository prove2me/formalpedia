-- Prove2me | solution 1 for MoritaEquiv.thm52_not_morita
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-13T20:05:34.398453+00:00
-- url     : https://prove2.me/submissions/4b8c47d3-bb56-49d4-8c75-17f0e344061b

import Mathlib
import Definitions.Def_MoritaEquiv_defs
import Theorems.Thm_MoritaEquiv_ElemEmb_exists_of_sortwise_equiv
import Theorems.Thm_MoritaEquiv_Sig_Hom_IsRenaming_exists_formula_pullback
import Theorems.Thm_MoritaEquiv_Sig_Hom_IsRenaming_exists_reduct_biembedding
import Theorems.Thm_MoritaEquiv_MoritaData_exists_isolated_model_iff

open CategoryTheory


namespace MoritaEquiv
namespace T52C
open Thm52
theorem one_of {M : Str sig} (h : M.Satisfies exactlyOne) : ∀ x y : M.carrier (), x = y := by
  obtain ⟨c, hc⟩ : ∃ c : M.carrier (), ∀ y, y = c := by
    have := h (fun i => i.elim0)
    by_contra hne
    push Not at hne
    apply this
    intro c hc
    obtain ⟨y, hy⟩ := hne c
    exact hy (hc y)
  intro x y; rw [hc x, hc y]

/-- the set of predicates true at the (unique) element -/
def pset (M : Str sig) : Set ℕ := {i | ∀ x : M.carrier (), M.relMap (PRel.p i) (fun _ => x)}

theorem fun1 {M : Str sig} (xs : (j : Fin 1) → M.carrier (uctx 1 j)) : xs = fun _ => xs 0 := by
  funext j; rw [Subsingleton.elim j 0]

theorem pset_iff {M : Str sig} (h1 : ∀ x y : M.carrier (), x = y) (i : ℕ)
    (xs : (j : Fin 1) → M.carrier (uctx 1 j)) : M.relMap (PRel.p i) xs ↔ i ∈ pset M := by
  constructor
  · intro h x; rw [fun1 xs] at h; rwa [h1 x (xs 0)]
  · intro h; rw [fun1 xs]; exact h _

theorem sub_hom {M N : Str sig} (h1 : ∀ x y : N.carrier (), x = y) :
    Subsingleton (ElemEmb M N) := by
  constructor
  intro f g
  cases f; cases g
  congr
  funext s x
  exact h1 _ _

/-- the canonical one-point structure with predicate set `S` -/
def mk (S : Set ℕ) : Str sig where
  carrier _ := Unit
  funMap f _ := (f : Empty).elim
  relMap r _ := match r with | PRel.p i => i ∈ S
  nonempty _ := ⟨()⟩

theorem mk_sat (S : Set ℕ) : (mk S).Satisfies exactlyOne := by
  intro v h
  exact h () (fun y => rfl)

theorem mk_pset (S : Set ℕ) : pset (mk S) = S := by
  ext i; exact ⟨fun h => h (), fun h _ => h⟩

theorem hom_iff {M N : Str sig} (hM : ∀ x y : M.carrier (), x = y)
    (hN : ∀ x y : N.carrier (), x = y) : Nonempty (ElemEmb M N) ↔ pset M = pset N := by
  constructor
  · rintro ⟨f⟩
    ext i
    obtain ⟨x⟩ := M.nonempty ()
    have := f.map_formula (pAt i) (fun _ => x)
    rw [← pset_iff hM i, ← pset_iff hN i]
    exact this.symm
  · intro h
    obtain ⟨x⟩ := M.nonempty ()
    obtain ⟨y⟩ := N.nonempty ()
    let e : M.carrier () ≃ N.carrier () :=
      ⟨fun _ => y, fun _ => x, fun a => hM _ _, fun b => hN _ _⟩
    obtain ⟨g, -⟩ := ElemEmb.exists_of_sortwise_equiv (A := M) (B := N) (fun s => match s with | () => e)
      (fun f _ => (f : Empty).elim)
      (fun {m dom} r xs => by
        cases r with
        | p i => rw [pset_iff hM i, pset_iff hN i, h])
    exact ⟨g⟩

theorem T1_sat (M : Model T1) : M.str.Satisfies exactlyOne := M.isModel _ rfl
theorem T2_sat (M : Model T2) : M.str.Satisfies exactlyOne := M.isModel _ (Or.inl rfl)

/-- the valid predicate sets for `T₂` -/
def Good : Set (Set ℕ) := {S | 0 ∈ S → ∀ i, i ∈ S}

theorem T2_good (M : Model T2) : pset M.str ∈ Good := by
  intro h0 i
  have hM := one_of (T2_sat M)
  have := M.isModel _ (Or.inr ⟨i, rfl⟩) (fun _ => Classical.choice (M.str.nonempty ()))
  intro x
  have h := this ((pset_iff hM 0 _).2 h0)
  exact (pset_iff hM i _).1 h x

theorem mk_T2 (S : Set ℕ) (hS : S ∈ Good) : (mk S).IsModel T2 := by
  rintro A (hA | ⟨i, rfl⟩)
  · rw [hA]; exact mk_sat S
  · intro v h; exact hS h i
end T52C
end MoritaEquiv

namespace MoritaEquiv
namespace T52N

theorem sent_emb {L : Sig} {M N : Str L} (h : ElemEmb M N) {Γ : Fin 0 → L.Srt}
    (φ : Formula L Γ) : (∀ v, φ.Realize N v) ↔ ∀ v, φ.Realize M v := by
  have hv : ∀ (w : (i : Fin 0) → N.carrier (Γ i)), w = fun i => h.toFun (Γ i) (i.elim0) :=
    fun w => funext fun i => i.elim0
  constructor
  · intro H v
    exact (h.map_formula φ v).1 (H _)
  · intro H w
    rw [hv w]
    exact (h.map_formula φ (fun i => i.elim0)).2 (H _)

/-- `T` has a model isolated (up to an elementary embedding into it) by a single sentence -/
def Isol {L : Sig} (T : Theory L) : Prop :=
  ∃ (M : Model T) (Γ : Fin 0 → L.Srt) (φ : Formula L Γ), (∀ v, φ.Realize M.str v) ∧
    ∀ N : Model T, (∀ v, φ.Realize N.str v) → Nonempty (N ⟶ M)

theorem reach_iff {L₁ : Sig} {T₁ : Theory L₁} {L₂ : Sig} {T₂ : Theory L₂}
    (h : MoritaReach T₁ T₂) : Isol T₁ ↔ Isol T₂ := by
  induction h with
  | refl T => exact Iff.rfl
  | step D _ ih => exact (MoritaData.exists_isolated_model_iff D).trans ih

/-- reduct of an elementary embedding along a signature morphism -/
def redEmb {L L' : Sig} (F : L.Hom L') {M N : Str L'} (g : ElemEmb M N) :
    ElemEmb (M.reduct F) (N.reduct F) where
  toFun s := g.toFun (F.onSrt s)
  map_formula φ v :=
    (Formula.realize_onFormula F N φ _).symm.trans
      ((g.map_formula (φ.onFormula F) v).trans (Formula.realize_onFormula F M φ v))

theorem rename {L₁ L₂ : Sig} {T₁ : Theory L₁} {T₂ : Theory L₂} {F : L₁.Hom L₂}
    (hF : F.IsRenaming) (hT : ∀ M : Str L₂, M.IsModel T₂ ↔ (M.reduct F).IsModel T₁) :
    Isol T₂ → Isol T₁ := by
  rintro ⟨M₂, Δ, φ, hM, hiso⟩
  have hΔ : Δ = F.onSrt ∘ (fun i : Fin 0 => i.elim0) := funext fun i => i.elim0
  subst hΔ
  obtain ⟨ψ, hψ⟩ := Sig.Hom.IsRenaming.exists_formula_pullback hF (fun i : Fin 0 => i.elim0) φ
  let M₁ : Model T₁ := ⟨M₂.str.reduct F, (hT _).1 M₂.isModel⟩
  refine ⟨M₁, _, ψ, fun v => (Formula.realize_onFormula F M₂.str ψ v).1 ((hψ _ v).1 (hM v)), ?_⟩
  intro N₁ hN
  obtain ⟨P, ⟨h⟩, ⟨h'⟩⟩ := Sig.Hom.IsRenaming.exists_reduct_biembedding hF N₁.str
  have hmod : (P.reduct F).IsModel T₁ := fun A hA v => (h.map_formula A.φ v).1 (N₁.isModel A hA _)
  let N₂ : Model T₂ := ⟨P, (hT _).2 hmod⟩
  have hP : ∀ v, φ.Realize P v := fun v =>
    (hψ P v).2 ((Formula.realize_onFormula F P ψ v).2 ((sent_emb h ψ).1 hN v))
  obtain ⟨g⟩ := hiso N₂ hP
  exact ⟨ElemEmb.comp (redEmb F g) h'⟩

open Thm52 T52C

/-- the predicate indices `< bnd φ` are the only ones `φ` can mention -/
def ridx {m : ℕ} {dom : Fin m → Unit} (r : PRel m dom) : ℕ := match r with | .p i => i + 1

def bnd : {n : ℕ} → {Γ : Fin n → sig.Srt} → Formula sig Γ → ℕ
  | _, _, .falsum => 0
  | _, _, .equal _ _ => 0
  | _, _, .rel r _ => ridx r
  | _, _, .imp φ ψ => max (bnd φ) (bnd ψ)
  | _, _, .all φ => bnd φ

theorem agree (S S' : Set ℕ) {n : ℕ} {Γ : Fin n → sig.Srt} (φ : Formula sig Γ)
    (h : ∀ i < bnd φ, (i ∈ S ↔ i ∈ S')) (v : (i : Fin n) → Unit) :
    φ.Realize (mk S) v ↔ φ.Realize (mk S') v := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ =>
    exact iff_of_true (Subsingleton.elim (α := Unit) _ _) (Subsingleton.elim (α := Unit) _ _)
  | rel r args =>
    cases r with
    | p i => exact h i (Nat.lt_succ_self i)
  | imp φ ψ ih₁ ih₂ =>
    exact imp_congr (ih₁ (fun i hi => h i (lt_max_of_lt_left hi)) v)
      (ih₂ (fun i hi => h i (lt_max_of_lt_right hi)) v)
  | all φ ih => exact forall_congr' fun a => ih h _

theorem T1_not_isol : ¬ Isol T1 := by
  rintro ⟨M, Γ, φ, hM, hiso⟩
  have hM1 := one_of (T1_sat M)
  set S := pset M.str
  set k := bnd φ
  let S' : Set ℕ := {i | i ∈ S ↔ i ≠ k}
  obtain ⟨e⟩ := (hom_iff hM1 (one_of (mk_sat S))).2 (mk_pset S).symm
  have hS : ∀ v, φ.Realize (mk S) v := (sent_emb e φ).2 hM
  have hS' : ∀ v, φ.Realize (mk S') v := fun v =>
    (agree S S' φ (fun i hi => by
      have : i ≠ k := Nat.ne_of_lt hi
      show i ∈ S ↔ (i ∈ S ↔ i ≠ k)
      simp [this]) v).1 (hS v)
  let N : Model T1 := ⟨mk S', by rintro A rfl; exact mk_sat S'⟩
  obtain ⟨g⟩ := hiso N hS'
  have heq := (hom_iff (one_of (mk_sat S')) hM1).1 ⟨g⟩
  rw [mk_pset] at heq
  have hk := Set.ext_iff.1 heq k
  change (k ∈ S ↔ k ≠ k) ↔ k ∈ S at hk
  by_cases h : k ∈ S <;> simp_all

theorem T2_isol : Isol T2 := by
  refine ⟨⟨mk Set.univ, mk_T2 _ (fun _ _ => trivial)⟩, uctx 0,
    Formula.exS (L := sig) (Γ := uctx 0) () (pAt 0), fun v h => h () trivial, ?_⟩
  intro N hN
  have hN1 := one_of (T2_sat N)
  have h0 : 0 ∈ pset N.str := by
    obtain ⟨x⟩ := N.str.nonempty ()
    by_contra hc
    apply hN (fun i => i.elim0)
    intro a ha
    exact hc ((pset_iff hN1 0 _).1 ha)
  have hu : pset N.str = Set.univ := Set.eq_univ_of_forall (T2_good N h0)
  obtain ⟨g⟩ := (hom_iff hN1 (one_of (mk_sat Set.univ))).2 (hu.trans (mk_pset _).symm)
  exact ⟨g⟩

theorem t52n_main : ¬ MoritaEquivalent T1 T2 := by
  rintro ⟨L₁', L₂', T₁', T₂', F, h₁, h₂, hF, hT⟩
  exact T1_not_isol ((reach_iff h₁).2 (rename hF hT ((reach_iff h₂).1 T2_isol)))

end T52N
end MoritaEquiv

theorem solution : ¬ MoritaEquiv.MoritaEquivalent MoritaEquiv.Thm52.T1 MoritaEquiv.Thm52.T2 :=
  MoritaEquiv.T52N.t52n_main
