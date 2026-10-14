-- Prove2me | solution 1 for MoritaEquiv.Sig.Hom.IsRenaming.exists_formula_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-13T20:05:35.514699+00:00
-- url     : https://prove2.me/submissions/accd5f76-9db3-4c1a-a3bf-619d56dc2d17

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv
namespace RNP

variable {L L' : Sig} {F : L.Hom L'}

theorem term_pull (hF : F.IsRenaming) {n : ℕ} (Γ : Fin n → L.Srt) {s : L'.Srt}
    (t : Term L' (F.onSrt ∘ Γ) s) :
    ∀ (s₀ : L.Srt) (hs : F.onSrt s₀ = s), ∃ u : Term L Γ s₀, ∀ (M : Str L')
      (v : (i : Fin n) → M.carrier (F.onSrt (Γ i))),
      t.realize M v = cast (congrArg M.carrier hs) ((u.onTerm F).realize M v) := by
  induction t with
  | var i =>
    intro s₀ hs
    have : s₀ = Γ i := hF.srt.1 hs
    subst this
    exact ⟨Term.var i, fun M v => rfl⟩
  | @func m dom s f args ih =>
    intro s₀ hs
    subst hs
    obtain ⟨dom₀, rfl⟩ : ∃ dom₀ : Fin m → L.Srt, F.onSrt ∘ dom₀ = dom :=
      ⟨fun j => (hF.srt.2 (dom j)).choose, funext fun j => (hF.srt.2 (dom j)).choose_spec⟩
    obtain ⟨f₀, rfl⟩ := (hF.func (dom := dom₀) (s := s₀)).2 f
    choose u hu using fun j => ih j (dom₀ j) rfl
    refine ⟨Term.func f₀ u, fun M v => ?_⟩
    show M.funMap (F.onFunc f₀) _ = M.funMap (F.onFunc f₀) _
    exact congrArg _ (funext fun j => hu j M v)

theorem form_pull (hF : F.IsRenaming) {n : ℕ} {Δ : Fin n → L'.Srt} (φ : Formula L' Δ) :
    ∀ (Γ : Fin n → L.Srt) (hΓ : F.onSrt ∘ Γ = Δ), ∃ ψ : Formula L Γ, ∀ (M : Str L')
      (v : (i : Fin n) → M.carrier (Δ i)),
      φ.Realize M v ↔ (ψ.onFormula F).Realize M (cast (by subst hΓ; rfl) v) := by
  induction φ with
  | falsum =>
    intro Γ hΓ; subst hΓ
    exact ⟨Formula.falsum, fun M v => Iff.rfl⟩
  | @equal n Δ s t₁ t₂ =>
    intro Γ hΓ; subst hΓ
    obtain ⟨u₁, hu₁⟩ := term_pull hF Γ t₁ _ (hF.srt.2 s).choose_spec
    obtain ⟨u₂, hu₂⟩ := term_pull hF Γ t₂ _ (hF.srt.2 s).choose_spec
    refine ⟨Formula.equal u₁ u₂, fun M v => ?_⟩
    show t₁.realize M v = t₂.realize M v ↔ (u₁.onTerm F).realize M v = (u₂.onTerm F).realize M v
    rw [hu₁ M v, hu₂ M v]
    exact cast_inj _
  | @rel n Δ m dom r args =>
    intro Γ hΓ; subst hΓ
    obtain ⟨dom₀, rfl⟩ : ∃ dom₀ : Fin m → L.Srt, F.onSrt ∘ dom₀ = dom :=
      ⟨fun j => (hF.srt.2 (dom j)).choose, funext fun j => (hF.srt.2 (dom j)).choose_spec⟩
    obtain ⟨r₀, rfl⟩ := (hF.rel (dom := dom₀)).2 r
    choose u hu using fun j => term_pull hF Γ (args j) (dom₀ j) rfl
    refine ⟨Formula.rel r₀ u, fun M v => ?_⟩
    show M.relMap (F.onRel r₀) _ ↔ M.relMap (F.onRel r₀) _
    exact iff_of_eq (congrArg _ (funext fun j => hu j M v))
  | imp φ ψ ihφ ihψ =>
    intro Γ hΓ; subst hΓ
    obtain ⟨a, ha⟩ := ihφ Γ rfl
    obtain ⟨b, hb⟩ := ihψ Γ rfl
    exact ⟨Formula.imp a b, fun M v => imp_congr (ha M v) (hb M v)⟩
  | @all n Γ' φ ih =>
    intro Γ hΓ
    obtain ⟨Γ₁, rfl⟩ : ∃ Γ₁ : Fin (n + 1) → L.Srt, F.onSrt ∘ Γ₁ = Γ' :=
      ⟨fun j => (hF.srt.2 (Γ' j)).choose, funext fun j => (hF.srt.2 (Γ' j)).choose_spec⟩
    have : Γ = Fin.tail Γ₁ := funext fun i => hF.srt.1 (congrFun hΓ i)
    subst this
    obtain ⟨ψ, hψ⟩ := ih Γ₁ rfl
    exact ⟨Formula.all ψ, fun M v => forall_congr' fun a => hψ M _⟩

theorem rnp_main {L L' : Sig} {F : L.Hom L'} (hF : F.IsRenaming) {n : ℕ} (Γ : Fin n → L.Srt)
    (φ : Formula L' (F.onSrt ∘ Γ)) :
    ∃ ψ : Formula L Γ, ∀ (M : Str L') (v : (i : Fin n) → M.carrier (F.onSrt (Γ i))),
      φ.Realize M v ↔ (ψ.onFormula F).Realize M v :=
  form_pull hF φ Γ rfl

end RNP
end MoritaEquiv

open MoritaEquiv in
theorem solution {L L' : Sig} {F : L.Hom L'} (hF : F.IsRenaming)
    {n : ℕ} (Γ : Fin n → L.Srt) (φ : Formula L' (F.onSrt ∘ Γ)) :
    ∃ ψ : Formula L Γ, ∀ (M : Str L') (v : (i : Fin n) → M.carrier (F.onSrt (Γ i))),
      φ.Realize M v ↔ (ψ.onFormula F).Realize M v :=
  MoritaEquiv.RNP.rnp_main hF Γ φ
