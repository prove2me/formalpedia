-- Prove2me | solution 1 for MoritaEquiv.MoritaData.exists_isolated_model_iff
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-13T20:05:37.534631+00:00
-- url     : https://prove2.me/submissions/5a1be037-9e0e-4f03-ba77-049604f70909

import Mathlib
import Definitions.Def_MoritaEquiv_defs
import Theorems.Thm_MoritaEquiv_proj_full
import Theorems.Thm_MoritaEquiv_expansion_exists_unique
import Theorems.Thm_MoritaEquiv_translation

open CategoryTheory

namespace MoritaEquiv
namespace MIS

/-- sentence truth is transported along any elementary embedding -/
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

variable {L : Sig} {T : Theory L} (D : MoritaData L T)

theorem proj_sent (N : Model D.ext) {Γ : Fin 0 → L.Srt} (φ : Formula L Γ) :
    (∀ v, (φ.onFormula D.incl).Realize N.str v) ↔ ∀ v, φ.Realize (D.proj.obj N).str v :=
  forall_congr' fun v => Formula.realize_onFormula D.incl N.str φ v

theorem fwd :
    (∃ (M : Model T) (Γ : Fin 0 → L.Srt) (φ : Formula L Γ), (∀ v, φ.Realize M.str v) ∧
      ∀ N : Model T, (∀ v, φ.Realize N.str v) → Nonempty (N ⟶ M)) →
    (∃ (M : Model D.ext) (Γ : Fin 0 → D.sig.Srt) (φ : Formula D.sig Γ), (∀ v, φ.Realize M.str v) ∧
      ∀ N : Model D.ext, (∀ v, φ.Realize N.str v) → Nonempty (N ⟶ M)) := by
  have := proj_full D
  rintro ⟨M, Γ, φ, hM, hiso⟩
  obtain ⟨⟨N₀, ⟨e⟩⟩, -⟩ := expansion_exists_unique D M
  refine ⟨N₀, _, φ.onFormula D.incl, ?_, ?_⟩
  · exact (proj_sent D N₀ φ).2 ((sent_emb e.hom φ).1 hM)
  · intro N hN
    obtain ⟨g⟩ := hiso (D.proj.obj N) ((proj_sent D N φ).1 hN)
    exact ⟨D.proj.preimage (g ≫ e.inv)⟩

theorem bwd :
    (∃ (M : Model D.ext) (Γ : Fin 0 → D.sig.Srt) (φ : Formula D.sig Γ), (∀ v, φ.Realize M.str v) ∧
      ∀ N : Model D.ext, (∀ v, φ.Realize N.str v) → Nonempty (N ⟶ M)) →
    (∃ (M : Model T) (Γ : Fin 0 → L.Srt) (φ : Formula L Γ), (∀ v, φ.Realize M.str v) ∧
      ∀ N : Model T, (∀ v, φ.Realize N.str v) → Nonempty (N ⟶ M)) := by
  rintro ⟨N₀, Δ, φ, hN₀, hiso⟩
  have hΔ : Δ = D.incl.onSrt ∘ (fun i : Fin 0 => i.elim0) := funext fun i => i.elim0
  subst hΔ
  obtain ⟨ψ, hψ⟩ := translation D (fun i : Fin 0 => i.elim0) φ
  have key : ∀ N : Model D.ext, (∀ v, φ.Realize N.str v) ↔ ∀ v, ψ.Realize (D.proj.obj N).str v :=
    fun N => (forall_congr' fun v => hψ N v).trans (proj_sent D N ψ)
  refine ⟨D.proj.obj N₀, _, ψ, (key N₀).1 hN₀, ?_⟩
  intro M hM
  obtain ⟨⟨N, ⟨e⟩⟩, -⟩ := expansion_exists_unique D M
  obtain ⟨g⟩ := hiso N ((key N).2 ((sent_emb e.inv ψ).2 hM))
  exact ⟨e.inv ≫ D.proj.map g⟩

theorem mis_main {L : Sig} {T : Theory L} (D : MoritaData L T) :
    (∃ (M : Model T) (Γ : Fin 0 → L.Srt) (φ : Formula L Γ), (∀ v, φ.Realize M.str v) ∧
      ∀ N : Model T, (∀ v, φ.Realize N.str v) → Nonempty (N ⟶ M)) ↔
    (∃ (M : Model D.ext) (Γ : Fin 0 → D.sig.Srt) (φ : Formula D.sig Γ), (∀ v, φ.Realize M.str v) ∧
      ∀ N : Model D.ext, (∀ v, φ.Realize N.str v) → Nonempty (N ⟶ M)) :=
  ⟨fwd D, bwd D⟩

end MIS
end MoritaEquiv

open MoritaEquiv in
theorem solution {L : Sig} {T : Theory L} (D : MoritaData L T) :
    (∃ (M : Model T) (Γ : Fin 0 → L.Srt) (φ : Formula L Γ), (∀ v, φ.Realize M.str v) ∧
      ∀ N : Model T, (∀ v, φ.Realize N.str v) → Nonempty (N ⟶ M)) ↔
    (∃ (M : Model D.ext) (Γ : Fin 0 → D.sig.Srt) (φ : Formula D.sig Γ), (∀ v, φ.Realize M.str v) ∧
      ∀ N : Model D.ext, (∀ v, φ.Realize N.str v) → Nonempty (N ⟶ M)) :=
  MoritaEquiv.MIS.mis_main D
