-- Prove2me | solution 1 for JardenShami.arrow_la_of_arrow_add_of_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:05.954772+00:00
-- url     : https://prove2.me/submissions/1a0ed9b6-b390-46e7-9bda-836c3818f25d

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Theorems.Thm_JardenShami_Pairs_mk_inj
import Theorems.Thm_JardenShami_isHomogeneous_iff_color
import Theorems.Thm_JardenShami_Pairs_map_mk
import Theorems.Thm_JardenShami_uMap_wellDefined_iff


set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
variable {X : Type w} [LinearOrder X]
namespace JardenShami
theorem _root_.solution (P Q : Cardinal.{v} → Prop)
    (hPQ : ∀ D : Type v, P #D → Q #D ∧ Q #(D → Option D)) (F : Set (Set X))
    (h : Arrow F F (fun _ D C => IsAdditive C ∧ Q #D)) :
    Arrow F F (fun _ D C => IsLocallyAdditive C ∧ P #D) := by
  classical
  rintro S hS D C ⟨hla, hD⟩
  have hwd := (uMap_wellDefined_iff C).2 hla
  -- `R p t v`: `p = {a, b}` with `a < b`, and `v = u_{a,b}(t)` with witness `c`.
  let R : Pairs S → D → D → Prop := fun p t v => ∃ (a b c : S) (hab : a < b) (hbc : b < c),
    p = Pairs.mk a b hab.ne ∧ C.color b c hbc = t ∧ C.color a c (hab.trans hbc) = v
  -- `C*(a,b) = u_{a,b}`, as a partial function `D → Option D` with domain `D_b`.
  let Cs : Coloring S (D → Option D) := fun p t =>
    if hv : ∃ v, R p t v then some hv.choose else none
  have key1 : ∀ (a b c : S) (hab : a < b) (hbc : b < c),
      Cs.color a b hab (C.color b c hbc) = some (C.color a c (hab.trans hbc)) := by
    intro a b c hab hbc
    have hex : ∃ v, R (Pairs.mk a b hab.ne) (C.color b c hbc) v :=
      ⟨_, a, b, c, hab, hbc, rfl, rfl, rfl⟩
    change (if hv : ∃ v, R (Pairs.mk a b hab.ne) (C.color b c hbc) v then some hv.choose
      else none) = _
    rw [dif_pos hex]
    obtain ⟨a', b', c', hab', hbc', hp, ht, hv⟩ := hex.choose_spec
    obtain ⟨rfl, rfl⟩ := Pairs.mk_inj hab hab' hp
    rw [← hv]
    exact congrArg some (hwd a b c' c hab hbc' hbc ht)
  have key2 : ∀ (a b : S) (hab : a < b) (t : D),
      (¬ ∃ (c : S) (hbc : b < c), C.color b c hbc = t) → Cs.color a b hab t = none := by
    intro a b hab t hn
    change (if hv : ∃ v, R (Pairs.mk a b hab.ne) t v then some hv.choose else none) = _
    have hn' : ¬ ∃ v, R (Pairs.mk a b hab.ne) t v := by
      rintro ⟨v, a', b', c', hab', hbc', hp, ht, -⟩
      obtain ⟨rfl, rfl⟩ := Pairs.mk_inj hab hab' hp
      exact hn ⟨c', hbc', ht⟩
    rw [dif_neg hn']
  -- Claim 2.8: `C*` is additive, with `s(f, g) = f ∘ g` (composition of partial functions).
  have hadd : IsAdditive Cs := by
    refine ⟨fun fg t => (fg.2 t).bind fg.1, ?_⟩
    intro a b c hab hbc
    funext t
    change Cs.color a c (hab.trans hbc) t = (Cs.color b c hbc t).bind (Cs.color a b hab)
    by_cases ht : ∃ (d : S) (hcd : c < d), C.color c d hcd = t
    · obtain ⟨d, hcd, rfl⟩ := ht
      rw [key1 b c d hbc hcd, Option.bind_some, key1 a b d hab (hbc.trans hcd),
        key1 a c d (hab.trans hbc) hcd]
    · rw [key2 b c hbc t ht, Option.bind_none, key2 a c (hab.trans hbc) t ht]
  obtain ⟨B, hBF, hBhom⟩ := h S hS (D → Option D) Cs ⟨hadd, (hPQ D hD).2⟩
  -- The coloring `C ↾ [B]^2`, as a coloring of `B` viewed as a subset of `X`.
  have hsub : ∀ x ∈ Subtype.val '' B, x ∈ S := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  let ι : (Subtype.val '' B : Set X) → S := fun x => ⟨x.1, hsub x.1 x.2⟩
  have hιB : ∀ x, ι x ∈ B := by
    rintro ⟨x, y, hy, rfl⟩
    exact hy
  have hι : StrictMono ι := fun _ _ h => h
  let Cb : Coloring (Subtype.val '' B : Set X) D := fun p => C (Pairs.map ι hι.injective p)
  have hCb : ∀ a b (hab : a < b), Cb.color a b hab = C.color (ι a) (ι b) (hι hab) := by
    intro a b hab
    exact congrArg C (Pairs.map_mk ι hι.injective a b hab.ne)
  -- `C ↾ [B]^2` is additive, with `s(x, y) = f(y)` where `f` is the constant value of `C*`.
  have hCbadd : IsAdditive Cb := by
    by_cases hp : ∃ (a b : S) (_ : a < b), a ∈ B ∧ b ∈ B
    · obtain ⟨a₀, b₀, h₀, ha₀, hb₀⟩ := hp
      refine ⟨fun xy => (Cs.color a₀ b₀ h₀ xy.2).getD xy.1, ?_⟩
      intro a b c hab hbc
      rw [hCb, hCb, hCb]
      have hc : Cs.color (ι a) (ι b) (hι hab) = Cs.color a₀ b₀ h₀ :=
        (isHomogeneous_iff_color Cs B).1 hBhom _ _ _ _ _ _ (hιB a) (hιB b) ha₀ hb₀
      change _ = (Cs.color a₀ b₀ h₀ (C.color (ι b) (ι c) (hι hbc))).getD _
      rw [← hc, key1]
      rfl
    · refine ⟨Prod.fst, ?_⟩
      intro a b c hab hbc
      exact absurd ⟨ι a, ι b, hι hab, hιB a, hιB b⟩ hp
  obtain ⟨E, hEF, hEhom⟩ := h _ hBF D Cb ⟨hCbadd, (hPQ D hD).1⟩
  refine ⟨ι '' E, ?_, ?_⟩
  · rw [Set.image_image]
    exact hEF
  · rw [isHomogeneous_iff_color]
    rintro _ _ _ _ hab hcd ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact (hCb a b hab).symm.trans
      (((isHomogeneous_iff_color Cb E).1 hEhom a b c d hab hcd ha hb hc hd).trans (hCb c d hcd))
end JardenShami
