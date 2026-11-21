-- Prove2me | solution 1 for JardenShami.laArrowKappa_of_forall_branch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:46.834362+00:00
-- url     : https://prove2.me/submissions/2a14b995-6a9b-47fe-bcc1-1a1039eaa3b4

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_Kappa_mk_eq
import Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_eq
import Theorems.Thm_JardenShami_Kappa_exists_sparse
import Theorems.Thm_JardenShami_fiberRestr_eq_fiberRestr
import Theorems.Thm_JardenShami_height_treeOfColoring
import Theorems.Thm_JardenShami_card_lev_treeOfColoring_le_of_aleph0_le
import Theorems.Thm_JardenShami_Pairs_exists_eq_mk


set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hμ : μ < κ)
    (h1 : ∀ (T : Type w) [PartialOrder T] [IsTree T], height T = κ.ord →
        (∀ α : Ordinal.{w}, #(Lev T α) ≤ μ) → ∃ b : Set T, IsBranch b ∧ #b = κ) :
    LaArrowKappa κ μ := by
  classical
  have hκ0 : ℵ₀ ≤ κ := hκ.aleph0_le
  intro C hC
  obtain ⟨B, hB, hBc⟩ := h1 (treeOfColoring C) (height_treeOfColoring C)
    (card_lev_treeOfColoring_le_of_aleph0_le κ μ hκ0 C hC)
  choose dg bg hbg hg using fun g : treeOfColoring C => g.2
  -- the levels of the nodes of `B` are unbounded in `κ`
  have hinj : Set.InjOn bg B := by
    intro g hgB g' hg'B he
    refine Subtype.ext ?_
    rw [hg g, hg g']
    rcases hB.1.total hgB hg'B with h | h
    · have hs : fiberRestr C (dg g) (bg g) (hbg g) ⊆ fiberRestr C (dg g') (bg g') (hbg g') := by
        rw [← hg g, ← hg g']
        exact h
      exact fiberRestr_eq_fiberRestr _ _ he ((fiberRestr_subset_iff _ _).1 hs).2
    · have hs : fiberRestr C (dg g') (bg g') (hbg g') ⊆ fiberRestr C (dg g) (bg g) (hbg g) := by
        rw [← hg g, ← hg g']
        exact h
      exact (fiberRestr_eq_fiberRestr _ _ he.symm ((fiberRestr_subset_iff _ _).1 hs).2).symm
  have hcard : #(bg '' B) = κ := by rw [Cardinal.mk_image_eq_of_injOn _ _ hinj, hBc]
  have hunb : ∀ γ : Kappa κ, ∃ g ∈ B, γ < bg g := by
    intro γ
    obtain ⟨_, ⟨g, hgB, rfl⟩, hγ⟩ := Kappa.exists_gt_of_card_eq hκ0 hcard γ
    exact ⟨g, hgB, hγ⟩
  choose G hGB hGb using hunb
  -- `F γ > γ` and `C(α, F γ) = C(α, F α)` for `α ≤ γ`
  let F : Kappa κ → Kappa κ := fun γ => dg (G γ)
  have hF : ∀ γ, γ < F γ := fun γ => (hGb γ).trans_le (hbg _)
  have hchain : ∀ α γ : Kappa κ, (hαγ : α ≤ γ) →
      C.color α (F γ) (hαγ.trans_lt (hF γ)) = C.color α (F α) (hF α) := by
    intro α γ hαγ
    have hα₁ : α < bg (G α) := hGb α
    have hα₂ : α < bg (G γ) := hαγ.trans_lt (hGb γ)
    rcases hB.1.total (hGB α) (hGB γ) with h | h
    · have hs : fiberRestr C (dg (G α)) (bg (G α)) (hbg _) ⊆
          fiberRestr C (dg (G γ)) (bg (G γ)) (hbg _) := by
        rw [← hg, ← hg]
        exact h
      exact (((fiberRestr_subset_iff _ _).1 hs).2 α hα₁ hα₂).symm
    · have hs : fiberRestr C (dg (G γ)) (bg (G γ)) (hbg _) ⊆
          fiberRestr C (dg (G α)) (bg (G α)) (hbg _) := by
        rw [← hg, ← hg]
        exact h
      exact ((fiberRestr_subset_iff _ _).1 hs).2 α hα₂ hα₁
  -- pigeonhole: `κ` many `γ` with the same color `C(F γ, F (F γ))`
  have hK : #(Kappa κ) = κ := Kappa.mk_eq κ
  obtain ⟨c, Γ, hΓs, hΓc, hΓ⟩ := Cardinal.infinite_pigeonhole_set
    (s := (Set.univ : Set (Kappa κ)))
    (fun γ => C.color (F γ) (F (F γ)) (hF (F γ))) κ
    (by rw [Cardinal.mk_univ, hK]) hκ0
    (by rw [Kappa.mk_eq, hκ.cof_ord]; exact hμ)
  have hΓκ : #Γ = κ := le_antisymm ((Cardinal.mk_set_le Γ).trans hK.le) hΓc
  -- thin out `Γ`
  obtain ⟨Γ', hΓ'Γ, hΓ'κ, hsp⟩ := Kappa.exists_sparse hκ hΓκ F
  refine ⟨F '' Γ', ?_, ?_⟩
  · have hinjF : Set.InjOn F Γ' := by
      intro x hx y hy hxy
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact (hxy ▸ (hsp x hx y hy h)).not_gt (hF y) |>.elim
      · exact (hxy ▸ (hsp y hy x hx h)).not_gt (hF x) |>.elim
    rw [Cardinal.mk_image_eq_of_injOn _ _ hinjF, hΓ'κ]
  · -- every pair from `F '' Γ'` has color `c`
    have key : ∀ p : Pairs (Kappa κ), (∀ x ∈ p.1, x ∈ F '' Γ') → C p = c := by
      intro p hp
      obtain ⟨x, y, hxy, rfl⟩ := p.exists_eq_mk
      obtain ⟨γ₀, hγ₀, rfl⟩ := hp x (Sym2.mem_mk_left x y)
      obtain ⟨γ, hγ, rfl⟩ := hp y (Sym2.mem_mk_right _ y)
      have hlt : γ₀ < γ := by
        rcases lt_trichotomy γ₀ γ with h | rfl | h
        · exact h
        · exact absurd hxy (lt_irrefl _)
        · exact absurd hxy ((hsp γ hγ γ₀ hγ₀ h).trans (hF γ₀)).not_gt
      change C.color (F γ₀) (F γ) hxy = c
      rw [hchain (F γ₀) γ (hsp γ₀ hγ₀ γ hγ hlt).le]
      exact hΓ (hΓ'Γ hγ₀)
    intro p q hp hq
    rw [key p hp, key q hq]
end JardenShami
