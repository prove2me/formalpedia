-- Prove2me | solution 1 for JardenShami.mk_lim_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:02.879019+00:00
-- url     : https://prove2.me/submissions/bd4fadf2-e183-4de2-b514-cfa25ee0b0df

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_mk_coe
import Theorems.Thm_JardenShami_Kappa_mk_eq
import Theorems.Thm_JardenShami_Tree_ht_injOn_of_isChain
import Theorems.Thm_JardenShami_Tree_ht_lt_height
attribute [local simp] JardenShami.Kappa.coe_mk
attribute [local simp] JardenShami.Kappa.mk_coe



set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution {T : Type w} [PartialOrder T] [IsTree T] {μ : Cardinal.{w}}
    (hT : height T = μ.ord) : #(Lim T) ≤ (#T + 1) ^ μ := by
  classical
  let Φ : Lim T → (Kappa μ → Option T) := fun b α =>
    if h : ∃ x ∈ b.1, ht x = (α : Ordinal.{w}) then some h.choose else none
  have hsub : ∀ b b' : Lim T, Φ b = Φ b' → b.1 ⊆ b'.1 := by
    intro b b' e x hx
    have hlt : ht x < μ.ord := hT ▸ ht_lt_height x
    let α : Kappa μ := Kappa.mk (ht x) hlt
    have hex : ∃ y ∈ b.1, ht y = (α : Ordinal.{w}) := ⟨x, hx, (Kappa.coe_mk _ _).symm⟩
    have hy : hex.choose = x := ht_injOn_of_isChain b.2.1.1 hex.choose_spec.1 hx
      (hex.choose_spec.2.trans (Kappa.coe_mk _ _))
    have h1 : Φ b α = some x := by
      simp only [Φ, dif_pos hex, hy]
    rw [e] at h1
    by_cases hex' : ∃ y ∈ b'.1, ht y = (α : Ordinal.{w})
    · simp only [Φ, dif_pos hex', Option.some.injEq] at h1
      exact h1 ▸ hex'.choose_spec.1
    · simp [Φ, hex'] at h1
  have hinj : Function.Injective Φ := fun b b' e =>
    Subtype.ext ((hsub b b' e).antisymm (hsub b' b e.symm))
  calc #(Lim T) ≤ #(Kappa μ → Option T) := Cardinal.mk_le_of_injective hinj
    _ = (#T + 1) ^ μ := by rw [← Cardinal.power_def, Cardinal.mk_option, Kappa.mk_eq]
end JardenShami
