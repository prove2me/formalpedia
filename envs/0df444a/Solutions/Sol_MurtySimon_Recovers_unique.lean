-- Prove2me | solution 1 for MurtySimon.Recovers.unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:01:54.633676+00:00
-- url     : https://prove2.me/submissions/fdfd6ebd-6ea4-49ce-afb6-62c346bc5b4d

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
public import Theorems.Thm_MurtySimon_IsMid_symm
public import Theorems.Thm_MurtySimon_IsMid_unique


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable {M : Finset (Sym2 V)}
namespace MurtySimon
namespace Recovers
theorem _root_.solution {p : V × V} {ℓ₁ ℓ₂ : Sym2 V} (h₁ : Recovers (G := G) (M := M) p ℓ₁)
    (h₂ : Recovers (G := G) (M := M) p ℓ₂) (hℓ₁ : ℓ₁ ∈ G.edgeSet) (hℓ₂ : ℓ₂ ∈ G.edgeSet) :
    ℓ₁ = ℓ₂ := by
  rcases h₁ with h₁ | ⟨z₁, u₁, hz₁, hm₁, rfl⟩ <;> rcases h₂ with h₂ | ⟨z₂, u₂, hz₂, hm₂, rfl⟩
  · exact h₁.symm.trans h₂
  · have : s(z₂, p.2) ∈ G.edgeSet := by rw [← hz₂, h₁]; exact hℓ₁
    exact absurd this hm₂.2.1
  · have : s(z₁, p.2) ∈ G.edgeSet := by rw [← hz₁, h₂]; exact hℓ₂
    exact absurd this hm₁.2.1
  · have hz : z₁ = z₂ := Sym2.congr_left.1 (hz₁.symm.trans hz₂)
    subst hz
    rw [hm₁.unique hm₂]
end Recovers
end MurtySimon
