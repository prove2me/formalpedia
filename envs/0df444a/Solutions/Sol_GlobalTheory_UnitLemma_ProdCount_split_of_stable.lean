-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ProdCount.split_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:59:05.002886+00:00
-- url     : https://prove2.me/submissions/fb9a68aa-f4e3-47c7-a22c-500e659de559

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ProdCount
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
variable {O : Type} [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [Algebra O A₁] [CommRing A₂] [Algebra O A₂]
namespace GlobalTheory.UnitLemma.ProdCount
theorem _root_.solution (g : A₁ × A₂) (he : ((1, 0) : A₁ × A₂) ∈ Algebra.adjoin O ({g} : Set (A₁ × A₂)))
    (L : Submodule O (A₁ × A₂)) (hL : ∀ y ∈ L, g * y ∈ L) : ∃ L₁ L₂, L = Submodule.prod L₁ L₂ := by
  have hall : ∀ u ∈ Algebra.adjoin O ({g} : Set (A₁ × A₂)), ∀ y ∈ L, u * y ∈ L := by
    intro u hu
    induction hu using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hL
    | algebraMap a => intro y hy; rw [← Algebra.smul_def]; exact L.smul_mem a hy
    | add a b _ _ ha hb => intro y hy; rw [add_mul]; exact L.add_mem (ha y hy) (hb y hy)
    | mul a b _ _ ha hb => intro y hy; rw [mul_assoc]; exact ha _ (hb y hy)
  refine ⟨L.comap (LinearMap.inl O A₁ A₂), L.comap (LinearMap.inr O A₁ A₂), ?_⟩
  ext ⟨a, b⟩
  simp only [Submodule.mem_prod, Submodule.mem_comap, LinearMap.inl_apply, LinearMap.inr_apply]
  constructor
  · intro h
    have h1 : ((a, 0) : A₁ × A₂) ∈ L := by simpa using hall _ he _ h
    exact ⟨h1, by simpa using L.sub_mem h h1⟩
  · rintro ⟨h1, h2⟩
    simpa using L.add_mem h1 h2
end GlobalTheory.UnitLemma.ProdCount
