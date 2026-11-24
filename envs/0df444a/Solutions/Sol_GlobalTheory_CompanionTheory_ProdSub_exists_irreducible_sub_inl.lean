-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdSub.exists_irreducible_sub_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:28:03.762797+00:00
-- url     : https://prove2.me/submissions/e4b7af87-c85c-4359-a31f-f348fa906fc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIrreducibleOfFixed
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_mem_fixed_iff_forall
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_exists_irreducible_of_fixed
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_inl_inr_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_exists_fixed_of_ne_bot
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdSub
namespace GlobalTheory.CompanionTheory.ProdSub
theorem _root_.solution : ∀ {G H V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup V] [Module ℂ V], (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → (∀ U ∈ 𝓝 (1 : H), ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H) ∧ (K : Set H) ⊆ U) → ∀ ρ : Representation ℂ (G × H) V, IsAdmissible ρ → ρ.IsIrreducible → ∃ (K : Subgroup G) (S : Subrepresentation (ρ.comp (MonoidHom.inl G H))) (u : V), IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ u ∈ S.toSubmodule ∧ u ≠ 0 ∧ (∀ x ∈ K, ρ (x, 1) u = u) ∧ S.toRepresentation.IsIrreducible ∧ FiniteDimensional ℂ (fixed S.toRepresentation K) := by
  intro G H V _ _ _ _ _ _ _ _ hG hH ρ hadm hi
  haveI : IsSimpleOrder (Subrepresentation ρ) := hi
  obtain ⟨v, hv0⟩ : ∃ v : V, v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    apply Subrepresentation.ext
    ext x
    rw [hcon x]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  have hU : {gh : G × H | ρ gh v = v} ∈ 𝓝 ((1 : G), (1 : H)) :=
    (hadm.1 v).mem_nhds (by show ρ (1, 1) v = v; rw [Prod.mk_one_one, map_one, Module.End.one_apply])
  obtain ⟨U1, hU1, U2, hU2, hUU⟩ := mem_nhds_prod_iff.mp hU
  obtain ⟨K1, hK1o, hK1c, hK1U⟩ := hG U1 hU1
  obtain ⟨K2, hK2o, hK2c, hK2U⟩ := hH U2 hU2
  have hfix : ∀ k1 ∈ K1, ∀ k2 ∈ K2, ρ (k1, k2) v = v := fun k1 hk1 k2 hk2 =>
    hUU ⟨hK1U hk1, hK2U hk2⟩
  have hinl : ∀ (g : G) (x : V), (ρ.comp (MonoidHom.inl G H)) g x = ρ (g, 1) x := fun g x => rfl
  let W : Submodule ℂ V := fixed (ρ.comp (MonoidHom.inr G H)) K2
  have hW : ∀ g, ∀ ⦃x⦄, x ∈ W → (ρ.comp (MonoidHom.inl G H)) g x ∈ W := by
    intro g x hx
    have hx' : x ∈ fixed (ρ.comp (MonoidHom.inr G H)) K2 := hx
    show _ ∈ fixed (ρ.comp (MonoidHom.inr G H)) K2
    rw [mem_fixed_iff_forall] at hx' ⊢
    intro k hk
    have e := hx' k hk
    show ρ (1, k) (ρ (g, 1) x) = ρ (g, 1) x
    rw [← inl_inr_comm]
    exact congrArg (ρ (g, 1)) e
  have hvW : v ∈ W := by
    show v ∈ fixed (ρ.comp (MonoidHom.inr G H)) K2
    rw [mem_fixed_iff_forall]
    intro k hk
    exact hfix 1 (one_mem K1) k hk
  have hW0 : W ≠ ⊥ := by
    intro h
    apply hv0
    have hvW' := hvW
    rw [h] at hvW'
    exact (Submodule.mem_bot ℂ).mp hvW'
  have hvK : v ∈ fixed (ρ.comp (MonoidHom.inl G H)) K1 := by
    rw [mem_fixed_iff_forall]
    intro k hk
    exact hfix k hk 1 (one_mem K2)
  have hprodO : IsOpen ((K1.prod K2 : Subgroup (G × H)) : Set (G × H)) := by
    rw [Subgroup.coe_prod]
    exact hK1o.prod hK2o
  have hprodC : IsCompact ((K1.prod K2 : Subgroup (G × H)) : Set (G × H)) := by
    rw [Subgroup.coe_prod]
    exact hK1c.prod hK2c
  haveI hfprod : FiniteDimensional ℂ ↥(fixed ρ (K1.prod K2)) := hadm.2 _ hprodO hprodC
  have hfin : FiniteDimensional ℂ ↥(W ⊓ fixed (ρ.comp (MonoidHom.inl G H)) K1) := by
    refine Submodule.finiteDimensional_of_le (S₂ := fixed ρ (K1.prod K2)) ?_
    rintro x ⟨hxW0, hxK0⟩
    have hxW : x ∈ fixed (ρ.comp (MonoidHom.inr G H)) K2 := hxW0
    have hxK : x ∈ fixed (ρ.comp (MonoidHom.inl G H)) K1 := hxK0
    show x ∈ fixed ρ (K1.prod K2)
    rw [mem_fixed_iff_forall] at hxW hxK ⊢
    rintro ⟨k1, k2⟩ ⟨hk1, hk2⟩
    have e : ((k1, k2) : G × H) = (k1, 1) * (1, k2) := Prod.ext (by simp) (by simp)
    rw [e, map_mul, Module.End.mul_apply]
    have e2 : ρ (1, k2) x = x := hxW k2 hk2
    have e3 : ρ (k1, 1) x = x := hxK k1 hk1
    rw [e2, e3]
  have hs : IsSmooth (ρ.comp (MonoidHom.inl G H)) := by
    intro x
    have hc : Continuous fun g : G => ((g, 1) : G × H) := by fun_prop
    exact (hadm.1 x).preimage hc
  have hnz : ∀ A : Submodule ℂ V, (∀ g, ∀ ⦃x⦄, x ∈ A → (ρ.comp (MonoidHom.inl G H)) g x ∈ A) → A ≠ ⊥ →
      ∃ x ∈ A, x ∈ fixed (ρ.comp (MonoidHom.inl G H)) K1 ∧ x ≠ 0 :=
    fun A hA hA0 => exists_fixed_of_ne_bot ρ hi hs hK1c hv0 hvK A hA hA0
  obtain ⟨S, u, huS, hu0, huK, hSirr, hSfin⟩ := exists_irreducible_of_fixed hW hW0 hfin hnz
  exact ⟨K1, S, u, hK1o, hK1c, huS, hu0, fun x hx => (mem_fixed_iff_forall.mp huK) x hx, hSirr, hSfin⟩
end GlobalTheory.CompanionTheory.ProdSub
