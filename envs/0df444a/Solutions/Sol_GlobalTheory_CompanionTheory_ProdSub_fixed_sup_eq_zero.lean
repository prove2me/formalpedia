-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdSub.fixed_sup_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:55:12.498232+00:00
-- url     : https://prove2.me/submissions/87e6e237-e7ec-4a8a-ae5b-235d7c9ef5f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIrreducibleOfFixed
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_mem_fixed_iff_forall
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_fixed_map_eq


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
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.ProdSub
theorem _root_.solution [TopologicalSpace G] [IsTopologicalGroup G] {π : Representation ℂ G V}
    (hπ : IsSmooth π) {K : Subgroup G} (hK : IsCompact (K : Set G)) {A B : Submodule ℂ V}
    (hA : ∀ g, ∀ ⦃x⦄, x ∈ A → π g x ∈ A) (hB : ∀ g, ∀ ⦃x⦄, x ∈ B → π g x ∈ B)
    (hA0 : ∀ x ∈ A, x ∈ fixed π K → x = 0) (hB0 : ∀ x ∈ B, x ∈ fixed π K → x = 0)
    {x : V} (hx : x ∈ A ⊔ B) (hf : x ∈ fixed π K) : x = 0 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  let S : Subrepresentation π := ⟨B, hB⟩
  have hS : IsSmooth S.toRepresentation := by
    intro w
    have e : {g | S.toRepresentation g w = w} = {g | π g w = w} := by
      ext g
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [e]
    exact hπ w
  have hinv : ∀ h ∈ K, ((A.mkQ).comp B.subtype) (S.toRepresentation h ⟨b, hb⟩) =
      ((A.mkQ).comp B.subtype) ⟨b, hb⟩ := by
    intro h hh
    have hx' := (mem_fixed_iff_forall.mp hf) h hh
    rw [map_add] at hx'
    have e : (S.toRepresentation h ⟨b, hb⟩ : V) = π h b := rfl
    have e2 : π h b - b = a - π h a := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm, hx']
    show A.mkQ ((S.toRepresentation h ⟨b, hb⟩ : V)) = A.mkQ b
    rw [e, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, e2]
    exact A.sub_mem ha (hA h ha)
  obtain ⟨v, hvK, hv⟩ := GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq hS hK ((A.mkQ).comp B.subtype) ⟨b, hb⟩ hinv
  have hvK' : (v : V) ∈ fixed π K := by
    rw [mem_fixed_iff_forall] at hvK ⊢
    intro k hk
    exact congrArg Subtype.val (hvK k hk)
  have hv0 : (v : V) = 0 := hB0 v v.2 hvK'
  have hbA : b ∈ A := by
    have h1 : A.mkQ (v : V) = A.mkQ b := hv
    rw [hv0, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, zero_sub] at h1
    simpa using A.neg_mem h1
  exact hA0 _ (A.add_mem ha hbA) hf
end GlobalTheory.CompanionTheory.ProdSub
