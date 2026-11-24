-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdSub.exists_irreducible_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:55:11.361731+00:00
-- url     : https://prove2.me/submissions/0f20299d-ad3f-4ef9-9a42-0f38d90d0dd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIrreducibleOfFixed
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_mem_fixed_iff_forall
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


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
theorem _root_.solution {π : Representation ℂ G V} {K : Subgroup G} {W : Submodule ℂ V}
    (hW : ∀ g, ∀ ⦃x⦄, x ∈ W → π g x ∈ W) (hW0 : W ≠ ⊥)
    (hfin : FiniteDimensional ℂ ↥(W ⊓ fixed π K))
    (hnz : ∀ A : Submodule ℂ V, (∀ g, ∀ ⦃x⦄, x ∈ A → π g x ∈ A) → A ≠ ⊥ →
      ∃ x ∈ A, x ∈ fixed π K ∧ x ≠ 0) :
    ∃ (S : Subrepresentation π) (u : V), u ∈ S.toSubmodule ∧ u ≠ 0 ∧ u ∈ fixed π K ∧
      S.toRepresentation.IsIrreducible ∧ FiniteDimensional ℂ (fixed S.toRepresentation K) := by
  classical
  haveI := hfin
  have hfinM : ∀ M : Submodule ℂ V, M ≤ W → FiniteDimensional ℂ ↥(M ⊓ fixed π K) :=
    fun M hM => Submodule.finiteDimensional_of_le (inf_le_inf_right (fixed π K) hM)
  have hex : ∃ n, ∃ M : Submodule ℂ V, (∀ g, ∀ ⦃x⦄, x ∈ M → π g x ∈ M) ∧ M ≤ W ∧ M ≠ ⊥ ∧
      Module.finrank ℂ ↥(M ⊓ fixed π K) = n := ⟨_, W, hW, le_rfl, hW0, rfl⟩
  obtain ⟨M0, hM0inv, hM0W, hM0ne, hM0d⟩ := Nat.find_spec hex
  have hmin : ∀ M : Submodule ℂ V, (∀ g, ∀ ⦃x⦄, x ∈ M → π g x ∈ M) → M ≤ W → M ≠ ⊥ →
      Module.finrank ℂ ↥(M0 ⊓ fixed π K) ≤ Module.finrank ℂ ↥(M ⊓ fixed π K) := by
    intro M hMinv hMW hMne
    rw [hM0d]
    exact Nat.find_min' hex ⟨M, hMinv, hMW, hMne, rfl⟩
  haveI := hfinM M0 hM0W
  let S1 : Submodule ℂ V := Submodule.span ℂ {x | ∃ g, ∃ y ∈ M0 ⊓ fixed π K, x = π g y}
  have hS1inv : ∀ g, ∀ ⦃x⦄, x ∈ S1 → π g x ∈ S1 := by
    intro g x hx
    have hle : S1 ≤ S1.comap (π g) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨g', y, hy, rfl⟩
      show π g (π g' y) ∈ S1
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g * g', y, hy, rfl⟩
    exact hle hx
  have hS1M0 : S1 ≤ M0 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, y, hy, rfl⟩
    exact hM0inv g hy.1
  have hF0S1 : M0 ⊓ fixed π K ≤ S1 := fun y hy =>
    Submodule.subset_span ⟨1, y, hy, by rw [map_one, Module.End.one_apply]⟩
  have hkey : ∀ T : Submodule ℂ V, (∀ g, ∀ ⦃x⦄, x ∈ T → π g x ∈ T) → T ≤ S1 → T ≠ ⊥ → S1 ≤ T := by
    intro T hTinv hTS1 hTne
    have hTM0 : T ≤ M0 := hTS1.trans hS1M0
    have hle : T ⊓ fixed π K ≤ M0 ⊓ fixed π K := inf_le_inf_right (fixed π K) hTM0
    have heq : T ⊓ fixed π K = M0 ⊓ fixed π K :=
      Submodule.eq_of_le_of_finrank_le hle (hmin T hTinv (hTM0.trans hM0W) hTne)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, y, hy, rfl⟩
    have hy' : y ∈ T ⊓ fixed π K := by rw [heq]; exact hy
    exact hTinv g hy'.1
  obtain ⟨u, huM0, huF, hu0⟩ := hnz M0 hM0inv hM0ne
  have huS1 : u ∈ S1 := hF0S1 ⟨huM0, huF⟩
  let S : Subrepresentation π := ⟨S1, hS1inv⟩
  refine ⟨S, u, huS1, hu0, huF, ?_, ?_⟩
  · show IsSimpleOrder (Subrepresentation S.toRepresentation)
    refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
    · intro h
      have hmem : (⟨u, huS1⟩ : ↥S1) ∈ (⊤ : Subrepresentation S.toRepresentation).toSubmodule :=
        Submodule.mem_top
      rw [← h] at hmem
      have h0 : (⟨u, huS1⟩ : ↥S1) = 0 := (Submodule.mem_bot ℂ).mp hmem
      exact hu0 (congrArg Subtype.val h0)
    · intro X
      by_cases hX : X.toSubmodule = ⊥
      · left
        exact Subrepresentation.ext hX
      · right
        apply Subrepresentation.ext
        show X.toSubmodule = ⊤
        let T : Submodule ℂ V := X.toSubmodule.map S1.subtype
        have hTinv : ∀ g, ∀ ⦃x⦄, x ∈ T → π g x ∈ T := by
          rintro g _ ⟨y, hy, rfl⟩
          exact ⟨S.toRepresentation g y, X.apply_mem_toSubmodule g hy, rfl⟩
        have hTS1 : T ≤ S1 := Submodule.map_subtype_le S1 _
        have hTne : T ≠ ⊥ := by
          intro hT
          apply hX
          rw [eq_bot_iff]
          intro y hy
          have hyT : (y : V) ∈ T := ⟨y, hy, rfl⟩
          rw [hT] at hyT
          exact (Submodule.mem_bot ℂ).mpr (Subtype.ext ((Submodule.mem_bot ℂ).mp hyT))
        have hST := hkey T hTinv hTS1 hTne
        rw [eq_top_iff]
        intro y _
        obtain ⟨y', hy', hyy'⟩ := hST y.2
        have hyy : y' = y := Subtype.ext hyy'
        rw [← hyy]
        exact hy'
  · have hle : (fixed S.toRepresentation K).map S1.subtype ≤ W ⊓ fixed π K := by
      rintro _ ⟨y, hy0, rfl⟩
      have hy : y ∈ fixed S.toRepresentation K := hy0
      refine ⟨hM0W (hS1M0 y.2), ?_⟩
      show (y : V) ∈ fixed π K
      rw [mem_fixed_iff_forall] at hy ⊢
      intro k hk
      exact congrArg Subtype.val (hy k hk)
    haveI : FiniteDimensional ℂ ↥((fixed S.toRepresentation K).map S1.subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective S1.subtype Subtype.val_injective _).symm
end GlobalTheory.CompanionTheory.ProdSub
