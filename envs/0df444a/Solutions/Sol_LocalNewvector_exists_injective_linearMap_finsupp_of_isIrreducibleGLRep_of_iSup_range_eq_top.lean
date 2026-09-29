-- Prove2me | solution 1 for LocalNewvector.exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/bf766379-7460-58e6-af1b-51c456178a25

import Definitions.Def_LocalNewvector_ConductorDatum
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Isotypic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top

set_option autoImplicit false

private theorem representation_isIrreducible_of_isIrreducibleGLRep (q : ℕ) [Fact q.Prime]
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V] (hV : LocalNewvector.IsIrreducibleGLRep q V) :
    (Representation.ofDistribMulAction ℂ (GL (Fin 2) ℚ_[q]) V).IsIrreducible := by
  obtain ⟨⟨v, hv⟩, hstable⟩ := hV
  haveI : Nontrivial V := nontrivial_of_ne v 0 hv
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun p => ?_ }
  · exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) (congrArg Subrepresentation.toSubmodule h)
  · rcases hstable p.toSubmodule (fun g w hw => p.apply_mem_toSubmodule g hw) with h | h
    · left
      apply Subrepresentation.toSubmodule_injective
      exact h
    · right
      apply Subrepresentation.toSubmodule_injective
      exact h

section core

variable {G : Type} [Group G]
variable (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V]
variable (W : Type) [AddCommGroup W] [Module ℂ W] [DistribMulAction G W] [SMulCommClass G ℂ W]

local notation "ρV" => Representation.ofDistribMulAction ℂ G V
local notation "ρW" => Representation.ofDistribMulAction ℂ G W

set_option backward.isDefEq.respectTransparency false in

private theorem exists_injective_equivariant_finsupp_of_isIrreducible (hirr : (ρV).IsIrreducible)
    (κ : Type) (f : κ → (V →ₗ[ℂ] W)) (hf : ∀ (i : κ) (x : G) (v : V), f i (x • v) = x • f i v)
    (hW : ⨆ i : κ, LinearMap.range (f i) = ⊤) :
    ∃ (ι : Type) (L : W →ₗ[ℂ] (ι →₀ V)),
      Function.Injective L ∧ ∀ (x : G) (w : W), L (x • w) = x • L w := by
  classical
  haveI : IsSimpleModule (MonoidAlgebra ℂ G) (ρV).asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule (ρV)).mp hirr
  let Φ : κ → (ρV).IntertwiningMap (ρW) := fun i =>
    (f i).intertwiningMap_of_isIntertwiningMap (ρV) (ρW) (fun g v => hf i g v)
  let F : κ → ((ρV).asModule →ₗ[MonoidAlgebra ℂ G] (ρW).asModule) := fun i =>
    Representation.IntertwiningMap.equivLinearMapAsModule (ρV) (ρW) (Φ i)
  have hF : ∀ i, Function.Injective (F i) ∨ F i = 0 := fun i => by
    rcases Representation.IsIrreducible.injective_or_eq_zero (Φ i) with h | h
    · exact Or.inl h
    · right
      simp only [F, h, map_zero]
  let S : Set (Submodule (MonoidAlgebra ℂ G) (ρW).asModule) :=
    Set.range fun i : {i : κ // Function.Injective (F i)} => LinearMap.range (F i.1)
  have hS_simple : ∀ t ∈ S, IsSimpleModule (MonoidAlgebra ℂ G) t := by
    rintro t ⟨⟨i, hi⟩, rfl⟩
    exact IsSimpleModule.congr (LinearEquiv.ofInjective (F i) hi).symm
  have hS_top : sSup S = ⊤ := by
    refine eq_top_iff.mpr fun w' _ => ?_
    have hw : (ρW).asModuleEquiv w' ∈ (⊤ : Submodule ℂ W) := Submodule.mem_top
    rw [← hW] at hw
    have key : ∀ w : W, w ∈ ⨆ i, LinearMap.range (f i) → (ρW).asModuleEquiv.symm w ∈ sSup S := by
      intro w hw
      refine Submodule.iSup_induction (motive := fun w => (ρW).asModuleEquiv.symm w ∈ sSup S) _ hw ?_ ?_ ?_
      · rintro i _ ⟨v, rfl⟩
        rcases hF i with hi | hi
        · have hmem : (ρW).asModuleEquiv.symm (f i v) ∈ LinearMap.range (F i) :=
            ⟨(ρV).asModuleEquiv.symm v, rfl⟩
          exact (le_sSup ⟨⟨i, hi⟩, rfl⟩ : LinearMap.range (F i) ≤ sSup S) hmem
        · have hzero : f i v = 0 := by
            have h0 := LinearMap.congr_fun hi ((ρV).asModuleEquiv.symm v)
            exact h0
          rw [hzero, map_zero]
          exact Submodule.zero_mem _
      · show (ρW).asModuleEquiv.symm 0 ∈ sSup S
        rw [map_zero]
        exact Submodule.zero_mem _
      · intro a b ha hb
        show (ρW).asModuleEquiv.symm (a + b) ∈ sSup S
        rw [map_add]
        exact Submodule.add_mem _ ha hb
    have := key _ hw
    rwa [LinearEquiv.symm_apply_apply] at this
  haveI hS_inst : ∀ t : S, IsSimpleModule (MonoidAlgebra ℂ G) t := fun t => hS_simple t.1 t.2
  have hiso : IsIsotypicOfType (MonoidAlgebra ℂ G) (ρW).asModule (ρV).asModule := by
    intro m hm
    obtain ⟨t, ht, ⟨e⟩⟩ := Submodule.linearEquiv_of_le_sSup m S (hS_top ▸ le_top)
    obtain ⟨⟨i, hi⟩, rfl⟩ := ht
    exact ⟨e.trans (LinearEquiv.ofInjective (F i) hi).symm⟩
  haveI hss : IsSemisimpleModule (MonoidAlgebra ℂ G) (ρW).asModule := by
    refine IsSemisimpleModule.of_sSup_simples_eq_top (top_le_iff.mp ?_)
    rw [← hS_top]
    exact sSup_le_sSup fun t ht => hS_simple t ht
  obtain ⟨ι, ⟨e⟩⟩ := hiso.linearEquiv_finsupp
  refine ⟨ι, Finsupp.mapRange.linearMap (ρV).asModuleEquiv.toLinearMap ∘ₗ
    (e.restrictScalars ℂ).toLinearMap ∘ₗ (ρW).asModuleEquiv.symm.toLinearMap, ?_, ?_⟩
  · intro a b hab
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.mapRange.linearMap_apply] at hab
    have h1 := Finsupp.mapRange_injective _ _ (ρV).asModuleEquiv.injective hab
    have h2 := (e.restrictScalars ℂ).injective h1
    exact (ρW).asModuleEquiv.symm.injective h2
  · intro x w
    have h1 : (ρW).asModuleEquiv.symm (x • w) = MonoidAlgebra.of ℂ G x • (ρW).asModuleEquiv.symm w :=
      Representation.asModuleEquiv_symm_map_rho (ρW) x w
    have h2 : (e.restrictScalars ℂ) ((ρW).asModuleEquiv.symm (x • w)) =
        MonoidAlgebra.of ℂ G x • (e.restrictScalars ℂ) ((ρW).asModuleEquiv.symm w) := by
      rw [h1]
      exact map_smul e _ _
    ext i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_apply, Finsupp.smul_apply, h2, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
    rfl

end core

theorem solution
    (q : ℕ) [Fact q.Prime]
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    (W : Type) [AddCommGroup W] [Module ℂ W] [DistribMulAction (GL (Fin 2) ℚ_[q]) W]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W]
    (hV : LocalNewvector.IsIrreducibleGLRep q V)
    (κ : Type) (f : κ → (V →ₗ[ℂ] W))
    (hf : ∀ (i : κ) (x : GL (Fin 2) ℚ_[q]) (v : V), f i (x • v) = x • f i v)
    (hW : ⨆ i : κ, LinearMap.range (f i) = ⊤) :
    ∃ (ι : Type) (L : W →ₗ[ℂ] (ι →₀ V)),
      Function.Injective L ∧ ∀ (x : GL (Fin 2) ℚ_[q]) (w : W), L (x • w) = x • L w := by
  exact exists_injective_equivariant_finsupp_of_isIrreducible V W
    (representation_isIrreducible_of_isIrreducibleGLRep q V hV) κ f hf hW

end S_LocalNewvector_exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top
end P2MW
export P2MW.S_LocalNewvector_exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top (solution)
