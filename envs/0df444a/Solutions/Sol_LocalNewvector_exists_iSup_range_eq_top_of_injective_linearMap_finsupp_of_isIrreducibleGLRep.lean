-- Prove2me | solution 1 for LocalNewvector.exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e01500df-2ceb-5e93-85ce-dbabd06799ee

import Definitions.Def_LocalNewvector_ConductorDatum
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Isotypic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep

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
variable (M : Type) [AddCommGroup M] [Module ℂ M] [DistribMulAction G M] [SMulCommClass G ℂ M]

local notation "ρV" => Representation.ofDistribMulAction ℂ G V
local notation "ρM" => Representation.ofDistribMulAction ℂ G M

set_option backward.isDefEq.respectTransparency false in

private theorem isSemisimple_and_isIsotypic_of_spanned (hirr : (ρV).IsIrreducible)
    (κ : Type) (f : κ → (V →ₗ[ℂ] M)) (hf : ∀ (i : κ) (x : G) (v : V), f i (x • v) = x • f i v)
    (hM : ⨆ i : κ, LinearMap.range (f i) = ⊤) :
    IsSemisimpleModule (MonoidAlgebra ℂ G) (ρM).asModule ∧
      IsIsotypicOfType (MonoidAlgebra ℂ G) (ρM).asModule (ρV).asModule := by
  classical
  haveI : IsSimpleModule (MonoidAlgebra ℂ G) (ρV).asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule (ρV)).mp hirr
  let Φ : κ → (ρV).IntertwiningMap (ρM) := fun i =>
    (f i).intertwiningMap_of_isIntertwiningMap (ρV) (ρM) (fun g v => hf i g v)
  let F : κ → ((ρV).asModule →ₗ[MonoidAlgebra ℂ G] (ρM).asModule) := fun i =>
    Representation.IntertwiningMap.equivLinearMapAsModule (ρV) (ρM) (Φ i)
  have hF : ∀ i, Function.Injective (F i) ∨ F i = 0 := fun i => by
    rcases Representation.IsIrreducible.injective_or_eq_zero (Φ i) with h | h
    · exact Or.inl h
    · right
      simp only [F, h, map_zero]
  let S : Set (Submodule (MonoidAlgebra ℂ G) (ρM).asModule) :=
    Set.range fun i : {i : κ // Function.Injective (F i)} => LinearMap.range (F i.1)
  have hS_simple : ∀ t ∈ S, IsSimpleModule (MonoidAlgebra ℂ G) t := by
    rintro t ⟨⟨i, hi⟩, rfl⟩
    exact IsSimpleModule.congr (LinearEquiv.ofInjective (F i) hi).symm
  have hS_top : sSup S = ⊤ := by
    refine eq_top_iff.mpr fun m' _ => ?_
    have hm : (ρM).asModuleEquiv m' ∈ (⊤ : Submodule ℂ M) := Submodule.mem_top
    rw [← hM] at hm
    have key : ∀ m : M, m ∈ ⨆ i, LinearMap.range (f i) → (ρM).asModuleEquiv.symm m ∈ sSup S := by
      intro m hm
      refine Submodule.iSup_induction (motive := fun m => (ρM).asModuleEquiv.symm m ∈ sSup S) _ hm ?_ ?_ ?_
      · rintro i _ ⟨v, rfl⟩
        rcases hF i with hi | hi
        · have hmem : (ρM).asModuleEquiv.symm (f i v) ∈ LinearMap.range (F i) :=
            ⟨(ρV).asModuleEquiv.symm v, rfl⟩
          exact (le_sSup ⟨⟨i, hi⟩, rfl⟩ : LinearMap.range (F i) ≤ sSup S) hmem
        · have hzero : f i v = 0 := by
            have h0 := LinearMap.congr_fun hi ((ρV).asModuleEquiv.symm v)
            exact h0
          rw [hzero, map_zero]
          exact Submodule.zero_mem _
      · show (ρM).asModuleEquiv.symm 0 ∈ sSup S
        rw [map_zero]
        exact Submodule.zero_mem _
      · intro a b ha hb
        show (ρM).asModuleEquiv.symm (a + b) ∈ sSup S
        rw [map_add]
        exact Submodule.add_mem _ ha hb
    have := key _ hm
    rwa [LinearEquiv.symm_apply_apply] at this
  haveI hS_inst : ∀ t : S, IsSimpleModule (MonoidAlgebra ℂ G) t := fun t => hS_simple t.1 t.2
  refine ⟨?_, ?_⟩
  · refine IsSemisimpleModule.of_sSup_simples_eq_top (top_le_iff.mp ?_)
    rw [← hS_top]
    exact sSup_le_sSup fun t ht => hS_simple t ht
  · intro m hm
    obtain ⟨t, ht, ⟨e⟩⟩ := Submodule.linearEquiv_of_le_sSup m S (hS_top ▸ le_top)
    obtain ⟨⟨i, hi⟩, rfl⟩ := ht
    exact ⟨e.trans (LinearEquiv.ofInjective (F i) hi).symm⟩

end core

section converse

variable {G : Type} [Group G]
variable (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V]
variable (N : Type) [AddCommGroup N] [Module ℂ N] [DistribMulAction G N] [SMulCommClass G ℂ N]

local notation "ρV" => Representation.ofDistribMulAction ℂ G V
local notation "ρN" => Representation.ofDistribMulAction ℂ G N

set_option backward.isDefEq.respectTransparency false in

private theorem exists_spanning_of_injective_finsupp (hirr : (ρV).IsIrreducible)
    (ι : Type) (L : N →ₗ[ℂ] (ι →₀ V)) (hL : Function.Injective L)
    (hLx : ∀ (x : G) (n : N), L (x • n) = x • L n) :
    ∃ (κ : Type) (f : κ → (V →ₗ[ℂ] N)),
      (∀ (i : κ) (x : G) (v : V), f i (x • v) = x • f i v) ∧
        ⨆ i : κ, LinearMap.range (f i) = ⊤ := by
  classical
  obtain ⟨hssT, hisoT⟩ := isSemisimple_and_isIsotypic_of_spanned V (ι →₀ V) hirr ι
    (fun i => Finsupp.lsingle i) (fun i x v => (Finsupp.smul_single x i v).symm)
    Finsupp.iSup_lsingle_range
  let Φ : (ρN).IntertwiningMap (Representation.ofDistribMulAction ℂ G (ι →₀ V)) :=
    L.intertwiningMap_of_isIntertwiningMap (ρN) (Representation.ofDistribMulAction ℂ G (ι →₀ V))
      (fun g n => hLx g n)
  let F : (ρN).asModule →ₗ[MonoidAlgebra ℂ G]
      (Representation.ofDistribMulAction ℂ G (ι →₀ V)).asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule (ρN)
      (Representation.ofDistribMulAction ℂ G (ι →₀ V)) Φ
  have hF : Function.Injective F := fun a b hab => hL hab
  haveI hssN : IsSemisimpleModule (MonoidAlgebra ℂ G) (ρN).asModule :=
    IsSemisimpleModule.of_injective F hF
  have hisoN : IsIsotypicOfType (MonoidAlgebra ℂ G) (ρN).asModule (ρV).asModule :=
    hisoT.of_injective F hF
  obtain ⟨κ, ⟨e⟩⟩ := hisoN.linearEquiv_finsupp
  let g : κ → (V →ₗ[ℂ] N) := fun j =>
    (ρN).asModuleEquiv.toLinearMap ∘ₗ (e.symm.restrictScalars ℂ).toLinearMap ∘ₗ
      (Finsupp.lsingle j : (ρV).asModule →ₗ[MonoidAlgebra ℂ G] (κ →₀ (ρV).asModule)).restrictScalars ℂ ∘ₗ
        (ρV).asModuleEquiv.symm.toLinearMap
  refine ⟨κ, g, ?_, ?_⟩
  · intro j x v
    have h1 : (ρV).asModuleEquiv.symm (x • v) = MonoidAlgebra.of ℂ G x • (ρV).asModuleEquiv.symm v :=
      Representation.asModuleEquiv_symm_map_rho (ρV) x v
    show (ρN).asModuleEquiv (e.symm
        ((Finsupp.lsingle j : (ρV).asModule →ₗ[MonoidAlgebra ℂ G] (κ →₀ (ρV).asModule))
          ((ρV).asModuleEquiv.symm (x • v)))) =
      x • (ρN).asModuleEquiv (e.symm
        ((Finsupp.lsingle j : (ρV).asModule →ₗ[MonoidAlgebra ℂ G] (κ →₀ (ρV).asModule))
          ((ρV).asModuleEquiv.symm v)))
    rw [h1, LinearMap.map_smul, LinearEquiv.map_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
    rfl
  · refine eq_top_iff.mpr fun n _ => ?_
    have hn : n = (ρN).asModuleEquiv (e.symm (e ((ρN).asModuleEquiv.symm n))) := by
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
    rw [hn]
    generalize e ((ρN).asModuleEquiv.symm n) = t
    refine Finsupp.induction_linear t ?_ ?_ ?_
    · rw [map_zero, map_zero]
      exact Submodule.zero_mem _
    · intro a b ha hb
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb
    · intro j w
      refine Submodule.mem_iSup_of_mem j ⟨(ρV).asModuleEquiv w, ?_⟩
      show (ρN).asModuleEquiv (e.symm (Finsupp.lsingle j ((ρV).asModuleEquiv.symm ((ρV).asModuleEquiv w)))) =
        (ρN).asModuleEquiv (e.symm (Finsupp.single j w))
      rw [LinearEquiv.symm_apply_apply]
      rfl

end converse

theorem solution
    (q : ℕ) [Fact q.Prime]
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    (N : Type) [AddCommGroup N] [Module ℂ N] [DistribMulAction (GL (Fin 2) ℚ_[q]) N]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ N]
    (hV : LocalNewvector.IsIrreducibleGLRep q V)
    (ι : Type) (L : N →ₗ[ℂ] (ι →₀ V)) (hL : Function.Injective L)
    (hLx : ∀ (x : GL (Fin 2) ℚ_[q]) (n : N), L (x • n) = x • L n) :
    ∃ (κ : Type) (f : κ → (V →ₗ[ℂ] N)),
      (∀ (i : κ) (x : GL (Fin 2) ℚ_[q]) (v : V), f i (x • v) = x • f i v) ∧
        ⨆ i : κ, LinearMap.range (f i) = ⊤ := by
  exact exists_spanning_of_injective_finsupp V N
    (representation_isIrreducible_of_isIrreducibleGLRep q V hV) ι L hL hLx

#print axioms solution

end S_LocalNewvector_exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep
end P2MW
export P2MW.S_LocalNewvector_exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep (solution)
