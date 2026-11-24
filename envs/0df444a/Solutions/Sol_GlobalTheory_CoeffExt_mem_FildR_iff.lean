-- Prove2me | solution 1 for GlobalTheory.CoeffExt.mem_FildR_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:33.9883+00:00
-- url     : https://prove2.me/submissions/3c149bbe-992d-485e-a1dc-cf179ab854e0

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
import Theorems.Thm_GlobalTheory_CoeffExt_tensCoord_map
import Theorems.Thm_GlobalTheory_CoeffExt_tensCoord_actVdR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)}
namespace GlobalTheory.CoeffExt
theorem _root_.solution (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (τ : K →ₐ[Qp] LL)
    (τ' : K →ₐ[Qp] LL') (hτ : ∀ c, τ' c = algebraMap LL LL' (τ c)) (a : ℤ) (x : V' ⊗[Qp] BdR) :
    x ∈ FildR PD ρ' τ' a ↔ ∀ i, tensCoord E BdR x i ∈ FildR PD ρ τ a := by

  have hA : ∀ y : V' ⊗[Qp] BdR, y ∈ DdR PD ρ' ↔ ∀ i, tensCoord E BdR y i ∈ DdR PD ρ := by
    intro y
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    constructor
    · intro hy i g
      rw [← tensCoord_actVdR PD hE g y i, hy g]
    · intro hy g
      apply (tensCoord E BdR).injective
      funext i
      rw [tensCoord_actVdR PD hE]
      exact hy i g

  have hmul : ∀ (c : K) (y : V' ⊗[Qp] BdR) i,
      tensCoord E BdR (mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL') c y) i =
        mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (tensCoord E BdR y i) :=
    fun c y i => tensCoord_map E LinearMap.id LinearMap.id (fun _ _ => rfl) _ y i
  have hsm : ∀ (c : K) (y : V' ⊗[Qp] BdR) i,
      tensCoord E BdR (τ' c • y) i = τ c • tensCoord E BdR y i := by
    intro c y i
    rw [hτ, algebraMap_smul, map_smul, Pi.smul_apply]
  have hB : ∀ y : V' ⊗[Qp] BdR, (∀ c : K, mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL') c y =
      τ' c • y) ↔ ∀ i, ∀ c : K, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c
        (tensCoord E BdR y i) = τ c • tensCoord E BdR y i := by
    intro y
    constructor
    · intro hy i c
      rw [← hmul, ← hsm, hy c]
    · intro hy c
      apply (tensCoord E BdR).injective
      funext i
      rw [hmul, hsm]
      exact hy i c

  have hC : ∀ y : V' ⊗[Qp] BdR, y ∈ FilV PD (LL := LL') (V := V') a ↔
      ∀ i, tensCoord E BdR y i ∈ FilV PD (LL := LL) (V := V) a := by
    intro y
    have hmap : ∀ (z : V' ⊗[Qp] ↥((PD.Fil a).restrictScalars Qp)) i,
        tensCoord E BdR (AlgebraTensorModule.map (LinearMap.id : V' →ₗ[LL'] V')
          ((PD.Fil a).restrictScalars Qp).subtype z) i =
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype
          (tensCoord E _ z i) :=
      fun z i => tensCoord_map E LinearMap.id LinearMap.id (fun _ _ => rfl) _ z i
    simp only [FilV, LinearMap.mem_range]
    constructor
    · rintro ⟨z, rfl⟩ i
      exact ⟨tensCoord E _ z i, (hmap z i).symm⟩
    · intro hy
      choose z hz using hy
      refine ⟨(tensCoord E _).symm z, ?_⟩
      apply (tensCoord E BdR).injective
      funext i
      rw [hmap, LinearEquiv.apply_symm_apply, hz i]
  simp only [FildR, DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  rw [hA, hB, hC]
  simp only [forall_and]
end GlobalTheory.CoeffExt
