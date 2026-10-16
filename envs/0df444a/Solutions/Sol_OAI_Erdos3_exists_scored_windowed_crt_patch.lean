-- Prove2me | solution 1 for OAI.Erdos3.exists_scored_windowed_crt_patch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T01:27:12.049064+00:00
-- url     : https://prove2.me/submissions/c0e51870-fa68-4fcb-a27b-aeabf95ec4a4

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1330
import Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_scored_native_chart

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace TriangularSlots

variable {d : ℕ}

end TriangularSlots

namespace TriangularSlots

variable {d : ℕ} (A : TriangularSlots d) (Φ : PatchKernel d)

end TriangularSlots

end Erdos3

end

section

namespace Erdos3.TriangularSlots

variable {d : ℕ}

end Erdos3.TriangularSlots

end

section

namespace Erdos3

variable {D E : ℕ}

namespace TriangularSlots

end TriangularSlots

namespace PatchKernel

end PatchKernel

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

namespace SlotInterleaving

variable {D E : ℕ}

end SlotInterleaving

end Erdos3

end

section

namespace Erdos3

namespace TriangularSlots

variable {D E : ℕ}

end TriangularSlots

end Erdos3

end

section

namespace Erdos3.TriangularSlots

variable {D E d : ℕ}

end Erdos3.TriangularSlots

end

section

namespace Erdos3

variable {D E : ℕ}

namespace TriangularSlots

end TriangularSlots

namespace PatchKernel

end PatchKernel

namespace TriangularSlots

end TriangularSlots

end Erdos3

end

section

namespace Erdos3.TriangularSlots

variable {D E : ℕ}

theorem factorized_patchValue_at_lift
    (A : TriangularSlots D) (B : (Fin D → ℤ) → TriangularSlots E)
    (T : TriangularSlots (D + E)) (Φ : PatchKernel D) (Ψ : PatchKernel E)
    (K : PatchKernel (D + E)) (I : SlotInterleaving D E)
    (hterm : ∀ z, K.value (T.residual z) =
      Φ.value (A.residual (fun j => z (I.left j))) *
      Ψ.value ((B (fun j => z (I.left j))).residual (fun j => z (I.right j))))
    (b : Fin D → ℤ) (hb : ∀ i, |A.residual b i| ≤ 1 / 3) :
    T.patchValue K = Φ.value (A.residual b) * (B b).patchValue Ψ := by
  have hleft (z : Fin (D + E) → ℤ)
      (hz : Φ.value (A.residual (fun j => z (I.left j))) ≠ 0) :
      (fun j => z (I.left j)) = b :=
    A.integer_unique (by norm_num) (Φ.support _ hz) hb
  by_cases hφ : Φ.value (A.residual b) = 0
  · rw [hφ, zero_mul]
    apply T.patchValue_eq_zero K
    intro z
    rw [hterm]
    by_cases hz : Φ.value (A.residual (fun j => z (I.left j))) = 0
    · rw [hz, zero_mul]
    · rw [hleft z hz, hφ, zero_mul]
  · by_cases hc : ∃ c, Ψ.value ((B b).residual c) ≠ 0
    · obtain ⟨c, hc⟩ := hc
      have hz : K.value (T.residual (I.fill b c)) ≠ 0 := by
        simpa only [hterm, SlotInterleaving.fill_left, SlotInterleaving.fill_right] using
          mul_ne_zero hφ hc
      rw [T.patchValue_eq_of_nonzero K hz, (B b).patchValue_eq_of_nonzero Ψ hc, hterm]
      simp only [SlotInterleaving.fill_left, SlotInterleaving.fill_right]
    · have hc : ∀ c, Ψ.value ((B b).residual c) = 0 := by simpa using hc
      rw [(B b).patchValue_eq_zero Ψ hc, mul_zero]
      apply T.patchValue_eq_zero K
      intro z
      rw [hterm]
      by_cases hz : Φ.value (A.residual (fun j => z (I.left j))) = 0
      · rw [hz, zero_mul]
      · rw [hleft z hz, hc, mul_zero]

theorem factorized_patchValue
    (A : TriangularSlots D) (B : (Fin D → ℤ) → TriangularSlots E)
    (T : TriangularSlots (D + E)) (Φ : PatchKernel D) (Ψ : PatchKernel E)
    (K : PatchKernel (D + E)) (I : SlotInterleaving D E)
    (hterm : ∀ z, K.value (T.residual z) =
      Φ.value (A.residual (fun j => z (I.left j))) *
      Ψ.value ((B (fun j => z (I.left j))).residual (fun j => z (I.right j)))) :
    T.patchValue K = ∑' b, Φ.value (A.residual b) * (B b).patchValue Ψ := by
  classical
  by_cases h : ∃ b, Φ.value (A.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := h
    rw [A.factorized_patchValue_at_lift B T Φ Ψ K I hterm b
      (fun i => (Φ.support _ hb i).trans (by norm_num))]
    symm
    apply tsum_eq_single b
    intro c hcb
    have hc : Φ.value (A.residual c) = 0 := by
      by_contra hc
      exact hcb (A.contributing_unique Φ hc hb)
    rw [hc, zero_mul]
  · have hzero : ∀ b, Φ.value (A.residual b) = 0 := by simpa using h
    rw [T.patchValue_eq_zero K (fun z => by rw [hterm, hzero, zero_mul])]
    simp only [hzero, zero_mul, tsum_zero]

end Erdos3.TriangularSlots

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d D E : ℕ} {w : Fin d → ℕ}

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem ofCoordinates_center (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (t : σ → ℝ) (x : Fin d → ℝ) (i : Fin d) :
    ((ofCoordinates P hP).slots t).center x i = aeval t (P i) := by
  simp only [slots, ofCoordinates, MvPolynomial.comp_aeval_apply, aeval_X, Sum.elim_inl]

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

end PolynomialPatch

namespace PolynomialPatch

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

end PolynomialSlots

namespace PolynomialPatch

variable {σ τ : Type*} {s d : ℕ}

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open _root_.MvPolynomial

variable {X : Type*} {s d : ℕ}

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d n D E : ℕ}

end PolynomialSlots

end Erdos3

end

section

namespace Erdos3

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3
namespace PolynomialPatch

open _root_.MvPolynomial

variable {σ τ : Type*} {s : ℕ}

end PolynomialPatch
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*}

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem finite_card_rational_grid_box {ι : Type*} [Fintype ι]
    (S : Set (ι → ℚ)) (l N : ℕ) (hl : 0 < l) {B : ℝ}
    (hgrid : S ⊆ denominatorGrid l)
    (hbound : ∀ x ∈ S, ∀ i, |(x i : ℝ)| ≤ B)
    (hN : (l : ℝ) * B ≤ N) :
    S.Finite ∧ S.ncard ≤ (2 * N + 1) ^ Fintype.card ι := by
  classical
  let z : S → ι → ℤ := fun x => Classical.choose (hgrid x.property)
  have hz (x : S) (i : ι) : (l : ℚ) * x.val i = (z x i : ℚ) :=
    Classical.choose_spec (hgrid x.property) i
  have hzi (x : S) (i : ι) : z x i ∈ Set.Icc (-(N : ℤ)) N := by
    have heq : (l : ℝ) * (x.val i : ℝ) = (z x i : ℝ) := by exact_mod_cast hz x i
    have hb : |(z x i : ℝ)| ≤ (N : ℝ) := by
      rw [← heq, abs_mul, abs_of_nonneg (Nat.cast_nonneg l)]
      exact (mul_le_mul_of_nonneg_left (hbound x x.property i) (Nat.cast_nonneg l)).trans hN
    apply abs_le.mp
    exact_mod_cast hb
  let f : S → (ι → Set.Icc (-(N : ℤ)) N) := fun x i => ⟨z x i, hzi x i⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hi : z x i = z y i := congrArg Subtype.val (congrFun hxy i)
    apply mul_left_cancel₀ (show (l : ℚ) ≠ 0 by exact_mod_cast hl.ne')
    rw [hz, hz, hi]
  let : Finite S := Finite.of_injective f hf
  have hcardI : Fintype.card (Set.Icc (-(N : ℤ)) N) = 2 * N + 1 := by
    have h := Int.card_fintype_Icc_of_le (-(N : ℤ)) N (show -(N : ℤ) ≤ N + 1 by omega)
    omega
  refine ⟨Set.toFinite S, ?_⟩
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_fun, hcardI] using hc

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open Topology

variable {ι : Type*}

variable [Finite ι]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem finite_index_of_bounded_grid_representatives {G ι : Type*} [Group G] [Fintype ι]
    (f : G → ι → ℚ) (hf : Function.Injective f) (Γ Λ : Subgroup G)
    (l N : ℕ) (hl : 0 < l) {B : ℝ}
    (hgrid : ∀ g ∈ Γ, f g ∈ denominatorGrid l) (hN : (l : ℝ) * B ≤ N)
    (hrep : ∀ g ∈ Γ, ∃ r ∈ Γ, (∀ i, |(f r i : ℝ)| ≤ B) ∧
      ∃ γ ∈ Λ, g = r * γ) :
    (Λ.subgroupOf Γ).FiniteIndex ∧ Λ.relIndex Γ ≤ (2 * N + 1) ^ Fintype.card ι := by
  classical
  let R : Set G := {r | r ∈ Γ ∧ ∀ i, |(f r i : ℝ)| ≤ B}
  let S : Set (ι → ℚ) := f '' R
  have hS := finite_card_rational_grid_box S l N hl
    (by rintro _ ⟨r, hr, rfl⟩; exact hgrid r hr.1)
    (by rintro _ ⟨r, hr, rfl⟩ i; exact hr.2 i) hN
  let : Finite S := hS.1.to_subtype
  let fR : R → S := fun r => ⟨f r.val, ⟨r.val, r.property, rfl⟩⟩
  have hfR : Function.Injective fR := by
    intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  let : Finite R := Finite.of_injective fR hfR
  let q : R → (Γ ⧸ Λ.subgroupOf Γ) := fun r => QuotientGroup.mk (⟨r.val, r.property.1⟩ : Γ)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨r, hr, hb, γ, hγ, heq⟩ := hrep g g.property
    refine ⟨⟨r, hr, hb⟩, ?_⟩
    apply QuotientGroup.eq.mpr
    change r⁻¹ * g.val ∈ Λ
    rw [heq, inv_mul_cancel_left]
    exact hγ
  let : Finite (Γ ⧸ Λ.subgroupOf Γ) := Finite.of_surjective q hq
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  exact (Nat.card_le_card_of_surjective q hq).trans
    ((Nat.card_le_card_of_injective fR hfR).trans hS.2)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℚ V]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ChartCutoff
namespace OAI

section

namespace Erdos3

open _root_.Set
open scoped NNReal

theorem chartCutoff_apply {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) {v : E} (hv : v ∈ e.source) :
    chartCutoff e ψ (e v) = ψ v := by
  simp only [chartCutoff, if_pos (e.map_source hv), e.left_inv hv]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥} [TopologicalSpace L]

section Real

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L]

end Real

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable [TopologicalSpace L]

variable [IsTopologicalAddGroup L] [ContinuousSMul ℝ L]

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

variable [IsScalarTower ℚ ℝ L]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set Manifold
open scoped Manifold ContDiff Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_realification_topology_of_grid (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ τ : TopologicalSpace (ℝ ⊗[ℚ] L),
      letI := τ
      IsTopologicalAddGroup (ℝ ⊗[ℚ] L) ∧ ContinuousSMul ℝ (ℝ ⊗[ℚ] L) ∧ T2Space (ℝ ⊗[ℚ] L) ∧
      IsTopologicalGroup (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) ∧
      ConnectedSpace (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) ∧
      SimplyConnectedSpace (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) ∧
      IsClosed (Γ.map NilpotentLieBCHGroup.realificationHom : Set
        (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))) ∧
      IsDiscrete (Γ.map NilpotentLieBCHGroup.realificationHom : Set
        (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))) := by
  let τ := moduleTopology ℝ (ℝ ⊗[ℚ] L)
  let : TopologicalSpace (ℝ ⊗[ℚ] L) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] L) := IsModuleTopology.topologicalAddGroup ℝ _
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (e.baseChange ℝ).finiteDimensional_of_finite
  have hcoord : Continuous (e.baseChange ℝ).equivFun :=
    IsModuleTopology.continuous_of_linearMap (e.baseChange ℝ).equivFun.toLinearMap
  let : T2Space (ℝ ⊗[ℚ] L) :=
    T2Space.of_injective_continuous (e.baseChange ℝ).equivFun.injective hcoord
  refine ⟨τ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact NilpotentLieBCHGroup.realification_subgroup_closed_discrete e Γ l hl hgrid

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set Manifold
open scoped Manifold ContDiff Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BoundedAdaptedBasis
namespace OAI

section

namespace Erdos3

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end Erdos3

end

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

theorem sub_coordinate_mem_tail (e : Basis (Fin d) ℚ L) (j : Fin d) {x : L}
    (hx : x ∈ basisTail e j.val) :
    x - e.repr x j • e j ∈ basisTail e (j.val + 1) := by
  classical
  intro k hk
  by_cases hkj : k = j
  · subst k
    simp
  · have hlt : k.val < j.val := by
      have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
      omega
    simp only [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply,
      hx k hlt, Basis.repr_self, Finsupp.single_eq_of_ne hkj, smul_zero, sub_zero]

namespace IsCentralLieBasis

variable {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
include he

end IsCentralLieBasis

end Erdos3

end

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d n : ℕ}

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

include F

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {d : ℕ}

theorem realBasisTail_eq_span (e : Basis (Fin d) ℝ L) (i : ℕ) :
    realBasisTail e i = Submodule.span ℝ (e '' {j : Fin d | i ≤ j.val}) := by
  ext x
  rw [e.mem_span_image]
  constructor
  · intro hx j hj
    by_contra h
    exact (Finsupp.mem_support_iff.mp hj) (hx j (Nat.lt_of_not_ge h))
  · intro hx j hj
    by_contra h
    exact (not_le_of_gt hj) (hx (Finsupp.mem_support_iff.mpr h))

theorem real_basis_mem_tail (e : Basis (Fin d) ℝ L) (j : Fin d) {i : ℕ} (hij : i ≤ j.val) :
    e j ∈ realBasisTail e i := by
  rw [realBasisTail_eq_span]
  exact Submodule.subset_span ⟨j, hij, rfl⟩

namespace IsRealCentralLieBasis

variable {e : Basis (Fin d) ℝ L} (he : IsRealCentralLieBasis e)
include he

end IsRealCentralLieBasis

end Erdos3

namespace Erdos3

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

theorem IsCentralLieBasis.real_baseChange {e : Basis (Fin d) ℚ L}
    (he : IsCentralLieBasis e) : IsRealCentralLieBasis (e.baseChange ℝ) := by
  intro j a
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
      intro k hk
      simp only [Basis.baseChange_apply, LieAlgebra.ExtendScalars.bracket_tmul,
        mul_one, Basis.baseChange_repr_tmul, he j a k hk, zero_smul]
  | add a b ha hb =>
      rw [add_lie]
      exact (realBasisTail (e.baseChange ℝ) (j.val + 1)).add_mem ha hb

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHOrderedReduction
namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include he hnil

theorem peel_mem_tail (j : Fin d) (g : NilpotentLieBCHGroup L s hnil)
    (hg : g.coord ∈ basisTail e j.val) :
    (((⟨e.repr g.coord j • e j⟩ : NilpotentLieBCHGroup L s hnil)⁻¹ * g).coord) ∈
      basisTail e (j.val + 1) := by
  change lieBCH s (-(e.repr g.coord j • e j)) g.coord ∈ _
  have herr := he.bch_remainder_mem_tail hnil j.val (-(e.repr g.coord j • e j)) hg
  have hlin : -(e.repr g.coord j • e j) + g.coord ∈ basisTail e (j.val + 1) := by
    simpa only [sub_eq_add_neg, add_comm] using sub_coordinate_mem_tail e j hg
  simpa only [sub_add_cancel] using (basisTail e (j.val + 1)).add_mem herr hlin

theorem leading_coordinate (j : Fin d) (t : ℚ) (r : NilpotentLieBCHGroup L s hnil)
    (hr : r.coord ∈ basisTail e (j.val + 1)) :
    e.repr (((⟨t • e j⟩ : NilpotentLieBCHGroup L s hnil) * r).coord) j = t := by
  change e.repr (lieBCH s (t • e j) r.coord) j = t
  rw [he.bch_low_coordinate hnil j.val (t • e j)
    (basisTail_antitone e (Nat.le_succ j.val) hr) j le_rfl]
  simp only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, hr j (Nat.lt_succ_self j.val), add_zero]

end Erdos3.IsCentralLieBasis

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.OrderedBasisCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (e : Basis (Fin d) ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

theorem orderedBasisTailProduct_terminal {i : ℕ} (hi : d ≤ i) (t : Fin d → ℚ) :
    orderedBasisTailProduct e hnil i t = 1 := by
  simp only [orderedBasisTailProduct,
    List.drop_eq_nil_of_le (as := List.finRange d) (i := i) (by simpa using hi),
    List.map_nil, List.prod_nil]

theorem orderedBasisTailProduct_step (j : Fin d) (t : Fin d → ℚ) :
    orderedBasisTailProduct e hnil j.val t =
      (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil) * orderedBasisTailProduct e hnil (j.val + 1) t := by
  unfold orderedBasisTailProduct
  rw [List.drop_eq_getElem_cons (by simp), List.map_cons, List.prod_cons]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]

theorem orderedBasisTailProduct_congr (i : ℕ) {t u : Fin d → ℚ}
    (h : ∀ j : Fin d, i ≤ j.val → t j = u j) :
    orderedBasisTailProduct e hnil i t = orderedBasisTailProduct e hnil i u := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  rw [h j (mem_drop_finRange_iff.mp hj)]

namespace IsCentralLieBasis

variable {e} (he : IsCentralLieBasis e)
include he

theorem orderedBasisTailProduct_mem_tail (i : ℕ) (t : Fin d → ℚ) :
    (orderedBasisTailProduct e hnil i t).coord ∈ basisTail e i := by
  change orderedBasisTailProduct e hnil i t ∈
    NilpotentLieBCHGroup.subgroup (he.tailIdeal i).toLieSubalgebra
  unfold orderedBasisTailProduct
  apply list_prod_mem
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  exact (basisTail e i).smul_mem _ (basis_mem_tail e j (mem_drop_finRange_iff.mp hj))

theorem orderedBasisTailProduct_leading (j : Fin d) (t : Fin d → ℚ) :
    e.repr (orderedBasisTailProduct e hnil j.val t).coord j = t j := by
  rw [orderedBasisTailProduct_step]
  exact he.leading_coordinate hnil j (t j) _ (he.orderedBasisTailProduct_mem_tail hnil _ t)

end IsCentralLieBasis
end Erdos3

end

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include he

theorem orderedBasisTailProduct_eq_of_product_eq {t u : Fin d → ℚ}
    (h : orderedBasisProduct e hnil t = orderedBasisProduct e hnil u)
    (i : ℕ) (hi : i ≤ d) :
    orderedBasisTailProduct e hnil i t = orderedBasisTailProduct e hnil i u := by
  induction i with
  | zero => exact h
  | succ i ih =>
      have hid : i < d := by omega
      let j : Fin d := ⟨i, hid⟩
      have ht := ih (by omega)
      change orderedBasisTailProduct e hnil j.val t =
        orderedBasisTailProduct e hnil j.val u at ht
      have hc : t j = u j := by
        have hc := congrArg (fun g => e.repr g.coord j) ht
        simpa only [he.orderedBasisTailProduct_leading hnil j] using hc
      rw [orderedBasisTailProduct_step, orderedBasisTailProduct_step, hc] at ht
      exact mul_left_cancel ht

theorem orderedBasisProduct_injective : Function.Injective (orderedBasisProduct e hnil) := by
  intro t u h
  funext j
  have ht := he.orderedBasisTailProduct_eq_of_product_eq hnil h j.val (Nat.le_of_lt j.isLt)
  have hc := congrArg (fun g => e.repr g.coord j) ht
  simpa only [he.orderedBasisTailProduct_leading hnil j] using hc

end Erdos3.IsCentralLieBasis

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageRepresentatives
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

end Erdos3

end

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_rational_representatives_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m H : ℕ) (p : ℝ),
      Λ ≤ Γ → 0 < l → 0 < m → bchSubgroupCoordinates e Γ ⊆ denominatorGrid l →
      scaledIntegerGrid m ⊆ bchSubgroupCoordinates e Λ →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (m : ℝ) ≤ Real.exp p →
      ∀ g ∈ Γ, ∃ r ∈ Γ, (∀ i, |(e.repr r.coord i : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        ∃ γ ∈ Λ, g = r * γ := by
  obtain ⟨C, hC, hreal⟩ := exists_realification_representatives_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e hnil Γ Λ l m H p hΛ hl hm houter hinner hc hp hd hH hmb g hg
  obtain ⟨τ, hA, hS, _⟩ := exists_realification_topology_of_grid e Γ l hl houter
  let : TopologicalSpace (ℝ ⊗[ℚ] L) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] L) := hA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] L) := hS
  obtain ⟨r, hr, γR, hγR, heq⟩ :=
    hreal e hnil Λ m H p hm hinner hc hp hd hH hmb (NilpotentLieBCHGroup.realificationHom g)
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hγR
  let rQ := g * γ⁻¹
  have hphi : NilpotentLieBCHGroup.realificationHom rQ = r := by
    rw [map_mul, map_inv, heq]
    group
  refine ⟨rQ, Γ.mul_mem hg (Γ.inv_mem (hΛ hγ)), ?_, γ, hγ, ?_⟩
  · intro i
    have hi := hr i
    rw [← hphi] at hi
    change |(e.baseChange ℝ).equivFun (NilpotentLieBCHGroup.realificationHom rQ).coord i| ≤ _ at hi
    rwa [NilpotentLieBCHGroup.realificationHom_coordinates] at hi
  · dsimp [rQ]
    group

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_subgroup_index_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m H : ℕ) (p : ℝ),
      Λ ≤ Γ → 0 < l → 0 < m → bchSubgroupCoordinates e Γ ⊆ denominatorGrid l →
      scaledIntegerGrid m ⊆ bchSubgroupCoordinates e Λ →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (l : ℝ) ≤ Real.exp p → (m : ℝ) ≤ Real.exp p →
      (Λ.subgroupOf Γ).FiniteIndex ∧ (Λ.relIndex Γ : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hrep⟩ := exists_rational_representatives_exp_bound s
  refine ⟨C + 5, by omega, ?_⟩
  intro ι L _ _ _ e hnil Γ Λ l m H p hΛ hl hm houter hinner hc hp hd hH hlb hmb
  let f : NilpotentLieBCHGroup L s hnil → ι → ℚ := fun g => e.equivFun g.coord
  have hf : Function.Injective f := by
    intro x y hxy
    exact NilpotentLieBCHGroup.ext (e.equivFun.injective hxy)
  obtain ⟨hfinite, hindex⟩ := finite_index_of_bounded_grid_representatives f hf Γ Λ l
    ⌈(l : ℝ) * Real.exp ((p + C) ^ C)⌉₊ hl
    (fun g hg => houter ((bchSubgroupCoordinates_repr e Γ g).mpr hg))
    (Nat.le_ceil _) (hrep e hnil Γ Λ l m H p hΛ hl hm houter hinner hc hp hd hH hmb)
  refine ⟨hfinite, ?_⟩
  apply (Nat.cast_le.mpr hindex).trans
  simpa only [Nat.cast_add, Nat.cast_ofNat] using grid_box_count_le_exp C (Fintype.card ι) l hC hp hd hlb

end Erdos3

end

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped NNReal

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

theorem patch_term {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1)
    (t : σ → ℝ) (b : Fin 1 → ℤ) :
    (w.patch s hs P hP).kernel.value (((w.patch s hs P hP).form.slots t).residual b) =
      w.value (aeval t P - (b 0 : ℝ)) := by
  simp only [patch, PolynomialPatch.ofCoordinates, kernel, TriangularSlots.residual,
    PolynomialSlots.ofCoordinates_center, map_sub, aeval_C, Algebra.algebraMap_self_apply]
  congr 1
  ring

theorem patch_value {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1) (t : σ → ℝ) :
    (w.patch s hs P hP).value t = w.value (Int.fract (aeval t P)) := by
  change (∑' b : Fin 1 → ℤ, (w.patch s hs P hP).kernel.value
    (((w.patch s hs P hP).form.slots t).residual b)) = _
  simp_rw [w.patch_term s hs P hP t]
  rw [tsum_eq_single (fun _ : Fin 1 => ⌊aeval t P⌋)]
  · rfl
  · intro b hb
    by_contra h
    obtain ⟨h0, h1⟩ := w.interior _ h
    have hfloor : ⌊aeval t P⌋ = b 0 := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    apply hb
    funext i
    fin_cases i
    exact hfloor.symm

theorem patch_contributing_lift {σ : Type*} (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1)
    (t : σ → ℝ) (b : Fin 1 → ℤ)
    (hb : (w.patch s hs P hP).kernel.value
      (((w.patch s hs P hP).form.slots t).residual b) ≠ 0) :
    b 0 = ⌊aeval t P⌋ := by
  rw [w.patch_term s hs P hP t] at hb
  obtain ⟨h0, h1⟩ := w.interior _ hb
  exact (Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩).symm

end RepresentativeWindow
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealBCHOrderedReduction
namespace OAI

section

namespace Erdos3.IsRealCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L] {d s : ℕ}
  {e : Basis (Fin d) ℝ L} (he : IsRealCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include he hnil

theorem bch_remainder_mem_tail (i : ℕ) (a : L) {b : L} (hb : b ∈ realBasisTail e i) :
    lieBCH s a b - (a + b) ∈ realBasisTail e (i + 1) :=
  lieBCH_sub_add_mem hnil (he.tailIdeal (i + 1)) a b (he.lie_mem_tail_succ i a hb)

theorem bch_low_coordinate (i : ℕ) (a : L) {b : L} (hb : b ∈ realBasisTail e i)
    (k : Fin d) (hk : k.val ≤ i) :
    e.repr (lieBCH s a b) k = e.repr a k + e.repr b k := by
  have h := he.bch_remainder_mem_tail hnil i a hb k (Nat.lt_succ_of_le hk)
  rw [map_sub, Finsupp.sub_apply, map_add, Finsupp.add_apply] at h
  exact sub_eq_zero.mp h

end Erdos3.IsRealCentralLieBasis

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealOrderedBasisProduct
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] {d s : ℕ}
  (e : Basis (Fin d) ℝ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

theorem realOrderedBasisTailProduct_step (j : Fin d) (t : Fin d → ℝ) :
    realOrderedBasisTailProduct e hnil j.val t =
      (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil) * realOrderedBasisTailProduct e hnil (j.val + 1) t := by
  unfold realOrderedBasisTailProduct
  rw [List.drop_eq_getElem_cons (by simp), List.map_cons, List.prod_cons]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]

theorem realOrderedBasisProduct_eq_prefix_mul_tail (i : ℕ) (t : Fin d → ℝ) :
    realOrderedBasisProduct e hnil t =
      realOrderedBasisPrefixProduct e hnil i t * realOrderedBasisTailProduct e hnil i t := by
  unfold realOrderedBasisProduct realOrderedBasisPrefixProduct realOrderedBasisTailProduct
  rw [List.drop_zero, ← List.prod_append, ← List.map_append, List.take_append_drop]

variable [IsScalarTower ℚ ℝ L]

namespace IsRealCentralLieBasis

variable {e} (he : IsRealCentralLieBasis e)
include he

theorem realOrderedBasisTailProduct_mem_tail (i : ℕ) (t : Fin d → ℝ) :
    (realOrderedBasisTailProduct e hnil i t).coord ∈ realBasisTail e i := by
  change realOrderedBasisTailProduct e hnil i t ∈
    NilpotentLieBCHGroup.subgroup (he.tailIdeal i).toLieSubalgebra
  unfold realOrderedBasisTailProduct
  apply list_prod_mem
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  exact (realBasisTail e i).smul_mem _ (real_basis_mem_tail e j (mem_drop_finRange_iff.mp hj))

theorem mul_tail_coordinate (a b : NilpotentLieBCHGroup L s hnil) (j : Fin d)
    (hb : b.coord ∈ realBasisTail e (j.val + 1)) :
    e.repr (a * b).coord j = e.repr a.coord j := by
  change e.repr (lieBCH s a.coord b.coord) j = _
  rw [he.bch_low_coordinate hnil (j.val + 1) a.coord hb j (Nat.le_succ _),
    hb j (Nat.lt_succ_self _), add_zero]

theorem mul_basis_coordinate (a : NilpotentLieBCHGroup L s hnil) (j : Fin d) (t : ℝ) :
    e.repr (a * (⟨t • e j⟩ : NilpotentLieBCHGroup L s hnil)).coord j =
      e.repr a.coord j + t := by
  change e.repr (lieBCH s a.coord (t • e j)) j = _
  rw [he.bch_low_coordinate hnil j.val a.coord
    ((realBasisTail e j.val).smul_mem t (real_basis_mem_tail e j le_rfl)) j le_rfl]
  simp only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]

theorem mul_realOrderedBasisProduct_coordinate (a : NilpotentLieBCHGroup L s hnil)
    (t : Fin d → ℝ) (j : Fin d) :
    e.repr (a * realOrderedBasisProduct e hnil t).coord j =
      e.repr (a * realOrderedBasisPrefixProduct e hnil j.val t).coord j + t j := by
  calc
    _ = e.repr (((a * realOrderedBasisPrefixProduct e hnil j.val t) *
        (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil)) *
        realOrderedBasisTailProduct e hnil (j.val + 1) t).coord j := by
      rw [realOrderedBasisProduct_eq_prefix_mul_tail e hnil j.val,
        realOrderedBasisTailProduct_step]
      simp only [mul_assoc]
    _ = e.repr ((a * realOrderedBasisPrefixProduct e hnil j.val t) *
        (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil)).coord j :=
      he.mul_tail_coordinate hnil _ _ j (he.realOrderedBasisTailProduct_mem_tail hnil _ t)
    _ = _ := he.mul_basis_coordinate hnil _ j (t j)

end IsRealCentralLieBasis
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledIntegralCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (e : Basis (Fin d) ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

theorem integral_basis_factor_mem (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B) (j : Fin d) (n : ℤ) :
    (⟨((B : ℚ) * (n : ℚ)) • e j⟩ : NilpotentLieBCHGroup L s hnil) ∈ Λ := by
  apply (bchSubgroupCoordinates_repr e Λ _).mp
  rw [hgrid]
  have h := (coordinateGridModule e B).smul_mem n (scaled_basis_mem_coordinateGridModule e B j)
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_comm (n : ℚ) (B : ℚ)] at h
  exact h

theorem integralOrderedBasisProduct_mem (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B) (z : Fin d → ℤ) :
    integralOrderedBasisProduct e hnil B z ∈ Λ := by
  apply list_prod_mem
  intro g hg
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
  exact integral_basis_factor_mem e hnil Λ B hgrid j (z j)

namespace IsCentralLieBasis

variable {e} (he : IsCentralLieBasis e)
include he

theorem integralOrderedBasisProduct_injective (B : ℕ) (hB : 0 < B) :
    Function.Injective (integralOrderedBasisProduct e hnil B) := by
  intro z w hzw
  have h := he.orderedBasisProduct_injective hnil hzw
  funext j
  apply Int.cast_injective (α := ℚ)
  exact mul_left_cancel₀ (show (B : ℚ) ≠ 0 by exact_mod_cast hB.ne') (congrFun h j)

theorem exists_integralOrderedBasisProduct
    (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g ∈ Λ) :
    ∃ z : Fin d → ℤ, integralOrderedBasisProduct e hnil B z = g := by
  classical
  have hfactor (k i : ℕ) (hik : i + k = d)
      (g : NilpotentLieBCHGroup L s hnil) (hg : g ∈ Λ) (hgt : g.coord ∈ basisTail e i) :
      ∃ z : Fin d → ℤ,
        orderedBasisTailProduct e hnil i (fun j => (B : ℚ) * (z j : ℚ)) = g := by
    induction k generalizing i g with
    | zero =>
        have hi : i = d := by omega
        subst i
        refine ⟨fun _ => 0, ?_⟩
        rw [orderedBasisTailProduct_terminal e hnil le_rfl]
        apply NilpotentLieBCHGroup.ext
        have hz : g.coord = 0 := by
          simpa only [basisTail_terminal, Submodule.mem_bot] using hgt
        exact hz.symm
    | succ k ih =>
        have hi : i < d := by omega
        let j : Fin d := ⟨i, hi⟩
        have hcoord := (bchSubgroupCoordinates_repr e Λ g).mpr hg
        rw [hgrid] at hcoord
        obtain ⟨v, hv⟩ := hcoord
        have hvj : e.repr g.coord j = (B : ℚ) * (v j : ℚ) := congrFun hv j
        let a : NilpotentLieBCHGroup L s hnil := ⟨((B : ℚ) * (v j : ℚ)) • e j⟩
        have ha : a ∈ Λ := integral_basis_factor_mem e hnil Λ B hgrid j (v j)
        let r := a⁻¹ * g
        have hr : r ∈ Λ := Λ.mul_mem (Λ.inv_mem ha) hg
        have hrt : r.coord ∈ basisTail e (i + 1) := by
          simpa only [hvj] using he.peel_mem_tail hnil j g hgt
        obtain ⟨z, hz⟩ := ih (i + 1) (by omega) r hr hrt
        let u := Function.update z j (v j)
        have huj : u j = v j := by simp [u]
        have hu : orderedBasisTailProduct e hnil (i + 1) (fun l => (B : ℚ) * (u l : ℚ)) =
            orderedBasisTailProduct e hnil (i + 1) (fun l => (B : ℚ) * (z l : ℚ)) := by
          apply orderedBasisTailProduct_congr
          intro l hl
          have hlj : l ≠ j := by
            intro h
            subst l
            change i + 1 ≤ i at hl
            omega
          simp only [u, Function.update_of_ne hlj]
        refine ⟨u, ?_⟩
        change orderedBasisTailProduct e hnil j.val _ = g
        rw [orderedBasisTailProduct_step, huj]
        change a * orderedBasisTailProduct e hnil (i + 1) _ = g
        rw [hu, hz]
        exact mul_inv_cancel_left a g
  exact hfactor d 0 (by omega) g hg (by simp [basisTail_zero])

theorem exists_unique_integralOrderedBasisProduct
    (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ) (hB : 0 < B)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g ∈ Λ) :
    ∃! z : Fin d → ℤ, integralOrderedBasisProduct e hnil B z = g := by
  obtain ⟨z, hz⟩ := he.exists_integralOrderedBasisProduct hnil Λ B hgrid g hg
  exact ⟨z, hz, fun w hw => he.integralOrderedBasisProduct_injective hnil B hB (hw.trans hz.symm)⟩

end IsCentralLieBasis
end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (e : Basis (Fin d) ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

theorem realification_integralOrderedBasisProduct (B : ℕ) (z : Fin d → ℤ) :
    realificationHom (integralOrderedBasisProduct e hnil B z) =
      realIntegralOrderedBasisProduct e hnil B z := by
  unfold integralOrderedBasisProduct orderedBasisProduct orderedBasisTailProduct
    realIntegralOrderedBasisProduct realOrderedBasisProduct realOrderedBasisTailProduct
  rw [map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _
  apply NilpotentLieBCHGroup.ext
  change rationalLieInclusion (((B : ℚ) * (z j : ℚ)) • e j) =
    ((B : ℝ) * (z j : ℝ)) • (e.baseChange ℝ) j
  rw [map_smul, Basis.baseChange_apply]
  simp only [rationalLieInclusion_apply, ← Rat.cast_smul_eq_qsmul ℝ,
    Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast]

theorem realIntegralOrderedBasisProduct_mem
    (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B) (z : Fin d → ℤ) :
    realIntegralOrderedBasisProduct e hnil B z ∈ Λ.map realificationHom := by
  exact Subgroup.mem_map.mpr ⟨integralOrderedBasisProduct e hnil B z,
    integralOrderedBasisProduct_mem e hnil Λ B hgrid z,
    realification_integralOrderedBasisProduct e hnil B z⟩

namespace IsCentralLieBasis

variable {e} (he : IsCentralLieBasis e)
include he

theorem exists_realIntegralOrderedBasisProduct
    (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℕ)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (hg : g ∈ Λ.map realificationHom) :
    ∃ z : Fin d → ℤ, realIntegralOrderedBasisProduct e hnil B z = g := by
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  obtain ⟨z, hz⟩ := he.exists_integralOrderedBasisProduct hnil Λ B hgrid a ha
  exact ⟨z, (realification_integralOrderedBasisProduct e hnil B z).symm.trans
    (congrArg realificationHom hz)⟩

end IsCentralLieBasis
end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_controlled_integral_coordinates (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (e : Basis (Fin d) ℚ L) (_he : IsCentralLieBasis e)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ),
      0 < l → (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      bchSubgroupCoordinates e Γ ⊆ denominatorGrid l →
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∃ (B : ℕ) (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)),
        0 < B ∧ l ∣ B ∧ (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        Λ ≤ Γ ∧ (Λ.subgroupOf Γ).FiniteIndex ∧
        bchSubgroupCoordinates e Λ = scaledIntegerGrid B ∧
        ∀ g ∈ Λ, ∃! z : Fin d → ℤ, integralOrderedBasisProduct e hnil B z = g := by
  obtain ⟨C, hC, hgrid⟩ := exists_integral_grid_subgroup_exp s
  obtain ⟨I, _, hindex⟩ := exists_subgroup_index_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro L _ _ d e he hnil Γ l H p hl hc hinner houter hp hd hH hlp
  obtain ⟨B, Λ, hB, hdiv, hbound, hΛ, hcoords⟩ :=
    hgrid e hnil Γ l H p hl hc hinner hp (by simpa only [Fintype.card_fin] using hd) hH hlp
  have hpq : p ≤ (p + C) ^ C := by
    calc
      p ≤ p + C := le_add_of_nonneg_right (Nat.cast_nonneg C)
      _ ≤ (p + C) ^ C := by
        simpa only [pow_one] using pow_le_pow_right₀ (show (1 : ℝ) ≤ p + C by
          have : (2 : ℝ) ≤ C := by exact_mod_cast hC
          linarith) (show 1 ≤ C by omega)
  have hfinite := (hindex e hnil Γ Λ l B H ((p + C) ^ C) hΛ hl hB houter
    (by rw [hcoords]) hc (hp.trans hpq) (by simpa only [Fintype.card_fin] using hd.trans hpq)
    (hH.trans (Real.exp_le_exp.mpr hpq)) (hlp.trans (Real.exp_le_exp.mpr hpq)) hbound).1
  exact ⟨B, Λ, hB, hdiv, hbound, hΛ, hfinite, hcoords,
    he.exists_unique_integralOrderedBasisProduct hnil Λ B hB hcoords⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealOrderedSlots
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] {d s : ℕ}
  (e : Basis (Fin d) ℝ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

namespace IsRealCentralLieBasis

variable [IsScalarTower ℚ ℝ L] {e} (he : IsRealCentralLieBasis e)
include he

theorem realOrderedSlots_residual (B : ℝ) (hB : B ≠ 0)
    (a : NilpotentLieBCHGroup L s hnil) (b : Fin d → ℤ) :
    (realOrderedSlots e hnil B a).residual b = fun j =>
      e.repr (a * realOrderedBasisProduct e hnil (fun k => B * (b k : ℝ))).coord j / B := by
  funext j
  dsimp only [TriangularSlots.residual, realOrderedSlots]
  rw [he.mul_realOrderedBasisProduct_coordinate hnil]
  field_simp; ring

theorem smul_realOrderedSlots_residual (B : ℝ) (hB : B ≠ 0)
    (a : NilpotentLieBCHGroup L s hnil) (b : Fin d → ℤ) :
    B • (realOrderedSlots e hnil B a).residual b =
      e.equivFun (a * realOrderedBasisProduct e hnil (fun k => B * (b k : ℝ))).coord := by
  rw [he.realOrderedSlots_residual hnil B hB]
  funext j
  change B * (_ / B) = _
  exact mul_div_cancel₀ _ hB

end IsRealCentralLieBasis
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeChartKernel
namespace OAI

section

namespace Erdos3

open _root_.Set
open scoped NNReal

variable {ι X : Type*} [Fintype ι] [MetricSpace X]

omit [Fintype ι] in
theorem chartCoordinateKernel_recover (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) {x : X} (hx : x ∈ phi.target) :
    chartCoordinateKernel phi F (phi.symm x) = F x :=
  chartCutoff_apply phi.symm F hx

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X : Type*} [MetricSpace X] {d : ℕ}
  (phi : OpenPartialHomeomorph (Fin d → ℝ) X) (F : X → ℝ)
  (A K r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1)
  (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hLip : LipschitzWith A F)
  (hsource : phi.source = {v | ∀ i, |v i| < (r : ℝ)})
  (hinner : tsupport F ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4))
  (hForward : LipschitzOnWith K phi phi.source) (B : ℕ) (hB : 4 ≤ B)

theorem scaledChartKernel_value (x : Fin d → ℝ) :
    (scaledChartKernel phi F A K r hr hr1 hF hLip hsource hinner hForward B hB).value x =
      chartCoordinateKernel phi F ((B : ℝ) • x) := rfl

theorem scaledChartKernel_recover {x : X} (hx : x ∈ phi.target) :
    (scaledChartKernel phi F A K r hr hr1 hF hLip hsource hinner hForward B hB).value
      (fun i => phi.symm x i / B) = F x := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  have he : (B : ℝ) • (fun i => phi.symm x i / B) = phi.symm x := by
    funext i
    change (B : ℝ) * (phi.symm x i / B) = phi.symm x i
    field_simp [hB0]
  rw [scaledChartKernel_value, he]
  exact chartCoordinateKernel_recover phi F hx

theorem chartKernel_log_bound {A K r : ℝ≥0} {B : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (hA : (A : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p)
    (hr : 1 / (r : ℝ) ≤ Real.exp p) (hB : (B : ℝ) ≤ Real.exp p) :
    Real.log (2 + (((A * K + 1 / (r / 4)) * B : ℝ≥0) : ℝ)) ≤ 3 * p + 6 := by
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_one, NNReal.coe_ofNat]
  rw [show 1 / ((r : ℝ) / 4) = 4 * (1 / (r : ℝ)) by ring]
  have he : 1 ≤ Real.exp p := Real.one_le_exp hp
  have he3 : 1 ≤ Real.exp p ^ 3 := one_le_pow₀ he
  have he23 : Real.exp p ^ 2 ≤ Real.exp p ^ 3 := pow_le_pow_right₀ he (by decide)
  have hAK := mul_le_mul hA hK K.coe_nonneg (Real.exp_nonneg p)
  have hfour := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 4)
  have hprod := mul_le_mul (add_le_add hAK hfour) hB (Nat.cast_nonneg B)
    (show 0 ≤ Real.exp p * Real.exp p + 4 * Real.exp p by positivity)
  have hseven : (7 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have hlast := mul_le_mul_of_nonneg_left hseven (show 0 ≤ Real.exp p ^ 3 by positivity)
  rw [Real.exp_add]
  have heq : Real.exp (3 * p) = Real.exp p ^ 3 := by
    simpa using Real.exp_nat_mul p 3
  rw [heq]
  nlinarith

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} (T : D.Niltest w)

variable (hT : T.UnitIntervalValued) (phi : OpenPartialHomeomorph (Fin d → ℝ) D.Space)
  (K r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1)
  (hsource : phi.source = {v | ∀ i, |v i| < (r : ℝ)})
  (hinner : tsupport T.observable ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4))
  (hForward : letI := D.metricSpace; LipschitzOnWith K phi phi.source) (hgrid : 4 ≤ D.grid)

theorem chartKernel_lip :
    (T.chartKernel hT phi K r hr hr1 hsource hinner hForward hgrid).lip =
      (T.lipBound * K + 1 / (r / 4)) * D.grid := rfl

theorem chartKernel_value (v : Fin d → ℝ) :
    letI := D.metricSpace
    (T.chartKernel hT phi K r hr hr1 hsource hinner hForward hgrid).value v =
      chartCoordinateKernel phi (fun x => (T.observable x).re) ((D.grid : ℝ) • v) := rfl

theorem chartKernel_recover {x : D.Space} (hx : x ∈ phi.target) :
    (T.chartKernel hT phi K r hr hr1 hsource hinner hForward hgrid).value
      (fun i => phi.symm x i / D.grid) = (T.observable x).re := by
  let := D.metricSpace
  exact scaledChartKernel_recover phi (fun x => (T.observable x).re) T.lipBound K r hr hr1
    (fun x => (hT x).2) T.realObservable_lipschitz hsource
    (T.realObservable_tsupport.trans hinner) hForward D.grid hgrid hx

theorem chartKernel_log_bound {p : ℝ} (hp : 0 ≤ p) (hcomplexity : T.ComplexityLE p)
    (hK : (K : ℝ) ≤ Real.exp p) (hri : 1 / (r : ℝ) ≤ Real.exp p) :
    Real.log (2 + ((T.chartKernel hT phi K r hr hr1 hsource hinner hForward hgrid).lip : ℝ)) ≤
      3 * p + 6 := by
  rw [T.chartKernel_lip]
  apply Erdos3.chartKernel_log_bound hp ?_ hK hri hcomplexity.1.2.1
  have hb := observable_budget hcomplexity
  linarith [T.normBound.coe_nonneg]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ChartLatticePeriodization
namespace OAI

section

namespace Erdos3

theorem triangular_patchValue_eq_chartObservable {G : Type*} [Group G] {d : ℕ}
    (Λ : Subgroup G) [MetricSpace (G ⧸ Λ)] (q : G ≃ (Fin d → ℝ))
    (gamma : (Fin d → ℤ) → G) (hgamma : ∀ b, gamma b ∈ Λ)
    (hsurj : ∀ a ∈ Λ, ∃ b, gamma b = a) (z g : G)
    (phi : OpenPartialHomeomorph (Fin d → ℝ) (G ⧸ Λ))
    (hphi : ∀ v, phi v = QuotientGroup.mk (z * q.symm v))
    (F : (G ⧸ Λ) → ℝ) (hF : Function.support F ⊆ phi.target)
    (A : TriangularSlots d) (Phi : PatchKernel d) (B : ℝ)
    (hPhi : ∀ v, Phi.value v = chartCoordinateKernel phi F (B • v))
    (hA : ∀ b, B • A.residual b = q (z⁻¹ * g * gamma b)) :
    A.patchValue Phi = F (QuotientGroup.mk g) := by
  have hchart (b : Fin d → ℤ) : phi (B • A.residual b) = QuotientGroup.mk g := by
    rw [hphi, hA, q.symm_apply_apply]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
    exact QuotientGroup.mk_mul_of_mem g (hgamma b)
  by_cases hzero : F (QuotientGroup.mk g) = 0
  · rw [hzero]
    apply A.patchValue_eq_zero
    intro b
    rw [hPhi]
    by_cases hb : B • A.residual b ∈ phi.source
    · rw [chartCoordinateKernel_of_mem phi F hb, hchart b, hzero]
    · exact chartCoordinateKernel_of_not_mem phi F hb
  · have hx : QuotientGroup.mk g ∈ phi.target := hF hzero
    let v := phi.symm (QuotientGroup.mk g)
    have hv : v ∈ phi.source := phi.map_target hx
    have heq : (QuotientGroup.mk (z * q.symm v) : G ⧸ Λ) = QuotientGroup.mk g :=
      (hphi v).symm.trans (phi.right_inv hx)
    have hmem : g⁻¹ * (z * q.symm v) ∈ Λ := QuotientGroup.eq.mp heq.symm
    obtain ⟨b, hb⟩ := hsurj _ hmem
    have hcoord : B • A.residual b = v := by
      rw [hA, hb]
      have hcancel : z⁻¹ * g * (g⁻¹ * (z * q.symm v)) = q.symm v := by group
      rw [hcancel, q.apply_symm_apply]
    have hvalue : Phi.value (A.residual b) = F (QuotientGroup.mk g) := by
      rw [hPhi, hcoord, chartCoordinateKernel_of_mem phi F hv, phi.right_inv hx]
    have hnz : Phi.value (A.residual b) ≠ 0 := by rwa [hvalue]
    exact (A.patchValue_eq_of_nonzero Phi hnz).trans hvalue

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealOrderedChartPatch
namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (Λ : Subgroup (NilpotentLieBCHGroup L s hnil))
  [MetricSpace (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
    (realification_lowerCentralSeries_eq_bot hnil) ⧸ Λ.map realificationHom)]

include he

theorem realOrderedSlots_patchValue (B : ℕ) (hB : 0 < B)
    (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B)
    (z g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (phi : OpenPartialHomeomorph (Fin d → ℝ)
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
        (realification_lowerCentralSeries_eq_bot hnil) ⧸ Λ.map realificationHom))
    (hphi : ∀ v, phi v = QuotientGroup.mk
      (z * (⟨(e.baseChange ℝ).equivFun.symm v⟩ : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
        (realification_lowerCentralSeries_eq_bot hnil))))
    (F : (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
      (realification_lowerCentralSeries_eq_bot hnil) ⧸ Λ.map realificationHom) → ℝ)
    (hF : Function.support F ⊆ phi.target) (Phi : PatchKernel d)
    (hPhi : ∀ v, Phi.value v = chartCoordinateKernel phi F ((B : ℝ) • v)) :
    (realOrderedSlots (e.baseChange ℝ) (realification_lowerCentralSeries_eq_bot hnil)
      (B : ℝ) (z⁻¹ * g)).patchValue Phi = F (QuotientGroup.mk g) := by
  let q : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) ≃
      (Fin d → ℝ) :=
    { toFun := fun a => (e.baseChange ℝ).equivFun a.coord
      invFun := fun v => ⟨(e.baseChange ℝ).equivFun.symm v⟩
      left_inv := fun a => NilpotentLieBCHGroup.ext
        ((e.baseChange ℝ).equivFun.symm_apply_apply a.coord)
      right_inv := fun v => (e.baseChange ℝ).equivFun.apply_symm_apply v }
  apply triangular_patchValue_eq_chartObservable (Λ.map realificationHom)
    q (realIntegralOrderedBasisProduct e hnil B)
    (realIntegralOrderedBasisProduct_mem e hnil Λ B hgrid)
    (he.exists_realIntegralOrderedBasisProduct hnil Λ B hgrid) z g phi hphi F hF
    _ Phi (B : ℝ) hPhi
  intro b
  exact he.real_baseChange.smul_realOrderedSlots_residual
    (realification_lowerCentralSeries_eq_bot hnil) (B : ℝ)
    (by exact_mod_cast hB.ne') (z⁻¹ * g) b

end Erdos3.IsCentralLieBasis

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

theorem eval₂_substitute (f : σ → MvPolynomial τ R) (x : τ → S)
    (p : VectorPolynomial σ R V) :
    eval₂ x (substitute f p) = eval₂ (fun i => MvPolynomial.aeval x (f i)) p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
      simp only [substitute_tmul, eval₂_tmul]
      rw [MvPolynomial.comp_aeval_apply]
  | add p q hp hq => simp only [map_add, hp, hq]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} (F : NilpotentLieFiltration L s)

theorem polynomialOrbitSubstitute_realEval {w : σ → ℕ} {v : τ → ℕ}
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    (p : F.PolynomialOrbit w) (x : τ → ℝ) :
    F.polynomialOrbitRealEval v x (F.polynomialOrbitSubstitute f hf p) =
      F.polynomialOrbitRealEval w (fun i => MvPolynomial.aeval x (f i)) p := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_substitute f x p.log

theorem polynomialOrbitRealEval_constant (w : σ → ℕ) (a : F.Group) (x : σ → ℝ) :
    F.polynomialOrbitRealEval w x (F.constantPolynomialOrbit w a) = a := by
  apply NilpotentLieBCHGroup.ext
  change eval₂ x (monomial 0 a.coord) = a.coord
  rw [eval₂_monomial, Finsupp.prod_zero_index, one_smul]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))

include hlayer

theorem orderedSlotFactor_realEval (B : ℝ) (i j : Fin d)
    (u : σ → ℝ) (v : Fin d → ℝ) :
    F.realification.polynomialOrbitRealEval (patchVariableWeight omega i)
      (Sum.elim u (fun k => v (earlierSlot i k)))
      (F.orderedSlotFactor e omega hlayer B i j) =
      (⟨(if j.val < i.val then B * v j else 0) • (e.baseChange ℝ) j⟩ :
        F.realification.Group) := by
  classical
  by_cases h : j.val < i.val
  · apply NilpotentLieBCHGroup.ext
    simp only [orderedSlotFactor, dif_pos h, polynomialOrbitRealEval_coord,
      polynomialOrbitOfLog_log, eval₂_monomial, pow_zero, Finsupp.prod_single_index,
      pow_one, Sum.elim_inr, earlierSlot, Fin.eta, if_pos h, smul_smul]
    rw [mul_comm]
  · simp only [orderedSlotFactor, dif_neg h, map_one, if_neg h, zero_smul]
    rfl

theorem orderedSlotOrbit_realEval (B : ℝ) (a : F.realification.Group)
    (p : F.realification.PolynomialOrbit (fun _ : σ => 1)) (i : Fin d)
    (u : σ → ℝ) (v : Fin d → ℝ) :
    F.realification.polynomialOrbitRealEval (patchVariableWeight omega i)
      (Sum.elim u (fun k => v (earlierSlot i k)))
      (F.orderedSlotOrbit e omega hlayer B a p i) =
      a * F.realification.polynomialOrbitRealEval (fun _ : σ => 1) u p *
        realOrderedBasisProduct (e.baseChange ℝ) F.realification.lowerCentralSeries_eq_bot
          (fun j => if j.val < i.val then B * v j else 0) := by
  classical
  simp only [orderedSlotOrbit, map_mul, polynomialOrbitRealEval_constant,
    map_list_prod, List.map_map, Function.comp_def, orderedSlotFactor_realEval]
  rw [F.realification.polynomialOrbitSubstitute_realEval]
  simp only [MvPolynomial.aeval_X, Sum.elim_inl]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (v : σ → ℕ) (P : ι → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE v (ω i))

include hlayers hP

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))

theorem orderedSlotOrbit_coordinate (he : IsCentralLieBasis e) (B : ℝ)
    (a : F.realification.Group) (p : F.realification.PolynomialOrbit (fun _ : σ => 1))
    (i : Fin d) (u : σ → ℝ) (v : Fin d → ℝ) :
    MvPolynomial.eval (Sum.elim u (fun k => v (earlierSlot i k)))
      (coordinate ((e.baseChange ℝ).coord i).toAddMonoidHom
        (F.orderedSlotOrbit e omega hlayer B a p i).log) =
      (e.baseChange ℝ).repr
        ((a * F.realification.polynomialOrbitRealEval (fun _ : σ => 1) u p) *
          realOrderedBasisPrefixProduct (e.baseChange ℝ)
            F.realification.lowerCentralSeries_eq_bot i.val (fun j => B * v j)).coord i := by
  rw [← coordinate_eval₂]
  change (e.baseChange ℝ).repr
    (F.realification.polynomialOrbitRealEval _ _
      (F.orderedSlotOrbit e omega hlayer B a p i)).coord i = _
  rw [F.orderedSlotOrbit_realEval,
    he.real_baseChange.mul_realOrderedBasisProduct_coordinate,
    if_neg (lt_irrefl i.val), add_zero]
  have hp : realOrderedBasisPrefixProduct (e.baseChange ℝ)
      F.realification.lowerCentralSeries_eq_bot i.val
      (fun j => if j.val < i.val then B * v j else 0) =
      realOrderedBasisPrefixProduct (e.baseChange ℝ)
        F.realification.lowerCentralSeries_eq_bot i.val (fun j => B * v j) := by
    apply realOrderedBasisPrefixProduct_congr
    intro j hj
    exact if_pos hj
  rw [hp]

theorem orderedPolynomialSlots_slots (he : IsCentralLieBasis e) (B : ℝ)
    (a : F.realification.Group) (p : F.realification.PolynomialOrbit (fun _ : σ => 1))
    (u : σ → ℝ) :
    (F.orderedPolynomialSlots e omega hlayer B a p).slots u =
      realOrderedSlots (e.baseChange ℝ) F.realification.lowerCentralSeries_eq_bot B
        (a * F.realification.polynomialOrbitRealEval (fun _ : σ => 1) u p) := by
  apply TriangularSlots.ext
  intro v i
  change MvPolynomial.aeval (Sum.elim u (fun k => v (earlierSlot i k)))
    (MvPolynomial.C (-1 / B) * coordinate ((e.baseChange ℝ).coord i).toAddMonoidHom
      (F.orderedSlotOrbit e omega hlayer B a p i).log) = _
  rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_eq_eval,
    F.orderedSlotOrbit_coordinate e omega hlayer he]
  dsimp only [realOrderedSlots]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, div_eq_mul_inv]
  ring

theorem orderedPolynomialPatch_value (he : IsCentralLieBasis e)
    (hpos : ∀ i, 1 ≤ omega i) (hmax : ∀ i, omega i ≤ s) (hmono : Monotone omega)
    (B : ℝ) (a : F.realification.Group)
    (p : F.realification.PolynomialOrbit (fun _ : σ => 1)) (Phi : PatchKernel d)
    (u : σ → ℝ) :
    (F.orderedPolynomialPatch e omega hlayer hpos hmax hmono B a p Phi).value u =
      (realOrderedSlots (e.baseChange ℝ) F.realification.lowerCentralSeries_eq_bot B
        (a * F.realification.polynomialOrbitRealEval (fun _ : σ => 1) u p)).patchValue Phi := by
  change ((F.orderedPolynomialSlots e omega hlayer B a p).slots u).patchValue Phi = _
  rw [F.orderedPolynomialSlots_slots e omega hlayer he]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))
  (Λ : Subgroup F.Group) [MetricSpace (F.realification.Group ⧸ Λ.map realificationHom)]

theorem orderedPolynomialPatch_chart_value (he : IsCentralLieBasis e)
    (hpos : ∀ i, 1 ≤ omega i) (hmax : ∀ i, omega i ≤ s) (hmono : Monotone omega)
    (B : ℕ) (hB : 0 < B) (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B)
    (z : F.realification.Group) (p : F.realification.PolynomialOrbit (fun _ : σ => 1))
    (phi : OpenPartialHomeomorph (Fin d → ℝ) (F.realification.Group ⧸ Λ.map realificationHom))
    (hphi : ∀ v, phi v = QuotientGroup.mk
      (z * (⟨(e.baseChange ℝ).equivFun.symm v⟩ : F.realification.Group)))
    (f : (F.realification.Group ⧸ Λ.map realificationHom) → ℝ)
    (hf : Function.support f ⊆ phi.target) (Phi : PatchKernel d)
    (hPhi : ∀ v, Phi.value v = chartCoordinateKernel phi f ((B : ℝ) • v)) (u : σ → ℝ) :
    (F.orderedPolynomialPatch e omega hlayer hpos hmax hmono (B : ℝ) z⁻¹ p Phi).value u =
      f (QuotientGroup.mk (F.realification.polynomialOrbitRealEval (fun _ : σ => 1) u p)) := by
  rw [F.orderedPolynomialPatch_value e omega hlayer he]
  exact he.realOrderedSlots_patchValue F.lowerCentralSeries_eq_bot Λ B hB hgrid z
    (F.realification.polynomialOrbitRealEval (fun _ : σ => 1) u p) phi hphi f hf Phi hPhi

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (v : σ → ℕ) (P : ι → MvPolynomial σ ℝ)

variable (hP : ∀ i, P i ∈ weightedSupportLE v (ω i))

end NilpotentLieFiltration

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem aeval_eq_of_weightedSupport {σ R : Type*} [CommRing R]
    {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (x y : σ → R)
    (hxy : ∀ i, w i ≤ d → x i = y i) : aeval x p = aeval y p := by
  classical
  rw [← p.support_sum_monomial_coeff]
  simp only [map_sum, aeval_monomial]
  apply Finset.sum_congr rfl
  intro α hα
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun z => z ^ α i)
    (hxy i ((Finsupp.le_weight_of_ne_zero' w (Finsupp.mem_support_iff.mp hi)).trans (hp hα)))

namespace WeightedParameterSlots

variable {σ : Type*} {p : σ → ℕ} {d : ℕ} {w : Fin d → ℕ}

end WeightedParameterSlots

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

end WeightedParameterPatch

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace SlotInterleaving

theorem sorted_left_lt_right {D E : ℕ} (w : Fin D → ℕ) (v : Fin E → ℕ)
    (hw : Monotone w) (hv : Monotone v) (i : Fin D) (j : Fin E) (h : w i ≤ v j) :
    (sorted w v hw hv).left i < (sorted w v hw hv).right j := by
  apply stable_sort_symm_lt (Fin.append w v)
  · simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  · simpa only [Fin.append_left, Fin.append_right] using h

end SlotInterleaving

namespace WeightedParameterSlots

variable {σ : Type*} {D E : ℕ} {w : Fin D → ℕ} {v : Fin E → ℕ}

theorem insertCenter_eval
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (hbefore : ∀ j i, w j ≤ v i → I.left j < I.right i)
    (i : Fin E) (t : σ → ℝ) (x : Fin (D + E) → ℝ) :
    aeval (Sum.elim t (fun j => x (earlierSlot (I.right i) j)))
        (B.insertCenter I (I.right i) i) =
      (B.slots (Sum.elim t (fun j => x (I.left j)))).center (fun j => x (I.right j)) i := by
  simp only [insertCenter, MvPolynomial.comp_aeval_apply, slots]
  apply aeval_eq_of_weightedSupport (B.degree i)
  intro a ha
  rcases a with (a | j) | j
  · simp [insertSubstitution]
  · have h : (I.left j).val < (I.right i).val := hbefore j i ha
    simp only [insertSubstitution, Sum.elim_inl, Sum.elim_inr, dif_pos h, aeval_X]
    rfl
  · have h : (I.right (earlierSlot i j)).val < (I.right i).val :=
      I.right_strictMono j.isLt
    simp only [insertSubstitution, Sum.elim_inr, PolynomialSlots.placementSubstitution,
      dif_pos h, aeval_X]
    rfl

end WeightedParameterSlots

namespace PolynomialSlots

variable {σ : Type*} {D E : ℕ} {w : Fin D → ℕ} {v : Fin E → ℕ}

theorem insertLifts_center_left (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (t : σ → ℝ) (x : Fin (D + E) → ℝ) (i : Fin D) :
    ((A.insertLifts B I).slots t).center x (I.left i) =
      (A.slots t).center (fun j => x (I.left j)) i := by
  change aeval _ (Fin.addCases _ _ (I.perm (I.left i))) = _
  rw [show I.perm (I.left i) = i.castAdd E from I.perm.apply_symm_apply _, Fin.addCases_left]
  exact A.placeCenter_eval I.left I.left_strictMono i t x

theorem insertLifts_center_right (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (hbefore : ∀ j i, w j ≤ v i → I.left j < I.right i)
    (t : σ → ℝ) (x : Fin (D + E) → ℝ) (i : Fin E) :
    ((A.insertLifts B I).slots t).center x (I.right i) =
      (B.slots (Sum.elim t (fun j => x (I.left j)))).center (fun j => x (I.right j)) i := by
  change aeval _ (Fin.addCases _ _ (I.perm (I.right i))) = _
  rw [show I.perm (I.right i) = i.natAdd D from I.perm.apply_symm_apply _, Fin.addCases_right]
  exact B.insertCenter_eval I hbefore i t x

theorem insertLifts_residual_left (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (t : σ → ℝ) (z : Fin (D + E) → ℤ) (i : Fin D) :
    ((A.insertLifts B I).slots t).residual z (I.left i) =
      (A.slots t).residual (fun j => z (I.left j)) i := by
  simp only [TriangularSlots.residual, insertLifts_center_left]

theorem insertLifts_residual_right (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (hbefore : ∀ j i, w j ≤ v i → I.left j < I.right i)
    (t : σ → ℝ) (z : Fin (D + E) → ℤ) (i : Fin E) :
    ((A.insertLifts B I).slots t).residual z (I.right i) =
      (B.slots (Sum.elim t (fun j => (z (I.left j) : ℝ)))).residual
        (fun j => z (I.right j)) i := by
  simp only [TriangularSlots.residual, insertLifts_center_right A B I hbefore]

end PolynomialSlots
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterSlots

variable {σ τ : Type*} {p : σ → ℕ} {q : τ → ℕ} {d : ℕ} {w : Fin d → ℕ}

theorem reparam_slots (A : WeightedParameterSlots σ p d w) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) (t : τ → ℝ) :
    (A.reparam f hf).slots t = A.slots (fun a => aeval t (f a)) := by
  apply TriangularSlots.ext
  intro x i
  simp only [slots, reparam, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun g : σ ⊕ Fin i.val → ℝ => aeval g (A.center i))
  funext a
  cases a with
  | inl a =>
    simp only [parameterSubstitution, Sum.elim_inl, MvPolynomial.comp_aeval_apply, aeval_X]
  | inr j => simp [parameterSubstitution]

end WeightedParameterSlots

namespace WeightedParameterPatch

variable {σ τ : Type*} {p : σ → ℕ} {q : τ → ℕ} {s d : ℕ}

theorem reparam_value (A : WeightedParameterPatch σ p s d) (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE q (p a)) (t : τ → ℝ) :
    (A.reparam f hf).value t = A.value (fun a => aeval t (f a)) := by
  change ((A.form.reparam f hf).slots t).patchValue A.kernel = _
  rw [WeightedParameterSlots.reparam_slots]
  rfl

end WeightedParameterPatch
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CentralAdaptedRebase
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem NilpotentLieFiltration.adapted_basis_weight_bounds
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ w i})) (i : Fin d) :
    1 ≤ w i ∧ w i ≤ s := by
  constructor
  · have h : b i ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
    rw [hlayers] at h
    exact b.self_mem_span_image.mp h
  · by_contra h
    have hi : s + 1 ≤ w i := by omega
    have hmem : b i ∈ F.layer (s + 1) := by
      rw [hlayers]
      exact b.self_mem_span_image.mpr hi
    rw [F.terminal, Submodule.mem_bot] at hmem
    exact b.ne_zero i hmem

namespace RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

theorem exists_central_adapted_model_data (D : RationalFilteredNilmanifold L s d)
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ F : D.AdaptedModelData, Monotone F.weight ∧ IsCentralLieBasis F.basis ∧
      (∀ i, 1 ≤ F.weight i ∧ F.weight i ≤ s) ∧
      F.model.GeometryComplexityLE ((p + 3) ^ 11) ∧
      ∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ p + 1 := by
  obtain ⟨b, w, N, hw, hc, hlayers, hb, _, hbracket, hN, hNp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let F : D.AdaptedModelData := ⟨b, w, hlayers, N, hN, hin, hout⟩
  have hbase : 1 ≤ p + 3 := by linarith
  have hpq : p ≤ (p + 3) ^ 11 := by
    calc
      p ≤ p + 3 := by linarith
      _ ≤ (p + 3) ^ 11 := by
        simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 11)
  have hdim : (finrank ℚ L : ℝ) ≤ (p + 3) ^ 11 := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hD.1.trans hpq
  refine ⟨F, hw, hc, D.filtration.adapted_basis_weight_bounds b w hlayers, ?_, hb⟩
  exact D.filtration.ofAdaptedBasis_geometry b w hlayers D.lattice N hN hin hout
    (by positivity) hdim
    (hNp.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by decide : 9 ≤ 11)))) hbracket

theorem exists_controlled_central_rebase :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∃ (F : D.AdaptedModelData) (H : ℕ)
        (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H),
        Monotone F.weight ∧ IsCentralLieBasis F.basis ∧
        (∀ i, 1 ≤ F.weight i ∧ F.weight i ≤ s) ∧
        p ≤ (p + 2) ^ C ∧ F.model.GeometryComplexityLE ((p + 2) ^ C) ∧
        ∀ {σ : Type*} {w : σ → ℕ} (T : D.Niltest w), T.ComplexityLE p →
          (F.rebaseNiltest H hH T).ComplexityLE ((p + 2) ^ C) := by
  let R : Polynomial ℕ := (Polynomial.X + 3) ^ 11 + Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget (R + (R + 2) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro L _ _ s d _ _ _ _ D p hp hD
  obtain ⟨F, hw, hc, hweights, hF, hb⟩ := D.exists_central_adapted_model_data hp hD
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH (i j) : RationalHeightLE (D.basis.repr (F.basis i) j) H :=
    rationalHeightLE_ceil_exp (hb i j)
  let r := (p + 3) ^ 11 + p + 2
  have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hfr : (p + 3) ^ 11 ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp.trans hpr
  have hHbound : (H : ℝ) ≤ Real.exp r :=
    (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
      (Real.exp_le_exp.mpr (by dsimp [r]; linarith))
  have hbud : r + (r + 2) ^ 2 ≤ (p + 2) ^ C := by
    simpa [R, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + 2) ^ C := (le_add_of_nonneg_right (sq_nonneg _)).trans hbud
  have hgeom : F.model.GeometryComplexityLE r := hF.mono F.model hfr
  refine ⟨F, H, hH, hw, hc, hweights, hpr.trans hrC, hgeom.mono F.model hrC, ?_⟩
  intro σ w T hT
  exact (F.rebaseNiltest_complexity H hH T hr (hT.mono hpr) hgeom hHbound).mono hbud

end RationalFilteredNilmanifold
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTIntegerRepresentative
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open _root_.MvPolynomial

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

theorem crtIntegerRepresentative_cast (u : J → ℤ) :
    (crtIntegerRepresentative N hN u : ZMod (∏ j, N j)) =
      (ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j))) := by
  let E := ZMod.prodEquivPi N hN
  have hcoeff (j : J) : (crtIntegerCoefficient N hN j : ZMod (∏ j, N j)) =
      E.symm (Pi.single j (1 : ZMod (N j))) := by
    simp only [crtIntegerCoefficient, Int.cast_natCast, ZMod.natCast_zmod_val, E]
  calc
    _ = ∑ j, E.symm (Pi.single j (1 : ZMod (N j))) * (u j : ZMod (∏ j, N j)) := by
      simp only [crtIntegerRepresentative, Int.cast_sum, Int.cast_mul, hcoeff]
    _ = E.symm (∑ j, Pi.single j (1 : ZMod (N j)) * (u j : (j : J) → ZMod (N j))) := by
      simp only [map_sum, map_mul, map_intCast]
    _ = _ := by
      congr 1
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply]
      rw [Finset.sum_eq_single j]
      · simp only [Pi.single_eq_same, one_mul]
      · intro i _ hij
        rw [Pi.single_eq_of_ne hij.symm, zero_mul]
      · simp

omit [NeZero (∏ j, N j)] in
theorem crtRepresentativePolynomial_eval (u : J → ℤ) :
    aeval (fun j => (u j : ℝ)) (crtRepresentativePolynomial N hN) =
      (crtIntegerRepresentative N hN u : ℝ) / (∏ i, N i : ℕ) := by
  simp only [crtRepresentativePolynomial, map_sum, map_smul, aeval_X,
    smul_eq_mul, crtIntegerRepresentative, Int.cast_sum, Int.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRepresentativeFraction
namespace OAI

section

namespace Erdos3

theorem integer_fraction_eq_zmod_val {N : ℕ} [NeZero N] (a : ℤ) :
    Int.fract ((a : ℝ) / N) = (((a : ZMod N).val : ℝ) / N) := by
  rw [Int.fract_div_intCast_eq_div_intCast_mod]
  exact congrArg (fun z : ℤ => (z : ℝ) / N) (ZMod.val_intCast a).symm

theorem integer_sub_floor_eq_zmod_val {N : ℕ} [NeZero N] (a : ℤ) :
    a - (N : ℤ) * ⌊(a : ℝ) / N⌋ = ((a : ZMod N).val : ℤ) := by
  rw [Int.floor_div_natCast, Int.floor_intCast, ZMod.val_intCast]
  have h := Int.emod_add_mul_ediv a (N : ℤ)
  omega

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RepresentativeWindowTransport
namespace OAI

section

namespace Erdos3.RepresentativeWindow

open _root_.MvPolynomial
open scoped BigOperators

theorem patch_weighted_value {σ : Type*} {N : ℕ} [NeZero N]
    (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial σ ℝ) (hP : P ∈ weightedSupportLE (fun _ => 1) 1)
    (t : σ → ℝ) (a : ℤ) (he : aeval t P = (a : ℝ) / N) (F : ℤ → ℝ) :
    (∑' b : Fin 1 → ℤ, (w.patch s hs P hP).kernel.value
      (((w.patch s hs P hP).form.slots t).residual b) * F (a - (N : ℤ) * b 0)) =
      w.value (((a : ZMod N).val : ℝ) / N) * F ((a : ZMod N).val) := by
  have hterm (b : Fin 1 → ℤ) :
      (w.patch s hs P hP).kernel.value (((w.patch s hs P hP).form.slots t).residual b) *
        F (a - (N : ℤ) * b 0) =
      (w.patch s hs P hP).kernel.value (((w.patch s hs P hP).form.slots t).residual b) *
        F ((a : ZMod N).val) := by
    by_cases hb : (w.patch s hs P hP).kernel.value
        (((w.patch s hs P hP).form.slots t).residual b) = 0
    · simp only [hb, zero_mul]
    · rw [w.patch_contributing_lift s hs P hP t b hb, he, integer_sub_floor_eq_zmod_val]
  simp_rw [hterm]
  rw [tsum_mul_right]
  change (w.patch s hs P hP).value t * F ((a : ZMod N).val) = _
  rw [w.patch_value s hs P hP t, he, integer_fraction_eq_zmod_val]

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

theorem crtPatch_weighted_value (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s)
    (u : J → ℤ) (F : ℤ → ℝ) :
    (∑' b : Fin 1 → ℤ, (w.crtPatch N hN s hs).kernel.value
      (((w.crtPatch N hN s hs).form.slots (fun j => (u j : ℝ))).residual b) *
        F (crtIntegerRepresentative N hN u - (∏ j, N j : ℕ) * b 0)) =
      w.value ((((ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j)))).val : ℝ) /
        (∏ j, N j : ℕ)) *
      F (((ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j)))).val) := by
  have h := w.patch_weighted_value s hs (crtRepresentativePolynomial N hN)
    (crtRepresentativePolynomial_degree N hN) (fun j => (u j : ℝ))
    (crtIntegerRepresentative N hN u) (crtRepresentativePolynomial_eval N hN u) F
  simpa only [crtIntegerRepresentative_cast, crtPatch] using h

end Erdos3.RepresentativeWindow

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialPatchComposition
namespace OAI

section

namespace Erdos3.PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

theorem liftInterleaving_before (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E)
    (j : Fin D) (i : Fin E) (h : A.weight j ≤ B.weight i) :
    (A.liftInterleaving B).left j < (A.liftInterleaving B).right i :=
  SlotInterleaving.sorted_left_lt_right _ _ _ _ j i h

theorem insertLifts_term (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E)
    (t : σ → ℝ) (z : Fin (D + E) → ℤ) :
    (A.insertLifts B).kernel.value (((A.insertLifts B).form.slots t).residual z) =
      A.kernel.value ((A.form.slots t).residual (fun j => z ((A.liftInterleaving B).left j))) *
      B.kernel.value ((B.form.slots (Sum.elim t
        (fun j => (z ((A.liftInterleaving B).left j) : ℝ)))).residual
          (fun j => z ((A.liftInterleaving B).right j))) := by
  let I := A.liftInterleaving B
  change A.kernel.value (fun i => ((A.form.insertLifts B.form I).slots t).residual z (I.left i)) *
    B.kernel.value (fun i => ((A.form.insertLifts B.form I).slots t).residual z (I.right i)) = _
  simp only [PolynomialSlots.insertLifts_residual_left,
    PolynomialSlots.insertLifts_residual_right A.form B.form I (A.liftInterleaving_before B)]
  rfl

theorem insertLifts_value (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E)
    (t : σ → ℝ) :
    (A.insertLifts B).value t = ∑' b : Fin D → ℤ,
      A.kernel.value ((A.form.slots t).residual b) *
        B.value (Sum.elim t (fun j => (b j : ℝ))) :=
  (A.form.slots t).factorized_patchValue
    (fun b => B.form.slots (Sum.elim t (fun j => (b j : ℝ))))
    ((A.insertLifts B).form.slots t) A.kernel B.kernel (A.insertLifts B).kernel
    (A.liftInterleaving B) (A.insertLifts_term B t)

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

omit [NeZero (∏ j, N j)] in
theorem crtLiftPolynomial_eval (u : J → ℤ) (b : Fin 1 → ℤ) :
    aeval (Sum.elim (fun j => (u j : ℝ)) (fun i => (b i : ℝ))) (crtLiftPolynomial N hN) =
      ((crtIntegerRepresentative N hN u - (∏ j, N j : ℕ) * b 0 : ℤ) : ℝ) := by
  simp only [crtLiftPolynomial, map_sub, map_sum, map_smul, aeval_X,
    Sum.elim_inl, Sum.elim_inr, smul_eq_mul, crtIntegerRepresentative,
    Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

namespace RepresentativeWindow

variable (w : RepresentativeWindow) (s : ℕ) (hs : 1 ≤ s) {d : ℕ}

theorem composeCRTPatch_value (P : PolynomialPatch Unit s d) (u : J → ℤ) :
    (w.composeCRTPatch N hN s hs P).value (fun j => (u j : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm (fun j => (u j : ZMod (N j)))).val : ℝ) /
        (∏ j, N j : ℕ)) *
      P.value (fun _ => (((ZMod.prodEquivPi N hN).symm
        (fun j => (u j : ZMod (N j)))).val : ℝ)) := by
  rw [composeCRTPatch, PolynomialPatch.insertLifts_value]
  simpa only [WeightedParameterPatch.reparam_value, PolynomialPatch.weightedParameters_value,
    crtLiftPolynomial_eval, Int.cast_natCast] using
    w.crtPatch_weighted_value N hN s hs u (fun n => P.value (fun _ => (n : ℝ)))

theorem composeCRTPatch_value_residues [∀ j, NeZero (N j)]
    (P : PolynomialPatch Unit s d) (u : (j : J) → ZMod (N j)) :
    (w.composeCRTPatch N hN s hs P).value (fun j => ((u j).val : ℝ)) =
      w.value ((((ZMod.prodEquivPi N hN).symm u).val : ℝ) / (∏ j, N j : ℕ)) *
      P.value (fun _ => (((ZMod.prodEquivPi N hN).symm u).val : ℝ)) := by
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
    w.composeCRTPatch_value N hN s hs P (fun j => ((u j).val : ℤ))

omit [NeZero (∏ j, N j)] in

theorem composeCRTPatch_cost (P : PolynomialPatch Unit s d) {p q : ℝ}
    (hP : (d : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ p)
    (hw : Real.log (2 + (w.lip : ℝ)) ≤ q) :
    ((1 + d : ℕ) : ℝ) +
      Real.log (2 + ((w.composeCRTPatch N hN s hs P).kernel.lip : ℝ)) ≤ p + q + 1 := by
  have hp0 := P.kernel.lip.coe_nonneg
  have hw0 := w.lip.coe_nonneg
  have hlog : Real.log (2 + ((w.lip : ℝ) + P.kernel.lip)) ≤
      Real.log (2 + (w.lip : ℝ)) + Real.log (2 + (P.kernel.lip : ℝ)) := by
    calc
      _ ≤ Real.log ((2 + (w.lip : ℝ)) * (2 + (P.kernel.lip : ℝ))) := by
        apply Real.log_le_log (by positivity)
        nlinarith [mul_nonneg hw0 hp0]
      _ = _ := Real.log_mul (by positivity) (by positivity)
  rw [composeCRTPatch_lip, NNReal.coe_add, Nat.cast_add, Nat.cast_one]
  linarith

end RepresentativeWindow
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IntegralCentralNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

theorem exists_integral_central_niltest_lift (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w) {p : ℝ},
      0 ≤ p → T.ComplexityLE p → T.UnitIntervalValued →
      ∃ (E : RationalFilteredNilmanifold L s (finrank ℚ L)) (omega : Fin (finrank ℚ L) → ℕ),
        E.filtration = D.filtration ∧ Monotone omega ∧ IsCentralLieBasis E.basis ∧
        (∀ i, 1 ≤ omega i ∧ omega i ≤ s) ∧
        (∀ k, E.filtration.layer k = Submodule.span ℚ (E.basis '' {i | k ≤ omega i})) ∧
        4 ≤ E.grid ∧ E.lattice ≤ D.lattice ∧ (E.lattice.subgroupOf D.lattice).FiniteIndex ∧
        bchSubgroupCoordinates E.basis E.lattice = scaledIntegerGrid E.grid ∧
        (∀ g ∈ E.lattice, ∃! z : Fin (finrank ℚ L) → ℤ,
          integralOrderedBasisProduct E.basis E.filtration.lowerCentralSeries_eq_bot E.grid z = g) ∧
        ∃ U : E.Niltest w, U.UnitIntervalValued ∧ U.ComplexityLE ((p + 2) ^ C) ∧
          ∀ x : σ → ℤ, U.eval x = T.eval x := by
  obtain ⟨A, _, hrebase⟩ := exists_controlled_central_rebase
  obtain ⟨B, _, hcover⟩ := exists_controlled_integral_coordinates s
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ A + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ _ D w T p hp hT hpositive
  obtain ⟨F, H, hH, hmono, hcentral, hweights, hpA, hF, htests⟩ := hrebase D hp hT.1
  let U₀ := F.rebaseNiltest H hH T
  have hU₀ : U₀.ComplexityLE ((p + 2) ^ A) := htests T hT
  let q₀ : ℝ := (p + 2) ^ A
  let q : ℝ := q₀ + 4
  let Hc := ⌈Real.exp q₀⌉₊
  have hq₀ : 0 ≤ q₀ := by dsimp [q₀]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq₀q : q₀ ≤ q := by dsimp [q]; linarith
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hlp : ((4 * F.grid : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    calc
      _ ≤ 4 * Real.exp q₀ := mul_le_mul_of_nonneg_left hF.2.1 (by norm_num)
      _ ≤ Real.exp 4 * Real.exp q₀ := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = Real.exp q := by rw [← Real.exp_add]; congr 1; dsimp [q]; ring
  have hHcp : (Hc : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hq₀).trans (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  have hdivgrid : F.grid ∣ 4 * F.grid := dvd_mul_left _ _
  have hinner : scaledIntegerGrid (4 * F.grid) ⊆ bchSubgroupCoordinates F.basis D.lattice :=
    (scaledIntegerGrid_subset_of_dvd hdivgrid).trans F.inner
  have houter : bchSubgroupCoordinates F.basis D.lattice ⊆ denominatorGrid (4 * F.grid) :=
    F.outer.trans (denominatorGrid_subset_of_dvd hdivgrid)
  obtain ⟨m, Λ, hm, hdiv, hmb, hΛ, hfinite, hcoords, hordered⟩ :=
    hcover F.basis hcentral D.filtration.lowerCentralSeries_eq_bot D.lattice
      (4 * F.grid) Hc q (Nat.mul_pos (by decide) F.grid_pos)
      (fun i j k => rationalHeightLE_ceil_exp (hF.2.2.1 i j k)) hinner houter hq
      (hF.1.trans hq₀q) hHcp hlp
  have hm4 : 4 ≤ m := by
    have hn := F.grid_pos
    have hle : 4 * F.grid ≤ m := Nat.le_of_dvd hm hdiv
    omega
  have hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates F.model.basis Λ := hcoords.symm.le
  have hout : bchSubgroupCoordinates F.model.basis Λ ⊆ denominatorGrid m := by
    change bchSubgroupCoordinates F.basis Λ ⊆ denominatorGrid m
    rw [hcoords]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid m m hx
  let E := F.model.withLattice Λ m hm hin hout
  let U : E.Niltest w := U₀.onSublattice Λ m hm hin hout hΛ
  have hcost : q + (q + B) ^ B ≤ (p + 2) ^ C := by
    simpa [Q, q, q₀, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hBC : (q + B) ^ B ≤ (p + 2) ^ C := (le_add_of_nonneg_left hq).trans hcost
  have hE : E.GeometryComplexityLE ((p + 2) ^ C) :=
    F.model.withLattice_geometry Λ m hm hin hout hF (hq₀q.trans hqC)
      (hmb.trans (Real.exp_le_exp.mpr hBC))
  refine ⟨E, F.weight, rfl, hmono, hcentral, hweights, F.layers, hm4, hΛ, hfinite,
    hcoords, hordered, U, ?_, ?_, ?_⟩
  · exact U₀.onSublattice_unit_interval Λ m hm hin hout hΛ hpositive
  · exact U₀.onSublattice_complexity Λ m hm hin hout hΛ (hU₀.mono (hq₀q.trans hqC)) hE
  · intro x
    rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.IntegralScoredKernel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal BigOperators

theorem exists_integral_scored_chart (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ X L : Type*} [Fintype X]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      (a : X → ℝ) (u : X → σ → ℤ) {p : ℝ},
      0 ≤ p → T.ComplexityLE p → T.UnitIntervalValued →
      Real.exp (-p) ≤ (𝔼 x, a x * (T.eval (u x)).re) →
      ∃ (E : RationalFilteredNilmanifold L s (finrank ℚ L)) (omega : Fin (finrank ℚ L) → ℕ),
        E.filtration = D.filtration ∧ Monotone omega ∧ IsCentralLieBasis E.basis ∧
        (∀ i, 1 ≤ omega i ∧ omega i ≤ s) ∧
        (∀ k, E.filtration.layer k = Submodule.span ℚ (E.basis '' {i | k ≤ omega i})) ∧
        4 ≤ E.grid ∧ E.lattice ≤ D.lattice ∧ (E.lattice.subgroupOf D.lattice).FiniteIndex ∧
        bchSubgroupCoordinates E.basis E.lattice = scaledIntegerGrid E.grid ∧
        (∀ g ∈ E.lattice, ∃! z : Fin (finrank ℚ L) → ℤ,
          integralOrderedBasisProduct E.basis E.filtration.lowerCentralSeries_eq_bot E.grid z = g) ∧
        letI := E.metricSpace
        ∃ (r : ℝ≥0) (z : E.RealGroup)
          (phi : OpenPartialHomeomorph (Fin (finrank ℚ L) → ℝ) E.Space),
          0 < r ∧ r ≤ 1 ∧ 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
          (∀ i, |(E.basis.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
          (∀ v, phi v = QuotientGroup.mk
            (z * (NilpotentLieBCHGroup.basisHomeomorph (E.basis.baseChange ℝ)).symm v)) ∧
          phi.source = {v | ∀ i, |v i| < (r : ℝ)} ∧
          ∃ V : E.Niltest w, V.UnitIntervalValued ∧ V.ComplexityLE ((p + 2) ^ C) ∧
            HasCompactSupport V.observable ∧ tsupport V.observable ⊆ phi.target ∧
            (Real.exp (-((p + 2) ^ C)) ≤ 𝔼 x, a x * (V.eval (u x)).re) ∧
            tsupport V.observable ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4) ∧
            ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
              LipschitzOnWith K phi phi.source := by
  obtain ⟨A, hA, hlift⟩ := exists_integral_central_niltest_lift s
  obtain ⟨B, hB, hchart⟩ := exists_scored_native_chart s
  let C := (A + 2) * B
  refine ⟨C, by dsimp [C]; nlinarith, ?_⟩
  intro σ X L _ _ _ d _ _ _ _ D w T a u p hp hT hpositive hscore
  obtain ⟨E, omega, hEF, hmono, hcentral, hweights, hlayers, hgrid, hsub, hfinite,
    hcoords, hordered, U, hUpositive, hU, heval⟩ := hlift D T hp hT hpositive
  let := E.metricSpace
  let q : ℝ := (p + 2) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by omega)
  have hscoreU : Real.exp (-q) ≤ 𝔼 x, a x * (U.eval (u x)).re := by
    simpa only [heval] using (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hscore
  obtain ⟨r, z, phi, hr, hr1, hri, hz, hphi, hsource, V, _, hVpositive, hV,
    hcompact, hsupport, hscoreV, hinner, K, hK, hForward⟩ := hchart E U a u hq hU hUpositive hscoreU
  have hb : (q + 2) ^ B ≤ (p + 2) ^ C := shifted_power_budget_le hp A B
  have hexp := Real.exp_le_exp.mpr hb
  exact ⟨E, omega, hEF, hmono, hcentral, hweights, hlayers, hgrid, hsub, hfinite,
    hcoords, hordered, r, z, phi, hr, hr1, hri.trans hexp,
    fun i => (hz i).trans hexp, hphi, hsource, V, hVpositive, hV.mono hb,
    hcompact, hsupport, (Real.exp_le_exp.mpr (neg_le_neg hb)).trans hscoreV,
    hinner, K, hK.trans hexp, hForward⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal BigOperators

theorem exists_integral_scored_kernel (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ X L : Type*} [Fintype X]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      (a : X → ℝ) (u : X → σ → ℤ) {p : ℝ},
      0 ≤ p → T.ComplexityLE p → T.UnitIntervalValued →
      Real.exp (-p) ≤ (𝔼 x, a x * (T.eval (u x)).re) →
      ∃ (E : RationalFilteredNilmanifold L s (finrank ℚ L)) (omega : Fin (finrank ℚ L) → ℕ),
        E.filtration = D.filtration ∧ Monotone omega ∧ IsCentralLieBasis E.basis ∧
        (∀ i, 1 ≤ omega i ∧ omega i ≤ s) ∧
        (∀ k, E.filtration.layer k = Submodule.span ℚ (E.basis '' {i | k ≤ omega i})) ∧
        4 ≤ E.grid ∧ E.lattice ≤ D.lattice ∧ (E.lattice.subgroupOf D.lattice).FiniteIndex ∧
        bchSubgroupCoordinates E.basis E.lattice = scaledIntegerGrid E.grid ∧
        (∀ g ∈ E.lattice, ∃! z : Fin (finrank ℚ L) → ℤ,
          integralOrderedBasisProduct E.basis E.filtration.lowerCentralSeries_eq_bot E.grid z = g) ∧
        letI := E.metricSpace
        ∃ (r : ℝ≥0) (z : E.RealGroup)
          (phi : OpenPartialHomeomorph (Fin (finrank ℚ L) → ℝ) E.Space),
          0 < r ∧ r ≤ 1 ∧ 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
          (∀ i, |(E.basis.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
          (∀ v, phi v = QuotientGroup.mk
            (z * (NilpotentLieBCHGroup.basisHomeomorph (E.basis.baseChange ℝ)).symm v)) ∧
          phi.source = {v | ∀ i, |v i| < (r : ℝ)} ∧
          ∃ V : E.Niltest w, V.UnitIntervalValued ∧ V.ComplexityLE ((p + 2) ^ C) ∧
            (Real.exp (-((p + 2) ^ C)) ≤ 𝔼 x, a x * (V.eval (u x)).re) ∧
            tsupport V.observable ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4) ∧
            ∃ Phi : PatchKernel (finrank ℚ L),
              Real.log (2 + (Phi.lip : ℝ)) ≤ (p + 2) ^ C ∧
              (∀ v, Phi.value v = chartCoordinateKernel phi (fun x => (V.observable x).re)
                ((E.grid : ℝ) • v)) ∧
              ∀ x ∈ phi.target,
                Phi.value (fun i => phi.symm x i / E.grid) = (V.observable x).re := by
  obtain ⟨A, _, hchart⟩ := exists_integral_scored_chart s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (3 * (Polynomial.X + 2) ^ A + 6)
  refine ⟨C, hC, ?_⟩
  intro σ X L _ _ _ d _ _ _ _ D w T a u p hp hT hpositive hscore
  obtain ⟨E, omega, hEF, hmono, hcentral, hweights, hlayers, hgrid, hsub, hfinite,
    hcoords, hordered, r, z, phi, hr, hr1, hri, hz, hphi, hsource,
    V, hVpositive, hV, _, _, hscoreV, hinner, K, hK, hForward⟩ :=
    hchart D T a u hp hT hpositive hscore
  let := E.metricSpace
  let q : ℝ := (p + 2) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 3 * q + 6 ≤ (p + 2) ^ C := by
    simpa [q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := by linarith
  have hexp := Real.exp_le_exp.mpr hqC
  let Phi := V.chartKernel hVpositive phi K r hr hr1 hsource hinner hForward hgrid
  have hPhi : Real.log (2 + (Phi.lip : ℝ)) ≤ (p + 2) ^ C :=
    (V.chartKernel_log_bound hVpositive phi K r hr hr1 hsource hinner hForward hgrid
      hq hV hK hri).trans hb
  refine ⟨E, omega, hEF, hmono, hcentral, hweights, hlayers, hgrid, hsub, hfinite,
    hcoords, hordered, r, z, phi, hr, hr1, hri.trans hexp, fun i => (hz i).trans hexp,
    hphi, hsource, V, hVpositive, hV.mono hqC,
    (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hscoreV, hinner, Phi, hPhi, ?_, ?_⟩
  · exact V.chartKernel_value hVpositive phi K r hr hr1 hsource hinner hForward hgrid
  · intro x hx
    exact V.chartKernel_recover hVpositive phi K r hr hr1 hsource hinner hForward hgrid hx

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScoredCyclicPolynomialPatch
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct BigOperators

theorem exists_scored_native_polynomial_patch (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ X L : Type*} [Fintype X]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (T : D.Niltest (fun _ : σ => 1))
      (a : X → ℝ) (u : X → σ → ℤ) {p : ℝ},
      0 ≤ p → T.ComplexityLE p → T.UnitIntervalValued →
      Real.exp (-p) ≤ (𝔼 x, a x * (T.eval (u x)).re) →
      ∃ P : PolynomialPatch σ s (finrank ℚ L),
        (finrank ℚ L : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
        Real.exp (-((p + 2) ^ C)) ≤
          (𝔼 x, a x * P.value (fun j => (u x j : ℝ))) := by
  obtain ⟨C, hC, hkernel⟩ := exists_integral_scored_kernel s
  refine ⟨C + 1, by omega, ?_⟩
  intro σ X L _ _ _ d _ _ _ _ D T a u p hp hT hpositive hscore
  obtain ⟨E, omega, _, hmono, hcentral, hweights, hlayers, hgrid, _, _, hcoords,
    _, r, z, phi, hr, _, _, _, hphi, hsource, V, _, hV, hscoreV, hinner,
    Phi, hPhiCost, hPhi, _⟩ := hkernel D T a u hp hT hpositive hscore
  let := E.metricSpace
  let P := E.filtration.orderedPolynomialPatch E.basis omega hlayers
    (fun i => (hweights i).1) (fun i => (hweights i).2) hmono (E.grid : ℝ) z⁻¹ V.orbit Phi
  have hsupport : Function.support (fun x => (V.observable x).re) ⊆ phi.target := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hinner (V.realObservable_tsupport (subset_closure hx))
    exact phi.map_source (closedBox_subset_chart_source phi hr hsource hv)
  have hvalue (v : σ → ℝ) : P.value v = (V.evalReal v).re := by
    let : MetricSpace (E.filtration.realification.Group ⧸
      E.lattice.map NilpotentLieBCHGroup.realificationHom) := E.metricSpace
    exact E.filtration.orderedPolynomialPatch_chart_value E.basis omega hlayers E.lattice
      hcentral (fun i => (hweights i).1) (fun i => (hweights i).2) hmono E.grid
      (by omega) hcoords z V.orbit phi hphi (fun x => (V.observable x).re) hsupport Phi hPhi v
  have heval (v : σ → ℤ) : P.value (fun j => (v j : ℝ)) = (V.eval v).re :=
    (hvalue _).trans (congrArg Complex.re (V.evalReal_integer v))
  have hpow : 0 ≤ (p + 2) ^ C := pow_nonneg (by linarith) C
  have hbudget : 2 * (p + 2) ^ C ≤ (p + 2) ^ (C + 1) := by
    rw [pow_succ]
    nlinarith
  refine ⟨P, ?_, ?_⟩
  · have hdim := hV.1.1
    change (finrank ℚ L : ℝ) ≤ (p + 2) ^ C at hdim
    change (finrank ℚ L : ℝ) + Real.log (2 + (Phi.lip : ℝ)) ≤ _
    linarith
  · have hmonoBudget : (p + 2) ^ C ≤ (p + 2) ^ (C + 1) := by linarith
    apply (Real.exp_le_exp.mpr (neg_le_neg hmonoBudget)).trans
    simpa only [heval] using hscoreV

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

theorem exists_scored_cyclic_patch (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {X : Type*} [Fintype X]
      (T : ZMod N → ℝ) (a : X → ℝ) (n : X → ZMod N) {p : ℝ},
      0 ≤ p → PositiveCyclicNiltest.{u} s N p T →
      Real.exp (-p) ≤ (𝔼 x, a x * T (n x)) →
      ∃ d : ℕ, ∃ P : PolynomialPatch Unit s d,
        (d : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
        Real.exp (-((p + 2) ^ C)) ≤ (𝔼 x, a x * P.value (fun _ => ((n x).val : ℝ))) := by
  obtain ⟨A, _, hconvert⟩ := RationalFilteredNilmanifold.exists_scored_native_polynomial_patch s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    ((Polynomial.X + (Polynomial.X + 2) ^ 2 + 5) ^ A)
  refine ⟨C, hC, ?_⟩
  intro N _ X _ T a n p hp hT hscore
  rcases hT with @⟨L, lie, alg, t, dim, top, add, smul, t2, D, ht, U, hU, hUc, hUeval⟩
  let V := U.raiseStep ht
  let r := raisedNiltestBudget p
  have hpR : p ≤ r := le_raisedNiltestBudget p
  have hr : 0 ≤ r := hp.trans hpR
  have heval (x : X) : (V.eval (fun _ : Unit => ((n x).val : ℤ))).re = T (n x) := by
    dsimp only [V]
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_eval]
    exact (hUeval (n x)).symm
  have hscoreV : Real.exp (-r) ≤ (𝔼 x, a x * (V.eval (fun _ : Unit => ((n x).val : ℤ))).re) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hpR)).trans
    simpa only [heval] using hscore
  obtain ⟨P, hcost, hscoreP⟩ := hconvert (D.raiseStep ht) V a
    (fun x _ => ((n x).val : ℤ)) hr (U.raiseStep_complexity ht hp hUc)
    (U.raiseStep_unit_interval ht hU) hscoreV
  have hb : (r + 2) ^ A ≤ (p + 2) ^ C := by
    have heq : r + 2 = p + (p + 2) ^ 2 + 5 := by
      dsimp only [r, raisedNiltestBudget]
      ring
    rw [heq]
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨_, P, hcost.trans hb, ?_⟩
  have hs := (Real.exp_le_exp.mpr (neg_le_neg hb)).trans hscoreP
  simpa only [Int.cast_natCast] using hs

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScoredCRTWindowPatch
namespace OAI

section

namespace Erdos3

open scoped BigOperators

universe u

theorem exists_scored_windowed_crt_patch_oai (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] [DecidableEq J]
      (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))
      (T : ZMod (∏ j, N j) → ℝ) (w : RepresentativeWindow)
      (a : ((j : J) → ZMod (N j)) → ℝ) {p : ℝ},
      0 ≤ p → PositiveCyclicNiltest.{u} s (∏ j, N j) p T →
      Real.log (2 + (w.lip : ℝ)) ≤ p →
      Real.exp (-p) ≤ (𝔼 x, (a x * T ((ZMod.prodEquivPi N hN).symm x)) *
        w.value ((((ZMod.prodEquivPi N hN).symm x).val : ℝ) / (∏ j, N j : ℕ))) →
      ∃ d : ℕ, ∃ P : PolynomialPatch J s d,
        (d : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
        Real.exp (-((p + 2) ^ C)) ≤ (𝔼 x, a x * P.value (fun j => ((x j).val : ℝ))) := by
  obtain ⟨A, _, hconvert⟩ := exists_scored_cyclic_patch.{u} s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    ((Polynomial.X + 2) ^ A + Polynomial.X + 1)
  refine ⟨C, hC, ?_⟩
  intro J _ _ N _ _ hN T w a p hp hT hw hscore
  let b := fun x : (j : J) → ZMod (N j) =>
    a x * w.value ((((ZMod.prodEquivPi N hN).symm x).val : ℝ) / (∏ j, N j : ℕ))
  have hscore' : Real.exp (-p) ≤ (𝔼 x, b x * T ((ZMod.prodEquivPi N hN).symm x)) := by
    have heq : (𝔼 x, b x * T ((ZMod.prodEquivPi N hN).symm x)) =
        (𝔼 x, (a x * T ((ZMod.prodEquivPi N hN).symm x)) *
          w.value ((((ZMod.prodEquivPi N hN).symm x).val : ℝ) / (∏ j, N j : ℕ))) := by
      apply Finset.expect_congr rfl
      intro x _
      dsimp only [b]
      ring
    rw [heq]
    exact hscore
  obtain ⟨d, Q, hQ, hscoreQ⟩ := hconvert T b (ZMod.prodEquivPi N hN).symm hp hT hscore'
  let P := w.composeCRTPatch N hN s hs Q
  have hcost : ((1 + d : ℕ) : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤
      (p + 2) ^ A + p + 1 := w.composeCRTPatch_cost N hN s hs Q hQ hw
  have hb : (p + 2) ^ A + p + 1 ≤ (p + 2) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hsame : (𝔼 x, a x * P.value (fun j => ((x j).val : ℝ))) =
      (𝔼 x, b x * Q.value (fun _ => (((ZMod.prodEquivPi N hN).symm x).val : ℝ))) := by
    apply Finset.expect_congr rfl
    intro x _
    rw [show P.value (fun j => ((x j).val : ℝ)) = _ from
      w.composeCRTPatch_value_residues N hN s hs Q x]
    dsimp only [b]
    ring
  refine ⟨1 + d, P, hcost.trans hb, ?_⟩
  rw [hsame]
  exact (Real.exp_le_exp.mpr (neg_le_neg (show (p + 2) ^ A ≤ (p + 2) ^ C by linarith))).trans hscoreQ

end Erdos3

end

end OAI

end

theorem solution.{u, u_1} : type_of% @OAI.Erdos3.exists_scored_windowed_crt_patch_oai.{u, u_1} := @OAI.Erdos3.exists_scored_windowed_crt_patch_oai.{u, u_1}
