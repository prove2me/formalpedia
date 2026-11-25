-- Prove2me | solution 1 for GlobalTheory.ChF.linDat_hodgeTate_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:03:31.257517+00:00
-- url     : https://prove2.me/submissions/7e75b744-24b9-416c-a77d-c01cc4c1f6ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LinearDataHodgeTateInclusion
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_ht_cp_surj
import Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_E
import Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_cp_ne
import Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_domain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
private lemma smul_mem_span_of_split {O κ : Type} [CommRing O] [Fintype κ] [DecidableEq κ] {g d r m : ℕ}
    (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (Ht : Matrix (Fin g) κ O)
    (s : Fin m → Fin d → O) (cp : O) (hex : SplitEx A B)
    (hB : ∀ i, ∃ k, s k = Bᵀ *ᵥ (fun l => Ht l i)) (hT : ∀ i, ∃ k, Aᵀ *ᵥ s k = Pi.single i 1)
    (hsurj : ∀ f : Fin g → O, ∃ t, Ht *ᵥ t = cp • f) (f : Fin d → O) :
    cp • f ∈ Submodule.span O (Set.range s) := by
  obtain ⟨-, A', B', -, -, h1⟩ := hex
  choose k hk using hT
  set u : Fin d → O := ∑ i, (Aᵀ *ᵥ f) i • s (k i) with hu
  have huS : u ∈ Submodule.span O (Set.range s) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k i, rfl⟩)
  have hAu : Aᵀ *ᵥ u = Aᵀ *ᵥ f := by
    rw [hu, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hk]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h0 : Aᵀ *ᵥ (f - u) = 0 := by rw [Matrix.mulVec_sub, hAu, sub_self]
  have h2 : A'ᵀ * Aᵀ + Bᵀ * B'ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.transpose_add, h1, Matrix.transpose_one]
  have h3 : f - u = Bᵀ *ᵥ (B'ᵀ *ᵥ (f - u)) := by
    have := congrArg (fun M => M *ᵥ (f - u)) h2
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, zero_add,
      Matrix.one_mulVec] at this
    exact this.symm
  obtain ⟨t, ht⟩ := hsurj (B'ᵀ *ᵥ (f - u))
  have h4 : cp • (f - u) = Bᵀ *ᵥ (Ht *ᵥ t) := by rw [ht, Matrix.mulVec_smul, ← h3]
  have h5 : Ht *ᵥ t = ∑ i, t i • (fun l => Ht l i) := by
    ext l
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have h6 : cp • (f - u) ∈ Submodule.span O (Set.range s) := by
    rw [h4, h5, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    obtain ⟨j, hj⟩ := hB i
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj⟩)
  have h7 : cp • f = cp • (f - u) + cp • u := by rw [← smul_add, sub_add_cancel]
  rw [h7]
  exact Submodule.add_mem _ h6 (Submodule.smul_mem _ _ huS)
end GlobalTheory.ChF
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ c : O, v (algebraMap O C c) ^ (p - 1) ≤ v (algebraMap O C (p : O)) → ∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range s) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hS g H d r m A B ρG N s hL c hc f
  have := htd_domain hS
  obtain ⟨hEt, hdiag, hdet⟩ := htd_E H
  have hsurj := ht_cp_surj H.Ht H.Bt _ cp hEt hdiag hdet (htd_cp_ne hS) H.form_eq_alt
  have hle : v (algebraMap O C c) ≤ v (algebraMap O C cp) := by
    rw [← hS.cp_val] at hc
    exact le_of_pow_le_pow_left₀ (by have := (Fact.out : p.Prime).two_le; omega) zero_le hc
  obtain ⟨e, rfl⟩ := hv.dvd_of_le hle
  rw [mul_comm, mul_smul]
  exact Submodule.smul_mem _ _
    (smul_mem_span_of_split A B H.Ht s cp hL.exact hL.fromB hL.fromT hsurj f)
end GlobalTheory.ChF
