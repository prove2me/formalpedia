-- Prove2me | solution 1 for GlobalTheory.topFormOrd_vw_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:41.597456+00:00
-- url     : https://prove2.me/submissions/d09bf2c7-e769-4004-8a7b-485b0333ec50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_formMap__Multi_014b852379ac
import Theorems.Thm_GlobalTheory_dlogWedge_empty
import Theorems.Thm_GlobalTheory_ordTop_vw_zero
import Theorems.Thm_GlobalTheory_fracKaehlerBasis_apply
import Theorems.Thm_GlobalTheory_topFormCoeff_topFormGen
import Theorems.Thm_GlobalTheory_topFormCoeff_smul_topFormGen
import Theorems.Thm_GlobalTheory_topFormOrd_vw_smul_topFormGen
import Theorems.Thm_GlobalTheory_topFormOrd_vw_eq
import Theorems.Thm_GlobalTheory_topFormOrd_vw_dWedge_nonneg
import Theorems.Thm_GlobalTheory_one_le_topFormOrd_vw_dWedge
import Theorems.Thm_GlobalTheory_neg_one_le_topFormOrd_vw_dlogWedge
import Theorems.Thm_GlobalTheory_topFormOrd_vw_dlogWedge_nonneg
import Theorems.Thm_GlobalTheory_exists_basis_kaehler_of_trdeg
import Theorems.Thm_GlobalTheory_trdeg_residueField_of_trdeg
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


attribute [local simp] GlobalTheory.formMap_ιMulti
attribute [local simp] GlobalTheory.dlogWedge_empty
attribute [local simp] GlobalTheory.ordTop_vw_zero
attribute [local simp] GlobalTheory.fracKaehlerBasis_apply
attribute [local simp] GlobalTheory.topFormCoeff_topFormGen

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
namespace GlobalTheory
theorem _root_.solution (K V F : Type*) [Field K] [CharZero K] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra K V] [Algebra.EssFiniteType K V]
    [Algebra.FormallySmooth K V] [Field F] [Algebra V F] [IsFractionRing V F] [Algebra K F]
    [IsScalarTower K V F] {n : ℕ} (hn : Algebra.trdeg K F = n) :
    Algebra.trdeg K (ResidueField V) = (n - 1 : ℕ) ∧
    (∀ t : V, Irreducible t → ∃ (h : 0 < n) (z : Fin n → V) (b : Basis (Fin n) V Ω[V⁄K]),
      z ⟨0, h⟩ = t ∧ ∀ k, b k = D K V (z k)) ∧
    Nonempty (Basis (Fin n) V Ω[V⁄K]) ∧
    ∀ b : Basis (Fin n) V Ω[V⁄K],
      (∀ (b' : Basis (Fin n) V Ω[V⁄K]) (ω : ⋀[F]^n Ω[F⁄K]),
        topFormOrd_vw F b ω = topFormOrd_vw F b' ω) ∧
      (∀ ω : ⋀[F]^n Ω[F⁄K], ∃! f : F, ω = f • topFormGen F b) ∧
      (∀ f : F, topFormOrd_vw F b (f • topFormGen F b) = ordTop_vw V f) ∧
      (∀ x : Fin n → V, 0 ≤ topFormOrd_vw F b (dWedge K fun i => algebraMap V F (x i))) ∧
      (∀ (x : Fin n → V) (i j : Fin n), i ≠ j → x i ∈ maximalIdeal V → x j ∈ maximalIdeal V →
        1 ≤ topFormOrd_vw F b (dWedge K fun i => algebraMap V F (x i))) ∧
      (∀ (k : ℕ) (x : Fin n → F), (∀ i : Fin n, i.val < k → x i ≠ 0) →
        (∀ i : Fin n, k ≤ i.val → x i ∈ Set.range (algebraMap V F)) →
        ((-1 : ℤ) : WithTop ℤ) ≤ topFormOrd_vw F b (exteriorPower.ιMulti F n fun i =>
          if i.val < k then (x i)⁻¹ • D K F (x i) else D K F (x i))) ∧
      (∀ (k : ℕ) (x : Fin n → V), (∀ i : Fin n, i.val < k → IsUnit (x i)) →
        0 ≤ topFormOrd_vw F b (exteriorPower.ιMulti F n fun i =>
          if i.val < k then (algebraMap V F (x i))⁻¹ • D K F (algebraMap V F (x i))
          else D K F (algebraMap V F (x i)))) := by
  refine ⟨trdeg_residueField_of_trdeg K V F hn,
    fun t ht => exists_basis_kaehler_of_trdeg K F hn ht, ?_, fun b =>
    ⟨topFormOrd_vw_eq b, fun ω => ⟨_, (topFormCoeff_smul_topFormGen b ω).symm, ?_⟩,
      topFormOrd_vw_smul_topFormGen b, topFormOrd_vw_dWedge_nonneg b,
      fun x i j hij hi hj => one_le_topFormOrd_vw_dWedge b x hij hi hj, ?_, ?_⟩⟩
  · obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨-, -, b, -, -⟩ := exists_basis_kaehler_of_trdeg K F hn ht
    exact ⟨b⟩
  · rintro f rfl
    simp
  · intro k x h₁ h₂
    have := neg_one_le_topFormOrd_vw_dlogWedge b (Finset.univ.filter fun i => i.val < k) x
      (fun i hi => h₁ i (by simpa using hi)) (fun i hi => h₂ i (by simpa using hi))
    simpa only [dlogWedge, Finset.mem_filter, Finset.mem_univ, true_and] using this
  · intro k x h₁
    have := topFormOrd_vw_dlogWedge_nonneg (F := F) b (Finset.univ.filter fun i => i.val < k) x
      (fun i hi => h₁ i (by simpa using hi))
    simpa only [dlogWedge, Finset.mem_filter, Finset.mem_univ, true_and] using this
end GlobalTheory
