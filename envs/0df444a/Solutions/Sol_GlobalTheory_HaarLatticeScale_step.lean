-- Prove2me | solution 1 for GlobalTheory.HaarLatticeScale.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:48.54602+00:00
-- url     : https://prove2.me/submissions/c663211f-cc81-4c5a-88c5-e63d2f65ecb8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsResidueEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MeasureRealValuedLeExp
import Theorems.Thm_GlobalTheory_HaarLatticeScale_exists_valued_eq_exp
import Theorems.Thm_GlobalTheory_HaarLatticeScale_lt_one_iff_le_exp
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_ResidueBoxVolume_measureReal_residueBox
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.HaarLatticeScale
namespace GlobalTheory.HaarLatticeScale
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (V : Type)
    [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι]
    (e : V ≃L[Fv F v] (ι → Fv F v)) (n : ℤ) :
    μ.real {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp (n - 1)} *
      (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) ^ Fintype.card ι =
    μ.real {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp n} := by
  obtain ⟨a, ha⟩ := exists_valued_eq_exp F v (-n)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  let e' : V ≃L[Fv F v] (ι → Fv F v) := e.trans
    (ContinuousLinearEquiv.piCongrRight fun _ : ι =>
      ContinuousLinearEquiv.unitsEquivAut (Fv F v) (Units.mk0 a ha0))
  have he' : ∀ x i, e' x i = e x i * a := fun x i => by
    simp [e']
  have hv : ∀ (y : Fv F v) (m : ℤ),
      Valued.v (y * a) ≤ WithZero.exp m ↔ Valued.v y ≤ WithZero.exp (n + m) := by
    intro y m
    rw [map_mul, ha, WithZero.exp_neg, mul_inv_le_iff₀ WithZero.exp_pos, ← WithZero.exp_add,
      add_comm]
  have h := GlobalTheory.ResidueBoxVolume.measureReal_residueBox F v V μ ι e' {0}
  have h1 : {x | ∀ i, e' x i ∈ v.adicCompletionIntegers F} =
      {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp n} := by
    ext x
    simp only [Set.mem_setOf_eq]
    refine forall_congr' fun i => ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, he', ← WithZero.exp_zero, hv, add_zero]
  have hres : ∀ y : v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) y = 0 ↔
        Valued.v (y : Fv F v) ≤ WithZero.exp (-1 : ℤ) := by
    intro y
    rw [IsLocalRing.residue_eq_zero_iff, ← lt_one_iff_le_exp]
    exact Valuation.mem_maximalIdeal_iff _ _
  have h2 : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e' x i = (y i : Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈
        ({0} : Set (ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F)))} =
      {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp (n - 1)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, funext_iff, Pi.zero_apply, hres]
    constructor
    · rintro ⟨y, hy, hy'⟩ i
      rw [sub_eq_add_neg, ← hv, ← he', hy]
      exact hy' i
    · intro hx
      have hx' : ∀ i, Valued.v (e' x i) ≤ WithZero.exp (-1 : ℤ) := fun i => by
        rw [he', hv, ← sub_eq_add_neg]
        exact hx i
      refine ⟨fun i => ⟨e' x i, ?_⟩, fun i => rfl, hx'⟩
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact ((lt_one_iff_le_exp _).2 (hx' i)).le
  rw [h1, h2] at h
  simpa using h
end GlobalTheory.HaarLatticeScale
