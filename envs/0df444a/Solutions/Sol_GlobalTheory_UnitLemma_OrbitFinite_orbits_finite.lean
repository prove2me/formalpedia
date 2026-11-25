-- Prove2me | solution 1 for GlobalTheory.UnitLemma.OrbitFinite.orbits_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:08:24.492965+00:00
-- url     : https://prove2.me/submissions/45d54467-38f4-4458-8ada-1299de666768

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsConductorMulMemAdjoinOfSeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenMulLeftImageLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusSubmoduleMulLeftImageMemSelfDualStableLattiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelIndexUnitStabilizerIntegralUnitsNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMaximalOrderHullSelfDualStableLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSelfDualIntegralHermitianLatticesModUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualStableLatticeUnitOrbitsFinite
import Theorems.Thm_GlobalTheory_T_exists_conductor_mul_mem_adjoin_of_separable
import Theorems.Thm_GlobalTheory_T_exists_maximalOrder_hull_selfDual_stable_lattice
import Theorems.Thm_GlobalTheory_T_finite_selfDualIntegral_hermitianLattices_modUnits
import Theorems.Thm_GlobalTheory_T_finite_submodules_between_mulLeftImage_lattice
import Theorems.Thm_GlobalTheory_T_relIndex_unitStabilizer_integralUnits_ne_zero
import Theorems.Thm_GlobalTheory_T_torus_submoduleMulLeftImage_mem_selfDualStableLattices
import Theorems.Thm_GlobalTheory_UnitLemma_isIntegral_of_isLat_stable
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_GlobalTheory_powGr_map_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.OrbitFinite
namespace GlobalTheory.UnitLemma.OrbitFinite
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → Finite (Orb K.O B.T (B.X x)) ∧ ∀ L ∈ B.X x, stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  intro K B hsep x hxu hxσ
  by_cases h0 : ∃ L0, L0 ∈ B.X x
  swap
  · push_neg at h0
    haveI : IsEmpty (B.X x) := ⟨fun L => h0 L.1 L.2⟩
    refine ⟨?_, fun L hL => absurd hL (h0 L)⟩
    unfold Orb
    infer_instance
  obtain ⟨L0, hL0⟩ := h0
  have hgi : IsIntegral K.O B.g := isIntegral_of_isLat_stable L0 hL0.1 B.g hL0.2.1
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.exists_conductor_mul_mem_adjoin_of_separable K B hsep hgi

  have hadj : ∀ L ∈ B.X x, ∀ a ∈ Algebra.adjoin K.O ({B.g} : Set B.A), ∀ y ∈ L, a * y ∈ L := by
    intro L hL a ha
    induction ha using Algebra.adjoin_induction with
    | mem a h =>
      rw [Set.mem_singleton_iff] at h
      subst h
      exact hL.2.1
    | algebraMap r =>
      intro y hy
      rw [← Algebra.smul_def]
      exact L.smul_mem r hy
    | add a b _ _ ha hb =>
      intro y hy
      rw [add_mul]
      exact L.add_mem (ha y hy) (hb y hy)
    | mul a b _ _ ha hb =>
      intro y hy
      rw [mul_assoc]
      exact ha _ (hb y hy)
  have hcL : ∀ L ∈ B.X x, ∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L :=
    fun L hL u hu y hy => hadj L hL _ (hc u hu) y hy
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hSf, hSl, hS⟩ := GlobalTheory.T.finite_selfDualIntegral_hermitianLattices_modUnits K B hsep x hxu hxσ c hc0
    set W : Set (Submodule K.O B.A) :=
      (⋃ J ∈ S, {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) J ≤ M ∧ M ≤ J}) ∩ B.X x with hW
    have hWf : W.Finite :=
      (hSf.biUnion fun J hJ => GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B J (hSl J hJ) c hc0).subset Set.inter_subset_left
    haveI : Finite W := hWf.to_subtype
    let f : W → Orb K.O B.T (B.X x) := fun M => Quot.mk _ ⟨M.1, M.2.2⟩
    apply Finite.of_surjective f
    intro o
    set L := (Quot.out o).1 with hLdef
    have hL : L ∈ B.X x := (Quot.out o).2
    obtain ⟨J, hJl, hJs, hJ1, hJ2, hJc, hLJ⟩ := GlobalTheory.T.exists_maximalOrder_hull_selfDual_stable_lattice K B x c hc0 L hL (hcL L hL)
    obtain ⟨t, ht, htS⟩ := hS J hJl hJs hJ1 hJ2
    have hcomm : mulLat K.O (algebraMap K.O B.A c) (mulLat K.O (t : B.A) J) =
        mulLat K.O (t : B.A) (mulLat K.O (algebraMap K.O B.A c) J) := by
      unfold mulLat
      rw [← Submodule.map_comp, ← Submodule.map_comp]
      congr 1
      ext y
      simp [mul_left_comm]
    have hmem : mulLat K.O (t : B.A) L ∈ W := by
      refine ⟨Set.mem_biUnion htS ⟨?_, Submodule.map_mono hLJ⟩, GlobalTheory.T.torus_submoduleMulLeftImage_mem_selfDualStableLattices K B x t ht L hL⟩
      rw [hcomm]
      exact Submodule.map_mono hJc
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [← Quot.out_eq o]
    exact (Quot.sound ⟨t, ht, rfl⟩).symm
  · intro L hL
    refine ⟨?_, GlobalTheory.T.relIndex_unitStabilizer_integralUnits_ne_zero K B L hL.1 c hc0 (hcL L hL)⟩
    rintro t ⟨hs, -⟩
    refine ⟨isIntegral_of_isLat_stable L hL.1 (t : B.A) fun y hy => (hs y).mp hy, ?_⟩
    refine isIntegral_of_isLat_stable L hL.1 _ fun y hy => (hs _).mpr ?_
    rw [← mul_assoc, Units.mul_inv, one_mul]
    exact hy
end GlobalTheory.UnitLemma.OrbitFinite
