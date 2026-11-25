-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isAdmissible_parabolicInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:55.29581+00:00
-- url     : https://prove2.me/submissions/2b691caa-e82d-41bd-8929-bec6c924a032

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompact_subgroupOf_levi
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_subgroupOf_levi
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_apply_mem_fixedVectors
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_apply_eq_out
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_hasBasis_nhds_one
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isSmooth_parabolicInd
import Theorems.Thm_GroundTheory_Automorphic_fixedVectors_antitone


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hσ : IsAdmissible σ) : IsAdmissible (parabolicInd F n β σ) := by
  classical
  refine ⟨isSmooth_parabolicInd σ, fun K hKc hKo => ?_⟩
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hKo.mem_nhds K.one_mem)
  have hle : congruenceSubgroup F n m ≤ K := hm
  suffices h : FiniteDimensional ℂ
      (fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m)) from
    Submodule.finiteDimensional_of_le (fixedVectors_antitone _ hle)
  set K₀ := integralGL F n
  set Km := congruenceSubgroup F n m
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hQ : Finite (K₀ ⧸ Km.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_congruenceSubgroup F n m).preimage continuous_subtype_val
  set L : Subgroup (levi F n β) := Km.subgroupOf (levi F n β)
  have hL : FiniteDimensional ℂ (fixedVectors σ L) :=
    hσ.2 L (isCompact_subgroupOf_levi (isCompact_congruenceSubgroup F n m))
      (isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m))

  let ev : fixedVectors (parabolicInd F n β σ) Km →ₗ[ℂ] (K₀ ⧸ Km.subgroupOf K₀ → fixedVectors σ L) :=
    LinearMap.pi fun c =>
      LinearMap.codRestrict _
        ((LinearMap.proj (((Quotient.out c : K₀) : GL (Fin n) F))).comp
          ((parabolicIndSpace F n β σ).subtype.comp (fixedVectors _ Km).subtype))
        fun f => apply_mem_fixedVectors f (Quotient.out c).2
  have hinj : Function.Injective ev := by
    intro f g hfg
    have hz : ∀ c : K₀ ⧸ Km.subgroupOf K₀,
        ((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) ((Quotient.out c : K₀) : GL (Fin n) F)
          = ((g : parabolicIndSpace F n β σ) : GL (Fin n) F → W)
            ((Quotient.out c : K₀) : GL (Fin n) F) :=
      fun c => congrArg Subtype.val (congrFun hfg c)
    apply Subtype.ext
    apply Subtype.ext
    funext x
    obtain ⟨p, c, hp⟩ := exists_apply_eq_out (σ := σ) m x
    rw [hp f, hp g, hz c]
  exact FiniteDimensional.of_injective ev hinj
end GroundTheory.Automorphic.Parabolic
