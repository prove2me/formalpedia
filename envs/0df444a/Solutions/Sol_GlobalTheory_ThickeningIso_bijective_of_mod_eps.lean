-- Prove2me | solution 1 for GlobalTheory.ThickeningIso.bijective_of_mod_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:54.283456+00:00
-- url     : https://prove2.me/submissions/a2621452-0e74-46c0-be04-a2469f18267d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoThickeningMapOfModEps
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_mul_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.ThickeningIso
namespace GlobalTheory.ThickeningIso
theorem _root_.solution {K B C D : Type} [Field K] [CommRing B] [CommRing C] [CommRing D]
    (a : DualNumber K →+* B) (φ : B →+* C) (p : C →+* D) (hf : (φ.comp a).Flat)
    (hs : Function.Surjective (p.comp φ))
    (hB : RingHom.ker (p.comp φ) = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map a)
    (hC : RingHom.ker p = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map (φ.comp a)) :
    Function.Bijective φ := by
  have hk : RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom = Ideal.span {DualNumber.eps} := by
    ext x
    rw [Ideal.mem_span_singleton', RingHom.mem_ker]
    constructor
    · intro hx
      have hx' : x.fst = 0 := hx
      exact ⟨TrivSqZeroExt.inl x.snd, by ext <;> simp [hx']⟩
    · rintro ⟨y, rfl⟩
      change (y * DualNumber.eps).fst = 0
      simp
  have hB' : ∀ b, p (φ b) = 0 → ∃ b', b = b' * a DualNumber.eps := fun b hb => by
    have : b ∈ RingHom.ker (p.comp φ) := hb
    rw [hB, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at this
    obtain ⟨b', h⟩ := this
    exact ⟨b', h.symm⟩
  have hC' : ∀ c, p c = 0 → ∃ c', c = c' * φ (a DualNumber.eps) := fun c hc => by
    have : c ∈ RingHom.ker p := hc
    rw [hC, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at this
    obtain ⟨b', h⟩ := this
    exact ⟨b', h.symm⟩
  have he : a DualNumber.eps * a DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hfl : ∀ c, c * φ (a DualNumber.eps) = 0 → p c = 0 := fun c hc => by
    let _ : Algebra (DualNumber K) C := (φ.comp a).toAlgebra
    have : Module.Flat (DualNumber K) C := hf
    obtain ⟨k, m, y, h1, h2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (R := DualNumber K) (M := C) (f := fun _ : Unit => DualNumber.eps) (x := fun _ => c) (by
        rw [Fintype.sum_unique, Algebra.smul_def, _root_.mul_comm]; exact hc)
    rw [← RingHom.mem_ker, show c = _ from h1 (), hC]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have h3 := congrArg TrivSqZeroExt.snd (h2 j)
    change (m () j).fst = 0
    simpa using h3
  have h1 : ∀ c, ∃ b c', c = φ b + c' * φ (a DualNumber.eps) := fun c => by
    obtain ⟨b, hb⟩ := hs (p c)
    obtain ⟨c', h⟩ := hC' (c - φ b) (by rw [map_sub, ← hb]; exact sub_self _)
    exact ⟨b, c', by rw [← h]; ring⟩
  refine ⟨(injective_iff_map_eq_zero φ).2 fun b hb => ?_, fun c => ?_⟩
  · obtain ⟨b', rfl⟩ := hB' b (by rw [hb, map_zero])
    obtain ⟨b'', rfl⟩ := hB' b' (hfl _ (by rw [← map_mul, hb]))
    rw [_root_.mul_assoc, he, mul_zero]
  · obtain ⟨b, c', rfl⟩ := h1 c
    obtain ⟨b', c'', rfl⟩ := h1 c'
    refine ⟨b + b' * a DualNumber.eps, ?_⟩
    rw [add_mul, _root_.mul_assoc, ← map_mul φ (a _), he]
    simp
end GlobalTheory.ThickeningIso
