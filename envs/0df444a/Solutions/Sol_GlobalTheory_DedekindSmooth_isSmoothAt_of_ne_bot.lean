-- Prove2me | solution 1 for GlobalTheory.DedekindSmooth.isSmoothAt_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:26:21.522265+00:00
-- url     : https://prove2.me/submissions/3a5736a6-151f-4e9a-9249-c3320652a168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmoothOfIsDedekindDomain
import Theorems.Thm_GlobalTheory_DedekindSmooth_exists_uniformiser

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DedekindSmooth
open Polynomial IsLocalRing
namespace GlobalTheory.DedekindSmooth
theorem _root_.solution (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : Ideal B) [hqp : q.IsPrime]
    (hq : q ≠ ⊥) : Algebra.IsSmoothAt k q := by
  obtain ⟨t, htq, ht0, hm⟩ := exists_uniformiser B q hq
  have hqm : q.IsMaximal := hqp.isMaximal hq
  have htr : Transcendental k t := by
    intro ha
    have hi := ha.isIntegral
    have hu : IsUnit t := hi.isUnit ht0
    exact hqp.ne_top (Ideal.eq_top_of_isUnit_mem _ htq hu)
  letI : Algebra k[X] B := (aeval t : k[X] →ₐ[k] B).toRingHom.toAlgebra
  have : IsScalarTower k k[X] B := .of_algebraMap_eq fun c => by
    change _ = aeval t (algebraMap k k[X] c)
    simp
  have hinj : Function.Injective (algebraMap k[X] B) := transcendental_iff_injective.mp htr
  have : FaithfulSMul k[X] B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Module.Flat k[X] B := inferInstance
  have : Algebra.FiniteType k[X] B := .of_restrictScalars_finiteType k _ _
  have : Algebra.FinitePresentation k[X] B :=
    (Algebra.FinitePresentation.of_finiteType (R := k[X]) (A := B)).mp ‹_›
  let p : Ideal k[X] := q.under k[X]
  letI := Localization.AtPrime.algebraOfLiesOver p q
  have hsep : Algebra.IsSeparable p.ResidueField q.ResidueField := by
    have : Module.Finite k (B ⧸ q) := by
      letI := Ideal.Quotient.field q
      exact finite_of_finite_type_of_isJacobsonRing k (B ⧸ q)
    have : Module.Finite k q.ResidueField :=
      Module.Finite.of_surjective (IsScalarTower.toAlgHom k (B ⧸ q) q.ResidueField).toLinearMap
        (Ideal.bijective_algebraMap_quotient_residueField q).2
    have : IsScalarTower k p.ResidueField q.ResidueField := .of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k k[X] p.ResidueField,
        ← IsScalarTower.algebraMap_apply k[X] p.ResidueField q.ResidueField,
        ← IsScalarTower.algebraMap_apply]
    exact Algebra.isSeparable_tower_top_of_isSeparable k _ _
  have hmap : p.map (algebraMap k[X] (Localization.AtPrime q)) = maximalIdeal _ := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply k[X] B (Localization.AtPrime q),
        IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q]
      exact hx
    · have hX : algebraMap k[X] B X = t := aeval_X t
      rw [hm, Ideal.span_singleton_le_iff_mem, ← hX, ← IsScalarTower.algebraMap_apply]
      apply Ideal.mem_map_of_mem
      change algebraMap k[X] B X ∈ q
      rwa [hX]
  have : Algebra.IsUnramifiedAt k[X] q :=
    (Algebra.isUnramifiedAt_iff_map_eq k[X] p q).mpr ⟨hsep, hmap⟩
  have : Algebra.IsEtaleAt k[X] q := .of_isUnramifiedAt_of_flat q
  exact Algebra.FormallySmooth.comp k k[X] _
end GlobalTheory.DedekindSmooth
