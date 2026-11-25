-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_fixedVectors_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:53.287799+00:00
-- url     : https://prove2.me/submissions/00351fbb-7064-4fad-8618-ecb301c1d6c6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_iterate_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_injective
import Theorems.Thm_GroundTheory_Automorphic_exists_fixedVectors_mk_eq_of_fixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {N M Nbar K : Subgroup G}
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Automorphic
theorem _root_.solution (hρ : IsAdmissible ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G))
    (hfact : ∀ k ∈ K, ∃ z ∈ K ⊓ Nbar, ∃ y ∈ K ⊓ M, ∃ x ∈ K ⊓ N, k = z * y * x)
    (a : G) (haN : ∀ n ∈ N, a * n * a⁻¹ ∈ N) (haN' : ∀ n ∈ N, a⁻¹ * n * a ∈ N)
    (haM : ∀ y ∈ K ⊓ M, a * y = y * a)
    (haK : ∀ z ∈ K ⊓ Nbar, a⁻¹ * z * a ∈ K)
    (hlim : ∀ U ∈ 𝓝 (1 : G), ∃ m : ℕ, ∀ z ∈ K ⊓ Nbar, (a ^ m)⁻¹ * z * a ^ m ∈ U)
    {v : V} (hv : ∀ y ∈ K ⊓ M, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ y v) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) v) :
    ∃ x ∈ fixedVectors ρ K, Representation.Coinvariants.mk (ρ.comp N.subtype) x =
      Representation.Coinvariants.mk (ρ.comp N.subtype) v := by
  classical
  obtain ⟨hsm, hadm⟩ := hρ

  have hfact' : ∀ k ∈ K, ∃ x ∈ K ⊓ N, ∃ y ∈ K ⊓ M, ∃ z ∈ K ⊓ Nbar, k = x * y * z := by
    intro k hk
    obtain ⟨z, hz, y, hy, x, hx, h⟩ := hfact k⁻¹ (K.inv_mem hk)
    refine ⟨x⁻¹, Subgroup.inv_mem _ hx, y⁻¹, Subgroup.inv_mem _ hy, z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
    rw [← inv_inv k, h]
    group
  set q := Representation.Coinvariants.mk (ρ.comp N.subtype) with hq
  set A := coinvariantsTranslate ρ N a haN with hA
  have hAinj : Function.Injective A := coinvariantsTranslate_injective haN haN'
  set I : Submodule ℂ (Representation.Coinvariants (ρ.comp N.subtype)) :=
    Submodule.map q (fixedVectors ρ K) with hI
  have : FiniteDimensional ℂ (fixedVectors ρ K) := hadm K hKc hKo
  have hIfin : FiniteDimensional ℂ I := by
    rw [hI]
    infer_instance

  have hAI : ∀ u ∈ I, A u ∈ I := by
    rintro _ ⟨x, hx, rfl⟩
    have hNbar : ∀ z ∈ K ⊓ Nbar, ρ z (ρ a x) = ρ a x := by
      intro z hz
      have : z = a * (a⁻¹ * z * a) * a⁻¹ := by group
      rw [this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        ← Module.End.mul_apply (ρ a⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
        hx _ (haK z hz)]
    have hM0 : ∀ y ∈ K ⊓ M, q (ρ y (ρ a x)) = q (ρ a x) := by
      intro y hy
      rw [← Module.End.mul_apply, ← map_mul, ← haM y hy, map_mul, Module.End.mul_apply,
        hx y (Subgroup.mem_inf.1 hy).1]
    obtain ⟨x', hx', hx'q⟩ := exists_fixedVectors_mk_eq_of_fixed hsm hKc hKo hfact' hNbar hM0
    refine ⟨x', hx', ?_⟩
    rw [hx'q, hA, coinvariantsTranslate_mk]

  set Ai : I →ₗ[ℂ] I := A.restrict hAI with hAi
  have hAiinj : Function.Injective Ai := by
    intro u u' h
    exact Subtype.ext (hAinj (congrArg Subtype.val h))
  have hAisurj : Function.Surjective Ai := LinearMap.injective_iff_surjective.1 hAiinj
  have hback : ∀ u, A u ∈ I → u ∈ I := by
    intro u hu
    obtain ⟨i, hi⟩ := hAisurj ⟨A u, hu⟩
    have : A i = A u := congrArg Subtype.val hi
    rw [← hAinj this]
    exact i.2
  have hiter : ∀ m : ℕ, ∀ u, A^[m] u ∈ I → u ∈ I := by
    intro m
    induction m with
    | zero => exact fun u hu => hu
    | succ m ih =>
      intro u hu
      rw [Function.iterate_succ_apply] at hu
      exact hback u (ih _ hu)

  obtain ⟨m, hm⟩ := hlim _ ((hsm v).mem_nhds (one_mem (stabilizerOf ρ v)))
  have hNbar : ∀ z ∈ K ⊓ Nbar, ρ z (ρ (a ^ m) v) = ρ (a ^ m) v := by
    intro z hz
    have : z = a ^ m * ((a ^ m)⁻¹ * z * a ^ m) * (a ^ m)⁻¹ := by group
    rw [this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ← Module.End.mul_apply (ρ (a ^ m)⁻¹), ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, mem_stabilizerOf.1 (hm z hz)]
  have hM0 : ∀ y ∈ K ⊓ M, q (ρ y (ρ (a ^ m) v)) = q (ρ (a ^ m) v) := by
    intro y hy
    have hc : a ^ m * y = y * a ^ m := ((Commute.pow_left (haM y hy) m))
    rw [← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply,
      ← iterate_coinvariantsTranslate_mk haN, hv y hy, iterate_coinvariantsTranslate_mk haN]
  obtain ⟨x, hx, hxq⟩ := exists_fixedVectors_mk_eq_of_fixed hsm hKc hKo hfact' hNbar hM0
  have hmem : A^[m] (q v) ∈ I := by
    rw [hA, iterate_coinvariantsTranslate_mk haN, ← hxq]
    exact ⟨x, hx, rfl⟩
  obtain ⟨x', hx', hx'q⟩ := hiter m _ hmem
  exact ⟨x', hx', hx'q⟩
end GroundTheory.Automorphic
