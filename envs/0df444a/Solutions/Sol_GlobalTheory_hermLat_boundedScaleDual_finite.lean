-- Prove2me | solution 1 for GlobalTheory.hermLat_boundedScaleDual_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:55:16.786991+00:00
-- url     : https://prove2.me/submissions/f6e13ba8-3e24-4c34-89be-0d57abb03bf7

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FiniteIsometryClassesDefiniteHermitianBoundedSca
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetFinite_core
import Theorems.Thm_Formalism_HermitianLatticesTheory_final_finIntermediate
import Theorems.Thm_Formalism_HermitianLatticesTheory_final_isomOfTrace
import Theorems.Thm_Formalism_HermitianLatticesTheory_final_shortVectors
import Theorems.Thm_Formalism_HermitianLatticesTheory_final_traceReal
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_covol_le
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_discr
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_trace_int
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) (d c : ℕ) (hd : 0 < d) (hc : 0 < c) :
    ∃ s : Finset (Submodule (𝓞 K) V), (∀ M₀ ∈ s, Submodule.IsLattice K M₀) ∧
      ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M →
        (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ Set.range (algebraMap (𝓞 K) K)) →
        (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M) →
        ∃ M₀ ∈ s, ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g M₀ = M := by
  classical
  obtain ⟨N, ι, hι, hmul, hlat⟩ := Formalism.HermitianLatticesTheory.final_traceReal K V h hs hpos
  set e : ℤ := NumberField.discr K with he
  have he0 : e ≠ 0 := NumberField.discr_ne_zero K
  have ecast : ((e.natAbs ^ 2 : ℕ) : K) = ((e : K)) * (e : K) := by
    have h0 : ((e.natAbs ^ 2 : ℕ) : ℤ) = e * e := by rw [Nat.cast_pow, Int.natAbs_sq, sq]
    rw [← Int.cast_natCast, h0, Int.cast_mul]
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    fun r => ⟨⟨star (algebraMap (𝓞 K) K r), r.isIntegral_coe.map (starRingEnd K).toIntAlgHom⟩, rfl⟩
  let S : Set (Submodule (𝓞 K) V) := {M | Submodule.IsLattice K M ∧
    (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ Set.range (algebraMap (𝓞 K) K)) ∧
    (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M)}
  obtain ⟨s, hs1, hs2⟩ := Formalism.HermitianLatticesTheory.classSetFinite_core Formalism.HermitianLatticesTheory.final_shortVectors
    Formalism.HermitianLatticesTheory.final_finIntermediate Formalism.HermitianLatticesTheory.final_isomOfTrace h hpos N ι hι hmul d hd
    (Real.sqrt (((c * e.natAbs ^ 2 : ℕ) : ℝ) ^ N)) S
    (fun M hM x hx y hy => Submodule.mem_one.mpr (hM.2.1 x hx y hy))
    (fun M hM => hlat M hM.1)
    (by
      intro M hM _ _
      apply Formalism.HermitianLatticesTheory.genusCovolBound_covol_le h N ι hι M (c * e.natAbs ^ 2)
        (Nat.mul_pos hc (pow_pos (Int.natAbs_pos.mpr he0) 2))
      have hdual : ∀ y, (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z) →
          ∀ x ∈ M, h x ((e : K) • y) ∈ Set.range (algebraMap (𝓞 K) K) := by
        intro y hy x hx
        rw [LinearMap.map_smul, smul_eq_mul]
        have hm : ((e : ℤ) : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
          apply Formalism.HermitianLatticesTheory.genusCovolBound_discr
          intro r
          obtain ⟨s, hs'⟩ := hstar r
          obtain ⟨z, hz⟩ := hy (s • x) (M.smul_mem s hx)
          refine ⟨z, ?_⟩
          rw [← hz]
          congr 1
          rw [← algebraMap_smul K s x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
            starRingEnd_apply, hs', star_star, mul_comm]
        exact Submodule.mem_one.mp hm
      intro y y' hy hy'
      have h1 : (c : K) • ((e : K) • y) ∈ M := hM.2.2 _ (hdual y hy)
      have h2 := hdual y' hy' _ h1
      have key : h ((c : K) • ((e : K) • y)) ((e : K) • y') =
          algebraMap ℚ K ((c * e.natAbs ^ 2 : ℕ) : ℚ) * h y y' := by
        rw [map_natCast, Nat.cast_mul, ecast]
        simp only [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply, star_intCast,
          star_natCast, smul_eq_mul]
        ring
      rw [key] at h2
      obtain ⟨r, hr⟩ := h2
      obtain ⟨z, hz⟩ := Formalism.HermitianLatticesTheory.genusCovolBound_trace_int (K := K) r
      refine ⟨z, ?_⟩
      rw [← hz, hr, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul])
  exact ⟨s, fun M₀ hM₀ => (hs1 M₀ hM₀).1, fun M hL hd' hc' => hs2 M ⟨hL, hd', hc'⟩⟩
end GlobalTheory
