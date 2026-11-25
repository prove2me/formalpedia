-- Prove2me | solution 1 for GlobalTheory.Conv.exists_chart_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:37:02.026017+00:00
-- url     : https://prove2.me/submissions/7a2113da-2d68-425f-be82-9c3c400a6acf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology ENNReal NNReal ContDiff
open Filter Metric
noncomputable section
open GlobalTheory GlobalTheory.Conv
open CategoryTheory AlgebraicGeometry
namespace GlobalTheory.Conv
theorem _root_.solution {Y : Scheme.{0}} (s : Y ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType s] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℂ R]
    (x : Spec (.of R) ⟶ Y) (hx : x ≫ s = Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :
    ∃ (A : CommRingCat.{0}) (_ : Algebra ℂ A) (_ : Algebra.FiniteType ℂ A) (i : Spec A ⟶ Y)
      (φ : A →ₐ[ℂ] R), IsOpenImmersion i ∧
        i ≫ s = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) ∧
        Spec.map (CommRingCat.ofHom (φ : A →+* R)) ≫ i = x := by
  obtain ⟨A, i, _, q, hq⟩ := Scheme.exists_Spec_apply_eq (x (IsLocalRing.closedPoint R))
  have hle : Set.range x ⊆ Set.range i := by
    rintro _ ⟨t, rfl⟩
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of R) x (U := i.opensRange)
      ⟨q, hq⟩).ge (Set.mem_univ t)
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ i = x := ⟨_, IsOpenImmersion.lift_fac i x hle⟩
  obtain ⟨a, rfl⟩ := Spec.map_surjective l
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ s)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  let : Algebra ℂ A := φ.hom.toAlgebra
  rw [Category.assoc, ← hφ, ← Spec.map_comp] at hx
  have hc := congrArg CommRingCat.Hom.hom (Spec.map_injective hx)
  exact ⟨A, this, hft, i, ⟨a.hom, fun c => DFunLike.congr_fun hc c⟩, ‹_›, hφ.symm, rfl⟩
end GlobalTheory.Conv
