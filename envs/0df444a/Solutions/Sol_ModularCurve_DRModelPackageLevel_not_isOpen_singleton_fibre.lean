-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.not_isOpen_singleton_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b014436d-d91b-57e1-9a44-08a35f08a683

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_not_isOpen_singleton_fibre

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
    (w : DRLevel.fibre (N₀ := N₀) toκ) : ¬ IsOpen ({w} : Set (DRLevel.fibre (N₀ := N₀) toκ)) := by
  intro hw
  haveI : IsProper (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := 𝔓.isProper_fibre0 toκ
  haveI : IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ) := 𝔓.isIntegral_fibre0 toκ
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) :=
    𝔓.smoothOfRelativeDimension_one_fibre0 toκ
  haveI : JacobsonSpace (DRLevel.fibre0 (N₀ := N₀) toκ) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))

  obtain ⟨i, u, hu⟩ : ∃ i : Fin 2, ∃ u, (𝔓.comp κ toκ i).base u = w := by
    rcases 𝔓.comp_jointly_surjective κ toκ w with ⟨u, hu⟩ | ⟨u, hu⟩
    exacts [⟨0, u, hu⟩, ⟨1, u, hu⟩]
  haveI : IsClosedImmersion (𝔓.comp κ toκ i) := 𝔓.comp_isClosedImmersion κ toκ i

  have hpre : (𝔓.comp κ toκ i).base ⁻¹' {w} = {u} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hv; exact (𝔓.comp κ toκ i).isClosedEmbedding.injective (hv.trans hu.symm)
    · rintro rfl; exact hu
  have hopen : IsOpen ({u} : Set (DRLevel.fibre0 (N₀ := N₀) toκ)) := by
    rw [← hpre]; exact hw.preimage (𝔓.comp κ toκ i).base.hom.continuous

  have hgen : genericPoint (DRLevel.fibre0 (N₀ := N₀) toκ) ∈ ({u} : Set _) :=
    ((genericPoint_spec (DRLevel.fibre0 (N₀ := N₀) toκ)).mem_open_set_iff hopen).mpr ⟨u, Set.mem_univ _, rfl⟩
  have hgu : genericPoint (DRLevel.fibre0 (N₀ := N₀) toκ) = u := hgen
  obtain ⟨z, hz, hzcl⟩ := nonempty_inter_closedPoints (Z := ({u} : Set (DRLevel.fibre0 (N₀ := N₀) toκ))) ⟨u, rfl⟩
    hopen.isLocallyClosed
  obtain rfl : z = u := hz
  have huniv : (Set.univ : Set (DRLevel.fibre0 (N₀ := N₀) toκ)) = {z} := by
    have h1 : closure ({z} : Set (DRLevel.fibre0 (N₀ := N₀) toκ)) = Set.univ := by
      rw [← hgu]; exact genericPoint_spec (DRLevel.fibre0 (N₀ := N₀) toκ)
    rw [← h1, (mem_closedPoints_iff.mp hzcl).closure_eq]

  have hinf := AlgebraicCurve.infinite_setOf_isClosed_singleton
    (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
  refine hinf ((Set.finite_singleton z).subset ?_)
  intro x _
  have : x ∈ (Set.univ : Set (DRLevel.fibre0 (N₀ := N₀) toκ)) := trivial
  rwa [huniv] at this

end S_ModularCurve_DRModelPackageLevel_not_isOpen_singleton_fibre
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_not_isOpen_singleton_fibre (solution)
