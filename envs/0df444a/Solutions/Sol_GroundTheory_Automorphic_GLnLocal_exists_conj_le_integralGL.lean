-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.exists_conj_le_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:56:51.943795+00:00
-- url     : https://prove2.me/submissions/b7cabbd6-03b7-4112-8629-626d83a0890c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_standardLattice
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_pow_mul_mem_of_isCompact

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
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution {H : Subgroup (GL (Fin n) F)}
    (hH : IsCompact (H : Set (GL (Fin n) F))) :
    ∃ g : GL (Fin n) F, ∀ h ∈ H, g⁻¹ * h * g ∈ integralGL F n := by
  obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_isCompact F n hH
  have hϖ : (uniformizer F : F) ^ m ≠ 0 :=
    pow_ne_zero _ fun h => valuation_uniformizer_ne_zero F (by rw [h, map_zero])
  let a : Fˣ := Units.mk0 _ hϖ
  let S : Set (Fin n → F) :=
    ⋃ h ∈ H, (mapSubmodule F n h (standardLattice F n) : Set (Fin n → F))
  let L : Submodule 𝒪[F] (Fin n → F) := Submodule.span 𝒪[F] S

  have hLa : L ≤ a⁻¹ • standardLattice F n := by
    rw [Submodule.span_le]
    intro v hv
    obtain ⟨h, hh, hv⟩ := Set.mem_iUnion₂.mp hv
    rw [SetLike.mem_coe, mapSubmodule, Submodule.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [SetLike.mem_coe, ← inv_smul_smul a (glLin F n h w)]
    refine Submodule.smul_mem_pointwise_smul _ _ _ ((mem_standardLattice F n).mpr fun i => ?_)
    change (uniformizer F : F) ^ m * ∑ j, h i j * w j ∈ 𝒪[F]
    rw [Finset.mul_sum]
    refine Subring.sum_mem _ fun j _ => ?_
    rw [← mul_assoc]
    exact Subring.mul_mem _ (hm h hh i j) (hw j)
  have hfg : L.FG :=
    Submodule.FG.of_le (Submodule.IsLattice.fg (A := F) (M := a⁻¹ • standardLattice F n)) hLa
  have hstd : standardLattice F n ≤ L := fun v hv => Submodule.subset_span
    (Set.mem_iUnion₂.mpr ⟨1, H.one_mem, by rw [mapSubmodule_one]; exact hv⟩)
  have hLlat : L.IsLattice F := Submodule.IsLattice.of_le_of_isLattice_of_fg F hstd hfg

  have hstab_le : ∀ h ∈ H, mapSubmodule F n h L ≤ L := by
    intro h hh
    rw [mapSubmodule, Submodule.map_span_le]
    intro v hv
    obtain ⟨h', hh', hv⟩ := Set.mem_iUnion₂.mp hv
    refine Submodule.subset_span (Set.mem_iUnion₂.mpr ⟨h * h', H.mul_mem hh hh', ?_⟩)
    rw [SetLike.mem_coe, mapSubmodule_mul]
    exact Submodule.mem_map_of_mem hv
  have hstab : ∀ h ∈ H, mapSubmodule F n h L = L := fun h hh =>
    le_antisymm (hstab_le h hh) (by
      have := Submodule.map_mono (f := glLin F n h) (hstab_le h⁻¹ (H.inv_mem hh))
      change mapSubmodule F n h (mapSubmodule F n h⁻¹ L) ≤ mapSubmodule F n h L at this
      rwa [mapSubmodule_mapSubmodule_inv] at this)
  obtain ⟨g, hg⟩ := exists_smul_standard F n ⟨L, hLlat⟩
  have hgL : mapSubmodule F n g (standardLattice F n) = L := congrArg Subtype.val hg
  refine ⟨g, fun h hh => (mapSubmodule_standardLattice_eq_iff F n).mp ?_⟩
  rw [mapSubmodule_mul, mapSubmodule_mul, hgL, hstab h hh, ← hgL, mapSubmodule_inv_mapSubmodule]
end GroundTheory.Automorphic.GLnLocal
