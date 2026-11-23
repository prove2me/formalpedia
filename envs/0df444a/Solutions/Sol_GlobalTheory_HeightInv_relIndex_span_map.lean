-- Prove2me | solution 1 for GlobalTheory.HeightInv.relIndex_span_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:47.423796+00:00
-- url     : https://prove2.me/submissions/86ec308e-ae5b-41ce-90c3-4d44a9e603d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.HeightInv
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
namespace GlobalTheory.HeightInv
namespace _root_.GlobalTheory.HeightInv
theorem _root_.solution {R K V ι : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] [Module R V] [IsScalarTower R K V] (Λ : Submodule R V) (f : V →ₗ[K] V)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) (hΛ : ∀ x, x ∈ Λ ↔ f x ∈ Λ)
    (w : ι → V) :
    (Submodule.span R (Set.range fun a => f (w a))).toAddSubgroup.relIndex
        (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range fun a => f (w a))).toAddSubgroup) =
      (Submodule.span R (Set.range w)).toAddSubgroup.relIndex
        (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup) := by
  let g : V →+ V := f.toAddMonoidHom
  have hg : Function.Injective g := hinj
  have hΛmap : Λ.toAddSubgroup.map g = Λ.toAddSubgroup := by
    ext v
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hΛ x).1 hx
    · intro hv
      obtain ⟨x, rfl⟩ := hsurj v
      exact ⟨x, (hΛ x).2 hv, rfl⟩
  have hK : Submodule.span K (Set.range fun a => f (w a)) = (Submodule.span K (Set.range w)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hR : Submodule.span R (Set.range fun a => f (w a)) =
      (Submodule.span R (Set.range w)).map (f.restrictScalars R) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hKg : ((Submodule.span K (Set.range w)).map f).toAddSubgroup =
      (Submodule.span K (Set.range w)).toAddSubgroup.map g := by
    ext v
    simp [Submodule.mem_map, AddSubgroup.mem_map, g]
  have hRg : ((Submodule.span R (Set.range w)).map (f.restrictScalars R)).toAddSubgroup =
      (Submodule.span R (Set.range w)).toAddSubgroup.map g := by
    ext v
    simp [Submodule.mem_map, AddSubgroup.mem_map, g]
  have hinf : Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup.map g =
      (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup).map g := by
    rw [AddSubgroup.map_inf_eq _ _ _ hg, hΛmap]
  rw [hK, hR, hKg, hRg, hinf, AddSubgroup.relIndex_map_map_of_injective _ _ hg]
end _root_.GlobalTheory.HeightInv
end GlobalTheory.HeightInv
