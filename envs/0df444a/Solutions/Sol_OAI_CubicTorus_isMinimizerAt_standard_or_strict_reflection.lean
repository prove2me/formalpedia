-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_standard_or_strict_reflection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:12:43.171872+00:00
-- url     : https://prove2.me/submissions/e9af4407-6093-4f8e-933c-ec1e6dd1891b

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_connected_or_standard_slab
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_connected_reflection_geometry
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_cylindrical_standard_tube
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_zero_coordinate_cylindrical

section
-- module Solutions.OAIQ079_CT.Compat
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

lemma cube_preimage : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
    univ.pi (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
  ext x
  simp [fundamentalCube]

end CubicTorus

namespace CubicTorus

lemma circle_measurePreserving_mk_Ico :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      (volume.restrict (Ico 0 1)) volume := by
  rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

lemma torusVolume_eq_product :
    torusVolume = Measure.map (WithLp.toLp 2 : ProductTorus → Torus) volume := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  have he := (PiLp.volume_preserving_toLp (Fin 3)).restrict_preimage measurableSet_fundamentalCube
  rw [cube_preimage] at he
  have hp := measurePreserving_pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ))))
    (fun _ => circle_measurePreserving_mk_Ico)
  have hs : (volume : Measure (Fin 3 → ℝ)).restrict
      (univ.pi (fun _ : Fin 3 => Ico 0 1)) =
      Measure.pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hto : Measurable (WithLp.toLp 2 : ProductTorus → Torus) :=
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable
  unfold torusVolume
  rw [← he.map_eq, hs, Measure.map_map measurable_quotientMap (PiLp.volume_preserving_toLp (Fin 3)).measurable]
  rw [volume_pi, ← hp.map_eq, Measure.map_map hto hp.measurable]
  rfl

end CubicTorus

namespace CubicTorus

instance torusVolume_haar : torusVolume.IsAddHaarMeasure := by
  rw [torusVolume_eq_product]
  exact AddEquiv.isAddHaarMeasure_map volume (WithLp.addEquiv 2 ProductTorus).symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.continuous
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).continuous

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVLocalTranslation
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

instance torusVolume_negInvariant : torusVolume.IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular torusVolume

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_CoordinateChamber
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma congruentAE_of_translated {E F C : Set Torus} {b : Torus}
    (he : F =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E)) (hc : CongruentAE F C) :
    CongruentAE E C := by
  obtain ⟨φ,hφ⟩ := hc
  refine ⟨φ.trans (IsometryEquiv.addRight b),?_⟩
  have hh := (measurePreserving_add_right torusVolume (-b)).quasiMeasurePreserving.preimage_ae_eq
    (he.symm.trans hφ)
  filter_upwards [hh] with x hx
  change (x+ -b+b∈E)=(x+ -b∈φ '' C) at hx
  rw [neg_add_cancel_right] at hx
  change (x∈E)=(x∈(φ.trans (IsometryEquiv.addRight b)) '' C)
  rw [hx]
  apply propext
  constructor
  · rintro ⟨y,hy,he⟩
    refine ⟨y,hy,?_⟩
    change φ y+b=x
    rw [he]; abel
  · rintro ⟨y,hy,he⟩
    refine ⟨y,hy,?_⟩
    change φ y+b=x at he
    rw [← he]; abel

theorem isMinimizerAt_standard_or_strict_reflection_oai {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmE : IsMinimizerAt V E) :
    SmallStandardRegion V E ∨
    ∃ (b : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x),
      MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E) ∧ IsMinimizerAt V F ∧
      IsPreconnected (frontier (openRepresentative F)) ∧
      IsNormalMeasure F μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ i : Fin 3,coordinateReflection i ⁻¹' F =ᵐ[torusVolume] F) ∧
      (∀ a : Torus,(∀ i,coordinateSine i (representative a)=0) → a∉frontier (openRepresentative F)) ∧
      ∀ i : Fin 3,
        (∀ a∈frontier (openRepresentative F)∩coordinateHalf i 0,0<N (representative a) i) ∨
        (∀ a∈frontier (openRepresentative F)∩coordinateHalf i 0,N (representative a) i<0) := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  rcases Periodic.isMinimizerAt_connected_or_standard_slab hV' hmE with hc|hs
  · obtain ⟨b,F,μ,N,hN,hp,hF,he,hmF,hcF,hμ,hae,href,hvert,hsg⟩ :=
      isMinimizerAt_connected_reflection_geometry hV' hmE hc
    by_cases hz : ∃ i : Fin 3,∀ a∈frontier (openRepresentative F),N (representative a) i=0
    · obtain ⟨i,hi⟩ := hz
      obtain ⟨c,r,hr0,hr,hbd⟩ := isMinimizerAt_zero_coordinate_cylindrical hV' hF hmF hcF hμ hN hp hae i hi
      obtain ⟨hlow,hupp,hcong⟩ := isMinimizerAt_cylindrical_standard_tube hV hF hmF i hr0 hr hbd
      exact Or.inl (Or.inr (Or.inl ⟨hlow,hupp,congruentAE_of_translated he hcong⟩))
    · refine Or.inr ⟨b,F,μ,N,hN,hp,hF,he,hmF,hcF,hμ,hae,href,hvert,?_⟩
      intro i
      exact (hsg i).resolve_left (fun hi => hz ⟨i,hi⟩)
  · exact Or.inl (by simpa only [StandardRegionAt,ite_eq_left hV.2] using hs.2.2)

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_standard_or_strict_reflection_oai := @OAI.CubicTorus.isMinimizerAt_standard_or_strict_reflection_oai
