-- Prove2me | solution 1 for OAI.PermanentBorder.Polar.homogeneous_normalized_proper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:05:04.458279+00:00
-- url     : https://prove2.me/submissions/7a6f4ab3-b20f-4d06-b957-24451339c30f

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/RegularSections.lean:L421-L466
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Polar.homogeneous_normalized_proper. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections

-- ---- from OAI.Algebra.Determinantal.RegularSections ----
namespace OAI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
section Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι]

end Algebra
section Good
variable {K ι : Type*} [Field K] [Fintype ι]

end Good
end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
section
variable {σ : Type*} [Fintype σ]

end
end PermanentBorder.CI

namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open Topology Set

theorem homogeneous_normalized_proper {T V : Type*} [TopologicalSpace T]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [ProperSpace V]
    (H : T → V → Prop) (hH : IsClosed {z : T × V | H z.1 z.2})
    (hsmul : ∀ t y (c : ℂ), H t y → H t (c • y))
    (L : T → V →ₗ[ℂ] ℂ) (hL : Continuous (fun z : T × V => L z.1 z.2))
    (hno : ∀ t y, H t y → L t y = 0 → y = 0) :
    IsProperMap (fun z : {z : T × V // H z.1 z.2 ∧ L z.1 z.2 = 1} => z.val.1) := by
  let S := Metric.sphere (0 : V) 1
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  let Q := {z : T × S // H z.1 z.2.val}
  let Z := {z : T × V // H z.1 z.2 ∧ L z.1 z.2 = 1}
  have hn (z : Q) : L z.val.1 z.val.2.val ≠ 0 := by
    intro h
    have he := hno _ _ z.property h
    have hh := z.val.2.property
    simp [S, he] at hh
  let q : Q → Z := fun z => ⟨(z.val.1,(L z.val.1 z.val.2.val)⁻¹ • z.val.2.val),
    hsmul _ _ _ z.property, by simp [map_smul, hn z]⟩
  have hq : Continuous q := by
    have hval : Continuous (fun z : Q => (z.val.1,z.val.2.val) : Q → T × V) := by fun_prop
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (((hL.comp hval).inv₀ hn).smul (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val)))
  have hsurj : Function.Surjective q := by
    intro z
    have hz : z.val.2 ≠ 0 := by
      intro he
      have hh := z.property.2
      simp [he] at hh
    have hc : (‖z.val.2‖ : ℂ) ≠ 0 := by simpa using (norm_ne_zero_iff.mpr hz)
    let y : S := ⟨(‖z.val.2‖ : ℂ)⁻¹ • z.val.2, by
      simp only [S, Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)⟩
    refine ⟨⟨(z.val.1,y), hsmul _ _ _ z.property.1⟩, ?_⟩
    apply Subtype.ext
    refine Prod.ext rfl ?_
    change (L z.val.1 ((‖z.val.2‖ : ℂ)⁻¹ • z.val.2))⁻¹ •
      ((‖z.val.2‖ : ℂ)⁻¹ • z.val.2) = z.val.2
    simp [map_smul, z.property.2, smul_smul, hc]
  have hclosed : IsClosed {z : T × S | H z.1 z.2.val} :=
    hH.preimage (show Continuous (fun z : T × S => (z.1,z.2.val)) by fun_prop)
  have hp : IsProperMap (fun z : Q => z.val.1) :=
    isProperMap_fst_of_compactSpace.comp hclosed.isProperMap_subtypeVal
  exact isProperMap_of_comp_of_surj hq (by fun_prop) hp hsurj

end PermanentBorder.Polar

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Polar
open Topology Set


theorem solution : type_of% @_root_.OAI.PermanentBorder.Polar.homogeneous_normalized_proper := @_root_.OAI.PermanentBorder.Polar.homogeneous_normalized_proper
