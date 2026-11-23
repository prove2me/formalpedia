-- Prove2me | solution 1 for NoHair.asymptotically_flat_end_proper_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:15:55.900323+00:00
-- url     : https://prove2.me/submissions/ea1d485c-5d51-4a43-bcf7-05977f5acd68

import Theorems.Thm_NoHair_asymptotically_flat_spatial_coordinates_escape
import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

private abbrev X := ADMPoint
private abbrev S := ADMSphere
open Metric

theorem solution (Q : Type) [m : MetricSpace Q] [ch : ChartedSpace ADMPoint Q] [sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [sr : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [rm : IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [cm : CompleteSpace Q] [cn : ConnectedSpace Q]
    [sc : SecondCountableTopology Q]
    (hend : HasScalarFlatZeroADMEnd Q) :
    ∃ e : ADMSphere × ℝ → Q, Topology.IsOpenEmbedding e ∧
      ∀ K : Set Q, IsCompact K → ∃ T : ℝ, ∀ n : ADMSphere, ∀ t : ℝ, T<t → e (n,t) ∉ K := by
  obtain ⟨R,e,rp,src,far⟩ := asymptotically_flat_spatial_coordinates_escape Q hend
  let Y := {x : X | R<‖x‖}
  let f := fun z : S × ℝ => (R+Real.exp z.2) • (z.1 : X)
  have cf : Continuous f := (continuous_const.add (Real.continuous_exp.comp continuous_snd)).smul
    (continuous_subtype_val.comp continuous_fst)
  have unit (n:S) : ‖(n:X)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using n.property
  have nf (z : S × ℝ) : ‖f z‖=R+Real.exp z.2 := by
    have pos := add_pos rp (Real.exp_pos z.2)
    simp only [f,norm_smul,Real.norm_eq_abs,abs_of_pos pos,unit,mul_one]
  have fy (z : S × ℝ) : f z∈e.source := by rw [src]; change R<‖f z‖; rw [nf]; linarith only [Real.exp_pos z.2]
  have farSource (z : X) (hz : z∈e.source) : R<‖z‖ := by rwa [src] at hz
  have yn (y : e.source) : R<‖y.val‖ := farSource y.val y.property
  let g := fun y : e.source => ‖y.val‖⁻¹ • y.val
  have gn (y : e.source) : ‖g y‖=1 := by
    have nz := (rp.trans (yn y)).ne'
    simp [g,norm_smul,nz]
  let h : S × ℝ ≃ₜ e.source :=
    { toFun := fun z => ⟨f z,fy z⟩
      invFun := fun y => (⟨g y,by simpa only [mem_sphere,dist_zero_right] using gn y⟩,
        Real.log (‖y.val‖-R))
      left_inv := by
        rintro ⟨n,t⟩
        apply Prod.ext
        · apply Subtype.ext
          change ‖f (n,t)‖⁻¹ • ((R+Real.exp t) • (n:X)) = (n:X)
          rw [nf,smul_smul,inv_mul_cancel₀ (add_pos rp (Real.exp_pos t)).ne',one_smul]
        · change Real.log (‖f (n,t)‖-R)=t
          rw [nf,add_sub_cancel_left,Real.log_exp]
      right_inv := by
        intro y
        apply Subtype.ext
        change (R+Real.exp (Real.log (‖y.val‖-R))) • (‖y.val‖⁻¹ • y.val) = y.val
        rw [Real.exp_log (sub_pos.mpr (yn y)),add_sub_cancel,smul_smul,mul_inv_cancel₀ (rp.trans (yn y)).ne',one_smul]
      continuous_toFun := cf.subtype_mk fy
      continuous_invFun := by
        have v : Continuous (fun y : e.source => ‖y.val‖⁻¹ • y.val) :=
          (continuous_subtype_val.norm.inv₀ (fun y => (rp.trans (yn y)).ne')).smul continuous_subtype_val
        exact (v.subtype_mk _).prodMk ((continuous_subtype_val.norm.sub continuous_const).log (fun y => (sub_pos.mpr (yn y)).ne')) }
  let E := fun z : S × ℝ => e (f z)
  have isc : Topology.IsOpenEmbedding E :=
    e.open_target.isOpenEmbedding_subtypeVal.comp (e.toHomeomorphSourceTarget.isOpenEmbedding.comp h.isOpenEmbedding)
  refine ⟨E,isc,?_⟩
  intro K compact
  obtain ⟨T,hT⟩ := far K compact
  refine ⟨T,fun n t ht => hT _ ?_⟩
  change T<‖f (n,t)‖
  rw [nf]
  linarith only [Real.add_one_le_exp t,rp,ht]
