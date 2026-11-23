-- Prove2me | solution 1 for NoHair.smooth_completion_atlas_from_reflected_static_point_chart
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T13:04:11.032913+00:00
-- url     : https://prove2.me/submissions/533c1d4b-a6d8-4bac-9540-db519de0c010

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

open Metric UniformSpace IsManifold
private abbrev X := ADMPoint
private abbrev I := 𝓘(ℝ,X)

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h) (a : StaticMinusPointChart Ω N h)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0))
    (p : UniformSpace.Completion d.carrier) (off : ∀ q:d.carrier, (q : UniformSpace.Completion d.carrier) ≠ p)
    (exhaust : ∀ w : UniformSpace.Completion d.carrier, w=p ∨ ∃ q:d.carrier, (q : UniformSpace.Completion d.carrier)=w)
    (e : OpenPartialHomeomorph ADMPoint (UniformSpace.Completion d.carrier))
    (ball : e.source=Metric.ball 0 a.radius) (center : e 0=p)
    (agrees : ∀ y ∈ a.change.source, e y=((d.side false).symm (a.change y) : UniformSpace.Completion d.carrier)) :
    ∃ ch : ChartedSpace ADMPoint (UniformSpace.Completion d.carrier), letI := ch
      IsManifold 𝓘(ℝ,ADMPoint) ∞ (UniformSpace.Completion d.carrier) ∧ e.symm ∈ atlas ADMPoint (UniformSpace.Completion d.carrier) ∧
      ∀ z ∈ atlas ADMPoint d.carrier, ∃ z' ∈ atlas ADMPoint (UniformSpace.Completion d.carrier),
        z'.source = (fun q:d.carrier => (q:(UniformSpace.Completion d.carrier))) '' z.source ∧ z'.target = z.target ∧
        (∀ q:d.carrier, z' (q:(UniformSpace.Completion d.carrier))=z q) ∧ (∀ x:ADMPoint, z'.symm x=(z.symm x:(UniformSpace.Completion d.carrier))) := by
  classical
  let C := Completion d.carrier
  let inc := fun q:d.carrier => (q : C)
  have ran : range inc=({p}:Set C)ᶜ := by
    ext y
    exact ⟨fun ⟨q,hq⟩ eq => off q (hq.trans eq),fun h => (exhaust y).resolve_left h⟩
  have oe : Topology.IsOpenEmbedding inc := ⟨(Completion.isUniformEmbedding_coe d.carrier).isEmbedding,
    by rw [ran]; exact isOpen_compl_singleton⟩
  let lift := fun z : OpenPartialHomeomorph d.carrier X => z.lift_openEmbedding oe
  let U := insert e.symm (lift '' atlas X d.carrier)
  let t := a.change.trans (d.side false).symm
  have ts : t.source=a.change.source := by
    change a.change.source ∩ a.change ⁻¹' (d.side false).target=a.change.source
    rw [d.target]; exact inter_eq_left.mpr (fun z hz => a.inside (a.change.map_source hz))
  have old (z:OpenPartialHomeomorph d.carrier X) (q:d.carrier) : lift z (inc q)=z q := z.lift_openEmbedding_apply oe
  have oldinv (z:OpenPartialHomeomorph d.carrier X) (x:X) : (lift z).symm x = inc (z.symm x) := rfl
  have oldmem {z:OpenPartialHomeomorph d.carrier X} {q:d.carrier} : inc q∈(lift z).source ↔ q∈z.source := by
    change inc q ∈ inc '' z.source ↔ q∈z.source
    exact oe.injective.mem_set_image
  have point : p∈e.target := by
    rw [←center]
    apply e.map_source; rw [ball]; exact mem_ball_self a.positive
  have cap {y:X} (hy:y∈t.source) : e y=inc (t y) := agrees y (ts ▸ hy)
  have ins {y:X} (hy:y∈e.source) (rg:e y∈range inc) : y∈t.source := by
    rw [ts,a.source,←ball]
    refine ⟨hy,?_⟩
    intro eq
    change y=0 at eq
    obtain ⟨q,hq⟩ := rg
    exact off q (hq.trans (eq ▸ center))
  have eb {y:X} (hy:y∈t.source) : y∈e.source := by
    rw [ball]; rw [ts,a.source] at hy; exact hy.1
  have inverseOld {q:d.carrier} (hq:q∈t.target) : e.symm (inc q)=t.symm q := by
    have b := t.map_target hq
    have eq := (cap b).trans (congrArg inc (t.right_inv hq))
    rw [←eq,e.left_inv (eb b)]
  have between {q:d.carrier} (hq:inc q∈e.target) : q∈t.target := by
    let y := e.symm (inc q)
    have ey : e y=inc q := e.right_inv hq
    have hy : y∈t.source := ins (e.map_target hq) ⟨q,ey.symm⟩
    have eq : q=t y := oe.injective (ey.symm.trans (cap hy))
    rw [eq]; exact t.map_source hy
  have tm : ContMDiffOn I I ∞ t t.source :=
    (d.smoothInverse false).comp ((contMDiffOn_iff_contDiffOn.mpr a.smoothChange).mono inter_subset_left)
      (fun _ hy => hy.2)
  have ti : ContMDiffOn I I ∞ t.symm t.target :=
    (contMDiffOn_iff_contDiffOn.mpr a.smoothInverse).comp ((d.smoothSide false).mono inter_subset_left)
      (fun _ hy => hy.2)
  have oldSmooth {z:OpenPartialHomeomorph d.carrier X} (hz:z∈atlas X d.carrier) :
      ContMDiffOn I I ∞ z z.source ∧ ContMDiffOn I I ∞ z.symm z.target := by
    have h := IsManifold.subset_maximalAtlas (I:=I) (n:=∞) hz
    exact ⟨contMDiffOn_of_mem_maximalAtlas h,contMDiffOn_symm_of_mem_maximalAtlas h⟩
  have cover (w:C) : ∃ z∈U,w∈z.source := by
    obtain eq|⟨q,rfl⟩ := exhaust w
    · exact ⟨e.symm,Or.inl rfl,eq ▸ point⟩
    · exact ⟨lift (chartAt X q),Or.inr ⟨_,chart_mem_atlas X q,rfl⟩,oldmem.mpr (mem_chart_source X q)⟩
  choose chosen member domain using cover
  let ch : ChartedSpace X C := {atlas:=U,chartAt:=chosen,mem_chart_source:=domain,chart_mem_atlas:=member}
  have compat (z w: OpenPartialHomeomorph C X) (hz:z∈U) (hw:w∈U) :
      ContDiffOn ℝ ∞ (z.symm.trans w) (z.symm.trans w).source := by
    rcases hz with rfl|⟨v,hv,rfl⟩ <;> rcases hw with rfl|⟨u,hu,rfl⟩
    · apply (contDiffOn_id : ContDiffOn ℝ ∞ id _).congr
      intro x hx; exact e.left_inv hx.1
    · intro x hx
      have hd (x:X) (h:x∈(e.trans (lift u)).source) : x∈t.source :=
        ins h.1 (by obtain ⟨q,_,eq⟩ := h.2; exact ⟨q,eq⟩)
      have htx := hd x hx
      have uq : t x∈u.source := oldmem.mp (by rw [←cap htx]; exact hx.2)
      have sm := ((oldSmooth hu).1.contMDiffAt (u.open_source.mem_nhds uq)).comp x
        (tm.contMDiffAt (t.open_source.mem_nhds htx))
      apply ((contMDiffAt_iff_contDiffAt.mp sm).congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [(e.trans (lift u)).open_source.mem_nhds hx] with y hy
      change lift u (e y)=u (t y)
      rw [cap (hd y hy),old]
    · intro x hx
      have hq := between (q:=v.symm x) hx.2
      have sm := (ti.contMDiffAt (t.open_target.mem_nhds hq)).comp x
        ((oldSmooth hv).2.contMDiffAt (v.open_target.mem_nhds hx.1))
      apply ((contMDiffAt_iff_contDiffAt.mp sm).congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [((lift v).symm.trans e.symm).open_source.mem_nhds hx] with y hy
      exact inverseOld (q:=v.symm y) (between hy.2)
    · intro x hx
      have uq : v.symm x ∈ u.source := oldmem.mp hx.2
      have sm := ((oldSmooth hu).1.contMDiffAt (u.open_source.mem_nhds uq)).comp x
        ((oldSmooth hv).2.contMDiffAt (v.open_target.mem_nhds hx.1))
      apply ((contMDiffAt_iff_contDiffAt.mp sm).congr_of_eventuallyEq ?_).contDiffWithinAt
      exact .of_forall (fun y => old u (v.symm y))
  letI := ch
  have m : IsManifold I ∞ C := by
    apply isManifold_of_contDiffOn
    intro z w hz hw
    first
    | simpa only [I,modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,
        preimage_id_eq,id_eq,Set.range_id,Set.inter_univ] using compat z w hz hw
    | apply (ContDiffOn.congr ((compat z w hz hw).mono (fun x hx => hx.1)))
      intro x hx
      rfl
  refine ⟨ch,m,Or.inl rfl,?_⟩
  intro z hz
  exact ⟨lift z,Or.inr ⟨z,hz,rfl⟩,rfl,rfl,old z,oldinv z⟩
