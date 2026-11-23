-- Prove2me | solution 1 for NoHair.spacetime_chart_of_static_spatial_isometry
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:30:18.855977+00:00
-- url     : https://prove2.me/submissions/0f4288a9-a5f8-401a-bc24-6b0e79f02869

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

private abbrev X := ADMPoint
private abbrev I3 := Fin 3
private abbrev I4 := Fin 4

private lemma compose_charts {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {f : E4 → E4} {g : E4 → M} {S U : Set E4} {D : Set M}
    (hf : IsDiffeoOnto f S U) (hg : IsDiffeoOnto g U D) : IsDiffeoOnto (g ∘ f) S D := by
  obtain ⟨j, hfu, hjs, hjf, hfj, hdf, hdj⟩ := hf
  obtain ⟨k, hgd, hku, hkg, hgk, hdg, hdk⟩ := hg
  refine ⟨j ∘ k, hgd.comp hfu, hjs.comp hku, ?_, ?_, hdg.comp hdf hfu, hdj.comp hdk hku⟩
  · intro x hx
    change j (k (g (f x))) = x
    rw [hkg (hfu hx), hjf hx]
  · intro x hx
    change g (f (j (k x))) = x
    rw [hfj (hku hx), hgk hx]

private noncomputable def projS : E4 →L[ℝ] X :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : I3 => PiLp.proj 2 (fun _ : I4 => ℝ) i.succ))

private lemma proj_eq (z : E4) : projS z = conformalSpatialPoint z := by
  ext i
  fin_cases i <;> rfl

private noncomputable def pack : (ℝ × X) →L[ℝ] E4 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I4 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : I4 => Fin.cases (ContinuousLinearMap.fst ℝ ℝ X)
      (fun j => (PiLp.proj 2 (fun _ : I3 => ℝ) j).comp (ContinuousLinearMap.snd ℝ ℝ X)) i))

private noncomputable def liftMap (f : X → X) (z : E4) := pack (z 0,f (projS z))

private lemma space_pack (t : ℝ) (x : X) : projS (pack (t,x))=x := by ext i; rfl
private lemma time_pack (t : ℝ) (x : X) : (pack (t,x)) 0=t := rfl
private lemma pack_eta (v : E4) : pack (v 0,projS v)=v := by
  ext i
  exact Fin.cases rfl (fun _ => rfl) i

private lemma clift {f : X → X} {z : E4} (cf : ContDiffAt ℝ ∞ f (projS z)) :
    ContDiffAt ℝ ∞ (liftMap f) z := pack.contDiff.contDiffAt.comp z
      ((PiLp.proj 2 (fun _ : I4 => ℝ) 0).contDiff.contDiffAt.prodMk (cf.comp z projS.contDiff.contDiffAt))

private lemma dlift {f : X → X} {z : E4} (cf : DifferentiableAt ℝ f (projS z)) (v : E4) :
    fderiv ℝ (liftMap f) z v = pack (v 0,fderiv ℝ f (projS z) (projS v)) := by
  have eq := (pack.hasFDerivAt.comp z (((PiLp.proj 2 (fun _ : I4 => ℝ) 0).hasFDerivAt).prodMk
    (cf.hasFDerivAt.comp z projS.hasFDerivAt))).fderiv
  change fderiv ℝ (liftMap f) z = _ at eq
  rw [eq]
  rfl

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D)
    (V : ADMPoint → ℝ) (hV : ∀ x, x ≠ 0 → -1 < V x)
    (hs : HasStaticSpatialDoubleChart c.Ω c.N c.h V) :
    HasConformalVacuumExterior g D (fun x => 2 / (1 + V x)) := by
  classical
  obtain ⟨σ,ss,st,cs,ct,metric⟩ := hs
  let U := fun x => 2/(1+V x)
  let S := conformalExteriorDomain U
  let T := conformalSpatialPoint ⁻¹' c.Ω
  have src : S=projS ⁻¹' σ.source := by
    ext z
    rw [Set.mem_preimage,ss]
    change (conformalSpatialPoint z≠0 ∧ 2/(1+V (conformalSpatialPoint z))<2) ↔
      (projS z≠0 ∧ 0<V (projS z))
    rw [← proj_eq]
    constructor
    · rintro ⟨hz,h⟩
      refine ⟨hz,?_⟩
      have pos : 0<1+V (projS z) := by linarith only [hV _ hz]
      linarith only [(div_lt_iff₀ pos).mp h]
    · rintro ⟨hz,h⟩
      refine ⟨hz,(div_lt_iff₀ (by linarith : 0<1+V (projS z))).mpr ?_⟩
      linarith
  have tgt : T=projS ⁻¹' σ.target := by
    rw [st]
    ext z
    change conformalSpatialPoint z ∈ c.Ω ↔ projS z ∈ c.Ω
    rw [proj_eq]
  have so : IsOpen S := src ▸ σ.open_source.preimage projS.continuous
  have to' : IsOpen T := tgt ▸ σ.open_target.preimage projS.continuous
  have h₁ {z : E4} (hz : z∈S) : projS z∈σ.source := by change z ∈ projS ⁻¹' σ.source; rwa [←src]
  have h₂ {z : E4} (hz : z∈T) : projS z∈σ.target := by change z ∈ projS ⁻¹' σ.target; rwa [←tgt]
  have sp (f : X → X) (z : E4) : projS (liftMap f z)=f (projS z) := space_pack _ _
  have maps : MapsTo (liftMap σ) S T := by
    intro z hz
    rw [tgt,Set.mem_preimage,sp]
    exact σ.map_source (h₁ hz)
  have ims : MapsTo (liftMap σ.symm) T S := by
    intro z hz
    rw [src,Set.mem_preimage,sp]
    exact σ.map_target (h₂ hz)
  have smoothS (z : E4) (hz : z ∈ S) := cs.contDiffAt (σ.open_source.mem_nhds (h₁ hz))
  have hdiff : IsDiffeoOnto (liftMap σ) S T := by
    refine ⟨liftMap σ.symm,maps,ims,?_,?_,?_,?_⟩
    · intro z hz
      change pack ((liftMap σ z) 0,σ.symm (projS (liftMap σ z)))=z
      rw [sp,σ.left_inv (h₁ hz)]
      exact pack_eta z
    · intro z hz
      change pack ((liftMap σ.symm z) 0,σ (projS (liftMap σ.symm z)))=z
      rw [sp,σ.right_inv (h₂ hz)]
      exact pack_eta z
    · exact contMDiffOn_iff_contDiffOn.mpr (fun z hz => (clift (smoothS z hz)).contDiffWithinAt)
    · exact contMDiffOn_iff_contDiffOn.mpr (fun z hz =>
        (clift (ct.contDiffAt (σ.open_target.mem_nhds (h₂ hz)))).contDiffWithinAt)
  refine ⟨c.openExterior,c.ψ ∘ liftMap σ,compose_charts hdiff c.exteriorChart,?_⟩
  intro z hz v w
  have hz' : z ∈ S := hz
  have ht := maps hz'
  have dψ := (c.exteriorChart.choose_spec.2.2.2.2.1.contMDiffAt (to'.mem_nhds ht)).mdifferentiableAt (by simp)
  have dl := (contMDiffAt_iff_contDiffAt.mpr (clift (smoothS z hz'))).mdifferentiableAt (by simp)
  rw [mfderiv_comp (I' := 𝓘(ℝ,E4)) z dψ dl]
  simp only [Function.comp_apply,ContinuousLinearMap.comp_apply]
  change g (c.ψ (liftMap σ z))
    (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) c.ψ (liftMap σ z) (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) (liftMap σ) z v))
    (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) c.ψ (liftMap σ z) (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) (liftMap σ) z w)) = _
  let deriv := mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) (liftMap σ) z
  refine (c.staticMetric _ ht (deriv v) (deriv w)).trans ?_
  have val (u : E4) : deriv u = pack (u 0,fderiv ℝ σ (projS z) (projS u)) := by
    change (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) (liftMap σ) z) u = _
    rw [mfderiv_eq_fderiv]
    exact dlift ((smoothS z hz').differentiableAt (by simp)) u
  rw [val v,val w]
  have a := metric _ (h₁ hz')
  let x := projS z
  have hxσ : x ∈ σ.source := h₁ hz'
  rw [ss] at hxσ
  have hp : 0 < V x := hxσ.2
  have nz : 1+V x ≠ 0 := by linarith
  have hsp : conformalSpatialPoint (liftMap σ z)=σ x := (proj_eq _).symm.trans (sp _ _)
  let dv := fderiv ℝ σ x (projS v)
  let dw := fderiv ℝ σ x (projS w)
  let H := ∑ i : I3, ∑ j : I3, c.h (σ x) i j * dv i * dw j
  have scaled : ((1+V x)/2)^4 * H = inner ℝ (projS v) (projS w) := by
    have h := a.2 (projS v) (projS w)
    dsimp only [H,dv,dw,x]
    simp only [Finset.mul_sum]
    simpa only [staticPositiveMetric,a.1,mul_assoc] using h
  have innerEq : inner ℝ (projS v) (projS w) = v 1*w 1 + v 2*w 2 + v 3*w 3 := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Fin.sum_univ_three]
    change w 1*v 1 + w 2*v 2 + w 3*v 3 = _
    ring
  rw [hsp,a.1]
  change -(V x)^2*v 0*w 0+H = conformalStaticForm (U (conformalSpatialPoint z)) v w
  rw [← proj_eq z]
  change -(V x)^2*v 0*w 0+H = -(2/(2/(1+V x))-1)^2*v 0*w 0+
    (2/(1+V x))^4*(v 1*w 1+v 2*w 2+v 3*w 3)
  rw [←innerEq,←scaled]
  field_simp [nz]
  <;> ring
