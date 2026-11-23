-- Prove2me | solution 1 for NoHair.asymptoticallyFlatEnd_timelike_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T07:02:35.163042+00:00
-- url     : https://prove2.me/submissions/10454bc8-e8b6-49c5-b6a8-735d0ca6cd1c

import Definitions.Def_NoHair_spacetime

open NoHair Set
open scoped ContDiff Manifold

noncomputable section

private abbrev I4 := 𝓘(ℝ,E4)
private lemma open_region (R : ℝ) : IsOpen (exteriorRegion R) := by
  apply isOpen_lt continuous_const
  unfold spatialRadius
  fun_prop

private lemma orbit_in_chart {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold I4 ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ) (y : E4) (hy : y ∈ exteriorRegion E.R) :
    flowGenerator φ (E.ψ y) = mfderiv I4 I4 E.ψ y (coordBasis 0) := by
  let l (s : ℝ) := y + s • coordBasis 0
  have hl : HasDerivAt l (coordBasis 0) 0 := by
    simpa [l] using (((hasDerivAt_id (0:ℝ)).smul_const (coordBasis 0)).const_add y)
  have h0 : l 0 = y := by simp [l]
  obtain ⟨χ,_,_,_,_,hψ,_⟩ := E.diffeo
  have hmd := ((hψ y hy).contMDiffAt ((open_region E.R).mem_nhds hy)).mdifferentiableAt (by simp)
  have hd : MDifferentiableAt I4 I4 E.ψ (l 0) := h0 ▸ hmd
  have he : (fun s => φ s (E.ψ y)) = E.ψ ∘ l := funext (fun s => (E.equivariant s y hy).symm)
  unfold flowGenerator
  rw [he, mfderiv_comp (I' := I4) 0 hd hl.differentiableAt.mdifferentiableAt]
  change mfderiv I4 I4 E.ψ (l 0) (mfderiv 𝓘(ℝ,ℝ) I4 l 0 1) = _
  rw [h0, mfderiv_eq_fderiv]
  exact congrArg (mfderiv I4 I4 E.ψ y) hl.deriv

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (R : ℝ) (hR : E.R ≤ R) (hC : E.C ≤ R) :
    ∃ E' : AsymptoticallyFlatEnd g F φ,
      E'.R = R ∧ E'.ψ = E.ψ ∧ E'.C = E.C ∧ E'.region = E.ψ '' exteriorRegion R ∧
      ∀ x ∈ E'.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0 := by
  let S := exteriorRegion E.R
  let A := exteriorRegion R
  have sub : A ⊆ S := fun _ hy => lt_of_le_of_lt hR hy
  have ims : E.ψ '' A ⊆ E.region := image_mono sub
  obtain ⟨χ,hmap,hχ,hl,hr,hs,ht⟩ := E.diffeo
  have eq : E.ψ '' A = E.region ∩ χ ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hmap (sub hy), by change χ (E.ψ y) ∈ A; rwa [hl (sub hy)]⟩
    · rintro ⟨hx,hy⟩
      exact ⟨χ x,hy,hr hx⟩
  have op : IsOpen (E.ψ '' A) := eq ▸ ht.continuousOn.isOpen_inter_preimage E.isOpen_image (open_region R)
  let E' : AsymptoticallyFlatEnd g F φ := {
    R := R
    ψ := E.ψ
    C := E.C
    R_pos := E.R_pos.trans_le hR
    diffeo := by
      refine ⟨χ,mapsTo_image _ _,?_,fun y hy => hl (sub hy),fun x hx => hr (ims hx),hs.mono sub,ht.mono ims⟩
      rintro _ ⟨y,hy,rfl⟩
      rwa [hl (sub hy)]
    isOpen_image := op
    equivariant := fun s y hy => E.equivariant s y (sub hy)
    metric_decay := fun y hy => E.metric_decay y (sub hy)
    metric_deriv_decay := fun y hy => E.metric_deriv_decay y (sub hy)
    field_decay := fun y hy => E.field_decay y (sub hy) }
  refine ⟨E',rfl,rfl,rfl,rfl,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  change g (E.ψ y) (flowGenerator φ (E.ψ y)) (flowGenerator φ (E.ψ y)) < 0
  rw [orbit_in_chart E y (sub hy)]
  change pullbackCoeffs g E.ψ y 0 0 < 0
  have est := E.metric_decay y (sub hy) 0 0
  have flat : minkowski 0 0 = -1 := by simp [minkowski]
  rw [flat] at est
  have rpos : 0 < spatialRadius y := (E.R_pos.trans_le hR).trans hy
  have fac : E.C / spatialRadius y < 1 := (div_lt_one rpos).2 (hC.trans_lt hy)
  linarith only [(le_abs_self _).trans est,fac]
