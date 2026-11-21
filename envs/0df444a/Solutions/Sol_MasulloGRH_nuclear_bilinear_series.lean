-- Prove2me | solution 1 for MasulloGRH.nuclear_bilinear_series
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:19:25.786184+00:00
-- url     : https://prove2.me/submissions/6b68d5df-b198-418a-8383-4e576c82f2fb

import Theorems.Thm_MasulloGRH_nuclear_banach_map_representation

open MasulloGRH Set Filter Topology Bornology
universe u

-- Keep the original topology on E while giving a second copy the pseudonorm p.
private def SeminormModel {E : Type*} [AddCommGroup E] [Module ℂ E] (_ : Seminorm ℂ E) := E

private noncomputable instance modelGroup {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : Seminorm ℂ E) : SeminormedAddCommGroup (SeminormModel p) := p.toAddGroupSeminorm.toSeminormedAddCommGroup

private noncomputable instance modelSpace {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : Seminorm ℂ E) : NormedSpace ℂ (SeminormModel p) :=
  { (inferInstance : Module ℂ E) with norm_smul_le := fun a x => (map_smul_eq_mul p a x).le }


private theorem continuous_of_seminorm_bound {E H : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [SeminormedAddCommGroup H] [NormedSpace ℂ H]
    (p : Seminorm ℂ E) (hp : Continuous p) (u : E →ₗ[ℂ] H) (hu : ∀ x, ‖u x‖ ≤ p x) :
    Continuous u := by
  apply continuous_of_continuousAt_zero u
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(hp.tendsto 0).eventually_lt_const (show p 0 < ε by simpa using hε)] with x hx
  simpa using (hu x).trans_lt hx

private theorem equicont_of_bound {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (f : ℕ → StrongDual ℂ E) (p : Seminorm ℂ E) (hp : Continuous p) (h : ∀ n x, ‖f n x‖ ≤ p x) :
    Equicontinuous (fun n => (f n : E → ℂ)) := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have he := ((norm_withSeminorms ℂ ℂ).equicontinuous_TFAE (fun n => (f n).toLinearMap)).out 3 1
  apply he.mp
  intro i
  exact ⟨p,hp,h⟩

theorem solution (E F : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] (hE : IsNuclear E)
    (p : Seminorm ℂ E) (hp : Continuous p) (r : Seminorm ℂ F)
    (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (hB : ∀ x y, ‖B x y‖ ≤ p x * r y) :
    ∃ (φ : ℕ → StrongDual ℂ E) (ψ : ℕ → F →ₗ[ℂ] ℂ) (c : ℕ → ℂ),
      Equicontinuous (fun m => (φ m : E → ℂ)) ∧ (∀ m y, ‖ψ m y‖ ≤ r y) ∧
      Summable (fun m => ‖c m‖) ∧
      ∀ x y, HasSum (fun m => c m * φ m x * ψ m y) (B x y) := by
  obtain ⟨ι,_,P,hP⟩ := hE.1.1
  let := hP.topologicalAddGroup
  let := hP.continuousSMul
  let j : F →ₗ[ℂ] SeminormModel r := LinearMap.id
  let H := StrongDual ℂ (SeminormModel r)
  let : NormedAddCommGroup H := NormedAddCommGroup.ofSeparation fun f hf => by
    ext y
    have h := f.le_opNorm y
    rw [hf,zero_mul] at h
    exact norm_le_zero_iff.mp h
  let b (x : E) : SeminormModel r →ₗ[ℂ] ℂ := B x
  let L (x : E) : H := (b x).mkContinuous (p x) (fun y => hB x y)
  let A : E →ₗ[ℂ] H := {
    toFun := L
    map_add' := fun x y => ContinuousLinearMap.ext fun z => by
      change B (x + y) z = B x z + B y z
      rw [map_add]
      rfl
    map_smul' := fun a x => ContinuousLinearMap.ext fun z => by
      change B (a • x) z = a • B x z
      rw [map_smul]
      rfl }
  have hb (x : E) : ‖A x‖ ≤ p x := (b x).mkContinuous_norm_le (apply_nonneg p x) (fun y => hB x y)
  let u : E →L[ℂ] H := ⟨A,continuous_of_seminorm_bound p hp A hb⟩
  obtain ⟨s,φ,v,c,hs,hφ,hv,hc,hexp⟩ := nuclear_banach_map_representation E H hE u

  let ψ (n : ℕ) : F →ₗ[ℂ] ℂ := (v n).toLinearMap.comp j
  have hψ (n : ℕ) (y : F) : ‖ψ n y‖ ≤ r y := by
    change ‖v n (j y)‖ ≤ r y
    exact ((v n).le_of_opNorm_le (hv n) (j y)).trans (by simp [j]; rfl)
  refine ⟨φ,ψ,c,equicont_of_bound φ s hs hφ,hψ,hc,?_⟩
  intro x y
  exact (ContinuousLinearMap.apply ℂ ℂ (j y)).hasSum (hexp x)
