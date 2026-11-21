-- Prove2me | solution 1 for MasulloGRH.continuous_epsTensor_map_left
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:42:07.533845+00:00
-- url     : https://prove2.me/submissions/65d3a3dd-6502-4355-af17-27b36b43a707

import Definitions.Def_MasulloGRH_LocallyConvex
open Set MasulloGRH TensorProduct TopologicalSpace
open scoped UniformConvergence
universe u

private def rectangles (F H : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] :
    Set (Set (StrongDual ℂ F × StrongDual ℂ H)) :=
  {s | ∃ (A : Set (StrongDual ℂ F)) (B : Set (StrongDual ℂ H)),
      Equicontinuous (fun a : A => (a : F → ℂ)) ∧
      Equicontinuous (fun b : B => (b : H → ℂ)) ∧ s = A ×ˢ B}

theorem solution (F G H : Type u) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] (f : F →L[ℂ] G) :
    @Continuous (F ⊗[ℂ] H) (G ⊗[ℂ] H) (epsTensorTopology F H) (epsTensorTopology G H)
      (TensorProduct.map f.toLinearMap (LinearMap.id : H →ₗ[ℂ] H)) := by
  classical
  let L := TensorProduct.map f.toLinearMap (LinearMap.id : H →ₗ[ℂ] H)
  let pull (g : StrongDual ℂ G) : StrongDual ℂ F := g.comp f
  let P := Prod.map pull (id : StrongDual ℂ H → StrongDual ℂ H)
  have hr : MapsTo (P '' ·) (rectangles G H) (rectangles F H) := by
    rintro S ⟨A, B, hA, hB, rfl⟩
    refine ⟨pull '' A, B, ?_, hB, by simp [P, prodMap_image_prod]⟩
    have hcomp : Equicontinuous (fun a : A => fun x : F => a.val (f x)) :=
      equicontinuous_iff_continuous.mpr ((equicontinuous_iff_continuous.mp hA).comp f.continuous)
    let pick (b : pull '' A) : A := ⟨b.property.choose, b.property.choose_spec.1⟩
    have he (b : pull '' A) : pull (pick b) = b.val := b.property.choose_spec.2
    convert hcomp.comp pick using 1
    funext b x
    exact (congrArg (fun g : StrongDual ℂ F => g x) (he b)).symm
  have hc := (UniformOnFun.precomp_uniformContinuous (β := ℂ) hr).continuous
  let evF (x : F ⊗[ℂ] H) := UniformOnFun.ofFun (rectangles F H) (fun ab => tensorFunctional F H ab x)
  let evG (x : G ⊗[ℂ] H) := UniformOnFun.ofFun (rectangles G H) (fun ab => tensorFunctional G H ab x)
  letI tF := epsTensorTopology F H
  have hev : Continuous evF := continuous_induced_dom
  change @Continuous _ _ tF (induced evG inferInstance) L
  apply continuous_induced_rng.mpr
  apply (hc.comp hev).congr
  intro x
  change (fun ab => tensorFunctional F H (P ab) x) = (fun ab => tensorFunctional G H ab (L x))
  funext ab
  change tensorFunctional F H (P ab) x = tensorFunctional G H ab (L x)
  simp only [tensorFunctional, L, TensorProduct.map_map, LinearMap.comp_id]
  rfl
