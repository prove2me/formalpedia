-- Prove2me | solution 1 for NoHair.global_isometry_of_flat_end_developing_cover
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:01:11.458774+00:00
-- url     : https://prove2.me/submissions/d8aea485-1338-45ac-be5c-771234635eb4

import Theorems.Thm_NoHair_euclidean_deck_trivial_at_infinity
import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

private abbrev I := 𝓘(ℝ,ADMPoint)

theorem solution (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    (d : FlatEndDevelopingMap Q) :
    ∃ f : Q ≃ᵢ ADMPoint, ContMDiff 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f ∧
      ContMDiff 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) ∞ f.symm ∧
      ∀ (q : Q) (v w : TangentSpace 𝓘(ℝ,ADMPoint) q),
        inner ℝ (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) f q v)
          (mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) f q w) = inner ℝ v w := by
  classical
  obtain ⟨R,sheet⟩ := d.sheet
  have inj : Function.Injective d.proj := by
    intro x y eq
    obtain ⟨γ,hy,pres⟩ := d.deck x y eq
    exact (euclidean_deck_trivial_at_infinity d.proj R sheet γ pres x).symm.trans hy
  have sur : Function.Surjective d.proj := fun q => by
    obtain ⟨x,hx,_⟩ := d.liftDistance 0 q
    exact ⟨x,hx⟩
  let f := d.localDiffeo.diffeomorphOfBijective ⟨inj,sur⟩
  have same : (f : ADMPoint → Q) = d.proj := rfl
  have iso : Isometry (f : ADMPoint → Q) := by
    apply Isometry.of_dist_eq
    intro x y
    obtain ⟨z,hz,hd⟩ := d.liftDistance x (d.proj y)
    rw [inj hz] at hd
    exact hd.symm
  let F : ADMPoint ≃ᵢ Q := ⟨f.toEquiv,iso⟩
  refine ⟨F.symm,f.symm.contMDiff,f.contMDiff,?_⟩
  intro q
  obtain ⟨x,rfl⟩ := sur q
  intro v w
  let q := d.proj x
  have back (v : TangentSpace I q) : mfderiv I I d.proj (f.symm q) (mfderiv I I f.symm q v) = v := by
    have chain := mfderiv_comp (I':=I) q (f.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (f.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    have et : (f : ADMPoint → Q) ∘ (f.symm : Q → ADMPoint) = id := by funext z; exact f.apply_symm_apply z
    rw [et,mfderiv_id] at chain
    exact (congrArg (fun L : TangentSpace I q →L[ℝ] TangentSpace I (f (f.symm q)) => L v) chain).symm
  have xb : f.symm q = x := f.symm_apply_apply x
  have bx (u : TangentSpace I (d.proj x)) : mfderiv I I d.proj x (mfderiv I I f.symm q u) = u := by
    have move := congrArg (fun z : ADMPoint => (mfderiv I I d.proj z (mfderiv I I f.symm q u) : ADMPoint)) xb
    exact move.symm.trans (back u)
  have h := d.innerMap x (mfderiv I I f.symm q v) (mfderiv I I f.symm q w)
  rw [bx,bx] at h
  exact h.symm
