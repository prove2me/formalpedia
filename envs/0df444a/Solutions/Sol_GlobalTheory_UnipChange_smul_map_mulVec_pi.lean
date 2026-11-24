-- Prove2me | solution 1 for GlobalTheory.UnipChange.smul_map_mulVec_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:49:50.371742+00:00
-- url     : https://prove2.me/submissions/88b5a11b-7808-44e9-b9be-632ec018ef25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitriangularMapInduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix
open scoped Pointwise
namespace GlobalTheory.UnipChange
section Shear
variable {k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k]
  {ι : Type} [Fintype ι]
end Shear
section Linear
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]
open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
private theorem map_mul_left_eq_smul' (a : F) (ha : a ≠ 0) :
    Measure.map (fun x => a * x) ν = distribHaarChar F (Units.mk0 a ha)⁻¹ • ν := by
  have hf : (fun x : F => a * x) = fun x => Units.mk0 a ha • x := by
    funext x; simp [Units.smul_def]
  ext s hs
  rw [Measure.map_apply (by rw [hf]; exact (continuous_const_smul _).measurable) hs, hf,
    Set.preimage_smul, ← distribHaarChar_mul ν]
  rw [Measure.coe_nnreal_smul_apply]
open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
private theorem map_diagonal_mulVec_pi (D : κ → F) (hD : ∀ i, D i ≠ 0) :
    Measure.map (diagonal D).mulVec (Measure.pi fun _ : κ => ν)
      = (∏ i, distribHaarChar F (Units.mk0 (D i) (hD i))⁻¹) • Measure.pi fun _ : κ => ν := by
  have hfun : (diagonal D).mulVec = fun x i => (fun y => D i * y) (x i) := by
    funext x i; simp [mulVec_diagonal]
  haveI : ∀ i, SigmaFinite (Measure.map (fun y => D i * y) ν) := fun i => by
    rw [map_mul_left_eq_smul' ν (D i) (hD i)]; infer_instance
  rw [hfun, Measure.pi_map_pi (f := fun i y => D i * y)
    (fun i => (continuous_const.mul continuous_id).aemeasurable)]
  simp_rw [map_mul_left_eq_smul' ν _ (hD _)]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi, ENNReal.coe_finset_prod,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => Measure.coe_nnreal_smul_apply _ _ _
open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
private theorem measurePreserving_transvection_mulVec (t : TransvectionStruct κ F) :
    MeasurePreserving t.toMatrix.mulVec (Measure.pi fun _ : κ => ν)
      (Measure.pi fun _ : κ => ν) := by
  let p : κ → Prop := fun i => i ≠ t.i
  let α : Type := { x // p x }
  let β : Type := { x // ¬p x }
  let g : (α → F) → (β → F) → β → F := fun a b => (fun _ => t.c * a ⟨t.j, t.hij.symm⟩) + b
  let G : (α → F) × (β → F) → (α → F) × (β → F) := fun q => (id q.1, g q.1 q.2)
  let e : (κ → F) ≃ᵐ (α → F) × (β → F) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : κ => F) p
  have hmv : t.toMatrix.mulVec = e.symm ∘ G ∘ e := by
    cases t with | mk i j hij c =>
    ext f k
    by_cases h : i = k
    · subst h
      simp [e, G, g, p, TransvectionStruct.toMatrix, transvection, mulVec, dotProduct,
        add_mul, Finset.sum_add_distrib, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd, Matrix.single, ite_and, Matrix.one_apply, ite_mul]
      ring
    · simp [e, G, g, p, TransvectionStruct.toMatrix, transvection, mulVec, dotProduct,
        add_mul, Finset.sum_add_distrib, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd, h, Matrix.single, ite_and, Ne.symm h, Matrix.one_apply,
        ite_mul]
  rw [hmv]
  have hA : MeasurePreserving e (Measure.pi fun _ : κ => ν)
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : κ => ν) p
  have hB : MeasurePreserving G ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν))
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν)) := by
    have hg : Measurable (Function.uncurry g) := by
      refine Measurable.add ?_ measurable_snd
      exact measurable_pi_lambda _ fun _ =>
        ((measurable_pi_apply _).comp measurable_fst).const_mul _
    exact (MeasurePreserving.id _).skew_product hg
      (Filter.Eventually.of_forall fun a => map_add_left_eq_self _ _)
  exact ((hA.symm e).comp hB).comp hA
end Linear
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointRadical
section Algebra
variable {k : Type} [Field k] {r : ℕ} {b : Fin r → ℕ}
end Algebra
section Top
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]
  {r : ℕ} {b : Fin r → ℕ}
end Top
end GlobalTheory.UnipChange
end

set_option autoImplicit false
open MeasureTheory Matrix
open scoped Pointwise
open GlobalTheory GlobalTheory.UnipChange
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]
open MeasureTheory Matrix
open scoped Pointwise
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.UnipChange
namespace _root_.GlobalTheory.UnipChange
theorem _root_.solution (M : Matrix κ κ F) (u : Fˣ)
    (hu : (u : F) = M.det) :
    (distribHaarChar F u : ENNReal) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν)
      = Measure.pi fun _ : κ => ν := by
  have hmeas : ∀ N : Matrix κ κ F, Measurable N.mulVec := fun N =>
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have key : ∀ u : Fˣ, (u : F) = M.det → Measure.map M.mulVec (Measure.pi fun _ : κ => ν)
      = distribHaarChar F u⁻¹ • Measure.pi fun _ : κ => ν := by
    refine diagonal_transvection_induction_of_det_ne_zero (fun N : Matrix κ κ F => ∀ u : Fˣ,
      (u : F) = N.det → Measure.map N.mulVec (Measure.pi fun _ : κ => ν)
        = distribHaarChar F u⁻¹ • Measure.pi fun _ : κ => ν) M
      (hu ▸ u.ne_zero) ?_ ?_ ?_
    · intro D hD u hu
      have hD' : ∀ i, D i ≠ 0 := fun i => by
        rw [det_diagonal] at hD
        exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
      rw [map_diagonal_mulVec_pi ν D hD']
      have hu' : u = ∏ i, Units.mk0 (D i) (hD' i) := by
        ext
        rw [hu, det_diagonal, Units.coe_prod]
        rfl
      rw [hu', ← Finset.prod_inv_distrib, map_prod]
    · intro t u hu
      have hu' : u = 1 := by
        ext
        rw [hu, TransvectionStruct.det, Units.val_one]
      rw [hu', inv_one, map_one, one_smul]
      exact (measurePreserving_transvection_mulVec ν t).map_eq
    · intro A B hA hB hPA hPB u hu
      have hcomp : (A * B).mulVec = A.mulVec ∘ B.mulVec :=
        funext fun x => (mulVec_mulVec x A B).symm
      have hu' : u = Units.mk0 _ hA * Units.mk0 _ hB := by
        ext
        simp [hu, det_mul]
      rw [hcomp, ← Measure.map_map (hmeas A) (hmeas B), hPB (Units.mk0 _ hB) rfl,
        Measure.map_smul, hPA (Units.mk0 _ hA) rfl, smul_smul, hu', _root_.mul_inv_rev, map_mul,
        mul_comm]
  rw [key u hu]
  ext s hs
  rw [Measure.smul_apply, Measure.coe_nnreal_smul_apply, smul_eq_mul, ← mul_assoc,
    ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one, one_mul]
end _root_.GlobalTheory.UnipChange
end GlobalTheory.UnipChange
