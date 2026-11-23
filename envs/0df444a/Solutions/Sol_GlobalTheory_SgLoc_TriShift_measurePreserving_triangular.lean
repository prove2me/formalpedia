-- Prove2me | solution 1 for GlobalTheory.SgLoc.TriShift.measurePreserving_triangular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:57.957717+00:00
-- url     : https://prove2.me/submissions/f47745c0-abb2-4cb3-8cd1-cfeaf632ecf3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CokernelPairSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
namespace GlobalTheory.SgLoc.TriShift
section General
variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddRightInvariant]
  {ι : Type} [Fintype ι]
open ValuativeRel MeasureTheory ComplexConjugate in
open scoped ComplexOrder in
variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddRightInvariant]
  {ι : Type} [Fintype ι] in
private lemma measurePreserving_update_add_of_indep [DecidableEq ι] (i : ι)
    (g : (ι → G) → G) (hg : Measurable g)
    (hgi : ∀ x y : ι → G, (∀ j, j ≠ i → x j = y j) → g x = g y) :
    MeasurePreserving (fun x : ι → G => Function.update x i (x i + g x))
      (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : ι => μ) := by
  let p : ι → Prop := fun j => j ≠ i
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G) p
  have he : MeasurePreserving e (Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : {j // p j} => μ).prod (Measure.pi fun _ : {j // ¬ p j} => μ)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p
  let c : ({j // p j} → G) → ({j // ¬ p j} → G) := fun y _ => g (e.symm (y, 0))
  have hc : Measurable c :=
    measurable_pi_lambda _ fun _ =>
      hg.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  have hT : MeasurePreserving
      (fun q : ({j // p j} → G) × ({j // ¬ p j} → G) => (id q.1, q.2 + c q.1))
      ((Measure.pi fun _ : {j // p j} => μ).prod (Measure.pi fun _ : {j // ¬ p j} => μ))
      ((Measure.pi fun _ : {j // p j} => μ).prod (Measure.pi fun _ : {j // ¬ p j} => μ)) :=
    (MeasurePreserving.id _).skew_product (g := fun y z => z + c y)
      (measurable_snd.add (hc.comp measurable_fst))
      (Filter.Eventually.of_forall fun y => map_add_right_eq_self _ _)
  have hcomp := (MeasurePreserving.symm e he).comp (hT.comp he)
  convert hcomp using 1
  funext x j
  by_cases hj : j = i
  · subst hj
    simp [e, c, p]
    exact hgi _ _ fun k hk => by simp [hk]
  · simp [e, c, p, hj]
end General
end GlobalTheory.SgLoc.TriShift
end

set_option autoImplicit false
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.TriShift
variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddRightInvariant]
  {ι : Type} [Fintype ι]
open ValuativeRel MeasureTheory ComplexConjugate
open scoped ComplexOrder
variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddRightInvariant]
  {ι : Type} [Fintype ι]
namespace GlobalTheory.SgLoc.TriShift
namespace _root_.GlobalTheory.SgLoc.TriShift
theorem _root_.solution (rk : ι → ℕ) (f : ι → (ι → G) → G)
    (hf : ∀ i, Measurable (f i))
    (hd : ∀ i x y, (∀ j, rk j < rk i → x j = y j) → f i x = f i y) :
    MeasurePreserving (fun (x : ι → G) i => x i + f i x) (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : ι => μ) := by
  classical
  let Φ : Finset ι → (ι → G) → ι → G := fun s x j => if j ∈ s then x j + f j x else x j
  have hΦ : ∀ s, MeasurePreserving (Φ s) (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : ι => μ) := by
    intro s
    induction s using Finset.induction_on_max_value rk with
    | empty =>
      convert MeasurePreserving.id (Measure.pi fun _ : ι => μ) using 1
      funext x j
      simp [Φ]
    | insert a s ha hmax ih =>
      have hstep := measurePreserving_update_add_of_indep μ a (f a) (hf a)
        fun x y hxy => hd a x y fun j hj => hxy j (by rintro rfl; exact lt_irrefl _ hj)
      convert ih.comp hstep using 1
      funext x j
      by_cases hja : j = a
      · subst hja
        simp [Φ, ha]
      · by_cases hjs : j ∈ s
        · have hf' : f j (Function.update x a (x a + f a x)) = f j x :=
            hd j _ _ fun k hk => by
              have hka : k ≠ a := by
                rintro rfl
                exact absurd (hmax j hjs) (not_le.2 hk)
              simp [hka]
          simp [Φ, hja, hjs, hf']
        · simp [Φ, hja, hjs]
  convert hΦ Finset.univ using 1
  funext x j
  simp [Φ]
end _root_.GlobalTheory.SgLoc.TriShift
end GlobalTheory.SgLoc.TriShift
