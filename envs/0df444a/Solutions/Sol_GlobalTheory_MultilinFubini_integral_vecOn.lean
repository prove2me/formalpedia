-- Prove2me | solution 1 for GlobalTheory.MultilinFubini.integral_vecOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:07:53.558803+00:00
-- url     : https://prove2.me/submissions/b0d6580b-2d3d-4d32-86bf-2bc20f5148cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralContinuousMultilinearMapPiMeasure
import Theorems.Thm_GlobalTheory_MultilinFubini_integrable_vecOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.MultilinFubini
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ i, MeasurableSpace (X i)]
  {E : ι → Type} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace GlobalTheory.MultilinFubini
theorem _root_.solution (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, CompleteSpace (E i)] [CompleteSpace F]
    (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i) (hg : ∀ i, Integrable (g i) (μ i))
    (s : Finset ι) : ∀ m : ∀ i, E i,
    ∫ x, Φ (vecOn g s m x) ∂(Measure.pi fun i : s => μ i) =
      Φ (fun i => if i ∈ s then ∫ y, g i y ∂μ i else m i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro m
    rw [Measure.pi_of_empty (x := fun i => isEmptyElim i)]
    have hc : (fun x : ∀ i : (∅ : Finset ι), X i => Φ (vecOn g ∅ m x)) = fun _ => Φ m := by
      funext x; congr 1
    rw [hc]; simp
  | insert a s ha ih =>
    intro m
    rw [Finset.insert_eq]
    have hd : Disjoint ({a} : Finset ι) s := Finset.disjoint_singleton_left.2 ha
    have hmp := measurePreserving_piFinsetUnion hd μ
    letI : Unique ↥({a} : Finset ι) :=
      ⟨⟨⟨a, Finset.mem_singleton_self a⟩⟩, fun j => Subtype.ext (Finset.mem_singleton.1 j.2)⟩
    have hpt : ∀ p : (∀ i : ({a} : Finset ι), X i) × (∀ i : s, X i),
        vecOn g ({a} ∪ s) m (MeasurableEquiv.piFinsetUnion X hd p) =
          vecOn g s (Function.update m a (g a (p.1 default))) p.2 := by
      rintro ⟨y, z⟩
      have he : (MeasurableEquiv.piFinsetUnion X hd (y, z) : ∀ i : ↥({a} ∪ s), X i) =
          Equiv.piFinsetUnion X hd (y, z) := rfl
      funext i
      by_cases hia : i = a
      · subst hia
        have h1 : i ∈ ({i} : Finset ι) ∪ s := by simp
        simp only [vecOn, dif_pos h1, dif_neg ha, Function.update_self, he]
        rw [Equiv.piFinsetUnion_left X hd (Finset.mem_singleton_self i)]
        rfl
      · by_cases his : i ∈ s
        · have h1 : i ∈ ({a} : Finset ι) ∪ s := by simp [his]
          simp only [vecOn, dif_pos h1, dif_pos his, he]
          rw [Equiv.piFinsetUnion_right X hd his]
        · have h1 : i ∉ ({a} : Finset ι) ∪ s := by simp [his, hia]
          simp only [vecOn, dif_neg h1, dif_neg his, Function.update_of_ne hia]
    have hint : Integrable (fun p => Φ (vecOn g ({a} ∪ s) m (MeasurableEquiv.piFinsetUnion X hd p)))
        ((Measure.pi fun i : ({a} : Finset ι) => μ i).prod (Measure.pi fun i : s => μ i)) :=
      (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2
        (integrable_vecOn μ Φ g hg _ m)
    rw [← hmp.integral_comp', integral_prod _ hint]
    simp only [hpt, ih]
    set w : ∀ i, E i := fun i => if i ∈ s then ∫ y, g i y ∂μ i else m i with hw
    have hupd : ∀ c : E a, (fun i => if i ∈ s then ∫ y, g i y ∂μ i else Function.update m a c i) =
        Function.update w a c := by
      intro c; funext i
      by_cases hia : i = a
      · subst hia; simp [hw, ha]
      · by_cases his : i ∈ s
        · simp [hw, his, Function.update_of_ne hia]
        · simp [hw, his, Function.update_of_ne hia]
    simp only [hupd]
    have hL : ∀ c : E a, Φ (Function.update w a c) = Φ.toContinuousLinearMap w a c := fun c => rfl
    simp only [hL]
    have h1 := (measurePreserving_piUnique (fun i : ({a} : Finset ι) => μ i)).integral_comp'
      (fun t => Φ.toContinuousLinearMap w a (g a t))
    rw [show (∫ x : ∀ i : ({a} : Finset ι), X i, Φ.toContinuousLinearMap w a (g a (x default))
        ∂Measure.pi fun i : ({a} : Finset ι) => μ i) = ∫ t, Φ.toContinuousLinearMap w a (g a t) ∂μ a from h1]
    rw [(Φ.toContinuousLinearMap w a).integral_comp_comm (hg a), ← hL]
    congr 1
    funext i
    by_cases hia : i = a
    · subst hia; simp [hw]
    · by_cases his : i ∈ s
      · simp [hw, his, Function.update_of_ne hia]
      · simp [hw, his, hia, Function.update_of_ne hia]
end GlobalTheory.MultilinFubini
