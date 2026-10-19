-- Prove2me | solution 1 for OAI.ClassicalON.continuousFKG_pi
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:54:28.036162+00:00
-- url     : https://prove2.me/submissions/fdee07ab-bd31-42fa-a545-f2d66a685942

import Mathlib
import Definitions.Def_OAIQWCO002

section
-- module Solutions.OAIQW_ClassicalON.AssociationCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ClassicalON

section CompactIntegral
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} [IsFiniteMeasure μ]

theorem compact_integrable {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem compact_integral_pos [IsProbabilityMeasure μ] {w : X → ℝ}
    (hw : Continuous w) (hp : ∀ x,0<w x) : 0<∫ x,w x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) (compact_integrable hw)).2
  have he : Function.support w=univ := by ext x; simp [Function.mem_support,(hp x).ne']
  rw [he,measure_univ]
  exact zero_lt_one

omit [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem compact_parametric_integral [FirstCountableTopology Y] [LocallyCompactSpace Y]
    (f : Y → X → ℝ) (hf : Continuous f.uncurry) : Continuous (fun y => ∫ x,f y x ∂μ) := by
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous hf (isCompact_univ : IsCompact (univ : Set X)))

end CompactIntegral

section Weighted
variable {X : Type uX} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
  [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {w : X → ℝ}
  (hw : Continuous w) (hp : ∀ x,0<w x)

include hw hp

theorem weightedMean_nonneg {f : X → ℝ} (hf : ∀ x,0≤f x) : 0≤weightedMean μ w f := by
  exact div_nonneg (integral_nonneg (fun x => mul_nonneg (hp x).le (hf x)))
    (compact_integral_pos hw hp).le

theorem weightedMean_mono {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x,f x≤g x) : weightedMean μ w f ≤ weightedMean μ w g := by
  exact div_le_div_of_nonneg_right
    (integral_mono (compact_integrable (hw.mul hf)) (compact_integrable (hw.mul hg))
      (fun x => mul_le_mul_of_nonneg_left (hfg x) (hp x).le)) (compact_integral_pos hw hp).le

theorem weightedMean_inequality_iff {f g : X → ℝ} :
    weightedMean μ w f * weightedMean μ w g ≤ weightedMean μ w (fun x => f x*g x) ↔
    (∫ x,w x*f x ∂μ)*(∫ x,w x*g x ∂μ) ≤ (∫ x,w x ∂μ)*(∫ x,w x*(f x*g x) ∂μ) := by
  unfold weightedMean
  have hm := compact_integral_pos (μ := μ) hw hp
  rw [div_mul_div_comm,div_le_div_iff₀ (mul_pos hm hm) hm]
  constructor <;> intro h <;> nlinarith

end Weighted

theorem continuousAssociated_chain {X : Type uX} [LinearOrder X] [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ] (w : X → ℝ)
    (hw : Continuous w) (hp : ∀ x,0<w x) : ContinuousAssociated μ w := by
  intro f g hf hg _ _ hfm hgm
  apply (weightedMean_inequality_iff hw hp).2
  have hc : ∀ x y,w x*f x*(w y*g y)+w x*g x*(w y*f y) ≤
      w x*(f x*g x)*w y+w x*(w y*(f y*g y)) := by
    intro x y
    have hdiff : 0≤(f x-f y)*(g x-g y) := by
      rcases le_total x y with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hfm h)) (sub_nonpos.mpr (hgm h))
      · exact mul_nonneg (sub_nonneg.mpr (hfm h)) (sub_nonneg.mpr (hgm h))
    have ht := mul_nonneg (mul_nonneg (hp x).le (hp y).le) hdiff
    nlinarith
  have hint := integral_mono
    (compact_integrable (μ := μ.prod μ) (show Continuous (fun p : X×X =>
      w p.1*f p.1*(w p.2*g p.2)+w p.1*g p.1*(w p.2*f p.2)) from by fun_prop))
    (compact_integrable (μ := μ.prod μ) (show Continuous (fun p : X×X =>
      w p.1*(f p.1*g p.1)*w p.2+w p.1*(w p.2*(f p.2*g p.2))) from by fun_prop))
    (fun p => hc p.1 p.2)
  rw [integral_add (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop)),
    integral_add (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop))] at hint
  rw [integral_prod_mul (fun x => w x*f x) (fun x => w x*g x),
    integral_prod_mul (fun x => w x*g x) (fun x => w x*f x),
    integral_prod_mul (fun x => w x*(f x*g x)) w,
    integral_prod_mul w (fun x => w x*(f x*g x))] at hint
  nlinarith

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.WeightedTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section
open MeasureTheory
namespace ClassicalON

section Tilt
variable {X : Type uX} [Preorder X] [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem weightedMean_tilt_mono {w v f : X → ℝ} (hw : Continuous w) (hv : Continuous v)
    (hp : ∀ x,0<w x) (hvp : ∀ x,0<v x) (hA : ContinuousAssociated μ w)
    (hf : Continuous f) (hfn : ∀ x,0≤f x) (hfm : Monotone f)
    (hr : Monotone (fun x => v x/w x)) : weightedMean μ w f ≤ weightedMean μ v f := by
  have hrc : Continuous (fun x => v x/w x) := hv.div hw (fun x => (hp x).ne')
  have h := hA f (fun x => v x/w x) hf hrc hfn
    (fun x => div_nonneg (hvp x).le (hp x).le) hfm hr
  rw [weightedMean_inequality_iff hw hp] at h
  have he1 : (fun x => w x*(v x/w x))=v := by
    funext x
    field_simp [(hp x).ne']
  have he2 : (fun x => w x*(f x*(v x/w x)))=(fun x => v x*f x) := by
    funext x
    field_simp [(hp x).ne']
  rw [he1,he2] at h
  unfold weightedMean
  exact (div_le_div_iff₀ (compact_integral_pos hw hp) (compact_integral_pos hv hvp)).2 (by nlinarith)

end Tilt

section Product
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology X] [FirstCountableTopology Y] [LocallyCompactSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology X] in
theorem marginalWeight_continuous {w : Y×X → ℝ} (hw : Continuous w) :
    Continuous (marginalWeight μ w) := compact_parametric_integral _ hw

omit [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology X]
  [FirstCountableTopology Y] [LocallyCompactSpace Y] in
theorem marginalWeight_pos {w : Y×X → ℝ} (hw : Continuous w) (hp : ∀ p,0<w p) (y : Y) :
    0 < marginalWeight μ w y := compact_integral_pos (by fun_prop) (fun x => hp (y,x))

omit [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology X] in
theorem conditionalMean_continuous {w f : Y×X → ℝ} (hw : Continuous w) (hf : Continuous f)
    (hp : ∀ p,0<w p) : Continuous (conditionalMean μ w f) := by
  exact (compact_parametric_integral _ (hw.mul hf)).div (marginalWeight_continuous μ hw)
    (fun y => (marginalWeight_pos μ hw hp y).ne')

omit [FirstCountableTopology Y] [LocallyCompactSpace Y] in
theorem weightedMean_prod {w f : Y×X → ℝ} (hw : Continuous w) (hf : Continuous f)
    (hp : ∀ p,0<w p) :
    weightedMean (ν.prod μ) w f = weightedMean ν (marginalWeight μ w) (conditionalMean μ w f) := by
  unfold weightedMean
  rw [integral_prod (fun p => w p*f p) (compact_integrable (show Continuous (fun p => w p*f p) from hw.mul hf)),
    integral_prod w (compact_integrable hw)]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  dsimp only [marginalWeight,conditionalMean,weightedMean]
  have hm : (∫ x,w (y,x) ∂μ)≠0 := (marginalWeight_pos μ hw hp y).ne'
  field_simp

end Product
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ProductFKG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section
open MeasureTheory
namespace ClassicalON

section Lattice
variable {X : Type uX} {Y : Type uY} [Lattice X] [LinearOrder Y]

theorem logSupermodular_slice {w : Y×X → ℝ} (h : LogSupermodular w) (y : Y) :
    LogSupermodular (fun x => w (y,x)) := by
  intro u v
  simpa only [Prod.inf_def,Prod.sup_def,inf_idem,sup_idem] using h (y,u) (y,v)

theorem logSupermodular_ratio_monotone {w : Y×X → ℝ} (h : LogSupermodular w)
    (hp : ∀ p,0<w p) {s t : Y} (hst : s≤t) :
    Monotone (fun x => w (t,x)/w (s,x)) := by
  intro u v huv
  have hh := h (t,u) (s,v)
  simp only [Prod.inf_def,Prod.sup_def,inf_eq_right.mpr hst,inf_eq_left.mpr huv,
    sup_eq_left.mpr hst,sup_eq_right.mpr huv] at hh
  exact (div_le_div_iff₀ (hp (s,u)) (hp (s,v))).2 (by nlinarith)

end Lattice

section Product
variable {X : Type uX} {Y : Type uY} [Lattice X] [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [LinearOrder Y] [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [FirstCountableTopology Y] [LocallyCompactSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [SecondCountableTopology X] [CompactSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] [SecondCountableTopology Y] [FirstCountableTopology Y]
  [LocallyCompactSpace Y] in
theorem conditionalMean_monotone (hX : ContinuousFKG μ) {w f : Y×X → ℝ}
    (hw : Continuous w) (hp : ∀ p,0<w p) (hLS : LogSupermodular w)
    (hf : Continuous f) (hfn : ∀ p,0≤f p) (hfm : Monotone f) :
    Monotone (conditionalMean μ w f) := by
  intro s t hst
  have hs : ContinuousAssociated μ (fun x => w (s,x)) :=
    hX _ (by fun_prop) (fun x => hp (s,x)) (logSupermodular_slice hLS s)
  calc
    conditionalMean μ w f s ≤ weightedMean μ (fun x => w (t,x)) (fun x => f (s,x)) := by
      apply weightedMean_tilt_mono (by fun_prop) (by fun_prop)
        (fun x => hp (s,x)) (fun x => hp (t,x)) hs (by fun_prop) (fun x => hfn (s,x))
      · exact fun u v huv => hfm ⟨le_rfl,huv⟩
      · exact logSupermodular_ratio_monotone hLS hp hst
    _ ≤ conditionalMean μ w f t := by
      apply weightedMean_mono (by fun_prop) (fun x => hp (t,x)) (by fun_prop) (by fun_prop)
      exact fun x => hfm ⟨hst,le_rfl⟩

theorem continuousFKG_prod (hX : ContinuousFKG μ) : ContinuousFKG (ν.prod μ) := by
  intro w hw hp hLS f g hf hg hfn hgn hfm hgm
  let m := marginalWeight μ w
  let F := conditionalMean μ w f
  let H := conditionalMean μ w g
  let J := conditionalMean μ w (fun p => f p*g p)
  have hmc : Continuous m := marginalWeight_continuous μ hw
  have hmp : ∀ y,0 < m y := marginalWeight_pos μ hw hp
  have hFc : Continuous F := conditionalMean_continuous μ hw hf hp
  have hHc : Continuous H := conditionalMean_continuous μ hw hg hp
  have hJc : Continuous J := conditionalMean_continuous μ hw (hf.mul hg) hp
  have hFn : ∀ y,0≤F y := fun y => weightedMean_nonneg (by fun_prop)
    (fun x => hp (y,x)) (fun x => hfn (y,x))
  have hHn : ∀ y,0≤H y := fun y => weightedMean_nonneg (by fun_prop)
    (fun x => hp (y,x)) (fun x => hgn (y,x))
  have hFm : Monotone F := conditionalMean_monotone hX hw hp hLS hf hfn hfm
  have hHm : Monotone H := conditionalMean_monotone hX hw hp hLS hg hgn hgm
  have hpoint : ∀ y,F y*H y≤J y := by
    intro y
    exact hX _ (show Continuous (fun x => w (y,x)) from by fun_prop) (fun x => hp (y,x))
      (logSupermodular_slice hLS y) _ _ (by fun_prop) (by fun_prop)
      (fun x => hfn (y,x)) (fun x => hgn (y,x))
      (fun u v huv => hfm ⟨le_rfl,huv⟩) (fun u v huv => hgm ⟨le_rfl,huv⟩)
  rw [weightedMean_prod μ ν hw hf hp,weightedMean_prod μ ν hw hg hp,
    weightedMean_prod μ ν hw (show Continuous (fun p => f p*g p) from hf.mul hg) hp]
  exact ((continuousAssociated_chain ν m hmc hmp) F H hFc hHc hFn hHn hFm hHm).trans
    (weightedMean_mono hmc hmp (hFc.mul hHc) hJc hpoint)

end Product
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FinFKG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uX uY uι

noncomputable section
open MeasureTheory
namespace ClassicalON

section Equivalence
variable {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace X] [TopologicalSpace Y] [Lattice X] [Lattice Y]
  {μ : Measure X} {ν : Measure Y}

omit [TopologicalSpace X] [TopologicalSpace Y] [Lattice X] [Lattice Y] in
theorem weightedMean_equiv (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (w f : Y → ℝ) :
    weightedMean μ (w ∘ e) (f ∘ e) = weightedMean ν w f := by
  unfold weightedMean
  change (∫ x,(fun y => w y*f y) (e x) ∂μ)/(∫ x,w (e x) ∂μ) = _
  rw [he.integral_comp' (fun y => w y*f y),he.integral_comp' w]

theorem continuousFKG_equiv (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (hc : Continuous e) (hm : Monotone e)
    (hi : ∀ x y,e (x⊓y)=e x⊓e y) (hs : ∀ x y,e (x⊔y)=e x⊔e y)
    (hX : ContinuousFKG μ) : ContinuousFKG ν := by
  intro w hw hp hLS f g hf hg hfn hgn hfm hgm
  have hL : LogSupermodular (w ∘ e) := by
    intro x y
    simpa [Function.comp_def,hi,hs] using hLS (e x) (e y)
  have h := hX (w ∘ e) (hw.comp hc) (fun x => hp (e x)) hL
    (f ∘ e) (g ∘ e) (hf.comp hc) (hg.comp hc) (fun x => hfn (e x))
    (fun x => hgn (e x)) (hfm.comp hm) (hgm.comp hm)
  change weightedMean μ (w ∘ e) (f ∘ e)*weightedMean μ (w ∘ e) (g ∘ e) ≤
    weightedMean μ (w ∘ e) ((fun y => f y*g y) ∘ e) at h
  simpa only [weightedMean_equiv e he] using h

end Equivalence

theorem continuousFKG_subsingleton {X : Type uX} [Subsingleton X] [Nonempty X]
    [MeasurableSpace X] [TopologicalSpace X] [Lattice X]
    (μ : Measure X) [IsProbabilityMeasure μ] : ContinuousFKG μ := by
  intro w _ hp _ f g _ _ _ _ _ _
  let x : X := Classical.choice inferInstance
  have hw : w=fun _ => w x := funext fun y => congrArg w (Subsingleton.elim y x)
  have hf : f=fun _ => f x := funext fun y => congrArg f (Subsingleton.elim y x)
  have hg : g=fun _ => g x := funext fun y => congrArg g (Subsingleton.elim y x)
  rw [hw,hf,hg]
  simp only [weightedMean,integral_const,probReal_univ,one_smul]
  field_simp [(hp x).ne']
  exact le_rfl

section Finite
variable {A : Type uA} [LinearOrder A] [TopologicalSpace A] [CompactSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [LocallyCompactSpace A] (μ : Measure A) [IsProbabilityMeasure μ]

theorem continuousFKG_fin (k : ℕ) : ContinuousFKG (Measure.pi (fun _ : Fin k => μ)) := by
  induction k with
  | zero => exact continuousFKG_subsingleton _
  | succ k ih =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => A) 0).symm
    have he : MeasurePreserving e (μ.prod (Measure.pi (fun _ : Fin k => μ)))
        (Measure.pi (fun _ : Fin (k+1) => μ)) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => μ) 0).symm
    have ha (p : A×(Fin k → A)) : e p = Fin.cons p.1 p.2 := by
      simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero']
    apply continuousFKG_equiv e he
    · apply continuous_pi
      intro i
      cases i using Fin.cases with
      | zero => simpa [ha] using (continuous_fst : Continuous (fun p : A×(Fin k → A) => p.1))
      | succ j => simpa [ha,Function.comp_def] using (continuous_apply j).comp (continuous_snd : Continuous (fun p : A×(Fin k → A) => p.2))
    · intro p q hpq i
      cases i using Fin.cases with
      | zero => simpa [ha] using hpq.1
      | succ j => simpa [ha] using hpq.2 j
    · intro p q
      ext i
      cases i using Fin.cases <;> simp [ha]
    · intro p q
      ext i
      cases i using Fin.cases <;> simp [ha]
    · exact continuousFKG_prod ih

theorem continuousFKG_pi_oai {ι : Type uι} [Fintype ι] :
    ContinuousFKG (Measure.pi (fun _ : ι => μ)) := by
  let f := (Fintype.equivFin ι).symm
  let e := MeasurableEquiv.piCongrLeft (fun _ : ι => A) f
  have ha (u : Fin (Fintype.card ι) → A) (i : ι) : e u i=u (f.symm i) := by
    simpa only [e,f.apply_symm_apply] using
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => A) f u (f.symm i)
  apply continuousFKG_equiv e (measurePreserving_piCongrLeft (fun _ : ι => μ) f)
  · apply continuous_pi
    intro i
    simpa only [ha] using (continuous_apply (f.symm i) : Continuous (fun u : Fin (Fintype.card ι) → A => u (f.symm i)))
  · intro u v huv i
    simpa only [ha] using huv (f.symm i)
  · intro u v; ext i; simp only [ha,Pi.inf_apply]
  · intro u v; ext i; simp only [ha,Pi.sup_apply]
  · exact continuousFKG_fin μ _

end Finite
end ClassicalON

end

end OAI
end

theorem solution.{uA, uι} : type_of% @OAI.ClassicalON.continuousFKG_pi_oai.{uA, uι} := @OAI.ClassicalON.continuousFKG_pi_oai.{uA, uι}
