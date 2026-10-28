-- Prove2me | solution 1 for OAI.ScalarConductivity.elliptic_fourier_matching_regular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:10:55.781282+00:00
-- url     : https://prove2.me/submissions/38039e08-94b6-4fa4-8b39-ef6cb39408a7

import Mathlib
import Definitions.Def_OAIQ059C008
import Theorems.Thm_OAI_ScalarConductivity_fourierMatchingFamily_correction

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFlatMode
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology

lemma flatPhaseMode_translation (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (phase T : ℝ)
    (x : Fin 3 → ℝ) :
    flatPhaseMode s h phase (x+![T,0,0]) = exp (-torusRate s h*T)*flatPhaseMode s h phase x := by
  simp only [flatPhaseMode,torusAngular,add_apply,
    smul_apply,ContinuousLinearMap.proj_apply,Pi.add_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    smul_eq_mul,add_zero]
  rw [mul_add,exp_add]
  ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_LocalSmoothSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

lemma local_iteratedFDeriv_tsum {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ι → E → F} {s : Set E} (hs : IsOpen s) (hsc : IsPreconnected s)
    (hf : ∀ i, ContDiff ℝ (↑(⊤:ℕ∞)) (f i))
    (v : ℕ → ι → ℝ) (hv : ∀ n, Summable (v n))
    (hbound : ∀ n i x, x∈s → ‖iteratedFDeriv ℝ n (f i) x‖≤v n i)
    (n : ℕ) {x : E} (hx : x∈s) :
    iteratedFDeriv ℝ n (fun x => ∑' i, f i x) x = ∑' i, iteratedFDeriv ℝ n (f i) x := by
  have ht := (local_smooth_taylor hs hsc hf v hv hbound).eq_iteratedFDerivWithin_of_uniqueDiffOn
    (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)) (hs.uniqueDiffOn) hx
  rw [iteratedFDerivWithin_of_isOpen n hs hx] at ht
  exact ht.symm

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFourierSmooth
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma flatFourier_iterated {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h, |a h|≤B)
    (n : ℕ) {x : Fin 3 → ℝ} (hx : 0<x 0) :
    iteratedFDeriv ℝ n (flatFourier s a phase) x =
      ∑' h, iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) x := by
  apply local_iteratedFDeriv_tsum (axial_halfspace_open (x 0/2)) (axial_halfspace_connected (x 0/2))
    (fun h => contDiff_const.mul (flatPhaseMode_smooth s h (phase h)))
    (fun n h => B*((torusRate s h+torusSize h)^n*exp (-(x 0/2)*torusRate s h)))
  · intro n
    exact (flatMode_derivative_summable hs n (by linarith)).mul_left B
  · intro n h y hy
    exact weighted_phase_halfspace_bound ha n h hy.le
  · change x 0/2<x 0
    linarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularPeriodization
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma AngularPeriodic.fderiv {T : ℝ} {f : Coord3 → E} (hf : AngularPeriodic T f) :
    AngularPeriodic T (fderiv ℝ f) := by
  intro n x
  have he : (fun y => f (y+angularShift T n))=f := funext (hf n)
  rw [←fderiv_comp_add_right,he]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusBoxFlux
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

lemma integral_coord2_Icc {a b : Fin 2 → ℝ} (hab : a≤b) {f : (Fin 2 → ℝ) → ℝ}
    (hf : Continuous f) :
    (∫ x in Icc a b,f x)=∫ y in a 0..b 0,∫ z in a 1..b 1,f ![y,z] := by
  have hc : Continuous (fun q : ℝ×ℝ => f ![q.1,q.2]) := hf.comp (by fun_prop)
  have hi := hc.continuousOn.integrableOn_compact (μ:=volume)
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)))
  have he := (volume_preserving_finTwoArrow ℝ).setIntegral_image_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding (fun q : ℝ×ℝ => f ![q.1,q.2]) (Icc a b)
  have hid (x : Fin 2 → ℝ) : ![x 0,x 1]=x := by ext i; fin_cases i <;> rfl
  simp only [MeasurableEquiv.finTwoArrow_apply] at he
  simp_rw [hid] at he
  have him : MeasurableEquiv.finTwoArrow '' Icc a b=Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1) := by
    ext q
    rw [MeasurableEquiv.image_eq_preimage_symm]
    simp only [mem_preimage,mem_Icc,Pi.le_def,mem_prod]
    constructor
    · intro h
      exact ⟨⟨h.1 0,h.2 0⟩,⟨h.1 1,h.2 1⟩⟩
    · intro h
      constructor <;> intro i <;> fin_cases i
      · exact h.1.1
      · exact h.2.1
      · exact h.1.2
      · exact h.2.2
  change (∫ y in (MeasurableEquiv.finTwoArrow '' Icc a b),f ![y.1,y.2])=_ at he
  rw [←he,him]
  change (∫ x in Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1),f ![x.1,x.2] ∂volume.prod volume)=_
  rw [setIntegral_prod _ hi]
  simp_rw [intervalIntegral.integral_of_le (hab 0),intervalIntegral.integral_of_le (hab 1),
    ←integral_Icc_eq_integral_Ioc]

lemma integral_coord3_Icc {a b : Coord3} (hab : a≤b) {f : Coord3 → ℝ} (hf : Continuous f) :
    (∫ x in Icc a b,f x)=∫ t in a 0..b 0,∫ y in a 1..b 1,∫ z in a 2..b 2,f ![t,y,z] := by
  have hc : Continuous (fun q : ℝ×(ℝ×ℝ) => f ![q.1,q.2.1,q.2.2]) := hf.comp (by fun_prop)
  have hi := hc.continuousOn.integrableOn_compact (μ:=volume)
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc) :
      IsCompact (Icc (a 0) (b 0) ×ˢ (Icc (a 1) (b 1) ×ˢ Icc (a 2) (b 2))))
  have he := threeArrow_volume.setIntegral_image_emb threeArrow.measurableEmbedding
    (fun q : ℝ×(ℝ×ℝ) => f ![q.1,q.2.1,q.2.2]) (Icc a b)
  simp only [threeArrow_apply] at he
  have hid (x : Coord3) : ![x 0,x 1,x 2]=x := by ext i; fin_cases i <;> rfl
  simp_rw [hid] at he
  have him : threeArrow '' Icc a b=Icc (a 0) (b 0) ×ˢ (Icc (a 1) (b 1) ×ˢ Icc (a 2) (b 2)) := by
    ext q
    rw [MeasurableEquiv.image_eq_preimage_symm]
    simp only [mem_preimage,mem_Icc,Pi.le_def,mem_prod,threeArrow_symm_apply]
    constructor
    · intro h
      exact ⟨⟨h.1 0,h.2 0⟩,⟨⟨h.1 1,h.2 1⟩,⟨h.1 2,h.2 2⟩⟩⟩
    · intro h
      constructor <;> intro i <;> fin_cases i
      · exact h.1.1
      · exact h.2.1.1
      · exact h.2.2.1
      · exact h.1.2
      · exact h.2.1.2
      · exact h.2.2.2
  change (∫ y in (threeArrow '' Icc a b),f ![y.1,y.2.1,y.2.2])=_ at he
  rw [←he,him]
  change (∫ x in Icc (a 0) (b 0) ×ˢ (Icc (a 1) (b 1) ×ˢ Icc (a 2) (b 2)),
    f ![x.1,x.2.1,x.2.2] ∂volume.prod volume)=_
  rw [setIntegral_prod _ hi]
  simp_rw [intervalIntegral.integral_of_le (hab 0),intervalIntegral.integral_of_le (hab 1),
    intervalIntegral.integral_of_le (hab 2),←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t _
  exact setIntegral_prod _ ((hc.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc))

lemma coordinateDivergence_eq_trace {F : Coord3 → Coord3} (hF : Differentiable ℝ F) (x : Coord3) :
    coordinateDivergence F x=∑ i : Fin 3,fderiv ℝ F x (Pi.single i 1) i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [(hasFDerivAt_pi'.mp (hF x).hasFDerivAt i).fderiv]
  rfl

theorem torus_band_divergence {T a b : ℝ} (hT : 0≤T) (hab : a≤b)
    {F : Coord3 → Coord3} (hF : ContDiff ℝ (↑(⊤:ℕ∞)) F) (hp : AngularPeriodic T F) :
    (∫ t in a..b,torusCellIntegral T (coordinateDivergence F) t)=
      torusCellIntegral T (fun x => F x 0) b-torusCellIntegral T (fun x => F x 0) a := by
  let A : Coord3 := ![a,0,0]
  let B : Coord3 := ![b,T,T]
  have hAB : A≤B := by intro i; fin_cases i; exact hab; exact hT; exact hT
  have hc := (coordinateDivergence_smooth hF).continuous
  have hfd := hF.differentiable (by simp)
  have hh := integral_divergence_of_hasFDerivAt_off_countable A B hAB F (fderiv ℝ F)
    ∅ countable_empty hF.continuous.continuousOn (fun x _ => (hfd x).hasFDerivAt)
    (by simpa only [←coordinateDivergence_eq_trace hfd] using (hc.continuousOn.integrableOn_compact
      (μ:=volume) (isCompact_Icc : IsCompact (Icc A B))))
  simp_rw [←coordinateDivergence_eq_trace hfd] at hh
  rw [integral_coord3_Icc hAB hc] at hh
  have h1 (q : Fin 2 → ℝ) : F ((1:Fin 3).insertNth T q) 1=F ((1:Fin 3).insertNth 0 q) 1 := by
    have he : ((1:Fin 3).insertNth 0 q)+angularShift T ![1,0]=(1:Fin 3).insertNth T q := by
      ext i; fin_cases i <;> simp [angularShift,Fin.insertNth,Fin.succAboveCases]
    have hh := hp ![1,0] ((1:Fin 3).insertNth 0 q)
    rw [he] at hh
    exact congrFun hh 1
  have h2 (q : Fin 2 → ℝ) : F ((2:Fin 3).insertNth T q) 2=F ((2:Fin 3).insertNth 0 q) 2 := by
    have he : ((2:Fin 3).insertNth 0 q)+angularShift T ![0,1]=(2:Fin 3).insertNth T q := by
      ext i; fin_cases i <;> simp [angularShift,Fin.insertNth,Fin.succAboveCases]
    have hh := hp ![0,1] ((2:Fin 3).insertNth 0 q)
    rw [he] at hh
    exact congrFun hh 2
  rw [Fin.sum_univ_succ] at hh
  simp only [Fin.sum_univ_two,Fin.succ_zero_eq_one,Fin.succ_one_eq_two] at hh
  simp only [A,B,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at hh
  simp_rw [h1,h2] at hh
  simp only [sub_self,add_zero] at hh
  have hf0 (c : ℝ) :
      (∫ q in Icc (A ∘ (0:Fin 3).succAbove) (B ∘ (0:Fin 3).succAbove),
        F ((0:Fin 3).insertNth c q) 0)=torusCellIntegral T (fun x => F x 0) c := by
    have hc0 : Continuous (fun q : Fin 2 → ℝ => F ((0:Fin 3).insertNth c q) 0) :=
      (continuous_apply 0).comp (hF.continuous.comp (by fun_prop))
    refine (integral_coord2_Icc (a:=A ∘ (0:Fin 3).succAbove) (b:=B ∘ (0:Fin 3).succAbove) (fun i => hAB ((0:Fin 3).succAbove i)) hc0).trans ?_
    change (∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,F ((0:Fin 3).insertNth c ![y,z]) 0)=_
    apply intervalIntegral.integral_congr
    intro y _
    apply intervalIntegral.integral_congr
    intro z _
    have hi : (0:Fin 3).insertNth c ![y,z]=![c,y,z] := by
      ext i
      fin_cases i <;> simp [Fin.insertNth,Fin.succAboveCases]
    exact congrArg (fun x : Coord3 => F x 0) hi
  exact hh.trans (congrArg₂ (· - ·) (hf0 b) (hf0 a))

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

lemma smooth_smul_of_support_in_open {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E→F} {ρ : E→ℝ} {S : Set E} (hS : IsOpen S)
    (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f S) (hρ : ContDiff ℝ (↑(⊤:ℕ∞)) ρ)
    (hs : tsupport ρ⊆S) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => ρ x • f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x∈tsupport ρ
  · exact hρ.contDiffAt.smul (hf.contDiffAt (hS.mem_nhds (hs hx)))
  · have he : (fun y => ρ y • f y)=ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma axial_band_smooth_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ a b T : ℝ} (ha : δ<a) {F : Coord3 → E}
    (hF : ContDiffOn ℝ (↑(⊤:ℕ∞)) F {x | δ<x 0}) (hp : AngularPeriodic T F) :
    ∃ G : Coord3 → E,ContDiff ℝ (↑(⊤:ℕ∞)) G ∧ AngularPeriodic T G ∧
      ∀ x : Coord3,x 0∈Icc a b → G=ᶠ[𝓝 x] F := by
  have hb : Bornology.IsBounded (Ioo δ (b+1)) :=
    (isCompact_Icc : IsCompact (Icc δ (b+1))).isBounded.subset Ioo_subset_Icc_self
  have hs : Icc a b⊆Ioo δ (b+1) := by
    intro t ht
    exact ⟨ha.trans_le ht.1,by linarith [ht.2]⟩
  obtain ⟨χ,hχ,hχc,hχs,hχb,hχ1⟩ := exists_smooth_core_cutoff
    (isCompact_Icc : IsCompact (Icc a b)) isOpen_Ioo hb hs
  let ρ : Coord3 → ℝ := fun x => χ (x 0)
  have hρ : ContDiff ℝ (↑(⊤:ℕ∞)) ρ := hχ.comp (contDiff_apply ℝ ℝ 0)
  have hρs : tsupport ρ⊆{x | δ<x 0} := by
    intro x hx
    exact (hχs (tsupport_comp_subset_preimage χ (f:=fun x : Coord3 => x 0) (continuous_apply 0) hx)).1
  refine ⟨fun x => ρ x • F x,smooth_smul_of_support_in_open
    (isOpen_lt continuous_const (continuous_apply 0)) hF hρ hρs,?_,?_⟩
  · intro n x
    change χ (x 0+0) • F (x+angularShift T n)=χ (x 0) • F x
    rw [add_zero,hp n x]
  · intro x hx
    have he : (fun y : Coord3 => χ (y 0))=ᶠ[𝓝 x] (fun _ => 1) :=
      (hχ1 (x 0) hx).comp_tendsto (continuous_apply 0).continuousAt
    filter_upwards [he] with y hy
    change χ (y 0) • F y=F y
    rw [hy,one_smul]

lemma coordinateDivergence_congr_nhds {F G : Coord3 → Coord3} {x : Coord3}
    (h : F=ᶠ[𝓝 x] G) : coordinateDivergence F x=coordinateDivergence G x := by
  unfold coordinateDivergence
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => F y i)=ᶠ[𝓝 x] (fun y => G y i) := h.mono (fun y hy => congrFun hy i)
  rw [he.fderiv_eq]

theorem torus_band_divergence_halfspace {δ T a b : ℝ} (ha : δ<a) (hT : 0≤T) (hab : a≤b)
    {F : Coord3 → Coord3} (hF : ContDiffOn ℝ (↑(⊤:ℕ∞)) F {x | δ<x 0})
    (hp : AngularPeriodic T F) :
    (∫ t in a..b,torusCellIntegral T (coordinateDivergence F) t)=
      torusCellIntegral T (fun x => F x 0) b-torusCellIntegral T (fun x => F x 0) a := by
  obtain ⟨G,hG,hGp,hGF⟩ := axial_band_smooth_extension ha hF hp (b:=b)
  have he (t : ℝ) (ht : t∈Icc a b) :
      torusCellIntegral T (coordinateDivergence G) t=torusCellIntegral T (coordinateDivergence F) t := by
    apply intervalIntegral.integral_congr
    intro y _
    apply intervalIntegral.integral_congr
    intro z _
    exact coordinateDivergence_congr_nhds (hGF ![t,y,z] ht)
  have heF (t : ℝ) (ht : t∈Icc a b) :
      torusCellIntegral T (fun x => G x 0) t=torusCellIntegral T (fun x => F x 0) t := by
    apply intervalIntegral.integral_congr
    intro y _
    apply intervalIntegral.integral_congr
    intro z _
    exact congrFun (hGF ![t,y,z] ht).self_of_nhds 0
  have hh := torus_band_divergence hT hab hG hGp
  have hl : (∫ t in a..b,torusCellIntegral T (coordinateDivergence G) t)=
      ∫ t in a..b,torusCellIntegral T (coordinateDivergence F) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact he t (by simpa only [uIcc_of_le hab] using ht)
  rw [hl,heF b (right_mem_Icc.mpr hab),heF a (left_mem_Icc.mpr hab)] at hh
  exact hh

lemma torus_flux_constant {δ T a b : ℝ} (ha : δ<a) (hT : 0≤T) (hab : a≤b)
    {F : Coord3 → Coord3} (hF : ContDiffOn ℝ (↑(⊤:ℕ∞)) F {x | δ<x 0})
    (hp : AngularPeriodic T F) (hd : ∀ x,δ<x 0 → coordinateDivergence F x=0) :
    torusCellIntegral T (fun x => F x 0) b=torusCellIntegral T (fun x => F x 0) a := by
  have hh := torus_band_divergence_halfspace ha hT hab hF hp
  have hz : (∫ t in a..b,torusCellIntegral T (coordinateDivergence F) t)=0 := by
    rw [←intervalIntegral.integral_zero (a:=a) (b:=b) (μ:=volume)]
    apply intervalIntegral.integral_congr
    intro t ht
    have hta : a≤t := (by simpa only [uIcc_of_le hab] using ht : t∈Icc a b).1
    have he (y z : ℝ) : coordinateDivergence F ![t,y,z]=0 := hd _ (ha.trans_le hta)
    simp only [torusCellIntegral,he,intervalIntegral.integral_zero]
  rw [hz] at hh
  linarith

lemma torus_flux_zero_of_tendsto {δ T a : ℝ} (ha : δ<a) (hT : 0≤T)
    {F : Coord3 → Coord3} (hF : ContDiffOn ℝ (↑(⊤:ℕ∞)) F {x | δ<x 0})
    (hp : AngularPeriodic T F) (hd : ∀ x,δ<x 0 → coordinateDivergence F x=0)
    (ht : Tendsto (fun t => torusCellIntegral T (fun x => F x 0) t) atTop (𝓝 0)) :
    torusCellIntegral T (fun x => F x 0) a=0 := by
  have he : (fun t => torusCellIntegral T (fun x => F x 0) t)=ᶠ[atTop]
      (fun _ => torusCellIntegral T (fun x => F x 0) a) := by
    filter_upwards [eventually_ge_atTop a] with b hab
    exact torus_flux_constant ha hT hab hF hp hd
  exact tendsto_nhds_unique tendsto_const_nhds (ht.congr' he)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_FlatTorusPDE
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma expCosLinear_deriv (L K : E →L[ℝ] ℝ) (p : ℝ) (x : E) :
    HasFDerivAt (expCosLinear L K p)
      (expCosLinear L K p x • L + expCosLinear L K (p+Real.pi/2) x • K) x := by
  have hh := (L.hasFDerivAt (x := x)).exp.mul ((K.hasFDerivAt.add_const p).cos)
  convert hh using 1 <;> ext v <;>
    simp [smul_eq_mul,expCosLinear,Pi.mul_apply,←add_assoc,cos_add_pi_div_two]
  ring

lemma expCosLinear_fderiv (L K : E →L[ℝ] ℝ) (p : ℝ) (x v : E) :
    fderiv ℝ (expCosLinear L K p) x v =
      expCosLinear L K p x*L v+expCosLinear L K (p+Real.pi/2) x*K v := by
  rw [(expCosLinear_deriv L K p x).fderiv]
  rfl

lemma expCosLinear_hessian (L K : E →L[ℝ] ℝ) (p : ℝ) (x v w : E) :
    (iteratedFDeriv ℝ 2 (expCosLinear L K p) x) ![v,w] =
      (L v*L w-K v*K w)*expCosLinear L K p x+
      (L v*K w+K v*L w)*expCosLinear L K (p+Real.pi/2) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (expCosLinear L K p)) x := by
    have hc : ContDiff ℝ 2 (expCosLinear L K p) := by unfold expCosLinear; fun_prop
    exact (hc.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have he := fderiv_clm_apply (c := fderiv ℝ (expCosLinear L K p)) hd
    (differentiableAt_const (c := w))
  have hfun : (fun y => fderiv ℝ (expCosLinear L K p) y w)=
      fun y => expCosLinear L K p y*L w+expCosLinear L K (p+Real.pi/2) y*K w := by
    funext y
    exact expCosLinear_fderiv L K p y w
  rw [hfun] at he
  have hh := ((expCosLinear_deriv L K p x).mul_const (L w)).add
    ((expCosLinear_deriv L K (p+Real.pi/2) x).mul_const (K w))
  have hhe := hh.fderiv
  change fderiv ℝ (fun y => expCosLinear L K p y*L w+
    expCosLinear L K (p+Real.pi/2) y*K w) x=_ at hhe
  rw [hhe] at he
  have hv := congrArg (fun A : E →L[ℝ] ℝ => A v) he
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,
    ContinuousLinearMap.flip_apply,add_apply,smul_apply,
    smul_eq_mul] at hv
  rw [←hv]
  have hp : p+Real.pi/2+Real.pi/2=p+Real.pi := by ring
  simp only [expCosLinear,hp,←add_assoc,cos_add_pi]
  ring

lemma flatPhaseMode_harmonic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (h : Fin 2 → ℤ) (p : ℝ) (x : Fin 3 → ℝ) :
    flatTensorLaplacian s (flatPhaseMode s h p) x=0 := by
  let L : (Fin 3 → ℝ) →L[ℝ] ℝ := -torusRate s h • ContinuousLinearMap.proj 0
  have hf : flatPhaseMode s h p=expCosLinear L (torusAngular h) p := rfl
  have hsq : torusRate s h^2=torusQuadratic s h := by
    apply sq_sqrt
    exact (by positivity : 0≤(1/2)*((h 0:ℝ)^2+(h 1:ℝ)^2)).trans (hs _ _)
  rw [flatTensorLaplacian,hf]
  simp only [flatTensorLaplacianCLM,add_apply,
    smul_apply,ContinuousMultilinearMap.apply_apply,smul_eq_mul,
    expCosLinear_hessian]
  simp only [L,torusAngular,add_apply,smul_apply,
    ContinuousLinearMap.proj_apply,flatAxis,Pi.single_apply,smul_eq_mul]
  simp only [show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide,
    show (2:Fin 3)≠1 by decide,show (2:Fin 3)≠0 by decide,
    show (0:Fin 3)≠1 by decide,show (1:Fin 3)≠0 by decide,
    ite_true,ite_false,mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero,
    zero_sub,neg_mul,neg_neg,mul_neg]
  dsimp [torusQuadratic] at hsq
  have hm := congrArg (fun r => r*expCosLinear L (torusAngular h) p x) hsq
  dsimp [L,torusAngular] at hm
  linear_combination hm

lemma weighted_flatPhaseMode_harmonic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (h : Fin 2 → ℤ) (p a : ℝ) (x : Fin 3 → ℝ) :
    flatTensorLaplacian s (fun y => a*flatPhaseMode s h p y) x=0 := by
  change flatTensorLaplacianCLM s (iteratedFDeriv ℝ 2 (a • flatPhaseMode s h p) x)=0
  rw [iteratedFDeriv_const_smul_apply
    (((contDiff_infty.mp (flatPhaseMode_smooth s h p)) 2).contDiffAt),map_smul]
  change a • flatTensorLaplacian s (flatPhaseMode s h p) x=0
  rw [flatPhaseMode_harmonic hs,smul_zero]

theorem flatFourier_harmonic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B)
    {x : Fin 3 → ℝ} (hx : 0<x 0) :
    flatTensorLaplacian s (flatFourier s a phase) x=0 := by
  have hb := (flatMode_derivative_summable hs 2 hx).mul_left B
  have hn : Summable (fun h => ‖iteratedFDeriv ℝ 2
      (fun y => a h*flatPhaseMode s h (phase h) y) x‖) :=
    Summable.of_nonneg_of_le (fun h => norm_nonneg _)
      (fun h => weighted_phase_halfspace_bound ha 2 h le_rfl) hb
  rw [flatTensorLaplacian,flatFourier_iterated hs ha 2 hx,
    (flatTensorLaplacianCLM s).map_tsum hn.of_norm]
  have hz (h : Fin 2 → ℤ) : flatTensorLaplacianCLM s (iteratedFDeriv ℝ 2
      (fun y => a h*flatPhaseMode s h (phase h) y) x)=0 :=
    weighted_flatPhaseMode_harmonic hs h (phase h) (a h) x
  simp only [hz,tsum_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FlatFourierFlux
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatModeFlux_smoothOn {s : Fin 3 → ℝ} {f : Coord3 → ℝ} {U : Set Coord3}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f U) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (flatModeFlux s f) U := by
  have hd := hf.fderiv_of_isOpen hU (m:=↑(⊤:ℕ∞)) (by simp)
  have he (i : Fin 3) := hd.clm_apply (contDiffOn_const (c:=flatAxis i))
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact he 0
  · exact (contDiffOn_const.mul (he 1)).add (contDiffOn_const.mul (he 2))
  · exact (contDiffOn_const.mul (he 1)).add (contDiffOn_const.mul (he 2))

lemma flatModeFlux_divergence {s : Fin 3 → ℝ} {f : Coord3 → ℝ} {x : Coord3}
    (hf : ContDiffAt ℝ (↑(⊤:ℕ∞)) f x) :
    coordinateDivergence (flatModeFlux s f) x=flatTensorLaplacian s f x := by
  have hd := (hf.fderiv_right (m:=1) (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))).differentiableAt (by simp)
  have he (i : Fin 3) :
      fderiv ℝ (fun y => fderiv ℝ f y (flatAxis i)) x=(fderiv ℝ (fderiv ℝ f) x).flip (flatAxis i) := by
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have he' (i : Fin 3) : DifferentiableAt ℝ (fun y => fderiv ℝ f y (flatAxis i)) x :=
    hd.clm_apply (differentiableAt_const _)
  have hsum := hf.isSymmSndFDerivAt (by simp)
  unfold coordinateDivergence
  rw [Fin.sum_univ_three]
  change fderiv ℝ (fun y => fderiv ℝ f y (flatAxis 0)) x (flatAxis 0)+
    fderiv ℝ (fun y => s 0*fderiv ℝ f y (flatAxis 1)+s 1*fderiv ℝ f y (flatAxis 2)) x (flatAxis 1)+
    fderiv ℝ (fun y => s 1*fderiv ℝ f y (flatAxis 1)+s 2*fderiv ℝ f y (flatAxis 2)) x (flatAxis 2)=_
  rw [fderiv_fun_add ((he' 1).const_mul _) ((he' 2).const_mul _),
    fderiv_fun_add ((he' 1).const_mul _) ((he' 2).const_mul _)]
  simp only [fderiv_const_mul (he' _),he,_root_.add_apply,
    _root_.smul_apply,ContinuousLinearMap.flip_apply,smul_eq_mul]
  unfold flatTensorLaplacian flatTensorLaplacianCLM
  simp only [_root_.add_apply,_root_.smul_apply,
    ContinuousMultilinearMap.apply_apply,smul_eq_mul,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [hsum.eq (flatAxis 2) (flatAxis 1)]
  ring

lemma flatModeFlux_periodic {s : Fin 3 → ℝ} {f : Coord3 → ℝ} {T : ℝ}
    (hf : AngularPeriodic T f) : AngularPeriodic T (flatModeFlux s f) := by
  intro n x
  unfold flatModeFlux
  rw [hf.fderiv n x]

lemma flatFourier_flux_divergence {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B) {x : Coord3} (hx : 0<x 0) :
    coordinateDivergence (flatModeFlux s (flatFourier s a phase)) x=0 := by
  rw [flatModeFlux_divergence ((flatFourier_smooth hs ha).contDiffAt
    ((axial_halfspace_open 0).mem_nhds hx)),flatFourier_harmonic hs ha hx]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CompactifiedFourierTail
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma linear_comp_iterated_point_bound {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → G} (g : F →L[ℝ] E)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (n : ℕ) (x : F) :
    ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤
      ‖iteratedFDeriv ℝ n f (g x)‖*‖g‖^n := by
  rw [g.iteratedFDeriv_comp_right ((contDiff_infty.mp hf) n) x le_rfl]
  simpa using (iteratedFDeriv ℝ n f (g x)).norm_compContinuousLinearMap_le (fun _ => g)

lemma glue_derivative_compact_bound {gap : ℝ} (hg : 0<gap) (n : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ p∈Icc (-gap⁻¹) gap⁻¹,
      ‖iteratedFDeriv ℝ n expNegInvGlue p‖≤C := by
  have hc := (expNegInvGlue.contDiff (n := (⊤:ℕ∞))).continuous_iteratedFDeriv
    (m := n) (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
  obtain ⟨C,hC⟩ := (isCompact_Icc.image hc).isBounded.exists_norm_le
  exact ⟨max C gap,hg.le.trans (le_max_right _ _),
    fun p hp => (hC _ ⟨p,hp,rfl⟩).trans (le_max_left _ _)⟩

lemma glue_scaled_iterated_bound {gap d C : ℝ} (hg : 0<gap) (hd : gap≤d)
    (n : ℕ) (hC : 0≤C) (hb : ∀ p∈Icc (-gap⁻¹) gap⁻¹,
      ‖iteratedFDeriv ℝ n expNegInvGlue p‖≤C)
    {z : ℝ×Coord3} (hz : |z.1|≤1) :
    ‖iteratedFDeriv ℝ n (fun z : ℝ×Coord3 => expNegInvGlue (z.1/d)) z‖≤C*gap⁻¹^n := by
  let P : (ℝ×Coord3) →L[ℝ] ℝ := d⁻¹ • ContinuousLinearMap.fst ℝ ℝ Coord3
  have hdpos : 0<d := hg.trans_le hd
  have hdi : d⁻¹≤gap⁻¹ := inv_anti₀ hg hd
  have hpn : ‖P‖≤gap⁻¹ := by
    dsimp [P]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hdpos)]
    exact (mul_le_of_le_one_right (inv_nonneg.mpr hdpos.le)
      (ContinuousLinearMap.norm_fst_le ℝ ℝ Coord3)).trans hdi
  have hpv : P z∈Icc (-gap⁻¹) gap⁻¹ := by
    have hab : |P z|≤gap⁻¹ := by
      change |d⁻¹*z.1|≤_
      rw [abs_mul,abs_of_pos (inv_pos.mpr hdpos)]
      exact (mul_le_of_le_one_right (inv_nonneg.mpr hdpos.le) hz).trans hdi
    exact abs_le.mp hab
  have he : (fun z : ℝ×Coord3 => expNegInvGlue (z.1/d))=expNegInvGlue ∘ P := by
    funext w; simp [P,div_eq_mul_inv,mul_comm]
  rw [he]
  exact (linear_comp_iterated_point_bound P expNegInvGlue.contDiff n z).trans
    (mul_le_mul (hb _ hpv) (pow_le_pow_left₀ (norm_nonneg _) hpn n)
      (by positivity) hC)

lemma flatPhaseMode_shift_snd_bound (s : Fin 3→ℝ) (h : Fin 2→ℤ)
    (phase T δ : ℝ) (n : ℕ) {z : ℝ×Coord3} (hz : δ≤T+z.2 0) :
    ‖iteratedFDeriv ℝ n (fun z : ℝ×Coord3 => flatPhaseMode s h phase (z.2+![T,0,0])) z‖≤
      (torusRate s h+torusSize h)^n*exp (-δ*torusRate s h) := by
  let f : Coord3→ℝ := fun y => flatPhaseMode s h phase (y+![T,0,0])
  let P : (ℝ×Coord3) →L[ℝ] Coord3 := ContinuousLinearMap.snd ℝ ℝ Coord3
  have hf : ContDiff ℝ (↑(⊤:ℕ∞)) f := (flatPhaseMode_smooth s h phase).comp (contDiff_id.add contDiff_const)
  change ‖iteratedFDeriv ℝ n (f ∘ P) z‖≤_
  apply (linear_comp_iterated_point_bound P hf n z).trans
  have hp : ‖P‖^n≤1 := pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ Coord3)
  apply (mul_le_of_le_one_right (norm_nonneg _) hp).trans
  have he : iteratedFDeriv ℝ n f (P z)=iteratedFDeriv ℝ n (flatPhaseMode s h phase) (z.2+![T,0,0]) :=
    iteratedFDeriv_comp_add_right (f := flatPhaseMode s h phase) n _ _
  rw [he]
  apply (flatPhaseMode_iterated_bound s h phase n _).trans
  have hr : 0≤torusRate s h := sqrt_nonneg _
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (add_nonneg hr (torusSize_nonneg h)) _)
  apply exp_le_exp.mpr
  simpa only [Pi.add_apply,Matrix.cons_val_zero] using
    (show -torusRate s h*(z.2 0+T)≤-δ*torusRate s h by nlinarith)

lemma compactifiedFourierTerm_smooth (s : Fin 3→ℝ) (lam T0 : ℝ)
    (a phase : (Fin 2→ℤ)→ℝ) (h : Fin 2→ℤ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (compactifiedFourierTerm s lam T0 a phase h) := by
  unfold compactifiedFourierTerm
  exact contDiff_const.mul ((expNegInvGlue.contDiff.comp (contDiff_fst.div_const _)).mul
    ((flatPhaseMode_smooth s h (phase h)).comp (contDiff_snd.add contDiff_const)))

lemma compactifiedFourierTerm_iterated_bound {s : Fin 3→ℝ} {lam T0 gap B δ : ℝ}
    {a phase : (Fin 2→ℤ)→ℝ} (hg : 0<gap) (hB : 0≤B) (ha : ∀ h,|a h|≤B)
    (hr : ∀ h,a h≠0 → lam+gap≤torusRate s h)
    (C : ℕ→ℝ) (hC : ∀ i,0≤C i)
    (hb : ∀ i p,p∈Icc (-gap⁻¹) gap⁻¹ → ‖iteratedFDeriv ℝ i expNegInvGlue p‖≤C i)
    (n : ℕ) (h : Fin 2→ℤ) {z : ℝ×Coord3} (hp : |z.1|≤1) (hx : δ≤T0+z.2 0) :
    ‖iteratedFDeriv ℝ n (compactifiedFourierTerm s lam T0 a phase h) z‖≤
      B*exp (lam*T0)*(∑ i∈Finset.range (n+1),(n.choose i:ℝ)*(C i*gap⁻¹^i)*
        ((torusRate s h+torusSize h)^(n-i)*exp (-δ*torusRate s h))) := by
  have hrate : 0≤torusRate s h := sqrt_nonneg _
  have hsize := torusSize_nonneg h
  by_cases hz : a h=0
  · have he : compactifiedFourierTerm s lam T0 a phase h = 0 := by
      funext w; simp [compactifiedFourierTerm,hz]
    rw [he,iteratedFDeriv_zero,Pi.zero_apply,norm_zero]
    apply mul_nonneg (mul_nonneg hB (exp_nonneg _))
    exact Finset.sum_nonneg fun i _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC i) (by positivity))) (by positivity)
  have hfun : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : ℝ×Coord3 =>
      expNegInvGlue (z.1/(torusRate s h-lam))*flatPhaseMode s h (phase h) (z.2+![T0,0,0])) :=
    (expNegInvGlue.contDiff.comp (contDiff_fst.div_const _)).mul
      ((flatPhaseMode_smooth s h (phase h)).comp (contDiff_snd.add contDiff_const))
  change ‖iteratedFDeriv ℝ n ((a h*exp (lam*T0)) •
      (fun z : ℝ×Coord3 => expNegInvGlue (z.1/(torusRate s h-lam))*
        flatPhaseMode s h (phase h) (z.2+![T0,0,0]))) z‖≤_
  rw [iteratedFDeriv_const_smul_apply (((contDiff_infty.mp hfun) n).contDiffAt),norm_smul,
    Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _)]
  apply mul_le_mul (mul_le_mul_of_nonneg_right (ha h) (exp_nonneg _)) _ (norm_nonneg _)
    (mul_nonneg hB (exp_nonneg _))
  apply (norm_iteratedFDeriv_mul_le
    (expNegInvGlue.contDiff.comp (contDiff_fst.div_const _))
    ((flatPhaseMode_smooth s h (phase h)).comp (contDiff_snd.add contDiff_const)) z
    (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).trans
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul (mul_le_mul_of_nonneg_left
    (glue_scaled_iterated_bound hg (by linarith [hr h hz]) i (hC i) (hb i) hp)
    (Nat.cast_nonneg _)) (flatPhaseMode_shift_snd_bound s h (phase h) T0 δ (n-i) hx)
    (norm_nonneg _) (by positivity [hC i])

theorem compactifiedFourierTail_smooth {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {lam T0 gap B δ : ℝ} {a phase : (Fin 2→ℤ)→ℝ}
    (hg : 0<gap) (hB : 0≤B) (ha : ∀ h,|a h|≤B) (hδ : 0<δ)
    (hr : ∀ h,a h≠0 → lam+gap≤torusRate s h) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (compactifiedFourierTail s lam T0 a phase)
      (Ioo (-1) 1 ×ˢ {x : Coord3 | δ-T0<x 0}) := by
  choose C hC hb using fun n => glue_derivative_compact_bound hg n
  apply local_smooth_tsum (isOpen_Ioo.prod (axial_halfspace_open _))
    ((convex_Ioo (𝕜 := ℝ) (-1 : ℝ) 1).isPreconnected.prod (axial_halfspace_connected _))
    (compactifiedFourierTerm_smooth s lam T0 a phase)
    (fun n h => B*exp (lam*T0)*(∑ i∈Finset.range (n+1),(n.choose i:ℝ)*(C i*gap⁻¹^i)*
      ((torusRate s h+torusSize h)^(n-i)*exp (-δ*torusRate s h))))
  · intro n
    apply Summable.mul_left
    exact summable_sum (fun i _ => (flatMode_derivative_summable hs (n-i) hδ).mul_left _)
  · intro n h z hz
    apply compactifiedFourierTerm_iterated_bound hg hB ha hr C hC hb n h
    · exact (abs_lt.mpr hz.1).le
    · have hx := hz.2
      dsimp at hx
      linarith

lemma compactifiedFourierTail_of_pos {s : Fin 3→ℝ} {lam T0 : ℝ}
    {a phase : (Fin 2→ℤ)→ℝ}
    (hr : ∀ h,a h≠0 → lam<torusRate s h) {p : ℝ} (hp : 0<p) (x : Coord3) :
    compactifiedFourierTail s lam T0 a phase (p,x)=
      exp (lam*(T0+1/p))*flatFourier s a phase (x+![T0+1/p,0,0]) := by
  unfold compactifiedFourierTail flatFourier
  rw [←tsum_mul_left]
  apply tsum_congr
  intro h
  by_cases ha : a h=0
  · simp [compactifiedFourierTerm,ha]
  have hd : 0<torusRate s h-lam := sub_pos.mpr (hr h ha)
  have hglue : expNegInvGlue (p/(torusRate s h-lam))=exp (-(torusRate s h-lam)/p) := by
    simp only [expNegInvGlue,ite_eq_right (not_le.mpr (div_pos hp hd)),inv_div]
    congr 1
    ring
  have he : exp (lam*T0)*exp (-(torusRate s h-lam)/p)*exp (-torusRate s h*T0)=
      exp (lam*(T0+1/p))*exp (-torusRate s h*(T0+1/p)) := by
    rw [←exp_add,←exp_add,←exp_add]
    congr 1
    ring
  simp only [compactifiedFourierTerm,hglue,flatPhaseMode_translation]
  calc
    _= a h*(exp (lam*T0)*exp (-(torusRate s h-lam)/p)*exp (-torusRate s h*T0))*
        flatPhaseMode s h (phase h) x := by ring
    _= _ := by rw [he]; ring

lemma compactifiedFourierTail_of_nonpos {s : Fin 3→ℝ} {lam T0 : ℝ}
    {a phase : (Fin 2→ℤ)→ℝ}
    (hr : ∀ h,a h≠0 → lam<torusRate s h) {p : ℝ} (hp : p≤0) (x : Coord3) :
    compactifiedFourierTail s lam T0 a phase (p,x)=0 := by
  calc
    _ = ∑' h : Fin 2→ℤ,(0:ℝ) := by
      apply tsum_congr
      intro h
      by_cases ha : a h=0
      · simp [compactifiedFourierTerm,ha]
      have hd : 0<torusRate s h-lam := sub_pos.mpr (hr h ha)
      simp only [compactifiedFourierTerm,
        expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hp hd.le),zero_mul,mul_zero]
    _ = 0 := tsum_zero

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_SimpleWallGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma real_section_hasDeriv {g : E × ℝ → ℝ} (hg : Differentiable ℝ g)
    (p : E) (z : ℝ) : HasDerivAt (fun t => g (p,t)) (wallDerivative g (p,z)) z := by
  simpa only [Function.comp_def,wallDerivative] using
    (hg (p,z)).hasFDerivAt.comp_hasDerivAt z ((hasDerivAt_const z p).prodMk (hasDerivAt_id z))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_RecenteredWallField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma wallDerivative_eq_of_hasDeriv {f : E×ℝ → ℝ} (hf : Differentiable ℝ f)
    {q : E} {z d : ℝ} (hd : HasDerivAt (fun t => f (q,t)) d z) :
    wallDerivative f (q,z)=d := (real_section_hasDeriv hf q z).unique hd

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PureModeWall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma pureWallMode_smooth (σ lam k : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (pureWallMode σ lam k) := by
  unfold pureWallMode
  fun_prop

lemma pureWallMode_normalDerivative (σ lam k : ℝ) (q : ℝ×ℝ) (z : ℝ) :
    wallDerivative (pureWallMode σ lam k) (q,z)=
      σ*exp (-lam*q.1)*(-sin (k*z)*k) := by
  apply wallDerivative_eq_of_hasDeriv ((pureWallMode_smooth σ lam k).differentiable (by simp))
  simpa only [pureWallMode,mul_one,id_eq] using
    (((hasDerivAt_id z).const_mul k).cos.const_mul (σ*exp (-lam*q.1)))

lemma pureWallMode_normalSecond (σ lam k : ℝ) (q : ℝ×ℝ) (z : ℝ) :
    wallDerivative (wallDerivative (pureWallMode σ lam k)) (q,z)=
      -(σ*exp (-lam*q.1)*cos (k*z)*k^2) := by
  apply wallDerivative_eq_of_hasDeriv
    ((wallDerivative_smooth (pureWallMode_smooth σ lam k)).differentiable (by simp))
  have h := (((((hasDerivAt_id z).const_mul k).sin.neg).mul_const k).const_mul
    (σ*exp (-lam*q.1)))
  convert! h using 1 <;> first | rfl | (simp only [pureWallMode_normalDerivative,id_eq,Pi.neg_apply] <;> ring)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PeriodicFamilyCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma flatPhaseMode_angularPeriodic (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (phase : ℝ) :
    AngularPeriodic (2*Real.pi) (flatPhaseMode s h phase) := by
  intro n x
  have he : torusAngular h (x+angularShift (2*Real.pi) n)+phase=
      torusAngular h x+phase+(h 0*n 0+h 1*n 1:ℤ)*(2*Real.pi) := by
    change (h 0:ℝ)*(x 1+2*Real.pi*(n 0:ℝ))+(h 1:ℝ)*(x 2+2*Real.pi*(n 1:ℝ))+phase=
      (h 0:ℝ)*x 1+(h 1:ℝ)*x 2+phase+(h 0*n 0+h 1*n 1:ℤ)*(2*Real.pi)
    push_cast
    ring
  change exp (-torusRate s h*(x 0+0))*cos (torusAngular h (x+angularShift (2*Real.pi) n)+phase)=_
  rw [add_zero,he,cos_add_int_mul_two_pi]
  rfl

lemma flatFourier_angularPeriodic (s : Fin 3 → ℝ) (a phase : (Fin 2 → ℤ) → ℝ) :
    AngularPeriodic (2*Real.pi) (flatFourier s a phase) := by
  intro n x
  unfold flatFourier
  apply tsum_congr
  intro h
  rw [flatPhaseMode_angularPeriodic s h (phase h) n x]

lemma compactifiedFourierTail_angularPeriodic (s : Fin 3 → ℝ) (lam T0 : ℝ)
    (a phase : (Fin 2 → ℤ) → ℝ) (p : ℝ) :
    AngularPeriodic (2*Real.pi) (fun x => compactifiedFourierTail s lam T0 a phase (p,x)) := by
  intro n x
  unfold compactifiedFourierTail
  apply tsum_congr
  intro h
  dsimp [compactifiedFourierTerm]
  have he : x+angularShift (2*Real.pi) n+![T0,0,0]=(x+![T0,0,0])+angularShift (2*Real.pi) n := by abel
  rw [he,flatPhaseMode_angularPeriodic]

lemma exists_normalized_periodic_end_cutoff {R T0 δ : ℝ} (hT : δ-T0 < -R) :
    ∃ ρ : (ℝ×Coord3)→ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) ρ ∧
      tsupport ρ⊆Ioo (-1) 1 ×ˢ {x : Coord3 | δ-T0<x 0} ∧
      (∀ z,ρ z∈Icc 0 1) ∧ (∀ p T,AngularPeriodic T (fun x => ρ (p,x))) ∧
      (∀ p∈Icc (-(1:ℝ)/2) (1/2),∀ x : Coord3, x 0∈Icc (-R) R → ρ (p,x)=1) := by
  let K : Set (ℝ×ℝ) := Icc (-(1:ℝ)/2) (1/2) ×ˢ Icc (-R) R
  let Ω : Set (ℝ×ℝ) := Ioo (-1) 1 ×ˢ Ioo (δ-T0) (R+1)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hΩ : IsOpen Ω := isOpen_Ioo.prod isOpen_Ioo
  have hb : Bornology.IsBounded Ω :=
    ((isCompact_Icc : IsCompact (Icc (-1:ℝ) 1)).isBounded.subset Ioo_subset_Icc_self).prod
      ((isCompact_Icc : IsCompact (Icc (δ-T0) (R+1))).isBounded.subset Ioo_subset_Icc_self)
  have hsub : K⊆Ω := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,
      ⟨hT.trans_le hz.2.1,by linarith [hz.2.2]⟩⟩
  obtain ⟨χ,hχ,hχc,hχs,hχb,hχ1⟩ := exists_smooth_core_cutoff hK hΩ hb hsub
  let Q : (ℝ×Coord3)→(ℝ×ℝ) := fun z => (z.1,z.2 0)
  have hQ : ContDiff ℝ (↑(⊤:ℕ∞)) Q := by dsimp [Q]; fun_prop
  refine ⟨χ ∘ Q,hχ.comp hQ,?_,fun z => hχb _,?_,?_⟩
  · intro z hz
    have he := hχs (tsupport_comp_subset_preimage χ hQ.continuous hz)
    exact ⟨he.1,he.2.1⟩
  · intro p T n x
    change χ (p,x 0+0)=χ (p,x 0)
    rw [add_zero]
  · intro p hp x hx
    exact (hχ1 (p,x 0) ⟨hp,hx⟩).self_of_nhds

theorem exists_smooth_periodic_normalized_tail {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {lam T0 gap B δ R : ℝ} {a phase : (Fin 2→ℤ)→ℝ}
    (hg : 0<gap) (hB : 0≤B) (ha : ∀ h,|a h|≤B) (hδ : 0<δ)
    (hr : ∀ h,a h≠0 → lam+gap≤torusRate s h) (hT : δ-T0 < -R) :
    ∃ f : (ℝ×Coord3)→ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) f ∧
      (∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x))) ∧
      (∀ p≤0,∀ x,f (p,x)=0) ∧
      (∀ p∈Ioc 0 (1/2),∀ x : Coord3,x 0∈Icc (-R) R →
        f (p,x)=exp (lam*(T0+1/p))*flatFourier s a phase (x+![T0+1/p,0,0])) := by
  obtain ⟨ρ,hρ,hρs,hρb,hρp,hρ1⟩ := exists_normalized_periodic_end_cutoff hT
  have hr' : ∀ h,a h≠0 → lam<torusRate s h := fun h hh => by linarith [hr h hh]
  refine ⟨fun z => ρ z*compactifiedFourierTail s lam T0 a phase z,
    smooth_mul_of_support_in_open (isOpen_Ioo.prod (axial_halfspace_open _))
      (compactifiedFourierTail_smooth hs hg hB ha hδ hr) hρ hρs,?_,?_,?_⟩
  · intro p n x
    dsimp only
    exact congrArg₂ (· * ·) (hρp p (2*Real.pi) n x)
      (compactifiedFourierTail_angularPeriodic s lam T0 a phase p n x)
  · intro p hp x
    dsimp only
    rw [compactifiedFourierTail_of_nonpos hr' hp,mul_zero]
  · intro p hp x hx
    dsimp only
    rw [hρ1 p ⟨by linarith [hp.1],hp.2⟩ x hx,one_mul,compactifiedFourierTail_of_pos hr' hp.1]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusLeadingDecay
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma spectral_shift_exp_bound {lam gap rate T R t : ℝ}
    (hlam : 0≤lam) (hgap : 0≤gap) (hrate : lam+gap ≤ rate)
    (hT : R+1≤T) (ht : -R≤t) :
    exp (lam*T)*exp (-rate*(T+t)) ≤
      exp (lam*(R+1))*exp (-gap*(T-R-1))*exp (-rate) := by
  rw [←exp_add,←exp_add,←exp_add]
  apply exp_le_exp.mpr
  have hr : 0 ≤ rate := le_trans (add_nonneg hlam hgap) hrate
  have h1 := mul_nonneg (sub_nonneg.mpr hrate) (show 0≤T-R-1 by linarith)
  have h2 := mul_nonneg hr (show 0≤t+R by linarith)
  nlinarith

lemma flatFourier_shift_uniform_bound {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B lam gap R T : ℝ}
    (ha : ∀ h, |a h|≤B) (hlam : 0≤lam) (hgap : 0≤gap)
    (hsep : ∀ h, a h≠0 → lam+gap≤torusRate s h) (hT : R+1≤T)
    (n : ℕ) {x : Fin 3 → ℝ} (hx : -R≤x 0) :
    exp (lam*T)*‖iteratedFDeriv ℝ n (flatFourier s a phase) (x+![T,0,0])‖ ≤
      (exp (lam*(R+1))*exp (-gap*(T-R-1)))*
        ∑' h, B*((torusRate s h+torusSize h)^n*exp (-torusRate s h)) := by
  have hy : 0<(x+![T,0,0]) 0 := by
    simp only [Pi.add_apply,Matrix.cons_val_zero]; linarith
  rw [flatFourier_iterated hs ha n hy]
  let C := exp (lam*(R+1))*exp (-gap*(T-R-1))
  have hC : 0≤C := by dsimp [C]; positivity
  have hB : 0≤B := (abs_nonneg (a 0)).trans (ha 0)
  have hb : Summable (fun h => B*((torusRate s h+torusSize h)^n*exp (-torusRate s h))) := by
    simpa using (flatMode_derivative_summable hs n (show (0:ℝ)<1 by norm_num)).mul_left B
  have hi (h : Fin 2 → ℤ) :
      exp (lam*T)*‖iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) (x+![T,0,0])‖ ≤
        C*(B*((torusRate s h+torusSize h)^n*exp (-torusRate s h))) := by
    by_cases hz : a h=0
    · simp only [hz,zero_mul,iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero,mul_zero]
      exact mul_nonneg hC (mul_nonneg hB (mul_nonneg (pow_nonneg (add_nonneg (sqrt_nonneg _) (torusSize_nonneg h)) n) (exp_nonneg _)))
    have hp : 0≤(torusRate s h+torusSize h)^n := by
      have := torusSize_nonneg h
      dsimp [torusRate]; positivity
    have h1 := mul_le_mul_of_nonneg_right (ha h) hp
    have h2 := spectral_shift_exp_bound hlam hgap (hsep h hz) hT hx
    have h3 := mul_le_mul h1 h2 (by positivity) (mul_nonneg hB hp)
    have hd := weighted_phase_iterated_bound (s:=s) (h:=h) (phase h) (a h) n (x+![T,0,0])
    apply (mul_le_mul_of_nonneg_left hd (exp_nonneg _)).trans
    simpa only [Pi.add_apply,Matrix.cons_val_zero,C,add_comm,mul_assoc,mul_left_comm,mul_comm] using h3
  have hn : Summable (fun h => ‖iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) (x+![T,0,0])‖) := by
    have hδ : 0<(x+![T,0,0]) 0/2 := by positivity
    exact Summable.of_nonneg_of_le (fun h => norm_nonneg _)
      (fun h => weighted_phase_halfspace_bound ha n h (by linarith : (x+![T,0,0]) 0/2≤(x+![T,0,0]) 0))
      ((flatMode_derivative_summable hs n hδ).mul_left B)
  calc
    _ ≤ exp (lam*T)*(∑' h, ‖iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) (x+![T,0,0])‖) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn) (exp_nonneg _)
    _ = ∑' h, exp (lam*T)*‖iteratedFDeriv ℝ n (fun y => a h*flatPhaseMode s h (phase h) y) (x+![T,0,0])‖ := tsum_mul_left.symm
    _ ≤ ∑' h, C*(B*((torusRate s h+torusSize h)^n*exp (-torusRate s h))) :=
      (hn.mul_left _).tsum_le_tsum hi (hb.mul_left C)
    _ = _ := tsum_mul_left

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusFluxDecay
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma torusCellIntegral_norm_le {T C t : ℝ} (hT : 0≤T) {f : Coord3 → ℝ}
    (hf : ∀ y z,‖f ![t,y,z]‖≤C) : ‖torusCellIntegral T f t‖≤C*T^2 := by
  have hz (y : ℝ) : ‖∫ z in (0:ℝ)..T,f ![t,y,z]‖≤C*T := by
    simpa only [sub_zero,abs_of_nonneg hT] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=T) (fun z _ => hf y z))
  have hy := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=T) (fun y _ => hz y)
  simpa only [sub_zero,abs_of_nonneg hT,torusCellIntegral,pow_two,mul_assoc] using hy

lemma torusCellIntegral_tendsto_zero {T : ℝ} (hT : 0≤T) {f : Coord3 → ℝ} {b : ℝ→ℝ}
    (hb : Tendsto b atTop (𝓝 0)) (hf : ∀ᶠ t in atTop,∀ y z,‖f ![t,y,z]‖≤b t) :
    Tendsto (torusCellIntegral T f) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (hf.mono (fun t ht => torusCellIntegral_norm_le hT ht))
  simpa using hb.mul_const (T^2)

lemma flatFourier_exponential_bound {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B gap : ℝ} (ha : ∀ h,|a h|≤B) (hg : 0≤gap)
    (hr : ∀ h,a h≠0 → gap≤torusRate s h) (n : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ x : Coord3,1≤x 0 →
      ‖iteratedFDeriv ℝ n (flatFourier s a phase) x‖≤C*exp (-gap*(x 0-1)) := by
  let C := ∑' h,B*((torusRate s h+torusSize h)^n*exp (-torusRate s h))
  have hB : 0≤B := (abs_nonneg (a 0)).trans (ha 0)
  refine ⟨C,tsum_nonneg (fun h => ?_),?_⟩
  · have ht := sqrt_nonneg (torusQuadratic s h)
    have hz := torusSize_nonneg h
    exact mul_nonneg hB (mul_nonneg (pow_nonneg (add_nonneg ht hz) n) (exp_nonneg _))
  · intro x hx
    have he : ![0,x 1,x 2]+![x 0,0,0]=x := by ext i; fin_cases i <;> simp
    have hh := flatFourier_shift_uniform_bound (a:=a) (phase:=phase) (lam:=0) (R:=0) (T:=x 0)
      hs ha le_rfl hg (by simpa only [zero_add] using hr) (by simpa using hx)
      n (x:=![0,x 1,x 2]) (by simp)
    rw [he] at hh
    simpa [C,mul_comm] using hh

lemma tendsto_exp_neg_gap {gap : ℝ} (hg : 0<gap) :
    Tendsto (fun t : ℝ => exp (-gap*(t-1))) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  exact (tendsto_atTop_add_const_right atTop (-1) tendsto_id).const_mul_atTop_of_neg (neg_neg_of_pos hg)

lemma flatFourier_mean_axial_flux_zero {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B gap t : ℝ} (ha : ∀ h,|a h|≤B) (hg : 0<gap)
    (hr : ∀ h,a h≠0 → gap≤torusRate s h) (ht : 0<t) :
    torusCellIntegral (2*Real.pi) (fun x => fderiv ℝ (flatFourier s a phase) x (flatAxis 0)) t=0 := by
  apply torus_flux_zero_of_tendsto (F:=flatModeFlux s (flatFourier s a phase)) ht
    (by positivity) (flatModeFlux_smoothOn (axial_halfspace_open 0) (flatFourier_smooth hs ha))
    (flatModeFlux_periodic (flatFourier_angularPeriodic s a phase))
    (fun x hx => flatFourier_flux_divergence hs ha hx)
  obtain ⟨C,hC,hb⟩ := flatFourier_exponential_bound (phase:=phase) hs ha hg.le hr 1
  apply torusCellIntegral_tendsto_zero (by positivity : (0:ℝ)≤2*Real.pi)
    (by simpa using (tendsto_exp_neg_gap hg).const_mul C)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht'
  intro y z
  simp only [flatModeFlux,Matrix.cons_val_zero]
  rw [←neg_mul]
  have hn : ‖flatAxis (0:Fin 3)‖=1 := by simp [flatAxis,Pi.norm_single]
  have hh := (fderiv ℝ (flatFourier s a phase) ![t,y,z]).le_opNorm (flatAxis 0)
  rw [hn,mul_one,←norm_iteratedFDeriv_one] at hh
  exact hh.trans (hb _ ht')

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma coordinateDivergence_smul_at {f : Coord3 → ℝ} {F : Coord3 → Coord3} {x : Coord3}
    (hf : DifferentiableAt ℝ f x) (hF : DifferentiableAt ℝ F x) :
    coordinateDivergence (fun y => f y • F y) x=
      f x*coordinateDivergence F x+fderiv ℝ f x (F x) := by
  have he (i : Fin 3) :
      fderiv ℝ (fun y => (f y • F y) i) x (Pi.single i 1)=
        f x*fderiv ℝ (fun y => F y i) x (Pi.single i 1)+
        F x i*fderiv ℝ f x (Pi.single i 1) := by
    change fderiv ℝ (fun y => f y*F y i) x _=_
    rw [fderiv_fun_mul hf ((hasFDerivAt_pi'.mp hF.hasFDerivAt i).differentiableAt)]
    rfl
  simp only [coordinateDivergence,he,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [←coordinate_fderiv_expansion]

lemma coordinateDivergence_sub_at {F G : Coord3 → Coord3} {x : Coord3}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    coordinateDivergence (fun y => F y-G y) x=coordinateDivergence F x-coordinateDivergence G x := by
  unfold coordinateDivergence
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change fderiv ℝ (fun y => F y i-G y i) x _=_
  rw [fderiv_fun_sub ((hasFDerivAt_pi'.mp hF.hasFDerivAt i).differentiableAt)
    ((hasFDerivAt_pi'.mp hG.hasFDerivAt i).differentiableAt)]
  rfl

lemma flat_flux_pairing (s : Fin 3→ℝ) (f g : Coord3→ℝ) (x : Coord3) :
    fderiv ℝ g x (flatModeFlux s f x)=fderiv ℝ f x (flatModeFlux s g x) := by
  rw [coordinate_fderiv_expansion,coordinate_fderiv_expansion]
  simp only [Fin.sum_univ_three,flatModeFlux,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,flatAxis]
  ring

lemma flatCrossFlux_smoothOn {s : Fin 3→ℝ} {f g : Coord3→ℝ} {U : Set Coord3}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f U)
    (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g U) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (flatCrossFlux s f g) U :=
  (hg.smul (flatModeFlux_smoothOn hU hf)).sub (hf.smul (flatModeFlux_smoothOn hU hg))

lemma flatModeFlux_differentiableAt {s : Fin 3→ℝ} {f : Coord3→ℝ} {x : Coord3}
    (hf : ContDiffAt ℝ (↑(⊤:ℕ∞)) f x) : DifferentiableAt ℝ (flatModeFlux s f) x := by
  have hd := (hf.fderiv_right (m:=1)
    (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))).differentiableAt (by simp)
  have he (i : Fin 3) := hd.clm_apply (differentiableAt_const (flatAxis i))
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i
  · exact he 0
  · exact ((he 1).const_mul _).add ((he 2).const_mul _)
  · exact ((he 1).const_mul _).add ((he 2).const_mul _)

lemma flatCrossFlux_divergence {s : Fin 3→ℝ} {f g : Coord3→ℝ} {x : Coord3}
    (hf : ContDiffAt ℝ (↑(⊤:ℕ∞)) f x) (hg : ContDiffAt ℝ (↑(⊤:ℕ∞)) g x) :
    coordinateDivergence (flatCrossFlux s f g) x=
      g x*flatTensorLaplacian s f x-f x*flatTensorLaplacian s g x := by
  have hfd := hf.differentiableAt (by simp)
  have hgd := hg.differentiableAt (by simp)
  have hff := flatModeFlux_differentiableAt (s:=s) hf
  have hgf := flatModeFlux_differentiableAt (s:=s) hg
  unfold flatCrossFlux
  rw [coordinateDivergence_sub_at (F:=fun y => g y • flatModeFlux s f y)
    (G:=fun y => f y • flatModeFlux s g y) (hgd.smul hff) (hfd.smul hgf),
    coordinateDivergence_smul_at hgd hff,coordinateDivergence_smul_at hfd hgf,
    flatModeFlux_divergence hf,flatModeFlux_divergence hg,flat_flux_pairing s f g x]
  ring

lemma flatCrossFlux_periodic {s : Fin 3→ℝ} {f g : Coord3→ℝ} {T : ℝ}
    (hf : AngularPeriodic T f) (hg : AngularPeriodic T g) : AngularPeriodic T (flatCrossFlux s f g) := by
  intro n x
  unfold flatCrossFlux
  rw [hg n x,hf n x,flatModeFlux_periodic hf n x,flatModeFlux_periodic hg n x]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_TorusMoments
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma coordinateDivergence_smul {f : Coord3 → ℝ} {F : Coord3 → Coord3}
    (hf : Differentiable ℝ f) (hF : Differentiable ℝ F) (x : Coord3) :
    coordinateDivergence (fun y => f y • F y) x=
      f x*coordinateDivergence F x+fderiv ℝ f x (F x) := by
  have he (i : Fin 3) :
      fderiv ℝ (fun y => (f y • F y) i) x (Pi.single i 1)=
        f x*fderiv ℝ (fun y => F y i) x (Pi.single i 1)+
        F x i*fderiv ℝ f x (Pi.single i 1) := by
    change fderiv ℝ (fun y => f y*F y i) x _=_
    rw [fderiv_fun_mul (hf x) ((hasFDerivAt_pi'.mp (hF x).hasFDerivAt i).differentiableAt)]
    rfl
  simp only [coordinateDivergence,he,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [←coordinate_fderiv_expansion]

lemma coordinateDivergence_sub {F G : Coord3 → Coord3}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (x : Coord3) :
    coordinateDivergence (fun y => F y-G y) x=coordinateDivergence F x-coordinateDivergence G x := by
  unfold coordinateDivergence
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change fderiv ℝ (fun y => F y i-G y i) x _=_
  rw [fderiv_fun_sub ((hasFDerivAt_pi'.mp (hF x).hasFDerivAt i).differentiableAt)
    ((hasFDerivAt_pi'.mp (hG x).hasFDerivAt i).differentiableAt)]
  rfl

lemma symmetricCrossFlux_smooth {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (symmetricCrossFlux H u) :=
  (((contDiff_pi.mp hu) 1).smul (symmetricFlux_smooth hH hu 0)).sub
    (((contDiff_pi.mp hu) 0).smul (symmetricFlux_smooth hH hu 1))

lemma symmetricCrossFlux_divergence {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hs : ∀ x,(H x).IsSymm) (x : Coord3) :
    coordinateDivergence (symmetricCrossFlux H u) x=
      u x 1*symmetricSource H u 0 x-u x 0*symmetricSource H u 1 x := by
  have huj (j : Fin 2) := ((contDiff_pi.mp hu) j).differentiable (by simp)
  have hF (j : Fin 2) := (symmetricFlux_smooth hH hu j).differentiable (by simp)
  unfold symmetricCrossFlux
  rw [coordinateDivergence_sub
    (F:=fun y => u y 1 • (H y*gradientColumns (fderiv ℝ u y)).col 0)
    (G:=fun y => u y 0 • (H y*gradientColumns (fderiv ℝ u y)).col 1)
    ((huj 1).smul (hF 0)) ((huj 0).smul (hF 1)),
    coordinateDivergence_smul (huj 1) (hF 0),coordinateDivergence_smul (huj 0) (hF 1),
    potential_component_fderiv (hu.differentiable (by simp)),
    potential_component_fderiv (hu.differentiable (by simp)),symmetric_potential_pairing _ _ (hs x)]
  unfold symmetricSource
  ring

lemma symmetricFlux_periodic {T : ℝ} {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : AngularPeriodic T H) (hu : AngularPeriodic T u) (j : Fin 2) :
    AngularPeriodic T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col j) := by
  intro n x
  dsimp only
  rw [hH n x,hu.fderiv n x]

lemma symmetricCrossFlux_periodic {T : ℝ} {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : AngularPeriodic T H) (hu : AngularPeriodic T u) :
    AngularPeriodic T (symmetricCrossFlux H u) := by
  intro n x
  unfold symmetricCrossFlux
  rw [hH n x,hu n x,hu.fderiv n x]

lemma torus_full_integral_eq_band {T a b : ℝ} (hab : a≤b) {f : Coord3 → ℝ}
    (hs : tsupport f⊆{x | x 0∈Icc a b}) :
    (∫ t,torusCellIntegral T f t)=∫ t in a..b,torusCellIntegral T f t := by
  rw [intervalIntegral.integral_of_le hab,←integral_Icc_eq_integral_Ioc]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hz (y z : ℝ) : f ![t,y,z]=0 := by
    by_contra hh
    exact ht (hs (subset_tsupport f hh))
  simp only [torusCellIntegral,hz,intervalIntegral.integral_zero]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_FlatBackgroundTensor
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma flatBackgroundTensor_flux {s : Fin 3→ℝ} {u : Coord3→Fin 2→ℝ}
    (hu : Differentiable ℝ u) (j : Fin 2) (x : Coord3) :
    (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col j=
      flatModeFlux s (fun y => u y j) x := by
  have hd (i : Fin 3) : gradientColumns (fderiv ℝ u x) i j=
      fderiv ℝ (fun y => u y j) x (flatAxis i) := by
    rw [potential_component_fderiv hu]
    rfl
  ext i
  fin_cases i <;>
    simp [Matrix.col_apply,Fin.sum_univ_three,hd,flatBackgroundTensor,
      flatModeFlux,Fin.reduceFinMk,Matrix.vecMul,dotProduct]

lemma flatBackgroundTensor_source {s : Fin 3→ℝ} {u : Coord3→Fin 2→ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (j : Fin 2) (x : Coord3) :
    symmetricSource (fun _ => flatBackgroundTensor s) u j x=
      flatTensorLaplacian s (fun y => u y j) x := by
  have he : (fun x => (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col j)=
      flatModeFlux s (fun y => u y j) := funext (flatBackgroundTensor_flux (hu.differentiable (by simp)) j)
  unfold symmetricSource
  rw [he,flatModeFlux_divergence (((contDiff_pi.mp hu) j).contDiffAt)]

lemma flatBackgroundTensor_crossFlux {s : Fin 3→ℝ} {u : Coord3→Fin 2→ℝ}
    (hu : Differentiable ℝ u) (x : Coord3) :
    symmetricCrossFlux (fun _ => flatBackgroundTensor s) u x=
      flatCrossFlux s (fun y => u y 0) (fun y => u y 1) x := by
  unfold symmetricCrossFlux flatCrossFlux
  rw [flatBackgroundTensor_flux hu,flatBackgroundTensor_flux hu]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusCrossFluxDecay
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma tendsto_linear_mul_exp_neg_gap {gap : ℝ} (hg : 0<gap) :
    Tendsto (fun t : ℝ => t*exp (-gap*(t-1))) atTop (𝓝 0) := by
  have hy : Tendsto (fun t : ℝ => gap*(t-1)) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-1) tendsto_id).const_mul_atTop hg
  have he := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hy
  have hh := (he.div_const gap).add (tendsto_exp_neg_gap hg)
  have hfun : (fun t : ℝ => (gap*(t-1))^1*exp (-(gap*(t-1)))/gap+exp (-gap*(t-1)))=
      fun t => t*exp (-gap*(t-1)) := by
    ext t
    rw [pow_one,←neg_mul]
    field_simp
    ring
  dsimp only [Function.comp_def] at hh
  rw [hfun] at hh
  simpa using hh

lemma flatCrossFlux_zero_of_bounds {s : Fin 3→ℝ} {f g : Coord3→ℝ}
    (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f {x | 0<x 0})
    (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g {x | 0<x 0})
    (hfp : AngularPeriodic (2*Real.pi) f) (hgp : AngularPeriodic (2*Real.pi) g)
    (hfh : ∀ x,0<x 0 → flatTensorLaplacian s f x=0)
    (hgh : ∀ x,0<x 0 → flatTensorLaplacian s g x=0)
    {A B C D E gap t : ℝ} (hA : 0≤A) (hB : 0≤B) (_ : 0≤C) (hD : 0≤D) (_ : 0≤E)
    (hgap : 0<gap) (ht : 0<t)
    (hb : ∀ x : Coord3,1≤x 0 →
      ‖f x‖≤A*x 0+B ∧ ‖fderiv ℝ f x (flatAxis 0)‖≤C ∧
      ‖g x‖≤D*exp (-gap*(x 0-1)) ∧
      ‖fderiv ℝ g x (flatAxis 0)‖≤E*exp (-gap*(x 0-1))) :
    torusCellIntegral (2*Real.pi) (fun x => flatCrossFlux s f g x 0) t=0 := by
  apply torus_flux_zero_of_tendsto ht (by positivity)
    (flatCrossFlux_smoothOn (axial_halfspace_open 0) hf hg)
    (flatCrossFlux_periodic hfp hgp)
  · intro x hx
    rw [flatCrossFlux_divergence (hf.contDiffAt ((axial_halfspace_open 0).mem_nhds hx))
      (hg.contDiffAt ((axial_halfspace_open 0).mem_nhds hx)),hfh x hx,hgh x hx]
    ring
  · have hlim : Tendsto (fun t : ℝ => (D*C+B*E)*exp (-gap*(t-1))+
        (A*E)*(t*exp (-gap*(t-1)))) atTop (𝓝 0) := by
      simpa using ((tendsto_exp_neg_gap hgap).const_mul (D*C+B*E)).add
        ((tendsto_linear_mul_exp_neg_gap hgap).const_mul (A*E))
    apply torusCellIntegral_tendsto_zero (by positivity) hlim
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht'
    intro y z
    obtain ⟨hfb,hfd,hgb,hgd⟩ := hb ![t,y,z] ht'
    have hAB : 0≤A*t+B := add_nonneg (mul_nonneg hA (le_trans zero_le_one ht')) hB
    calc
      _ ≤ ‖g ![t,y,z]‖*‖fderiv ℝ f ![t,y,z] (flatAxis 0)‖+
          ‖f ![t,y,z]‖*‖fderiv ℝ g ![t,y,z] (flatAxis 0)‖ := by
        simpa only [flatCrossFlux,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,flatModeFlux,
          Matrix.cons_val_zero,norm_mul] using norm_sub_le
          (g ![t,y,z]*fderiv ℝ f ![t,y,z] (flatAxis 0))
          (f ![t,y,z]*fderiv ℝ g ![t,y,z] (flatAxis 0))
      _ ≤ (D*exp (-gap*(t-1)))*C+(A*t+B)*(E*exp (-gap*(t-1))) :=
        add_le_add (mul_le_mul hgb hfd (norm_nonneg _) (mul_nonneg hD (exp_nonneg _)))
          (mul_le_mul hfb hgd (norm_nonneg _) hAB)
      _ = _ := by ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AffineFourierField
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatTensorLaplacian_add {s : Fin 3→ℝ} {f g : Coord3→ℝ} {x : Coord3}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    flatTensorLaplacian s (fun y => f y+g y) x=
      flatTensorLaplacian s f x+flatTensorLaplacian s g x := by
  unfold flatTensorLaplacian
  rw [fun_iteratedFDeriv_add_apply hf hg,map_add]

lemma axial_affine_fderiv (α β : ℝ) (x : Coord3) :
    fderiv ℝ (fun y : Coord3 => α*y 0+β) x=α • ContinuousLinearMap.proj 0 := by
  have hh := (((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 3 => ℝ) 0).hasFDerivAt (x:=x)).const_mul α).add_const β
  exact hh.fderiv

lemma flatTensorLaplacian_axial_affine (s : Fin 3→ℝ) (α β : ℝ) (x : Coord3) :
    flatTensorLaplacian s (fun y => α*y 0+β) x=0 := by
  have he : fderiv ℝ (fun y : Coord3 => α*y 0+β)=fun _ => α • ContinuousLinearMap.proj 0 :=
    funext (axial_affine_fderiv α β)
  unfold flatTensorLaplacian flatTensorLaplacianCLM
  simp only [_root_.add_apply,_root_.smul_apply,
    ContinuousMultilinearMap.apply_apply,smul_eq_mul,iteratedFDeriv_two_apply,he,
    fderiv_fun_const,Pi.zero_apply,_root_.zero_apply,mul_zero,add_zero]

lemma affineFourierField_smooth {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B) (α β : ℝ) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (affineFourierField s a phase α β) {x | 0<x 0} :=
  (show ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : Coord3 => α*x 0+β) by fun_prop).contDiffOn.add
    (flatFourier_smooth hs ha)

lemma affineFourierField_periodic (s : Fin 3→ℝ) (a phase : (Fin 2→ℤ)→ℝ) (α β : ℝ) :
    AngularPeriodic (2*Real.pi) (affineFourierField s a phase α β) := by
  intro n x
  unfold affineFourierField
  rw [flatFourier_angularPeriodic s a phase n x]
  change α*(x 0+0)+β+_=α*x 0+β+_
  rw [add_zero]

lemma affineFourierField_harmonic {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B) (α β : ℝ)
    {x : Coord3} (hx : 0<x 0) : flatTensorLaplacian s (affineFourierField s a phase α β) x=0 := by
  have hf := (flatFourier_smooth (phase:=phase) hs ha).contDiffAt ((axial_halfspace_open 0).mem_nhds hx)
  unfold affineFourierField
  rw [flatTensorLaplacian_add (by fun_prop)
    (hf.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))),
    flatTensorLaplacian_axial_affine,flatFourier_harmonic hs ha hx,add_zero]

lemma affineFourierField_fderiv {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B) (α β : ℝ)
    {x : Coord3} (hx : 0<x 0) :
    fderiv ℝ (affineFourierField s a phase α β) x=
      α • ContinuousLinearMap.proj 0+fderiv ℝ (flatFourier s a phase) x := by
  unfold affineFourierField
  rw [fderiv_fun_add (by fun_prop) (((flatFourier_smooth hs ha).contDiffAt
    ((axial_halfspace_open 0).mem_nhds hx)).differentiableAt (by simp)),axial_affine_fderiv]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierEndConcomitant
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatFourier_value_derivative_decay {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B gap : ℝ} (ha : ∀ h,|a h|≤B) (hg : 0≤gap)
    (hr : ∀ h,a h≠0 → gap≤torusRate s h) :
    ∃ C D : ℝ,0≤C ∧ 0≤D ∧ ∀ x : Coord3,1≤x 0 →
      ‖flatFourier s a phase x‖≤C*exp (-gap*(x 0-1)) ∧
      ‖fderiv ℝ (flatFourier s a phase) x (flatAxis 0)‖≤D*exp (-gap*(x 0-1)) := by
  obtain ⟨C,hC,hb⟩ := flatFourier_exponential_bound (phase:=phase) hs ha hg hr 0
  obtain ⟨D,hD,hd⟩ := flatFourier_exponential_bound (phase:=phase) hs ha hg hr 1
  refine ⟨C,D,hC,hD,fun x hx => ⟨?_,?_⟩⟩
  · simpa only [norm_iteratedFDeriv_zero] using hb x hx
  · have hh := (fderiv ℝ (flatFourier s a phase) x).le_opNorm (flatAxis 0)
    have hn : ‖flatAxis (0:Fin 3)‖=1 := by simp [flatAxis,Pi.norm_single]
    rw [hn,mul_one,←norm_iteratedFDeriv_one] at hh
    exact hh.trans (hd x hx)

theorem affine_fourier_cross_flux_zero {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a b pa pb : (Fin 2→ℤ)→ℝ} {Ba Bb ga gb t : ℝ}
    (ha : ∀ h,|a h|≤Ba) (hb : ∀ h,|b h|≤Bb) (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h) (hrb : ∀ h,b h≠0 → gb≤torusRate s h)
    (α β : ℝ) (ht : 0<t) :
    torusCellIntegral (2*Real.pi)
      (fun x => flatCrossFlux s (affineFourierField s a pa α β) (flatFourier s b pb) x 0) t=0 := by
  obtain ⟨C,D,hC,hD,hbd⟩ := flatFourier_value_derivative_decay (phase:=pa) hs ha hga.le hra
  obtain ⟨E,F,hE,hF,hbf⟩ := flatFourier_value_derivative_decay (phase:=pb) hs hb hgb.le hrb
  apply flatCrossFlux_zero_of_bounds
    (affineFourierField_smooth hs ha α β) (flatFourier_smooth hs hb)
    (affineFourierField_periodic s a pa α β) (flatFourier_angularPeriodic s b pb)
    (fun _ hx => affineFourierField_harmonic hs ha α β hx)
    (fun _ hx => flatFourier_harmonic hs hb hx)
    (A:=|α|) (B:=|β|+C) (C:=|α|+D) (D:=E) (E:=F)
    (abs_nonneg _) (add_nonneg (abs_nonneg _) hC) (add_nonneg (abs_nonneg _) hD)
    hE hF hgb ht
  intro x hx
  have hxp : 0<x 0 := lt_of_lt_of_le zero_lt_one hx
  have he : exp (-ga*(x 0-1))≤1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hga.le) (sub_nonneg.mpr hx))
  have h1 := (hbd x hx).1.trans (by simpa using mul_le_mul_of_nonneg_left he hC)
  have h2 := (hbd x hx).2.trans (by simpa using mul_le_mul_of_nonneg_left he hD)
  refine ⟨?_,?_,(hbf x hx).1,(hbf x hx).2⟩
  · change ‖α*x 0+β+flatFourier s a pa x‖≤_
    calc
      _ ≤ (‖α*x 0‖+‖β‖)+‖flatFourier s a pa x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ |α| *x 0+|β|+C := by
        simpa [norm_mul,Real.norm_eq_abs,abs_of_pos hxp] using add_le_add_left h1 (‖α*x 0‖+‖β‖)
      _ = _ := by ring
  · rw [affineFourierField_fderiv hs ha α β hxp]
    have heq : (α • (ContinuousLinearMap.proj 0 : Coord3→L[ℝ]ℝ)+fderiv ℝ (flatFourier s a pa) x) (flatAxis 0)=
        α+fderiv ℝ (flatFourier s a pa) x (flatAxis 0) := by simp [flatAxis]
    rw [heq]
    exact (norm_add_le _ _).trans (by simpa only [Real.norm_eq_abs] using add_le_add (le_refl |α|) h2)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusIntegralAlgebra
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma torusCellIntegral_eq_box {T t : ℝ} (hT : 0≤T) {f : Coord3→ℝ}
    (hf : Continuous (fun x : Fin 2→ℝ => f ![t,x 0,x 1])) :
    torusCellIntegral T f t=∫ x in Icc (0:Fin 2→ℝ) (fun _ => T),f ![t,x 0,x 1] := by
  symm
  simpa only [torusCellIntegral,Pi.zero_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using
    integral_coord2_Icc (a:=(0:Fin 2→ℝ)) (b:=fun _ => T) (fun _ => hT) hf

lemma torusCellIntegral_add {T t : ℝ} (hT : 0≤T) {f g : Coord3→ℝ}
    (hf : Continuous (fun x : Fin 2→ℝ => f ![t,x 0,x 1]))
    (hg : Continuous (fun x : Fin 2→ℝ => g ![t,x 0,x 1])) :
    torusCellIntegral T (fun x => f x+g x) t=torusCellIntegral T f t+torusCellIntegral T g t := by
  rw [torusCellIntegral_eq_box hT (hf.add hg),torusCellIntegral_eq_box hT hf,
    torusCellIntegral_eq_box hT hg]
  exact integral_add (hf.continuousOn.integrableOn_compact isCompact_Icc)
    (hg.continuousOn.integrableOn_compact isCompact_Icc)

lemma torusCellIntegral_const (T t c : ℝ) : torusCellIntegral T (fun _ => c) t=T^2*c := by
  simp only [torusCellIntegral,intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  ring

lemma halfspace_slice_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ t : ℝ} {f : Coord3→E} (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f {x | δ<x 0}) (ht : δ<t) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Fin 2→ℝ => f ![t,y 0,y 1]) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have hc : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Fin 2→ℝ => ![t,y 0,y 1]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact (hf.contDiffAt ((axial_halfspace_open δ).mem_nhds ht)).comp y hc.contDiffAt

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierEndFlux
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

theorem affine_fourier_mean_axial_flux {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B gap t : ℝ} (ha : ∀ h,|a h|≤B) (hg : 0<gap)
    (hr : ∀ h,a h≠0 → gap≤torusRate s h) (α β : ℝ) (ht : 0<t) :
    torusCellIntegral (2*Real.pi) (fun x => fderiv ℝ (affineFourierField s a phase α β) x (flatAxis 0)) t=
      (2*Real.pi)^2*α := by
  have hf := flatFourier_smooth (phase:=phase) hs ha
  have hd := (hf.fderiv_of_isOpen (axial_halfspace_open 0) (m:=↑(⊤:ℕ∞)) (by simp)).clm_apply
    (contDiffOn_const (c:=flatAxis 0))
  have hc := (halfspace_slice_smooth hd ht).continuous
  have he : torusCellIntegral (2*Real.pi)
      (fun x => fderiv ℝ (affineFourierField s a phase α β) x (flatAxis 0)) t=
      torusCellIntegral (2*Real.pi) (fun x => α+fderiv ℝ (flatFourier s a phase) x (flatAxis 0)) t := by
    apply intervalIntegral.integral_congr
    intro y _
    apply intervalIntegral.integral_congr
    intro z _
    change fderiv ℝ (affineFourierField s a phase α β) ![t,y,z] (flatAxis 0)=_
    rw [affineFourierField_fderiv hs ha α β (x:=![t,y,z]) ht]
    simp [flatAxis]
  rw [he,torusCellIntegral_add (by positivity) continuous_const hc,
    torusCellIntegral_const,flatFourier_mean_axial_flux_zero hs ha hg hr ht,add_zero]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierPairFlux
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma torusCellIntegral_congr_slice {T t : ℝ} {f g : Coord3 → ℝ}
    (h : ∀ x,x 0=t → f x=g x) : torusCellIntegral T f t=torusCellIntegral T g t := by
  apply intervalIntegral.integral_congr
  intro y _
  apply intervalIntegral.integral_congr
  intro z _
  exact h ![t,y,z] rfl

theorem fourier_pair_boundary_flux {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a b pa pb : (Fin 2 → ℤ) → ℝ} {Ba Bb ga gb t : ℝ}
    (ha : ∀ h,|a h|≤Ba) (hb : ∀ h,|b h|≤Bb) (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h) (hrb : ∀ h,b h≠0 → gb≤torusRate s h)
    (α β : ℝ) (ht : 0<t) {u : Coord3 → Fin 2 → ℝ}
    (hu : Differentiable ℝ u)
    (he0 : ∀ x,x 0=t → (fun y => u y 0)=ᶠ[𝓝 x] affineFourierField s a pa α β)
    (he1 : ∀ x,x 0=t → (fun y => u y 1)=ᶠ[𝓝 x] flatFourier s b pb) :
    torusCellIntegral (2*Real.pi)
      (fun x => (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col 0 0) t=(2*Real.pi)^2*α ∧
    torusCellIntegral (2*Real.pi)
      (fun x => (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col 1 0) t=0 ∧
    torusCellIntegral (2*Real.pi) (fun x => symmetricCrossFlux (fun _ => flatBackgroundTensor s) u x 0) t=0 := by
  have hf0 := torusCellIntegral_congr_slice (T:=2*Real.pi)
    (f:=fun x => (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col 0 0)
    (g:=fun x => fderiv ℝ (affineFourierField s a pa α β) x (flatAxis 0))
    (fun x hx => by
      rw [flatBackgroundTensor_flux hu]
      change fderiv ℝ (fun y => u y 0) x (flatAxis 0)=_
      rw [(he0 x hx).fderiv_eq])
  have hf1 := torusCellIntegral_congr_slice (T:=2*Real.pi)
    (f:=fun x => (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col 1 0)
    (g:=fun x => fderiv ℝ (flatFourier s b pb) x (flatAxis 0))
    (fun x hx => by
      rw [flatBackgroundTensor_flux hu]
      change fderiv ℝ (fun y => u y 1) x (flatAxis 0)=_
      rw [(he1 x hx).fderiv_eq])
  have hfc := torusCellIntegral_congr_slice (T:=2*Real.pi)
    (f:=fun x => symmetricCrossFlux (fun _ => flatBackgroundTensor s) u x 0)
    (g:=fun x => flatCrossFlux s (affineFourierField s a pa α β) (flatFourier s b pb) x 0)
    (fun x hx => by
      rw [flatBackgroundTensor_crossFlux hu]
      change u x 1*fderiv ℝ (fun y => u y 0) x (flatAxis 0)-
        u x 0*fderiv ℝ (fun y => u y 1) x (flatAxis 0)=_
      have hv0 : u x 0=affineFourierField s a pa α β x := (he0 x hx).self_of_nhds
      have hv1 : u x 1=flatFourier s b pb x := (he1 x hx).self_of_nhds
      rw [(he0 x hx).fderiv_eq,(he1 x hx).fderiv_eq,hv0,hv1]
      rfl)
  exact ⟨hf0.trans (affine_fourier_mean_axial_flux hs ha hga hra α β ht),
    hf1.trans (flatFourier_mean_axial_flux_zero hs hb hgb hrb ht),
    hfc.trans (affine_fourier_cross_flux_zero hs ha hb hga hgb hra hrb α β ht)⟩

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatFourier_add {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a b phase : (Fin 2 → ℤ) → ℝ} {A B : ℝ}
    (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B) {x : Coord3} (hx : 0<x 0) :
    flatFourier s (fun h => a h+b h) phase x=flatFourier s a phase x+flatFourier s b phase x := by
  unfold flatFourier
  simp only [add_mul]
  exact (flatFourier_summable hs ha hx).tsum_add (flatFourier_summable hs hb hx)

lemma flatFourier_single (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (c : ℝ)
    (phase : (Fin 2 → ℤ) → ℝ) (x : Coord3) :
    flatFourier s (Pi.single h c) phase x=c*flatPhaseMode s h (phase h) x := by
  classical
  unfold flatFourier
  rw [tsum_eq_single h]
  · simp
  · intro k hk
    simp [Pi.single_eq_of_ne hk]

lemma flatFourier_zero (s : Fin 3 → ℝ) (phase : (Fin 2 → ℤ) → ℝ) (x : Coord3) :
    flatFourier s (fun _ => 0) phase x=0 := by simp [flatFourier]

lemma flatFourier_const_mul (s : Fin 3 → ℝ) (a phase : (Fin 2 → ℤ) → ℝ) (c : ℝ) (x : Coord3) :
    flatFourier s (fun h => c*a h) phase x=c*flatFourier s a phase x := by
  simp only [flatFourier,mul_assoc,tsum_mul_left]

lemma flatFourier_translation (s : Fin 3 → ℝ) (a phase : (Fin 2 → ℤ) → ℝ) (T : ℝ) (x : Coord3) :
    flatFourier s a phase (x+![T,0,0])=
      flatFourier s (fun h => a h*exp (-torusRate s h*T)) phase x := by
  unfold flatFourier
  apply tsum_congr
  intro h
  rw [flatPhaseMode_translation]
  ring

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma normalizedFourierCoefficients_zero_iff (s : Fin 3 → ℝ) (lam T : ℝ)
    (a : (Fin 2 → ℤ) → ℝ) (h : Fin 2 → ℤ) :
    normalizedFourierCoefficients s lam T a h=0 ↔ a h=0 := by
  simp [normalizedFourierCoefficients,exp_ne_zero]

lemma normalizedFourierCoefficients_bound {s : Fin 3 → ℝ} {lam T B : ℝ}
    {a : (Fin 2 → ℤ) → ℝ} (ha : ∀ h,|a h|≤B) (hT : 0≤T)
    (hr : ∀ h,a h≠0 → lam≤torusRate s h) (h : Fin 2 → ℤ) :
    |normalizedFourierCoefficients s lam T a h|≤B := by
  by_cases hz : a h=0
  · simpa only [normalizedFourierCoefficients,hz,zero_mul,abs_zero] using
      (abs_nonneg (a h)).trans (ha h)
  have he : exp (-(torusRate s h-lam)*T)≤1 := exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr (hr h hz))) hT)
  rw [normalizedFourierCoefficients,abs_mul,abs_of_pos (exp_pos _)]
  exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans (by simpa using ha h)

lemma flatFourier_normalized_translation (s : Fin 3 → ℝ) (lam T : ℝ)
    (a phase : (Fin 2 → ℤ) → ℝ) (x : Coord3) :
    flatFourier s (normalizedFourierCoefficients s lam T a) phase x=
      exp (lam*T)*flatFourier s a phase (x+![T,0,0]) := by
  rw [flatFourier_translation,←flatFourier_const_mul]
  unfold flatFourier
  apply tsum_congr
  intro h
  have he : exp (-(torusRate s h-lam)*T)=exp (lam*T)*exp (-torusRate s h*T) := by
    rw [←exp_add]
    congr 1
    ring
  simp only [normalizedFourierCoefficients,he]
  ring

lemma pureWallMode_eq_flatPhaseMode (s : Fin 3 → ℝ) (k : ℤ) (x : Coord3) :
    pureWallMode 1 (torusRate s ![0,k]) (k:ℝ) (boxCoordinates x)=flatPhaseMode s ![0,k] 0 x := by
  simp [pureWallMode,flatPhaseMode,torusAngular,boxCoordinates_apply]

lemma single_fourier_coeff_bound (h : Fin 2 → ℤ) (k : Fin 2 → ℤ) : |(Pi.single h (1:ℝ) : (Fin 2 → ℤ) → ℝ) k|≤1 := by
  classical
  by_cases hk : k=h
  · subst k; simp
  · simp [Pi.single_eq_of_ne hk]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierMatchingInterpolation
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma fourierMatchingCutoff_smooth : ContDiff ℝ (↑(⊤:ℕ∞)) fourierMatchingCutoff :=
  contDiff_const.sub (smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const 2))

lemma fourierMatchingCutoff_left {t : ℝ} (ht : t≤2) : fourierMatchingCutoff t=1 := by
  rw [fourierMatchingCutoff,smoothTransition.zero_of_nonpos (by linarith),sub_zero]

lemma fourierMatchingCutoff_right {t : ℝ} (ht : 4≤t) : fourierMatchingCutoff t=0 := by
  rw [fourierMatchingCutoff,smoothTransition.one_of_one_le (by linarith),sub_self]

lemma fourierMatchingPair_smooth (s : Fin 3 → ℝ) (k : ℤ) {f g : ℝ×Coord3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤:ℕ∞)) g) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fourierMatchingPair s k f g) := by
  have ht : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : ℝ×Coord3 => z.2 0) :=
    (contDiff_apply ℝ ℝ (0:Fin 3)).comp contDiff_snd
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact ht.add ((fourierMatchingCutoff_smooth.comp ht).mul hf)
  · exact ((flatPhaseMode_smooth s ![0,k] 0).comp contDiff_snd).add
      ((fourierMatchingCutoff_smooth.comp ht).mul hg)

lemma fourierMatchingPair_periodic (s : Fin 3 → ℝ) (k : ℤ) {f g : ℝ×Coord3 → ℝ}
    (hf : ∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x)))
    (hg : ∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x))) (p : ℝ) :
    AngularPeriodic (2*Real.pi) (fun x => fourierMatchingPair s k f g (p,x)) := by
  intro n x
  dsimp only [fourierMatchingPair]
  have hfe : f (p,x+angularShift (2*Real.pi) n)=f (p,x) := hf p n x
  have hge : g (p,x+angularShift (2*Real.pi) n)=g (p,x) := hg p n x
  rw [hfe,hge,flatPhaseMode_angularPeriodic s ![0,k] 0 n x]
  have he : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  rw [he]

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma fourierResidualCutoff_one {t : ℝ} (ht : t∈Icc 2 4) : fourierResidualCutoff t=1 := by
  rw [fourierResidualCutoff,smoothTransition.one_of_one_le (by linarith [ht.1]),
    smoothTransition.one_of_one_le (by linarith [ht.2]),mul_one]
lemma fourierResidualCutoff_zero_left {t : ℝ} (ht : t≤1) : fourierResidualCutoff t=0 := by
  rw [fourierResidualCutoff,smoothTransition.zero_of_nonpos (by linarith),zero_mul]
lemma fourierResidualCutoff_zero_right {t : ℝ} (ht : 5≤t) : fourierResidualCutoff t=0 := by
  rw [fourierResidualCutoff,smoothTransition.zero_of_nonpos (show 5-t≤0 by linarith),mul_zero]

lemma fourierMatchingResidual_support (s : Fin 3 → ℝ) (k : ℤ) (f g : ℝ×Coord3 → ℝ)
    (p : ℝ) (j : Fin 2) :
    tsupport (fun x => fourierMatchingResidual s k f g j (p,x))⊆{x | x 0∈Icc 1 5} := by
  apply closure_minimal _ (isClosed_Icc.preimage (continuous_apply 0))
  intro x hx
  constructor
  · by_contra hh
    exact hx (by simp only [fourierMatchingResidual,fourierResidualCutoff_zero_left (le_of_not_ge hh),neg_zero,zero_mul])
  · by_contra hh
    exact hx (by simp only [fourierMatchingResidual,fourierResidualCutoff_zero_right (le_of_not_ge hh),neg_zero,zero_mul])

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusLocalizedMoments
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma torus_band_integral_congr {T a b : ℝ} (hab : a≤b) {f g : Coord3 → ℝ}
    (h : ∀ x,x 0∈Icc a b  →  f x=g x) :
    (∫ t in a..b,torusCellIntegral T f t)=∫ t in a..b,torusCellIntegral T g t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t∈Icc a b := by simpa only [uIcc_of_le hab] using ht
  apply intervalIntegral.integral_congr
  intro y _
  apply intervalIntegral.integral_congr
  intro z _
  exact h ![t,y,z] ht'

theorem periodic_localized_source_moment_formula {T a b : ℝ} (hT : 0≤T) (hab : a≤b)
    {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ} {r : Fin 2 → Coord3 → ℝ}
    (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hHp : AngularPeriodic T H) (hup : AngularPeriodic T u) (hHs : ∀ x,(H x).IsSymm)
    (hrs : ∀ j,tsupport (r j)⊆{x | x 0∈Icc a b})
    (hre : ∀ j x,x 0∈Icc a b  →  r j x=symmetricSource H u j x) :
    periodicSourceMoment T u r=
      ![torusCellIntegral T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col 0 0) b-
          torusCellIntegral T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col 0 0) a,
        torusCellIntegral T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col 1 0) b-
          torusCellIntegral T (fun x => (H x*gradientColumns (fderiv ℝ u x)).col 1 0) a,
        torusCellIntegral T (fun x => symmetricCrossFlux H u x 0) b-
          torusCellIntegral T (fun x => symmetricCrossFlux H u x 0) a] := by
  have hmain (j : Fin 2) := (torus_full_integral_eq_band hab (hrs j)).trans
    ((torus_band_integral_congr (T:=T) hab (hre j)).trans
      (torus_band_divergence hT hab (symmetricFlux_smooth hH hu j) (symmetricFlux_periodic hHp hup j)))
  have hts : tsupport (fun x => u x 1*r 0 x-u x 0*r 1 x)⊆{x | x 0∈Icc a b} :=
    (tsupport_sub _ _).trans (union_subset
      (tsupport_mul_subset_right.trans (hrs 0)) (tsupport_mul_subset_right.trans (hrs 1)))
  have hc := torus_full_integral_eq_band (T:=T) hab hts
  have he := torus_band_integral_congr (T:=T) hab (f:=fun x => u x 1*r 0 x-u x 0*r 1 x)
    (g:=coordinateDivergence (symmetricCrossFlux H u)) (fun x hx => by
      rw [symmetricCrossFlux_divergence hH hu hHs,hre 0 x hx,hre 1 x hx])
  have hd := torus_band_divergence hT hab (symmetricCrossFlux_smooth hH hu)
    (symmetricCrossFlux_periodic hHp hup)
  ext i
  fin_cases i
  · exact hmain 0
  · exact hmain 1
  · exact hc.trans (he.trans hd)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierMatchingLocalData
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatTensorLaplacian_congr_nhds (s : Fin 3 → ℝ) {f g : Coord3 → ℝ} {x : Coord3}
    (h : f=ᶠ[𝓝 x] g) : flatTensorLaplacian s f x=flatTensorLaplacian s g x :=
  congrArg (flatTensorLaplacianCLM s) ((h.iteratedFDeriv ℝ 2).self_of_nhds)

lemma fourier_left_coeff_bound {k : ℤ} {b : (Fin 2 → ℤ) → ℝ} {B : ℝ}
    (hb : ∀ h,|b h|≤B) (h : Fin 2 → ℤ) :
    |(Pi.single ![0,k] (1:ℝ) : (Fin 2 → ℤ) → ℝ) h+b h|≤1+B :=
  (abs_add_le _ _).trans (add_le_add (single_fourier_coeff_bound _ _) (hb h))

lemma fourierMatchingPair_left_fourier {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (k : ℤ) {f g : ℝ×Coord3 → ℝ} {a b pa pb : (Fin 2 → ℤ) → ℝ} {B p : ℝ}
    (hb : ∀ h,|b h|≤B) (hp : pb ![0,k]=0)
    (hf : ∀ y : Coord3,y 0∈Icc 0 6 → f (p,y)=flatFourier s a pa y)
    (hg : ∀ y : Coord3,y 0∈Icc 0 6 → g (p,y)=flatFourier s b pb y)
    {x : Coord3} (hx : x 0∈Ioo 0 2) :
    (fun y => fourierMatchingPair s k f g (p,y) 0)=ᶠ[𝓝 x] affineFourierField s a pa 1 0 ∧
    (fun y => fourierMatchingPair s k f g (p,y) 1)=ᶠ[𝓝 x]
      flatFourier s (fun h => (Pi.single ![0,k] (1:ℝ) : (Fin 2 → ℤ) → ℝ) h+b h) pb := by
  have hn : ∀ᶠ y in 𝓝 x,y 0∈Ioo 0 2 :=
    (isOpen_Ioo.preimage (continuous_apply 0)).mem_nhds hx
  constructor
  · filter_upwards [hn] with y hy
    change y 0+fourierMatchingCutoff (y 0)*f (p,y)=_
    rw [fourierMatchingCutoff_left hy.2.le,one_mul,hf y ⟨hy.1.le,by linarith [hy.2]⟩]
    simp only [affineFourierField,one_mul,add_zero]
  · filter_upwards [hn] with y hy
    change flatPhaseMode s ![0,k] 0 y+fourierMatchingCutoff (y 0)*g (p,y)=_
    rw [fourierMatchingCutoff_left hy.2.le,one_mul,hg y ⟨hy.1.le,by linarith [hy.2]⟩,
      flatFourier_add hs (single_fourier_coeff_bound ![0,k]) hb hy.1,
      flatFourier_single,hp,one_mul]

lemma fourierMatchingPair_right_fourier (s : Fin 3 → ℝ) (k : ℤ) (f g : ℝ×Coord3 → ℝ)
    (pa pb : (Fin 2 → ℤ) → ℝ) (hp : pb ![0,k]=0) (p : ℝ) {x : Coord3} (hx : 4<x 0) :
    (fun y => fourierMatchingPair s k f g (p,y) 0)=ᶠ[𝓝 x] affineFourierField s (fun _ => 0) pa 1 0 ∧
    (fun y => fourierMatchingPair s k f g (p,y) 1)=ᶠ[𝓝 x] flatFourier s (Pi.single ![0,k] 1) pb := by
  have hn : ∀ᶠ y in 𝓝 x,4<y 0 := (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hx
  constructor
  · filter_upwards [hn] with y hy
    change y 0+fourierMatchingCutoff (y 0)*f (p,y)=_
    simp only [fourierMatchingCutoff_right hy.le,zero_mul,add_zero,affineFourierField,
      flatFourier_zero,one_mul]
  · filter_upwards [hn] with y hy
    change flatPhaseMode s ![0,k] 0 y+fourierMatchingCutoff (y 0)*g (p,y)=_
    rw [fourierMatchingCutoff_right hy.le,zero_mul,add_zero,flatFourier_single,hp,one_mul]

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma periodicSourceMoment_neg (T : ℝ) (u : Coord3 → Fin 2 → ℝ) (r : Fin 2 → Coord3 → ℝ) :
    periodicSourceMoment T u (fun j x => -r j x)=-periodicSourceMoment T u r := by
  have hpoint (x : Coord3) : u x 1*(-r 0 x)-u x 0*(-r 1 x)=
      -(u x 1*r 0 x-u x 0*r 1 x) := by ring
  ext i
  fin_cases i
  · change (∫ t,∫ y in 0..T,∫ z in 0..T,-r 0 ![t,y,z])=-(∫ t,∫ y in 0..T,∫ z in 0..T,r 0 ![t,y,z])
    simp only [intervalIntegral.integral_neg,integral_neg]
  · change (∫ t,∫ y in 0..T,∫ z in 0..T,-r 1 ![t,y,z])=-(∫ t,∫ y in 0..T,∫ z in 0..T,r 1 ![t,y,z])
    simp only [intervalIntegral.integral_neg,integral_neg]
  · change (∫ t,∫ y in 0..T,∫ z in 0..T,u ![t,y,z] 1*(-r 0 ![t,y,z])-u ![t,y,z] 0*(-r 1 ![t,y,z]))=
        -(∫ t,∫ y in 0..T,∫ z in 0..T,u ![t,y,z] 1*r 0 ![t,y,z]-u ![t,y,z] 0*r 1 ![t,y,z])
    simp only [hpoint,intervalIntegral.integral_neg,integral_neg]

theorem fourier_matching_three_moments {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a b : Fin 2 → (Fin 2 → ℤ) → ℝ} {pa pb : Fin 2 → (Fin 2 → ℤ) → ℝ}
    {Ba Bb ga gb : Fin 2 → ℝ} {l d α : ℝ} {β : Fin 2 → ℝ}
    (ha : ∀ e h,|a e h|≤Ba e) (hb : ∀ e h,|b e h|≤Bb e)
    (hga : ∀ e,0<ga e) (hgb : ∀ e,0<gb e)
    (hra : ∀ e h,a e h≠0 → ga e≤torusRate s h)
    (hrb : ∀ e h,b e h≠0 → gb e≤torusRate s h)
    (hl : 0<l) (hld : l≤d) {u : Coord3 → Fin 2 → ℝ} {r : Fin 2 → Coord3 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (hup : AngularPeriodic (2*Real.pi) u)
    (he0 : ∀ e x,x 0=![l,d] e → (fun y => u y 0)=ᶠ[𝓝 x] affineFourierField s (a e) (pa e) α (β e))
    (he1 : ∀ e x,x 0=![l,d] e → (fun y => u y 1)=ᶠ[𝓝 x] flatFourier s (b e) (pb e))
    (hrs : ∀ j,tsupport (r j)⊆{x | x 0∈Icc l d})
    (hre : ∀ j x,x 0∈Icc l d → r j x=symmetricSource (fun _ => flatBackgroundTensor s) u j x) :
    periodicSourceMoment (2*Real.pi) u r=0 ∧
      periodicSourceMoment (2*Real.pi) u (fun j x => -r j x)=0 := by
  have ht (e : Fin 2) : 0<![l,d] e := by fin_cases e; exact hl; exact hl.trans_le hld
  have he (e : Fin 2) := fourier_pair_boundary_flux hs (ha e) (hb e) (hga e) (hgb e)
    (hra e) (hrb e) α (β e) (ht e) (hu.differentiable (by simp)) (he0 e) (he1 e)
  have heL := he 0
  have heR := he 1
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at heL heR
  have hm := periodic_localized_source_moment_formula (by positivity : 0≤2*Real.pi) hld
    (H:=fun _ => flatBackgroundTensor s) contDiff_const hu (fun _ _ => rfl) hup
    (fun _ => flatBackgroundTensor_symm s) hrs hre
  have hz : periodicSourceMoment (2*Real.pi) u r=0 := by
    rw [hm]
    ext i
    fin_cases i
    · change _-_=0
      rw [heR.1,heL.1,sub_self]
    · change _-_=0
      rw [heR.2.1,heL.2.1,sub_self]
    · change _-_=0
      rw [heR.2.2,heL.2.2,sub_self]
  exact ⟨hz,by rw [periodicSourceMoment_neg,hz,neg_zero]⟩

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma fourierMatchingResidual_exact {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (k : ℤ) {f g : ℝ×Coord3 → ℝ} {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B p : ℝ}
    (hfs : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hgs : ContDiff ℝ (↑(⊤:ℕ∞)) g)
    (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B) (hp : pb ![0,k]=0)
    (hf : ∀ y : Coord3,y 0∈Icc 0 6 → f (p,y)=flatFourier s a pa y)
    (hg : ∀ y : Coord3,y 0∈Icc 0 6 → g (p,y)=flatFourier s b pb y)
    (j : Fin 2) (x : Coord3) (hx : 0<x 0) :
    fourierMatchingResidual s k f g j (p,x)=
      -symmetricSource (fun _ => flatBackgroundTensor s) (fun y => fourierMatchingPair s k f g (p,y)) j x := by
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Coord3 => fourierMatchingPair s k f g (p,y)) :=
    (fourierMatchingPair_smooth s k hfs hgs).comp ((contDiff_const (c:=p)).prodMk contDiff_id)
  by_cases hmid : x 0∈Icc 2 4
  · simp only [fourierMatchingResidual,fourierResidualCutoff_one hmid,neg_mul,one_mul]
  have hz : symmetricSource (fun _ => flatBackgroundTensor s) (fun y => fourierMatchingPair s k f g (p,y)) j x=0 := by
    rw [flatBackgroundTensor_source hu]
    by_cases hleft : x 0<2
    · have he := fourierMatchingPair_left_fourier hs k hb hp hf hg (x:=x) ⟨hx,hleft⟩
      fin_cases j
      · change flatTensorLaplacian s (fun y => fourierMatchingPair s k f g (p,y) 0) x=0
        rw [flatTensorLaplacian_congr_nhds s he.1]
        exact affineFourierField_harmonic hs ha 1 0 hx
      · change flatTensorLaplacian s (fun y => fourierMatchingPair s k f g (p,y) 1) x=0
        rw [flatTensorLaplacian_congr_nhds s he.2]
        exact flatFourier_harmonic hs (fourier_left_coeff_bound hb) hx
    · have hright : 4<x 0 := by
        by_contra hh
        exact hmid ⟨le_of_not_gt hleft,le_of_not_gt hh⟩
      have he := fourierMatchingPair_right_fourier s k f g pa pb hp p hright
      fin_cases j
      · change flatTensorLaplacian s (fun y => fourierMatchingPair s k f g (p,y) 0) x=0
        rw [flatTensorLaplacian_congr_nhds s he.1]
        exact affineFourierField_harmonic hs (B:=0) (by intro h; simp) 1 0 (by linarith)
      · change flatTensorLaplacian s (fun y => fourierMatchingPair s k f g (p,y) 1) x=0
        rw [flatTensorLaplacian_congr_nhds s he.2]
        exact flatFourier_harmonic hs (single_fourier_coeff_bound ![0,k]) (by linarith)
  simp only [fourierMatchingResidual,hz,mul_zero,neg_zero]

lemma fourier_single_plus_rate {s : Fin 3 → ℝ} {k : ℤ} {b : (Fin 2 → ℤ) → ℝ}
    (hb : ∀ h,b h≠0 → torusRate s ![0,k]≤torusRate s h) :
    ∀ h,(Pi.single ![0,k] (1:ℝ) : (Fin 2 → ℤ) → ℝ) h+b h≠0 → torusRate s ![0,k]≤torusRate s h := by
  classical
  intro h hh
  by_cases he : h=![0,k]
  · subst h; exact le_rfl
  · apply hb h
    simpa only [Pi.single_eq_of_ne he,zero_add] using hh

lemma fourierMatchingResidual_moments {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (k : ℤ) {f g : ℝ×Coord3 → ℝ} {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B p ga : ℝ}
    (hfs : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hgs : ContDiff ℝ (↑(⊤:ℕ∞)) g)
    (hfp : ∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x)))
    (hgp : ∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x)))
    (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B) (hp : pb ![0,k]=0)
    (hga : 0<ga) (hgb : 0<torusRate s ![0,k])
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s ![0,k]≤torusRate s h)
    (hf : ∀ y : Coord3,y 0∈Icc 0 6 → f (p,y)=flatFourier s a pa y)
    (hg : ∀ y : Coord3,y 0∈Icc 0 6 → g (p,y)=flatFourier s b pb y) :
    periodicSourceMoment (2*Real.pi) (fun y => fourierMatchingPair s k f g (p,y))
      (fun j y => fourierMatchingResidual s k f g j (p,y))=0 := by
  classical
  let aa : Fin 2 → (Fin 2 → ℤ) → ℝ := ![a,fun _ => 0]
  let bb : Fin 2 → (Fin 2 → ℤ) → ℝ := ![fun h => (Pi.single ![0,k] (1:ℝ) : (Fin 2 → ℤ) → ℝ) h+b h,Pi.single ![0,k] 1]
  have haa : ∀ e h,|aa e h|≤![A,0] e := by intro e h; fin_cases e; exact ha h; simp [aa]
  have hbb : ∀ e h,|bb e h|≤![1+B,1] e := by
    intro e h
    fin_cases e
    · exact fourier_left_coeff_bound hb h
    · exact single_fourier_coeff_bound _ _
  have hraa : ∀ e h,aa e h≠0 → ga≤torusRate s h := by
    intro e h hh
    fin_cases e
    · exact hra h hh
    · exact False.elim (hh rfl)
  have hrbb : ∀ e h,bb e h≠0 → torusRate s ![0,k]≤torusRate s h := by
    intro e h hh
    fin_cases e
    · exact fourier_single_plus_rate hrb h hh
    · by_cases he : h=![0,k]
      · subst h; exact le_rfl
      · exact False.elim (hh (Pi.single_eq_of_ne he 1))
  have he (e : Fin 2) (x : Coord3) (hx : x 0=![1,5] e) :
      (fun y => fourierMatchingPair s k f g (p,y) 0)=ᶠ[𝓝 x] affineFourierField s (aa e) pa 1 0 ∧
      (fun y => fourierMatchingPair s k f g (p,y) 1)=ᶠ[𝓝 x] flatFourier s (bb e) pb := by
    fin_cases e
    · exact fourierMatchingPair_left_fourier hs k hb hp hf hg ⟨by simpa using hx ▸ (show (0:ℝ)<1 by norm_num),by simpa using hx ▸ (show (1:ℝ)<2 by norm_num)⟩
    · exact fourierMatchingPair_right_fourier s k f g pa pb hp p (by simpa using hx ▸ (show (4:ℝ)<5 by norm_num))
  have hrs (j : Fin 2) : tsupport (fun y => -fourierMatchingResidual s k f g j (p,y))⊆{x | x 0∈Icc 1 5} := by
    rw [show (fun y => -fourierMatchingResidual s k f g j (p,y))= -(fun y => fourierMatchingResidual s k f g j (p,y)) from rfl,tsupport_neg]
    exact fourierMatchingResidual_support s k f g p j
  have hre (j : Fin 2) (x : Coord3) (hx : x 0∈Icc 1 5) :
      -fourierMatchingResidual s k f g j (p,x)= symmetricSource (fun _ => flatBackgroundTensor s)
        (fun y => fourierMatchingPair s k f g (p,y)) j x := by
    rw [fourierMatchingResidual_exact hs k hfs hgs ha hb hp hf hg j x (by linarith [hx.1]),neg_neg]
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Coord3 => fourierMatchingPair s k f g (p,y)) :=
    (fourierMatchingPair_smooth s k hfs hgs).comp ((contDiff_const (c:=p)).prodMk contDiff_id)
  have hm := fourier_matching_three_moments hs haa hbb (fun _ => hga) (fun _ => hgb)
    hraa hrbb (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)≤5)
    hu
    (fourierMatchingPair_periodic s k hfp hgp p) (fun e x hx => (he e x hx).1) (fun e x hx => (he e x hx).2) hrs hre
  simpa only [neg_neg,Function.comp_apply] using hm.2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierMatchingFamilyCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real Matrix
open scoped Matrix.Norms.Elementwise

lemma axial_torusRate_pos {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) : 0<torusRate s ![0,k] := by
  have hb := torusRate_lower hs ![0,k]
  have hk' : (k:ℝ)≠0 := by exact_mod_cast hk
  have hp := abs_pos.mpr hk'
  simp only [torusSize,Matrix.cons_val_zero,Matrix.cons_val_one,Int.cast_zero,abs_zero,zero_add] at hb
  linarith

lemma fourierMatching_corrected_equation {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (k : ℤ) {f g : ℝ×Coord3 → ℝ} {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B p : ℝ}
    (hfs : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hgs : ContDiff ℝ (↑(⊤:ℕ∞)) g)
    (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B) (hp : pb ![0,k]=0)
    (hf : ∀ y : Coord3,y 0∈Icc 0 6 → f (p,y)=flatFourier s a pa y)
    (hg : ∀ y : Coord3,y 0∈Icc 0 6 → g (p,y)=flatFourier s b pb y)
    {H : Coord3 → Mat3} (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H)
    (hHr : ∀ j,symmetricSource H (fun y => fourierMatchingPair s k f g (p,y)) j=(fun y => fourierMatchingResidual s k f g j (p,y))) :
    ∀ j x,0<x 0 → symmetricSource (fun y => flatBackgroundTensor s+H y)
      (fun y => fourierMatchingPair s k f g (p,y)) j x=0 := by
  intro j x hx
  have hFs : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Coord3 => fourierMatchingPair s k f g (p,y)) :=
    (fourierMatchingPair_smooth s k hfs hgs).comp ((contDiff_const (c:=p)).prodMk contDiff_id)
  have hadd := congrFun (symmetricSource_add (H:=fun _ => flatBackgroundTensor s) (K:=H) contDiff_const hH hFs j) x
  have hr := congrFun (hHr j) x
  have hre := fourierMatchingResidual_exact hs k hfs hgs ha hb hp hf hg j x hx
  change symmetricSource (fun y => flatBackgroundTensor s+H y) (fun y => fourierMatchingPair s k f g (p,y)) j x=
      symmetricSource (fun _ => flatBackgroundTensor s) (fun y => fourierMatchingPair s k f g (p,y)) j x+
        symmetricSource H (fun y => fourierMatchingPair s k f g (p,y)) j x at hadd
  exact hadd.trans (by rw [hr,hre,add_neg_cancel])

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierMatchingElliptic
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real Matrix
open scoped Matrix.Norms.Elementwise

lemma flatBackgroundTensor_small_perturbation {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {H : Mat3} (hH : ‖H‖≤1/12) (v : Coord3) :
    (1/4)*(v ⬝ᵥ v) ≤ v ⬝ᵥ ((flatBackgroundTensor s+H)*ᵥv) ∧
      v ⬝ᵥ ((flatBackgroundTensor s+H)*ᵥv)≤(3*‖flatBackgroundTensor s‖+1)*(v ⬝ᵥ v) := by
  have hv : 0≤v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  have hb := flatBackgroundTensor_lower hs v
  have hq := abs_le.mp (matrix_quadratic_elementwise_bound H v)
  have hf := (le_abs_self (v ⬝ᵥ (flatBackgroundTensor s*ᵥv))).trans
    (matrix_quadratic_elementwise_bound (flatBackgroundTensor s) v)
  have he : v ⬝ᵥ ((flatBackgroundTensor s+H)*ᵥv)=
      v ⬝ᵥ (flatBackgroundTensor s*ᵥv)+v ⬝ᵥ (H*ᵥv) := by rw [add_mulVec,dotProduct_add]
  rw [he]
  have hm := mul_le_mul_of_nonneg_right hH hv
  constructor <;> nlinarith

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real Matrix
open scoped Matrix.Norms.Elementwise

theorem smooth_fourier_matching_with_origin {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s ![0,k]+gb≤torusRate s h)
    (hpb : pb ![0,k]=0) :
    ∃ f g : ℝ×Coord3 → ℝ,
      ContDiff ℝ (↑(⊤:ℕ∞)) f ∧ ContDiff ℝ (↑(⊤:ℕ∞)) g ∧
      (∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x))) ∧
      (∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x))) ∧
      (∀ x,f (0,x)=0) ∧ (∀ x,g (0,x)=0) ∧
      (∀ p∈Ioc 0 (1/2),∀ x : Coord3,x 0∈Icc 0 6 →
        f (p,x)=flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x ∧
        g (p,x)=flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x) ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ p in 𝓝 (0:ℝ),p∈Ioc 0 (1/2) →
        ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ AngularPeriodic (2*Real.pi) H ∧
          tsupport H⊆{x | x 0∈Icc (1/2) (11/2)} ∧ (∀ x,(H x).IsSymm) ∧
          (∀ x,‖H x‖≤ε) ∧ ∀ j x,0<x 0 →
            symmetricSource (fun y => flatBackgroundTensor s+H y) (fun y => fourierMatchingPair s k f g (p,y)) j x=0 := by
  obtain ⟨f,hfs,hfp,hfz,hfe⟩ := exists_smooth_periodic_normalized_tail
    (lam:=0) (T0:=10) (δ:=1) (R:=7) (phase:=pa) hs hga hA ha (by norm_num)
    (by simpa only [zero_add] using hra) (by norm_num)
  obtain ⟨g,hgs,hgp,hgz,hge⟩ := exists_smooth_periodic_normalized_tail
    (lam:=torusRate s ![0,k]) (T0:=10) (δ:=1) (R:=7) (phase:=pb) hs hgb hB hb (by norm_num)
    hrb (by norm_num)
  have hdata (p : ℝ) (hp : p∈Ioc 0 (1/2)) (x : Coord3) (hx : x 0∈Icc 0 6) :
      f (p,x)=flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x ∧
      g (p,x)=flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x := by
    have hx' : x 0∈Icc (-7:ℝ) 7 := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    constructor
    · rw [hfe p hp x hx',flatFourier_normalized_translation]
    · rw [hge p hp x hx',flatFourier_normalized_translation]
  refine ⟨f,g,hfs,hgs,hfp,hgp,hfz 0 le_rfl,hgz 0 le_rfl,hdata,?_⟩
  intro ε hε
  have hlam := axial_torusRate_pos hs hk
  have hcor := fourierMatchingFamily_correction hs hk hfs hgs hfp hgp (hfz 0 le_rfl) (hgz 0 le_rfl) hε
  filter_upwards [hcor] with p hcor
  intro hp
  have hT : 0≤10+1/p := by have hpos := hp.1; positivity
  let aa := normalizedFourierCoefficients s 0 (10+1/p) a
  let bb := normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b
  have haa : ∀ h,|aa h|≤A := normalizedFourierCoefficients_bound ha hT
    (fun h hh => hga.le.trans (hra h hh))
  have hbb : ∀ h,|bb h|≤B := normalizedFourierCoefficients_bound hb hT
    (fun h hh => by linarith [hrb h hh])
  have hraa : ∀ h,aa h≠0 → ga≤torusRate s h := by
    intro h hh
    exact hra h (fun hz => hh ((normalizedFourierCoefficients_zero_iff _ _ _ _ _).mpr hz))
  have hrbb : ∀ h,bb h≠0 → torusRate s ![0,k]≤torusRate s h := by
    intro h hh
    have hn : b h≠0 := fun hz => hh ((normalizedFourierCoefficients_zero_iff _ _ _ _ _).mpr hz)
    linarith [hrb h hn]
  have hff (x : Coord3) (hx : x 0∈Icc 0 6) : f (p,x)=flatFourier s aa pa x := (hdata p hp x hx).1
  have hgg (x : Coord3) (hx : x 0∈Icc 0 6) : g (p,x)=flatFourier s bb pb x := (hdata p hp x hx).2
  have hm := fourierMatchingResidual_moments hs k hfs hgs hfp hgp haa hbb hpb hga hlam hraa hrbb hff hgg
  obtain ⟨H,hH,hHp,hHs,hHsy,hHr,hHb⟩ := hcor hm
  refine ⟨H,hH,hHp,hHs,hHsy,hHb,?_⟩
  exact fourierMatching_corrected_equation hs k hfs hgs haa hbb hpb hff hgg hH hHr

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SimpleLevelNull
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.centralMeasure_finite _root_.OAI.ScalarConductivity.instCoeFunSubtypeForallBox3RealMemSubmoduleCentralSmoothFunctions _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

lemma simple_zeros_countable {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (U : Set ℝ)
    (hn : ∀ x∈U,f x=0 → deriv f x≠0) : ({x | x∈U ∧ f x=0} : Set ℝ).Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  have he := (hf.hasStrictDerivAt (by norm_num) (x:=x)).eventually_left_inverse (hn x hx.1 hx.2)
  obtain ⟨V,hVs,hV,hxV⟩ := mem_nhds_iff.mp he
  refine ⟨V,hV,?_⟩
  ext y
  constructor
  · intro hy
    have hxy := hVs hy.1
    change HasStrictDerivAt.localInverse f (deriv f x) x _ _ (f y)=y at hxy
    exact hxy.symm.trans ((congrArg (HasStrictDerivAt.localInverse f (deriv f x) x _ _)
      (hy.2.2.trans hx.2.symm)).trans he.self_of_nhds)
  · intro hy
    subst y
    exact ⟨hxV,hx⟩

lemma simple_wall_zero_null {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f)
    {U : Set Box3} (hU : MeasurableSet U)
    (hn : ∀ x∈U,f x=0 → wallDerivative f x≠0) : volume ({x | x∈U ∧ f x=0})=0 := by
  change (volume.prod volume) ({x : Box3 | x∈U ∧ f x=0})=0
  apply Measure.measure_prod_null_of_ae_null (hU.inter (isClosed_eq hf.continuous continuous_const).measurableSet)
  apply Filter.Eventually.of_forall
  intro q
  have hs : ContDiff ℝ 1 (fun z : ℝ => f (q,z)) :=
    (hf.comp (contDiff_const.prodMk contDiff_id)).of_le (show (1:WithTop ℕ∞)≤↑(⊤:ℕ∞) by norm_cast)
  have hh := simple_zeros_countable hs {z | (q,z)∈U} (by
    intro z hz he
    simpa only [←wallDerivative_slice (hf.differentiable (by simp))] using hn (q,z) hz he)
  exact hh.measure_zero volume

lemma wallDerivative_boxPullback {f : Coord3 → ℝ} (hf : Differentiable ℝ f) (p : Box3) :
    wallDerivative (fun y => f (boxCoordinates.symm y)) p=
      direction (Pi.single 2 1) f (boxCoordinates.symm p) := by
  have he := ((hf (boxCoordinates.symm p)).hasFDerivAt.comp p boxCoordinates.symm.hasFDerivAt).fderiv
  change fderiv ℝ (f ∘ boxCoordinates.symm) p (0,1)=_
  rw [he,ContinuousLinearMap.comp_apply]
  have hh : (boxCoordinates.symm : Box3 →L[ℝ] Coord3) (0,1)=Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp [boxCoordinates_symm_apply]
  rw [hh]
  rfl

lemma simple_coord_zero_ae {f : Coord3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f)
    {U : Set Coord3} (hU : MeasurableSet U)
    (hn : ∀ x∈U,f x=0 → direction (Pi.single 2 1) f x≠0) :
    ∀ᵐ x : Coord3,x∈U → f x≠0 := by
  have hh := simple_wall_zero_null (hf.comp boxCoordinates.symm.contDiff)
    (hU.preimage boxCoordinates.symm.continuous.measurable) (by
      intro p hp hz
      change wallDerivative (fun y => f (boxCoordinates.symm y)) p≠0
      rw [wallDerivative_boxPullback (hf.differentiable (by simp))]
      exact hn _ hp hz)
  have ha := boxCoordinates_volume.quasiMeasurePreserving.ae (compl_mem_ae_iff.mpr hh)
  filter_upwards [ha] with x hx
  simpa only [mem_compl_iff,mem_ofPred_eq,mem_preimage,Function.comp_def,boxCoordinates.symm_apply_apply,not_and] using hx

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma pairMinor_rank {u : Coord3 → Fin 2 → ℝ} {x : Coord3} (hn : pairMinor u x≠0) :
    LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col := by
  apply linearIndependent_fin2.mpr
  constructor
  · intro hz
    apply hn
    have h0 := congrFun hz 0
    have h2 := congrFun hz 2
    change fderiv ℝ u x (Pi.single 0 1) 1=0 at h0
    change fderiv ℝ u x (Pi.single 2 1) 1=0 at h2
    simp only [pairMinor,h0,h2,mul_zero,sub_self]
  · intro a he
    apply hn
    have h0 := congrFun he 0
    have h2 := congrFun he 2
    change a*fderiv ℝ u x (Pi.single 0 1) 1=fderiv ℝ u x (Pi.single 0 1) 0 at h0
    change a*fderiv ℝ u x (Pi.single 2 1) 1=fderiv ℝ u x (Pi.single 2 1) 0 at h2
    simp only [pairMinor,←h0,←h2]
    ring

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma familySpatialDerivative_smooth {u : P×Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : P×Coord3 => fderiv ℝ (fun y => u (z.1,y)) z.2) := by
  have hh : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : (P×Coord3)×Coord3 => u (z.1.1,z.2)) :=
    hu.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact hh.fderiv contDiff_snd (by simp)

lemma familyPairMinor_smooth {u : P×Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : P×Coord3 => pairMinor (fun y => u (z.1,y)) z.2) := by
  have hh (i : Fin 3) (j : Fin 2) : ContDiff ℝ (↑(⊤:ℕ∞))
      (fun z : P×Coord3 => fderiv ℝ (fun y => u (z.1,y)) z.2 (Pi.single i 1) j) :=
    (contDiff_apply ℝ ℝ j).comp ((familySpatialDerivative_smooth hu).clm_apply contDiff_const)
  exact ((hh 0 0).mul (hh 2 1)).sub ((hh 2 0).mul (hh 0 1))

lemma pairMinor_smooth {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (pairMinor u) := by
  have hh (i : Fin 3) (j : Fin 2) : ContDiff ℝ (↑(⊤:ℕ∞))
      (fun x => fderiv ℝ u x (Pi.single i 1) j) :=
    (contDiff_apply ℝ ℝ j).comp ((hu.fderiv_right (by simp)).clm_apply contDiff_const)
  exact ((hh 0 0).mul (hh 2 1)).sub ((hh 2 0).mul (hh 0 1))

lemma AngularPeriodic.pairMinor {T : ℝ} {u : Coord3 → Fin 2 → ℝ}
    (hu : AngularPeriodic T u) : AngularPeriodic T (pairMinor u) := by
  intro n x
  unfold ScalarConductivity.pairMinor
  rw [hu.fderiv n x]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PeriodicBandCompactness
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

lemma exists_angular_translate_mem_box {T : ℝ} (hT : 0<T) {a b : ℝ} (x : Coord3)
    (hx : x 0∈Icc a b) :
    ∃ n : Fin 2 → ℤ,x+angularShift T n∈Icc ![a,0,0] ![b,T,T] := by
  let n : Fin 2 → ℤ := fun i => -⌊x i.succ/T⌋
  have hn (i : Fin 2) : 0≤x i.succ+T*(n i:ℝ) ∧ x i.succ+T*(n i:ℝ)≤T := by
    have h0 := (le_div_iff₀ hT).mp (Int.floor_le (x i.succ/T))
    have h1 := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (x i.succ/T))
    simp only [n,Int.cast_neg]
    constructor <;> nlinarith
  refine ⟨n,?_,?_⟩
  · intro i
    fin_cases i
    · change a≤x 0+0
      simpa only [add_zero] using hx.1
    · exact (hn 0).1
    · exact (hn 1).1
  · intro i
    fin_cases i
    · change x 0+0≤b
      simpa only [add_zero] using hx.2
    · exact (hn 0).2
    · exact (hn 1).2

variable {P : Type*} [TopologicalSpace P]

lemma periodic_band_nonzero_eventually {F G : P×Coord3 → ℝ}
    (hF : Continuous F) (hG : Continuous G) {T : ℝ} (hT : 0<T)
    (hpF : ∀ p,AngularPeriodic T (fun x => F (p,x)))
    (hpG : ∀ p,AngularPeriodic T (fun x => G (p,x)))
    (p₀ : P) (a b : ℝ)
    (hb : ∀ x : Coord3,x 0∈Icc a b → F (p₀,x)≠0 ∨ G (p₀,x)≠0) :
    ∀ᶠ p in 𝓝 p₀,∀ x : Coord3,x 0∈Icc a b → F (p,x)≠0 ∨ G (p,x)≠0 := by
  have he : ∀ᶠ p in 𝓝 p₀,∀ x∈Icc (![a,0,0] : Coord3) ![b,T,T], F (p,x)≠0 ∨ G (p,x)≠0 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro x hx
    rcases hb x ⟨hx.1 0,hx.2 0⟩ with hf|hg
    · exact (hF.continuousAt.eventually_ne hf).mono (fun z hz => Or.inl hz)
    · exact (hG.continuousAt.eventually_ne hg).mono (fun z hz => Or.inr hz)
  filter_upwards [he] with p hp
  intro x hx
  obtain ⟨n,hn⟩ := exists_angular_translate_mem_box hT x hx
  simpa only [hpF p n x,hpG p n x] using hp (x+angularShift T n) hn

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Real

lemma pairMinor_wallCoordinatePair {v : Box3 → ℝ} (hv : Differentiable ℝ v) (x : Coord3) :
    pairMinor (wallCoordinatePair v) x=wallDerivative v (boxCoordinates x) := by
  simp [pairMinor,wallCoordinatePair_derivative hv,boxCoordinates_apply,wallDerivative]
  rfl

lemma direction_boxCoordinates {v : Box3 → ℝ} (hv : Differentiable ℝ v) (x : Coord3) :
    direction (Pi.single 2 1) (fun y => v (boxCoordinates y)) x=wallDerivative v (boxCoordinates x) := by
  change fderiv ℝ (v ∘ boxCoordinates) x (Pi.single 2 1)=_
  rw [boxCoordinates_fderiv v hv]
  simp [wallDerivative,boxCoordinates_apply]
  rfl

lemma pureMode_pairMinor_noncritical {σ lam k : ℝ} (hσ : σ≠0) (hk : k≠0) (x : Coord3) :
    pairMinor (wallCoordinatePair (pureWallMode σ lam k)) x≠0 ∨
      direction (Pi.single 2 1) (pairMinor (wallCoordinatePair (pureWallMode σ lam k))) x≠0 := by
  have hs := pureWallMode_smooth σ lam k
  have he : pairMinor (wallCoordinatePair (pureWallMode σ lam k))=
      fun x => wallDerivative (pureWallMode σ lam k) (boxCoordinates x) :=
    funext (pairMinor_wallCoordinatePair (hs.differentiable (by simp)))
  rw [he,direction_boxCoordinates ((wallDerivative_smooth hs).differentiable (by simp))]
  dsimp only
  rw [boxCoordinates_apply,pureWallMode_normalDerivative,pureWallMode_normalSecond]
  by_cases hz : sin (k*x 2)=0
  · right
    have hc : cos (k*x 2)≠0 := by
      intro hc
      have hh := sin_sq_add_cos_sq (k*x 2)
      rw [hz,hc] at hh
      norm_num at hh
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero hσ (exp_ne_zero _)) hc) (pow_ne_zero 2 hk))
  · left
    exact mul_ne_zero (mul_ne_zero hσ (exp_ne_zero _)) (mul_ne_zero (neg_ne_zero.mpr hz) hk)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma familyDirection_smooth {f : P×Coord3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (v : Coord3) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : P×Coord3 => direction v (fun y => f (z.1,y)) z.2) := by
  have hh : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : (P×Coord3)×Coord3 => f (z.1.1,z.2)) :=
    hf.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact (hh.fderiv contDiff_snd (by simp)).clm_apply contDiff_const

lemma AngularPeriodic.direction {T : ℝ} {f : Coord3 → ℝ} (hf : AngularPeriodic T f) (v : Coord3) :
    AngularPeriodic T (direction v f) := by
  intro n x
  change _root_.fderiv ℝ f (x+angularShift T n) v=_root_.fderiv ℝ f x v
  rw [hf.fderiv n x]

theorem periodic_pure_mode_rank_eventually {u : P×Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {T : ℝ} (hT : 0<T)
    (hp : ∀ p,AngularPeriodic T (fun x => u (p,x))) (p₀ : P)
    {σ lam k : ℝ} (hσ : σ≠0) (hk : k≠0)
    (hb : ∀ x,u (p₀,x)=wallCoordinatePair (pureWallMode σ lam k) x) (a b : ℝ) :
    ∀ᶠ p in 𝓝 p₀,∀ x : Coord3,x 0∈Icc a b → pairMinor (fun y => u (p,y)) x=0 →
      direction (Pi.single 2 1) (pairMinor (fun y => u (p,y))) x≠0 := by
  have hM := familyPairMinor_smooth hu
  have hN := familyDirection_smooth hM (Pi.single 2 1)
  have he := periodic_band_nonzero_eventually hM.continuous hN.continuous hT
    (fun p => (hp p).pairMinor) (fun p => (hp p).pairMinor.direction (Pi.single 2 1)) p₀ a b (by
      intro x _
      have hh : (fun y => u (p₀,y))=wallCoordinatePair (pureWallMode σ lam k) := funext hb
      simpa only [hh] using pureMode_pairMinor_noncritical hσ hk (lam:=lam) x)
  filter_upwards [he] with p hp
  intro x hx hz
  exact (hp x hx).resolve_left (not_not.mpr hz)

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

theorem elliptic_fourier_matching_regular_oai {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s ![0,k]+gb≤torusRate s h)
    (hpb : pb ![0,k]=0) {δ : ℝ} (hδ : 0<δ) :
    ∃ p : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧
      ∃ (u : Coord3 → Fin 2 → ℝ) (D : Coord3 → Mat3),
        ContDiff ℝ (↑(⊤:ℕ∞)) u ∧ ContDiff ℝ (↑(⊤:ℕ∞)) D ∧
        AngularPeriodic (2*Real.pi) u ∧ AngularPeriodic (2*Real.pi) D ∧
        (∀ x,(D x).IsSymm) ∧
        (∀ x v,(1/4)*(v ⬝ᵥ v)≤v ⬝ᵥ (D x*ᵥv) ∧
          v ⬝ᵥ (D x*ᵥv)≤(3*‖flatBackgroundTensor s‖+1)*(v ⬝ᵥ v)) ∧
        (∀ j x,0<x 0 → symmetricSource D u j x=0) ∧
        (∀ x,x 0∉Icc (1/2) (11/2) → D x=flatBackgroundTensor s) ∧
        (∀ x,x 0∈Icc 0 (1/2) → u x=
          ![x 0+flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x,
            flatPhaseMode s ![0,k] 0 x+
              flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x]) ∧
        (∀ x,4≤x 0 → u x=![x 0,flatPhaseMode s ![0,k] 0 x]) ∧
        ∀ᵐ x : Coord3,x 0∈Ioo 0 6 → LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col := by
  obtain ⟨f,g,hfs,hgs,hfp,hgp,hfz,hgz,hdata,hcor⟩ := smooth_fourier_matching_with_origin (pa:=pa) hs hk hA hB ha hb hga hgb hra hrb hpb
  have hF := fourierMatchingPair_smooth s k hfs hgs
  have hk' : (k:ℝ)≠0 := by exact_mod_cast hk
  have hbase (x : Coord3) : fourierMatchingPair s k f g (0,x)=
      wallCoordinatePair (pureWallMode 1 (torusRate s ![0,k]) (k:ℝ)) x := by
    ext j
    fin_cases j <;> simp [fourierMatchingPair,hfz,hgz,wallCoordinatePair,pureWallMode_eq_flatPhaseMode]
  have hRank := periodic_pure_mode_rank_eventually hF (by positivity : 0<2*Real.pi)
    (fourierMatchingPair_periodic s k hfp hgp) 0 (by norm_num : (1:ℝ)≠0) hk' hbase 0 6
  have hh := (hcor (1/12) (by norm_num)).and hRank
  obtain ⟨r,hr,hrb'⟩ := Metric.mem_nhds_iff.mp hh
  let p := min (r/2) (min (δ/2) (1/4))
  have hp : 0<p := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hpr : p < r := (min_le_left _ _).trans_lt (by linarith)
  have hpδ : p<δ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hp2 : p≤1/2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num)
  obtain ⟨hc,hr⟩ := hrb' (show p∈Metric.ball (0:ℝ) r from by simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos hp] using hpr)
  obtain ⟨H,hHs,hHp,hHt,hHsym,hHb,hHe⟩ := hc ⟨hp,hp2⟩
  refine ⟨p,⟨hp,hp2⟩,hpδ,(fun x => fourierMatchingPair s k f g (p,x)),
    (fun x => flatBackgroundTensor s+H x),
    (fourierMatchingPair_smooth s k hfs hgs).comp (contDiff_const.prodMk contDiff_id),
    contDiff_const.add hHs,fourierMatchingPair_periodic s k hfp hgp p,?_,?_,?_,hHe,?_,?_,?_,?_⟩
  · intro n x
    dsimp only
    rw [hHp n x]
  · intro x
    exact (flatBackgroundTensor_symm s).add (hHsym x)
  · intro x v
    exact flatBackgroundTensor_small_perturbation hs (hHb x) v
  · intro x hx
    have hz : H x=0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hHt hx'))
    dsimp only
    rw [hz,add_zero]
  · intro x hx
    have hd := hdata p ⟨hp,hp2⟩ x ⟨hx.1,by linarith [hx.2]⟩
    simp only [fourierMatchingPair,fourierMatchingCutoff_left (show x 0≤2 by linarith [hx.2]),one_mul,hd.1,hd.2]
  · intro x hx
    simp only [fourierMatchingPair,fourierMatchingCutoff_right hx,zero_mul,add_zero]

  · have hU : IsOpen {x : Coord3 | x 0∈Ioo (0:ℝ) 6} :=
      isOpen_Ioo.preimage (continuous_apply 0)
    have ha := simple_coord_zero_ae (pairMinor_smooth (hF.comp (contDiff_const.prodMk contDiff_id)))
      hU.measurableSet (by
        intro x hx
        exact hr x ⟨hx.1.le,hx.2.le⟩)
    filter_upwards [ha] with x hx
    intro hxU
    exact pairMinor_rank (hx hxU)

end ScalarConductivity

end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.elliptic_fourier_matching_regular_oai := @OAI.ScalarConductivity.elliptic_fourier_matching_regular_oai
