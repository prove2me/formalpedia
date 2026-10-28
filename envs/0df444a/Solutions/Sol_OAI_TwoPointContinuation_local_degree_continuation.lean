-- Prove2me | solution 1 for OAI.TwoPointContinuation.local_degree_continuation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T16:17:56.047205+00:00
-- url     : https://prove2.me/submissions/e8bfe077-0eb7-4b91-a13a-a89bd7ad4639

import Mathlib
import Definitions.Def_OAIQ10Bp001

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FiniteContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function MeasureTheory
namespace TwoPointContinuation

 theorem alternating_above_dimension (n : ℕ)
    (W : (Fin n → ℝ) [⋀^Fin (n+1)]→L[ℝ] ℝ) : W=0 := by
  ext v
  apply W.toAlternatingMap.map_linearDependent
  intro hv
  have h := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin,Module.finrank_pi] at h
  omega

 theorem closedForm_box_flux {n : ℕ}
    (W : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hW : Differentiable ℝ W) (hd : ∀ x, extDeriv W x=0)
    (a b : Fin (n+1) → ℝ) (hab : a≤b) :
    (∑ i : Fin (n+1),
      ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), formFlux W i (i.insertNth (b i) x))-
        ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), formFlux W i (i.insertNth (a i) x)))=0 := by
  let e : Fin (n+1) → (Fin (n+1) → ℝ) := fun j => Pi.single j 1
  let d := fun (i : Fin (n+1)) (x : Fin (n+1) → ℝ) =>
    (-1:ℝ)^i.val • fderiv ℝ (fun y => W y (i.removeNth e)) x
  have hD (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
      HasFDerivAt (formFlux W i) (d i x) x :=
    ((hW x).continuousAlternatingMap_apply_const (i.removeNth e)).hasFDerivAt.const_smul ((-1:ℝ)^i.val)
  have hdiv (x : Fin (n+1) → ℝ) : ∑ i, d i x (e i)=0 := by
    have h := congrArg (fun f => f e) (hd x)
    change extDeriv W x e = 0 at h
    rw [extDeriv_apply (hW x)] at h
    simpa [d, smul_eq_mul, zsmul_eq_mul] using h
  have hInt : IntegrableOn (fun x => ∑ i, d i x (e i)) (Icc a b) := by
    simp_rw [hdiv]
    exact integrableOn_zero
  have h := integral_divergence_of_hasFDerivAt_off_countable' a b hab (formFlux W) d ∅
    countable_empty (fun i => (Differentiable.continuous (fun x => (hD i x).differentiableAt)).continuousOn)
    (fun x _ i => hD i x) hInt
  change (∫ x in Icc a b, ∑ i, d i x (e i)) = _ at h
  simp only [hdiv,integral_zero] at h
  exact h.symm

 theorem pulledCoordinateForm_differentiable {n : ℕ}
    (F : (Fin (n+1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ ∞ F)
    (φ : (Fin n → ℝ) → ℝ) (hφ : Differentiable ℝ φ) :
    Differentiable ℝ (pulledCoordinateForm F φ) := by
  intro x
  exact (((hφ _).comp x (hF.differentiable (by simp) x)).smul (differentiableAt_const _)).continuousAlternatingMapCompContinuousLinearMap
      ((hF.fderiv_right (show (1:ℕ∞ω)+1≤∞ by decide)).differentiable (by decide) x)

 theorem pulledCoordinateForm_closed {n : ℕ}
    (F : (Fin (n+1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ ∞ F)
    (φ : (Fin n → ℝ) → ℝ) (hφ : Differentiable ℝ φ) (x : Fin (n+1) → ℝ) :
    extDeriv (pulledCoordinateForm F φ) x=0 := by
  change extDeriv (fun y => (φ (F y) • coordinateForm n).compContinuousLinearMap (fderiv ℝ F y)) x=0
  have hW : DifferentiableAt ℝ (fun y : Fin n → ℝ => φ y • coordinateForm n) (F x) :=
    (hφ _).smul_const _
  rw [extDeriv_pullback hW hF.contDiffAt (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)]
  rw [alternating_above_dimension n (extDeriv (fun y => φ y • coordinateForm n) (F x))]
  rfl

 theorem fderiv_initial_spatial {n : ℕ}
    (F : (Fin (n+1) → ℝ) → (Fin n → ℝ)) (hF : Differentiable ℝ F)
    (hzero : ∀ x, F (Fin.cons 0 x)=x) (x : Fin n → ℝ) (j : Fin n) :
    fderiv ℝ F (Fin.cons 0 x) (Pi.single j.succ 1)=Pi.single j 1 := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
    (0 : (Fin n → ℝ) →L[ℝ] ℝ).finCons (ContinuousLinearMap.id ℝ (Fin n → ℝ))
  have he : L (Pi.single j 1)=Pi.single j.succ 1 := by
    ext i
    refine Fin.cases ?_ (fun k => ?_) i <;> simp [L, Pi.single_apply, Fin.succ_inj, eq_comm]
  have h := (hF (Fin.cons 0 x)).hasFDerivAt.comp x
    ((hasFDerivAt_const (0:ℝ) x).finCons (hasFDerivAt_id x))
  change HasFDerivAt (fun y => F (Fin.cons 0 y)) ((fderiv ℝ F (Fin.cons 0 x)).comp L) x at h
  simp only [hzero] at h
  have hl := h.unique (hasFDerivAt_id x)
  have hv := congrArg (fun D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => D (Pi.single j 1)) hl
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,he] using hv

 theorem initial_flux {n : ℕ}
    (F : (Fin (n+1) → ℝ) → (Fin n → ℝ)) (hF : Differentiable ℝ F)
    (hzero : ∀ x, F (Fin.cons 0 x)=x) (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    formFlux (pulledCoordinateForm F φ) 0 (Fin.cons 0 x)=φ x := by
  have hvec : (fun j : Fin n => (fderiv ℝ F (Fin.cons 0 x)) (Pi.single j.succ 1))=
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    rw [fderiv_initial_spatial F hF hzero]
    simp [Pi.single_apply,Matrix.one_apply,eq_comm]
  simp only [formFlux,Fin.val_zero,pow_zero,one_smul,pulledCoordinateForm,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,ContinuousAlternatingMap.smul_apply,
    Fin.removeNth_zero,Fin.tail,Function.comp_def]
  rw [hzero,coordinateForm_apply,hvec,Matrix.det_one,smul_eq_mul,mul_one]


 

 

open scoped ContDiff Topology
open Set Filter Function MeasureTheory

theorem mem_cube_iff {n : ℕ} {R : ℝ} (hR : 0≤R) (x : Fin n → ℝ) :
    x ∈ Icc (cubeLower n R) (cubeUpper n R) ↔ ‖x‖≤R := by
  rw [pi_norm_le_iff_of_nonneg hR]
  simp only [Set.mem_Icc,Pi.le_def,cubeLower,cubeUpper,Real.norm_eq_abs,abs_le]
  exact ⟨fun h i => ⟨h.1 i,h.2 i⟩,fun h => ⟨fun i => (h i).1,fun i => (h i).2⟩⟩

theorem mem_cylinder_iff {n : ℕ} {R : ℝ} (hR : 0≤R) (y : Fin (n+1) → ℝ) :
    y ∈ Icc (cylinderLower n R) (cylinderUpper n R) ↔
      y 0 ∈ Icc (0:ℝ) 1 ∧ ‖Fin.tail y‖≤R := by
  rw [← mem_cube_iff hR]
  simp only [Set.mem_Icc,Pi.le_def,cylinderLower,cylinderUpper,Fin.forall_fin_succ,
    Fin.cons_zero,Fin.cons_succ,Fin.tail,cubeLower,cubeUpper]
  tauto

theorem tail_face_norm {n : ℕ} {R : ℝ} (hR : 0≤R) {y : Fin (n+1) → ℝ}
    (hy : y ∈ Icc (cylinderLower n R) (cylinderUpper n R))
    (j : Fin n) (hj : y j.succ=R ∨ y j.succ= -R) : ‖Fin.tail y‖=R := by
  apply le_antisymm ((mem_cylinder_iff hR y).mp hy).2
  have h := norm_le_pi_norm (Fin.tail y) j
  change ‖y j.succ‖≤‖Fin.tail y‖ at h
  rcases hj with hj|hj <;> simpa [hj,abs_of_nonneg hR] using h

 theorem finite_continuation (n : ℕ)
    (F : (Fin (n+1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ ∞ F)
    (hzero : ∀ x, F (Fin.cons 0 x)=x)
    (R : ℝ) (hR : 0<R)
    (hside : ∀ t ∈ Icc (0:ℝ) 1, ∀ x : Fin n → ℝ,
      ‖x‖=R → F (Fin.cons t x) ≠ 0) :
    ∃ x : Fin n → ℝ, ‖x‖<R ∧ F (Fin.cons 1 x)=0 := by
  classical
  by_contra hno
  have hfinal (x : Fin n → ℝ) (hx : ‖x‖≤R) : F (Fin.cons 1 x)≠0 := by
    rcases lt_or_eq_of_le hx with hx|hx
    · exact fun he => hno ⟨x,hx,he⟩
    · exact hside 1 ⟨zero_le_one,le_rfl⟩ x hx
  let a := cylinderLower n R
  let b := cylinderUpper n R
  let K := Icc a b ∩ {y : Fin (n+1) → ℝ | y 0=1 ∨ ‖Fin.tail y‖=R}
  have htail : Continuous (Fin.tail : (Fin (n+1) → ℝ) → (Fin n → ℝ)) := by
    exact continuous_pi (fun j => continuous_apply j.succ)
  have hK : IsCompact K := isCompact_Icc.inter_right
    ((isClosed_eq (continuous_apply 0) continuous_const).union
      (isClosed_eq htail.norm continuous_const))
  have hK0 (y : Fin (n+1) → ℝ) (hy : y ∈ K) : F y≠0 := by
    have hc := (mem_cylinder_iff hR.le y).mp hy.1
    have he : Fin.cons (y 0) (Fin.tail y)=y := Fin.cons_self_tail y
    rcases hy.2 with hy|hy
    · have hf := hfinal (Fin.tail y) hc.2
      simpa only [← hy,he] using hf
    · have hf := hside (y 0) hc.1 (Fin.tail y) hy
      simpa only [he] using hf
  have hz : (0 : Fin n → ℝ) ∈ (F '' K)ᶜ := by
    rintro ⟨y,hy,he⟩
    exact hK0 y hy he
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (hK.image hF.continuous).isClosed.isOpen_compl 0 hz
  let δ := min ε R
  have hδ : 0<δ := lt_min hε hR
  let φ : ContDiffBump (0 : Fin n → ℝ) := ⟨δ/2,δ,half_pos hδ,half_lt_self hδ⟩
  have hφzero (y : Fin (n+1) → ℝ) (hy : y ∈ K) : φ (F y)=0 := by
    by_contra hn
    have hm : F y ∈ Metric.ball 0 δ := by
      rw [← φ.support_eq]
      exact hn
    have hm' : F y ∈ Metric.ball 0 ε :=
      Metric.ball_subset_ball (min_le_left ε R) hm
    exact hball hm' ⟨y,hy,rfl⟩
  have hφpos : 0 < ∫ x in Icc (cubeLower n R) (cubeUpper n R), φ x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)]
    · exact φ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
        φ.hasCompactSupport φ.nonneg' (ne_of_gt (φ.pos_of_mem_ball (Metric.mem_ball_self φ.rOut_pos)))
    · apply φ.zero_of_le_dist
      change δ ≤ dist x 0
      rw [dist_zero_right]
      exact (min_le_right ε R).trans (le_of_lt (lt_of_not_ge (fun hn => hx ((mem_cube_iff hR.le x).mpr hn))))
  have hab : a≤b := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact zero_le_one
    · exact neg_le_self hR.le
  have hface (i : Fin (n+1)) (c : ℝ) (hc : c=a i ∨ c=b i)
      (x : Fin n → ℝ) (hx : x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      i.insertNth c x ∈ Icc a b := by
    constructor
    · apply Fin.le_insertNth_iff.mpr
      exact ⟨by rcases hc with rfl|rfl; exact le_rfl; exact hab i,hx.1⟩
    · apply Fin.insertNth_le_iff.mpr
      exact ⟨by rcases hc with rfl|rfl; exact hab i; exact le_rfl,hx.2⟩
  have htop (i : Fin (n+1)) (x : Fin n → ℝ)
      (hx : x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      i.insertNth (b i) x ∈ K := by
    refine ⟨hface i (b i) (Or.inr rfl) x hx,?_⟩
    cases i using Fin.cases with
    | zero =>
      left
      simp [b,cylinderUpper]
    | succ j =>
      right
      apply tail_face_norm hR.le (hface j.succ (b j.succ) (Or.inr rfl) x hx) j
      left
      simp [b,cylinderUpper,cubeUpper]
  have hbottom (i : Fin (n+1)) (hi : i≠0) (x : Fin n → ℝ)
      (hx : x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      i.insertNth (a i) x ∈ K := by
    refine ⟨hface i (a i) (Or.inl rfl) x hx,Or.inr ?_⟩
    cases i using Fin.cases with
    | zero => exact (hi rfl).elim
    | succ j =>
      apply tail_face_norm hR.le (hface j.succ (a j.succ) (Or.inl rfl) x hx) j
      right
      simp [a,cylinderLower,cubeLower]
  have hfluxzero (i : Fin (n+1)) (y : Fin (n+1) → ℝ) (hy : y ∈ K) :
      formFlux (pulledCoordinateForm F φ) i y=0 := by
    simp [formFlux,pulledCoordinateForm,hφzero y hy]
  have hup (i : Fin (n+1)) :
      (∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        formFlux (pulledCoordinateForm F φ) i (i.insertNth (b i) x))=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact hfluxzero i _ (htop i x hx)
  have hdown (i : Fin (n+1)) (hi : i≠0) :
      (∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        formFlux (pulledCoordinateForm F φ) i (i.insertNth (a i) x))=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact hfluxzero i _ (hbottom i hi x hx)
  have h := closedForm_box_flux (pulledCoordinateForm F φ)
    (pulledCoordinateForm_differentiable F hF φ ((φ.contDiff : ContDiff ℝ ∞ φ).differentiable (by decide)))
    (pulledCoordinateForm_closed F hF φ ((φ.contDiff : ContDiff ℝ ∞ φ).differentiable (by decide))) a b hab
  simp only [hup,zero_sub] at h
  rw [Finset.sum_eq_single (0 : Fin (n+1)) (fun i _ hi => by rw [hdown i hi,neg_zero])
    (by simp)] at h
  have hi : (∫ x in Icc (a ∘ (0 : Fin (n+1)).succAbove) (b ∘ (0 : Fin (n+1)).succAbove),
      formFlux (pulledCoordinateForm F φ) 0 ((0 : Fin (n+1)).insertNth (a 0) x))=
      ∫ x in Icc (cubeLower n R) (cubeUpper n R), φ x := by
    simp only [a,b,cylinderLower,cylinderUpper,Fin.succAbove_zero,Function.comp_def,
      Fin.cons_succ,Fin.cons_zero,Fin.insertNth_zero]
    congr 1
    funext x
    exact initial_flux F (hF.differentiable (by decide)) hzero φ x
  rw [hi] at h
  linarith


 

 

open scoped ContDiff Topology Manifold
open Set Filter Function

 

theorem localized_continuation (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ ∞ F)
    (hzero : ∀ x, F (0,x)=x)
    (Ω : Set (Fin n → ℝ)) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (h0 : 0∈Ω)
    (hside : ∀ t∈Icc (0:ℝ) 1, ∀ x∈closure Ω, x∉Ω → F (t,x)≠0) :
    ∃ x∈Ω, F (1,x)=0 := by
  classical
  let Z := (Icc (0:ℝ) 1 ×ˢ closure Ω) ∩ {y | F y=0}
  have hZ : IsCompact Z := (isCompact_Icc.prod hb.isCompact_closure).inter_right
    (isClosed_eq hF.continuous continuous_const)
  let X := Prod.snd '' Z
  have hX : IsCompact X := hZ.image continuous_snd
  have hXΩ : X⊆Ω := by
    rintro x ⟨⟨t,x⟩,hy,rfl⟩
    by_contra hx
    exact hside t hy.1.1 x hy.1.2 hx hy.2
  obtain ⟨χ,hχ0,hχ1,hχb⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (𝓘(ℝ, (Fin n → ℝ))) ho.isClosed_compl hX.isClosed
    (Set.disjoint_left.mpr (fun x hx hxX => hx (hXΩ hxX))) (n := ⊤)
  have hχ : ContDiff ℝ ∞ (fun x => χ x) := contMDiff_iff_contDiff.mp χ.contMDiff
  obtain ⟨R,hR,hΩ⟩ := hb.subset_ball_lt 0 (0 : Fin n → ℝ)
  let G : (Fin (n+1) → ℝ) → (Fin n → ℝ) :=
    fun y => F (y 0 * χ (Fin.tail y), Fin.tail y)
  have ht : ContDiff ℝ ∞ (Fin.tail : (Fin (n+1) → ℝ) → (Fin n → ℝ)) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ ℝ i.succ)
  have hG : ContDiff ℝ ∞ G := hF.comp
    (((contDiff_apply ℝ ℝ 0).mul (hχ.comp ht)).prodMk ht)
  have hG0 (x : Fin n → ℝ) : G (Fin.cons 0 x)=x := by
    simp only [G,Fin.cons_zero,Fin.tail_cons,zero_mul,hzero]
  have hGb (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : Fin n → ℝ) (hx : ‖x‖=R) :
      G (Fin.cons t x)≠0 := by
    have hn : x∉Ω := fun h => (ne_of_lt (by simpa using hΩ h)) hx
    have he : χ x=0 := hχ0 hn
    have hGe : G (Fin.cons t x)=x := by
      simp only [G,Fin.cons_zero,Fin.tail_cons,he,mul_zero,hzero]
    rw [hGe]
    intro he
    have : R=0 := by simpa only [he,norm_zero] using hx.symm
    exact (ne_of_gt hR) this
  obtain ⟨x,hx,hGx⟩ := finite_continuation n G hG hG0 R hR hGb
  have hxΩ : x∈Ω := by
    by_contra hn
    have he : χ x=0 := hχ0 hn
    have hx0 : x=0 := by simpa only [G,Fin.cons_zero,Fin.tail_cons,he,mul_zero,hzero] using hGx
    exact hn (hx0 ▸ h0)
  have hz : (χ x,x)∈Z := by
    refine ⟨⟨hχb x,subset_closure hxΩ⟩,?_⟩
    change F (χ x,x)=0
    simpa only [G,Fin.cons_zero,Fin.tail_cons,one_mul] using hGx
  have he : χ x=1 := hχ1 ⟨(χ x,x),hz,rfl⟩
  refine ⟨x,hxΩ,?_⟩
  simpa only [G,Fin.cons_zero,Fin.tail_cons,he,one_mul] using hGx


 

 

open scoped ContDiff Topology
open Set Filter Function

 theorem continuous_localized_continuation (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → (Fin n → ℝ)) (hF : Continuous F)
    (hzero : ∀ x, F (0,x)=x)
    (Ω : Set (Fin n → ℝ)) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (h0 : 0∈Ω)
    (hside : ∀ t∈Icc (0:ℝ) 1, ∀ x∈closure Ω, x∉Ω → F (t,x)≠0) :
    ∃ x∈Ω, F (1,x)=0 := by
  classical
  by_contra hn
  have hfinal (x : Fin n → ℝ) (hx : x∈closure Ω) : F (1,x)≠0 := by
    by_cases hm : x∈Ω
    · exact fun he => hn ⟨x,hm,he⟩
    · exact hside 1 ⟨zero_le_one,le_rfl⟩ x hx hm
  let K := (Icc (0:ℝ) 1 ×ˢ (closure Ω\Ω)) ∪ ({1} ×ˢ closure Ω)
  have hK : IsCompact K := ((isCompact_Icc.prod
    (hb.isCompact_closure.inter_right ho.isClosed_compl))).union
      (isCompact_singleton.prod hb.isCompact_closure)
  have hz : (0 : Fin n → ℝ)∉F '' K := by
    rintro ⟨⟨t,x⟩,hy,he⟩
    rcases hy with hy|hy
    · exact hside t hy.1 x hy.2.1 hy.2.2 he
    · have ht : t=1 := hy.1
      exact hfinal x hy.2 (ht ▸ he)
  obtain ⟨ε,hε,havoid⟩ := Metric.isOpen_iff.mp (hK.image hF).isClosed.isOpen_compl 0 hz
  obtain ⟨H,hH,happ,_⟩ := hF.exists_contDiff_approx ⊤
    (continuous_const (y := ε/3)) (fun _ => by positivity)
  let G : ℝ × (Fin n → ℝ) → (Fin n → ℝ) := fun y => H y-H (0,y.2)+y.2
  have hG : ContDiff ℝ ∞ G :=
    (hH.sub (hH.comp (contDiff_const.prodMk contDiff_snd))).add contDiff_snd
  have hG0 (x : Fin n → ℝ) : G (0,x)=x := by simp [G]
  have hdist (y : ℝ × (Fin n → ℝ)) : dist (G y) (F y)<ε := by
    have h1 := happ y
    have h2 := happ (0,y.2)
    rw [hzero] at h2
    rw [dist_eq_norm] at h1 h2 ⊢
    have he : G y-F y=(H y-F y)-(H (0,y.2)-y.2) := by dsimp [G]; abel
    rw [he]
    have hh := norm_sub_le (H y-F y) (H (0,y.2)-y.2)
    linarith
  have hnonzero (y : ℝ × (Fin n → ℝ)) (hy : y∈K) : G y≠0 := by
    intro he
    have hball : F y∈Metric.ball 0 ε := by
      have hd := hdist y
      rw [he,dist_comm] at hd
      exact hd
    exact havoid hball ⟨y,hy,rfl⟩
  obtain ⟨x,hx,hGx⟩ := localized_continuation n G hG hG0 Ω ho hb h0 (by
    intro t ht x hx hn
    exact hnonzero (t,x) (Or.inl ⟨ht,hx,hn⟩))
  exact hnonzero (1,x) (Or.inr ⟨rfl,subset_closure hx⟩) hGx


 

 

open scoped ContDiff Topology
open Set Filter Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 

theorem finite_rank_approx (S : Set E) (hS : IsCompact S) (ε : ℝ) (hε : 0<ε) :
    ∃ V : Submodule ℝ E, FiniteDimensional ℝ V ∧
      ∃ P : E → V, Continuous P ∧ ∀ x∈S, ‖(P x : E)-x‖<ε := by
  classical
  obtain ⟨s,hs⟩ := hS.elim_finite_subcover (fun x : E => Metric.ball x (ε/2))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨x,Metric.mem_ball_self (half_pos hε)⟩)
  have hcov : S⊆⋃ i : (↑s : Set E), Metric.ball (i:E) (ε/2) := by
    intro x hx
    obtain ⟨y,hy,hm⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hm⟩
  obtain ⟨ρ,hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite
    hS.isClosed (fun i : (↑s : Set E) => Metric.ball (i:E) (ε/2))
    (fun _ => Metric.isOpen_ball) (locallyFinite_of_finite _) hcov
  let V := Submodule.span ℝ (↑s : Set E)
  have hV : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ s.finite_toSet
  let Q : E → E := fun x => ∑ i : (↑s : Set E), ρ i x • (i:E)
  have hQmem (x : E) : Q x∈V := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem V _ (Submodule.subset_span i.property)
  let P : E → V := fun x => ⟨Q x,hQmem x⟩
  have hQ : Continuous Q := continuous_finsetSum _ (fun index _ => (ρ index).continuous.smul continuous_const)
  refine ⟨V,hV,P,hQ.subtype_mk _,?_⟩
  intro x hx
  have hsum : ∑ i : (↑s : Set E), ρ i x=1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
  have he : (P x : E)-x=∑ i : (↑s : Set E), ρ i x • ((i:E)-x) := by
    change Q x-x=_
    change (∑ i : (↑s : Set E), ρ i x • (i:E))-x=_
    simp only [smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul,hsum,one_smul]
  have ht (i : (↑s : Set E)) : ‖ρ i x • ((i:E)-x)‖≤ρ i x*(ε/2) := by
    by_cases hi : ρ i x=0
    · simp only [hi,zero_smul,norm_zero,zero_mul,le_refl]
    · have hm := hρ i (subset_tsupport _ hi)
      have hd : ‖(i:E)-x‖<ε/2 := by simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hm
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (ρ.nonneg i x)]
      exact mul_le_mul_of_nonneg_left hd.le (ρ.nonneg i x)
  rw [he]
  calc
    ‖∑ i : (↑s : Set E), ρ i x • ((i:E)-x)‖ ≤ ∑ i : (↑s : Set E), ‖ρ i x • ((i:E)-x)‖ := norm_sum_le _ _
    _ ≤ ∑ i : (↑s : Set E), ρ i x*(ε/2) := Finset.sum_le_sum (fun i _ => ht i)
    _ = ε/2 := by rw [←Finset.sum_mul,hsum,one_mul]
    _ < ε := half_lt_self hε

end TwoPointContinuation

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_CompactContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function
namespace TwoPointContinuation

 theorem finite_space_continuation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (F : ℝ × E → E) (hF : Continuous F) (hzero : ∀ x, F (0,x)=x)
    (Ω : Set E) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (h0 : 0∈Ω)
    (hside : ∀ t∈Icc (0:ℝ) 1, ∀ x∈closure Ω, x∉Ω → F (t,x)≠0) :
    ∃ x∈Ω, F (1,x)=0 := by
  let n := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  let G : ℝ × (Fin n → ℝ) → (Fin n → ℝ) := fun y => e (F (y.1,e.symm y.2))
  have hG : Continuous G := e.continuous.comp (hF.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
  have hG0 (x : Fin n → ℝ) : G (0,x)=x := by simp [G,hzero]
  let U := e.symm ⁻¹' Ω
  have hU : U=e '' Ω := by
    ext x
    constructor
    · intro hx
      exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
    · rintro ⟨x,hx,rfl⟩
      simpa only [U,Set.mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hx
  have hu : IsOpen U := ho.preimage e.symm.continuous
  have hbu : Bornology.IsBounded U := by rw [hU]; exact e.toContinuousLinearMap.lipschitz.isBounded_image hb
  have h0u : 0∈U := by simpa only [U,Set.mem_preimage,ContinuousLinearEquiv.map_zero] using h0
  have hsu (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : Fin n → ℝ) (hx : x∈closure U) (hn : x∉U) : G (t,x)≠0 := by
    have hcl : e.symm x∈closure Ω := e.symm.continuous.closure_preimage_subset Ω hx
    intro he
    have hh : F (t,e.symm x)=0 := e.injective (by simpa only [G,ContinuousLinearEquiv.map_zero] using he)
    exact hside t ht (e.symm x) hcl hn hh
  obtain ⟨x,hx,hx0⟩ := continuous_localized_continuation n G hG hG0 U hu hbu h0u hsu
  refine ⟨e.symm x,hx,e.injective ?_⟩
  simpa only [G,ContinuousLinearEquiv.map_zero] using hx0


 

 

open scoped ContDiff Topology
open Set Filter Function

 theorem compact_residual_gap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ × E → E) (hT : Continuous T) (D : Set (ℝ × E)) (hD : IsClosed D)
    (ht : ∀ y∈D, y.1∈Icc (0:ℝ) 1)
    (S : Set E) (hS : IsCompact S) (hTS : ∀ y∈D, T y∈S)
    (hno : ∀ y∈D, y.2-T y≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ y∈D, δ≤‖y.2-T y‖ := by
  classical
  by_contra hn
  push Not at hn
  have hh (n : ℕ) : ∃ y∈D, ‖y.2-T y‖<1/((n:ℝ)+1) := hn _ (by positivity)
  choose y hy hyr using hh
  have hr : Tendsto (fun n => (y n).2-T (y n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hyr n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨a,ha,φ,hφ,hm⟩ := (isCompact_Icc.prod hS).tendsto_subseq
    (x := fun n => ((y n).1,T (y n))) (fun n => ⟨ht (y n) (hy n),hTS (y n) (hy n)⟩)
  have hx : Tendsto (fun n => (y (φ n)).2) atTop (𝓝 a.2) := by
    have hh := hm.snd_nhds.add (hr.comp hφ.tendsto_atTop)
    simpa only [comp_apply,add_sub_cancel,add_zero] using hh
  have hyconv : Tendsto (y ∘ φ) atTop (𝓝 a) := hm.fst_nhds.prodMk_nhds hx
  have had : a∈D := hD.mem_of_tendsto hyconv (Eventually.of_forall (fun n => hy (φ n)))
  have he : T a=a.2 := tendsto_nhds_unique (hT.continuousAt.tendsto.comp hyconv) hm.snd_nhds
  exact hno a had (sub_eq_zero.mpr he.symm)


 

 

open scoped ContDiff Topology
open Set Filter Function

 

theorem compact_continuation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ × E → E) (hT : Continuous T) (hzero : ∀ x, T (0,x)=0)
    (Ω : Set E) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (h0 : 0∈Ω)
    (S : Set E) (hS : IsCompact S)
    (hTS : ∀ t∈Icc (0:ℝ) 1, ∀ x∈closure Ω, T (t,x)∈S)
    (hside : ∀ t∈Icc (0:ℝ) 1, ∀ x∈closure Ω, x∉Ω → T (t,x)≠x) :
    ∃ x∈Ω, T (1,x)=x := by
  classical
  by_contra hn
  have hfinal (x : E) (hx : x∈closure Ω) : T (1,x)≠x := by
    by_cases hm : x∈Ω
    · exact fun he => hn ⟨x,hm,he⟩
    · exact hside 1 ⟨zero_le_one,le_rfl⟩ x hx hm
  let D := (Icc (0:ℝ) 1 ×ˢ (closure Ω\Ω)) ∪ ({1} ×ˢ closure Ω)
  have hD : IsClosed D := (isClosed_Icc.prod (isClosed_closure.inter ho.isClosed_compl)).union
    (isClosed_singleton.prod isClosed_closure)
  have htd (y : ℝ × E) (hy : y∈D) : y.1∈Icc (0:ℝ) 1 := by
    rcases hy with hy|hy
    · exact hy.1
    · rw [show y.1=1 from hy.1]; exact ⟨zero_le_one,le_rfl⟩
  have hxd (y : ℝ × E) (hy : y∈D) : y.2∈closure Ω := by
    rcases hy with hy|hy
    · exact hy.2.1
    · exact hy.2
  have hTSd (y : ℝ × E) (hy : y∈D) : T y∈S := hTS y.1 (htd y hy) y.2 (hxd y hy)
  have hno (y : ℝ × E) (hy : y∈D) : y.2-T y≠0 := by
    intro he
    have he' : T y=y.2 := (sub_eq_zero.mp he).symm
    rcases hy with hy|hy
    · exact hside y.1 hy.1 y.2 hy.2.1 hy.2.2 he'
    · have ht : y.1=1 := hy.1
      exact hfinal y.2 hy.2 (by simpa only [←ht] using he')
  obtain ⟨δ,hδ,hgap⟩ := compact_residual_gap T hT D hD htd S hS hTSd hno
  obtain ⟨V,hV,P,hP,happ⟩ := finite_rank_approx (S∪{0}) (hS.union isCompact_singleton)
    (δ/4) (by positivity)
  let : FiniteDimensional ℝ V := hV
  let F : ℝ × V → V := fun y => y.2-(P (T (y.1,(y.2:E)))-P 0)
  have hF : Continuous F := continuous_snd.sub
    ((hP.comp (hT.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))).sub continuous_const)
  have hF0 (x : V) : F (0,x)=x := by simp [F,hzero]
  let U := ((↑) : V → E) ⁻¹' Ω
  have hu : IsOpen U := ho.preimage continuous_subtype_val
  have hbu : Bornology.IsBounded U := by
    obtain ⟨R,hR,hbR⟩ := hb.exists_pos_norm_le
    apply (Metric.isBounded_iff_subset_closedBall (0:V)).mpr
    refine ⟨R,fun x hx => ?_⟩
    change dist x 0≤R
    rw [dist_zero_right]
    change ‖(x:E)‖≤R
    exact hbR (x:E) hx
  have h0u : (0:V)∈U := h0
  have hclose (x : V) (hx : x∈closure U) : (x:E)∈closure Ω :=
    continuous_subtype_val.closure_preimage_subset Ω hx
  have hnear (t : ℝ) (x : V) (hmem : T (t,(x:E))∈S) (hf : F (t,x)=0) :
      ‖(x:E)-T (t,(x:E))‖<δ := by
    have he : (x:E)=(P (T (t,(x:E))) : E)-(P 0:E) :=
      congrArg (fun u : V => (u:E)) (sub_eq_zero.mp hf)
    have h1 := happ (T (t,(x:E))) (Or.inl hmem)
    have h2 := happ 0 (Or.inr rfl)
    simp only [sub_zero] at h2
    have he' : (x:E)-T (t,(x:E))=((P (T (t,(x:E))):E)-T (t,(x:E)))-(P 0:E) := by
      calc
        (x:E)-T (t,(x:E))=((P (T (t,(x:E))):E)-(P 0:E))-T (t,(x:E)) :=
          congrArg (fun v : E => v-T (t,(x:E))) he
        _ = _ := by abel
    rw [he']
    have hh := norm_sub_le ((P (T (t,(x:E))):E)-T (t,(x:E))) (P 0:E)
    linarith
  have hsideF (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : V) (hx : x∈closure U) (hn : x∉U) : F (t,x)≠0 := by
    intro hf
    exact (not_lt_of_ge (hgap (t,(x:E)) (Or.inl ⟨ht,hclose x hx,hn⟩)))
      (hnear t x (hTS t ht (x:E) (hclose x hx)) hf)
  obtain ⟨x,hx,hfx⟩ := finite_space_continuation F hF hF0 U hu hbu h0u hsideF
  have hxcl : (x:E)∈closure Ω := subset_closure hx
  exact (not_lt_of_ge (hgap (1,(x:E)) (Or.inr ⟨rfl,hxcl⟩)))
    (hnear 1 x (hTS 1 ⟨zero_le_one,le_rfl⟩ (x:E) hxcl) hfx)


 

 

open scoped ContDiff Topology
open Set Filter Function

 theorem local_compact_continuation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ × E → E) (U : Set E) (hU : IsOpen U)
    (hT : ∀ t∈Icc (0:ℝ) 1, ∀ x∈U, ContinuousAt T (t,x))
    (hzero : ∀ x∈U, T (0,x)=0)
    (S : Set E) (hS : IsCompact S) (hTS : ∀ t∈Icc (0:ℝ) 1, ∀ x∈U, T (t,x)∈S)
    (K : Set E) (hK : IsCompact K) (hKU : K⊆U) (h0 : 0∈K)
    (hfix : ∀ t∈Icc (0:ℝ) 1, ∀ x∈U, T (t,x)=x → x∈K) :
    ∃ x∈U, T (1,x)=x := by
  classical
  obtain ⟨χ,hχ0,hχ1,hχb⟩ := exists_continuous_zero_one_of_isClosed
    hU.isClosed_compl hK.isClosed (Set.disjoint_left.mpr (fun x hx hk => hx (hKU hk)))
  let ρ : E → ℝ := fun x => min 1 (max 0 (4*(χ x-1/4)))
  have hρ : Continuous ρ := continuous_const.min (continuous_const.max
    (continuous_const.mul (χ.continuous.sub continuous_const)))
  have hρb (x : E) : ρ x∈Icc (0:ℝ) 1 := by
    dsimp [ρ]
    exact ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
  have hρone (x : E) (hx : (1/2:ℝ)≤χ x) : ρ x=1 := by
    dsimp [ρ]
    rw [min_eq_left]
    exact (by linarith : (1:ℝ)≤4*(χ x-1/4)).trans (le_max_right _ _)
  have hρzero (x : E) (hx : χ x≤(1/4:ℝ)) : ρ x=0 := by
    dsimp [ρ]
    rw [max_eq_left (by linarith),min_eq_right (by norm_num)]
  let τ : ℝ → ℝ := fun t => min 1 (max 0 t)
  have hτ : Continuous τ := continuous_const.min (continuous_const.max continuous_id)
  have hτb (t : ℝ) : τ t∈Icc (0:ℝ) 1 :=
    ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
  have hτe (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : τ t=t := by
    dsimp [τ]; rw [max_eq_right ht.1,min_eq_right ht.2]
  let G : ℝ × E → E := fun y => ρ y.2 • T (τ y.1,y.2)
  have hG : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hx : y.2∈U
    · exact (hρ.comp continuous_snd).continuousAt.smul
        ((hT (τ y.1) (hτb y.1) y.2 hx).comp (f := fun z : ℝ × E => (τ z.1,z.2)) ((hτ.comp continuous_fst).prodMk continuous_snd).continuousAt)
    · have hc : χ y.2=0 := hχ0 hx
      have hn : ∀ᶠ z : ℝ × E in 𝓝 y, χ z.2<(1/4:ℝ) :=
        (χ.continuous.comp continuous_snd).continuousAt.eventually (eventually_lt_nhds (by change χ y.2<(1/4:ℝ); rw [hc]; norm_num))
      apply (continuousAt_const (y := (0:E))).congr_of_eventuallyEq
      filter_upwards [hn] with z hz
      change ρ z.2 • T (τ z.1,z.2)=(0:E)
      rw [hρzero z.2 hz.le,zero_smul]
  have hG0 (x : E) : G (0,x)=0 := by
    by_cases hx : x∈U
    · simp only [G,hτe 0 ⟨le_rfl,zero_le_one⟩,hzero x hx,smul_zero]
    · simp only [G,hρzero x (by rw [hχ0 hx]; norm_num),zero_smul]
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 (0:E)
  let Ω := {x : E | (3/4:ℝ)<χ x} ∩ Metric.ball 0 R
  have ho : IsOpen Ω := (isOpen_lt continuous_const χ.continuous).inter Metric.isOpen_ball
  have hb : Bornology.IsBounded Ω := Metric.isBounded_ball.subset inter_subset_right
  have hKΩ : K⊆Ω := by
    intro x hx
    exact ⟨by change (3/4:ℝ)<χ x; rw [hχ1 hx]; norm_num,hKR hx⟩
  have hcl (x : E) (hx : x∈closure Ω) : (3/4:ℝ)≤χ x := by
    exact closure_minimal (t := {x : E | (3/4:ℝ)≤χ x}) (by intro x (hx : x∈Ω); change (3/4:ℝ)≤χ x; exact hx.1.le) (isClosed_le continuous_const χ.continuous) hx
  have hclU (x : E) (hx : x∈closure Ω) : x∈U := by
    by_contra hn
    have hh := hcl x hx
    rw [hχ0 hn] at hh
    norm_num at hh
  have hGe (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : E) (hx : x∈closure Ω) : G (t,x)=T (t,x) := by
    simp only [G,hτe t ht,hρone x (by have hh := hcl x hx; linarith),one_smul]
  obtain ⟨x,hx,he⟩ := compact_continuation G hG hG0 Ω ho hb (hKΩ h0) S hS
    (fun t ht x hx => by rw [hGe t ht x hx]; exact hTS t ht x (hclU x hx))
    (by
      intro t ht x hx hn he
      rw [hGe t ht x hx] at he
      exact hn (hKΩ (hfix t ht x (hclU x hx) he)))
  exact ⟨x,hclU x (subset_closure hx),by rwa [hGe 1 ⟨zero_le_one,le_rfl⟩ x (subset_closure hx)] at he⟩


 

 

open scoped Topology
open Set Filter Function

 theorem compact_tube_precompact {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace F] (T : ℝ × E → F) (K : Set E) (hK : IsCompact K)
    (hlocal : ∀ y∈Icc (0:ℝ) 1 ×ˢ K, LocallyPrecompact T y) :
    ∃ U : Set E, IsOpen U ∧ K⊆U ∧ ∃ S : Set F, IsCompact S ∧
      ∀ t∈Icc (0:ℝ) 1, ∀ x∈U, T (t,x)∈S := by
  classical
  let Y := Icc (0:ℝ) 1 ×ˢ K
  have hY : IsCompact Y := isCompact_Icc.prod hK
  have hchoice : ∀ y : Y, ∃ W : Set (ℝ×E), IsOpen W ∧ (y : ℝ×E)∈W ∧
      ∃ C : Set F, IsCompact C ∧ T '' W⊆C := by
    intro y
    obtain ⟨V,hV,C,hC,hTC⟩ := hlocal y y.2
    obtain ⟨W,hWV,ho,hyW⟩ := mem_nhds_iff.mp hV
    exact ⟨W,ho,hyW,C,hC,(image_mono hWV).trans hTC⟩
  choose W hWo hyW C hC hTC using hchoice
  obtain ⟨s,hs⟩ := hY.elim_finite_subcover W hWo (by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hyW ⟨y,hy⟩⟩)
  let O := ⋃ y∈s, W y
  have ho : IsOpen O := isOpen_biUnion (fun y hy => hWo y)
  obtain ⟨δ,hδ,hδO⟩ := hY.exists_thickening_subset_open ho hs
  refine ⟨Metric.thickening δ K,Metric.isOpen_thickening,Metric.self_subset_thickening hδ _,
    ⋃ y∈s, C y,?_ ,?_⟩
  · exact s.finite_toSet.isCompact_biUnion (fun y hy => hC y)
  · intro t ht x hx
    obtain ⟨k,hk,hxk⟩ := Metric.mem_thickening_iff.mp hx
    have hyO : (t,x)∈O := hδO (Metric.mem_thickening_iff.mpr ⟨(t,k),⟨ht,hk⟩,by
      simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : (0:ℝ)≤dist x k)] using hxk⟩)
    obtain ⟨y,hy,hyW⟩ := mem_iUnion₂.mp hyO
    exact mem_iUnion₂.mpr ⟨y,hy,hTC y ⟨(t,x),hyW,rfl⟩⟩

 theorem local_degree_continuation_oai {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ × E → E) (V : Set E) (hV : IsOpen V)
    (hT : ∀ t∈Icc (0:ℝ) 1, ∀ x∈V, ContinuousAt T (t,x))
    (hzero : ∀ x∈V, T (0,x)=0)
    (K : Set E) (hK : IsCompact K) (hKV : K⊆V) (h0 : 0∈K)
    (hfix : ∀ t∈Icc (0:ℝ) 1, ∀ x∈V, T (t,x)=x → x∈K)
    (hloc : ∀ t∈Icc (0:ℝ) 1, ∀ x∈K, LocallyPrecompact T (t,x)) :
    ∃ x∈V, T (1,x)=x := by
  obtain ⟨U,hU,hKU,S,hS,hTS⟩ := compact_tube_precompact T K hK (fun y hy => hloc y.1 hy.1 y.2 hy.2)
  obtain ⟨x,hx,he⟩ := local_compact_continuation T (U∩V) (hU.inter hV)
    (fun t ht x hx => hT t ht x hx.2) (fun x hx => hzero x hx.2) S hS
    (fun t ht x hx => hTS t ht x hx.1) K hK (fun x hx => ⟨hKU hx,hKV hx⟩) h0
    (fun t ht x hx he => hfix t ht x hx.2 he)
  exact ⟨x,hx.2,he⟩

end TwoPointContinuation

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TwoPointContinuation.local_degree_continuation_oai.{u_1} := @OAI.TwoPointContinuation.local_degree_continuation_oai.{u_1}
