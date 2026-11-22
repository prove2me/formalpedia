-- Prove2me | solution 1 for NoHair.schwarzschild_time_translation_static
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:52:36.7338+00:00
-- url     : https://prove2.me/submissions/fa3fbad7-2f7e-4798-b198-b838d8315ed9

import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms

open NoHair NoHair.KNE Set
open scoped Manifold ContDiff Topology

noncomputable section

private abbrev I4 := 𝓘(ℝ,E4)
private abbrev U := kerrNewmanSpacetime 0

private lemma generator (φ : ℝ → U → U) (act : ∀ s x, (φ s x).val = x.val+s • coordBasis 0)
    (x : U) : flowGenerator φ x = coordBasis 0 := by
  let orbit := fun t : ℝ => φ t x
  let inc := (Subtype.val : U → E4)
  have heq : inc ∘ orbit = fun s : ℝ => x.val+s • coordBasis 0 := funext (fun s => act s x)
  have smooth : ContMDiff 𝓘(ℝ,ℝ) I4 ∞ orbit := by
    apply (ContMDiff.subtypeVal_comp_iff U orbit).mp
    rw [heq]
    exact contMDiff_const.add (contMDiff_id.smul contMDiff_const)
  have dinc : (mfderiv I4 I4 inc (orbit 0) : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 :=
    mfderiv_extChartAt_self (I := I4) (x := orbit 0)
  have hd : HasDerivAt (fun s : ℝ => x.val+s • coordBasis 0) (coordBasis 0) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (coordBasis 0)).const_add x.val
  have compId : mfderiv 𝓘(ℝ,ℝ) I4 (inc ∘ orbit) 0 =
      (mfderiv 𝓘(ℝ,ℝ) I4 orbit 0 : ℝ →L[ℝ] E4) := by
    rw [mfderiv_comp (I' := I4) _ ((contMDiff_subtype_val (I := I4) (U := U) (n := ∞)).mdifferentiableAt (by simp))
      (smooth.mdifferentiableAt (by simp)),dinc]; rfl
  change (mfderiv 𝓘(ℝ,ℝ) I4 orbit 0 : ℝ →L[ℝ] E4) 1 = _
  rw [← compId,heq,mfderiv_eq_fderiv]
  exact hd.deriv

private lemma entry (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    matrixBilin A (coordBasis i) (coordBasis j) = A i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (coordBasis i)) (WithLp.ofLp (coordBasis j)) = _
  simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
  rw [Matrix.toLinearMap₂'_apply]
  simp_rw [← Finset.smul_sum]
  simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']

private lemma four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by fin_cases i <;> decide
private lemma v0 {α : Type*} (a b c d : α) : ![a,b,c,d] (0 : Fin 4) = a := rfl
private lemma v1 {α : Type*} (a b c d : α) : ![a,b,c,d] (1 : Fin 4) = b := rfl
private lemma v2 {α : Type*} (a b c d : α) : ![a,b,c,d] (2 : Fin 4) = c := rfl
private lemma v3 {α : Type*} (a b c d : α) : ![a,b,c,d] (3 : Fin 4) = d := rfl

set_option maxHeartbeats 4500000 in
private lemma twist_atoms (R X Y Z W : ℝ) (i j k : Fin 4) :
    let K := fun l => etaT 0 l + fA 0 1 0 R W * Kv X Y Z l
    let J := dgA 0 1 0 R X Y Z W 0
    K i*(J k j-J j k)+K j*(J i k-J k i)+K k*(J j i-J i j) = 0 := by
  dsimp only
  rcases four i with rfl | rfl | rfl | rfl <;>
    rcases four j with rfl | rfl | rfl | rfl <;>
    rcases four k with rfl | rfl | rfl | rfl <;>
    first | (solve | ring) | (simp only [dgA, dfA, fA, Kv, dKt, etaT, Matrix.of_apply, v0,v1,v2,v3,
      mul_zero, zero_mul, zero_add, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0)] <;> ring)

theorem solution (φ : ℝ → kerrNewmanSpacetime 0 → kerrNewmanSpacetime 0)
    (hφ : ∀ s x, (φ s x).val = x.val + s • coordBasis 0) :
    IsStaticOn (kerrNewmanMetricField 1 0 0) φ Set.univ := by
  intro e he y hy _ i j k
  obtain ⟨_, hp⟩ := TopologicalSpace.Opens.chart_eq (H := E4) ⟨e.symm y⟩ he
  have hchart (x : U) : e = chartAt E4 x := hp.trans (by rfl)
  have hval (z : E4) (hz : z ∈ e.target) : (e.symm z).val = z := by
    have hh (x : U) : e x = x.val := by rw [hchart x]; rfl
    exact (hh (e.symm z)).symm.trans (e.right_inv hz)
  have hder (z : E4) (hz : z ∈ e.target) :
      (mfderiv I4 I4 e.symm z : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    have der (x : U) : (mfderiv I4 I4 e.symm x.val : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
      rw [hchart x]
      have hd := mfderivWithin_range_extChartAt_symm (I := I4) (x := x)
      simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hd
      exact hd
    have hd := der (e.symm z)
    rwa [hval z hz] at hd
  let K := fun z => loweredCoeffs (kerrNewmanMetricField 1 0 0) (flowGenerator φ) e.symm z
  have coeff (z : E4) (hz : z ∈ e.target) (l : Fin 4) : K z l = kerrNewmanMetric 1 0 0 z 0 l := by
    dsimp only [K,loweredCoeffs]
    rw [generator φ hφ, hder z hz]
    change matrixBilin (kerrNewmanMetric 1 0 0 (e.symm z).val) (coordBasis 0) (coordBasis l) = _
    rw [hval z hz, entry]
  have hr : 0 < ksRadius 0 y := hval y hy ▸ (e.symm y).property
  have J (a b : Fin 4) : coordPartial (fun z => K z a) b y =
      dgA 0 1 0 (ksRadius 0 y) (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3) (Wf 0 y) 0 a b := by
    have eq : EqOn (fun z => K z a) (fun z => kerrNewmanMetric 1 0 0 z 0 a) e.target :=
      fun z hz => coeff z hz a
    have dd := (eq.eventuallyEq_of_mem (e.open_target.mem_nhds hy)).fderiv_eq (𝕜 := ℝ)
    calc
      _ = coordPartial (fun z => kerrNewmanMetric 1 0 0 z 0 a) b y := by simp only [coordPartial, dd]
      _ = _ := cp_metric 1 0 0 y hr 0 a b
  have valK (l : Fin 4) : K y l = etaT 0 l + fA 0 1 0 (ksRadius 0 y) (Wf 0 y) *
      Kv (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3) l := by
    rw [coeff y hy, kerrNewmanMetric, profile_eq 1 0 0 y hr,ksNull_zero,mul_one]
    rw [minkowski_eq]
    exact congrArg (fun t => etaT 0 l + fA 0 1 0 (ksRadius 0 y) (Wf 0 y)*t)
      (congrFun (ksNull_eq_Kv 0 y) l)
  change K y i*(coordPartial (fun z => K z k) j y - coordPartial (fun z => K z j) k y)+
    K y j*(coordPartial (fun z => K z i) k y - coordPartial (fun z => K z k) i y)+
    K y k*(coordPartial (fun z => K z j) i y - coordPartial (fun z => K z i) j y)=0
  simp only [J, valK]
  exact twist_atoms _ _ _ _ _ i j k
