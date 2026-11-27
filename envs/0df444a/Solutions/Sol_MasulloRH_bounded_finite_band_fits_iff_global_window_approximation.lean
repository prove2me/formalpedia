-- Prove2me | solution 1 for MasulloRH.bounded_finite_band_fits_iff_global_window_approximation
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T04:31:41.656624+00:00
-- url     : https://prove2.me/submissions/9ee8b2d1-3ccd-4882-8d03-1db25fe0ff15

import Definitions.Def_MasulloRH_FiniteMellinBands
import Theorems.Thm_MasulloRH_common_rational_gaussian_fit_on_every_finite_frequency_band
import Theorems.Thm_MasulloRH_window_energy_sandwiched_by_endpoint_mellin_errors
import Theorems.Thm_MasulloRH_fixed_gaussian_energy_lower_at_every_zeta_zero
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter Topology MasulloRH MasulloRH.GaussianApproximation
open MasulloRH.RationalThetaGrid MasulloRH.VerticalThetaApproximation MasulloRH.FiniteMellinBands

private lemma densityNonnegative {m : ℕ} (L U : ℝ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ) (t : ℝ) :
    0 ≤ errorDensity L U a y t := add_nonneg (sq_nonneg _) (sq_nonneg _)

private lemma densityIntegral {m : ℕ} (L U : ℝ) (hL : 0<L) (hLU : L<U) (hU : U<1)
    (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ) :
    Integrable (errorDensity L U a y) ∧ (∫ t : ℝ, errorDensity L U a y t)=total L U a y := by
  have hl := ((window_energy_sandwiched_by_endpoint_mellin_errors a y).1 L hL (hLU.trans hU)).1
  have hu := ((window_energy_sandwiched_by_endpoint_mellin_errors a y).1 U (hL.trans hLU) hU).1
  exact ⟨hl.add hu,integral_add hl hu⟩

private lemma smallTail {m : ℕ} (L U η : ℝ) (hL : 0<L) (hLU : L<U) (hU : U<1) (hη : 0<η)
    (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ) :
    ∃ T : ℝ, 0≤T ∧ total L U a y - band L U T a y < η := by
  let S := fun n : ℕ => Icc (-(n:ℝ)) (n:ℝ)
  have mono : Monotone S := fun _ _ hij => Icc_subset_Icc (neg_le_neg (Nat.cast_le.mpr hij)) (by exact_mod_cast hij)
  have cover : (⋃ n, S n)=univ := iUnion_eq_univ_iff.mpr fun t =>
    ⟨⌈|t|⌉₊,abs_le.mp (Nat.le_ceil |t|)⟩
  have ⟨hi,eq⟩ := densityIntegral L U hL hLU hU a y
  have h := tendsto_setIntegral_of_monotone (fun n => (measurableSet_Icc : MeasurableSet (S n))) mono hi.integrableOn
  rw [cover,setIntegral_univ,eq] at h
  obtain ⟨n,h⟩ := (h.eventually_const_lt (sub_lt_self _ hη)).exists
  exact ⟨n,Nat.cast_nonneg n,by change total L U a y - (∫ t in S n, errorDensity L U a y t)<η; linarith⟩

private def scaled (u : ℚ) (a : ℚ×ℚ) := (u*a.1,u*a.2)
private lemma scaleComplex (u : ℚ) (a : ℚ×ℚ) : asComplex (scaled u a) = (u:ℂ)*asComplex a := by
  simp [scaled,asComplex,mul_add,mul_assoc]

private lemma convexBounds (q : ℚ) (hq : 0≤q) (hq' : q≤1) (u v : ℂ) :
    ‖((1-(q:ℝ):ℝ):ℂ)*u+((q:ℝ):ℂ)*v‖^2 ≤ (1-(q:ℝ))*‖u‖^2+(q:ℝ)*‖v‖^2 ∧
    ‖((1-(q:ℝ):ℝ):ℂ)*u+((q:ℝ):ℂ)*v‖^2 ≤ 2*‖u‖^2+2*(q:ℝ)^2*‖v‖^2 := by
  let r : ℝ := q
  have hr : 0≤r := by dsimp [r]; exact_mod_cast hq
  have h1 : 0≤1-r := by dsimp [r]; exact_mod_cast sub_nonneg.mpr hq'
  have hnorm : ‖((1-r:ℝ):ℂ)*u+(r:ℂ)*v‖ ≤ (1-r)*‖u‖+r*‖v‖ := by
    apply (norm_add_le _ _).trans_eq
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h1,abs_of_nonneg hr]
  have hs := mul_self_le_mul_self (norm_nonneg _) hnorm
  change ‖((1-r:ℝ):ℂ)*u+(r:ℂ)*v‖^2 ≤ _ ∧ ‖((1-r:ℝ):ℂ)*u+(r:ℂ)*v‖^2 ≤ _
  change _ ≤ (1-r)*‖u‖^2+r*‖v‖^2 ∧ _ ≤ 2*‖u‖^2+2*r^2*‖v‖^2
  constructor
  · nlinarith only [hs,mul_nonneg (mul_nonneg hr h1) (sq_nonneg (‖u‖-‖v‖))]
  · have hsq : 0≤1-(1-r)^2 := by nlinarith only [hr,mul_nonneg hr h1]
    nlinarith only [hs,sq_nonneg ((1-r)*‖u‖-r*‖v‖),mul_nonneg hsq (sq_nonneg ‖u‖)]

private lemma mixing (L U T : ℝ) (hL : 0<L) (hLU : L<U) (hU : U<1)
    (q : ℚ) (hq : 0≤q) (hq' : q≤1)
    {m n : ℕ} (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ) (b : Fin n → ℚ×ℚ) (z : Fin n → ℚ) :
    ∃ (k : ℕ) (d : Fin k → ℚ×ℚ) (v : Fin k → ℚ), total L U d v ≤
      (1-(q:ℝ))*total L U a y + (q:ℝ)*band L U T b z +
      2*(total L U a y-band L U T a y) + 2*(q:ℝ)^2*total L U b z := by
  let d := Fin.append (fun i => scaled (1-q) (a i)) (fun j => scaled q (b j))
  let v := Fin.append y z
  let E := fun {k : ℕ} (a : Fin k → ℚ×ℚ) (y : Fin k → ℚ) => errorDensity L U a y
  have eq (c t : ℝ) : VerticalThetaApproximation.spectrum c d v t =
      ((1-(q:ℝ):ℝ):ℂ)*VerticalThetaApproximation.spectrum c a y t +
      ((q:ℝ):ℂ)*VerticalThetaApproximation.spectrum c b z t := by
    simp only [VerticalThetaApproximation.spectrum,d,v,Fin.sum_univ_add,Fin.append_left,Fin.append_right,
      scaleComplex,mul_assoc,← Finset.mul_sum]
    push_cast
    ring
  let r : ℝ := q
  have hr : 0≤r := by dsimp [r]; exact_mod_cast hq
  have h1 : 0≤1-r := by dsimp [r]; exact_mod_cast sub_nonneg.mpr hq'
  have point (t : ℝ) : E d v t ≤ (1-r)*E a y t+r*E b z t ∧
      E d v t ≤ 2*E a y t+(2*r^2)*E b z t := by
    have h (c : ℝ) := convexBounds q hq hq' (VerticalThetaApproximation.spectrum c a y t)
      (VerticalThetaApproximation.spectrum c b z t)
    dsimp only [E,errorDensity]
    rw [eq,eq]
    dsimp only [r]
    constructor
    · linarith only [(h L).1,(h U).1]
    · linarith only [(h L).2,(h U).2]
  let S := Icc (-T) T
  obtain ⟨ia,ea⟩ := densityIntegral L U hL hLU hU a y
  obtain ⟨ib,eb⟩ := densityIntegral L U hL hLU hU b z
  obtain ⟨id,ed⟩ := densityIntegral L U hL hLU hU d v
  have lo := setIntegral_mono_ae (s:=S) id.integrableOn
    ((ia.const_mul (1-r)).add (ib.const_mul r)).integrableOn (Eventually.of_forall fun t => (point t).1)
  have hi := setIntegral_mono_ae (s:=Sᶜ) id.integrableOn
    ((ia.const_mul 2).add (ib.const_mul (2*r^2))).integrableOn (Eventually.of_forall fun t => (point t).2)
  change (∫ t in S, E d v t) ≤ ∫ t in S, (1-r)*E a y t+r*E b z t at lo
  change (∫ t in Sᶜ, E d v t) ≤ ∫ t in Sᶜ, 2*E a y t+(2*r^2)*E b z t at hi
  rw [integral_add (ia.integrableOn.const_mul _) (ib.integrableOn.const_mul _),integral_const_mul,integral_const_mul] at lo hi
  have eD := (integral_add_compl (s:=S) measurableSet_Icc id).trans ed
  have eA := (integral_add_compl (s:=S) measurableSet_Icc ia).trans ea
  have hA := (setIntegral_le_integral (s:=S) ia (Eventually.of_forall (densityNonnegative L U a y))).trans_eq ea
  have hB := (setIntegral_le_integral (s:=Sᶜ) ib (Eventually.of_forall (densityNonnegative L U b z))).trans_eq eb
  refine ⟨m+n,d,v,?_⟩
  change total L U d v ≤ (1-r)*total L U a y+r*(∫ t in S, E b z t)+
    2*(total L U a y-(∫ t in S, E a y t))+2*r^2*total L U b z
  change (∫ t in S, E d v t)+(∫ t in Sᶜ,E d v t)=_ at eD
  change (∫ t in S, E a y t)+(∫ t in Sᶜ,E a y t)=_ at eA
  change (∫ t in S, E a y t)≤_ at hA
  change (∫ t in Sᶜ, E b z t)≤_ at hB
  linarith only [lo,hi,eD,eA,mul_le_mul_of_nonneg_left hA h1,
    mul_le_mul_of_nonneg_left hB (show 0≤2*r^2 by positivity)]

private lemma boundedIff (L U : ℝ) (hL : 0<L) (hLU : L<U) (hU : U<1) :
    boundedFits L U ↔ ∀ ε : ℝ, 0<ε → ∃ (m : ℕ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ),
      total L U a y < ε := by
  constructor
  · rintro ⟨B,fit⟩
    let S : Set ℝ := {t | ∃ (m : ℕ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ), t=total L U a y}
    let d := sInf S
    have tot0 {m : ℕ} (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ) : 0≤total L U a y :=
      (integral_nonneg (densityNonnegative L U a y)).trans_eq (densityIntegral L U hL hLU hU a y).2
    obtain ⟨m,a,y,_,hB⟩ := fit 0 1 le_rfl one_pos
    have hBp : 0≤B := (tot0 a y).trans hB
    have ne : S.Nonempty := ⟨_,m,a,y,rfl⟩
    have lb : BddBelow S := ⟨0,by rintro _ ⟨m,a,y,rfl⟩;exact tot0 a y⟩
    have hd0 : 0≤d := le_csInf ne (by rintro _ ⟨m,a,y,rfl⟩;exact tot0 a y)
    have lower {m : ℕ} (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ) : d≤total L U a y :=
      csInf_le lb ⟨m,a,y,rfl⟩
    have dz : d=0 := by
      by_contra hn
      have dp : 0<d := lt_of_le_of_ne hd0 (Ne.symm hn)
      obtain ⟨q,hq,hq'⟩ := exists_rat_btwn (lt_min zero_lt_one (div_pos dp (show 0<8*(B+1) by positivity)))
      let r : ℝ := q
      have hr : 0<r := hq
      have hr1 : r<1 := (lt_min_iff.mp hq').1
      have small := (lt_div_iff₀ (show 0<8*(B+1) by positivity)).mp (lt_min_iff.mp hq').2
      change r*(8*(B+1))<d at small
      have slack : 0<r*d/8 := by positivity
      obtain ⟨_,⟨j,a,y,rfl⟩,hnear⟩ := exists_lt_of_csInf_lt ne (show d<d+r*d/8 by linarith)
      obtain ⟨T,hT,htail⟩ := smallTail L U (r*d/8) hL hLU hU slack a y
      obtain ⟨n,b,z,hloc,hfull⟩ := fit T (d/4) hT (by positivity)
      obtain ⟨_,v,w,hv⟩ := mixing L U T hL hLU hU q (by exact_mod_cast hq.le)
        (by exact_mod_cast (lt_min_iff.mp hq').1.le) a y b z
      have hlow := (lower v w).trans hv
      change d ≤ (1-r)*total L U a y + r*band L U T b z+
        2*(total L U a y-band L U T a y)+2*r^2*total L U b z at hlow
      have hnear' := mul_lt_mul_of_pos_left hnear (sub_pos.mpr hr1)
      have hloc' := mul_lt_mul_of_pos_left hloc hr
      have hsmall := mul_lt_mul_of_pos_left small hr
      have hf := mul_le_mul_of_nonneg_left hfull (sq_nonneg r)
      nlinarith only [hlow,hnear',hloc',htail,hsmall,hf,mul_pos hr dp,mul_nonneg (sq_nonneg r) dp.le,sq_nonneg r]
    intro ε hε
    obtain ⟨_,⟨m,a,y,rfl⟩,h⟩ := exists_lt_of_csInf_lt ne (show d<ε by rwa [dz])
    exact ⟨m,a,y,h⟩
  · intro fit
    refine ⟨1,fun T ε _ hε => ?_⟩
    obtain ⟨m,a,y,h⟩ := fit (min 1 ε) (lt_min one_pos hε)
    have ⟨hi,he⟩ := densityIntegral L U hL hLU hU a y
    have ha := (setIntegral_le_integral (s:=Icc (-T) T) hi (Eventually.of_forall (densityNonnegative L U a y))).trans_eq he
    exact ⟨m,a,y,ha.trans_lt ((lt_min_iff.mp h).2),(lt_min_iff.mp h).1.le⟩

theorem solution (L U : ℝ) (hL : 0<L) (hLU : L<U) (hU : U<1) :
    (boundedFits L U ↔ ∀ ε : ℝ, 0<ε →
      ∃ (m : ℕ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ), total L U a y < ε) ∧
    (∀ s : ℂ, L<s.re → s.re<U → riemannZeta s=0 → ∀ B : ℝ,
      ∃ T ε : ℝ, 0≤T ∧ 0<ε ∧
        (∃ (m : ℕ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ), band L U T a y < ε) ∧
        ∀ (m : ℕ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ),
          band L U T a y < ε → B<total L U a y) := by
  refine ⟨boundedIff L U hL hLU hU,?_⟩
  intro s hs hs' hz B
  let c := (L+U)/2
  let b := (U-L)/2
  have hl : c-b=L := by dsimp [c,b];ring
  have hu : c+b=U := by dsimp [c,b];ring
  have hi : |s.re-c|<b := abs_lt.mpr (by constructor <;> dsimp [c,b] <;> linarith)
  have bp : 0<b := (abs_nonneg _).trans_lt hi
  let C := Real.exp ((s.re^2-s.im^2)/2)*((b^2-(s.re-c)^2)/b)
  have cc : 0<C := by
    apply mul_pos (Real.exp_pos _) (div_pos _ bp)
    have ⟨hm,hp⟩ := abs_lt.mp hi
    nlinarith only [mul_pos (show 0<b-(s.re-c) by linarith) (show 0<b+(s.re-c) by linarith)]
  have nope : ¬boundedFits L U := by
    intro h
    obtain ⟨m,a,y,ht⟩ := (boundedIff L U hL hLU hU).mp h (2*Real.pi*C) (by positivity)
    have he := fixed_gaussian_energy_lower_at_every_zeta_zero c b (hl ▸ hL) (hu ▸ hU)
      (fun i => asComplex (a i)) (fun i => (y i:ℝ)) s hi hz
    have hwin := ((window_energy_sandwiched_by_endpoint_mellin_errors a y).2 c b bp.le
      (hl ▸ hL) (hu ▸ hU)).2.2
    rw [hl,hu] at hwin
    change C≤energy c b (approximation a y) at he
    change 2*Real.pi*energy c b (approximation a y) ≤ total L U a y at hwin
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left he (by positivity : 0≤2*Real.pi)).trans hwin)) ht
  unfold boundedFits at nope
  push Not at nope
  obtain ⟨T,ε,hT,hε,obstruction⟩ := nope B
  refine ⟨T,ε,hT,hε,common_rational_gaussian_fit_on_every_finite_frequency_band L U T ε hL hLU hU hε,?_⟩
  exact obstruction
