-- Prove2me | solution 1 for OAI.DeligneDrinfeld.FourFrames.associator_pentagon
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:54:12.729984+00:00
-- url     : https://prove2.me/submissions/944431d8-973e-48ac-981f-805479d08ba1

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldBraid

set_option linter.all false





section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section

namespace FinitePicard

section
open MeasureTheory Set intervalIntegral
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

variable [CompleteSpace A]

theorem continuous_term {Ω : ℝ → A} (hΩ : Continuous Ω) (a : ℝ) (n : ℕ) :
    Continuous (term Ω a n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact (intervalIntegral.differentiable_integral_of_continuous (hΩ.mul ih)).continuous

theorem derivative_succ {Ω : ℝ → A} (hΩ : Continuous Ω) (a t : ℝ) (n : ℕ) :
    HasDerivAt (term Ω a (n+1)) (Ω t * term Ω a n t) t := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (hΩ.mul (continuous_term hΩ a n)).intervalIntegrable a t
  · exact (hΩ.mul (continuous_term hΩ a n)).stronglyMeasurableAtFilter volume _
  · exact (hΩ.mul (continuous_term hΩ a n)).continuousAt

end

open MeasureTheory Set intervalIntegral
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

variable [FiniteDimensional ℝ A]

end FinitePicard

end

end DeligneDrinfeld

end

end OAI

end



section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section

namespace FinitePicard
open MeasureTheory Set
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem transition_constant_closed {f g Ω : ℝ → A} {a b u v : ℝ} (hab : a < b)
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (Ω s*f s) s)
    (hg : ∀ s ∈ Ioo a b, HasDerivAt g (Ω s*g s) s)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hu : ∀ s ∈ Icc a b, IsUnit (f s)) (huv : u ∈ Icc a b) (hvv : v ∈ Icc a b) :
    Ring.inverse (f u)*g u=Ring.inverse (f v)*g v := by
  let c := (a+b)/2
  have hc : c ∈ Ioo a b := ⟨by dsimp [c]; linarith,by dsimp [c]; linarith⟩
  have he : EqOn (fun s => Ring.inverse (f s)*g s)
      (fun _ => Ring.inverse (f c)*g c) (Ioo a b) := by
    intro s hs
    exact transition_constant hf hg (fun s hs => hu s ⟨hs.1.le,hs.2.le⟩) hs hc
  have hi : ContinuousOn (fun s => Ring.inverse (f s)) (Icc a b) := by
    intro s hs
    have hh := NormedRing.inverse_continuousAt (hu s hs).unit
    rw [(hu s hs).unit_spec] at hh
    exact hh.comp_continuousWithinAt (hfc s hs)
  have he' := he.of_subset_closure (hi.mul hgc) continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])
  exact (he' huv).trans (he' hvv).symm

variable [FiniteDimensional ℝ A]

theorem transport_eq_fundamental (F : NilpotentFiltration A) {Ω f : ℝ → A}
    (hΩ : ∀ s, Ω s ∈ F.space 1) {a b : ℝ} (hab : a < b)
    (hi : IntervalIntegrable Ω volume a b) (hc : ContinuousOn Ω (Ioo a b))
    (hf : ∀ s ∈ Ioo a b, HasDerivAt f (Ω s*f s) s)
    (hfc : ContinuousOn f (Icc a b)) (hu : ∀ s ∈ Icc a b, IsUnit (f s)) :
    transport Ω a F.cutoff b=f b*Ring.inverse (f a) := by
  have hcont := continuousOn_transport hi F.cutoff
  rw [uIcc_of_le hab.le] at hcont
  have h := transition_constant_closed hab hf
    (fun s hs => derivative_nilpotent_transport F hΩ hi hc hs)
    hfc hcont hu (right_mem_Icc.mpr hab.le) (left_mem_Icc.mpr hab.le)
  rw [transport_base,mul_one] at h
  calc
    transport Ω a F.cutoff b = f b*(Ring.inverse (f b)*transport Ω a F.cutoff b) := by
      rw [←mul_assoc,Ring.mul_inverse_cancel _ (hu b (right_mem_Icc.mpr hab.le)),one_mul]
    _ = f b*Ring.inverse (f a) := congrArg (f b*·) h

end FinitePicard

namespace KZCollar
open MeasureTheory Set Filter FinitePicard
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A]

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem bulkForm_mem (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) (s : ℝ) :
    bulkForm X Y s ∈ F.space 1 := (F.space 1).add_mem
      ((F.space 1).smul_mem _ hX) ((F.space 1).smul_mem _ hY)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem bulkForm_continuous (X Y : A) : ContinuousOn (bulkForm X Y) (Ioo 0 1) := by
  apply ContinuousOn.add
  · exact (continuousOn_id.inv₀ (fun s hs => ne_of_gt hs.1)).smul continuousOn_const
  · exact ((continuousOn_id.sub continuousOn_const).inv₀
      (fun s hs => ne_of_lt (sub_neg.mpr hs.2))).smul continuousOn_const

theorem bulk_transport (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) {r t : ℝ}
    (hr : 0 < r) (hrt : r < t) (ht : t < 1) :
    transport (bulkForm X Y) r F.cutoff t =
      normalizedSolution F X Y t * Ring.inverse (normalizedSolution F X Y r) := by
  have hs : Icc r t ⊆ Ioo (0:ℝ) 1 := fun s hs =>
    ⟨lt_of_lt_of_le hr hs.1,lt_of_le_of_lt hs.2 ht⟩
  have hc := (bulkForm_continuous X Y).mono hs
  apply transport_eq_fundamental F (bulkForm_mem F hX hY) hrt
  · exact hc.intervalIntegrable_of_Icc hrt.le
  · exact hc.mono Ioo_subset_Icc_self
  · exact fun s h => normalizedSolution_derivative_on F hX hY (hs ⟨h.1.le,h.2.le⟩)
  · exact fun s h => (normalizedSolution_derivative_on F hX hY (hs h)).continuousAt.continuousWithinAt
  · exact fun s _ => normalizedSolution_isUnit F hX hY s

end KZCollar
end

section

end

namespace RegularSingular
open MeasureTheory Set Filter FinitePicard KZCollar
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem regular_finite (X : A) (R : ℝ → A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    regular X R s=∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
      (Real.log s^(i+j)*((-1:ℝ)^i/((i.factorial:ℝ)*(j.factorial:ℝ)))) • (X^i*R s*X^j) := by
  have hnX : (-X)^(N+1)=0 := by rw [neg_pow,hX,mul_zero]
  unfold regular
  rw [gauge_finite (-X) hnX,gauge_finite X hX,Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [neg_pow]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
  have hp : (-1:A)^i*X^i*R s*X^j=(-1:ℝ)^i • (X^i*R s*X^j) := by
    simp only [Algebra.smul_def,map_pow,map_neg,map_one]
    noncomm_ring
  rw [hp,smul_smul]
  congr 1
  rw [pow_add]
  ring

theorem regular_integrable (X : A) {R : ℝ → A} {N : ℕ} (hX : X^(N+1)=0)
    {b : ℝ} (hb : 0≤b) (hR : ContinuousOn R (Icc 0 b)) :
    IntervalIntegrable (regular X R) volume 0 b := by
  have h : regular X R=fun s => ∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
      (Real.log s^(i+j)*((-1:ℝ)^i/((i.factorial:ℝ)*(j.factorial:ℝ)))) • (X^i*R s*X^j) :=
    funext (regular_finite X R hX)
  rw [h]
  have hi (i j : ℕ) : IntervalIntegrable (fun s =>
      (Real.log s^(i+j)*((-1:ℝ)^i/((i.factorial:ℝ)*(j.factorial:ℝ)))) • (X^i*R s*X^j)) volume 0 b :=
    ((LogCollar.log_pow (i+j) hb).mul_const _).smul_continuousOn
      (by rw [uIcc_of_le hb]; exact (continuousOn_const.mul hR).mul continuousOn_const)
  have hh := IntervalIntegrable.sum (ε:=A) (Finset.range (N+1))
    (fun i _ => IntervalIntegrable.sum (ε:=A) (Finset.range (N+1)) (fun j _ => hi i j))
  have he : (∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1), fun s =>
      (Real.log s^(i+j)*((-1:ℝ)^i/((i.factorial:ℝ)*(j.factorial:ℝ)))) • (X^i*R s*X^j)) =
      (fun s => ∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
      (Real.log s^(i+j)*((-1:ℝ)^i/((i.factorial:ℝ)*(j.factorial:ℝ)))) • (X^i*R s*X^j)) := by
    ext s
    simp only [Finset.sum_apply]
  rw [he] at hh
  exact hh

theorem regular_mem (F : NilpotentFiltration A) {X : A} (hX : X∈F.space 1)
    {R : ℝ → A} (hR : ∀ s,R s∈F.space 1) (s : ℝ) : regular X R s∈F.space 1 := by
  rw [regular_finite X R (pow_cutoff_eq_zero F hX)]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact F.antitone (by omega : 1 ≤ i+1+j)
    (F.mul_mem (i+1) j (F.mul_mem i 1 (pow_mem F hX i) (hR s)) (pow_mem F hX j))

def solution (F : NilpotentFiltration A) (X : A) (R : ℝ → A) (s : ℝ) : A :=
  gauge X s*transport (regular X R) 0 F.cutoff s

variable [CompleteSpace A]

theorem regular_continuous {X : A} {R : ℝ → A} {b : ℝ}
    (hR : ContinuousOn R (Icc 0 b)) : ContinuousOn (regular X R) (Ioo 0 b) := by
  intro s hs
  have hg (X : A) : ContinuousAt (gauge X) s := (gauge_derivative X (ne_of_gt hs.1)).continuousAt
  exact (((hg (-X)).continuousWithinAt.mul ((hR.mono Ioo_subset_Icc_self) s hs)).mul
    (hg X).continuousWithinAt)

variable [FiniteDimensional ℝ A]

theorem solution_derivative (F : NilpotentFiltration A) {X : A} (hX : X∈F.space 1)
    {R : ℝ → A} (hRm : ∀ s,R s∈F.space 1) {b s : ℝ}
    (hR : ContinuousOn R (Icc 0 b)) (hs : s∈Ioo 0 b) :
    HasDerivAt (solution F X R) ((s⁻¹ • X+R s)*solution F X R s) s := by
  have hi := regular_integrable X (pow_cutoff_eq_zero F hX) (hs.1.le.trans hs.2.le) hR
  have hh := derivative_nilpotent_transport F (regular_mem F hX hRm) hi (regular_continuous hR) hs
  apply ((gauge_derivative X (ne_of_gt hs.1)).mul hh).congr_deriv
  let P := transport (regular X R) 0 F.cutoff s
  change (s⁻¹ • (X*gauge X s))*P+gauge X s*((gauge (-X) s*R s*gauge X s)*P)=
    (s⁻¹ • X+R s)*(gauge X s*P)
  rw [←mul_assoc (gauge X s),←mul_assoc (gauge X s),←mul_assoc (gauge X s),gauge_mul_neg,one_mul]
  simp only [add_mul,smul_mul_assoc,mul_assoc]

theorem solution_isUnit (F : NilpotentFiltration A) {X : A} (hX : X∈F.space 1)
    {R : ℝ → A} (hR : ∀ s,R s∈F.space 1) (s : ℝ) : IsUnit (solution F X R s) := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  exact (NormedSpace.isUnit_exp _).mul (transport_isUnit F (regular_mem F hX hR) 0 s F.cutoff)

end RegularSingular

namespace FinitePicard
open MeasureTheory Set intervalIntegral
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def integralNorm (Ω : ℝ → A) (a b : ℝ) : ℝ := ∫ s in a..b,‖Ω s‖

omit [NormedAlgebra ℝ A] in
theorem integralNorm_nonneg (Ω : ℝ → A) {a b : ℝ} (hab : a≤b) :
    0 ≤ integralNorm Ω a b := integral_nonneg hab (fun _ _ => norm_nonneg _)

theorem norm_term_le {Ω : ℝ → A} {a b L : ℝ} (hab : a≤b)
    (hi : IntervalIntegrable Ω volume a b) (hL : 0≤L)
    (hbound : ∀ t∈Icc a b,integralNorm Ω a t≤L) (n : ℕ) :
    ∀ t∈Icc a b,‖term Ω a n t‖≤‖(1:A)‖*L^n := by
  induction n with
  | zero => intro t ht; simp only [term_zero,pow_zero,mul_one,le_refl]
  | succ n ih =>
    intro t ht
    have his : IntervalIntegrable Ω volume a t := hi.mono_set (by simpa only [uIcc_of_le hab,uIcc_of_le ht.1] using Icc_subset_Icc_right ht.2)
    have hcont := continuousOn_term hi n
    have hm : IntervalIntegrable (fun s => Ω s*term Ω a n s) volume a t :=
      (hi.mul_continuousOn hcont).mono_set (by simpa only [uIcc_of_le hab,uIcc_of_le ht.1] using Icc_subset_Icc_right ht.2)
    calc
      ‖term Ω a (n+1) t‖ ≤ ∫ s in a..t,‖Ω s*term Ω a n s‖ := norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in a..t,‖Ω s‖*(‖(1:A)‖*L^n) := by
        apply integral_mono_on ht.1 hm.norm (his.norm.mul_const _)
        intro s hs
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (ih s ⟨hs.1,hs.2.trans ht.2⟩) (norm_nonneg _))
      _ = integralNorm Ω a t*(‖(1:A)‖*L^n) := integral_mul_const _ _
      _ ≤ L*(‖(1:A)‖*L^n) := mul_le_mul_of_nonneg_right (hbound t ht) (mul_nonneg (norm_nonneg _) (pow_nonneg hL _))
      _ = ‖(1:A)‖*L^(n+1) := by rw [pow_succ]; ring

omit [NormedAlgebra ℝ A] in
theorem integrable_partial {Ω : ℝ → A} {a b t : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (ht : t∈Icc a b) :
    IntervalIntegrable Ω volume a t :=
  hi.mono_set (by simpa only [uIcc_of_le ht.1,uIcc_of_le (ht.1.trans ht.2)]
    using Icc_subset_Icc_right ht.2)

omit [NormedAlgebra ℝ A] in
theorem integralNorm_partial {Ω : ℝ → A} {a b t : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (ht : t∈Icc a b) :
    integralNorm Ω a t≤ integralNorm Ω a b :=
  integral_mono_interval le_rfl ht.1 ht.2 (Filter.Eventually.of_forall (fun s => norm_nonneg (Ω s))) hi.norm

theorem norm_term_bound {Ω : ℝ → A} {a b : ℝ} (hi : IntervalIntegrable Ω volume a b)
    (n : ℕ) {t : ℝ} (ht : t∈Icc a b) :
    ‖term Ω a n t‖≤‖(1:A)‖*(integralNorm Ω a b)^n :=
  norm_term_le (ht.1.trans ht.2) hi (integralNorm_nonneg Ω (ht.1.trans ht.2))
    (fun _ hs => integralNorm_partial hi hs) n t ht

theorem norm_term_sub_le {Ω Θ : ℝ → A} {a b L E : ℝ} (hab : a≤b)
    (hΩ : IntervalIntegrable Ω volume a b) (hΘ : IntervalIntegrable Θ volume a b)
    (hL : 0≤L) (hE : 0≤E)
    (hΩL : integralNorm Ω a b≤L) (hΘL : integralNorm Θ a b≤L)
    (hEL : integralNorm (fun s => Ω s-Θ s) a b≤E) (n : ℕ) :
    ∀ t∈Icc a b,‖term Ω a n t-term Θ a n t‖≤(‖(1:A)‖*E)*(n:ℝ)*(L+1)^n := by
  have hM : 0≤L+1 := by positivity
  have hML : L≤L+1 := by linarith
  have cΩ := norm_term_le hab hΩ hM (fun t ht => (integralNorm_partial hΩ ht).trans (hΩL.trans hML))
  induction n with
  | zero => intro t ht; simp
  | succ n ih =>
    intro t ht
    have hiΩ := integrable_partial (hΩ.mul_continuousOn (continuousOn_term hΩ n)) ht
    have hiΘ := integrable_partial (hΘ.mul_continuousOn (continuousOn_term hΘ n)) ht
    have hsΩ := integrable_partial hΩ ht
    have hsΘ := integrable_partial hΘ ht
    have hd := integralNorm_partial (hΩ.sub hΘ) ht
    have hbΘ := (integralNorm_partial hΘ ht).trans hΘL
    have hp : 0≤(L+1)^n := pow_nonneg hM n
    have hC : 0≤‖(1:A)‖ := norm_nonneg _
    calc
      ‖term Ω a (n+1) t-term Θ a (n+1) t‖ =
        ‖∫ s in a..t,Ω s*term Ω a n s-Θ s*term Θ a n s‖ := by rw [integral_sub hiΩ hiΘ]; rfl
      _ ≤ ∫ s in a..t,‖Ω s*term Ω a n s-Θ s*term Θ a n s‖ := norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in a..t,‖Ω s-Θ s‖*(‖(1:A)‖*(L+1)^n)+‖Θ s‖*((‖(1:A)‖*E)*(n:ℝ)*(L+1)^n) := by
        apply integral_mono_on ht.1 (hiΩ.sub hiΘ).norm
          (((hsΩ.sub hsΘ).norm.mul_const _).add (hsΘ.norm.mul_const _))
        intro s hs
        have hs' : s∈Icc a b := ⟨hs.1,hs.2.trans ht.2⟩
        calc
          _ = ‖(Ω s-Θ s)*term Ω a n s+Θ s*(term Ω a n s-term Θ a n s)‖ := by congr 1; noncomm_ring
          _ ≤ ‖(Ω s-Θ s)*term Ω a n s‖+‖Θ s*(term Ω a n s-term Θ a n s)‖ := norm_add_le _ _
          _ ≤ ‖Ω s-Θ s‖*‖term Ω a n s‖+‖Θ s‖*‖term Ω a n s-term Θ a n s‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
          _ ≤ _ := add_le_add
            (mul_le_mul_of_nonneg_left (cΩ n s hs') (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (ih s hs') (norm_nonneg _))
      _ = integralNorm (fun s => Ω s-Θ s) a t*(‖(1:A)‖*(L+1)^n)+
          integralNorm Θ a t*((‖(1:A)‖*E)*(n:ℝ)*(L+1)^n) := by
        rw [integral_add ((hsΩ.sub hsΘ).norm.mul_const _) (hsΘ.norm.mul_const _),intervalIntegral.integral_mul_const,intervalIntegral.integral_mul_const]; rfl
      _ ≤ E*(‖(1:A)‖*(L+1)^n)+L*((‖(1:A)‖*E)*(n:ℝ)*(L+1)^n) :=
        add_le_add (mul_le_mul_of_nonneg_right (hd.trans hEL) (mul_nonneg hC hp))
          (mul_le_mul_of_nonneg_right hbΘ (by positivity))
      _ = (‖(1:A)‖*E*(L+1)^n)*(1+L*(n:ℝ)) := by ring
      _ ≤ (‖(1:A)‖*E*(L+1)^n)*(((n:ℝ)+1)*(L+1)) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
        nlinarith
      _ = (‖(1:A)‖*E)*((n+1:ℕ):ℝ)*(L+1)^(n+1) := by rw [Nat.cast_add,Nat.cast_one,pow_succ]; ring

def transportPoly (N : ℕ) (u : ℝ) : ℝ := ∑ n∈Finset.range (N+1),u^n

def errorPoly (N : ℕ) (u : ℝ) : ℝ := ∑ n∈Finset.range (N+1),(n:ℝ)*u^n

theorem norm_transport_le {Ω : ℝ → A} {a b L : ℝ} (hab : a≤b)
    (hΩ : IntervalIntegrable Ω volume a b) (hL : 0≤L)
    (hb : integralNorm Ω a b≤L) (N : ℕ) :
    ‖transport Ω a N b‖≤‖(1:A)‖*transportPoly N L := by
  calc
    _ ≤ ∑ n∈Finset.range (N+1),‖term Ω a n b‖ := norm_sum_le _ _
    _ ≤ ∑ n∈Finset.range (N+1),‖(1:A)‖*L^n :=
      Finset.sum_le_sum (fun n _ => norm_term_le hab hΩ hL
        (fun _ ht => (integralNorm_partial hΩ ht).trans hb) n b ⟨hab,le_rfl⟩)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem norm_transport_sub_le {Ω Θ : ℝ → A} {a b L E : ℝ} (hab : a≤b)
    (hΩ : IntervalIntegrable Ω volume a b) (hΘ : IntervalIntegrable Θ volume a b)
    (hL : 0≤L) (hE : 0≤E)
    (hΩL : integralNorm Ω a b≤L) (hΘL : integralNorm Θ a b≤L)
    (hEL : integralNorm (fun s => Ω s-Θ s) a b≤E) (N : ℕ) :
    ‖transport Ω a N b-transport Θ a N b‖≤(‖(1:A)‖*E)*errorPoly N (L+1) := by
  unfold transport
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n∈Finset.range (N+1),‖term Ω a n b-term Θ a n b‖ := norm_sum_le _ _
    _ ≤ ∑ n∈Finset.range (N+1),(‖(1:A)‖*E)*(n:ℝ)*(L+1)^n :=
      Finset.sum_le_sum (fun n _ => norm_term_sub_le hab hΩ hΘ hL hE hΩL hΘL hEL n b ⟨hab,le_rfl⟩)
    _ = _ := by simp only [errorPoly,Finset.mul_sum,mul_assoc]

end FinitePicard

namespace PowerAsymptotic

section
open MeasureTheory Set Filter Asymptotics FinitePicard KZCollar RegularSingular
open scoped Topology

def PowerSmall {E : Type*} [Norm E] (f : ℝ → E) : Prop :=
  ∃ p : ℝ,0<p ∧ f =O[𝓝[>] 0] (fun s : ℝ => s^p)

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

lemma rpow_mul_eventually (p q : ℝ) :
    (fun s : ℝ => s^p*s^q) =ᶠ[𝓝[>] 0] (fun s : ℝ => s^(p+q)) := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (Real.rpow_add (show 0<s from hs) p q).symm

theorem log_pow_subpower (n : ℕ) : Subpower (fun s : ℝ => Real.log s^n) := by
  intro p hp
  have h := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (n:ℝ) (neg_lt_zero.mpr hp)).isBigO
  apply IsBigO.of_norm_left
  simpa only [Real.rpow_natCast,Real.norm_eq_abs,norm_pow] using h

omit [NormedAlgebra ℝ A] in
theorem Subpower.add {f g : ℝ → A} (hf : Subpower f) (hg : Subpower g) :
    Subpower (fun s => f s+g s) := fun p hp => (hf p hp).add (hg p hp)

omit [NormedAlgebra ℝ A] in
theorem Subpower.mul {f g : ℝ → A} (hf : Subpower f) (hg : Subpower g) :
    Subpower (fun s => f s*g s) := by
  intro p hp
  have h := (hf (p/2) (by linarith)).mul (hg (p/2) (by linarith))
  apply h.congr' .rfl
  filter_upwards [rpow_mul_eventually (-(p/2)) (-(p/2))] with s hs
  convert! hs using 1
  congr 1
  ring

theorem const_subpower (a : A) : Subpower (fun _ : ℝ => a) := by
  intro p hp
  have h := (log_pow_subpower 0 p hp)
  have h' := h.smul (isBigO_const_const a (one_ne_zero : (1:ℝ)≠0) (𝓝[>] (0:ℝ)))
  simpa only [pow_zero,one_smul,smul_eq_mul,mul_one] using h'

omit [NormedAlgebra ℝ A] in
theorem continuousAt_subpower {f : ℝ → A} (hf : ContinuousAt f 0) : Subpower f := by
  intro p hp
  exact (isBigO_const_of_tendsto hf (one_ne_zero : (1:ℝ)≠0)).mono inf_le_left |>.trans
    (by simpa only [pow_zero] using! log_pow_subpower 0 p hp)

theorem gauge_subpower {X : A} {N : ℕ} (hX : X^(N+1)=0) : Subpower (gauge X) := by
  intro p hp
  have h (i : ℕ) : (fun s : ℝ => (Real.log s^i / (i.factorial:ℝ)) • X^i)
      =O[𝓝[>] 0] (fun s : ℝ => s^(-p)) := by
    have hr := (log_pow_subpower i p hp).smul
      (isBigO_const_const (((i.factorial:ℝ)⁻¹) • X^i) (one_ne_zero : (1:ℝ)≠0) (𝓝[>] (0:ℝ)))
    simpa only [smul_smul,smul_eq_mul,mul_one,div_eq_mul_inv] using hr
  have hh := IsBigO.sum (s:=Finset.range (N+1)) (fun i _ => h i)
  apply hh.congr_left
  intro s
  simp only [Finset.sum_apply]
  exact (gauge_finite X hX s).symm

omit [NormedAlgebra ℝ A] in
theorem PowerSmall.mul_subpower {f g : ℝ → A} (hf : PowerSmall f) (hg : Subpower g) :
    PowerSmall (fun s => f s*g s) := by
  obtain ⟨p,hp,hf⟩ := hf
  refine ⟨p/2,by linarith,?_⟩
  apply (hf.mul (hg (p/2) (by linarith))).congr' .rfl
  filter_upwards [rpow_mul_eventually p (-(p/2))] with s hs
  convert! hs using 1
  congr 1
  ring

omit [NormedAlgebra ℝ A] in
omit [NormedAlgebra ℝ A] in
theorem Subpower.mul_powerSmall {f g : ℝ → A} (hf : Subpower f) (hg : PowerSmall g) :
    PowerSmall (fun s => f s*g s) := by
  obtain ⟨p,hp,hg⟩ := hg
  refine ⟨p/2,by linarith,?_⟩
  apply ((hf (p/2) (by linarith)).mul hg).congr' .rfl
  filter_upwards [rpow_mul_eventually (-(p/2)) p] with s hs
  convert! hs using 1
  congr 1
  ring

omit [NormedAlgebra ℝ A] in
theorem PowerSmall.tendsto_zero {f : ℝ → A} (hf : PowerSmall f) :
    Tendsto f (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨p,hp,hf⟩ := hf
  apply hf.trans_tendsto
  simpa only [Real.zero_rpow (ne_of_gt hp)] using!
    (Real.continuousAt_rpow_const (x:=(0:ℝ)) p (Or.inr hp.le)).tendsto.mono_left inf_le_left

omit [NormedAlgebra ℝ A] in

theorem integralNorm_isBigO {Ω : ℝ → A} {b r : ℝ} (hb : 0<b) (hr : -1<r)
    (hi : IntervalIntegrable Ω volume 0 b)
    (ho : Ω =O[𝓝[>] 0] (fun s : ℝ => s^r)) :
    (fun s => integralNorm Ω 0 s) =O[𝓝[>] 0] (fun s : ℝ => s^(r+1)) := by
  obtain ⟨C,hC,hbound⟩ := ho.exists_nonneg
  obtain ⟨c,hc,hcb⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hbound.bound
  let d := min b c
  have hd : 0<d := lt_min hb hc
  apply isBigO_iff.mpr
  refine ⟨C/(r+1),?_⟩
  filter_upwards [Ioc_mem_nhdsGT hd] with s hs
  have hs0 : 0 ≤ s := hs.1.le
  have hsb : s ≤ b := hs.2.trans (min_le_left _ _)
  have his := integrable_partial hi ⟨hs0,hsb⟩
  have hir : IntervalIntegrable (fun t : ℝ => C*t^r) volume 0 s :=
    (intervalIntegral.intervalIntegrable_rpow' hr).const_mul C
  have hbnd : integralNorm Ω 0 s ≤ C/(r+1)*s^(r+1) := by
    calc
      _ ≤ ∫ t in 0..s,C*t^r := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hs0 his.norm hir
        intro t ht
        have ht0 : 0<t := ht.1
        have hh := hcb (show t∈Ioc 0 c from ⟨ht0,ht.2.le.trans (hs.2.trans (min_le_right _ _))⟩)
        simpa only [Set.mem_ofPred_eq,Real.norm_of_nonneg (Real.rpow_nonneg ht0.le r)] using hh
      _ = C/(r+1)*s^(r+1) := by
        rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl hr),
          Real.zero_rpow (by linarith : r+1≠0),sub_zero]
        ring
  simpa only [Real.norm_of_nonneg (integralNorm_nonneg Ω hs0),
    Real.norm_of_nonneg (Real.rpow_nonneg hs0 (r+1))] using hbnd

theorem transport_sub_one_isBigO_integralNorm {Ω : ℝ → A} {b : ℝ} (hb : 0 < b)
    (hi : IntervalIntegrable Ω volume 0 b) (N : ℕ) :
    (fun s => transport Ω 0 N s-1) =O[𝓝[>] 0] (fun s => integralNorm Ω 0 s) := by
  let L := integralNorm Ω 0 b
  let C := ∑ n∈Finset.range N,‖(1:A)‖*L^n
  apply isBigO_iff.mpr
  refine ⟨C,?_⟩
  filter_upwards [Ioc_mem_nhdsGT hb] with s hs
  have hs' : s∈Icc 0 b := ⟨hs.1.le,hs.2⟩
  have his := integrable_partial hi hs'
  have hn (n : ℕ) : ‖term Ω 0 (n+1) s‖ ≤ integralNorm Ω 0 s*(‖(1:A)‖*L^n) := by
    have hit := integrable_partial (hi.mul_continuousOn (continuousOn_term hi n)) hs'
    calc
      _ ≤ ∫ t in 0..s,‖Ω t*term Ω 0 n t‖ := intervalIntegral.norm_integral_le_integral_norm hs.1.le
      _ ≤ ∫ t in 0..s,‖Ω t‖*(‖(1:A)‖*L^n) := by
        apply intervalIntegral.integral_mono_on hs.1.le hit.norm (his.norm.mul_const _)
        intro t ht
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
          (norm_term_bound hi n ⟨ht.1,ht.2.trans hs.2⟩) (norm_nonneg _))
      _ = _ := intervalIntegral.integral_mul_const _ _
  have he : transport Ω 0 N s-1=∑ n∈Finset.range N,term Ω 0 (n+1) s := by
    simp only [transport,Finset.sum_range_succ',term_zero,add_sub_cancel_right]
  rw [he,Real.norm_of_nonneg (integralNorm_nonneg Ω hs.1.le)]
  calc
    _ ≤ ∑ n∈Finset.range N,‖term Ω 0 (n+1) s‖ := norm_sum_le _ _
    _ ≤ ∑ n∈Finset.range N,integralNorm Ω 0 s*(‖(1:A)‖*L^n) :=
      Finset.sum_le_sum (fun n _ => hn n)
    _ = C*integralNorm Ω 0 s := by rw [←Finset.mul_sum]; exact mul_comm _ _

theorem transport_sub_one_powerSmall {Ω : ℝ → A} {b : ℝ} (hb : 0 < b)
    (hi : IntervalIntegrable Ω volume 0 b) (ho : Subpower Ω) (N : ℕ) :
    PowerSmall (fun s => transport Ω 0 N s-1) := by
  refine ⟨1/2,by norm_num,?_⟩
  have h := (transport_sub_one_isBigO_integralNorm hb hi N).trans
    (integralNorm_isBigO hb (by norm_num : -1 < -(1/2:ℝ)) hi (ho (1/2) (by norm_num)))
  convert! h using 1
  norm_num

end

open MeasureTheory Set Filter Asymptotics FinitePicard KZCollar RegularSingular
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
theorem tendsto_subpower {f : ℝ → A} {a : A} (hf : Tendsto f (𝓝[>] 0) (𝓝 a)) : Subpower f := by
  intro p hp
  exact (isBigO_const_of_tendsto hf (one_ne_zero : (1:ℝ)≠0)).trans
    (by simpa only [pow_zero] using! log_pow_subpower 0 p hp)

omit [NormedAlgebra ℝ A] in
theorem continuousOn_subpower {R : ℝ → A} {b : ℝ} (hb : 0 < b)
    (hR : ContinuousOn R (Icc 0 b)) : Subpower R := by
  have h := hR 0 (left_mem_Icc.mpr hb.le)
  rw [ContinuousWithinAt,nhdsWithin_Icc_eq_nhdsGE hb] at h
  exact tendsto_subpower (h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self))

omit [NormedAlgebra ℝ A] in
theorem PowerSmall.congr {f g : ℝ → A} (hf : PowerSmall f) (hh : ∀ s,f s=g s) :
    PowerSmall g := by
  obtain ⟨p,hp,hf⟩ := hf
  exact ⟨p,hp,hf.congr_left hh⟩

theorem regular_subpower {X : A} {N : ℕ} (hX : X^(N+1)=0)
    {R : ℝ → A} (hR : Subpower R) : Subpower (regular X R) :=
  ((gauge_subpower (by rw [neg_pow,hX,mul_zero] : (-X)^(N+1)=0)).mul hR).mul (gauge_subpower hX)

theorem solution_sub_gauge {X : A} (F : NilpotentFiltration A) (hX : X∈F.space 1)
    {R : ℝ → A} {b : ℝ} (hb : 0 < b) (hR : ContinuousOn R (Icc 0 b)) :
    PowerSmall (fun s => solution F X R s-gauge X s) := by
  have h := transport_sub_one_powerSmall hb (regular_integrable X (pow_cutoff_eq_zero F hX) hb.le hR)
    (regular_subpower (pow_cutoff_eq_zero F hX) (continuousOn_subpower hb hR)) F.cutoff
  apply ((gauge_subpower (pow_cutoff_eq_zero F hX)).mul_powerSmall h).congr
  intro s
  simp only [solution,mul_sub,mul_one]

theorem Subpower.pow {f : ℝ → A} (hf : Subpower f) (n : ℕ) : Subpower (fun s => f s^n) := by
  induction n with
  | zero => simpa only [pow_zero] using const_subpower (1:A)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

omit [NormedAlgebra ℝ A] in
theorem Subpower.sum {ι : Type*} (S : Finset ι) {f : ι → ℝ → A}
    (hf : ∀ i∈S,Subpower (f i)) : Subpower (fun s => ∑ i∈S,f i s) := by
  intro p hp
  have h := IsBigO.sum (fun i hi => hf i hi p hp)
  apply h.congr_left
  intro s
  simp only [Finset.sum_apply]

theorem errorPoly_subpower {L : ℝ → ℝ} (hL : Subpower L) (N : ℕ) :
    Subpower (fun s => errorPoly N (L s+1)) := by
  apply Subpower.sum
  intro n hn
  exact (const_subpower (n:ℝ)).mul ((hL.add (const_subpower 1)).pow n)

variable [CompleteSpace A]

omit [NormedAlgebra ℝ A] in
theorem inverse_tendsto_one {f : ℝ → A} (hf : Tendsto f (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun s => Ring.inverse (f s)) (𝓝[>] 0) (𝓝 1) := by
  simpa only [Units.val_one,Ring.inverse_one] using! (NormedRing.inverse_continuousAt (1:Aˣ)).tendsto.comp hf

omit [NormedAlgebra ℝ A] in
theorem inverse_sub_one_powerSmall {f : ℝ → A} (hu : ∀ s,IsUnit (f s))
    (hf : PowerSmall (fun s => f s-1)) : PowerSmall (fun s => Ring.inverse (f s)-1) := by
  have ht : Tendsto f (𝓝[>] 0) (𝓝 1) := by
    simpa only [zero_add,sub_add_cancel] using! hf.tendsto_zero.add_const (1:A)
  have hi := tendsto_subpower (inverse_tendsto_one ht)
  have h := hi.mul_powerSmall hf
  obtain ⟨p,hp,h⟩ := h
  refine ⟨p,hp,?_⟩
  apply h.neg_left.congr_left
  intro s
  rw [mul_sub,mul_one,Ring.inverse_mul_cancel _ (hu s),neg_sub]

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem inverse_mul_of_units {a b : A} (ha : IsUnit a) (hb : IsUnit b) :
    Ring.inverse (a*b)=Ring.inverse b*Ring.inverse a := by
  obtain ⟨u,rfl⟩ := ha
  obtain ⟨v,rfl⟩ := hb
  rw [←Units.val_mul,Ring.inverse_unit,Ring.inverse_unit,Ring.inverse_unit,mul_inv_rev]
  rfl

theorem inverse_gauge (X : A) (s : ℝ) : Ring.inverse (gauge X s)=gauge (-X) s := by
  have hu : IsUnit (gauge X s) := by
    let := NormedAlgebra.restrictScalars ℚ ℝ A
    exact NormedSpace.isUnit_exp _
  calc
    _ = Ring.inverse (gauge X s)*(gauge X s*gauge (-X) s) := by rw [gauge_mul_neg,mul_one]
    _ = gauge (-X) s := by rw [←mul_assoc,Ring.inverse_mul_cancel _ hu,one_mul]

variable [FiniteDimensional ℝ A]

theorem inverse_solution_sub_gauge {X : A} (F : NilpotentFiltration A) (hX : X∈F.space 1)
    {R : ℝ → A} (hRm : ∀ s,R s∈F.space 1) {b : ℝ} (hb : 0 < b)
    (hR : ContinuousOn R (Icc 0 b)) :
    PowerSmall (fun s => Ring.inverse (solution F X R s)-gauge (-X) s) := by
  have hnil := pow_cutoff_eq_zero F hX
  have hh := transport_sub_one_powerSmall hb (regular_integrable X hnil hb.le hR)
    (regular_subpower hnil (continuousOn_subpower hb hR)) F.cutoff
  have hu (s : ℝ) := transport_isUnit F (regular_mem F hX hRm) 0 s F.cutoff
  have hi := inverse_sub_one_powerSmall hu hh
  apply (hi.mul_subpower (gauge_subpower (by rw [neg_pow,hnil,mul_zero] : (-X)^(F.cutoff+1)=0))).congr
  intro s
  have hg : IsUnit (gauge X s) := by
    let := NormedAlgebra.restrictScalars ℚ ℝ A
    exact NormedSpace.isUnit_exp _
  rw [solution,inverse_mul_of_units hg (hu s),inverse_gauge,sub_mul,one_mul]

end PowerAsymptotic

namespace KZCollar
open Set Filter PowerAsymptotic Asymptotics
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem linear_powerSmall (c : ℝ) : PowerSmall (fun s : ℝ => c*s) := by
  refine ⟨1,by norm_num,IsBigO.of_bound |c| ?_⟩
  filter_upwards [] with s
  simp only [Real.rpow_one,Real.norm_eq_abs,abs_mul,le_refl]

variable [CompleteSpace A]

theorem gauge_mul_scale (X : A) {r s : ℝ} (hr : r≠0) (hs : s≠0) :
    gauge X (r*s)=gauge X r*gauge X s := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  unfold gauge
  rw [Real.log_mul hr hs,add_smul,NormedSpace.exp_add_of_commute]
  exact (Commute.refl X).smul_left _ |>.smul_right _

theorem gauge_add_of_commute {X Y : A} (h : Commute X Y) (s : ℝ) :
    gauge (X+Y) s=gauge X s*gauge Y s := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  unfold gauge
  rw [smul_add,NormedSpace.exp_add_of_commute ((h.smul_left _).smul_right _)]

theorem gauge_continuousAt {X : A} {s : ℝ} (hs : s≠0) : ContinuousAt (gauge X) s :=
  (gauge_derivative X hs).continuousAt

theorem gauge_ratio_limit (X : A) :
    Tendsto (fun s : ℝ => gauge X (1+s)) (𝓝[>] 0) (𝓝 (1:A)) := by
  have ht : Tendsto (fun s : ℝ => 1+s) (𝓝[>] 0) (𝓝 1) := by
    simpa only [add_zero] using! (tendsto_const_nhds (x:=(1:ℝ))).add
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0))
  simpa only [gauge_one] using! (gauge_continuousAt (X:=X) (by norm_num : (1:ℝ)≠0)).tendsto.comp ht

end KZCollar

namespace FinitePicard

section
open MeasureTheory Set KZCollar
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def centralizer (Z : A) : Submodule ℝ A where
  carrier := {a | Commute Z a}
  zero_mem' := Commute.zero_right Z
  add_mem' := fun h h' => h.add_right h'
  smul_mem' := fun r _ h => h.smul_right r

variable [FiniteDimensional ℝ A]

theorem term_commute (Z : A) {Ω : ℝ → A} (hΩ : ∀ t,Commute Z (Ω t)) (a : ℝ) (n : ℕ) (t : ℝ) :
    Commute Z (term Ω a n t) := by
  induction n generalizing t with
  | zero => exact Commute.one_right Z
  | succ n ih =>
    exact integral_mem_submodule (centralizer Z) (fun s => Ω s*term Ω a n s) a t
      (fun s => (hΩ s).mul_right (ih s))

theorem transport_commute (Z : A) {Ω : ℝ → A} (hΩ : ∀ t,Commute Z (Ω t)) (a : ℝ) (N : ℕ) (t : ℝ) :
    Commute Z (transport Ω a N t) :=
  Commute.sum_right (Finset.range (N+1)) _ Z (fun n _ => term_commute Z hΩ a n t)

omit [FiniteDimensional ℝ A] in
theorem gauge_commute {X Z : A} {N : ℕ} (hX : X^(N+1)=0) (h : Commute Z X) (s : ℝ) :
    Commute Z (gauge X s) := by
  rw [gauge_finite X hX]
  exact Commute.sum_right _ _ Z (fun n _ => (h.pow_right n).smul_right _)

end

open MeasureTheory Set
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

end FinitePicard

end DeligneDrinfeld

end

end OAI

end



section

namespace OAI

noncomputable section

namespace DeligneDrinfeld.KZCollar
open FinitePicard
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem associator_swap (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    associator F Y X=Ring.inverse (associator F X Y) := by
  unfold associator rightSolution
  norm_num only [show (1:ℝ)-1/2=1/2 by norm_num]
  rw [Ring.inverse_mul (Or.inr (normalizedSolution_isUnit F hX hY (1/2))),
    Ring.inverse_inverse (normalizedSolution_isUnit F hY hX (1/2))]

end DeligneDrinfeld.KZCollar

namespace DeligneDrinfeld
namespace FinitePicard

section
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem parameter_integral_derivative {f f' : ℝ → ℝ → E} (hf : Continuous f.uncurry)
    (hf' : Continuous f'.uncurry) {c d x a b : ℝ} (hx : x ∈ Ioo c d)
    (hd : ∀ s ∈ Ioo c d, ∀ t ∈ uIcc a b, HasDerivAt (fun s => f s t) (f' s t) s) :
    HasDerivAt (fun s => ∫ t in a..b, f s t) (∫ t in a..b, f' x t) x := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod (isCompact_uIcc (a:=a) (b:=b))).exists_bound_of_continuousOn
    (hf'.continuousOn : ContinuousOn f'.uncurry (Icc c d ×ˢ uIcc a b))
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=Ioo c d) (bound:=fun _ => C) (Ioo_mem_nhds hx.1 hx.2) _ _ _ _
    (intervalIntegrable_const) _).2
  · exact Eventually.of_forall (fun s => (hf.uncurry_left s).aestronglyMeasurable)
  · exact (hf.uncurry_left x).intervalIntegrable a b
  · exact (hf'.uncurry_left x).aestronglyMeasurable
  · exact ae_of_all _ (fun t ht s hs => hC (s,t) ⟨⟨hs.1.le,hs.2.le⟩,uIoc_subset_uIcc ht⟩)
  · exact ae_of_all _ (fun t ht s hs => hd s hs t (uIoc_subset_uIcc ht))

end

section
open MeasureTheory Set
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def dterm (Ω Ωs : ℝ → ℝ → A) (a : ℝ) : ℕ → ℝ → ℝ → A
  | 0 => fun _ _ => 0
  | n+1 => fun s t => ∫ u in a..t, Ωs s u * term (Ω s) a n u + Ω s u * dterm Ω Ωs a n s u

@[simp] theorem dterm_zero (Ω Ωs : ℝ → ℝ → A) (a s t : ℝ) : dterm Ω Ωs a 0 s t=0 := rfl
@[simp] theorem dterm_base (Ω Ωs : ℝ → ℝ → A) (a s : ℝ) (n : ℕ) : dterm Ω Ωs a n s a=0 := by
  cases n <;> simp [dterm]

theorem continuous_term_parameter {Ω : ℝ → ℝ → A} (hΩ : Continuous Ω.uncurry) (a : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => term (Ω p.1) a n p.2) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact intervalIntegral.continuous_parametric_primitive_of_continuous
      (f:=fun s t => Ω s t * term (Ω s) a n t) (hΩ.mul ih)

theorem continuous_dterm {Ω Ωs : ℝ → ℝ → A} (hΩ : Continuous Ω.uncurry)
    (hΩs : Continuous Ωs.uncurry) (a : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => dterm Ω Ωs a n p.1 p.2) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact intervalIntegral.continuous_parametric_primitive_of_continuous
      (f:=fun s t => Ωs s t * term (Ω s) a n t + Ω s t * dterm Ω Ωs a n s t)
      ((hΩs.mul (continuous_term_parameter hΩ a n)).add (hΩ.mul ih))

theorem derivative_term_parameter {Ω Ωs : ℝ → ℝ → A} (hΩ : Continuous Ω.uncurry)
    (hΩs : Continuous Ωs.uncurry) {a b c d : ℝ}
    (hd : ∀ s ∈ Ioo c d, ∀ t ∈ uIcc a b, HasDerivAt (fun s => Ω s t) (Ωs s t) s)
    (n : ℕ) : ∀ s ∈ Ioo c d, ∀ t ∈ uIcc a b,
      HasDerivAt (fun s => term (Ω s) a n t) (dterm Ω Ωs a n s t) s := by
  induction n with
  | zero => exact fun s _ t _ => hasDerivAt_const s 1
  | succ n ih =>
    intro s hs t ht
    apply parameter_integral_derivative
      (f:=fun s u => Ω s u *term (Ω s) a n u)
      (f':=fun s u => Ωs s u *term (Ω s) a n u + Ω s u * dterm Ω Ωs a n s u)
      (hΩ.mul (continuous_term_parameter hΩ a n))
      ((hΩs.mul (continuous_term_parameter hΩ a n)).add (hΩ.mul (continuous_dterm hΩ hΩs a n))) hs
    intro v hv u hu
    have hu' := uIcc_subset_uIcc_left ht hu
    exact (hd v hv u hu').mul (ih v hv u hu')

end

open MeasureTheory Set
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem dterm_flat_formula {Ω Ωs B : ℝ → ℝ → A}
    (hΩ : Continuous Ω.uncurry) (hΩs : Continuous Ωs.uncurry)
    {a b s : ℝ}
    (hB : ∀ t ∈ uIcc a b, HasDerivAt (B s) (Ωs s t) t)
    (hcomm : ∀ t ∈ uIcc a b, Commute (Ω s t) (B s t))
    (n : ℕ) : ∀ t ∈ uIcc a b,
      dterm Ω Ωs a (n+1) s t =
        B s t * term (Ω s) a n t - term (Ω s) a n t * B s a := by
  induction n with
  | zero =>
    intro t ht
    simp only [dterm,term_zero,mul_one,mul_zero,add_zero,one_mul]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hB u (uIcc_subset_uIcc_left ht hu))
      ((hΩs.uncurry_left s).intervalIntegrable a t)
  | succ n ih =>
    intro t ht
    have hd : ∀ u ∈ uIcc a t,
        HasDerivAt (fun u => B s u*term (Ω s) a (n+1) u - term (Ω s) a (n+1) u*B s a)
          (Ωs s u * term (Ω s) a (n+1) u + Ω s u * dterm Ω Ωs a (n+1) s u) u := by
      intro u hu
      have hu' := uIcc_subset_uIcc_left ht hu
      have hp := derivative_succ (hΩ.uncurry_left s) a u n
      apply ((hB u hu').mul hp |>.sub (hp.mul_const (B s a))).congr_deriv
      rw [ih u hu']
      rw [←mul_assoc (B s u) (Ω s u),←(hcomm u hu').eq]
      noncomm_ring
    have hi := (((hΩs.uncurry_left s).mul (continuous_term (hΩ.uncurry_left s) a (n+1))).add
      ((hΩ.uncurry_left s).mul ((continuous_dterm hΩ hΩs a (n+1)).comp
        ((continuous_const : Continuous (fun _ : ℝ => s)).prodMk continuous_id)))).intervalIntegrable (μ:=volume) a t
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
    simpa only [dterm,term_base,mul_zero,zero_mul,sub_self,sub_zero] using hh

variable [FiniteDimensional ℝ A]

theorem derivative_transport_flat (F : NilpotentFiltration A) {Ω Ωs B : ℝ → ℝ → A}
    (hΩ : Continuous Ω.uncurry) (hΩs : Continuous Ωs.uncurry)
    (hΩm : ∀ s t, Ω s t ∈ F.space 1)
    {a b c d s : ℝ} (hs : s ∈ Ioo c d)
    (hDs : ∀ v ∈ Ioo c d, ∀ t ∈ uIcc a b, HasDerivAt (fun v => Ω v t) (Ωs v t) v)
    (hDt : ∀ t ∈ uIcc a b, HasDerivAt (B s) (Ωs s t) t)
    (hcomm : ∀ t ∈ uIcc a b, Commute (Ω s t) (B s t)) :
    HasDerivAt (fun s => transport (Ω s) a F.cutoff b)
      (B s b * transport (Ω s) a F.cutoff b - transport (Ω s) a F.cutoff b * B s a) s := by
  have hp (t : ℝ) : transport (Ω t) a (F.cutoff+1) b=transport (Ω t) a F.cutoff b := by
    simp only [transport,Finset.sum_range_succ,last_term_zero F (hΩm t),add_zero]
  have hd := HasDerivAt.fun_sum (u:=Finset.range (F.cutoff+2))
    (fun n _ => derivative_term_parameter hΩ hΩs hDs n s hs b right_mem_uIcc)
  have hf : (fun v => ∑ n∈Finset.range (F.cutoff+2),term (Ω v) a n b)=
      (fun v => transport (Ω v) a F.cutoff b) := by
    funext v
    exact hp v
  rw [hf] at hd
  apply hd.congr_deriv
  rw [Finset.sum_range_succ']
  simp only [dterm_zero,add_zero]
  simp_rw [dterm_flat_formula hΩ hΩs hDt hcomm _ b right_mem_uIcc]
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_mul,transport]

end FinitePicard
end DeligneDrinfeld

namespace DeligneDrinfeld.FinitePicard

section
open MeasureTheory Set Filter
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem term_congr {Ω Θ : ℝ → A} {a b : ℝ} (h : EqOn Ω Θ (uIcc a b))
    (n : ℕ) : ∀ t∈uIcc a b,term Ω a n t=term Θ a n t := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro t ht
    simp only [term_succ]
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' := uIcc_subset_uIcc_left ht hu
    change Ω u*term Ω a n u=Θ u*term Θ a n u
    rw [h hu',ih u hu']

theorem transport_congr {Ω Θ : ℝ → A} {a b : ℝ} (h : EqOn Ω Θ (uIcc a b))
    (n : ℕ) : transport Ω a n b=transport Θ a n b := by
  apply Finset.sum_congr rfl
  intro i hi
  exact term_congr h i b right_mem_uIcc

def rectExtend {a b c d : ℝ} (hab : a≤b) (hcd : c≤d) (Ω : ℝ → ℝ → A) (s t : ℝ) : A :=
  Ω (projIcc c d hcd s) (projIcc a b hab t)

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem rectExtend_eq {a b c d : ℝ} (hab : a≤b) (hcd : c≤d) (Ω : ℝ → ℝ → A)
    {s t : ℝ} (hs : s∈Icc c d) (ht : t∈Icc a b) : rectExtend hab hcd Ω s t=Ω s t := by
  simp only [rectExtend,projIcc_of_mem hcd hs,projIcc_of_mem hab ht]

omit [NormedAlgebra ℝ A] in
theorem continuous_rectExtend {a b c d : ℝ} (hab : a≤b) (hcd : c≤d) {Ω : ℝ → ℝ → A}
    (hΩ : ContinuousOn Ω.uncurry (Icc c d ×ˢ Icc a b)) : Continuous (rectExtend hab hcd Ω).uncurry := by
  apply hΩ.comp_continuous
    (((continuous_subtype_val.comp (continuous_projIcc (h:=hcd))).comp continuous_fst).prodMk
      ((continuous_subtype_val.comp (continuous_projIcc (h:=hab))).comp continuous_snd))
  intro p
  exact ⟨(projIcc c d hcd p.1).property,(projIcc a b hab p.2).property⟩

theorem rectExtend_derivative {a b c d s t : ℝ} (hab : a≤b) (hcd : c≤d)
    {Ω Ωs : ℝ → ℝ → A} (hs : s∈Ioo c d) (ht : t∈Icc a b)
    (hd : HasDerivAt (fun v => Ω v t) (Ωs s t) s) :
    HasDerivAt (fun v => rectExtend hab hcd Ω v t) (rectExtend hab hcd Ωs s t) s := by
  rw [rectExtend_eq hab hcd Ωs ⟨hs.1.le,hs.2.le⟩ ht]
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with v hv
  exact rectExtend_eq hab hcd Ω ⟨hv.1.le,hv.2.le⟩ ht

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem derivative_transport_flat_local (F : NilpotentFiltration A) {Ω Ωs B : ℝ → ℝ → A}
    {a b c d s : ℝ} (hab : a≤b) (hcd : c≤d)
    (hΩ : ContinuousOn Ω.uncurry (Icc c d ×ˢ Icc a b))
    (hΩs : ContinuousOn Ωs.uncurry (Icc c d ×ˢ Icc a b))
    (hΩm : ∀ v∈Icc c d,∀ t∈Icc a b,Ω v t∈F.space 1)
    (hs : s∈Ioo c d)
    (hDs : ∀ v∈Ioo c d,∀ t∈Icc a b,HasDerivAt (fun v => Ω v t) (Ωs v t) v)
    (hDt : ∀ t∈Icc a b,HasDerivAt (B s) (Ωs s t) t)
    (hcomm : ∀ t∈Icc a b,Commute (Ω s t) (B s t)) :
    HasDerivAt (fun s => transport (Ω s) a F.cutoff b)
      (B s b*transport (Ω s) a F.cutoff b-transport (Ω s) a F.cutoff b*B s a) s := by
  have he (v : ℝ) (hv : v∈Icc c d) :
      transport (rectExtend hab hcd Ω v) a F.cutoff b=transport (Ω v) a F.cutoff b := by
    apply transport_congr
    intro t ht
    exact rectExtend_eq hab hcd Ω hv (by simpa only [uIcc_of_le hab] using ht)
  have hh := derivative_transport_flat F (a:=a) (b:=b) (B:=B) (continuous_rectExtend hab hcd hΩ)
    (continuous_rectExtend hab hcd hΩs)
    (fun v t => hΩm _ (projIcc c d hcd v).property _ (projIcc a b hab t).property) hs
    (fun v hv t ht => rectExtend_derivative hab hcd hv
      (by simpa only [uIcc_of_le hab] using ht) (hDs v hv t (by simpa only [uIcc_of_le hab] using ht)))
    (fun t ht => by
      rw [rectExtend_eq hab hcd Ωs ⟨hs.1.le,hs.2.le⟩ (by simpa only [uIcc_of_le hab] using ht)]
      exact hDt t (by simpa only [uIcc_of_le hab] using ht))
    (fun t ht => by
      rw [rectExtend_eq hab hcd Ω ⟨hs.1.le,hs.2.le⟩ (by simpa only [uIcc_of_le hab] using ht)]
      exact hcomm t (by simpa only [uIcc_of_le hab] using ht))
  rw [he s ⟨hs.1.le,hs.2.le⟩] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with v hv
  exact (he v ⟨hv.1.le,hv.2.le⟩).symm

end

open MeasureTheory Set Filter
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
theorem continuousOn_transport_parameter {Ω : ℝ → ℝ → A} {a b c d : ℝ}
    (hab : a≤b) (hcd : c≤d)
    (hΩ : ContinuousOn Ω.uncurry (Icc c d ×ˢ Icc a b)) (N : ℕ) :
    ContinuousOn (fun s => transport (Ω s) a N b) (Icc c d) := by
  have hh : Continuous (fun s => transport (rectExtend hab hcd Ω s) a N b) := by
    unfold transport
    apply continuous_finsetSum
    intro n hn
    exact (continuous_term_parameter (continuous_rectExtend hab hcd hΩ) a n).comp
      (continuous_id.prodMk continuous_const)
  apply hh.continuousOn.congr
  intro s hs
  apply transport_congr
  intro t ht
  exact (rectExtend_eq hab hcd Ω hs (by simpa only [uIcc_of_le hab] using ht)).symm

variable [FiniteDimensional ℝ A]

end DeligneDrinfeld.FinitePicard

namespace DeligneDrinfeld
namespace KZFlat
variable {K : Type*} [Field K]

def wedge (u v : Fin 6 → K) (i j : Fin 6) : K :=u i*v j-u j*v i

theorem arnold (u v du dv eu ev : K) (hu : u≠0) (hv : v≠0) (huv : u+v≠0) :
    du/u*((eu+ev)/(u+v))-(du+dv)/(u+v)*(eu/u)-
      (du/u*(ev/v)-dv/v*(eu/u))+
      ((du+dv)/(u+v)*(ev/v)-dv/v*((eu+ev)/(u+v)))=0 := by
  field_simp
  ring

variable {M : Type*} [LieRing M] [LieAlgebra K M]

def combine (a b c d e f : M) (u : Fin 6 → K) : M :=
  u 0 • a+u 1 • b+u 2 • c+u 3 • d+u 4 • e+u 5 • f

theorem expand (a b c d e f : M)
    (had : ⁅a,d⁆ = -⁅a,b⁆) (hae : ⁅a,e⁆ = -⁅a,c⁆) (haf : ⁅a,f⁆=0)
    (hbd : ⁅b,d⁆ = ⁅a,b⁆) (hbe : ⁅b,e⁆=0) (hbf : ⁅b,f⁆ = -⁅b,c⁆)
    (hcd : ⁅c,d⁆=0) (hce : ⁅c,e⁆ = ⁅a,c⁆) (hcf : ⁅c,f⁆ = ⁅b,c⁆)
    (hdf : ⁅d,f⁆ = -⁅d,e⁆) (hef : ⁅e,f⁆ = ⁅d,e⁆)
    (u v : Fin 6 → K) :
    ⁅combine a b c d e f u,combine a b c d e f v⁆ =
      (wedge u v 0 1-wedge u v 0 3+wedge u v 1 3) • ⁅a,b⁆+
      (wedge u v 0 2-wedge u v 0 4+wedge u v 2 4) • ⁅a,c⁆+
      (wedge u v 1 2-wedge u v 1 5+wedge u v 2 5) • ⁅b,c⁆+
      (wedge u v 3 4-wedge u v 3 5+wedge u v 4 5) • ⁅d,e⁆ := by
  have hba : ⁅b,a⁆ = -⁅a,b⁆ := (lie_skew b a).symm
  have hca : ⁅c,a⁆ = -⁅a,c⁆ := (lie_skew c a).symm
  have hcb : ⁅c,b⁆ = -⁅b,c⁆ := (lie_skew c b).symm
  have hda : ⁅d,a⁆ = ⁅a,b⁆ := by rw [←lie_skew d a,had,neg_neg]
  have hdb : ⁅d,b⁆ = -⁅a,b⁆ := by rw [←lie_skew d b,hbd]
  have hdc : ⁅d,c⁆=0 := by rw [←lie_skew d c,hcd,neg_zero]
  have hea : ⁅e,a⁆ = ⁅a,c⁆ := by rw [←lie_skew e a,hae,neg_neg]
  have heb : ⁅e,b⁆=0 := by rw [←lie_skew e b,hbe,neg_zero]
  have hec : ⁅e,c⁆ = -⁅a,c⁆ := by rw [←lie_skew e c,hce]
  have hed : ⁅e,d⁆ = -⁅d,e⁆ := (lie_skew e d).symm
  have hfa : ⁅f,a⁆=0 := by rw [←lie_skew f a,haf,neg_zero]
  have hfb : ⁅f,b⁆ = ⁅b,c⁆ := by rw [←lie_skew f b,hbf,neg_neg]
  have hfc : ⁅f,c⁆ = -⁅b,c⁆ := by rw [←lie_skew f c,hcf]
  have hfd : ⁅f,d⁆ = ⁅d,e⁆ := by rw [←lie_skew f d,hdf,neg_neg]
  have hfe : ⁅f,e⁆ = -⁅d,e⁆ := by rw [←lie_skew f e,hef]
  simp only [combine,lie_add,add_lie,lie_smul,smul_lie,lie_self,had,hae,haf,hbd,hbe,
    hbf,hcd,hce,hcf,hdf,hef,hba,hca,hcb,hda,hdb,hdc,hea,heb,hec,hed,hfa,hfb,hfc,hfd,hfe]
  unfold wedge
  module

open GenericBraid

theorem adjacent {α : Type*} (i j k : α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅GenericBraid.t (R:=K) i j,GenericBraid.t (R:=K) j k⁆ = -⁅GenericBraid.t (R:=K) i j,GenericBraid.t (R:=K) i k⁆ := by
  have h := GenericBraid.t_three (R:=K) i j k hij hik hjk
  rw [lie_add] at h
  exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h)

theorem outer {α : Type*} (i j k : α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅GenericBraid.t (R:=K) i k,GenericBraid.t (R:=K) j k⁆ = ⁅GenericBraid.t (R:=K) i j,GenericBraid.t (R:=K) i k⁆ := by
  have h := GenericBraid.t_three (R:=K) i k j hik hij hjk.symm
  rw [GenericBraid.t_comm k j,lie_add,←lie_skew (GenericBraid.t (R:=K) i k) (GenericBraid.t (R:=K) i j)] at h
  exact (neg_add_eq_zero.mp h).symm

def dlog (z v : Fin 4 → K) (i j : Fin 4) : K :=(v i-v j)/(z i-z j)

def coefficients (z v : Fin 4 → K) : Fin 6 → K :=
  ![dlog z v 0 1,dlog z v 0 2,dlog z v 0 3,dlog z v 1 2,dlog z v 1 3,dlog z v 2 3]

def connection (z v : Fin 4 → K) : T K (Fin 4) :=
  combine (GenericBraid.t 0 1) (GenericBraid.t 0 2) (GenericBraid.t 0 3) (GenericBraid.t 1 2) (GenericBraid.t 1 3) (GenericBraid.t 2 3) (coefficients z v)

theorem arnold_dlog (z v w : Fin 4 → K) (hz : Function.Injective z)
    (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    dlog z v i j*dlog z w i k-dlog z v i k*dlog z w i j-
      (dlog z v i j*dlog z w j k-dlog z v j k*dlog z w i j)+
      (dlog z v i k*dlog z w j k-dlog z v j k*dlog z w i k)=0 := by
  have hu : z i-z j≠0 := sub_ne_zero.mpr (hz.ne hij)
  have hv : z j-z k≠0 := sub_ne_zero.mpr (hz.ne hjk)
  have huv : z i-z j+(z j-z k)≠0 := by simpa using sub_ne_zero.mpr (hz.ne hik)
  simpa only [dlog,sub_add_sub_cancel] using
    arnold (z i-z j) (z j-z k) (v i-v j) (v j-v k) (w i-w j) (w j-w k) hu hv huv

theorem flat (z v w : Fin 4 → K) (hz : Function.Injective z) :
    ⁅connection z v,connection z w⁆=0 := by
  rw [connection,connection,expand _ _ _ _ _ _
    (adjacent 0 1 2 (by decide) (by decide) (by decide))
    (adjacent 0 1 3 (by decide) (by decide) (by decide))
    (GenericBraid.t_disjoint 0 1 2 3 (by decide) (by decide) (by decide) (by decide))
    (outer 0 1 2 (by decide) (by decide) (by decide))
    (GenericBraid.t_disjoint 0 2 1 3 (by decide) (by decide) (by decide) (by decide))
    (adjacent 0 2 3 (by decide) (by decide) (by decide))
    (GenericBraid.t_disjoint 0 3 1 2 (by decide) (by decide) (by decide) (by decide))
    (outer 0 1 3 (by decide) (by decide) (by decide))
    (outer 0 2 3 (by decide) (by decide) (by decide))
    (adjacent 1 2 3 (by decide) (by decide) (by decide))
    (outer 1 2 3 (by decide) (by decide) (by decide))]
  dsimp [wedge,coefficients]
  rw [arnold_dlog z v w hz 0 1 2 (by decide) (by decide) (by decide),
    arnold_dlog z v w hz 0 1 3 (by decide) (by decide) (by decide),
    arnold_dlog z v w hz 0 2 3 (by decide) (by decide) (by decide),
    arnold_dlog z v w hz 1 2 3 (by decide) (by decide) (by decide)]
  simp

end KZFlat
end DeligneDrinfeld

namespace DeligneDrinfeld.LogRectangle
open MeasureTheory Set Filter FinitePicard
open scoped Topology
variable {K A E : Type*} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
  [NormedRing A] [NormedAlgebra K A] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A]
  [Fintype E]

def mixed (c : E → A) (z zs zt zst : E → K) : A :=
  ∑ i,((zst i*z i-zt i*zs i)/(z i)^2) • c i

theorem derivative_s (c : E → A) {z zt : ℝ → E → K} {zs zst : E → K} {s : ℝ}
    (hz : ∀ i,HasDerivAt (fun s => z s i) (zs i) s)
    (hv : ∀ i,HasDerivAt (fun s => zt s i) (zst i) s)
    (hn : ∀ i,z s i≠0) :
    HasDerivAt (fun s => form c (z s) (zt s)) (mixed c (z s) zs (zt s) zst) s := by
  apply HasDerivAt.fun_sum
  intro i hi
  exact ((hv i).div (hz i) (hn i)).smul_const (c i)

theorem derivative_t (c : E → A) {z zs : ℝ → E → K} {zt zst : E → K} {t : ℝ}
    (hz : ∀ i,HasDerivAt (fun t => z t i) (zt i) t)
    (hv : ∀ i,HasDerivAt (fun t => zs t i) (zst i) t)
    (hn : ∀ i,z t i≠0) :
    HasDerivAt (fun t => form c (z t) (zs t)) (mixed c (z t) (zs t) zt zst) t := by
  convert derivative_s c hz hv hn using 1
  simp only [mixed,mul_comm (zt _)]

omit [NormedAlgebra ℝ K] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A] in
theorem continuousOn_form (c : E → A) {X : Type*} [TopologicalSpace X]
    {z v : X → E → K} {S : Set X}
    (hz : ∀ i,ContinuousOn (fun x => z x i) S)
    (hv : ∀ i,ContinuousOn (fun x => v x i) S)
    (hn : ∀ x∈S,∀ i,z x i≠0) :
    ContinuousOn (fun x => form c (z x) (v x)) S := by
  apply continuousOn_finsetSum
  intro i hi
  exact ((hv i).div (hz i) (fun x hx => hn x hx i)).smul continuousOn_const

omit [NormedAlgebra ℝ K] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A] in
theorem continuousOn_mixed (c : E → A) {X : Type*} [TopologicalSpace X]
    {z zs zt zst : X → E → K} {S : Set X}
    (hz : ∀ i,ContinuousOn (fun x => z x i) S)
    (hs : ∀ i,ContinuousOn (fun x => zs x i) S)
    (ht : ∀ i,ContinuousOn (fun x => zt x i) S)
    (hst : ∀ i,ContinuousOn (fun x => zst x i) S)
    (hn : ∀ x∈S,∀ i,z x i≠0) :
    ContinuousOn (fun x => mixed c (z x) (zs x) (zt x) (zst x)) S := by
  apply continuousOn_finsetSum
  intro i hi
  exact ((((hst i).mul (hz i)).sub ((ht i).mul (hs i))).div
    ((hz i).pow 2) (fun x hx => pow_ne_zero _ (hn x hx i))).smul continuousOn_const

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem transport_derivative (F : NilpotentFiltration A) (c : E → A)
    {z zs zt zst : ℝ → ℝ → E → K} {a b u v s : ℝ}
    (hab : a≤b) (huv : u≤v)
    (hc : ∀ i (r : K),r • c i∈F.space 1)
    (hz : ∀ i,ContinuousOn (fun w : ℝ×ℝ => z w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hs : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zs w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (ht : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zt w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hst : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zst w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hn : ∀ s∈Icc u v,∀ t∈Icc a b,∀ i,z s t i≠0)
    (hDsz : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun s => z s t i) (zs s t i) s)
    (hDszt : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun s => zt s t i) (zst s t i) s)
    (hDtz : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun t => z s t i) (zt s t i) t)
    (hDtzs : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun t => zs s t i) (zst s t i) t)
    (hflat : ∀ t∈Icc a b,
      Commute (form c (z s t) (zt s t)) (form c (z s t) (zs s t)))
    (hss : s∈Ioo u v) :
    HasDerivAt (fun s => transport (fun t => form c (z s t) (zt s t)) a F.cutoff b)
      (form c (z s b) (zs s b)*transport (fun t => form c (z s t) (zt s t)) a F.cutoff b-
        transport (fun t => form c (z s t) (zt s t)) a F.cutoff b*form c (z s a) (zs s a)) s := by
  apply derivative_transport_flat_local F (Ω:=fun s t => form c (z s t) (zt s t)) (B:=fun s t => form c (z s t) (zs s t))
    (Ωs:=fun s t => mixed c (z s t) (zs s t) (zt s t) (zst s t)) hab huv
    (continuousOn_form c hz ht (fun w hw => hn w.1 hw.1 w.2 hw.2))
    (continuousOn_mixed c hz hs ht hst (fun w hw => hn w.1 hw.1 w.2 hw.2))
    _ hss _ _ hflat
  · intro s hs t ht
    exact (F.space 1).sum_mem (fun i hi => hc i _)
  · intro s hs t ht
    exact derivative_s c (hDsz s hs t ht) (hDszt s hs t ht) (hn s ⟨hs.1.le,hs.2.le⟩ t ht)
  · intro t ht
    exact derivative_t c (hDtz s hss t ht) (hDtzs s hss t ht) (hn s ⟨hss.1.le,hss.2.le⟩ t ht)

end DeligneDrinfeld.LogRectangle

namespace DeligneDrinfeld.KZCollar
open Set Filter FinitePicard
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem regularizedBulk_two_eq (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) {r s : ℝ}
    (hr : 0<r) (hs : 0<s) (hrs : r+s<1) :
    gauge (-Y) s*transport (bulkForm X Y) r F.cutoff (1-s)*gauge X r =
      transport (regularForm Y X) 0 F.cutoff s*associator F X Y*
        Ring.inverse (transport (regularForm X Y) 0 F.cutoff r) := by
  have hu := transport_isUnit F (regularForm_mem F hX hY) 0 r F.cutoff
  have hg : Ring.inverse (normalizedSolution F X Y r)*gauge X r =
      Ring.inverse (transport (regularForm X Y) 0 F.cutoff r) := by
    rw [Ring.inverse_mul_eq_iff_eq_mul _ _ _ (normalizedSolution_isUnit F hX hY r)]
    simp only [normalizedSolution,mul_assoc,Ring.mul_inverse_cancel _ hu,mul_one]
  have ht : 1-s∈Ioo (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  rw [bulk_transport F hX hY hr (by linarith) ht.2,left_eq_right_mul_associator F hX hY ht]
  unfold rightSolution
  rw [show 1-(1-s)=s by ring]
  simp only [normalizedSolution,mul_assoc] at hg ⊢
  rw [←mul_assoc (gauge (-Y) s) (gauge Y s),gauge_neg_mul,one_mul,hg]

theorem regularizedBulk_two_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) {r s : ℝ → ℝ}
    (hr : Tendsto r (𝓝[>] 0) (𝓝[>] 0)) (hs : Tendsto s (𝓝[>] 0) (𝓝[>] 0)) :
    Tendsto (fun t => gauge (-Y) (s t)*transport (bulkForm X Y) (r t) F.cutoff (1-s t)*gauge X (r t))
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have h0 := (regularTransport_limit (Y:=Y) F hX).comp hr
  have h1 := (regularTransport_limit (Y:=X) F hY).comp hs
  have hi : Tendsto (fun t => Ring.inverse (transport (regularForm X Y) 0 F.cutoff (r t)))
      (𝓝[>] 0) (𝓝 (1:A)) := by
    simpa only [Units.val_one,Ring.inverse_one] using! (NormedRing.inverse_continuousAt (1:Aˣ)).tendsto.comp h0
  have hlim := (h1.mul (tendsto_const_nhds (x:=associator F X Y))).mul hi
  simp only [one_mul,mul_one] at hlim
  have hrs : ∀ᶠ t in 𝓝[>] 0,r t+s t<1 := by
    have h := (hr.mono_right nhdsWithin_le_nhds).add (hs.mono_right nhdsWithin_le_nhds)
    simpa only [zero_add] using h.eventually (eventually_lt_nhds (by norm_num))
  apply hlim.congr'
  filter_upwards [hr.eventually self_mem_nhdsWithin,hs.eventually self_mem_nhdsWithin,hrs] with t hrt hst hrst
  exact (regularizedBulk_two_eq F hX hY hrt hst hrst).symm

end DeligneDrinfeld.KZCollar

namespace DeligneDrinfeld.PowerAsymptotic
open MeasureTheory Set Filter Asymptotics FinitePicard
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
theorem powerSmall_of_real_bound {f : ℝ → A} {g : ℝ → ℝ} (hg : PowerSmall g)
    (h : ∀ᶠ s in 𝓝[>] 0, ‖f s‖ ≤ g s) : PowerSmall f := by
  obtain ⟨p,hp,hg⟩ := hg
  exact ⟨p,hp,(IsBigO.of_norm_eventuallyLE h).trans hg⟩

omit [NormedAlgebra ℝ A] in
theorem subpower_of_real_bound {f : ℝ → A} {g : ℝ → ℝ} (hg : Subpower g)
    (h : ∀ᶠ s in 𝓝[>] 0, ‖f s‖ ≤ g s) : Subpower f :=
  fun p hp => (IsBigO.of_norm_eventuallyLE h).trans (hg p hp)

theorem transportPoly_subpower {L : ℝ → ℝ} (hL : Subpower L) (N : ℕ) :
    Subpower (fun s => transportPoly N (L s)) := by
  apply Subpower.sum
  intro n hn
  exact hL.pow n

theorem transport_subpower {Ω : ℝ → ℝ → A} {a b L : ℝ → ℝ}
    (h : ∀ᶠ s in 𝓝[>] 0,a s ≤ b s ∧ IntervalIntegrable (Ω s) volume (a s) (b s) ∧
      0 ≤ L s ∧ integralNorm (Ω s) (a s) (b s) ≤ L s)
    (hL : Subpower L) (N : ℕ) :
    Subpower (fun s => transport (Ω s) (a s) N (b s)) := by
  apply subpower_of_real_bound ((const_subpower ‖(1:A)‖).mul (transportPoly_subpower hL N))
  filter_upwards [h] with s hs
  exact norm_transport_le hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 N

theorem transport_perturbation_powerSmall {Ω Θ : ℝ → ℝ → A} {a b L E : ℝ → ℝ}
    (h : ∀ᶠ s in 𝓝[>] 0,a s ≤ b s ∧
      IntervalIntegrable (Ω s) volume (a s) (b s) ∧
      IntervalIntegrable (Θ s) volume (a s) (b s) ∧
      0 ≤ L s ∧ 0 ≤ E s ∧
      integralNorm (Ω s) (a s) (b s) ≤ L s ∧
      integralNorm (Θ s) (a s) (b s) ≤ L s ∧
      integralNorm (fun t => Ω s t-Θ s t) (a s) (b s) ≤ E s)
    (hL : Subpower L) (hE : PowerSmall E) (N : ℕ) :
    PowerSmall (fun s => transport (Ω s) (a s) N (b s)-transport (Θ s) (a s) N (b s)) := by
  apply powerSmall_of_real_bound
    (((const_subpower ‖(1:A)‖).mul_powerSmall hE).mul_subpower (errorPoly_subpower hL N))
  filter_upwards [h] with s hs
  exact norm_transport_sub_le hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1
    hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2 N

omit [NormedAlgebra ℝ A] in

theorem normalized_perturbation_limit {f g l r : ℝ → A}
    (h : PowerSmall (fun s => f s-g s)) (hl : Subpower l) (hr : Subpower r) :
    Tendsto (fun s => l s*f s*r s-l s*g s*r s) (𝓝[>] 0) (𝓝 0) := by
  have h' := ((hl.mul_powerSmall h).mul_subpower hr).tendsto_zero
  simpa only [mul_sub,sub_mul] using h'

end DeligneDrinfeld.PowerAsymptotic

end

end OAI

end





section

namespace OAI

noncomputable section

section

end

namespace DeligneDrinfeld.PoleEstimate

section
open MeasureTheory Set intervalIntegral

lemma continuousOn_inv {a b : ℝ} (ha : 0<a) : ContinuousOn (fun t : ℝ => t⁻¹) (Icc a b) :=
  continuousOn_id.inv₀ (fun _ ht => ne_of_gt (ha.trans_le ht.1))

lemma integral_inv_sq {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b,(t⁻¹)^2)=a⁻¹-b⁻¹ := by
  have hi : IntervalIntegrable (fun t : ℝ => (t⁻¹)^2) volume a b :=
    ((continuousOn_inv ha).pow 2).intervalIntegrable_of_Icc hab
  have hd (t : ℝ) (ht : t∈uIcc a b) : HasDerivAt (fun t : ℝ => -t⁻¹) ((t⁻¹)^2) t := by
    rw [uIcc_of_le hab] at ht
    have h := ((hasDerivAt_id t).inv (ne_of_gt (ha.trans_le ht.1))).neg
    convert! h using 1
    simp [div_eq_mul_inv,inv_pow]
  have h := integral_eq_sub_of_hasDerivAt hd hi
  linarith

lemma integral_inv_sq_le {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b,(t⁻¹)^2)≤a⁻¹ := by
  rw [integral_inv_sq ha hab]
  exact sub_le_self _ (inv_nonneg.mpr (ha.le.trans hab))

lemma integral_inv_le {a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b≤1) :
    (∫ t in a..b,t⁻¹)≤-Real.log a := by
  rw [integral_inv_of_pos ha (ha.trans_le hab),Real.log_div (ne_of_gt (ha.trans_le hab)) (ne_of_gt ha)]
  have h : Real.log b≤0 := Real.log_nonpos (ha.le.trans hab) hb
  linarith

lemma abs_inv_add_sub_inv_le {t δ : ℝ} (ht : 0<t) (hδ : 0≤δ) :
    |(t+δ)⁻¹-t⁻¹|≤δ*(t⁻¹)^2 := by
  have htd : 0<t+δ := by linarith
  have horder : (t+δ)⁻¹≤t⁻¹ := inv_anti₀ ht (by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr horder)]
  have he : -((t+δ)⁻¹-t⁻¹)=δ*t⁻¹*(t+δ)⁻¹ := by
    field_simp
    ring
  rw [he]
  calc
    _ ≤ δ*t⁻¹*t⁻¹ := mul_le_mul_of_nonneg_left horder (mul_nonneg hδ (inv_nonneg.mpr ht.le))
    _ = _ := by ring

lemma abs_inv_sub_sub_inv_le {t δ : ℝ} (ht : 0<t) (hδ : 0≤δ) (hd : 2*δ≤t) :
    |(t-δ)⁻¹-t⁻¹|≤2*δ*(t⁻¹)^2 := by
  have htd : 0<t-δ := by linarith
  have horder : t⁻¹≤(t-δ)⁻¹ := inv_anti₀ htd (by linarith)
  rw [abs_of_nonneg (sub_nonneg.mpr horder)]
  have he : (t-δ)⁻¹-t⁻¹=δ*t⁻¹*(t-δ)⁻¹ := by
    field_simp
    ring
  have hbound : (t-δ)⁻¹≤2*t⁻¹ := by
    calc
      _ ≤ (t/2)⁻¹ := inv_anti₀ (by linarith) (by linarith)
      _ = 2*t⁻¹ := by field_simp
  rw [he]
  calc
    _ ≤ δ*t⁻¹*(2*t⁻¹) := mul_le_mul_of_nonneg_left hbound (mul_nonneg hδ (inv_nonneg.mpr ht.le))
    _ = _ := by ring

lemma integral_abs_inv_add_sub_inv_le {a b δ : ℝ} (ha : 0<a) (hab : a≤b) (hδ : 0≤δ) :
    (∫ t in a..b,|(t+δ)⁻¹-t⁻¹|)≤δ*a⁻¹ := by
  have hc : ContinuousOn (fun t : ℝ => |(t+δ)⁻¹-t⁻¹|) (Icc a b) :=
    (((continuousOn_id.add continuousOn_const).inv₀
      (fun t ht => ne_of_gt (show 0<t+δ by linarith [ht.1]))).sub (continuousOn_inv ha)).abs
  have hi : IntervalIntegrable (fun t : ℝ => δ*(t⁻¹)^2) volume a b :=
    (continuousOn_const.mul ((continuousOn_inv ha).pow 2)).intervalIntegrable_of_Icc hab
  calc
    _ ≤ ∫ t in a..b,δ*(t⁻¹)^2 := integral_mono_on hab (hc.intervalIntegrable_of_Icc hab) hi
      (fun t ht => abs_inv_add_sub_inv_le (ha.trans_le ht.1) hδ)
    _ = δ*(∫ t in a..b,(t⁻¹)^2) := integral_const_mul _ _
    _ ≤ δ*a⁻¹ := mul_le_mul_of_nonneg_left (integral_inv_sq_le ha hab) hδ

lemma integral_abs_inv_sub_sub_inv_le {a b δ : ℝ} (ha : 0<a) (hab : a≤b)
    (hδ : 0≤δ) (hd : 2*δ≤a) :
    (∫ t in a..b,|(t-δ)⁻¹-t⁻¹|)≤2*δ*a⁻¹ := by
  have hc : ContinuousOn (fun t : ℝ => |(t-δ)⁻¹-t⁻¹|) (Icc a b) :=
    (((continuousOn_id.sub continuousOn_const).inv₀
      (fun t ht => ne_of_gt (show 0<t-δ by linarith [ht.1]))).sub (continuousOn_inv ha)).abs
  have hi : IntervalIntegrable (fun t : ℝ => 2*δ*(t⁻¹)^2) volume a b :=
    (continuousOn_const.mul ((continuousOn_inv ha).pow 2)).intervalIntegrable_of_Icc hab
  calc
    _ ≤ ∫ t in a..b,2*δ*(t⁻¹)^2 := integral_mono_on hab (hc.intervalIntegrable_of_Icc hab) hi
      (fun t ht => abs_inv_sub_sub_inv_le (ha.trans_le ht.1) hδ (hd.trans ht.1))
    _ = 2*δ*(∫ t in a..b,(t⁻¹)^2) := integral_const_mul _ _
    _ ≤ 2*δ*a⁻¹ := mul_le_mul_of_nonneg_left (integral_inv_sq_le ha hab) (by positivity)

end

open MeasureTheory Set intervalIntegral FinitePicard KZCollar
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
theorem integralNorm_add_le {f g : ℝ → A} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    integralNorm (fun t => f t+g t) a b ≤ integralNorm f a b+integralNorm g a b := by
  calc
    _  ≤  ∫ t in a..b,‖f t‖+‖g t‖ := integral_mono_on hab (hf.add hg).norm (hf.norm.add hg.norm)
      (fun _ _ => norm_add_le _ _)
    _ = _ := intervalIntegral.integral_add hf.norm hg.norm

lemma scalar_right_inv_continuous {a b : ℝ} (hb : b<1) :
    ContinuousOn (fun t : ℝ => (t-1)⁻¹) (Icc a b) :=
  (continuousOn_id.sub continuousOn_const).inv₀
    (fun t ht => ne_of_lt (show t-1<0 by linarith [ht.2]))

lemma integral_right_inv_abs {a b : ℝ} (ha : 0<a) (hab : a ≤ b) (hb : b<1) :
    (∫ t in a..b,|(t-1)⁻¹|) ≤ -Real.log (1-b) := by
  have he : (fun t : ℝ => |(t-1)⁻¹|)=fun t => |(1-t)⁻¹| := by
    funext t
    rw [show t-1=-(1-t) by ring,inv_neg,abs_neg]
  rw [he,integral_comp_sub_left (fun t : ℝ => |t⁻¹|) 1]
  have hba : 1-b ≤ 1-a := by linarith
  have he' : (∫ t in (1-b)..(1-a),|t⁻¹|)=∫ t in (1-b)..(1-a),t⁻¹ := by
    apply integral_congr
    intro t ht
    rw [uIcc_of_le hba] at ht
    exact abs_of_nonneg (inv_nonneg.mpr (by linarith [ht.1]))
  rw [he']
  exact integral_inv_le (by linarith) hba (by linarith)

theorem bulkForm_mass {X Y : A} {a b : ℝ} (ha : 0<a) (hab : a ≤ b) (hb : b<1) :
    integralNorm (bulkForm X Y) a b ≤ ‖X‖*(-Real.log a)+‖Y‖*(-Real.log (1-b)) := by
  have hc0 := continuousOn_inv (b:=b) ha
  have hc1 := scalar_right_inv_continuous (a:=a) hb
  have hi0 : IntervalIntegrable (fun t : ℝ => t⁻¹ • X) volume a b := (hc0.smul (continuousOn_const (c:=X))).intervalIntegrable_of_Icc hab
  have hi1 : IntervalIntegrable (fun t : ℝ => (t-1)⁻¹ • Y) volume a b := (hc1.smul (continuousOn_const (c:=Y))).intervalIntegrable_of_Icc hab
  have h0 : integralNorm (fun t : ℝ => t⁻¹ • X) a b ≤ ‖X‖*(-Real.log a) := by
    unfold integralNorm
    simp only [norm_smul,Real.norm_eq_abs]
    rw [intervalIntegral.integral_mul_const]
    have he : (∫ t in a..b,|t⁻¹|)=∫ t in a..b,t⁻¹ := by
      apply integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact abs_of_nonneg (inv_nonneg.mpr (ha.le.trans ht.1))
    rw [he,mul_comm]
    exact mul_le_mul_of_nonneg_left (integral_inv_le ha hab hb.le) (norm_nonneg _)
  have h1 : integralNorm (fun t : ℝ => (t-1)⁻¹ • Y) a b ≤ ‖Y‖*(-Real.log (1-b)) := by
    unfold integralNorm
    simp only [norm_smul,Real.norm_eq_abs]
    rw [intervalIntegral.integral_mul_const,mul_comm]
    exact mul_le_mul_of_nonneg_left (integral_right_inv_abs ha hab hb) (norm_nonneg _)
  exact (integralNorm_add_le hab hi0 hi1).trans (add_le_add h0 h1)

def shiftedBulk (X Y U V : A) (δ t : ℝ) : A :=
  bulkForm X Y t+((t+δ)⁻¹-t⁻¹) • U+((t+δ-1)⁻¹-(t-1)⁻¹) • V

lemma right_shift_abs (δ t : ℝ) :
    |(t+δ-1)⁻¹-(t-1)⁻¹|=|((1-t)-δ)⁻¹-(1-t)⁻¹| := by
  rw [show t+δ-1=-((1-t)-δ) by ring,show t-1=-(1-t) by ring,inv_neg,inv_neg,neg_sub_neg,abs_sub_comm]

lemma integral_right_shift {a b δ : ℝ} (hab : a ≤ b) (hb : b<1) (hδ : 0 ≤ δ) (hd : 2*δ ≤ 1-b) :
    (∫ t in a..b,|(t+δ-1)⁻¹-(t-1)⁻¹|) ≤ 2*δ*(1-b)⁻¹ := by
  simp_rw [right_shift_abs]
  rw [integral_comp_sub_left (fun t => |(t-δ)⁻¹-t⁻¹|) 1]
  exact integral_abs_inv_sub_sub_inv_le (by linarith) (by linarith) hδ hd

lemma shiftedBulk_continuous (X Y U V : A) {a b δ : ℝ}
    (ha : 0<a) (hb : b<1) (hδ : 0 ≤ δ) (hd : 2*δ ≤ 1-b) :
    ContinuousOn (shiftedBulk X Y U V δ) (Icc a b) := by
  have h0 := continuousOn_inv (b:=b) ha
  have h1 := scalar_right_inv_continuous (a:=a) hb
  have h2 : ContinuousOn (fun t : ℝ => (t+δ)⁻¹) (Icc a b) :=
    (continuousOn_id.add continuousOn_const).inv₀
      (fun t ht => ne_of_gt (show 0<t+δ by linarith [ht.1]))
  have h3 : ContinuousOn (fun t : ℝ => (t+δ-1)⁻¹) (Icc a b) :=
    ((continuousOn_id.add continuousOn_const).sub continuousOn_const).inv₀
      (fun t ht => ne_of_lt (show t+δ-1<0 by linarith [ht.2]))
  exact (((h0.smul continuousOn_const).add (h1.smul continuousOn_const)).add
    ((h2.sub h0).smul continuousOn_const)).add ((h3.sub h1).smul continuousOn_const)

lemma shiftedBulk_error_mass {X Y U V : A} {a b δ : ℝ}
    (ha : 0<a) (hab : a ≤ b) (hb : b<1) (hδ : 0 ≤ δ) (hd : 2*δ ≤ 1-b) :
    integralNorm (fun t => shiftedBulk X Y U V δ t-bulkForm X Y t) a b ≤
      ‖U‖*(δ*a⁻¹)+‖V‖*(2*δ*(1-b)⁻¹) := by
  have h0 := continuousOn_inv (b:=b) ha
  have h1 := scalar_right_inv_continuous (a:=a) hb
  have h2 : ContinuousOn (fun t : ℝ => (t+δ)⁻¹) (Icc a b) :=
    (continuousOn_id.add continuousOn_const).inv₀
      (fun t ht => ne_of_gt (show 0<t+δ by linarith [ht.1]))
  have h3 : ContinuousOn (fun t : ℝ => (t+δ-1)⁻¹) (Icc a b) :=
    ((continuousOn_id.add continuousOn_const).sub continuousOn_const).inv₀
      (fun t ht => ne_of_lt (show t+δ-1<0 by linarith [ht.2]))
  have he : (fun t => shiftedBulk X Y U V δ t-bulkForm X Y t)=
      (fun t => ((t+δ)⁻¹-t⁻¹) • U+((t+δ-1)⁻¹-(t-1)⁻¹) • V) := by
    funext t
    unfold shiftedBulk
    abel
  rw [he]
  calc
    _  ≤  integralNorm (fun t => ((t+δ)⁻¹-t⁻¹) • U) a b+
        integralNorm (fun t => ((t+δ-1)⁻¹-(t-1)⁻¹) • V) a b :=
      integralNorm_add_le hab (((h2.sub h0).smul continuousOn_const).intervalIntegrable_of_Icc hab)
        (((h3.sub h1).smul continuousOn_const).intervalIntegrable_of_Icc hab)
    _ = ‖U‖*(∫ t in a..b,|(t+δ)⁻¹-t⁻¹|)+‖V‖*(∫ t in a..b,|(t+δ-1)⁻¹-(t-1)⁻¹|) := by
      simp only [integralNorm,norm_smul,Real.norm_eq_abs,intervalIntegral.integral_mul_const]
      ring
    _  ≤  _ := add_le_add
      (mul_le_mul_of_nonneg_left (integral_abs_inv_add_sub_inv_le ha hab hδ) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (integral_right_shift hab hb hδ hd) (norm_nonneg _))

end DeligneDrinfeld.PoleEstimate

namespace DeligneDrinfeld.FourCollar
open MeasureTheory Set Filter FinitePicard KZCollar RegularSingular
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def form (a b d e f : A) (x y vx vy : ℝ) : A :=
  (vx/x) • a+(vy/y) • b+((vy-vx)/(y-x)) • d+
    (vx/(x-1)) • e+(vy/(y-1)) • f

def cx : Fin 5 → ℝ → ℝ := ![(fun s => s^2),(fun s => s),
  (fun s => 1-s-s^2),(fun s => s^2),(fun s => 1-s)]
def cy : Fin 5 → ℝ → ℝ := ![(fun s => s),(fun s => s+s^2),
  (fun s => 1-s),(fun s => 1-s^2),(fun s => 1-s^2)]
def vx : Fin 5 → ℝ → ℝ := ![(fun s => 2*s),(fun _ => 1),
  (fun s => -1-2*s),(fun s => 2*s),(fun _ => -1)]
def vy : Fin 5 → ℝ → ℝ := ![(fun _ => 1),(fun s => 1+2*s),
  (fun _ => -1),(fun s => -2*s),(fun s => -2*s)]

def residue (a b d e f : A) : Fin 5 → A :=
  ![2 • a+b+d,a+b+2 • d,f+e+2 • d,2 • a+2 • f,2 • f+e+d]

def remainder (a b d e f : A) : Fin 5 → ℝ → A :=
  ![(fun s => -((1-s)⁻¹) • (d+f)-(2*s/(1-s^2)) • e),
    (fun s => (1+s)⁻¹ • b-(1-s)⁻¹ • e-((1+2*s)/(1-s-s^2)) • f),
    (fun s => (1+s)⁻¹ • e-(1-s)⁻¹ • b-((1+2*s)/(1-s-s^2)) • a),
    (fun s => -(2*s/(1-s^2)) • (b+e)-(4*s/(1-2*s^2)) • d),
    (fun s => -((1-s)⁻¹) • (d+a)-(2*s/(1-s^2)) • b)]

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem coordinates_derivative (i : Fin 5) (s : ℝ) :
    HasDerivAt (cx i) (vx i s) s ∧ HasDerivAt (cy i) (vy i s) s := by
  have hd : HasDerivAt (fun t : ℝ => t) 1 s := hasDerivAt_id s
  have hc (c : ℝ) : HasDerivAt (fun _ : ℝ => c) 0 s := hasDerivAt_const s c
  have hp : HasDerivAt (fun s : ℝ => s^2) (2*s) s := by
    convert! hd.pow 2 using 1; norm_num
  fin_cases i
  · change HasDerivAt (fun s : ℝ => s^2) (2*s) s ∧ HasDerivAt id 1 s
    exact ⟨hp,hd⟩
  · change HasDerivAt id 1 s ∧ HasDerivAt (fun s : ℝ => s+s^2) (1+2*s) s
    exact ⟨hd,hd.add hp⟩
  · change HasDerivAt (fun s : ℝ => 1-s-s^2) (-1-2*s) s ∧ HasDerivAt (fun s : ℝ => 1-s) (-1) s
    exact ⟨by simpa using! ((hc 1).sub hd).sub hp,by simpa using! (hc 1).sub hd⟩
  · change HasDerivAt (fun s : ℝ => s^2) (2*s) s ∧ HasDerivAt (fun s : ℝ => 1-s^2) (-2*s) s
    exact ⟨hp,by simpa using! (hc 1).sub hp⟩
  · change HasDerivAt (fun s : ℝ => 1-s) (-1) s ∧ HasDerivAt (fun s : ℝ => 1-s^2) (-2*s) s
    exact ⟨by simpa using! (hc 1).sub hd,by simpa using! (hc 1).sub hp⟩

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem scalar_nonzero {s : ℝ} (hs : s∈Icc 0 (1/4)) :
    1-s≠0 ∧ 1+s≠0 ∧ 1-s^2≠0 ∧ 1-s-s^2≠0 ∧ 1-2*s^2≠0 := by
  have hsq : s^2≤1/16 := by nlinarith [hs.1,hs.2,sq_nonneg (s-1/4)]
  exact ⟨by linarith [hs.2],by linarith [hs.1],by linarith,
    by linarith [hs.2],by linarith⟩

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem chamber (i : Fin 5) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    0<cx i s ∧ cx i s<cy i s ∧ cy i s<1 := by
  have hsq : s^2≤1/16 := by nlinarith [hs.1,hs.2,sq_nonneg (s-1/4)]
  have hss : s^2<s := by nlinarith [hs.1,hs.2]
  fin_cases i
  · change 0<s^2 ∧ s^2<s ∧ s<1
    exact ⟨sq_pos_of_pos hs.1,hss,by linarith [hs.2]⟩
  · change 0<s ∧ s<s+s^2 ∧ s+s^2<1
    exact ⟨hs.1,by nlinarith [sq_pos_of_pos hs.1],by nlinarith [hs.2]⟩
  · change 0<1-s-s^2 ∧ 1-s-s^2<1-s ∧ 1-s<1
    exact ⟨by linarith [hs.2],by nlinarith [sq_pos_of_pos hs.1],by linarith [hs.1]⟩
  · change 0<s^2 ∧ s^2<1-s^2 ∧ 1-s^2<1
    exact ⟨sq_pos_of_pos hs.1,by linarith,by nlinarith [sq_pos_of_pos hs.1]⟩
  · change 0<1-s ∧ 1-s<1-s^2 ∧ 1-s^2<1
    exact ⟨by nlinarith [hs.1,hs.2,sq_pos_of_pos hs.1],
    by nlinarith [hs.1,hs.2,sq_pos_of_pos hs.1],by nlinarith [hs.1,hs.2,sq_pos_of_pos hs.1]⟩

theorem form_collar (a b d e f : A) (i : Fin 5) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    form a b d e f (cx i s) (cy i s) (vx i s) (vy i s)=
      s⁻¹ • residue a b d e f i+remainder a b d e f i s := by
  obtain ⟨h1,hp,h2,h3,h4⟩ := scalar_nonzero ⟨hs.1.le,hs.2⟩
  have h0 : s≠0 := ne_of_gt hs.1
  have hss : s-s^2≠0 := by nlinarith [hs.1,hs.2]
  have hsp : s+s^2≠0 := by nlinarith [hs.1,sq_nonneg s]
  have hm : s-1≠0 := sub_ne_zero.mpr (by linarith [hs.2])
  have hs2 : s^2-1≠0 := by exact sub_ne_zero.mpr (sub_ne_zero.mp h2).symm
  have hn3 : -1+s+s^2≠0 := by intro h; apply h3; linarith
  have hnsp : -s-s^2≠0 := by intro h; apply hsp; linarith
  have hn4 : 1-s^2*2≠0 := by intro h; apply h4; linarith
  have hnp : -1-s≠0 := by intro h; apply hp; linarith
  fin_cases i
  · change form a b d e f (s^2) s (2*s) 1=
      s⁻¹ • (2 • a+b+d)+(-((1-s)⁻¹) • (d+f)-(2*s/(1-s^2)) • e)
    unfold form
    match_scalars <;> field_simp [h0,h1,hp,h2,h3,h4,hss,hsp,hm,hs2,hn3,hnsp,hn4] <;> ring
  · change form a b d e f s (s+s^2) 1 (1+2*s)=
      s⁻¹ • (a+b+2 • d)+((1+s)⁻¹ • b-(1-s)⁻¹ • e-((1+2*s)/(1-s-s^2)) • f)
    unfold form
    match_scalars <;> field_simp [h0,h1,hp,h2,h3,h4,hss,hsp,hm,hs2,hn3,hnsp,hn4] <;> first | ring1 | (ring_nf; field_simp [h0,hn3,hnsp,hn4,hnp]; ring)
  · change form a b d e f (1-s-s^2) (1-s) (-1-2*s) (-1)=
      s⁻¹ • (f+e+2 • d)+((1+s)⁻¹ • e-(1-s)⁻¹ • b-((1+2*s)/(1-s-s^2)) • a)
    unfold form
    match_scalars <;> field_simp [h0,h1,hp,h2,h3,h4,hss,hsp,hm,hs2,hn3,hnsp,hn4] <;> first | ring1 | (ring_nf; field_simp [h0,hn3,hnsp,hn4,hnp]; ring)
  · change form a b d e f (s^2) (1-s^2) (2*s) (-2*s)=
      s⁻¹ • (2 • a+2 • f)+(-(2*s/(1-s^2)) • (b+e)-(4*s/(1-2*s^2)) • d)
    unfold form
    match_scalars <;> field_simp [h0,h1,hp,h2,h3,h4,hss,hsp,hm,hs2,hn3,hnsp,hn4] <;> first | ring1 | (ring_nf; field_simp [h0,hn3,hnsp,hn4,hnp]; ring)
  · change form a b d e f (1-s) (1-s^2) (-1) (-2*s)=
      s⁻¹ • (2 • f+e+d)+(-((1-s)⁻¹) • (d+a)-(2*s/(1-s^2)) • b)
    unfold form
    match_scalars <;> field_simp [h0,h1,hp,h2,h3,h4,hss,hsp,hm,hs2,hn3,hnsp,hn4] <;> ring

 theorem remainder_continuous (a b d e f : A) (i : Fin 5) :
    ContinuousOn (remainder a b d e f i) (Icc 0 (1/4)) := by
  have h1 : ContinuousOn (fun s : ℝ => (1-s)⁻¹) (Icc 0 (1/4)) :=
    (continuousOn_const.sub continuousOn_id).inv₀ (fun s hs => (scalar_nonzero hs).1)
  have hp : ContinuousOn (fun s : ℝ => (1+s)⁻¹) (Icc 0 (1/4)) :=
    (continuousOn_const.add continuousOn_id).inv₀ (fun s hs => (scalar_nonzero hs).2.1)
  have h2 : ContinuousOn (fun s : ℝ => 2*s/(1-s^2)) (Icc 0 (1/4)) :=
    (continuousOn_const.mul continuousOn_id).div (continuousOn_const.sub (continuousOn_id.pow 2))
      (fun s hs => (scalar_nonzero hs).2.2.1)
  have h3 : ContinuousOn (fun s : ℝ => (1+2*s)/(1-s-s^2)) (Icc 0 (1/4)) :=
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).div
      ((continuousOn_const.sub continuousOn_id).sub (continuousOn_id.pow 2))
      (fun s hs => (scalar_nonzero hs).2.2.2.1)
  have h4 : ContinuousOn (fun s : ℝ => 4*s/(1-2*s^2)) (Icc 0 (1/4)) :=
    (continuousOn_const.mul continuousOn_id).div
      (continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.pow 2)))
      (fun s hs => (scalar_nonzero hs).2.2.2.2)
  fin_cases i
  all_goals norm_num only [remainder,Fin.reduceFinMk,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact ((h1.neg).smul continuousOn_const).sub (h2.smul continuousOn_const)
  · exact ((hp.smul continuousOn_const).sub (h1.smul continuousOn_const)).sub (h3.smul continuousOn_const)
  · exact ((hp.smul continuousOn_const).sub (h1.smul continuousOn_const)).sub (h3.smul continuousOn_const)
  · exact ((h2.neg).smul continuousOn_const).sub (h4.smul continuousOn_const)
  · exact ((h1.neg).smul continuousOn_const).sub (h2.smul continuousOn_const)

variable (F : NilpotentFiltration A) {a b d e f : A}
  (ha : a∈F.space 1) (hb : b∈F.space 1) (hd : d∈F.space 1)
  (he : e∈F.space 1) (hf : f∈F.space 1)

include ha hb hd he hf

theorem residue_mem (i : Fin 5) : residue a b d e f i∈F.space 1 := by
  fin_cases i
  · exact (F.space 1).add_mem ((F.space 1).add_mem ((F.space 1).nsmul_mem ha _) hb) hd
  · exact (F.space 1).add_mem ((F.space 1).add_mem ha hb) ((F.space 1).nsmul_mem hd _)
  · exact (F.space 1).add_mem ((F.space 1).add_mem hf he) ((F.space 1).nsmul_mem hd _)
  · exact (F.space 1).add_mem ((F.space 1).nsmul_mem ha _) ((F.space 1).nsmul_mem hf _)
  · exact (F.space 1).add_mem ((F.space 1).add_mem ((F.space 1).nsmul_mem hf _) he) hd

theorem remainder_mem (i : Fin 5) (s : ℝ) : remainder a b d e f i s∈F.space 1 := by
  fin_cases i
  · exact (F.space 1).sub_mem ((F.space 1).smul_mem _ ((F.space 1).add_mem hd hf))
      ((F.space 1).smul_mem _ he)
  · exact (F.space 1).sub_mem ((F.space 1).sub_mem ((F.space 1).smul_mem _ hb)
      ((F.space 1).smul_mem _ he)) ((F.space 1).smul_mem _ hf)
  · exact (F.space 1).sub_mem ((F.space 1).sub_mem ((F.space 1).smul_mem _ he)
      ((F.space 1).smul_mem _ hb)) ((F.space 1).smul_mem _ ha)
  · exact (F.space 1).sub_mem ((F.space 1).smul_mem _ ((F.space 1).add_mem hb he))
      ((F.space 1).smul_mem _ hd)
  · exact (F.space 1).sub_mem ((F.space 1).smul_mem _ ((F.space 1).add_mem hd ha))
      ((F.space 1).smul_mem _ hb)

def normalized (i : Fin 5) : ℝ → A :=
  RegularSingular.solution F (residue a b d e f i) (remainder a b d e f i)

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem normalized_derivative (i : Fin 5) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    HasDerivAt (normalized F (a:=a) (b:=b) (d:=d) (e:=e) (f:=f) i)
      (form a b d e f (cx i s) (cy i s) (vx i s) (vy i s)*normalized F (a:=a) (b:=b) (d:=d) (e:=e) (f:=f) i s) s := by
  rw [form_collar a b d e f i ⟨hs.1,hs.2.le⟩]
  exact solution_derivative F (residue_mem F ha hb hd he hf i)
    (remainder_mem F ha hb hd he hf i) (remainder_continuous a b d e f i) hs

theorem normalized_isUnit (i : Fin 5) (s : ℝ) :
    IsUnit (normalized F (a:=a) (b:=b) (d:=d) (e:=e) (f:=f) i s) :=
  solution_isUnit F (residue_mem F ha hb hd he hf i) (remainder_mem F ha hb hd he hf i) s

end DeligneDrinfeld.FourCollar

namespace DeligneDrinfeld.BCBoundary

section
open MeasureTheory Set Filter Asymptotics FinitePicard KZCollar PowerAsymptotic PoleEstimate
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def endpoint (s : ℝ) : ℝ := 1-s-s^2

theorem interval_bounds {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    s ≤ endpoint s ∧ endpoint s<1 ∧ 2*s^2 ≤ 1-endpoint s := by
  have hsq : s^2 ≤ 1/16 := by nlinarith [hs.1,hs.2,sq_nonneg (s-1/4)]
  simp only [endpoint]
  exact ⟨by nlinarith [hs.1,hs.2],by nlinarith [hs.1],by nlinarith [hs.1,hs.2]⟩

theorem form_eq (a b d e f : A) (s t : ℝ) :
    FourCollar.form a b d e f t (t+s^2) 1 1=shiftedBulk (a+b) (e+f) b f (s^2) t := by
  simp only [FourCollar.form,shiftedBulk,bulkForm,one_div,sub_self,zero_div,zero_smul,add_zero,
    smul_add,sub_smul]
  abel

theorem error_bound (X Y U V : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    integralNorm (fun t => shiftedBulk X Y U V (s^2) t-bulkForm X Y t) s (endpoint s) ≤
      (‖U‖+2*‖V‖)*s := by
  obtain ⟨hab,hb,hd⟩ := interval_bounds hs
  have h := shiftedBulk_error_mass (X:=X) (Y:=Y) (U:=U) (V:=V) hs.1 hab hb (sq_nonneg s) hd
  have he : s^2*s⁻¹=s := by field_simp
  have hgap : s ≤ 1-endpoint s := by dsimp [endpoint]; nlinarith [sq_nonneg s]
  have hr : (1-endpoint s)⁻¹ ≤ s⁻¹ := inv_anti₀ hs.1 hgap
  have he2 : 2*s^2*(1-endpoint s)⁻¹ ≤ 2*s := by
    calc
      _ ≤ 2*s^2*s⁻¹ := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 2*s := by rw [mul_assoc,he]
  calc
    _ ≤ ‖U‖*(s^2*s⁻¹)+‖V‖*(2*s^2*(1-endpoint s)⁻¹) := h
    _ ≤ ‖U‖*s+‖V‖*(2*s) := by rw [he]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left he2 (norm_nonneg V))
    _ = _ := by ring

theorem bulk_bound (X Y : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    integralNorm (bulkForm X Y) s (endpoint s) ≤ (‖X‖+‖Y‖)*(-Real.log s) := by
  obtain ⟨hab,hb,hd⟩ := interval_bounds hs
  have hh : -Real.log (1-endpoint s) ≤ -Real.log s := by
    apply neg_le_neg
    exact Real.log_le_log hs.1 (by dsimp [endpoint]; nlinarith [sq_nonneg s])
  calc
    _ ≤ ‖X‖*(-Real.log s)+‖Y‖*(-Real.log (1-endpoint s)) := bulkForm_mass hs.1 hab hb
    _ ≤ ‖X‖*(-Real.log s)+‖Y‖*(-Real.log s) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hh (norm_nonneg Y))
    _ = _ := by ring

def mass (X Y U V : A) (s : ℝ) : ℝ :=
  (‖X‖+‖Y‖)*(-Real.log s)+(‖U‖+2*‖V‖)*s

omit [NormedAlgebra ℝ A] in
theorem mass_subpower (X Y U V : A) : Subpower (mass X Y U V) := by
  have hl : Subpower (fun s : ℝ => -Real.log s) := by
    simpa only [pow_one,neg_one_mul] using (const_subpower (-1:ℝ)).mul (log_pow_subpower 1)
  exact ((const_subpower _).mul hl).add (continuousAt_subpower (continuousAt_const.mul continuousAt_id))

theorem perturbation (X Y U V : A) (N : ℕ) :
    PowerSmall (fun s => transport (shiftedBulk X Y U V (s^2)) s N (endpoint s)-
      transport (bulkForm X Y) s N (endpoint s)) := by
  apply transport_perturbation_powerSmall (L:=mass X Y U V)
    (E:=fun s => (‖U‖+2*‖V‖)*s) _ (mass_subpower X Y U V) (linear_powerSmall _) N
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  obtain ⟨hab,hb,hd⟩ := interval_bounds hs
  have hcΩ := shiftedBulk_continuous X Y U V hs.1 hb (sq_nonneg s) hd
  have hcΘ := (bulkForm_continuous X Y).mono (show Icc s (endpoint s)⊆Ioo 0 1 from
    fun t ht => ⟨hs.1.trans_le ht.1,ht.2.trans_lt hb⟩)
  have hiΩ : IntervalIntegrable (shiftedBulk X Y U V (s^2)) volume s (endpoint s) := hcΩ.intervalIntegrable_of_Icc hab
  have hiΘ : IntervalIntegrable (bulkForm X Y) volume s (endpoint s) := hcΘ.intervalIntegrable_of_Icc hab
  have hE : 0 ≤ (‖U‖+2*‖V‖)*s := mul_nonneg (by positivity) hs.1.le
  have hlog : 0 ≤ -Real.log s := neg_nonneg.mpr (Real.log_nonpos hs.1.le (by linarith [hs.2]))
  have hbase : 0 ≤ (‖X‖+‖Y‖)*(-Real.log s) := mul_nonneg (by positivity) hlog
  have he := error_bound X Y U V hs
  have hΘ := bulk_bound X Y hs
  have hΩ : integralNorm (shiftedBulk X Y U V (s^2)) s (endpoint s) ≤ mass X Y U V s := by
    have h := integralNorm_add_le hab hiΘ (hiΩ.sub hiΘ)
    have hf : (fun t => bulkForm X Y t+(shiftedBulk X Y U V (s^2) t-bulkForm X Y t))=
        shiftedBulk X Y U V (s^2) := by funext t; abel
    rw [hf] at h
    exact h.trans (add_le_add hΘ he)
  exact ⟨hab,hiΩ,hiΘ,add_nonneg hbase hE,hE,hΩ,hΘ.trans (le_add_of_nonneg_right hE),he⟩

end

open Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem shared_residue_cancel {X Y Z : A} {N : ℕ} (hZ : Z^(N+1)=0)
    (hZX : Commute Z X) (hZY : Commute Z Y) (a b s : ℝ) :
    gauge (-(Y+Z)) s*transport (bulkForm X Y) a N b*gauge (X+Z) s =
      gauge (-Y) s*transport (bulkForm X Y) a N b*gauge X s := by
  have ht := transport_commute Z (fun t : ℝ => (hZX.smul_right (t⁻¹)).add_right (hZY.smul_right ((t-1)⁻¹))) a N b
  have hg := gauge_commute hZ ht.symm s
  change Commute (transport (bulkForm X Y) a N b) (gauge Z s) at hg
  have hy : gauge (-(Y+Z)) s=gauge (-Y) s*gauge (-Z) s := by
    rw [neg_add,gauge_add_of_commute]; exact hZY.symm.neg_left.neg_right
  have hx : gauge (X+Z) s=gauge Z s*gauge X s := by
    rw [add_comm,gauge_add_of_commute hZX]
  rw [hy,hx]
  calc
    _ = gauge (-Y) s*(gauge (-Z) s*(transport (bulkForm X Y) a N b*gauge Z s))*gauge X s := by simp only [mul_assoc]
    _ = gauge (-Y) s*(gauge (-Z) s*(gauge Z s*transport (bulkForm X Y) a N b))*gauge X s := by rw [hg.eq]
    _ = _ := by rw [←mul_assoc (gauge (-Z) s),gauge_neg_mul,one_mul]

omit [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem gap_tendsto : Tendsto (fun s : ℝ => s+s^2) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_pow (by omega : 2≠0),zero_add] using h.add (h.pow 2)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact add_pos_of_pos_of_nonneg hs (sq_nonneg s)

theorem bulk_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    Tendsto (fun s => gauge (-Y) s*transport (bulkForm X Y) s F.cutoff (endpoint s)*gauge X s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have h := (gauge_ratio_limit Y).mul (regularizedBulk_two_limit F hX hY tendsto_id gap_tendsto)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 0<s at hs
  have hg : gauge Y (1+s)*gauge (-Y) (s+s^2)=gauge (-Y) s := by
    rw [show s+s^2=(1+s)*s by ring,gauge_mul_scale _ (by linarith) hs.ne',←mul_assoc,gauge_mul_neg,one_mul]
  simp only [←mul_assoc]
  rw [hg,show 1-(s+s^2)=endpoint s by dsimp [endpoint]; ring]
  rfl

theorem limit (F : NilpotentFiltration A) {X Y Z : A} (U V : A)
    (hX : X∈F.space 1) (hY : Y∈F.space 1) (hZ : Z∈F.space 1)
    (hZX : Commute Z X) (hZY : Commute Z Y) :
    Tendsto (fun s => gauge (-(Y+Z)) s*
      transport (shiftedBulk X Y U V (s^2)) s F.cutoff (endpoint s)*gauge (X+Z) s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have hl := normalized_perturbation_limit (perturbation X Y U V F.cutoff)
    (gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).neg_mem ((F.space 1).add_mem hY hZ))))
    (gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).add_mem hX hZ)))
  have hb := bulk_limit F hX hY
  have he (s : ℝ) := shared_residue_cancel (pow_cutoff_eq_zero F hZ) hZX hZY s (endpoint s) s
  have hb' : Tendsto (fun s => gauge (-(Y+Z)) s*transport (bulkForm X Y) s F.cutoff (endpoint s)*gauge (X+Z) s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := hb.congr (fun s => (he s).symm)
  simpa only [zero_add,sub_add_cancel] using! hl.add hb'

end DeligneDrinfeld.BCBoundary

namespace DeligneDrinfeld.KZRectangle
open MeasureTheory Set Filter FinitePicard LogRectangle
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {K A : Type*} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
  [NormedRing A] [NormedAlgebra K A] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A]

def dif (z : Fin 4 → K) (i : Fin 6) : K := z (edges i).1-z (edges i).2

omit [NormedAlgebra ℝ K] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A] in
theorem form_eq (j : GenericBraid.T K (Fin 4) →ₗ⁅K⁆ A) (z v : Fin 4 → K) :
    form (chords j) (dif z) (dif v)=j (KZFlat.connection z v) := by
  simp only [form,Fin.sum_univ_succ,KZFlat.connection,KZFlat.combine,KZFlat.coefficients,
    KZFlat.dlog,dif,chords,edges,map_add,map_smul]
  norm_num only [Fin.reduceFinMk,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.isValue,
    Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Fin.zero_eta,Fin.mk_one]
  simp only [Fin.sum_univ_zero,add_zero]
  abel

omit [NormedAlgebra ℝ K] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A] in
theorem form_commute (j : GenericBraid.T K (Fin 4) →ₗ⁅K⁆ A)
    (z v w : Fin 4 → K) (hz : Function.Injective z) :
    Commute (form (chords j) (dif z) (dif v)) (form (chords j) (dif z) (dif w)) := by
  rw [form_eq,form_eq]
  have h := congrArg j (KZFlat.flat z v w hz)
  rw [j.map_lie,map_zero] at h
  exact sub_eq_zero.mp h

omit [NormedRing A] [NormedAlgebra K A] [NormedAlgebra ℝ K] [NormedAlgebra ℝ A]
  [IsScalarTower ℝ K A] in
theorem dif_ne_zero (z : Fin 4 → K) (hz : Function.Injective z) (i : Fin 6) : dif z i≠0 := by
  apply sub_ne_zero.mpr (hz.ne _)
  fin_cases i <;> decide

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem transport_derivative (F : NilpotentFiltration A)
    (j : GenericBraid.T K (Fin 4) →ₗ⁅K⁆ A)
    {z zs zt zst : ℝ → ℝ → Fin 4 → K} {a b u v s : ℝ}
    (hab : a≤b) (huv : u≤v)
    (hc : ∀ i (r : K),r • chords j i∈F.space 1)
    (hz : ∀ i,ContinuousOn (fun w : ℝ×ℝ => z w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hs : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zs w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (ht : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zt w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hst : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zst w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hn : ∀ s∈Icc u v,∀ t∈Icc a b,Function.Injective (z s t))
    (hDsz : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun s => z s t i) (zs s t i) s)
    (hDszt : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun s => zt s t i) (zst s t i) s)
    (hDtz : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun t => z s t i) (zt s t i) t)
    (hDtzs : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun t => zs s t i) (zst s t i) t)
    (hss : s∈Ioo u v) :
    HasDerivAt (fun s => transport (fun t => j (KZFlat.connection (z s t) (zt s t))) a F.cutoff b)
      (j (KZFlat.connection (z s b) (zs s b))*transport (fun t => j (KZFlat.connection (z s t) (zt s t))) a F.cutoff b-
        transport (fun t => j (KZFlat.connection (z s t) (zt s t))) a F.cutoff b*j (KZFlat.connection (z s a) (zs s a))) s := by
  simp only [←form_eq]
  apply LogRectangle.transport_derivative F (chords j) (z:=fun s t => dif (z s t))
    (zt:=fun s t => dif (zt s t)) (zs:=fun s t => dif (zs s t))
    (zst:=fun s t => dif (zst s t)) hab huv hc
  · intro i
    exact (hz _).sub (hz _)
  · intro i
    exact (hs _).sub (hs _)
  · intro i
    exact (ht _).sub (ht _)
  · intro i
    exact (hst _).sub (hst _)
  · intro s hs t ht i
    exact dif_ne_zero _ (hn s hs t ht) i
  · intro s hs t ht i
    exact (hDsz s hs t ht _).sub (hDsz s hs t ht _)
  · intro s hs t ht i
    exact (hDszt s hs t ht _).sub (hDszt s hs t ht _)
  · intro s hs t ht i
    exact (hDtz s hs t ht _).sub (hDtz s hs t ht _)
  · intro s hs t ht i
    exact (hDtzs s hs t ht _).sub (hDtzs s hs t ht _)
  · intro t ht
    exact form_commute j _ _ _ (hn s ⟨hss.1.le,hss.2.le⟩ t ht)
  · exact hss

end DeligneDrinfeld.KZRectangle

namespace DeligneDrinfeld.StraightKZ
open MeasureTheory Set Filter FinitePicard KZRectangle LogRectangle
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def segment (p q : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) : ℝ := (1-t)*p i+t*q i

def velocity (p q : Fin 4 → ℝ) (i : Fin 4) : ℝ := q i-p i

@[simp] theorem segment_zero (p q : Fin 4 → ℝ) : segment p q 0=p := by
  ext i; simp [segment]
@[simp] theorem segment_one (p q : Fin 4 → ℝ) : segment p q 1=q := by
  ext i; simp [segment]

theorem segment_strictMono {p q : Fin 4 → ℝ} (hp : StrictMono p) (hq : StrictMono q)
    {t : ℝ} (ht : t∈Icc 0 1) : StrictMono (segment p q t) := by
  intro i k hik
  dsimp [segment]
  have h0 := hp hik
  have h1 := hq hik
  have h := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h0.le)
  have hh := mul_nonneg ht.1 (sub_nonneg.mpr h1.le)
  by_cases htp : 0<t
  · have hpos := mul_pos htp (sub_pos.mpr h1)
    nlinarith
  · have htz : t=0 := le_antisymm (not_lt.mp htp) ht.1
    simpa only [htz,sub_zero,one_mul,zero_mul,add_zero] using h0

theorem segment_derivative (p q : Fin 4 → ℝ) (t : ℝ) (i : Fin 4) :
    HasDerivAt (fun t => segment p q t i) (velocity p q i) t := by
  have h : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
  convert! (((hasDerivAt_const t (1:ℝ)).sub h).mul_const (p i)).add (h.mul_const (q i)) using 1
  dsimp [velocity]
  ring

def connection (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (p q : Fin 4 → ℝ) (t : ℝ) : A :=
  j (KZFlat.connection (segment p q t) (velocity p q))

def fundamental (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
    (p q : Fin 4 → ℝ) : A := transport (connection j p q) 0 F.cutoff 1

lemma connection_mem (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
    (hc : ∀ i,chords j i∈F.space 1) (z v : Fin 4 → ℝ) : j (KZFlat.connection z v)∈F.space 1 := by
  rw [←form_eq]
  exact (F.space 1).sum_mem (fun i hi => (F.space 1).smul_mem _ (hc i))

lemma zero_connection (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (p : Fin 4 → ℝ) :
    j (KZFlat.connection p 0)=0 := by
  rw [←form_eq]
  simp [form,dif]

variable [CompleteSpace A] [FiniteDimensional ℝ A]

omit [CompleteSpace A] in
theorem fundamental_isUnit (F : NilpotentFiltration A)
    (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (hc : ∀ i,chords j i∈F.space 1) (p q : Fin 4 → ℝ) :
    IsUnit (fundamental F j p q) :=
  transport_isUnit F (fun _ => connection_mem F j hc _ _) _ _ _

theorem fundamental_derivative (F : NilpotentFiltration A)
    (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (hc : ∀ i,chords j i∈F.space 1)
    {p : Fin 4 → ℝ} {q q' : ℝ → Fin 4 → ℝ} {a b s : ℝ}
    (hp : StrictMono p) (hq : ∀ s∈Icc a b,StrictMono (q s))
    (hqc : ∀ i,ContinuousOn (fun s => q s i) (Icc a b))
    (hqc' : ∀ i,ContinuousOn (fun s => q' s i) (Icc a b))
    (hqd : ∀ s∈Ioo a b,∀ i,HasDerivAt (fun s => q s i) (q' s i) s)
    (hs : s∈Ioo a b) :
    HasDerivAt (fun s => fundamental F j p (q s))
      (j (KZFlat.connection (q s) (q' s))*fundamental F j p (q s)) s := by
  have hab : a≤b := le_trans hs.1.le hs.2.le
  have hq2 (i : Fin 4) : ContinuousOn (fun w : ℝ×ℝ => q w.1 i) (Icc a b ×ˢ Icc 0 1) :=
    (hqc i).comp continuous_fst.continuousOn (fun w hw => hw.1)
  have hq2' (i : Fin 4) : ContinuousOn (fun w : ℝ×ℝ => q' w.1 i) (Icc a b ×ˢ Icc 0 1) :=
    (hqc' i).comp continuous_fst.continuousOn (fun w hw => hw.1)
  have h := KZRectangle.transport_derivative F j (z:=fun s t => segment p (q s) t)
    (zt:=fun s _ => velocity p (q s)) (zs:=fun s t i => t*q' s i)
    (zst:=fun s _ => q' s) (by norm_num : (0:ℝ)≤1) hab
    (fun i r => (F.space 1).smul_mem r (hc i))
    (fun i => ((continuousOn_const.sub continuous_snd.continuousOn).mul continuousOn_const).add
      (continuous_snd.continuousOn.mul (hq2 i)))
    (fun i => continuous_snd.continuousOn.mul (hq2' i))
    (fun i => (hq2 i).sub continuousOn_const) (fun i => hq2' i)
    (fun v hv t ht => (segment_strictMono hp (hq v hv) ht).injective)
    (fun v hv t ht i => by
      simpa only [segment,Pi.add_apply,zero_add] using! (hasDerivAt_const v ((1-t)*p i)).add ((hqd v hv i).const_mul t))
    (fun v hv t ht i => by
      simpa [velocity] using! (hqd v hv i).sub_const (p i))
    (fun v hv t ht i => segment_derivative p (q v) t i)
    (fun v hv t ht i => by
      simpa using! (hasDerivAt_id t).mul_const (q' v i)) hs
  have hzero : (fun i => (0:ℝ)*q' s i)=(0:Fin 4 → ℝ) := by ext; simp
  have hone : (fun i => (1:ℝ)*q' s i)=q' s := by ext; simp
  simpa only [segment_zero,segment_one,hzero,hone,zero_connection,mul_zero,sub_zero,
    fundamental,StraightKZ.connection] using! h

end DeligneDrinfeld.StraightKZ

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace StraightKZ
open MeasureTheory Set Filter FinitePicard KZRectangle LogRectangle
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem connection_continuousOn (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
    {X : Type*} [TopologicalSpace X] {z v : X → Fin 4 → ℝ} {S : Set X}
    (hz : ∀ i,ContinuousOn (fun x => z x i) S) (hv : ∀ i,ContinuousOn (fun x => v x i) S)
    (hn : ∀ x∈S,Function.Injective (z x)) :
    ContinuousOn (fun x => j (KZFlat.connection (z x) (v x))) S := by
  simp only [←form_eq]
  apply LogRectangle.continuousOn_form (chords j)
  · intro i
    exact (hz _).sub (hz _)
  · intro i
    exact (hv _).sub (hv _)
  · intro x hx i
    exact dif_ne_zero _ (hn x hx) i

theorem segment_connection_continuousOn (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
    {p : Fin 4 → ℝ} {q : ℝ → Fin 4 → ℝ} {a b : ℝ}
    (hp : StrictMono p) (hq : ∀ s∈Icc a b,StrictMono (q s))
    (hqc : ∀ i,ContinuousOn (fun s => q s i) (Icc a b)) :
    ContinuousOn (fun w : ℝ×ℝ => connection j p (q w.1) w.2) (Icc a b ×ˢ Icc 0 1) := by
  have hq2 (i : Fin 4) : ContinuousOn (fun w : ℝ×ℝ => q w.1 i) (Icc a b ×ˢ Icc 0 1) :=
    (hqc i).comp continuous_fst.continuousOn (fun w hw => hw.1)
  apply connection_continuousOn j
  · intro i
    exact ((continuousOn_const.sub continuous_snd.continuousOn).mul continuousOn_const).add
      (continuous_snd.continuousOn.mul (hq2 i))
  · intro i
    exact (hq2 i).sub continuousOn_const
  · intro w hw
    exact (segment_strictMono hp (hq w.1 hw.1) hw.2).injective

theorem fundamental_continuousOn (F : NilpotentFiltration A)
    (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
    {p : Fin 4 → ℝ} {q : ℝ → Fin 4 → ℝ} {a b : ℝ} (hab : a≤b)
    (hp : StrictMono p) (hq : ∀ s∈Icc a b,StrictMono (q s))
    (hqc : ∀ i,ContinuousOn (fun s => q s i) (Icc a b)) :
    ContinuousOn (fun s => fundamental F j p (q s)) (Icc a b) :=
  continuousOn_transport_parameter (Ω:=fun s t => connection j p (q s) t) (by norm_num) hab (segment_connection_continuousOn j hp hq hqc) F.cutoff

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem transport_eq_ratio (F : NilpotentFiltration A)
    (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (hc : ∀ i,chords j i∈F.space 1)
    {p : Fin 4 → ℝ} {q q' : ℝ → Fin 4 → ℝ} {a b : ℝ} (hab : a<b)
    (hp : StrictMono p) (hq : ∀ s∈Icc a b,StrictMono (q s))
    (hqc : ∀ i,ContinuousOn (fun s => q s i) (Icc a b))
    (hqc' : ∀ i,ContinuousOn (fun s => q' s i) (Icc a b))
    (hqd : ∀ s∈Ioo a b,∀ i,HasDerivAt (fun s => q s i) (q' s i) s) :
    transport (fun s => j (KZFlat.connection (q s) (q' s))) a F.cutoff b=
      fundamental F j p (q b)*Ring.inverse (fundamental F j p (q a)) := by
  have hcon := connection_continuousOn j hqc hqc' (fun s hs => (hq s hs).injective)
  apply transport_eq_fundamental F (fun _ => connection_mem F j hc _ _) hab
    (hcon.intervalIntegrable_of_Icc hab.le) (hcon.mono Ioo_subset_Icc_self)
    (fun s hs => fundamental_derivative F j hc hp hq hqc hqc' hqd hs)
    (fundamental_continuousOn F j hab.le hp hq hqc)
    (fun s hs => fundamental_isUnit F j hc _ _)

end StraightKZ

namespace FourFrames
open MeasureTheory Set Filter FinitePicard KZCollar FourCollar KZRectangle StraightKZ
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def point (x y : ℝ) : Fin 4 → ℝ := ![0,x,y,1]
def speed (vx vy : ℝ) : Fin 4 → ℝ := ![0,vx,vy,0]
def path (i : Fin 5) (s : ℝ) : Fin 4 → ℝ := point (cx i s) (cy i s)
def tangent (i : Fin 5) (s : ℝ) : Fin 4 → ℝ := speed (vx i s) (vy i s)

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem point_strictMono {x y : ℝ} (h : 0<x ∧ x<y ∧ y<1) : StrictMono (point x y) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem path_strictMono (i : Fin 5) {s : ℝ} (hs : s∈Ioc 0 (1/4)) : StrictMono (path i s) :=
  point_strictMono (chamber i hs)

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem path_derivative (i : Fin 5) (s : ℝ) (k : Fin 4) :
    HasDerivAt (fun s => path i s k) (tangent i s k) s := by
  rcases coordinates_derivative i s with ⟨hx,hy⟩
  fin_cases k
  · exact hasDerivAt_const s 0
  · exact hx
  · exact hy
  · exact hasDerivAt_const s 1

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem path_continuous (i : Fin 5) (k : Fin 4) : Continuous (fun s => path i s k) :=
  continuous_iff_continuousAt.mpr (fun s => (path_derivative i s k).continuousAt)

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem tangent_continuous (i : Fin 5) (k : Fin 4) : Continuous (fun s => tangent i s k) := by
  fin_cases k
  · exact continuous_const
  · change Continuous (vx i)
    fin_cases i
    · exact continuous_const.mul continuous_id
    · exact continuous_const
    · exact continuous_const.sub (continuous_const.mul continuous_id)
    · exact continuous_const.mul continuous_id
    · exact continuous_const
  · change Continuous (vy i)
    fin_cases i
    · exact continuous_const
    · exact continuous_const.add (continuous_const.mul continuous_id)
    · exact continuous_const
    · exact continuous_const.mul continuous_id
    · exact continuous_const.mul continuous_id
  · exact continuous_const

theorem form_eq (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A) (x y vx vy : ℝ) :
    j (KZFlat.connection (point x y) (speed vx vy))=
      FourCollar.form (chords j 0) (chords j 1) (chords j 3) (chords j 4) (chords j 5) x y vx vy := by
  simp only [KZFlat.connection,KZFlat.combine,map_add,map_smul]
  change ((0-vx) / (0-x)) • j (GenericBraid.t 0 1)+((0-vy) / (0-y)) • j (GenericBraid.t 0 2)+
    ((0-0) / (0-1:ℝ)) • j (GenericBraid.t 0 3)+((vx-vy)/(x-y)) • j (GenericBraid.t 1 2)+
    ((vx-0)/(x-1)) • j (GenericBraid.t 1 3)+((vy-0)/(y-1)) • j (GenericBraid.t 2 3)=
    (vx/x) • j (GenericBraid.t 0 1)+(vy/y) • j (GenericBraid.t 0 2)+
    ((vy-vx)/(y-x)) • j (GenericBraid.t 1 2)+(vx/(x-1)) • j (GenericBraid.t 1 3)+
    (vy/(y-1)) • j (GenericBraid.t 2 3)
  simp only [zero_sub,sub_zero,neg_div_neg_eq,zero_div,zero_smul,add_zero]
  have h : (vx-vy)/(x-y)=(vy-vx)/(y-x) := by
    rw [←neg_sub vy vx,←neg_sub y x,neg_div_neg_eq]
  rw [h]

variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1) [CompleteSpace A] [FiniteDimensional ℝ A]

def radial (i : Fin 5) : ℝ → A :=
  normalized F (a:=chords j 0) (b:=chords j 1) (d:=chords j 3) (e:=chords j 4) (f:=chords j 5) i

include hc in
theorem radial_derivative (i : Fin 5) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    HasDerivAt (radial F j i)
      (j (KZFlat.connection (path i s) (tangent i s))*radial F j i s) s := by
  rw [path,tangent,form_eq]
  exact normalized_derivative F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i hs

include hc in
theorem radial_isUnit (i : Fin 5) (s : ℝ) : IsUnit (radial F j i s) :=
  normalized_isUnit F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i s

include hc in
theorem fundamental_path_derivative {p : Fin 4 → ℝ} (hp : StrictMono p)
    (i : Fin 5) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    HasDerivAt (fun s => fundamental F j p (path i s))
      (j (KZFlat.connection (path i s) (tangent i s))*fundamental F j p (path i s)) s := by
  apply fundamental_derivative F j hc (a:=s/2) (b:=(s+1/4)/2) hp
  · intro t ht
    apply path_strictMono i
    exact ⟨by linarith [hs.1,ht.1],by linarith [hs.2,ht.2]⟩
  · intro k
    exact (path_continuous i k).continuousOn
  · intro k
    exact (tangent_continuous i k).continuousOn
  · intro t ht k
    exact path_derivative i t k
  · exact ⟨by linarith [hs.1],by linarith [hs.2]⟩

def corner (p : Fin 4 → ℝ) (i : Fin 5) : A :=
  Ring.inverse (fundamental F j p (path i (1/8)))*radial F j i (1/8)

include hc in
theorem corner_eq {p : Fin 4 → ℝ} (hp : StrictMono p) (i : Fin 5)
    {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    Ring.inverse (fundamental F j p (path i s))*radial F j i s=corner F j p i := by
  exact transition_constant (fun t ht => fundamental_path_derivative F j hc hp i ht)
    (fun t ht => radial_derivative F j hc i ht)
    (fun _ _ => fundamental_isUnit F j hc _ _) hs (by norm_num : (1/8:ℝ)∈Ioo 0 (1/4))

include hc in
theorem corner_isUnit (p : Fin 4 → ℝ) (i : Fin 5) : IsUnit (corner F j p i) :=
by
  have hu := fundamental_isUnit F j hc p (path i (1/8))
  rw [corner,Ring.inverse_of_isUnit hu]
  exact (hu.unit⁻¹).isUnit.mul (radial_isUnit F j hc i _)

include hc in
theorem radial_eq {p : Fin 4 → ℝ} (hp : StrictMono p) (i : Fin 5)
    {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    radial F j i s=fundamental F j p (path i s)*corner F j p i := by
  rw [←corner_eq F j hc hp i hs,←mul_assoc,
    Ring.mul_inverse_cancel _ (fundamental_isUnit F j hc _ _),one_mul]

include hc in

theorem corner_cocycle (p : Fin 4 → ℝ) (i k l : Fin 5) :
    (Ring.inverse (corner F j p i)*corner F j p k)*
      (Ring.inverse (corner F j p k)*corner F j p l)=
      Ring.inverse (corner F j p i)*corner F j p l := by
  rw [mul_assoc,←mul_assoc (corner F j p k),
    Ring.mul_inverse_cancel _ (corner_isUnit F j hc p k),one_mul]

end FourFrames

section
namespace PowerAsymptotic
open Set Filter FinitePicard KZCollar Asymptotics
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
theorem PowerSmall.add {f g : ℝ → A} (hf : PowerSmall f) (hg : PowerSmall g) :
    PowerSmall (fun s => f s+g s) := by
  obtain ⟨p,hp,hf⟩ := hf
  obtain ⟨q,hq,hg⟩ := hg
  have hd (u v : ℝ) (hvu : v ≤ u) :
      (fun s : ℝ => s^u) =O[𝓝[>] 0] (fun s : ℝ => s^v) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with s hs
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hs.1.le _)]
    exact Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2 hvu
  exact ⟨min p q,lt_min hp hq,(hf.trans (hd p _ (min_le_left _ _))).add
    (hg.trans (hd q _ (min_le_right _ _)))⟩

omit [NormedAlgebra ℝ A] in
theorem PowerSmall.subpower {f : ℝ → A} (hf : PowerSmall f) : Subpower f :=
  tendsto_subpower hf.tendsto_zero

omit [NormedAlgebra ℝ A] in
theorem subpower_of_sub {f g : ℝ → A} (hg : Subpower g)
    (hf : PowerSmall (fun s => f s-g s)) : Subpower f := by
  simpa only [sub_add_cancel] using! hf.subpower.add hg

omit [NormedAlgebra ℝ A] in
theorem frame_replacement (f l l₀ r r₀ : ℝ → A)
    (hf : Subpower f) (hl₀ : Subpower l₀) (hr₀ : Subpower r₀)
    (hl : PowerSmall (fun s => l s-l₀ s)) (hr : PowerSmall (fun s => r s-r₀ s)) :
    PowerSmall (fun s => l s*f s*r s-l₀ s*f s*r₀ s) := by
  have h := ((hl.mul_subpower hf).mul_subpower (subpower_of_sub hr₀ hr)).add
    ((hl₀.mul hf).mul_powerSmall hr)
  apply h.congr
  intro s
  simp only [sub_mul,mul_sub]
  abel

end PowerAsymptotic
namespace FourFrames
open Set Filter FinitePicard KZCollar FourCollar KZRectangle PowerAsymptotic
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1) [CompleteSpace A] [FiniteDimensional ℝ A]

def model (i : Fin 5) (s : ℝ) : A :=
  gauge (residue (chords j 0) (chords j 1) (chords j 3) (chords j 4) (chords j 5) i) s

def inverseModel (i : Fin 5) (s : ℝ) : A :=
  gauge (-residue (chords j 0) (chords j 1) (chords j 3) (chords j 4) (chords j 5) i) s

include hc in
omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem radial_error (i : Fin 5) : PowerSmall (fun s => radial F j i s-model j i s) :=
  solution_sub_gauge F (residue_mem F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i)
    (by norm_num : (0:ℝ)<1/4) (remainder_continuous _ _ _ _ _ i)

include hc in
theorem inverse_radial_error (i : Fin 5) :
    PowerSmall (fun s => Ring.inverse (radial F j i s)-inverseModel j i s) :=
  inverse_solution_sub_gauge F (residue_mem F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i)
    (remainder_mem F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i)
    (by norm_num : (0:ℝ)<1/4) (remainder_continuous _ _ _ _ _ i)

include hc in
omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem model_subpower (i : Fin 5) : Subpower (model j i) :=
  gauge_subpower (pow_cutoff_eq_zero F (residue_mem F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i))

include hc in
omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem inverseModel_subpower (i : Fin 5) : Subpower (inverseModel j i) :=
  gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).neg_mem (residue_mem F (hc 0) (hc 1) (hc 3) (hc 4) (hc 5) i)))

include hc in
theorem radial_replacement (i k : Fin 5) {f : ℝ → A} (hf : Subpower f) :
    PowerSmall (fun s => Ring.inverse (radial F j k s)*f s*radial F j i s-
      inverseModel j k s*f s*model j i s) :=
  frame_replacement f _ _ _ _ hf (inverseModel_subpower F j hc k) (model_subpower F j hc i)
    (inverse_radial_error F j hc k) (radial_error F j hc i)

end FourFrames

end

namespace FourFrames
open Set Filter FinitePicard KZCollar KZRectangle StraightKZ PowerAsymptotic
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

include hc in
theorem normalized_transport_eq_corner {p : Fin 4 → ℝ} (hp : StrictMono p)
    (i k : Fin 5) {s : ℝ} (hs : s∈Ioo 0 (1/4)) {T : A}
    (hT : T=fundamental F j p (path k s)*Ring.inverse (fundamental F j p (path i s))) :
    Ring.inverse (radial F j k s)*T*radial F j i s=
      Ring.inverse (corner F j p k)*corner F j p i := by
  rw [hT,radial_eq F j hc hp i hs,radial_eq F j hc hp k hs,
    inverse_mul_of_units (fundamental_isUnit F j hc _ _) (corner_isUnit F j hc p k)]
  simp only [mul_assoc]
  rw [←mul_assoc (Ring.inverse (fundamental F j p (path i s))),
    Ring.inverse_mul_cancel _ (fundamental_isUnit F j hc _ _),one_mul,
    ←mul_assoc (Ring.inverse (fundamental F j p (path k s))),
    Ring.inverse_mul_cancel _ (fundamental_isUnit F j hc _ _),one_mul]

include hc in

theorem corner_eq_of_limit {p : Fin 4 → ℝ} (hp : StrictMono p) (i k : Fin 5)
    {T : ℝ → A} {v : A} (hT : Subpower T)
    (hpath : ∀ᶠ s in 𝓝[>] 0,s∈Ioo 0 (1/4) ∧
      T s=fundamental F j p (path k s)*Ring.inverse (fundamental F j p (path i s)))
    (hlim : Tendsto (fun s => inverseModel j k s*T s*model j i s) (𝓝[>] 0) (𝓝 v)) :
    Ring.inverse (corner F j p k)*corner F j p i=v := by
  have hr := (radial_replacement F j hc i k hT).tendsto_zero.add hlim
  simp only [zero_add,sub_add_cancel] at hr
  have he : (fun s => Ring.inverse (radial F j k s)*T s*radial F j i s) =ᶠ[𝓝[>] 0]
      (fun _ => Ring.inverse (corner F j p k)*corner F j p i) := by
    filter_upwards [hpath] with s hs
    exact normalized_transport_eq_corner F j hc hp i k hs.1 hs.2
  exact tendsto_nhds_unique tendsto_const_nhds (hr.congr' he)

end FourFrames

section
namespace BCBoundary
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem bulk_subpower (X Y : A) (N : ℕ) :
    Subpower (fun s => transport (bulkForm X Y) s N (endpoint s)) := by
  apply transport_subpower (L:=mass X Y 0 0) _ (mass_subpower X Y 0 0) N
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  obtain ⟨hab,hb,hd⟩ := interval_bounds hs
  have hc := (bulkForm_continuous X Y).mono (show Icc s (endpoint s)⊆Ioo 0 1 from
    fun t ht => ⟨hs.1.trans_le ht.1,ht.2.trans_lt hb⟩)
  have hlog : 0 ≤ -Real.log s := neg_nonneg.mpr (Real.log_nonpos hs.1.le (by linarith [hs.2]))
  refine ⟨hab,hc.intervalIntegrable_of_Icc hab,?_,?_⟩
  · simp only [mass,norm_zero,mul_zero,zero_mul,add_zero]
    exact mul_nonneg (by positivity) hlog
  · simpa only [mass,norm_zero,mul_zero,zero_mul,add_zero] using bulk_bound X Y hs

theorem edge_subpower (X Y U V : A) (N : ℕ) :
    Subpower (fun s => transport (shiftedBulk X Y U V (s^2)) s N (endpoint s)) :=
  subpower_of_sub (bulk_subpower X Y N) (perturbation X Y U V N)

end BCBoundary
namespace FourFrames
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
  KZRectangle StraightKZ BCBoundary
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem chord_triple (i k l : Fin 4) (hik : i≠k) (hil : i≠l) (hkl : k≠l) :
    Commute (j (GenericBraid.t i k)) (j (GenericBraid.t i l)+j (GenericBraid.t k l)) := by
  have h := congrArg j (GenericBraid.t_three (R:=ℝ) i k l hik hil hkl)
  rw [j.map_lie,map_add,map_zero] at h
  exact sub_eq_zero.mp h

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem BC_commute_left : Commute (chords j 3) (chords j 0+chords j 1) := by
  have h := chord_triple j 1 2 0 (by decide) (by decide) (by decide)
  rw [GenericBraid.t_comm 1 0,GenericBraid.t_comm 2 0] at h
  exact h

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem BC_commute_right : Commute (chords j 3) (chords j 4+chords j 5) :=
  chord_triple j 1 2 3 (by decide) (by decide) (by decide)

def BCtransport (s : ℝ) : A :=
  transport (shiftedBulk (chords j 0+chords j 1) (chords j 4+chords j 5)
    (chords j 1) (chords j 5) (s^2)) s F.cutoff (endpoint s)

include hc in
theorem BC_model_limit : Tendsto (fun s => inverseModel j 2 s*BCtransport F j s*model j 1 s)
    (𝓝[>] 0) (𝓝 (associator F (chords j 0+chords j 1) (chords j 4+chords j 5))) := by
  have hl := BCBoundary.limit F (chords j 1) (chords j 5)
    ((F.space 1).add_mem (hc 0) (hc 1)) ((F.space 1).add_mem (hc 4) (hc 5))
    ((F.space 1).add_mem (hc 3) (hc 3))
    ((BC_commute_left j).add_left (BC_commute_left j))
    ((BC_commute_right j).add_left (BC_commute_right j))
  convert! hl using 1
  funext s
  change KZCollar.gauge (-(chords j 5+chords j 4+2 • chords j 3)) s*BCtransport F j s*
    KZCollar.gauge (chords j 0+chords j 1+2 • chords j 3) s=
    KZCollar.gauge (-(chords j 4+chords j 5+(chords j 3+chords j 3))) s*BCtransport F j s*
    KZCollar.gauge (chords j 0+chords j 1+(chords j 3+chords j 3)) s
  rw [two_smul ℕ,add_comm (chords j 5) (chords j 4)]

include hc in
theorem BC_transport_eq {p : Fin 4 → ℝ} (hp : StrictMono p) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    BCtransport F j s=fundamental F j p (path 2 s)*Ring.inverse (fundamental F j p (path 1 s)) := by
  let q : ℝ → Fin 4 → ℝ := fun t => point t (t+s^2)
  let q' : ℝ → Fin 4 → ℝ := fun _ => speed 1 1
  have hsq : s^2 ≤ 1/16 := by nlinarith [hs.1,hs.2,sq_nonneg (s-1/4)]
  have hab : s<endpoint s := by dsimp [endpoint]; nlinarith [hs.1,hs.2]
  have hq (t : ℝ) (ht : t∈Icc s (endpoint s)) : StrictMono (q t) := by
    apply point_strictMono
    exact ⟨hs.1.trans_le ht.1,by nlinarith [sq_pos_of_pos hs.1],by dsimp [endpoint] at ht; linarith [ht.2,hs.1]⟩
  have hqc (i : Fin 4) : ContinuousOn (fun t => q t i) (Icc s (endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact continuousOn_id
    · exact continuousOn_id.add continuousOn_const
    · exact continuousOn_const
  have hqc' (i : Fin 4) : ContinuousOn (fun t => q' t i) (Icc s (endpoint s)) := continuousOn_const
  have hqd (t : ℝ) (_ : t∈Ioo s (endpoint s)) (i : Fin 4) : HasDerivAt (fun t => q t i) (q' t i) t := by
    fin_cases i
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_id _
    · exact (hasDerivAt_id t).add_const (s^2)
    · exact hasDerivAt_const _ _
  have ht := transport_eq_ratio F j hc hab hp hq hqc hqc' hqd
  have hform : (fun t => j (KZFlat.connection (q t) (q' t)))=
      shiftedBulk (chords j 0+chords j 1) (chords j 4+chords j 5) (chords j 1) (chords j 5) (s^2) := by
    funext t
    rw [show q t=point t (t+s^2) from rfl,show q' t=speed 1 1 from rfl,FourFrames.form_eq,BCBoundary.form_eq]
  rw [hform] at ht
  have hqb : q (endpoint s)=path 2 s := by
    funext i
    fin_cases i <;> simp [q,path,point,FourCollar.cx,FourCollar.cy,endpoint]
  rw [hqb] at ht
  exact ht

include hc in
theorem BC_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 2)*corner F j p 1=
      associator F (chords j 0+chords j 1) (chords j 4+chords j 5) := by
  apply corner_eq_of_limit F j hc hp 1 2
    (BCBoundary.edge_subpower _ _ _ _ F.cutoff) _ (BC_model_limit F j hc)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact ⟨hs,BC_transport_eq F j hc hp hs⟩

end FourFrames

end

namespace ADBoundary
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def endpoint (s : ℝ) : ℝ := 1-s^2

def movedPole (X Y U : A) (δ t : ℝ) : A := bulkForm X Y t+((t-δ)⁻¹-t⁻¹) • U

theorem bounds {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    s<endpoint s ∧ endpoint s<1 ∧ 2*s^2 ≤ s := by
  have hsq : s^2 ≤ 1/16 := by nlinarith [hs.1,hs.2,sq_nonneg (s-1/4)]
  unfold endpoint
  exact ⟨by nlinarith [hs.2],by nlinarith [sq_pos_of_pos hs.1],by nlinarith [hs.1,hs.2]⟩

theorem continuous (X Y U : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    ContinuousOn (movedPole X Y U (s^2)) (Icc s (endpoint s)) := by
  have hb := bounds hs
  have h0 := continuousOn_inv (b:=endpoint s) hs.1
  have hm : ContinuousOn (fun t : ℝ => (t-s^2)⁻¹) (Icc s (endpoint s)) :=
    (continuousOn_id.sub continuousOn_const).inv₀ (fun t ht => ne_of_gt (by change 0<t-s^2; nlinarith [hb.2.2,ht.1,hs.1]))
  have hbulk := (bulkForm_continuous X Y).mono (show Icc s (endpoint s)⊆Ioo 0 1 from
    fun t ht => ⟨hs.1.trans_le ht.1,ht.2.trans_lt hb.2.1⟩)
  exact hbulk.add ((hm.sub h0).smul continuousOn_const)

theorem error_bound (X Y U : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    integralNorm (fun t => movedPole X Y U (s^2) t-bulkForm X Y t) s (endpoint s) ≤ 2*‖U‖*s := by
  have hb := bounds hs
  have he : (fun t => movedPole X Y U (s^2) t-bulkForm X Y t)=
      (fun t => ((t-s^2)⁻¹-t⁻¹) • U) := by funext t; unfold movedPole; abel
  rw [he]
  calc
    _ = (∫ t in s..endpoint s,|(t-s^2)⁻¹-t⁻¹|)*‖U‖ := by
      simp only [integralNorm,norm_smul,Real.norm_eq_abs,intervalIntegral.integral_mul_const]
    _ ≤ (2*s^2*s⁻¹)*‖U‖ := mul_le_mul_of_nonneg_right
      (integral_abs_inv_sub_sub_inv_le hs.1 hb.1.le (sq_nonneg _) hb.2.2) (norm_nonneg _)
    _ = _ := by field_simp

theorem bulk_bound (X Y : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    integralNorm (bulkForm X Y) s (endpoint s) ≤ (‖X‖+2*‖Y‖)*(-Real.log s) := by
  have hb := bounds hs
  have h := bulkForm_mass (X:=X) (Y:=Y) hs.1 hb.1.le hb.2.1
  rw [show 1-endpoint s=s^2 by dsimp [endpoint]; ring,Real.log_pow] at h
  convert! h using 1; ring

def mass (X Y U : A) (s : ℝ) : ℝ := (‖X‖+2*‖Y‖)*(-Real.log s)+2*‖U‖*s

omit [NormedAlgebra ℝ A] in
theorem mass_subpower (X Y U : A) : Subpower (mass X Y U) := by
  have hl : Subpower (fun s : ℝ => -Real.log s) := by
    simpa only [pow_one,neg_one_mul] using (const_subpower (-1:ℝ)).mul (log_pow_subpower 1)
  exact ((const_subpower _).mul hl).add (continuousAt_subpower (continuousAt_const.mul continuousAt_id))

theorem estimates (X Y U : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    s ≤ endpoint s ∧ IntervalIntegrable (movedPole X Y U (s^2)) volume s (endpoint s) ∧
    IntervalIntegrable (bulkForm X Y) volume s (endpoint s) ∧
    0 ≤ mass X Y U s ∧ 0 ≤ 2*‖U‖*s ∧
    integralNorm (movedPole X Y U (s^2)) s (endpoint s) ≤ mass X Y U s ∧
    integralNorm (bulkForm X Y) s (endpoint s) ≤ mass X Y U s ∧
    integralNorm (fun t => movedPole X Y U (s^2) t-bulkForm X Y t) s (endpoint s) ≤ 2*‖U‖*s := by
  have hb := bounds hs
  have hiΩ : IntervalIntegrable (movedPole X Y U (s^2)) volume s (endpoint s) :=
    (continuous X Y U hs).intervalIntegrable_of_Icc hb.1.le
  have hiΘ : IntervalIntegrable (bulkForm X Y) volume s (endpoint s) :=
    ((bulkForm_continuous X Y).mono (show Icc s (endpoint s)⊆Ioo 0 1 from
      fun t ht => ⟨hs.1.trans_le ht.1,ht.2.trans_lt hb.2.1⟩)).intervalIntegrable_of_Icc hb.1.le
  have hE : 0 ≤ 2*‖U‖*s := mul_nonneg (by positivity) hs.1.le
  have hB : 0 ≤ (‖X‖+2*‖Y‖)*(-Real.log s) := mul_nonneg (by positivity)
    (neg_nonneg.mpr (Real.log_nonpos hs.1.le (by linarith [hs.2])))
  have hΩ : integralNorm (movedPole X Y U (s^2)) s (endpoint s) ≤ mass X Y U s := by
    have h := integralNorm_add_le hb.1.le hiΘ (hiΩ.sub hiΘ)
    have he : (fun t => bulkForm X Y t+(movedPole X Y U (s^2) t-bulkForm X Y t))=movedPole X Y U (s^2) := by funext t; abel
    rw [he] at h
    exact h.trans (add_le_add (bulk_bound X Y hs) (error_bound X Y U hs))
  exact ⟨hb.1.le,hiΩ,hiΘ,add_nonneg hB hE,hE,hΩ,
    (bulk_bound X Y hs).trans (le_add_of_nonneg_right hE),error_bound X Y U hs⟩

theorem perturbation (X Y U : A) (N : ℕ) :
    PowerSmall (fun s => transport (movedPole X Y U (s^2)) s N (endpoint s)-
      transport (bulkForm X Y) s N (endpoint s)) := by
  apply transport_perturbation_powerSmall (L:=mass X Y U) (E:=fun s => 2*‖U‖*s)
    _ (mass_subpower X Y U) (linear_powerSmall _) N
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact estimates X Y U hs

theorem transport_subpower (X Y U : A) (N : ℕ) :
    Subpower (fun s => transport (movedPole X Y U (s^2)) s N (endpoint s)) := by
  apply PowerAsymptotic.transport_subpower (L:=mass X Y U) _ (mass_subpower X Y U) N
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  have h := estimates X Y U hs
  exact ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2.2.1⟩

theorem gauge_double (X : A) (s : ℝ) : KZCollar.gauge (X+X) s=KZCollar.gauge X (s^2) := by
  unfold KZCollar.gauge
  congr 1
  rw [Real.log_pow]
  norm_num
  module

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem square_tendsto : Tendsto (fun s : ℝ => s^2) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · simpa only [id_eq,zero_pow (by decide : 2≠0)] using
      ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).pow 2)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact sq_pos_of_pos (show 0<s from hs)

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem model_bulk_eq (F : NilpotentFiltration A) {X Y Z : A} (hZ : Z∈F.space 1)
    (hZX : Commute Z X) (hZY : Commute Z Y) (s : ℝ) :
    KZCollar.gauge (-(Z+(Y+Y))) s*transport (bulkForm X Y) s F.cutoff (endpoint s)*
      KZCollar.gauge (Z+X) s=
    KZCollar.gauge (-Y) (s^2)*transport (bulkForm X Y) s F.cutoff (1-s^2)*KZCollar.gauge X s := by
  have ht := transport_commute Z (fun t : ℝ => (hZX.smul_right (t⁻¹)).add_right (hZY.smul_right ((t-1)⁻¹))) s F.cutoff (endpoint s)
  have hg := gauge_commute (pow_cutoff_eq_zero F hZ) ht.symm s
  change Commute (transport (bulkForm X Y) s F.cutoff (endpoint s)) (KZCollar.gauge Z s) at hg
  rw [show -(Z+(Y+Y))=(-Y + -Y)+ -Z by abel,
    gauge_add_of_commute ((hZY.symm.neg_left.neg_right).add_left (hZY.symm.neg_left.neg_right)),
    gauge_double,gauge_add_of_commute hZX]
  calc
    _ = KZCollar.gauge (-Y) (s^2)*(KZCollar.gauge (-Z) s*
      (transport (bulkForm X Y) s F.cutoff (endpoint s)*KZCollar.gauge Z s))*KZCollar.gauge X s := by simp only [mul_assoc]
    _ = KZCollar.gauge (-Y) (s^2)*(KZCollar.gauge (-Z) s*
      (KZCollar.gauge Z s*transport (bulkForm X Y) s F.cutoff (endpoint s)))*KZCollar.gauge X s := by rw [hg.eq]
    _ = _ := by rw [←mul_assoc (KZCollar.gauge (-Z) s),gauge_neg_mul,one_mul]; rfl

theorem limit (F : NilpotentFiltration A) {X Y Z : A} (U : A)
    (hX : X∈F.space 1) (hY : Y∈F.space 1) (hZ : Z∈F.space 1)
    (hZX : Commute Z X) (hZY : Commute Z Y) :
    Tendsto (fun s => KZCollar.gauge (-(Z+(Y+Y))) s*
      transport (movedPole X Y U (s^2)) s F.cutoff (endpoint s)*KZCollar.gauge (Z+X) s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have hb := regularizedBulk_two_limit F hX hY tendsto_id square_tendsto
  have he (s : ℝ) := model_bulk_eq F hZ hZX hZY s
  have hb' : Tendsto (fun s => KZCollar.gauge (-(Z+(Y+Y))) s*
      transport (bulkForm X Y) s F.cutoff (endpoint s)*KZCollar.gauge (Z+X) s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := hb.congr (fun s => (he s).symm)
  have hl := normalized_perturbation_limit (perturbation X Y U F.cutoff)
    (gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).neg_mem ((F.space 1).add_mem hZ ((F.space 1).add_mem hY hY)))))
    (gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).add_mem hZ hX)))
  simpa only [zero_add,sub_add_cancel] using! hl.add hb'

end ADBoundary

namespace FourFrames
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
  KZRectangle StraightKZ
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem AD_commute_left : Commute (chords j 0) (chords j 1+chords j 3) :=
  chord_triple j 0 1 2 (by decide) (by decide) (by decide)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem AD_commute_right : Commute (chords j 0) (chords j 5) := by
  have h := congrArg j (GenericBraid.t_disjoint (R:=ℝ) (0:Fin 4) 1 2 3
    (by decide) (by decide) (by decide) (by decide))
  rw [j.map_lie,map_zero] at h
  exact sub_eq_zero.mp h

def ADtransport (s : ℝ) : A :=
  transport (ADBoundary.movedPole (chords j 1+chords j 3) (chords j 5) (chords j 3) (s^2))
    s F.cutoff (ADBoundary.endpoint s)

include hc in
theorem AD_model_limit : Tendsto (fun s => inverseModel j 3 s*ADtransport F j s*model j 0 s)
    (𝓝[>] 0) (𝓝 (associator F (chords j 1+chords j 3) (chords j 5))) := by
  have hl := ADBoundary.limit F (chords j 3)
    ((F.space 1).add_mem (hc 1) (hc 3)) (hc 5)
    ((F.space 1).add_mem (hc 0) (hc 0))
    ((AD_commute_left j).add_left (AD_commute_left j))
    ((AD_commute_right j).add_left (AD_commute_right j))
  convert! hl using 1
  funext s
  change KZCollar.gauge (-(2 • chords j 0+2 • chords j 5)) s*ADtransport F j s*
    KZCollar.gauge (2 • chords j 0+chords j 1+chords j 3) s=
    KZCollar.gauge (-((chords j 0+chords j 0)+(chords j 5+chords j 5))) s*ADtransport F j s*
    KZCollar.gauge ((chords j 0+chords j 0)+(chords j 1+chords j 3)) s
  simp only [two_smul ℕ,add_assoc]

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem AD_form (s t : ℝ) :
    FourCollar.form (chords j 0) (chords j 1) (chords j 3) (chords j 4) (chords j 5)
      (s^2) t 0 1=ADBoundary.movedPole (chords j 1+chords j 3) (chords j 5) (chords j 3) (s^2) t := by
  simp only [FourCollar.form,ADBoundary.movedPole,bulkForm,one_div,sub_zero,zero_div,zero_smul,zero_add,add_zero,
    smul_add,sub_smul]
  abel

include hc in
theorem AD_transport_eq {p : Fin 4 → ℝ} (hp : StrictMono p) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    ADtransport F j s=fundamental F j p (path 3 s)*Ring.inverse (fundamental F j p (path 0 s)) := by
  let q : ℝ → Fin 4 → ℝ := fun t => point (s^2) t
  let q' : ℝ → Fin 4 → ℝ := fun _ => speed 0 1
  have hb := ADBoundary.bounds ⟨hs.1,hs.2.le⟩
  have hq (t : ℝ) (ht : t∈Icc s (ADBoundary.endpoint s)) : StrictMono (q t) := by
    apply point_strictMono
    exact ⟨sq_pos_of_pos hs.1,by nlinarith [hb.2.2,ht.1,hs.1],ht.2.trans_lt hb.2.1⟩
  have hqc (i : Fin 4) : ContinuousOn (fun t => q t i) (Icc s (ADBoundary.endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact continuousOn_const
    · exact continuousOn_id
    · exact continuousOn_const
  have hqc' (i : Fin 4) : ContinuousOn (fun t => q' t i) (Icc s (ADBoundary.endpoint s)) := continuousOn_const
  have hqd (t : ℝ) (_ : t∈Ioo s (ADBoundary.endpoint s)) (i : Fin 4) : HasDerivAt (fun t => q t i) (q' t i) t := by
    fin_cases i
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_id _
    · exact hasDerivAt_const _ _
  have ht := transport_eq_ratio F j hc hb.1 hp hq hqc hqc' hqd
  have hform : (fun t => j (KZFlat.connection (q t) (q' t)))=
      ADBoundary.movedPole (chords j 1+chords j 3) (chords j 5) (chords j 3) (s^2) := by
    funext t
    rw [show q t=point (s^2) t from rfl,show q' t=speed 0 1 from rfl,FourFrames.form_eq,AD_form]
  rw [hform] at ht
  exact ht

include hc in
theorem AD_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 3)*corner F j p 0=
      associator F (chords j 1+chords j 3) (chords j 5) := by
  apply corner_eq_of_limit F j hc hp 0 3
    (ADBoundary.transport_subpower _ _ _ F.cutoff) _ (AD_model_limit F j hc)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact ⟨hs,AD_transport_eq F j hc hp hs⟩

end FourFrames

namespace ABBoundary

section
open Set Filter
open scoped Topology

def endpoint (s : ℝ) : ℝ := (1+s)⁻¹
def slope (s : ℝ) : ℝ := s^2/(endpoint s-s)
def scale (s t : ℝ) : ℝ := s+slope s*(t-s)
def scaleV (s t : ℝ) : ℝ := scale s t+t*slope s

theorem endpoint_bounds {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    1/2 ≤ endpoint s-s ∧ endpoint s<1 ∧ s<endpoint s := by
  have hp : 0<1+s := by linarith [hs.1]
  have hlo : 3/4 ≤ endpoint s := by
    rw [endpoint,←one_div]
    rw [le_div_iff₀ hp]
    nlinarith [hs.2]
  have hup : endpoint s<1 := by
    rw [endpoint,inv_lt_one₀ hp]
    linarith [hs.1]
  exact ⟨by linarith [hs.2],hup,by linarith [hs.2]⟩

theorem slope_bounds {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    0≤ slope s ∧ slope s≤ 2*s^2 := by
  have hb := endpoint_bounds hs
  have hp : 0<endpoint s-s := by linarith [hb.1]
  constructor
  · exact div_nonneg (sq_nonneg _) hp.le
  · rw [slope,div_le_iff₀ hp]
    nlinarith [sq_nonneg s]

theorem scale_start (s : ℝ) : scale s s=s := by simp [scale]

theorem scale_end {s : ℝ} (hs : s∈Ioc 0 (1/4)) : scale s (endpoint s)=s+s^2 := by
  unfold scale slope
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (endpoint_bounds hs).2.2.ne')]

theorem endpoint_mul_scale {s : ℝ} (hs : s∈Ioc 0 (1/4)) : endpoint s*scale s (endpoint s)=s := by
  rw [scale_end hs,endpoint]
  have h : 1+s≠0 := by linarith [hs.1]
  field_simp

theorem scale_bounds {s t : ℝ} (hs : s∈Ioc 0 (1/4)) (ht : t∈Icc s (endpoint s)) :
    s≤ scale s t ∧ scale s t≤ s+s^2 ∧ scale s t≤ 1/2 ∧ 0≤ t ∧ t≤ 1 := by
  have hc := slope_bounds hs
  have hlow : s≤ scale s t := le_add_of_nonneg_right (mul_nonneg hc.1 (sub_nonneg.mpr ht.1))
  have hhigh : scale s t≤ s+s^2 := by
    rw [←scale_end hs]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 s) hc.1)
  have hsq : s^2≤ 1/16 := by nlinarith [hs.1,hs.2,sq_nonneg (s-1/4)]
  exact ⟨hlow,hhigh,by linarith [hs.2],hs.1.le.trans ht.1,ht.2.trans (endpoint_bounds hs).2.1.le⟩

theorem velocity_bounds {s t : ℝ} (hs : s∈Ioc 0 (1/4)) (ht : t∈Icc s (endpoint s)) :
    0≤ scaleV s t ∧ scaleV s t≤ 2*s := by
  have hb := scale_bounds hs ht
  have hc := slope_bounds hs
  unfold scaleV
  constructor
  · exact add_nonneg (hs.1.le.trans hb.1) (mul_nonneg hb.2.2.2.1 hc.1)
  · have hm := mul_le_mul_of_nonneg_right hb.2.2.2.2 hc.1
    nlinarith [hs.1,hs.2]

theorem coefficient_bounds {s t : ℝ} (hs : s∈Ioc 0 (1/4)) (ht : t∈Icc s (endpoint s)) :
    |slope s/scale s t|≤ 2*s ∧ |scaleV s t/(t*scale s t-1)|≤ 4*s ∧
    |slope s/(scale s t-1)|≤ 4*s := by
  have hb := scale_bounds hs ht
  have hc := slope_bounds hs
  have hv := velocity_bounds hs ht
  have hy : 0<scale s t := hs.1.trans_le hb.1
  have hxy : t*scale s t≤ 1/2 := (mul_le_of_le_one_left hy.le hb.2.2.2.2).trans hb.2.2.1
  constructor
  · rw [abs_of_nonneg (div_nonneg hc.1 hy.le),div_le_iff₀ hy]
    nlinarith [mul_le_mul_of_nonneg_left hb.1 hs.1.le]
  constructor
  · rw [abs_div,abs_of_nonneg hv.1,abs_of_nonpos (by linarith : t*scale s t-1≤ 0)]
    rw [div_le_iff₀ (by linarith : 0< -(t*scale s t-1))]
    nlinarith [mul_le_mul_of_nonneg_left hxy hs.1.le]
  · rw [abs_div,abs_of_nonneg hc.1,abs_of_nonpos (by linarith [hb.2.2.1] : scale s t-1≤ 0)]
    rw [div_le_iff₀ (by linarith [hb.2.2.1] : 0< -(scale s t-1))]
    nlinarith [mul_le_mul_of_nonneg_left hb.2.2.1 hs.1.le,hs.2,hs.1]

theorem chamber {s t : ℝ} (hs : s∈Ioc 0 (1/4)) (ht : t∈Icc s (endpoint s)) :
    0<t*scale s t ∧ t*scale s t<scale s t ∧ scale s t<1 := by
  have hb := scale_bounds hs ht
  have hy := hs.1.trans_le hb.1
  exact ⟨mul_pos (hs.1.trans_le ht.1) hy,mul_lt_of_lt_one_left hy (ht.2.trans_lt (endpoint_bounds hs).2.1),
    lt_of_le_of_lt hb.2.2.1 (by norm_num)⟩

theorem scale_deriv (s t : ℝ) : HasDerivAt (scale s) (slope s) t := by
  simpa only [scale,id_eq,mul_one] using! ((hasDerivAt_id t).sub_const s).const_mul (slope s) |>.const_add s

theorem x_deriv (s t : ℝ) : HasDerivAt (fun t => t*scale s t) (scaleV s t) t := by
  simpa only [scaleV,Pi.mul_apply,id_eq,one_mul] using! (hasDerivAt_id t).mul (scale_deriv s t)

theorem scale_continuous (s : ℝ) : Continuous (scale s) :=
  continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))

theorem form_eq {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (a b d e f : A) {s t : ℝ} (hs : s∈Ioc 0 (1/4)) (ht : t∈Icc s (endpoint s)) :
    FourCollar.form a b d e f (t*scale s t) (scale s t) (scaleV s t) (slope s)=
      KZCollar.bulkForm a d t+(slope s/scale s t) • (a+b+d)+
        (scaleV s t/(t*scale s t-1)) • e+(slope s/(scale s t-1)) • f := by
  have hb := scale_bounds hs ht
  have ht0 : t≠0 := ne_of_gt (hs.1.trans_le ht.1)
  have hy : scale s t≠0 := ne_of_gt (hs.1.trans_le hb.1)
  have ht1 : t-1≠0 := ne_of_lt (sub_neg.mpr (ht.2.trans_lt (endpoint_bounds hs).2.1))
  have hxy : scale s t-t*scale s t≠0 := ne_of_gt (sub_pos.mpr (chamber hs ht).2.1)
  have h1t : 1-t≠0 := ne_of_gt (sub_pos.mpr (ht.2.trans_lt (endpoint_bounds hs).2.1))
  unfold FourCollar.form KZCollar.bulkForm scaleV
  match_scalars <;> field_simp [ht0,hy,ht1,hxy,h1t]
  ring

end

section
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def error (S E V : A) (s t : ℝ) : A :=
  (slope s/scale s t) • S+(scaleV s t/(t*scale s t-1)) • E+(slope s/(scale s t-1)) • V

def edgeForm (X Y S E V : A) (s t : ℝ) : A := bulkForm X Y t+error S E V s t

def errorConst (S E V : A) : ℝ := 2*‖S‖+4*‖E‖+4*‖V‖

omit [NormedAlgebra ℝ A] in
theorem errorConst_nonneg (S E V : A) : 0 ≤ errorConst S E V := by unfold errorConst; positivity

theorem error_norm (S E V : A) {s t : ℝ} (hs : s∈Ioc 0 (1/4)) (ht : t∈Icc s (endpoint s)) :
    ‖error S E V s t‖ ≤ errorConst S E V*s := by
  have hb := coefficient_bounds hs ht
  calc
    _ ≤ ‖(slope s/scale s t) • S‖+‖(scaleV s t/(t*scale s t-1)) • E‖+‖(slope s/(scale s t-1)) • V‖ := norm_add₃_le
    _ ≤ (2*s)*‖S‖+(4*s)*‖E‖+(4*s)*‖V‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hb.1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hb.2.1 (norm_nonneg _)))
        (mul_le_mul_of_nonneg_right hb.2.2 (norm_nonneg _))
    _ = _ := by unfold errorConst; ring

theorem error_continuous (S E V : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    ContinuousOn (error S E V s) (Icc s (endpoint s)) := by
  have hy := (scale_continuous s).continuousOn (s:=Icc s (endpoint s))
  have hv : ContinuousOn (scaleV s) (Icc s (endpoint s)) := hy.add (continuousOn_id.mul continuousOn_const)
  have hm := (continuousOn_id.mul hy).sub (continuousOn_const (c:=(1:ℝ)))
  have hy0 : ∀ t∈Icc s (endpoint s),scale s t≠0 := fun t ht => ne_of_gt (hs.1.trans_le (scale_bounds hs ht).1)
  have hm0 : ∀ t∈Icc s (endpoint s),t*scale s t-1≠0 := fun t ht => ne_of_lt (by
    have h := chamber hs ht; linarith [h.2.1,h.2.2])
  have hy1 : ∀ t∈Icc s (endpoint s),scale s t-1≠0 := fun t ht => ne_of_lt (by linarith [(chamber hs ht).2.2])
  exact (((continuousOn_const.div hy hy0).smul continuousOn_const).add
    ((hv.div hm hm0).smul continuousOn_const)).add
      ((continuousOn_const.div (hy.sub continuousOn_const) hy1).smul continuousOn_const)

theorem bulk_continuous (X Y : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    ContinuousOn (bulkForm X Y) (Icc s (endpoint s)) :=
  (bulkForm_continuous X Y).mono (fun _ ht => ⟨hs.1.trans_le ht.1,ht.2.trans_lt (endpoint_bounds hs).2.1⟩)

theorem continuous (X Y S E V : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    ContinuousOn (edgeForm X Y S E V s) (Icc s (endpoint s)) :=
  (bulk_continuous X Y hs).add (error_continuous S E V hs)

theorem error_bound (X Y S E V : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    integralNorm (fun t => edgeForm X Y S E V s t-bulkForm X Y t) s (endpoint s) ≤ errorConst S E V*s := by
  simp only [edgeForm,add_sub_cancel_left]
  have hb := endpoint_bounds hs
  have hi : IntervalIntegrable (error S E V s) volume s (endpoint s) :=
    (error_continuous S E V hs).intervalIntegrable_of_Icc hb.2.2.le
  calc
    _ ≤ ∫ _ in s..endpoint s,errorConst S E V*s :=
      intervalIntegral.integral_mono_on hb.2.2.le hi.norm intervalIntegrable_const (fun t ht => error_norm S E V hs ht)
    _ = (endpoint s-s)*(errorConst S E V*s) := by rw [intervalIntegral.integral_const,smul_eq_mul]
    _ ≤ _ := mul_le_of_le_one_left (mul_nonneg (errorConst_nonneg S E V) hs.1.le)
      (by linarith [hb.2.1,hs.1])

def mass (X Y S E V : A) (s : ℝ) : ℝ :=
  (‖X‖+‖Y‖)*(-Real.log s)+‖Y‖*Real.log 2+errorConst S E V*s

theorem gap_eq {s : ℝ} (hs : 0<s) : 1-endpoint s=s/(1+s) := by
  unfold endpoint
  field_simp
  ring

theorem gap_bound {s : ℝ} (hs : s∈Ioc 0 (1/4)) : s/2 ≤ 1-endpoint s := by
  rw [gap_eq hs.1]
  have hp : 0<1+s := by linarith [hs.1]
  rw [le_div_iff₀ hp]
  nlinarith [hs.1,hs.2]

theorem bulk_bound (X Y : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    integralNorm (bulkForm X Y) s (endpoint s) ≤ (‖X‖+‖Y‖)*(-Real.log s)+‖Y‖*Real.log 2 := by
  have hb := endpoint_bounds hs
  have hl : -Real.log (1-endpoint s) ≤ -Real.log s+Real.log 2 := by
    have h := Real.log_le_log (by linarith [hs.1] : 0<s/2) (gap_bound hs)
    rw [Real.log_div hs.1.ne' (by norm_num)] at h
    linarith
  calc
    _ ≤ ‖X‖*(-Real.log s)+‖Y‖*(-Real.log (1-endpoint s)) := bulkForm_mass hs.1 hb.2.2.le hb.2.1
    _ ≤ ‖X‖*(-Real.log s)+‖Y‖*(-Real.log s+Real.log 2) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hl (norm_nonneg _))
    _ = _ := by ring

omit [NormedAlgebra ℝ A] in
theorem mass_subpower (X Y S E V : A) : Subpower (mass X Y S E V) := by
  have hl : Subpower (fun s : ℝ => -Real.log s) := by
    simpa only [pow_one,neg_one_mul] using (const_subpower (-1:ℝ)).mul (log_pow_subpower 1)
  exact (((const_subpower _).mul hl).add (const_subpower _)).add
    (continuousAt_subpower (continuousAt_const.mul continuousAt_id))

theorem estimates (X Y S E V : A) {s : ℝ} (hs : s∈Ioc 0 (1/4)) :
    s ≤ endpoint s ∧ IntervalIntegrable (edgeForm X Y S E V s) volume s (endpoint s) ∧
      IntervalIntegrable (bulkForm X Y) volume s (endpoint s) ∧ 0 ≤ mass X Y S E V s ∧
      0 ≤ errorConst S E V*s ∧ integralNorm (edgeForm X Y S E V s) s (endpoint s) ≤ mass X Y S E V s ∧
      integralNorm (bulkForm X Y) s (endpoint s) ≤ mass X Y S E V s ∧
      integralNorm (fun t => edgeForm X Y S E V s t-bulkForm X Y t) s (endpoint s) ≤ errorConst S E V*s := by
  have hb := endpoint_bounds hs
  have hiΩ : IntervalIntegrable (edgeForm X Y S E V s) volume s (endpoint s) := (continuous X Y S E V hs).intervalIntegrable_of_Icc hb.2.2.le
  have hiΘ : IntervalIntegrable (bulkForm X Y) volume s (endpoint s) := (bulk_continuous X Y hs).intervalIntegrable_of_Icc hb.2.2.le
  have hE : 0 ≤ errorConst S E V*s := mul_nonneg (errorConst_nonneg S E V) hs.1.le
  have hl : 0 ≤ -Real.log s := neg_nonneg.mpr (Real.log_nonpos hs.1.le (by linarith [hs.2]))
  have hL : 0 ≤ mass X Y S E V s := add_nonneg (add_nonneg (mul_nonneg (by positivity) hl)
    (mul_nonneg (norm_nonneg _) (Real.log_nonneg (by norm_num)))) hE
  have hΩ : integralNorm (edgeForm X Y S E V s) s (endpoint s) ≤ mass X Y S E V s := by
    have h := integralNorm_add_le hb.2.2.le hiΘ (hiΩ.sub hiΘ)
    have he : (fun t => bulkForm X Y t+(edgeForm X Y S E V s t-bulkForm X Y t))=edgeForm X Y S E V s := by funext t; abel
    rw [he] at h
    exact h.trans (add_le_add (bulk_bound X Y hs) (error_bound X Y S E V hs))
  exact ⟨hb.2.2.le,hiΩ,hiΘ,hL,hE,hΩ,(bulk_bound X Y hs).trans (le_add_of_nonneg_right hE),error_bound X Y S E V hs⟩

theorem perturbation (X Y S E V : A) (N : ℕ) :
    PowerSmall (fun s => transport (edgeForm X Y S E V s) s N (endpoint s)-transport (bulkForm X Y) s N (endpoint s)) := by
  apply transport_perturbation_powerSmall (L:=mass X Y S E V) (E:=fun s => errorConst S E V*s)
    _ (mass_subpower X Y S E V) (linear_powerSmall _) N
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact estimates X Y S E V hs

theorem transport_subpower (X Y S E V : A) (N : ℕ) :
    Subpower (fun s => transport (edgeForm X Y S E V s) s N (endpoint s)) := by
  apply PowerAsymptotic.transport_subpower (L:=mass X Y S E V) _ (mass_subpower X Y S E V) N
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  have h := estimates X Y S E V hs
  exact ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2.2.1⟩

end

open Set Filter FinitePicard KZCollar PowerAsymptotic
open scoped Topology

theorem gap_tendsto : Tendsto (fun s : ℝ => s/(1+s)) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [add_zero,zero_div] using! h.div (tendsto_const_nhds.add h) (by norm_num : (1:ℝ)+0≠0)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change 0<s at hs
    exact div_pos hs (by linarith)

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem bulk_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    Tendsto (fun s => gauge (-Y) s*transport (bulkForm X Y) s F.cutoff (endpoint s)*gauge X s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have h := (gauge_ratio_limit (-Y)).mul (regularizedBulk_two_limit F hX hY tendsto_id gap_tendsto)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 0<s at hs
  have hp : 0<1+s := by linarith
  have hg : gauge (-Y) (1+s)*gauge (-Y) (s/(1+s))=gauge (-Y) s := by
    rw [←gauge_mul_scale _ hp.ne' (ne_of_gt (div_pos hs hp)),mul_div_cancel₀ _ hp.ne']
  simp only [←mul_assoc]
  rw [hg,show 1-s/(1+s)=endpoint s by have he := gap_eq hs; linarith]
  rfl

theorem limit (F : NilpotentFiltration A) {X Y Z : A} (S E V : A)
    (hX : X∈F.space 1) (hY : Y∈F.space 1) (hZ : Z∈F.space 1)
    (hZX : Commute Z X) (hZY : Commute Z Y) :
    Tendsto (fun s => gauge (-(Y+Z)) s*transport (edgeForm X Y S E V s) s F.cutoff (endpoint s)*gauge (X+Z) s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have hl := normalized_perturbation_limit (perturbation X Y S E V F.cutoff)
    (gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).neg_mem ((F.space 1).add_mem hY hZ))))
    (gauge_subpower (pow_cutoff_eq_zero F ((F.space 1).add_mem hX hZ)))
  have he (s : ℝ) := BCBoundary.shared_residue_cancel (pow_cutoff_eq_zero F hZ) hZX hZY s (endpoint s) s
  have hb : Tendsto (fun s => gauge (-(Y+Z)) s*transport (bulkForm X Y) s F.cutoff (endpoint s)*gauge (X+Z) s)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := (bulk_limit F hX hY).congr (fun s => (he s).symm)
  simpa only [zero_add,sub_add_cancel] using! hl.add hb

end ABBoundary

namespace FourFrames

section
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
  KZRectangle StraightKZ
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem AB_commute_left : Commute (chords j 0+chords j 1+chords j 3) (chords j 0) := by
  rw [add_assoc]
  exact (Commute.refl _).add_left (AD_commute_left j).symm

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem AB_commute_right : Commute (chords j 0+chords j 1+chords j 3) (chords j 3) :=
  (BC_commute_left j).symm.add_left (Commute.refl _)

def ABtransport (s : ℝ) : A :=
  transport (ABBoundary.edgeForm (chords j 0) (chords j 3) (chords j 0+chords j 1+chords j 3)
    (chords j 4) (chords j 5) s) s F.cutoff (ABBoundary.endpoint s)

include hc in
theorem AB_model_limit : Tendsto (fun s => inverseModel j 1 s*ABtransport F j s*model j 0 s)
    (𝓝[>] 0) (𝓝 (associator F (chords j 0) (chords j 3))) := by
  have hl := ABBoundary.limit F (chords j 0+chords j 1+chords j 3) (chords j 4) (chords j 5)
    (hc 0) (hc 3) ((F.space 1).add_mem ((F.space 1).add_mem (hc 0) (hc 1)) (hc 3))
    (AB_commute_left j) (AB_commute_right j)
  convert! hl using 1
  funext s
  change KZCollar.gauge (-(chords j 0+chords j 1+2 • chords j 3)) s*ABtransport F j s*
    KZCollar.gauge (2 • chords j 0+chords j 1+chords j 3) s=
    KZCollar.gauge (-(chords j 3+(chords j 0+chords j 1+chords j 3))) s*ABtransport F j s*
    KZCollar.gauge (chords j 0+(chords j 0+chords j 1+chords j 3)) s
  rw [two_smul ℕ,two_smul ℕ,show chords j 0+chords j 1+(chords j 3+chords j 3)=
    chords j 3+(chords j 0+chords j 1+chords j 3) by abel]
  simp only [add_assoc]

include hc in
theorem AB_transport_eq {p : Fin 4 → ℝ} (hp : StrictMono p) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    ABtransport F j s=fundamental F j p (path 1 s)*Ring.inverse (fundamental F j p (path 0 s)) := by
  let q : ℝ → Fin 4 → ℝ := fun t => point (t*ABBoundary.scale s t) (ABBoundary.scale s t)
  let q' : ℝ → Fin 4 → ℝ := fun t => speed (ABBoundary.scaleV s t) (ABBoundary.slope s)
  have hb := ABBoundary.endpoint_bounds ⟨hs.1,hs.2.le⟩
  have hq (t : ℝ) (ht : t∈Icc s (ABBoundary.endpoint s)) : StrictMono (q t) :=
    point_strictMono (ABBoundary.chamber ⟨hs.1,hs.2.le⟩ ht)
  have hqc (i : Fin 4) : ContinuousOn (fun t => q t i) (Icc s (ABBoundary.endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact (continuous_id.mul (ABBoundary.scale_continuous s)).continuousOn
    · exact (ABBoundary.scale_continuous s).continuousOn
    · exact continuousOn_const
  have hqc' (i : Fin 4) : ContinuousOn (fun t => q' t i) (Icc s (ABBoundary.endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact ((ABBoundary.scale_continuous s).add (continuous_id.mul continuous_const)).continuousOn
    · exact continuousOn_const
    · exact continuousOn_const
  have hqd (t : ℝ) (_ : t∈Ioo s (ABBoundary.endpoint s)) (i : Fin 4) : HasDerivAt (fun t => q t i) (q' t i) t := by
    fin_cases i
    · exact hasDerivAt_const _ _
    · exact ABBoundary.x_deriv s t
    · exact ABBoundary.scale_deriv s t
    · exact hasDerivAt_const _ _
  have ht := transport_eq_ratio F j hc hb.2.2 hp hq hqc hqc' hqd
  have hform : Set.EqOn (fun t => j (KZFlat.connection (q t) (q' t)))
      (ABBoundary.edgeForm (chords j 0) (chords j 3) (chords j 0+chords j 1+chords j 3)
        (chords j 4) (chords j 5) s) (Icc s (ABBoundary.endpoint s)) := by
    intro t hti
    dsimp only
    rw [show q t=point (t*ABBoundary.scale s t) (ABBoundary.scale s t) from rfl,
      show q' t=speed (ABBoundary.scaleV s t) (ABBoundary.slope s) from rfl,FourFrames.form_eq,
      ABBoundary.form_eq _ _ _ _ _ ⟨hs.1,hs.2.le⟩ hti]
    simp only [ABBoundary.edgeForm,ABBoundary.error,add_assoc]
  have he := transport_congr (a:=s) (b:=ABBoundary.endpoint s) (by simpa only [uIcc_of_le hb.2.2.le] using hform) F.cutoff
  rw [he] at ht
  have hqb : q (ABBoundary.endpoint s)=path 1 s := by
    funext i
    fin_cases i <;> simp [q,path,point,FourCollar.cx,FourCollar.cy,ABBoundary.scale_end ⟨hs.1,hs.2.le⟩]
    have he := ABBoundary.endpoint_mul_scale ⟨hs.1,hs.2.le⟩
    rw [ABBoundary.scale_end ⟨hs.1,hs.2.le⟩] at he
    exact he
  have hqa : q s=path 0 s := by
    funext i
    fin_cases i <;> simp [q,path,point,FourCollar.cx,FourCollar.cy,ABBoundary.scale_start,pow_two]
  rw [hqa,hqb] at ht
  exact ht

include hc in
theorem AB_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 1)*corner F j p 0=associator F (chords j 0) (chords j 3) := by
  apply corner_eq_of_limit F j hc hp 0 1
    (ABBoundary.transport_subpower _ _ _ _ _ F.cutoff) _ (AB_model_limit F j hc)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact ⟨hs,AB_transport_eq F j hc hp hs⟩

end

section
open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
  KZRectangle StraightKZ
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem ED_commute_left : Commute (chords j 5) (chords j 4+chords j 3) := by
  have h := chord_triple j 2 3 1 (by decide) (by decide) (by decide)
  rw [GenericBraid.t_comm 2 1,GenericBraid.t_comm 3 1,add_comm] at h
  exact h

def EDtransport (s : ℝ) : A :=
  transport (ADBoundary.movedPole (chords j 4+chords j 3) (chords j 0) (chords j 3) (s^2))
    s F.cutoff (ADBoundary.endpoint s)

include hc in
theorem ED_model_limit : Tendsto (fun s => inverseModel j 3 s*EDtransport F j s*model j 4 s)
    (𝓝[>] 0) (𝓝 (associator F (chords j 4+chords j 3) (chords j 0))) := by
  have hl := ADBoundary.limit F (chords j 3)
    ((F.space 1).add_mem (hc 4) (hc 3)) (hc 0)
    ((F.space 1).add_mem (hc 5) (hc 5))
    ((ED_commute_left j).add_left (ED_commute_left j))
    ((AD_commute_right j).symm.add_left (AD_commute_right j).symm)
  convert! hl using 1
  funext s
  change KZCollar.gauge (-(2 • chords j 0+2 • chords j 5)) s*EDtransport F j s*
    KZCollar.gauge (2 • chords j 5+chords j 4+chords j 3) s=
    KZCollar.gauge (-((chords j 5+chords j 5)+(chords j 0+chords j 0))) s*EDtransport F j s*
    KZCollar.gauge ((chords j 5+chords j 5)+(chords j 4+chords j 3)) s
  rw [add_comm (2 • chords j 0) (2 • chords j 5)]
  simp only [two_smul ℕ,add_assoc]

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem ED_form (s t : ℝ) :
    FourCollar.form (chords j 0) (chords j 1) (chords j 3) (chords j 4) (chords j 5)
      (1-t) (1-s^2) (-1) 0=
      ADBoundary.movedPole (chords j 4+chords j 3) (chords j 0) (chords j 3) (s^2) t := by
  unfold FourCollar.form ADBoundary.movedPole bulkForm
  rw [show 1-s^2-(1-t)=t-s^2 by ring,show 1-t-1= -t by ring,
    show 1-t= -(t-1) by ring]
  simp only [zero_div,zero_smul,add_zero,zero_sub,neg_neg,neg_div_neg_eq,one_div,
    smul_add,sub_smul]
  abel

include hc in
theorem ED_transport_eq {p : Fin 4 → ℝ} (hp : StrictMono p) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    EDtransport F j s=fundamental F j p (path 3 s)*Ring.inverse (fundamental F j p (path 4 s)) := by
  let q : ℝ → Fin 4 → ℝ := fun t => point (1-t) (1-s^2)
  let q' : ℝ → Fin 4 → ℝ := fun _ => speed (-1) 0
  have hb := ADBoundary.bounds ⟨hs.1,hs.2.le⟩
  have hq (t : ℝ) (ht : t∈Icc s (ADBoundary.endpoint s)) : StrictMono (q t) := by
    apply point_strictMono
    exact ⟨by linarith [ht.2.trans_lt hb.2.1],by nlinarith [hb.2.2,ht.1,hs.1],by nlinarith [sq_pos_of_pos hs.1]⟩
  have hqc (i : Fin 4) : ContinuousOn (fun t => q t i) (Icc s (ADBoundary.endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact continuousOn_const.sub continuousOn_id
    · exact continuousOn_const
    · exact continuousOn_const
  have hqc' (i : Fin 4) : ContinuousOn (fun t => q' t i) (Icc s (ADBoundary.endpoint s)) := continuousOn_const
  have hqd (t : ℝ) (_ : t∈Ioo s (ADBoundary.endpoint s)) (i : Fin 4) : HasDerivAt (fun t => q t i) (q' t i) t := by
    fin_cases i
    · exact hasDerivAt_const _ _
    · change HasDerivAt (fun t : ℝ => 1-t) (-1) t
      simpa only [Pi.sub_apply,id_eq,zero_sub] using! (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
    · exact hasDerivAt_const _ _
    · exact hasDerivAt_const _ _
  have ht := transport_eq_ratio F j hc hb.1 hp hq hqc hqc' hqd
  have hform : (fun t => j (KZFlat.connection (q t) (q' t)))=
      ADBoundary.movedPole (chords j 4+chords j 3) (chords j 0) (chords j 3) (s^2) := by
    funext t
    rw [show q t=point (1-t) (1-s^2) from rfl,show q' t=speed (-1) 0 from rfl,FourFrames.form_eq,ED_form]
  rw [hform] at ht
  have hqb : q (ADBoundary.endpoint s)=path 3 s := by
    funext i
    fin_cases i <;> simp [q,path,point,FourCollar.cx,FourCollar.cy,ADBoundary.endpoint]
  rw [hqb] at ht
  exact ht

include hc in
theorem ED_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 3)*corner F j p 4=
      associator F (chords j 4+chords j 3) (chords j 0) := by
  apply corner_eq_of_limit F j hc hp 4 3
    (ADBoundary.transport_subpower _ _ _ F.cutoff) _ (ED_model_limit F j hc)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact ⟨hs,ED_transport_eq F j hc hp hs⟩

end

open MeasureTheory Set Filter FinitePicard KZCollar PowerAsymptotic PoleEstimate
  KZRectangle StraightKZ
open scoped Topology
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem EC_commute_left : Commute (chords j 5+chords j 4+chords j 3) (chords j 5) := by
  rw [add_assoc]
  exact (Commute.refl _).add_left (ED_commute_left j).symm

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem EC_commute_right : Commute (chords j 5+chords j 4+chords j 3) (chords j 3) := by
  rw [add_comm (chords j 5) (chords j 4)]
  exact (BC_commute_right j).symm.add_left (Commute.refl _)

def ECtransport (s : ℝ) : A :=
  transport (ABBoundary.edgeForm (chords j 5) (chords j 3) (chords j 5+chords j 4+chords j 3)
    (chords j 1) (chords j 0) s) s F.cutoff (ABBoundary.endpoint s)

include hc in
theorem EC_model_limit : Tendsto (fun s => inverseModel j 2 s*ECtransport F j s*model j 4 s)
    (𝓝[>] 0) (𝓝 (associator F (chords j 5) (chords j 3))) := by
  have hl := ABBoundary.limit F (chords j 5+chords j 4+chords j 3) (chords j 1) (chords j 0)
    (hc 5) (hc 3) ((F.space 1).add_mem ((F.space 1).add_mem (hc 5) (hc 4)) (hc 3))
    (EC_commute_left j) (EC_commute_right j)
  convert! hl using 1
  funext s
  change KZCollar.gauge (-(chords j 5+chords j 4+2 • chords j 3)) s*ECtransport F j s*
    KZCollar.gauge (2 • chords j 5+chords j 4+chords j 3) s=
    KZCollar.gauge (-(chords j 3+(chords j 5+chords j 4+chords j 3))) s*ECtransport F j s*
    KZCollar.gauge (chords j 5+(chords j 5+chords j 4+chords j 3)) s
  rw [two_smul ℕ,two_smul ℕ,show chords j 5+chords j 4+(chords j 3+chords j 3)=
    chords j 3+(chords j 5+chords j 4+chords j 3) by abel]
  simp only [add_assoc]

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem form_reflection (a b d e f : A) (x y vx vy : ℝ) :
    FourCollar.form a b d e f (1-y) (1-x) (-vy) (-vx)=FourCollar.form f e d b a x y vx vy := by
  unfold FourCollar.form
  rw [show (1-x)-(1-y)=y-x by ring,show -vx- -vy=vy-vx by ring,
    show 1-y-1= -y by ring,show 1-x-1= -x by ring,
    show 1-y= -(y-1) by ring,show 1-x= -(x-1) by ring]
  simp only [neg_div_neg_eq]
  abel

include hc in
theorem EC_transport_eq {p : Fin 4 → ℝ} (hp : StrictMono p) {s : ℝ} (hs : s∈Ioo 0 (1/4)) :
    ECtransport F j s=fundamental F j p (path 2 s)*Ring.inverse (fundamental F j p (path 4 s)) := by
  let q : ℝ → Fin 4 → ℝ := fun t => point (1-ABBoundary.scale s t) (1-t*ABBoundary.scale s t)
  let q' : ℝ → Fin 4 → ℝ := fun t => speed (-ABBoundary.slope s) (-ABBoundary.scaleV s t)
  have hb := ABBoundary.endpoint_bounds ⟨hs.1,hs.2.le⟩
  have hq (t : ℝ) (ht : t∈Icc s (ABBoundary.endpoint s)) : StrictMono (q t) := by
    apply point_strictMono
    have hg := ABBoundary.chamber ⟨hs.1,hs.2.le⟩ ht
    exact ⟨by linarith [hg.2.2],by linarith [hg.2.1],by linarith [hg.1]⟩
  have hqc (i : Fin 4) : ContinuousOn (fun t => q t i) (Icc s (ABBoundary.endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact (continuous_const.sub (ABBoundary.scale_continuous s)).continuousOn
    · exact (continuous_const.sub (continuous_id.mul (ABBoundary.scale_continuous s))).continuousOn
    · exact continuousOn_const
  have hqc' (i : Fin 4) : ContinuousOn (fun t => q' t i) (Icc s (ABBoundary.endpoint s)) := by
    fin_cases i
    · exact continuousOn_const
    · exact continuousOn_const
    · exact (((ABBoundary.scale_continuous s).add (continuous_id.mul continuous_const)).neg).continuousOn
    · exact continuousOn_const
  have hqd (t : ℝ) (_ : t∈Ioo s (ABBoundary.endpoint s)) (i : Fin 4) : HasDerivAt (fun t => q t i) (q' t i) t := by
    fin_cases i
    · exact hasDerivAt_const _ _
    · change HasDerivAt (fun t => 1-ABBoundary.scale s t) (-ABBoundary.slope s) t
      simpa only [Pi.sub_apply,zero_sub] using! (hasDerivAt_const t (1:ℝ)).sub (ABBoundary.scale_deriv s t)
    · change HasDerivAt (fun t => 1-t*ABBoundary.scale s t) (-ABBoundary.scaleV s t) t
      simpa only [Pi.sub_apply,zero_sub] using! (hasDerivAt_const t (1:ℝ)).sub (ABBoundary.x_deriv s t)
    · exact hasDerivAt_const _ _
  have ht := transport_eq_ratio F j hc hb.2.2 hp hq hqc hqc' hqd
  have hform : Set.EqOn (fun t => j (KZFlat.connection (q t) (q' t)))
      (ABBoundary.edgeForm (chords j 5) (chords j 3) (chords j 5+chords j 4+chords j 3)
        (chords j 1) (chords j 0) s) (Icc s (ABBoundary.endpoint s)) := by
    intro t hti
    dsimp only
    rw [show q t=point (1-ABBoundary.scale s t) (1-t*ABBoundary.scale s t) from rfl,
      show q' t=speed (-ABBoundary.slope s) (-ABBoundary.scaleV s t) from rfl,FourFrames.form_eq,form_reflection,
      ABBoundary.form_eq _ _ _ _ _ ⟨hs.1,hs.2.le⟩ hti]
    simp only [ABBoundary.edgeForm,ABBoundary.error,add_assoc]
  have he := transport_congr (a:=s) (b:=ABBoundary.endpoint s) (by simpa only [uIcc_of_le hb.2.2.le] using hform) F.cutoff
  rw [he] at ht
  have hqb : q (ABBoundary.endpoint s)=path 2 s := by
    funext i
    fin_cases i <;> simp [q,path,point,FourCollar.cx,FourCollar.cy,ABBoundary.scale_end ⟨hs.1,hs.2.le⟩,sub_add_eq_sub_sub]
    have he := ABBoundary.endpoint_mul_scale ⟨hs.1,hs.2.le⟩
    rw [ABBoundary.scale_end ⟨hs.1,hs.2.le⟩] at he
    exact he
  have hqa : q s=path 4 s := by
    funext i
    fin_cases i <;> simp [q,path,point,FourCollar.cx,FourCollar.cy,ABBoundary.scale_start,pow_two]
  rw [hqa,hqb] at ht
  exact ht

include hc in
theorem EC_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 2)*corner F j p 4=associator F (chords j 5) (chords j 3) := by
  apply corner_eq_of_limit F j hc hp 4 2
    (ABBoundary.transport_subpower _ _ _ _ _ F.cutoff) _ (EC_model_limit F j hc)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/4)] with s hs
  exact ⟨hs,EC_transport_eq F j hc hp hs⟩

end FourFrames

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld.FourFrames
open FinitePicard KZCollar KZRectangle StraightKZ
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

include hc in
theorem corner_reverse (p : Fin 4 → ℝ) (k l : Fin 5) :
    Ring.inverse (Ring.inverse (corner F j p k)*corner F j p l)=
      Ring.inverse (corner F j p l)*corner F j p k := by
  rw [Ring.inverse_mul (Or.inr (corner_isUnit F j hc p l)),
    Ring.inverse_inverse (corner_isUnit F j hc p k)]

include hc in
theorem DE_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 4)*corner F j p 3=
      associator F (chords j 0) (chords j 3+chords j 4) := by
  rw [←corner_reverse F j hc p 3 4,ED_insertion F j hc hp,add_comm (chords j 4),
    associator_swap F (hc 0) ((F.space 1).add_mem (hc 3) (hc 4)),
    Ring.inverse_inverse (associator_isUnit F (hc 0) ((F.space 1).add_mem (hc 3) (hc 4)))]

include hc in
theorem CE_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 4)*corner F j p 2=associator F (chords j 3) (chords j 5) := by
  rw [←corner_reverse F j hc p 2 4,EC_insertion F j hc hp,
    associator_swap F (hc 3) (hc 5),Ring.inverse_inverse (associator_isUnit F (hc 3) (hc 5))]

include hc in

theorem associator_pentagon_oai :
    associator F (chords j 0) (chords j 3+chords j 4)*
      associator F (chords j 1+chords j 3) (chords j 5)=
    associator F (chords j 3) (chords j 5)*
      associator F (chords j 0+chords j 1) (chords j 4+chords j 5)*
        associator F (chords j 0) (chords j 3) := by
  let p : Fin 4 → ℝ := fun i => (i:ℕ)
  have hp : StrictMono p := by
    intro i k hik
    change ((i:ℕ):ℝ)<((k:ℕ):ℝ)
    exact_mod_cast hik
  rw [←DE_insertion F j hc hp,←AD_insertion F j hc hp,←CE_insertion F j hc hp,
    ←BC_insertion F j hc hp,←AB_insertion F j hc hp,
    corner_cocycle F j hc p 4 3 0,corner_cocycle F j hc p 4 2 1,
    corner_cocycle F j hc p 4 1 0]

end DeligneDrinfeld.FourFrames

section

end

end

end OAI

end





universe u_1
section
open OAI.DeligneDrinfeld.FourFrames in
attribute [local instance] LieRing.ofAssociativeRing in
theorem solution : ∀ {A : Type u_1} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] [FiniteDimensional ℝ A] (F : OAI.DeligneDrinfeld.FinitePicard.NilpotentFiltration A)
    (j : OAI.DeligneDrinfeld.GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
    (hc : ∀ (i : Fin 6), OAI.DeligneDrinfeld.KZRectangle.chords j i ∈ F.space 1),
    OAI.DeligneDrinfeld.KZCollar.associator F (OAI.DeligneDrinfeld.KZRectangle.chords j 0)
          (OAI.DeligneDrinfeld.KZRectangle.chords j 3 + OAI.DeligneDrinfeld.KZRectangle.chords j 4) *
        OAI.DeligneDrinfeld.KZCollar.associator F
          (OAI.DeligneDrinfeld.KZRectangle.chords j 1 + OAI.DeligneDrinfeld.KZRectangle.chords j 3)
          (OAI.DeligneDrinfeld.KZRectangle.chords j 5) =
      OAI.DeligneDrinfeld.KZCollar.associator F (OAI.DeligneDrinfeld.KZRectangle.chords j 3)
            (OAI.DeligneDrinfeld.KZRectangle.chords j 5) *
          OAI.DeligneDrinfeld.KZCollar.associator F
            (OAI.DeligneDrinfeld.KZRectangle.chords j 0 + OAI.DeligneDrinfeld.KZRectangle.chords j 1)
            (OAI.DeligneDrinfeld.KZRectangle.chords j 4 + OAI.DeligneDrinfeld.KZRectangle.chords j 5) *
        OAI.DeligneDrinfeld.KZCollar.associator F (OAI.DeligneDrinfeld.KZRectangle.chords j 0)
          (OAI.DeligneDrinfeld.KZRectangle.chords j 3) :=
  @OAI.DeligneDrinfeld.FourFrames.associator_pentagon_oai
end
