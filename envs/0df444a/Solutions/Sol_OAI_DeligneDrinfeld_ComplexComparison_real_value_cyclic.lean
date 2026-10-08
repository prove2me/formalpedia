-- Prove2me | solution 1 for OAI.DeligneDrinfeld.ComplexComparison.real_value_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:54:14.834385+00:00
-- url     : https://prove2.me/submissions/dd73f98c-2a25-48c3-b114-db1e26f6f7dd

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldBraid

set_option linter.all false





section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
namespace FiniteAlgebraNorm
open scoped Matrix.Norms.Operator
variable (A : Type*) [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]

variable (K A : Type*) [RCLike K] [Ring A] [Algebra K A] [FiniteDimensional K A]

abbrev normedRingOver : NormedRing A :=
  NormedRing.induced A (Matrix (Fin (Module.finrank K A)) (Fin (Module.finrank K A)) K)
    (Algebra.leftMulMatrix (Module.finBasis K A))
    (Algebra.leftMulMatrix_injective (Module.finBasis K A))

abbrev normedAlgebraOver : @NormedAlgebra K A _ (normedRingOver K A).toSeminormedRing :=
  NormedAlgebra.induced K A (Matrix (Fin (Module.finrank K A)) (Fin (Module.finrank K A)) K)
    (Algebra.leftMulMatrix (Module.finBasis K A))

end FiniteAlgebraNorm

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
open MeasureTheory Set intervalIntegral
variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedRing B] [NormedAlgebra ℝ B]
variable [FiniteDimensional ℝ A] [CompleteSpace B]

theorem map_term (f : A →ₐ[ℝ] B) {Ω : ℝ → A} {a b : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (N : ℕ) {t : ℝ} (ht : t ∈ uIcc a b) :
    f (term Ω a N t)=term (fun s => f (Ω s)) a N t := by
  induction N generalizing t with
  | zero => simp
  | succ N ih =>
    rw [term_succ,term_succ]
    let fc := f.toLinearMap.toContinuousLinearMap
    have hi' : IntervalIntegrable (fun s => Ω s * term Ω a N s) volume a t :=
      (hi.mul_continuousOn (continuousOn_term hi N)).mono_set (uIcc_subset_uIcc_left ht)
    change fc (∫ s in a..t, Ω s * term Ω a N s)=_
    rw [←fc.intervalIntegral_comp_comm hi']
    apply intervalIntegral.integral_congr
    intro s hs
    have hst : s ∈ uIcc a b := uIcc_subset_uIcc_left ht hs
    change f (Ω s*term Ω a N s)=f (Ω s)*term (fun s => f (Ω s)) a N s
    rw [map_mul,ih hst]

theorem map_transport (f : A →ₐ[ℝ] B) {Ω : ℝ → A} {a b : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (N : ℕ) {t : ℝ} (ht : t ∈ uIcc a b) :
    f (transport Ω a N t)=transport (fun s => f (Ω s)) a N t := by
  simp only [transport,map_sum]
  exact Finset.sum_congr rfl (fun n _ => map_term f hi n ht)

end FinitePicard

namespace KZCollar
open MeasureTheory Set Filter FinitePicard
variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedRing B] [NormedAlgebra ℝ B]

theorem map_gauge (f : A →ₐ[ℝ] B) (X : A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    f (gauge X s)=gauge (f X) s := by
  have hY : (f X)^(N+1)=0 := by rw [←map_pow,hX,map_zero]
  rw [gauge_finite X hX,gauge_finite (f X) hY]
  simp only [map_sum,map_smul,map_pow]

theorem map_regularForm (f : A →ₐ[ℝ] B) (X Y : A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    f (regularForm X Y s)=regularForm (f X) (f Y) s := by
  have hN : (-X)^(N+1)=0 := by rw [neg_pow,hX,mul_zero]
  simp only [regularForm,map_mul,map_smul,map_gauge f X hX,map_gauge f (-X) hN,map_neg]

variable [FiniteDimensional ℝ A] [CompleteSpace B]

theorem map_normalizedSolution (f : A →ₐ[ℝ] B)
    (F : NilpotentFiltration A) (G : NilpotentFiltration B) (hN : F.cutoff=G.cutoff)
    {X : A} (hX : X ∈ F.space 1) (Y : A) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    f (normalizedSolution F X Y s)=normalizedSolution G (f X) (f Y) s := by
  have hi := regularForm_integrable X Y (pow_cutoff_eq_zero F hX) hs hs1
  simp only [normalizedSolution,map_mul,map_gauge f X (pow_cutoff_eq_zero F hX)]
  rw [map_transport f hi F.cutoff right_mem_uIcc,hN]
  have hh : (fun s => f (regularForm X Y s))=regularForm (f X) (f Y) := by
    funext s
    exact map_regularForm f X Y (pow_cutoff_eq_zero F hX) s
  rw [hh]

omit [FiniteDimensional ℝ A] [CompleteSpace B] in
theorem map_unit_inverse (f : A →ₐ[ℝ] B) {x : A} (hx : IsUnit x) :
    f (Ring.inverse x)=Ring.inverse (f x) := by
  calc
    f (Ring.inverse x)=f (Ring.inverse x)*(f x*Ring.inverse (f x)) := by
      rw [Ring.mul_inverse_cancel _ (hx.map f),mul_one]
    _ = (f (Ring.inverse x)*f x)*Ring.inverse (f x) := (mul_assoc _ _ _).symm
    _ = Ring.inverse (f x) := by rw [←map_mul,Ring.inverse_mul_cancel _ hx,map_one,one_mul]

variable [CompleteSpace A]

theorem map_associator (f : A →ₐ[ℝ] B)
    (F : NilpotentFiltration A) (G : NilpotentFiltration B) (hN : F.cutoff=G.cutoff)
    {X Y : A} (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) :
    f (associator F X Y)=associator G (f X) (f Y) := by
  rw [associator,map_mul,map_unit_inverse f (rightSolution_isUnit F hX hY (1/2))]
  unfold rightSolution
  rw [map_normalizedSolution f F G hN hY X (by norm_num) (by norm_num),
    map_normalizedSolution f F G hN hX Y (by norm_num) (by norm_num)]
  rfl

end KZCollar

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

namespace FinitePicard
open MeasureTheory Set intervalIntegral
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def integralNorm (Ω : ℝ → A) (a b : ℝ) : ℝ := ∫ s in a..b,‖Ω s‖

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

def errorPoly (N : ℕ) (u : ℝ) : ℝ := ∑ n∈Finset.range (N+1),(n:ℝ)*u^n

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

end

open MeasureTheory Set Filter Asymptotics FinitePicard KZCollar RegularSingular
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

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

variable [FiniteDimensional ℝ A]

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

theorem gauge_continuousAt {X : A} {s : ℝ} (hs : s≠0) : ContinuousAt (gauge X) s :=
  (gauge_derivative X hs).continuousAt

theorem gauge_ratio_limit (X : A) :
    Tendsto (fun s : ℝ => gauge X (1+s)) (𝓝[>] 0) (𝓝 (1:A)) := by
  have ht : Tendsto (fun s : ℝ => 1+s) (𝓝[>] 0) (𝓝 1) := by
    simpa only [add_zero] using! (tendsto_const_nhds (x:=(1:ℝ))).add
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0))
  simpa only [gauge_one] using! (gauge_continuousAt (X:=X) (by norm_num : (1:ℝ)≠0)).tendsto.comp ht

end KZCollar

namespace ConjugateComparison

section
open AssociativeElimination TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] (N : ℕ)
local notation "Q" => TruncatedWords.Q (∅ : Set (A R Bool)) N
local notation "F" => filtration (∅ : Set (A R Bool)) N

theorem inverse_normalized (P : Qˣ) (hP : (P:Q)-1∈F 1) : ((P⁻¹:Qˣ):Q)-1∈F 1 := by
  have h := filtration_mul ∅ N 0 1 (mem_zero N ((P⁻¹:Qˣ):Q)) hP
  have he : ((P⁻¹:Qˣ):Q)*((P:Q)-1)=-(((P⁻¹:Qˣ):Q)-1) := by
    rw [mul_sub,Units.inv_mul,mul_one,neg_sub]
  rw [he] at h
  exact (F 1).neg_mem_iff.mp h

theorem theta_transport (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) (u : Q) :
    theta N P V hP hV (transport N P hP u)=transport N V hV u := by
  exact congrArg (transport N V hV) ((transport N P hP).symm_apply_apply u)

theorem theta_x (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    theta N P V hP hV (gen N false)=gen N false := by
  simpa only [transport_gen,family] using theta_transport N P V hP hV (gen N false)

theorem theta_y (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    theta N P V hP hV (gen N true)=
      (((unitArrow N P V hP hV)⁻¹:Qˣ):Q)*gen N true*(unitArrow N P V hP hV:Q) := by
  have hh := theta_transport N P V hP hV (gen N true)
  simp only [transport_gen,family,map_mul] at hh
  let M := Units.map (theta N P V hP hV).toMonoidHom P
  have h : ((M⁻¹:Qˣ):Q)*theta N P V hP hV (gen N true)*(M:Q)=
      ((V⁻¹:Qˣ):Q)*gen N true*(V:Q) := hh
  have hh := congrArg (fun z : Q => (M:Q)*z*((M⁻¹:Qˣ):Q)) h
  simp only [mul_assoc,Units.mul_inv_cancel_left] at hh
  simpa only [unitArrow,mul_inv_rev,inv_inv,Units.val_mul,M,mul_assoc,Units.mul_inv,mul_one] using hh

end

open AssociativeElimination TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] (N : ℕ)
local notation "Q" => TruncatedWords.Q (∅ : Set (A R Bool)) N
local notation "F" => filtration (∅ : Set (A R Bool)) N

theorem transport_raises (P : Qˣ) (hP : (P:Q)-1∈F 1) (n : ℕ) (u : Q) (hu : u∈F n) :
    transport N P hP u-u∈F (n+1) :=
  subst_raises N (family N P) (family_mem N P) (family_leading N P hP) n u hu

theorem transport_inverse_preserves (P : Qˣ) (hP : (P:Q)-1∈F 1)
    (n : ℕ) (u : Q) (hu : u∈F n) : (transport N P hP).symm u∈F n := by
  have hh : ∀ k≤n,(transport N P hP).symm u∈F k := by
    intro k
    induction k with
    | zero => intro _; exact mem_zero N _
    | succ k ih =>
      intro hk
      have hd := transport_raises N P hP k _ (ih (by omega))
      rw [AlgEquiv.apply_symm_apply] at hd
      have he := (F (k+1)).sub_mem (filtration_antitone ∅ N hk hu) hd
      simpa only [sub_sub_cancel] using he
  exact hh n le_rfl

theorem theta_raises (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1)
    (n : ℕ) (u : Q) (hu : u∈F n) : theta N P V hP hV u-u∈F (n+1) := by
  have hh := transport_inverse_preserves N P hP n u hu
  have hd := (F (n+1)).sub_mem (transport_raises N V hV n _ hh)
    (transport_raises N P hP n _ hh)
  simpa only [sub_sub_sub_cancel_right,AlgEquiv.apply_symm_apply,theta,AlgEquiv.trans_apply] using hd

theorem theta_preserves (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1)
    (n : ℕ) (u : Q) (hu : u∈F n) : theta N P V hP hV u∈F n := by
  have h := (F n).add_mem (filtration_antitone ∅ N (Nat.le_succ n)
    (theta_raises N P V hP hV n u hu)) hu
  simpa only [sub_add_cancel] using h

theorem mul_normalized (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    ((P*V:Qˣ):Q)-1∈F 1 := by
  have h := (F 1).add_mem
    (filtration_mul ∅ N 1 0 hP (mem_zero N (V:Q))) hV
  simpa only [sub_mul,one_mul,sub_add_sub_cancel,Units.val_mul] using h

theorem unitArrow_normalized (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    (unitArrow N P V hP hV:Q)-1∈F 1 := by
  apply mul_normalized N V _ hV
  apply inverse_normalized N
  change theta N P V hP hV (P:Q)-1∈_
  simpa only [map_sub,map_one] using theta_preserves N P V hP hV 1 ((P:Q)-1) hP

end ConjugateComparison

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace OperatorLog

section
open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem sum_range_extend {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n m : ℕ} (h : n ≤ m)
    (hz : ∀ k,n ≤ k → k < m → f k=0) :
    ∑ k∈Finset.range n,f k=∑ k∈Finset.range m,f k := by
  apply Finset.sum_subset (Finset.range_mono h)
  intro k hkm hkn
  exact hz k (Nat.le_of_not_lt (by simpa using hkn)) (Finset.mem_range.mp hkm)

theorem interpolate_nat (N : ℕ) (T : Module.End ℚ V) (hT : T^(N+1)=0) (m : ℕ) :
    interpolate N T m=(1+T)^m := by
  have hpow : ∀ k,N+1 ≤ k → T^k=0 := fun k hk => by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add,hT,zero_mul]
  have hsmall : ∀ k,m+1 ≤ k → (m.choose k : ℚ) • T^k=0 := by
    intro k hk
    rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_smul]
  unfold interpolate
  simp only [binom_eval_nat]
  rw [sum_range_extend (fun k => (m.choose k : ℚ) • T^k) (m:=N+m+2) (by omega)
    (fun k hk _ => by rw [hpow k hk,smul_zero])]
  rw [←sum_range_extend (fun k => (m.choose k : ℚ) • T^k) (n:=m+1) (m:=N+m+2) (by omega)
    (fun k hk _ => hsmall k hk)]
  rw [add_comm (1:Module.End ℚ V) T,(Commute.one_right T).add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [one_pow,mul_one,Algebra.smul_def,map_natCast]
  exact Nat.cast_comm _ _

def valuePolynomial (N : ℕ) (T : Module.End ℚ V) (a : V) (l : V →ₗ[ℚ] ℚ) : ℚ[X] :=
  ∑ k∈Finset.range (N+1),binom k*C (l ((T^k) a))

theorem value_eval (N : ℕ) (T : Module.End ℚ V) (a : V) (l : V →ₗ[ℚ] ℚ) (s : ℚ) :
    (valuePolynomial N T a l).eval s=l (interpolate N T s a) := by
  simp [valuePolynomial,interpolate,LinearMap.sum_apply,LinearMap.smul_apply,Polynomial.eval_finsetSum]

theorem value_one (N : ℕ) (T : Module.End ℚ V) (a : V) (l : V →ₗ[ℚ] ℚ) :
    (valuePolynomial N T a l).coeff 1=l (logarithm N T a) := by
  simp [valuePolynomial,logarithm,LinearMap.sum_apply,LinearMap.smul_apply]

theorem polynomial_ext_nat {p q : ℚ[X]} (h : ∀ n : ℕ,p.eval (n:ℚ)=q.eval (n:ℚ)) : p=q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R:=ℚ))).mono
  rintro _ ⟨n,rfl⟩
  exact h n

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]

def pairPolynomial (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (a : V) (b : W) (l : U →ₗ[ℚ] ℚ) : ℚ[X] :=
  ∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
    (binom i*binom j)*C (l (B ((T^i) a) ((S^j) b)))

theorem pair_eval (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (a : V) (b : W) (l : U →ₗ[ℚ] ℚ) (s : ℚ) :
    (pairPolynomial N T S B a b l).eval s=
      l (B (interpolate N T s a) (interpolate N S s b)) := by
  simp only [pairPolynomial,Polynomial.eval_finsetSum,eval_mul,eval_C,interpolate,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem pair_one (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (a : V) (b : W) (l : U →ₗ[ℚ] ℚ) :
    (pairPolynomial N T S B a b l).coeff 1=
      l (B (logarithm N T a) b+B a (logarithm N S b)) := by
  simp [pairPolynomial,logarithm,LinearMap.sum_apply,LinearMap.smul_apply,mul_coeff_one,
    binom_coeff_zero,add_mul,Finset.sum_add_distrib,ite_mul,mul_ite,add_comm]

theorem powers_bilinear (A : Module.End ℚ V) (C : Module.End ℚ W) (D : Module.End ℚ U)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (h : ∀ a b,D (B a b)=B (A a) (C b)) (m : ℕ) (a : V) (b : W) :
    (D^m) (B a b)=B ((A^m) a) ((C^m) b) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [pow_succ',Module.End.mul_apply,ih,h]

theorem logarithm_bilinear (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (R : Module.End ℚ U) (hT : T^(N+1)=0) (hS : S^(N+1)=0) (hR : R^(N+1)=0)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U)
    (h : ∀ a b,(1+R) (B a b)=B ((1+T) a) ((1+S) b)) (a : V) (b : W) :
    logarithm N R (B a b)=B (logarithm N T a) b+B a (logarithm N S b) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ
    (logarithm N R (B a b)-(B (logarithm N T a) b+B a (logarithm N S b)))).mp
  intro l
  have hp : valuePolynomial N R (B a b) l=pairPolynomial N T S B a b l := by
    apply polynomial_ext_nat
    intro m
    rw [value_eval,pair_eval,interpolate_nat N R hR,interpolate_nat N T hT,interpolate_nat N S hS]
    exact congrArg l (powers_bilinear _ _ _ B h m a b)
  have hc := congrArg (fun p : ℚ[X] => p.coeff 1) hp
  rw [value_one,pair_one] at hc
  simpa only [map_sub,sub_eq_zero] using hc

end

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

theorem powers_natural (T : Module.End ℚ V) (S : Module.End ℚ W) (f : V →ₗ[ℚ] W)
    (h : ∀ v,f (T v)=S (f v)) (n : ℕ) (v : V) : f ((T^n) v)=(S^n) (f v) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Module.End.mul_apply,h,ih]

theorem logarithm_natural (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (f : V →ₗ[ℚ] W) (h : ∀ v,f (T v)=S (f v)) (v : V) :
    f (logarithm N T v)=logarithm N S (f v) := by
  simp only [logarithm,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    powers_natural T S f h]

end OperatorLog

namespace LogCategory
open OperatorLog
variable {A O : Type*} [Ring A] [Algebra ℚ A]

theorem delta_comp (g : Data A O) (p q r : O) (a b : A) :
    delta g p r (b*a)=delta g q r b*a+b*delta g p q a := by
  apply logarithm_bilinear g.N (g.S q r-1) (g.S p q-1) (g.S p r-1)
    (g.nilpotent q r) (g.nilpotent p q) (g.nilpotent p r) (LinearMap.mul ℚ A)
  intro b a
  have he : ∀ p q,(1+(g.S p q-1))=g.S p q := by intros; abel
  simpa only [he,LinearMap.mul_apply'] using g.comp p q r a b

attribute [local instance] LieRing.ofAssociativeRing

theorem unit_cocycle (g : Data A O) (p q r : O) :
    delta g p r 1=delta g q r 1+delta g p q 1 := by
  simpa only [one_mul,mul_one] using delta_comp g p q r 1 1

end LogCategory

namespace KZComparison
open CutoffDepth CutoffKZ FinitePicard KZCollar

 theorem negative_val (N : ℕ) : (negative N:Q ℝ N)=associator (weight N) (-X N) (-Y N) := by
  change CutoffScaling.map N (-1:ℝ) (positive N:Q ℝ N)=_
  rw [positive_val,map_associator _ (weight N) (weight N) rfl (gen_weight N false) (gen_weight N true)]
  have h (b : Bool) : CutoffScaling.map N (-1:ℝ) (gen N b)= -gen N b := by
    simpa only [neg_smul,one_smul,gen,TruncatedSubstitution.gen] using CutoffScaling.map_gen N (-1:ℝ) b
  rw [h false,h true]

end KZComparison

namespace TruncatedSubstitution
open AssociativeElimination TruncatedWords
variable {R α B : Type*} [CommRing R] [Ring B] [Algebra R B]
 theorem hom_ext (N : ℕ) (f g : Q (∅ : Set (A R α)) N →ₐ[R] B)
    (h : ∀ a,f (gen N a)=g (gen N a)) : f=g := by
  have he : f.comp (quotient ∅ N)=g.comp (quotient ∅ N) := by
    apply AssociativeElimination.hom_ext
    exact h
  apply AlgHom.ext
  intro u
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations (∅ : Set (A R α)) N) u
  exact AlgHom.congr_fun he p
end TruncatedSubstitution

namespace ConjugateCoalgebra
open scoped TensorProduct
open CutoffDepth CutoffKZ CutoffDiagonal ConjugateComparison

theorem transport_cutoff_gen (N : ℕ) (P : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1) (b : Bool) :
    transport N P hP (gen N b)=family N P b := transport_gen N P hP b

theorem natural_inverse {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    (f : A →ₐ[ℝ] B) (e : A ≃ₐ[ℝ] A) (d : B ≃ₐ[ℝ] B)
    (he : ∀ u,f (e u)=d (f u)) (u : A) : f (e.symm u)=d.symm (f u) := by
  apply d.injective
  rw [d.apply_symm_apply,←he,e.apply_symm_apply]

end ConjugateCoalgebra

end DeligneDrinfeld

end

end OAI

end


section

namespace OAI

noncomputable section

namespace DeligneDrinfeld.UnitConjugation
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

def hom (u : Aˣ) : A →ₐ[R] A where
  toFun a := (u:A)*a*((u⁻¹:Aˣ):A)
  map_zero' := by simp only [mul_zero,zero_mul]
  map_one' := by simp only [mul_one,Units.mul_inv]
  map_add' a b := by rw [mul_add,add_mul]
  map_mul' a b := by
    simp only [mul_assoc]
    rw [←mul_assoc (((u⁻¹:Aˣ):A)) (u:A),Units.inv_mul,one_mul]
  commutes' r := by
    rw [←Algebra.commutes,mul_assoc,Units.mul_inv,mul_one]

@[simp] theorem hom_apply (u : Aˣ) (a : A) : hom (R:=R) u a=(u:A)*a*((u⁻¹:Aˣ):A) := rfl

@[simp] theorem inverse (u : Aˣ) (a : A) : hom (R:=R) u⁻¹ (hom (R:=R) u a)=a := by
  simp only [hom_apply,inv_inv,mul_assoc]
  rw [Units.inv_mul_cancel_left,Units.inv_mul,mul_one]

@[simp] theorem mul_apply (u v : Aˣ) (a : A) : hom (R:=R) (u*v) a=hom (R:=R) u (hom (R:=R) v a) := by
  simp only [hom_apply,Units.val_mul,mul_inv_rev,mul_assoc]

theorem natural {B : Type*} [Ring B] [Algebra R B] (f : A →ₐ[R] B) (u : Aˣ) (a : A) :
    f (hom (R:=R) u a)=hom (R:=R) (Units.map f.toMonoidHom u) (f a) := by
  simp only [hom_apply,map_mul]
  rfl

end DeligneDrinfeld.UnitConjugation

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

namespace DeligneDrinfeld.ComplexLogChamber
open MeasureTheory Set Filter FinitePicard
open scoped Topology
variable {A E : Type*} [NormedRing A] [NormedAlgebra ℂ A] [Fintype E]

def field (p : E → ℂ) (c : E → A) (z : ℂ) : A := ∑ i,(z-p i)⁻¹ • c i

def connection (p : E → ℂ) (c : E → A) (z v : ℂ) : A := v • field p c z

theorem form_eq (p : E → ℂ) (c : E → A) (z v : ℂ) :
    LogRectangle.form c (fun i => z-p i) (fun _ => v)=connection p c z v := by
  simp only [LogRectangle.form,connection,field,Finset.smul_sum,smul_smul,div_eq_mul_inv]

theorem connection_commute (p : E → ℂ) (c : E → A) (z v w : ℂ) :
    Commute (connection p c z v) (connection p c z w) := by
  change (v • field p c z)*(w • field p c z)=(w • field p c z)*(v • field p c z)
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm v w]

theorem connection_mem (F : NilpotentFiltration A) (p : E → ℂ) (c : E → A)
    (hc : ∀ i (r : ℂ),r • c i∈F.space 1) (z v : ℂ) : connection p c z v∈F.space 1 := by
  rw [←form_eq]
  exact (F.space 1).sum_mem (fun i hi => hc i _)

@[simp] theorem connection_zero (p : E → ℂ) (c : E → A) (z : ℂ) : connection p c z 0=0 :=
  zero_smul ℂ _

theorem connection_continuousOn (p : E → ℂ) (c : E → A)
    {X : Type*} [TopologicalSpace X] {z v : X → ℂ} {S : Set X}
    (hz : ContinuousOn z S) (hv : ContinuousOn v S)
    (hn : ∀ x∈S,∀ i,z x≠p i) : ContinuousOn (fun x => connection p c (z x) (v x)) S := by
  simp only [←form_eq]
  exact LogRectangle.continuousOn_form c (fun i => hz.sub continuousOn_const)
    (fun _ => hv) (fun x hx i => sub_ne_zero.mpr (hn x hx i))

def segment (u v : ℂ) (t : ℝ) : ℂ := (1-t) • u+t • v

@[simp] theorem segment_zero (u v : ℂ) : segment u v 0=u := by simp [segment]
@[simp] theorem segment_one (u v : ℂ) : segment u v 1=v := by simp [segment]

theorem segment_derivative (u v : ℂ) (t : ℝ) : HasDerivAt (segment u v) (v-u) t := by
  convert! (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).smul_const u).add
    ((hasDerivAt_id t).smul_const v) using 1
  simp [sub_eq_add_neg,add_comm]

def fundamental (F : NilpotentFiltration A) (p : E → ℂ) (c : E → A) (u v : ℂ) : A :=
  transport (fun t => connection p c (segment u v t) (v-u)) 0 F.cutoff 1

variable [CompleteSpace A] [FiniteDimensional ℝ A]

omit [CompleteSpace A] in
theorem fundamental_isUnit (F : NilpotentFiltration A) (p : E → ℂ) (c : E → A)
    (hc : ∀ i (r : ℂ),r • c i∈F.space 1) (u v : ℂ) : IsUnit (fundamental F p c u v) :=
  transport_isUnit F (fun _ => connection_mem F p c hc _ _) _ _ _

theorem fundamental_derivative (F : NilpotentFiltration A) (p : E → ℂ) (c : E → A)
    (hc : ∀ i (r : ℂ),r • c i∈F.space 1) {C : Set ℂ} {u : ℂ}
    (hp : ∀ z∈C,∀ t∈Icc (0:ℝ) 1,∀ i,segment u z t≠p i)
    {q q' : ℝ → ℂ} {a b s : ℝ} (hq : ∀ s∈Icc a b,q s∈C)
    (hqc : ContinuousOn q (Icc a b)) (hqc' : ContinuousOn q' (Icc a b))
    (hqd : ∀ s∈Ioo a b,HasDerivAt q (q' s) s) (hs : s∈Ioo a b) :
    HasDerivAt (fun s => fundamental F p c u (q s))
      (connection p c (q s) (q' s)*fundamental F p c u (q s)) s := by
  have hab : a≤b := le_trans hs.1.le hs.2.le
  have hq2 : ContinuousOn (fun w : ℝ×ℝ => q w.1) (Icc a b ×ˢ Icc 0 1) :=
    hqc.comp continuous_fst.continuousOn (fun w hw => hw.1)
  have hq2' : ContinuousOn (fun w : ℝ×ℝ => q' w.1) (Icc a b ×ˢ Icc 0 1) :=
    hqc'.comp continuous_fst.continuousOn (fun w hw => hw.1)
  have hh := LogRectangle.transport_derivative F c
    (z:=fun s t i => segment u (q s) t-p i)
    (zt:=fun s _ _ => q s-u) (zs:=fun s t _ => t • q' s) (zst:=fun s _ _ => q' s)
    (by norm_num : (0:ℝ)≤1) hab hc
    (fun i => (((continuousOn_const.sub continuous_snd.continuousOn).smul continuousOn_const).add
      (continuous_snd.continuousOn.smul hq2)).sub continuousOn_const)
    (fun _ => continuous_snd.continuousOn.smul hq2')
    (fun _ => hq2.sub continuousOn_const) (fun _ => hq2')
    (fun v hv t ht i => sub_ne_zero.mpr (hp _ (hq v hv) t ht i))
    (fun v hv t ht i => by
      simpa only [segment,Pi.add_apply,zero_add] using!
        ((hasDerivAt_const v ((1-t) • u)).add ((hqd v hv).const_smul t)).sub_const (p i))
    (fun v hv t ht i => (hqd v hv).sub_const u)
    (fun v hv t ht i => (segment_derivative u (q v) t).sub_const (p i))
    (fun v hv t ht i => by simpa only [one_smul] using! (hasDerivAt_id t).smul_const (q' v))
    (fun t ht => by rw [form_eq,form_eq]; exact connection_commute p c _ _ _) hs
  simpa only [segment_zero,segment_one,zero_smul,one_smul,form_eq,connection_zero,
    mul_zero,sub_zero,fundamental] using! hh

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem fundamental_continuousOn (F : NilpotentFiltration A) (p : E → ℂ) (c : E → A)
    {C : Set ℂ} {u : ℂ}
    (hp : ∀ z∈C,∀ t∈Icc (0:ℝ) 1,∀ i,segment u z t≠p i)
    {q : ℝ → ℂ} {a b : ℝ} (hab : a≤b) (hq : ∀ s∈Icc a b,q s∈C)
    (hqc : ContinuousOn q (Icc a b)) :
    ContinuousOn (fun s => fundamental F p c u (q s)) (Icc a b) := by
  apply continuousOn_transport_parameter (a:=0) (b:=1) (by norm_num) hab _ F.cutoff
  have hq2 : ContinuousOn (fun w : ℝ×ℝ => q w.1) (Icc a b ×ˢ Icc 0 1) :=
    hqc.comp continuous_fst.continuousOn (fun w hw => hw.1)
  exact connection_continuousOn p c
    (((continuousOn_const.sub continuous_snd.continuousOn).smul continuousOn_const).add
      (continuous_snd.continuousOn.smul hq2)) (hq2.sub continuousOn_const)
    (fun w hw i => hp _ (hq w.1 hw.1) w.2 hw.2 i)

theorem transport_eq_ratio (F : NilpotentFiltration A) (p : E → ℂ) (c : E → A)
    (hc : ∀ i (r : ℂ),r • c i∈F.space 1) {C : Set ℂ} {u : ℂ}
    (hp : ∀ z∈C,∀ t∈Icc (0:ℝ) 1,∀ i,segment u z t≠p i)
    {q q' : ℝ → ℂ} {a b : ℝ} (hab : a<b) (hq : ∀ s∈Icc a b,q s∈C)
    (hqc : ContinuousOn q (Icc a b)) (hqc' : ContinuousOn q' (Icc a b))
    (hqd : ∀ s∈Ioo a b,HasDerivAt q (q' s) s) :
    transport (fun s => connection p c (q s) (q' s)) a F.cutoff b=
      fundamental F p c u (q b)*Ring.inverse (fundamental F p c u (q a)) := by
  have hcon := connection_continuousOn p c hqc hqc' (fun s hs => by simpa using hp _ (hq s hs) 1 ⟨by norm_num,le_rfl⟩)
  apply transport_eq_fundamental F (fun _ => connection_mem F p c hc _ _) hab
    (hcon.intervalIntegrable_of_Icc hab.le) (hcon.mono Ioo_subset_Icc_self)
    (fun s hs => fundamental_derivative F p c hc hp hq hqc hqc' hqd hs)
    (fundamental_continuousOn F p c hp hab.le hq hqc)
    (fun s hs => fundamental_isUnit F p c hc _ _)

end DeligneDrinfeld.ComplexLogChamber

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

namespace DeligneDrinfeld.ComplexKZ
open Set Filter FinitePicard ComplexLogChamber
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

def form (X Y : A) (z v : ℂ) : A := (v/z) • X+(v/(z-1)) • Y

def poles : Bool → ℂ := fun b => if b then 1 else 0

def residues (X Y : A) : Bool → A := fun b => if b then Y else X

theorem form_eq (X Y : A) (z v : ℂ) :
    form X Y z v=connection poles (residues X Y) z v := by
  rw [←ComplexLogChamber.form_eq]
  simp [form,LogRectangle.form,poles,residues,add_comm]

def domain : Set ℂ := {z | 0≤z.im ∧ z≠0 ∧ z≠1}

theorem real_mem {s : ℝ} (h0 : s≠0) (h1 : s≠1) : (s:ℂ)∈domain := by
  simp [domain,h0,h1]

theorem star_avoids {z : ℂ} (hz : z∈domain) {t : ℝ} (ht : t∈Icc 0 1) (b : Bool) :
    segment Complex.I z t≠poles b := by
  intro he
  have hp : (poles b).im=0 := by cases b <;> simp [poles]
  have him := congrArg Complex.im he
  simp only [ComplexLogChamber.segment,Complex.add_im,Complex.smul_im,smul_eq_mul,Complex.I_im] at him
  rw [hp] at him
  have ht1 : t=1 := by
    have hprod : 0≤t*z.im := mul_nonneg ht.1 hz.1
    nlinarith [ht.2]
  rw [ht1,segment_one] at he
  cases b
  · exact hz.2.1 (by simpa [poles] using he)
  · exact hz.2.2 (by simpa [poles] using he)

def turn (z : ℂ) : ℂ := (1-z)⁻¹

def turnDeriv (z : ℂ) : ℂ := (1-z)⁻¹^2

theorem turn_nonzero {z : ℂ} (hz : z≠1) : turn z≠0 := by
  exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm hz))

theorem turn_sub_one {z : ℂ} (hz : z≠1) : turn z-1=z/(1-z) := by
  unfold turn
  field_simp [sub_ne_zero.mpr (Ne.symm hz)]
  ring

theorem turn_ne_one {z : ℂ} (h0 : z≠0) (h1 : z≠1) : turn z≠1 := by
  intro h
  have hh := turn_sub_one h1
  rw [h,sub_self] at hh
  exact (div_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))) hh.symm

theorem turn_mem {z : ℂ} (hz : z∈domain) : turn z∈domain := by
  refine ⟨?_,turn_nonzero hz.2.2,turn_ne_one hz.2.1 hz.2.2⟩
  simp only [turn,Complex.inv_im,Complex.sub_im,Complex.one_im,zero_sub,neg_neg]
  exact div_nonneg hz.1 (Complex.normSq_nonneg _)

theorem turn_twice {z : ℂ} (h0 : z≠0) (h1 : z≠1) : turn (turn z)=(z-1)/z := by
  unfold turn
  field_simp [h0,sub_ne_zero.mpr (Ne.symm h1)]
  ring

theorem turn_thrice {z : ℂ} (h0 : z≠0) (h1 : z≠1) : turn (turn (turn z))=z := by
  rw [turn_twice h0 h1]
  unfold turn
  field_simp [h0]
  ring

theorem form_turn (X Y : A) {z : ℂ} (h0 : z≠0) (h1 : z≠1) (v : ℂ) :
    form X Y (turn z) (turnDeriv z*v)=form Y (-X-Y) z v := by
  rw [form,form,turn_sub_one h1]
  have hX : turnDeriv z*v/turn z=-(v/(z-1)) := by
    unfold turnDeriv turn
    field_simp [h0,sub_ne_zero.mpr (Ne.symm h1),sub_ne_zero.mpr h1]
    ring
  have hY : turnDeriv z*v/(z/(1-z))=v/z-v/(z-1) := by
    unfold turnDeriv
    field_simp [h0,sub_ne_zero.mpr (Ne.symm h1),sub_ne_zero.mpr h1]
    ring
  rw [hX,hY]
  simp only [sub_smul,smul_sub,smul_neg,neg_smul]
  abel

theorem turn_derivative {q : ℝ → ℂ} {q' : ℂ} {s : ℝ}
    (hq : HasDerivAt q q' s) (h1 : q s≠1) :
    HasDerivAt (fun s => turn (q s)) (turnDeriv (q s)*q') s := by
  have hd := ((hasDerivAt_const s (1:ℂ)).sub hq).inv (sub_ne_zero.mpr (Ne.symm h1))
  convert! hd using 1
  simp only [zero_sub,neg_neg,turnDeriv,Pi.sub_apply,div_eq_mul_inv,inv_pow]
  ring

theorem turn_continuousOn {q : ℝ → ℂ} {S : Set ℝ} (hq : ContinuousOn q S)
    (h1 : ∀ s∈S,q s≠1) : ContinuousOn (fun s => turn (q s)) S :=
  (continuousOn_const.sub hq).inv₀ (fun s hs => sub_ne_zero.mpr (Ne.symm (h1 s hs)))

theorem turnDeriv_continuousOn {q : ℝ → ℂ} {S : Set ℝ} (hq : ContinuousOn q S)
    (h1 : ∀ s∈S,q s≠1) : ContinuousOn (fun s => turnDeriv (q s)) S :=
  (turn_continuousOn hq h1).pow 2

theorem form_real (X Y : A) (s : ℝ) : form X Y s 1=KZCollar.bulkForm X Y s := by
  simp only [form,KZCollar.bulkForm,one_div]
  congr 1
  · rw [←Complex.ofReal_inv,Complex.coe_smul]
  · rw [←Complex.ofReal_one,←Complex.ofReal_sub,←Complex.ofReal_inv,Complex.coe_smul]

end DeligneDrinfeld.ComplexKZ

namespace DeligneDrinfeld.PowerAsymptotic
open MeasureTheory Set Filter Asymptotics FinitePicard
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
theorem powerSmall_of_real_bound {f : ℝ → A} {g : ℝ → ℝ} (hg : PowerSmall g)
    (h : ∀ᶠ s in 𝓝[>] 0, ‖f s‖ ≤ g s) : PowerSmall f := by
  obtain ⟨p,hp,hg⟩ := hg
  exact ⟨p,hp,(IsBigO.of_norm_eventuallyLE h).trans hg⟩

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

namespace DeligneDrinfeld.ComplexKZ

section
open Set Filter MeasureTheory FinitePicard KZCollar PowerAsymptotic
open scoped Topology

def arc (r t : ℝ) : ℂ := (r:ℂ)*Complex.exp ((((1-t)*Real.pi:ℝ):ℂ)*Complex.I)

def angular : ℂ := -((Real.pi:ℂ)*Complex.I)

@[simp] theorem arc_zero (r : ℝ) : arc r 0=-(r:ℂ) := by
  simp [arc,Complex.exp_pi_mul_I]

@[simp] theorem arc_one (r : ℝ) : arc r 1=(r:ℂ) := by simp [arc]

theorem norm_arc {r : ℝ} (hr : 0≤r) (t : ℝ) : ‖arc r t‖=r := by
  simp [arc,Complex.norm_exp,hr,Real.norm_eq_abs,abs_of_nonneg]

theorem arc_mem {r t : ℝ} (hr : 0<r) (hr1 : r<1) (ht : t∈Icc 0 1) :
    arc r t∈domain := by
  have hn := norm_arc hr.le t
  refine ⟨?_,?_,?_⟩
  · simp only [arc,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      Complex.exp_im,Complex.mul_re,Complex.I_re,mul_zero,Complex.I_im,zero_sub,neg_zero,
      Real.exp_zero,Complex.mul_im,one_mul,mul_one]
    exact mul_nonneg hr.le (Real.sin_nonneg_of_mem_Icc ⟨mul_nonneg (sub_nonneg.mpr ht.2) Real.pi_pos.le, by nlinarith [mul_nonneg ht.1 Real.pi_pos.le]⟩)
  · intro h; rw [h,norm_zero] at hn; linarith
  · intro h; rw [h,norm_one] at hn; linarith

theorem arc_derivative (r t : ℝ) : HasDerivAt (arc r) (angular*arc r t) t := by
  have hreal := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul_const Real.pi)
  have hcomplex := hreal.ofReal_comp
  have hexp := (Complex.hasDerivAt_exp _).scomp t (hcomplex.mul_const Complex.I)
  convert! hexp.const_mul (r:ℂ) using 1
  simp only [angular,arc,zero_sub,Complex.ofReal_neg,neg_mul,Pi.sub_apply,id_eq,smul_eq_mul]
  ring_nf

theorem arc_continuous (r : ℝ) : Continuous (arc r) :=
  continuous_iff_continuousAt.2 (fun t => (arc_derivative r t).continuousAt)

@[simp] theorem norm_angular : ‖angular‖=Real.pi := by
  simp [angular,Real.pi_pos.le,abs_of_nonneg]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

def arcForm (X Y : A) (r t : ℝ) : A := form X Y (arc r t) (angular*arc r t)

theorem arcForm_eq (X Y : A) {r : ℝ} (hr : 0<r) (t : ℝ) :
    arcForm X Y r t=angular • X+(angular*arc r t/(arc r t-1)) • Y := by
  have hn : arc r t≠0 := by intro h; have he:=norm_arc hr.le t; rw [h,norm_zero] at he; linarith
  unfold arcForm form
  rw [mul_div_cancel_right₀ _ hn]

theorem norm_arcForm_sub_le (X Y : A) {r : ℝ} (hr : 0<r) (hr1 : r≤1/2) (t : ℝ) :
    ‖arcForm X Y r t-angular • X‖≤(2*Real.pi*‖Y‖)*r := by
  rw [arcForm_eq X Y hr,add_sub_cancel_left,norm_smul,norm_div,norm_mul,norm_angular,norm_arc hr.le]
  have hden : (1:ℝ)/2≤‖arc r t-1‖ := by
    have h := norm_sub_norm_le (1:ℂ) (arc r t)
    rw [norm_one,norm_arc hr.le,norm_sub_rev] at h
    linarith
  have hb : Real.pi*r/‖arc r t-1‖≤2*Real.pi*r := by
    apply (div_le_iff₀ (by linarith : 0<‖arc r t-1‖)).mpr
    calc
      Real.pi*r=(2*Real.pi*r)*(1/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)
  exact (mul_le_mul_of_nonneg_right hb (norm_nonneg Y)).trans_eq (by ring)

theorem arcForm_continuousOn (X Y : A) {r : ℝ} (hr : 0<r) (hr1 : r<1) :
    ContinuousOn (arcForm X Y r) (Icc 0 1) := by
  change ContinuousOn (fun t => arcForm X Y r t) _
  simp only [arcForm,form_eq]
  apply ComplexLogChamber.connection_continuousOn _ _ (arc_continuous r).continuousOn
    (continuous_const.mul (arc_continuous r)).continuousOn
  intro t ht b
  cases b
  · exact (arc_mem hr hr1 ht).2.1
  · exact (arc_mem hr hr1 ht).2.2

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem constant_transport (F : NilpotentFiltration A) {X : A} (hX : X∈F.space 1) :
    transport (fun _ => X) 0 F.cutoff 1=NormedSpace.exp X := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  have h := transport_eq_fundamental F (fun _ => hX) (by norm_num : (0:ℝ)<1)
    intervalIntegrable_const continuousOn_const
    (f:=fun t : ℝ => NormedSpace.exp (t • X))
    (fun t ht => hasDerivAt_exp_smul_const' X t)
    (by fun_prop) (fun t ht => NormedSpace.isUnit_exp _)
  simpa using h

end

section
open Set Filter FinitePicard ComplexLogChamber
open scoped Topology

structure Path (a b : ℝ) where
  pos : a<b
  q : ℝ → ℂ
  v : ℝ → ℂ
  mem : ∀ t∈Icc a b,q t∈domain
  continuous_q : ContinuousOn q (Icc a b)
  continuous_v : ContinuousOn v (Icc a b)
  derivative : ∀ t∈Ioo a b,HasDerivAt q (v t) t

namespace Path
variable {a b : ℝ}

def rotate (P : Path a b) : Path a b where
  pos := P.pos
  q := fun t => turn (P.q t)
  v := fun t => turnDeriv (P.q t)*P.v t
  mem := fun t ht => turn_mem (P.mem t ht)
  continuous_q := turn_continuousOn P.continuous_q (fun t ht => (P.mem t ht).2.2)
  continuous_v := (turnDeriv_continuousOn P.continuous_q (fun t ht => (P.mem t ht).2.2)).mul P.continuous_v
  derivative := fun t ht => turn_derivative (P.derivative t ht) (P.mem t (Ioo_subset_Icc_self ht)).2.2

def interval (ha : 0<a) (hab : a<b) (hb : b<1) : Path a b where
  pos := hab
  q t := t
  v _ := 1
  mem t ht := real_mem (ne_of_gt (ha.trans_le ht.1)) (ne_of_lt (ht.2.trans_lt hb))
  continuous_q := Complex.continuous_ofReal.continuousOn
  continuous_v := continuousOn_const
  derivative t _ := by simpa only [Complex.ofReal_one] using! (hasDerivAt_id t).ofReal_comp

def semicircle {r : ℝ} (hr : 0<r) (hr1 : r<1) : Path 0 1 where
  pos := by norm_num
  q := arc r
  v t := angular*arc r t
  mem t ht := arc_mem hr hr1 ht
  continuous_q := (arc_continuous r).continuousOn
  continuous_v := (continuous_const.mul (arc_continuous r)).continuousOn
  derivative t _ := arc_derivative r t

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

def holonomy (F : NilpotentFiltration A) (X Y : A) (P : Path a b) : A :=
  transport (fun s => form X Y (P.q s) (P.v s)) a F.cutoff b

theorem rotate_holonomy (F : NilpotentFiltration A) (X Y : A) (P : Path a b) :
    holonomy F X Y P.rotate=holonomy F Y (-X-Y) P := by
  apply transport_congr
  intro s hs
  rw [uIcc_of_le P.pos.le] at hs
  exact form_turn X Y (P.mem s hs).2.1 (P.mem s hs).2.2 _

theorem rotate_twice_holonomy (F : NilpotentFiltration A) (X Y : A) (P : Path a b) :
    holonomy F X Y P.rotate.rotate=holonomy F (-X-Y) X P := by
  rw [rotate_holonomy,rotate_holonomy]
  congr 1
  abel

theorem interval_holonomy (F : NilpotentFiltration A) (X Y : A)
    (ha : 0<a) (hab : a<b) (hb : b<1) :
    holonomy F X Y (interval ha hab hb)=transport (KZCollar.bulkForm X Y) a F.cutoff b := by
  change transport (fun t => form X Y (t:ℂ) 1) a F.cutoff b=_
  congr 1
  funext t
  exact form_real X Y t

variable [CompleteSpace A] [FiniteDimensional ℝ A]

def frame (F : NilpotentFiltration A) (X Y : A) (z : ℂ) : A :=
  fundamental F poles (residues X Y) Complex.I z

omit [CompleteSpace A] in
theorem frame_isUnit (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1) (z : ℂ) :
    IsUnit (frame F X Y z) := by
  apply fundamental_isUnit
  intro b c
  cases b
  · exact hX c
  · exact hY c

theorem holonomy_ratio (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1) (P : Path a b) :
    holonomy F X Y P=frame F X Y (P.q b)*Ring.inverse (frame F X Y (P.q a)) := by
  unfold holonomy frame
  simp only [form_eq]
  exact transport_eq_ratio F poles (residues X Y)
    (fun b c => by cases b; exact hX c; exact hY c)
    (fun z hz t ht b => star_avoids hz ht b) P.pos P.mem P.continuous_q P.continuous_v P.derivative

end Path
end

open Set Filter FinitePicard
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem cycle_identity (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1)
    {a b c d : ℝ} (P : Path a b) (Q : Path c d)
    (hstart : P.q a=Q.q d) (hend : P.q b=turn (Q.q c)) :
    Path.holonomy F X Y Q*Path.holonomy F X Y P.rotate.rotate*
      Path.holonomy F X Y Q.rotate.rotate*Path.holonomy F X Y P.rotate*
      Path.holonomy F X Y Q.rotate*Path.holonomy F X Y P=1 := by
  rw [Path.holonomy_ratio F hX hY Q,Path.holonomy_ratio F hX hY P.rotate.rotate,
    Path.holonomy_ratio F hX hY Q.rotate.rotate,Path.holonomy_ratio F hX hY P.rotate,
    Path.holonomy_ratio F hX hY Q.rotate,Path.holonomy_ratio F hX hY P]
  simp only [Path.rotate]
  rw [hstart,hend,turn_thrice (Q.mem c (left_mem_Icc.mpr Q.pos.le)).2.1
    (Q.mem c (left_mem_Icc.mpr Q.pos.le)).2.2]
  have hu := Path.frame_isUnit F hX hY
  have cancel (u : ℂ) (v : A) : Ring.inverse (Path.frame F X Y u)*(Path.frame F X Y u*v)=v :=
    Ring.inverse_mul_cancel_left _ _ (hu u)
  simp only [mul_assoc,cancel,Ring.mul_inverse_cancel _ (hu _)]

def bulkEndpoint (r : ℝ) : ℝ := (1+r)⁻¹

theorem bulkEndpoint_bounds {r : ℝ} (hr : 0<r) (hr1 : r<1/2) :
    0<bulkEndpoint r ∧ r<bulkEndpoint r ∧ bulkEndpoint r<1 := by
  have hd : 0<1+r := by linarith
  refine ⟨inv_pos.mpr hd,?_,?_⟩
  · change r<(1+r)⁻¹
    rw [←one_div]
    apply (lt_div_iff₀ hd).mpr
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr1.le)]
  · exact (inv_lt_one₀ hd).mpr (by linarith)

theorem bulkEndpoint_turn (r : ℝ) : (bulkEndpoint r:ℂ)=turn (-(r:ℂ)) := by
  simp [bulkEndpoint,turn,sub_neg_eq_add]

theorem bulk_arc_identity (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1)
    {r : ℝ} (hr : 0<r) (hr1 : r<1/2) :
    transport (arcForm X Y r) 0 F.cutoff 1*
      transport (KZCollar.bulkForm (-X-Y) X) r F.cutoff (bulkEndpoint r)*
      transport (arcForm (-X-Y) X r) 0 F.cutoff 1*
      transport (KZCollar.bulkForm Y (-X-Y)) r F.cutoff (bulkEndpoint r)*
      transport (arcForm Y (-X-Y) r) 0 F.cutoff 1*
      transport (KZCollar.bulkForm X Y) r F.cutoff (bulkEndpoint r)=1 := by
  have hb := bulkEndpoint_bounds hr hr1
  let P := Path.interval hr hb.2.1 hb.2.2
  let Q := Path.semicircle hr (by linarith : r<1)
  have hh := cycle_identity F hX hY P Q (by simp [P,Q,Path.interval,Path.semicircle])
    (by simpa [P,Q,Path.interval,Path.semicircle] using bulkEndpoint_turn r)
  rw [Path.rotate_twice_holonomy,Path.rotate_twice_holonomy,
    Path.rotate_holonomy,Path.rotate_holonomy] at hh
  dsimp only [P] at hh
  rw [Path.interval_holonomy,Path.interval_holonomy,Path.interval_holonomy] at hh
  exact hh

end DeligneDrinfeld.ComplexKZ

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace ComplexKZ

section
open Set Filter FinitePicard KZCollar
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem bulkScale_limit : Tendsto (fun r : ℝ => r/(1+r)) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [Pi.div_apply,add_zero,zero_div] using! h.div ((tendsto_const_nhds (x:=(1:ℝ))).add h) (by norm_num : (1:ℝ)+0≠0)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    change 0<r at hr
    exact div_pos hr (by linarith)

theorem bulk_normalized_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    Tendsto (fun r => gauge (-Y) r*transport (bulkForm X Y) r F.cutoff (bulkEndpoint r)*gauge X r)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have hh := regularizedBulk_two_limit F hX hY tendsto_id bulkScale_limit
  have ht := (gauge_ratio_limit (-Y)).mul hh
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0<r at hr
  have hd : 1+r≠0 := ne_of_gt (by linarith : 0<1+r)
  have hs : r/(1+r)≠0 := div_ne_zero (ne_of_gt hr) hd
  have he : (1+r)*(r/(1+r))=r := by field_simp
  have hb : 1-r/(1+r)=bulkEndpoint r := by unfold bulkEndpoint; field_simp; ring
  rw [hb,←mul_assoc,←mul_assoc,←gauge_mul_scale (-Y) hd hs,he]
  rfl

end

section
open Set Filter MeasureTheory FinitePicard KZCollar PowerAsymptotic
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [FiniteDimensional ℝ A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] [FiniteDimensional ℝ A] in
private theorem mass_bound {Ω : ℝ → A} (hc : ContinuousOn Ω (Icc 0 1)) {C : ℝ}
    (h : ∀ t∈Icc 0 1,‖Ω t‖≤C) : integralNorm Ω 0 1≤C := by
  calc
    _ ≤ ∫ t in (0:ℝ)..1,C := intervalIntegral.integral_mono_on (by norm_num)
      (hc.intervalIntegrable_of_Icc (by norm_num)).norm intervalIntegrable_const h
    _ = C := by simp

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem arc_transport_error (X Y : A) (N : ℕ) :
    PowerSmall (fun r => transport (arcForm X Y r) 0 N 1-
      transport (fun _ => angular • X) 0 N 1) := by
  let C := 2*Real.pi*‖Y‖
  let L := Real.pi*‖X‖+C
  apply transport_perturbation_powerSmall (L:=fun _ => L) (E:=fun r => C*r)
    ?_ (const_subpower L) (linear_powerSmall C) N
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)).filter_mono nhdsWithin_le_nhds] with r hr hr1
  have hc := arcForm_continuousOn X Y hr (by linarith : r<1)
  have hb := norm_arcForm_sub_le X Y hr hr1.le
  have hC : 0≤C := by dsimp [C]; positivity
  have he : C*r≤C := mul_le_of_le_one_right hC (by linarith)
  have hX : ‖angular • X‖=Real.pi*‖X‖ := by rw [norm_smul,norm_angular]
  refine ⟨by norm_num,hc.intervalIntegrable_of_Icc (by norm_num),intervalIntegrable_const,
    by dsimp [L]; positivity,mul_nonneg hC hr.le,?_,?_,?_⟩
  · apply mass_bound hc
    intro t ht
    have hh := norm_le_norm_add_norm_sub (angular • X) (arcForm X Y r t)
    rw [hX,norm_sub_rev] at hh
    exact hh.trans (add_le_add le_rfl ((hb t).trans he))
  · apply mass_bound continuousOn_const
    intro t ht
    rw [hX]
    exact le_add_of_nonneg_right hC
  · exact mass_bound (hc.sub continuousOn_const) (fun t _ => hb t)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem gauge_exp_smul_commute (X : A) (r : ℝ) (c : ℂ) :
    Commute (gauge X r) (NormedSpace.exp (c • X)) := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  exact (((Commute.refl X).smul_left (Real.log r)).smul_right c).exp_left.exp_right

theorem arc_normalized_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) :
    Tendsto (fun r => gauge (-X) r*transport (arcForm X Y r) 0 F.cutoff 1*gauge X r)
      (𝓝[>] 0) (𝓝 (NormedSpace.exp (angular • X))) := by
  have hX' : X∈F.space 1 := by simpa using hX 1
  have hn := pow_cutoff_eq_zero F hX'
  have hneg := pow_cutoff_eq_zero F ((F.space 1).neg_mem hX')
  have herr := normalized_perturbation_limit (arc_transport_error X Y F.cutoff)
    (gauge_subpower hneg) (gauge_subpower hn)
  have hc := constant_transport F (hX angular)
  have he : ∀ r,gauge (-X) r*transport (fun _ => angular • X) 0 F.cutoff 1*gauge X r=
      NormedSpace.exp (angular • X) := by
    intro r
    have hcmt := gauge_exp_smul_commute (-X) r (-angular)
    simp only [neg_smul,smul_neg,neg_neg] at hcmt
    rw [hc,hcmt.eq]
    rw [mul_assoc,gauge_neg_mul,mul_one]
  simp only [he] at herr
  have hh := herr.add_const (NormedSpace.exp (angular • X))
  simpa only [sub_add_cancel,zero_add] using hh

end

open Set Filter FinitePicard KZCollar
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem normalized_cycle (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1)
    {r : ℝ} (hr : 0<r) (hr1 : r<1/2) :
    (gauge (-X) r*transport (arcForm X Y r) 0 F.cutoff 1*gauge X r)*
      (gauge (-X) r*transport (bulkForm (-X-Y) X) r F.cutoff (bulkEndpoint r)*gauge (-X-Y) r)*
      (gauge (-(-X-Y)) r*transport (arcForm (-X-Y) X r) 0 F.cutoff 1*gauge (-X-Y) r)*
      (gauge (-(-X-Y)) r*transport (bulkForm Y (-X-Y)) r F.cutoff (bulkEndpoint r)*gauge Y r)*
      (gauge (-Y) r*transport (arcForm Y (-X-Y) r) 0 F.cutoff 1*gauge Y r)*
      (gauge (-Y) r*transport (bulkForm X Y) r F.cutoff (bulkEndpoint r)*gauge X r)=1 := by
  have hg (u v : A) : gauge u r*(gauge (-u) r*v)=v := by
    rw [←mul_assoc,gauge_mul_neg,one_mul]
  simp only [mul_assoc,hg]
  have h := bulk_arc_identity F hX hY hr hr1
  have hh := congrArg (fun v => gauge (-X) r*v*gauge X r) h
  simpa only [mul_assoc,one_mul,gauge_neg_mul] using hh

theorem associator_hexagon (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1) :
    NormedSpace.exp (angular • X)*associator F (-X-Y) X*
      NormedSpace.exp (angular • (-X-Y))*associator F Y (-X-Y)*
      NormedSpace.exp (angular • Y)*associator F X Y=1 := by
  have hX' : X∈F.space 1 := by simpa using hX 1
  have hY' : Y∈F.space 1 := by simpa using hY 1
  have hZ : ∀ c : ℂ,c • (-X-Y)∈F.space 1 := by
    intro c
    rw [smul_sub,smul_neg]
    exact (F.space 1).sub_mem ((F.space 1).neg_mem (hX c)) (hY c)
  have hZ' : -X-Y∈F.space 1 := by simpa using hZ 1
  have ht := (((((arc_normalized_limit F hX (Y:=Y)).mul
    (bulk_normalized_limit F hZ' hX')).mul (arc_normalized_limit F hZ (Y:=X))).mul
    (bulk_normalized_limit F hY' hZ')).mul (arc_normalized_limit F hY (Y:=-X-Y))).mul
    (bulk_normalized_limit F hX' hY')
  apply tendsto_nhds_unique ht
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)).filter_mono nhdsWithin_le_nhds] with r hr hr1
  exact (normalized_cycle F hX hY hr hr1).symm

end ComplexKZ

namespace PairedHexagon
variable {G : Type*} [Group G]

 theorem meridian (a b c P Q R : G)
    (hp : a*R*c*Q*b*P=1) (hm : a⁻¹*R*c⁻¹*Q*b⁻¹*P=1) :
    R*c^2*R⁻¹=a⁻¹*(P⁻¹*b^2*P)⁻¹*a⁻¹ := by
  have h₁ : R*c*Q=a⁻¹*P⁻¹*b⁻¹ := by
    calc R*c*Q=a⁻¹*(a*R*c*Q*b*P)*P⁻¹*b⁻¹ := by group
         _=a⁻¹*P⁻¹*b⁻¹ := by rw [hp]; group
  have h₂ : R*c⁻¹*Q=a*P⁻¹*b := by
    calc R*c⁻¹*Q=a*(a⁻¹*R*c⁻¹*Q*b⁻¹*P)*P⁻¹*b := by group
         _=a*P⁻¹*b := by rw [hm]; group
  calc R*c^2*R⁻¹=(R*c*Q)*(R*c⁻¹*Q)⁻¹ := by rw [pow_two]; group
       _=(a⁻¹*P⁻¹*b⁻¹)*(a*P⁻¹*b)⁻¹ := by rw [h₁,h₂]
       _=a⁻¹*(P⁻¹*b^2*P)⁻¹*a⁻¹ := by group

 theorem compared_meridian (θ : G →* G) (a b c P Q R V W T : G)
    (hp : a*R*c*Q*b*P=1) (hm : a⁻¹*R*c⁻¹*Q*b⁻¹*P=1)
    (hv : a*T*c*W*b*V=1) (hn : a⁻¹*T*c⁻¹*W*b⁻¹*V=1)
    (ha : θ a=a) (hb : θ (P⁻¹*b^2*P)=V⁻¹*b^2*V) :
    θ (R*c^2*R⁻¹)=T*c^2*T⁻¹ := by
  rw [meridian a b c P Q R hp hm, map_mul,map_mul,map_inv,ha,map_inv,hb,
    meridian a b c V W T hv hn]

 theorem compared_middle (θ : G →* G) (a b c P Q R V W T U H : G)
    (hp : a*R*c*Q*b*P=1) (hv : a*T*c*W*b*V=1)
    (ha : θ a=a) (hb : θ b=U⁻¹*b*U) (hc : θ c=H⁻¹*c*H)
    (hP : U*θ P=V) (hR : θ R=T*H) :
    H*θ Q*U⁻¹=W := by
  have hh := congrArg θ hp
  simp only [map_mul,map_one,ha,hb,hc,hR] at hh
  have he : a*T*c*(H*θ Q*U⁻¹)*b*V=1 := by
    rw [←hP]
    convert hh using 1; group
  have heq : a*T*c*(H*θ Q*U⁻¹)*b*V=a*T*c*W*b*V := he.trans hv.symm
  exact mul_left_cancel (mul_right_cancel (mul_right_cancel heq))
end PairedHexagon

namespace NilpotentExp
open FinitePicard KZCollar
variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A]

 theorem power_difference (F : NilpotentFiltration A) {a b : A}
    (ha : a∈F.space 1) (hb : b∈F.space 1) {n : ℕ} (hd : a-b∈F.space n) (k : ℕ) :
    a^(k+1)-b^(k+1)∈F.space (n+k) := by
  induction k with
  | zero => simpa only [Nat.zero_add,pow_one,Nat.add_zero] using hd
  | succ k ih =>
    have he : a^(k+1+1)-b^(k+1+1)=(a-b)*b^(k+1)+a*(a^(k+1)-b^(k+1)) := by
      simp only [pow_succ',sub_mul,mul_sub]
      abel
    rw [he]
    apply (F.space (n+(k+1))).add_mem
    · exact F.mul_mem n (k+1) hd (pow_mem F hb (k+1))
    · simpa only [show 1+(n+k)=n+(k+1) by omega] using F.mul_mem 1 (n+k) ha ih

 theorem exp_linear (F : NilpotentFiltration A) {a : A} (ha : a∈F.space 1) :
    NormedSpace.exp a=1+a+∑ i∈Finset.range (F.cutoff+1),
      (((i+2).factorial:ℝ)⁻¹) • a^(i+2) := by
  have hz : a^(F.cutoff+2+1)=0 := pow_eq_zero_of_le (by omega) (pow_cutoff_eq_zero F ha)
  have hh := exp_smul_finite a hz 1
  simp only [one_smul,one_pow,one_div] at hh
  rw [Finset.sum_range_succ',Finset.sum_range_succ'] at hh
  simp only [pow_zero,pow_one,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,
    inv_one,one_smul,Nat.zero_add] at hh
  simp only [show ∀ k : ℕ,k+1+1=k+2 from fun k => by omega] at hh
  rw [hh]
  abel

 theorem exp_difference (F : NilpotentFiltration A) {a b : A}
    (ha : a∈F.space 1) (hb : b∈F.space 1) {n : ℕ} (hd : a-b∈F.space n) :
    NormedSpace.exp a-NormedSpace.exp b-(a-b)∈F.space (n+1) := by
  rw [exp_linear F ha,exp_linear F hb]
  have he : 1+a+(∑ i∈Finset.range (F.cutoff+1),(((i+2).factorial:ℝ)⁻¹) • a^(i+2))-
      (1+b+(∑ i∈Finset.range (F.cutoff+1),(((i+2).factorial:ℝ)⁻¹) • b^(i+2)))-(a-b)=
      ∑ i∈Finset.range (F.cutoff+1),(((i+2).factorial:ℝ)⁻¹) • (a^(i+2)-b^(i+2)) := by
    simp only [smul_sub,Finset.sum_sub_distrib]
    abel
  rw [he]
  apply Submodule.sum_mem
  intro i hi
  apply (F.space (n+1)).smul_mem
  exact F.antitone (by omega : n+1≤n+(i+1)) (power_difference F ha hb hd (i+1))

 theorem injective (F : NilpotentFiltration A) {a b : A}
    (ha : a∈F.space 1) (hb : b∈F.space 1) (he : NormedSpace.exp a=NormedSpace.exp b) : a=b := by
  have hh : ∀ n,a-b∈F.space (n+1) := by
    intro n
    induction n with
    | zero => exact (F.space 1).sub_mem ha hb
    | succ n ih =>
      have hc := exp_difference F ha hb ih
      rw [he,sub_self,zero_sub] at hc
      exact (F.space (n+1+1)).neg_mem_iff.mp hc
  have ht := hh F.cutoff
  simpa only [F.terminal,Submodule.mem_bot,sub_eq_zero] using ht

variable [NormedRing B] [NormedAlgebra ℝ B]
end NilpotentExp

namespace HexagonUnits
open FinitePicard KZCollar
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [FiniteDimensional ℝ A]

local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A

def phi (F : NilpotentFiltration A) {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1) : Aˣ :=
  (associator_isUnit F hX hY).unit
@[simp] theorem phi_val (F : NilpotentFiltration A) {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    (phi F hX hY:A)=associator F X Y := (associator_isUnit F hX hY).unit_spec

theorem phi_swap (F : NilpotentFiltration A) {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    phi F hY hX=(phi F hX hY)⁻¹ := by
  apply Units.ext
  rw [phi_val,associator_swap F hX hY,←phi_val F hX hY,Ring.inverse_unit]

theorem positive (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1)
    (hX' : X∈F.space 1) (hY' : Y∈F.space 1) (hZ : -X-Y∈F.space 1) :
    exp (ComplexKZ.angular • X)*phi F hZ hX'*exp (ComplexKZ.angular • (-X-Y))*
      phi F hY' hZ*exp (ComplexKZ.angular • Y)*phi F hX' hY'=1 := by
  apply Units.ext
  simpa only [Units.val_mul,exp_val,phi_val,Units.val_one] using
    ComplexKZ.associator_hexagon F hX hY

theorem negative (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1)
    (hX' : X∈F.space 1) (hY' : Y∈F.space 1) (hZ : -X-Y∈F.space 1) :
    (exp (ComplexKZ.angular • X))⁻¹*phi F hZ hX'*(exp (ComplexKZ.angular • (-X-Y)))⁻¹*
      phi F hY' hZ*(exp (ComplexKZ.angular • Y))⁻¹*phi F hX' hY'=1 := by
  have hz : -Y-X= -X-Y := by abel
  have hh := positive F hY hX hY' hX' (hz.symm ▸ hZ)
  simp only [hz,phi_swap F hX' hY',phi_swap F hY' hZ,phi_swap F hZ hX'] at hh
  have hi := congrArg (fun u : Aˣ => (phi F hX' hY')⁻¹*u⁻¹*phi F hX' hY') hh
  convert hi using 1 <;> group

 omit [FiniteDimensional ℝ A] in
 theorem exp_square (a : A) : ((exp a)^2:Aˣ)=exp ((2:ℝ) • a) := by
  apply Units.ext
  simp only [pow_two,Units.val_mul,exp_val,show (2:ℝ) • a=a+a from by simpa using (two_smul ℝ a),
    NormedSpace.exp_add_of_commute (Commute.refl a)]

 theorem exp_map (f : A →ₐ[ℝ] A) (a : A) : Units.map f.toMonoidHom (exp a)=exp (f a) := by
  apply Units.ext
  change f (exp a:A)=(exp (f a):A)
  rw [exp_val,exp_val]
  exact NormedSpace.map_exp f f.toLinearMap.toContinuousLinearMap.continuous a

 omit [FiniteDimensional ℝ A] in
 theorem exp_conj (u : Aˣ) (a : A) : exp ((u:A)*a*((u⁻¹:Aˣ):A))=u*exp a*u⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul,exp_val,NormedSpace.exp_units_conj]
end HexagonUnits

namespace ComplexCutoff
open AssociativeElimination
variable {α : Type*} [Finite α]
variable (P : Set (A ℂ α)) (N : ℕ)

instance normedRing : NormedRing (TruncatedWords.Q P N) :=
  FiniteAlgebraNorm.normedRingOver ℂ _
instance normedAlgebraComplex : NormedAlgebra ℂ (TruncatedWords.Q P N) :=
  FiniteAlgebraNorm.normedAlgebraOver ℂ _
instance normedAlgebraReal : NormedAlgebra ℝ (TruncatedWords.Q P N) :=
  NormedAlgebra.complexToReal
instance finiteReal : FiniteDimensional ℝ (TruncatedWords.Q P N) :=
  Module.Finite.trans ℂ (TruncatedWords.Q P N)

def filtration : FinitePicard.NilpotentFiltration (TruncatedWords.Q P N) where
  space n := (TruncatedWords.filtration P N n).restrictScalars ℝ
  antitone := TruncatedWords.filtration_antitone P N
  one_mem := TruncatedWords.filtration_one P N
  mul_mem := TruncatedWords.filtration_mul P N
  cutoff := N
  terminal := by rw [TruncatedWords.filtration_terminal]; rfl

end ComplexCutoff

namespace ComplexComparison

section
open CutoffDepth HexagonUnits
abbrev F (N : ℕ) := ComplexCutoff.filtration (∅ : Set (AssociativeElimination.A ℂ Bool)) N
abbrev X (N : ℕ) : Q ℂ N := gen N false
abbrev Y (N : ℕ) : Q ℂ N := gen N true
abbrev Z (N : ℕ) : Q ℂ N := -X N-Y N

theorem xm (N : ℕ) : X N∈(F N).space 1 := gen_weight N false
theorem ym (N : ℕ) : Y N∈(F N).space 1 := gen_weight N true
theorem zm (N : ℕ) : Z N∈(F N).space 1 := ((F N).space 1).sub_mem (((F N).space 1).neg_mem (xm N)) (ym N)
theorem xc (N : ℕ) (c : ℂ) : c • X N∈(F N).space 1 :=
  (TruncatedWords.filtration ∅ N 1).smul_mem c (gen_weight (R:=ℂ) N false)
theorem yc (N : ℕ) (c : ℂ) : c • Y N∈(F N).space 1 :=
  (TruncatedWords.filtration ∅ N 1).smul_mem c (gen_weight (R:=ℂ) N true)

def P (N : ℕ) : (Q ℂ N)ˣ := phi (F N) (xm N) (ym N)
def Qq (N : ℕ) : (Q ℂ N)ˣ := phi (F N) (ym N) (zm N)
def Rr (N : ℕ) : (Q ℂ N)ˣ := phi (F N) (zm N) (xm N)
def V (N : ℕ) : (Q ℂ N)ˣ := phi (F N) (((F N).space 1).neg_mem (xm N)) (((F N).space 1).neg_mem (ym N))
def W (N : ℕ) : (Q ℂ N)ˣ := phi (F N) (((F N).space 1).neg_mem (ym N)) (((F N).space 1).neg_mem (zm N))
def T (N : ℕ) : (Q ℂ N)ˣ := phi (F N) (((F N).space 1).neg_mem (zm N)) (((F N).space 1).neg_mem (xm N))
abbrev a (N : ℕ) := exp (ComplexKZ.angular • X N)
abbrev b (N : ℕ) := exp (ComplexKZ.angular • Y N)
abbrev c (N : ℕ) := exp (ComplexKZ.angular • Z N)

theorem p_hex (N : ℕ) : a N*Rr N*c N*Qq N*b N*P N=1 :=
  positive (F N) (xc N) (yc N) (xm N) (ym N) (zm N)
theorem p_hex_neg (N : ℕ) : (a N)⁻¹*Rr N*(c N)⁻¹*Qq N*(b N)⁻¹*P N=1 :=
  negative (F N) (xc N) (yc N) (xm N) (ym N) (zm N)

theorem v_hex (N : ℕ) : a N*T N*c N*W N*b N*V N=1 := by
  have hx : ∀ s : ℂ,s • (-X N)∈(F N).space 1 := fun s => by
    rw [smul_neg]; exact ((F N).space 1).neg_mem (xc N s)
  have hy : ∀ s : ℂ,s • (-Y N)∈(F N).space 1 := fun s => by
    rw [smul_neg]; exact ((F N).space 1).neg_mem (yc N s)
  have hz : -(-X N)-(-Y N)= -Z N := by dsimp [Z]; abel
  have hh := negative (F N) hx hy (((F N).space 1).neg_mem (xm N))
    (((F N).space 1).neg_mem (ym N)) (hz.symm ▸ ((F N).space 1).neg_mem (zm N))
  simpa only [hz,smul_neg,exp_neg,inv_inv,a,b,c,T,W,V] using hh

theorem v_hex_neg (N : ℕ) : (a N)⁻¹*T N*(c N)⁻¹*W N*(b N)⁻¹*V N=1 := by
  have hx : ∀ s : ℂ,s • (-X N)∈(F N).space 1 := fun s => by
    rw [smul_neg]; exact ((F N).space 1).neg_mem (xc N s)
  have hy : ∀ s : ℂ,s • (-Y N)∈(F N).space 1 := fun s => by
    rw [smul_neg]; exact ((F N).space 1).neg_mem (yc N s)
  have hz : -(-X N)-(-Y N)= -Z N := by dsimp [Z]; abel
  have hh := positive (F N) hx hy (((F N).space 1).neg_mem (xm N))
    (((F N).space 1).neg_mem (ym N)) (hz.symm ▸ ((F N).space 1).neg_mem (zm N))
  simpa only [hz,smul_neg,exp_neg,a,b,c,T,W,V] using hh

theorem P_weight (N : ℕ) : (P N:Q ℂ N)-1∈TruncatedWords.filtration ∅ N 1 := by
  change (phi (F N) (xm N) (ym N):Q ℂ N)-1∈(F N).space 1
  rw [phi_val]
  exact KZCollar.associator_sub_one_mem (F N)
    (by apply Submodule.ext; intro u; change u∈TruncatedWords.filtration ∅ N 0 ↔ True
        rw [TruncatedSubstitution.filtration_initial]; simp only [Submodule.mem_top]) (xm N) (ym N)
theorem V_weight (N : ℕ) : (V N:Q ℂ N)-1∈TruncatedWords.filtration ∅ N 1 := by
  change (phi (F N) _ _:Q ℂ N)-1∈(F N).space 1
  rw [phi_val]
  exact KZCollar.associator_sub_one_mem (F N)
    (by apply Submodule.ext; intro u; change u∈TruncatedWords.filtration ∅ N 0 ↔ True
        rw [TruncatedSubstitution.filtration_initial]; simp only [Submodule.mem_top])
    (((F N).space 1).neg_mem (xm N)) (((F N).space 1).neg_mem (ym N))

def theta (N : ℕ) : Q ℂ N ≃ₐ[ℂ] Q ℂ N := ConjugateComparison.theta N (P N) (V N) (P_weight N) (V_weight N)
def U (N : ℕ) : (Q ℂ N)ˣ := ConjugateComparison.unitArrow N (P N) (V N) (P_weight N) (V_weight N)
def H (N : ℕ) : (Q ℂ N)ˣ := (T N)⁻¹*Units.map (theta N).toMonoidHom (Rr N)

theorem theta_x (N : ℕ) : theta N (X N)=X N := ConjugateComparison.theta_x N _ _ _ _
theorem theta_y (N : ℕ) : theta N (Y N)=((U N)⁻¹:(Q ℂ N)ˣ)*Y N*(U N:Q ℂ N) :=
  ConjugateComparison.theta_y N _ _ _ _
theorem U_compare (N : ℕ) : U N*Units.map (theta N).toMonoidHom (P N)=V N := by
  unfold U ConjugateComparison.unitArrow theta
  group

theorem H_compare (N : ℕ) : Units.map (theta N).toMonoidHom (Rr N)=T N*H N := by
  unfold H
  group

def realMap (N : ℕ) : CutoffDepth.Q ℝ N →ₐ[ℝ] Q ℂ N :=
  NilpotentFreeLift.eval (F N) (gen N) (gen_weight N)
@[simp] theorem realMap_gen (N : ℕ) (i : Bool) : realMap N (gen N i)=gen N i :=
  NilpotentFreeLift.eval_gen _ _ _ i

theorem positive_realMap (N : ℕ) : Units.map (realMap N).toMonoidHom (KZComparison.positive N)=P N := by
  apply Units.ext
  change realMap N (KZComparison.positive N:CutoffDepth.Q ℝ N)=(P N:Q ℂ N)
  rw [KZComparison.positive_val]
  change _=(phi (F N) (xm N) (ym N):Q ℂ N)
  simp only [CutoffKZ.X,CutoffKZ.Y]
  rw [phi_val]
  have hh := KZCollar.map_associator (realMap N) (CutoffKZ.weight N) (F N) rfl
    (gen_weight (R:=ℝ) N false) (gen_weight (R:=ℝ) N true)
  change realMap N (KZCollar.associator (CutoffKZ.weight N) (gen N false) (gen N true))=
    KZCollar.associator (F N) (realMap N (gen N false)) (realMap N (gen N true)) at hh
  rw [realMap_gen,realMap_gen] at hh
  exact hh

theorem negative_realMap (N : ℕ) : Units.map (realMap N).toMonoidHom (KZComparison.negative N)=V N := by
  apply Units.ext
  change realMap N (KZComparison.negative N:CutoffDepth.Q ℝ N)=(V N:Q ℂ N)
  rw [KZComparison.negative_val]
  change _=(phi (F N) _ _:Q ℂ N)
  simp only [CutoffKZ.X,CutoffKZ.Y]
  rw [phi_val]
  have hh := KZCollar.map_associator (realMap N) (CutoffKZ.weight N) (F N) rfl
    (((CutoffKZ.weight N).space 1).neg_mem (gen_weight (R:=ℝ) N false))
    (((CutoffKZ.weight N).space 1).neg_mem (gen_weight (R:=ℝ) N true))
  change realMap N (KZCollar.associator (CutoffKZ.weight N) (-gen N false) (-gen N true))=
    KZCollar.associator (F N) (realMap N (-gen N false)) (realMap N (-gen N true)) at hh
  rw [map_neg,map_neg,realMap_gen,realMap_gen] at hh
  exact hh

theorem theta_exp (N : ℕ) (u : Q ℂ N) :
    Units.map (theta N).toMonoidHom (exp u)=exp (theta N u) :=
  exp_map ((theta N).toAlgHom.restrictScalars ℝ) u

theorem exp_smul_conj (N : ℕ) (s : ℂ) (u : (Q ℂ N)ˣ) (v : Q ℂ N) :
    exp (s • ((u:Q ℂ N)*v*((u⁻¹:(Q ℂ N)ˣ):Q ℂ N)))=u*exp (s • v)*u⁻¹ := by
  rw [←smul_mul_assoc,←mul_smul_comm,exp_conj]

theorem theta_a (N : ℕ) : Units.map (theta N).toMonoidHom (a N)=a N := by
  rw [a,theta_exp,map_smul,theta_x]

theorem theta_b (N : ℕ) : Units.map (theta N).toMonoidHom (b N)=(U N)⁻¹*b N*U N := by
  rw [b,theta_exp,map_smul,theta_y]
  simpa only [inv_inv] using exp_smul_conj N ComplexKZ.angular (U N)⁻¹ (Y N)

theorem theta_meridian_y (N : ℕ) :
    Units.map (theta N).toMonoidHom ((P N)⁻¹*(b N)^2*P N)=(V N)⁻¹*(b N)^2*V N := by
  rw [map_mul,map_mul,map_inv,map_pow,theta_b,←U_compare N]
  simp only [pow_two]
  group

theorem theta_meridian_z (N : ℕ) :
    Units.map (theta N).toMonoidHom ((c N)^2)=(H N)⁻¹*(c N)^2*H N := by
  have hh := PairedHexagon.compared_meridian (Units.map (theta N).toMonoidHom)
    (a N) (b N) (c N) (P N) (Qq N) (Rr N) (V N) (W N) (T N)
    (p_hex N) (p_hex_neg N) (v_hex N) (v_hex_neg N) (theta_a N) (theta_meridian_y N)
  simp only [map_mul,map_inv,H_compare] at hh
  have hi := congrArg (fun u : (Q ℂ N)ˣ => (H N)⁻¹*(T N)⁻¹*u*T N*H N) hh
  convert hi using 1 <;> group

theorem conj_weight (N n : ℕ) (u : (Q ℂ N)ˣ) {v : Q ℂ N}
    (hv : v∈TruncatedWords.filtration ∅ N n) :
    (u:Q ℂ N)*v*((u⁻¹:(Q ℂ N)ˣ):Q ℂ N)∈TruncatedWords.filtration ∅ N n := by
  simpa only [Nat.zero_add,Nat.add_zero] using TruncatedWords.filtration_mul ∅ N (0+n) 0
    (TruncatedWords.filtration_mul ∅ N 0 n (ConjugateComparison.mem_zero N (u:Q ℂ N)) hv)
    (ConjugateComparison.mem_zero N ((u⁻¹:(Q ℂ N)ˣ):Q ℂ N))

theorem theta_z (N : ℕ) : theta N (Z N)=((H N)⁻¹:(Q ℂ N)ˣ)*Z N*(H N:Q ℂ N) := by
  let s : ℂ := ComplexKZ.angular+ComplexKZ.angular
  have hs : s≠0 := by
    have ha : ComplexKZ.angular≠0 := by
      intro h
      have hn := ComplexKZ.norm_angular
      rw [h,norm_zero] at hn
      exact Real.pi_ne_zero hn.symm
    dsimp [s]
    intro h
    apply ha
    have h2 : (2:ℂ)*ComplexKZ.angular=0 := by linear_combination h
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have hc : (c N)^2=exp (s • Z N) := by
    rw [c,exp_square,two_smul ℝ,←add_smul]
  have hh := theta_meridian_z N
  rw [hc,theta_exp,map_smul] at hh
  have he : exp (s • theta N (Z N))=
      exp (s • (((H N)⁻¹:(Q ℂ N)ˣ)*Z N*(H N:Q ℂ N))) := by
    rw [hh]
    have hh := exp_smul_conj N s (H N)⁻¹ (Z N)
    simpa only [inv_inv] using hh.symm
  have hv := congrArg Units.val he
  simp only [exp_val] at hv
  have h₁ : s • theta N (Z N)∈(F N).space 1 :=
    (TruncatedWords.filtration ∅ N 1).smul_mem s
      (ConjugateComparison.theta_preserves N (P N) (V N) (P_weight N) (V_weight N) 1 (Z N) (zm N))
  have h₂ : s • (((H N)⁻¹:(Q ℂ N)ˣ)*Z N*(H N:Q ℂ N))∈(F N).space 1 :=
    (TruncatedWords.filtration ∅ N 1).smul_mem s
      (by simpa only [inv_inv] using conj_weight N 1 (H N)⁻¹ (zm N))
  exact smul_right_injective (Q ℂ N) hs (NilpotentExp.injective (F N) h₁ h₂ hv)

theorem theta_c (N : ℕ) : Units.map (theta N).toMonoidHom (c N)=(H N)⁻¹*c N*H N := by
  rw [c,theta_exp,map_smul,theta_z]
  simpa only [inv_inv] using exp_smul_conj N ComplexKZ.angular (H N)⁻¹ (Z N)

theorem middle_compare (N : ℕ) : H N*Units.map (theta N).toMonoidHom (Qq N)*(U N)⁻¹=W N :=
  PairedHexagon.compared_middle (Units.map (theta N).toMonoidHom)
    (a N) (b N) (c N) (P N) (Qq N) (Rr N) (V N) (W N) (T N) (U N) (H N)
    (p_hex N) (v_hex N) (theta_a N) (theta_b N) (theta_c N) (U_compare N) (H_compare N)

def rho (N : ℕ) : Q ℂ N →ₐ[ℂ] Q ℂ N :=
  TruncatedSubstitution.subst N (fun i => if i then Z N else Y N)
    (fun i => by cases i; exact ym N; exact zm N)
@[simp] theorem rho_x (N : ℕ) : rho N (X N)=Y N := TruncatedSubstitution.subst_gen N _ _ false
@[simp] theorem rho_y (N : ℕ) : rho N (Y N)=Z N := TruncatedSubstitution.subst_gen N _ _ true
@[simp] theorem rho_z (N : ℕ) : rho N (Z N)=X N := by
  rw [Z,map_sub,map_neg,rho_x,rho_y]
  dsimp [Z]
  abel

theorem rho_phi (N : ℕ) {x y : Q ℂ N}
    (hx : x∈(F N).space 1) (hy : y∈(F N).space 1)
    (hrx : rho N x∈(F N).space 1) (hry : rho N y∈(F N).space 1) :
    Units.map (rho N).toMonoidHom (phi (F N) hx hy)=phi (F N) hrx hry := by
  apply Units.ext
  change rho N (phi (F N) hx hy:Q ℂ N)=(phi (F N) hrx hry:Q ℂ N)
  rw [phi_val,phi_val]
  exact KZCollar.map_associator ((rho N).restrictScalars ℝ) (F N) (F N) rfl hx hy

theorem rho_P (N : ℕ) : Units.map (rho N).toMonoidHom (P N)=Qq N := by
  have hh := rho_phi N (xm N) (ym N) (by rw [rho_x]; exact ym N) (by rw [rho_y]; exact zm N)
  simpa only [rho_x,rho_y,P,Qq,X,Y] using hh

theorem rho_R (N : ℕ) : Units.map (rho N).toMonoidHom (Rr N)=P N := by
  have hh := rho_phi N (zm N) (xm N) (by rw [rho_z]; exact xm N) (by rw [rho_x]; exact ym N)
  simpa only [rho_z,rho_x,Rr,P,X,Y] using hh

theorem rho_V (N : ℕ) : Units.map (rho N).toMonoidHom (V N)=W N := by
  have hh := rho_phi N (((F N).space 1).neg_mem (xm N)) (((F N).space 1).neg_mem (ym N))
    (by rw [map_neg,rho_x]; exact ((F N).space 1).neg_mem (ym N))
    (by rw [map_neg,rho_y]; exact ((F N).space 1).neg_mem (zm N))
  simpa only [map_neg,rho_x,rho_y,V,W,X,Y] using hh

theorem rho_T (N : ℕ) : Units.map (rho N).toMonoidHom (T N)=V N := by
  have hh := rho_phi N (((F N).space 1).neg_mem (zm N)) (((F N).space 1).neg_mem (xm N))
    (by rw [map_neg,rho_z]; exact ((F N).space 1).neg_mem (xm N))
    (by rw [map_neg,rho_x]; exact ((F N).space 1).neg_mem (ym N))
  simpa only [map_neg,rho_z,rho_x,T,V,X,Y] using hh

 theorem transport_y (N : ℕ) (p : (Q ℂ N)ˣ) (hp : (p:Q ℂ N)-1∈TruncatedWords.filtration ∅ N 1) :
    ConjugateComparison.transport N p hp (Y N)=UnitConjugation.hom (R:=ℂ) p⁻¹ (Y N) := by
  change ConjugateComparison.transport N p hp (TruncatedSubstitution.gen N true)=_
  rw [ConjugateComparison.transport_gen,ConjugateComparison.family,UnitConjugation.hom_apply,inv_inv]
  rfl

theorem rho_theta (N : ℕ) (u : Q ℂ N) :
    rho N (theta N u)=UnitConjugation.hom (R:=ℂ) (U N) (theta N (rho N u)) := by
  let τ := ConjugateComparison.transport N (P N) (P_weight N)
  have he : ((rho N).comp (theta N).toAlgHom).comp τ.toAlgHom=
      ((UnitConjugation.hom (R:=ℂ) (U N)).comp ((theta N).toAlgHom.comp (rho N))).comp τ.toAlgHom := by
    apply TruncatedSubstitution.hom_ext N
    intro i
    cases i
    · change rho N (theta N (τ (X N)))=UnitConjugation.hom (R:=ℂ) (U N) (theta N (rho N (τ (X N))))
      have hτ : τ (X N)=X N := ConjugateComparison.transport_gen N _ _ false
      rw [hτ,theta_x,rho_x,theta_y]
      simp only [UnitConjugation.hom_apply,mul_assoc,Units.mul_inv_cancel_left,Units.mul_inv,mul_one]
    · change rho N (theta N (τ (Y N)))=UnitConjugation.hom (R:=ℂ) (U N) (theta N (rho N (τ (Y N))))
      have h₁ : theta N (τ (Y N))=ConjugateComparison.transport N (V N) (V_weight N) (Y N) :=
        ConjugateComparison.theta_transport N _ _ _ _ _
      rw [h₁,transport_y,UnitConjugation.natural,map_inv,rho_V,rho_y]
      change UnitConjugation.hom (R:=ℂ) (W N)⁻¹ (Z N)=_
      rw [show τ (Y N)=UnitConjugation.hom (R:=ℂ) (P N)⁻¹ (Y N) from transport_y N _ _,
        UnitConjugation.natural,map_inv,rho_P,rho_y]
      rw [show theta N (UnitConjugation.hom (R:=ℂ) (Qq N)⁻¹ (Z N))=
        UnitConjugation.hom (R:=ℂ) (Units.map (theta N).toMonoidHom ((Qq N)⁻¹)) (theta N (Z N)) from
        UnitConjugation.natural (theta N).toAlgHom (Qq N)⁻¹ (Z N),map_inv]
      have hz : theta N (Z N)=UnitConjugation.hom (R:=ℂ) (H N)⁻¹ (Z N) := by
        simpa only [UnitConjugation.hom_apply,inv_inv] using theta_z N
      rw [hz,←UnitConjugation.mul_apply,←UnitConjugation.mul_apply]
      have hm : U N*(Units.map (theta N).toMonoidHom (Qq N))⁻¹*(H N)⁻¹=(W N)⁻¹ := by
        rw [←middle_compare N]
        group
      rw [hm]
  obtain ⟨v,rfl⟩ := τ.surjective u
  exact AlgHom.congr_fun he v

theorem rho_theta_unit (N : ℕ) (u : (Q ℂ N)ˣ) :
    Units.map (rho N).toMonoidHom (Units.map (theta N).toMonoidHom u)=
      U N*Units.map (theta N).toMonoidHom (Units.map (rho N).toMonoidHom u)*(U N)⁻¹ := by
  apply Units.ext
  exact rho_theta N (u:Q ℂ N)

theorem rho_U (N : ℕ) : Units.map (rho N).toMonoidHom (U N)=H N*(U N)⁻¹ := by
  change Units.map (rho N).toMonoidHom (V N*(Units.map (theta N).toMonoidHom (P N))⁻¹)=_
  rw [map_mul,map_inv,rho_V,rho_theta_unit,rho_P,←middle_compare N]
  group

theorem rho_H (N : ℕ) : Units.map (rho N).toMonoidHom (H N)=(U N)⁻¹ := by
  rw [H,map_mul,map_inv,rho_T,rho_theta_unit,rho_R,←U_compare N]
  group

end

section
open CutoffDepth

def cycle : Fin 3 → Fin 3 := ![1,2,0]
def frames (N : ℕ) : Fin 3 → (Q ℂ N)ˣ := ![1,U N,H N]
def rationalWeight (N n : ℕ) : Submodule ℚ (Q ℂ N) :=
  (TruncatedWords.filtration ∅ N n).restrictScalars ℚ

theorem rationalWeight_initial (N : ℕ) : rationalWeight N 0=⊤ := by
  apply Submodule.ext
  intro u
  change u∈TruncatedWords.filtration ∅ N 0 ↔ True
  rw [TruncatedSubstitution.filtration_initial]
  simp only [Submodule.mem_top]
theorem rationalWeight_terminal (N : ℕ) : rationalWeight N (N+2)=⊥ := by
  apply eq_bot_iff.mpr
  intro u hu
  have hh := TruncatedWords.filtration_antitone ∅ N (show N+1≤N+2 by omega) hu
  simpa only [TruncatedWords.filtration_terminal,Submodule.mem_bot] using hh

theorem U_weight (N : ℕ) : (U N:Q ℂ N)-1∈TruncatedWords.filtration ∅ N 1 :=
  ConjugateComparison.unitArrow_normalized N _ _ _ _

theorem H_weight (N : ℕ) : (H N:Q ℂ N)-1∈TruncatedWords.filtration ∅ N 1 := by
  have he : H N=Units.map (rho N).toMonoidHom (U N)*U N := by rw [rho_U]; group
  rw [he]
  apply ConjugateComparison.mul_normalized N _ _ _ (U_weight N)
  have hh := TruncatedSubstitution.subst_preserves N
    (fun i => if i then Z N else Y N) (fun i => by cases i; exact ym N; exact zm N)
    1 ((U N:Q ℂ N)-1) (U_weight N)
  change rho N ((U N:Q ℂ N)-1)∈_ at hh
  change rho N (U N:Q ℂ N)-1∈_
  simpa only [map_sub,map_one] using hh

theorem frames_weight (N : ℕ) (p : Fin 3) : (frames N p:Q ℂ N)-1∈rationalWeight N 1 := by
  fin_cases p
  · change (1:Q ℂ N)-1∈_
    simp only [sub_self,Submodule.zero_mem]
  · exact U_weight N
  · exact H_weight N

def category (N : ℕ) : LogCategory.Data (Q ℂ N) (Fin 3) :=
  GaugeAutomorphism.data ((theta N).restrictScalars ℚ) (frames N) (rationalWeight N) (N+1)
    (TruncatedWords.filtration_antitone ∅ N) (rationalWeight_initial N) (rationalWeight_terminal N)
    (TruncatedWords.filtration_mul ∅ N)
    (ConjugateComparison.theta_raises N (P N) (V N) (P_weight N) (V_weight N)) (frames_weight N)

def value (N : ℕ) : Q ℂ N := LogCategory.delta (category N) 0 1 1

theorem rho_frames (N : ℕ) (p : Fin 3) :
    Units.map (rho N).toMonoidHom (frames N p)=frames N (cycle p)*(U N)⁻¹ := by
  fin_cases p
  · simp [frames,cycle]
  · exact rho_U N
  · change Units.map (rho N).toMonoidHom (H N)=1*(U N)⁻¹
    simpa only [one_mul] using rho_H N

theorem category_rotate (N : ℕ) (p q : Fin 3) (u : Q ℂ N) :
    rho N ((category N).S p q u)=(category N).S (cycle p) (cycle q) (rho N u) := by
  have hf (p : Fin 3) : rho N (frames N p:Q ℂ N)=(frames N (cycle p)*(U N)⁻¹:(Q ℂ N)ˣ) :=
    congrArg Units.val (rho_frames N p)
  have hi (p : Fin 3) : rho N (((frames N p)⁻¹:(Q ℂ N)ˣ):Q ℂ N)=
      ((frames N (cycle p)*(U N)⁻¹)⁻¹:(Q ℂ N)ˣ) :=
    congrArg (fun v => ((v⁻¹:(Q ℂ N)ˣ):Q ℂ N)) (rho_frames N p)
  simp only [category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,
    AlgEquiv.restrictScalars_apply,map_mul,hf,hi,rho_theta,UnitConjugation.hom_apply,
    Units.val_mul,mul_inv_rev,inv_inv,mul_assoc,Units.inv_mul_cancel_left]

theorem delta_rotate (N : ℕ) (p q : Fin 3) (u : Q ℂ N) :
    rho N (LogCategory.delta (category N) p q u)=
      LogCategory.delta (category N) (cycle p) (cycle q) (rho N u) := by
  exact OperatorLog.logarithm_natural (category N).N
    ((category N).S p q-1) ((category N).S (cycle p) (cycle q)-1)
    ((rho N).toLinearMap.restrictScalars ℚ) (by
      intro v
      change rho N ((category N).S p q v-v)=_
      rw [map_sub,category_rotate]
      rfl) u

theorem value_cyclic (N : ℕ) : value N+rho N (value N)+rho N (rho N (value N))=0 := by
  have h₁ : rho N (value N)=LogCategory.delta (category N) 1 2 1 := by
    simpa only [value,cycle,Matrix.cons_val_zero,Matrix.cons_val_one,map_one] using delta_rotate N 0 1 1
  have h₂ : rho N (rho N (value N))=LogCategory.delta (category N) 2 0 1 := by
    rw [h₁,delta_rotate,map_one]
    rfl
  have ha := LogCategory.unit_cocycle (category N) 0 1 2
  have hb := LogCategory.unit_cocycle (category N) 0 2 0
  rw [LogCategory.delta_one_loop] at hb
  change value N+_+_=0
  rw [h₂,h₁]
  change LogCategory.delta (category N) 0 1 1+_+_=0
  rw [add_comm (LogCategory.delta (category N) 0 1 1),←ha,add_comm]
  exact hb.symm
end

open CutoffDepth ConjugateComparison WordGrading

theorem transport_realMap (N : ℕ) (p : (Q ℝ N)ˣ) (q : (Q ℂ N)ˣ)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hq : (q:Q ℂ N)-1∈TruncatedWords.filtration ∅ N 1)
    (h : Units.map (realMap N).toMonoidHom p=q) (u : Q ℝ N) :
    realMap N (transport N p hp u)=transport N q hq (realMap N u) := by
  have hv : realMap N (p:Q ℝ N)=(q:Q ℂ N) := congrArg Units.val h
  have hi : realMap N ((p⁻¹:(Q ℝ N)ˣ):Q ℝ N)=((q⁻¹:(Q ℂ N)ˣ):Q ℂ N) :=
    congrArg (fun v => ((v⁻¹:(Q ℂ N)ˣ):Q ℂ N)) h
  have he : (realMap N).comp (transport N p hp).toAlgHom=
      ((transport N q hq).restrictScalars ℝ).toAlgHom.comp (realMap N) := by
    apply TruncatedSubstitution.hom_ext N
    intro b
    change realMap N (transport N p hp (gen N b))=transport N q hq (realMap N (gen N b))
    rw [ConjugateCoalgebra.transport_cutoff_gen,realMap_gen]
    have hqg := transport_gen N q hq b
    change transport N q hq (gen N b)=_ at hqg
    rw [hqg]
    cases b
    · exact realMap_gen N false
    · change realMap N (((p⁻¹:(Q ℝ N)ˣ):Q ℝ N)*gen N true*(p:Q ℝ N))=_
      rw [map_mul,map_mul,hi,hv,realMap_gen]
      rfl
  exact AlgHom.congr_fun he u

theorem theta_realMap (N : ℕ) (u : Q ℝ N) :
    realMap N (KZComparison.theta N u)=theta N (realMap N u) := by
  change realMap N (ConjugateComparison.theta N _ _ _ _ u)=ConjugateComparison.theta N _ _ _ _ (realMap N u)
  rw [ConjugateComparison.theta,AlgEquiv.trans_apply,
    transport_realMap N _ _ (KZComparison.negative_weight N) (V_weight N) (negative_realMap N)]
  have hh := ConjugateCoalgebra.natural_inverse (realMap N)
    (transport N (KZComparison.positive N) (KZComparison.positive_weight N))
    ((transport N (P N) (P_weight N)).restrictScalars ℝ)
    (transport_realMap N _ _ (KZComparison.positive_weight N) (P_weight N) (positive_realMap N)) u
  rw [hh]
  rfl

theorem arrow_realMap (N : ℕ) : Units.map (realMap N).toMonoidHom (KZComparison.arrow N)=U N := by
  have ht : Units.map (realMap N).toMonoidHom
      (Units.map (KZComparison.theta N).toMonoidHom (KZComparison.positive N))=
      Units.map (theta N).toMonoidHom (P N) := by
    apply Units.ext
    change realMap N (KZComparison.theta N (KZComparison.positive N:Q ℝ N))=_
    rw [theta_realMap,show realMap N (KZComparison.positive N:Q ℝ N)=(P N:Q ℂ N) from congrArg Units.val (positive_realMap N)]
    rfl
  change Units.map (realMap N).toMonoidHom (KZComparison.negative N*
    (Units.map (KZComparison.theta N).toMonoidHom (KZComparison.positive N))⁻¹)=_
  rw [map_mul,map_inv,negative_realMap,ht]
  rfl

theorem S_realMap (N : ℕ) (u : Q ℝ N) :
    realMap N ((KZComparison.category N).S false true u)=(category N).S 0 1 (realMap N u) := by
  simp only [KZComparison.category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,
    KZComparison.frames,inv_one,Units.val_one,mul_one]
  change realMap N ((KZComparison.arrow N:Q ℝ N)*KZComparison.theta N u)=_
  rw [map_mul,theta_realMap,show realMap N (KZComparison.arrow N:Q ℝ N)=(U N:Q ℂ N) from congrArg Units.val (arrow_realMap N)]
  simp only [category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,frames,
    Matrix.cons_val_zero,Matrix.cons_val_one,inv_one,Units.val_one,mul_one]
  rfl

theorem value_realMap (N : ℕ) : realMap N (KZComparison.value N)=value N := by
  have hh := OperatorLog.logarithm_natural (N+1) ((KZComparison.category N).S false true-1)
    ((category N).S 0 1-1) ((realMap N).toLinearMap.restrictScalars ℚ) (by
      intro u
      change realMap N ((KZComparison.category N).S false true u-u)=_
      rw [map_sub,S_realMap]
      rfl) 1
  change realMap N (KZComparison.value N)=OperatorLog.logarithm (N+1) _ (realMap N 1) at hh
  rw [map_one] at hh
  exact hh

open AssociativeElimination

theorem realMap_word (N : ℕ) (w : FreeMonoid Bool) :
    realMap N (TruncatedWords.quotient ∅ N (word (R:=ℝ) w))=
      TruncatedWords.quotient ∅ N (word (R:=ℂ) w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [word_one,map_one]
  | of_mul a w ih =>
    rw [word_mul,word_mul,word_of,word_of,map_mul,map_mul,map_mul,ih]
    change realMap N (gen N a)*_=gen N a*_
    rw [realMap_gen]

theorem realMap_coefficient (N : ℕ) (w : FreeMonoid Bool) (u : Q ℝ N) :
    TruncatedFree.coefficient N w (realMap N u)=
      ((TruncatedFree.coefficient (R:=ℝ) N w u):ℂ) := by
  classical
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (TruncatedWords.relations (∅:Set (A ℝ Bool)) N) u
  change TruncatedFree.coefficient N w (realMap N (TruncatedWords.quotient ∅ N p))=
    ((TruncatedFree.coefficient (R:=ℝ) N w (TruncatedWords.quotient ∅ N p)):ℂ)
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change TruncatedFree.coefficient N w (realMap N (TruncatedWords.quotient ∅ N (word v)))=
      ((TruncatedFree.coefficient (R:=ℝ) N w (TruncatedWords.quotient ∅ N (word v))):ℂ)
    rw [realMap_word,TruncatedFree.coefficient_quotient,TruncatedFree.coefficient_quotient]
    simp only [word,MonoidAlgebra.coeff_single,Finsupp.single_apply]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add,hp,hq,Complex.ofReal_add]
  | smul c p hp =>
    rw [map_smul,map_smul,LinearMap.map_smul_of_tower,hp]
    rw [map_smul (TruncatedFree.coefficient (R:=ℝ) N w)]
    simp only [Complex.real_smul,smul_eq_mul,Complex.ofReal_mul]

theorem realMap_injective (N : ℕ) : Function.Injective (realMap N) := by
  intro u v huv
  apply (TruncatedFree.equiv (R:=ℝ) (α:=Bool) N).injective
  apply Subtype.ext
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  have hh := congrArg (TruncatedFree.coefficient N w) huv
  rw [realMap_coefficient,realMap_coefficient] at hh
  exact Complex.ofReal_injective hh

theorem rotate_realMap (N : ℕ) (u : Q ℝ N) : realMap N (realRotate N u)=rho N (realMap N u) := by
  have he : (realMap N).comp (realRotate N)=((rho N).restrictScalars ℝ).comp (realMap N) := by
    apply TruncatedSubstitution.hom_ext N
    intro b
    change realMap N (realRotate N (gen N b))=rho N (realMap N (gen N b))
    rw [realMap_gen,realRotate_gen]
    cases b
    · change realMap N (gen N true)=_
      rw [realMap_gen]
      exact (rho_x N).symm
    · change realMap N (-gen N false-gen N true)=_
      rw [map_sub,map_neg,realMap_gen,realMap_gen]
      exact (rho_y N).symm
  exact AlgHom.congr_fun he u

theorem real_value_cyclic_oai (N : ℕ) : KZComparison.value N+realRotate N (KZComparison.value N)+
    realRotate N (realRotate N (KZComparison.value N))=0 := by
  apply realMap_injective N
  rw [map_add,map_add,map_zero,rotate_realMap,rotate_realMap,rotate_realMap,value_realMap]
  exact value_cyclic N
end ComplexComparison

end DeligneDrinfeld

end

end OAI

end











section
open OAI.DeligneDrinfeld.ComplexComparison in
theorem solution : ∀ (N : ℕ),
    OAI.DeligneDrinfeld.KZComparison.value N +
          (OAI.DeligneDrinfeld.ComplexComparison.realRotate N) (OAI.DeligneDrinfeld.KZComparison.value N) +
        (OAI.DeligneDrinfeld.ComplexComparison.realRotate N)
          ((OAI.DeligneDrinfeld.ComplexComparison.realRotate N) (OAI.DeligneDrinfeld.KZComparison.value N)) =
      0 :=
  @OAI.DeligneDrinfeld.ComplexComparison.real_value_cyclic_oai
end
