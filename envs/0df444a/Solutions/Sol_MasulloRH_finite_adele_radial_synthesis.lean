-- Prove2me | solution 1 for MasulloRH.finite_adele_radial_synthesis
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:40:41.193174+00:00
-- url     : https://prove2.me/submissions/ad4531c7-63f1-4170-b108-3ebc97b2364f

import Definitions.Def_MasulloRH_RationalFiniteRadial
import Theorems.Thm_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff
import Mathlib
import Theorems.Thm_NumberField_AdelicBox_integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers
import Theorems.Thm_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles
import Theorems.Thm_RatIdele_sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one

section
open NumberField IsDedekindDomain
namespace MasulloRH.RationalFinite
noncomputable section

def integerSubring : Subring A where
  carrier := O
  one_mem' := fun v => one_mem (v.adicCompletionIntegers ℚ)
  add_mem' := fun hx hy v => add_mem (hx v) (hy v)
  mul_mem' := fun hx hy v => mul_mem (hx v) (hy v)
  neg_mem' := fun hx v => neg_mem (hx v)
  zero_mem' := fun v => zero_mem (v.adicCompletionIntegers ℚ)

theorem diagonal_integral_iff (q : ℚ) : diag q ∈ O ↔ ∃ m : ℤ, q = m := by
  have hh := NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff ℚ
    (1 : 𝓞 ℚ) one_ne_zero 0 q
  simp only [map_zero,map_one,zero_add,one_mul,Set.image_id'] at hh
  constructor
  · intro h
    obtain ⟨a,ha⟩ := hh.mp h
    exact ⟨Rat.ringOfIntegersEquiv a, ha.trans (Rat.ringOfIntegersEquiv_apply_coe a).symm⟩
  · rintro ⟨m,rfl⟩
    exact hh.mpr ⟨Rat.ringOfIntegersEquiv.symm m, (Rat.ringOfIntegersEquiv_symm_apply_coe m).symm⟩

theorem invert_diag_mul (r : ℚ) (hr : r ≠ 0) (x : A) : diag r⁻¹ * (diag r*x) = x := by
  rw [← mul_assoc,← map_mul,inv_mul_cancel₀ hr,map_one,one_mul]

theorem mem_centered_iff (s : ℚ) (hs : s ≠ 0) (x : A) :
    x ∈ centeredBall s ↔ diag s⁻¹ * x ∈ O := by
  constructor
  · rintro ⟨z,hz,rfl⟩
    change diag s⁻¹ * (diag s * z) ∈ O
    rwa [invert_diag_mul s hs]
  · intro hx
    refine ⟨_,hx,?_⟩
    change diag s * (diag s⁻¹ * x) = x
    rw [← mul_assoc,← map_mul,mul_inv_cancel₀ hs,map_one,one_mul]

theorem mem_translated_iff (k d : ℚ) (x : A) :
    x ∈ translatedBall k d ↔ x-diag k ∈ centeredBall d := by
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,hz,by dsimp; abel⟩
  · rintro ⟨z,hz,he⟩
    exact ⟨z,hz,by dsimp at he ⊢; rw [he]; abel⟩

theorem rational_mem_centered_iff (q s : ℚ) (hs : s ≠ 0) :
    diag q ∈ centeredBall s ↔ ∃ m : ℤ, q = s * m := by
  rw [mem_centered_iff _ hs,← map_mul,diagonal_integral_iff]
  constructor
  · rintro ⟨m,hm⟩
    exact ⟨m,by rw [←hm]; field_simp⟩
  · rintro ⟨m,rfl⟩
    exact ⟨m,by field_simp⟩

theorem int_mem_centered_nat_iff (j : ℤ) (N : ℕ) [NeZero N] :
    (j:A) ∈ centeredBall (N:ℚ) ↔ (N:ℤ) ∣ j := by
  have h := rational_mem_centered_iff (j:ℚ) (N:ℚ) (by exact_mod_cast NeZero.ne N)
  have hcast : diag (j:ℚ) = (j:A) := map_intCast _ _
  rw [hcast] at h
  rw [h]
  constructor
  · rintro ⟨m,hm⟩; exact ⟨m,by exact_mod_cast hm⟩
  · rintro ⟨m,hm⟩; exact ⟨m,by exact_mod_cast hm⟩

theorem mem_centered_sub_perturb (N : ℕ) [NeZero N] {x y : A}
    (h : x-y ∈ centeredBall (N:ℚ)) : x ∈ centeredBall (N:ℚ) ↔ y ∈ centeredBall (N:ℚ) := by
  have hN : (N:ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [mem_centered_iff _ hN,mul_sub] at h
  rw [mem_centered_iff _ hN,mem_centered_iff _ hN]
  constructor
  · intro hx
    have hz := integerSubring.sub_mem hx h
    change _ ∈ integerSubring
    simpa using hz
  · intro hy
    have hz := integerSubring.add_mem h hy
    change _ ∈ integerSubring
    simpa using hz

theorem mem_translated_unit_integer_iff {N : ℕ} [NeZero N] (u : K) (r : (ZMod N)ˣ)
    (hr : (u.val:A) - ((r.val.val:ℕ):A) ∈ centeredBall (N:ℚ)) (a m : ℤ) :
    (u.val:A) * (m:A) ∈ translatedBall (a:ℚ) (N:ℚ) ↔ r.val * (m:ZMod N) = a := by
  let j : ℤ := (r.val.val : ℤ)*m-a
  rw [mem_translated_iff]
  have hj : (u.val:A)*(m:A)-diag (a:ℚ) - (j:A) =
      ((u.val:A)-(r.val.val:A)) * (m:A) := by simp [j]; ring
  have hm : (m:A) ∈ integerSubring := intCast_mem integerSubring m
  have hdelta : (u.val:A)*(m:A)-diag (a:ℚ) - (j:A) ∈ centeredBall (N:ℚ) := by
    rw [hj]
    rcases hr with ⟨v,hv,he⟩
    exact ⟨v*(m:A),integerSubring.mul_mem hv hm,by dsimp at he ⊢; rw [←he]; ring⟩
  rw [mem_centered_sub_perturb N hdelta,int_mem_centered_nat_iff,← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp [j,sub_eq_zero]

end
end MasulloRH.RationalFinite
end

section
open NumberField IsDedekindDomain
namespace MasulloRH.RationalFinite
noncomputable section

theorem mem_translated_scale_iff (b : ℚ) (hb : b ≠ 0) (k d : ℚ) (x : A) :
    diag b * x ∈ translatedBall (b*k) (b*d) ↔ x ∈ translatedBall k d := by
  have eqn (z : A) : diag (b*k) + diag (b*d)*z = diag b*(diag k + diag d*z) := by
    simp only [map_mul]; ring
  constructor
  · rintro ⟨z,hz,he⟩
    change diag (b*k) + diag (b*d)*z = diag b*x at he
    rw [eqn] at he
    exact ⟨z,hz,by simpa only [invert_diag_mul b hb] using congrArg (fun t => diag b⁻¹*t) he⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,hz,eqn z⟩

theorem integral_of_in_translated_int_ball (a : ℤ) (N : ℕ) {x : A}
    (hx : x ∈ translatedBall (a:ℚ) (N:ℚ)) : x ∈ O := by
  rcases hx with ⟨z,hz,rfl⟩
  change diag (a:ℚ) + diag (N:ℚ) * z ∈ integerSubring
  rw [map_intCast,map_natCast]
  exact integerSubring.add_mem (intCast_mem _ _) (integerSubring.mul_mem (natCast_mem _ _) hz)

theorem integral_of_unit_mul (u : K) (x : A) (hu : (u.val:A)*x ∈ O) : x ∈ O := by
  have hi : (↑(u.val⁻¹):A) ∈ integerSubring := u.property.2
  have h := integerSubring.mul_mem hi hu
  change x ∈ integerSubring
  simpa only [← mul_assoc,Units.inv_mul,one_mul] using h

theorem mem_of_scaled_unit_iff (u : K) (b : ℚ) (hb : b ≠ 0) (a : ℤ) (N : ℕ) (q : ℚ) :
    (u.val:A) * diag q ∈ translatedBall (b*(a:ℚ)) (b*(N:ℚ)) ↔
      (u.val:A) * diag (q/b) ∈ translatedBall (a:ℚ) (N:ℚ) := by
  rw [← mem_translated_scale_iff b hb (a:ℚ) (N:ℚ) ((u.val:A) * diag (q/b))]
  have he : b*(q/b)=q := by field_simp
  rw [mul_left_comm (diag b),← map_mul,he]

theorem outside_lattice_unit (u : K) (b : ℚ) (hb : b≠0) (a : ℤ) (N : ℕ) (q : ℚ)
    (hq : ¬ ∃ m : ℤ, q=b*m) :
    (u.val:A)*diag q ∉ translatedBall (b*(a:ℚ)) (b*(N:ℚ)) := by
  intro h
  have hz := integral_of_unit_mul u _ (integral_of_in_translated_int_ball a N
    ((mem_of_scaled_unit_iff u b hb a N q).mp h))
  obtain ⟨m,hm⟩ := (diagonal_integral_iff _).mp hz
  exact hq ⟨m,by rw [←hm]; field_simp⟩

theorem inside_lattice_unit (u : K) {N : ℕ} [NeZero N] (r : (ZMod N)ˣ)
    (hr : (u.val:A) - ((r.val.val:ℕ):A) ∈ centeredBall (N:ℚ))
    (b : ℚ) (hb : b≠0) (a m : ℤ) :
    (u.val:A)*diag (b*m) ∈ translatedBall (b*(a:ℚ)) (b*(N:ℚ)) ↔
      r.val * (m:ZMod N) = a := by
  rw [mem_of_scaled_unit_iff _ _ hb,show b*(m:ℚ)/b = m by field_simp,map_intCast]
  exact mem_translated_unit_integer_iff _ _ hr _ _

theorem centeredBall_neg_eq (b : ℚ) : centeredBall (-b) = centeredBall b := by
  ext x
  constructor <;> rintro ⟨z,hz,rfl⟩ <;> refine ⟨-z,integerSubring.neg_mem hz,?_⟩ <;>
    simp [diag]

theorem centeredBall_abs_eq (b : ℚ) : centeredBall |b| = centeredBall b := by
  rcases le_total 0 b with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,centeredBall_neg_eq]

theorem inside_lattice_dvd (b : ℚ) (hb : b≠0) (e : ℕ) (he : e ≠ 0) (m : ℤ) :
    diag (b*m) ∈ centeredBall |b*(e:ℚ)| ↔ (e:ℤ) ∣ m := by
  rw [centeredBall_abs_eq,rational_mem_centered_iff _ _ (mul_ne_zero hb (by exact_mod_cast he))]
  constructor
  · rintro ⟨j,hj⟩
    rw [mul_assoc] at hj
    exact ⟨j,by exact_mod_cast (mul_left_cancel₀ hb hj)⟩
  · rintro ⟨j,hj⟩
    exact ⟨j,by rw [hj]; push_cast; ring⟩

theorem outside_lattice_dvd (b : ℚ) (hb : b≠0) (e : ℕ) (he : e ≠ 0) (q : ℚ)
    (hq : ¬ ∃ m : ℤ, q=b*m) : diag q ∉ centeredBall |b*(e:ℚ)| := by
  rw [centeredBall_abs_eq,rational_mem_centered_iff _ _ (mul_ne_zero hb (by exact_mod_cast he))]
  rintro ⟨j,hj⟩
  exact hq ⟨(e:ℤ)*j,by rw [hj]; push_cast; ring⟩

theorem num_isUnit (t : ℚ) : IsUnit (t.num : ZMod t.den) := by
  have hc := (ZMod.isUnit_iff_coprime t.num.natAbs t.den).mpr t.reduced
  rcases Int.natAbs_eq t.num with h|h
  · rwa [h,Int.cast_natCast]
  · rw [h,Int.cast_neg,Int.cast_natCast]
    exact hc.neg

end
end MasulloRH.RationalFinite
end

section
open Set MeasureTheory
open scoped BigOperators Topology
namespace MasulloRH.RationalFinite
noncomputable section

/-- Uniform mass of a fibre of a finite group quotient under invariant probability measure. -/
theorem quotient_fiber_measureReal {K H : Type*} [Group K] [MeasurableSpace K] [MeasurableMul K]
    [Group H] [Fintype H] (μ : Measure K) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (π : K →* H) (hs : Function.Surjective π)
    (hM : ∀ a : H, MeasurableSet (π ⁻¹' {a})) (a : H) :
    μ.real (π ⁻¹' {a}) = (Fintype.card H : ℝ)⁻¹ := by
  classical
  have heq (b : H) : μ.real (π ⁻¹' {b}) = μ.real (π ⁻¹' {a}) := by
    obtain ⟨k,hk⟩ := hs (a*b⁻¹)
    have hp : (fun u : K => k*u) ⁻¹' (π ⁻¹' {a}) = π ⁻¹' {b} := by
      ext u
      change π (k*u)=a ↔ π u=b
      rw [map_mul, hk, mul_assoc]
      constructor
      · intro hu
        have hu' : b⁻¹*π u = 1 := mul_left_cancel (by simpa only [mul_one] using hu : a*(b⁻¹*π u)=a*1)
        calc
          π u = b*(b⁻¹*π u) := by simp
          _ = b := by rw [hu',mul_one]
      · intro hu
        simp [hu]
    rw [← hp,measureReal_def,measureReal_def,measure_preimage_mul]
  have h := sum_measureReal_preimage_singleton (μ:=μ) (f:=π) Finset.univ (fun b _ => hM b)
  simp only [heq, Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.coe_univ,preimage_univ] at h
  have hu : μ.real univ = 1 := by simp [measureReal_def]
  rw [hu] at h
  have hc : (Fintype.card H:ℝ) ≠ 0 := by positivity
  field_simp
  linarith only [h]

/-- Average of a unit residue-class indicator at an arbitrary residue, including at level one. -/
theorem unit_residue_average {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (N : ℕ) [NeZero N] (π : K →* (ZMod N)ˣ) (hc : Continuous π) (hs : Function.Surjective π)
    (a : (ZMod N)ˣ) (r : ZMod N) :
    (∫ u : K, (if (π u : ZMod N)*r = (a : ZMod N) then (1:ℂ) else 0) ∂μ) =
      if IsUnit r then (N.totient:ℂ)⁻¹ else 0 := by
  classical
  by_cases hr : IsUnit r
  · obtain ⟨v,rfl⟩ := hr
    rw [if_pos v.isUnit]
    have hM (b : (ZMod N)ˣ) : MeasurableSet (π ⁻¹' {b}) :=
      (isClosed_singleton.preimage hc).measurableSet
    let b := a*v⁻¹
    have hfun (u : K) : (if (π u : ZMod N)*(v : ZMod N) = (a:ZMod N) then (1:ℂ) else 0) =
        (π ⁻¹' {b}).indicator (fun _ : K => (1:ℂ)) u := by
      have he : ((π u : ZMod N)*(v : ZMod N) = (a:ZMod N)) ↔ π u=b := by
        change (((π u*v : (ZMod N)ˣ):ZMod N) = (a:ZMod N)) ↔ _
        rw [Units.val_inj, eq_mul_inv_iff_mul_eq]
      simp only [Set.indicator,mem_preimage,mem_singleton_iff,he]
    simp only [hfun,integral_indicator (hM b),setIntegral_const,quotient_fiber_measureReal μ π hs hM,
      ZMod.card_units_eq_totient,Complex.real_smul, mul_one,Complex.ofReal_inv,Complex.ofReal_natCast]
  · rw [if_neg hr]
    have hne (u : K) : (π u : ZMod N)*r ≠ (a:ZMod N) := by
      intro h
      exact hr (isUnit_of_mul_isUnit_right (show IsUnit ((π u : ZMod N)*r) by rw [h]; exact a.isUnit))
    simp [hne]

/-- For all integers m the unit indicator modulo positive N is the Möbius sum of the
divisibility indicators for the positive divisors of N. -/
theorem unit_indicator_moebius (N : ℕ) [NeZero N] (m : ℤ) :
    (if IsUnit (m:ZMod N) then (1:ℂ) else 0) =
      ∑ e ∈ N.divisors, if (e:ℤ) ∣ m then (ArithmeticFunction.moebius e:ℂ) else 0 := by
  classical
  let g := Nat.gcd N m.natAbs
  have hg : g ≠ 0 := (Nat.gcd_pos_of_pos_left m.natAbs (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  have hd : N.divisors.filter (fun e : ℕ => (e:ℤ) ∣ m) = g.divisors := by
    ext e
    simp only [Finset.mem_filter,Nat.mem_divisors,Int.natCast_dvd,g,Nat.dvd_gcd_iff]
    have hN := NeZero.ne N
    change g ≠ 0 at hg
    change N.gcd m.natAbs ≠ 0 at hg
    tauto
  have he : IsUnit (m:ZMod N) ↔ g=1 := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime,Int.isCoprime_iff_gcd_eq_one]
    rfl
  rw [← Finset.sum_filter,hd, if_congr he rfl rfl]
  have hsum := congrArg (fun f : ArithmeticFunction ℤ => f g) ArithmeticFunction.coe_zeta_mul_moebius
  simp only [ArithmeticFunction.coe_zeta_mul_apply,ArithmeticFunction.one_apply] at hsum
  split_ifs at hsum ⊢ with h
  · exact_mod_cast hsum.symm
  · exact_mod_cast hsum.symm

/-- The integral depends only on the gcd of the integer argument with the positive level. -/
theorem unit_residue_average_eq_gcd {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (N : ℕ) [NeZero N] (π : K →* (ZMod N)ˣ) (hc : Continuous π) (hs : Function.Surjective π)
    (a : (ZMod N)ˣ) (m : ℤ) :
    (∫ u : K, (if (π u : ZMod N)*(m:ZMod N) = (a : ZMod N) then (1:ℂ) else 0) ∂μ) =
      if Nat.gcd N m.natAbs = 1 then (N.totient:ℂ)⁻¹ else 0 := by
  rw [unit_residue_average μ N π hc hs]
  have he : IsUnit (m:ZMod N) ↔ Nat.gcd N m.natAbs = 1 :=
    (ZMod.coe_int_isUnit_iff_isCoprime m N).trans Int.isCoprime_iff_gcd_eq_one
  exact if_congr he rfl rfl

/-- Haar projection of a unit residue class along the integer diagonal, written as a finite sum
of the divisibility indicators. -/
theorem unit_residue_average_eq_divisors {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (N : ℕ) [NeZero N] (π : K →* (ZMod N)ˣ) (hc : Continuous π) (hs : Function.Surjective π)
    (a : (ZMod N)ˣ) (m : ℤ) :
    (∫ u : K, (if (π u : ZMod N)*(m:ZMod N) = (a : ZMod N) then (1:ℂ) else 0) ∂μ) =
      (N.totient:ℂ)⁻¹ * ∑ e ∈ N.divisors, if (e:ℤ) ∣ m then (ArithmeticFunction.moebius e:ℂ) else 0 := by
  rw [unit_residue_average μ N π hc hs, ← unit_indicator_moebius]
  split_ifs <;> simp

end
end MasulloRH.RationalFinite
end

section
open NumberField IsDedekindDomain MeasureTheory
open scoped BigOperators
namespace MasulloRH.RationalFinite
noncomputable section
variable [MeasurableSpace K] [BorelSpace K]

/-- Finite Haar average of one ball in the normalized rational dilation variables. -/
theorem scaled_ball_explicit_diagonal (μ : Measure K) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (N : ℕ) [NeZero N] (π : K →* (ZMod N)ˣ) (hc : Continuous π) (hs : Function.Surjective π)
    (hπ : ∀ u : K, (u.val:A) - ((π u).val.val:A) ∈ centeredBall (N:ℚ))
    (b : ℚ) (hb : b≠0) (a : ℤ) (ha : IsUnit (a:ZMod N)) :
    let f : A→ℂ := (N.totient:ℂ)⁻¹ • ∑ e ∈ N.divisors, (ArithmeticFunction.moebius e:ℂ) •
      (centeredBall |b*(e:ℚ)|).indicator (1:A→ℂ)
    f ∈ radialSpan ∧ ∀ q : ℚ, (∫ u : K, (translatedBall (b*(a:ℚ)) (b*(N:ℚ))).indicator (1:A→ℂ)
      ((u.val:A)*diag q) ∂μ) = f (diag q) := by
  classical
  let G (e : ℕ) := (centeredBall |b*(e:ℚ)|).indicator (1 : A→ℂ)
  let f : A → ℂ := (N.totient:ℂ)⁻¹ • ∑ e ∈ N.divisors, (ArithmeticFunction.moebius e:ℂ) • G e
  have hef (e : ℕ) (h : e ∈ N.divisors) : e ≠ 0 := (Nat.pos_of_mem_divisors h).ne'
  have hf : f ∈ radialSpan := by
    apply radialSpan.smul_mem
    apply radialSpan.sum_mem
    intro e he
    apply radialSpan.smul_mem
    apply Submodule.subset_span
    exact ⟨|b*(e:ℚ)|,abs_pos.mpr (mul_ne_zero hb (by exact_mod_cast hef e he)),rfl⟩
  refine ⟨hf,fun q => ?_⟩
  change _ = f (diag q)
  have hval (x : A) : f x = (N.totient:ℂ)⁻¹ *
      ∑ e ∈ N.divisors, (ArithmeticFunction.moebius e:ℂ) * G e x := by
    simp [f,Finset.sum_apply]
  by_cases hm : ∃ m : ℤ, q=b*m
  · obtain ⟨m,rfl⟩ := hm
    let v := ha.unit
    have hv : (v:ZMod N) = (a:ZMod N) := ha.unit_spec
    rw [hval]
    calc
      _ = ∫ u : K, (if (π u : ZMod N)*(m:ZMod N)=(v:ZMod N) then (1:ℂ) else 0) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun u => by
          dsimp only
          rw [Set.indicator_apply,hv]
          simp only [inside_lattice_unit u (π u) (hπ u) b hb a m,Pi.one_apply]
      _ = _ := by
        rw [unit_residue_average_eq_divisors μ N π hc hs v m]
        congr 1
        apply Finset.sum_congr rfl
        intro e he
        simp only [G,Set.indicator_apply,inside_lattice_dvd b hb e (hef e he) m,Pi.one_apply]
        split_ifs <;> simp
  · have hzero (u : K) : (translatedBall (b*(a:ℚ)) (b*(N:ℚ))).indicator (1 : A→ℂ)
        ((u.val:A)*diag q) = 0 := Set.indicator_of_notMem (outside_lattice_unit u b hb a N q hm) _
    simp only [hzero,integral_zero,hval]
    rw [Finset.sum_eq_zero (fun e he => ?_),mul_zero]
    rw [show G e (diag q) = 0 from Set.indicator_of_notMem (outside_lattice_dvd b hb e (hef e he) q hm) _,mul_zero]

/-- Finite Haar average of one ball in the normalized rational dilation variables. -/
theorem scaled_ball_on_diagonal (μ : Measure K) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (N : ℕ) [NeZero N] (π : K →* (ZMod N)ˣ) (hc : Continuous π) (hs : Function.Surjective π)
    (hπ : ∀ u : K, (u.val:A) - ((π u).val.val:A) ∈ centeredBall (N:ℚ))
    (b : ℚ) (hb : b≠0) (a : ℤ) (ha : IsUnit (a:ZMod N)) :
    ∃ f ∈ radialSpan, ∀ q : ℚ,
      (∫ u : K, (translatedBall (b*(a:ℚ)) (b*(N:ℚ))).indicator (1 : A→ℂ)
        ((u.val:A)*diag q) ∂μ) = f (diag q) := by
  have h := scaled_ball_explicit_diagonal μ N π hc hs hπ b hb a ha
  exact ⟨_,h.1,h.2⟩

theorem rational_ball_on_diagonal (μ : Measure K) [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ]
    (P : ∀ (N : ℕ) [NeZero N], ∃ π : K →* (ZMod N)ˣ,
      Continuous π ∧ Function.Surjective π ∧ ∀ u : K, (u.val:A)-((π u).val.val:A) ∈ centeredBall (N:ℚ))
    (k d : ℚ) (hd : d≠0) :
    ∃ f ∈ radialSpan, ∀ q : ℚ,
      (∫ u : K, (translatedBall k d).indicator (1 : A→ℂ) ((u.val:A)*diag q) ∂μ) = f (diag q) := by
  let t := k/d
  let N := t.den
  let b := d/(N:ℚ)
  have : NeZero N := ⟨t.den_nz⟩
  have hn : (N:ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hb : b≠0 := div_ne_zero hd hn
  have hscale : b*(N:ℚ)=d := div_mul_cancel₀ d hn
  have hnum : b*(t.num:ℚ)=k := by
    have ht : (t.num:ℚ)/(N:ℚ)=t := t.num_div_den
    calc
      _ = d*((t.num:ℚ)/(N:ℚ)) := by dsimp [b]; ring
      _ = k := by rw [ht]; dsimp [t]; field_simp
  obtain ⟨π,hc,hs,hπ⟩ := P N
  simpa only [hscale,hnum] using scaled_ball_on_diagonal μ N π hc hs hπ b hb t.num (num_isUnit t)

end
end MasulloRH.RationalFinite
end

section
open NumberField NumberField.AdelicBox IsDedekindDomain MeasureTheory Set Filter
open scoped Topology
namespace MasulloRH.RationalFinite
noncomputable section

/-- Every diagonal rational scaling by a nonzero scalar is invertible. -/
private lemma inv_scale (d : ℚ) (hd : d ≠ 0) (x : A) : diag d⁻¹ * (diag d * x) = x := by
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hd, map_one, one_mul]

theorem denseRange_diag : DenseRange diag := by
  intro x
  obtain ⟨s,hs,hx⟩ := exists_mul_mem_integralFiniteAdeles (𝓞 ℚ) ℚ x
  have hs' : (s:ℚ) ≠ 0 := by exact_mod_cast hs
  let F (y : A) := diag (s:ℚ)⁻¹*y
  have hmaps : MapsTo F (Set.range (algebraMap (𝓞 ℚ) A)) (Set.range diag) := by
    rintro _ ⟨a,rfl⟩
    exact ⟨(s:ℚ)⁻¹*(a:ℚ), map_mul _ _ _⟩
  have hcl := hmaps.closure (show Continuous F from continuous_const.mul continuous_id)
  have h := hcl (integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers ℚ hx)
  exact (inv_scale (s:ℚ) hs' x) ▸ h

theorem compact_unitIdeles : CompactSpace K := by
  let S : Set (A×A) := (O ×ˢ O) ∩ {z | z.1*z.2=1}
  have hc : IsCompact S := (isCompact_integralFiniteAdeles ℚ).prod (isCompact_integralFiniteAdeles ℚ) |>.inter_right
    (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hc
  let f (z : S) : Aˣ := ⟨z.val.1,z.val.2,z.prop.2, (mul_comm _ _).trans z.prop.2⟩
  let F (z : S) : K := ⟨f z,z.prop.1⟩
  have h : Continuous f := Units.continuous_iff.mpr
    ⟨continuous_fst.comp continuous_subtype_val,continuous_snd.comp continuous_subtype_val⟩
  have hF : Continuous F := h.subtype_mk _
  have hsurj : Function.Surjective F := by
    intro u
    exact ⟨⟨((u.val:A),↑u.val⁻¹),u.prop,Units.mul_inv u.val⟩,Subtype.ext (Units.ext rfl)⟩
  exact hsurj.compactSpace hF

theorem isClopen_centeredBall (d : ℚ) (hd : d ≠ 0) : IsClopen (centeredBall d) := by
  have hset : centeredBall d = (fun z : A => diag d⁻¹*z) ⁻¹' O := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      simpa only [Set.mem_preimage,inv_scale d hd] using hw
    · intro hz
      refine ⟨diag d⁻¹*z,hz,?_⟩
      simpa using inv_scale d⁻¹ (inv_ne_zero hd) z
  rw [hset]
  have hO : IsClopen O := ⟨(isCompact_integralFiniteAdeles ℚ).isClosed, isOpen_integralFiniteAdeles ℚ⟩
  exact hO.preimage (continuous_const.mul continuous_id)

theorem isClopen_translatedBall (k d : ℚ) (hd : d ≠ 0) : IsClopen (translatedBall k d) := by
  have hset : translatedBall k d = (fun z : A => z-diag k) ⁻¹' centeredBall d := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w,hw,(add_sub_cancel_left _ _).symm⟩
    · rintro ⟨w,hw,e⟩
      change diag d * w = z-diag k at e
      exact ⟨w,hw, by change diag k + diag d * w = z; rw [e]; abel⟩
  rw [hset]
  exact (isClopen_centeredBall d hd).preimage (continuous_id.sub continuous_const)

theorem continuous_of_mem_radialSpan {f : A → ℂ} (hf : f ∈ radialSpan) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨d,hd,rfl⟩ := hf
    exact (isClopen_centeredBall d hd.ne').continuous_indicator continuous_const
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c f _ hf => exact continuous_const.smul hf

/-- Compactness of the acting parameter gives simultaneous local constancy of each orbit integral. -/
theorem isLocallyConstant_average {B : Type*} [TopologicalSpace B] [CompactSpace B] [MeasurableSpace B]
    (μ : Measure B) (m : B → A) (hm : Continuous m) {f : A → ℂ} (hf : IsLocallyConstant f) :
    IsLocallyConstant (fun x : A => ∫ u, f (m u*x) ∂μ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let C : Set (A×B) := {z | f (m z.2*z.1) ≠ f (m z.2*x)}
  have h1 : IsLocallyConstant (fun z : A×B => f (m z.2*z.1)) :=
    hf.comp_continuous ((hm.comp continuous_snd).mul continuous_fst)
  have h2 : IsLocallyConstant (fun z : A×B => f (m z.2*x)) :=
    hf.comp_continuous ((hm.comp continuous_snd).mul continuous_const)
  have hc : IsClosed C := by
    refine ⟨?_⟩
    convert (h1.prodMk h2) {z : ℂ × ℂ | z.1 = z.2} using 1
    ext z
    simp [C]
  have hopen := (isClosedMap_fst_of_compactSpace C hc).isOpen_compl
  have hx : x ∈ (Prod.fst '' C)ᶜ := by
    rintro ⟨⟨y,u⟩,hn,hy⟩
    exact hn (congrArg (fun t => f (m u*t)) hy)
  filter_upwards [hopen.mem_nhds hx] with y hy
  apply integral_congr_ae
  exact ae_of_all _ fun u => by
    by_contra hn
    exact hy ⟨(y,u),hn,rfl⟩

end
end MasulloRH.RationalFinite
end

section
open NumberField NumberField.AdelicBox IsDedekindDomain MeasureTheory Set Filter
open scoped Topology
namespace MasulloRH.RationalFinite
noncomputable section

theorem average_mem_radialSpan [MeasurableSpace K] [OpensMeasurableSpace K] (μ : Measure K)
    [IsFiniteMeasure μ]
    (hball : ∀ (k : ℚ) (d : 𝓞 ℚ), d ≠ 0 → ∃ g ∈ radialSpan, ∀ q : ℚ,
      (∫ u : K, (translatedBall k (d:ℚ)).indicator (1 : A → ℂ) ((u.val:A) * diag q) ∂μ) =
        g (diag q))
    {h : A → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    (fun x : A => ∫ u : K, h ((u.val:A) * x) ∂μ) ∈ radialSpan := by
  classical
  let : CompactSpace K := compact_unitIdeles
  have hm : Continuous (fun u : K => (u.val : A)) := Units.continuous_val.comp continuous_subtype_val
  obtain ⟨d,hd,s,c,hs⟩ := exists_eq_sum_indicator_image_integralFiniteAdeles ℚ hlc hcs
  let b (k : ℚ) : A → ℂ := (translatedBall k (d:ℚ)).indicator 1
  let a (k : ℚ) (x : A) : ℂ := ∫ u : K, b k ((u.val:A)*x) ∂μ
  have hbl (k : ℚ) : IsLocallyConstant (b k) := by
    exact (LocallyConstant.charFn ℂ (isClopen_translatedBall k d (by exact_mod_cast hd))).isLocallyConstant
  have ha (k : ℚ) : a k ∈ radialSpan := by
    obtain ⟨g,hg,he⟩ := hball k d hd
    have hcont : Continuous (a k) := (isLocallyConstant_average μ _ hm (hbl k)).continuous
    have hag : a k = g := denseRange_diag.equalizer hcont (continuous_of_mem_radialSpan hg) (funext he)
    exact hag ▸ hg
  have hi (k : ℚ) (x : A) : Integrable (fun u : K => b k ((u.val:A)*x)) μ := by
    have hcont := (hbl k).continuous.comp (hm.mul (continuous_const (y:=x)))
    exact (integrableOn_univ.mp (hcont.continuousOn.integrableOn_compact isCompact_univ))
  have heq : (fun x : A => ∫ u : K, h ((u.val:A)*x) ∂μ) = ∑ k ∈ s, c k • a k := by
    funext x
    have hc (y : A) : h y = ∑ k ∈ s, c k * b k y := by
      simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,b,translatedBall] using congrFun hs y
    simp_rw [hc]
    rw [integral_finsetSum _ (fun k _ => (hi k x).const_mul (c k))]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,integral_const_mul,a]
  rw [heq]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (ha k)

end
end MasulloRH.RationalFinite
end

section
open NumberField IsDedekindDomain MeasureTheory Set
namespace MasulloRH.RationalFinite
noncomputable section

theorem unit_mul_mem_centeredBall_iff (u : K) (d : ℚ) (x : A) :
    (u.val:A)*x ∈ centeredBall d ↔ x ∈ centeredBall d := by
  have h (v : K) {y : A} (hy : y ∈ centeredBall d) : (v.val:A)*y ∈ centeredBall d := by
    obtain ⟨z,hz,rfl⟩ := hy
    refine ⟨(v.val:A)*z,fun w => mul_mem (v.property.1 w) (hz w),?_⟩
    change _ = (v.val:A)*(diag d*z)
    ring
  constructor
  · intro hx
    have ht := h u⁻¹ hx
    change (↑u.val⁻¹:A)*((u.val:A)*x) ∈ _ at ht
    simpa only [← mul_assoc, Units.inv_mul,one_mul] using ht
  · exact h u

theorem radialSpan_properties {f : A → ℂ} (hf : f ∈ radialSpan) :
    IsLocallyConstant f ∧ HasCompactSupport f ∧ ∀ u : K, ∀ x : A, f ((u.val:A)*x)=f x := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨d,hd,rfl⟩ := hf
    refine ⟨(LocallyConstant.charFn ℂ (isClopen_centeredBall d hd.ne')).isLocallyConstant,?_,?_⟩
    · have hcompact : IsCompact (centeredBall d) := (NumberField.AdelicBox.isCompact_integralFiniteAdeles ℚ).image ((continuous_const (y:=diag d)).mul continuous_id)
      exact HasCompactSupport.of_support_subset_isCompact hcompact Set.support_indicator_subset
    · intro u x
      by_cases hx : x ∈ centeredBall d
      · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem ((unit_mul_mem_centeredBall_iff u d x).mpr hx), Pi.one_apply]
      · simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (unit_mul_mem_centeredBall_iff u d x).mp hx)]
  | zero => exact ⟨IsLocallyConstant.const _, HasCompactSupport.zero,fun _ _ => rfl⟩
  | add f g _ _ hf hg =>
    refine ⟨hf.1.add hg.1,hf.2.1.add hg.2.1,?_⟩
    intro u x
    simp only [Pi.add_apply, hf.2.2 u x, hg.2.2 u x]
  | smul c f _ hf =>
    refine ⟨hf.1.comp (c • ·),hf.2.1.smul_left,?_⟩
    intro u x
    simp only [Pi.smul_apply,hf.2.2 u x]

variable [MeasurableSpace K]

theorem average_of_mem_radialSpan (μ : Measure K) [IsProbabilityMeasure μ] {f : A → ℂ} (hf : f ∈ radialSpan) (x : A) :
    ∫ u : K, f ((u.val:A)*x) ∂μ = f x := by
  simp only [(radialSpan_properties hf).2.2 _ x, integral_const, probReal_univ, one_smul]

theorem mem_radialSpan_iff_average (μ : Measure K) [IsProbabilityMeasure μ]
    (hproj : ∀ h : A → ℂ, IsLocallyConstant h → HasCompactSupport h →
      (fun x : A => ∫ u : K, h ((u.val:A)*x) ∂μ) ∈ radialSpan) (f : A → ℂ) :
    f ∈ radialSpan ↔ ∃ h : A → ℂ, IsLocallyConstant h ∧ HasCompactSupport h ∧
      ∀ x : A, f x = ∫ u : K, h ((u.val:A)*x) ∂μ := by
  constructor
  · intro hf
    obtain ⟨hl,hc,_⟩ := radialSpan_properties hf
    exact ⟨f,hl,hc,fun x => (average_of_mem_radialSpan μ hf x).symm⟩
  · rintro ⟨h,hl,hc,he⟩
    rw [funext he]
    exact hproj h hl hc
theorem mem_radialSpan_iff_invariant_test (μ : Measure K) [IsProbabilityMeasure μ]
    (hproj : ∀ h : A → ℂ, IsLocallyConstant h → HasCompactSupport h →
      (fun x : A => ∫ u : K, h ((u.val:A)*x) ∂μ) ∈ radialSpan) (f : A → ℂ) :
    f ∈ radialSpan ↔ IsLocallyConstant f ∧ HasCompactSupport f ∧
      ∀ u : K, ∀ x : A, f ((u.val:A)*x) = f x := by
  refine ⟨radialSpan_properties, ?_⟩
  rintro ⟨hl,hc,hinv⟩
  apply (mem_radialSpan_iff_average μ hproj f).mpr
  exact ⟨f,hl,hc,fun x => by simp only [hinv _ x, integral_const, probReal_univ, one_smul]⟩

end
end MasulloRH.RationalFinite
end

section
open NumberField IsDedekindDomain Set
open scoped NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing
namespace MasulloRH.RationalFinite
noncomputable section

abbrev lattice (N : ℕ) : Set A := centeredBall (N:ℚ)

def unitReduction (N : ℕ) [NeZero N] : K →* (ZMod N)ˣ :=
  ((RatIdele.unitResidue N).comp ((Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ)).comp K.subtype)).toHomUnits

theorem diag_apply (q : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    diag q v = algebraMap ℚ (v.adicCompletion ℚ) q := rfl

theorem nat_apply (n : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (n:A) v = (n : v.adicCompletion ℚ) := by
  rw [← map_natCast diag, diag_apply, map_natCast]

theorem valued_unit (u : K) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((u.val : A) v) = 1 := by
  have h₁ := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (u.property.1 v)
  have h₂ := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (u.property.2 v)
  apply le_antisymm h₁
  have hprod : Valued.v ((u.val:A) v) * Valued.v (((u.val⁻¹ : Aˣ):A) v) = 1 := by
    rw [← map_mul]
    change Valued.v ((↑u.val * (↑u.val⁻¹ : A) : A) v) = 1
    rw [Units.mul_inv]
    exact map_one _
  simpa only [hprod, mul_one] using mul_le_mul_of_nonneg_left h₂ (show 0 ≤ Valued.v ((u.val:A) v) from zero_le)

private theorem bound_nat (N : ℕ) [NeZero N] (v : HeightOneSpectrum (𝓞 ℚ)) :
    AdelicLevel.idealBound (𝓞 ℚ) (Ideal.span {(N : 𝓞 ℚ)}) v = Valued.v (N : v.adicCompletion ℚ) := by
  have h : (N : 𝓞 ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), RatIdele.valued_algebraMap_rat,
    ← map_natCast (algebraMap (𝓞 ℚ) ℚ), HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg _ h,
    AdelicLevel.idealBound_of_ne_bot (by simpa using h)]

theorem idealBall_eq_lattice (N : ℕ) [NeZero N] :
    AdelicLevel.idealBall (𝓞 ℚ) ℚ (Ideal.span {(N:𝓞 ℚ)}) = lattice N := by
  ext x
  rw [lattice, mem_centered_iff _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  change (∀ v, Valued.v (x v) ≤ _) ↔ ∀ v : HeightOneSpectrum (𝓞 ℚ), (diag (N:ℚ)⁻¹ * x) v ∈ v.adicCompletionIntegers ℚ
  apply forall_congr'
  intro v
  rw [bound_nat, HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v (x v) ≤ _ ↔ Valued.v ((diag ((N:ℚ)⁻¹) v) * x v) ≤ 1
  rw [diag_apply, map_inv₀, map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), map_mul, map_inv₀, inv_mul_le_iff₀]
  · rw [mul_one]
  · exact zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr (RatIdele.natCast_adicCompletion_ne_zero v (NeZero.ne N)))

theorem unitReduction_congr (N : ℕ) [NeZero N] (u : K) :
    (u.val:A) - (((unitReduction N u : ZMod N).val : ℕ) : A) ∈ centeredBall (N:ℚ) := by
  change _ ∈ lattice N
  rw [← idealBall_eq_lattice]
  exact RatIdele.sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one N u.val (valued_unit u)

end
end MasulloRH.RationalFinite
end

section
open NumberField IsDedekindDomain Set Filter
open scoped NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing
namespace MasulloRH.RationalFinite
noncomputable section

theorem lattice_sub (N : ℕ) {x y : A} (hx : x ∈ lattice N) (hy : y ∈ lattice N) :
    x-y ∈ lattice N := by
  obtain ⟨x,hx,rfl⟩ := hx
  obtain ⟨y,hy,rfl⟩ := hy
  exact ⟨x-y, fun v => sub_mem (hx v) (hy v), mul_sub _ _ _⟩

theorem unitReduction_eq_iff (N : ℕ) [NeZero N] (u : K) (n : ℕ) :
    (unitReduction N u : ZMod N) = (n : ZMod N) ↔ (u.val:A) - n ∈ lattice N := by
  let a := (unitReduction N u : ZMod N).val
  have hr : (a:ZMod N) = (unitReduction N u:ZMod N) := ZMod.natCast_zmod_val _
  have hu := unitReduction_congr N u
  change (u.val:A) - a ∈ lattice N at hu
  have subeq : (a:A) - n ∈ lattice N ↔ (a:ZMod N) = n := by
    have h := (int_mem_centered_nat_iff ((a:ℤ)-(n:ℤ)) N).trans (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm
    simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero] using h
  rw [← hr, ← subeq]
  constructor
  · intro hh
    have hz : (0:A) ∈ lattice N := ⟨0,fun v => zero_mem _, mul_zero _⟩
    have h := lattice_sub N hu (lattice_sub N hz hh)
    convert h using 1
    abel
  · intro hh
    have h := lattice_sub N hh hu
    convert h using 1
    abel

theorem unitReduction_continuous (N : ℕ) [NeZero N] : Continuous (unitReduction N) := by
  apply continuous_discrete_rng.mpr
  intro b
  have hf : (unitReduction N) ⁻¹' {b} =
      (fun u : K => (u.val:A) - (((b : ZMod N).val : ℕ) : A)) ⁻¹' lattice N := by
    ext u
    change (unitReduction N u = b) ↔ (u.val:A) - ((b:ZMod N).val : A) ∈ lattice N
    exact (Units.ext_iff.trans (by simpa only [ZMod.natCast_zmod_val] using unitReduction_eq_iff N u (b:ZMod N).val))
  rw [hf, ← idealBall_eq_lattice]
  apply (AdelicLevel.isOpen_idealBall (𝓞 ℚ) ℚ (by simpa using (Nat.cast_ne_zero.mpr (NeZero.ne N) : (N:𝓞 ℚ)≠0))).preimage
  fun_prop

end
end MasulloRH.RationalFinite
end

section
open NumberField IsDedekindDomain Set Filter
open scoped NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing
open Rat.HeightOneSpectrum
namespace MasulloRH.RationalFinite
noncomputable section

private def liftCoord (N a : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) : v.adicCompletion ℚ :=
  if natGenerator v ∣ N then (a : v.adicCompletion ℚ) else 1

private theorem valued_liftCoord (N a : ℕ) (ha : a.Coprime N) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (liftCoord N a v) = 1 := by
  unfold liftCoord
  split_ifs with h
  · rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)), RatIdele.valued_algebraMap_rat]
    apply RatIdele.valuation_natCast_of_not_dvd
    intro hp
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨_, prime_natGenerator v, hp, h⟩) ha
  · exact map_one _

private def liftFiniteUnit (N a : ℕ) (ha : a.Coprime N) : K := by
  let f := liftCoord N a
  have hv (v : HeightOneSpectrum (𝓞 ℚ)) : Valued.v (f v) = 1 := valued_liftCoord N a ha v
  have hne (v : HeightOneSpectrum (𝓞 ℚ)) : f v ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hv]; exact one_ne_zero)
  have hO (v : HeightOneSpectrum (𝓞 ℚ)) : f v ∈ v.adicCompletionIntegers ℚ :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hv v).le
  have hiO (v : HeightOneSpectrum (𝓞 ℚ)) : (f v)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  let z : A := ⟨f, Eventually.of_forall hO⟩
  let iz : A := ⟨fun v => (f v)⁻¹, Eventually.of_forall hiO⟩
  let u : Aˣ := ⟨z,iz,FiniteAdeleRing.ext ℚ (fun v => mul_inv_cancel₀ (hne v)),
    FiniteAdeleRing.ext ℚ (fun v => inv_mul_cancel₀ (hne v))⟩
  exact ⟨u,hO,hiO⟩

theorem unitReduction_surjective (N : ℕ) [NeZero N] : Function.Surjective (unitReduction N) := by
  intro b
  let a := (b : ZMod N).val
  have hc : a.Coprime N := ZMod.val_coe_unit_coprime b
  let u := liftFiniteUnit N a hc
  refine ⟨u,Units.ext ?_⟩
  have hval : (a:ZMod N) = (b:ZMod N) := ZMod.natCast_zmod_val _
  rw [←hval, unitReduction_eq_iff]
  rw [← idealBall_eq_lattice]
  intro v
  change Valued.v (liftCoord N a v - (a:A) v) ≤ _
  rw [nat_apply]
  by_cases h : natGenerator v ∣ N
  · simp [liftCoord,h]
  · have hbound : AdelicLevel.idealBound (𝓞 ℚ) (Ideal.span {(N:𝓞 ℚ)}) v = 1 := by
      rw [AdelicLevel.idealBound_eq_one_of_not_dvd]
      · simpa using (Nat.cast_ne_zero.mpr (NeZero.ne N) : (N:𝓞 ℚ)≠0)
      · rwa [Ideal.dvd_span_singleton, RatIdele.natCast_mem_asIdeal_iff]
    rw [hbound]
    apply (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp
    exact sub_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (valued_liftCoord N a hc v).le)
      (natCast_mem (v.adicCompletionIntegers ℚ) a)
end
end MasulloRH.RationalFinite
end

section
open NumberField IsDedekindDomain MeasureTheory
open MasulloRH.RationalFinite
open scoped BigOperators

theorem solution [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ] :
    (∀ f : A→ℂ, (f ∈ radialSpan ↔ ∃ h : A→ℂ, IsLocallyConstant h ∧ HasCompactSupport h ∧
      ∀ x : A, f x = ∫ u : K, h ((u.val:A)*x) ∂μ) ∧
      (f ∈ radialSpan ↔ IsLocallyConstant f ∧ HasCompactSupport f ∧
        ∀ u : K, ∀ x : A, f ((u.val:A)*x) = f x)) ∧
    (∀ (N : ℕ) [NeZero N] (a : ℤ), IsUnit (a:ZMod N) → ∀ (b : ℚ), b ≠ 0 →
      ∀ x : A, (∫ u : K, (translatedBall (b*(a:ℚ)) (b*(N:ℚ))).indicator (1:A→ℂ)
        ((u.val:A)*x) ∂μ) = ((N.totient:ℂ)⁻¹ • ∑ e ∈ N.divisors, (ArithmeticFunction.moebius e:ℂ) •
          (centeredBall |b*(e:ℚ)|).indicator (1:A→ℂ)) x) := by
  classical
  have hp : ∀ (N : ℕ) [NeZero N], ∃ π : K →* (ZMod N)ˣ,
      Continuous π ∧ Function.Surjective π ∧ ∀ u : K, (u.val:A)-((π u).val.val:A) ∈ centeredBall (N:ℚ) :=
    fun N _ => ⟨unitReduction N,unitReduction_continuous N,unitReduction_surjective N,unitReduction_congr N⟩
  have hproj (h : A→ℂ) (hl : IsLocallyConstant h) (hc : HasCompactSupport h) :
      (fun x : A => ∫ u : K, h ((u.val:A)*x) ∂μ) ∈ radialSpan := by
    exact average_mem_radialSpan μ (fun k d hd => rational_ball_on_diagonal μ hp k d (by exact_mod_cast hd)) hl hc
  refine ⟨fun f => ⟨mem_radialSpan_iff_average μ hproj f, mem_radialSpan_iff_invariant_test μ hproj f⟩,?_⟩
  intro N _ a ha b hb
  obtain ⟨π,hc,hs,hπ⟩ := hp N
  obtain ⟨hf,he⟩ := scaled_ball_explicit_diagonal μ N π hc hs hπ b hb a ha
  let : CompactSpace K := compact_unitIdeles
  have hm : Continuous (fun u : K => (u.val : A)) := Units.continuous_val.comp continuous_subtype_val
  let h := (translatedBall (b*(a:ℚ)) (b*(N:ℚ))).indicator (1:A→ℂ)
  have hl : IsLocallyConstant h := (LocallyConstant.charFn ℂ (isClopen_translatedBall _ _
    (mul_ne_zero hb (by exact_mod_cast NeZero.ne N)))).isLocallyConstant
  have eh := denseRange_diag.equalizer (isLocallyConstant_average μ _ hm hl).continuous
    (continuous_of_mem_radialSpan hf) (funext he)
  exact congrFun eh
end
