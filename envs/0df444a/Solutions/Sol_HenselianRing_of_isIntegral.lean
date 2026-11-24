-- Prove2me | solution 1 for HenselianRing.of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T23:30:43.505223+00:00
-- url     : https://prove2.me/submissions/cfbc85b1-b015-48cf-ac3e-f12508e5918e

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
import Mathlib.RingTheory.Nakayama
import Mathlib.Tactic.Ring
import Theorems.Thm_HenselianRing_exists_monic_factorization_of_map_eq_X_pow_mul_sub_one_pow

set_option maxHeartbeats 1600000

noncomputable section

section

section

set_option autoImplicit false

open Polynomial

namespace PhilipponHenselianIdempotents

/-- Idempotents of an affine quotient lift across a henselian pair. -/
theorem exists_lift {A B : Type*} [CommRing A] [CommRing B]
    (r : A →+* B) (hr : Function.Surjective r) [HenselianRing A (RingHom.ker r)]
    (e : B) (he : IsIdempotentElem e) : ∃ a : A, IsIdempotentElem a ∧ r a = e := by
  obtain ⟨a₀, ha₀⟩ := hr e
  let f : A[X] := X ^ 2 - X
  have hmonic : f.Monic := monic_X_pow_sub (degree_X_le.trans_lt (by decide))
  have hf : f.eval a₀ ∈ RingHom.ker r := by
    rw [RingHom.mem_ker]
    simp [f, ha₀, pow_two, he.eq]
  have hderiv : IsUnit (2 * e - 1) := by
    apply IsUnit.of_mul_eq_one (b := 2 * e - 1)
    calc
      (2 * e - 1) * (2 * e - 1) = 4 * (e * e - e) + 1 := by ring
      _ = 1 := by simp [he.eq]
  let q := r.quotientKerEquivOfSurjective hr
  have hmap : q (Ideal.Quotient.mk _ (f.derivative.eval a₀)) = 2 * e - 1 := by
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
    simp [f, ha₀, two_mul, add_mul]
  let d := Ideal.Quotient.mk (RingHom.ker r) (f.derivative.eval a₀)
  have hq : IsUnit (q d) := hmap.symm ▸ hderiv
  have hunit : IsUnit d := by
    have hback : IsUnit (q.symm (q d)) := hq.map q.symm.toMonoidHom
    rwa [RingEquiv.symm_apply_apply] at hback
  obtain ⟨a, ha, hdiff⟩ := HenselianRing.is_henselian f hmonic a₀ hf hunit
  refine ⟨a, ?_, ?_⟩
  · simpa [Polynomial.IsRoot, f, pow_two, sub_eq_zero, IsIdempotentElem] using ha
  · rw [RingHom.mem_ker, map_sub, sub_eq_zero, ha₀] at hdiff
    exact hdiff

/-- Idempotent lifts are unique across a map whose kernel lies in the
Jacobson radical. -/
theorem eq_of_map_eq {A B : Type*} [CommRing A] [CommRing B]
    (r : A →+* B) (h : RingHom.ker r ≤ Ideal.jacobson ⊥)
    {a b : A} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) (hab : r a = r b) : a = b := by
  let d := a - b
  have hd : d ∈ Ideal.jacobson (⊥ : Ideal A) := h (by
    rw [RingHom.mem_ker, show d = a - b from rfl, map_sub, hab, sub_self])
  have hu : IsUnit (d * (-d) + 1) := Ideal.mem_jacobson_bot.mp hd (-d)
  apply sub_eq_zero.mp (hu.mul_left_inj.mp ?_)
  rw [zero_mul]
  calc
    d * (d * (-d) + 1) = (a - b) - ((a * a) * a - 3 * (a * a) * b + 3 * a * (b * b) - (b * b) * b) := by
      dsimp [d]
      ring
    _ = 0 := by
      rw [ha.eq, hb.eq, ha.eq, hb.eq]
      ring

/-- The extension of an ideal in the Jacobson radical remains in the
Jacobson radical under an integral map. -/
theorem map_le_jacobson {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.IsIntegral) (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥) :
    I.map f ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.jacobson]
  apply le_sInf
  rintro m ⟨_, hm⟩
  let : m.IsMaximal := hm
  rw [Ideal.map_le_iff_le_comap]
  exact hI.trans (sInf_le ⟨bot_le, Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf m⟩)

end PhilipponHenselianIdempotents

end

section

set_option autoImplicit false

open Polynomial


namespace PhilipponHenselianRootByIdempotents

private theorem map_mul_eq_eval_mul {A T : Type*} [CommRing A] [CommRing T]
    (k : A[X] →+* T) (a : A) (e : T) (h : k (X - C a) * e = 0) (p : A[X]) :
    k p * e = k (C (p.eval a)) * e := by
  have hg : k ((X - C a) * (p /ₘ (X - C a))) * e = 0 := by
    rw [map_mul, mul_right_comm, h, zero_mul]
  rwa [X_sub_C_mul_divByMonic_eq_sub_modByMonic, modByMonic_X_sub_C_eq_C_eval,
    map_sub, sub_mul, sub_eq_zero] at hg

/-- Lifting the idempotents in the quotients of monic polynomial algebras
implies the simple-root criterion for a henselian pair. -/
theorem henselian_of_adjoinRoot_idempotents {A : Type*} [CommRing A]
    (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (liftIdem : ∀ (p : A[X]), p.Monic →
      let J := I.map (algebraMap A (AdjoinRoot p))
      ∀ b : AdjoinRoot p ⧸ J, IsIdempotentElem b →
        ∃ e : AdjoinRoot p, IsIdempotentElem e ∧ Ideal.Quotient.mk J e = b) :
    HenselianRing A I where
  jac := hI
  is_henselian p hp a₀ h₀ hderiv := by
    let T := AdjoinRoot p
    let F := algebraMap A T
    let J := I.map F
    let π := Ideal.Quotient.mk I
    let ρ := Ideal.Quotient.mk J
    let k := ρ.comp (AdjoinRoot.mk p)
    let g := p /ₘ (X - C a₀)
    have hge : g.eval a₀ = p.derivative.eval a₀ := by
      have h := congrArg (eval a₀) (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative p a₀)
      simpa [g] using h
    let : IsLocalHom π := isLocalHom_of_le_jacobson_bot I hI
    have hunit : IsUnit (g.eval a₀) := (isUnit_map_iff π _).mp (by rw [hge]; exact hderiv)
    obtain ⟨u, hu⟩ := hunit
    let v := (↑u⁻¹ : A)
    have hv : v * g.eval a₀ = 1 := by rw [← hu, Units.inv_mul]
    let b := AdjoinRoot.mk p (C v * g)
    have hkg : k (X - C a₀) * k g = 0 := by
      rw [← map_mul]
      change k ((X - C a₀) * (p /ₘ (X - C a₀))) = 0
      rw [X_sub_C_mul_divByMonic_eq_sub_modByMonic, modByMonic_X_sub_C_eq_C_eval, map_sub]
      have hz : k (C (p.eval a₀)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem F h₀)
      have hk : k p = 0 := by
        change ρ (AdjoinRoot.mk p p) = 0
        rw [AdjoinRoot.mk_self, map_zero]
      rw [hk, hz, sub_zero]
    have hb : k (X - C a₀) * ρ b = 0 := by
      change k (X - C a₀) * k (C v * g) = 0
      rw [map_mul, mul_left_comm, hkg, mul_zero]
    obtain ⟨e, he, heq⟩ := liftIdem p hp (ρ b) (by
      change k (C v * g) * ρ b = ρ b
      rw [map_mul_eq_eval_mul k a₀ (ρ b) hb (C v * g), eval_mul, eval_C, hv, C_1, map_one, one_mul])
    have heproj : k (X - C a₀) * ρ e = 0 := by rw [heq, hb]
    have hπ : p.eval₂ π (π a₀) = 0 := by
      rw [eval₂_at_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h₀
    let φ := AdjoinRoot.lift π (π a₀) hπ
    have hφF (a : A) : φ (F a) = π a := AdjoinRoot.lift_of hπ
    have hφJ : J ≤ RingHom.ker φ := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      change φ (F a) = 0
      rw [hφF]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have hφe : φ e = 1 := by
      calc
        φ e = φ b := congrArg (Ideal.Quotient.lift J φ hφJ) heq
        _ = 1 := by
          change φ (AdjoinRoot.mk p (C v * g)) = 1
          rw [AdjoinRoot.lift_mk, eval₂_at_apply, eval_mul, eval_C, hv, map_one]
    let m : T →ₗ[A] T :=
      { toFun := fun x => x * e
        map_add' := fun x y => add_mul x y e
        map_smul' := fun a x => smul_mul_assoc a x e }
    let N := Submodule.span A {e}
    have hmod : m.range ≤ N ⊔ I • m.range := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective (g := p) x
      let c := F (r.eval a₀)
      let d := AdjoinRoot.mk p r * e - c * e
      have hd : d ∈ J := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        change ρ (AdjoinRoot.mk p r * e - c * e) = 0
        rw [map_sub, map_mul, map_mul, sub_eq_zero]
        exact map_mul_eq_eval_mul k a₀ (ρ e) heproj r
      have hdm : m d = d := by
        change (AdjoinRoot.mk p r * e - c * e) * e = _
        rw [sub_mul, mul_assoc, mul_assoc, he.eq]
      have hd' : d ∈ I • m.range := by
        rw [← Submodule.map_top, ← Submodule.map_smul'', Ideal.smul_top_eq_map]
        exact ⟨d, hd, hdm⟩
      have hce : c * e ∈ N := Submodule.mem_span_singleton.mpr ⟨r.eval a₀, Algebra.smul_def ..⟩
      refine Submodule.mem_sup.mpr ⟨c * e, hce, d, hd', ?_⟩
      change c * e + (AdjoinRoot.mk p r * e - c * e) = AdjoinRoot.mk p r * e
      exact add_sub_cancel _ _
    let : Module.Finite A T := hp.finite_adjoinRoot
    have hfg : m.range.FG := by
      rw [← Submodule.map_top]
      exact Module.Finite.fg_top.map m
    have hN := Submodule.le_of_le_smul_of_le_jacobson_bot hfg hI hmod
    let t := AdjoinRoot.root p
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hN ⟨t, rfl⟩)
    change a • e = t * e at ha
    rw [Algebra.smul_def] at ha
    have heval : AdjoinRoot.mk p (X - C a) * e = 0 := by
      rw [map_sub, sub_mul, sub_eq_zero]
      exact ha.symm
    let evalLift := (leval a₀).comp (AdjoinRoot.modByMonicHom hp)
    have hEvalLift (x : T) : π (evalLift x) = φ x := by
      symm
      calc
        φ x = φ (AdjoinRoot.mk p (AdjoinRoot.modByMonicHom hp x)) :=
          congrArg φ (AdjoinRoot.mk_leftInverse hp x).symm
        _ = π (evalLift x) := by rw [AdjoinRoot.lift_mk, eval₂_at_apply]; rfl
    have hEvalLiftUnit : IsUnit (evalLift e) := (isUnit_map_iff π _).mp (by
      rw [hEvalLift, hφe]
      exact isUnit_one)
    have hroot : F (p.eval a) * e = 0 := by
      have h := map_mul_eq_eval_mul (AdjoinRoot.mk p) a e heval p
      rw [AdjoinRoot.mk_self, zero_mul, AdjoinRoot.mk_C] at h
      exact h.symm
    refine ⟨a, ?_, ?_⟩
    · change p.eval a = 0
      have h := congrArg evalLift hroot
      change evalLift (F (p.eval a) * e) = evalLift 0 at h
      rw [← Algebra.smul_def] at h
      rw [map_smul, map_zero, smul_eq_mul] at h
      exact hEvalLiftUnit.mul_left_inj.mp (h.trans (zero_mul _).symm)
    · apply Ideal.Quotient.eq.mp
      change π a = π a₀
      have h := congrArg φ ha
      change φ (F a * e) = φ (t * e) at h
      rw [map_mul, map_mul, hφF, hφe, mul_one, mul_one] at h
      exact h.trans (AdjoinRoot.lift_root hπ)

end PhilipponHenselianRootByIdempotents

end

section

set_option autoImplicit false

open Polynomial


namespace PhilipponHenselianIntegralStability

/-- The monic factor lifting needed for idempotents is the case where the
two reduced factors are equal positive powers of `X` and `X - 1`. -/
abbrev liftsPowerFactors (A : Type*) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (p : A[X]) (n : ℕ), n ≠ 0 → p.Monic →
    p.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ n →
    ∃ g h : A[X], p = g * h ∧ g.Monic ∧ h.Monic ∧
      g.map (Ideal.Quotient.mk I) = X ^ n ∧ h.map (Ideal.Quotient.mk I) = (X - 1) ^ n

/-- The determinant trick and monic factor lifting produce idempotent lifts
in the quotient of any integral extension. -/
theorem lift_idempotent {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.IsIntegral) (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (factor : liftsPowerFactors A I) (e₀ : B ⧸ I.map f) (he₀ : IsIdempotentElem e₀) :
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk (I.map f) e = e₀ := by
  let : Algebra A B := f.toAlgebra
  let : Algebra.IsIntegral A B := ⟨hf⟩
  let J := I.map f
  let ρ := Ideal.Quotient.mk J
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective e₀
  change IsIdempotentElem (ρ b) at he₀
  by_cases hB : Subsingleton B
  · exact ⟨0, IsIdempotentElem.zero, congrArg ρ (hB.elim _ _)⟩
  let : Nontrivial B := not_subsingleton_iff_nontrivial.mp hB
  let : Nontrivial A := ⟨⟨0, 1, fun h => (zero_ne_one (α := B)) (by simpa using congrArg f h)⟩⟩
  have hz : b * (b - 1) ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change ρ (b * (b - 1)) = 0
    rw [map_mul, map_sub, map_one, mul_sub, he₀.eq, mul_one, sub_self]
  obtain ⟨p, hp, hpa, hcoeff⟩ := exists_monic_aeval_eq_zero_forall_mem_of_mem_map
    (R := A) (S := B) (I := I) hz
  let n := p.natDegree
  have hn : n ≠ 0 := by
    intro h
    rw [eq_one_of_monic_natDegree_zero hp h, map_one] at hpa
    exact one_ne_zero hpa
  let π := Ideal.Quotient.mk I
  have hpmod : p.map π = X ^ n := by
    ext d
    rw [coeff_map, coeff_X_pow]
    split_ifs with hd
    · subst d
      rw [hp.coeff_natDegree, map_one]
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr (hcoeff d hd)
  let q := p.comp (X * (X - 1))
  have hlin : (X - 1 : A[X]).Monic := by simpa using monic_X_sub_C (1 : A)
  have hqM : q.Monic := hp.comp (monic_X.mul hlin) (by
    rw [monic_X.natDegree_mul hlin, natDegree_X]
    simp)
  have hqzero : aeval b q = 0 := by
    change aeval b (p.comp (X * (X - 1))) = 0
    rw [aeval_comp, map_mul, map_sub, aeval_X, map_one]
    exact hpa
  have hqmod : q.map π = X ^ n * (X - 1) ^ n := by
    change (p.comp (X * (X - 1))).map π = _
    rw [map_comp, hpmod, Polynomial.map_mul, Polynomial.map_sub, map_X, Polynomial.map_one,
      pow_comp, X_comp, mul_pow]
  obtain ⟨g, h, hq, _, _, hg, hh⟩ := factor q n hn hqM hqmod
  let c := aeval b g
  let d := aeval b h
  have hcd : c * d = 0 := by
    change aeval b g * aeval b h = 0
    rw [← map_mul, ← hq, hqzero]
  have hIJ : I ≤ J.comap f := Ideal.le_comap_map
  let qmap := Ideal.quotientMap J f hIJ
  let : Algebra (A ⧸ I) (B ⧸ J) := qmap.toAlgebra
  have hreduce (t : A[X]) : ρ (aeval b t) = aeval (ρ b) (t.map π) :=
    map_aeval_eq_aeval_map (Ideal.quotientMap_comp_mk hIJ) t b
  have hc : ρ c = ρ b := by
    change ρ (aeval b g) = ρ b
    rw [hreduce, hg, map_pow, aeval_X, he₀.pow_eq hn]
  have hd : ρ d = (ρ b - 1) ^ n := by
    change ρ (aeval b h) = (ρ b - 1) ^ n
    rw [hreduce, hh, map_pow, map_sub, aeval_X, map_one]
  let d' := (-1 : B) ^ n * d
  have hd' : ρ d' = 1 - ρ b := by
    change ρ ((-1 : B) ^ n * d) = _
    rw [map_mul, map_pow, map_neg, map_one, hd, ← mul_pow, neg_one_mul, neg_sub]
    exact he₀.one_sub.pow_eq hn
  have hcd' : c * d' = 0 := by
    change c * ((-1 : B) ^ n * d) = 0
    rw [mul_left_comm, hcd, mul_zero]
  have hsum : ρ (c + d') = 1 := by rw [map_add, hc, hd', add_sub_cancel]
  let : IsLocalHom ρ := isLocalHom_of_le_jacobson_bot J
    (PhilipponHenselianIdempotents.map_le_jacobson f hf I hI)
  have hu : IsUnit (c + d') := (isUnit_map_iff ρ _).mp (hsum.symm ▸ isUnit_one)
  obtain ⟨u, hu⟩ := hu
  let w := (↑u⁻¹ : B)
  have hw : w * (c + d') = 1 := by rw [← hu, Units.inv_mul]
  have hwmod : ρ w = 1 := by
    have h := congrArg ρ hw
    rwa [map_mul, hsum, mul_one, map_one] at h
  refine ⟨w * c, ?_, ?_⟩
  · change (w * c) * (w * c) = w * c
    have hcc : c * (c + d') = c * c := by rw [mul_add, hcd', add_zero]
    calc
      (w * c) * (w * c) = w * w * (c * c) := by ring
      _ = (w * c) * (w * (c + d')) := by rw [← hcc]; ring
      _ = w * c := by rw [hw, mul_one]
  · change ρ (w * c) = ρ b
    rw [map_mul, hwmod, hc, one_mul]

/-- Stability under integral maps follows from the special monic factor
lifting over the base, applied to idempotents of the target's root algebras. -/
theorem of_isIntegral_of_power_factors {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) [HenselianRing A I] (hf : f.IsIntegral)
    (factor : liftsPowerFactors A I) : HenselianRing B (I.map f) := by
  have hI := HenselianRing.jac (R := A) (I := I)
  apply PhilipponHenselianRootByIdempotents.henselian_of_adjoinRoot_idempotents _
    (PhilipponHenselianIdempotents.map_le_jacobson f hf I hI)
  intro p hp
  let : Module.Finite B (AdjoinRoot p) := hp.finite_adjoinRoot
  let r := algebraMap B (AdjoinRoot p)
  have hr : r.IsIntegral := Algebra.IsIntegral.isIntegral
  have hcomp := RingHom.IsIntegral.trans f r hf hr
  rw [Ideal.map_map]
  exact lift_idempotent (r.comp f) hcomp I hI factor

end PhilipponHenselianIntegralStability

end

section

set_option autoImplicit false
open Polynomial
universe u

theorem solution
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A)
    [HenselianRing A I] (hf : f.IsIntegral) : HenselianRing B (I.map f) := by
  exact PhilipponHenselianIntegralStability.of_isIntegral_of_power_factors f I hf
    (fun p n hn hp hred => HenselianRing.exists_monic_factorization_of_map_eq_X_pow_mul_sub_one_pow I p n hn hp hred)

end

end
