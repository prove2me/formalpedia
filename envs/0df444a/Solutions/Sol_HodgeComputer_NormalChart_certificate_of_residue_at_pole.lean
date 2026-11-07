-- Prove2me | solution 1 for HodgeComputer.NormalChart.certificate_of_residue_at_pole
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T03:52:07.838301+00:00
-- url     : https://prove2.me/submissions/8d913142-852b-4940-ad5f-af8a9003943a

import Definitions.Def_HodgeComputerNormalChart
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open HodgeComputer HodgeComputer.NormalChart MvPolynomial
open scoped BigOperators

private theorem mixed_partials (F : AmbientPoly 5) (i j : Fin 6) :
    pderiv i (pderiv j F) = pderiv j (pderiv i F) := by
  ext m
  simp only [coeff_pderiv]
  have he : m + Finsupp.single i 1 + Finsupp.single j 1 =
      m + Finsupp.single j 1 + Finsupp.single i 1 := by ac_rfl
  rw [he]
  by_cases hij : i = j
  · subst j
    rfl
  · simp [Finsupp.add_apply, Finsupp.single_apply, hij, Ne.symm hij]
    ring

private theorem gradient_identity (F A S : AmbientPoly 5) (W : Fin 5 → AmbientPoly 5) :
    directional F (numerator F A S W) = A * denominator F S := by
  simp only [directional, Fin.sum_univ_succ, numerator, Fin.cases_zero, Fin.cases_succ,
    denominator]
  have he (j : Fin 5) : pderiv j.succ F * (normal F * W j) =
      normal F * (pderiv j.succ F * W j) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  unfold normal
  ring

private theorem residue_identity (F A S : AmbientPoly 5) (W : Fin 5 → AmbientPoly 5) :
    divergenceNumerator (denominator F S) (numerator F A S W) = residue F A S W := by
  have hc (j : Fin 5) : pderiv 0 (pderiv j.succ F) = pderiv j.succ (normal F) :=
    mixed_partials F 0 j.succ
  simp only [divergenceNumerator, divergence, directional, Fin.sum_univ_succ,
    numerator, Fin.cases_zero, Fin.cases_succ, denominator, residue,
    map_sub, map_add, map_sum, pderiv_mul, hc]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  ring

private theorem integer_homogeneous {P : AmbientPoly 5} {d : ℕ}
    (h : P.IsHomogeneous d) : Homogeneous P (d : ℤ) := by
  intro m hm
  have he : m.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using h hm
  exact_mod_cast he

theorem solution (q : ℕ) (hq : 0 < q)
    (F A S : AmbientPoly 5) (W : Fin 5 → AmbientPoly 5) (Q : AmbientPoly 5)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous 6) (hAhom : A.IsHomogeneous (6 * q))
    (hP : normal F ≠ 0) (hFP : IsRelPrime F (normal F))
    (hS : S ≠ 0) (hShom : S.IsHomogeneous S.totalDegree) (hFS : IsRelPrime F S)
    (hWhom : ∀ j, (W j).IsHomogeneous (S.totalDegree + (6 * q - 5)))
    (hres : residue F (MvPolynomial.C ((q : ℂ)⁻¹) * A) S W = F ^ q * Q) :
    Verify F A 6 q (denominator F S)
      (numerator F (MvPolynomial.C ((q : ℂ)⁻¹) * A) S W) Q := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hscale : (q : AmbientPoly 5) * (MvPolynomial.C ((q : ℂ)⁻¹) * A) = A := by
    rw [← map_natCast (MvPolynomial.C : ℂ →+* AmbientPoly 5) q,
      ← mul_assoc, ← map_mul, mul_inv_cancel₀ hqC, map_one, one_mul]
  have hBhom : (MvPolynomial.C ((q : ℂ)⁻¹) * A).IsHomogeneous (6 * q) := by
    simpa only [zero_add] using (isHomogeneous_C (Fin 6) ((q : ℂ)⁻¹)).mul hAhom
  have hPhom : (normal F).IsHomogeneous 5 := hFhom.pderiv
  have hD : denominator F S ≠ 0 := mul_ne_zero hP hS
  have hDhom : (denominator F S).IsHomogeneous (5 + S.totalDegree) := hPhom.mul hShom
  have hDdeg : (denominator F S).totalDegree = 5 + S.totalDegree := hDhom.totalDegree hD
  have hNhom : ∀ i, (numerator F (MvPolynomial.C ((q : ℂ)⁻¹) * A) S W i).IsHomogeneous
      (6 * q + S.totalDegree) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change ((MvPolynomial.C ((q : ℂ)⁻¹) * A) * S -
        ∑ j : Fin 5, pderiv j.succ F * W j).IsHomogeneous _
      apply (hBhom.mul hShom).sub
      apply IsHomogeneous.sum
      intro j _
      simpa only [show 6 - 1 = 5 from rfl,
        show 5 + (S.totalDegree + (6 * q - 5)) = 6 * q + S.totalDegree by omega] using
        (hFhom.pderiv (i := j.succ)).mul (hWhom j)
    · change (normal F * W j).IsHomogeneous _
      simpa only [show 5 + (S.totalDegree + (6 * q - 5)) = 6 * q + S.totalDegree by omega] using
        hPhom.mul (hWhom j)
  refine {
    hypersurface_ne_zero := hF
    hypersurface_homogeneous := hFhom
    source_homogeneous := ?_
    denominator_ne_zero := hD
    denominator_homogeneous := ?_
    numerator_homogeneous := ?_
    denominator_legal := hFP.mul_right hFS
    identity := ?_ }
  · convert integer_homogeneous hAhom using 1 <;> push_cast <;> omega
  · simpa only [hDdeg] using hDhom
  · intro i
    convert integer_homogeneous (hNhom i) using 1 <;> rw [hDdeg] <;> push_cast <;> omega
  · unfold defect
    rw [gradient_identity, residue_identity, hres]
    calc
      _ = (A - (q : AmbientPoly 5) * (MvPolynomial.C ((q : ℂ)⁻¹) * A)) *
          (denominator F S)^2 + F^(q+1) * Q := by rw [pow_succ]; ring
      _ = _ := by rw [hscale]; ring

#print axioms solution
