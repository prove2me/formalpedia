-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedLogMatrix_mulVec_eq_formalJet_of_cutoff
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-07T21:25:45.539973+00:00
-- url     : https://prove2.me/submissions/dfa87116-e9db-4825-af43-eae54361b154

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
open OAI.PiExponent
open OAI.PiExponent.FormalInterpolation

noncomputable def badP : WeightedPolynomial (m := 1) 0 (fun _ : Fin 1 => (0 : Real)) 2 := by
  apply Subtype.mk (MvPolynomial.X (1 : Fin 2))
  intro a ha
  rw [MvPolynomial.support_X] at ha
  simp only [Finset.mem_singleton] at ha
  subst a
  simp [InterpolationMatrix.columnWeights]
  norm_num [Fin.cases, Fin.induction, Fin.induction.go]

noncomputable def badRow : InterpolationMatrix.Row 1 1 1 (fun _ : Fin 1 => (0 : Real)) 2 := by
  let a : Fin 2 -> Nat := fun i => if i = 0 then 1 else 0
  apply Prod.mk 0
  apply Subtype.mk a
  simp only [OAI.PiExponent.strictWeightedSimplex, Finset.mem_filter]
  constructor
  · simp only [OAI.PiExponent.realWeightedSimplex, Finset.mem_filter,
      Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · intro i
      fin_cases i <;> norm_num [a, InterpolationMatrix.rowWeights, Fin.cases, Fin.induction, Fin.induction.go]
    · norm_num [a, InterpolationMatrix.rowWeights, Fin.sum_univ_succ, Fin.cases, Fin.induction, Fin.induction.go]
  · norm_num [a, InterpolationMatrix.rowWeights, Fin.sum_univ_succ, Fin.cases, Fin.induction, Fin.induction.go]

theorem solution : Not (forall {m K : Nat} (w0 v0 theta H : Real)
    (w : Fin m -> Real) (T : Fin m -> Nat) (r : Fin m -> Complex)
    (P : FormalInterpolation.WeightedPolynomial w0 w H),
    0 < v0 -> 0 < theta -> (forall i, 0 <= w i) ->
    (forall i, w i / theta <= (T i : Real) * v0) ->
    forall rho : InterpolationMatrix.Row K v0 theta w H,
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
          (fun c => P.val.coeff (InterpolationMatrix.exponentVector c.1)) rho =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
          (FormalInterpolation.formalJet (fun i => (rho.1.val : Complex) * r i) P.val)) := by
  intro h
  have hh := h (m := 1) (K := 1) 0 1 1 2
    (fun _ : Fin 1 => (0 : Real)) (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => (0 : Complex)) badP
    (by norm_num) (by norm_num)
    (by intro i; norm_num) (by intro i; norm_num) badRow
  have hleft :
      (InterpolationMatrix.truncatedLogMatrix 1 0 1 1 (fun _ : Fin 1 => (0 : Real)) 2
        (fun _ => (0 : Complex)) (fun _ => 0)).mulVecLin
        (fun c : InterpolationMatrix.Column 0 (fun _ : Fin 1 => (0 : Real)) 2 =>
          badP.val.coeff (InterpolationMatrix.exponentVector c.1)) badRow = 0 := by
    have hcol : forall c : InterpolationMatrix.Column 0 (fun _ : Fin 1 => (0 : Real)) 2,
        c.1 = (fun _ : Fin 2 => 0) := by
      intro c
      have hmem : c.1 ∈ OAI.PiExponent.realWeightedSimplex
          (InterpolationMatrix.columnWeights 0 (fun _ : Fin 1 => (0 : Real))) 2 := c.2
      simp only [OAI.PiExponent.realWeightedSimplex, Finset.mem_filter] at hmem
      have hp := Fintype.mem_piFinset.mp hmem.1
      ext i
      fin_cases i
      · have hi := hp (0 : Fin 2)
        simpa [InterpolationMatrix.columnWeights, Fin.cases] using hi
      · have hi := hp (1 : Fin 2)
        have hw : InterpolationMatrix.columnWeights 0 (fun _ : Fin 1 => (0 : Real))
            (1 : Fin 2) = 0 := by rfl
        have hf : ⌊(2 : Real) /
            InterpolationMatrix.columnWeights 0 (fun _ : Fin 1 => (0 : Real)) (1 : Fin 2)⌋₊ = 0 := by
          rw [hw]
          norm_num
        have hz : c.1 1 < 1 := by
          simpa [Finset.mem_range, hw, hf] using hi
        exact Nat.lt_one_iff.mp hz
    rw [Matrix.mulVecLin_apply, Matrix.mulVec]
    apply Finset.sum_eq_zero
    intro c hc
    rw [mul_eq_zero]
    right
    simp [badP, hcol c, InterpolationMatrix.exponentVector,
      Finsupp.equivFunOnFinite, MvPolynomial.coeff_X]
    intro he
    have hv := congrArg (fun f : Finsupp (Fin 2) Nat => f 1) he
    norm_num [Finsupp.single_apply] at hv
  have hidx : InterpolationMatrix.exponentVector badRow.2.val =
      Finsupp.single (0 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [badRow, InterpolationMatrix.exponentVector, Finsupp.single_apply]
  let L : MvPowerSeries (Fin 2) Complex :=
    FormalInterpolation.liftSeries 1 (PowerSeries.log Complex)
  have hlift : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) L = 1 := by
    have hc := MvPowerSeries.coeff_coeff_finSuccEquiv
      (p := L) (k := 1) (x := (0 : Finsupp (Fin 1) Nat))
    have hcons : Finsupp.cons 1 (0 : Finsupp (Fin 1) Nat) =
        Finsupp.single (0 : Fin 2) 1 := by
      exact (Finsupp.cons_eq_single_zero_iff).2 ⟨rfl, rfl⟩
    have hc' : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) L =
        MvPowerSeries.coeff (0 : Finsupp (Fin 1) Nat)
          (PowerSeries.coeff 1 (MvPowerSeries.finSuccEquiv Complex 1 L)) := by
      simpa [hcons] using hc.symm
    rw [hc']
    simp [L, FormalInterpolation.liftSeries, PowerSeries.coeff_map, PowerSeries.coeff_log]
  have hjet : FormalInterpolation.formalJet (fun _ => (0 : Complex)) badP.val =
      MvPowerSeries.X 1 + L := by
    simp [L, badP, FormalInterpolation.formalJet, FormalInterpolation.liftSeries,
      Fin.cases, Fin.induction, Fin.induction.go]
  have hrhs :
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector badRow.2.val)
        (FormalInterpolation.formalJet (fun _ => (0 : Complex)) badP.val) =
          (1 : Complex) := by
    rw [hidx, hjet]
    simp [hlift, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff]
  rw [hleft] at hh
  rw [hidx] at hh
  simp [badRow, zero_mul] at hh
  norm_num at hh
  rw [hjet] at hh
  norm_num [MvPowerSeries.coeff_X, hlift, Finsupp.single_eq_single_iff] at hh
