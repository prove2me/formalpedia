-- Prove2me | solution 1 for MTT.periods_exist
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-06T14:08:59.168029+00:00
-- url     : https://prove2.me/submissions/7dd67ec3-521e-41b8-994a-5f5f01402717

import Theorems.Thm_MTT_Cohomology_base_change
import Theorems.Thm_MTT_Cohomology_integration_map
import Theorems.Thm_MTT_Cohomology_signed_evaluation
import Theorems.Thm_MTT_Cohomology_integral_finite_generation
import Theorems.Thm_MTT_Cohomology_signed_packet_multiplicity_one
import Theorems.Thm_MTT_Cohomology_eigenclass_descent
import Theorems.Thm_MTT_Cohomology_evaluation_lattice
import Mathlib.RingTheory.Flat.TorsionFree
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

private lemma evaluation_extends {N n : ℕ} (ι : MTT.Qbar →+* ℂ)
    (ψ : Hc N n MTT.Qbar) (φ : Hc N n ℂ) (h : Extends ι ψ φ)
    (j : ℕ) (r : ℚ) : ι (evaluation j r ψ) = evaluation j r φ := by
  have hh := congrArg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm
    (fun i : Fin 2 => if i = 0 then j else n-j))) (h OnePoint.infty (r : Cusp))
  simpa [evaluation, MvPolynomial.coeff_map] using hh.symm

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    Nonempty (MTT.Periods k ι f.form) := by
  obtain ⟨I, _hinj, hT, hI⟩ := MTT.Cohomology.integration_map hN hk
  obtain ⟨φ, hφ⟩ := MTT.Cohomology.signed_evaluation hN hk I hI hT ι f
  have hZ := MTT.Cohomology.integral_finite_generation (n := k-2) hN
  have hQ := MTT.Cohomology.base_change (n := k-2) hN MTT.Qbar
  have hC := MTT.Cohomology.base_change (n := k-2) hN ℂ
  have hd : ∀ s, ∃ ω : ℂ, ω ≠ 0 ∧ ∃ ψ : Hc N (k-2) MTT.Qbar,
      Extends ι ψ (ω⁻¹ • φ s) := by
    intro s
    exact MTT.Cohomology.eigenclass_descent hZ hQ hC ι f.epsilon f.coeff s
      (fun x y hx hy => MTT.Cohomology.signed_packet_multiplicity_one hN hk ι f s x y hx hy)
      (φ s) (hφ s).2
  choose ω hω ψ hψ using hd
  refine ⟨{
    omega := ω
    omega_ne := hω
    value := fun s j r => evaluation j r (ψ s) / ((k-2).choose j : MTT.Qbar)
    comparison := ?_
    lattice_fg := MTT.Cohomology.evaluation_lattice hZ hQ ψ }⟩
  intro s j r hj
  have he := evaluation_extends ι (ψ s) ((ω s)⁻¹ • φ s) (hψ s) j r
  have hi := (hφ s).1 j r hj
  have hb : (((k-2).choose j : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hj)
  simp only [map_smul, smul_eq_mul] at he
  rw [hi] at he
  rw [map_div₀, map_natCast, he]
  field_simp
