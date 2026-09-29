-- Prove2me | solution 1 for MTT.Cohomology.period_reflected_cusp_form
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-07T22:23:48.736935+00:00
-- url     : https://prove2.me/submissions/a6c39f70-f2ea-4195-9d3b-e41dc4b072e7

import Definitions.Def_MTT_PeriodPairing
import Mathlib.Tactic.FinCases
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate MatrixGroups Pointwise ModularForm
open UpperHalfPlane MTT.Cohomology

private lemma J_inv : J⁻¹ = J := by
  apply inv_eq_of_mul_eq_one_right
  simpa [sq] using J_sq

private lemma reflection_level (N : ℕ) (a : GL (Fin 2) ℝ)
    (ha : a ∈ MTT.GammaOne N) : J * a * J⁻¹ ∈ MTT.GammaOne N := by
  obtain ⟨b, hb, rfl⟩ := ha
  let c : SL(2, ℤ) := ⟨!![b 0 0, -b 0 1; -b 1 0, b 1 1], by
    have hd := b.property
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two]
    change b 0 0 * b 1 1 - (-b 0 1) * (-b 1 0) = 1
    simpa only [neg_mul_neg] using hd⟩
  refine ⟨c, ?_, ?_⟩
  · apply (CongruenceSubgroup.Gamma1_mem N c).mpr
    have hb' := (CongruenceSubgroup.Gamma1_mem N b).mp hb
    simpa [c] using hb'
  · rw [J_inv]
    ext i j
    change (c i j : ℝ) = ∑ x : Fin 2, (∑ y : Fin 2, J.val i y * (b y x : ℝ)) * J.val x j
    fin_cases i <;> fin_cases j <;> simp [c, Fin.sum_univ_two]

private lemma reflection_level_eq (N : ℕ) :
    ConjAct.toConjAct J⁻¹ • MTT.GammaOne N = MTT.GammaOne N := by
  ext a
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  constructor
  · intro ha
    have hh := reflection_level N _ ha
    have he : J * (J * a * J⁻¹) * J⁻¹ = a := by
      calc
        _ = (J * J) * a * (J⁻¹ * J⁻¹) := by simp only [mul_assoc]
        _ = a := by simp [J_inv, ← sq]
    simpa only [he] using hh
  · exact reflection_level N a

 theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (h : CuspForm (MTT.GammaOne N) (k : ℤ)) :
    ∃ v : CuspForm (MTT.GammaOne N) (k : ℤ),
      (∀ z : UpperHalfPlane, conj (v z) = h (periodReflect z)) ∧
      (v = 0 ↔ h = 0) := by
  let v : CuspForm (MTT.GammaOne N) (k : ℤ) :=
    CuspForm.mcast rfl (CuspForm.translate h J) (reflection_level_eq N).symm
  have hv (z : UpperHalfPlane) : v z = conj (h (periodReflect z)) := by
    change (⇑h ∣[(k : ℤ)] J) z = _
    have hz : J • z = periodReflect z := by
      apply UpperHalfPlane.ext
      simp [coe_J_smul, periodReflect]
    simp [ModularForm.slash_def, hz]
  refine ⟨v, fun z => by simp [hv], ?_⟩
  constructor
  · intro he
    ext z
    have hz : periodReflect (periodReflect z) = z := by
      apply UpperHalfPlane.ext
      simp [periodReflect]
    have hh := hv (periodReflect z)
    simp [he, hz] at hh
    have hh' := congrArg (starRingEnd ℂ) hh
    simpa using hh'.symm
  · intro he
    ext z
    simp [hv, he]
