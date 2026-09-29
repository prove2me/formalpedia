-- Prove2me | solution 1 for ModularCurve.eisensteinQuotientRational_isTorsion_heckeModuleBar_of_perPrimeFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/942319a9-66f1-596a-b0b8-90a2e3f567cf

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_JZeroTorsionFinite
import Definitions.Def_ModularCurve_EisensteinIdeal
import Mathlib.Algebra.Ring.Action.Submonoid
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eisensteinQuotientRational_isTorsion_heckeModuleBar_of_perPrimeFinite
open ModularCurve AlgebraicCurve

set_option autoImplicit false

private theorem one_notMem_eisensteinMaximalIdeal (p : ℕ) {q : ℕ} (hq : q.Prime) :
    (1 : HeckeAlg) ∉ eisensteinMaximalIdeal p q := by
  rw [mem_eisensteinMaximalIdeal_iff, map_one, Int.natCast_dvd, Int.natAbs_one]
  exact hq.not_dvd_one

private theorem quot_smul_eq_zero_of_JZero_smul_eq_zero (p : ℕ) [Fact p.Prime]
    (s : HeckeAlg) (hs : letI := heckeModuleBar p; ∀ x : JZero p, s • x = 0) :
    letI := heckeModuleBar p
    ∀ w : EisensteinQuotient p (heckeModuleBar p), s • w = 0 := by
  letI := heckeModuleBar p
  intro w
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [← Submodule.Quotient.mk_smul, hs x, Submodule.Quotient.mk_zero]

private theorem fg_of_le_of_addGroupFG {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (C : AddSubgroup M) (hC : AddGroup.FG ↥C) (N : Submodule R M) (hle : ∀ w ∈ N, w ∈ C) :
    N.FG := by
  haveI : Module.Finite ℤ ↥C := Module.Finite.iff_addGroup_fg.mpr hC
  let f : ↥C →ₗ[ℤ] M := C.subtype.toIntLinearMap
  have h1 : ((N.restrictScalars ℤ).comap f).FG := IsNoetherian.noetherian _
  have h2 : ((N.restrictScalars ℤ).comap f).map f = N.restrictScalars ℤ := by
    apply Submodule.map_comap_eq_self
    intro w hw
    exact ⟨⟨w, hle w hw⟩, rfl⟩
  have h3 : (N.restrictScalars ℤ).FG := h2 ▸ h1.map f
  exact Submodule.FG.of_restrictScalars ℤ h3

private theorem fg_of_le_closure (p : ℕ) [Fact p.Prime]
    (hfgc : letI := heckeModuleBar p
      AddGroup.FG ↥(AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)))) :
    letI := heckeModuleBar p
    ∀ N' : Submodule HeckeAlg (EisensteinQuotient p (heckeModuleBar p)),
      (∀ w ∈ N', w ∈ AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p))) →
      N'.FG := by
  intro N' hle
  exact fg_of_le_of_addGroupFG _ hfgc N' hle

private theorem smul_mem_rational (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) :
    letI := heckeModuleBar p
    ∀ (t : HeckeAlg), ∀ z ∈ eisensteinQuotientRational p (heckeModuleBar p),
      t • z ∈ eisensteinQuotientRational p (heckeModuleBar p) := by
  letI := heckeModuleBar p
  haveI := smulCommClass_JZero_of_heckeOperatorsCommuteBar p hcomm
  rintro t z ⟨x, hx, rfl⟩
  refine ⟨t • x, ?_, ?_⟩
  · intro σ
    have h := (eisensteinKernelSubmodule p (heckeModuleBar p)).smul_mem t (hx σ)
    rwa [smul_sub, ← smul_comm σ t x] at h
  · rfl

private theorem smul_mem_closure_rational (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p) :
    letI := heckeModuleBar p
    ∀ (t : HeckeAlg), ∀ w ∈ AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)),
      t • w ∈ AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)) := by
  letI := heckeModuleBar p
  intro t w hw
  induction hw using AddSubgroup.closure_induction with
  | mem x hx => exact AddSubgroup.subset_closure (smul_mem_rational p hcomm t x hx)
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

private theorem span_le_closure (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) :
    letI := heckeModuleBar p
    ∀ w ∈ Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p)),
      w ∈ AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)) := by
  letI := heckeModuleBar p
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact AddSubgroup.subset_closure hx
  | zero => exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => exact AddSubgroup.add_mem _ hx hy
  | smul t x _ hx => exact smul_mem_closure_rational p hcomm t x hx

private theorem witness_dvd (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p)
    (hfgc : letI := heckeModuleBar p
      AddGroup.FG ↥(AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p))))
    (hA : letI := heckeModuleBar p
      ∀ q : ℕ, q.Prime → q ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12 →
        ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
          (eisensteinMaximalIdeal p q ^ m •
              Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))) =
            (eisensteinMaximalIdeal p q ^ m₀ •
              Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))))
    (q : ℕ) (hq : q.Prime) (hdvd : q ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12) :
    letI := heckeModuleBar p
    ∀ z ∈ eisensteinQuotientRational p (heckeModuleBar p),
      ∃ s : HeckeAlg, s ∉ eisensteinMaximalIdeal p q ∧ IsOfFinAddOrder (s • z) := by
  letI := heckeModuleBar p
  obtain ⟨m₀, hstab⟩ := hA q hq hdvd
  set M := Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p)) with hMdef
  set N' := eisensteinMaximalIdeal p q ^ m₀ • M with hN'def
  have hPN : eisensteinMaximalIdeal p q • N' = N' := by
    have h1 := hstab (m₀ + 1) (Nat.le_succ m₀)
    calc eisensteinMaximalIdeal p q • N'
        = (eisensteinMaximalIdeal p q * eisensteinMaximalIdeal p q ^ m₀) • M :=
          (Submodule.mul_smul _ _ _).symm
      _ = eisensteinMaximalIdeal p q ^ (m₀ + 1) • M := by rw [← pow_succ']
      _ = N' := h1
  have hfg : N'.FG :=
    fg_of_le_closure p hfgc N'
      (fun w hw => span_le_closure p hcomm w (Submodule.smul_le_right hw))
  obtain ⟨r, hr1, hr0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      (eisensteinMaximalIdeal p q) N' hfg (le_of_eq hPN.symm)
  intro z hz
  refine ⟨r, ?_, ?_⟩
  · intro hrmem
    have h1 : (1 : HeckeAlg) ∈ eisensteinMaximalIdeal p q := by
      have h2 := Ideal.sub_mem _ hrmem hr1
      simpa using h2
    exact one_notMem_eisensteinMaximalIdeal p hq h1
  · rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨q ^ m₀, pow_pos hq.pos m₀, ?_⟩
    have hzM : z ∈ M := Submodule.subset_span hz
    have hmem : ((q : HeckeAlg) ^ m₀) • z ∈ N' :=
      Submodule.smul_mem_smul (Ideal.pow_mem_pow (natCast_mem_eisensteinMaximalIdeal p q) m₀) hzM
    have h0 : r • (((q : HeckeAlg) ^ m₀) • z) = 0 := hr0 _ hmem
    calc (q ^ m₀ : ℕ) • (r • z)
        = (((q ^ m₀ : ℕ) : HeckeAlg)) • (r • z) := (Nat.cast_smul_eq_nsmul HeckeAlg _ _).symm
      _ = ((q : HeckeAlg) ^ m₀) • (r • z) := by rw [Nat.cast_pow]
      _ = (((q : HeckeAlg) ^ m₀) * r) • z := (mul_smul _ _ _).symm
      _ = (r * ((q : HeckeAlg) ^ m₀)) • z := by rw [mul_comm]
      _ = r • (((q : HeckeAlg) ^ m₀) • z) := mul_smul _ _ _
      _ = 0 := h0

private theorem witness_not_dvd (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p)
    (hC : ∃ t ∈ eisensteinIdeal p, ∃ k : ℤ, k ≠ 0 ∧
        k.natAbs ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12 ∧
        heckeEvalBar hcomm t = k • (1 : Module.End ℤ (JZero p)))
    (q : ℕ) (hnd : ¬ q ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12) :
    letI := heckeModuleBar p
    ∀ z : EisensteinQuotient p (heckeModuleBar p),
      ∃ s : HeckeAlg, s ∉ eisensteinMaximalIdeal p q ∧ IsOfFinAddOrder (s • z) := by
  letI := heckeModuleBar p
  intro z
  obtain ⟨t, ht, k, _, hkdvd, heq⟩ := hC
  refine ⟨(k : HeckeAlg) - t, ?_, ?_⟩
  ·
    rw [mem_eisensteinMaximalIdeal_iff, map_sub, map_intCast]
    have ht0 : eisensteinEval p t = 0 := (mem_eigenIdeal_iff _ _).mp ht
    rw [ht0, sub_zero, Int.natCast_dvd]
    exact fun h => hnd (h.trans hkdvd)
  ·
    have hzero : ∀ x : JZero p, ((k : HeckeAlg) - t) • x = 0 := by
      intro x
      rw [sub_smul, heckeModuleBar_smul_def hcomm t x, heq, LinearMap.smul_apply,
        Module.End.one_apply, Int.cast_smul_eq_zsmul, sub_self]
    rw [quot_smul_eq_zero_of_JZero_smul_eq_zero p _ hzero z]
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨1, one_pos, one_nsmul 0⟩

theorem solution
    (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p)
    (hfgc : letI := heckeModuleBar p
      AddGroup.FG ↥(AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p))))
    (hA : letI := heckeModuleBar p
      ∀ q : ℕ, q.Prime → q ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12 →
        ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
          (eisensteinMaximalIdeal p q ^ m •
              Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))) =
            (eisensteinMaximalIdeal p q ^ m₀ •
              Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p))))
    (hB : letI := heckeModuleBar p
      ∀ z ∈ AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)),
        (∀ q : ℕ, q.Prime →
            ∃ s : HeckeAlg, s ∉ eisensteinMaximalIdeal p q ∧ IsOfFinAddOrder (s • z)) →
          IsOfFinAddOrder z)
    (hC : ∃ t ∈ eisensteinIdeal p, ∃ k : ℤ, k ≠ 0 ∧
        k.natAbs ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12 ∧
        heckeEvalBar hcomm t = k • (1 : Module.End ℤ (JZero p))) :
    letI := heckeModuleBar p
    ∀ z ∈ eisensteinQuotientRational p (heckeModuleBar p), ∃ n : ℕ, 0 < n ∧ n • z = 0 := by
  letI := heckeModuleBar p
  intro z hz
  rw [← isOfFinAddOrder_iff_nsmul_eq_zero]
  refine hB z (AddSubgroup.subset_closure hz) ?_
  intro q hq
  by_cases hdvd : q ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12
  · exact witness_dvd p hcomm hfgc hA q hq hdvd z hz
  · exact witness_not_dvd p hcomm hC q hdvd z

end S_ModularCurve_eisensteinQuotientRational_isTorsion_heckeModuleBar_of_perPrimeFinite
end P2MW
export P2MW.S_ModularCurve_eisensteinQuotientRational_isTorsion_heckeModuleBar_of_perPrimeFinite (solution)
