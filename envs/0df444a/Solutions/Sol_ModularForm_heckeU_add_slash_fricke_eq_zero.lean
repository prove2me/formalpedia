-- Prove2me | solution 1 for ModularForm.heckeU_add_slash_fricke_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/1cd1897a-3cf4-551b-bc28-69a72a242662

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_heckeU_add_slash_fricke_eq_zero

set_option autoImplicit false

open scoped ModularForm MatrixGroups
open UpperHalfPlane

namespace P2mSolHeckeUAddSlashFrickeMF

def R (j : ℤ) : SL(2, ℤ) := ⟨!![0, -1; 1, j], by simp [Matrix.det_fin_two_of]⟩

@[scoped simp] theorem coe_R (j : ℤ) : ((R j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, j] :=
  rfl

theorem R_apply_10 (j : ℤ) : (R j : SL(2, ℤ)) 1 0 = 1 := rfl

theorem R_inv_apply_10 (j : ℤ) : ((R j)⁻¹ : SL(2, ℤ)) 1 0 = -1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem R_mul_R_inv_apply_10 (i j : ℤ) : ((R i) * (R j)⁻¹ : SL(2, ℤ)) 1 0 = j - i := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

theorem R_mul_apply_10 (j : ℤ) (g : SL(2, ℤ)) : ((R j) * g : SL(2, ℤ)) 1 0 = g 0 0 + j * g 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem slash_two_scalar (f : ℍ → ℂ) (u : ℝˣ) :
    f ∣[(2 : ℤ)] (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = f := by
  ext τ
  have hdet : (((Matrix.GeneralLinearGroup.scalar (Fin 2) u).det : ℝˣ) : ℝ) = u * u := by
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.scalar, sq]
  have hpos : 0 < (((Matrix.GeneralLinearGroup.scalar (Fin 2) u).det : ℝˣ) : ℝ) := by
    rw [hdet]; exact mul_self_pos.mpr u.ne_zero
  rw [ModularForm.slash_apply, glScalar_smul, denom_scalar, hdet]
  simp only [σ, hpos, if_true, ContinuousAlgEquiv.refl_apply]
  have hu : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast u.ne_zero
  rw [abs_mul_self]
  push_cast
  field_simp

noncomputable abbrev mk' : SL(2, ℤ) →* ↥𝒮ℒ := (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict

abbrev Γ (p : ℕ) : Subgroup (GL (Fin 2) ℝ) := (CongruenceSubgroup.Gamma0 p : Subgroup SL(2, ℤ))

abbrev Q (p : ℕ) := ↥𝒮ℒ ⧸ ((Γ p).subgroupOf 𝒮ℒ)

theorem mk_eq_mk_iff (p : ℕ) (a b : SL(2, ℤ)) :
    (⟦mk' a⟧ : Q p) = ⟦mk' b⟧ ↔ a⁻¹ * b ∈ CongruenceSubgroup.Gamma0 p := by
  rw [Quotient.eq, QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf, ← map_inv, ← map_mul]
  exact Subgroup.mem_map_iff_mem Matrix.SpecialLinearGroup.mapGL_injective

theorem mk'_surjective : Function.Surjective mk' := MonoidHom.rangeRestrict_surjective _

noncomputable def ι (p : ℕ) : Option (Fin p) → Q p
  | none => ⟦mk' 1⟧
  | some j => ⟦mk' (R (j : ℕ))⁻¹⟧

theorem ι_bijective (p : ℕ) [hp : Fact p.Prime] : Function.Bijective (ι p) := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  constructor
  · rintro (_ | i) (_ | j) h
    · rfl
    · exfalso
      simp only [ι] at h
      rw [mk_eq_mk_iff, inv_one, one_mul, CongruenceSubgroup.Gamma0_mem, R_inv_apply_10] at h
      simp at h
    · exfalso
      simp only [ι] at h
      rw [mk_eq_mk_iff, inv_inv, mul_one, CongruenceSubgroup.Gamma0_mem, R_apply_10] at h
      simp at h
    · simp only [ι] at h
      rw [mk_eq_mk_iff, inv_inv, CongruenceSubgroup.Gamma0_mem, R_mul_R_inv_apply_10] at h
      push_cast at h
      rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff'] at h
      congr 1
      exact Fin.ext (by
        rw [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt i.isLt] at h
        exact h.symm)
  · intro q
    induction q using Quotient.inductionOn with
    | h x =>
      obtain ⟨g, rfl⟩ := mk'_surjective x
      by_cases hc : ((g 1 0 : ℤ) : ZMod p) = 0
      · refine ⟨none, ?_⟩
        simp only [ι]
        rw [mk_eq_mk_iff, inv_one, one_mul, CongruenceSubgroup.Gamma0_mem]
        exact hc
      · set j : ZMod p := -((g 0 0 : ℤ) : ZMod p) * ((g 1 0 : ℤ) : ZMod p)⁻¹ with hj
        refine ⟨some ⟨j.val, ZMod.val_lt j⟩, ?_⟩
        simp only [ι]
        rw [mk_eq_mk_iff, inv_inv, CongruenceSubgroup.Gamma0_mem, R_mul_apply_10]
        push_cast
        rw [ZMod.natCast_zmod_val, hj]
        field_simp
        ring

theorem quotientFunc_ι_none (p : ℕ) (f : ModularForm (Γ p) 2) :
    SlashInvariantForm.quotientFunc f (ι p none) = ⇑f := by
  simp [ι, SlashInvariantForm.quotientFunc_mk]

theorem quotientFunc_ι_some (p : ℕ) (f : ModularForm (Γ p) 2) (j : Fin p) :
    SlashInvariantForm.quotientFunc f (ι p (some j)) =
      ⇑f ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (R (j : ℕ)) : GL (Fin 2) ℝ) := by
  simp [ι, SlashInvariantForm.quotientFunc_mk]

theorem sum_quotientFunc_eq (p : ℕ) [Fact p.Prime] (f : ModularForm (Γ p) 2) [Fintype (Q p)] :
    ∑ q : Q p, SlashInvariantForm.quotientFunc f q =
      ⇑f + ∑ j : Fin p, ⇑f ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (R (j : ℕ)) : GL (Fin 2) ℝ) := by
  rw [← (Equiv.ofBijective (ι p) (ι_bijective p)).sum_comp, Fintype.sum_option]
  simp only [Equiv.ofBijective_apply, quotientFunc_ι_none, quotientFunc_ι_some]

theorem fricke_mul_heckeMatrix (p : ℕ) (hp : p ≠ 0) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) (j : ℕ) :
    W * ModularForm.heckeMatrix p j =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) (by exact_mod_cast hp)) *
        (Matrix.SpecialLinearGroup.mapGL ℝ (R (j : ℕ)) : GL (Fin 2) ℝ) := by
  ext i k
  rw [Units.val_mul, Units.val_mul, hW, ModularForm.val_heckeMatrix hp,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar, R, Matrix.natCast_apply]

theorem heckeU_slash_fricke_eq (p : ℕ) (hp : p ≠ 0) (f : ℍ → ℂ) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ModularForm.heckeU 2 p (f ∣[(2 : ℤ)] W) =
      ∑ j : Fin p, f ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (R (j : ℕ)) : GL (Fin 2) ℝ) := by
  rw [ModularForm.heckeU_def, ← Finset.sum_range fun j => f ∣[(2 : ℤ)]
    (Matrix.SpecialLinearGroup.mapGL ℝ (R (j : ℕ)) : GL (Fin 2) ℝ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← SlashAction.slash_mul, fricke_mul_heckeMatrix p hp W hW j, SlashAction.slash_mul,
    slash_two_scalar]

theorem main (p : ℕ) [hp : Fact p.Prime] (f : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ModularForm.heckeU 2 p (⇑f ∣[(2 : ℤ)] W) + ⇑f = 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h0 : ModularForm.trace 𝒮ℒ f = 0 :=
    rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero _
  have h1 := congrArg (fun g : ModularForm 𝒮ℒ 2 => (⇑g : ℍ → ℂ)) h0
  simp only [ModularForm.coe_trace, ModularForm.coe_zero] at h1
  rw [sum_quotientFunc_eq] at h1
  rw [heckeU_slash_fricke_eq p hp.out.ne_zero _ W hW, add_comm]
  exact h1

def frickeConj (p : ℕ) (g : SL(2, ℤ)) (hg : (p : ℤ) ∣ g 1 0) : SL(2, ℤ) :=
  ⟨!![g 1 1, -(g 1 0 / p); -(p * g 0 1), g 0 0], by
    have hdet := Matrix.det_fin_two g.1
    rw [g.2] at hdet
    rw [Matrix.det_fin_two_of]
    have := Int.ediv_mul_cancel hg
    linear_combination (-1 : ℤ) * hdet - (g 0 1) * this⟩

theorem frickeConj_mem (p : ℕ) (g : SL(2, ℤ)) (hg : (p : ℤ) ∣ g 1 0) :
    frickeConj p g hg ∈ CongruenceSubgroup.Gamma0 p := by
  rw [CongruenceSubgroup.Gamma0_mem]
  show (((!![g 1 1, -(g 1 0 / p); -(p * g 0 1), g 0 0] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) :
    ZMod p) = 0
  simp

theorem fricke_mul_mapGL (p : ℕ) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0])
    (g : SL(2, ℤ)) (hg : (p : ℤ) ∣ g 1 0) :
    W * (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ (frickeConj p g hg) : GL (Fin 2) ℝ) * W := by
  have hc : (((g 1 0 / p : ℤ) : ℝ)) * (p : ℝ) = ((g 1 0 : ℤ) : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hg
  ext i k
  rw [Units.val_mul, Units.val_mul, hW, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, frickeConj] <;> linarith [hc]

open ConjAct Pointwise in
theorem le_conj (p : ℕ) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    Γ p ≤ toConjAct W⁻¹ • Γ p := by
  rintro x ⟨g, hg, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← toConjAct_inv, inv_inv, toConjAct_smul]
  have hg' : (p : ℤ) ∣ g 1 0 := by
    have := (CongruenceSubgroup.Gamma0_mem (N := p) (A := g)).mp hg
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  rw [fricke_mul_mapGL p W hW g hg', mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨_, frickeConj_mem p g hg', rfl⟩

open ConjAct Pointwise in

noncomputable def slashFricke (p : ℕ) (f : ModularForm (Γ p) 2) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ModularForm (Γ p) 2 where
  toFun := ⇑f ∣[(2 : ℤ)] W
  slash_action_eq' γ hγ := (ModularForm.translate f W).slash_action_eq' γ (le_conj p W hW hγ)
  holo' := (ModularForm.translate f W).holo'
  bdd_at_cusps' hc := (ModularForm.translate f W).bdd_at_cusps' (hc.mono (le_conj p W hW))

theorem coe_slashFricke (p : ℕ) (f : ModularForm (Γ p) 2) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ⇑(slashFricke p f W hW) = ⇑f ∣[(2 : ℤ)] W := rfl

theorem fricke_mul_self (p : ℕ) (hp : p ≠ 0) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    W * W = Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.mk0 (-(p : ℝ)) (neg_ne_zero.mpr (by exact_mod_cast hp))) := by
  ext i k
  rw [Units.val_mul, hW]
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar]

theorem main' (p : ℕ) [hp : Fact p.Prime] (f : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ModularForm.heckeU 2 p ⇑f + ⇑f ∣[(2 : ℤ)] W = 0 := by
  have h := main p (slashFricke p f W hW) W hW
  rwa [coe_slashFricke, ← SlashAction.slash_mul, fricke_mul_self p hp.out.ne_zero W hW,
    slash_two_scalar] at h

end P2mSolHeckeUAddSlashFrickeMF
p2m_reactivate "P2MW.S_ModularForm_heckeU_add_slash_fricke_eq_zero.P2mSolHeckeUAddSlashFrickeMF"

theorem solution (p : ℕ) [Fact p.Prime]
    (f : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (W : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, -1; (p : ℝ), 0]) :
    ModularForm.heckeU 2 p ⇑f + ⇑f ∣[(2 : ℤ)] W = 0 :=
  P2mSolHeckeUAddSlashFrickeMF.main' p f W hW

end S_ModularForm_heckeU_add_slash_fricke_eq_zero
end P2MW
export P2MW.S_ModularForm_heckeU_add_slash_fricke_eq_zero (solution)
