-- Prove2me | solution 1 for GlobalTheory.SW.weil_level_and_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:39:47.633801+00:00
-- url     : https://prove2.me/submissions/cb204f6c-b781-4bd3-af0a-41ea3cb0efc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Theorems.Thm_GlobalTheory_SW_WeilLevel_sq_le_of_finsum_eq
import Theorems.Thm_GlobalTheory_SW_WeilLevel_relIndex_nsmul
import Theorems.Thm_GlobalTheory_SW_WeilLevel_levelL_mul
import Theorems.Thm_GlobalTheory_SW_WeilLevel_hasLevel_of_levelL
import Theorems.Thm_GlobalTheory_SW_WeilLevel_heisH_fix
import Theorems.Thm_GlobalTheory_SW_WeilLevel_cols_mul
import Theorems.Thm_GlobalTheory_SW_WeilLevel_levelL_of_fix
import Theorems.Thm_GlobalTheory_SW_Base_mem_stdL
import Theorems.Thm_GlobalTheory_SW_LinChange_haar_eq_haarAt
import Theorems.Thm_GlobalTheory_SW_Model_mem_stdL
import Theorems.Thm_GlobalTheory_SW_haar_eq_haarAt
import Theorems.Thm_GlobalTheory_SW_heisH_laws
import Theorems.Thm_GlobalTheory_SW_unitary_act_halfSpace
import Theorems.Thm_GlobalTheory_SW_weil_action


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
open WeilLevel
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ c R : ℕ, 0 < c → 0 < R → ∃ (R' : ℕ) (C : ℝ), 0 < R' ∧ ∀ (M : ℕ), ∀ Λ ∈ Vset E n M, ∀ γ ∈ UU E N, Den c γ → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, LevelL Λ R φ → IsSB φ ∧ LevelL Λ R' (weil Ψ γ φ) ∧ ∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → ∀ x, ‖weil Ψ γ φ x‖ ≤ C * B := by
  intro E _ _ _ Ψ hΨ n N hn c R hc hR
  have hD : 0 < (NumberField.discr E).natAbs := Int.natAbs_pos.2 (NumberField.discr_ne_zero E)
  set R' : ℕ := (NumberField.discr E).natAbs * (2 * R * c) with hR'
  have hR'0 : 0 < R' := by positivity
  set e := Module.finrank ℚ E * (Fintype.card (Fin n) * Fintype.card (Fin N)) with he
  refine ⟨R', (R' : ℝ) ^ e, hR'0, ?_⟩
  rintro M Λ ⟨-, hΛ, s, hs, -, h1, h2⟩ γ hγ hden φ hφ
  have hSB : IsSB φ := ⟨s * R, by positivity, hasLevel_of_levelL h1 h2 hφ⟩
  have hψ : LevelL Λ R' (weil Ψ γ φ) := by
    refine levelL_of_fix hΛ fun d b hd hb => ?_
    set X := Matrix.fromCols d b * ((c : E) • γ) with hX
    have hX1 : ColsIn Λ X.toCols₁ := fun a => cols_mul hd hb hden (Sum.inl a)
    have hX2 : ColsIn Λ X.toCols₂ := fun a => cols_mul hd hb hden (Sum.inr a)
    have h3 := (GlobalTheory.SW.heisH_laws E Ψ hΨ n N hn (((2 * R : ℕ) : E) • X.toCols₁)
      (((2 * R : ℕ) : E) • X.toCols₂) φ hSB).2.2 γ hγ
    have h4 : Matrix.fromCols (((2 * R : ℕ) : E) • X.toCols₁) (((2 * R : ℕ) : E) • X.toCols₂) =
        ((2 * R : ℕ) : E) • X := by
      ext k (j | j) <;> rfl
    rw [heisH_fix hΛ hφ hX1 hX2, h4, hX, Matrix.mul_smul, smul_smul, Matrix.smul_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).1.1, Matrix.mul_one,
      ← Nat.cast_mul] at h3
    exact h3.symm
  refine ⟨hSB, hψ, fun B hB x => ?_⟩
  have hφ' : LevelL Λ R' φ := by
    have := levelL_mul hφ ((NumberField.discr E).natAbs * (2 * c))
    rwa [show (NumberField.discr E).natAbs * (2 * c) * R = R' by rw [hR']; ring] at this
  have hip := ((GlobalTheory.SW.weil_action E Ψ hΨ n N hn γ hγ φ hSB).2.2.2.1 φ hSB).1
  have hsq : ∀ k : Matrix (Fin n) (Fin N) E → ℂ, LevelL Λ R' k →
      ip k k = haarAt (s * R') fun x => k x * conj (k x) := by
    intro k hk
    have hk' := hasLevel_of_levelL h1 h2 hk
    exact (haar_eq_haarAt E _ _ (s * R') _ (by positivity)
      ⟨fun x hx => hk'.1 x (left_ne_zero_of_mul hx), fun x y hy => by simp only [hk'.2 x y hy]⟩).1
  rw [hsq _ hψ, hsq _ hφ', haarAt, haarAt] at hip
  have hip2 := mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _
    (by exact_mod_cast (show s * R' ≠ 0 by positivity)))) hip
  let u : AddSubgroup (Matrix (Fin n) (Fin N) E) :=
    { carrier := {x | ColsIn Λ ((R' : E) • x)}
      zero_mem' := fun a => by rw [smul_zero]; exact Λ.zero_mem
      add_mem' := fun {x y} hx hy a => by rw [smul_add]; exact Λ.add_mem (hx a) (hy a)
      neg_mem' := fun {x} hx a => by rw [smul_neg]; exact Λ.neg_mem (hx a) }
  have hu : ∀ x ∈ u, IntM (((s * R' : ℕ) : E) • x) := fun x hx k a => by
    rw [Nat.cast_mul, mul_smul]
    exact (Model.mem_stdL _).1 (h1 _ (hx a)) k
  set t := u.map (nsmulAddMonoidHom (R' * R')) with ht
  have htu : t ≤ u := by
    rintro _ ⟨y, hy, rfl⟩
    exact u.nsmul_mem hy _
  have hper : ∀ k : Matrix (Fin n) (Fin N) E → ℂ, LevelL Λ R' k → ∀ x, ∀ y ∈ t,
      k (x + y) = k x := by
    rintro k hk x _ ⟨y, hy, rfl⟩
    rw [nsmulAddMonoidHom_apply, ← Nat.cast_smul_eq_nsmul E, Nat.cast_mul, mul_smul]
    exact hk.2 x _ hy
  have hR'E : (R' : E) ≠ 0 := by exact_mod_cast hR'0.ne'
  have hst : perSub E (Fin n) (Fin N) (s * R') ≤ t := by
    rw [perSub, AddSubgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(R' : E)⁻¹ • (s : E) • y, fun a => ?_, ?_⟩
    · rw [smul_inv_smul₀ hR'E]
      exact h2 _ ((Model.mem_stdL _).2 fun k => hy k a)
    · rw [nsmulAddMonoidHom_apply, ← Nat.cast_smul_eq_nsmul E, Nat.cast_mul, mul_smul,
        smul_inv_smul₀ hR'E, smul_smul, Nat.cast_mul s, mul_comm (s : E)]
  have hle : t.map (nsmulAddMonoidHom ((s * R') * (s * R'))) ≤
      perSub E (Fin n) (Fin N) (s * R') := by
    rintro _ ⟨y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨_, hu y (htu hy), ?_⟩
    rw [nsmulAddMonoidHom_apply, ← Nat.cast_smul_eq_nsmul E, Nat.cast_mul, mul_smul]
  have hi1 := (relIndex_nsmul t (show 0 < s * R' by positivity) (fun x hx => hu x (htu hx))
    (show 0 < (s * R') * (s * R') by positivity)).1
  obtain ⟨hi2, hi3⟩ := relIndex_nsmul u (show 0 < s * R' by positivity) hu
    (show 0 < R' * R' by positivity)
  have h5 := sq_le_of_finsum_eq hst
    (ne_zero_of_dvd_ne_zero hi1 (AddSubgroup.relIndex_dvd_of_le_left _ hle)) hi2 φ (weil Ψ γ φ)
    (hper _ hφ') (hper _ hψ) hφ'.1 hψ.1 hip2.symm B hB x
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (h5.trans ?_)
  have h6 : ((t.relIndex u : ℕ) : ℝ) ≤ ((R' : ℝ) ^ e) ^ 2 := by
    rw [sq, ← mul_pow]
    exact_mod_cast hi3
  rw [mul_pow]
  gcongr
end GlobalTheory.SW
