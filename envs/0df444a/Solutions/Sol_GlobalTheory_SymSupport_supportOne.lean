-- Prove2me | solution 1 for GlobalTheory.SymSupport.supportOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:55.576356+00:00
-- url     : https://prove2.me/submissions/ba2cf8fb-4430-4c13-872d-a22ac6da6d07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Theorems.Thm_GlobalTheory_SymSupport_mem_R_of_inR
import Theorems.Thm_GlobalTheory_SymSupport_typeFrame_val
import Theorems.Thm_GlobalTheory_SymSupport_typeFrame_inv_val
import Theorems.Thm_GlobalTheory_SymSupport_InR_conj
import Theorems.Thm_GlobalTheory_SymSupport_exists_factor
import Theorems.Thm_GlobalTheory_SymSupport_exists_match
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg
import Theorems.Thm_GlobalTheory_StepData_intM_fromBlocks
import Theorems.Thm_GlobalTheory_StepData_intM_one
import Theorems.Thm_GlobalTheory_StepData_intM_zero
import Theorems.Thm_GlobalTheory_StepData_mem_KO
import Theorems.Thm_GlobalTheory_StepData_mem_stabLat
import Theorems.Thm_GlobalTheory_StepData_standardOrderExtendedBasis_apply_low_block
import Theorems.Thm_GlobalTheory_StepData_stdOrd_f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymSupport
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SymSupport
theorem _root_.solution (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (hP : S.Pattern t) :
    S.SupportOne t := by
  intro j c H h hh x₀ e hΦ
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  let B := (typeFrame S.ϖ o).bas
  let B' := (typeFrame S.ϖ o').bas
  have hG : B⁻¹ * h * B ∈ KO k _ := mem_stabLat.1 hh
  let Z := (B⁻¹).val * affPt 1 x₀ e * B'.val
  let J := (S.P.iter t S.μ S.tame (j + 1)).reindex o
  have hΦ' : (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      ((((B⁻¹ * h * B)⁻¹).val * Z.submatrix id o').submatrix ((ixSucc _ t j).trans o) id) ≠ 0 := by
    have e1 : ((B⁻¹ * h * B)⁻¹).val * Z = (B⁻¹).val * ((h⁻¹).val * affPt 1 x₀ e) * B'.val := by
      simp only [Z, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B.val, Units.mul_inv, Matrix.one_mul]
    have e2 : ((B⁻¹ * h * B)⁻¹).val * Z.submatrix id o' = (((B⁻¹ * h * B)⁻¹).val * Z).submatrix id o' := rfl
    rw [e2, e1]
    exact hΦ
  obtain ⟨κ₀, hκ, hc⟩ := exists_match _ _ _ hG _ hΦ'
  have hκ' : κ₀ ∈ J.J := hκ
  have hZ : ∀ r s, Z r s = Sum.elim (fun _ => 1) (fun i : Fin (c + 1) => ((S.ϖ : k) ^ (i.val + 1))⁻¹) r *
      affPt 1 x₀ e r s * Sum.elim (fun _ => 1) (fun i : Fin (c + 1 + 1) => (S.ϖ : k) ^ (i.val + 1)) s := by
    intro r s
    simp only [Z, B, B', typeFrame_val, typeFrame_inv_val, mul_diagonal, diagonal_mul]
  obtain ⟨r, hr, D, hD, hD0, u, hu, eq⟩ := exists_factor (mul_mem hG (J.le_KO hκ'))
    (fun s => ∃ i, s = .inl (.inl i)) (by
      rintro l _ ⟨i, rfl⟩
      have h1 : valuation k ((B⁻¹ * h * B * κ₀).val (.inr l) (.inl (.inl (.inl i))) -
        Z (.inr l) (.inl (.inl (.inl i)))) < 1 := hc (.inr l) (.inl (.inl i))
      rwa [hZ, show affPt 1 x₀ e (.inr l) (.inl (.inl (.inl i))) = 0 by simp [affPt, basePt, Free],
        mul_zero, zero_mul, sub_zero] at h1) (by
      intro r i hl
      have h1 : valuation k ((B⁻¹ * h * B * κ₀).val r (o (.inl (.inr ⟨i.val, by omega⟩))) -
        Z r (o' (.inl (.inr ⟨i.castSucc.val, by simp; omega⟩)))) < 1 := hc r (.inl (.inr ⟨i.val, by omega⟩))
      rw [standardOrderExtendedBasis_apply_low_block, standardOrderExtendedBasis_apply_low_block, hZ] at h1
      convert h1 using 3
      rcases r with r | r
      · have : i = 0 := by simpa [lev] using hl
        simp [affPt, basePt, Free, this]
      · have : ¬ r < i := by simpa [lev] using hl
        by_cases hri : r = i
        · subst hri; simp [affPt, basePt, Free]
        · simp [affPt, basePt, Free, this, hri, Fin.val_inj])
  have hlow : lowU D ∈ J.J := by
    have hK : lowU D ∈ KO k _ := mem_KO.2 ⟨intM_fromBlocks.2 ⟨intM_one, intM_zero, hD, intM_one⟩,
      intM_fromBlocks.2 ⟨intM_one, intM_zero, hD.neg, intM_one⟩⟩
    refine (hP (j + 1) ((reGL o).symm (lowU D))).2 ⟨?_, fun a b hab => ?_⟩
    · obtain ⟨h1, h2⟩ := mem_KO.1 hK
      exact mem_KO.2 ⟨fun a b => h1 _ _, fun a b => by rw [← map_inv]; exact h2 _ _⟩
    · have : (lowU D).val (o a) (o b) = (1 : Matrix _ _ k) (o a) (o b) := by
        obtain ⟨a, rfl⟩ := o.symm.surjective a
        obtain ⟨b, rfl⟩ := o.symm.surjective b
        rw [o.apply_symm_apply, o.apply_symm_apply]
        rcases a with a | a <;> rcases b with b | b
        · simp [lowU, Matrix.one_apply]
        · simp [lowU]
        · have a1 : o.symm (.inr a) = .inl (.inr ⟨a.val, by omega⟩) :=
            o.symm_apply_eq.2 (standardOrderExtendedBasis_apply_low_block _ t _ _ _ a).symm
          rcases b with (b | b) | b
          · simpa [lowU] using hD0 a _ ⟨b, rfl⟩
          · have a3 : o.symm (.inl (.inl (.inr b))) = .inl (.inr ⟨c + 1 + b.val, by omega⟩) :=
              o.symm_apply_eq.2 (stdOrd_f _ t _ _ _ b).symm
            rw [a1, a3] at hab
            exact absurd (show a.val < c + 1 + b.val by omega) hab
          · have a6 : o.symm (.inl (.inr b)) = .inr b := o.symm_apply_eq.2 rfl
            rw [a1, a6] at hab
            exact absurd trivial hab
        · simp [lowU, Matrix.one_apply]
      rw [reGL_symm_val, submatrix_apply, this]
      simp [Matrix.one_apply]
  have hJ : lowU D * u * κ₀⁻¹ ∈ J.J := mul_mem (mul_mem hlow (J.KOne_le hu)) (inv_mem hκ')
  refine ⟨B * r * B⁻¹, mem_R_of_inR (hr.conj S.ϖ o), B * (lowU D * u * κ₀⁻¹) * B⁻¹, ?_, ?_⟩
  · change (reGL o).symm (B⁻¹ * (B * (lowU D * u * κ₀⁻¹) * B⁻¹) * B) ∈ (S.P.iter t S.μ S.tame (j + 1)).J
    have : B⁻¹ * (B * (lowU D * u * κ₀⁻¹) * B⁻¹) * B = lowU D * u * κ₀⁻¹ := by group
    rw [this]; exact hJ
  · calc h = B * (B⁻¹ * h * B * κ₀) * κ₀⁻¹ * B⁻¹ := by group
      _ = _ := by rw [eq]; group
end GlobalTheory.SymSupport
