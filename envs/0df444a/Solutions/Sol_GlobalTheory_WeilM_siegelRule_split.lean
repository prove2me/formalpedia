-- Prove2me | solution 1 for GlobalTheory.WeilM.siegelRule_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:36:08.318392+00:00
-- url     : https://prove2.me/submissions/a21335ed-fa06-4d83-8b86-2015d8d8738b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Theorems.Thm_GlobalTheory_WeilM_diag_invariant_comp
import Theorems.Thm_GlobalTheory_WeilM_det_siegel
import Theorems.Thm_GlobalTheory_WeilM_flat_fromCols
import Theorems.Thm_GlobalTheory_WeilM_isDblCoord_split
import Theorems.Thm_GlobalTheory_WeilM_norm_pair
import Theorems.Thm_GlobalTheory_WeilM_splitOm_apply
import Theorems.Thm_GlobalTheory_WeilM_splitOm_mem_SB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] [Invertible (2 : F)]
namespace GlobalTheory.WeilM
theorem _root_.solution (ψ : AddChar F ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {JA : Matrix α α (F × F)}
    {JB : Matrix β β (F × F)} (hA : IsHerm (swapA F) JA) (hB : IsHerm (swapA F) JB) (σ : κ ≃ α × β)
    (χ : (F × F)ˣ →* Circle) (hχ : ∀ a : Fˣ, χ (Units.map (algebraMap F (F × F) : F →* F × F) a) = 1) :
    SiegelRule (swapA F) (sbClass F) ψ (1, -1) JA (dbl JB) (splitDarboux hA hB.dbl (dblNum σ)) χ (diagCols β)
      (splitOm (distribHaarChar F) χ (dbl JB) (dblNum σ)) := by
  classical
  intro l _ hl p t hp φ hφ
  have hD : ∀ {S : Type} [CommRing S] (z : Matrix α β S), z * (diagCols β : Matrix (β ⊕ β) β S)ᵀ = fromCols z z := by
    intro S _ z
    rw [diagCols, transpose_fromRows, mul_fromCols, transpose_one, Matrix.mul_one]
  have hl' : ∀ x y : κ → F, ∀ φ ∈ SB (κ ⊕ κ → F), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ := by
    intro x y φ hφ
    have := hl ((splitDarboux hA hB σ).e.symm (x, y)) φ hφ
    rwa [Darboux.rho, hD, isDblCoord_split hA hB σ, LinearEquiv.apply_symm_apply] at this
  obtain ⟨h1, h2⟩ := det_siegel hB p t.val hp
  let t₁ : GL β F := GeneralLinearGroup.map (RingHom.fst F F) t
  let t₂ : GL β F := GeneralLinearGroup.map (RingHom.snd F F) t
  have h2' : GeneralLinearGroup.det (ugFst _ p) = GeneralLinearGroup.det t₁ * (GeneralLinearGroup.det t₂)⁻¹ :=
    eq_mul_inv_of_mul_eq (Units.ext h2)
  have h1' : ((ugFst _ p)⁻¹).val * (diagCols β : Matrix (β ⊕ β) β F) =
      (diagCols β : Matrix (β ⊕ β) β F) * (t₁⁻¹).val := by
    have h3 : (ugFst _ p).val * (diagCols β : Matrix (β ⊕ β) β F) = (diagCols β : Matrix (β ⊕ β) β F) * t₁.val := h1
    have := congrArg (fun N => ((ugFst _ p)⁻¹).val * N * (t₁⁻¹).val) h3
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
    rw [this, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  let G : Matrix κ κ F := ((1 : Matrix α α F) ⊗ₖ (t₁⁻¹).val).submatrix σ σ
  have hG : G.det = ((GeneralLinearGroup.det t₁)⁻¹ ^ Fintype.card α : Fˣ) := by
    rw [det_submatrix_equiv_self, det_kronecker, det_one, one_pow, one_mul, ← map_inv, Units.val_pow_eq_pow_val]
    rfl
  let g : GL κ F := GeneralLinearGroup.mkOfDetNeZero G (hG ▸ Units.ne_zero _)
  have hg : GeneralLinearGroup.det g = (GeneralLinearGroup.det t₁)⁻¹ ^ Fintype.card α := Units.ext hG
  have hgx : ∀ X : Matrix α β F, g.val.mulVec (flat σ X) = flat σ (X * (t₁⁻¹).valᵀ) := by
    intro X
    funext k
    show ∑ k', ((1 : Matrix α α F) ⊗ₖ (t₁⁻¹).val) (σ k) (σ k') * X (σ k').1 (σ k').2 = _
    rw [Fintype.sum_equiv σ _ (fun q => ((1 : Matrix α α F) ⊗ₖ (t₁⁻¹).val) (σ k) q * X q.1 q.2) fun _ => rfl,
      Fintype.sum_prod_type, flat_apply, mul_apply]
    simp [kroneckerMap_apply, one_apply, mul_comm]
  set s := splitChar (distribHaarChar F) χ (Fintype.card α) (GeneralLinearGroup.det (ugFst _ p)) with hs
  have key := diag_invariant_comp ψ hψ hψ1 l hl' g ((SB _).smul_mem s hφ)
    (splitOm_mem_SB (distribHaarChar F) χ (dbl JB) (dblNum σ) p hφ) (fun x => by
      obtain ⟨X, rfl⟩ := (flat σ).surjective x
      rw [splitOm_apply, hgx, ← flat_fromCols, ← flat_fromCols, LinearEquiv.symm_apply_apply, ← hD, ← hD,
        Matrix.mul_assoc, Matrix.mul_assoc, ← transpose_mul, ← transpose_mul, h1']
      rfl)
  have hpos : ∀ u : Fˣ, (0 : ℝ) < distribHaarChar F u := fun u => distribHaarChar_pos (A := F) (g := u)
  have hne : ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos _).ne'
  refine mul_left_cancel₀ hne ?_
  rw [key, map_smul, smul_eq_mul, ← mul_assoc]
  congr 1
  have hdet : GeneralLinearGroup.det t = Units.map (MonoidHom.inl F F) (GeneralLinearGroup.det (ugFst _ p)) *
      Units.map (algebraMap F (F × F) : F →* F × F) (GeneralLinearGroup.det t₂) := by
    refine Units.ext (Prod.ext ?_ ?_)
    · exact ((RingHom.fst F F).map_det t.val).trans h2.symm
    · exact ((RingHom.snd F F).map_det t.val).trans (one_mul _).symm
  have hN : Units.map (Algebra.norm F : F × F →* F) (GeneralLinearGroup.det t) =
      GeneralLinearGroup.det t₁ * GeneralLinearGroup.det t₂ := by
    refine Units.ext ((norm_pair _).trans ?_)
    exact congrArg₂ (· * ·) ((RingHom.fst F F).map_det t.val) ((RingHom.snd F F).map_det t.val)
  rw [hN, hdet, map_mul χ, hχ, mul_one, hs, mul_left_comm]
  refine congrArg₂ (fun x y : ℂ => x * y) rfl ?_
  show ((_ : ℝ) : ℂ) = _ * (((distribHaarChar F _ : ℝ) ^ _ : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, hg, h2']
  congr 1
  simp only [map_mul, map_pow, map_inv, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv]
  have p1 := hpos (GeneralLinearGroup.det t₁)
  have p2 := hpos (GeneralLinearGroup.det t₂)
  generalize (distribHaarChar F (GeneralLinearGroup.det t₁) : ℝ) = a at p1
  generalize (distribHaarChar F (GeneralLinearGroup.det t₂) : ℝ) = b at p2
  rw [Real.mul_rpow p1.le (inv_pos.mpr p2).le, Real.mul_rpow p1.le p2.le, Real.inv_rpow p2.le, ← Real.rpow_neg p2.le,
    inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg p1.le, ← mul_assoc, ← Real.rpow_add p1]
  congr 2 <;> ring
end GlobalTheory.WeilM
