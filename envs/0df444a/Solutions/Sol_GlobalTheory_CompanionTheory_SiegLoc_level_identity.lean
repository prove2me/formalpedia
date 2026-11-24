-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.level_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:39:43.755413+00:00
-- url     : https://prove2.me/submissions/dc0ef207-fe7d-4f8a-97c5-23c2541afdb4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianRepCountFourierExpansion
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_image_sol
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_gram_sub_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_neg_mem_herm
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_nuAt_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory.CompanionTheory.SiegLoc.LevelId
namespace GlobalTheory.CompanionTheory.SiegLoc
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (m n k : ℕ) (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), cT σ S = S → cT σ T = T → (∀ Y : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k), Y ∈ hermMod σ ϖ n k → (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = (Nat.card (hermMod σ ϖ n k) : ℂ)) ∧ (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = 0)) → (∀ B ∈ hermMod σ ϖ n k, (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ψ k (Matrix.trace (B * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x)))) = (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) * (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B))) → siegAt ϖ σ ψ q ε m T k = ((densAt σ ϖ S T k : ℝ) : ℂ) := by
  intro R _ σ ϖ q ε hR _ ψ hψ m n k S T hS hT horth hgauss
  classical
  have : Fintype ↥(hermMod σ ϖ n k) := Fintype.ofFinite _
  have hx : ∀ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
      (∑' B : hermMod σ ϖ n k,
        ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x - red ϖ k T)))) =
        if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then
          (Nat.card (hermMod σ ϖ n k) : ℂ) else 0 := by
    intro x
    have hmem := gram_sub_mem σ ϖ hR.inv hR.fix_ϖ k S T hS hT x
    by_cases hxe : cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T
    · rw [if_pos hxe]
      exact (horth _ hmem).1 (sub_eq_zero.mpr hxe)
    · rw [if_neg hxe]
      exact (horth _ hmem).2 (sub_ne_zero.mpr hxe)
  have hsplit : ∀ (B : hermMod σ ϖ n k) (x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)),
      ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x - red ϖ k T))) =
        ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
          ψ k (-Matrix.trace (B.1 * red ϖ k T)) := by
    intro B x
    rw [Matrix.mul_sub, Matrix.trace_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hsol : (solCount σ ϖ S T k : ℂ) = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
      if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0 := by
    unfold solCount
    rw [image_sol σ ϖ hR.fix_ϖ k S T, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.natCast_card_filter]
    exact Finset.sum_congr rfl fun x _ => if_congr Iff.rfl rfl rfl
  have h1 : ∀ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), (Nat.card (hermMod σ ϖ n k) : ℂ) *
      (if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0) =
      ∑ B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
        ψ k (-Matrix.trace (B.1 * red ϖ k T)) := by
    intro x
    rw [mul_ite, mul_one, mul_zero, ← hx x, tsum_fintype]
    exact Finset.sum_congr rfl fun B _ => hsplit B x
  have hcount : (Nat.card (hermMod σ ϖ n k) : ℂ) * (solCount σ ϖ S T k : ℂ) =
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) *
        ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
          ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    calc (Nat.card (hermMod σ ϖ n k) : ℂ) * (solCount σ ϖ S T k : ℂ)
        = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), (Nat.card (hermMod σ ϖ n k) : ℂ) *
            (if cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x = red ϖ k T then (1 : ℂ) else 0) := by
          rw [hsol, Finset.mul_sum]
      _ = ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ∑ B : hermMod σ ϖ n k,
            ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
              ψ k (-Matrix.trace (B.1 * red ϖ k T)) := Finset.sum_congr rfl fun x _ => h1 x
      _ = ∑ B : hermMod σ ϖ n k, ∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
            ψ k (Matrix.trace (B.1 * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x))) *
              ψ k (-Matrix.trace (B.1 * red ϖ k T)) := Finset.sum_comm
      _ = ∑ B : hermMod σ ϖ n k, (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) *
            (ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
              ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1)) := by
          refine Finset.sum_congr rfl fun B _ => ?_
          rw [← Finset.sum_mul, hgauss B.1 B.2]
          ring
      _ = _ := by rw [Finset.mul_sum]
  have hneg : ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) =
      ∑ B : hermMod σ ϖ n k, ψ k (Matrix.trace (red ϖ k T * B.1)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    let e : hermMod σ ϖ n k ≃ hermMod σ ϖ n k :=
      { toFun := fun B => ⟨-B.1, neg_mem_herm σ ϖ n k B.2⟩
        invFun := fun B => ⟨-B.1, neg_mem_herm σ ϖ n k B.2⟩
        left_inv := fun B => Subtype.ext (neg_neg _)
        right_inv := fun B => Subtype.ext (neg_neg _) }
    refine Fintype.sum_equiv e _ _ fun B => ?_
    show _ = ψ k (Matrix.trace (red ϖ k T * -B.1)) *
      ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ (-B.1))
    rw [nuAt_neg, Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_mul_comm]
  have hfin : siegAt ϖ σ ψ q ε m T k = ∑ B : hermMod σ ϖ n k, ψ k (-Matrix.trace (B.1 * red ϖ k T)) *
        ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1) := by
    unfold siegAt
    rw [tsum_fintype, hneg]
  have hM : (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcast : ((densAt σ ϖ S T k : ℝ) : ℂ) = (solCount σ ϖ S T k : ℂ) * (Nat.card (hermMod σ ϖ n k) : ℂ) /
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) := by
    unfold densAt
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_natCast,
      Complex.ofReal_natCast]
  rw [hfin, hcast, eq_div_iff hM]
  linear_combination (-1 : ℂ) * hcount
end GlobalTheory.CompanionTheory.SiegLoc
