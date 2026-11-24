-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.step_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:27:42.174914+00:00
-- url     : https://prove2.me/submissions/60108b32-675c-46f9-bead-1a82a375b3d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_support_step
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_psi_shift
import Theorems.Thm_GlobalTheory_FunObj_DiagLattice_exists_symR_diag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k}
namespace GlobalTheory.FunObj.OneCosetProof
theorem _root_.solution [ν.IsAddHaarMeasure] (hs : 1 ≤ G.s) (hψ : HasConductor ψ 1)
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) (h : flatTensor hs ψ ν (moved G false g T) x y ≠ 0) (j : Fin (G.m - 1))
    (hj : frameGL (src_eq hs j) (g (G.m, j)) = diagGL (Sum.elim (fun _ => 1) fun p => ϖ ^ (e * (p.val + 1)))) :
    ∃ r ∈ symR k _ _, ∃ w ∈ KO k _, frameGL (tgt_eq hs j) (g (G.m, j + 1)) =
      r * diagGL (Sum.elim (fun _ => 1) fun p => ϖ ^ (e * (p.val + 1))) * w := by
  classical
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Vars G, moved G false g T (fill hs x y v₀) ≠ 0 := by
    by_contra hne
    push Not at hne
    apply h
    simp [flatTensor, flatIntegrand, hne]
  have hsupp := support_step hs hT g x y v₀ hv₀ j
  rw [hj] at hsupp
  refine DiagLattice.exists_symR_diag k _ _ (fun p => ϖ ^ (e * (p.val + 1))) _ ?_ ?_
  · intro i
    refine ⟨fun r => stepPt (x j) (v₀ j) r (.inr i.castSucc), ?_, ?_, ?_, ?_⟩
    · simp [stepPt, basePt, Free, Kept]
    · intro l hl
      have hl' : i.val < l.val := hl
      simp only [stepPt, basePt, Matrix.add_apply, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, Fin.val_castSucc]
      rw [dif_neg]
      · simp [hl'.ne']
      · rintro (hF | hK)
        · simp [Free] at hF; omega
        · simp [Kept] at hK
    · intro hi r
      simp only [stepPt, basePt, Matrix.add_apply, Matrix.of_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_add]
      rw [dif_neg]
      rintro (hF | hK)
      · simp [Free] at hF; omega
      · simp only [Kept, Fin.val_castSucc] at hK
        obtain ⟨hE, hEq⟩ := hK
        rw [Nat.even_iff] at hE
        omega
    · intro t
      have := hsupp t (.inr i.castSucc)
      convert this using 1
      rw [Matrix.mulVec_smul, diagGL_val, Matrix.mul_diagonal]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.mul_apply, Sum.elim_inr, Fin.val_castSucc, Units.val_pow_eq_pow_val]
      ring
  · intro i y' hy hl hlow
    have hinv : ∀ r, ∑ q, ((frameGL (tgt_eq hs j) (g (G.m, ↑j + 1)))⁻¹).val r q *
        ((frameGL (tgt_eq hs j) (g (G.m, ↑j + 1))).val *ᵥ y') q = y' r := by
      intro r
      have := congrFun (Matrix.mulVec_mulVec y' ((frameGL (tgt_eq hs j) (g (G.m, ↑j + 1)))⁻¹).val
        (frameGL (tgt_eq hs j) (g (G.m, ↑j + 1))).val) r
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
      simpa [Matrix.mulVec, dotProduct] using this
    by_cases ha0 : ((frameGL (tgt_eq hs j) (g (G.m, ↑j + 1))).val *ᵥ y') (.inr i) = 0
    · rw [ha0, map_zero]; exact zero_le
    have hd : (((ϖ ^ (e * (i.val + 1)) : kˣ) : k)) ≠ 0 := Units.ne_zero _
    have key : valuation k (((frameGL (tgt_eq hs j) (g (G.m, ↑j + 1))).val *ᵥ y') (.inr i) *
        (((ϖ ^ (e * (i.val + 1)) : kˣ) : k))⁻¹) ≤ valuation k ((1 : kˣ) : k) := by
      refine (hψ _).mp fun y'' hy'' => ?_
      let M : Matrix (Fin (topRank G (↑j + 1)) ⊕ Fin (G.m - 2 - ↑j)) (Fin (topRank G ↑j) ⊕ Fin (G.m - 2 - ↑j + 1)) k :=
        Matrix.of fun r s => if s = .inr i.succ then
          y'' / ((frameGL (tgt_eq hs j) (g (G.m, ↑j + 1))).val *ᵥ y') (.inr i) *
            ((frameGL (tgt_eq hs j) (g (G.m, ↑j + 1))).val *ᵥ y') r else 0
      have hps := psi_shift hs hT g x y h (Pi.single j M) ?_ ?_ ?_
      · rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb, ch])
          (fun hj' => absurd (Finset.mem_univ _) hj'), Pi.single_eq_same] at hps
        convert hps using 2
        simp [ch, M, Finset.sum_ite_eq', div_mul_cancel₀ _ ha0]
      · intro j' r s hF
        by_cases hjj : j' = j
        · subst hjj
          rw [Pi.single_eq_same]
          simp only [M, Matrix.of_apply]
          split_ifs with hs'
          · subst hs'
            rcases r with r | l
            · have hi : i.val < (G.m - 2 - j'.val) / 2 := by
                by_contra hc
                apply hF
                simp only [Free, Fin.val_succ]
                omega
              simp [hlow hi r]
            · have hil : i < l := by
                by_contra hc
                apply hF
                simp only [Free, Fin.val_succ]
                rw [Fin.lt_def] at hc
                omega
              simp [hl l hil]
          · rfl
        · rw [Pi.single_eq_of_ne hjj]; rfl
      · intro j' r s
        by_cases hjj : j' = j
        · subst hjj; simp [M]
        · rw [Pi.single_eq_of_ne hjj]; rfl
      · intro j' r s
        by_cases hjj : j' = j
        · subst hjj
          rw [Pi.single_eq_same, hj, diagGL_val, Matrix.mul_diagonal]
          rcases s with s | s
          · simp [M, Matrix.mul_apply]
          · by_cases hsi : s = i.succ
            · subst hsi
              have hx1 : ((frameGL (tgt_eq hs j') (g (G.m, ↑j' + 1))).val *ᵥ y') (.inr i) *
                  (((ϖ ^ (e * (i.val + 1)) : kˣ) : k))⁻¹ ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hd)
              have hent : ((((frameGL (tgt_eq hs j') (g (G.m, ↑j' + 1)))⁻¹).val * M) r (.inr i.succ)) *
                  ((Sum.elim (fun _ : Fin (topRank G ↑j') => (1 : kˣ)) (fun p : Fin (G.m - 2 - ↑j' + 1) => ϖ ^ (e * (p.val + 1))) (.inr i.succ) : kˣ) : k) =
                  (y'' / (((frameGL (tgt_eq hs j') (g (G.m, ↑j' + 1))).val *ᵥ y') (.inr i) *
                    (((ϖ ^ (e * (i.val + 1)) : kˣ) : k))⁻¹)) * y' r * ((ϖ ^ e : kˣ) : k) := by
                simp only [M, Matrix.mul_apply, Matrix.of_apply, if_true, Sum.elim_inr, Fin.val_succ]
                rw [← hinv r, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
                refine Finset.sum_congr rfl fun q _ => ?_
                simp only [Units.val_pow_eq_pow_val]
                field_simp
                ring
              rw [hent, map_mul, map_mul]
              have h1 : valuation k (y'' / (((frameGL (tgt_eq hs j') (g (G.m, ↑j' + 1))).val *ᵥ y') (.inr i) *
                  (((ϖ ^ (e * (i.val + 1)) : kˣ) : k))⁻¹)) ≤ 1 := by
                rw [map_div₀]
                exact div_le_one_of_le₀ hy'' zero_le
              have h2 : valuation k (y' r) ≤ 1 := hy r
              calc _ ≤ 1 * 1 * valuation k ((ϖ ^ e : kˣ) : k) := by gcongr
                _ = _ := by simp
            · simp [M, Matrix.mul_apply, hsi]
        · rw [Pi.single_eq_of_ne hjj]; simp
    rw [map_mul, map_inv₀, Units.val_one, map_one] at key
    have hpos : 0 < valuation k (((ϖ ^ (e * (i.val + 1)) : kˣ) : k)) := zero_lt_iff.mpr ((map_ne_zero _).mpr hd)
    have hfin := (mul_inv_le_iff₀ hpos).mp key
    rw [one_mul] at hfin
    exact hfin
end GlobalTheory.FunObj.OneCosetProof
