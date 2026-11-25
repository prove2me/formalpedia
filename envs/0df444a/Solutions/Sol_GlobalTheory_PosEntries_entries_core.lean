-- Prove2me | solution 1 for GlobalTheory.PosEntries.entries_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:17.096971+00:00
-- url     : https://prove2.me/submissions/b856fb49-722b-477e-80da-ba9fbad95dbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeBlockDiagonalTargetEntryConditions
import Theorems.Thm_GlobalTheory_PosEntries_shape_inr
import Theorems.Thm_GlobalTheory_PosEntries_shape_inl
import Theorems.Thm_GlobalTheory_PosEntries_mulD_inr
import Theorems.Thm_GlobalTheory_PosEntries_mulD_inl
import Theorems.Thm_GlobalTheory_PosEntries_opE_translate_free
import Theorems.Thm_GlobalTheory_PosEntries_exists_affPt_ne_zero

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
open GlobalTheory GlobalTheory.PosEntries
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.PosEntries
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (hψ : HasConductor ψ 1)
    (ϖ : kˣ) (hϖ : valuation k (ϖ : k) < 1) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (c p : ℕ) (hp1 : 1 ≤ p) (A : GL (n ⊕ Fin c) k)
    (hA1 : A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (hA2 : A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)))
    (hB1 : (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (hB2 : (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)))
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (hInt : ∀ x, Ψ x ≠ 0 → IntM (A.val * x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val))
    (hMax : ∀ x z, MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) →
      Ψ (x + z) = Ψ x)
    (hE : opE ψ ν p Ψ ≠ 0) :
    (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧
      (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) ∧
    ∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] := by
  classical
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hE
  obtain ⟨e, he⟩ := exists_affPt_ne_zero ψ ν p hx₀
  have hI := hInt _ he
  have hx_diag : ∀ i : Fin c, affPt p x₀ e (Sum.inr i) (Sum.inr i.castSucc) = 1 := by
    intro i; simp [affPt, basePt, Free]
  have hx_X : ∀ (y : n) (q : Fin c), q.val + 1 = p → affPt p x₀ e (Sum.inl y) (Sum.inr q.castSucc) = 0 := by
    intro y q hq; subst hq; simp [affPt, basePt, Free]
  have hAB : ∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (A⁻¹).val (Sum.inr i) (Sum.inr i) = 1 := by
    intro i
    have h := congrFun (congrFun (Units.mul_inv A) (Sum.inr i)) (Sum.inr i)
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)] at h
    · simpa using h
    · intro s _ hs
      by_cases h0 : A.val (Sum.inr i) s = 0
      · simp [h0]
      · exact absurd (shape_inr hA1 hA2 i s h0) hs
    · simp
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · have h := hI (Sum.inr i) (Sum.inr i.castSucc)
    rw [mulD_inr, Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i), hx_diag] at h
    · simpa using h
    · intro s _ hs
      by_cases h0 : A.val (Sum.inr i) s = 0
      · simp [h0]
      · exact absurd (shape_inr hA1 hA2 i s h0) hs
    · simp
  · have hb0 : (A⁻¹).val (Sum.inr i) (Sum.inr i) ≠ 0 := right_ne_zero_of_mul_eq_one (hAB i)
    have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
    have key : ∀ y : k, valuation k y ≤ valuation k ((A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹) →
        ψ y = 1 := by
      intro y hy
      let ζ := y * ((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹
      let E : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
        Matrix.of fun u s => if u = Sum.inr i ∧ s = Sum.inr i.succ then ζ else 0
      let z := (A⁻¹).val * E
      have hAz : A.val * z = E := by simp only [z, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      have hzent : ∀ r s, z r s = if s = Sum.inr i.succ then (A⁻¹).val r (Sum.inr i) * ζ else 0 := by
        intro r s
        simp only [z, E, Matrix.mul_apply, Matrix.of_apply]
        split_ifs with hs
        · rw [Finset.sum_eq_single (Sum.inr i)] <;> simp_all
        · simp [hs]
      have hval : valuation k (ζ * (ϖ : k) ^ (i.val + 2)) < 1 := by
        have h1 : (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ *
            (((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹ * (ϖ : k) ^ (i.val + 2)) = ϖ := by
          field_simp; ring
        calc valuation k (ζ * (ϖ : k) ^ (i.val + 2))
            = valuation k y * valuation k (((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹ * (ϖ : k) ^ (i.val + 2)) := by
              rw [← map_mul, mul_assoc]
          _ ≤ valuation k ((A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹) *
              valuation k (((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹ * (ϖ : k) ^ (i.val + 2)) := by gcongr
          _ = valuation k (ϖ : k) := by rw [← map_mul, h1]
          _ < 1 := hϖ
      have hmax : MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) := by
        intro r s
        rw [hAz]
        rcases s with y' | l
        · rw [mulD_inl]; simp [E]
        · rw [mulD_inr]
          simp only [E, Matrix.of_apply]
          split_ifs with h
          · obtain ⟨rfl, hl⟩ := h
            obtain rfl : l = i.succ := Sum.inr_injective hl
            rw [show (i.succ : Fin (c + 1)).val + 1 = i.val + 2 by simp [Fin.val_succ]]
            exact hval
          · simp
      have hfree : ∀ r s, ¬ Free p (r, s) → z r s = 0 := by
        intro r s hns
        rw [hzent]
        split_ifs with hs
        · subst hs
          by_cases h0 : (A⁻¹).val r (Sum.inr i) = 0
          · simp [h0]
          · exfalso; apply hns
            rcases r with y' | j
            · have := shape_inl hp1 hB1 hB2 y' i h0
              simp [Free, Fin.val_succ]; omega
            · obtain ⟨⟩ := shape_inr hB1 hB2 j (Sum.inr i) h0
              simp [Free, Fin.val_succ]
        · rfl
      have htr := opE_translate_free ψ ν p hfree (fun x' => hMax x' z hmax) x₀
      have hch : ch z = y := by
        simp only [ch, hzent]
        rw [Finset.sum_eq_single i]
        · simp only [if_true, ζ]; field_simp
        · intro j _ hj; simp [Fin.succ_inj, hj]
        · simp
      have h1 : (ψ (-ch z) : ℂ) = 1 := by
        have : ((ψ (-ch z) : ℂ) - 1) * opE ψ ν p Ψ x₀ = 0 := by rw [sub_mul, ← htr]; ring
        rcases mul_eq_zero.mp this with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hx₀
      have h2 : ψ (-ch z) = 1 := Circle.ext (by simpa using h1)
      rw [AddChar.map_neg_eq_inv, inv_eq_one, hch] at h2
      exact h2
    have hle := (hψ _).mp key
    simp only [Units.val_one, map_one] at hle
    exact hle
  · intro q hq y
    have h := hI (Sum.inl y) (Sum.inr q.castSucc)
    rw [mulD_inr, Matrix.mul_apply, Finset.sum_eq_single (Sum.inr q)] at h
    · rw [hx_diag] at h; simpa using h
    · intro s _ hs
      rcases s with z | j
      · simp [hx_X z q hq]
      · by_cases h0 : A.val (Sum.inl y) (Sum.inr j) = 0
        · simp [h0]
        · have := shape_inl hp1 hA1 hA2 y j h0
          exact absurd (by congr 1; exact Fin.ext (by omega)) hs
    · simp
end GlobalTheory.PosEntries
