-- Prove2me | solution 1 for GlobalTheory.TensorExpansion.exists_sum_pureTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:58:07.046282+00:00
-- url     : https://prove2.me/submissions/dc524f1e-401f-4721-8e5d-143a1a7b8f54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumPureTensorOfIsTensorDepth
import Theorems.Thm_GlobalTheory_TensorExpansion_resMk_eq_iff
import Theorems.Thm_GlobalTheory_TensorExpansion_mem_matLat_pow_smul_iff
import Theorems.Thm_GlobalTheory_TensorExpansion_isNatDatum_resClass
import Theorems.Thm_GlobalTheory_SplitFlip_mem_matLat_stdLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.FunObj
noncomputable section
open GlobalTheory GlobalTheory.TensorExpansion
open GlobalTheory.SplitFlip ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.TensorExpansion
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : GlobalTheory.SplitFlip.Grid k) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (e : ℕ) (γ : List GlobalTheory.SplitFlip.Edge) (T : G.Args → ℂ), G.IsTensor ϖ e γ T → ∃ (n : ℕ) (x : Fin n → ℂ) (φ : Fin n → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ i, ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ i b)) ∧ ∀ z, T z = ∑ i, x i * G.lines₂ γ (φ i) z := by
  intro k _ _ _ _ G ϖ hϖ e γ T hT
  classical
  let L := γ.toFinset
  let I := ∀ b : L, Fin (G.rank b.1.tgt) → Fin (G.rank b.1.src) → Res k e
  let rep : I → G.Args := fun c b => if h : b ∈ L then liftRes (c ⟨b, h⟩) else 0
  let ψ : I → ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ :=
    fun c b => if h : b ∈ L then (resClass ϖ (c ⟨b, h⟩)).indicator 1 else 1
  have key : ∀ z, T z = ∑ c, T (rep c) * G.lines₂ γ (ψ c) z := by
    intro z
    simp only [Grid.lines₂]
    by_cases hint : ∀ b ∈ γ, z b ∈ matLat _ (stdLat k _)
    · let c0 : I := fun b i j => Ideal.Quotient.mk _
        ⟨z b.1 i j, mem_matLat_stdLat.1 (hint b.1 (List.mem_toFinset.1 b.2)) i j⟩
      have hmem : ∀ (c : I) (b : L), z b.1 ∈ resClass ϖ (c b) ↔ c b = c0 b := by
        intro c b
        have hz := mem_matLat_stdLat.1 (hint b.1 (List.mem_toFinset.1 b.2))
        constructor
        · intro h
          funext i j
          have := (resMk_eq_iff hϖ e ⟨z b.1 i j, hz i j⟩ (Quotient.out (c b i j))).2 (h i j).2
          rw [Ideal.Quotient.mk_out] at this
          exact this.symm
        · rintro h i j
          refine ⟨hz i j, ?_⟩
          exact (resMk_eq_iff hϖ e ⟨z b.1 i j, hz i j⟩ (Quotient.out (c b i j))).1
            (by rw [Ideal.Quotient.mk_out, h])
      rw [Finset.sum_eq_single c0]
      · have hprod : (γ.map fun b => ψ c0 b (z b)).prod = 1 := by
          refine List.prod_eq_one fun x hx => ?_
          obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
          have hb' : b ∈ L := List.mem_toFinset.2 hb
          simp only [ψ, dif_pos hb']
          exact Set.indicator_of_mem ((hmem c0 ⟨b, hb'⟩).2 rfl) _
        rw [hprod, mul_one]
        let w : G.Args := fun b => if b ∈ γ then z b - rep c0 b else 0
        have hw : ∀ b, w b ∈ matLat _ (ϖ ^ e • stdLat k _) := by
          intro b
          by_cases hb : b ∈ γ
          · have hb' : b ∈ L := List.mem_toFinset.2 hb
            have h2 := (hmem c0 ⟨b, hb'⟩).2 rfl
            refine (mem_matLat_pow_smul_iff ϖ e).2 fun i j => ?_
            simp only [w, if_pos hb, rep, dif_pos hb', Matrix.sub_apply]
            exact (h2 i j).2
          · simp only [w, if_neg hb]
            exact zero_mem _
        rw [← hT.2.2 (rep c0) w hw]
        refine hT.1 fun b hb => ?_
        have hb : b ∈ γ := hb
        simp [w, hb]
      · intro c _ hc
        obtain ⟨b, hb⟩ : ∃ b : L, c b ≠ c0 b := by
          by_contra hne
          push_neg at hne
          exact hc (funext hne)
        rw [List.prod_eq_zero (List.mem_map.2 ⟨b.1, List.mem_toFinset.1 b.2, ?_⟩), mul_zero]
        simp only [ψ, dif_pos b.2]
        exact Set.indicator_of_notMem (mt (hmem c b).1 hb) _
      · intro h
        exact absurd (Finset.mem_univ _) h
    · push_neg at hint
      obtain ⟨b, hb, hz⟩ := hint
      rw [hT.2.1 z b hb hz]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      rw [List.prod_eq_zero (List.mem_map.2 ⟨b, hb, ?_⟩), mul_zero]
      have hb' : b ∈ L := List.mem_toFinset.2 hb
      simp only [ψ, dif_pos hb']
      have hn : z b ∉ resClass ϖ (c ⟨b, hb'⟩) := fun h =>
        hz (mem_matLat_stdLat.2 fun i j => (h i j).1)
      exact Set.indicator_of_notMem hn _
  refine ⟨Fintype.card I, fun i => T (rep ((Fintype.equivFin I).symm i)),
    fun i => ψ ((Fintype.equivFin I).symm i), ?_, ?_⟩
  · intro i b hb
    have hb' : b ∈ L := List.mem_toFinset.2 hb
    simp only [ψ, dif_pos hb']
    exact isNatDatum_resClass hϖ e _
  · intro z
    rw [key z]
    exact (Equiv.sum_comp (Fintype.equivFin I).symm (fun c => T (rep c) * G.lines₂ γ (ψ c) z)).symm
end GlobalTheory.TensorExpansion
