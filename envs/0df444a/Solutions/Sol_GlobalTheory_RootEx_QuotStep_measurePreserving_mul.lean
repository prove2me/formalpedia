-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.measurePreserving_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:28.567802+00:00
-- url     : https://prove2.me/submissions/e8f8606d-3232-4291-a91f-ab3fe4dbf430

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_ext_pos
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_chart_val
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_continuous_ext
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_SgLoc_TriShift_measurePreserving_triangular
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotStep
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
variable {b : ι → ℕ} {S : ι × ι → Prop}
variable (hS : ∀ rs, S rs → b rs.1 < b rs.2)
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.RootEx.QuotStep
theorem _root_.solution {n : Type} [Fintype n] [Fintype {rs // S rs}]
    [Fintype {rs : ι × ι // b rs.1 < b rs.2}] (j : n → ι × ι) (hj : Function.Injective j)
    (hjS : ∀ x, ¬ S (j x)) (hjb : ∀ x, b (j x).1 < b (j x).2)
    (hcov : ∀ rs, b rs.1 < b rs.2 → S rs ∨ ∃ x, j x = rs)
    (E : (n → k) → GL ι k) (hE : ∀ β x, (E β).val (j x).1 (j x).2 = β x)
    (hE' : ∀ β r s, (∀ x, j x ≠ (r, s)) → (E β).val r s = (1 : Matrix ι ι k) r s) :
    MeasurePreserving (fun (y : (n → k) × ({rs // S rs} → k)) (i : {rs : ι × ι // b rs.1 < b rs.2}) =>
        (chart hS y.2 * E y.1).val i.1.1 i.1.2)
      ((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) (Measure.pi fun _ => ν) := by
  classical
  haveI := secondCountable k
  haveI := t2Space k
  let S' : ι × ι → Prop := fun rs => b rs.1 < b rs.2
  let σ : n ⊕ {rs // S rs} ≃ {rs // S' rs} := Equiv.ofBijective
    (Sum.elim (fun x => ⟨j x, hjb x⟩) fun i => ⟨i.1, hS _ i.2⟩) (by
      constructor
      · rintro (x | x) (y | y) h <;> simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
        · rw [hj h]
        · exact absurd (h ▸ y.2) (hjS x)
        · exact absurd (h ▸ x.2) (hjS y)
        · rw [Subtype.ext h]
      · rintro ⟨rs, h⟩
        rcases hcov rs h with h' | ⟨x, rfl⟩
        · exact ⟨Sum.inr ⟨rs, h'⟩, rfl⟩
        · exact ⟨Sum.inl x, rfl⟩)
  have hT := GlobalTheory.SgLoc.TriShift.measurePreserving_triangular ν (fun i : {rs // S' rs} => b i.1.2 - b i.1.1)
    (fun i e => ∑ t, (if S (i.1.1, t) then ext S' e i.1.1 t else 0) *
      (if S (t, i.1.2) then 0 else ext S' e t i.1.2))
    (fun i => (continuous_finset_sum _ fun t _ => by
      refine Continuous.mul ?_ ?_ <;> split_ifs <;>
        first | exact continuous_const | exact continuous_ext S' _ _).measurable)
    (fun i x y hxy => by
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h1 : S' (i.1.1, t)
      · by_cases h2 : S' (t, i.1.2)
        · have h1' : b i.1.1 < b t := h1
          have h2' : b t < b i.1.2 := h2
          rw [ext_pos _ h1, ext_pos _ h1, ext_pos _ h2, ext_pos _ h2,
            hxy ⟨_, h1⟩ (by dsimp only; omega), hxy ⟨_, h2⟩ (by dsimp only; omega)]
        · simp [ext_neg _ h2]
      · simp [ext_neg _ h1])
  have hJ := (measurePreserving_piCongrLeft (fun _ : {rs // S' rs} => ν) σ).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : n ⊕ {rs // S rs} => ν))
  convert hT.comp hJ using 1
  funext ⟨β, e⟩ i
  set ε := (MeasurableEquiv.piCongrLeft (fun _ : {rs // S' rs} => k) σ
    ((MeasurableEquiv.sumPiEquivProdPi fun _ : n ⊕ {rs // S rs} => k).symm (β, e))) with hε
  have h1 : ∀ x, ε (σ (Sum.inl x)) = β x := fun x => by
    rw [hε, MeasurableEquiv.piCongrLeft_apply_apply]; rfl
  have h2 : ∀ x, ε (σ (Sum.inr x)) = e x := fun x => by
    rw [hε, MeasurableEquiv.piCongrLeft_apply_apply]; rfl
  have hA : ∀ r s, (if S (r, s) then ext S' ε r s else 0) = ext S e r s := fun r s => by
    split_ifs with h
    · rw [ext_pos _ h, ext_pos (S := S') _ (hS _ h)]; exact h2 ⟨_, h⟩
    · rw [ext_neg _ h]
  have hB : ∀ r s, (if S (r, s) then 0 else ext S' ε r s) = ((E β).val - 1) r s := fun r s => by
    by_cases hx : ∃ x, j x = (r, s)
    · obtain ⟨x, hx⟩ := hx
      obtain rfl : (j x).1 = r := congrArg Prod.fst hx
      obtain rfl : (j x).2 = s := congrArg Prod.snd hx
      have hne : (j x).1 ≠ (j x).2 := fun h => absurd (hjb x) (by rw [h]; exact lt_irrefl _)
      rw [if_neg (hjS x), ext_pos (S := S') _ (hjb x), Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero, hE]
      exact h1 x
    · rw [Matrix.sub_apply, hE' β r s fun x h => hx ⟨x, h⟩, sub_self]
      split_ifs with h
      · rfl
      · exact ext_neg _ fun h' => (hcov _ h').elim h hx
  have hne : i.1.1 ≠ i.1.2 := fun h => absurd i.2 (by rw [h]; exact lt_irrefl _)
  have : (chart hS e * E β).val = 1 + ((ext S e + ((E β).val - 1)) + ext S e * ((E β).val - 1)) := by
    rw [Units.val_mul, chart_val]; noncomm_ring
  change _ = ε i + ∑ t, (if S (i.1.1, t) then ext S' ε i.1.1 t else 0) *
      (if S (t, i.1.2) then 0 else ext S' ε t i.1.2)
  simp only [hA, hB]
  rw [this, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.add_apply, Matrix.add_apply, ← hA, ← hB,
    ext_pos (S := S') ε i.2]
  congr 1
  split_ifs <;> simp
end GlobalTheory.RootEx.QuotStep
