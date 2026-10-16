-- Prove2me | solution 1 for OAI.PartialPermutation.TableauZeta.deficitTerm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:41:57.21617+00:00
-- url     : https://prove2.me/submissions/9717ae2d-a9d4-45d7-a0cd-74d981b849de

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/TableauWeights.lean:L71-L89
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.TableauZeta.deficitTerm_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Equivalences
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SymmetricTransfer
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_StandardTableaux
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RankFillings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagonalBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_FillingExtensions
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Interleavings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RowBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Truncation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TailBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagramCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DeficitCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TableauWeights
import Theorems.Thm_OAI_PartialPermutation_Tableau_binomial_lower_bound

-- ---- from OAI.RepresentationTheory.PartialPermutation.StandardTableaux ----
namespace OAI

section
namespace PartialPermutation
namespace Tableau

noncomputable section
open Finset

lemma standardCount_pos (μ : YoungDiagram) : 0 < standardCount μ := by
  let : Nonempty (StandardFilling μ.cells) := ⟨chosenFilling _⟩
  exact Fintype.card_pos

end
end Tableau
end PartialPermutation
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.RankFillings ----
namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

lemma exists_rankEnumeration (α ι : Type*) [Fintype α] [LinearOrder ι]
    (r : α → ι) :
    ∃ e : α ≃ Fin (Fintype.card α), ∀ a b, r a < r b → e a < e b := by
  classical
  let e₀ := Fintype.equivFin α
  let key : α → ι ×ₗ Fin (Fintype.card α) := fun a => toLex (r a, e₀ a)
  have hk : Function.Injective key := by
    intro a b h
    exact e₀.injective (congrArg (fun z : ι ×ₗ Fin (Fintype.card α) => (ofLex z).2) h)
  let : LinearOrder α := LinearOrder.lift' key hk
  let e := (Fintype.orderIsoFinOfCardEq α rfl).symm
  refine ⟨e.toEquiv, ?_⟩
  intro a b h
  apply e.strictMono
  exact Prod.Lex.left _ _ h

lemma fiberPermutation_rank {α ι : Type*} (r : α → ι)
    (p : ∀ i, Equiv.Perm {a // r a = i}) (a : α) :
    r (fiberPermutation r p a) = r a := (p (r a) ⟨a,rfl⟩).2

lemma fiberPermutation_injective {α ι : Type*} (r : α → ι) :
    Function.Injective (fiberPermutation r) := by
  intro p q h
  funext i
  apply Equiv.ext
  rintro ⟨a,ha⟩
  subst i
  apply Subtype.ext
  exact Equiv.congr_fun h a

lemma rank_factorial_le_filling_count (α ι : Type*) [Fintype α] [PartialOrder α]
    [Fintype ι] [LinearOrder ι] (r : α → ι) (hr : StrictMono r) :
    (∏ i, (Fintype.card {a // r a = i}).factorial) ≤
      Fintype.card (StandardFilling α) := by
  classical
  obtain ⟨e,he⟩ := exists_rankEnumeration α ι r
  let f : (∀ i, Equiv.Perm {a // r a = i}) → StandardFilling α := fun p =>
    ⟨(fiberPermutation r p).trans e, fun a b hab => he _ _ (by
      simpa only [fiberPermutation_rank] using hr hab)⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply fiberPermutation_injective r
    apply Equiv.ext
    intro a
    apply e.injective
    exact congrArg (fun t : StandardFilling α => t.1 a) hpq
  simpa only [Fintype.card_pi, Fintype.card_perm] using Fintype.card_le_of_injective f hf

lemma two_pow_pred_le_factorial (n : ℕ) : 2^(n-1) ≤ n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases n with _ | n
    · simp
    · rw [Nat.factorial_succ]
      simp only [Nat.add_sub_cancel] at ih ⊢
      calc
        2^(n+1) = 2 * 2^n := by rw [pow_succ]; omega
        _ ≤ (n+2) * (n+1).factorial := Nat.mul_le_mul (by omega) ih

lemma power_count_sub_ranks_le_factorials (ι : Type*) [Fintype ι] (a : ι → ℕ) :
    2^((∑ i, a i)-Fintype.card ι) ≤ ∏ i, (a i).factorial := by
  classical
  have h : ∑ i, a i ≤ (∑ i, (a i-1)) + Fintype.card ι := by
    calc
      _ ≤ ∑ i, (a i-1+1) := Finset.sum_le_sum (fun i _ => by omega)
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  calc
    _ ≤ 2^(∑ i, (a i-1)) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = ∏ i, 2^(a i-1) := by rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ _ := Finset.prod_le_prod' (fun index _ => two_pow_pred_le_factorial (a index))

lemma rank_power_le_filling_count (α ι : Type*) [Fintype α] [PartialOrder α]
    [Fintype ι] [LinearOrder ι] (r : α → ι) (hr : StrictMono r) :
    2^(Fintype.card α - Fintype.card ι) ≤ Fintype.card (StandardFilling α) := by
  have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv r)
  rw [Fintype.card_sigma] at hh
  rw [← hh]
  exact (power_count_sub_ranks_le_factorials ι (fun i => Fintype.card {a // r a=i})).trans
    (rank_factorial_le_filling_count α ι r hr)

end
end Tableau
end PartialPermutation
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.DiagonalBounds ----
namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

lemma diagonalRank_strictMono (μ : YoungDiagram) : StrictMono (diagonalRank μ) := by
  intro x y hxy
  have h1 : x.1.1 ≤ y.1.1 := hxy.le.1
  have h2 : x.1.2 ≤ y.1.2 := hxy.le.2
  have hn : x.1 ≠ y.1 := fun h => (ne_of_lt hxy) (Subtype.ext h)
  change x.1.1+x.1.2 < y.1.1+y.1.2
  by_contra h
  apply hn
  exact Prod.ext (by omega) (by omega)

lemma diagonal_power_lower_bound (μ : YoungDiagram) :
    2^(μ.cells.card - (diagonalIndices μ).card) ≤ standardCount μ := by
  simpa only [Fintype.card_coe, standardCount] using
    rank_power_le_filling_count _ _ (diagonalRank μ) (diagonalRank_strictMono μ)

lemma diagonal_count_le (μ : YoungDiagram) : (diagonalIndices μ).card ≤ 2*maxLine μ-1 := by
  apply (Finset.card_le_card (t := Finset.range (2*maxLine μ-1)) ?_).trans_eq (Finset.card_range _)
  intro k hk
  obtain ⟨⟨i,j⟩,hij,rfl⟩ := Finset.mem_image.mp hk
  have hj : j < maxLine μ := (μ.mem_iff_lt_rowLen.mp hij).trans_le
    ((μ.rowLen_anti 0 i (Nat.zero_le _)).trans (le_max_left _ _))
  have hi : i < maxLine μ := (μ.mem_iff_lt_colLen.mp hij).trans_le
    ((μ.colLen_anti 0 j (Nat.zero_le _)).trans (le_max_right _ _))
  simp only [Finset.mem_range]
  omega

lemma width_height_power_lower_bound (μ : YoungDiagram) :
    2^(μ.cells.card - (2*maxLine μ-1)) ≤ standardCount μ :=
  (Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_left (diagonal_count_le μ) _)).trans
    (diagonal_power_lower_bound μ)

end
end Tableau
end PartialPermutation
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.RowBounds ----
namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

lemma topRow_le_card (μ : YoungDiagram) : μ.rowLen 0 ≤ μ.cells.card := by
  have h := Fintype.card_le_of_injective (topRowEquiv μ).symm
    (topRowEquiv μ).symm.injective
  have h' := Fintype.card_subtype_le (fun x : μ.cells => x.1.1=0)
  simpa only [Fintype.card_fin, Fintype.card_coe] using h.trans h'

end
end Tableau
end PartialPermutation
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.TailBounds ----
namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

lemma standardCount_transpose (μ : YoungDiagram) : standardCount μ.transpose = standardCount μ :=
  (Fintype.card_congr (fillingCongr (transposeCellsEquiv μ))).symm

lemma card_transpose (μ : YoungDiagram) : μ.transpose.cells.card = μ.cells.card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (transposeCellsEquiv μ).toEquiv).symm

lemma maxLine_transpose (μ : YoungDiagram) : maxLine μ.transpose = maxLine μ := by
  simp only [maxLine, YoungDiagram.rowLen_transpose, YoungDiagram.colLen_transpose, max_comm]

lemma deficit_transpose (μ : YoungDiagram) : deficit μ.transpose = deficit μ := by
  simp only [deficit, card_transpose, maxLine_transpose]

lemma two_pow_le_centralBinom (b : ℕ) : 2^b ≤ (2*b).choose b := by
  change 2^b ≤ Nat.centralBinom b
  induction b with
  | zero => simp
  | succ b ih =>
    have he := Nat.succ_mul_centralBinom_succ b
    have hstep : 2 * Nat.centralBinom b ≤ Nat.centralBinom (b+1) := by
      by_contra h
      have hh := Nat.mul_lt_mul_of_pos_left (show Nat.centralBinom (b+1) < 2*Nat.centralBinom b by omega)
        (Nat.succ_pos b)
      nlinarith
    calc
      2^(b+1) = 2 * 2^b := by rw [pow_succ']
      _ ≤ 2 * Nat.centralBinom b := Nat.mul_le_mul_left _ ih
      _ ≤ _ := hstep

lemma tail_power_lower_bound_oriented (μ : YoungDiagram)
    (hor : μ.colLen 0 ≤ μ.rowLen 0) : 2^(deficit μ/8) ≤ standardCount μ := by
  have hL : maxLine μ = μ.rowLen 0 := max_eq_left hor
  by_cases hsmall : 4*maxLine μ ≤ μ.cells.card
  · apply le_trans (Nat.pow_le_pow_right (by omega) (show deficit μ/8 ≤
        μ.cells.card-(2*maxLine μ-1) by unfold deficit; omega))
      (width_height_power_lower_bound μ)
  · let b := min (deficit μ) (μ.rowLen 0/2)
    have hb₁ : b ≤ deficit μ := min_le_left _ _
    have hb₂ : b ≤ μ.rowLen 0/2 := min_le_right _ _
    have hba : b ≤ min (μ.rowLen 0) (μ.cells.card-μ.rowLen 0) := by
      rw [deficit,hL] at hb₁
      exact le_min (by omega) hb₁
    have hkb : deficit μ/8 ≤ b := by
      have hc := topRow_le_card μ
      dsimp [b]
      apply le_min
      · exact Nat.div_le_self _ _
      · rw [hL] at hsmall
        unfold deficit
        rw [hL]
        omega
    calc
      2^(deficit μ/8) ≤ 2^b := Nat.pow_le_pow_right (by omega) hkb
      _ ≤ (2*b).choose b := two_pow_le_centralBinom b
      _ ≤ (μ.rowLen 0).choose b := Nat.choose_le_choose b (by omega)
      _ ≤ standardCount μ := binomial_lower_bound μ b hba

lemma tail_power_lower_bound (μ : YoungDiagram) : 2^(deficit μ/8) ≤ standardCount μ := by
  by_cases h : μ.colLen 0 ≤ μ.rowLen 0
  · exact tail_power_lower_bound_oriented μ h
  · have hh := tail_power_lower_bound_oriented μ.transpose (by
      simpa only [YoungDiagram.rowLen_transpose, YoungDiagram.colLen_transpose] using le_of_not_ge h)
    simpa only [deficit_transpose, standardCount_transpose] using hh

end
end Tableau
end PartialPermutation

end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.DeficitCounts ----
namespace OAI

section
namespace PartialPermutation
namespace DiagramCounting
noncomputable section
open Finset

lemma eq_of_dropTop_row (μ ν : YoungDiagram) (hd : dropTop μ=dropTop ν)
    (hr : μ.rowLen 0=ν.rowLen 0) : μ=ν := by
  apply YoungDiagram.ext
  apply Finset.ext
  rintro ⟨i,j⟩
  cases i with
  | zero => exact μ.mem_iff_lt_rowLen.trans (hr ▸ ν.mem_iff_lt_rowLen.symm)
  | succ i =>
    change (i+1,j) ∈ μ ↔ (i+1,j) ∈ ν
    rw [← mem_dropTop μ, ← mem_dropTop ν,hd]

lemma deficitCode_injective (n k : ℕ) : Function.Injective (deficitCode n k) := by
  intro μ ν he
  unfold deficitCode at he
  split_ifs at he with hμ hν hν
  · have hd : dropTop μ.1.1=dropTop ν.1.1 := congrArg (fun t : Bool × Shape k => t.2.1) he
    have hcμ := μ.2
    have hcν := ν.2
    rw [μ.1.2,max_eq_left hμ] at hcμ
    rw [ν.1.2,max_eq_left hν] at hcν
    have hleμ := rowLen_le_card μ.1.1 0
    have hleν := rowLen_le_card ν.1.1 0
    rw [μ.1.2] at hleμ
    rw [ν.1.2] at hleν
    apply Subtype.ext; apply Subtype.ext
    exact eq_of_dropTop_row _ _ hd (by omega)
  · have hh := congrArg Prod.fst he; cases hh
  · have hh := congrArg Prod.fst he; cases hh
  · have hd : dropTop μ.1.1.transpose=dropTop ν.1.1.transpose :=
      congrArg (fun t : Bool × Shape k => t.2.1) he
    have hcμ := μ.2
    have hcν := ν.2
    rw [μ.1.2,max_eq_right (le_of_not_ge hμ)] at hcμ
    rw [ν.1.2,max_eq_right (le_of_not_ge hν)] at hcν
    have hleμ := colLen_le_card μ.1.1 0
    have hleν := colLen_le_card ν.1.1 0
    rw [μ.1.2] at hleμ
    rw [ν.1.2] at hleν
    have htr := eq_of_dropTop_row _ _ hd (by
      simp only [YoungDiagram.rowLen_transpose]; omega)
    apply Subtype.ext; apply Subtype.ext
    have hh := congrArg YoungDiagram.transpose htr
    simpa only [YoungDiagram.transpose_transpose] using hh

lemma deficit_count_le (n k : ℕ) : Fintype.card (ShapeDeficit n k) ≤ 2*partitionCount k := by
  simpa only [Fintype.card_prod,Fintype.card_bool,partitionCount] using
    Fintype.card_le_of_injective (deficitCode n k) (deficitCode_injective n k)

end
end DiagramCounting
end PartialPermutation
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.TableauWeights ----
namespace OAI

section
namespace PartialPermutation
namespace TableauZeta
noncomputable section
open Finset Filter
open Tableau DiagramCounting

lemma inverse_tableau_bound (μ : YoungDiagram) (u : ℝ) (hu : 0 < u) :
    (standardCount μ : ℝ)^(-u) ≤
      Real.exp (u*Real.log 2 - (u*Real.log 2/8)*(deficit μ : ℝ)) := by
  have hc : (0:ℝ)<standardCount μ := by exact_mod_cast standardCount_pos μ
  have hb : (2:ℝ)^(deficit μ/8) ≤ standardCount μ := by
    exact_mod_cast tail_power_lower_bound μ
  have hh := Real.rpow_le_rpow_of_nonpos (show (0:ℝ)<2^(deficit μ/8) by positivity)
    hb (neg_nonpos.mpr hu.le)
  apply hh.trans
  rw [Real.rpow_def_of_pos (by positivity),Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hk : (deficit μ : ℝ) < 8*(deficit μ/8 : ℕ)+8 := by
    exact_mod_cast (show deficit μ < 8*(deficit μ/8)+8 by omega)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hk.le (show 0 ≤ u*Real.log 2/8 by positivity)
  nlinarith

lemma inverseWeight_nonneg (u : ℝ) (μ : YoungDiagram) : 0 ≤ inverseWeight u μ := by
  unfold inverseWeight
  split_ifs <;> positivity

lemma deficitTerm_nonneg (n : ℕ) (u : ℝ) (k : ℕ) : 0 ≤ deficitTerm n u k :=
  Finset.sum_nonneg (fun μ _ => inverseWeight_nonneg u μ.1.1)

lemma deficitTerm_bound (n : ℕ) (u : ℝ) (hu : 0 < u) (k : ℕ) :
    ‖deficitTerm n u k‖ ≤ majorant u k := by
  rw [Real.norm_eq_abs,abs_of_nonneg (deficitTerm_nonneg n u k)]
  have hcard : (Fintype.card (ShapeDeficit n k):ℝ) ≤ 2*partitionCount k := by
    exact_mod_cast deficit_count_le n k
  calc
    deficitTerm n u k ≤ ∑ μ : ShapeDeficit n k,
        Real.exp (u*Real.log 2 - (u*Real.log 2/8)*k) := by
      apply Finset.sum_le_sum
      intro μ _
      unfold inverseWeight
      split_ifs
      · exact Real.exp_nonneg _
      · have hh := inverse_tableau_bound μ.1.1 u hu
        have he : deficit μ.1.1=k := μ.2
        simpa only [he] using hh
    _ = (Fintype.card (ShapeDeficit n k):ℝ)*
        Real.exp (u*Real.log 2 - (u*Real.log 2/8)*k) := by simp
    _ ≤ majorant u k := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)

end
end TableauZeta
end PartialPermutation
end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation OAI.PartialPermutation.TableauZeta
open Finset Filter
open Tableau DiagramCounting


theorem solution : type_of% @_root_.OAI.PartialPermutation.TableauZeta.deficitTerm_bound := @_root_.OAI.PartialPermutation.TableauZeta.deficitTerm_bound
