-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.finite_masked_dissipation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:48:53.879925+00:00
-- url     : https://prove2.me/submissions/1bf0b804-205b-4ab6-bd6a-6902127375b2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MaskedDissipation.lean:L87-L113
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.finite_masked_dissipation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Theorems.Thm_OAI_TriangularHilbert_Heat_finite_mesh_energy_jump_le
import Theorems.Thm_OAI_TriangularHilbert_Heat_integrated_strict_dissipation
import Theorems.Thm_OAI_TriangularHilbert_Heat_mesh_mass_le
import Theorems.Thm_OAI_TriangularHilbert_Heat_sum_jumpMax_le
import Theorems.Thm_OAI_TriangularHilbert_Heat_totalPlaneEnergy_le_mass
import Theorems.Thm_OAI_TriangularHilbert_intInterval_sum_fin

-- ---- from OAI.Analysis.TriangularHilbert.MatrixSupport ----
namespace OAI

universe uι uκ uX uμ

section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

variable [DecidableEq ι]

theorem traceReal_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    traceReal (conjStarAlgAut ℂ _ U X) = traceReal X := by
  unfold traceReal
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem energy_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    energy (conjStarAlgAut ℂ _ U P) = energy P := by
  have hs : CFC.sqrt (conjStarAlgAut ℂ _ U P) =
      conjStarAlgAut ℂ _ U (CFC.sqrt P) := by
    apply CFC.sqrt_unique
    · rw [← map_mul, CFC.sqrt_mul_sqrt_self P hP.nonneg]
    · simpa only [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
        ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).mul_mul_conjTranspose_same
          (U : Matrix ι ι ℂ)).nonneg
  simp only [energy, hs, ← map_mul, traceReal_unitary_conj]

theorem sqrt_diagonal_nonneg (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    CFC.sqrt (Matrix.diagonal (fun i => (q i : ℂ))) =
      Matrix.diagonal (fun i => ((Real.sqrt (q i) : ℝ) : ℂ)) := by
  apply CFC.sqrt_unique
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact_mod_cast (Real.mul_self_sqrt (hq i))
  · exact (Matrix.PosSemidef.diagonal (fun i =>
      RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _))).nonneg

theorem energy_diagonal (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    energy (Matrix.diagonal (fun i => (q i : ℂ))) = ∑ i, q i * Real.sqrt (q i) := by
  simp [energy, sqrt_diagonal_nonneg q hq, Matrix.diagonal_mul_diagonal, traceReal]

theorem energy_spectral {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    energy P = ∑ i, hP.isHermitian.eigenvalues i * Real.sqrt (hP.isHermitian.eigenvalues i) := by
  rw [← energy_unitary_conj (star hP.isHermitian.eigenvectorUnitary) hP,
    hP.isHermitian.conjStarAlgAut_star_eigenvectorUnitary]
  exact energy_diagonal _ hP.eigenvalues_nonneg

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

variable [DecidableEq κ]

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianGram ----
namespace OAI

universe uι

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weight_pos {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ) (u p : ℝ) :
    0 < weight h u p σ := mul_pos hh (density_pos hσ _)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.NormBounds ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma energy_gram_nonneg (R : Matrix ι ι ℂ) : 0 ≤ energy (Rᴴ * R) := by
  rw [energy_spectral (Matrix.posSemidef_conjTranspose_mul_self R)]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg ((Matrix.posSemidef_conjTranspose_mul_self R).eigenvalues_nonneg i)
    (Real.sqrt_nonneg _)

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.InitialPlane ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma totalPlaneEnergy_nonneg (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (σ : Three → ℝ) : 0 ≤ totalPlaneEnergy A h u d σ := by
  apply Finset.sum_nonneg
  intro v _
  exact integral_nonneg (fun _ => energy_gram_nonneg _)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.IntWeak ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma mem_intInterval (m n : ℤ) (r : ℕ) :
    m ∈ intInterval n r ↔ n-(r:ℤ) ≤ m ∧ m ≤ n+r := Finset.mem_Icc

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.IntMax ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma mem_intInterval_iff_dist (m n : ℤ) (r : ℕ) :
    m ∈ intInterval n r ↔ (m-n).natAbs ≤ r := by
  rw [mem_intInterval]
  have he : (m-n).natAbs ≤ r ↔ |m-n| ≤ (r:ℤ) := by
    rw [← Int.natCast_natAbs]
    omega
  rw [he,abs_le]
  constructor <;> intro h <;> constructor <;> omega

lemma intAverage_nonneg (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m) (n : ℤ) (r : ℕ) :
    0 ≤ intAverage D f n r := by
  exact div_nonneg (Finset.sum_nonneg (fun m hm => hf m (Finset.mem_inter.mp hm).1)) (by positivity)

lemma inter_intInterval_of_supportRadius_le (D : Finset ℤ) (n : ℤ) {r : ℕ}
    (hr : supportRadius D n ≤ r) : D ∩ intInterval n r = D := by
  apply Finset.inter_eq_left.mpr
  intro m hm
  rw [mem_intInterval_iff_dist]
  exact (Finset.le_sup hm).trans hr

lemma intAverage_le_intMax (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (n : ℤ) (r : ℕ) : intAverage D f n r ≤ intMax D f n := by
  by_cases hr : r ≤ supportRadius D n
  · exact Finset.le_sup' _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  · have hb : supportRadius D n ≤ r := le_of_lt (lt_of_not_ge hr)
    have hm : intAverage D f n r ≤ intAverage D f n (supportRadius D n) := by
      unfold intAverage
      rw [inter_intInterval_of_supportRadius_le D n hb,
        inter_intInterval_of_supportRadius_le D n le_rfl]
      apply div_le_div_of_nonneg_left (Finset.sum_nonneg hf) (by positivity)
      exact_mod_cast (by omega : 2*supportRadius D n+1 ≤ 2*r+1)
    exact hm.trans (Finset.le_sup' _ (Finset.mem_range.mpr (Nat.lt_succ_self _)))

lemma intMax_nonneg (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m) (n : ℤ) :
    0 ≤ intMax D f n := (intAverage_nonneg D f hf n 0).trans (intAverage_le_intMax D f hf n 0)

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.FiniteLineMax ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uκ

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma lineMax_nonneg (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m) (n : ℤ) :
    0 ≤ lineMax D f n := by
  exact intMax_nonneg D (lineExtend D f) (fun m hm => by simpa only [lineExtend,dite_eq_left hm] using hf ⟨m,hm⟩) n

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MeshJump ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators
noncomputable section

lemma jumpMax_nonneg (D : Finset ℤ) (A : Three → Matrix D D ℂ) (i j : D) :
    0 ≤ jumpMax D A i j := by
  unfold jumpMax
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (by norm_num) (lineMax_nonneg _ _ (fun _ => sq_nonneg _) _))
    (mul_nonneg (by norm_num) (lineMax_nonneg _ _ (fun _ => sq_nonneg _) _)))
    (lineMax_nonneg _ _ (fun _ => sq_nonneg _) _)) (lineMax_nonneg _ _ (fun _ => sq_nonneg _) _)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MeshFinite ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators
noncomputable section

lemma finite_mesh_mass_le (D : Finset ℤ) {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (p : ℝ) :
    (∑ i : D, weight h (h*(i:ℤ)) p σ) ≤ meshMassConstant := by
  let N := supportRadius D 0
  have hD : D ⊆ intInterval 0 N := by
    intro m hm
    rw [mem_intInterval_iff_dist]
    exact Finset.le_sup (f := fun k : ℤ => (k-0).natAbs) hm
  rw [Finset.sum_coe_sort D (fun i : ℤ => weight h (h*(i:ℝ)) p σ)]
  have hi : (∑ i ∈ D, weight h (h*(i:ℝ)) p σ) ≤ ∑ i ∈ intInterval 0 N, weight h (h*(i:ℝ)) p σ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hD
    intro i _ _
    exact (weight_pos hh ((sq_pos_of_pos hh).trans_le hσ) _ _).le
  apply hi.trans
  rw [intInterval_sum_fin]
  have he (i : Fin (2*N+1)) : weight h (h*((0-(N:ℤ)+(i:ℕ):ℤ):ℝ)) p σ =
      h*density σ ((-(h*N)-p)+h*i) := by
    unfold weight
    congr 2
    push_cast
    ring
  simp_rw [he]
  exact mesh_mass_le hh hσ (-(h*N)-p) (2*N+1)

lemma finite_mesh_totalPlaneEnergy_le (D : Finset ℤ) (A : Three → Matrix D D ℂ)
    {h : ℝ} (hh : 0 < h) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ v, h^2 ≤ σ v) :
    totalPlaneEnergy A h (fun i => h*(i:ℤ)) d σ ≤
      2*Real.sqrt 2*meshMassConstant*arrayCubic A h := by
  exact totalPlaneEnergy_le_mass A hh _ d (fun v => (sq_pos_of_pos hh).trans_le (hσ v)) meshMassConstant_pos.le
    (fun p v => finite_mesh_mass_le D hh (hσ v) (p v))
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.Switch ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma telescope_with_jumps (E : ℕ → ℕ → ℝ) (n : ℕ) (hn : 0 ≤ E n n) :
    (∑ k ∈ Finset.range n, (E k k-E k (k+1))) ≤ E 0 0+
      ∑ k ∈ Finset.range n, |E (k+1) (k+1)-E k (k+1)| := by
  have he : (∑ k ∈ Finset.range n, (E k k-E k (k+1))) = E 0 0-E n n+
      ∑ k ∈ Finset.range n, (E (k+1) (k+1)-E k (k+1)) := by
    clear hn
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,Finset.sum_range_succ,ih]; ring
  rw [he]
  have hi := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) =>
    le_abs_self (E (k+1) (k+1)-E k (k+1)))
  linarith

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MaskedDissipation ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

lemma arrayCubic_eq (D : Finset ℤ) (A : Three → Matrix D D ℂ) (h : ℝ) :
    arrayCubic A h = h^2*(∑ v, ∑ i, ∑ j, ‖A v i j‖^3) := by
  simp only [arrayCubic,Finset.mul_sum]

lemma arrayCubic_mono {ι : Type uι} [Fintype ι] (A B : Three → Matrix ι ι ℂ)
    (hAB : ∀ v i j, ‖A v i j‖ ≤ ‖B v i j‖) (h : ℝ) : arrayCubic A h ≤ arrayCubic B h := by
  unfold arrayCubic
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  gcongr
  exact hAB v i j

lemma arrayCubic_replaceZero_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) (B : Matrix D D ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (h : ℝ) : arrayCubic (replaceZero A B) h ≤ arrayCubic A h := by
  apply arrayCubic_mono
  intro v i j
  by_cases hv : v=0
  · subst v; exact hB i j
  · simp [replaceZero,hv]

lemma finite_mesh_total_jumps_le (D : Finset ℤ) (A : Three → Matrix D D ℂ)
    (B : ℕ → Matrix D D ℂ) (hB : ∀ k i j, ‖B k i j‖ ≤ ‖A 0 i j‖) (n : ℕ)
    (hvar : ∀ i j, (∑ k ∈ Finset.range n, ‖B (k+1) i j-B k i j‖) ≤ 2*‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) (σ : ℕ → Three → ℝ) (hσ : ∀ k v, h^2 ≤ σ k v) :
    (∑ k ∈ Finset.range n,
      |totalPlaneEnergy (replaceZero A (B (k+1))) h (fun m => h*(m:ℤ)) 0 (σ k)-
        totalPlaneEnergy (replaceZero A (B k)) h (fun m => h*(m:ℤ)) 0 (σ k)|) ≤
      3*meshMassConstant*jumpScalarConstant*arrayCubic A h := by
  have hj := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) =>
    finite_mesh_energy_jump_le D A (B (k+1)) (B k) (hB (k+1)) (hB k) hh (hσ k))
  apply hj.trans
  rw [← Finset.mul_sum]
  have he : (∑ k ∈ Finset.range n, ∑ i : D, ∑ j : D, ‖B (k+1) i j-B k i j‖*jumpMax D A i j) =
      ∑ i : D, ∑ j : D, (∑ k ∈ Finset.range n, ‖B (k+1) i j-B k i j‖)*jumpMax D A i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
  rw [he]
  have hs : (∑ i : D, ∑ j : D, (∑ k ∈ Finset.range n, ‖B (k+1) i j-B k i j‖)*jumpMax D A i j) ≤
      2*(∑ i : D, ∑ j : D, ‖A 0 i j‖*jumpMax D A i j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have ht := mul_le_mul_of_nonneg_right (hvar i j) (jumpMax_nonneg D A i j)
    simpa only [mul_assoc] using ht
  have hz : 0 ≤ 3/2*meshMassConstant*h^2 := by have hm := meshMassConstant_pos; positivity
  calc
    _ ≤ (3/2*meshMassConstant*h^2)*(2*(∑ i : D, ∑ j : D, ‖A 0 i j‖*jumpMax D A i j)) := mul_le_mul_of_nonneg_left hs hz
    _ ≤ (3/2*meshMassConstant*h^2)*(2*(jumpScalarConstant*(∑ v, ∑ i, ∑ j, ‖A v i j‖^3))) := by
      gcongr
      exact sum_jumpMax_le D A
    _ = _ := by rw [arrayCubic_eq]; ring

lemma strictRate_ge_one (i v : Three) : 1 ≤ strictRate i v := by
  unfold strictRate; split_ifs <;> norm_num

lemma finite_masked_dissipation (D : Finset ℤ) (A : Three → Matrix D D ℂ)
    (B : ℕ → Matrix D D ℂ) (hB : ∀ k i j, ‖B k i j‖ ≤ ‖A 0 i j‖) (n : ℕ)
    (hvar : ∀ i j, (∑ k ∈ Finset.range n, ‖B (k+1) i j-B k i j‖) ≤ 2*‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) (t : ℕ → ℝ) (ht : Monotone t) (ht0 : h^2 ≤ t 0) (r : Three) :
    strictConstant * (∑ k ∈ Finset.range n,
      ∫ s in t k..t (k+1), ∑ v, planeIntegral (fun p => heatCost (replaceZero A (B k)) h
        (fun m => h*(m:ℤ)) p (fun z => strictRate r z*s) v v) 0) ≤ maskedConstant*arrayCubic A h := by
  have htpos (k : ℕ) : 0 < t k := (sq_pos_of_pos hh).trans_le (ht0.trans (ht (Nat.zero_le _)))
  have hσ (k : ℕ) (v : Three) : h^2 ≤ strictRate r v*t k :=
    (ht0.trans (ht (Nat.zero_le _))).trans (le_mul_of_one_le_left (htpos k).le (strictRate_ge_one r v))
  have hi := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) =>
    integrated_strict_dissipation (replaceZero A (B k)) hh (fun m => h*(m:ℤ)) 0 r
      (htpos k) (ht (Nat.le_succ k)))
  rw [← Finset.mul_sum] at hi
  apply hi.trans
  let E : ℕ → ℕ → ℝ := fun k l => totalPlaneEnergy (replaceZero A (B k)) h (fun m => h*(m:ℤ)) 0
    (fun v => strictRate r v*t l)
  have htel := telescope_with_jumps E n (totalPlaneEnergy_nonneg _ _ _ _ _)
  apply htel.trans
  have hin := (finite_mesh_totalPlaneEnergy_le D (replaceZero A (B 0)) hh 0 (hσ 0)).trans
    (mul_le_mul_of_nonneg_left (arrayCubic_replaceZero_le D A (B 0) (hB 0) h) (by have hm := meshMassConstant_pos; positivity))
  have hj := finite_mesh_total_jumps_le D A B hB n hvar hh (fun k v => strictRate r v*t (k+1)) (fun k v => hσ (k+1) v)
  change E 0 0 ≤ _ at hin
  change (∑ k ∈ Finset.range n, |E (k+1) (k+1)-E k (k+1)|) ≤ _ at hj
  apply (add_le_add hin hj).trans_eq
  unfold maskedConstant
  ring
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.finite_masked_dissipation := @_root_.OAI.TriangularHilbert.Heat.finite_masked_dissipation
